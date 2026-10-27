module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGammaS5

public section

namespace CFSG.ComponentClassification.GMS78.RuGamma

open CFSG.Open CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma

variable {G : Type*} [Group G]

theorem eq_of_mem_of_card_two {Z : Subgroup G} (hZc : Nat.card Z = 2) {a b : G} (ha : a ∈ Z)
    (hb : b ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZc]; norm_num)
  have := Fintype.ofFinite Z
  have h3 : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hab (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm, fun h => hb1 (congrArg Subtype.val h).symm⟩
  have h := Finset.card_le_univ ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset Z)
  rw [h3, ← Nat.card_eq_fintype_card, hZc] at h
  omega

theorem formB_zero_left (v : Fin 2 → F4) : formB 0 v = 0 := by
  have h := formB_add_left 0 0 v
  rw [add_zero] at h
  exact add_eq_left.1 h.symm

theorem exists_conj_mul_inv_mem_centralizer {H J X Z : Subgroup G} (hX : IsElemAbelian 2 X)
    (hXc : Nat.card X = 32) (hZX : Z ≤ X) (hZc : Nat.card Z = 2)
    (hZcen : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ = z) (hXn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hJ : ∀ h, h ∈ J ↔ h ∈ H ∧ ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ Z) (hidx : J.relIndex H = 120)
    (htr : ∀ x ∈ X, x ∉ Z → ∀ x' ∈ X, x' ∉ Z → ∃ h ∈ H, h * x * h⁻¹ * x'⁻¹ ∈ Z) {j j' : G}
    (hj : j ∈ J) (hj' : j' ∈ J) (hjX : j ∉ Subgroup.centralizer (X : Set G))
    (hj'X : j' ∉ Subgroup.centralizer (X : Set G)) :
    ∃ h ∈ H, h * j * h⁻¹ * j'⁻¹ ∈ J ⊓ Subgroup.centralizer (X : Set G) := by
  classical
  obtain ⟨-, φ, ψ, hφs, -, hψs, hψk, hψi⟩ := dempwolff218 hX hXc hZX hZc hZcen hXn hJ hidx htr
  have hJH : ∀ k ∈ J, k ∈ H := fun k hk => ((hJ k).1 hk).1
  have hcZ : ∀ k ∈ J, ∀ x ∈ X, k * x * k⁻¹ * x⁻¹ ∈ Z := fun k hk => ((hJ k).1 hk).2
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (@mul_comm' X _ hX.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have huniq : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ 1 → b ≠ 1 → a = b := fun a ha b hb =>
    eq_of_mem_of_card_two hZc ha hb
  let ind : G → F4 := fun c => if c = 1 then 0 else 1
  have hind : ∀ a ∈ Z, ∀ b ∈ Z, ind (a * b) = ind a + ind b := by
    intro a ha b hb
    by_cases ha1 : a = 1
    · subst ha1
      simp [ind]
    by_cases hb1 : b = 1
    · subst hb1
      simp [ind]
    obtain rfl := huniq a ha b hb ha1 hb1
    have ha2 : a * a = 1 := by
      by_contra h
      exact ha1 (mul_eq_left.1 (huniq _ (Z.mul_mem ha ha) a ha h ha1))
    simp only [ind, ha2, ha1, ite_true, ite_false]
    decide
  let sec : (Fin 2 → F4) → X := fun v => Function.surjInv hψs (Multiplicative.ofAdd v)
  have hsec : ∀ v, ψ (sec v) = Multiplicative.ofAdd v := fun v => Function.surjInv_eq hψs _
  have hsurjV : ∀ v : Fin 2 → F4, ∃ u : X, Multiplicative.toAdd (ψ u) = v :=
    fun v => ⟨sec v, by rw [hsec]; rfl⟩
  let ℓ : G → (Fin 2 → F4) → F4 := fun k v => ind (k * (sec v : G) * k⁻¹ * (sec v : G)⁻¹)
  have hℓ : ∀ k ∈ J, ∀ u : X,
      ℓ k (Multiplicative.toAdd (ψ u)) = ind (k * u * k⁻¹ * (u : G)⁻¹) := by
    intro k hk u
    set s := sec (Multiplicative.toAdd (ψ u))
    have hs : ψ s = ψ u := by rw [hsec, ofAdd_toAdd]
    have hz : (s : G)⁻¹ * u ∈ Z := by
      have h1 : s⁻¹ * u ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
      rw [hψk, Subgroup.mem_subgroupOf] at h1
      simpa using h1
    have hzc : k * ((s : G)⁻¹ * u) * k⁻¹ = (s : G)⁻¹ * u := hZcen k (hJH k hk) _ hz
    have e : k * u * k⁻¹ * (u : G)⁻¹ = k * s * k⁻¹ * (s : G)⁻¹ :=
      calc k * u * k⁻¹ * (u : G)⁻¹
          = k * s * k⁻¹ * (k * ((s : G)⁻¹ * u) * k⁻¹) * ((s : G)⁻¹ * u)⁻¹ * (s : G)⁻¹ := by
            group
        _ = k * s * k⁻¹ * (s : G)⁻¹ := by rw [hzc]; group
    rw [e]
  have hadd : ∀ k ∈ J, ∀ v w, ℓ k (v + w) = ℓ k v + ℓ k w := by
    intro k hk v w
    obtain ⟨u, rfl⟩ := hsurjV v
    obtain ⟨u', rfl⟩ := hsurjV w
    rw [← toAdd_mul, ← map_mul, hℓ k hk, hℓ k hk, hℓ k hk]
    have hc' := hcZ k hk u' u'.2
    have hcomm := hXcomm _ (hZX hc') _ (X.inv_mem u.2)
    have e : k * ((u * u' : X) : G) * k⁻¹ * ((u * u' : X) : G)⁻¹ =
        (k * u * k⁻¹ * (u : G)⁻¹) * (k * u' * k⁻¹ * (u' : G)⁻¹) :=
      calc k * ((u * u' : X) : G) * k⁻¹ * ((u * u' : X) : G)⁻¹
          = k * u * k⁻¹ * ((k * u' * k⁻¹ * (u' : G)⁻¹) * (u : G)⁻¹) := by
            rw [Subgroup.coe_mul]
            group
        _ = k * u * k⁻¹ * ((u : G)⁻¹ * (k * u' * k⁻¹ * (u' : G)⁻¹)) := by rw [hcomm]
        _ = (k * u * k⁻¹ * (u : G)⁻¹) * (k * u' * k⁻¹ * (u' : G)⁻¹) := by group
    rw [e]
    exact hind _ (hcZ k hk u u.2) _ hc'
  have hval : ∀ k v, ℓ k v = 0 ∨ ℓ k v = 1 := by
    intro k v
    simp only [ℓ, ind]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hconjJ : ∀ h ∈ H, ∀ k ∈ J, h * k * h⁻¹ ∈ J := by
    intro h hh k hk
    refine (hJ _).2 ⟨H.mul_mem (H.mul_mem hh (hJH k hk)) (H.inv_mem hh), fun x hx => ?_⟩
    have hx' : h⁻¹ * x * h⁻¹⁻¹ ∈ X := hXn h⁻¹ (H.inv_mem hh) x hx
    have hc := hcZ k hk _ hx'
    have e : h * k * h⁻¹ * x * (h * k * h⁻¹)⁻¹ * x⁻¹ =
        h * (k * (h⁻¹ * x * h⁻¹⁻¹) * k⁻¹ * (h⁻¹ * x * h⁻¹⁻¹)⁻¹) * h⁻¹ := by group
    rw [e, hZcen h hh _ hc]
    exact hc
  have hconjℓ : ∀ (h : H) (k : G), k ∈ J → ∀ v,
      ℓ (h * k * (h : G)⁻¹) (sigmaAct (φ h) v) = ℓ k v := by
    intro h k hk v
    obtain ⟨u, rfl⟩ := hsurjV v
    have hu' := hψi h u ⟨h * u * (h : G)⁻¹, hXn h h.2 u u.2⟩ rfl
    rw [show sigmaAct (φ h) (Multiplicative.toAdd (ψ u)) =
      Multiplicative.toAdd (ψ ⟨h * u * (h : G)⁻¹, hXn h h.2 u u.2⟩) by rw [hu']; rfl,
      hℓ _ (hconjJ h h.2 k hk), hℓ k hk]
    have e : (h : G) * k * (h : G)⁻¹ * ((h : G) * u * (h : G)⁻¹) * ((h : G) * k * (h : G)⁻¹)⁻¹ *
        ((h : G) * u * (h : G)⁻¹)⁻¹ = h * (k * u * k⁻¹ * (u : G)⁻¹) * (h : G)⁻¹ := by group
    change ind ((h : G) * k * (h : G)⁻¹ * ((h : G) * u * (h : G)⁻¹) *
      ((h : G) * k * (h : G)⁻¹)⁻¹ * ((h : G) * u * (h : G)⁻¹)⁻¹) = _
    rw [e, hZcen h h.2 _ (hcZ k hk u u.2)]
  have hw : ∀ k ∈ J, ∃ w, ∀ v, formB w v = ℓ k v := fun k hk =>
    exists_formB_eq (ℓ k) (hadd k hk) (hval k)
  have hw0 : ∀ k ∈ J, k ∉ Subgroup.centralizer (X : Set G) → ∀ w : Fin 2 → F4,
      (∀ v, formB w v = ℓ k v) → w ≠ 0 := by
    rintro k hk hkX w hw rfl
    apply hkX
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hw (Multiplicative.toAdd (ψ ⟨x, hx⟩))
    rw [formB_zero_left, hℓ k hk] at h1
    have h2 : k * x * k⁻¹ * x⁻¹ = 1 := by
      by_contra h
      simp only [ind, h, ite_false] at h1
      exact one_ne_zero h1.symm
    calc x * k = (k * x * k⁻¹ * x⁻¹)⁻¹ * k * x := by group
      _ = k * x := by rw [h2]; group
  obtain ⟨w₁, hw₁⟩ := hw j hj
  obtain ⟨w₂, hw₂⟩ := hw j' hj'
  obtain ⟨y, hy⟩ := exists_sigmaAct_eq (hw0 j hj hjX w₁ hw₁) (hw0 j' hj' hj'X w₂ hw₂)
  obtain ⟨h, rfl⟩ := hφs y
  refine ⟨h, h.2, Subgroup.mem_inf.2 ⟨J.mul_mem (hconjJ h h.2 j hj) (J.inv_mem hj'), ?_⟩⟩
  have hℓeq : ∀ v, ℓ (h * j * (h : G)⁻¹) v = ℓ j' v := by
    intro v
    have hv : v = sigmaAct (φ h) (sigmaAct (φ h)⁻¹ v) := by
      rw [← sigmaAct_mul, mul_inv_cancel, sigmaAct_one]
    rw [hv, hconjℓ h j hj, ← hw₁, ← hw₂, ← hy, formB_sigmaAct]
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : j'⁻¹ * x * j'⁻¹⁻¹ ∈ X := hXn j'⁻¹ (H.inv_mem (hJH j' hj')) x hx
  set u : X := ⟨j'⁻¹ * x * j'⁻¹⁻¹, hx'⟩
  have h1 := hℓeq (Multiplicative.toAdd (ψ u))
  rw [hℓ _ (hconjJ h h.2 j hj), hℓ j' hj'] at h1
  have hc1 := hcZ _ (hconjJ h h.2 j hj) u u.2
  have hc2 := hcZ j' hj' u u.2
  have heq : h * j * (h : G)⁻¹ * u * (h * j * (h : G)⁻¹)⁻¹ * (u : G)⁻¹ =
      j' * u * j'⁻¹ * (u : G)⁻¹ := by
    by_cases ha : h * j * (h : G)⁻¹ * u * (h * j * (h : G)⁻¹)⁻¹ * (u : G)⁻¹ = 1
    · by_cases hb : j' * u * j'⁻¹ * (u : G)⁻¹ = 1
      · rw [ha, hb]
      · simp only [ind, ha, hb, ite_true, ite_false] at h1
        exact absurd h1 zero_ne_one
    · by_cases hb : j' * u * j'⁻¹ * (u : G)⁻¹ = 1
      · simp only [ind, ha, hb, ite_true, ite_false] at h1
        exact absurd h1 one_ne_zero
      · exact huniq _ hc1 _ hc2 ha hb
  have hu : (u : G) = j'⁻¹ * x * j'⁻¹⁻¹ := rfl
  rw [hu] at heq
  have key : h * j * (h : G)⁻¹ * (j'⁻¹ * x * j'⁻¹⁻¹) * (h * j * (h : G)⁻¹)⁻¹ = x := by
    rw [mul_right_cancel heq]
    group
  calc x * (h * j * (h : G)⁻¹ * j'⁻¹)
      = h * j * (h : G)⁻¹ * (j'⁻¹ * x * j'⁻¹⁻¹) * (h * j * (h : G)⁻¹)⁻¹ *
          (h * j * (h : G)⁻¹ * j'⁻¹) := by rw [key]
    _ = h * j * (h : G)⁻¹ * j'⁻¹ * x := by group

end CFSG.ComponentClassification.GMS78.RuGamma
