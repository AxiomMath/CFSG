module

public import CFSG.ClassicalGroups.Unitary.Generation

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open scoped commutatorElement

variable {K : Type} [Field K]

section PairStab

@[expose] def uqPairStab (σ : K ≃+* K) (n : ℕ) (i j : Fin n) : Subgroup (GL (Fin n) K) :=
  SUid σ n ⊓ ⨅ k : Fin n, ⨅ (_ : k ≠ i), ⨅ (_ : k ≠ j),
    MulAction.stabilizer (GL (Fin n) K) (Pi.single k (1 : K) : Fin n → K)

theorem mem_uqPairStab {σ : K ≃+* K} {n : ℕ} {i j : Fin n} {g : GL (Fin n) K} :
    g ∈ uqPairStab σ n i j ↔ g ∈ SUid σ n ∧ ∀ k : Fin n, k ≠ i → k ≠ j →
      (g : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single k (1 : K) : Fin n → K) =
        Pi.single k (1 : K) := by
  unfold uqPairStab
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  rfl

end PairStab

section Plane

variable {σ : K ≃+* K} {n : ℕ}

@[expose] def uqPairPlane (i j : Fin n) : (Fin 2 → K) →ₗ[K] (Fin n → K) where
  toFun u := Pi.single i (u 0) + Pi.single j (u 1)
  map_add' u v := by
    simp only [Pi.add_apply, Pi.single_add]
    abel
  map_smul' c u := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add]
    rw [← Pi.single_smul, ← Pi.single_smul]
    rfl

theorem uqPairPlane_apply (i j : Fin n) (u : Fin 2 → K) :
    uqPairPlane i j u = Pi.single i (u 0) + Pi.single j (u 1) := rfl

theorem uqPairPlane_apply_left {i j : Fin n} (hij : i ≠ j) (u : Fin 2 → K) :
    uqPairPlane i j u i = u 0 := by
  simp [uqPairPlane_apply, Pi.single_eq_of_ne hij]

theorem uqPairPlane_apply_right {i j : Fin n} (hij : i ≠ j) (u : Fin 2 → K) :
    uqPairPlane i j u j = u 1 := by
  simp [uqPairPlane_apply, Pi.single_eq_of_ne hij.symm]

theorem uqPairPlane_apply_of_ne {i j k : Fin n} (hi : k ≠ i) (hj : k ≠ j) (u : Fin 2 → K) :
    uqPairPlane i j u k = 0 := by
  simp [uqPairPlane_apply, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj]

theorem herm_uqPairPlane {i j : Fin n} (hij : i ≠ j) (u v : Fin 2 → K) :
    herm σ (uqPairPlane i j u) (uqPairPlane i j v) = herm σ u v := by
  rw [uqPairPlane_apply, uqPairPlane_apply, herm_add_left, herm_single_left, herm_single_left]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm]
  simp only [herm, Fin.sum_univ_two]
  ring

theorem herm_uqPairPlane_eq_zero {i j : Fin n} {w : Fin n → K} (hi : w i = 0) (hj : w j = 0)
    (u : Fin 2 → K) : herm σ (uqPairPlane i j u) w = 0 := by
  rw [uqPairPlane_apply, herm_add_left, herm_single_left, herm_single_left, hi, hj]
  simp

theorem herm_uqPairPlane_single {i j k : Fin n} (hi : k ≠ i) (hj : k ≠ j) (u : Fin 2 → K) :
    herm σ (uqPairPlane i j u) (Pi.single k (1 : K) : Fin n → K) = 0 := by
  rw [herm_single_right, uqPairPlane_apply_of_ne hi hj, map_zero, zero_mul]

theorem uq_pair_sub_perp {i j : Fin n} (hij : i ≠ j) (v : Fin n → K) (u : Fin 2 → K) :
    herm σ (uqPairPlane i j u) (v - uqPairPlane i j ![v i, v j]) = 0 := by
  apply herm_uqPairPlane_eq_zero
  · simp [uqPairPlane_apply_left hij]
  · simp [uqPairPlane_apply_right hij]

theorem uq_pair_ext {i j : Fin n} (hij : i ≠ j) {g₁ g₂ : SUid σ n}
    (h1 : ∀ u : Fin 2 → K, g₁ • uqPairPlane i j u = g₂ • uqPairPlane i j u)
    (h2 : ∀ v : Fin n → K, (∀ u : Fin 2 → K, herm σ (uqPairPlane i j u) v = 0) →
      g₁ • v = g₂ • v) :
    g₁ = g₂ := by
  apply ext_smul
  intro v
  have hv : v = uqPairPlane i j ![v i, v j] + (v - uqPairPlane i j ![v i, v j]) := by abel
  rw [hv, smul_add, smul_add, h1, h2 _ (uq_pair_sub_perp hij v)]

end Plane

section Lift

variable {σ : K ≃+* K} {n : ℕ}

@[expose] def UqPairLift (i j : Fin n) (g : SUid σ n) (x : SUid σ 2) : Prop :=
  (∀ u : Fin 2 → K, g • uqPairPlane i j u = uqPairPlane i j (x • u)) ∧
    ∀ v : Fin n → K, (∀ u : Fin 2 → K, herm σ (uqPairPlane i j u) v = 0) → g • v = v

theorem UqPairLift.one (i j : Fin n) : UqPairLift i j (1 : SUid σ n) (1 : SUid σ 2) :=
  ⟨fun u => by rw [one_smul, one_smul], fun v _ => one_smul _ v⟩

theorem UqPairLift.mul {i j : Fin n} {g₁ g₂ : SUid σ n} {x₁ x₂ : SUid σ 2}
    (h₁ : UqPairLift i j g₁ x₁) (h₂ : UqPairLift i j g₂ x₂) :
    UqPairLift i j (g₁ * g₂) (x₁ * x₂) :=
  ⟨fun u => by rw [mul_smul, h₂.1, h₁.1, mul_smul], fun v hv => by
    rw [mul_smul, h₂.2 v hv, h₁.2 v hv]⟩

theorem UqPairLift.inv {i j : Fin n} {g : SUid σ n} {x : SUid σ 2} (h : UqPairLift i j g x) :
    UqPairLift i j g⁻¹ x⁻¹ :=
  ⟨fun u => by rw [inv_smul_eq_iff, h.1, smul_inv_smul], fun v hv => by
    rw [inv_smul_eq_iff, h.2 v hv]⟩

theorem UqPairLift.commutator {i j : Fin n} {g₁ g₂ : SUid σ n} {x₁ x₂ : SUid σ 2}
    (h₁ : UqPairLift i j g₁ x₁) (h₂ : UqPairLift i j g₂ x₂) :
    UqPairLift i j ⁅g₁, g₂⁆ ⁅x₁, x₂⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  exact ((h₁.mul h₂).mul h₁.inv).mul h₂.inv

theorem UqPairLift.mem_pairStab {i j : Fin n} {g : SUid σ n} {x : SUid σ 2}
    (h : UqPairLift i j g x) : (g : GL (Fin n) K) ∈ uqPairStab σ n i j := by
  rw [mem_uqPairStab]
  refine ⟨g.2, fun k hki hkj => ?_⟩
  exact h.2 _ (fun u => herm_uqPairPlane_single hki hkj u)

theorem uq_pair_exists_lift (hσ : IsUnitaryInvolution σ) (hP : Group.IsPerfect (SUid σ 2))
    {i j : Fin n} (hij : i ≠ j) (x : SUid σ 2) :
    ∃ g : SUid σ n, (g : GL (Fin n) K) ∈ ⁅uqPairStab σ n i j, uqPairStab σ n i j⁆ ∧
      UqPairLift i j g x := by
  set S := uqPairStab σ n i j
  let R : Subgroup (SUid σ 2) :=
    { carrier := {x | ∃ g : SUid σ n, (g : GL (Fin n) K) ∈ ⁅S, S⁆ ∧ UqPairLift i j g x}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨g₁, h₁, l₁⟩ := ha
        obtain ⟨g₂, h₂, l₂⟩ := hb
        exact ⟨g₁ * g₂, (⁅S, S⁆).mul_mem h₁ h₂, l₁.mul l₂⟩
      one_mem' := ⟨1, (⁅S, S⁆).one_mem, UqPairLift.one i j⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨g, h, l⟩ := ha
        exact ⟨g⁻¹, (⁅S, S⁆).inv_mem h, l.inv⟩ }
  have hlift : ∀ y : SUid σ 2, ∃ g : SUid σ n, UqPairLift i j g y := fun y => by
    obtain ⟨g, -, h1, h2⟩ := transport hσ.invol (uqPairPlane i j)
      (fun u v => herm_uqPairPlane hij u v) ((T_two_eq_top hσ).symm ▸ Subgroup.mem_top y)
    exact ⟨g, h1, h2⟩
  have hcomm : ⁅(⊤ : Subgroup (SUid σ 2)), ⊤⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro y _ z _
    obtain ⟨y', hy'⟩ := hlift y
    obtain ⟨z', hz'⟩ := hlift z
    exact ⟨⁅y', z'⁆, Subgroup.commutator_mem_commutator hy'.mem_pairStab
      hz'.mem_pairStab, hy'.commutator hz'⟩
  have htop : (⊤ : Subgroup (SUid σ 2)) ≤ R := by
    rw [← commutator_def, hP.commutator_eq_top] at hcomm
    exact hcomm
  exact htop (Subgroup.mem_top x)

end Lift

section Rotation

variable {σ : K ≃+* K} {n : ℕ}

theorem uq_pair_exists_rot (hσ : ∀ c, σ (σ c) = c) {u0 u1 : K}
    (h : σ u0 * u0 + σ u1 * u1 = 1) :
    ∃ x : SUid σ 2, ∀ v : Fin 2 → K,
      x • v = ![σ u0 * v 0 + σ u1 * v 1, -u1 * v 0 + u0 * v 1] := by
  set M : Matrix (Fin 2) (Fin 2) K := !![σ u0, σ u1; -u1, u0] with hM
  have hdet : M.det = 1 := by
    rw [hM, det_fin_two_of]
    linear_combination h
  have hu : conjTr σ M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, hM, Matrix.mul_apply, Fin.sum_univ_two, hσ] <;>
      first | ring1 | linear_combination h
  refine ⟨mkSU σ M hdet (fun x y => by rw [herm_mulVec, hu, one_mulVec]), fun v => ?_⟩
  rw [mkSU_smul]
  ext i
  fin_cases i <;> simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem uq_pair_exists_reduce (hσ : IsUnitaryInvolution σ) {s t : K}
    (hν : σ s * s + σ t * t ≠ 0) :
    ∃ (x : SUid σ 2) (b : K), b ≠ 0 ∧ x • ![s, t] = ![b, 0] := by
  have hsfix : σ (σ s * s + σ t * t) = σ s * s + σ t * t := by
    rw [map_add, hσ.norm_fixed, hσ.norm_fixed]
  obtain ⟨μ, hμ⟩ := hσ.exists_norm hsfix
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hμ
    exact hν hμ.symm
  have hσμ0 : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ0
  have hu : σ (s / μ) * (s / μ) + σ (t / μ) * (t / μ) = 1 := by
    rw [map_div₀, map_div₀]
    field_simp
    linear_combination -hμ
  obtain ⟨x, hx⟩ := uq_pair_exists_rot hσ.invol hu
  refine ⟨x, (σ s * s + σ t * t) / σ μ, div_ne_zero hν hσμ0, ?_⟩
  rw [hx]
  ext i
  fin_cases i
  · show σ (s / μ) * s + σ (t / μ) * t = (σ s * s + σ t * t) / σ μ
    rw [map_div₀, map_div₀]
    field_simp
  · show -(t / μ) * s + s / μ * t = 0
    ring

theorem uq_pair_smul_eq {i j : Fin n} (hij : i ≠ j) {g : SUid σ n} {x : SUid σ 2}
    (hg : UqPairLift i j g x) (a : Fin n → K) :
    g • a = a + uqPairPlane i j (x • ![a i, a j] - ![a i, a j]) := by
  have hv : a = uqPairPlane i j ![a i, a j] + (a - uqPairPlane i j ![a i, a j]) := by abel
  conv_lhs => rw [hv]
  rw [smul_add, hg.1, hg.2 _ (uq_pair_sub_perp hij a), map_sub]
  abel

end Rotation

section Support

variable {σ : K ≃+* K} {n : ℕ}

@[expose] noncomputable def uqPairSupp (a : Fin n → K) : Finset (Fin n) :=
  open Classical in Finset.univ.filter fun k => a k ≠ 0

theorem mem_uqPairSupp {a : Fin n → K} {k : Fin n} : k ∈ uqPairSupp a ↔ a k ≠ 0 := by
  simp [uqPairSupp]

theorem herm_self_eq_sum_uqPairSupp (a : Fin n → K) :
    herm σ a a = ∑ k ∈ uqPairSupp a, σ (a k) * a k := by
  rw [herm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have : a k = 0 := by
    by_contra h
    exact hk (mem_uqPairSupp.2 h)
  rw [this, map_zero, zero_mul]

theorem uq_pair_card_ne_one {a : Fin n → K} (ha : herm σ a a = 0) :
    (uqPairSupp a).card ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
  have hak : a k ≠ 0 := mem_uqPairSupp.1 (by rw [hk]; exact Finset.mem_singleton_self k)
  rw [herm_self_eq_sum_uqPairSupp, hk, Finset.sum_singleton] at ha
  exact mul_ne_zero ((map_ne_zero σ).mpr hak) hak ha

theorem uq_pair_exists_pair (h2 : (2 : K) ≠ 0) {a : Fin n → K} (hm : 3 ≤ (uqPairSupp a).card) :
    ∃ p q, p ∈ uqPairSupp a ∧ q ∈ uqPairSupp a ∧ p ≠ q ∧
      σ (a p) * a p + σ (a q) * a q ≠ 0 := by
  obtain ⟨i, j, l, hi, hj, hl, hij, hil, hjl⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < (uqPairSupp a).card)
  have hνi : σ (a i) * a i ≠ 0 :=
    mul_ne_zero ((map_ne_zero σ).mpr (mem_uqPairSupp.1 hi)) (mem_uqPairSupp.1 hi)
  by_contra hcon
  push Not at hcon
  have e1 := hcon i j hi hj hij
  have e2 := hcon i l hi hl hil
  have e3 := hcon j l hj hl hjl
  have : (2 : K) * (σ (a i) * a i) = 0 := by linear_combination e1 + e2 - e3
  exact hνi ((mul_eq_zero.mp this).resolve_left h2)

theorem uq_pair_card_lt {i j : Fin n} (hij : i ≠ j) {g : SUid σ n} {x : SUid σ 2}
    (hg : UqPairLift i j g x) {a : Fin n → K} {b : K}
    (hx : x • ![a i, a j] = ![b, 0]) (hi : a i ≠ 0) (hj : a j ≠ 0) :
    (uqPairSupp (g • a)).card < (uqPairSupp a).card := by
  have hsub : uqPairSupp (g • a) ⊆ (uqPairSupp a).erase j := by
    intro k hk
    rw [mem_uqPairSupp, uq_pair_smul_eq hij hg a, hx] at hk
    rw [Finset.mem_erase, mem_uqPairSupp]
    by_cases hkj : k = j
    · subst hkj
      simp [uqPairPlane_apply_right hij] at hk
    · refine ⟨hkj, ?_⟩
      by_cases hki : k = i
      · subst hki
        exact hi
      · simpa [uqPairPlane_apply_of_ne hki hkj] using hk
  exact lt_of_le_of_lt (Finset.card_le_card hsub)
    (Finset.card_erase_lt_of_mem (mem_uqPairSupp.2 hj))

end Support

section Generation

variable {σ : K ≃+* K} {n : ℕ}

theorem uq_pair_tv_mem_of_card_two (hσ : IsUnitaryInvolution σ) (hP : Group.IsPerfect (SUid σ 2))
    {a : Fin n → K} (ha : herm σ a a = 0) {c : K} (hc : c + σ c = 0)
    (hm : (uqPairSupp a).card = 2) :
    ∃ i j : Fin n, i ≠ j ∧ ((tv hσ.invol ha hc : SUid σ n) : GL (Fin n) K) ∈
      ⁅uqPairStab σ n i j, uqPairStab σ n i j⁆ := by
  obtain ⟨i, j, hij, hsupp⟩ := Finset.card_eq_two.mp hm
  have ha_eq : a = uqPairPlane i j ![a i, a j] := by
    funext k
    by_cases hki : k = i
    · subst hki
      rw [uqPairPlane_apply_left hij]
      rfl
    · by_cases hkj : k = j
      · subst hkj
        rw [uqPairPlane_apply_right hij]
        rfl
      · rw [uqPairPlane_apply_of_ne hki hkj]
        by_contra hne
        have := mem_uqPairSupp.2 hne
        rw [hsupp] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        tauto
  set a2 : Fin 2 → K := ![a i, a j]
  have ha2iso : herm σ a2 a2 = 0 := by
    rw [← herm_uqPairPlane (σ := σ) hij, ← ha_eq]
    exact ha
  obtain ⟨g, hgS, hg⟩ := uq_pair_exists_lift hσ hP hij (tv hσ.invol ha2iso hc)
  have hgt : g = tv hσ.invol ha hc := by
    apply uq_pair_ext hij
    · intro u
      have e1 : herm σ a (uqPairPlane i j u) = herm σ a2 u := by
        conv_lhs => rw [ha_eq]
        exact herm_uqPairPlane hij _ _
      rw [hg.1, tv_smul, tv_smul, e1, map_add, map_smul, ← ha_eq]
    · intro v hv
      have e2 : herm σ a v = 0 := by
        rw [ha_eq]
        exact hv a2
      rw [hg.2 v hv, tv_smul, e2, mul_zero, zero_smul, add_zero]
  exact ⟨i, j, hij, hgt ▸ hgS⟩

theorem uq_pair_tv_mem (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0)
    (hP : Group.IsPerfect (SUid σ 2)) (H : Subgroup (GL (Fin n) K))
    (hH : ∀ i j : Fin n, i ≠ j → ⁅uqPairStab σ n i j, uqPairStab σ n i j⁆ ≤ H)
    (a : Fin n → K) (ha : herm σ a a = 0) {c : K} (hc : c + σ c = 0) :
    ((tv hσ.invol ha hc : SUid σ n) : GL (Fin n) K) ∈ H := by
  suffices key : ∀ m : ℕ, ∀ a : Fin n → K, (uqPairSupp a).card = m → ∀ (ha : herm σ a a = 0)
      {c : K} (hc : c + σ c = 0), ((tv hσ.invol ha hc : SUid σ n) : GL (Fin n) K) ∈ H from
    key _ a rfl ha hc
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro a hm ha c hc
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · interval_cases m
      · have : tv hσ.invol ha hc = 1 := by
          apply ext_smul
          intro v
          have ha0 : a = 0 := funext fun k => by
            by_contra h
            have := mem_uqPairSupp.2 h
            rw [Finset.card_eq_zero.mp hm] at this
            simp at this
          rw [tv_smul, ha0, herm_zero_left, mul_zero, zero_smul, add_zero, one_smul]
        rw [this]
        exact H.one_mem
      · exact absurd hm (uq_pair_card_ne_one ha)
      · obtain ⟨i, j, hij, hmem⟩ := uq_pair_tv_mem_of_card_two hσ hP ha hc hm
        exact hH i j hij hmem
    · obtain ⟨p, q, hp, hq, hpq, hν⟩ := uq_pair_exists_pair (σ := σ) (a := a) h2 (by omega)
      obtain ⟨x, b, -, hx⟩ := uq_pair_exists_reduce hσ hν
      obtain ⟨g, hgS, hg⟩ := uq_pair_exists_lift hσ hP hpq x
      have ha' : herm σ (g • a) (g • a) = 0 := by
        rw [herm_smul_smul]
        exact ha
      have hlt := uq_pair_card_lt hpq hg hx (mem_uqPairSupp.1 hp) (mem_uqPairSupp.1 hq)
      have ih' := ih _ (hm ▸ hlt) (g • a) rfl ha' hc
      have ht : tv hσ.invol ha hc = g⁻¹ * tv hσ.invol ha' hc * g := by
        apply ext_smul
        intro v
        have := conj_smul_of_tv g⁻¹ (tv hσ.invol ha' hc) (a := g • a) (c := c)
          (tv_smul hσ.invol ha' hc) v
        rw [inv_smul_smul, inv_inv] at this
        rw [tv_smul, this]
      rw [ht]
      have h1 : (g : GL (Fin n) K) ∈ H := hH p q hpq hgS
      exact H.mul_mem (H.mul_mem (H.inv_mem h1) ih') h1

theorem uq_le_of_pair_derived (hσ : IsUnitaryInvolution σ)
    (hq : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) (h2 : (2 : K) ≠ 0) (hP : Group.IsPerfect (SUid σ 2))
    {n : ℕ} (hn : 3 ≤ n) (H : Subgroup (GL (Fin n) K))
    (hH : ∀ i j : Fin n, i ≠ j → ⁅uqPairStab σ n i j, uqPairStab σ n i j⁆ ≤ H) :
    SUid σ n ≤ H := by
  intro g hg
  have hT : T σ n = ⊤ := T_eq_top hσ (by omega) (fun _ => hq)
  have hle : T σ n ≤ H.comap (SUid σ n).subtype := by
    rw [T, Subgroup.closure_le]
    rintro t ⟨a, c, ha, hc, ht⟩
    have : t = tv hσ.invol ha hc := by
      apply ext_smul
      intro v
      rw [ht, tv_smul]
    rw [this]
    exact uq_pair_tv_mem hσ h2 hP H hH a ha hc
  have hgT : (⟨g, hg⟩ : SUid σ n) ∈ T σ n := by
    rw [hT]
    exact Subgroup.mem_top _
  exact hle hgT

end Generation

end CFSG.GH74.GLS.Stage2.Bender.Thm1
