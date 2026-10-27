module

public import CFSG.GH74.GLS.Stage4.T2P56Wr
public import CFSG.GH74.GLS.Stage4.T2P56Outer

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.Assembly.LowTwoRank

section Sub

variable {G : Type} [Group G] [Finite G]

theorem hasWreathedSylow_sub (X : Subgroup G) {T : Subgroup G} {z u a w h : G}
    (hTX : T ≤ X) (hzX : z ∈ X) (huX : u ∈ X) (haX : a ∈ X) (hwX : w ∈ X) (hhX : h ∈ X)
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hT2 : ∀ x ∈ T, TwoElt x)
    (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) (hz1 : z ≠ 1) (hu1 : u ≠ 1)
    (hzne : z ≠ u) (hzT : z ∈ T) (huT : u ∈ T)
    (hΩ : ∀ x ∈ T, x * x = 1 → x ∈ t2U z u)
    (hcent : ∀ g ∈ X, g * z = z * g → g * u = u * g → TwoElt g → g ∈ T)
    (hT4 : ∃ x ∈ T, x * x ≠ 1)
    (haT : ∀ x ∈ T, a * x * a⁻¹ ∈ T) (haT' : ∀ x ∈ T, a⁻¹ * x * a ∈ T)
    (ha3 : ∀ x ∈ T, a ^ 3 * x = x * a ^ 3) (haz : a⁻¹ * z * a = u) (hau : a⁻¹ * u * a = z * u)
    (hw2 : w * w = z) (hwT : ∀ x ∈ T, w * x * w⁻¹ ∈ T) (hwu : w * u * w⁻¹ = u * z)
    (hh : ∀ x ∈ T, h * x = x * h) (hwa : w * a * w⁻¹ = a⁻¹ * h) :
    ∃ S : Sylow 2 ↥X, ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥(S : Subgroup ↥X) ≃* CFSG.Open.WreathedTwoGroup m) := by
  have hmemT : ∀ x : ↥X, x ∈ T.subgroupOf X ↔ (x : G) ∈ T := fun x => Subgroup.mem_subgroupOf
  have hz' : (⟨z, hzX⟩ : ↥X) ∈ T.subgroupOf X := (hmemT _).2 hzT
  have hu' : (⟨u, huX⟩ : ↥X) ∈ T.subgroupOf X := (hmemT _).2 huT
  refine hasWreathedSylow_of_data (T := T.subgroupOf X) (z := ⟨z, hzX⟩) (u := ⟨u, huX⟩)
    (a := ⟨a, haX⟩) (w := ⟨w, hwX⟩) (h := ⟨h, hhX⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz' hu' ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx y hy
    exact Subtype.ext (hTc _ ((hmemT x).1 hx) _ ((hmemT y).1 hy))
  · intro x hx
    obtain ⟨k, hk⟩ := hT2 _ ((hmemT x).1 hx)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · exact Subtype.ext (by simpa using hz2)
  · exact Subtype.ext (by simpa using hu2)
  · exact Subtype.ext hzu
  · intro h'
    exact hz1 (congrArg Subtype.val h')
  · intro h'
    exact hu1 (congrArg Subtype.val h')
  · intro h'
    exact hzne (congrArg Subtype.val h')
  ·
    intro x hx hx2
    have hx2' : (x : G) * (x : G) = 1 := by simpa using congrArg Subtype.val hx2
    have h1 := hΩ _ ((hmemT x).1 hx) hx2'
    have hmem := (t2U_mem hz2 hu2 hzu).1 h1
    have hz2' : (⟨z, hzX⟩ : ↥X) * ⟨z, hzX⟩ = 1 := Subtype.ext (by simpa using hz2)
    have hu2' : (⟨u, huX⟩ : ↥X) * ⟨u, huX⟩ = 1 := Subtype.ext (by simpa using hu2)
    have hzu' : (⟨z, hzX⟩ : ↥X) * ⟨u, huX⟩ = ⟨u, huX⟩ * ⟨z, hzX⟩ := Subtype.ext hzu
    refine (t2U_mem hz2' hu2' hzu').2 ?_
    rcases hmem with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  ·
    intro g hgz hgu hg2
    refine (hmemT g).2 (hcent g g.2 ?_ ?_ ?_)
    · exact congrArg Subtype.val hgz
    · exact congrArg Subtype.val hgu
    · obtain ⟨k, hk⟩ := hg2
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  ·
    obtain ⟨x, hx, hx1⟩ := hT4
    exact ⟨⟨x, hTX hx⟩, (hmemT _).2 hx, fun h' => hx1 (by simpa using congrArg Subtype.val h')⟩
  · intro x hx
    exact (hmemT _).2 (haT _ ((hmemT _).1 hx))
  · intro x hx
    exact (hmemT _).2 (haT' _ ((hmemT _).1 hx))
  · intro x hx
    exact Subtype.ext (by simpa using ha3 _ ((hmemT x).1 hx))
  · exact Subtype.ext haz
  · exact Subtype.ext hau
  · exact Subtype.ext hw2
  · intro x hx
    exact (hmemT _).2 (hwT _ ((hmemT _).1 hx))
  · exact Subtype.ext hwu
  · intro x hx
    exact Subtype.ext (hh _ ((hmemT x).1 hx))
  · exact Subtype.ext hwa

end Sub

section Cyc

variable {G : Type} [Group G]

theorem cyc_invol (H₁ : Subgroup G) (hH : IsCyclic ↥H₁) (hdvd : 4 ∣ Nat.card ↥H₁) {z : G}
    (hzH : z ∈ H₁) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    (∀ y ∈ H₁, y * y = 1 → y = 1 ∨ y = z) ∧ ∃ c ∈ H₁, c * c = z := by
  obtain ⟨g, hg⟩ := hH.exists_generator
  set c : G := (g : G) with hc
  obtain ⟨m, hm⟩ := hdvd
  have hord : orderOf c = 4 * m := by
    rw [hc, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact hm
  have hcH : c ∈ H₁ := g.2
  have hpow : ∀ x ∈ H₁, ∃ n : ℤ, c ^ n = x := by
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    exact ⟨n, congrArg Subtype.val hn⟩
  have hww : c ^ (2 * m) * c ^ (2 * m) = 1 := by
    rw [← pow_add, show 2 * m + 2 * m = 4 * m by ring, ← hord]
    exact pow_orderOf_eq_one c
  have hA : ∀ y ∈ H₁, y * y = 1 → y = 1 ∨ y = c ^ (2 * m) := by
    intro y hy hy2
    obtain ⟨r, rfl⟩ := hpow y hy
    have h1 : c ^ (r + r) = 1 := by rw [zpow_add, hy2]
    have h2 : ((4 * m : ℕ) : ℤ) ∣ r + r := by
      rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.2 h1
    have h3 : ((2 * m : ℕ) : ℤ) ∣ r := by
      have : (2 : ℤ) * ((2 * m : ℕ) : ℤ) ∣ 2 * r := by
        have e : r + r = 2 * r := by ring
        rw [e] at h2
        have e2 : ((4 * m : ℕ) : ℤ) = 2 * ((2 * m : ℕ) : ℤ) := by push_cast; ring
        rwa [e2] at h2
      exact Int.dvd_of_mul_dvd_mul_left (by norm_num) this
    obtain ⟨s, hs⟩ := h3
    have h4 : c ^ r = (c ^ (2 * m)) ^ s := by
      rw [hs, zpow_mul, zpow_natCast]
    rcases t2H_zpow_invol hww s with h5 | h5
    · left; rw [h4, h5]
    · right; rw [h4, h5]
  have hzw : z = c ^ (2 * m) := (hA z hzH hz2).resolve_left hz1
  refine ⟨?_, ⟨c ^ m, H₁.pow_mem hcH m, ?_⟩⟩
  · intro y hy hy2
    rcases hA y hy hy2 with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzw.symm)
  · rw [← pow_add, show m + m = 2 * m by ring]
    exact hzw.symm

end Cyc

section InvolU

variable {G : Type} [Group G]

theorem invol_mem_sup_aux {H H₁ H₂ K₁ K₂ : Subgroup G} {z c₁ c₂ : G}
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (h₁ : H₁ ≤ H) (h₂ : H₂ ≤ H) (hzH : z ∈ H)
    (hH₁K : H₁ ≤ K₁) (hH₂K : H₂ ≤ K₂) (hKK : K₁ ⊓ K₂ ≤ Subgroup.zpowers z) (hz2 : z * z = 1)
    (hinv₁ : ∀ y ∈ H₁, y * y = 1 → y = 1 ∨ y = z) (hinv₂ : ∀ y ∈ H₂, y * y = 1 → y = 1 ∨ y = z)
    (hc₁ : c₁ ∈ H₁) (hc₁sq : c₁ * c₁ = z) (hc₂ : c₂ ∈ H₂) (hc₂sq : c₂ * c₂ = z)
    {x : G} (hx : x ∈ H₁ ⊔ H₂) (hx2 : x * x = 1) :
    x = 1 ∨ x = z ∨ x = c₁ * c₂ ∨ x = z * (c₁ * c₂) := by
  have hcomm12 : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a := fun a ha b hb => hHc a (h₁ ha) b (h₂ hb)
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := (mem_sup_iff_of_comm hcomm12 x).1 hx
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hc₁H : c₁ ∈ H := h₁ hc₁
  have hc₂H : c₂ ∈ H := h₂ hc₂
  have hp₁H : p₁ ∈ H := h₁ hp₁
  have hp₂H : p₂ ∈ H := h₂ hp₂
  have hc12 : p₁ * p₂ = p₂ * p₁ := hcomm12 p₁ hp₁ p₂ hp₂
  have hsq : (p₁ * p₁) * (p₂ * p₂) = 1 := by
    calc (p₁ * p₁) * (p₂ * p₂) = p₁ * (p₁ * p₂) * p₂ := by group
      _ = p₁ * (p₂ * p₁) * p₂ := by rw [hc12]
      _ = (p₁ * p₂) * (p₁ * p₂) := by group
      _ = 1 := hx2
  have hp₁sq : p₁ * p₁ ∈ Subgroup.zpowers z := by
    apply hKK
    refine ⟨(K₁).mul_mem (hH₁K hp₁) (hH₁K hp₁), ?_⟩
    have : p₁ * p₁ = (p₂ * p₂)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact K₂.inv_mem (K₂.mul_mem (hH₂K hp₂) (hH₂K hp₂))
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hp₁sq
  have hcz₁ : c₁ * z = z * c₁ := hHc c₁ hc₁H z hzH
  have hcz₂ : c₂ * z = z * c₂ := hHc c₂ hc₂H z hzH
  rcases t2H_zpow_invol hz2 n with h | h
  ·
    have h11 : p₁ * p₁ = 1 := by rw [← hn, h]
    have h22 : p₂ * p₂ = 1 := by rw [h11, one_mul] at hsq; exact hsq
    rcases hinv₁ p₁ hp₁ h11 with rfl | rfl <;> rcases hinv₂ p₂ hp₂ h22 with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inl hz2
  ·
    have h11 : p₁ * p₁ = z := by rw [← hn, h]
    have h22 : p₂ * p₂ = z := by
      rw [h11] at hsq
      calc p₂ * p₂ = z⁻¹ * (z * (p₂ * p₂)) := by group
        _ = z := by rw [hsq, mul_one, hzi]
    have e₁ : p₁ = c₁ ∨ p₁ = z * c₁ := by
      have hc : (p₁ * c₁⁻¹) * (p₁ * c₁⁻¹) = 1 := by
        have hpc : p₁ * c₁⁻¹ = c₁⁻¹ * p₁ := by
          have := hHc p₁ hp₁H c₁⁻¹ (H.inv_mem hc₁H)
          exact this
        calc (p₁ * c₁⁻¹) * (p₁ * c₁⁻¹) = p₁ * (c₁⁻¹ * p₁) * c₁⁻¹ := by group
          _ = p₁ * (p₁ * c₁⁻¹) * c₁⁻¹ := by rw [← hpc]
          _ = (p₁ * p₁) * (c₁⁻¹ * c₁⁻¹) := by group
          _ = z * (c₁ * c₁)⁻¹ := by rw [h11]; group
          _ = 1 := by rw [hc₁sq, hzi]; exact hz2
      have hmem : p₁ * c₁⁻¹ ∈ H₁ := H₁.mul_mem hp₁ (H₁.inv_mem hc₁)
      rcases hinv₁ _ hmem hc with h' | h'
      · left; calc p₁ = (p₁ * c₁⁻¹) * c₁ := by group
          _ = c₁ := by rw [h', one_mul]
      · right; calc p₁ = (p₁ * c₁⁻¹) * c₁ := by group
          _ = z * c₁ := by rw [h']
    have e₂ : p₂ = c₂ ∨ p₂ = z * c₂ := by
      have hc : (p₂ * c₂⁻¹) * (p₂ * c₂⁻¹) = 1 := by
        have hpc : p₂ * c₂⁻¹ = c₂⁻¹ * p₂ := by
          have := hHc p₂ hp₂H c₂⁻¹ (H.inv_mem hc₂H)
          exact this
        calc (p₂ * c₂⁻¹) * (p₂ * c₂⁻¹) = p₂ * (c₂⁻¹ * p₂) * c₂⁻¹ := by group
          _ = p₂ * (p₂ * c₂⁻¹) * c₂⁻¹ := by rw [← hpc]
          _ = (p₂ * p₂) * (c₂⁻¹ * c₂⁻¹) := by group
          _ = z * (c₂ * c₂)⁻¹ := by rw [h22]; group
          _ = 1 := by rw [hc₂sq, hzi]; exact hz2
      have hmem : p₂ * c₂⁻¹ ∈ H₂ := H₂.mul_mem hp₂ (H₂.inv_mem hc₂)
      rcases hinv₂ _ hmem hc with h' | h'
      · left; calc p₂ = (p₂ * c₂⁻¹) * c₂ := by group
          _ = c₂ := by rw [h', one_mul]
      · right; calc p₂ = (p₂ * c₂⁻¹) * c₂ := by group
          _ = z * c₂ := by rw [h']
    have hzc₁ : z * c₁ = c₁ * z := hcz₁.symm
    rcases e₁ with rfl | rfl <;> rcases e₂ with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · refine Or.inr (Or.inr (Or.inr ?_))
      calc p₁ * (z * c₂) = (p₁ * z) * c₂ := by group
        _ = (z * p₁) * c₂ := by rw [hcz₁]
        _ = z * (p₁ * c₂) := by group
    · refine Or.inr (Or.inr (Or.inr ?_))
      group
    · refine Or.inr (Or.inr (Or.inl ?_))
      calc z * c₁ * (z * c₂) = z * (c₁ * z) * c₂ := by group
        _ = z * (z * c₁) * c₂ := by rw [hcz₁]
        _ = (z * z) * (c₁ * c₂) := by group
        _ = c₁ * c₂ := by rw [hz2, one_mul]

end InvolU

section Loc

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

def twoPart (H : Subgroup G) (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) : Subgroup G where
  carrier := {x | x ∈ H ∧ TwoElt x}
  mul_mem' := by
    intro a b ha hb
    exact ⟨H.mul_mem ha.1 hb.1, TwoElt.mul (hc a ha.1 b hb.1) ha.2 hb.2⟩
  one_mem' := ⟨H.one_mem, TwoElt.one⟩
  inv_mem' := by
    intro a ha
    exact ⟨H.inv_mem ha.1, ha.2.inv⟩

omit [Finite G] in
theorem mem_twoPart {H : Subgroup G} {hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x} {x : G} :
    x ∈ twoPart H hc ↔ x ∈ H ∧ TwoElt x := Iff.rfl

theorem involution_mem_U
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5 N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) (h₁ : q₁ % 4 = 1) (h₂ : q₂ % 4 = 1) :
    ∀ x ∈ N.H, x * x = 1 → x ∈ t2U N.z u := by
  subst hz hK₁ hK₂ hq₁ hq₂
  have hHc := hLoc.H_comm
  have hz2 : N.z * N.z = 1 := by
    have h := pow_orderOf_eq_one N.z
    rw [hLoc.z_ord, sq] at h
    exact h
  have hz1 : N.z ≠ 1 := by
    intro h
    have := hLoc.z_ord
    rw [h, orderOf_one] at this
    omega
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  have hzu : N.z * u = u * N.z := hHc _ hLoc.z_mem_H u hLoc.u_mem_H
  have hq₁5 : 5 ≤ N.q₁ := hLoc.q₁_ge
  have hq₂5 : 5 ≤ N.q₂ := by have := hLoc.q₂_ge; omega
  have hd₁ : 4 ∣ Nat.card ↥(N.H ⊓ N.K₁) := by rw [hLoc.card_H_K₁]; omega
  have hd₂ : 4 ∣ Nat.card ↥(N.H ⊓ N.K₂) := by rw [hLoc.card_H_K₂]; omega
  obtain ⟨hinv₁, c₁, hc₁H, hc₁⟩ := cyc_invol (N.H ⊓ N.K₁) hLoc.H₁_cyc hd₁
    ⟨hLoc.z_mem_H, hLoc.z_mem_K₁⟩ hz2 hz1
  obtain ⟨hinv₂, c₂, hc₂H, hc₂⟩ := cyc_invol (N.H ⊓ N.K₂) hLoc.H₂_cyc hd₂
    ⟨hLoc.z_mem_H, hLoc.z_mem_K₂⟩ hz2 hz1
  set M : Subgroup G := (N.H ⊓ N.K₁) ⊔ (N.H ⊓ N.K₂) with hM
  have hMK : M ≤ N.K₁ ⊔ N.K₂ :=
    sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)
  have hHK : ∀ x ∈ N.H, x ∈ N.K₁ ⊔ N.K₂ → x ∈ M := by
    intro x hxH hxK
    by_contra hxM
    have hidx' : (M.subgroupOf N.H).index = 2 := hLoc.H_idx
    obtain ⟨h₀, hh₀H, hh₀K⟩ := IsConcreteLE.not_le_iff_exists.1 hLoc.H_not_le_K
    have hh₀M : h₀ ∉ M := fun h => hh₀K (hMK h)
    have hmem : x * h₀ ∈ M := by
      have : (⟨x, hxH⟩ : ↥N.H) * ⟨h₀, hh₀H⟩ ∈ M.subgroupOf N.H := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx']
        exact iff_of_false (by rwa [Subgroup.mem_subgroupOf]) (by rwa [Subgroup.mem_subgroupOf])
      exact this
    apply hh₀K
    have : h₀ = x⁻¹ * (x * h₀) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxK) (hMK hmem)
  have hS4 : ∀ x ∈ N.H, x * x = 1 →
      x = 1 ∨ x = N.z ∨ x = c₁ * c₂ ∨ x = N.z * (c₁ * c₂) := by
    intro x hx hx2
    have hxK : x ∈ N.K₁ ⊔ N.K₂ := by
      by_contra hxK
      exact no_invol_outside_K hSet hRem hLoc rfl rfl rfl rfl rfl h₂ hx hxK hx2
    exact invol_mem_sup_aux hHc inf_le_left inf_le_left hLoc.z_mem_H inf_le_right inf_le_right
      hLoc.K_inter hz2 hinv₁ hinv₂ hc₁H hc₁ hc₂H hc₂ (hHK x hx hxK) hx2
  have hu := hS4 u hLoc.u_mem_H hu2
  have hzi : N.z⁻¹ = N.z := inv_eq_of_mul_eq_one_right hz2
  intro x hx hx2
  refine (t2U_mem hz2 hu2 hzu).2 ?_
  have hzz : N.z * (N.z * (c₁ * c₂)) = c₁ * c₂ := by
    calc N.z * (N.z * (c₁ * c₂)) = (N.z * N.z) * (c₁ * c₂) := by group
      _ = c₁ * c₂ := by rw [hz2, one_mul]
  rcases hu with hu | hu | hu | hu
  · exact absurd hu hu1
  · exact absurd hu hLoc.u_ne
  · rcases hS4 x hx hx2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (h.trans hu.symm)))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, hu])))
  · rcases hS4 x hx hx2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (by rw [h, hu, hzz])))
    · exact Or.inr (Or.inr (Or.inl (h.trans hu.symm)))

theorem hasWreathedSylow_of_loc5
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5 N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) (h₁ : q₁ % 4 = 1) (h₂ : q₂ % 4 = 1) {y : G} (hyH : y ∈ N.H) (hy1 : y ≠ 1)
    (hyodd : Odd (orderOf y)) {a w h₀ : G} (haN : a ∈ normalizer (N.H : Set G)) (ha3 : a ^ 3 ∈ N.H)
    (haz : a⁻¹ * N.z * a = u) (hau : a⁻¹ * u * a = N.z * u) (hay : a * y = y * a)
    (hwy : w * y = y * w) (hwN : w ∈ normalizer (N.H : Set G)) (hw2 : w * w = N.z)
    (hwu : w * u * w⁻¹ = u * N.z) (hh₀ : h₀ ∈ N.H) (hwa : w * a * w⁻¹ = a⁻¹ * h₀) :
    HasWreathedSylow ↥(centralizer ({y} : Set G)) := by
  have hHc := hLoc.H_comm
  have hy2 : y * y ≠ 1 := by
    intro h
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
    · exact hy1 (orderOf_eq_one_iff.1 h3)
    · rw [h3] at hyodd
      exact absurd hyodd (by decide)
  have hz2 : N.z * N.z = 1 := by
    have h := pow_orderOf_eq_one N.z
    rw [hLoc.z_ord, sq] at h
    exact h
  have hz1 : N.z ≠ 1 := by
    intro h
    have := hLoc.z_ord
    rw [h, orderOf_one] at this
    omega
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  have hzu : N.z * u = u * N.z := hHc _ hLoc.z_mem_H u hLoc.u_mem_H
  have hΩ := involution_mem_U hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂ h₁ h₂
  have hzT : N.z ∈ twoPart N.H hHc := ⟨hLoc.z_mem_H, TwoElt.of_sq_eq_one hz2⟩
  have huT : u ∈ twoPart N.H hHc := ⟨hLoc.u_mem_H, TwoElt.of_sq_eq_one hu2⟩
  have hcomm : ∀ x ∈ N.H, x * y = y * x := fun x hx => hHc x hx y hyH
  have hmemX : ∀ x : G, x * y = y * x → x ∈ centralizer ({y} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 hx
  have hq₁5 : 5 ≤ q₁ := by rw [← hq₁]; exact hLoc.q₁_ge
  have hd₁ : 4 ∣ Nat.card ↥(N.H ⊓ N.K₁) := by rw [hLoc.card_H_K₁, hq₁]; omega
  obtain ⟨-, c₁, hc₁H, hc₁⟩ := cyc_invol (N.H ⊓ N.K₁) hLoc.H₁_cyc hd₁
    ⟨hLoc.z_mem_H, hLoc.z_mem_K₁⟩ hz2 hz1
  have hT4 : ∃ x ∈ twoPart N.H hHc, x * x ≠ 1 := by
    refine ⟨c₁, ⟨hc₁H.1, ⟨2, ?_⟩⟩, ?_⟩
    · calc c₁ ^ 2 ^ 2 = (c₁ * c₁) * (c₁ * c₁) := by
            rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
        _ = 1 := by rw [hc₁]; exact hz2
    · rw [hc₁]; exact hz1
  have hres := hasWreathedSylow_sub (centralizer ({y} : Set G)) (T := twoPart N.H hHc)
    (z := N.z) (u := u) (a := a) (w := w) (h := h₀)
    (fun x hx => hmemX x (hcomm x hx.1)) (hmemX _ (hcomm _ hLoc.z_mem_H))
    (hmemX _ (hcomm _ hLoc.u_mem_H)) (hmemX _ hay) (hmemX _ hwy) (hmemX _ (hcomm _ hh₀))
    (fun x hx y' hy' => hHc x hx.1 y' hy'.1) (fun x hx => hx.2) hz2 hu2 hzu hz1 hu1 hLoc.u_ne.symm
    hzT huT (fun x hx hx2 => hΩ x hx.1 hx2)
    (fun g hg hgz hgu hg2 => ⟨twoElt_cent_mem_H hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂ hyH hy2
      (Subgroup.mem_centralizer_singleton_iff.1 hg) hgz hgu hg2, hg2⟩) hT4
    (fun x hx => ⟨(Subgroup.mem_normalizer_iff.1 haN x).1 hx.1, hx.2.conj a⟩)
    (fun x hx => ⟨(Subgroup.mem_normalizer_iff.1 haN (a⁻¹ * x * a)).2
        (by rw [show a * (a⁻¹ * x * a) * a⁻¹ = x by group]; exact hx.1), by simpa using hx.2.conj a⁻¹⟩)
    (fun x hx => hHc _ ha3 x hx.1) haz hau hw2
    (fun x hx => ⟨(Subgroup.mem_normalizer_iff.1 hwN x).1 hx.1, hx.2.conj w⟩) hwu
    (fun x hx => hHc _ hh₀ x hx.1) hwa
  exact hres

end Loc

end CFSG.GH74.GLS.Stage4.Rest
