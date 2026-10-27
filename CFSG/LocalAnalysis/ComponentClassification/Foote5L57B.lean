module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56L

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

theorem dihedral_four_sq_ne_one :
    ∀ d : DihedralGroup 4, d * d ≠ 1 → d = DihedralGroup.r 1 ∨ d = DihedralGroup.r 3 := by
  decide

theorem dihedral_four_center :
    ∀ d : DihedralGroup 4, d ≠ 1 → (∀ d', d * d' = d' * d) → d = DihedralGroup.r 2 := by
  decide

theorem dihedral_four_gen : ∀ d₀ : DihedralGroup 4, d₀ * d₀ = 1 → d₀ ≠ 1 →
    d₀ ≠ DihedralGroup.r 2 →
      ∀ d, ∃ i : Fin 4, ∃ j : Fin 2, d = DihedralGroup.r 1 ^ (i : ℕ) * d₀ ^ (j : ℕ) := by
  decide

variable {G : Type} [Group G] [Finite G]

theorem card_le_four_mul_of_tests {S C : Subgroup G} (hCS : C ≤ S) {a a' b b' : G}
    (ha : ∀ x ∈ S, x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a')
    (hb : ∀ x ∈ S, x * b * x⁻¹ = b ∨ x * b * x⁻¹ = b')
    (hCab : ∀ c ∈ C, c * a * c⁻¹ = a ∧ c * b * c⁻¹ = b)
    (hC : ∀ x ∈ S, x * a * x⁻¹ = a → x * b * x⁻¹ = b → x ∈ C) :
    Nat.card S ≤ 4 * Nat.card C := by
  classical
  set T : Finset (G × G) := {(a, b), (a, b'), (a', b), (a', b')} with hTdef
  have hT : ∀ x : S, ((x : G) * a * (x : G)⁻¹, (x : G) * b * (x : G)⁻¹) ∈ T := by
    intro x
    rcases ha x x.2 with h1 | h1 <;> rcases hb x x.2 with h2 | h2 <;> rw [h1, h2] <;> simp [hTdef]
  set f : S → T := fun x => ⟨((x : G) * a * (x : G)⁻¹, (x : G) * b * (x : G)⁻¹), hT x⟩ with hf
  have hconst : ∀ x y : S, x⁻¹ * y ∈ C.subgroupOf S → f x = f y := by
    intro x y hxy
    rw [mem_subgroupOf] at hxy
    obtain ⟨hca, hcb⟩ := hCab _ hxy
    have hy : (y : G) = x * (((x⁻¹ * y : S)) : G) := by simp
    apply Subtype.ext
    simp only [hf, Prod.mk.injEq]
    constructor
    · rw [hy, show (x : G) * ((x⁻¹ * y : S) : G) * a * ((x : G) * ((x⁻¹ * y : S) : G))⁻¹ =
        (x : G) * (((x⁻¹ * y : S) : G) * a * ((x⁻¹ * y : S) : G)⁻¹) * (x : G)⁻¹ by group, hca]
    · rw [hy, show (x : G) * ((x⁻¹ * y : S) : G) * b * ((x : G) * ((x⁻¹ * y : S) : G))⁻¹ =
        (x : G) * (((x⁻¹ * y : S) : G) * b * ((x⁻¹ * y : S) : G)⁻¹) * (x : G)⁻¹ by group, hcb]
  set F : S ⧸ C.subgroupOf S → T :=
    Quotient.lift f fun x y hxy => hconst x y (QuotientGroup.leftRel_apply.mp hxy) with hF
  have hFinj : Function.Injective F := by
    intro p p' hpp'
    induction p using QuotientGroup.induction_on with | H x => ?_
    induction p' using QuotientGroup.induction_on with | H y => ?_
    have hxy : f x = f y := hpp'
    simp only [hf, Subtype.mk.injEq, Prod.mk.injEq] at hxy
    obtain ⟨hxa, hxb⟩ := hxy
    rw [QuotientGroup.eq, mem_subgroupOf]
    refine hC _ (mul_mem (inv_mem x.2) y.2) ?_ ?_
    · rw [show ((x⁻¹ * y : S) : G) * a * ((x⁻¹ * y : S) : G)⁻¹ =
        (x : G)⁻¹ * ((y : G) * a * (y : G)⁻¹) * x by simp; group, ← hxa]
      group
    · rw [show ((x⁻¹ * y : S) : G) * b * ((x⁻¹ * y : S) : G)⁻¹ =
        (x : G)⁻¹ * ((y : G) * b * (y : G)⁻¹) * x by simp; group, ← hxb]
      group
  have h1 := Nat.card_le_card_of_injective F hFinj
  have h2 : Nat.card T ≤ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_four
  have h3 := card_eq_card_quotient_mul_card_subgroup (C.subgroupOf S)
  rw [Nat.card_congr (subgroupOfEquivOfLe hCS).toEquiv] at h3
  rw [h3]
  exact Nat.mul_le_mul_right _ (h1.trans h2)

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem card_centralizer_R_le (hD : Foote5AutData 𝕊 Lin) :
    Nat.card ↥(S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)) ≤ 4 * Nat.card Q := by
  have hK₀N : S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ≤ normalizer (L : Set G) :=
    inf_le_left.trans h.S_le
  have h1 := card_eq_card_inf_mul_card_actImage ε hK₀N
  have h2 : Nat.card ↥(S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓
      coreActionKernel L) ≤ Nat.card Q := by
    refine card_le_of_le ?_
    rw [← h.inf_coreActionKernel]
    exact inf_le_inf_right _ inf_le_left
  have hfix : ∀ α ∈ actImage L ε (S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G)),
      ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ := by
    intro α hα ρ hρ
    obtain ⟨k, hk, rfl⟩ := (mem_actImage ε hK₀N).mp hα
    exact (h.actG_fix_iff ε (mem_inf.mp hk).1).mpr
      (fun r' hr' => (mem_centralizer_iff.mp (mem_inf.mp hk).2 r' hr').symm) ρ hρ
  have h3 := (hD.centralizer_sylow (h.Rbar ε) _
    (isPGroup_actImage ε (h.isPGroup_S.to_le inf_le_left)) hfix).2
  rw [h1]
  calc _ ≤ Nat.card Q * 4 := Nat.mul_le_mul h2 h3
    _ = 4 * Nat.card Q := mul_comm _ _

theorem dihedral_four_t (e : ↥(S ⊓ L) ≃* DihedralGroup 4) :
    e ⟨t, h.tR⟩ = DihedralGroup.r 2 := by
  refine dihedral_four_center _ (fun h1 => h.t_ne_one ?_) fun d => ?_
  · have h2 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val h2
  · obtain ⟨y, rfl⟩ := e.surjective d
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.tZ _ (mem_inf.mp y.2).1).symm

theorem ne_one_ne_t_of_dihedral_four (e : ↥(S ⊓ L) ≃* DihedralGroup 4) {d : DihedralGroup 4}
    (hd1 : d ≠ 1) (hd2 : d ≠ DihedralGroup.r 2) :
    ((e.symm d : ↥(S ⊓ L)) : G) ≠ 1 ∧ ((e.symm d : ↥(S ⊓ L)) : G) ≠ t := by
  constructor
  · intro h1
    apply hd1
    have h2 : e.symm d = 1 := Subtype.ext h1
    rw [← e.apply_symm_apply d, h2, map_one]
  · intro h1
    apply hd2
    have h2 : e.symm d = ⟨t, h.tR⟩ := Subtype.ext h1
    rw [← e.apply_symm_apply d, h2, h.dihedral_four_t e]

theorem mem_innAut_of_mem_conjugate_Q (hD : Foote5AutData 𝕊 Lin) (hQ4 : Nat.card Q = 4)
    (hQsq : ∀ q ∈ Q, q * q = 1) {s : G} (hsN : s ∈ normalizer (S : Set G))
    (htQs : t ∈ conjugate Q s) (e : ↥(S ⊓ L) ≃* DihedralGroup 4) {v : G}
    (hv : v ∈ conjugate Q s) (hlin : actG L ε v ∈ Lin) : actG L ε v ∈ innAut5 𝕊 := by
  by_contra hinn
  have hvS := h.conjugate_Q_le hsN hv
  have hv2 : v * v = 1 := conjugate_sq_eq_one hQsq hv
  have hvR : v ∉ S ⊓ L := fun h1 => hinn (by
    rw [actG_of_mem_self ε (mem_inf.mp h1).2]
    exact ⟨_, rfl⟩)
  have hQs4 : Nat.card (conjugate Q s) = 4 := by rw [card_conjugate_eq_card, hQ4]
  have hQssq : ∀ c ∈ conjugate Q s, c * c = 1 := fun c hc => conjugate_sq_eq_one hQsq hc
  have hcomm : ∀ r ∈ S ⊓ L, v * r * v⁻¹ * r⁻¹ = 1 ∨ v * r * v⁻¹ * r⁻¹ = t := by
    intro r hr
    have hcQ : v * r * v⁻¹ * r⁻¹ ∈ conjugate Q s := by
      rw [show v * r * v⁻¹ * r⁻¹ = v * (r * v⁻¹ * r⁻¹) by group]
      exact mul_mem hv (h.conj_mem_conjugate_Q hsN (mem_inf.mp hr).1 (inv_mem hv))
    have hcR : v * r * v⁻¹ * r⁻¹ ∈ S ⊓ L := mul_mem (h.conj_mem_R hvS hr) (inv_mem hr)
    by_contra hne
    push Not at hne
    rcases eq_of_mem_four hQs4 hQssq htQs hcQ h.t_ne_one hne.1 (Ne.symm hne.2) hv with
      h1 | h1 | h1 | h1 <;> apply hvR <;> rw [h1]
    · exact mul_mem h.tR hcR
    · exact h.tR
    · exact hcR
    · exact one_mem _
  have hnc : ∀ r ∈ S ⊓ L, r * v = v * r → r = 1 ∨ r = t :=
    fun r hr hrv => h.eq_one_or_eq_t_of_pgl ε hD hvS hv2 hlin hinn hr hrv
  have hcomm' : ∀ r ∈ S ⊓ L, v * r * v⁻¹ * r⁻¹ = 1 → r * v = v * r := by
    intro r hr h1
    calc r * v = v * r * v⁻¹ * r⁻¹ * (r * v) := by rw [h1, one_mul]
      _ = v * r := by group
  set ρ : G := ((e.symm (DihedralGroup.r 1) : ↥(S ⊓ L)) : G) with hρ
  set b : G := ((e.symm (DihedralGroup.sr 0) : ↥(S ⊓ L)) : G) with hb
  have hρR : ρ ∈ S ⊓ L := (e.symm _).2
  have hbR : b ∈ S ⊓ L := (e.symm _).2
  have hρb : ρ * b = ((e.symm (DihedralGroup.r 1 * DihedralGroup.sr 0) : ↥(S ⊓ L)) : G) := by
    rw [map_mul]
    rfl
  have hρ1 := h.ne_one_ne_t_of_dihedral_four e (d := DihedralGroup.r 1) (by decide) (by decide)
  have hb1 := h.ne_one_ne_t_of_dihedral_four e (d := DihedralGroup.sr 0) (by decide) (by decide)
  have hρb1 := h.ne_one_ne_t_of_dihedral_four e (d := DihedralGroup.r 1 * DihedralGroup.sr 0)
    (by decide) (by decide)
  rw [← hρ] at hρ1
  rw [← hb] at hb1
  rw [← hρb] at hρb1
  have hfail : ∀ r ∈ S ⊓ L, r ≠ 1 → r ≠ t → v * r * v⁻¹ * r⁻¹ = t := by
    intro r hr hr1 hrt
    rcases hcomm r hr with h1 | h1
    · rcases hnc r hr (hcomm' r hr h1) with h2 | h2
      · exact absurd h2 hr1
      · exact absurd h2 hrt
    · exact h1
  have h1 := hfail ρ hρR hρ1.1 hρ1.2
  have h2 := hfail b hbR hb1.1 hb1.2
  have h3 := hfail (ρ * b) (mul_mem hρR hbR) hρb1.1 hρb1.2
  have htρ : t * ρ = ρ * t := h.tZ ρ (mem_inf.mp hρR).1 |>.symm
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  apply h.t_ne_one
  calc t = v * (ρ * b) * v⁻¹ * (ρ * b)⁻¹ := h3.symm
    _ = (v * ρ * v⁻¹ * ρ⁻¹) * ρ * (v * b * v⁻¹ * b⁻¹) * ρ⁻¹ := by group
    _ = t * ρ * t * ρ⁻¹ := by rw [h1, h2]
    _ = ρ * (t * t) * ρ⁻¹ := by rw [htρ]; group
    _ = 1 := by rw [ht22, mul_one, mul_inv_cancel]

end Sec5

end CFSG.ComponentClassification.Foote5
