module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Transport
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Tools2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51C
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51B

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

theorem dihedral_conj_eq_mul {m : ℕ} (hm : 2 ≤ m) {d : DihedralGroup (2 ^ m)} (hd : d * d = 1)
    (hdc : d ∉ center (DihedralGroup (2 ^ m))) :
    d * DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) * d⁻¹ =
      DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) *
        DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases d with i | i
  · exfalso
    apply hdc
    have h2 : i + i = 0 := by
      rw [DihedralGroup.r_mul_r, DihedralGroup.one_def] at hd
      exact DihedralGroup.r.inj hd
    rw [mem_center_iff]
    intro g
    rcases g with j | j
    · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
      exact congrArg _ (add_comm j i)
    · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
      congr 1
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left h2]
  · rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_r]
    congr 1
    have h1 : ((2 ^ (n + 2 - 2) : ℕ) : ZMod (2 ^ (n + 2))) + ((2 ^ (n + 2 - 2) : ℕ) : ZMod _) +
        ((2 ^ (n + 2 - 1) : ℕ) : ZMod _) = 0 := by
      rw [← Nat.cast_add, ← Nat.cast_add, show n + 2 - 2 = n by omega,
        show n + 2 - 1 = n + 1 by omega,
        show 2 ^ n + 2 ^ n + 2 ^ (n + 1) = 2 ^ (n + 2) by ring, ZMod.natCast_self]
    rw [show i - (i + ((2 ^ (n + 2 - 2) : ℕ) : ZMod (2 ^ (n + 2)))) =
      -((2 ^ (n + 2 - 2) : ℕ) : ZMod (2 ^ (n + 2))) by ring]
    rw [neg_eq_iff_add_eq_zero, ← add_assoc]
    exact h1

variable {G : Type} [Group G] [Finite G]

theorem three_le_card_of_ne {X : Type*} [Group X] [Finite X] {K : Subgroup X} {a b : X} (ha : a ∈ K)
    (hb : b ∈ K) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : 3 ≤ Nat.card K := by
  classical
  set F : Finset X := {1, a, b} with hF
  have hFc : F.card = 3 := Finset.card_eq_three.mpr ⟨1, a, b, ha1.symm, hb1.symm, hab, rfl⟩
  have hmem : ∀ x ∈ F, x ∈ K := by
    intro x hx
    rw [hF, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact one_mem K
    · exact ha
    · exact hb
  have h1 := Nat.card_le_card_of_injective (fun x : F => (⟨x, hmem x x.2⟩ : K))
    fun x y hxy => Subtype.ext (by simpa using hxy)
  rwa [Nat.card_eq_finsetCard, hFc] at h1

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

omit [Finite 𝕊] in
theorem card_Rbar : Nat.card (h.Rbar ε : Subgroup 𝕊) = Nat.card ↥(S ⊓ L) := by
  set K := (S ⊓ L).subgroupOf L with hK
  have hinj : Function.Injective ((psi L ε).comp K.subtype) := by
    intro a b hab
    have h1 := h.eq_of_psi_eq ε (mem_subgroupOf.mp a.2) (mem_subgroupOf.mp b.2) hab
    exact Subtype.ext (Subtype.ext h1)
  have hrange : ((psi L ε).comp K.subtype).range = K.map (psi L ε) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [coe_sylowImage, ← hK, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv

theorem four_le_card_R : 4 ≤ Nat.card ↥(S ⊓ L) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := h.exists_dihedral_R
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right two_pos hm
  omega

end Sec5

end CFSG.ComponentClassification.Foote5
