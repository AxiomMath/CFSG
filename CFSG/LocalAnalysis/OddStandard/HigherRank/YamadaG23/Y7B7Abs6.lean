module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isElemAbelian_top_of_sq_eq_one (Q : Type*) [Group Q] [Finite Q]
    (h : ∀ q : Q, q ^ 2 = 1) : IsElemAbelian 2 (⊤ : Subgroup Q) := by
  have hinv : ∀ a : Q, a⁻¹ = a := fun a =>
    (inv_eq_iff_mul_eq_one).mpr (by simpa [pow_two] using h a)
  have hcomm : ∀ a b : Q, a * b = b * a := fun a b => by
    have hab : a * b = (a * b)⁻¹ :=
      (mul_eq_one_iff_eq_inv).mp (by simpa [pow_two] using h (a * b))
    calc a * b = (a * b)⁻¹ := hab
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv b, hinv a]
  exact ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a b),
    fun x _ => h x⟩

theorem y7b_secProp_of_sq_mem {V N : Subgroup G} (hNV : N ≤ V)
    (hnorm : ∀ v ∈ V, ∀ n ∈ N, v * n * v⁻¹ ∈ N) (hsq : ∀ v ∈ V, v ^ 2 ∈ N) :
    SecProp V N (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y)) := by
  have hN : (N.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff hNV).mpr fun h k hh hk => hnorm k hk h hh
  refine ⟨hN, ?_⟩
  haveI : (N.subgroupOf V).Normal := hN
  apply isElemAbelian_top_of_sq_eq_one
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf V) q
  have hx : x ^ 2 ∈ N.subgroupOf V := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hsq x x.2
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (x ^ 2)).mpr hx

theorem y7b_quotEquiv_sup {B M F : Subgroup G} (hBM : B ≤ normalizer (M : Set G))
    (hF : B ⊓ M = F) [(F.subgroupOf B).Normal] [(M.subgroupOf (B ⊔ M)).Normal] :
    ∃ ι : ↥B ⧸ F.subgroupOf B ≃* ↥(B ⊔ M) ⧸ M.subgroupOf (B ⊔ M),
      ∀ b : ↥B, ι (QuotientGroup.mk b) =
        QuotientGroup.mk (⟨(b : G), Subgroup.mem_sup_left b.2⟩ : ↥(B ⊔ M)) := by
  let ψ : ↥B →* ↥(B ⊔ M) ⧸ M.subgroupOf (B ⊔ M) :=
    (QuotientGroup.mk' (M.subgroupOf (B ⊔ M))).comp (Subgroup.inclusion le_sup_left)
  have hker : ψ.ker = F.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hF, Subgroup.mem_inf]
    constructor
    · intro h
      have h' : (Subgroup.inclusion le_sup_left b : ↥(B ⊔ M)) ∈ M.subgroupOf (B ⊔ M) :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion le_sup_left b)).mp h
      exact ⟨b.2, by simpa [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] using h'⟩
    · rintro ⟨-, h'⟩
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion le_sup_left b)).mpr
        (by simpa [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] using h')
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf (B ⊔ M)) q
    have hx : (x : G) ∈ (B : Set G) * (M : Set G) := by
      have hx' : (x : G) ∈ (↑(B ⊔ M) : Set G) := x.2
      rwa [Subgroup.coe_mul_of_left_le_normalizer_right B M hBM] at hx'
    obtain ⟨b, hb, m, hm, hbm⟩ := Set.mem_mul.mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    have hx_eq : (⟨(b : G) * (m : G), (B ⊔ M).mul_mem (Subgroup.mem_sup_left hb)
        (Subgroup.mem_sup_right hm)⟩ : ↥(B ⊔ M)) = x := Subtype.ext hbm
    rw [← hx_eq]
    change QuotientGroup.mk' (M.subgroupOf (B ⊔ M)) (Subgroup.inclusion le_sup_left ⟨b, hb⟩) =
      QuotientGroup.mk' (M.subgroupOf (B ⊔ M)) ⟨(b : G) * (m : G),
        (B ⊔ M).mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hm)⟩
    rw [QuotientGroup.mk'_eq_mk']
    exact ⟨⟨m, Subgroup.mem_sup_right hm⟩, hm, Subtype.ext rfl⟩
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj), ?_⟩
  intro b
  rw [MulEquiv.trans_apply, ← QuotientGroup.quotientMulEquivOfEq_mk hker b,
    MulEquiv.symm_apply_apply]
  rfl

end CFSG.OddStandard.HigherRank.YamadaG23
