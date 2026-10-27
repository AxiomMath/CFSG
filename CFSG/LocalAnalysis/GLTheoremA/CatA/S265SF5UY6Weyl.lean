module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE8
import CFSG.LocalAnalysis.StandardType.GGTableBExcSylowE8Five
import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UY6Nil

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.NoOffRest Module

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "𝕍" => Fin Tag.E8.rank → ZMod 5

local instance y6FactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance y6NeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

private theorem torusLin_mul_E8 (a b : WeylGroup .E8) :
    torusLin .E8 5 (a * b) = torusLin .E8 5 a * torusLin .E8 5 b := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, torusLin_apply, torusLin_apply, torusLin_apply,
    TableBExc.torusAct_mul]

private theorem torusLin_one_E8 : torusLin .E8 5 (1 : WeylGroup .E8) = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [torusLin_apply, TableBExc.torusAct_one]
  rfl

private theorem torusLin_pow_E8 (u : WeylGroup .E8) (n : ℕ) :
    torusLin .E8 5 (u ^ n) = torusLin .E8 5 u ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, torusLin_one_E8]
  | succ n ih => rw [pow_succ, pow_succ, torusLin_mul_E8, ih]

private theorem sub_one_cube_ne_AB : ∀ c : Fin 5,
    ((fun x => TableBExc.torusWord .E8 5 (TableBExc.wordE8AB c) x - x)^[3] (Pi.single 4 1) :
      Fin Tag.E8.rank → ZMod 5) ≠ 0 := by
  decide +kernel

private theorem sub_one_cube_ne_B :
    ((fun x => TableBExc.torusWord .E8 5 TableBExc.wordE8B x - x)^[3] (Pi.single 4 1) :
      Fin Tag.E8.rank → ZMod 5) ≠ 0 := by
  decide +kernel

private theorem torusLin_wordProd
    (ω : List (Fin Tag.E8.rank)) (x : Fin Tag.E8.rank → ZMod 5) :
    torusLin .E8 5 ((coxeterSystem .E8).wordProd ω) x = TableBExc.torusWord .E8 5 ω x := by
  rw [torusLin_apply, TableBExc.torusWord_eq_torusAct TableBExc.Three.cartan_symm_E8]

private theorem sub_one_cube_ne_rep
    {r : WeylGroup .E8}
    (hr : r = TableBExc.weylE8B ∨
      ∃ c : ℕ, c < 5 ∧ r = TableBExc.weylE8A * TableBExc.weylE8B ^ c) :
    ((torusLin .E8 5 r - (1 : Module.End (ZMod 5) 𝕍)) ^ 3) (Pi.single 4 1) ≠ 0 := by
  have key : ∀ ω : List (Fin Tag.E8.rank),
      ((torusLin .E8 5 ((coxeterSystem .E8).wordProd ω) - (1 : Module.End (ZMod 5) 𝕍)) ^ 3)
          (Pi.single 4 1) =
        (fun x => TableBExc.torusWord .E8 5 ω x - x)^[3] (Pi.single 4 1) := fun ω => by
    rw [sub_one_pow_apply]
    congr 1
    funext y
    rw [torusLin_wordProd]
  rcases hr with hr | ⟨c, hc, hr⟩
  · rw [hr]
    intro h
    refine sub_one_cube_ne_B ?_
    rw [← key TableBExc.wordE8B]
    exact h
  · rw [hr, ← TableBExc.wordProd_wordE8AB]
    intro h
    refine sub_one_cube_ne_AB ⟨c, hc⟩ ?_
    rw [← key]
    exact h

theorem finrank_eig_fix_le_one
    {lam : ZMod 5} (hlam : lam * lam = -1) {u : WeylGroup .E8}
    (hu : u ∈ centE8W) (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1) :
    finrank (ZMod 5) ↥(eigE8 5 lam ⊓ fixSp (torusLin .E8 5 u)) ≤ 1 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hcomm := mul_comm_of_mem_centE8W hu
  have hlam' : (-lam) * (-lam) = -1 := by rw [neg_mul_neg]; exact hlam
  have hdual := dualHyp_E8 hp2 hcomm hlam
  set U := torusLin .E8 5 u with hUdef
  set N : Module.End (ZMod 5) 𝕍 := U - LinearMap.id with hNdef
  have hU5 : U ^ 5 = 1 := by rw [hUdef, ← torusLin_pow_E8, hu5, torusLin_one_E8]
  have hN5 : N ^ 5 = 0 := by
    haveI : CharP (Module.End (ZMod 5) 𝕍) 5 :=
      charP_of_injective_algebraMap (algebraMap (ZMod 5) (Module.End (ZMod 5) 𝕍)).injective 5
    have h1 : (U - (1 : Module.End (ZMod 5) 𝕍)) ^ 5 = U ^ 5 - 1 ^ 5 :=
      sub_pow_char_of_commute 5 (Commute.one_right U)
    rw [hU5, one_pow, sub_self] at h1
    exact h1
  have hstab : ∀ c : ZMod 5, ∀ x ∈ eigE8 5 c, N x ∈ eigE8 5 c := fun c x hx =>
    Submodule.sub_mem _ (torusAct_mem_eigE8 hu hx) hx
  have hk1 : 2 ≤ finrank (ZMod 5) ↥(eigE8 5 lam ⊓ LinearMap.ker N) := hcon
  have hk2 : 2 ≤ finrank (ZMod 5) ↥(eigE8 5 (-lam) ⊓ LinearMap.ker N) := by
    have := hdual.finrank_eig_fix_eq
    change finrank (ZMod 5) ↥(eigE8 5 lam ⊓ fixSp U) =
      finrank (ZMod 5) ↥(eigE8 5 (-lam) ⊓ fixSp U) at this
    change 1 < finrank (ZMod 5) ↥(eigE8 5 lam ⊓ fixSp U) at hcon
    change 2 ≤ finrank (ZMod 5) ↥(eigE8 5 (-lam) ⊓ fixSp U)
    omega
  have hN3 : N ^ 3 = 0 := by
    refine LinearMap.ext fun x => ?_
    have hsup : eigE8 5 lam ⊔ eigE8 5 (-lam) = ⊤ :=
      eig_sup_eq_top hdual.sq hlam (two_ne_zero_zmod hp2)
    have hx : x ∈ eigE8 5 lam ⊔ eigE8 5 (-lam) := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, pow_three_apply_eq_zero hN5 (hstab lam) (finrank_eigE8 hp2 hlam) hk1 a ha,
      pow_three_apply_eq_zero hN5 (hstab (-lam)) (finrank_eigE8 hp2 hlam') hk2 b hb, add_zero]
    rfl
  have hidx : ¬ 5 ∣ TableBExc.weylE8S.index := by
    rw [NoOffExc.index_eq_of_card TableBExc.card_weylE8S NoOffExc.card_weyl_E8
      (show 25 * 27869184 = 696729600 by norm_num) (by norm_num)]
    norm_num
  have hpg : IsPGroup 5 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hu5 hu1]; simp)
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_five hidx hpg
  have hgmem : g * u * g⁻¹ ∈ TableBExc.weylE8S := hg ⟨u, Subgroup.mem_zpowers u, rfl⟩
  have hne : g * u * g⁻¹ ≠ 1 := fun h => hu1 (by
    have h1 : u = g⁻¹ * (g * u * g⁻¹) * g := by group
    rw [h1, h]
    group)
  obtain ⟨k, hk⟩ := TableBExc.exists_pow_eq_rep hgmem hne
  have hGG' : torusLin .E8 5 g * torusLin .E8 5 g⁻¹ = 1 := by
    rw [← torusLin_mul_E8, mul_inv_cancel, torusLin_one_E8]
  have hG'G : torusLin .E8 5 g⁻¹ * torusLin .E8 5 g = 1 := by
    rw [← torusLin_mul_E8, inv_mul_cancel, torusLin_one_E8]
  have hM1 : (torusLin .E8 5 (g * u * g⁻¹) - (1 : Module.End (ZMod 5) 𝕍)) ^ 3 = 0 := by
    have e : torusLin .E8 5 (g * u * g⁻¹) - (1 : Module.End (ZMod 5) 𝕍) =
        torusLin .E8 5 g * N * torusLin .E8 5 g⁻¹ := by
      rw [torusLin_mul_E8, torusLin_mul_E8, hNdef, ← hUdef, Module.End.one_eq_id.symm, mul_sub,
        sub_mul, mul_one, hGG']
    rw [e]
    exact (Units.conj_pow (Units.mk _ _ hGG' hG'G) N 3).trans (by rw [hN3, mul_zero, zero_mul])
  have hMk : (torusLin .E8 5 ((g * u * g⁻¹) ^ k) - (1 : Module.End (ZMod 5) 𝕍)) ^ 3 = 0 := by
    rw [torusLin_pow_E8]
    set M := torusLin .E8 5 (g * u * g⁻¹)
    have e : M ^ k - (1 : Module.End (ZMod 5) 𝕍) = (∑ i ∈ Finset.range k, M ^ i) * (M - 1) :=
      (geom_sum_mul M k).symm
    have hc : Commute (∑ i ∈ Finset.range k, M ^ i) (M - 1) :=
      Commute.sum_left _ _ _ fun i _ =>
        ((Commute.refl M).pow_left i).sub_right (Commute.one_right _)
    rw [e, hc.mul_pow, hM1, mul_zero]
  exact sub_one_cube_ne_rep hk (by rw [hMk]; rfl)

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
