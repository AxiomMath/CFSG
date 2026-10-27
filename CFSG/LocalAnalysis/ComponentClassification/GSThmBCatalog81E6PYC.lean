module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PYT
public import CFSG.Sporadic.SmallOddCore.McLAut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXC

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211Y

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer P211 P211X
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier

theorem mcl_involution_square
    {t : mclP}
    (ht : orderOf t = 2) : ∃ y : mclP, y * y = t := by
  have hwmem : mclGen 0 * mclGen 1 ^ 2 ∈ mclP :=
    mclP.mul_mem (mclGen_mem_P 0 (by norm_num)) (mclP.pow_mem (mclGen_mem_P 1 (by norm_num)) 2)
  set w : mclP := ⟨_, hwmem⟩ with hwdef
  have hw : orderOf w = 12 := by
    rw [hwdef, Subgroup.orderOf_mk]
    exact mcl_word_orders'.1
  have hw6 : orderOf (w ^ 6) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hw]; norm_num), hw]
  obtain ⟨c, hc⟩ := mcl_involution_conj_a hw6
  obtain ⟨d, hd⟩ := mcl_involution_conj_a ht
  refine ⟨(d * c⁻¹) * w ^ 3 * (d * c⁻¹)⁻¹, ?_⟩
  have h6 : w ^ 3 * w ^ 3 = c * mcla0 * c⁻¹ := by
    rw [← pow_add]
    exact hc
  calc (d * c⁻¹) * w ^ 3 * (d * c⁻¹)⁻¹ * ((d * c⁻¹) * w ^ 3 * (d * c⁻¹)⁻¹)
      = (d * c⁻¹) * (w ^ 3 * w ^ 3) * (d * c⁻¹)⁻¹ := by group
    _ = t := by
      rw [h6, hd]
      group

theorem p211For_McL :
    P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .McL := by
  intro X _ _ hsimp hC ⟨e⟩ p f hp hp2 hf a J D _ _ _ _ hJt hJF hDJ hDsyl hbound b K hb hb1
    hKC hK hKt
  exfalso
  have : (generalizedFitting X).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := X)).2
  have hKF := le_fstar_of_solvable hC (outer_solvable_of_equiv e AT_McL_Schreier.2) hKC hK
  have hKcard := le_card_of_socle hp hp2 hf hKt
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb) hb1
  have hbK := not_mem_of_center_socle hbo hKC (center_socle_eq_bot hp hp2 hf hKt)
  have hle : Nat.card K ≤ Nat.card ↥(generalizedFitting X ⊓ centralizer ({b} : Set X)) :=
    card_le_of_le (le_inf hKF hKC)
  set θ : ↥(generalizedFitting X) ≃* mclP := e.trans mclPermEquiv with hθ
  have hinj := mcl_autModel.embed_injective (generalizedFitting X) θ hC
  have hcardC : Nat.card ↥(generalizedFitting X ⊓ centralizer ({b} : Set X)) =
      Nat.card ↥(mclP ⊓ centralizer ({mcl_autModel.embed (generalizedFitting X) θ b} :
        Set (Equiv.Perm (Fin 275)))) :=
    Nat.card_congr (mcl_autModel.centralizerEquiv (generalizedFitting X) θ hC b).toEquiv
  have hιb : orderOf (mcl_autModel.embed (generalizedFitting X) θ b) = 2 := by
    rw [orderOf_injective _ hinj, hbo]
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ := mcl_involution_centralizers
  obtain ⟨r, hr, g, hg, hrg⟩ :=
    hcover _ (mcl_autModel.embed_mem (generalizedFitting X) θ b) hιb
  have hcr : Nat.card ↥(mclP ⊓ centralizer ({mcl_autModel.embed (generalizedFitting X) θ b} :
      Set (Equiv.Perm (Fin 275)))) = r.centOrder := by
    rw [hrg, inf_centralizer_conj mclP hg, card_map_of_injective (MulAut.conj g).injective,
      (hrows r hr).2.2.2.2.1]
  have hm := List.mem_map_of_mem (f := fun r : ClassRow => (r.outer, r.classSize, r.centOrder))
    hr
  rw [hmap] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨hout, -, h40⟩ | ⟨-, -, h79⟩
  ·
    have hrP : tp 275 r.rep ∈ mclP := by
      by_contra hn
      have h1 := ((hrows r hr).2.2.1).mpr hn
      rw [hout] at h1
      exact absurd h1 (by decide)
    have hιbP : mcl_autModel.embed (generalizedFitting X) θ b ∈ mclP := by
      rw [hrg]
      exact mclP.mul_mem (mclP.mul_mem hg hrP) (mclP.inv_mem hg)
    obtain ⟨s, hs⟩ := θ.surjective ⟨_, hιbP⟩
    have hsb : (s : X) = b := hinj (by
      rw [mcl_autModel.embed_coe (generalizedFitting X) θ s, hs])
    have hso : orderOf (θ s) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, hsb, hbo]
    obtain ⟨y, hy⟩ := mcl_involution_square hso
    set g' : X := ((θ.symm y : ↥(generalizedFitting X)) : X) with hg'
    have hgg : g' * g' = b := by
      rw [hg', ← Subgroup.coe_mul, ← map_mul, hy, MulEquiv.symm_apply_apply, hsb]
    have hg'C : g' ∈ generalizedFitting X ⊓ centralizer ({b} : Set X) := by
      refine mem_inf.mpr ⟨(θ.symm y).2, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← hgg, mul_assoc]
    have hsq := sq_mem_of_card_le_two_mul (le_inf hKF hKC) (by omega) hg'C
    rw [hgg] at hsq
    exact hbK hsq
  ·
    omega

end P211Y

end CFSG.ComponentClassification.GSThmB
