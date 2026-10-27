module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD3Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ResidueDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ElimFacts
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Fix
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open
open scoped MatrixGroups

theorem lt_card_psl_four_four : 40320 < Nat.card PSL(4, GaloisField 2 2) := by
  let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) = 987033600 := by
    rw [Matrix.card_SL_field, hq]
    simp only [Fin.prod_univ_four]
    norm_num
  have hZ : Nat.card (center (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2))) ≤ 4 := by
    rw [Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 4)).toEquiv,
      Fintype.card_fin]
    exact card_rootsOfUnity (GaloisField 2 2) 4
  have h := card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)))
  rw [hSL] at h
  by_contra hle
  have hle' : Nat.card PSL(4, GaloisField 2 2) ≤ 40320 := by omega
  have := Nat.mul_le_mul hle' hZ
  change 987033600 = Nat.card PSL(4, GaloisField 2 2) * _ at h
  omega

theorem not_hasElemAbThree81_of_layer_L44 (hAut : AtlasL44Aut) (hRank : AtlasL44ThreeRank)
    (hFix : AtlasL44FixedPoints) {X : Type} [Group X] [Finite X] {z : X} {H : Subgroup X}
    (hz : orderOf z = 2) (hH : Nonempty (H ≃* alternatingGroup (Fin 8)))
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X))
    (hE : Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* PSL(4, GaloisField 2 2))) :
    ¬ HasElemAbThree81 (X ⧸ fusionOddCore X) := by
  rintro ⟨S, hS81, hScomm, hS3⟩
  obtain ⟨e⟩ := hE
  obtain ⟨eA⟩ := hH
  obtain ⟨hs, hnab⟩ := isSimpleGroup_and_not_comm_of_mulEquiv_alt8 eA
  obtain ⟨-, -, hHcard, ho, ht', hC'⟩ := quotient_facts_of_centralizer_eq hnab hz hC hz'
  have hO : fusionOddCore (X ⧸ fusionOddCore X) = ⊥ :=
    standardComponentOddCore_quotient_fusionOddCore_eq_bot X
  have hHcard' : Nat.card (H.map (QuotientGroup.mk' (fusionOddCore X))) = 20160 := by
    rw [hHcard, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have ht : QuotientGroup.mk' (fusionOddCore X) z ^ 2 = 1 := by rw [← ho, pow_orderOf_eq_one]
  have hEbig : 40320 < Nat.card (egaLayer (X ⧸ fusionOddCore X)) := by
    rw [Nat.card_congr e.toEquiv]
    exact lt_card_psl_four_four
  have hCcard : Nat.card (centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
      Set (X ⧸ fusionOddCore X))) ≤ 40320 := by
    rw [hC']
    calc Nat.card (H.map (QuotientGroup.mk' (fusionOddCore X)) ⊔
          zpowers (QuotientGroup.mk' (fusionOddCore X) z) : Subgroup _)
        ≤ Nat.card (H.map (QuotientGroup.mk' (fusionOddCore X))) *
            Nat.card (zpowers (QuotientGroup.mk' (fusionOddCore X) z)) :=
          card_sup_zpowers_le (centralizer_le_normalizer _ ht')
      _ = 40320 := by rw [hHcard', Nat.card_zpowers, ho]
  have hnot : ¬ egaLayer (X ⧸ fusionOddCore X) ≤
      centralizer ({QuotientGroup.mk' (fusionOddCore X) z} : Set (X ⧸ fusionOddCore X)) :=
    fun hle => absurd ((card_le_of_le hle).trans hCcard) (by omega)
  have htQ : QuotientGroup.mk' (fusionOddCore X) z ∉
      centralizer (egaLayer (X ⧸ fusionOddCore X) : Set (X ⧸ fusionOddCore X)) := fun h =>
    hnot fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h x hx)
  obtain ⟨f, hf, hfix, -⟩ := exists_mulAut_of_normal e ht
  have hf1 : f ≠ 1 := by
    rintro rfl
    apply hnot
    have h2 : Nat.card {g : PSL(4, GaloisField 2 2) // (1 : MulAut PSL(4, GaloisField 2 2)) g = g} =
        Nat.card PSL(4, GaloisField 2 2) := Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)
    rw [h2, ← Nat.card_congr e.toEquiv] at hfix
    rw [← eq_of_le_of_card_ge inf_le_left hfix.le]
    exact inf_le_right
  have h3 := hFix _ ⟨MulEquiv.refl _⟩ f hf hf1
  rw [hfix] at h3
  have hHE := map_le_of_two_lt_card_inf_centralizer hnab hz hC hz' (egaLayer_normal _)
    (by omega)
  have hCQ := centralizer_inf_centralizer_mk_le_zpowers hnab hz hC hz' hHE
  have hQbot : centralizer (egaLayer (X ⧸ fusionOddCore X) : Set (X ⧸ fusionOddCore X)) = ⊥ := by
    have hle := normal_le_fusionOddCore_of_fixedPointFree
      (centralizer (egaLayer (X ⧸ fusionOddCore X) : Set (X ⧸ fusionOddCore X)))
      (QuotientGroup.mk' (fusionOddCore X) z) (by rw [← sq, ht]) fun s hs hst => by
        rcases eq_one_or_eq_of_mem_zpowers ho
          (hCQ (mem_inf.2 ⟨hs, mem_centralizer_singleton_iff.2 hst.symm⟩)) with h | h
        · exact h
        · exact absurd (h ▸ hs) htQ
    rwa [hO, le_bot_iff] at hle
  have hinj : Function.Injective (MulAut.conjNormal (G := X ⧸ fusionOddCore X)
      (H := egaLayer (X ⧸ fusionOddCore X))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgC : g ∈ centralizer (egaLayer (X ⧸ fusionOddCore X) : Set (X ⧸ fusionOddCore X)) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 : g * x * g⁻¹ = x := by
        have h0 := congrArg Subtype.val (DFunLike.congr_fun hg ⟨x, hx⟩)
        simpa [MulAut.conjNormal_apply] using h0
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hQbot, mem_bot] at hgC
    exact hgC
  have hdvd : Nat.card (X ⧸ fusionOddCore X) ∣
      4 * Nat.card (egaLayer (X ⧸ fusionOddCore X)) := by
    rw [← hAut _ ⟨e⟩]
    exact card_dvd_of_injective _ hinj
  have hq : Nat.card ((X ⧸ fusionOddCore X) ⧸ egaLayer (X ⧸ fusionOddCore X)) ∣ 4 := by
    rw [card_eq_card_quotient_mul_card_subgroup (egaLayer (X ⧸ fusionOddCore X))] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hdvd
  have hSE : S ≤ egaLayer (X ⧸ fusionOddCore X) := by
    have h1 : Nat.card (S.map (QuotientGroup.mk' (egaLayer (X ⧸ fusionOddCore X)))) ∣ 81 :=
      hS81 ▸ card_map_dvd S _
    have h2 : Nat.card (S.map (QuotientGroup.mk' (egaLayer (X ⧸ fusionOddCore X)))) ∣ 4 :=
      (card_subgroup_dvd_card _).trans hq
    have h4 := Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 81 4) h1 h2
    rwa [card_eq_one, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h4
  have h27 := hRank _ ⟨e⟩ (S.subgroupOf (egaLayer (X ⧸ fusionOddCore X)))
    (fun s hs u hu => Subtype.ext (hScomm _ hs _ hu))
    (fun s hs => Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hS3 _ hs))
  rw [Nat.card_congr (subgroupOfEquivOfLe hSE).toEquiv, hS81] at h27
  omega

end CFSG.EvenSporadicStandard.M24Std
