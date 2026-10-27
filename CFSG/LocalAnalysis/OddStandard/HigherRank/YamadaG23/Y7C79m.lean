module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79d
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79i
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79k

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma conjSub_eq_bot_iff {t : G} {Y : Subgroup G} : conjSub t Y = ⊥ ↔ Y = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective Y (MulAut.conj t).injective

private lemma map_subgroupOf_equivMapOfInjective (E N : Subgroup G) (f : G →* G)
    (hf : Function.Injective f) :
    (N.subgroupOf E).map (Subgroup.equivMapOfInjective E f hf) =
      (N.map f).subgroupOf (E.map f) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : G), hy, (Subgroup.coe_equivMapOfInjective_apply E f hf y).symm⟩
  · rintro ⟨n, hn, hfn⟩
    have hnE : n ∈ E := by
      rw [← Subgroup.comap_map_eq_self_of_injective hf E, Subgroup.mem_comap, hfn]
      exact x.2
    refine ⟨⟨n, hnE⟩, ?_, ?_⟩
    · exact hn
    · apply Subtype.ext
      exact (Subgroup.coe_equivMapOfInjective_apply E f hf ⟨n, hnE⟩).trans hfn

theorem y7c_isGL3Ext_conjSub {E N : Subgroup G} {t : G} (h : IsGL3Ext E N)
    (hN : conjSub t N = N) : IsGL3Ext (conjSub t E) N := by
  unfold IsGL3Ext SecProp at h ⊢
  obtain ⟨hNE, hNnorm, ⟨e0⟩⟩ := h
  haveI : (N.subgroupOf E).Normal := hNnorm
  have hEnorm : E ≤ normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).mp hNnorm
  let f : G →* G := (MulAut.conj t).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj t).injective
  have hNf : N.map f = N := hN
  have hNle : N ≤ conjSub t E := by
    rw [← hN]
    exact Subgroup.map_mono hNE
  have hKnorm : conjSub t E ≤ normalizer (N : Set G) := by
    calc conjSub t E ≤ (normalizer (N : Set G)).map f := Subgroup.map_mono hEnorm
      _ ≤ normalizer ((N.map f : Subgroup G) : Set G) :=
          Subgroup.le_normalizer_map (H := N) f
      _ = normalizer (N : Set G) := by rw [hNf]
  have hnorm : (N.subgroupOf (conjSub t E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hKnorm
  refine ⟨hNle, hnorm, ?_⟩
  let e := Subgroup.equivMapOfInjective E f hf
  have hsub : (N.subgroupOf E).map e = (N.map f).subgroupOf (E.map f) :=
    map_subgroupOf_equivMapOfInjective E N f hf
  have hsub' : (N.subgroupOf E).map e = N.subgroupOf (E.map f) := by
    rw [hNf] at hsub
    exact hsub
  haveI : (N.subgroupOf (E.map f)).Normal := hnorm
  exact ⟨(QuotientGroup.congr (N.subgroupOf E) (N.subgroupOf (E.map f)) e hsub').symm.trans e0⟩

theorem y7c_79_main {M L1 P V J : Subgroup G} {t : G}
    (hM2 : IsElemAbelian 2 M) (hMc : Nat.card M = 2 ^ 6) (ht2 : t ^ 2 = 1)
    (htM : conjSub t M = M) (hext1 : IsGL3Ext L1 M) (hinf : L1 ⊓ conjSub t L1 = M)
    (hcomm : ⁅L1, conjSub t L1⁆ ≤ M) (hP : IsSylowIn 2 (L1 ⊔ conjSub t L1) P)
    (hV : V ≤ M) (hVc : Nat.card V = 4) (hVP : ∀ v ∈ V, ∀ x ∈ P, v * x = x * v)
    (hJK : J ≤ L1 ⊔ conjSub t L1) (hJt : ∀ j ∈ J, j * t = t * j) (hJc : Nat.card J = 1344)
    (hJM : centIn M J = ⊥)
    (hSM : Nat.card
      (CFSG.Open.griessHopfMultiplier (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2) :
    IsInternalDirect (L1 ⊔ conjSub t L1) ⁅L1, L1⁆ (conjSub t ⁅L1, L1⁆) ∧
      Nonempty (↥⁅L1, L1⁆ ≃* ↥(centEl (L1 ⊔ conjSub t L1) t)) ∧
      centEl (L1 ⊔ conjSub t L1) t = J := by
  have hpair : Gl3Pair M L1 (conjSub t L1) :=
    { elem := hM2, card := hMc, inf := hinf, comm := hcomm, ext1 := hext1
      ext2 := y7c_isGL3Ext_conjSub hext1 htM }
  by_cases hU1 : centIn M L1 = ⊥
  · have hU2 : centIn M (conjSub t L1) = ⊥ := by
      rw [y7c_centIn_conjSub htM, hU1]
      exact conjSub_eq_bot_iff.mpr rfl
    exact (y7c_step1 hpair hP hV hVc hVP hU1 hU2).elim
  · have hU2 : centIn M (conjSub t L1) ≠ ⊥ := by
      intro h
      apply hU1
      have h' : conjSub t (centIn M L1) = ⊥ := by
        rw [← y7c_centIn_conjSub htM]
        exact h
      exact conjSub_eq_bot_iff.mp h'
    have hcinf : centIn M L1 ⊓ centIn M (conjSub t L1) = ⊥ :=
      y7c_cent_inf (M := M) (L1 := L1) (L2 := conjSub t L1) (J := J) hJK hJM
    have hccard := y7c_cent_card hpair hJK hJM hU1 hU2
    have hcsup := y7c_cent_sup hpair hJK hJM hU1 hU2
    have hc1 := y7c_comm_inf_eq hSM hpair hJK hJM hU1 hU2
    have hJK' : J ≤ conjSub t L1 ⊔ L1 := by simpa [sup_comm] using hJK
    have hc2 := y7c_comm_inf_eq hSM hpair.symm hJK' hJM hU2 hU1
    have hd0 := y7c_direct hpair hc1 hc2 hcinf hcsup
    have hAB : conjSub t ⁅L1, L1⁆ = ⁅conjSub t L1, conjSub t L1⁆ :=
      y7c_comm_conjSub t L1
    have hd : IsInternalDirect (L1 ⊔ conjSub t L1) ⁅L1, L1⁆ (conjSub t ⁅L1, L1⁆) := by
      rw [hAB]; exact hd0
    refine ⟨hd, y7c_centEl_equiv hd0 hAB ht2, ?_⟩
    have hcardA : Nat.card ↥⁅L1, L1⁆ = 1344 := by
      rw [IsGL3Ext.card_comm hext1, hc1, hccard.2]
    exact y7c_centEl_eq hd0 hAB ht2 hJK hJt (by rw [hJc, hcardA])

end CFSG.OddStandard.HigherRank.YamadaG23
