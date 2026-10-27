module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalInSitu
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalMax
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTransport
public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open KFactProofs.Sp62Local

theorem kFactSp62Local :
    KFactSp62Local := by
  intro Y _ _ _ K d hd hKn ⟨e⟩ hC T Y₀ _ hW hY₀ hKl
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨i, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨e₂⟩ := CFSG.RankThree.PartTwo.Census.nonempty_typeBGroupEquiv_sp6 q hv hqp hqe
  have hK : K = ⊤ := top_of_centralizer_eq_bot K (e.trans e₂) hC
  let Ψ₀ : Y ≃* H6 := Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr hK.symm).trans (e.trans e₂))
  have hs : Function.Surjective Ψ₀.toMonoidHom := fun x => Ψ₀.surjective x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H6 (Sylow.mapSurjective hs T) T0S
  let Ψ : Y ≃* H6 := Ψ₀.trans (MulAut.conj g)
  have hT : (T : Subgroup Y).map Ψ.toMonoidHom = T0 := by
    have h1 := congrArg (fun P : Sylow 3 H6 => (P : Subgroup H6)) hg
    simp only [Sylow.coe_subgroup_smul, coe_T0S, Sylow.coe_mapSurjective] at h1
    rw [← h1]
    show Subgroup.map Ψ.toMonoidHom (T : Subgroup Y) =
      Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map Ψ₀.toMonoidHom (T : Subgroup Y))
    rw [Subgroup.map_map]
    rfl
  have hmapsymm : ∀ A : Subgroup H6,
      (A.map Ψ.symm.toMonoidHom).map Ψ.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    ext x
    simp
  have hmap : ∀ A : Subgroup Y,
      (A.map Ψ.toMonoidHom).map Ψ.symm.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    ext x
    simp
  have hrank : 3 ≤ Open.pRank 3 B0 :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl B0_elemAbelian card_B0
  have hN : Subgroup.normalizer (B0 : Set H6) ≤ GLBWeakCore 3 T0 :=
    normalizer_le_weakCore_of_commutative_overgroup 3 Nat.prime_three B0_le_T0 le_rfl
      B0_elemAbelian.1 (by omega) hrank
  have hcore : GLBWeakCore 3 T0 ≤ Y₀.map Ψ.toMonoidHom := by
    have h1 := map_glbWeakCore_le Nat.prime_three Ψ.symm.toMonoidHom Ψ.symm.injective T0
    rw [show T0.map Ψ.symm.toMonoidHom = (T : Subgroup Y) by rw [← hT, hmap]] at h1
    have h2 := Subgroup.map_mono (f := Ψ.toMonoidHom) (h1.trans hW)
    rwa [hmapsymm] at h2
  have hne : Y₀.map Ψ.toMonoidHom ≠ ⊤ := by
    intro h
    apply hY₀
    have := congrArg (Subgroup.map Ψ.symm.toMonoidHom) h
    rwa [hmap, Subgroup.map_top_of_surjective _ Ψ.symm.surjective] at this
  have hK' : ¬ HasKlingenData 3 T0S (Y₀.map Ψ.toMonoidHom) := by
    intro h
    apply hKl
    have := hasKlingenData_of_mulEquiv Ψ.symm (T := T0S) (T' := T)
      (by rw [coe_T0S, ← hT, hmap]) h
    rwa [hmap] at this
  have hWY : W0 ≤ Y₀.map Ψ.toMonoidHom := W0_le_of_not_klingen (hN.trans hcore) hK'
  have hY : Y₀.map Ψ.toMonoidHom = W0 := eq_W0_of_ne_top hWY hne
  refine ⟨V0.map Ψ.symm.toMonoidHom, Sp62InSitu.of_mulEquiv Ψ ?_⟩
  rw [hT, hY, hmapsymm]
  exact sp62InSitu_W0

end CFSG.AGLEmbedding
