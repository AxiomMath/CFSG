module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62EscapeModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalMax
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalAut
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTransport
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open KFactProofs.Sp62Local

theorem exists_equiv_H6
    {Y : Type} [Group Y] [Finite Y] [Fact (Nat.Prime 3)]
    (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex) (hd : IsSpSixTwoIndex d) [K.Normal]
    (e : K ≃* CatGroup d) (hC : Subgroup.centralizer (K : Set Y) = ⊥) (T : Sylow 3 Y)
    (Y₀ : Subgroup Y) (hW : GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀) (hY₀ : Y₀ ≠ ⊤)
    (hKl : ¬ HasKlingenData 3 T Y₀) :
    ∃ Ψ : Y ≃* H6, (T : Subgroup Y).map Ψ.toMonoidHom = T0 ∧ Y₀.map Ψ.toMonoidHom = W0 := by
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
  have hrank : 3 ≤ CFSG.Open.pRank 3 B0 :=
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
  exact ⟨Ψ, hT, eq_W0_of_ne_top hWY hne⟩

theorem kFactSp62Escape :
    KFactSp62Escape := by
  intro Y _ _ _ K d hd hKn ⟨e⟩ hC T Y₀ _ hW hY₀ hKl
  obtain ⟨Ψ, hT, hY⟩ := exists_equiv_H6 K d hd e hC T Y₀ hW hY₀ hKl
  have hmemT : ∀ a ∈ T0, Ψ.symm a ∈ (T : Subgroup Y) := fun a ha => by
    rw [← hT] at ha
    exact Subgroup.mem_map_equiv.1 ha
  have hcomm : ∀ a ∈ Subgroup.centralizer ({elt cW0} : Set H6),
      Ψ.symm a ∈ Subgroup.centralizer ({Ψ.symm (elt cW0)} : Set Y) := fun a ha => by
    rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
    rw [← map_mul, ← map_mul, ha]
  refine ⟨Ψ.symm (elt cW0), hmemT _ (B0_le_T0 w0_mem_B0), ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_w0
  · intro hle
    apply elt_cAlt0_not_mem_W0
    have hy := hle (hcomm _ (Alt0_le_centralizer elt_cAlt0_mem_Alt0))
    rw [← hY]
    exact Subgroup.mem_map_equiv.2 hy
  · refine ⟨B0.map Ψ.symm.toMonoidHom, le_inf ?_ ?_, elementary_abelian_map 3 B0_elemAbelian _, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact hmemT b (B0_le_T0 hb)
    · rintro _ ⟨b, hb, rfl⟩
      refine hcomm b ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (B0_elemAbelian.1.is_comm.comm (⟨b, hb⟩ : B0) ⟨_, w0_mem_B0⟩)
    · rw [Subgroup.card_map_of_injective Ψ.symm.injective, card_B0]
  · obtain ⟨φ⟩ := nonempty_Alt0_mulEquiv
    refine ⟨Alt0.map Ψ.symm.toMonoidHom, ?_,
      ⟨(Subgroup.equivMapOfInjective Alt0 Ψ.symm.toMonoidHom Ψ.symm.injective).symm.trans φ⟩⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hcomm b (Alt0_le_centralizer hb)

end CFSG.AGLEmbedding
