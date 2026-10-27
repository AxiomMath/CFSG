module

import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ChevFrontier
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.FinalSmall
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.J3
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Final
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Model
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22Three
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi24Prime
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McL
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Suz
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ON
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HN
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Ly
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Th
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.B
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.M
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux1
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux2
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_PComp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Plumb
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJFinal
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

section ZJAny

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ
open scoped commutatorElement

@[expose] def KFactZJFactorizationAny : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X],
    CFSG.AGLEmbedding.CatalogSimpleSections X →
    centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X →
    ∀ K : Subgroup X, K.Normal → CFSG.IsPComponent p K →
    (∃ T : Sylow 2 X, K ⊔ (T : Subgroup X) = ⊤) →
    ¬ 3 ∣ Nat.card (⁅K, (CFSG.pPrimeCore p K).map K.subtype⁆ : Subgroup X) →
    (∀ T₂ : Sylow 2 (CFSG.pPrimeCore p X), (T₂ : Subgroup (CFSG.pPrimeCore p X)).Normal) →
    ∀ S : Subgroup X, IsPGroup 2 S → CFSG.pCore 2 X ≤ S →
    (∀ Z : Subgroup X, Z ≤ S → Z ≠ ⊥ → (Z.subgroupOf S).Characteristic →
      ¬ K ≤ normalizer (Z : Set X) ⊔ CFSG.pPrimeCore p X) →
    IsChevTwo ((↥K ⧸ CFSG.pPrimeCore p ↥K) ⧸ center (↥K ⧸ CFSG.pPrimeCore p ↥K)) ∨
      ∃ n : ℕ, Nonempty ((↥K ⧸ CFSG.pPrimeCore p ↥K) ⧸ center (↥K ⧸ CFSG.pPrimeCore p ↥K) ≃*
        alternatingGroup (Fin n))

theorem kFactZJFactorizationAny_of_ffChev
    (hFF : CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.FFChevModuleTheorem) :
    KFactZJFactorizationAny := by
  intro p hp hp2 X _ _ hsec hcent K hKn hK hT h3 h2cl S hS2 hcore hchar
  haveI : K.Normal := hKn
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hKT⟩ := hT
  haveI : Nontrivial X := zj_nontrivial_of_pComponent hK
  have hCh : CharTwo (⊤ : Subgroup X) := by
    unfold CharTwo
    rw [pCoreOf_top]
    exact inf_le_right.trans hcent
  have hQS : pCoreOf 2 (⊤ : Subgroup X) ≤ S := by
    rw [pCoreOf_top]
    exact hcore
  haveI : (gnC S).Normal := gnC_normal S
  have hKC : ¬ K ≤ gnC S := zj_not_le_centralizer hS2 hcore hcent hchar
  have hcoreC : CFSG.pCore 2 X ≤ gnC S := zj_pCore_le_gnC hcore hcent
  have hO2 := zj_pCore_quotient_eq_bot hp hp2 hK T hKT h2cl hcoreC hKC
  obtain ⟨A, hAmax, hAnot⟩ := zj_exists_offender hS2 hcore hcent hchar
  have hA2 : IsPGroup 2 A := hS2.to_le hAmax.1
  have hKA : ⁅K, A⁆ = K := zj_commutator_eq_of_not_le_pCore hp hp2 hK T hKT h2cl hA2 hAnot
  have hRodd : Odd (Nat.card ↥((K ⊓ CFSG.pPrimeCore p X).map (QuotientGroup.mk' (gnC S)))) :=
    zj_odd_card_map_le_pPrimeCore h2cl hcoreC inf_le_right
  have hle : K ⊓ CFSG.pPrimeCore p X ≤ (CFSG.pPrimeCore p ↥K).map K.subtype := by
    rw [zj_pPrimeCore_eq_subgroupOf, Subgroup.subgroupOf_map_subtype, inf_comm]
  have h3' : ¬ 3 ∣ Nat.card ↥(⁅K, K ⊓ CFSG.pPrimeCore p X⁆ : Subgroup X) := fun h =>
    h3 (h.trans (Subgroup.card_dvd_of_le (Subgroup.commutator_mono le_rfl hle)))
  have hcentC := zj_commutator_le_gnC_of_offender hCh hQS hAmax (zj_pComponent_perfect hK) hKA
    hRodd h3'
  have hcentC' : ⁅K ⊓ CFSG.pPrimeCore p X, K⁆ ≤ gnC S := by
    rw [Subgroup.commutator_comm]
    exact hcentC
  obtain ⟨hq, ⟨e⟩⟩ := zj_component_image hK hKC
    (fun r hr y hy => hcentC' (Subgroup.commutator_mem_commutator hr hy))
  haveI : (K.map (QuotientGroup.mk' (gnC S))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hKc : IsComponentOf (K.map (QuotientGroup.mk' (gnC S))) ⊤ :=
    (CFSG.isComponent_iff_open _).mp ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩
  have hKA' : ⁅K.map (QuotientGroup.mk' (gnC S)), A.map (QuotientGroup.mk' (gnC S))⁆ ≠ ⊥ := by
    rw [← Subgroup.map_commutator, hKA]
    intro hbot
    apply hKC
    intro k hk
    have hmem : QuotientGroup.mk' (gnC S) k ∈ K.map (QuotientGroup.mk' (gnC S)) := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff k).mp hmem
  have hFFC := zj_chev_of_component hFF hsec hCh hQS hAmax hO2 hKc hKA'
  have hres := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffChevConclusion_of_mulEquiv
    e.symm hFFC
  rcases hres with h | ⟨m, -, hm⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, hm⟩

section Assembly

theorem kFactZJFactorizationAny_holds : KFactZJFactorizationAny :=
  kFactZJFactorizationAny_of_ffChev
    (HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffChevModuleTheorem_of
        (HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadic_of_each
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_J3
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Co1
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Co2
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Co3
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Fi22
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Fi23
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Fi24Prime
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_McL
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Suz
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_ONan
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_HN
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Ly
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Th
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_B
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_M)
        (HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOdd_of_nodes
            HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOddExceptional
            HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOddSmall))

end Assembly

end ZJAny

section Apply

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem zj_apply_any {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (hK1 : KFactZJFactorizationAny) (hsec : CFSG.AGLEmbedding.CatalogSimpleSections Y)
    (hcharTwo : centralizer (CFSG.pCore 2 Y : Set Y) ≤ CFSG.pCore 2 Y)
    (hsylow : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.pCore 2 Y) (CFSG.pPrimeCore p Y))
    {J V : Subgroup Y} (hJn : J.Normal) (hJc : CFSG.IsPComponent p J)
    {L : Subgroup (Y ⧸ CFSG.pPrimeCore p Y)} (hLs : IsSimpleGroup L)
    (hLnab : ∃ a b : L, a * b ≠ b * a)
    (hLn : L.Normal) (hLc : centralizer (L : Set (Y ⧸ CFSG.pPrimeCore p Y)) = ⊥)
    (hJL : J.map (QuotientGroup.mk' (CFSG.pPrimeCore p Y)) = L)
    (hJp : pElementSubgroup p J = J) (hV : IsPGroup 2 V) (hcore : CFSG.pCore 2 Y ≤ V)
    (hJ0 : ¬ 3 ∣ Nat.card (⁅J, (CFSG.pPrimeCore p ↥J).map J.subtype⁆ : Subgroup Y))
    (hnc : ∀ Z : Subgroup Y, Z ≤ V → Z ≠ ⊥ → (Z.subgroupOf V).Characteristic →
      ¬ J ≤ normalizer (Z : Set Y) ⊔ CFSG.pPrimeCore p Y) :
    IsChevTwo L ∨ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n)) := by
  have _ := hJc
  have : Fact p.Prime := ⟨hp⟩
  have : J.Normal := hJn
  have : IsSimpleGroup L := hLs
  obtain ⟨W, hW⟩ : ∃ W : Subgroup Y, J ⊔ V = W := ⟨_, rfl⟩
  have hJW : J ≤ W := hW ▸ le_sup_left
  have hVW : V ≤ W := hW ▸ le_sup_right
  have hRW : CFSG.pCore 2 Y ≤ W := hcore.trans hVW
  have hpL : p ∣ Nat.card L := zja_dvd_card hp hLnab hJL hJp
  have hpc : CFSG.pCore 2 W = (CFSG.pCore 2 Y).subgroupOf W :=
    zja_pCore_eq hp hp2 hsylow hLs hLn hLc hpL hJL hJW
  have hPle : (CFSG.pPrimeCore p W).map W.subtype ≤ CFSG.pPrimeCore p Y :=
    zja_map_subtype_le hp hLs hLn hLc hpL hJL hJW (N := CFSG.pPrimeCore p W)
      CFSG.pPrimeCore_coprime_card
  have hcharW : centralizer (CFSG.pCore 2 W : Set W) ≤ CFSG.pCore 2 W := by
    rw [hpc]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hcharTwo
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) ⟨r, hRW hr⟩ hr)
  have h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore p W),
      (T₂ : Subgroup (CFSG.pPrimeCore p W)).Normal :=
    fun T₂ => zja_sylow_normal hsylow hPle T₂
  have hKn : (J.subgroupOf W).Normal := inferInstance
  have hKp : pElementSubgroup p (J.subgroupOf W) = J.subgroupOf W :=
    zja_pElementSubgroup_subgroupOf hJW hJp
  obtain ⟨e₂⟩ := zja_exists_equiv_image hp hLs hLn hLc hpL hJL hJW
  have hcomp : CFSG.IsComponent
      ((J.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore p W))) := by
    refine ⟨?_, ?_⟩
    · have : IsSimpleGroup
          ↥((J.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore p W))) :=
        e₂.isSimpleGroup
      refine zja_isQuasisimple_of_simple ?_
      obtain ⟨a, b, hab⟩ := hLnab
      exact ⟨e₂.symm a, e₂.symm b, fun h => hab (by simpa using congrArg e₂ h)⟩
    · exact Subgroup.Normal.isSubnormal
        (Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _))
  have hPC : CFSG.IsPComponent p (J.subgroupOf W) :=
    isPComponent_of_normal hp hKn hKp hcomp rfl
  have hS2 : IsPGroup 2 (V.subgroupOf W) := hV.comap_subtype
  have hKS : J.subgroupOf W ⊔ V.subgroupOf W = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJW,
      Subgroup.map_subgroupOf_eq_of_le hVW, hW, Subgroup.map_top, Subgroup.range_subtype]
  have hT : ∃ T : Sylow 2 W, J.subgroupOf W ⊔ (T : Subgroup W) = ⊤ := by
    obtain ⟨T, hT⟩ := hS2.exists_le_sylow
    exact ⟨T, eq_top_iff.mpr (hKS.ge.trans (sup_le_sup_left hT _))⟩
  have h3 : ¬ 3 ∣ Nat.card (⁅J.subgroupOf W,
      (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map (J.subgroupOf W).subtype⁆ : Subgroup W) := by
    let ι : ↥(J.subgroupOf W) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJW
    have hcore' : (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map ι.toMonoidHom =
        CFSG.pPrimeCore p ↥J := CFSG.pPrimeCore_map_iso p ι
    have hhom : W.subtype.comp (J.subgroupOf W).subtype = J.subtype.comp ι.toMonoidHom := by
      ext x
      rfl
    have himg : ((CFSG.pPrimeCore p ↥(J.subgroupOf W)).map (J.subgroupOf W).subtype).map
        W.subtype = (CFSG.pPrimeCore p ↥J).map J.subtype := by
      rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hcore']
    have hcomm : (⁅J.subgroupOf W, (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map
        (J.subgroupOf W).subtype⁆ : Subgroup W).map W.subtype =
        ⁅J, (CFSG.pPrimeCore p ↥J).map J.subtype⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJW, himg]
    have hcard := Subgroup.card_map_of_injective
      (K := (⁅J.subgroupOf W, (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map
        (J.subgroupOf W).subtype⁆ : Subgroup W)) W.subtype_injective
    rw [hcomm] at hcard
    rw [← hcard]
    exact hJ0
  have hnc' : ∀ Z' : Subgroup W, Z' ≤ V.subgroupOf W → Z' ≠ ⊥ →
      (Z'.subgroupOf (V.subgroupOf W)).Characteristic →
      ¬ J.subgroupOf W ≤ normalizer (Z' : Set W) ⊔ CFSG.pPrimeCore p W := by
    intro Z' hZ'S hZ'1 hZ'c hcover
    have hZV : Z'.map W.subtype ≤ V := by
      rintro _ ⟨z, hz, rfl⟩
      exact hZ'S hz
    have hZ1 : Z'.map W.subtype ≠ ⊥ := fun h =>
      hZ'1 ((Subgroup.map_eq_bot_iff_of_injective Z' W.subtype_injective).mp h)
    have hZc : ((Z'.map W.subtype).subgroupOf V).Characteristic := by
      let e : ↥(V.subgroupOf W) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVW
      have hchar := zja_characteristic_map e hZ'c
      have heq : (Z'.subgroupOf (V.subgroupOf W)).map e.toMonoidHom =
          (Z'.map W.subtype).subgroupOf V := by
        ext x
        constructor
        · rintro ⟨s, hs, rfl⟩
          exact ⟨s, hs, rfl⟩
        · intro hx
          obtain ⟨z, hz, hzx⟩ := hx
          exact ⟨⟨z, hZ'S hz⟩, hz, Subtype.ext hzx⟩
      rw [← heq]
      exact hchar
    refine hnc _ hZV hZ1 hZc ?_
    have h1 : (J.subgroupOf W).map W.subtype ≤
        (normalizer (Z' : Set W) ⊔ CFSG.pPrimeCore p W).map W.subtype :=
      Subgroup.map_mono hcover
    rw [Subgroup.map_subgroupOf_eq_of_le hJW, Subgroup.map_sup] at h1
    refine h1.trans (sup_le_sup ?_ hPle)
    rintro _ ⟨g, hg, rfl⟩
    exact thg_mem_normalizer_map hg
  have hcoreS : CFSG.pCore 2 W ≤ V.subgroupOf W := by
    rw [hpc]
    exact Subgroup.comap_mono hcore
  have key := hK1 p hp hp2 (↥W) (hsec.subgroup W) hcharW (J.subgroupOf W) hKn hPC hT
    h3 h2cl (V.subgroupOf W) hS2 hcoreS hnc'
  have hLcen : center L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : (z : Y ⧸ CFSG.pPrimeCore p Y) ∈
        centralizer (L : Set (Y ⧸ CFSG.pPrimeCore p Y)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨h, hh⟩)
    rw [hLc, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (Subtype.ext hz')
  let ψ₀ : ↥(J.subgroupOf W) →* Y ⧸ CFSG.pPrimeCore p Y :=
    ((QuotientGroup.mk' (CFSG.pPrimeCore p Y)).comp W.subtype).comp (J.subgroupOf W).subtype
  have hψ₀L : ∀ x : ↥(J.subgroupOf W), ψ₀ x ∈ L := by
    intro x
    rw [← hJL]
    exact Subgroup.mem_map_of_mem _ x.2
  let ψ : ↥(J.subgroupOf W) →* ↥L := ψ₀.codRestrict L hψ₀L
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hJL] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact ⟨⟨⟨j, hJW hj⟩, hj⟩, rfl⟩
  have hker : p.Coprime (Nat.card ψ.ker) := by
    have hle : ψ.ker.map (W.subtype.comp (J.subgroupOf W).subtype) ≤ CFSG.pPrimeCore p Y := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : ψ₀ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff _).mp hx1
    have hinj : Function.Injective (W.subtype.comp (J.subgroupOf W).subtype) :=
      W.subtype_injective.comp (J.subgroupOf W).subtype_injective
    rw [← Subgroup.card_map_of_injective hinj]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      CFSG.pPrimeCore_coprime_card
  obtain ⟨e⟩ := zja_quotient_equiv hp (G := ↥(J.subgroupOf W)) (M := ↥L) hpL hLcen ψ hψ hker
  exact zja_chevTwo_or_alt_of_mulEquiv e key

end Apply

end CFSG.LocalAnalysis.RankThreeTheoremC
