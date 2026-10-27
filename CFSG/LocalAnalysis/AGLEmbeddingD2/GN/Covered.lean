module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.Background.C1GNDefs
import CFSG.Quasithin.Background.C118NoOuter
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowFrattiniSup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.Quasithin.EmptyFaithful.S1412
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.Equivariance
import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X] {T : Subgroup X}

theorem mem_sup_gnC_iff (T W : Subgroup X) (h : X) :
    h ∈ W ⊔ gnC T ↔ QuotientGroup.mk' (gnC T) h ∈ gnImg T W := by
  have := Subgroup.comap_map_eq (QuotientGroup.mk' (gnC T)) W
  rw [QuotientGroup.ker_mk'] at this
  rw [← this]
  exact Iff.rfl

theorem le_or_le_of_not_gnYComponent {T₁ T₂ : Subgroup X} {L : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤) (hY : ¬ GNYComponent T T₁ T₂ L) :
    L ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
      L ≤ gnImg T (Subgroup.normalizer (T₂ : Set X)) := by
  by_contra hn
  rw [not_or] at hn
  exact hY ⟨hL, hn.1, hn.2⟩

theorem gnA_eq_of_le_centralizer {T₁ : Subgroup X} {L : Subgroup (X ⧸ gnC T)}
    (h : L ≤ gnImg T (Subgroup.centralizer (T₁ : Set X))) : gnA T T₁ L = L :=
  inf_eq_right.2 (h.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _)))

theorem gnA_eq_of_le_normalizer {T₂ : Subgroup X} {L : Subgroup (X ⧸ gnC T)}
    (h : L ≤ gnImg T (Subgroup.normalizer (T₂ : Set X))) : gnA T T₂ L = L :=
  inf_eq_right.2 h

theorem isGNPair_of_isC118Pair {C₁ C₂ : Subgroup X} (h : IsC118Pair T C₁ C₂) :
    IsGNPair T C₁ C₂ := by
  obtain ⟨h1ne, h1Z, h1ch, h2ne, h2B, h2ch, -⟩ := h
  exact ⟨h1ne, h2ne, h1Z, h2B.trans (C1GN.baum_le T), h1ch,
    C1GN.characteristic_subgroupOf_trans (C1GN.baum_le T) h2B (C1GN.characteristic_baum T) h2ch⟩

variable [Finite X]

theorem exists_isC118Pair (hX : GNSetting X T) (hT : T ≠ ⊥) :
    ∃ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ :=
  theoremC118 X T hX.sylow.2.1 hT

theorem normalizer_gnImg_eq (hX : GNSetting X T) {W : Subgroup X} (hWT : W ≤ T)
    (hTW : T ≤ Subgroup.normalizer (W : Set X))
    (hR : ∀ R : Subgroup X, W ≤ R → R ≤ T →
      Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (W : Set X)) :
    Subgroup.normalizer (gnImg T W : Set (X ⧸ gnC T)) =
      gnImg T (Subgroup.normalizer (W : Set X)) := by
  refine le_antisymm ?_ (Subgroup.le_normalizer_map _)
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg : g ∈ Subgroup.normalizer ((W ⊔ gnC T : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff] at hq ⊢
    intro h
    rw [mem_sup_gnC_iff, mem_sup_gnC_iff]
    have := hq (QuotientGroup.mk' (gnC T) h)
    simpa using this
  obtain ⟨c, hc, n, hn, hgcn⟩ := Tits.OrdinaryProofs.exists_mul_of_mem_normalizer_sup
    (M := ⊤) (C := gnC T) (T := T) (X := W) le_top
    (by rw [Subgroup.normalizer_eq_top]) hX.sylow hWT hTW
    (hR _ (le_inf hWT le_sup_left) inf_le_left) (Subgroup.mem_top g) hg
  refine ⟨n, hn.2, ?_⟩
  rw [hgcn, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).2 hc, one_mul]
  rfl

theorem normalizer_gnImg_thompsonJ (hX : GNSetting X T) :
    Subgroup.normalizer (gnImg T (thompsonJ T) : Set (X ⧸ gnC T)) =
      gnImg T (Subgroup.normalizer (thompsonJ T : Set X)) :=
  normalizer_gnImg_eq hX (C1GN.thompsonJ_le T)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T))
    fun R hWR hRT => (normalizer_le_normalizer_thompsonJ R).trans
      (by rw [thompsonJ_eq_of_le hWR hRT])

theorem normalizer_gnImg_baum (hX : GNSetting X T) :
    Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T)) =
      gnImg T (Subgroup.normalizer (baum T : Set X)) :=
  normalizer_gnImg_eq hX (C1GN.baum_le T)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
    fun R hWR hRT => (normalizer_le_normalizer_baum R).trans
      (by rw [baum_eq_of_le hWR hRT])

theorem omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ (T : Subgroup X) :
    omegaOneCenterOf T ≤ omegaOneCenterOf (thompsonJ T) := by
  rw [← (omegaOne_centralizer_thompsonJ T).1]
  refine (Subgroup.closure_le _).2 fun z hz => Subgroup.subset_closure ⟨⟨hz.1.1, ?_⟩, hz.2⟩
  exact Subgroup.centralizer_le (C1GN.thompsonJ_le T) hz.1.2

theorem covered_isComponentOf (hX : GNSetting X T) {C₁ C₂ : Subgroup X}
    (h1 : C₁ ≤ omegaOneCenterOf T) (h2 : C₂ ≤ baum T)
    (h2c : (C₂.subgroupOf (baum T)).Characteristic) {L : Subgroup (X ⧸ gnC T)}
    (hL : Open.IsComponentOf L ⊤)
    (hLJ : L ≤ Subgroup.normalizer (gnImg T (thompsonJ T) : Set (X ⧸ gnC T))) :
    L ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      L ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  set J : Subgroup X := thompsonJ T
  set E : Subgroup X := omegaOneCenterOf J
  set N : Subgroup X := Subgroup.normalizer (J : Set X)
  set K : Subgroup X := N ⊓ Subgroup.centralizer (E : Set X)
  rw [normalizer_gnImg_thompsonJ hX] at hLJ
  have hTN : T ≤ N := Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  have hNE : N ≤ Subgroup.normalizer (E : Set X) :=
    normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv J
  have hNK : N ≤ Subgroup.normalizer (K : Set X) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hn,
      GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup E (hNE hn)⟩
  have hKN : gnImg T K ≤ gnImg T N := Subgroup.map_mono inf_le_left
  have hKnormal : ((gnImg T K).subgroupOf (gnImg T N)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKN]
    exact (Subgroup.map_mono hNK).trans (Subgroup.le_normalizer_map _)
  have hLsub : L.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff L).1 hL.2.1
  have hqs : CFSG.GorensteinWalter.IsQuasisimple ↥L := by
    have := hL.2.2.2
    exact ⟨(QuotientGroup.mk_surjective (s := Subgroup.center ↥L)).nontrivial, hL.2.2.1,
      hL.2.2.2⟩
  have hLcomp : CFSG.GorensteinWalter.IsComponentOf L (gnImg T N) := ⟨hLJ, hLsub.subgroupOf, hqs⟩
  rcases CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf
    hKN hKnormal.isSubnormal hLcomp with hle | hcomm
  · left
    refine hle.trans (Subgroup.map_mono fun x hx => ?_)
    exact Subgroup.centralizer_le
      (h1.trans (omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ T)) hx.2
  · right
    have hBK : gnImg T (baum T) ≤ gnImg T K :=
      Subgroup.map_mono fun x hx => ⟨hTN hx.1, hx.2⟩
    have hLc : L ≤ Subgroup.centralizer (gnImg T (baum T) : Set (X ⧸ gnC T)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm).trans (Subgroup.centralizer_le hBK)
    have hLn : L ≤ Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T)) :=
      hLc.trans (Subgroup.centralizer_le_normalizer _)
    rw [normalizer_gnImg_baum hX] at hLn
    exact hLn.trans
      (Subgroup.map_mono (normalizer_le_normalizer_of_characteristic_subgroupOf h2 h2c))

section JNormalizes

open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

theorem thompsonJ_le_normalizer_of_isComponentOf (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤) :
    gnImg T (thompsonJ T) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := by
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hC : CFSG.IsComponent L := (CFSG.isComponent_iff_open L).2 hL
  unfold gnImg thompsonJ
  rw [Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hA =>
    (le_bestOffenderSub (isElementaryAbelian_map_mk hA) (isBestOffender_gnRep hV hX hA)).trans
      (bestOffenderSub_le_normalizer_component (gnRep hV) (gnRep_injective hV) hC)

theorem commutator_eq_of_gnYComponent (hX : GNSetting X T) {C₁ C₂ : Subgroup X}
    (h1 : C₁ ≤ omegaOneCenterOf T) (h2 : C₂ ≤ baum T)
    (h2c : (C₂.subgroupOf (baum T)).Characteristic) {L : Subgroup (X ⧸ gnC T)}
    (hY : GNYComponent T C₁ C₂ L) : ⁅L, gnImg T (thompsonJ T)⁆ = L := by
  obtain ⟨hL, hn1, hn2⟩ := hY
  have hJ := thompsonJ_le_normalizer_of_isComponentOf hX hL
  by_cases hb : ⁅L, gnImg T (thompsonJ T)⁆ = ⊥
  ·
    exfalso
    have hc : L ≤ Subgroup.centralizer (gnImg T (thompsonJ T) : Set (X ⧸ gnC T)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hb
    rcases covered_isComponentOf hX h1 h2 h2c hL
      (hc.trans (Subgroup.centralizer_le_normalizer _)) with h | h
    · exact hn1 h
    · exact hn2 h
  ·
    exact commutator_eq_of_ne_bot ((CFSG.isComponent_iff_open L).2 hL).1 hJ hb

end JNormalizes

section AlternatingRank

open Equiv

private theorem sign_viaEmbeddingHom {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (ι : α ↪ β) (e : Perm α) :
    Perm.sign (Perm.viaEmbeddingHom ι e) = Perm.sign e :=
  @Perm.sign_extendDomain α _ β _ _ _ e (fun b => b ∈ Set.range ι)
    (fun _ => Classical.propDecidable _) (Equiv.ofInjective ι.1 ι.2)

private theorem exists_injective_alt_three_prod {n : ℕ} (hn : 6 ≤ n) :
    ∃ f : alternatingGroup (Fin 3) × alternatingGroup (Fin 3) →* alternatingGroup (Fin n),
      Function.Injective f := by
  let ι : Fin 3 ⊕ Fin 3 ↪ Fin n :=
    (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin (3 + 3)).toEmbedding.trans (Fin.castLEEmb (by omega))
  let φ : alternatingGroup (Fin 3) × alternatingGroup (Fin 3) →* Perm (Fin n) :=
    ((Perm.viaEmbeddingHom ι).comp (Perm.sumCongrHom (Fin 3) (Fin 3))).comp
      ((alternatingGroup (Fin 3)).subtype.prodMap (alternatingGroup (Fin 3)).subtype)
  have hφ : Function.Injective φ := fun x y h =>
    Prod.ext
      (Subtype.ext (congrArg Prod.fst
        (Perm.sumCongrHom_injective (Perm.viaEmbeddingHom_injective ι h))))
      (Subtype.ext (congrArg Prod.snd
        (Perm.sumCongrHom_injective (Perm.viaEmbeddingHom_injective ι h))))
  refine ⟨φ.codRestrict (alternatingGroup (Fin n)) fun x => ?_,
    fun x y h => hφ (congrArg Subtype.val h)⟩
  change Perm.sign (Perm.viaEmbeddingHom ι (Perm.sumCongr x.1.1 x.2.1)) = 1
  rw [sign_viaEmbeddingHom, Perm.sign_sumCongr, Perm.mem_alternatingGroup.1 x.1.2,
    Perm.mem_alternatingGroup.1 x.2.2, one_mul]

theorem two_le_pRank_of_mulEquiv_alternatingGroup {Y : Type*} [Group Y] [Finite Y]
    {L : Subgroup Y} {n : ℕ} (hn : 6 ≤ n) (e : ↥L ≃* alternatingGroup (Fin n)) :
    2 ≤ Open.pRank 3 L := by
  obtain ⟨g, hg⟩ := exists_injective_alt_three_prod hn
  have hcomm : ∀ a b : alternatingGroup (Fin 3), a * b = b * a := by decide
  have hpow : ∀ a : alternatingGroup (Fin 3), a ^ 3 = 1 := by decide
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  let f : alternatingGroup (Fin 3) × alternatingGroup (Fin 3) →* Y :=
    L.subtype.comp (e.symm.toMonoidHom.comp g)
  refine SectionRank.le_pRank_of_injective
    (A := alternatingGroup (Fin 3) × alternatingGroup (Fin 3)) (by norm_num)
    (fun a b => Prod.ext (hcomm _ _) (hcomm _ _)) (fun a => Prod.ext (hpow _) (hpow _))
    (by simp only [Nat.card_prod, hcard]; norm_num) f
    (L.subtype_injective.comp (e.symm.injective.comp hg)) ?_
  rintro _ ⟨x, rfl⟩
  exact (e.symm (g x)).2

end AlternatingRank

theorem one_lt_pRank_of_covered {T₁ T₂ : Subgroup X} {L : Subgroup (X ⧸ gnC T)} {n : ℕ}
    (hn : 6 ≤ n) (e : ↥L ≃* alternatingGroup (Fin n))
    (hcov : L ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
      L ≤ gnImg T (Subgroup.normalizer (T₂ : Set X))) :
    1 < Open.pRank 3 (gnA T T₁ L) ∨ 1 < Open.pRank 3 (gnA T T₂ L) := by
  have h2 := two_le_pRank_of_mulEquiv_alternatingGroup hn e
  rcases hcov with h | h
  · left
    rw [gnA_eq_of_le_centralizer h]
    exact h2
  · right
    rw [gnA_eq_of_le_normalizer h]
    exact h2

@[expose] def GNYComponentFacts (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ L : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ L →
    (IsChevTwo (↥L ⧸ Subgroup.center ↥L) → ∀ P, IsMinOverBorel L (gnImg T T ⊓ L) P →
        pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
          pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (T₂ : Set X))) ∧
      (gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) →
        Nonempty (↥L ≃* alternatingGroup (Fin 7)) →
          1 < Open.pRank 3 (gnA T T₁ L) ∨ 1 < Open.pRank 3 (gnA T T₂ L)) ∧
      (∀ n : ℕ, 8 < n → Nonempty (↥L ≃* alternatingGroup (Fin n)) →
        1 < Open.pRank 3 (gnA T T₁ L) ∨ 1 < Open.pRank 3 (gnA T T₂ L))

theorem gnParabolic_gnAlt7_gnAltBig_of_yFacts {T₁ T₂ : Subgroup X}
    (h : GNYComponentFacts T T₁ T₂) :
    GNParabolic T T₁ T₂ ∧ GNAlt7 T T₁ T₂ ∧ GNAltBig T T₁ T₂ := by
  refine ⟨fun L hL hChev P hP => ?_, fun L hL hLT hA => ?_, fun L hL n hn hA => ?_⟩
  · by_cases hY : GNYComponent T T₁ T₂ L
    · exact (h L hY).1 hChev P hP
    · have hPL : pElementSubgroup 2 P ≤ L := (pElementSubgroup_le P).trans hP.1
      exact (le_or_le_of_not_gnYComponent hL hY).imp hPL.trans hPL.trans
  · by_cases hY : GNYComponent T T₁ T₂ L
    · exact (h L hY).2.1 hLT hA
    · obtain ⟨e⟩ := hA
      exact one_lt_pRank_of_covered (by norm_num) e (le_or_le_of_not_gnYComponent hL hY)
  · by_cases hY : GNYComponent T T₁ T₂ L
    · exact (h L hY).2.2 n hn hA
    · obtain ⟨e⟩ := hA
      exact one_lt_pRank_of_covered (by omega) e (le_or_le_of_not_gnYComponent hL hY)

theorem glaubermanNiles_of_yFacts
    (h : ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
      ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ →
        GNYComponentFacts T C₁ C₂ ∧ GNThree T C₁ C₂ ∧ GNCentre T C₁ C₂) :
    GlaubermanNilesInput := by
  intro X _ _ T hX hT
  obtain ⟨C₁, C₂, hC⟩ := exists_isC118Pair hX hT
  obtain ⟨hF, h3, hc⟩ := h X T hX hT C₁ C₂ hC
  obtain ⟨hP, h7, hB⟩ := gnParabolic_gnAlt7_gnAltBig_of_yFacts hF
  exact ⟨C₁, C₂, isGNPair_of_isC118Pair hC, hP, h3, hc, h7, hB⟩

end CFSG.AGLEmbeddingD2.GN
