module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.GN

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

@[expose] def FFChevConclusion (Y : Type) [Group Y] : Prop :=
  IsChevTwo Y ∨ ∃ m : ℕ, 5 ≤ m ∧ Nonempty (Y ≃* alternatingGroup (Fin m))

@[expose] def FFChevModuleTheorem : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H L : Subgroup (MulAut V), FFHyp H L → IsFFModule H →
      FFChevConclusion (↥L ⧸ Subgroup.center ↥L)

theorem isChevTwo_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsChevTwo Y) : IsChevTwo Y' := by
  rcases h with ⟨d, hd, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨d, hd, ⟨φ⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans φ⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans φ⟩⟩)

theorem ffChevConclusion_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : FFChevConclusion Y) : FFChevConclusion Y' := by
  rcases h with h | ⟨m, hm, ⟨φ⟩⟩
  · exact Or.inl (isChevTwo_of_mulEquiv e h)
  · exact Or.inr ⟨m, hm, ⟨e.symm.trans φ⟩⟩

theorem ffChevConclusion_of_ffConclusion {Y : Type} [Group Y] (h : FFConclusion Y) :
    FFChevConclusion Y := by
  rcases h with h | h
  · exact Or.inl (isChevTwo_of_classicalTwoOrG2 h)
  · exact Or.inr h

theorem ffChevModuleTheorem_of_ffModuleTheorem (hFF : FFModuleTheorem) : FFChevModuleTheorem :=
  fun V _ _ hV H L hhyp hmod => ffChevConclusion_of_ffConclusion (hFF V hV H L hhyp hmod)

theorem exists_ffHyp_of_component (X : Type) [Group X] [Finite X]
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) X W)
    (hρ : Function.Injective ρ) (hK : CFSG.Open.IsKGroup X) (hO2 : CFSG.pCore 2 X = ⊥)
    (A : Subgroup X) (hAel : CFSG.IsElementaryAbelian 2 A)
    (hAbest : CFSG.RankThree.FFModules.IsBestOffender ρ A) (K : Subgroup X)
    (hKc : CFSG.Open.IsComponentOf K ⊤) (hKA : ⁅K, A⁆ ≠ ⊥) :
    ∃ (V : Type) (_ : CommGroup V) (_ : Finite V) (H L : Subgroup (MulAut V)),
      (∀ v : V, v ^ 2 = 1) ∧ FFHyp H L ∧ IsFFModule H ∧
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* ↥K ⧸ Subgroup.center ↥K) := by
  classical
  obtain ⟨V, _, _, f, E, hV, hf0, hirr, hEN, hE0, hEel, -, hoff⟩ :=
    GeneralFF.componentSectionProp X W ρ hρ hO2 A hAel hAbest K hKc hKA
  have hKq : CFSG.IsQuasisimple ↥K := ((CFSG.isComponent_iff_open K).mpr hKc).1
  obtain ⟨hLq, ⟨e⟩⟩ := CFSG.QuasithinUnique.Setup.X5.quasisimple_range_centerQuotientEquiv hKq f hf0
  set L := f.range with hL
  set H : Subgroup (MulAut V) := L ⊔ E with hH
  have hLH : L ≤ H := le_sup_left
  have hEH : E ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) := sup_le Subgroup.le_normalizer hEN
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  have hVnt : Nontrivial V := hirr.1
  have hP : ∀ P : Subgroup (MulAut V), IsPGroup 2 ↥P →
      (∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P) → P = ⊥ := by
    intro P hP2 hPn
    have hinv : ∀ g ∈ L, ∀ v ∈ fixV P, g v ∈ fixV P := by
      intro g hg v hv p hp
      have h1 : g⁻¹ * p * g⁻¹⁻¹ ∈ P := hPn _ (H.inv_mem (hLH hg)) p hp
      have h2 := hv _ h1
      rw [inv_inv] at h2
      calc p (g v) = g ((g⁻¹ * p * g) v) := by simp [MulAut.mul_apply]
        _ = g v := by rw [h2]
    have hfix : fixV P = ⊤ := by
      rcases hirr.2 (fixV P) hinv with h | h
      · exact absurd h (fixV_ne_bot_of_isPGroup' hV2 hP2)
      · exact h
    rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    ext v
    have hv : v ∈ fixV P := by rw [hfix]; exact Subgroup.mem_top v
    exact hv p hp
  have hNorm2 : ∀ N : Subgroup ↥H, N.Normal → IsPGroup 2 ↥N → N = ⊥ := by
    intro N hNn hN2
    have h1 := hP (N.map H.subtype) (hN2.map H.subtype) (fun h hh p hp => by
      obtain ⟨q, hq, rfl⟩ := hp
      exact ⟨⟨h, hh⟩ * q * ⟨h, hh⟩⁻¹, hNn.conj_mem q hq ⟨h, hh⟩, rfl⟩)
    rwa [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h1
  have hpCore : CFSG.pCore 2 ↥H = ⊥ := by
    unfold CFSG.pCore
    rw [sSup_eq_bot]
    rintro K ⟨hKn, hK2⟩
    exact hNorm2 K hKn hK2
  have hpCoreOf : CFSG.Open.pCoreOf 2 H = ⊥ := by
    unfold CFSG.Open.pCoreOf
    rw [CFSG.pCore_eq_iSup]
    rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective]
    simp only [iSup_eq_bot]
    intro N hNn hN2
    exact hNorm2 N hNn hN2
  have hF : CFSG.Open.quasithinGenFitting H = L := by
    refine C124.quasithinGenFitting_eq_of_two_group_quot hLH (fun y hy l hl =>
      (Subgroup.mem_normalizer_iff.mp (hHN hy) l).mp hl) (.inl (B1Red.isQuasisimple_to_open hLq))
      (fun y hy => ?_) hpCoreOf
    have hmem : y ∈ ((L ⊔ E : Subgroup (MulAut V)) : Set (MulAut V)) := hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L E hEN] at hmem
    obtain ⟨l, hl, a, ha, rfl⟩ := hmem
    refine ⟨1, ?_⟩
    have h1 : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hEN ha) l).mp hl
    have h2 : a * a = 1 := hEel.2 a ha
    have e1 : (l * a) ^ 2 ^ 1 = l * (a * l * a⁻¹) * (a * a) := by rw [pow_one, pow_two]; group
    rw [e1, h2, mul_one]
    exact L.mul_mem hl h1
  have hHyp : FFHyp H L := by
    refine ⟨hF.symm, hLq, hpCore, ?_⟩
    obtain ⟨i, ⟨e'⟩⟩ := isCatalogGroup_centerQuotient' hK hKq
    exact ⟨i, ⟨e.trans e'⟩⟩
  exact ⟨V, inferInstance, inferInstance, H, L, hV2, hHyp, ⟨E, hEH, hE0, hEel, hoff⟩, ⟨e⟩⟩

theorem chevConclusion_of_component (hFF : FFChevModuleTheorem) (X : Type) [Group X] [Finite X]
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) X W)
    (hρ : Function.Injective ρ) (hK : CFSG.Open.IsKGroup X) (hO2 : CFSG.pCore 2 X = ⊥)
    (A : Subgroup X) (hAel : CFSG.IsElementaryAbelian 2 A)
    (hAbest : CFSG.RankThree.FFModules.IsBestOffender ρ A) (K : Subgroup X)
    (hKc : CFSG.Open.IsComponentOf K ⊤) (hKA : ⁅K, A⁆ ≠ ⊥) :
    FFChevConclusion (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨V, _, _, H, L, hV2, hHyp, hmod, ⟨e⟩⟩ :=
    exists_ffHyp_of_component X W ρ hρ hK hO2 A hAel hAbest K hKc hKA
  exact ffChevConclusion_of_mulEquiv e (hFF V hV2 H L hHyp hmod)

theorem gn_chevConclusion (hFF : FFChevModuleTheorem)
    (X : Type) [Group X] [Finite X] (T : Subgroup X) (hGN : GNSetting X T)
    (L : Subgroup (X ⧸ gnC T)) (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    FFChevConclusion (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨W, _, _, _, ρ, hρ, A, hAel, hAbest, -, hLA⟩ := exists_rep_offender X T hGN L hL hJ
  have hLbot : L ≠ ⊥ := by
    intro h
    have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
    subst h
    have : Nontrivial (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T))) :=
      hs.toNontrivial
    obtain ⟨x, y, hxy⟩ := exists_pair_ne
      (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T)))
    induction x using QuotientGroup.induction_on with
    | _ a =>
      induction y using QuotientGroup.induction_on with
      | _ b => exact hxy (congrArg QuotientGroup.mk (Subsingleton.elim a b))
  exact chevConclusion_of_component hFF (X ⧸ gnC T) W ρ hρ (isKGroup_gnQuot hGN)
    (pCore_two_gnQuot hGN) A hAel hAbest L hL (by rw [hLA]; exact hLbot)

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531
