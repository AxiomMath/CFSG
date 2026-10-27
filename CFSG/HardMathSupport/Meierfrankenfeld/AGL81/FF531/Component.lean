module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bActor
public import CFSG.Quasithin.Background.C124FStar

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Meierfrankenfeld

theorem isCatalogGroup_centerQuotient' {X : Type*} [Group X]
    (hX : CFSG.Open.IsKGroup X) {K : Subgroup X} (hK : CFSG.IsQuasisimple ↥K) :
    CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) := by
  have heq : ((Subgroup.center ↥K).map K.subtype).subgroupOf K = Subgroup.center ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hle : (Subgroup.center ↥K).map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hnorm : (((Subgroup.center ↥K).map K.subtype).subgroupOf K).Normal := by
    rw [heq]; infer_instance
  let e0 : ↥K ⧸ ((Subgroup.center ↥K).map K.subtype).subgroupOf K ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.quotientMulEquivOfEq heq
  have hsimple : IsSimpleGroup (↥K ⧸ ((Subgroup.center ↥K).map K.subtype).subgroupOf K) :=
    haveI := hK.2.1
    e0.isSimpleGroup
  have hnab : ∃ a b : ↥K ⧸ ((Subgroup.center ↥K).map K.subtype).subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact ⟨e0.symm a, e0.symm b, fun h => hab (by simpa using congrArg e0 h)⟩
  obtain ⟨i, ⟨e⟩⟩ := hX K ((Subgroup.center ↥K).map K.subtype) hle hsimple hnab
  exact ⟨i, ⟨e0.symm.trans e⟩⟩

theorem ffConclusion_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : FFConclusion Y) : FFConclusion Y' := by
  rcases h with (⟨d, hd, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨d, hd, ⟨e'⟩⟩) | ⟨m, hm, ⟨e'⟩⟩
  · exact .inl (.inl ⟨d, hd, ⟨e.symm.trans e'⟩⟩)
  · exact .inl (.inr (.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩))
  · exact .inl (.inr (.inr ⟨d, hd, ⟨e.symm.trans e'⟩⟩))
  · exact .inr ⟨m, hm, ⟨e.symm.trans e'⟩⟩

theorem fixV_ne_bot_of_isPGroup' {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    [Nontrivial V] {P : Subgroup (MulAut V)} (hP : IsPGroup 2 ↥P) : fixV P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints V
  have hfix : Nat.card (MulAction.fixedPoints ↥P V) = Nat.card (fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one]; exact hV v⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  have heven : Nat.card V % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hmod
  have := hmod.symm
  unfold Nat.ModEq at this
  omega


theorem ffConclusion_of_component (hFF : FFModuleTheorem) (X : Type) [Group X] [Finite X]
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) X W)
    (hρ : Function.Injective ρ) (hK : CFSG.Open.IsKGroup X) (hO2 : CFSG.pCore 2 X = ⊥)
    (A : Subgroup X) (hAel : CFSG.IsElementaryAbelian 2 A)
    (hAbest : CFSG.RankThree.FFModules.IsBestOffender ρ A) (K : Subgroup X)
    (hKc : CFSG.Open.IsComponentOf K ⊤) (hKA : ⁅K, A⁆ ≠ ⊥) :
    FFConclusion (↥K ⧸ Subgroup.center ↥K) := by
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
  have hFFmod : IsFFModule H := ⟨E, hEH, hE0, hEel, hoff⟩
  exact ffConclusion_of_mulEquiv e (hFF V hV2 H L hHyp hFFmod)

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531
