module

public import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.ComponentClassification.Layer

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

abbrev Qt (Y : Type) [Group Y] : Type := Y ⧸ GLAPPrimeCore 2 Y

abbrev mkQ (Y : Type) [Group Y] : Y →* Qt Y := QuotientGroup.mk' (GLAPPrimeCore 2 Y)

@[expose] noncomputable def Ybar (Y : Type) [Group Y] : Subgroup (Qt Y) :=
  CFSG.ComponentClassification.Layer.subgroup (Qt Y) ⊔ CFSG.Open.pCore 2 (Qt Y)

abbrev preimQ {Y : Type} [Group Y] (T : Subgroup (Qt Y)) : Subgroup Y := T.comap (mkQ Y)

@[expose] noncomputable def qAct {Y : Type} [Group Y] {Γ : Type*} [Group Γ]
    (ρ : Γ →* MulAut Y) : Γ →* MulAut (Qt Y) :=
  quotAutHom (GLAPPrimeCore 2 Y) ρ (fun γ => glaPPrimeCore_map_iso 2 (ρ γ))

section Basic

variable {Y : Type} [Group Y] {Γ : Type*} [Group Γ] (ρ : Γ →* MulAut Y)

theorem qAct_mk (γ : Γ) (y : Y) : qAct ρ γ (mkQ Y y) = mkQ Y (ρ γ y) :=
  quotAutHom_mk (GLAPPrimeCore 2 Y) ρ (fun γ => glaPPrimeCore_map_iso 2 (ρ γ)) γ y

theorem mem_preimQ {T : Subgroup (Qt Y)} {y : Y} : y ∈ preimQ T ↔ mkQ Y y ∈ T := Iff.rfl

theorem ker_le_preimQ (T : Subgroup (Qt Y)) : GLAPPrimeCore 2 Y ≤ preimQ T := by
  intro y hy
  have : mkQ Y y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  rw [mem_preimQ, this]
  exact one_mem T

theorem map_mkQ_preimQ (T : Subgroup (Qt Y)) : (preimQ T).map (mkQ Y) = T :=
  Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) T

theorem map_preimQ {T : Subgroup (Qt Y)} (γ : Γ) (hT : T.map (qAct ρ γ).toMonoidHom = T) :
    (preimQ T).map (ρ γ).toMonoidHom = preimQ T := by
  have hmem : ∀ y : Y, (ρ γ)⁻¹ y ∈ preimQ T ↔ y ∈ preimQ T := by
    intro y
    have h1 : ∀ z : Qt Y, z ∈ T ↔ (qAct ρ γ) z ∈ T := by
      intro z
      constructor
      · intro hz
        have : (qAct ρ γ) z ∈ T.map (qAct ρ γ).toMonoidHom := ⟨z, hz, rfl⟩
        rwa [hT] at this
      · intro hz
        rw [← hT] at hz
        obtain ⟨w, hw, hwz⟩ := hz
        have : w = z := (qAct ρ γ).injective hwz
        rwa [← this]
    rw [mem_preimQ, mem_preimQ, h1, qAct_mk]
    simp
  ext y
  rw [Subgroup.mem_map_equiv]
  exact hmem y

theorem isComponentOf_map_qAct [Finite Y] {K : Subgroup (Qt Y)} (hK : IsComponentOf K ⊤)
    (γ : Γ) : IsComponentOf (K.map (qAct ρ γ).toMonoidHom) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (qAct ρ γ) K).2 hK

theorem map_qAct_Ybar [Finite Y] (γ : Γ) :
    (Ybar Y).map (qAct ρ γ).toMonoidHom = Ybar Y := by
  unfold Ybar
  rw [Subgroup.map_sup, CFSG.ComponentClassification.Layer.equiv_invariant (qAct ρ γ),
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (qAct ρ γ)]

theorem normal_Ybar [Finite Y] : (Ybar Y).Normal := by
  have := CFSG.ComponentClassification.Layer.normal (Qt Y)
  have : (CFSG.Open.pCore 2 (Qt Y)).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  unfold Ybar
  infer_instance

theorem normal_subgroupOf_preimQ {A B : Subgroup (Qt Y)} (hAB : A ≤ B)
    (h : (A.subgroupOf B).Normal) : ((preimQ A).subgroupOf (preimQ B)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : (⟨mkQ Y (n : Y), hAB hn⟩ : B) ∈ A.subgroupOf B := hn
  have key := h.conj_mem _ hn' ⟨mkQ Y (g : Y), g.2⟩
  rw [Subgroup.mem_subgroupOf] at key
  simpa using key

theorem le_ker_of_normal_odd [Finite Y] {K : Subgroup Y} {T : Subgroup (Qt Y)} (hT : T.Normal)
    (hKT : K ≤ preimQ T) (hKn : (K.subgroupOf (preimQ T)).Normal)
    (hodd : ¬ 2 ∣ Nat.card K) : K ≤ GLAPPrimeCore 2 Y := by
  have hn : (preimQ T).Normal := hT.comap (mkQ Y)
  have hKle : K ≤ GLAPPrimeCoreOf 2 (preimQ T) := by
    intro k hk
    refine ⟨⟨k, hKT hk⟩, ?_, rfl⟩
    have hcop : Nat.Coprime 2 (Nat.card (K.subgroupOf (preimQ T))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
    have h1 : K.subgroupOf (preimQ T) ≤ GLAPPrimeCore 2 (preimQ T) := le_sSup ⟨hKn, hcop⟩
    exact h1 (Subgroup.mem_subgroupOf.2 hk)
  have hle : GLAPPrimeCoreOf 2 (preimQ T) ≤ GLAPPrimeCoreOf 2 (⊤ : Subgroup Y) :=
    glaPPrimeCoreOf_le_of_normal Nat.prime_two le_top (hn.subgroupOf ⊤)
  have htop : GLAPPrimeCoreOf 2 (⊤ : Subgroup Y) = GLAPPrimeCore 2 Y :=
    glaPPrimeCore_map_iso 2 (Subgroup.topEquiv (G := Y))
  exact hKle.trans (htop ▸ hle)

end Basic

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
