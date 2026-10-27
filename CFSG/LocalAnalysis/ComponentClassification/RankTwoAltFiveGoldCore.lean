module

public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinal

public section

open Subgroup CFSG.Open

namespace CFSG.ComponentClassification.RankTwoAltFive

theorem goldschmidtOddCore_eq_bot_of_mulEquiv {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : goldschmidtOddCore Z = ⊥) : goldschmidtOddCore Y = ⊥ := by
  rw [eq_bot_iff]
  refine sSup_le fun N hN => ?_
  have hle : N.map e.toMonoidHom ≤ goldschmidtOddCore Z :=
    le_sSup ⟨hN.1.map _ e.surjective, by rw [card_map_of_injective e.injective]; exact hN.2⟩
  rw [h, le_bot_iff] at hle
  intro y hy
  have hy' : e y ∈ N.map e.toMonoidHom := mem_map_of_mem e.toMonoidHom hy
  rw [hle, mem_bot] at hy'
  rw [mem_bot]
  exact e.injective (by rw [hy', map_one])

theorem coreStatement_of_goldschmidtTheoremA (hGA : Asc76X.GoldschmidtTheoremA) :
    Goldschmidt.CoreStatement := by
  intro Z _ _ S A hAS hAab hAcl htop hO
  obtain ⟨h1, h2, h3⟩ := hGA Z S A hAS hAab hAcl
  set M := normalClosure (A : Set Z) with hMdef
  let e₁ : M ≃* Z := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hOM : goldschmidtOddCore M = ⊥ := goldschmidtOddCore_eq_bot_of_mulEquiv e₁ hO
  let e₂ : M ⧸ goldschmidtOddCore M ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq hOM).trans QuotientGroup.quotientBot
  let ψ : M ⧸ goldschmidtOddCore M ≃* Z := e₂.trans e₁
  have hψ : ∀ m : M, ψ (QuotientGroup.mk' _ m) = (m : Z) := fun m => rfl
  have hmem : ∀ z : Z, z ∈ M := fun z => htop ▸ mem_top z
  have himg : ∀ B : Subgroup Z,
      ((B.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M))).map ψ.toMonoidHom = B := by
    intro B
    ext z
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      change ψ (QuotientGroup.mk' _ m) ∈ B
      rw [hψ]
      exact mem_subgroupOf.mp hm
    · intro hz
      exact ⟨_, ⟨⟨z, hmem z⟩, mem_subgroupOf.mpr hz, rfl⟩, rfl⟩
  have hP := Goldschmidt.SStarTransport.pCore_map_mulEquiv 2 ψ
  have hL := Goldschmidt.SStarTransport.goldschmidtLayer_map_mulEquiv' ψ
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (Subgroup.map ψ.toMonoidHom) h1
    rwa [Subgroup.map_sup, hP, hL, Subgroup.map_top_of_surjective _ ψ.surjective] at this
  · have := congrArg (Subgroup.map ψ.toMonoidHom) h2
    rw [himg, Subgroup.map_sup, hP, MonoidHom.map_closure] at this
    rw [this]
    congr 2
    ext t
    constructor
    · rintro ⟨y, ⟨hyT, hy2⟩, rfl⟩
      refine ⟨?_, by rw [← map_pow]; change ψ (y ^ 2) = 1; rw [hy2, map_one]⟩
      have h := mem_map_of_mem ψ.toMonoidHom hyT
      rwa [Subgroup.map_inf_eq _ _ _ ψ.injective, himg, hL] at h
    · rintro ⟨htT, ht2⟩
      refine ⟨ψ.symm t, ⟨?_, ?_⟩, by simp⟩
      · have h : t ∈ (((S : Subgroup Z).subgroupOf M).map
            (QuotientGroup.mk' (goldschmidtOddCore M)) ⊓
            goldschmidtLayer (M ⧸ goldschmidtOddCore M)).map ψ.toMonoidHom := by
          rwa [Subgroup.map_inf_eq _ _ _ ψ.injective, himg, hL]
        obtain ⟨y, hy, hyt⟩ := h
        rwa [← hyt, show ψ.symm (ψ.toMonoidHom y) = y from ψ.symm_apply_apply y]
      · apply ψ.injective
        rw [map_pow, MulEquiv.apply_symm_apply, ht2, map_one]
  · intro K hK
    have hK' := Goldschmidt.SStarTransport.isComponentOf_top_map_mulEquiv ψ.symm hK
    have e : ↥K ≃* ↥(K.map ψ.symm.toMonoidHom) :=
      K.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective
    exact Asc76X.goldschmidtSimpleType_of_mulEquiv
      (Goldschmidt.SStarTransport.quotientCenterEquiv e) (h3 _ hK')

end CFSG.ComponentClassification.RankTwoAltFive
