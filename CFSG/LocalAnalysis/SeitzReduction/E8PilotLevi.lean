module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviHom
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction.EPilot

section Isogeny

variable {K : Type} [Field K] [CharP K 2]


theorem coe_xPar_eq_pinnedX_E7 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    ((xPar (rootOperatorFamily .E7) γ c : adjointGroup .E7 K) : ModGL .E7 K) =
      pinnedX .E7 K γ c := by
  rw [(rootOperatorFamily .E7).pinnedX_eq_eltUnit K hγ,
    intCast_eq_one_of_charTwo ((rootOperatorFamily .E7).pinnedFamilySign_eq γ), one_mul,
    xPar_of_isRoot hγ]
  rfl

variable [Finite K]

theorem e7Isogeny_injective_of_charTwo : Function.Injective (e7Isogeny K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← center_minGroup_e7_eq_bot (K := K)]
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 K) (exists_e7Isogeny_ne_one K)

variable (K) in
@[expose] noncomputable def e7MinEquivAdjoint :
    ↥(e7Data_valid.minGroup K) ≃* ↥(adjointGroup .E7 K) :=
  MulEquiv.ofBijective (e7Isogeny K) ⟨e7Isogeny_injective_of_charTwo, e7Isogeny_surjective K⟩

theorem e7MinEquivAdjoint_apply (g : e7Data_valid.minGroup K) :
    e7MinEquivAdjoint K g = e7Isogeny K g :=
  rfl

theorem coe_e7Isogeny_xm {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    ((e7Isogeny K (e7Data_valid.xm K γ c) : adjointGroup .E7 K) : ModGL .E7 K) =
      pinnedX .E7 K γ c := by
  rw [e7Isogeny_xm, intCast_eq_one_of_charTwo (e7Eps_eq_one_or γ), one_mul,
    coe_xPar_eq_pinnedX_E7 hγ]

end Isogeny

section Equiv


variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def e7LeviEquiv : ↥(e7Levi K) ≃* ↥(adjointGroup .E7 K) :=
  (e7MinEquivLevi K).symm.trans (e7MinEquivAdjoint K)

variable {K}

theorem e7LeviEquiv_e7LeviPar {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    e7LeviEquiv K ⟨e7LeviPar K γ c, e7LeviPar_mem_e7Levi hγ c⟩ =
      ⟨pinnedX .E7 K γ c, pinnedX_mem_adjointGroup γ c⟩ := by
  apply Subtype.ext
  rw [e7LeviEquiv, MulEquiv.trans_apply, ← e7MinEquivLevi_xm hγ c, MulEquiv.symm_apply_apply,
    e7MinEquivAdjoint_apply, coe_e7Isogeny_xm hγ]

theorem coe_e7LeviEquiv_of_coe_eq_pinnedX {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    {c : K} {g : e7Levi K}
    (hg : ((g : adjointGroup .E8 K) : ModGL .E8 K) = pinnedX .E8 K (e7Embed γ) c) :
    ((e7LeviEquiv K g : adjointGroup .E7 K) : ModGL .E7 K) = pinnedX .E7 K γ c := by
  have hg' : g = ⟨e7LeviPar K γ c, e7LeviPar_mem_e7Levi hγ c⟩ :=
    Subtype.ext (Subtype.ext hg)
  rw [hg', e7LeviEquiv_e7LeviPar hγ c]

theorem e7LeviEquiv_symm_pinnedX {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    (e7LeviEquiv K).symm ⟨pinnedX .E7 K γ c, pinnedX_mem_adjointGroup γ c⟩ =
      ⟨e7LeviPar K γ c, e7LeviPar_mem_e7Levi hγ c⟩ := by
  rw [MulEquiv.symm_apply_eq, e7LeviEquiv_e7LeviPar hγ c]

theorem coe_e7LeviEquiv_symm_pinnedX {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    ((((e7LeviEquiv K).symm ⟨pinnedX .E7 K γ c, pinnedX_mem_adjointGroup γ c⟩ : e7Levi K) :
        adjointGroup .E8 K) : ModGL .E8 K) = pinnedX .E8 K (e7Embed γ) c := by
  rw [e7LeviEquiv_symm_pinnedX hγ c]
  rfl

variable (K) in
theorem exists_perpLevi_mulEquiv_adjointGroup_E7 :
    ∃ e : ↥((rootSpan .E8 K (perpRoots .E8)).subgroupOf (adjointGroup .E8 K)) ≃*
        ↥(adjointGroup .E7 K),
      ∀ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ → ∀ (c : K)
        (g : (rootSpan .E8 K (perpRoots .E8)).subgroupOf (adjointGroup .E8 K)),
        ((g : adjointGroup .E8 K) : ModGL .E8 K) = pinnedX .E8 K (e7Embed γ) c →
          ((e g : adjointGroup .E7 K) : ModGL .E7 K) = pinnedX .E7 K γ c :=
  ⟨e7LeviEquiv K, fun _ hγ _ _ hg => coe_e7LeviEquiv_of_coe_eq_pinnedX hγ hg⟩

theorem isQuasisimple_e7Levi : CFSG.IsQuasisimple (e7Levi K) :=
  CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := (e7MinEquivLevi K).toMonoidHom)
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 K) (e7MinEquivLevi K).surjective (by
      obtain ⟨g, hg⟩ := exists_e7ToE8_ne_one (K := K)
      refine ⟨g, fun h => hg ?_⟩
      rw [← coe_e7MinEquivLevi]
      exact congrArg Subtype.val h)

theorem center_e7Levi_eq_bot : center (e7Levi K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : (e7LeviEquiv K) z ∈ center (adjointGroup .E7 K) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := (e7LeviEquiv K).surjective g
    rw [← map_mul, ← map_mul, (mem_center_iff.1 hz) y]
  rw [center_adjointGroup_eq_bot, mem_bot] at hz'
  rw [mem_bot]
  exact (e7LeviEquiv K).injective (hz'.trans (map_one _).symm)

theorem isQuasisimple_open_e7Levi : CFSG.Open.IsQuasisimple (e7Levi K) :=
  ⟨(isQuasisimple_e7Levi (K := K)).1.commutator_eq_top, (isQuasisimple_e7Levi (K := K)).2.1⟩

@[expose] noncomputable def e7LeviEquivAdjointQuotient : ↥(e7Levi K) ≃* AdjointQuotient .E7 K :=
  (e7LeviEquiv K).trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
    QuotientGroup.quotientBot).symm

theorem chevalleyExceptionalModel_e7Levi {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    ChevalleyExceptionalModel (e7Levi K) .E7 2 f :=
  ⟨⟨Nat.prime_two, hf, rfl⟩, K, inferInstance, inferInstance, hK, ⟨e7LeviEquivAdjointQuotient⟩⟩

theorem lieModel_e7Levi {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    LieModel (e7Levi K) .E7 0 2 f :=
  Or.inr (Or.inl ⟨rfl, by decide, chevalleyExceptionalModel_e7Levi hf hK⟩)

theorem isSimpleGroup_e7Levi : IsSimpleGroup (e7Levi K) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  exact (CFSG.LieType.Simplicity.fam_e7_simplicity _ 2 n
    (chevalleyExceptionalModel_e7Levi n.pos hK)).2

end Equiv

end CFSG.SeitzReduction.E8Pilot
