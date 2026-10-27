module

public import CFSG.LargeExtraspecial.AS35ZSJ
public import CFSG.LargeExtraspecial.AS35ZSNtC
public import CFSG.LargeExtraspecial.AS35ZNEnd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

namespace AS35ZS

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V}

theorem ZSHyp.exists_endo (h : ZSHyp n q ρ) :
    ∃ f : V →ₗ[ZMod 2] V, (∀ g : PG n, ∀ v, ρ g (f v) = f (ρ g v)) ∧ f ≠ 0 ∧ f ≠ 1 := by
  obtain ⟨J, hJρ, hJo⟩ := h.exists_J
  obtain ⟨x, a, ha, hne⟩ := h.exists_oLine_ne
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (map_zero _)
  refine ⟨J, hJρ, fun h0 => ?_, fun h1 => ?_⟩
  · have e := hJo x a ha
    rw [h0, LinearMap.zero_apply] at e
    exact h.oLine_ne_zero x.2.1 x.2.2 ha ha0 e.symm
  · have e := hJo x a ha
    rw [h1, Module.End.one_apply] at e
    exact hne e.symm

end AS35ZS

namespace AS35ZS

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem commute_of_mem_center {L : Subgroup (V ≃ₗ[ZMod 2] V)} {z : L}
    (hz : z ∈ Subgroup.center L) : ∀ g ∈ L, ∀ v, g (((z : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) v) =
      ((z : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) (g v) := by
  intro g hg v
  have e := Subgroup.mem_center_iff.1 hz ⟨g, hg⟩
  have e2 := congrArg (fun w : L => (w : V ≃ₗ[ZMod 2] V) v) e
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at e2
  exact e2

theorem center_eq_bot_of_endo {L : Subgroup (V ≃ₗ[ZMod 2] V)} [Nontrivial V]
    (hcon : ∀ f : V →ₗ[ZMod 2] V, (∀ g ∈ L, ∀ v, g (f v) = f (g v)) → f ≠ 0 → f = 1) :
    Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hf := hcon _ (commute_of_mem_center hz) (fun h0 => by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have := LinearMap.congr_fun h0 v
    simp only [LinearEquiv.coe_coe, LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at this
    exact hv this)
  apply Subtype.ext
  ext v
  exact LinearMap.congr_fun hf v

end AS35ZS

namespace S14

open AS35ZS

theorem suModuleEndInput : SUModuleEndInput := by
  intro V _ _ _ q hq n hn hfin L D hDL hcl hA hiso hψ hirr
  by_contra hcon
  push Not at hcon
  obtain ⟨ψ, hψD⟩ := hψ
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hcent := center_eq_bot_of_endo hcon
  set e₁ : L ⧸ Subgroup.center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hcent).trans QuotientGroup.quotientBot with he₁
  set φ : PG n ≃* L := ψ.symm.trans e₁ with hφ
  set ρ : PG n →* (V ≃ₗ[ZMod 2] V) := L.subtype.comp φ.toMonoidHom with hρ
  have hρφ : ∀ g : L, ρ (φ.symm g) = g := fun g => by
    simp [hρ]
  have hφψ : ∀ x : L, φ (ψ (QuotientGroup.mk x)) = x := fun x => by
    rw [hφ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := by
    by_contra hD
    rw [Set.not_nonempty_iff_eq_empty] at hD
    have hL : L = ⊥ := by rw [← hcl, hD, Subgroup.closure_empty]
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    rcases hirr ((ZMod 2) ∙ v) (fun g hg w hw => by
        rw [hL, Subgroup.mem_bot] at hg
        rw [hg]
        exact hw) with h0 | htop
    · exact hv ((Submodule.span_singleton_eq_bot).1 h0)
    · have h1 := finrank_span_singleton (K := ZMod 2) hv
      rw [htop, finrank_top] at h1
      omega
  have hρt : ρ (ψ (QuotientGroup.mk ⟨d₀, hDL hd₀⟩)) = d₀ := by
    simp only [hρ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hφψ,
      Subgroup.coe_subtype]
  have hA' : ∀ d ∈ DG n, IsTypeA q (ρ d) 2 := by
    intro d hd
    obtain ⟨w, hw0, hw, hwt⟩ := hψD d₀ hd₀
    rw [DG_eq_isConj (by omega) hw0 hw] at hd
    obtain ⟨c, rfl⟩ := isConj_iff.1 hd
    rw [map_mul, map_mul, map_inv, hwt, hρt]
    refine isTypeA_conj (hA d₀ hd₀) (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ?_)
    exact hiso _ (φ c).2
  have h : ZSHyp n q ρ :=
    { four_le := hn
      finrank_eq := hfin
      a2 := ⟨hq, fun x y hxy => φ.injective (Subtype.ext hxy), fun x v => hiso _ (φ x).2 v, hA'⟩
      irred := fun W hW => hirr W fun g hg w hw => by
        have := hW (φ.symm ⟨g, hg⟩) w hw
        rwa [hρφ] at this }
  obtain ⟨f, hfρ, hf0, hf1⟩ := h.exists_endo
  exact hf1 (hcon f (fun g hg v => by
    have := hfρ (φ.symm ⟨g, hg⟩) v
    rwa [hρφ] at this) hf0)

end S14

end CFSG.LargeExtraspecial
