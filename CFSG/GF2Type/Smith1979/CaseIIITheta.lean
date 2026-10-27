module

public import CFSG.GF2Type.Smith1979.SixStage
public import CFSG.GF2Type.Smith1979.CaseIIIFix
public import CFSG.LargeExtraspecial.S10EightA
public import CFSG.LargeExtraspecial.S10ThreeA
public import CFSG.LargeExtraspecial.S14W4LocDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14 CFSG.GF2Type.Smith1980Orth
  CFSG.LargeExtraspecial.S10

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem noPGL25_of_width_six [IsSimpleGroup G] (I : TimInputs) (hw : S.width = 6) (hirr : ¬ S.IsReducible)
    (hnoAll : S11.NoA2All S) (g : G) : NoPGL25 S g := by
  intro H hNo C τ hτ hτ1 hVQ hR hLN hP
  have hSt : Stage S g τ := ⟨by omega, H, hnoAll, C, hirr, hτ, hτ1, hR, hLN⟩
  obtain ⟨c, hocc, -⟩ := exists_config I.hCorB I.hFacts I.hCE I.h83 I.hRes I.h9 hSt
    ⟨H, C, hτ, hτ1, hVQ, Or.inr (Or.inr (Or.inr hP))⟩
  have h6 : (6 : ℕ) = c.width := hw ▸ hocc.2.1
  cases c <;> simp [Config.width] at h6

theorem exists_dec108_of_width_six (I : TimInputs) {g : G} {t : S.O} (X : Hyp10 S g t)
    (hw : S.width = 6) : ∃ Xb Yb : Subgroup S.O, Dec108 X Xb Yb ∧ Nbar S g t ≤ Xb := by
  obtain ⟨Xb, Yb, D, hN, hW, y, hyY, hyL, hyN⟩ := exists_dirDec_of_width_six I.hCE X hw
  exact ⟨Xb, Yb, ⟨D, hW, y, hyY, hyL, hyN⟩, hN⟩

theorem exists_theta (I : TimInputs) {g : G} {t : S.O} {X : Hyp10 S g t} {Xb Yb : Subgroup S.O}
    (D : Dec108 X Xb Yb) :
    ∃ θ ∈ ⁅Yb, Yb⁆, θ ≠ 1 ∧ θ ^ 3 = 1 ∧ θ ∈ S.Mbar ∧
      (∀ v, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0) ∧ ⁅Yb, Yb⁆ = zpowers θ := by
  obtain ⟨θ, hθ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 D.dec.commutator_ne_bot
  have hθ3 : (θ : S.O) ^ 3 = 1 := ((D.dec.mem_commutator_iff).1 θ.2).2
  have hθ1' : (θ : S.O) ≠ 1 := fun h => hθ1 (Subtype.ext h)
  have hord : orderOf (θ : S.O) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hθ3 hθ1'
  have hz : ⁅Yb, Yb⁆ = zpowers (θ : S.O) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 θ.2) ?_
    rw [D.dec.card_commutator, Nat.card_zpowers, hord]
  refine ⟨θ, θ.2, hθ1', hθ3, ?_, ?_, hz⟩
  · exact Rbar_le_Mbar (D.dec.le_Rbar_right ((D.dec.mem_commutator_iff).1 θ.2).1)
  · intro v hv
    refine timmesfeld_10_3_alpha I.hCE X D.dec fun y hy => ?_
    rw [hz] at hy
    have hle : zpowers (θ : S.O) ≤ MulAction.stabilizer S.O v :=
      zpowers_le.2 (show (θ : S.O) • v = v from hv)
    exact hle hy

theorem finrank_commSpace_of_inverts {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 12) {s θ : V ≃ₗ[ZMod 2] V}
    (hs2 : ∀ v, s (s v) = v) (hinv : ∀ v, s (θ v) = θ (θ (s v)))
    (hθ3 : ∀ v, θ (θ (θ v)) = v) (hfix : ∀ v, θ v = v → v = 0) :
    finrank (ZMod 2) (commSpace s) = 6 := by
  set F := fixSpace s with hF
  have hdisj : F ⊓ F.map (θ : V →ₗ[ZMod 2] V) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, ⟨w, hw, rfl⟩⟩
    rw [SetLike.mem_coe, mem_fixSpace] at hv hw
    have h1 : θ (θ w) = θ w := by
      have := hinv w
      rw [hw] at this
      change s (θ w) = θ w at hv
      rw [hv] at this
      exact this.symm
    have h2 : θ w = w := by
      have := congrArg θ h1
      rw [hθ3] at this
      exact h1.symm.trans this.symm
    rw [Submodule.mem_bot]
    change θ w = 0
    rw [h2]
    exact hfix w h2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq F (F.map (θ : V →ₗ[ZMod 2] V))
  rw [hdisj, finrank_bot, add_zero, LinearEquiv.finrank_map_eq] at hsum
  have hle := Submodule.finrank_le (F ⊔ F.map (θ : V →ₗ[ZMod 2] V))
  rw [hV] at hle
  have hcf : commSpace s ≤ F := by
    intro w hw
    obtain ⟨v, rfl⟩ := mem_commSpace.1 hw
    rw [hF, mem_fixSpace, map_sub, hs2]
    have hneg : ∀ x : V, -x = x := fun x => by
      rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [show v - s v = -(s v - v) by abel, hneg]
  have h1 := Submodule.finrank_mono hcf
  have h2 := finrank_commSpace_add_finrank_fixSpace s
  rw [hV, ← hF] at h2
  omega

theorem finrank_Vt_le_one_of_Rbar_eq {g : G} (H : Hyp4 S g) {s : S.O}
    (hR : Rbar S g s = S.Lbar g) : finrank (ZMod 2) (Vt S g s) ≤ 1 := by
  have hle : Vt S g s ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, hsh, rfl⟩
    have h1 : S.Lbar ((h : G) * g) ≤ S.Lbar g := hR ▸ Lbar_mul_le_Rbar hsh
    have hcard : Nat.card (S.Lbar ((h : G) * g)) = Nat.card (S.Lbar g) := by
      rw [Lbar_mul S h g, Subgroup.card_map_of_injective (MulAut.conj (S.ρ h)).injective]
    have h2 : S.Lbar ((h : G) * g) = S.Lbar (((1 : S.M) : G) * g) := by
      rw [OneMemClass.coe_one, one_mul]
      exact Subgroup.eq_of_le_of_card_ge h1 hcard.ge
    have h3 := cl_eq_of_Lbar_eq H h2
    rw [OneMemClass.coe_one, one_mul] at h3
    rw [SetLike.mem_coe, show (h : G) * g * S.z * ((h : G) * g)⁻¹ = (h : G) * g * S.z *
      ((h : G) * g)⁻¹ from rfl, h3]
    exact Submodule.mem_span_singleton_self _
  refine (Submodule.finrank_mono hle).trans ?_
  have := finrank_span_le_card (R := ZMod 2) ({S.cl (g * S.z * g⁻¹)} : Set S.Qt)
  simpa using this

theorem finrank_Vt_le_two_of_inverts [IsSimpleGroup G] (I : TimInputs) (hw : S.width = 6)
    (hirr : ¬ S.IsReducible) (hnoAll : S11.NoA2All S) {g : G} (H : Hyp4 S g) (C : Cons311 S g)
    (hI : ∀ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      ¬ (OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = 6 ∧ Nbar S g t = zpowers t))
    (hII : ∀ (t : S.O) (ht : t ∈ S.Lbar g), t ≠ 1 →
      ¬ (LinCase S g ht ∧ finrank (ZMod 2) (Vt S g t) = 3))
    {θ : S.O} (hθ1 : θ ≠ 1) (hθ3 : θ ^ 3 = 1)
    (hfix : ∀ v, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0) {s : S.O} (hs : s ∈ S.Lbar g)
    (hinv : s * θ = θ⁻¹ * s) : finrank (ZMod 2) (Vt S g s) ≤ 2 := by
  have hθinv : θ⁻¹ = θ * θ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hθ3, pow_three]
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hθ1
    rw [one_mul, mul_one] at hinv
    have h2 : θ * θ = 1 := by
      calc θ * θ = θ * θ⁻¹ := by rw [← hinv]
        _ = 1 := mul_inv_cancel θ
    calc θ = θ ^ 3 * (θ * θ)⁻¹ := by rw [pow_three]; group
      _ = 1 := by rw [hθ3, h2, inv_one, one_mul]
  rcases classify_six I hw hirr hnoAll H C hs hs1 with hR | ⟨hL, h2 | h3⟩ | hX |
    ⟨hVQ, hΩ, h6, hN⟩
  · exact (finrank_Vt_le_one_of_Rbar_eq H hR).trans (by norm_num)
  · omega
  · exact absurd ⟨hL, h3⟩ (hII s hs hs1)
  · exfalso
    have hc := (commSpace_t_eq H C hs hs1 hX.hVQ).1
    have hss : ∀ v, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := fun v => by
      have := LinearEquiv.congr_fun (congrArg Subtype.val (mul_self_of_mem_Lbar S H.conj_mem hs)) v
      simpa using this
    have hsθ : ∀ v, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) :=
      fun v => by
        have := LinearEquiv.congr_fun (congrArg Subtype.val hinv) v
        rw [hθinv] at this
        simpa [LinearEquiv.mul_apply] using this
    have hθθθ : ∀ v, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = v := fun v => by
      have := LinearEquiv.congr_fun (congrArg Subtype.val hθ3) v
      simpa [pow_succ, LinearEquiv.mul_apply] using this
    have hdim : finrank (ZMod 2) S.Qt = 12 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
    have h6' := finrank_commSpace_of_inverts hdim hss hsθ hθθθ hfix
    rw [hc, hX.h4] at h6'
    omega
  · exact absurd ⟨hΩ, h6, hN⟩ (hI s hs hs1 hVQ)

end CFSG.GF2Type.Smith1979
