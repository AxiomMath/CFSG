module

public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LieType.Chevalley.TwistMapFixed
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.CurtisTits.Recognition
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.Isogeny

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open scoped commutatorElement

theorem closure_xm_simple_eq_top {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*)
    [Field k] :
    Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : k),
      g = hV.xm k (Pi.single i 1) c ∨ g = hV.xm k (-Pi.single i 1) c} = ⊤ := by
  set S := Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : k),
    g = hV.xm k (Pi.single i 1) c ∨ g = hV.xm k (-Pi.single i 1) c}
  have hn : ∀ i, hV.nm k i ∈ S := fun i =>
    mul_mem (mul_mem (Subgroup.subset_closure ⟨i, _, Or.inl rfl⟩)
      (Subgroup.subset_closure ⟨i, _, Or.inr rfl⟩)) (Subgroup.subset_closure ⟨i, _, Or.inl rfl⟩)
  have hx : ∀ γ, IsRoot τ γ → ∀ c : k, hV.xm k γ c ∈ S := by
    intro γ hγ
    induction hγ with
    | basis j => exact fun c => Subgroup.subset_closure ⟨j, c, Or.inl rfl⟩
    | @reflect i v hv ih =>
      intro c
      obtain ⟨σ, hσ, h⟩ := hV.nm_conj_xm k hv i
      have e : hV.xm k (reflect τ i v) c = hV.nm k i * hV.xm k v (σ * c) * (hV.nm k i)⁻¹ := by
        rw [h, ← mul_assoc, hσ.mul_self, one_mul]
      rw [e]
      exact mul_mem (mul_mem (hn i) (ih _)) (inv_mem (hn i))
  rw [eq_top_iff, ← hV.iSup_rootGroup k]
  refine iSup₂_le fun γ hγ => ?_
  intro g hg
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hg
  exact hx γ hγ c

theorem commutatorElement_mul_mul_of_mem_center {G : Type*} [Group G] (a b : G) {z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : ∀ g, z * g * z⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
  have h2 : ∀ g, w * g * w⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hw g, mul_inv_cancel_right]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [h1]; group
    _ = ⁅a, b⁆ := by rw [h2, commutatorElement_def]

section Twist

variable {k : Type} [Field k] [Finite k] (θ : k →+* k)

omit [Finite k] in
theorem eltElement_simpleRoot_E6 (i : Fin (Tag.rank .E6)) (c : k) :
    (rootOperatorFamily .E6).eltElement (simpleRoot .E6 i) c = xElement i c :=
  Subtype.ext ((rootOperatorFamily .E6).eltUnit_simple i c)

omit [Finite k] in
theorem eltElement_neg_simpleRoot_E6 (i : Fin (Tag.rank .E6)) (c : k) :
    (rootOperatorFamily .E6).eltElement (-simpleRoot .E6 i) c = yElement i c :=
  Subtype.ext ((rootOperatorFamily .E6).eltUnit_neg_simple i c)

variable (k) in
@[expose] def e6IsogenyT : ↥(e6Data_valid.minGroup k) →* ↥(adjointGroup TwistTag.E6.tag k) :=
  e6Isogeny k

theorem e6IsogenyT_surjective : Function.Surjective (e6IsogenyT k) :=
  e6Isogeny_surjective k

theorem e6IsogenyT_sigma (g : ↥(e6Data_valid.minGroup k)) :
    e6IsogenyT k (sigma k θ g) = twistC .E6 k θ (e6IsogenyT k g) := by
  have h : (e6IsogenyT k).comp (sigma k θ) = (twistC .E6 k θ).comp (e6IsogenyT k) := by
    refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid k) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, sigma_xm_single]
      change e6Isogeny k _ = twistC .E6 k θ (e6Isogeny k _)
      rw [e6Isogeny_xm_single, e6Isogeny_xm_single, eltElement_simpleRoot_E6,
        eltElement_simpleRoot_E6]
      exact (twistC_xElement .E6 k θ i c).symm
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, sigma_xm_neg_single]
      change e6Isogeny k _ = twistC .E6 k θ (e6Isogeny k _)
      rw [e6Isogeny_xm_neg_single, e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6,
        eltElement_neg_simpleRoot_E6]
      exact (twistC_yElement .E6 k θ i c).symm
  exact DFunLike.congr_fun h g

theorem e6Isogeny_sigma (g : ↥(e6Data_valid.minGroup k)) :
    e6Isogeny k (sigma k θ g) = twistC .E6 k θ (e6Isogeny k g) :=
  e6IsogenyT_sigma θ g

theorem e6IsogenyT_mem_twistedFixedGroup {g : ↥(e6Data_valid.minGroup k)}
    (hg : g ∈ fixedGroup k θ) :
    ((e6IsogenyT k g : ↥(adjointGroup TwistTag.E6.tag k)) : ModGL TwistTag.E6.tag k) ∈
      twistedFixedGroup .E6 k θ :=
  (coe_mem_twistedFixedGroup_iff .E6 k θ (e6IsogenyT k g)).2 (by
    rw [← e6IsogenyT_sigma θ g, (mem_fixedGroup θ).1 hg])

@[expose] def e6IsogenyFixed : ↥(fixedGroup k θ) →* ModGL TwistTag.E6.tag k :=
  (adjointGroup TwistTag.E6.tag k).subtype.comp ((e6IsogenyT k).comp (fixedGroup k θ).subtype)

theorem e6IsogenyFixed_apply (g : ↥(fixedGroup k θ)) :
    e6IsogenyFixed θ g =
      ((e6IsogenyT k g : ↥(adjointGroup TwistTag.E6.tag k)) : ModGL TwistTag.E6.tag k) :=
  rfl

variable (k) in
theorem ker_e6IsogenyT_le_center : (e6IsogenyT k).ker ≤ Subgroup.center _ :=
  CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 k) (e6Isogeny_ne_one k)

theorem range_e6IsogenyFixed (hθ : ∀ c, θ (θ c) = c) (hk : 4 ≤ Nat.card k) :
    (e6IsogenyFixed θ).range = ⁅twistedFixedGroup .E6 k θ, twistedFixedGroup .E6 k θ⁆ := by
  refine le_antisymm ?_ ?_
  ·
    have hle : (⊤ : Subgroup ↥(fixedGroup k θ)).map (e6IsogenyFixed θ) ≤
        twistedFixedGroup .E6 k θ := by
      rintro _ ⟨g, -, rfl⟩
      exact e6IsogenyT_mem_twistedFixedGroup θ g.2
    rw [MonoidHom.range_eq_map,
      ← (fixedGroup_isPerfect_of_four_le_card θ hθ hk).commutator_eq_top, commutator_def,
      Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  · rw [Subgroup.commutator_le]
    intro h₁ hh₁ h₂ hh₂
    have lift : ∀ h ∈ twistedFixedGroup .E6 k θ, ∃ g : ↥(e6Data_valid.minGroup k),
        ((e6IsogenyT k g : ↥(adjointGroup TwistTag.E6.tag k)) : ModGL TwistTag.E6.tag k) = h ∧
          g⁻¹ * sigma k θ g ∈ Subgroup.center _ := by
      intro h hh
      obtain ⟨g, hg⟩ := e6IsogenyT_surjective (k := k)
        ⟨h, twistedFixedGroup_le_adjointGroup .E6 k θ hh⟩
      refine ⟨g, by rw [hg], ker_e6IsogenyT_le_center k ?_⟩
      have hF := (coe_mem_twistedFixedGroup_iff .E6 k θ
        ⟨h, twistedFixedGroup_le_adjointGroup .E6 k θ hh⟩).1 hh
      rw [MonoidHom.mem_ker, map_mul, map_inv, e6IsogenyT_sigma, hg, hF, inv_mul_cancel]
    obtain ⟨g₁, rfl, hz₁⟩ := lift h₁ hh₁
    obtain ⟨g₂, rfl, hz₂⟩ := lift h₂ hh₂
    have hfix : ⁅g₁, g₂⁆ ∈ fixedGroup k θ := by
      rw [mem_fixedGroup, map_commutatorElement, ← mul_inv_cancel_left g₁ (sigma k θ g₁),
        ← mul_inv_cancel_left g₂ (sigma k θ g₂)]
      exact commutatorElement_mul_mul_of_mem_center g₁ g₂ hz₁ hz₂
    refine ⟨⟨_, hfix⟩, ?_⟩
    rw [e6IsogenyFixed_apply, map_commutatorElement]
    rfl

end Twist

variable (p f : ℕ) [Fact p.Prime]

theorem four_le_card_galoisField (hf : 1 ≤ f) : 4 ≤ Nat.card (GaloisField p (2 * f)) := by
  rw [GaloisField.card p (2 * f) (by omega), pow_mul]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 : 4 ≤ p ^ 2 := by nlinarith
  calc 4 ≤ p ^ 2 := h1
    _ ≤ (p ^ 2) ^ f := Nat.le_self_pow (by omega) _

theorem range_e6IsogenyFixed_frobQ (hf : 1 ≤ f) :
    (e6IsogenyFixed (frobQ p f)).range =
      ⁅twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f),
        twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f)⁆ :=
  range_e6IsogenyFixed (frobQ p f) (frobQ_frobQ p f hf) (four_le_card_galoisField p f hf)

@[expose] def twistedE6Isogeny (hf : 1 ≤ f) :
    twistedE6Group p f →*
      ↥⁅twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f),
        twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f)⁆ :=
  (e6IsogenyFixed (frobQ p f)).codRestrict _ fun g => by
    rw [← range_e6IsogenyFixed_frobQ p f hf]
    exact ⟨g, rfl⟩

theorem coe_twistedE6Isogeny (hf : 1 ≤ f) (g : twistedE6Group p f) :
    ((twistedE6Isogeny p f hf g : ↥⁅twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f),
        twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f)⁆) :
          ModGL TwistTag.E6.tag (GaloisField p (2 * f))) =
      ((e6IsogenyT (GaloisField p (2 * f)) g :
          ↥(adjointGroup TwistTag.E6.tag (GaloisField p (2 * f)))) :
        ModGL TwistTag.E6.tag (GaloisField p (2 * f))) :=
  rfl

theorem twistedE6Isogeny_surjective (hf : 1 ≤ f) :
    Function.Surjective (twistedE6Isogeny p f hf) := by
  rintro ⟨y, hy⟩
  rw [← range_e6IsogenyFixed_frobQ p f hf] at hy
  obtain ⟨g, rfl⟩ := hy
  exact ⟨g, rfl⟩

theorem twistedE6Isogeny_ne_one (hf : 1 ≤ f) : ∃ g, twistedE6Isogeny p f hf g ≠ 1 := by
  set i : Fin (Tag.rank .E6) := ⟨1, by decide⟩
  have hfix : e6Data_valid.xm (GaloisField p (2 * f)) (Pi.single i 1) 1 ∈
      fixedGroup (GaloisField p (2 * f)) (frobQ p f) := by
    rw [mem_fixedGroup, sigma_xm_single, map_one]
    rfl
  refine ⟨⟨_, hfix⟩, fun h => ?_⟩
  have h' := congrArg (fun y : ↥⁅twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f),
    twistedFixedGroup .E6 (GaloisField p (2 * f)) (frobQ p f)⁆ =>
      (y : ModGL TwistTag.E6.tag (GaloisField p (2 * f)))) h
  simp only [coe_twistedE6Isogeny, OneMemClass.coe_one] at h'
  exact e6Isogeny_xm_single_one_ne_one _ i (Subtype.ext h')

end CFSG.LieType.Steinberg.Isogeny
