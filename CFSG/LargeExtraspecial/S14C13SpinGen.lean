module

public import CFSG.LargeExtraspecial.S14C13Five
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.OrthoF2SpRadical
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : LinearMap.BilinForm (ZMod 2) V}

theorem lin_apply_inv (g : V ≃ₗ[ZMod 2] V) (x : V) : g (g⁻¹ x) = x := g.apply_symm_apply x

theorem lin_inv_apply (g : V ≃ₗ[ZMod 2] V) (x : V) : g⁻¹ (g x) = x := g.symm_apply_apply x

theorem conj_mem_spPointRadical {g t : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup f) {a : V} (ht : t ∈ spPointRadical f a) :
    g * t * g⁻¹ ∈ spPointRadical f (g a) := by
  obtain ⟨hti, hta, ht1, ht2⟩ := mem_spPointRadical.mp ht
  have hgi := TauCeti.BilinForm.mem_isometryGroup_iff.mp hg
  have hgi' := TauCeti.BilinForm.mem_isometryGroup_iff.mp (inv_mem hg)
  refine mem_spPointRadical.mpr ⟨mul_mem (mul_mem hg hti) (inv_mem hg), ?_, fun x hx => ?_,
    fun v => ?_⟩
  · show g (t (g⁻¹ (g a))) = g a
    rw [lin_inv_apply, hta]
  · have hx' : f a (g⁻¹ x) = 0 := by
      have h := hgi' (g a) x
      rw [lin_inv_apply] at h
      rw [h]
      exact hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (ht1 _ hx')
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    show c • g a = g (t (g⁻¹ x)) - x
    rw [← map_smul, hc, map_sub, lin_apply_inv]
  · show f (g a) (g (t (g⁻¹ v)) - v) = 0
    have := ht2 (g⁻¹ v)
    rw [← hgi a (t (g⁻¹ v) - g⁻¹ v), map_sub, lin_apply_inv] at this
    exact this

theorem spTransvection_comm {g : V ≃ₗ[ZMod 2] V} (hf : f.IsAlt)
    (hg : g ∈ TauCeti.BilinForm.isometryGroup f) {c : V} (hgc : g c = c) (v : V) :
    g (spTransvection f hf c v) = spTransvection f hf c (g v) := by
  rw [spTransvection_apply, spTransvection_apply, map_add, map_smul, hgc,
    ← TauCeti.BilinForm.mem_isometryGroup_iff.mp hg v c, hgc]

theorem exists_orderOf_five_fix_pair [FiniteDimensional (ZMod 2) V] (hf : f.IsAlt)
    (hnd : f.Nondegenerate) (hdim : finrank (ZMod 2) V = 6) {e p : V} (hpe : f p e = 1) :
    ∃ ε ∈ TauCeti.BilinForm.isometryGroup f, orderOf ε = 5 ∧ ε e = e ∧ ε p = p := by
  have hZ : finrank (ZMod 2) (f.orthogonal (Submodule.span (ZMod 2) {e, p})) = 2 * 2 := by
    have := hf.finrank_orthogonal_span_pair_add_two hnd hpe
    omega
  have hcard : Nat.card (MulAction.stabilizer (TauCeti.BilinForm.isometryGroup f) (e, p)) =
      720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_stabilizer_pair hf hpe,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup 2
        (f.restrict (f.orthogonal (Submodule.span (ZMod 2) {e, p})))
        (fun z => hf.self_eq_zero (z : V)) (hf.restrict_nondegenerate_orthogonal_span_pair hpe hnd)
        hZ, Nat.card_zmod]
    decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite (MulAction.stabilizer (TauCeti.BilinForm.isometryGroup f) (e, p)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' 5
    (show 5 ∣ Nat.card (MulAction.stabilizer (TauCeti.BilinForm.isometryGroup f) (e, p)) by
      rw [hcard]; norm_num)
  have hxfix := MulAction.mem_stabilizer_iff.mp x.2
  refine ⟨((x : TauCeti.BilinForm.isometryGroup f) : V ≃ₗ[ZMod 2] V),
    (x : TauCeti.BilinForm.isometryGroup f).2, ?_, congrArg Prod.fst hxfix,
    congrArg Prod.snd hxfix⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx5]

theorem apply_mem_fixOf_of_conj {H M : Type*} [Group H] {X : Subgroup H} [AddCommGroup M]
    [Module (ZMod 2) M] (ρ : X →* (M ≃ₗ[ZMod 2] M)) {T T' : Set H} (x : X)
    (hT : ∀ u : X, (u : H) ∈ T → ((x⁻¹ * u * x : X) : H) ∈ T') {v : M}
    (hv : v ∈ S2.fixOf ρ T') : ρ x v ∈ S2.fixOf ρ T := by
  rw [S2.mem_fixOf] at hv ⊢
  intro u hu
  have h := hv _ (hT u hu)
  have e : ρ u = ρ x * ρ (x⁻¹ * u * x) * (ρ x)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    group
  have h2 : (ρ x)⁻¹ (ρ x v) = v := (ρ x).symm_apply_apply v
  rw [e, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h2, h]

theorem fixfree_of_orderOf_five {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (hM : Nat.card M = 256) (hf : f.IsAlt)
    (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M)) {a p₁ : V} (hap : f a p₁ = 1)
    (hcomp : IsCompl (S2.fixOf ρ (spPointRadical f a : Set (V ≃ₗ[ZMod 2] V)))
      (S2.fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (x : TauCeti.BilinForm.isometryGroup f) (hx5 : x ^ 5 = 1)
    (hxa : (x : V ≃ₗ[ZMod 2] V) a = a) (hxp : (x : V ≃ₗ[ZMod 2] V) p₁ = p₁)
    (hx1 : ∃ v, ρ x v ≠ v) : ∀ w, ρ x w = w → w = 0 := by
  have h2a : a + a = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have h2p : p₁ + p₁ = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hpa : f p₁ a = 1 := by
    rw [← hf.neg_eq, hap]
    rfl
  have hτa : spTransvection f hf (a + p₁) a = p₁ := by
    rw [spTransvection_apply, map_add, hf.self_eq_zero, hap, zero_add, one_smul, ← add_assoc,
      h2a, zero_add]
  have hτp : spTransvection f hf (a + p₁) p₁ = a := by
    rw [spTransvection_apply, map_add, hf.self_eq_zero, hpa, add_zero, one_smul,
      add_comm a p₁, ← add_assoc, h2p, zero_add]
  have hτia : (spTransvection f hf (a + p₁))⁻¹ p₁ = a := by
    have h := lin_inv_apply (spTransvection f hf (a + p₁)) a
    rwa [hτa] at h
  have hτip : (spTransvection f hf (a + p₁))⁻¹ a = p₁ := by
    have h := lin_inv_apply (spTransvection f hf (a + p₁)) p₁
    rwa [hτp] at h
  have hxia : (x : V ≃ₗ[ZMod 2] V)⁻¹ a = a := by
    have h := lin_inv_apply (x : V ≃ₗ[ZMod 2] V) a
    rwa [hxa] at h
  have hxip : (x : V ≃ₗ[ZMod 2] V)⁻¹ p₁ = p₁ := by
    have h := lin_inv_apply (x : V ≃ₗ[ZMod 2] V) p₁
    rwa [hxp] at h
  let xτ : TauCeti.BilinForm.isometryGroup f :=
    ⟨spTransvection f hf (a + p₁), spTransvection_mem_isometryGroup hf (a + p₁)⟩
  have hconj : ∀ (y : TauCeti.BilinForm.isometryGroup f) {c d : V},
      (y : V ≃ₗ[ZMod 2] V)⁻¹ c = d → ∀ u : TauCeti.BilinForm.isometryGroup f,
        (u : V ≃ₗ[ZMod 2] V) ∈ spPointRadical f c →
        ((y⁻¹ * u * y : TauCeti.BilinForm.isometryGroup f) : V ≃ₗ[ZMod 2] V) ∈
          spPointRadical f d := by
    intro y c d hcd u hu
    have := conj_mem_spPointRadical (inv_mem y.2) hu
    rw [inv_inv, hcd] at this
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hfA : ∀ v ∈ S2.fixOf ρ (spPointRadical f a : Set (V ≃ₗ[ZMod 2] V)),
      ρ x v ∈ S2.fixOf ρ (spPointRadical f a : Set (V ≃ₗ[ZMod 2] V)) :=
    fun v hv => apply_mem_fixOf_of_conj ρ x (hconj x hxia) hv
  have hfB : ∀ v ∈ S2.fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)),
      ρ x v ∈ S2.fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)) :=
    fun v hv => apply_mem_fixOf_of_conj ρ x (hconj x hxip) hv
  have hhA : ∀ v ∈ S2.fixOf ρ (spPointRadical f a : Set (V ≃ₗ[ZMod 2] V)),
      ρ xτ v ∈ S2.fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)) :=
    fun v hv => apply_mem_fixOf_of_conj ρ xτ (hconj xτ hτia) hv
  have hhB : ∀ v ∈ S2.fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)),
      ρ xτ v ∈ S2.fixOf ρ (spPointRadical f a : Set (V ≃ₗ[ZMod 2] V)) :=
    fun v hv => apply_mem_fixOf_of_conj ρ xτ (hconj xτ hτip) hv
  have hc : (x : V ≃ₗ[ZMod 2] V) (a + p₁) = a + p₁ := by rw [map_add, hxa, hxp]
  have hcomm : x * xτ = xτ * x := Subtype.ext (LinearEquiv.ext fun v =>
    spTransvection_comm hf x.2 hc v)
  have hfh : ∀ v, ρ x (ρ xτ v) = ρ xτ (ρ x v) := fun v => by
    rw [← LinearEquiv.mul_apply, ← map_mul, hcomm, map_mul, LinearEquiv.mul_apply]
  have hf5 : ρ x ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
  exact fixfree_of_swap hM hcomp hf5 hfA hfB hhA hhB hfh hx1

end CFSG.LargeExtraspecial.S14
