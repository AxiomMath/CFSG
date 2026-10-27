module

public import Mathlib.RepresentationTheory.Irreducible
public import CFSG.FeitThompson.Representations.ConjTransitiveAbelianCharsCentralChar
import CFSG.FeitThompson.Representations.ExtraspecialQuotientAlternatingForm
import CFSG.FeitThompson.Representations.CoprimeAbelianWeightDecomposition
import CFSG.FeitThompson.Representations.ExtraspecialWeightCosetBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.ExtraspecialWeight

open CFSG.FeitThompson CFSG.FeitThompson.Representation

open scoped commutatorElement

universe u v w

variable {p n : ℕ} {P : Type u} [Group P] {B : Subgroup P} {k : Type v} [Field k]
  {V : Type w} [AddCommGroup V] [Module k V] {ρ : Representation k P V}
  {zeta : ↥(Subgroup.center P) →* kˣ} {hcl : commutator P ≤ Subgroup.center P}

theorem injective_of_ne_one (hP : IsExtraspecial p P) (hzeta : zeta ≠ 1) :
    Function.Injective zeta := by
  have : Fact (Nat.card ↥(Subgroup.center P)).Prime := ⟨hP.card_center ▸ hP.prime⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card zeta.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exact absurd (MonoidHom.ker_eq_top_iff.1 h) hzeta

theorem bijective_mk_out :
    Function.Bijective fun q : P ⧸ Subgroup.center P =>
      (QuotientGroup.mk (Quotient.out q) : P ⧸ Subgroup.center P) := by
  have hid : (fun q : P ⧸ Subgroup.center P =>
      (QuotientGroup.mk (Quotient.out q) : P ⧸ Subgroup.center P)) = id := by
    funext q; simp [QuotientGroup.mk]
  rw [hid]; exact Function.bijective_id

def conjWeight (hcl : commutator P ≤ Subgroup.center P) (zeta : ↥(Subgroup.center P) →* kˣ)
    (t : P) : P ⧸ Subgroup.center P →* kˣ :=
  QuotientGroup.lift _
    (MonoidHom.mk' (fun u => zeta (commCenter hcl u t))
      (fun u₁ u₂ => by rw [commCenter_mul_left, map_mul])) <| by
    intro u hu
    simp [MonoidHom.mem_ker, commCenter_eq_one_left hu]

theorem conjWeight_mk (t u : P) :
    conjWeight hcl zeta t (QuotientGroup.mk u) = zeta (commCenter hcl u t) := (rfl)

def conjWeightHom (hcl : commutator P ≤ Subgroup.center P)
    (zeta : ↥(Subgroup.center P) →* kˣ) : P →* (P ⧸ Subgroup.center P →* kˣ) where
  toFun := conjWeight hcl zeta
  map_one' := MonoidHom.ext fun q => by
    induction q using QuotientGroup.induction_on with
    | H u => rw [conjWeight_mk, commCenter_one_right, map_one, MonoidHom.one_apply]
  map_mul' t s := MonoidHom.ext fun q => by
    induction q using QuotientGroup.induction_on with
    | H u =>
      rw [MonoidHom.mul_apply, conjWeight_mk, conjWeight_mk, conjWeight_mk,
        commCenter_mul_right, map_mul]

theorem conjWeightHom_apply (t : P) : conjWeightHom hcl zeta t = conjWeight hcl zeta t := (rfl)

theorem ker_conjWeightHom (hinj : Function.Injective zeta) :
    (conjWeightHom hcl zeta).ker = Subgroup.center P := by
  ext t
  simp only [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h u
    have hq := congrArg (fun f => f (QuotientGroup.mk u)) h
    rw [conjWeightHom_apply, conjWeight_mk, MonoidHom.one_apply] at hq
    exact (commCenter_eq_one_iff (hcl := hcl)).1 (hinj (by rw [hq, map_one]))
  · intro h
    refine MonoidHom.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H u =>
      rw [conjWeightHom_apply, conjWeight_mk, MonoidHom.one_apply,
        (commCenter_eq_one_iff (hcl := hcl)).2 (h u), map_one]

def endConj (ρ : Representation k P V) (zeta : ↥(Subgroup.center P) →* kˣ)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w) :
    Representation k (P ⧸ Subgroup.center P) (Module.End k V) :=
  QuotientGroup.lift _ (ρ.linHom ρ) <| by
    intro z hzc
    rw [MonoidHom.mem_ker]
    set c : k := (zeta ⟨z, hzc⟩ : k) with hc
    have hzz : ∀ w : V, ρ z w = c • w := fun w => hz ⟨z, hzc⟩ w
    have hzi : ∀ w : V, ρ z⁻¹ w = c⁻¹ • w := fun w => by
      have h := hz ⟨z, hzc⟩⁻¹ w
      simpa [hc] using h
    refine LinearMap.ext fun f => LinearMap.ext fun w => ?_
    rw [Representation.linHom_apply]
    simp only [LinearMap.comp_apply, Module.End.one_apply]
    rw [hzi w, LinearMap.map_smul, hzz (c⁻¹ • f w), smul_smul,
      mul_inv_cancel₀ (Units.ne_zero _), one_smul]

theorem endConj_mk_apply (hz : ∀ (z : ↥(Subgroup.center P)) (w : V),
    ρ (z : P) w = (zeta z : k) • w) (u : P) (f : Module.End k V) :
    endConj ρ zeta hz (QuotientGroup.mk u) f = (ρ u : Module.End k V) * f * ρ u⁻¹ := by
  change (ρ.linHom ρ) u f = _
  rw [Representation.linHom_apply]
  rfl

theorem endConj_mk_apply_rho (hcl : commutator P ≤ Subgroup.center P)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w) (u t : P) :
    endConj ρ zeta hz (QuotientGroup.mk u) (ρ t) =
      (zeta (commCenter hcl u t) : k) • (ρ t : Module.End k V) := by
  rw [endConj_mk_apply hz]
  have h1 : (ρ u : Module.End k V) * ρ t * ρ u⁻¹ = ρ (⁅u, t⁆ * t) := by
    rw [← map_mul, ← map_mul]
    congr 1
    rw [commutatorElement_def]
    group
  rw [h1, map_mul]
  have h2 : (ρ ⁅u, t⁆ : Module.End k V) = (zeta (commCenter hcl u t) : k) • 1 := by
    have hzc := hz (commCenter hcl u t)
    refine LinearMap.ext fun w => ?_
    rw [show (ρ ⁅u, t⁆) w = ρ ((commCenter hcl u t : ↥(Subgroup.center P)) : P) w from by
      rw [coe_commCenter], hzc]
    simp
  rw [h2]
  ext w
  simp

theorem linearIndependent_rho (hP : IsExtraspecial p P) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w)
    (hirr : ρ.IsIrreducible) {ι : Type*} (T : ι → P)
    (hT : Function.Injective fun i => (QuotientGroup.mk (T i) : P ⧸ Subgroup.center P)) :
    LinearIndependent k fun i => (ρ (T i) : Module.End k V) := by
  have hcl := hP.commutator_le_center
  have hinj := injective_of_ne_one hP hzeta
  let _ : CommGroup (P ⧸ Subgroup.center P) :=
    haveI := hP.isMulCommutative_quotient_center; IsMulCommutative.instCommGroup
  have hchar : Function.Injective fun i => conjWeight hcl zeta (T i) := by
    intro i j hij
    refine hT ?_
    have h : conjWeightHom hcl zeta (T i) = conjWeightHom hcl zeta (T j) := hij
    have hm : (T i)⁻¹ * T j ∈ (conjWeightHom hcl zeta).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [ker_conjWeightHom hinj] at hm
    exact QuotientGroup.eq.2 hm
  have hnt := nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv0⟩ := exists_ne (0 : V)
  refine linearIndependent_of_mem_characterSpace (endConj ρ zeta hz) hchar (fun i => ?_)
    (fun i => ?_)
  · rw [mem_characterSpace_iff]
    intro a
    induction a using QuotientGroup.induction_on with
    | H u => rw [endConj_mk_apply_rho hcl hz, conjWeight_mk]
  · intro hc
    refine apply_ne_zero (ρ := ρ) (T i) hv0 ?_
    have h : (ρ (T i) : Module.End k V) v = 0 := by rw [hc]; exact LinearMap.zero_apply v
    exact h

theorem finrank_end_eq_finrank_mul_finrank (V : Type w) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    Module.finrank k (Module.End k V) = Module.finrank k V * Module.finrank k V :=
  Module.finrank_linearMap k k V V

theorem finrank_end_eq_index_center (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hirr : ρ.IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w) :
    Module.finrank k (Module.End k V) = (Subgroup.center P).index := by
  have := hP.finite
  have hfd := finiteDimensional_of_isIrreducible hirr
  have hV : Module.finrank k V = p ^ n :=
    finrank_eq_pow hP hZB hCB hPB hp hirr zeta hzeta hz
  rw [finrank_end_eq_finrank_mul_finrank V, hV, ← Subgroup.relIndex_mul_index hZB, hBZ, hPB]

theorem span_rho_eq_top (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hirr : ρ.IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w)
    {ι : Type*} (T : ι → P)
    (hT : Function.Bijective fun i => (QuotientGroup.mk (T i) : P ⧸ Subgroup.center P)) :
    Submodule.span k (Set.range fun i => (ρ (T i) : Module.End k V)) = ⊤ := by
  have := hP.finite
  have : Finite ι := Finite.of_injective _ hT.injective
  have : Fintype ι := Fintype.ofFinite ι
  have : Nonempty ι := ⟨(hT.surjective (QuotientGroup.mk 1)).choose⟩
  refine (linearIndependent_rho hP hzeta hz hirr T hT.injective).span_eq_top_of_card_eq_finrank ?_
  rw [finrank_end_eq_index_center hP hZB hCB hPB hBZ hp hirr hzeta hz,
    Subgroup.index_eq_card, ← Nat.card_eq_of_bijective _ hT, Nat.card_eq_fintype_card]

noncomputable def endBasis (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hirr : ρ.IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w)
    {ι : Type*} (T : ι → P)
    (hT : Function.Bijective fun i => (QuotientGroup.mk (T i) : P ⧸ Subgroup.center P)) :
    Module.Basis ι k (Module.End k V) :=
  Module.Basis.mk (linearIndependent_rho hP hzeta hz hirr T hT.injective)
    (span_rho_eq_top hP hZB hCB hPB hBZ hp hirr hzeta hz T hT).ge

@[simp]
theorem endBasis_apply (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hirr : ρ.IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w)
    {ι : Type*} (T : ι → P)
    (hT : Function.Bijective fun i => (QuotientGroup.mk (T i) : P ⧸ Subgroup.center P)) (i : ι) :
    endBasis hP hZB hCB hPB hBZ hp hirr hzeta hz T hT i = (ρ (T i) : Module.End k V) := by
  rw [endBasis, Module.Basis.mk_apply]

theorem span_range_rho_eq_top (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hirr : ρ.IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), ρ (z : P) w = (zeta z : k) • w) :
    Submodule.span k (Set.range fun t : P => (ρ t : Module.End k V)) = ⊤ := by
  refine top_unique ?_
  rw [← span_rho_eq_top hP hZB hCB hPB hBZ hp hirr hzeta hz
    (fun q : P ⧸ Subgroup.center P => Quotient.out q) bijective_mk_out]
  refine Submodule.span_mono ?_
  rintro f ⟨q, rfl⟩
  exact ⟨Quotient.out q, rfl⟩

end CFSG.FeitThompson.ExtraspecialWeight
