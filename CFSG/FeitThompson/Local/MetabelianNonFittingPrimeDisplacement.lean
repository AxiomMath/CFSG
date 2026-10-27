module

public import Mathlib.GroupTheory.Sylow
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.SylowExistencePrimePower
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise
open scoped commutatorElement

variable {E : Type*} [Group E] {D Q : Subgroup E} {q : ℕ}

theorem exists_pow_eq_of_natCard_eq_prime [Finite E] (hq : q.Prime) (hQ : Nat.card Q = q)
    {y : E} (hy : y ∈ Q) (hy1 : y ≠ 1) {x : E} (hx : x ∈ Q) : ∃ n : ℕ, x = y ^ n := by
  have hle : Subgroup.zpowers y ≤ Q := by rwa [Subgroup.zpowers_le]
  have hcard : Nat.card (Subgroup.zpowers y) = q := by
    have hdvd : Nat.card (Subgroup.zpowers y) ∣ q := hQ ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hq).1 hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h ▸ Subgroup.mem_zpowers y)
        (by simpa [Subgroup.mem_bot] using hy1)
    · exact h
  have heq : Subgroup.zpowers y = Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hQ, hcard])
  have : x ∈ Subgroup.zpowers y := heq ▸ hx
  obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.2 this
  exact ⟨n, hn.symm⟩

theorem normal_commutator_top_left (Q : Subgroup E) : (⁅(⊤ : Subgroup E), Q⁆).Normal := by
  have h := Subgroup.normal_subgroupOf_commutator_sup (⊤ : Subgroup E) Q
  rw [top_sup_eq] at h
  have h2 := h.map (⊤ : Subgroup E).subtype
    (by rw [← MonoidHom.range_eq_top, Subgroup.range_subtype])
  rwa [Subgroup.subgroupOf_map_subtype, inf_top_eq] at h2

theorem commutator_top_left_le_commutator (Q : Subgroup E) :
    ⁅(⊤ : Subgroup E), Q⁆ ≤ _root_.commutator E := by
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mono le_rfl le_top

theorem isMulCommutative_commutator_top_left (hE : IsMulCommutative (_root_.commutator E))
    (Q : Subgroup E) : IsMulCommutative ↥(⁅(⊤ : Subgroup E), Q⁆) :=
  have := hE
  .of_setLike_mul_comm fun _ ha _ hb =>
    setLike_mul_comm (s := _root_.commutator E) (commutator_top_left_le_commutator Q ha)
      (commutator_top_left_le_commutator Q hb)

theorem commutator_top_left_le_fittingRaw [Finite E]
    (hE : IsMulCommutative (_root_.commutator E)) (Q : Subgroup E) :
    ⁅(⊤ : Subgroup E), Q⁆ ≤ fittingRaw E := by
  have hcomm := isMulCommutative_commutator_top_left hE Q
  let _ : CommGroup ↥(⁅(⊤ : Subgroup E), Q⁆) := IsMulCommutative.instCommGroup
  exact le_fittingRaw_of_normal_of_isNilpotent (normal_commutator_top_left Q)
    (CommGroup.isNilpotent (G := ↥(⁅(⊤ : Subgroup E), Q⁆)))

theorem not_dvd_natCard_fittingRaw [Finite E] (hq : q.Prime)
    (hcyc : ∀ S : Sylow q E, IsCyclic (S : Subgroup E))
    (hQ : Nat.card Q = q) (hQF : ¬ Q ≤ fittingRaw E) : ¬ q ∣ Nat.card (fittingRaw E) := by
  have : Fact q.Prime := ⟨hq⟩
  have hFn : (fittingRaw E).Normal := fittingRaw_normal E
  intro hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (fittingRaw E : Subgroup E)) q hdvd
  have hQ₁card : Nat.card (Subgroup.zpowers (y : E)) = q := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy]
  have hQ₁F : Subgroup.zpowers (y : E) ≤ fittingRaw E := by
    rw [Subgroup.zpowers_le]; exact y.2
  obtain ⟨S, hQS⟩ := IsPGroup.exists_le_sylow (P := Q)
    (IsPGroup.of_card (n := 1) (by simpa using hQ))
  have hR : Nat.card (S : Subgroup E) = q ^ (Nat.card E).factorization q := S.card_eq_multiplicity
  have : IsCyclic (S : Subgroup E) := hcyc S
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup hR (S := Subgroup.zpowers (y : E))
    (IsPGroup.of_card (n := 1) (by simpa using hQ₁card))
  have hQ₂S : MulAut.conj g⁻¹ • Subgroup.zpowers (y : E) ≤ (S : Subgroup E) := by
    have h1 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := (MulAut.conj g)⁻¹)).2 hg
    rw [inv_smul_smul] at h1
    rwa [map_inv]
  have hQ₂card : Nat.card (MulAut.conj g⁻¹ • Subgroup.zpowers (y : E) : Subgroup E) = q := by
    rw [natCard_conj_smul, hQ₁card]
  have hQ₂F : MulAut.conj g⁻¹ • Subgroup.zpowers (y : E) ≤ fittingRaw E :=
    conj_smul_le_of_normal _ hQ₁F
  have heq : Q = MulAut.conj g⁻¹ • Subgroup.zpowers (y : E) :=
    eq_of_le_of_natCard_eq_of_isCyclic hQS hQ₂S (by rw [hQ, hQ₂card])
  exact hQF (heq ▸ hQ₂F)

theorem not_dvd_natCard_commutator_top_left [Finite E] (hq : q.Prime)
    (hE : IsMulCommutative (_root_.commutator E))
    (hcyc : ∀ S : Sylow q E, IsCyclic (S : Subgroup E))
    (hQ : Nat.card Q = q) (hQF : ¬ Q ≤ fittingRaw E) :
    ¬ q ∣ Nat.card (⁅(⊤ : Subgroup E), Q⁆ : Subgroup E) := fun hdvd =>
  not_dvd_natCard_fittingRaw hq hcyc hQ hQF
    (hdvd.trans (Subgroup.card_dvd_of_le (commutator_top_left_le_fittingRaw hE Q)))

section Frattini

variable [D.Normal] (hDQ : ⁅(⊤ : Subgroup E), Q⁆ ≤ D)

include hDQ

theorem normal_sup_of_commutator_le : (D ⊔ Q).Normal := by
  constructor
  intro n hn g
  have key : D ⊔ Q ≤ (D ⊔ Q).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun d hd => ?_) fun x hx => ?_
    · exact Subgroup.mem_sup_left (‹D.Normal›.conj_mem d hd g)
    · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hcomm : g * x * g⁻¹ * x⁻¹ ∈ D := by
        have h := Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup E)) (H₂ := Q)
          (mem_top g) hx
        rw [commutatorElement_def] at h
        exact hDQ h
      have hc : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
      rw [hc]
      exact mul_mem (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hx)
  exact key hn

variable (hq : q.Prime) (hQ : Nat.card Q = q) (hDq : ¬ q ∣ Nat.card D)

include hq hQ hDq

omit [D.Normal] hDQ in
theorem inf_eq_bot_of_not_dvd : D ⊓ Q = ⊥ := by
  have h1 : Nat.card (D ⊓ Q : Subgroup E) ∣ Nat.card D := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card (D ⊓ Q : Subgroup E) ∣ q := hQ ▸ Subgroup.card_dvd_of_le inf_le_right
  refine Subgroup.card_eq_one.1 ?_
  rcases (Nat.dvd_prime hq).1 h2 with h | h
  · exact h
  · exact absurd (h ▸ h1) hDq

omit [D.Normal] in
theorem normalizer_eq_centralizer_of_commutator_le :
    normalizer (Q : Set E) = centralizer (Q : Set E) := by
  refine le_antisymm (fun n hn => ?_) (centralizer_le_normalizer _)
  rw [mem_centralizer_iff]
  intro x hx
  rw [SetLike.mem_coe] at hx
  have hxQ : n * x * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hn x).1 hx
  have hcD : n * x * n⁻¹ * x⁻¹ ∈ D := by
    have h := Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup E)) (H₂ := Q)
      (mem_top n) hx
    rw [commutatorElement_def] at h
    exact hDQ h
  have hmem : n * x * n⁻¹ * x⁻¹ ∈ D ⊓ Q := ⟨hcD, Q.mul_mem hxQ (Q.inv_mem hx)⟩
  rw [inf_eq_bot_of_not_dvd hq hQ hDq, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  rw [mul_inv_eq_iff_eq_mul] at hmem
  exact hmem.symm

theorem sup_centralizer_eq_top_of_commutator_le [Finite E] :
    D ⊔ centralizer (Q : Set E) = ⊤ := by
  have : Fact q.Prime := ⟨hq⟩
  have hDQn : (D ⊔ Q).Normal := normal_sup_of_commutator_le hDQ
  have hQsyl : Nat.card Q = q ^ (Nat.card (D ⊔ Q : Subgroup E)).factorization q := by
    have hcard : Nat.card (D ⊔ Q : Subgroup E) = q ^ 1 * Nat.card D := by
      rw [natCard_sup_eq_mul_of_normal_of_inf_eq_bot (inf_eq_bot_of_not_dvd hq hQ hDq), hQ,
        pow_one, mul_comm]
    rw [hQ, factorization_eq_of_eq_pow_mul hq hDq hcard, pow_one]
  have hfr : normalizer (Q : Set E) ⊔ (D ⊔ Q) = ⊤ :=
    normalizer_sup_eq_top_of_normal (p := q) (R := D ⊔ Q) (P := Q) le_sup_right hQsyl
  rw [normalizer_eq_centralizer_of_commutator_le hDQ hq hQ hDq] at hfr
  have hQC : Q ≤ centralizer (Q : Set E) := by
    rw [← normalizer_eq_centralizer_of_commutator_le hDQ hq hQ hDq]
    exact Subgroup.le_normalizer
  refine le_antisymm le_top ?_
  rw [← hfr]
  exact sup_le le_sup_right (sup_le le_sup_left (le_sup_of_le_right hQC))

end Frattini

theorem commutator_top_left_sup_centralizer_eq_top [Finite E] (hq : q.Prime)
    (hE : IsMulCommutative (_root_.commutator E))
    (hcyc : ∀ S : Sylow q E, IsCyclic (S : Subgroup E))
    (hQ : Nat.card Q = q) (hQF : ¬ Q ≤ fittingRaw E) :
    ⁅(⊤ : Subgroup E), Q⁆ ⊔ centralizer (Q : Set E) = ⊤ := by
  have : (⁅(⊤ : Subgroup E), Q⁆).Normal := normal_commutator_top_left Q
  exact sup_centralizer_eq_top_of_commutator_le le_rfl hq hQ
    (not_dvd_natCard_commutator_top_left hq hE hcyc hQ hQF)

theorem commutator_eq_self_of_sup_centralizer_eq_top [D.Normal]
    (hD : ⁅(⊤ : Subgroup E), Q⁆ = D) (hE : D ⊔ centralizer (Q : Set E) = ⊤) : ⁅D, Q⁆ = D := by
  refine le_antisymm (hD ▸ Subgroup.commutator_mono le_top le_rfl) ?_
  have hstep : ⁅(⊤ : Subgroup E), Q⁆ ≤ ⁅D, Q⁆ := by
    rw [Subgroup.commutator_le]
    intro g _ x hx
    have hg : g ∈ (D : Set E) * (centralizer (Q : Set E) : Set E) := by
      rw [← Subgroup.normal_mul, hE]; trivial
    obtain ⟨d, hd, c, hc, rfl⟩ := hg
    have hcx : c * x = x * c := ((mem_centralizer_iff.1 hc) x hx).symm
    have hkey : (d * c) * x * (d * c)⁻¹ * x⁻¹ = d * x * d⁻¹ * x⁻¹ := by
      have hcx' : c * x * c⁻¹ = x := by rw [hcx]; group
      calc d * c * x * (d * c)⁻¹ * x⁻¹ = d * (c * x * c⁻¹) * d⁻¹ * x⁻¹ := by group
        _ = d * x * d⁻¹ * x⁻¹ := by rw [hcx']
    change ⁅(d * c : E), x⁆ ∈ ⁅D, Q⁆
    rw [commutatorElement_def, hkey, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hd hx
  exact hD ▸ hstep

theorem commutator_commutator_top_left_eq_self [Finite E] (hq : q.Prime)
    (hE : IsMulCommutative (_root_.commutator E))
    (hcyc : ∀ S : Sylow q E, IsCyclic (S : Subgroup E))
    (hQ : Nat.card Q = q) (hQF : ¬ Q ≤ fittingRaw E) :
    ⁅(⁅(⊤ : Subgroup E), Q⁆ : Subgroup E), Q⁆ = ⁅(⊤ : Subgroup E), Q⁆ := by
  have : (⁅(⊤ : Subgroup E), Q⁆).Normal := normal_commutator_top_left Q
  exact commutator_eq_self_of_sup_centralizer_eq_top rfl
    (commutator_top_left_sup_centralizer_eq_top hq hE hcyc hQ hQF)

theorem commutator_top_left_ne_bot [Finite E] (hq : q.Prime) (hQ : Nat.card Q = q)
    (hQF : ¬ Q ≤ fittingRaw E) : ⁅(⊤ : Subgroup E), Q⁆ ≠ ⊥ := by
  intro hD
  have hQnormal : Q.Normal := by
    constructor
    intro n hn g
    have h := Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup E)) (H₂ := Q)
      (mem_top g) hn
    rw [hD, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one] at h
    rw [h]
    exact hn
  exact hQF (le_fittingRaw_of_isPGroup hq hQnormal (IsPGroup.of_card (n := 1) (by simpa using hQ)))

theorem inf_centralizer_eq_bot_of_commutator_eq_self [Finite E] [D.Normal]
    (hDab : IsMulCommutative D) {y : E} (hyQ : y ∈ Q)
    (hQy : ∀ x ∈ Q, ∃ n : ℕ, x = y ^ n) (hDQ : ⁅D, Q⁆ = D) :
    D ⊓ centralizer (Q : Set E) = ⊥ := by
  have := hDab
  let _ : CommGroup D := IsMulCommutative.instCommGroup
  set σ : MulAut D := MulAut.conjNormal y with hσ
  let ψ : D →* D :=
    { toFun := fun d => d * (σ d)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        rw [mul_comm ((σ b)⁻¹) ((σ a)⁻¹)]
        ac_rfl }
  have hψ : ∀ d : D, ψ d = d * (σ d)⁻¹ := fun _ => rfl
  have hσpow : ∀ n : ℕ, σ ^ n = MulAut.conjNormal (y ^ n) := fun n => by rw [hσ, ← map_pow]
  have key : ∀ n : ℕ, ∀ d : D, d * ((σ ^ n) d)⁻¹ ∈ ψ.range := by
    intro n
    induction n with
    | zero => intro d; simp
    | succ n ih =>
      intro d
      have hstep : d * ((σ ^ (n + 1)) d)⁻¹ = (d * ((σ ^ n) d)⁻¹) * ψ ((σ ^ n) d) := by
        rw [hψ, pow_succ']
        simp only [MulAut.mul_apply]
        group
      rw [hstep]
      exact mul_mem (ih d) ⟨_, rfl⟩
  have hle : ⁅D, Q⁆ ≤ (ψ.range).map D.subtype := by
    rw [Subgroup.commutator_le]
    intro d hd x hx
    obtain ⟨n, rfl⟩ := hQy x hx
    refine ⟨⟨d, hd⟩ * ((σ ^ n) ⟨d, hd⟩)⁻¹, key n ⟨d, hd⟩, ?_⟩
    have hc : ((σ ^ n) ⟨d, hd⟩ : E) = y ^ n * d * (y ^ n)⁻¹ := by
      rw [hσpow n]; exact MulAut.conjNormal_apply _ _
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hc]
    rw [commutatorElement_def]
    group
  have hrange : ψ.range = ⊤ := by
    have h1 : D ≤ (ψ.range).map D.subtype := le_trans hDQ.ge hle
    refine eq_top_iff.2 fun d _ => ?_
    obtain ⟨e, he, hed⟩ := h1 d.2
    have hde : e = d := Subtype.ext hed
    exact hde ▸ he
  have hinj : Function.Injective ψ :=
    (Finite.injective_iff_surjective).2 (MonoidHom.range_eq_top.1 hrange)
  refine le_antisymm (fun d hd => ?_) bot_le
  obtain ⟨hdD, hdC⟩ := hd
  have hdD' : d ∈ D := hdD
  have hfix : σ ⟨d, hdD'⟩ = ⟨d, hdD'⟩ := by
    refine Subtype.ext ?_
    have hcomm : y * d = d * y := (mem_centralizer_iff.1 hdC) y hyQ
    have hcy : y * d * y⁻¹ = d := by rw [hcomm]; group
    simpa [hσ, MulAut.conjNormal_apply] using hcy
  have hker : ψ ⟨d, hdD'⟩ = ψ 1 := by
    rw [hψ ⟨d, hdD'⟩, hψ 1, hfix]
    simp
  have hd1 := hinj hker
  simpa [Subgroup.mem_bot] using congrArg Subtype.val hd1

theorem inf_centralizer_eq_bot [Finite E] (hq : q.Prime)
    (hE : IsMulCommutative (_root_.commutator E))
    (hcyc : ∀ S : Sylow q E, IsCyclic (S : Subgroup E))
    (hQ : Nat.card Q = q) (hQF : ¬ Q ≤ fittingRaw E) :
    (⁅(⊤ : Subgroup E), Q⁆ : Subgroup E) ⊓ centralizer (Q : Set E) = ⊥ := by
  have hDn : (⁅(⊤ : Subgroup E), Q⁆).Normal := normal_commutator_top_left Q
  have hQ1 : Q ≠ ⊥ := by
    intro h
    rw [h] at hQ
    simp only [Nat.card_unique] at hQ
    exact hq.one_lt.ne' hQ.symm
  obtain ⟨y, hyQ, hy1⟩ : ∃ y ∈ Q, y ≠ 1 := by
    rw [ne_eq, Subgroup.eq_bot_iff_forall] at hQ1
    push Not at hQ1
    obtain ⟨y, hy, hy1⟩ := hQ1
    exact ⟨y, hy, hy1⟩
  exact inf_centralizer_eq_bot_of_commutator_eq_self
    (isMulCommutative_commutator_top_left hE Q) hyQ
    (fun x hx => exists_pow_eq_of_natCard_eq_prime hq hQ hyQ hy1 hx)
    (commutator_commutator_top_left_eq_self hq hE hcyc hQ hQF)

theorem not_dvd_natCard_fittingRaw_and_commutator_top_left_spec [Finite E] (hq : q.Prime)
    (hE : IsMulCommutative (_root_.commutator E))
    (hcyc : ∀ S : Sylow q E, IsCyclic (S : Subgroup E))
    (hQ : Nat.card Q = q) (hQF : ¬ Q ≤ fittingRaw E) :
    ¬ q ∣ Nat.card (fittingRaw E) ∧
      (⁅(⊤ : Subgroup E), Q⁆).Normal ∧
      IsMulCommutative ↥(⁅(⊤ : Subgroup E), Q⁆) ∧
      ⁅(⊤ : Subgroup E), Q⁆ ≠ ⊥ ∧
      ¬ q ∣ Nat.card (⁅(⊤ : Subgroup E), Q⁆ : Subgroup E) ∧
      ⁅(⊤ : Subgroup E), Q⁆ ⊔ centralizer (Q : Set E) = ⊤ ∧
      ⁅(⁅(⊤ : Subgroup E), Q⁆ : Subgroup E), Q⁆ = ⁅(⊤ : Subgroup E), Q⁆ ∧
      (⁅(⊤ : Subgroup E), Q⁆ : Subgroup E) ⊓ centralizer (Q : Set E) = ⊥ :=
  ⟨not_dvd_natCard_fittingRaw hq hcyc hQ hQF, normal_commutator_top_left Q,
    isMulCommutative_commutator_top_left hE Q, commutator_top_left_ne_bot hq hQ hQF,
    not_dvd_natCard_commutator_top_left hq hE hcyc hQ hQF,
    commutator_top_left_sup_centralizer_eq_top hq hE hcyc hQ hQF,
    commutator_commutator_top_left_eq_self hq hE hcyc hQ hQF,
    inf_centralizer_eq_bot hq hE hcyc hQ hQF⟩

end

end CFSG.FeitThompson
