module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitCentTorus

public noncomputable section

namespace CFSG.AGLEmbedding.LinearThreeKit

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

namespace IsFixedLine

variable {p : ℕ} {u : SpecialLinearGroup (Fin 3) K} {x : Fin 3 → K}

def evalRoot {r : K} (hr : (centPoly u).IsRoot r) : AdjoinRoot (centPoly u) →+* K :=
  AdjoinRoot.lift (RingHom.id K) r (by rw [eval₂_id]; exact hr)

theorem evalRoot_quadElem {r : K} (hr : (centPoly u).IsRoot r) (a b : K) :
    evalRoot hr (quadElem _ a b) = a + b * r := by
  simp [evalRoot, quadElem, AdjoinRoot.lift_of, AdjoinRoot.lift_root]

theorem isRoot_inv {r : K} (hr : (centPoly u).IsRoot r) : (centPoly u).IsRoot r⁻¹ := by
  obtain ⟨hr0, ht⟩ := trace_eq_of_isRoot hr
  simp only [centPoly, quadPoly, IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_mul,
    eval_C, eval_one, ht]
  field_simp
  ring

theorem finite_card_le_of_split (h : IsFixedLine p u x) {r : K} (hr : (centPoly u).IsRoot r)
    {E : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hE : E ≤ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)))
    (hEp : ∀ g ∈ E, g ^ p = 1) : Finite E ∧ Nat.card E ≤ p ^ 2 := by
  have : NeZero p := ⟨h.odd.pos.ne'⟩
  obtain ⟨-, -, -, -, -, -, hrr, -, -⟩ := h.exists_splitTorus hr
  set e := h.centralizerEquiv with he
  have hmem : ∀ (φ : AdjoinRoot (centPoly u) →+* K) (g : E),
      Units.map φ.toMonoidHom (e ⟨g, hE g.2⟩) ∈ rootsOfUnity p K := fun φ g => by
    rw [mem_rootsOfUnity, ← map_pow, ← map_pow, show (⟨g, hE g.2⟩ : Subgroup.centralizer {u}) ^ p
      = 1 from Subtype.ext (hEp g g.2), map_one, map_one]
  let f : E → rootsOfUnity p K × rootsOfUnity p K := fun g =>
    (⟨_, hmem (evalRoot hr) g⟩, ⟨_, hmem (evalRoot (isRoot_inv hr)) g⟩)
  have hf : Function.Injective f := fun a b hab => by
    have h1 : evalRoot hr (e ⟨a, hE a.2⟩ : AdjoinRoot (centPoly u)) =
        evalRoot hr (e ⟨b, hE b.2⟩ : AdjoinRoot (centPoly u)) :=
      congrArg (fun z => ((z.1 : Kˣ) : K)) hab
    have h2 : evalRoot (isRoot_inv hr) (e ⟨a, hE a.2⟩ : AdjoinRoot (centPoly u)) =
        evalRoot (isRoot_inv hr) (e ⟨b, hE b.2⟩ : AdjoinRoot (centPoly u)) :=
      congrArg (fun z => ((z.2 : Kˣ) : K)) hab
    obtain ⟨a₁, b₁, ha⟩ := exists_quadElem_eq _ (e ⟨a, hE a.2⟩ : AdjoinRoot (centPoly u))
    obtain ⟨a₂, b₂, hb⟩ := exists_quadElem_eq _ (e ⟨b, hE b.2⟩ : AdjoinRoot (centPoly u))
    rw [ha, hb, evalRoot_quadElem, evalRoot_quadElem] at h1 h2
    have hbb : b₁ = b₂ := by
      have : (b₁ - b₂) * (r - r⁻¹) = 0 := by linear_combination h1 - h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hrr))
    have haa : a₁ = a₂ := by rw [hbb] at h1; linear_combination h1
    have := e.injective (a₁ := ⟨a, hE a.2⟩) (a₂ := ⟨b, hE b.2⟩)
      (Units.ext (by rw [ha, hb, haa, hbb]))
    exact Subtype.ext (congrArg (Subtype.val : Subgroup.centralizer ({u} : Set
      (SpecialLinearGroup (Fin 3) K)) → SpecialLinearGroup (Fin 3) K) this)
  refine ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  rw [Nat.card_prod, sq]
  exact Nat.mul_le_mul (card_rootsOfUnity K p) (card_rootsOfUnity K p)

theorem finite_card_le_sq (h : IsFixedLine p u x) {E : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hE : E ≤ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)))
    (hEp : ∀ g ∈ E, g ^ p = 1) : Finite E ∧ Nat.card E ≤ p ^ 2 := by
  by_cases hs : ∃ r : K, (centPoly u).IsRoot r
  · obtain ⟨r, hr⟩ := hs
    exact h.finite_card_le_of_split hr hE hEp
  · push Not at hs
    obtain ⟨hfin, hcard⟩ := h.finite_card_le_of_nonsplit hs hE hEp
    exact ⟨hfin, hcard.trans (Nat.le_self_pow two_ne_zero p)⟩

theorem commute_of_mem (h : IsFixedLine p u x) {a b : SpecialLinearGroup (Fin 3) K}
    (ha : a ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)))
    (hb : b ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))) :
    Commute a b := by
  have := h.centralizerHom_injective (a₁ := ⟨a, ha⟩ * ⟨b, hb⟩) (a₂ := ⟨b, hb⟩ * ⟨a, ha⟩)
    (by rw [map_mul, map_mul, mul_comm])
  exact congrArg (Subtype.val : Subgroup.centralizer ({u} : Set
    (SpecialLinearGroup (Fin 3) K)) → SpecialLinearGroup (Fin 3) K) this

def omega (h : IsFixedLine p u x) : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | g ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)) ∧
    g ^ p = 1}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [(h.commute_of_mem ha.1 hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem mem_omega (h : IsFixedLine p u x) {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ h.omega ↔
      g ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)) ∧ g ^ p = 1 :=
  Iff.rfl

theorem finite_card_omega_le (h : IsFixedLine p u x) :
    Finite h.omega ∧ Nat.card h.omega ≤ p ^ 2 :=
  h.finite_card_le_sq (fun _ hg => hg.1) fun _ hg => hg.2

theorem eq_omega_of_card_eq (h : IsFixedLine p u x) {E : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hE : E ≤ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)))
    (hEp : ∀ g ∈ E, g ^ p = 1) (hcard : Nat.card E = p ^ 2) : E = h.omega := by
  obtain ⟨hfin, hle⟩ := h.finite_card_omega_le
  exact Subgroup.eq_of_le_of_card_ge (fun g hg => ⟨hE hg, hEp g hg⟩) (hcard ▸ hle)

theorem omega_eq_zpowers_of_nonsplit (h : IsFixedLine p u x)
    (hns : ∀ r : K, ¬ (centPoly u).IsRoot r) (hp : p.Prime) :
    h.omega = Subgroup.zpowers u := by
  refine le_antisymm (fun g hg => h.mem_zpowers_of_pow_eq_one hns hp hg.1 hg.2) ?_
  rw [Subgroup.zpowers_le]
  exact ⟨self_mem_centralizer u, h.pow_eq_one⟩

theorem exists_isRoot_iff_dvd [Fintype K] (h : IsFixedLine p u x) (hp : p.Prime) :
    (∃ r : K, (centPoly u).IsRoot r) ↔ p ∣ Fintype.card K - 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨-, -, -, -, -, hr1, -, hrp, -⟩ := h.exists_splitTorus hr
    have hr0 := (trace_eq_of_isRoot hr).1
    have ho : orderOf (Units.mk0 r hr0) = p :=
      orderOf_eq_prime (Units.ext (by simpa using hrp)) fun h1 => hr1 (by
        simpa using congrArg Units.val h1)
    rw [← Fintype.card_units K, ← ho]
    exact orderOf_dvd_card
  · intro hdvd
    by_contra hns
    push Not at hns
    have : Fact (Irreducible (centPoly u)) := ⟨irreducible_centPoly hns⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card p (by rwa [Fintype.card_units K])
    have hprim : IsPrimitiveRoot (AdjoinRoot.of (centPoly u) (ζ : K)) p :=
      (IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζ)).map_of_injective
        (AdjoinRoot.of (centPoly u)).injective
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one (ξ := AdjoinRoot.root (centPoly u)) (by
      rw [← h.centralizerEquiv_self, ← Units.val_pow_eq_pow_val, ← map_pow,
        show (⟨u, self_mem_centralizer u⟩ : Subgroup.centralizer {u}) ^ p = 1 from
          Subtype.ext h.pow_eq_one, map_one, Units.val_one])
    have := (quadElem_injective (t := Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1)
      (a := (ζ : K) ^ i) (b := 0) (a' := 0) (b' := 1)
      (by rw [quadElem, quadElem, map_pow, hi]; simp)).2
    exact zero_ne_one this

theorem isCyclic_centralizer_of_not_dvd [Fintype K] (h : IsFixedLine p u x) (hp : p.Prime)
    (hpq : ¬ p ∣ Fintype.card K - 1) :
    IsCyclic (Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))) :=
  h.isCyclic_of_le_centralizer (fun r hr => hpq ((h.exists_isRoot_iff_dvd hp).mp ⟨r, hr⟩)) le_rfl

theorem mem_zpowers_of_not_dvd [Fintype K] (h : IsFixedLine p u x) (hp : p.Prime)
    (hpq : ¬ p ∣ Fintype.card K - 1) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)))
    (hgp : g ^ p = 1) : g ∈ Subgroup.zpowers u :=
  h.mem_zpowers_of_pow_eq_one (fun r hr => hpq ((h.exists_isRoot_iff_dvd hp).mp ⟨r, hr⟩)) hp
    hg hgp

end IsFixedLine

end CFSG.AGLEmbedding.LinearThreeKit
