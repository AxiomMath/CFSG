module

public import CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCoverLifts
public import CFSG.LieType.Chevalley.F4FieldTwoRootPairs

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

abbrev f4Len (r : Fin Tag.F4.rank → ℤ) : ℚ := f4Euclid r ⬝ᵥ f4Euclid r

abbrev f4Ip (r s : Fin Tag.F4.rank → ℤ) : ℚ := f4Euclid r ⬝ᵥ f4Euclid s

@[expose] def RootPair (r s : Fin Tag.F4.rank → ℤ) : Prop :=
  IsRoot .F4 r ∧ IsRoot .F4 s ∧ r ≠ s ∧ r ≠ -s

theorem isRoot_of_ofFn {v : Fin Tag.F4.rank → ℤ}
    (h : ∃ k : Fin 48, List.ofFn (Tag.F4.rootCertificate.root k) = List.ofFn v) :
    IsRoot .F4 v := by
  obtain ⟨k, hk⟩ := h
  exact isRoot_f4_iff.mpr ⟨k, List.ofFn_injective hk⟩

theorem eq_of_ofFn {v w : Fin Tag.F4.rank → ℤ} (h : List.ofFn v = List.ofFn w) : v = w :=
  List.ofFn_injective h

theorem rootPair_of_ofFn {r s : Fin Tag.F4.rank → ℤ}
    (h : (∃ k : Fin 48, List.ofFn (Tag.F4.rootCertificate.root k) = List.ofFn r) ∧
      (∃ k : Fin 48, List.ofFn (Tag.F4.rootCertificate.root k) = List.ofFn s) ∧
      List.ofFn r ≠ List.ofFn s ∧ List.ofFn r ≠ List.ofFn (-s)) : RootPair r s :=
  ⟨isRoot_of_ofFn h.1, isRoot_of_ofFn h.2.1, fun e => h.2.2.1 (congrArg List.ofFn e),
    fun e => h.2.2.2 (congrArg List.ofFn e)⟩

theorem RootPair.symm {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s) : RootPair s r :=
  ⟨h.2.1, h.1, fun e => h.2.2.1 e.symm, fun e => h.2.2.2 (by rw [e, neg_neg])⟩

theorem rootPair_of_ip {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (h1 : f4Ip r s ≠ f4Len r) (h2 : f4Ip r s ≠ -f4Len r) : RootPair r s := by
  refine ⟨hr, hs, fun e => h1 (by rw [e]), fun e => h2 ?_⟩
  rw [e]
  simp only [f4Ip, f4Len, f4Euclid_neg, neg_dotProduct, dotProduct_neg, neg_neg]

variable {K : Type} [Field K]

@[expose] def xr (r : Fin Tag.F4.rank → ℤ) : adjointGroup .F4 K :=
  ⟨pinnedX .F4 K r 1, pinnedX_mem_adjointGroup r 1⟩

theorem coe_commutatorElement_adjoint (a b : adjointGroup .F4 K) :
    ((⁅a, b⁆ : adjointGroup .F4 K) : ModGL .F4 K) = ⁅(a : ModGL .F4 K), (b : ModGL .F4 K)⁆ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]

variable (hK : Nat.card K = 2)

include hK in
theorem xr_mul_self {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) : xr (K := K) r * xr r = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hinv, -⟩ := f4_field_two_root_pair_relations hK
  refine Subtype.ext ?_
  have h := pow_orderOf_eq_one (pinnedX .F4 K r 1)
  rw [(hinv r hr).2, sq] at h
  exact h

include hK in
theorem xr_commutatorElement_obtuse {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s)
    (hl : f4Len r = f4Len s) (hip : 2 * f4Ip r s = -f4Len r) :
    IsRoot .F4 (r + s) ∧ ⁅xr (K := K) r, xr (K := K) s⁆ = xr (K := K) (r + s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrel⟩ := f4_field_two_root_pair_relations hK
  obtain ⟨h1, h2⟩ := (hrel r s h.1 h.2.1 h.2.2.1 h.2.2.2).1 ⟨hl, hip⟩
  exact ⟨h1, Subtype.ext (by rw [coe_commutatorElement_adjoint]; exact h2)⟩

include hK in
theorem xr_commutatorElement_mixed {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s)
    (hA : f4Len r = 2) (hB : f4Len s = 1) (hC : f4Ip r s = -1) :
    IsRoot .F4 (r + s) ∧ IsRoot .F4 (r + 2 • s) ∧ f4Len (r + s) = 1 ∧
      f4Len (r + 2 • s) = 2 ∧
      ⁅xr (K := K) r, xr (K := K) s⁆ = xr (K := K) (r + s) * xr (K := K) (r + 2 • s) ∧
      ⁅xr (K := K) s, xr (K := K) r⁆ = xr (K := K) (r + s) * xr (K := K) (r + 2 • s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrel⟩ := f4_field_two_root_pair_relations hK
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := (hrel r s h.1 h.2.1 h.2.2.1 h.2.2.2).2.1 ⟨hA, hB, hC⟩
  exact ⟨h1, h2, h3, h4, Subtype.ext (by rw [coe_commutatorElement_adjoint]; exact h5),
    Subtype.ext (by rw [coe_commutatorElement_adjoint]; exact h6)⟩

include hK in
theorem xr_commute {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s)
    (h1 : ¬(f4Len r = f4Len s ∧ 2 * f4Ip r s = -f4Len r))
    (h2 : ¬(f4Len r = 2 ∧ f4Len s = 1 ∧ f4Ip r s = -1))
    (h3 : ¬(f4Len r = 1 ∧ f4Len s = 2 ∧ f4Ip r s = -1)) :
    xr (K := K) r * xr (K := K) s = xr (K := K) s * xr (K := K) r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrel⟩ := f4_field_two_root_pair_relations hK
  exact Subtype.ext ((hrel r s h.1 h.2.1 h.2.2.1 h.2.2.2).2.2 h1 h2 h3).eq

include hK in
theorem exists_conj_pair {r s r' s' : Fin Tag.F4.rank → ℤ} (h : RootPair r s)
    (h' : RootPair r' s') (h1 : f4Len r = f4Len r') (h2 : f4Len s = f4Len s')
    (h3 : f4Ip r s = f4Ip r' s') :
    ∃ g : adjointGroup .F4 K, g * xr (K := K) r * g⁻¹ = xr (K := K) r' ∧
      g * xr (K := K) s * g⁻¹ = xr (K := K) s' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, htrans, -⟩ := f4_field_two_root_pair_relations hK
  obtain ⟨w, hwr, hws, g, hg, hgt⟩ := htrans r s r' s' h.1 h.2.1 h'.1 h'.2.1 h.2.2.1 h.2.2.2
    h'.2.2.1 h'.2.2.2 h1 h2 h3
  refine ⟨⟨g, hg⟩, Subtype.ext ?_, Subtype.ext ?_⟩
  · change g * pinnedX .F4 K r 1 * g⁻¹ = pinnedX .F4 K r' 1
    rw [hgt r h.1, hwr]
  · change g * pinnedX .F4 K s 1 * g⁻¹ = pinnedX .F4 K s' 1
    rw [hgt s h.2.1, hws]

theorem conj_eq_commutatorElement_mul {G : Type*} [Group G] (g w : G) :
    g * w * g⁻¹ = ⁅g, w⁆ * w := by
  rw [commutatorElement_def]
  group

theorem conj_eq_self_of_commute {G : Type*} [Group G] {g u : G} (h : g * u = u * g) :
    g * u * g⁻¹ = u := by
  rw [h, mul_inv_cancel_right]

abbrev vL1 : Fin Tag.F4.rank → ℤ := ![0, 1, 2, 2]
abbrev vL2 : Fin Tag.F4.rank → ℤ := ![1, 1, 2, 2]
abbrev vL3 : Fin Tag.F4.rank → ℤ := ![1, 2, 2, 2]
abbrev vLq : Fin Tag.F4.rank → ℤ := ![-1, -1, 0, 0]
abbrev vS1 : Fin Tag.F4.rank → ℤ := ![1, 2, 3, 2]
abbrev vS2 : Fin Tag.F4.rank → ℤ := ![1, 2, 3, 1]
abbrev vS3 : Fin Tag.F4.rank → ℤ := ![1, 2, 2, 1]
abbrev vSq : Fin Tag.F4.rank → ℤ := ![0, 0, 1, 1]
abbrev vE23 : Fin Tag.F4.rank → ℤ := ![1, 2, 2, 0]
abbrev vE24 : Fin Tag.F4.rank → ℤ := ![1, 1, 2, 0]
abbrev vE3m4 : Fin Tag.F4.rank → ℤ := ![0, 1, 0, 0]
abbrev vE12 : Fin Tag.F4.rank → ℤ := ![2, 3, 4, 2]
abbrev vE2 : Fin Tag.F4.rank → ℤ := ![1, 1, 1, 0]
abbrev vMa4 : Fin Tag.F4.rank → ℤ := ![0, 0, 0, -1]
abbrev vHalf : Fin Tag.F4.rank → ℤ := ![0, 1, 2, 1]
abbrev vE34 : Fin Tag.F4.rank → ℤ := ![0, 1, 2, 0]

variable {E : Type*} [Group E] {η : E →* adjointGroup .F4 K} (hη : Function.Surjective η)
  (hC : η.ker ≤ Subgroup.center E)

include hK hη hC in
theorem liftsCommute_longRow : LiftsCommute η (xr vL2) (xr vL1) := by
  have hq3 := (xr_commutatorElement_obtuse (K := K) hK (r := vLq) (s := vL3)
    (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)).2
  rw [eq_of_ofFn (show List.ofFn (vLq + vL3) = List.ofFn vL1 by decide +kernel)] at hq3
  refine liftsCommute_of_conj_eq_mul hη hC (w := xr vL3) (g := xr vLq) ?_ ?_ ?_
  · exact xr_commute hK (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact conj_eq_self_of_commute (xr_commute hK (rootPair_of_ofFn (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · rw [conj_eq_commutatorElement_mul, hq3]

include hK hη hC in
theorem liftsCommute_shortRow : LiftsCommute η (xr vS2) (xr vS1) := by
  have hq3 := (xr_commutatorElement_obtuse (K := K) hK (r := vSq) (s := vS3)
    (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)).2
  rw [eq_of_ofFn (show List.ofFn (vSq + vS3) = List.ofFn vS1 by decide +kernel)] at hq3
  refine liftsCommute_of_conj_eq_mul hη hC (w := xr vS3) (g := xr vSq) ?_ ?_ ?_
  · exact xr_commute hK (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact conj_eq_self_of_commute (xr_commute hK (rootPair_of_ofFn (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · rw [conj_eq_commutatorElement_mul, hq3]

include hK hη hC in
theorem liftsCommute_mixedOrth : LiftsCommute η (xr vS1) (xr vE23) := by
  have hδ := (xr_commutatorElement_obtuse (K := K) hK (r := vE3m4) (s := vE24)
    (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)).2
  rw [eq_of_ofFn (show List.ofFn (vE3m4 + vE24) = List.ofFn vE23 by decide +kernel)] at hδ
  refine liftsCommute_of_conj_eq_mul hη hC (w := xr vE24) (g := xr vE3m4) ?_ ?_ ?_
  · exact xr_commute hK (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact conj_eq_self_of_commute (xr_commute hK (rootPair_of_ofFn (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · rw [conj_eq_commutatorElement_mul, hδ]

include hK hη hC in
theorem liftsCommute_mixedAcute : LiftsCommute η (xr vS1) (xr vE12) := by
  obtain ⟨-, -, -, -, -, h6⟩ := xr_commutatorElement_mixed (K := K) hK (r := vL1) (s := vE2)
    (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rw [eq_of_ofFn (show List.ofFn (vL1 + vE2) = List.ofFn vS1 by decide +kernel),
    eq_of_ofFn (show List.ofFn (vL1 + 2 • vE2) = List.ofFn vE12 by decide +kernel)] at h6
  refine LiftsCommute.of_mul_left (liftsCommute_of_conj_eq_mul hη hC (w := xr vL1)
    (g := xr vE2) ?_ ?_ ?_)
  · exact xr_commute hK (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact conj_eq_self_of_commute (xr_commute hK (rootPair_of_ofFn (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · rw [conj_eq_commutatorElement_mul, h6]

include hK hη in
theorem liftsCommute_of_rep {r₀ s₀ : Fin Tag.F4.rank → ℤ} (h₀ : RootPair r₀ s₀)
    (hc : LiftsCommute η (xr r₀) (xr s₀)) {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s)
    (h1 : f4Len r₀ = f4Len r) (h2 : f4Len s₀ = f4Len s) (h3 : f4Ip r₀ s₀ = f4Ip r s) :
    LiftsCommute η (xr r) (xr s) := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair hK h₀ h h1 h2 h3
  have := hc.conj hη g
  rwa [hg1, hg2] at this

include hK hη hC in
theorem liftsCommute_longOrth : LiftsCommute η (xr vE12) (xr vE34) := by
  obtain ⟨-, -, -, -, -, h6⟩ := xr_commutatorElement_mixed (K := K) hK (r := vL1) (s := vMa4)
    (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rw [eq_of_ofFn (show List.ofFn (vL1 + vMa4) = List.ofFn vHalf by decide +kernel),
    eq_of_ofFn (show List.ofFn (vL1 + 2 • vMa4) = List.ofFn vE34 by decide +kernel)] at h6
  have hbs : LiftsCommute η (xr vE12) (xr vHalf) :=
    liftsCommute_of_rep hK hη (rootPair_of_ofFn (by decide +kernel))
      (liftsCommute_mixedOrth hK hη hC).symm (rootPair_of_ofFn (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine LiftsCommute.of_mul_right hη (liftsCommute_of_conj_eq_mul hη hC (w := xr vL1)
    (g := xr vMa4) ?_ ?_ ?_) hbs
  · exact xr_commute hK (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact conj_eq_self_of_commute (xr_commute hK (rootPair_of_ofFn (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · rw [conj_eq_commutatorElement_mul, h6]

theorem f4_pair_invariants : ∀ k k' : Fin 48,
    (f4Len (Tag.F4.rootCertificate.root k) = 1 ∨ f4Len (Tag.F4.rootCertificate.root k) = 2) ∧
    (f4Ip (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k') ∈
      ({-2, -1, -1 / 2, 0, 1 / 2, 1, 2} : Finset ℚ)) := by
  decide +kernel

theorem f4Len_of_isRoot {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) :
    f4Len r = 1 ∨ f4Len r = 2 := by
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.mp hr
  exact (f4_pair_invariants k k).1

theorem f4Ip_comm (r s : Fin Tag.F4.rank → ℤ) : f4Ip r s = f4Ip s r :=
  dotProduct_comm _ _

include hK hη hC in
theorem liftsCommute_xr {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s)
    (hrs : (f4Len r = f4Len s ∧ 2 * f4Ip r s = f4Len r) ∨
      (f4Len r = 2 ∧ f4Len s = 2 ∧ f4Ip r s = 0) ∨
      (f4Len r = 1 ∧ f4Len s = 2 ∧ (f4Ip r s = 0 ∨ f4Ip r s = 1)) ∨
      (f4Len r = 2 ∧ f4Len s = 1 ∧ (f4Ip r s = 0 ∨ f4Ip r s = 1))) :
    LiftsCommute η (xr r) (xr s) := by
  have hmixed : ∀ {r s : Fin Tag.F4.rank → ℤ}, RootPair r s → f4Len r = 1 → f4Len s = 2 →
      (f4Ip r s = 0 ∨ f4Ip r s = 1) → LiftsCommute η (xr r) (xr s) := by
    intro r s h hr hs hip
    rcases hip with hip | hip
    · exact liftsCommute_of_rep hK hη (rootPair_of_ofFn (by decide +kernel))
        (liftsCommute_mixedOrth hK hη hC) h (by rw [hr]; decide +kernel)
        (by rw [hs]; decide +kernel) (by rw [hip]; decide +kernel)
    · exact liftsCommute_of_rep hK hη (rootPair_of_ofFn (by decide +kernel))
        (liftsCommute_mixedAcute hK hη hC) h (by rw [hr]; decide +kernel)
        (by rw [hs]; decide +kernel) (by rw [hip]; decide +kernel)
  rcases hrs with ⟨hl, hip⟩ | ⟨hr, hs, hip⟩ | ⟨hr, hs, hip⟩ | ⟨hr, hs, hip⟩
  · rcases f4Len_of_isRoot h.1 with hr | hr
    · have hip' : f4Ip r s = 1 / 2 := by linarith
      exact liftsCommute_of_rep hK hη (rootPair_of_ofFn (by decide +kernel))
        (liftsCommute_shortRow hK hη hC) h (by rw [hr]; decide +kernel)
        (by rw [← hl, hr]; decide +kernel) (by rw [hip']; decide +kernel)
    · have hip' : f4Ip r s = 1 := by linarith
      exact liftsCommute_of_rep hK hη (rootPair_of_ofFn (by decide +kernel))
        (liftsCommute_longRow hK hη hC) h (by rw [hr]; decide +kernel)
        (by rw [← hl, hr]; decide +kernel) (by rw [hip']; decide +kernel)
  · exact liftsCommute_of_rep hK hη (rootPair_of_ofFn (by decide +kernel))
      (liftsCommute_longOrth hK hη hC) h (by rw [hr]; decide +kernel)
      (by rw [hs]; decide +kernel) (by rw [hip]; decide +kernel)
  · exact hmixed h hr hs hip
  · exact (hmixed h.symm hs hr (by rwa [f4Ip_comm])).symm

theorem f4_exists_acute : ∀ k : Fin 48,
    (f4Len (Tag.F4.rootCertificate.root k) = 2 → ∃ k' : Fin 48,
      f4Len (Tag.F4.rootCertificate.root k') = 2 ∧
        f4Ip (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k') = 1) ∧
    (f4Len (Tag.F4.rootCertificate.root k) = 1 → ∃ k' : Fin 48,
      f4Len (Tag.F4.rootCertificate.root k') = 1 ∧
        f4Ip (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k') = 1 / 2) := by
  decide +kernel

include hK hη hC in
theorem exists_lift_mul_self_xr {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) :
    ∃ y, η y = xr r ∧ y * y = 1 := by
  have hlong : ∃ y, η y = xr vL1 ∧ y * y = 1 := by
    have hq3 := (xr_commutatorElement_obtuse (K := K) hK (r := vLq) (s := vL3)
      (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)).2
    rw [eq_of_ofFn (show List.ofFn (vLq + vL3) = List.ofFn vL1 by decide +kernel)] at hq3
    refine exists_lift_mul_self_of_conj_eq_mul hη hC (w := xr vL3) (g := xr vLq)
      (xr_mul_self hK (isRoot_of_ofFn (by decide +kernel)))
      (liftsCommute_xr hK hη hC (rootPair_of_ofFn (by decide +kernel))
        (Or.inl ⟨by decide +kernel, by decide +kernel⟩)) ?_
    rw [conj_eq_commutatorElement_mul, hq3]
  have hshort : ∃ y, η y = xr vS1 ∧ y * y = 1 := by
    have hq3 := (xr_commutatorElement_obtuse (K := K) hK (r := vSq) (s := vS3)
      (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)).2
    rw [eq_of_ofFn (show List.ofFn (vSq + vS3) = List.ofFn vS1 by decide +kernel)] at hq3
    refine exists_lift_mul_self_of_conj_eq_mul hη hC (w := xr vS3) (g := xr vSq)
      (xr_mul_self hK (isRoot_of_ofFn (by decide +kernel)))
      (liftsCommute_xr hK hη hC (rootPair_of_ofFn (by decide +kernel))
        (Or.inl ⟨by decide +kernel, by decide +kernel⟩)) ?_
    rw [conj_eq_commutatorElement_mul, hq3]
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.mp hr
  rcases f4Len_of_isRoot hr with hl | hl
  · obtain ⟨k', hk'l, hk'ip⟩ := (f4_exists_acute k).2 hl
    have hs := isRoot_f4_iff.mpr ⟨k', rfl⟩
    have h' : RootPair (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k') :=
      rootPair_of_ip hr hs (by rw [hk'ip, hl]; norm_num) (by rw [hk'ip, hl]; norm_num)
    obtain ⟨g, hg, -⟩ := exists_conj_pair hK (r := vS1) (s := vS3)
      (rootPair_of_ofFn (by decide +kernel)) h' (by rw [hl]; decide +kernel)
      (by rw [hk'l]; decide +kernel) (by rw [hk'ip]; decide +kernel)
    have := exists_lift_mul_self_conj hη hshort g
    rwa [hg] at this
  · obtain ⟨k', hk'l, hk'ip⟩ := (f4_exists_acute k).1 hl
    have hs := isRoot_f4_iff.mpr ⟨k', rfl⟩
    have h' : RootPair (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k') :=
      rootPair_of_ip hr hs (by rw [hk'ip, hl]; norm_num) (by rw [hk'ip, hl]; norm_num)
    obtain ⟨g, hg, -⟩ := exists_conj_pair hK (r := vL1) (s := vL3)
      (rootPair_of_ofFn (by decide +kernel)) h' (by rw [hl]; decide +kernel)
      (by rw [hk'l]; decide +kernel) (by rw [hk'ip]; decide +kernel)
    have := exists_lift_mul_self_conj hη hlong g
    rwa [hg] at this

end CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
