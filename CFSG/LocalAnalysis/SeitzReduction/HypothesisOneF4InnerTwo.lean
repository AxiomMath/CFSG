module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4Inner
public import CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCoverRoots

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover (xr RootPair f4Len f4Ip)
open CFSG.LieType.Ree (ReeTag)
open scoped commutatorElement

theorem le_closure_odd_of_le_commutator {G : Type*} [Group G] [Finite G] {t : G}
    {A P : Subgroup G} (hAP : A ≤ P) (hPt : ∀ x ∈ P, x * t = t * x) (hA : A ≤ ⁅A, P⁆) :
    A ≤ closure {c : G | c * t = t * c ∧ Odd (orderOf c)} := by
  classical
  set M := closure {c : G | c * t = t * c ∧ Odd (orderOf c)} with hM
  have hconj : ∀ g ∈ P, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hg m hm
    induction hm using closure_induction with
    | mem c hc =>
      refine subset_closure ⟨?_, ?_⟩
      · have h1 : Commute g t := hPt g hg
        have h2 : Commute c t := hc.1
        exact ((h1.mul_left h2).mul_left h1.inv_left).eq
      · rw [show g * c * g⁻¹ = MulAut.conj g c from rfl, MulEquiv.orderOf_eq]
        exact hc.2
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx
  let N : Subgroup P := M.subgroupOf P
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hconj g g.2 n hn⟩
  have h2 : IsPGroup 2 (P ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine subset_closure ⟨?_, ?_⟩
      · rw [Subgroup.coe_pow]
        exact (Commute.pow_left (hPt x x.2 : Commute (x : G) t) (2 ^ k)).eq
      · rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd (by positivity) (Dvd.intro m hxm.symm), hxm,
          Nat.mul_div_cancel_left _ (by positivity)]
        exact hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 h2.isNilpotent
  let π : P →* P ⧸ N := QuotientGroup.mk' N
  let A' : Subgroup (P ⧸ N) := (A.subgroupOf P).map π
  have hA'' : A.subgroupOf P ≤ ⁅A.subgroupOf P, ⊤⁆ := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    have e : ⁅A, P⁆ = Subgroup.map P.subtype ⁅A.subgroupOf P, (⊤ : Subgroup P)⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAP, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have h1 := hA ha
    rw [e] at h1
    obtain ⟨b, hb, hba⟩ := h1
    rwa [show a = b from Subtype.ext hba.symm]
  have hA' : A' ≤ ⁅A', ⊤⁆ :=
    calc A' ≤ Subgroup.map π ⁅A.subgroupOf P, (⊤ : Subgroup P)⁆ := Subgroup.map_mono hA''
      _ = ⁅A', (⊤ : Subgroup P).map π⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅A', ⊤⁆ := Subgroup.commutator_mono le_rfl le_top
  have hlcs : ∀ n, A' ≤ (⊤ : Subgroup (P ⧸ N)).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact hA'.trans (Subgroup.commutator_mono ih le_rfl)
  intro a ha
  have hmem : π ⟨a, hAP ha⟩ ∈ A' :=
    ⟨⟨a, hAP ha⟩, by simpa [Subgroup.mem_subgroupOf] using ha, rfl⟩
  have h1 := hlcs n hmem
  rw [hn, Subgroup.mem_bot] at h1
  have h3 := (QuotientGroup.eq_one_iff _).1 h1
  rwa [Subgroup.mem_subgroupOf] at h3

@[expose] def f4NeBool (r s : Fin Tag.F4.rank → ℤ) : Bool :=
  (List.ofFn r != List.ofFn s) && (List.ofFn r != List.ofFn (-s))

@[expose] def f4ObtuseRule (a b g : ℕ) : Bool :=
  f4NeBool (orbitCertRoot .F4 a) (orbitCertRoot .F4 b) &&
    decide (f4Len (orbitCertRoot .F4 a) = f4Len (orbitCertRoot .F4 b)) &&
    decide (2 * f4Ip (orbitCertRoot .F4 a) (orbitCertRoot .F4 b) =
      -f4Len (orbitCertRoot .F4 a)) &&
    (List.ofFn (orbitCertRoot .F4 a + orbitCertRoot .F4 b) == List.ofFn (orbitCertRoot .F4 g))

@[expose] def f4MixedRule (a b g d : ℕ) : Bool :=
  f4NeBool (orbitCertRoot .F4 a) (orbitCertRoot .F4 b) &&
    decide (f4Len (orbitCertRoot .F4 a) = 2) && decide (f4Len (orbitCertRoot .F4 b) = 1) &&
    decide (f4Ip (orbitCertRoot .F4 a) (orbitCertRoot .F4 b) = -1) &&
    (((List.ofFn (orbitCertRoot .F4 a + orbitCertRoot .F4 b) == List.ofFn (orbitCertRoot .F4 d)) &&
      (List.ofFn (orbitCertRoot .F4 a + 2 • orbitCertRoot .F4 b) ==
        List.ofFn (orbitCertRoot .F4 g))) ||
    ((List.ofFn (orbitCertRoot .F4 a + orbitCertRoot .F4 b) == List.ofFn (orbitCertRoot .F4 g)) &&
      (List.ofFn (orbitCertRoot .F4 a + 2 • orbitCertRoot .F4 b) ==
        List.ofFn (orbitCertRoot .F4 d))))

@[expose] def f4CommuteRule (a b : ℕ) : Bool :=
  f4NeBool (orbitCertRoot .F4 a) (orbitCertRoot .F4 b) &&
    !decide (f4Len (orbitCertRoot .F4 a) = f4Len (orbitCertRoot .F4 b) ∧
      2 * f4Ip (orbitCertRoot .F4 a) (orbitCertRoot .F4 b) = -f4Len (orbitCertRoot .F4 a)) &&
    !decide (f4Len (orbitCertRoot .F4 a) = 2 ∧ f4Len (orbitCertRoot .F4 b) = 1 ∧
      f4Ip (orbitCertRoot .F4 a) (orbitCertRoot .F4 b) = -1) &&
    !decide (f4Len (orbitCertRoot .F4 a) = 1 ∧ f4Len (orbitCertRoot .F4 b) = 2 ∧
      f4Ip (orbitCertRoot .F4 a) (orbitCertRoot .F4 b) = -1)

@[expose] def f4StepOK (SA SP done : List ℕ) (s : ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (s.2.1 < 48) && decide (s.2.2.1 < 48) &&
    ((decide (s.2.1 ∈ SA) && decide (s.2.2.1 ∈ SP)) ||
      (decide (s.2.1 ∈ SP) && decide (s.2.2.1 ∈ SA))) &&
    (f4ObtuseRule s.2.1 s.2.2.1 s.1 ||
      (decide (s.2.2.2 ∈ done) && f4MixedRule s.2.1 s.2.2.1 s.1 s.2.2.2))

@[expose] def f4DerivOK (SA SP : List ℕ) : List ℕ → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | done, s :: L => f4StepOK SA SP done s && f4DerivOK SA SP (s.1 :: done) L

theorem isRoot_orbitCertRoot_F4
    {p : ℕ} (hp : p < 48) : IsRoot .F4 (orbitCertRoot .F4 p) :=
  isRoot_decodeVec_witness (by rw [f4_witnesses_length]; exact hp)

theorem rootPair_of_f4NeBool {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (h : f4NeBool r s = true) : RootPair r s := by
  simp only [f4NeBool, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨hr, hs, fun e => h.1 (congrArg List.ofFn e), fun e => h.2 (congrArg List.ofFn e)⟩

theorem eq_zero_or_eq_one_of_card_eq_two {K : Type} [Field K] (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  have h' : c * (c - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

@[expose] def f4ParabolicOne : List ℕ := List.range' 15 33

@[expose] def f4ParabolicOneDeriv : List (ℕ × ℕ × ℕ × ℕ) :=
  [(33, 15, 39, 0), (34, 15, 42, 0), (37, 15, 45, 0), (40, 15, 46, 0), (18, 16, 25, 0),
    (19, 16, 26, 0), (21, 16, 28, 0), (22, 16, 29, 0), (35, 16, 43, 0), (36, 16, 44, 0),
    (20, 17, 25, 19), (27, 17, 28, 22), (47, 17, 43, 36), (39, 17, 45, 0), (42, 17, 46, 0),
    (16, 18, 22, 0), (23, 18, 28, 0), (25, 18, 31, 0), (38, 18, 44, 0), (24, 19, 29, 0),
    (26, 19, 31, 0), (15, 20, 21, 18), (17, 20, 22, 19), (30, 20, 28, 25), (32, 20, 29, 26),
    (45, 20, 46, 0), (28, 21, 31, 0), (41, 21, 44, 0), (29, 22, 31, 0), (43, 23, 44, 0),
    (44, 24, 43, 0), (31, 25, 29, 0), (46, 27, 45, 0)]

theorem f4ParabolicOne_check :
    f4DerivOK f4ParabolicOne f4ParabolicOne [] f4ParabolicOneDeriv = true ∧
      (∀ p ∈ f4ParabolicOne, p ∈ f4ParabolicOneDeriv.map Prod.fst) ∧
      (∀ p ∈ f4ParabolicOne, p < 48 ∧ (p = 47 ∨ f4CommuteRule p 47 = true)) := by
  decide +kernel


variable {K : Type} [Field K]

theorem f4_step_sound (hK : Nat.card K = 2) {A P : Subgroup (adjointGroup .F4 K)}
    {SA SP done : List ℕ} (hSA : ∀ p ∈ SA, xr (K := K) (orbitCertRoot .F4 p) ∈ A)
    (hSP : ∀ p ∈ SP, xr (K := K) (orbitCertRoot .F4 p) ∈ P)
    (hdone : ∀ p ∈ done, xr (K := K) (orbitCertRoot .F4 p) ∈ ⁅A, P⁆) {s : ℕ × ℕ × ℕ × ℕ}
    (hs : f4StepOK SA SP done s = true) : xr (K := K) (orbitCertRoot .F4 s.1) ∈ ⁅A, P⁆ := by
  obtain ⟨g, a, b, d⟩ := s
  simp only [f4StepOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨ha, hb⟩, hab⟩, hrule⟩ := hs
  have hc : ⁅xr (K := K) (orbitCertRoot .F4 a), xr (K := K) (orbitCertRoot .F4 b)⁆ ∈ ⁅A, P⁆ := by
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact commutator_mem_commutator (hSA a h1) (hSP b h2)
    · rw [Subgroup.commutator_comm]
      exact commutator_mem_commutator (hSP a h1) (hSA b h2)
  rcases hrule with hob | ⟨hd, hmix⟩
  · simp only [f4ObtuseRule, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hob
    obtain ⟨⟨⟨hne, hl⟩, hip⟩, hsum⟩ := hob
    have hpair := rootPair_of_f4NeBool (isRoot_orbitCertRoot_F4 ha) (isRoot_orbitCertRoot_F4 hb) hne
    have h := (CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover.xr_commutatorElement_obtuse
      (K := K) hK hpair hl hip).2
    rw [List.ofFn_injective hsum] at h
    rw [← h]
    exact hc
  · simp only [f4MixedRule, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hmix
    obtain ⟨⟨⟨⟨hne, hA⟩, hB⟩, hC⟩, hsums⟩ := hmix
    have hpair := rootPair_of_f4NeBool (isRoot_orbitCertRoot_F4 ha) (isRoot_orbitCertRoot_F4 hb) hne
    obtain ⟨-, -, -, -, h5, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover.xr_commutatorElement_mixed (K := K) hK
        hpair hA hB hC
    have hdm := hdone d hd
    rcases hsums with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [List.ofFn_injective e1, List.ofFn_injective e2] at h5
      have e : xr (K := K) (orbitCertRoot .F4 g) = (xr (K := K) (orbitCertRoot .F4 d))⁻¹ *
          ⁅xr (K := K) (orbitCertRoot .F4 a), xr (K := K) (orbitCertRoot .F4 b)⁆ := by
        rw [h5]; group
      rw [e]
      exact mul_mem (inv_mem hdm) hc
    · rw [List.ofFn_injective e1, List.ofFn_injective e2] at h5
      have e : xr (K := K) (orbitCertRoot .F4 g) =
          ⁅xr (K := K) (orbitCertRoot .F4 a), xr (K := K) (orbitCertRoot .F4 b)⁆ *
            (xr (K := K) (orbitCertRoot .F4 d))⁻¹ := by
        rw [h5]; group
      rw [e]
      exact mul_mem hc (inv_mem hdm)

theorem f4_deriv_sound (hK : Nat.card K = 2) {A P : Subgroup (adjointGroup .F4 K)}
    {SA SP : List ℕ} (hSA : ∀ p ∈ SA, xr (K := K) (orbitCertRoot .F4 p) ∈ A)
    (hSP : ∀ p ∈ SP, xr (K := K) (orbitCertRoot .F4 p) ∈ P) :
    ∀ (L : List (ℕ × ℕ × ℕ × ℕ)) (done : List ℕ),
      (∀ p ∈ done, xr (K := K) (orbitCertRoot .F4 p) ∈ ⁅A, P⁆) →
      f4DerivOK SA SP done L = true → ∀ s ∈ L, xr (K := K) (orbitCertRoot .F4 s.1) ∈ ⁅A, P⁆
  | [], _, _, _ => by simp
  | s :: L, done, hdone, h => by
    simp only [f4DerivOK, Bool.and_eq_true] at h
    have h1 := f4_step_sound hK hSA hSP hdone h.1
    intro s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact h1
    · refine f4_deriv_sound hK hSA hSP L (s.1 :: done) (fun p hp => ?_) h.2 s' hs'
      rcases List.mem_cons.1 hp with rfl | hp
      · exact h1
      · exact hdone p hp

theorem f4_commute_sound (hK : Nat.card K = 2) {a b : ℕ} (ha : a < 48) (hb : b < 48)
    (h : f4CommuteRule a b = true) :
    xr (K := K) (orbitCertRoot .F4 a) * xr (K := K) (orbitCertRoot .F4 b) =
      xr (K := K) (orbitCertRoot .F4 b) * xr (K := K) (orbitCertRoot .F4 a) := by
  simp only [f4CommuteRule, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨hne, h1⟩, h2⟩, h3⟩ := h
  exact CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover.xr_commute hK
    (rootPair_of_f4NeBool (isRoot_orbitCertRoot_F4 ha) (isRoot_orbitCertRoot_F4 hb) hne) h1 h2 h3

theorem mem_of_mem_posUnipotent_of_forall_xr (hK : Nat.card K = 2)
    {H : Subgroup (adjointGroup .F4 K)}
    (h : ∀ p, 24 ≤ p → p ≤ 47 → xr (K := K) (orbitCertRoot .F4 p) ∈ H)
    {u : adjointGroup .F4 K} (hu : (u : ModGL .F4 K) ∈ posUnipotent .F4 K) : u ∈ H := by
  refine mem_of_mem_posUnipotent_of_forall_f4x (fun p hp hp' c => ?_) hu
  rcases eq_zero_or_eq_one_of_card_eq_two hK c with rfl | rfl
  · convert one_mem H
    exact Subtype.ext (f4x_zero p)
  · exact h p hp hp'

theorem posUnipotent_le_closure_odd_longRoot_two [Finite K] (hK : Nat.card K = 2)
    {u : adjointGroup .F4 K} (hu : (u : ModGL .F4 K) ∈ posUnipotent .F4 K) :
    u ∈ closure {c : adjointGroup .F4 K | c * xr (orbitCertRoot .F4 47) =
      xr (orbitCertRoot .F4 47) * c ∧ Odd (orderOf c)} := by
  have : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨hder, hcov, hcomm⟩ := f4ParabolicOne_check
  set P : Subgroup (adjointGroup .F4 K) :=
    closure ((fun p => xr (K := K) (orbitCertRoot .F4 p)) '' {p | p ∈ f4ParabolicOne}) with hP
  have hgen : ∀ p ∈ f4ParabolicOne, xr (K := K) (orbitCertRoot .F4 p) ∈ P :=
    fun p hp => subset_closure ⟨p, hp, rfl⟩
  have hPt : ∀ x ∈ P, x * xr (orbitCertRoot .F4 47) = xr (orbitCertRoot .F4 47) * x := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨hp48, h47 | hc⟩ := hcomm p hp
      · rw [h47]
      · exact f4_commute_sound hK hp48 (by norm_num) hc
    | one => rw [one_mul, mul_one]
    | mul x y _ _ hx hy => exact (Commute.mul_left (hx : Commute x _) hy).eq
    | inv x _ hx => exact (Commute.inv_left (hx : Commute x _)).eq
  have hperf : P ≤ ⁅P, P⁆ := by
    rw [hP, closure_le]
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (hcov p hp)
    exact f4_deriv_sound hK hgen hgen f4ParabolicOneDeriv [] (by simp) hder s hs
  have hU : u ∈ P := mem_of_mem_posUnipotent_of_forall_xr hK
    (fun p hp hp' => hgen p (List.mem_range'_1.2 ⟨by omega, by omega⟩)) hu
  exact le_closure_odd_of_le_commutator le_rfl hPt hperf hU

theorem innerCentralizerCriterion_F4_longRoot_two [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    InnerCentralizerCriterion
      (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) :=
  innerCentralizerCriterion_F4_of_posUnipotent_le le_rfl (by rw [pow_one]; exact hK)
    fun _ hu => posUnipotent_le_closure_odd_longRoot_two hK hu

theorem innerCentralizerCriterion_F4_longRoot' {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) := by
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact innerCentralizerCriterion_F4_longRoot_two (by simpa using hK)
  · exact innerCentralizerCriterion_F4_longRoot h hK

theorem innerCentralizerCriterion_F4_shortRoot' {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have h := (innerCentralizerCriterion_F4_longRoot' hf hK).map (f4Phi (K := K))
  rwa [(f4Phi_f4x_47_44 (K := K)).1] at h

end CFSG.SeitzReduction
