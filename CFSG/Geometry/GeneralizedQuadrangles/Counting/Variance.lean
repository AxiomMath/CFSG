module

public import CFSG.Geometry.GeneralizedQuadrangles.Counting.Variance2
public import Mathlib.Algebra.Order.Chebyshev

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V}

section Basic

variable [Fintype V] [DecidableRel Γ.Adj]

@[expose] noncomputable def varianceR [Fintype V] (Γ : SimpleGraph V) (X : Finset V)
    (z : V) : ℕ := by
  classical
  exact (X.filter fun a => Γ.dist z a = 2).card

theorem varianceR_eq_zero_of_mem_X (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {x y : V} (hxy : Γ.dist x y = 4) {X : Finset V} (hX : (X : Set V) ⊆ spanSet Γ x y)
    {a : V} (ha : a ∈ X) : varianceR Γ X a = 0 := by
  classical
  rw [varianceR, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro a' ha'
  rw [Finset.mem_filter] at ha'
  obtain ⟨ha'X, h2⟩ := ha'
  by_cases hne : a = a'
  · subst hne
    simp at h2
  · have h4 := dist_eq_four_of_mem_X hP hT hxy hX ha ha'X hne
    omega

theorem varianceR_eq_card_of_mem_varianceTrace (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {x y : V} (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) {u : V} (hu : u ∈ varianceTrace Γ x y) :
    varianceR Γ X u = X.card := by
  classical
  have hfilter : (X.filter fun a => Γ.dist u a = 2) = X := by
    refine Finset.filter_true_of_mem fun a ha => ?_
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX ha) hu
  rw [varianceR, hfilter]

theorem varianceR_le_one_of_not_mem_varianceTrace (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {x y : V} (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) {z : V} (hzT : z ∉ varianceTrace Γ x y) :
    varianceR Γ X z ≤ 1 := by
  classical
  rw [varianceR]
  refine Finset.card_le_one_iff.mpr ?_
  intro a a' ha ha'
  rw [Finset.mem_filter] at ha ha'
  obtain ⟨haX, h2a⟩ := ha
  obtain ⟨ha'X, h2a'⟩ := ha'
  by_contra hne
  have hzIn : z ∈ traceSet Γ x y := by
    have htrace := (span_eq_of_mem hP hT hxy (hX haX) (hX ha'X) hne).2.2
    rw [← htrace]
    exact ⟨by rwa [SimpleGraph.dist_comm], by rwa [SimpleGraph.dist_comm]⟩
  exact hzT (by simpa [mem_varianceTrace] using hzIn)

theorem varianceR_eq_zero_of_mem_varianceZ {c : Γ.Coloring (Fin 2)} {X : Finset V}
    {z : V} (hz : z ∈ varianceZ Γ c X) : varianceR Γ X z = 0 := by
  classical
  rw [mem_varianceZ] at hz
  rw [varianceR, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro a ha
  rw [Finset.mem_filter] at ha
  have := hz.2 a ha.1
  omega

theorem not_mem_X_of_mem_varianceZ {c : Γ.Coloring (Fin 2)} {X : Finset V} {z : V}
    (hz : z ∈ varianceZ Γ c X) : z ∉ X := by
  intro hzX
  rw [mem_varianceZ] at hz
  have := hz.2 z hzX
  simp at this

theorem mem_varianceZ_of_varianceR_eq_zero (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {c : Γ.Coloring (Fin 2)} {x y : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) {X : Finset V} (hX : (X : Set V) ⊆ spanSet Γ x y)
    {z : V} (hz0 : c z = 0) (hzX : z ∉ X) (hr : varianceR Γ X z = 0) :
    z ∈ varianceZ Γ c X := by
  classical
  rw [varianceR, Finset.card_eq_zero] at hr
  rw [mem_varianceZ]
  refine ⟨hz0, fun a haX => ?_⟩
  have h2 : Γ.dist z a ≠ 2 := by
    intro h2
    have hmem : a ∈ X.filter (fun a => Γ.dist z a = 2) :=
      Finset.mem_filter.mpr ⟨haX, h2⟩
    rw [hr] at hmem
    simp at hmem
  have hza : z ≠ a := by
    intro h
    exact hzX (by simpa [h] using haX)
  have hca : c a = 0 := color_eq_zero_of_mem_span hP hT hx hxy (hX haX)
  exact two_lt_dist_of_ne_of_not_dist_two hP hz0 hca hza h2

theorem card_noncollinear_add (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) :
    (varianceZ Γ c X).card + (X.card - 1) * (s * t + s - t) = s ^ 2 * t := by
  classical
  let P := pointFinset c
  let T := varianceTrace Γ x y
  let Z := varianceZ Γ c X
  let R := P.filter fun z => z ∉ X ∧ z ∉ T ∧ z ∉ Z
  let r : V → ℕ := varianceR Γ X
  have hXP : X ⊆ P := by
    intro a ha
    rw [show P = pointFinset c from rfl, mem_pointFinset]
    exact color_eq_zero_of_mem_span hP hT hx hxy (hX ha)
  have hTP : T ⊆ P := by
    intro u hu
    rw [show P = pointFinset c from rfl, mem_pointFinset]
    exact color_eq_zero_of_mem_varianceTrace hP hx hu
  have hZP : Z ⊆ P := by
    intro z hz
    rw [show Z = varianceZ Γ c X from rfl, mem_varianceZ] at hz
    rw [show P = pointFinset c from rfl, mem_pointFinset]
    exact hz.1
  have hRP : R ⊆ P := Finset.filter_subset _ _
  have hXT : Disjoint X T := by
    rw [Finset.disjoint_left]
    intro u huX huT
    exact not_mem_X_of_mem_varianceTrace hP hT hxy hX huT huX
  have hXZ : Disjoint X Z := by
    rw [Finset.disjoint_left]
    intro z hzX hzZ
    exact not_mem_X_of_mem_varianceZ hzZ hzX
  have hTZ : Disjoint T Z := by
    rw [Finset.disjoint_left]
    intro z hzT hzZ
    exact not_mem_varianceTrace_of_mem_varianceZ hP hT hxy hX hm hzZ hzT
  have hRX : Disjoint R X := by
    rw [Finset.disjoint_left]
    intro z hzR hzX
    have hz' : z ∈ P ∧ z ∉ X ∧ z ∉ T ∧ z ∉ Z := by
      simpa only [R, Finset.mem_filter] using hzR
    exact hz'.2.1 hzX
  have hRT : Disjoint R T := by
    rw [Finset.disjoint_left]
    intro z hzR hzT
    have hz' : z ∈ P ∧ z ∉ X ∧ z ∉ T ∧ z ∉ Z := by
      simpa only [R, Finset.mem_filter] using hzR
    exact hz'.2.2.1 hzT
  have hRZ : Disjoint R Z := by
    rw [Finset.disjoint_left]
    intro z hzR hzZ
    have hz' : z ∈ P ∧ z ∉ X ∧ z ∉ T ∧ z ∉ Z := by
      simpa only [R, Finset.mem_filter] using hzR
    exact hz'.2.2.2 hzZ
  have hZR : Disjoint Z R := hRZ.symm
  have hUV : Disjoint (X ∪ T) (Z ∪ R) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rcases Finset.mem_union.mp hz with hzX | hzT
    · rcases Finset.mem_union.mp hz' with hzZ | hzR
      · exact (Finset.disjoint_left.mp hXZ) hzX hzZ
      · exact (Finset.disjoint_left.mp hRX) hzR hzX
    · rcases Finset.mem_union.mp hz' with hzZ | hzR
      · exact (Finset.disjoint_left.mp hTZ) hzT hzZ
      · exact (Finset.disjoint_left.mp hRT) hzR hzT
  have hpart : P = (X ∪ T) ∪ (Z ∪ R) := by
    ext z
    constructor
    · intro hzP
      by_cases hzX : z ∈ X
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hzX)
      · by_cases hzT : z ∈ T
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hzT)
        · by_cases hzZ : z ∈ Z
          · exact Finset.mem_union_right _ (Finset.mem_union_left _ hzZ)
          · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
            have : z ∈ P.filter (fun z => z ∉ X ∧ z ∉ T ∧ z ∉ Z) :=
              Finset.mem_filter.mpr ⟨hzP, hzX, hzT, hzZ⟩
            simpa only [R] using this
    · intro hz
      rcases Finset.mem_union.mp hz with hz' | hz'
      · rcases Finset.mem_union.mp hz' with hzX | hzT
        · exact hXP hzX
        · exact hTP hzT
      · rcases Finset.mem_union.mp hz' with hzZ | hzR
        · exact hZP hzZ
        · exact hRP hzR
  have hPcard : P.card = X.card + T.card + Z.card + R.card := by
    rw [hpart, Finset.card_union_of_disjoint hUV, Finset.card_union_of_disjoint hXT,
      Finset.card_union_of_disjoint hZR]
    omega
  have hsumP : ∑ z ∈ P, r z = X.card * (s * (t + 1)) := by
    have h1 : ∑ z ∈ P, r z
        = ∑ z ∈ P, ∑ a ∈ X, (if Γ.dist z a = 2 then 1 else 0) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      change (X.filter fun a => Γ.dist z a = 2).card
        = ∑ a ∈ X, (if Γ.dist z a = 2 then 1 else 0)
      rw [Finset.card_filter]
    rw [h1, Finset.sum_comm]
    have h2 : ∀ a ∈ X, ∑ z ∈ P, (if Γ.dist z a = 2 then 1 else 0) = s * (t + 1) := by
      intro a ha
      have hca : c a = 0 := by
        have := hXP ha
        simpa only [P, mem_pointFinset] using this
      rw [← Finset.card_filter]
      have hPfilter : P.filter (fun z => Γ.dist z a = 2)
          = Finset.univ.filter (fun z => Γ.dist a z = 2) := by
        ext z
        rw [show P = pointFinset c from rfl, Finset.mem_filter, Finset.mem_filter,
          mem_pointFinset]
        constructor
        · rintro ⟨-, h2⟩
          exact ⟨Finset.mem_univ _, by rwa [SimpleGraph.dist_comm]⟩
        · rintro ⟨-, h2⟩
          refine ⟨?_, by rwa [SimpleGraph.dist_comm]⟩
          rw [← hca]
          exact ((hP.eq_iff_even_dist c a z).2 (by rw [h2]; norm_num)).symm
      rw [hPfilter, card_collinear hP c hdeg hca]
    calc
      ∑ a ∈ X, ∑ z ∈ P, (if Γ.dist z a = 2 then 1 else 0)
          = ∑ a ∈ X, s * (t + 1) := Finset.sum_congr rfl h2
      _ = X.card * (s * (t + 1)) := by rw [Finset.sum_const, smul_eq_mul]
  have hsumT : ∑ z ∈ T, r z = X.card * T.card := by
    calc
      ∑ z ∈ T, r z = ∑ z ∈ T, X.card := by
        refine Finset.sum_congr rfl fun u hu => ?_
        exact varianceR_eq_card_of_mem_varianceTrace hP hT hxy hX hu
      _ = X.card * T.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hsumX : ∑ z ∈ X, r z = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    exact varianceR_eq_zero_of_mem_X hP hT hxy hX ha
  have hsumZ : ∑ z ∈ Z, r z = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    exact varianceR_eq_zero_of_mem_varianceZ hz
  have hsumR : ∑ z ∈ R, r z = R.card := by
    calc
      ∑ z ∈ R, r z = ∑ z ∈ R, 1 := by
        refine Finset.sum_congr rfl fun z hz => ?_
        have hz' : z ∈ P ∧ z ∉ X ∧ z ∉ T ∧ z ∉ Z := by
          simpa only [R, Finset.mem_filter] using hz
        have hle := varianceR_le_one_of_not_mem_varianceTrace hP hT hxy hX hz'.2.2.1
        have hne0 : r z ≠ 0 := by
          intro h0
          have hz0 : c z = 0 := by
            have := hz'.1
            simpa only [P, mem_pointFinset] using this
          exact hz'.2.2.2 (mem_varianceZ_of_varianceR_eq_zero hP hT hx hxy hX hz0 hz'.2.1 h0)
        dsimp only [r] at hne0 ⊢
        omega
      _ = R.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
  have hsumSplit : ∑ z ∈ P, r z
      = ∑ z ∈ X, r z + ∑ z ∈ T, r z + ∑ z ∈ Z, r z + ∑ z ∈ R, r z := by
    rw [hpart, Finset.sum_union hUV, Finset.sum_union hXT, Finset.sum_union hZR]
    ring
  have hRcard : R.card + X.card * T.card = X.card * T.card * s := by
    have h1 : ∑ z ∈ P, r z = X.card * T.card + R.card := by
      rw [hsumSplit, hsumX, hsumT, hsumZ, hsumR]
      ring
    have h1' : X.card * T.card + R.card = X.card * (s * T.card) := by
      calc
        X.card * T.card + R.card = ∑ z ∈ P, r z := h1.symm
        _ = X.card * (s * (t + 1)) := hsumP
        _ = X.card * (s * T.card) := by
              rw [show T = varianceTrace Γ x y from rfl,
                varianceTrace_card hP c hdeg hx hxy]
    calc
      R.card + X.card * T.card = X.card * T.card + R.card := Nat.add_comm _ _
      _ = X.card * (s * T.card) := h1'
      _ = X.card * T.card * s := by ring
  have hZeq : Z.card + X.card + T.card + X.card * T.card * s
      = P.card + X.card * T.card := by
    nlinarith [hPcard, hRcard]
  have hTcard : T.card = t + 1 := by
    rw [show T = varianceTrace Γ x y from rfl]
    exact varianceTrace_card hP c hdeg hx hxy
  have hPcardVal : P.card = (s + 1) * (s * t + 1) := by
    rw [show P = pointFinset c from rfl]
    exact card_pointFinset hP hT c hdeg
  rw [hTcard, hPcardVal] at hZeq
  have hZeqZ : (Z.card : ℤ) + (X.card : ℤ) + (t + 1) + (X.card : ℤ) * (t + 1) * s
      = ((s + 1) * (s * t + 1) : ℕ) + (X.card : ℤ) * (t + 1) := by
    push_cast
    exact_mod_cast hZeq
  have hm1 : ((X.card - 1 : ℕ) : ℤ) = (X.card : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ X.card)]
    norm_num
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have hst : ((s * t + s - t : ℕ) : ℤ) = (s : ℤ) * t + s - t := by
    have hle : t ≤ s * t + s := by
      have h1 : t ≤ s * t := by
        calc
          t = 1 * t := (Nat.one_mul t).symm
          _ ≤ s * t := Nat.mul_le_mul_right t (by omega)
      omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hgoalZ : (Z.card : ℤ) + (((X.card - 1) * (s * t + s - t) : ℕ) : ℤ)
      = ((s ^ 2 * t : ℕ) : ℤ) := by
    rw [Nat.cast_mul, hm1, hst]
    push_cast
    nlinarith [hZeqZ]
  exact_mod_cast hgoalZ

theorem sum_centres_sq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) :
    ∑ z ∈ varianceZ Γ c X, varianceTz Γ (varianceTrace Γ x y) z ^ 2
      = (t + 1) * t * (t + 1 - X.card) + (t + 1) * (t + 1 - X.card) * s := by
  classical
  have hsq : ∀ n : ℕ, n ^ 2 = n * (n - 1) + n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp
    · rw [pow_two, ← Nat.mul_succ, Nat.succ_eq_add_one,
        Nat.sub_one_add_one_eq_of_pos h]
  calc
    ∑ z ∈ varianceZ Γ c X, varianceTz Γ (varianceTrace Γ x y) z ^ 2
        = ∑ z ∈ varianceZ Γ c X,
            (varianceTz Γ (varianceTrace Γ x y) z *
                (varianceTz Γ (varianceTrace Γ x y) z - 1) +
              varianceTz Γ (varianceTrace Γ x y) z) := by
          refine Finset.sum_congr rfl fun z _ => hsq _
    _ = ∑ z ∈ varianceZ Γ c X,
            varianceTz Γ (varianceTrace Γ x y) z *
              (varianceTz Γ (varianceTrace Γ x y) z - 1) +
          ∑ z ∈ varianceZ Γ c X, varianceTz Γ (varianceTrace Γ x y) z := by
          rw [Finset.sum_add_distrib]
    _ = (t + 1) * t * (t + 1 - X.card) + (t + 1) * (t + 1 - X.card) * s := by
          rw [sum_centres_choose_two hP hT c hdeg hx hxy hX hm,
            sum_centres hP hT c hdeg hx hxy hX hm]

theorem variance_identity (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) :
    ((varianceZ Γ c X).card : ℤ) *
        (∑ z ∈ varianceZ Γ c X, (varianceTz Γ (varianceTrace Γ x y) z : ℤ) ^ 2) -
      (∑ z ∈ varianceZ Γ c X, (varianceTz Γ (varianceTrace Γ x y) z : ℤ)) ^ 2
      = (t + 1 : ℤ) * ((t + 1 - X.card : ℕ) : ℤ) * (t : ℤ) * ((s : ℤ) - 1) *
          ((s : ℤ) ^ 2 - ((X.card - 1 : ℕ) : ℤ) * (t : ℤ)) := by
  classical
  have hmle : X.card ≤ t + 1 :=
    card_le_t_add_one_of_subset_span hP hT c hdeg hx hxy hX
  have hm1 : 1 ≤ X.card := by omega
  have hm1c : ((X.card - 1 : ℕ) : ℤ) = (X.card : ℤ) - 1 := by
    rw [Nat.cast_sub hm1]
    norm_num
  have hsc : ((t + 1 - X.card : ℕ) : ℤ) = (t : ℤ) + 1 - (X.card : ℤ) := by
    rw [Nat.cast_sub hmle]
    push_cast
    ring
  have hst : ((s * t + s - t : ℕ) : ℤ) = (s : ℤ) * t + s - t := by
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    have hle : t ≤ s * t + s := by
      have h1 : t ≤ s * t := by
        calc
          t = 1 * t := (Nat.one_mul t).symm
          _ ≤ s * t := Nat.mul_le_mul_right t (by omega)
      omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hA : ((varianceZ Γ c X).card : ℤ) =
      ((s ^ 2 * t : ℕ) : ℤ) - (((X.card - 1) * (s * t + s - t) : ℕ) : ℤ) := by
    have h := card_noncollinear_add hP hT c hdeg hx hxy hX hm
    have hcast : ((varianceZ Γ c X).card : ℤ) +
        (((X.card - 1) * (s * t + s - t) : ℕ) : ℤ) = ((s ^ 2 * t : ℕ) : ℤ) := by
      exact_mod_cast h
    linarith
  have hA' : ((varianceZ Γ c X).card : ℤ) =
      (s : ℤ) ^ 2 * t - ((X.card : ℤ) - 1) * ((s : ℤ) * t + s - t) := by
    have hK : (((X.card - 1) * (s * t + s - t) : ℕ) : ℤ) =
        ((X.card : ℤ) - 1) * ((s : ℤ) * t + s - t) := by
      rw [Nat.cast_mul, hm1c, hst]
    rw [hK] at hA
    push_cast at hA
    linarith
  have hB : (∑ z ∈ varianceZ Γ c X, (varianceTz Γ (varianceTrace Γ x y) z : ℤ)) =
      (t + 1 : ℤ) * ((t : ℤ) + 1 - (X.card : ℤ)) * (s : ℤ) := by
    have h := sum_centres hP hT c hdeg hx hxy hX hm
    have hcast : (∑ z ∈ varianceZ Γ c X, (varianceTz Γ (varianceTrace Γ x y) z : ℤ))
        = (((t + 1) * (t + 1 - X.card) * s : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [hcast]
    push_cast
    rw [hsc]
  have hC : (∑ z ∈ varianceZ Γ c X, (varianceTz Γ (varianceTrace Γ x y) z : ℤ) ^ 2) =
      (t + 1 : ℤ) * (t : ℤ) * ((t : ℤ) + 1 - (X.card : ℤ)) +
        (t + 1 : ℤ) * ((t : ℤ) + 1 - (X.card : ℤ)) * (s : ℤ) := by
    have h := sum_centres_sq hP hT c hdeg hx hxy hX hm
    have hcast : (∑ z ∈ varianceZ Γ c X,
        (varianceTz Γ (varianceTrace Γ x y) z : ℤ) ^ 2) =
        (((t + 1) * t * (t + 1 - X.card) +
          (t + 1) * (t + 1 - X.card) * s : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [hcast]
    push_cast
    rw [hsc]
  rw [hm1c, hsc, hA', hB, hC]
  ring

theorem two_mul_card_mul_sum_sq_sub_sq_sum (T : Finset V) (f : V → ℤ) :
    2 * ((T.card : ℤ) * (∑ z ∈ T, f z ^ 2) - (∑ z ∈ T, f z) ^ 2)
      = ∑ z ∈ T, ∑ z' ∈ T, (f z - f z') ^ 2 := by
  classical
  have h1 : (∑ z ∈ T, f z) ^ 2 = ∑ z ∈ T, ∑ z' ∈ T, f z * f z' := by
    rw [pow_two, Finset.sum_mul_sum]
  have h2a : (T.card : ℤ) * (∑ z ∈ T, f z ^ 2) = ∑ z ∈ T, ∑ z' ∈ T, f z ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_const]
    simp
  have h2b : (T.card : ℤ) * (∑ z ∈ T, f z ^ 2) = ∑ z ∈ T, ∑ z' ∈ T, f z' ^ 2 := by
    rw [h2a]
    conv_lhs => rw [Finset.sum_comm]
  calc
    2 * ((T.card : ℤ) * (∑ z ∈ T, f z ^ 2) - (∑ z ∈ T, f z) ^ 2)
        = (T.card : ℤ) * (∑ z ∈ T, f z ^ 2) + (T.card : ℤ) * (∑ z ∈ T, f z ^ 2) -
          2 * (∑ z ∈ T, f z) ^ 2 := by
          ring
    _ = ((∑ z ∈ T, ∑ z' ∈ T, f z ^ 2) + (∑ z ∈ T, ∑ z' ∈ T, f z' ^ 2)) -
          2 * (∑ z ∈ T, ∑ z' ∈ T, f z * f z') := by
          nth_rewrite 1 [h2a]
          nth_rewrite 1 [h2b]
          rw [h1]
    _ = ∑ z ∈ T, ∑ z' ∈ T, (f z ^ 2 + f z' ^ 2 - 2 * (f z * f z')) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    _ = ∑ z ∈ T, ∑ z' ∈ T, (f z - f z') ^ 2 := by
          refine Finset.sum_congr rfl fun z _ => ?_
          refine Finset.sum_congr rfl fun z' _ => ?_
          ring

theorem exists_const_of_card_mul_sum_sq_eq_sq_sum (T : Finset V) (f : V → ℤ)
    (h : (T.card : ℤ) * (∑ z ∈ T, f z ^ 2) = (∑ z ∈ T, f z) ^ 2) :
    ∃ k, ∀ z ∈ T, f z = k := by
  classical
  have hzero : ∑ z ∈ T, ∑ z' ∈ T, (f z - f z') ^ 2 = 0 := by
    rw [← two_mul_card_mul_sum_sq_sub_sq_sum T f, h]
    ring
  have hinner : ∀ z ∈ T, ∀ z' ∈ T, f z = f z' := by
    intro z hz z' hz'
    have hnonneg : ∀ z ∈ T, 0 ≤ ∑ z' ∈ T, (f z - f z') ^ 2 := by
      intro z _
      exact Finset.sum_nonneg fun z' _ => sq_nonneg _
    have hzsum : ∑ z' ∈ T, (f z - f z') ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero z hz
    have hdiff : f z - f z' = 0 := by
      exact (Finset.sum_sq_eq_zero_iff T (fun z' => f z - f z')).mp hzsum z' hz'
    exact sub_eq_zero.mp hdiff
  by_cases hne : T.Nonempty
  · obtain ⟨z0, hz0⟩ := hne
    exact ⟨f z0, fun z hz => hinner z hz z0 hz0⟩
  · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne⟩

theorem centres_const_of_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) (hmt : X.card ≤ t)
    (heq : (X.card - 1) * t = s ^ 2) :
    ∃ k, ∀ z ∈ varianceZ Γ c X, varianceTz Γ (varianceTrace Γ x y) z = k := by
  classical
  let Z := varianceZ Γ c X
  let T := varianceTrace Γ x y
  let tz : V → ℕ := fun z => varianceTz Γ T z
  have hprod : ((X.card - 1 : ℕ) : ℤ) * (t : ℤ) = (s : ℤ) ^ 2 := by
    have hcast : (((X.card - 1) * t : ℕ) : ℤ) = ((s ^ 2 : ℕ) : ℤ) := by
      exact_mod_cast heq
    push_cast at hcast
    exact hcast
  have hzero : (Z.card : ℤ) * (∑ z ∈ Z, (tz z : ℤ) ^ 2) - (∑ z ∈ Z, (tz z : ℤ)) ^ 2 = 0 := by
    have hid := variance_identity hP hT c hdeg hx hxy hX hm
    dsimp only [Z, T, tz]
    rw [hid, hprod]
    ring
  have hAC : (Z.card : ℤ) * (∑ z ∈ Z, (tz z : ℤ) ^ 2) = (∑ z ∈ Z, (tz z : ℤ)) ^ 2 := by
    linarith
  obtain ⟨k, hk⟩ := exists_const_of_card_mul_sum_sq_eq_sq_sum Z (fun z => (tz z : ℤ)) hAC
  by_cases hne : Z.Nonempty
  · obtain ⟨z0, hz0⟩ := hne
    refine ⟨tz z0, fun z hz => ?_⟩
    have h1 : (tz z : ℤ) = k := hk z hz
    have h0 : (tz z0 : ℤ) = k := hk z0 hz0
    have : (tz z : ℤ) = (tz z0 : ℤ) := h1.trans h0.symm
    exact_mod_cast this
  · refine ⟨0, fun z hz => ?_⟩
    exact absurd ⟨z, hz⟩ hne

theorem t_le_s_of_card_eq_t_add_one (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) (hcard : X.card = t + 1) :
    t ≤ s := by
  classical
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  obtain ⟨a, haX⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  have hTcard : (varianceTrace Γ x y).card = t + 1 :=
    varianceTrace_card hP c hdeg hx hxy
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [hTcard]; omega : 0 < _)
  have hcu : c u = 0 := color_eq_zero_of_mem_varianceTrace hP hx hu
  have hua : Γ.dist u a = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX haX) hu
  let L := commonNeighbor hP hua
  have huL : Γ.Adj u L := commonNeighbor_adj_left hP hua
  have haL : Γ.Adj a L := commonNeighbor_adj_right hP hua
  have hcL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hcu huL
  have hLdeg : (Γ.neighborFinset L).card = s + 1 := by
    rw [card_neighborFinset_eq_degree Γ L, degree_eq_s_add_one_of_color_one hdeg hcL]
  have hu_mem : u ∈ Γ.neighborFinset L := by
    rw [mem_neighborFinset]; exact huL.symm
  have ha_mem : a ∈ Γ.neighborFinset L := by
    rw [mem_neighborFinset]; exact haL.symm
  have hua_ne : u ≠ a := by
    intro h
    subst h
    exact not_mem_X_of_mem_varianceTrace hP hT hxy hX hu haX
  have hpos : 0 < (((Γ.neighborFinset L).erase u).erase a).card := by
    rw [Finset.card_erase_of_mem (by
      rw [Finset.mem_erase]; exact ⟨hua_ne.symm, ha_mem⟩),
      Finset.card_erase_of_mem hu_mem, hLdeg]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_erase, Finset.mem_erase, mem_neighborFinset] at hw
  obtain ⟨hwa, hwu, hLw⟩ := hw
  have hwu2 : Γ.dist w u = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hLw.symm huL.symm hwu
  have hczw : c w = 0 := by
    have hne := c.valid hLw
    have hfin : ∀ z : Fin 2, z = 0 ∨ z = 1 := by decide
    rcases hfin (c w) with h | h
    · exact h
    · exact absurd (hcL.trans h.symm) hne
  have hw_notX : w ∉ X := by
    intro hwX
    have h4 : Γ.dist w a = 4 :=
      dist_eq_four_of_mem_X hP hT hxy hX hwX haX hwa
    have h2 : Γ.dist w a = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLw.symm haL.symm hwa
    omega
  have hnotadj : ∀ a' ∈ X, a' ≠ a → ¬ Γ.Adj a' L := by
    intro a' ha'X hne h
    have h4 : Γ.dist a' a = 4 :=
      dist_eq_four_of_mem_X hP hT hxy hX ha'X haX hne
    have h2 : Γ.dist a' a = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP h haL.symm hne
    omega
  have hwa_four : ∀ a' ∈ X, a' ≠ a → Γ.dist w a' = 4 := by
    intro a' ha'X hne
    have ha'L := hnotadj a' ha'X hne
    have hw_ne : w ≠ a' := by
      intro h
      exact ha'L (by simpa [h] using hLw.symm)
    have h2_not : Γ.dist w a' ≠ 2 := by
      intro h2
      have hau' : Γ.dist a' u = 2 :=
        dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX ha'X) hu
      have hwu_eq : w = u :=
        eq_of_adj_of_dist_two_of_not_adj (hP := hP) (c := c) ha'L hLw huL.symm
          (by rw [SimpleGraph.dist_comm]; exact h2) hau'
      exact hwu hwu_eq
    have hca' : c a' = 0 := color_eq_zero_of_mem_span hP hT hx hxy (hX ha'X)
    have heven : Even (Γ.dist w a') :=
      (hP.eq_iff_even_dist c w a').1 (hczw.trans hca'.symm)
    have hle : Γ.dist w a' ≤ 4 := hP.dist_le (by norm_num) w a'
    have hgt : 2 < Γ.dist w a' :=
      two_lt_dist_of_ne_of_not_dist_two hP hczw hca' hw_ne h2_not
    obtain ⟨k, hk⟩ := heven
    omega
  have hfiber : ∀ a' ∈ X.erase a, ((varianceTrace Γ w a').erase u).card = t := by
    intro a' ha'
    rw [Finset.mem_erase] at ha'
    obtain ⟨hne, ha'X⟩ := ha'
    have hw4 : Γ.dist w a' = 4 := hwa_four a' ha'X hne
    have htrace : (varianceTrace Γ w a').card = t + 1 :=
      varianceTrace_card hP c hdeg hczw hw4
    have hu_trace : u ∈ varianceTrace Γ w a' := by
      rw [mem_varianceTrace]
      exact ⟨hwu2, dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX ha'X) hu⟩
    rw [Finset.card_erase_of_mem hu_trace, htrace]
    omega
  have hdisj : (↑(X.erase a) : Set V).PairwiseDisjoint
      (fun a' => (varianceTrace Γ w a').erase u) := by
    intro a' ha' a'' ha'' hne
    change Disjoint ((varianceTrace Γ w a').erase u) ((varianceTrace Γ w a'').erase u)
    rw [Finset.disjoint_left]
    intro z hz' hz''
    rw [Finset.mem_erase] at hz' hz''
    obtain ⟨hz'u, hz'trace⟩ := hz'
    obtain ⟨hz''u, hz''trace⟩ := hz''
    rw [mem_varianceTrace] at hz'trace hz''trace
    rw [Finset.mem_coe, Finset.mem_erase] at ha' ha''
    obtain ⟨-, ha'X⟩ := ha'
    obtain ⟨-, ha''X⟩ := ha''
    have hzT : z ∈ varianceTrace Γ x y := by
      have htrace := (span_eq_of_mem hP hT hxy (hX ha'X) (hX ha''X) hne).2.2
      have hzTrace : z ∈ traceSet Γ a' a'' := ⟨hz'trace.2, hz''trace.2⟩
      rw [htrace] at hzTrace
      simpa [mem_varianceTrace] using hzTrace
    have huz : u ≠ z := fun h => hz'u h.symm
    have huz4 : Γ.dist u z = 4 :=
      dist_eq_four_of_mem_varianceTrace hP hxy hu hzT huz
    have hTzcard : (traceSet Γ u z).ncard = t + 1 := by
      rw [ncard_trace hP huz4, degree_eq_t_add_one_of_color_zero hdeg hcu]
    have hXsub : (X : Set V) ⊆ traceSet Γ u z := by
      intro b hbX
      exact ⟨by
        rw [SimpleGraph.dist_comm]
        exact dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX hbX) hu,
        by
        rw [SimpleGraph.dist_comm]
        exact dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX hbX) hzT⟩
    have hXeq : (X : Set V) = traceSet Γ u z :=
      Set.eq_of_subset_of_ncard_le hXsub (by
        rw [hTzcard, Set.ncard_coe_finset, hcard])
    have hwT : w ∈ traceSet Γ u z := by
      refine ⟨by rw [SimpleGraph.dist_comm]; exact hwu2, ?_⟩
      rw [SimpleGraph.dist_comm]
      exact hz'trace.1
    rw [← hXeq] at hwT
    exact hw_notX hwT
  let Tgt := ((Γ.neighborFinset w).erase L).biUnion fun M => (Γ.neighborFinset M).erase w
  have hLw_mem : L ∈ Γ.neighborFinset w := by
    rw [mem_neighborFinset]; exact hLw.symm
  have hcardTgt : Tgt.card = t * s := by
    rw [show Tgt = ((Γ.neighborFinset w).erase L).biUnion
      (fun M => (Γ.neighborFinset M).erase w) from rfl, Finset.card_biUnion]
    · calc
        ∑ M ∈ (Γ.neighborFinset w).erase L, ((Γ.neighborFinset M).erase w).card
            = ∑ M ∈ (Γ.neighborFinset w).erase L, s := by
              refine Finset.sum_congr rfl fun M hM => ?_
              rw [Finset.mem_erase] at hM
              have hwM : Γ.Adj w M := by
                simpa using hM.2
              exact card_erase_neighborFinset_of_line hdeg hwM
                (color_eq_one_of_adj_of_color_eq_zero hczw hwM)
        _ = ((Γ.neighborFinset w).erase L).card • s := Finset.sum_const s
        _ = t * s := by
              rw [Finset.card_erase_of_mem hLw_mem, card_neighborFinset_eq_degree Γ w,
                degree_eq_t_add_one_of_color_zero hdeg hczw, smul_eq_mul]
              congr 1
    · intro M hM M' hM' hne
      exact disjoint_erase_neighborFinset hP (Finset.mem_erase.mp hM).2
        (Finset.mem_erase.mp hM').2 hne
  have hUsub : (X.erase a).biUnion (fun a' => (varianceTrace Γ w a').erase u) ⊆ Tgt := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨a', ha', hzF⟩ := hz
    rw [Finset.mem_erase] at hzF ha'
    obtain ⟨ha'ne, ha'X⟩ := ha'
    obtain ⟨hz'u, hz'trace⟩ := hzF
    rw [mem_varianceTrace] at hz'trace
    have hzw : Γ.dist w z = 2 := hz'trace.1
    have hzw' : Γ.dist z w = 2 := by rwa [SimpleGraph.dist_comm]
    let M := commonNeighbor hP hzw'
    have hMz : Γ.Adj z M := commonNeighbor_adj_left hP hzw'
    have hMw : Γ.Adj w M := commonNeighbor_adj_right hP hzw'
    have hML : M ≠ L := by
      intro hML
      have hzL : Γ.Adj z L := by simpa [hML] using hMz
      have ha'L := hnotadj a' ha'X ha'ne
      have hau' : Γ.dist a' u = 2 :=
        dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX ha'X) hu
      have hzu_eq : z = u :=
        eq_of_adj_of_dist_two_of_not_adj (hP := hP) (c := c) ha'L hzL.symm huL.symm
          hz'trace.2 hau'
      exact hz'u hzu_eq
    refine Finset.mem_biUnion.mpr ⟨M, ?_, ?_⟩
    · rw [Finset.mem_erase, mem_neighborFinset]
      exact ⟨hML, hMw⟩
    · rw [Finset.mem_erase, mem_neighborFinset]
      refine ⟨?_, hMz.symm⟩
      intro h
      rw [h] at hzw
      simp at hzw
  have hUcard : ((X.erase a).biUnion (fun a' => (varianceTrace Γ w a').erase u)).card = t * t := by
    rw [Finset.card_biUnion hdisj]
    calc
      ∑ a' ∈ X.erase a, ((varianceTrace Γ w a').erase u).card
          = ∑ a' ∈ X.erase a, t := Finset.sum_congr rfl hfiber
      _ = (X.erase a).card * t := by rw [Finset.sum_const, smul_eq_mul]
      _ = (X.card - 1) * t := by rw [Finset.card_erase_of_mem haX]
      _ = t * t := by rw [hcard]; simp
  have hle : t * t ≤ t * s := by
    rw [← hUcard, ← hcardTgt]
    exact Finset.card_le_card hUsub
  exact Nat.le_of_mul_le_mul_left hle (by omega)

theorem mul_le_sq_of_subset_span (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) :
    (X.card - 1) * t ≤ s ^ 2 := by
  classical
  have hmle : X.card ≤ t + 1 :=
    card_le_t_add_one_of_subset_span hP hT c hdeg hx hxy hX
  by_cases hcase : X.card ≤ t
  · let Z := varianceZ Γ c X
    let T := varianceTrace Γ x y
    let tz : V → ℕ := fun z => varianceTz Γ T z
    have hCS : (∑ z ∈ Z, (tz z : ℤ)) ^ 2 ≤
        (Z.card : ℤ) * (∑ z ∈ Z, (tz z : ℤ) ^ 2) :=
      sq_sum_le_card_mul_sum_sq
    have hid := variance_identity hP hT c hdeg hx hxy hX hm
    have hnonneg : (0 : ℤ) ≤ (t + 1 : ℤ) * ((t + 1 - X.card : ℕ) : ℤ) * (t : ℤ) *
        ((s : ℤ) - 1) * ((s : ℤ) ^ 2 - ((X.card - 1 : ℕ) : ℤ) * (t : ℤ)) := by
      rw [← hid]
      linarith
    have hfac : (0 : ℤ) < (t + 1 : ℤ) * ((t + 1 - X.card : ℕ) : ℤ) * (t : ℤ) *
        ((s : ℤ) - 1) := by
      have h1 : (0 : ℤ) < (t + 1 : ℤ) := by
        have := two_le_t hP hT c hdeg
        omega
      have h2 : (0 : ℤ) < ((t + 1 - X.card : ℕ) : ℤ) := by
        rw [Nat.cast_sub hmle]
        push_cast
        omega
      have h3 : (0 : ℤ) < (t : ℤ) := by
        have := two_le_t hP hT c hdeg
        omega
      have h4 : (0 : ℤ) < (s : ℤ) - 1 := by
        have := two_le_s hP hT c hdeg
        omega
      exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4
    have hlast : (0 : ℤ) ≤ (s : ℤ) ^ 2 - ((X.card - 1 : ℕ) : ℤ) * (t : ℤ) :=
      (mul_nonneg_iff_of_pos_left hfac).mp (by simpa [mul_assoc] using hnonneg)
    have hlast' : (((X.card - 1) * t : ℕ) : ℤ) ≤ ((s ^ 2 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast hlast'
  · have hcard : X.card = t + 1 := by omega
    have htle : t ≤ s :=
      t_le_s_of_card_eq_t_add_one hP hT c hdeg hx hxy hX hm hcard
    calc
      (X.card - 1) * t = t * t := by rw [hcard]; simp
      _ = t ^ 2 := by ring
      _ ≤ s ^ 2 := Nat.pow_le_pow_left htle 2

end Basic

end CFSG.Geometry.GeneralizedQuadrangles
