module

public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus

public section

namespace CFSG.LieType.Chevalley.ExceptionalCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

@[expose] def UnitCoord (v : Fin τ.rank → ℤ) : Prop :=
  ∃ k, cartanCoord v k = 1 ∨ cartanCoord v k = -1 ∨ cartanCoord v k = 2 ∨ cartanCoord v k = -2

instance (v : Fin τ.rank → ℤ) : Decidable (UnitCoord v) := by
  unfold UnitCoord
  infer_instance

@[expose] def MinorBound (v w : Fin τ.rank → ℤ) : Prop :=
  ∃ k k', cartanCoord v k * cartanCoord w k' - cartanCoord v k' * cartanCoord w k ≠ 0 ∧
    |cartanCoord v k * cartanCoord w k' - cartanCoord v k' * cartanCoord w k| < 7

instance (v w : Fin τ.rank → ℤ) : Decidable (MinorBound v w) := by
  unfold MinorBound
  infer_instance

variable (τ) in
@[expose] def UnitCheck (n : ℕ) : Prop :=
  0 < height (τ.rootCertificate.root n) → UnitCoord (τ.rootCertificate.root n)

instance (n : ℕ) : Decidable (UnitCheck τ n) := by
  unfold UnitCheck
  infer_instance

variable (τ) in
@[expose] def PairCheck (n n' : ℕ) : Prop :=
  0 < height (τ.rootCertificate.root n) → 0 < height (τ.rootCertificate.root n') →
    τ.rootCertificate.root n ≠ τ.rootCertificate.root n' →
      MinorBound (τ.rootCertificate.root n) (τ.rootCertificate.root n')

instance (n n' : ℕ) : Decidable (PairCheck τ n n') := by
  unfold PairCheck
  infer_instance

theorem unitCheck_G2 : ∀ n < Tag.G2.rootCertificate.roots.length, UnitCheck .G2 n := by
  decide +kernel

theorem unitCheck_F4 : ∀ n < Tag.F4.rootCertificate.roots.length, UnitCheck .F4 n := by
  decide +kernel

theorem unitCheck_E6 : ∀ n < Tag.E6.rootCertificate.roots.length, UnitCheck .E6 n := by
  decide +kernel

theorem unitCheck_E7 : ∀ n < Tag.E7.rootCertificate.roots.length, UnitCheck .E7 n := by
  decide +kernel

theorem unitCheck_E8 : ∀ n < Tag.E8.rootCertificate.roots.length, UnitCheck .E8 n := by
  decide +kernel

theorem pairCheck_G2 : ∀ n < Tag.G2.rootCertificate.roots.length,
    ∀ n' < Tag.G2.rootCertificate.roots.length, PairCheck .G2 n n' := by
  decide +kernel

theorem pairCheck_F4 : ∀ n < Tag.F4.rootCertificate.roots.length,
    ∀ n' < Tag.F4.rootCertificate.roots.length, PairCheck .F4 n n' := by
  decide +kernel

theorem pairCheck_E6 : ∀ n < Tag.E6.rootCertificate.roots.length,
    ∀ n' < Tag.E6.rootCertificate.roots.length, PairCheck .E6 n n' := by
  decide +kernel

theorem pairCheck_E7 : ∀ n < Tag.E7.rootCertificate.roots.length,
    ∀ n' < Tag.E7.rootCertificate.roots.length, PairCheck .E7 n n' := by
  decide +kernel

@[expose] def e8PosCodes : List (ℕ × ℕ) :=
  [(2290649225, 2290648970), (2290649240, 2290645160), (2290649480, 2290645639), (2290653320, 2290591608),
    (2290714760, 2289727624), (2291697800, 2275903624), (2307426440, 2054719624), (2559084680, 2810742920),
    (2290649481, 2290645385), (2290653336, 2290587544), (2290653576, 2290588023), (2290718856, 2289670008),
    (2291763336, 2274982024), (2308475016, 2039974024), (2575861896, 2574813320), (2290653577, 2290587769),
    (2290653592, 2290583959), (2290718872, 2289665944), (2290719112, 2289666423), (2291767432, 2274924408),
    (2308540552, 2039052424), (2576910472, 2560067720), (2290653593, 2290583705), (2290719113, 2289666169),
    (2290719128, 2289662359), (2291767448, 2274920344), (2291767688, 2274920823), (2308544648, 2038994808),
    (2576976008, 2559146120), (2290719129, 2289662105), (2291767689, 2274920569), (2290723224, 2289604743),
    (2291767704, 2274916759), (2308544664, 2038990744), (2308544904, 2038991223), (2576980104, 2559088504),
    (2290723225, 2289604489), (2291767705, 2274916505), (2308544905, 2038990969), (2291771800, 2274859143),
    (2308544920, 2038987159), (2576980120, 2559084440), (2576980360, 2559084919), (2290723481, 2289600904),
    (2291771801, 2274858889), (2308544921, 2038986905), (2576980361, 2559084665), (2291837336, 2273937543),
    (2308549016, 2038929543), (2576980376, 2559080855), (2291772057, 2274855304), (2291837337, 2273937289),
    (2308549017, 2038929289), (2576980377, 2559080601), (2308614552, 2038007943), (2576984472, 2559023239),
    (2291837593, 2273933704), (2308549273, 2038925704), (2308614553, 2038007689), (2576984473, 2559022985),
    (2309663128, 2023262343), (2577050008, 2558101639), (2291841689, 2273876088), (2308614809, 2038004104),
    (2576984729, 2559019400), (2309663129, 2023262089), (2577050009, 2558101385), (2578098584, 2543356039),
    (2291841705, 2273872024), (2308618905, 2037946488), (2309663385, 2023258504), (2577050265, 2558097800),
    (2578098585, 2543355785), (2594875800, 2307426439), (2308618921, 2037942424), (2309667481, 2023200888),
    (2577054361, 2558040184), (2578098841, 2543352200), (2594875801, 2307426185), (2309667497, 2023196824),
    (2577054377, 2558036120), (2309733017, 2022279288), (2578102937, 2543294584), (2594876057, 2307422600),
    (2309733033, 2022275224), (2578102953, 2543290520), (2578168473, 2542372984), (2594880153, 2307364984),
    (2309737129, 2022217608), (2578168489, 2542368920), (2594880169, 2307360920), (2594945689, 2306443384),
    (2309737385, 2022214023), (2578172585, 2542311304), (2594945705, 2306439320), (2595994265, 2291697784),
    (2309737386, 2022213769), (2578172841, 2542307719), (2594949801, 2306381704), (2595994281, 2291693720),
    (2578172842, 2542307465), (2594950057, 2306378119), (2595998377, 2291636104), (2594950058, 2306377865),
    (2595998633, 2291632519), (2596063913, 2290714504), (2595998634, 2291632265), (2596064169, 2290710919),
    (2596064170, 2290710665), (2596068265, 2290653303), (2596068266, 2290653049), (2596068281, 2290649239),
    (2596068282, 2290648985), (2596068522, 2290649464), (2596068538, 2290645400), (2596072634, 2290587784),
    (2596138170, 2289666184), (2597186746, 2274920584), (2613963962, 2038990984), (2882399418, 2559084680)]

@[expose] def e8PosTable : List (List ℤ × List ℤ) :=
  e8PosCodes.map fun c =>
    (List.ofFn (decodeVec (τ := .E8) c.1), List.ofFn (decodeVec (τ := .E8) c.2))

theorem e8PosTable_eq :
    ((List.range Tag.E8.rootCertificate.roots.length).filter
        (fun n => decide (0 < height (τ := .E8) (Tag.E8.rootCertificate.root n)))).map
      (fun n => (List.ofFn (Tag.E8.rootCertificate.root n),
        List.ofFn (cartanCoord (τ := .E8) (Tag.E8.rootCertificate.root n)))) = e8PosTable := by
  decide +kernel

@[expose] def listMinor (u v : List ℤ) (k k' : ℕ) : ℤ :=
  u.getD k 0 * v.getD k' 0 - u.getD k' 0 * v.getD k 0

private theorem forall_mem_take_drop {α : Type} {P : α → Prop} (L : List α) (k : ℕ)
    (h1 : ∀ p ∈ L.take k, P p) (h2 : ∀ p ∈ L.drop k, P p) : ∀ p ∈ L, P p := by
  intro p hp
  rw [← List.take_append_drop k L, List.mem_append] at hp
  exact hp.elim (h1 p) (h2 p)

theorem e8PosTable_minor0 : ∀ p ∈ e8PosTable.take 30,
    ∀ q ∈ e8PosTable, p.1 ≠ q.1 →
    ∃ k < Tag.E8.rank, ∃ k' < Tag.E8.rank,
      listMinor p.2 q.2 k k' ≠ 0 ∧ |listMinor p.2 q.2 k k'| < 7 := by
  decide +kernel

theorem e8PosTable_minor1 : ∀ p ∈ (e8PosTable.drop 30).take 30,
    ∀ q ∈ e8PosTable, p.1 ≠ q.1 →
    ∃ k < Tag.E8.rank, ∃ k' < Tag.E8.rank,
      listMinor p.2 q.2 k k' ≠ 0 ∧ |listMinor p.2 q.2 k k'| < 7 := by
  decide +kernel

theorem e8PosTable_minor2 : ∀ p ∈ ((e8PosTable.drop 30).drop 30).take 30,
    ∀ q ∈ e8PosTable, p.1 ≠ q.1 →
    ∃ k < Tag.E8.rank, ∃ k' < Tag.E8.rank,
      listMinor p.2 q.2 k k' ≠ 0 ∧ |listMinor p.2 q.2 k k'| < 7 := by
  decide +kernel

theorem e8PosTable_minor3 : ∀ p ∈ ((e8PosTable.drop 30).drop 30).drop 30,
    ∀ q ∈ e8PosTable, p.1 ≠ q.1 →
    ∃ k < Tag.E8.rank, ∃ k' < Tag.E8.rank,
      listMinor p.2 q.2 k k' ≠ 0 ∧ |listMinor p.2 q.2 k k'| < 7 := by
  decide +kernel

theorem e8PosTable_minor : ∀ p ∈ e8PosTable, ∀ q ∈ e8PosTable, p.1 ≠ q.1 →
    ∃ k < Tag.E8.rank, ∃ k' < Tag.E8.rank,
      listMinor p.2 q.2 k k' ≠ 0 ∧ |listMinor p.2 q.2 k k'| < 7 :=
  forall_mem_take_drop _ 30 e8PosTable_minor0 <|
    forall_mem_take_drop _ 30 e8PosTable_minor1 <|
      forall_mem_take_drop _ 30 e8PosTable_minor2 e8PosTable_minor3

theorem ofFn_getD_int {n : ℕ} (f : Fin n → ℤ) (k : ℕ) (hk : k < n) :
    (List.ofFn f).getD k 0 = f ⟨k, hk⟩ := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem mem_e8PosTable {n : ℕ} (hn : n < Tag.E8.rootCertificate.roots.length)
    (hp : 0 < height (τ := .E8) (Tag.E8.rootCertificate.root n)) :
    (List.ofFn (Tag.E8.rootCertificate.root n),
      List.ofFn (cartanCoord (τ := .E8) (Tag.E8.rootCertificate.root n))) ∈ e8PosTable := by
  rw [← e8PosTable_eq]
  exact List.mem_map_of_mem (List.mem_filter.2 ⟨List.mem_range.2 hn, decide_eq_true hp⟩)

theorem pairCheck_E8 : ∀ n < Tag.E8.rootCertificate.roots.length,
    ∀ n' < Tag.E8.rootCertificate.roots.length, PairCheck .E8 n n' := by
  intro n hn n' hn' hp hp' hne
  obtain ⟨k, hk, k', hk', h1, h2⟩ := e8PosTable_minor _ (mem_e8PosTable hn hp) _
    (mem_e8PosTable hn' hp') (fun h => hne (List.ofFn_injective h))
  refine ⟨⟨k, hk⟩, ⟨k', hk'⟩, ?_⟩
  simp only [listMinor, ofFn_getD_int _ _ hk, ofFn_getD_int _ _ hk'] at h1 h2
  exact ⟨h1, h2⟩

theorem isCoprime_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) (i : ℕ) :
    IsCoprime (2 ^ f - 1 : ℤ) (2 ^ i) := by
  refine IsCoprime.pow_right ⟨-1, 2 ^ (f - 1), ?_⟩
  have h : (2 : ℤ) ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h]
  ring

theorem le_two_pow_sub_one {f : ℕ} (hf : 3 ≤ f) : (7 : ℤ) ≤ 2 ^ f - 1 := by
  have h : (8 : ℤ) ≤ 2 ^ f := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hf
  linarith

theorem not_dvd_two_pow_add {f i j : ℕ} (hf : 3 ≤ f) (hi : i < f) (hj : j < f) :
    ¬ (2 ^ f - 1 : ℤ) ∣ 2 ^ i + 2 ^ j := by
  wlog hij : i ≤ j generalizing i j
  · rw [add_comm]
    exact this hj hi (by omega)
  intro hd
  have e : (2 : ℤ) ^ i + 2 ^ j = 2 ^ i * (1 + 2 ^ (j - i)) := by
    rw [mul_add, mul_one, ← pow_add, Nat.add_sub_cancel' hij]
  rw [e] at hd
  have hd' := (isCoprime_two_pow_sub_one (by omega) i).dvd_of_dvd_mul_left hd
  have hpos : (0 : ℤ) < 1 + 2 ^ (j - i) := by positivity
  have hle : (2 : ℤ) ^ (j - i) ≤ 2 ^ (f - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hf2 : (2 : ℤ) ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h4 : (4 : ℤ) ≤ 2 ^ (f - 1) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlt : 1 + 2 ^ (j - i) < (2 ^ f - 1 : ℤ) := by rw [hf2]; linarith
  exact absurd (Int.le_of_dvd hpos hd') (not_le.2 hlt)

theorem not_forall_dvd_of_unitCoord {f : ℕ} (hf : 3 ≤ f) {α : Fin τ.rank → ℤ}
    (hα : UnitCoord α) {i j : ℕ} (hi : i < f) (hj : j < f) :
    ¬ ∀ k, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord α k := by
  intro h
  obtain ⟨k, hk⟩ := hα
  have hd := h k
  rw [← add_mul] at hd
  have hu : IsCoprime (2 ^ f - 1 : ℤ) (cartanCoord α k) := by
    rcases hk with hk | hk | hk | hk <;> rw [hk]
    · exact isCoprime_one_right
    · exact isCoprime_one_right.neg_right
    · simpa using isCoprime_two_pow_sub_one (f := f) (by omega) 1
    · simpa using (isCoprime_two_pow_sub_one (f := f) (by omega) 1).neg_right
  exact not_dvd_two_pow_add hf hi hj (hu.dvd_of_dvd_mul_right hd)

theorem not_forall_dvd_of_minorBound {f : ℕ} (hf : 3 ≤ f) {α β : Fin τ.rank → ℤ}
    (hαβ : MinorBound α β) (i j : ℕ) :
    ¬ ∀ k, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k := by
  intro h
  obtain ⟨k, k', hne, hlt⟩ := hαβ
  set D := cartanCoord α k * cartanCoord β k' - cartanCoord α k' * cartanCoord β k with hD
  have hdvd : (2 ^ f - 1 : ℤ) ∣ 2 ^ i * D := by
    have e : (2 : ℤ) ^ i * D =
        (2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k) * cartanCoord β k' -
          (2 ^ i * cartanCoord α k' + 2 ^ j * cartanCoord β k') * cartanCoord β k := by
      rw [hD]
      ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_left (h k) _) (dvd_mul_of_dvd_left (h k') _)
  have hD' := (isCoprime_two_pow_sub_one (by omega) i).dvd_of_dvd_mul_left hdvd
  have h7 := le_two_pow_sub_one hf
  have habs := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hD')
  omega

theorem checks_of_tag (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (∀ n < τ.rootCertificate.roots.length, UnitCheck τ n) ∧
      ∀ n < τ.rootCertificate.roots.length, ∀ n' < τ.rootCertificate.roots.length,
        PairCheck τ n n' := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨unitCheck_G2, pairCheck_G2⟩
  · exact ⟨unitCheck_F4, pairCheck_F4⟩
  · exact ⟨unitCheck_E6, pairCheck_E6⟩
  · exact ⟨unitCheck_E7, pairCheck_E7⟩
  · exact ⟨unitCheck_E8, pairCheck_E8⟩

theorem unitCoord_of_tag
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hαp : 0 < height α) : UnitCoord α := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hα
  exact (checks_of_tag hτ).1 n hn hαp

theorem pair_not_dvd
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 3 ≤ f) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hαp : 0 < height α)
    (hβ : IsRoot τ β) (hβp : 0 < height β) (i j : ℕ) (hi : i < f) (hj : j < f) :
    ¬ ∀ k, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k := by
  by_cases hab : α = β
  · subst hab
    exact not_forall_dvd_of_unitCoord hf (unitCoord_of_tag hτ hα hαp) hi hj
  · obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hα
    obtain ⟨n', hn', rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hβ
    exact not_forall_dvd_of_minorBound hf ((checks_of_tag hτ).2 n hn n' hn' hαp hβp hab) i j

theorem exists_not_dvd_cartanCoord
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 2 ≤ f) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hαp : 0 < height α) :
    ∃ k, ¬ (2 ^ f - 1 : ℤ) ∣ cartanCoord α k := by
  obtain ⟨k, hk⟩ := unitCoord_of_tag hτ hα hαp
  refine ⟨k, fun hd => ?_⟩
  have h3 : (3 : ℤ) ≤ 2 ^ f - 1 := by
    have : (4 : ℤ) ≤ 2 ^ f := by
      calc (4 : ℤ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hf
    linarith
  rcases hk with hk | hk | hk | hk <;> rw [hk] at hd
  · exact absurd (Int.le_of_dvd one_pos hd) (by omega)
  · exact absurd (Int.le_of_dvd one_pos (dvd_neg.1 hd)) (by omega)
  · exact absurd (Int.le_of_dvd two_pos hd) (by omega)
  · exact absurd (Int.le_of_dvd two_pos (dvd_neg.1 hd)) (by omega)

end CFSG.LieType.Chevalley.ExceptionalCover
