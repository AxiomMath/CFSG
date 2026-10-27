module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Blueprint.ChevalleyPinned

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def highRoot : (τ : Tag) → Fin τ.rank → ℤ
  | .G2 => (![2, 3] : Fin 2 → ℤ)
  | .F4 => (![2, 3, 4, 2] : Fin 4 → ℤ)
  | .D4 => (![1, 1, 2, 1] : Fin 4 → ℤ)
  | .E6 => (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)
  | .E7 => (![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ)
  | .E8 => (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ)

@[expose] def highRootPos : Tag → ℕ × ℕ
  | .G2 => (7, 10)
  | .F4 => (43, 46)
  | .D4 => (22, 23)
  | .E6 => (70, 71)
  | .E7 => (124, 125)
  | .E8 => (238, 239)

@[expose] def highRootPairWords : Tag → List ℕ
  | .G2 =>
    [0, 0, 1, 0, 0, 33, 34, 0, 0, 514, 0, 8227]
  | .F4 =>
    [0, 0, 0, 0, 1, 0, 33, 0, 0, 65, 0, 97, 514, 0, 578, 0, 0, 0, 1058, 1602, 9219, 0, 0, 9315, 0,
      0, 16899, 25635, 147492, 148996, 0, 0, 410116, 410180, 2383909, 0, 0, 6562821, 38142534, 0,
      0, 105005094, 610280487, 0, 0, 1680081479, 0, 26881303656]
  | .D4 =>
    [0, 0, 0, 0, 1, 0, 33, 0, 65, 0, 97, 1026, 0, 0, 1058, 0, 1602, 16899, 25603, 0, 25635, 410116,
      0, 0]
  | .E6 =>
    [0, 0, 0, 0, 0, 0, 1, 0, 33, 0, 65, 0, 97, 0, 129, 0, 161, 1026, 0, 1570, 0, 0, 1602, 0, 2146,
      0, 2690, 25603, 0, 0, 25635, 34339, 0, 0, 34371, 0, 43107, 410116, 549892, 0, 0, 549924,
      689700, 0, 0, 689732, 8798725, 11035653, 0, 0, 8798821, 11035685, 0, 140781062, 176570886, 0,
      0, 176570982, 0, 2252496967, 2825135623, 0, 0, 2825135751, 45202169928, 45202171912, 0,
      723234750537, 0, 11571756008554, 0, 0]
  | .E7 =>
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 33, 0, 65, 0, 97, 0, 129, 0, 161, 0, 193, 1026, 0, 1570, 0, 0,
      1602, 0, 2146, 0, 2690, 0, 3234, 25603, 0, 0, 25635, 34339, 0, 0, 34371, 0, 43107, 0, 51843,
      410116, 549892, 0, 0, 549924, 689700, 0, 0, 0, 689732, 0, 829540, 8798725, 11035653, 0, 0, 0,
      8798821, 11035685, 13272613, 0, 0, 13272645, 140781062, 176570886, 212362246, 0, 0, 0,
      176570982, 212362278, 0, 0, 2252496967, 2825135623, 3397796359, 0, 0, 0, 2825135751,
      3397796455, 0, 45202169928, 45202171912, 54364743176, 0, 0, 0, 54364743304, 0, 723234750537,
      869835890761, 869835892745, 0, 0, 0, 869835892905, 11571756008554, 13917374283850,
      13917374286346, 0, 0, 0, 185148096136747, 222677988541547, 222677988581451, 0, 0,
      3562847816664620, 3562847817303148, 0, 0, 57005565076850221, 57005565076850317, 0,
      912089041229604910, 0, 14593424659673678447, 0, 233494794554778854992, 0, 0]
  | .E8 =>
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 33, 0, 65, 0, 97, 0, 129, 0, 161, 0, 193, 0, 225, 1026, 0, 1570,
      0, 0, 1602, 0, 2146, 0, 2690, 0, 3234, 0, 3778, 25603, 0, 0, 25635, 34339, 0, 0, 34371, 0,
      43107, 0, 51843, 0, 60579, 410116, 549892, 0, 0, 549924, 689700, 0, 0, 0, 689732, 0, 829540,
      0, 969348, 8798725, 11035653, 0, 0, 0, 8798821, 11035685, 13272613, 0, 0, 0, 13272645, 0,
      15509605, 140781062, 176570886, 212362246, 0, 0, 0, 0, 176570982, 212362278, 248153638, 0, 0,
      0, 248153670, 2252496967, 2825135623, 3397796359, 3970458631, 0, 0, 0, 0, 2825135751,
      3397796455, 3970458663, 0, 0, 45202169928, 45202171912, 54364743176, 63527338504, 0, 0, 0, 0,
      54364743304, 63527338600, 0, 0, 723234750537, 869835890761, 869835892745, 1016437417481, 0,
      0, 0, 0, 0, 869835892905, 1016437417609, 0, 11571756008554, 13917374283850, 16262998679626,
      13917374286346, 16262998681610, 0, 0, 0, 0, 0, 16262998681770, 0, 185148096136747,
      222677988541547, 222677988581451, 260207978905675, 260207978908171, 0, 0, 0, 0, 0,
      260207978908363, 3562847816664620, 3562847817303148, 4163327662490732, 4163327662530636,
      4163327662533644, 0, 0, 0, 0, 0, 57005565076850221, 66613242599851565, 57005565076850317,
      66613242600490093, 66613242600538189, 0, 0, 0, 0, 912089041229604910, 1065811881607841326,
      1065811881607841422, 1065811881608610926, 0, 0, 0, 0, 14593424659673678447,
      17052990105725462575, 17052990105737774639, 17052990105737774735, 0, 0, 0, 0,
      233494794554778854992, 272847841691607401072, 272847841691804395568, 272847841691804395696,
      0, 0, 0, 0, 3735916712876461679633, 4365565467065718416977, 4365565467068870328945,
      4365565467068870330929, 0, 0, 0, 69849047473051494671378, 69849047473101925262930,
      69849047473101925294706, 0, 0, 0, 1117584759569630804206611, 1117584759569630804715091,
      1117584759569630804715155, 0, 0, 17881356153114092875441172, 17881356153114092875442260, 0,
      0, 286101698449825486007075861, 286101698449825486007075957, 0, 0,
      4577627175197207776113214998, 4577627175197207776113215030, 0, 0,
      73242034803155324417811440151, 73242034803155324417811439703, 0,
      1171872556850485190684983034936, 0, 18749960909607763050959728558713, 0,
      299999374553724208815355656939162, 0, 4799989992859587341045690511026363, 0,
      76799839885753397456731048176421596, 0, 0]

variable {τ : Tag}

@[expose] def wordPos (C : RootCertificate τ) (ω : List ℕ) (k : ℕ) : ℕ :=
  ω.foldl (fun k i => C.image k (τ.idx i)) k

@[expose] def highRootCheck (C : RootCertificate τ) (r : Fin τ.rank → ℤ) (kr kn : ℕ)
    (words : List ℕ) : Bool :=
  decide (kr < C.roots.length) && decide (kn < C.roots.length) &&
    (List.ofFn (C.root kr) == List.ofFn r) && (List.ofFn (C.root kn) == List.ofFn (-r)) &&
    ((List.range C.roots.length).all fun k => decide (height (C.root k) ≤ height r)) &&
    (List.range C.roots.length).all fun k => decide (k = kn) ||
      (decide (0 < height (C.root (wordPos C (decodeWord (words.getD k 0)) kr))) &&
        decide (0 < height (C.root (wordPos C (decodeWord (words.getD k 0)) k))))

theorem highRootCheck_eq_true : ∀ τ : Tag,
    highRootCheck τ.rootCertificate (highRoot τ) (highRootPos τ).1 (highRootPos τ).2
      (highRootPairWords τ) = true
  | .G2 => by decide +kernel
  | .F4 => by decide +kernel
  | .D4 => by decide +kernel
  | .E6 => by decide +kernel
  | .E7 => by decide +kernel
  | .E8 => by decide +kernel

noncomputable def weylOfWord (τ : Tag) : List ℕ → WeylGroup τ
  | [] => 1
  | i :: ω => weylOfWord τ ω * simple τ (τ.idx i)

theorem image_spec_of_check {C : RootCertificate τ} (hC : C.check = true) {k : ℕ}
    (hk : k < C.roots.length) (i : Fin τ.rank) :
    C.image k i < C.roots.length ∧ C.root (C.image k i) = reflect τ i (C.root k) := by
  simp only [RootCertificate.check, Bool.and_eq_true] at hC
  obtain ⟨-, ht⟩ := hC
  simp only [RootCertificate.checkTable, List.all_eq_true, List.mem_range, List.mem_finRange,
    true_implies, Bool.and_eq_true, decide_eq_true_eq] at ht
  exact ⟨(ht k hk i).1, RootCertificate.eq_of_ofFn_beq (ht k hk i).2⟩

theorem wordPos_spec {C : RootCertificate τ} (hC : C.check = true) (ω : List ℕ) {k : ℕ}
    (hk : k < C.roots.length) :
    wordPos C ω k < C.roots.length ∧ C.root (wordPos C ω k) = weylOfWord τ ω • C.root k := by
  induction ω generalizing k with
  | nil => exact ⟨hk, by rw [weylOfWord, one_smul]; rfl⟩
  | cons i ω ih =>
    obtain ⟨h1, h2⟩ := image_spec_of_check hC hk (τ.idx i)
    obtain ⟨h3, h4⟩ := ih h1
    refine ⟨h3, ?_⟩
    change C.root (wordPos C ω (C.image k (τ.idx i))) = _
    rw [h4, h2, weylOfWord, mul_smul, simple_smul]

theorem highRootCheck_sound {C : RootCertificate τ} (hC : C.check = true)
    {r : Fin τ.rank → ℤ} {kr kn : ℕ} {words : List ℕ}
    (h : highRootCheck C r kr kn words = true) :
    IsRoot τ r ∧ (∀ α, IsRoot τ α → height α ≤ height r) ∧
      ∀ s, IsRoot τ s → s ≠ -r → ∃ v : WeylGroup τ, 0 < height (v • r) ∧ 0 < height (v • s) := by
  simp only [highRootCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hkr, -⟩, hr⟩, hn⟩, hht⟩, hw⟩ := h
  have hr' : C.root kr = r := RootCertificate.eq_of_ofFn_beq hr
  have hn' : C.root kn = -r := RootCertificate.eq_of_ofFn_beq hn
  refine ⟨hr' ▸ RootCertificate.isRoot_root hC kr hkr, fun α hα => ?_, fun s hs hne => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq hC hα
    exact hht k hk
  · obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq hC hs
    rcases hw k hk with hkn | ⟨h1, h2⟩
    · exact absurd (hkn ▸ hn') hne
    · refine ⟨weylOfWord τ (decodeWord (words.getD k 0)), ?_, ?_⟩
      · rw [← hr', ← (wordPos_spec hC _ hkr).2]
        exact h1
      · rw [← (wordPos_spec hC _ hk).2]
        exact h2

theorem isRoot_highRoot (τ : Tag) : IsRoot τ (highRoot τ) :=
  (highRootCheck_sound τ.rootCertificate_check (highRootCheck_eq_true τ)).1

theorem height_le_height_highRoot {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    height α ≤ height (highRoot τ) :=
  (highRootCheck_sound τ.rootCertificate_check (highRootCheck_eq_true τ)).2.1 α hα

theorem height_highRoot_pos (τ : Tag) : 0 < height (highRoot τ) := by
  cases τ <;> decide

theorem not_isRoot_nsmul_add_nsmul_highRoot {β : Fin τ.rank → ℤ} (hβp : 0 < height β)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : ¬IsRoot τ (a • β + b • highRoot τ) := by
  intro h
  have h1 := height_le_height_highRoot h
  have he : height (a • β + b • highRoot τ) = a * height β + b * height (highRoot τ) := by
    simp [height, Finset.sum_add_distrib, Finset.mul_sum]
  rw [he] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hr := height_highRoot_pos τ
  nlinarith

theorem exists_height_smul_highRoot_pos {s : Fin τ.rank → ℤ} (hs : IsRoot τ s)
    (hne : s ≠ -highRoot τ) :
    ∃ v : WeylGroup τ, 0 < height (v • highRoot τ) ∧ 0 < height (v • s) :=
  (highRootCheck_sound τ.rootCertificate_check (highRootCheck_eq_true τ)).2.2 s hs hne

end CFSG.SeitzReduction
