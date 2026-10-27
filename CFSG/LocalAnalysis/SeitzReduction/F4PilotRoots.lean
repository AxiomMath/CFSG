module

public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance f4PilotRootsNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def rootR : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

@[expose] def rootS : Fin (Tag.rank .F4) → ℤ := ![1, 2, 3, 2]

@[expose] def C3Roots : List (Fin (Tag.rank .F4) → ℤ) :=
  [![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 1, 1, 0], ![0, 0, 1, 1], ![0, 1, 2, 0],
    ![0, 1, 1, 1], ![0, 1, 2, 1], ![0, 1, 2, 2], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1],
    ![0, -1, -1, 0], ![0, 0, -1, -1], ![0, -1, -2, 0], ![0, -1, -1, -1], ![0, -1, -2, -1],
    ![0, -1, -2, -2]]

@[expose] def B3Roots : List (Fin (Tag.rank .F4) → ℤ) :=
  [![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![1, 1, 0, 0], ![0, 1, 1, 0], ![1, 1, 1, 0],
    ![0, 1, 2, 0], ![1, 1, 2, 0], ![1, 2, 2, 0], ![-1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0],
    ![-1, -1, 0, 0], ![0, -1, -1, 0], ![-1, -1, -1, 0], ![0, -1, -2, 0], ![-1, -1, -2, 0],
    ![-1, -2, -2, 0]]

@[expose] def C3Set : Set (Fin (Tag.rank .F4) → ℤ) := {γ | γ ∈ C3Roots}

@[expose] def B3Set : Set (Fin (Tag.rank .F4) → ℤ) := {γ | γ ∈ B3Roots}

@[expose] def rsSpanRoots : List (Fin (Tag.rank .F4) → ℤ) :=
  [rootR, rootS, rootR - rootS, (2 : ℤ) • rootS - rootR, -rootR, -rootS, rootS - rootR,
    rootR - (2 : ℤ) • rootS]

@[expose] def rsPerpRoots : List (Fin (Tag.rank .F4) → ℤ) :=
  [![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![0, -1, 0, 0], ![0, -1, -2, 0],
    ![0, 0, -1, 0], ![0, -1, -1, 0]]

@[expose] def root1221 : Fin (Tag.rank .F4) → ℤ := ![1, 2, 2, 1]

@[expose] def root1242 : Fin (Tag.rank .F4) → ℤ := ![1, 2, 4, 2]

@[expose] def endPerpRoots : List (Fin (Tag.rank .F4) → ℤ) :=
  [root1221, root1242, -root1221, -root1242]

theorem rootR_mem_rootFinset : rootR ∈ rootFinset .F4 := by decide +kernel

theorem rootS_mem_rootFinset : rootS ∈ rootFinset .F4 := by decide +kernel

theorem iform_rootR_rootS_values :
    iform rootR rootR = 4 ∧ iform rootS rootS = 2 ∧ iform rootR rootS = 2 := by decide +kernel

theorem rootR_sub_rootS : rootR - rootS = ![1, 1, 1, 0] ∧ (2 : ℤ) • rootS - rootR = ![0, 1, 2, 2] :=
  ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

theorem iform_rootR_single : ∀ j : Fin (Tag.rank .F4),
    iform rootR (Pi.single j 1) = if j = 0 then 2 else 0 := by decide +kernel

theorem iform_rootS_single : ∀ j : Fin (Tag.rank .F4),
    iform rootS (Pi.single j 1) = if j = 3 then 1 else 0 := by decide +kernel

theorem C3Roots_check : (∀ γ ∈ C3Roots, γ ∈ rootFinset .F4 ∧ γ 0 = 0) ∧
    ∀ γ ∈ rootFinset .F4, γ 0 = 0 → γ ∈ C3Roots := by
  decide +kernel

theorem B3Roots_check : (∀ γ ∈ B3Roots, γ ∈ rootFinset .F4 ∧ γ 3 = 0) ∧
    ∀ γ ∈ rootFinset .F4, γ 3 = 0 → γ ∈ B3Roots := by
  decide +kernel

theorem rsSpanRoots_check : (∀ γ ∈ rsSpanRoots, γ ∈ rootFinset .F4 ∧
      iform (Pi.single 1 1) γ = 0 ∧ iform (Pi.single 2 1) γ = 0) ∧
    ∀ γ ∈ rootFinset .F4, iform (Pi.single 1 1) γ = 0 → iform (Pi.single 2 1) γ = 0 →
      γ ∈ rsSpanRoots := by
  decide +kernel

theorem rsPerpRoots_check : (∀ γ ∈ rsPerpRoots, γ ∈ rootFinset .F4 ∧ γ 0 = 0 ∧ γ 3 = 0) ∧
    ∀ γ ∈ rootFinset .F4, γ 0 = 0 → γ 3 = 0 → γ ∈ rsPerpRoots := by
  decide +kernel

theorem endPerpRoots_check : (∀ γ ∈ endPerpRoots, γ ∈ rootFinset .F4 ∧
      iform (Pi.single 0 1) γ = 0 ∧ iform (Pi.single 3 1) γ = 0) ∧
    ∀ γ ∈ rootFinset .F4, iform (Pi.single 0 1) γ = 0 → iform (Pi.single 3 1) γ = 0 →
      γ ∈ endPerpRoots := by
  decide +kernel

theorem C3Roots_B3Roots_card :
    C3Roots.Nodup ∧ C3Roots.length = 18 ∧
      (C3Roots.filter fun γ => iform γ γ = 4).length = 6 ∧
      (C3Roots.filter fun γ => iform γ γ = 2).length = 12 ∧
    B3Roots.Nodup ∧ B3Roots.length = 18 ∧
      (B3Roots.filter fun γ => iform γ γ = 4).length = 12 ∧
      (B3Roots.filter fun γ => iform γ γ = 2).length = 6 := by
  decide +kernel

theorem coeff_check : ∀ γ ∈ rootFinset .F4,
    |γ 0| ≤ 2 ∧ (γ 0 = 2 → γ = rootR) ∧ (iform γ γ = 2 → |γ 0| ≤ 1) ∧ |γ 3| ≤ 2 ∧
      (|γ 3| = 2 ↔ γ = rootS ∨ γ = -rootS ∨ (iform γ γ = 4 ∧ γ 3 ≠ 0)) ∧
      (iform γ γ = 2 ∨ iform γ γ = 4) := by
  decide +kernel

theorem commonPerp_check : ∀ a ∈ rootFinset .F4, ∀ b ∈ rootFinset .F4, a ≠ b → a ≠ -b →
    ∃ c ∈ rootFinset .F4, iform c a = 0 ∧ iform c b = 0 := by
  decide +kernel

theorem iform_eq_sum_mul_iform_single {τ : Tag} (θ v : Fin τ.rank → ℤ) :
    iform θ v = ∑ j, v j * iform θ (Pi.single j 1) := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem iform_rootR (v : Fin (Tag.rank .F4) → ℤ) : iform rootR v = 2 * v 0 := by
  rw [iform_eq_sum_mul_iform_single]
  simp only [iform_rootR_single, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

theorem iform_rootS (v : Fin (Tag.rank .F4) → ℤ) : iform rootS v = v 3 := by
  rw [iform_eq_sum_mul_iform_single]
  simp only [iform_rootS_single, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem corootPair_rootR (v : Fin (Tag.rank .F4) → ℤ) : corootPair rootR v = v 0 := by
  rw [corootPair, iform_rootR, iform_rootR_rootS_values.1]
  omega

theorem corootPair_rootS (v : Fin (Tag.rank .F4) → ℤ) : corootPair rootS v = v 3 := by
  rw [corootPair, iform_rootS, iform_rootR_rootS_values.2.1]
  omega

section Membership

variable {γ : Fin (Tag.rank .F4) → ℤ}

theorem isRoot_rootR : IsRoot .F4 rootR := mem_rootFinset.1 rootR_mem_rootFinset

theorem isRoot_rootS : IsRoot .F4 rootS := mem_rootFinset.1 rootS_mem_rootFinset

theorem mem_C3Roots_iff : γ ∈ C3Roots ↔ IsRoot .F4 γ ∧ γ 0 = 0 :=
  ⟨fun h => ⟨mem_rootFinset.1 (C3Roots_check.1 γ h).1, (C3Roots_check.1 γ h).2⟩,
    fun h => C3Roots_check.2 γ (mem_rootFinset.2 h.1) h.2⟩

theorem mem_C3Roots_iff_iform : γ ∈ C3Roots ↔ IsRoot .F4 γ ∧ iform rootR γ = 0 := by
  rw [mem_C3Roots_iff, iform_rootR]
  exact and_congr_right fun _ => by omega

theorem mem_B3Roots_iff : γ ∈ B3Roots ↔ IsRoot .F4 γ ∧ γ 3 = 0 :=
  ⟨fun h => ⟨mem_rootFinset.1 (B3Roots_check.1 γ h).1, (B3Roots_check.1 γ h).2⟩,
    fun h => B3Roots_check.2 γ (mem_rootFinset.2 h.1) h.2⟩

theorem mem_B3Roots_iff_iform : γ ∈ B3Roots ↔ IsRoot .F4 γ ∧ iform rootS γ = 0 := by
  rw [mem_B3Roots_iff, iform_rootS]

theorem mem_C3Set_iff : γ ∈ C3Set ↔ IsRoot .F4 γ ∧ γ 0 = 0 := mem_C3Roots_iff

theorem mem_B3Set_iff : γ ∈ B3Set ↔ IsRoot .F4 γ ∧ γ 3 = 0 := mem_B3Roots_iff

theorem mem_rsSpanRoots_iff : γ ∈ rsSpanRoots ↔
    IsRoot .F4 γ ∧ iform (Pi.single 1 1) γ = 0 ∧ iform (Pi.single 2 1) γ = 0 :=
  ⟨fun h => ⟨mem_rootFinset.1 (rsSpanRoots_check.1 γ h).1, (rsSpanRoots_check.1 γ h).2⟩,
    fun h => rsSpanRoots_check.2 γ (mem_rootFinset.2 h.1) h.2.1 h.2.2⟩

theorem mem_rsPerpRoots_iff : γ ∈ rsPerpRoots ↔ IsRoot .F4 γ ∧ γ 0 = 0 ∧ γ 3 = 0 :=
  ⟨fun h => ⟨mem_rootFinset.1 (rsPerpRoots_check.1 γ h).1, (rsPerpRoots_check.1 γ h).2⟩,
    fun h => rsPerpRoots_check.2 γ (mem_rootFinset.2 h.1) h.2.1 h.2.2⟩

theorem mem_rsPerpRoots_iff_iform : γ ∈ rsPerpRoots ↔
    IsRoot .F4 γ ∧ iform rootR γ = 0 ∧ iform rootS γ = 0 := by
  rw [mem_rsPerpRoots_iff, iform_rootR, iform_rootS]
  exact and_congr_right fun _ => and_congr_left fun _ => by omega

theorem mem_endPerpRoots_iff : γ ∈ endPerpRoots ↔
    IsRoot .F4 γ ∧ iform (Pi.single 0 1) γ = 0 ∧ iform (Pi.single 3 1) γ = 0 :=
  ⟨fun h => ⟨mem_rootFinset.1 (endPerpRoots_check.1 γ h).1, (endPerpRoots_check.1 γ h).2⟩,
    fun h => endPerpRoots_check.2 γ (mem_rootFinset.2 h.1) h.2.1 h.2.2⟩

theorem mem_C3Roots_and_mem_B3Roots_iff : γ ∈ C3Roots ∧ γ ∈ B3Roots ↔ γ ∈ rsPerpRoots := by
  rw [mem_C3Roots_iff, mem_B3Roots_iff, mem_rsPerpRoots_iff]
  tauto

theorem iform_self_eq_two_or_four (hγ : IsRoot .F4 γ) : iform γ γ = 2 ∨ iform γ γ = 4 :=
  (coeff_check γ (mem_rootFinset.2 hγ)).2.2.2.2.2

theorem abs_coeff_zero_le_two (hγ : IsRoot .F4 γ) : |γ 0| ≤ 2 :=
  (coeff_check γ (mem_rootFinset.2 hγ)).1

theorem eq_rootR_of_coeff_zero_eq_two (hγ : IsRoot .F4 γ) (h : γ 0 = 2) : γ = rootR :=
  (coeff_check γ (mem_rootFinset.2 hγ)).2.1 h

theorem eq_rootR_or_eq_neg_of_abs_coeff_zero (hγ : IsRoot .F4 γ) (h : |γ 0| = 2) :
    γ = rootR ∨ γ = -rootR := by
  rcases abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.1 h with h | h
  · exact Or.inl (eq_rootR_of_coeff_zero_eq_two hγ h)
  · right
    have h' : (-γ) 0 = 2 := by rw [Pi.neg_apply, h]; norm_num
    rw [← eq_rootR_of_coeff_zero_eq_two (IsRoot.neg hγ) h', neg_neg]

theorem abs_coeff_zero_le_one_of_short (hγ : IsRoot .F4 γ) (hs : iform γ γ = 2) : |γ 0| ≤ 1 :=
  (coeff_check γ (mem_rootFinset.2 hγ)).2.2.1 hs

theorem abs_coeff_three_le_two (hγ : IsRoot .F4 γ) : |γ 3| ≤ 2 :=
  (coeff_check γ (mem_rootFinset.2 hγ)).2.2.2.1

theorem abs_coeff_three_eq_two_iff (hγ : IsRoot .F4 γ) :
    |γ 3| = 2 ↔ γ = rootS ∨ γ = -rootS ∨ (iform γ γ = 4 ∧ γ 3 ≠ 0) :=
  (coeff_check γ (mem_rootFinset.2 hγ)).2.2.2.2.1

theorem exists_isRoot_perp_of_ne {a b : Fin (Tag.rank .F4) → ℤ} (ha : IsRoot .F4 a)
    (hb : IsRoot .F4 b) (hab : a ≠ b) (hab' : a ≠ -b) :
    ∃ c, IsRoot .F4 c ∧ iform c a = 0 ∧ iform c b = 0 := by
  obtain ⟨c, hc, h⟩ := commonPerp_check a (mem_rootFinset.2 ha) b (mem_rootFinset.2 hb) hab hab'
  exact ⟨c, mem_rootFinset.1 hc, h⟩

end Membership

theorem posPerp_01 : ∀ γ ∈ rootFinset .F4, 0 < height γ →
    (iform (Pi.single 0 1) γ = 0 ∧ iform (Pi.single 1 1) γ = 0 ↔
      γ ∈ ([![0, 0, 0, 1], ![1, 2, 3, 1], ![1, 2, 3, 2]] : List (Fin (Tag.rank .F4) → ℤ))) := by
  decide +kernel

theorem posPerp_02 : ∀ γ ∈ rootFinset .F4, 0 < height γ →
    (iform (Pi.single 0 1) γ = 0 ∧ iform (Pi.single 2 1) γ = 0 ↔
      γ ∈ ([![1, 2, 2, 0], ![1, 2, 3, 2]] : List (Fin (Tag.rank .F4) → ℤ))) := by
  decide +kernel

theorem posPerp_03 : ∀ γ ∈ rootFinset .F4, 0 < height γ →
    (iform (Pi.single 0 1) γ = 0 ∧ iform (Pi.single 3 1) γ = 0 ↔
      γ ∈ ([![1, 2, 4, 2], ![1, 2, 2, 1]] : List (Fin (Tag.rank .F4) → ℤ))) := by
  decide +kernel

theorem posPerp_12 : ∀ γ ∈ rootFinset .F4, 0 < height γ →
    (iform (Pi.single 1 1) γ = 0 ∧ iform (Pi.single 2 1) γ = 0 ↔
      γ ∈ ([![0, 1, 2, 2], ![2, 3, 4, 2], ![1, 1, 1, 0], ![1, 2, 3, 2]] :
        List (Fin (Tag.rank .F4) → ℤ))) := by
  decide +kernel

theorem posPerp_13 : ∀ γ ∈ rootFinset .F4, 0 < height γ →
    (iform (Pi.single 1 1) γ = 0 ∧ iform (Pi.single 3 1) γ = 0 ↔
      γ ∈ ([![2, 3, 4, 2], ![0, 1, 2, 1]] : List (Fin (Tag.rank .F4) → ℤ))) := by
  decide +kernel

theorem posPerp_23 : ∀ γ ∈ rootFinset .F4, 0 < height γ →
    (iform (Pi.single 2 1) γ = 0 ∧ iform (Pi.single 3 1) γ = 0 ↔
      γ ∈ ([![1, 0, 0, 0], ![1, 3, 4, 2], ![2, 3, 4, 2]] : List (Fin (Tag.rank .F4) → ℤ))) := by
  decide +kernel

@[expose] def rootWords : List ℕ :=
  [38151207, 38151175, 1680105511, 1680081479, 610419208, 2384454, 610418728, 2384390, 105006598,
    26881688136, 105005094, 26881303656, 9766699529, 149029, 9766699593, 147973, 6562917, 6562821,
    430107010089, 430100858441, 156267193354, 9316, 9252, 156267193450, 410180, 410116,
    6881712161290, 6881613734954, 2500275093547, 2500275095051, 579, 25635, 110105819759115,
    110105819759179, 40004401520684, 34, 1602, 1761693116146700, 640070424330829, 1, 97,
    28187089858347053, 10241126789293102, 0, 0, 450993437733552718, 163858028628689423,
    7215895003736843375]

@[expose] def rootWordsCheck : Bool :=
  (List.range 48).all fun k =>
    wordPos Tag.F4.rootCertificate (decodeWord (rootWords.getD k 0)) k ==
      if iform (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k) = 4 then 43 else 44

theorem rootWordsCheck_eq_true : rootWordsCheck = true := by decide +kernel

@[expose] def stabWords : List ℕ :=
  [0, 0, 17955, 16963, 0, 0, 0, 0, 1122, 287300, 1058, 271460, 0, 0, 0, 0, 6562917, 65, 4596773,
    4343365, 0, 0, 0, 0, 410180, 0, 0, 69493798, 0, 0, 0, 25635, 0, 1111900743, 0, 0, 1602, 0, 0,
    0, 97, 0, 0, 0, 0, 0, 0, 0]

@[expose] def stabWordsCheck : Bool :=
  (List.range 48).all fun k =>
    (decide (iform (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k) = 4) ||
      decide (Tag.F4.rootCertificate.root k 0 ≠ 0 ∧ Tag.F4.rootCertificate.root k 0 ≠ 1)) ||
    (wordPos Tag.F4.rootCertificate (decodeWord (stabWords.getD k 0)) 43 == 43 &&
      wordPos Tag.F4.rootCertificate (decodeWord (stabWords.getD k 0)) k ==
        if Tag.F4.rootCertificate.root k 0 = 0 then 25 else 44)

theorem stabWordsCheck_eq_true : stabWordsCheck = true := by decide +kernel

theorem certificate_positions :
    Tag.F4.rootCertificate.roots.length = 48 ∧ Tag.F4.rootCertificate.root 43 = rootR ∧
      Tag.F4.rootCertificate.root 44 = rootS ∧ Tag.F4.rootCertificate.root 25 = ![0, 1, 2, 1] ∧
      Tag.F4.rootCertificate.root 1 = ![0, 1, 0, 0] ∧
      Tag.F4.rootCertificate.root 0 = ![1, 0, 0, 0] ∧
      Tag.F4.rootCertificate.root 35 = root1242 ∧
      Tag.F4.rootCertificate.root 36 = root1221 ∧
      Tag.F4.rootCertificate.root 15 = ![0, 1, 2, 2] ∧
      Tag.F4.rootCertificate.root 8 = ![0, 1, 1, 0] :=
  ⟨by decide +kernel, List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

theorem explicitWords_check :
    wordPos Tag.F4.rootCertificate [0, 1] 43 = 35 ∧
    wordPos Tag.F4.rootCertificate [0, 2, 1, 3, 2, 1, 0] 43 = 15 ∧
    wordPos Tag.F4.rootCertificate [0, 2, 1, 3, 2, 1, 0] 44 = 25 ∧
    wordPos Tag.F4.rootCertificate [1, 2, 1, 3, 2, 1, 0] 44 = 25 ∧
    wordPos Tag.F4.rootCertificate [1, 2, 1, 3, 2, 1, 0] 36 = 8 ∧
    wordPos Tag.F4.rootCertificate [1, 2, 1, 3, 2, 1, 0] 35 = 15 := by
  decide +kernel

section Weyl


theorem weylOfWord_smul_root_of_wordPos {ω : List ℕ} {k k' : ℕ} (hk : k < 48)
    (h : wordPos Tag.F4.rootCertificate ω k = k') :
    weylOfWord .F4 ω • Tag.F4.rootCertificate.root k = Tag.F4.rootCertificate.root k' := by
  rw [← h, ← (wordPos_spec (Tag.rootCertificate_check .F4) ω
    (by rw [certificate_positions.1]; exact hk)).2]

theorem exists_smul_eq_rootR {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hl : iform γ γ = 4) : ∃ w : WeylGroup .F4, w • γ = rootR := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hγ
  rw [certificate_positions.1] at hk
  have h := rootWordsCheck_eq_true
  simp only [rootWordsCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hk' := h k hk
  rw [ite_eq_left hl] at hk'
  exact ⟨_, (weylOfWord_smul_root_of_wordPos hk hk').trans certificate_positions.2.1⟩

theorem exists_smul_eq_rootS {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hs : iform γ γ = 2) : ∃ w : WeylGroup .F4, w • γ = rootS := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hγ
  rw [certificate_positions.1] at hk
  have h := rootWordsCheck_eq_true
  simp only [rootWordsCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hk' := h k hk
  rw [ite_eq_right (by omega)] at hk'
  exact ⟨_, (weylOfWord_smul_root_of_wordPos hk hk').trans certificate_positions.2.2.1⟩


theorem exists_smul_mem_C3Roots_of_perp {c : Fin (Tag.rank .F4) → ℤ} (hc : IsRoot .F4 c)
    (hl : iform c c = 4) : ∃ w : WeylGroup .F4, w • c = rootR ∧
      ∀ γ, IsRoot .F4 γ → iform c γ = 0 → w • γ ∈ C3Roots := by
  obtain ⟨w, hw⟩ := exists_smul_eq_rootR hc hl
  refine ⟨w, hw, fun γ hγ h0 => mem_C3Roots_iff_iform.2 ⟨IsRoot.smul hγ w, ?_⟩⟩
  rw [← hw, iform_smul, h0]

theorem exists_smul_mem_B3Roots_of_perp {c : Fin (Tag.rank .F4) → ℤ} (hc : IsRoot .F4 c)
    (hs : iform c c = 2) : ∃ w : WeylGroup .F4, w • c = rootS ∧
      ∀ γ, IsRoot .F4 γ → iform c γ = 0 → w • γ ∈ B3Roots := by
  obtain ⟨w, hw⟩ := exists_smul_eq_rootS hc hs
  refine ⟨w, hw, fun γ hγ h0 => mem_B3Roots_iff_iform.2 ⟨IsRoot.smul hγ w, ?_⟩⟩
  rw [← hw, iform_smul, h0]

theorem exists_smul_mem_C3Roots_or_B3Roots {a b : Fin (Tag.rank .F4) → ℤ} (ha : IsRoot .F4 a)
    (hb : IsRoot .F4 b) (hab : a ≠ b) (hab' : a ≠ -b) : ∃ w : WeylGroup .F4,
      (w • a ∈ C3Roots ∧ w • b ∈ C3Roots) ∨ (w • a ∈ B3Roots ∧ w • b ∈ B3Roots) := by
  obtain ⟨c, hc, hca, hcb⟩ := exists_isRoot_perp_of_ne ha hb hab hab'
  rcases iform_self_eq_two_or_four hc with h | h
  · obtain ⟨w, -, hw⟩ := exists_smul_mem_B3Roots_of_perp hc h
    exact ⟨w, Or.inr ⟨hw a ha hca, hw b hb hcb⟩⟩
  · obtain ⟨w, -, hw⟩ := exists_smul_mem_C3Roots_of_perp hc h
    exact ⟨w, Or.inl ⟨hw a ha hca, hw b hb hcb⟩⟩

theorem exists_smul_eq_of_stab {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (hs : iform β β = 2) (h01 : β 0 = 0 ∨ β 0 = 1) : ∃ u : WeylGroup .F4, u • rootR = rootR ∧
      (β 0 = 0 → u • β = ![0, 1, 2, 1]) ∧ (β 0 = 1 → u • β = rootS) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hβ
  rw [certificate_positions.1] at hk
  have h := stabWordsCheck_eq_true
  simp only [stabWordsCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
  rcases h k hk with (h4 | h0) | ⟨hr, hw⟩
  · omega
  · omega
  · refine ⟨weylOfWord .F4 (decodeWord (stabWords.getD k 0)), ?_, fun h0 => ?_, fun h1 => ?_⟩
    · rw [← certificate_positions.2.1, weylOfWord_smul_root_of_wordPos (by norm_num) hr]
    · rw [weylOfWord_smul_root_of_wordPos hk hw, ite_eq_left h0]
      exact certificate_positions.2.2.2.1
    · rw [weylOfWord_smul_root_of_wordPos hk hw, ite_eq_right (by omega)]
      exact certificate_positions.2.2.1

theorem exists_smul_eq_of_perp {a b : Fin (Tag.rank .F4) → ℤ} (ha : IsRoot .F4 a)
    (hal : iform a a = 4) (hb : IsRoot .F4 b) (hbs : iform b b = 2) (hab : iform a b = 0) :
    ∃ w : WeylGroup .F4, w • a = rootR ∧ w • b = ![0, 1, 2, 1] := by
  obtain ⟨w, hw⟩ := exists_smul_eq_rootR ha hal
  have hb' : iform rootR (w • b) = 0 := by rw [← hw, iform_smul, hab]
  rw [iform_rootR] at hb'
  have h0 : (w • b) 0 = 0 := by omega
  obtain ⟨u, hur, hub, -⟩ := exists_smul_eq_of_stab (IsRoot.smul hb w) (by rw [iform_smul, hbs])
    (Or.inl h0)
  exact ⟨u * w, by rw [mul_smul, hw, hur], by rw [mul_smul, hub h0]⟩

theorem exists_smul_eq_rootR_rootS {a b : Fin (Tag.rank .F4) → ℤ} (ha : IsRoot .F4 a)
    (hal : iform a a = 4) (hb : IsRoot .F4 b) (hbs : iform b b = 2) (hab : iform a b = 2) :
    ∃ w : WeylGroup .F4, w • a = rootR ∧ w • b = rootS := by
  obtain ⟨w, hw⟩ := exists_smul_eq_rootR ha hal
  have hb' : iform rootR (w • b) = 2 := by rw [← hw, iform_smul, hab]
  rw [iform_rootR] at hb'
  have h1 : (w • b) 0 = 1 := by omega
  obtain ⟨u, hur, -, hub⟩ := exists_smul_eq_of_stab (IsRoot.smul hb w) (by rw [iform_smul, hbs])
    (Or.inr h1)
  exact ⟨u * w, by rw [mul_smul, hw, hur], by rw [mul_smul, hub h1]⟩

theorem weylOfWord_rootR_eq : weylOfWord .F4 [0, 1] • rootR = root1242 := by
  rw [← certificate_positions.2.1, weylOfWord_smul_root_of_wordPos (by norm_num)
    explicitWords_check.1, certificate_positions.2.2.2.2.2.2.1]

theorem weylOfWord_rootR_rootS_mem_C3Roots :
    weylOfWord .F4 [0, 2, 1, 3, 2, 1, 0] • rootR = ![0, 1, 2, 2] ∧
      weylOfWord .F4 [0, 2, 1, 3, 2, 1, 0] • rootS = ![0, 1, 2, 1] := by
  constructor
  · rw [← certificate_positions.2.1, weylOfWord_smul_root_of_wordPos (by norm_num)
      explicitWords_check.2.1, certificate_positions.2.2.2.2.2.2.2.2.1]
  · rw [← certificate_positions.2.2.1, weylOfWord_smul_root_of_wordPos (by norm_num)
      explicitWords_check.2.2.1, certificate_positions.2.2.2.1]

theorem weylOfWord_rootS_mem_C3Roots :
    weylOfWord .F4 [1, 2, 1, 3, 2, 1, 0] • rootS = ![0, 1, 2, 1] := by
  rw [← certificate_positions.2.2.1, weylOfWord_smul_root_of_wordPos (by norm_num)
    explicitWords_check.2.2.2.1, certificate_positions.2.2.2.1]

theorem weylOfWord_endPair_mem_C3Roots :
    weylOfWord .F4 [1, 2, 1, 3, 2, 1, 0] • root1221 = ![0, 1, 1, 0] ∧
      weylOfWord .F4 [1, 2, 1, 3, 2, 1, 0] • root1242 = ![0, 1, 2, 2] := by
  constructor
  · rw [← certificate_positions.2.2.2.2.2.2.2.1, weylOfWord_smul_root_of_wordPos (by norm_num)
      explicitWords_check.2.2.2.2.1, certificate_positions.2.2.2.2.2.2.2.2.2]
  · rw [← certificate_positions.2.2.2.2.2.2.1, weylOfWord_smul_root_of_wordPos (by norm_num)
      explicitWords_check.2.2.2.2.2, certificate_positions.2.2.2.2.2.2.2.2.1]

end Weyl

end CFSG.SeitzReduction.F4Pilot
