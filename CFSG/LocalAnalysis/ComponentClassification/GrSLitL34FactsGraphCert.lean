module

public import Certificates.Certificate22210
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup

structure GraphParts : Prop where
  bits : bitsOK = true
  decomp : decompOK = true
  invert : ∀ ρ ∈ [r₂T, r₃T, r₄T],
    ∀ t ∈ (orbitBFS 42 gTabs (gTabs.map (invTab 42)) ρ 1963).tabs.toList, invertOK xAll t = true

theorem graphParts : GraphParts := by
  have h := Certificates.certificate22210
  unfold graphOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, fun ρ hρ => List.all_eq_true.mp (h.2 ρ hρ)⟩

theorem commBit_cbit {κ k w : ℕ} (hκ : κ ∈ [0, 1, 2])
    (hk : k < 16) (hw : w = 4 ∨ w = 8) :
    commBit κ k w (cbit κ k w) = true ∧ commBit κ (4 * k) w (cbit κ (4 * k) w) = true := by
  have h := graphParts.bits
  simp only [bitsOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact h κ hκ k hk w (by rcases hw with rfl | rfl <;> simp)

theorem tabRep_xTab (k m : ℕ) : TabRep (xTab k m) (wordPerm (tg k) * wordPerm (tg (4 * m))) :=
  (tabRep_wordTab _).comp (tabRep_wordTab _)

theorem exists_decomp
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) :
    ∃ k < 16, ∃ m < 16, wordPerm (tg k) * wordPerm (tg (4 * m)) = t := by
  obtain ⟨n, hn, rfl⟩ := exists_tg ht
  have h := graphParts.decomp
  simp only [decompOK, allBelow_eq_true, anyBelow_eq_true] at h
  obtain ⟨k, hk, m, hm, he⟩ := h n hn
  exact ⟨k, hk, m, hm, ((tabRep_xTab k m).beq_iff (tabRep_wordTab _)).1 he⟩

theorem xTab_mem_xTabs {κ k m : ℕ} (hk : k < 16) (hm : m < 16) (hx : xc κ k m = true) :
    xTab k m ∈ xTabs κ := by
  simp only [xTabs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter]
  exact ⟨k, hk, m, ⟨hm, hx⟩, rfl⟩

theorem xTabs_mem_xAll {κ : ℕ} (hκ : κ ∈ [0, 1, 2]) : xTabs κ ∈ xAll := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
  rcases hκ with rfl | rfl | rfl <;> simp [xAll]

theorem exists_orbit_tab {r : Equiv.Perm (Fin 42)} (hrR : r ∈ R)
    (hr2 : r * r = 1) (hrS : r ∉ S) :
    ∃ ρ ∈ [r₂T, r₃T, r₄T], ∃ t ∈ (orbitBFS 42 gTabs (gTabs.map (invTab 42)) ρ 1963).tabs.toList,
      TabRep t r := by
  have hord : orderOf (⟨r, hrR⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hrS ?_
    · simp only [OneMemClass.coe_one, pow_two]
      exact hr2
    · have h' : r = 1 := congrArg Subtype.val h
      rw [h']
      exact S.one_mem
  rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
  · exact absurd (mem_S_of_isConj₁ h) hrS
  · obtain ⟨t, ht, hrep⟩ := (conjClass₂.1 _).1 h
    exact ⟨r₂T, List.mem_cons_self .., t, ht, hrep⟩
  · obtain ⟨t, ht, hrep⟩ := (conjClass₃.1 _).1 h
    exact ⟨r₃T, List.mem_cons_of_mem _ (List.mem_cons_self ..), t, ht, hrep⟩
  · obtain ⟨t, ht, hrep⟩ := (conjClass₄.1 _).1 h
    exact ⟨r₄T, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), t, ht,
      hrep⟩

theorem invert_spec
    {r : Equiv.Perm (Fin 42)} (hrR : r ∈ R) (hr2 : r * r = 1) (hrS : r ∉ S)
    (h4 : r * wordPerm (tg 4) = wordPerm (tg 4) * r)
    (h8 : r * wordPerm (tg 8) = wordPerm (tg 8) * r) {κ : ℕ} (hκ : κ ∈ [0, 1, 2])
    {k m k' m' : ℕ} (hk : k < 16) (hm : m < 16) (hk' : k' < 16) (hm' : m' < 16)
    (hx : xc κ k m = true) (hx' : xc κ k' m' = true)
    (he : r * (wordPerm (tg k) * wordPerm (tg (4 * m))) * r⁻¹ =
      wordPerm (tg k') * wordPerm (tg (4 * m'))) :
    wordPerm (tg k') * wordPerm (tg (4 * m')) * (wordPerm (tg k) * wordPerm (tg (4 * m))) = 1 := by
  obtain ⟨ρ, hρ, t, ht, hrep⟩ := exists_orbit_tab hrR hr2 hrS
  have hI := graphParts.invert ρ hρ t ht
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hc4 : (comp 42 t (wordTab (tg 4)) == comp 42 (wordTab (tg 4)) t) = true :=
    ((hrep.comp (tabRep_wordTab _)).beq_iff ((tabRep_wordTab _).comp hrep)).2 h4
  have hc8 : (comp 42 t (wordTab (tg 8)) == comp 42 (wordTab (tg 8)) t) = true :=
    ((hrep.comp (tabRep_wordTab _)).beq_iff ((tabRep_wordTab _).comp hrep)).2 h8
  rw [invertOK, hc4, hc8, Bool.and_self, Bool.not_true, Bool.false_or, List.all_eq_true] at hI
  have h1 := List.all_eq_true.mp (hI _ (xTabs_mem_xAll hκ)) _ (xTab_mem_xTabs hk hm hx)
  have hrep' : TabRep t r⁻¹ := by rw [hri]; exact hrep
  have hy := hrep.conjTab (tabRep_xTab k m) hrep'
  rw [he] at hy
  rw [hy.tab_eq (tabRep_xTab k' m'), List.contains_iff_mem.mpr (xTab_mem_xTabs hk' hm' hx'),
    Bool.not_true, Bool.false_or] at h1
  exact ((tabRep_xTab k' m').comp (tabRep_xTab k m)).beq_iff TabRep.idTab |>.1 h1

end CFSG.ComponentClassification.GrSLit.L34Facts
