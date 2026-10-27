module

public import Certificates.Data.Kernel.Bounds.Table
public import TauCeti.GroupTheory.Presentation.GroupPresentation
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.QuotientGroup
import CFSG.Sporadic.Presentation.Common
public import CFSG.Certificates.Kernel.CosetBoundsLemmas
import Mathlib

public section

namespace CFSG.Certificates.KB

open CFSG.Certificates.KB.Sound

@[expose] def sword {G : Type*} [Group G] (gen : ℕ → G) (w : List (ℕ × Bool)) : G :=
  (w.map fun x => if x.2 then gen x.1 else (gen x.1)⁻¹).prod

def inAlpha (amap g : ℕ) : Prop := g < 256 ∧ byte amap g ≠ 0

abbrev alphaSub {G : Type*} [Group G] (gen : ℕ → G) (amap : ℕ) : Subgroup G :=
  Subgroup.closure (gen '' {g | inAlpha amap g})

abbrev wordSub {G : Type*} [Group G] (gen : ℕ → G) (ws : List (List (ℕ × Bool))) : Subgroup G :=
  Subgroup.closure (sword gen '' {w | w ∈ ws})

theorem idAmap_succ (n : ℕ) :
    idAmap (n + 1) = Nat.lor (idAmap n) (Nat.shiftLeft (n + 1) (Nat.shiftLeft n 3)) := rfl

theorem idAmap_spec (n : ℕ) (hn : n ≤ 255) :
    idAmap n < 2 ^ (8 * n) ∧ ∀ g, byte (idAmap n) g = if g < n then g + 1 else 0 := by
  induction n with
  | zero =>
    refine ⟨by decide, fun g => ?_⟩
    rw [byte_eq]
    simp [idAmap]
  | succ n ih =>
    obtain ⟨hlt, hb⟩ := ih (by omega)
    have h8 : n <<< 3 = 8 * n := by
      rw [Nat.shiftLeft_eq]
      ring
    have he : idAmap (n + 1) = (n + 1) * 2 ^ (8 * n) + idAmap n := by
      rw [idAmap_succ]
      change idAmap n ||| (n + 1) <<< (n <<< 3) = _
      rw [h8, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq]
    have hP : 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 := by
      rw [Nat.mul_succ, pow_add]
      norm_num
    have hbd : idAmap (n + 1) < 2 ^ (8 * (n + 1)) := by
      rw [he, hP]
      have := Nat.mul_le_mul_right (2 ^ (8 * n)) (show n + 2 ≤ 256 by omega)
      nlinarith
    refine ⟨hbd, fun g => ?_⟩
    rcases lt_trichotomy g n with hg | rfl | hg
    · have hg1 : g < n + 1 := by omega
      have hbg := hb g
      simp only [hg, hg1, ↓reduceIte] at hbg ⊢
      rw [byte_eq] at hbg
      rw [byte_eq, he]
      obtain ⟨d, rfl⟩ : ∃ d, n = g + 1 + d := ⟨n - g - 1, by omega⟩
      have h8d : 8 * (g + 1 + d) = 8 * g + 8 + 8 * d := by ring
      have hQ : (g + 1 + d + 1) * 2 ^ (8 * (g + 1 + d)) =
          (256 * ((g + 1 + d + 1) * 2 ^ (8 * d))) * 2 ^ (8 * g) := by
        rw [h8d, pow_add, pow_add]
        ring
      rw [hQ, add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_left]
      exact hbg
    · have hg1 : g < g + 1 := by omega
      simp only [hg1, ↓reduceIte]
      rw [byte_eq, he, add_comm, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt hlt, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · have hg1 : ¬g < n + 1 := by omega
      simp only [hg1, ↓reduceIte]
      rw [byte_eq, Nat.div_eq_of_lt
        (lt_of_lt_of_le hbd (Nat.pow_le_pow_right (by norm_num) (by omega))), Nat.zero_mod]

theorem topOk_sound {amap n : ℕ} (hn : n < 256) (h : topOk amap n = true) (g : ℕ) :
    inAlpha amap g ↔ g < n := by
  unfold topOk at h
  rw [Nat.eq_of_beq_eq_true h]
  unfold inAlpha
  rw [(idAmap_spec n (by omega)).2 g]
  by_cases hg : g < n
  · simp [hg]
    omega
  · simp [hg]

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h (by simp [andB])
  · exact ⟨rfl, h⟩

theorem tableOk_alphaOk {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ}
    {amap : ℕ} {rels words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) : alphaOk amap L = true := by
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨h7, -⟩ := andB_true h
  exact (andB_true (andB_true h7).2).2

theorem lensLt_iff (ws : List (List (ℕ × Bool))) (b : ℕ) :
    lensLt ws b = true ↔ ∀ w ∈ ws, w.length < b := by
  have hlen : ∀ w : List (ℕ × Bool),
      List.rec (motive := fun _ => ℕ) 0 (fun _ _ n => Nat.succ n) w = w.length := by
    intro w
    induction w with
    | nil => rfl
    | cons x w ih => exact congrArg Nat.succ ih
  induction ws with
  | nil => simp [lensLt]
  | cons w ws ih =>
    change andB (Nat.blt (List.rec (motive := fun _ => ℕ) 0 (fun _ _ n => Nat.succ n) w) b)
      (lensLt ws b) = true ↔ _
    rw [hlen]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := andB_true h
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Nat.blt_eq.mp h1
      · exact (ih.mp h2) v hv
    · intro h
      have h1 : Nat.blt w.length b = true := Nat.blt_eq.mpr (h w (List.mem_cons_self ..))
      have h2 : lensLt ws b = true := ih.mpr fun v hv => h v (List.mem_cons_of_mem _ hv)
      rw [h1, h2]
      rfl

theorem tableOk_lens {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ}
    {amap : ℕ} {rels words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) : (∀ r ∈ rels, r.length < 256) ∧ ∀ w ∈ words, w.length < 256 := by
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨hr, h⟩ := andB_true h
  obtain ⟨hw, -⟩ := andB_true h
  exact ⟨(lensLt_iff _ _).mp hr, (lensLt_iff _ _).mp hw⟩

noncomputable def alphaGen (amap k : ℕ) : ℕ :=
  open Classical in if h : ∃ g, g < 256 ∧ byte amap g = k + 1 then Classical.choose h else 0

theorem alphaGen_spec {amap k : ℕ} (h : ∃ g, g < 256 ∧ byte amap g = k + 1) :
    alphaGen amap k < 256 ∧ byte amap (alphaGen amap k) = k + 1 := by
  unfold alphaGen
  split
  · exact Classical.choose_spec ‹_›
  · contradiction

noncomputable def letterVal {G : Type*} [Group G] (gen : ℕ → G) (amap L c : ℕ) : G :=
  if c < L then
    (if c % 2 = 0 then gen (alphaGen amap (c / 2)) else (gen (alphaGen amap (c / 2)))⁻¹)
  else 1

structure AlphaStruct (amap cnt : ℕ) : Prop where
  le : ∀ g < 256, byte amap g ≤ cnt
  inj : ∀ g1 g2, g1 < 256 → g2 < 256 → byte amap g1 ≠ 0 → byte amap g1 = byte amap g2 → g1 = g2
  surj : ∀ k, 1 ≤ k → k ≤ cnt → ∃ g < 256, byte amap g = k

theorem alphaGen_byte {amap cnt g : ℕ} (hA : AlphaStruct amap cnt) (hg : inAlpha amap g) :
    alphaGen amap (byte amap g - 1) = g := by
  have hb0 := hg.2
  have hex : ∃ g', g' < 256 ∧ byte amap g' = byte amap g - 1 + 1 := ⟨g, hg.1, by omega⟩
  obtain ⟨h1, h2⟩ := alphaGen_spec hex
  exact hA.inj _ _ h1 hg.1 (by omega) (by omega)

theorem alphaGen_mem {amap cnt k : ℕ} (hA : AlphaStruct amap cnt) (hk : k < cnt) :
    inAlpha amap (alphaGen amap k) := by
  obtain ⟨g, hg, hb⟩ := hA.surj (k + 1) (by omega) (by omega)
  obtain ⟨h1, h2⟩ := alphaGen_spec ⟨g, hg, hb⟩
  exact ⟨h1, by omega⟩

theorem sCode_val {G : Type*} [Group G] (gen : ℕ → G) {amap cnt L : ℕ} (hA : AlphaStruct amap cnt)
    (hL : L = 2 * cnt) {g : ℕ} (b : Bool) (hg : inAlpha amap g) :
    sCode amap (g, b) < L ∧
      letterVal gen amap L (sCode amap (g, b)) = if b then gen g else (gen g)⁻¹ := by
  have hc : sCode amap (g, b) = 2 * (byte amap g - 1) + (if b = true then 0 else 1) := by
    have hg' : g < 256 ∧ byte amap g ≠ 0 := hg
    rw [sCode_eq, ite_eq_left_of_eq_true _ _ (eq_true hg')]
  have hle := hA.le g hg.1
  have hb0 := hg.2
  have hgen := alphaGen_byte hA hg
  rw [hc]
  cases b
  · have h1 : 2 * (byte amap g - 1) + 1 < L := by omega
    have h2 : ¬ (2 * (byte amap g - 1) + 1) % 2 = 0 := by omega
    have h3 : (2 * (byte amap g - 1) + 1) / 2 = byte amap g - 1 := by omega
    refine ⟨by simpa using h1, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte, letterVal, h1, h2, h3, hgen]
  · have h1 : 2 * (byte amap g - 1) < L := by omega
    have h2 : (2 * (byte amap g - 1)) % 2 = 0 := by omega
    have h3 : (2 * (byte amap g - 1)) / 2 = byte amap g - 1 := by omega
    refine ⟨by simpa using h1, ?_⟩
    simp only [↓reduceIte, letterVal, h1, h2, h3, hgen, add_zero]

theorem lv_codes {G : Type*} [Group G] (gen : ℕ → G) {amap cnt L : ℕ} (hA : AlphaStruct amap cnt)
    (hL : L = 2 * cnt) : ∀ w : List (ℕ × Bool), (∀ x ∈ w, inAlpha amap x.1) →
      lv (letterVal gen amap L) (w.map (sCode amap)) = sword gen w
  | [], _ => rfl
  | (g, b) :: w, h => by
    rw [List.map_cons, lv_cons, lv_codes gen hA hL w (fun y hy => h y (by simp [hy])),
      (sCode_val gen hA hL b (h (g, b) (by simp))).2]
    simp only [sword, List.map_cons, List.prod_cons]

theorem letterVal_xor {G : Type*} [Group G] (gen : ℕ → G) {amap L c : ℕ} (hLe : L % 2 = 0)
    (hc : c < L) : Nat.xor c 1 < L ∧ letterVal gen amap L (Nat.xor c 1) = (letterVal gen amap L c)⁻¹ := by
  have hx : Nat.xor c 1 = c ^^^ 1 := rfl
  rw [hx]
  rcases Nat.even_or_odd c with he | ho
  · rw [Nat.xor_one_of_even he]
    obtain ⟨k, hk⟩ := he
    have h1 : c + 1 < L := by omega
    have h2 : ¬ (c + 1) % 2 = 0 := by omega
    have h3 : (c + 1) / 2 = c / 2 := by omega
    have h4 : c % 2 = 0 := by omega
    refine ⟨h1, ?_⟩
    simp only [letterVal, h1, hc, h2, h3, h4, ↓reduceIte]
  · rw [Nat.xor_one_of_odd ho]
    obtain ⟨k, hk⟩ := ho
    have h1 : c - 1 < L := by omega
    have h2 : (c - 1) % 2 = 0 := by omega
    have h3 : (c - 1) / 2 = c / 2 := by omega
    have h4 : ¬ c % 2 = 0 := by omega
    refine ⟨h1, ?_⟩
    simp only [letterVal, h1, hc, h2, h3, h4, ↓reduceIte, inv_inv]

theorem letterVal_mem {G : Type*} [Group G] (gen : ℕ → G) {amap cnt L : ℕ}
    (hA : AlphaStruct amap cnt) (hL : L = 2 * cnt) (c : ℕ) :
    letterVal gen amap L c ∈ alphaSub gen amap := by
  unfold letterVal
  split_ifs with h1 h2
  · exact Subgroup.subset_closure ⟨_, alphaGen_mem hA (by omega), rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, alphaGen_mem hA (by omega), rfl⟩)
  · exact Subgroup.one_mem _

theorem alphaSub_le_closure {G : Type*} [Group G] (gen : ℕ → G) {amap cnt L : ℕ}
    (hA : AlphaStruct amap cnt) (hL : L = 2 * cnt) :
    alphaSub gen amap ≤ Subgroup.closure (letterVal gen amap L '' {c | c < L}) := by
  rw [alphaSub, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨h1, h2⟩ := sCode_val gen hA hL true hg
  exact Subgroup.subset_closure ⟨_, h1, by rw [h2]; rfl⟩

theorem sword_mem {G : Type*} [Group G] (gen : ℕ → G) {amap : ℕ} :
    ∀ w : List (ℕ × Bool), (∀ x ∈ w, inAlpha amap x.1) → sword gen w ∈ alphaSub gen amap
  | [], _ => Subgroup.one_mem _
  | x :: w, h => by
    have hx : gen x.1 ∈ alphaSub gen amap := Subgroup.subset_closure ⟨x.1, h x (by simp), rfl⟩
    have hw := sword_mem gen w (fun y hy => h y (by simp [hy]))
    simp only [sword, List.map_cons, List.prod_cons]
    refine Subgroup.mul_mem _ ?_ hw
    split_ifs
    · exact hx
    · exact Subgroup.inv_mem _ hx

theorem tableOk_sound_alpha {G : Type*} [Group G] (gen : ℕ → G) {rels : List (List (ℕ × Bool))}
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    (hrels : ∀ r ∈ rels, (∀ x ∈ r, inAlpha amap x.1) → sword gen r = 1)
    {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) :
    wordSub gen words ≤ alphaSub gen amap ∧ (wordSub gen words).relIndex (alphaSub gen amap) ≠ 0 ∧
      (wordSub gen words).relIndex (alphaSub gen amap) ≤ N := by
  obtain ⟨hlr, hlw⟩ := tableOk_lens h
  unfold tableOk at h
  simp only [andB_true_iff] at h
  obtain ⟨hL128, hN1, hNl, hlab, hlabbad, hFbad, hnRb, hnSb, -, -, hhdr, hrel, hsub, hwords, hw2,
    htree, hwalk, hcov⟩ := h
  have hL128' : L + 1 ≤ 128 := Nat.le_of_ble_eq_true hL128
  have hN1' : 1 ≤ N := Nat.le_of_ble_eq_true hN1
  have hNl' : N ≤ nLab := Nat.le_of_ble_eq_true hNl
  have hlab' : nLab = nT + 1 := Nat.eq_of_beq_eq_true hlab
  have hlabbad' : nLab + 1 ≤ bad := Nat.le_of_ble_eq_true hlabbad
  have hFbad' : nF + 1 ≤ bad := Nat.le_of_ble_eq_true hFbad
  have hnRb' : nR + 1 ≤ bad := Nat.le_of_ble_eq_true hnRb
  have hnSb' : nS + 1 ≤ bad := Nat.le_of_ble_eq_true hnSb
  have hwalk' := Nat.eq_of_beq_eq_true hwalk
  have hcov' := Nat.eq_of_beq_eq_true hcov
  obtain ⟨heps, hinvOk, halpha⟩ := hdrOk_spec hhdr
  obtain ⟨cnt, hL, hcard, hsurj⟩ := alphaOk_spec halpha
  obtain ⟨hle, hinj⟩ := alpha_struct hcard hsurj
  have hA : AlphaStruct amap cnt := ⟨hle, hinj, hsurj⟩
  obtain ⟨hinvL, hinvc⟩ := invOk_spec hinvOk
  have hLe : L % 2 = 0 := by omega
  have hxor : ∀ c < L, letterVal gen amap L (Nat.xor c 1) = (letterVal gen amap L c)⁻¹ :=
    fun c hc => (letterVal_xor gen hLe hc).2
  have hvL : letterVal gen amap L L = 1 := by
    unfold letterVal
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.lt_irrefl L))]
  have hinvv : ∀ c ≤ L, letterVal gen amap L (byte inv c) = (letterVal gen amap L c)⁻¹ := by
    intro c hc
    rcases Nat.lt_or_eq_of_le hc with hc | rfl
    · rw [hinvc c hc]
      exact hxor c hc
    · rw [hinvL, hvL, inv_one]
  have hR : ∀ i < nR, wLetters (R i) = pkb 256 (wbytes (R i)) ∧
      lv (letterVal gen amap L) (wbytes (R i)) = 1 := by
    unfold relsOk at hrel
    have hfold := Nat.eq_of_beq_eq_true hrel
    have hg := (relsOk_run R amap rels 0).good (by rw [hfold]; omega)
    rw [hfold] at hg
    intro i hi
    obtain ⟨r, hr, hok, hRi⟩ := hg i (Nat.zero_le _) hi
    have hrlen := hlr r hr
    obtain ⟨hs1, hs2⟩ := sEnc_spec amap r (by omega)
    have hin : ∀ x ∈ r, inAlpha amap x.1 := fun x hx => sCode_lt (hs1.1 hok x hx)
    have hcodes : ∀ d ∈ r.map (sCode amap), d < 256 := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      exact hs1.1 hok x hx
    have hwb : wbytes (r.length + 2 ^ 24 * pkb 256 (r.map (sCode amap))) = r.map (sCode amap) := by
      rw [wbytes, entry_wN _ _ hrlen, entry_wLetters _ _ (by omega)]
      have := bytes_pkb _ hcodes
      rwa [List.length_map] at this
    rw [hRi, hs2 hok, hwb, entry_wLetters _ _ (by omega), lv_codes gen hA hL r hin]
    exact ⟨rfl, hrels r hr hin⟩
  obtain ⟨hnS, hS⟩ := subsOk_spec hsub (by omega)
  have hwords_in : ∀ w ∈ words, ∀ x ∈ w, inAlpha amap x.1 := by
    intro w hw x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
    have hwlen := hlw _ hw
    exact sCode_lt ((sEnc_spec amap _ (by omega)).1.1 (hS i hi).1 x hx)
  have hSv : ∀ i < nS, lv (letterVal gen amap L) (wbytes (S i)) ∈ wordSub gen words := by
    intro i hi
    rw [hnS] at hi
    obtain ⟨hok, hSi⟩ := hS i hi
    have hwmem : words[i] ∈ words := List.getElem_mem hi
    have hwlen := hlw _ hwmem
    obtain ⟨hs1, hs2⟩ := sEnc_spec amap words[i] (by omega)
    have hcodes : ∀ d ∈ words[i].map (sCode amap), d < 256 := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      exact hs1.1 hok x hx
    have hwb : wbytes ((words[i].length + 256) + 2 ^ 24 * pkb 256 (words[i].map (sCode amap))) =
        words[i].map (sCode amap) := by
      rw [wbytes, entry_wN_lor _ _ hwlen, entry_wLetters _ _ (by omega)]
      have := bytes_pkb _ hcodes
      rwa [List.length_map] at this
    rw [hSi, hs2 hok, entry_lor _ _ hwlen, hwb, lv_codes gen hA hL _ (hwords_in _ hwmem)]
    exact Subgroup.subset_closure ⟨_, hwmem, rfl⟩
  have hW : ∀ j < nW, (∀ q < wN (Wd j), letter (Wd j) q ≤ L) ∧
      (wKind (Wd j) = 0 → lv (letterVal gen amap L) (wbytes (Wd j)) = 1) ∧
      (wKind (Wd j) = 1 → lv (letterVal gen amap L) (wbytes (Wd j)) ∈ wordSub gen words) := by
    intro j hj
    unfold wordsOkB at hwords
    obtain ⟨h1, h2⟩ := natrec_all2 (fun i => wordOkB R S inv eps nR nS (Wd i))
      (fun i => lettersLe eps (Wd i)) nW hwords j hj
    have := word_sem (wordSub gen words) (letterVal gen amap L) (by omega : eps < 128)
      (by rw [heps]; exact hvL) (fun c hc => hinvv c (by omega)) hR hSv h1 h2
    rwa [heps] at this
  have hcl := cover_closed (wordSub gen words) (letterVal gen amap L) hNl' hlab' hlabbad' hFbad'
    hxor hinvv hW hw2 htree hwalk' hcov'
  have hHA : wordSub gen words ≤ alphaSub gen amap := by
    rw [wordSub, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact sword_mem gen w (hwords_in w hw)
  obtain ⟨h0, hle'⟩ := index_le (letterVal gen amap L) (rep (letterVal gen amap L) F D nT)
    (alphaSub_le_closure gen hA hL) (rep_mem _ F D nT _ (letterVal_mem gen hA hL))
    (rep_zero _ F D nT) hN1'
    (fun c hc => ⟨Nat.xor c 1, (letterVal_xor gen (amap := amap) hLe hc).1,
      (letterVal_xor gen hLe hc).2⟩) hcl
  exact ⟨hHA, h0, hle'⟩

theorem tableOk_sound {G : Type*} [Group G] (gen : ℕ → G) {rels : List (List (ℕ × Bool))}
    (hrels : ∀ r ∈ rels, sword gen r = 1)
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) :
    wordSub gen words ≤ alphaSub gen amap ∧ (wordSub gen words).relIndex (alphaSub gen amap) ≠ 0 ∧
      (wordSub gen words).relIndex (alphaSub gen amap) ≤ N :=
  tableOk_sound_alpha gen (fun r hr _ => hrels r hr) h

theorem linkOk_sound {G : Type*} [Group G] (gen : ℕ → G) {amap' : ℕ}
    {ws : List (List (ℕ × Bool))} (hws : ∀ w ∈ ws, w.length < 256) (h : linkOk amap' ws = true) :
    wordSub gen ws = alphaSub gen amap' := by
  obtain ⟨hcard, hws'⟩ := linkOk_spec h
  have key : ∀ i (hi : i < ws.length), ∃ g, g < 256 ∧ byte amap' g = i + 1 ∧ ws[i] = [(g, true)] := by
    intro i hi
    obtain ⟨hok, he⟩ := hws' i hi
    have hlen := hws _ (List.getElem_mem hi)
    obtain ⟨hs1, hs2⟩ := sEnc_spec amap' ws[i] (by omega)
    rw [hs2 hok] at he
    have hr : Nat.lor 1 (Nat.shiftLeft (Nat.shiftLeft i 1) 24) = 1 + 2 ^ 24 * (2 * i) := by
      change 1 ||| ((i <<< 1) <<< 24) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by norm_num : 1 < 2 ^ 24),
        Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      ring
    rw [hr] at he
    norm_num at he
    have hl1 : ws[i].length = 1 := by omega
    have hP : pkb 256 (ws[i].map (sCode amap')) = 2 * i := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl1
    have hin := sCode_lt (hs1.1 hok x (by rw [hx]; simp))
    rw [hx] at hP
    obtain ⟨g, b⟩ := x
    simp only at hin
    simp only [List.map_cons, List.map_nil, pkb_cons, pkb_nil, mul_zero, add_zero] at hP
    rw [sCode_eq, ite_eq_left_of_eq_true _ _ (eq_true hin)] at hP
    cases b
    · simp at hP
      omega
    · simp at hP
      exact ⟨g, hin.1, by have := hin.2; omega, hx⟩
  have hsurj : ∀ k, 1 ≤ k → k ≤ ws.length → ∃ g < 256, byte amap' g = k := by
    intro k hk1 hk2
    obtain ⟨g, hg, hb, -⟩ := key (k - 1) (by omega)
    exact ⟨g, hg, by omega⟩
  obtain ⟨hle, hinj⟩ := alpha_struct hcard hsurj
  apply le_antisymm
  · rw [wordSub, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
    obtain ⟨g, hg, hb, he⟩ := key i hi
    rw [he]
    have hgm : gen g ∈ alphaSub gen amap' := Subgroup.subset_closure ⟨g, ⟨hg, by omega⟩, rfl⟩
    simpa [sword] using hgm
  · rw [alphaSub, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : inAlpha amap' g := hg
    have hb := hle g hg'.1
    have hb0 := hg'.2
    obtain ⟨g', hg'', hb', he⟩ := key (byte amap' g - 1) (by omega)
    have hgg : g' = g := hinj g' g hg'' hg'.1 (by omega) (by omega)
    subst hgg
    apply Subgroup.subset_closure
    refine ⟨_, List.getElem_mem (by omega : byte amap' g' - 1 < ws.length), ?_⟩
    rw [he]
    simp [sword]

theorem hasRel_cons (amap e : ℕ) (r : List (ℕ × Bool)) (rels : List (List (ℕ × Bool))) :
    hasRel amap e (r :: rels) = Bool.rec (hasRel amap e rels)
      (Bool.rec (hasRel amap e rels) true (Nat.beq (sEnc amap r).1 e)) (sEnc amap r).2 := rfl

theorem hasRel_spec {amap e : ℕ} : ∀ {rels : List (List (ℕ × Bool))}, hasRel amap e rels = true →
    ∃ r ∈ rels, (sEnc amap r).2 = true ∧ (sEnc amap r).1 = e
  | [], h => absurd h Bool.false_ne_true
  | r :: rels, h => by
    rw [hasRel_cons] at h
    cases hok : (sEnc amap r).2 <;> rw [hok] at h
    · obtain ⟨r', hr', h'⟩ := hasRel_spec h
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩
    · cases hb : Nat.beq (sEnc amap r).1 e <;> rw [hb] at h
      · obtain ⟨r', hr', h'⟩ := hasRel_spec h
        exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩
      · exact ⟨r, by simp, hok, Nat.eq_of_beq_eq_true hb⟩

theorem pkb_rep (l : List ℕ) (hl : ∀ d ∈ l, d < 256) (P : ℕ) (hP : P = pkb 256 l) : ∀ k,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun _ acc => Nat.lor (Nat.shiftLeft acc (Nat.shiftLeft l.length (nat_lit 3))) P) k =
      pkb 256 (List.replicate k l).flatten
  | 0 => rfl
  | k + 1 => by
    change Nat.lor (Nat.shiftLeft (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun _ acc => Nat.lor (Nat.shiftLeft acc (Nat.shiftLeft l.length (nat_lit 3))) P) k)
      (Nat.shiftLeft l.length (nat_lit 3))) P = _
    rw [pkb_rep l hl P hP k]
    refine (Nat.lor_comm _ _).trans ?_
    rw [hP]
    refine (lor_shift _ _ _ (pkb_lt hl)).trans ?_
    rw [List.replicate_succ, List.flatten_cons, pkb_append]

theorem lv_rep {G : Type*} [Group G] (val : ℕ → G) (l : List ℕ) :
    ∀ k, lv val (List.replicate k l).flatten = lv val l ^ k
  | 0 => by
    rw [List.replicate_zero, List.flatten_nil, pow_zero]
    rfl
  | k + 1 => by
    rw [List.replicate_succ, List.flatten_cons, lv_append, lv_rep val l k, pow_succ']

theorem length_rep (l : List ℕ) : ∀ k, ((List.replicate k l).flatten).length = l.length * k
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, List.flatten_cons, List.length_append, length_rep l k]
    ring

theorem powOk_sound {G : Type*} [Group G] (gen : ℕ → G) {rels : List (List (ℕ × Bool))}
    (hrels : ∀ r ∈ rels, sword gen r = 1) (hrl : ∀ r ∈ rels, r.length < 256)
    {amap L k : ℕ} {ws : List (List (ℕ × Bool))} (hws : ∀ w ∈ ws, w.length < 256)
    (hα : alphaOk amap L = true) (h : powOk amap ws k rels = true) :
    ∃ w, ws = [w] ∧ 0 < k ∧ (w.length * k < 2 ^ 24 → sword gen w ^ k = 1) := by
  rcases ws with _ | ⟨w, tl⟩
  · exact absurd h Bool.false_ne_true
  have e : powOk amap (w :: tl) k rels = Bool.rec false
      (Bool.rec false (Bool.rec false (hasRel amap (powEnc (sEnc amap w).1 k) rels)
        (sEnc amap w).2) (Nat.ble (nat_lit 1) k))
      (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) tl) := rfl
  rw [e] at h
  rcases tl with _ | ⟨_, _⟩
  swap
  · exact absurd h Bool.false_ne_true
  cases hk : Nat.ble (nat_lit 1) k <;> rw [hk] at h
  · exact absurd h Bool.false_ne_true
  cases hok : (sEnc amap w).2 <;> rw [hok] at h
  · exact absurd h Bool.false_ne_true
  refine ⟨w, rfl, Nat.le_of_ble_eq_true hk, fun hlen => ?_⟩
  obtain ⟨cnt, hL, hcard, hsurj⟩ := alphaOk_spec hα
  obtain ⟨hle, hinj⟩ := alpha_struct hcard hsurj
  have hA : AlphaStruct amap cnt := ⟨hle, hinj, hsurj⟩
  have hwl := hws w (by simp)
  obtain ⟨hs1, hs2⟩ := sEnc_spec amap w (by omega)
  have hwin : ∀ x ∈ w, inAlpha amap x.1 := fun x hx => sCode_lt (hs1.1 hok x hx)
  have hcodes : ∀ d ∈ w.map (sCode amap), d < 256 := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact hs1.1 hok x hx
  have hll : (w.map (sCode amap)).length = w.length := List.length_map _
  have hpow : powEnc (sEnc amap w).1 k =
      (w.length * k) + 2 ^ 24 * pkb 256 (List.replicate k (w.map (sCode amap))).flatten := by
    rw [hs2 hok]
    unfold powEnc
    have hn : Nat.land (w.length + 2 ^ 24 * pkb 256 (w.map (sCode amap))) (nat_lit 16777215) =
        (w.map (sCode amap)).length := by
      change (w.length + 2 ^ 24 * pkb 256 (w.map (sCode amap))) &&& (2 ^ 24 - 1) = _
      rw [land_mask, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), hll]
    have hP : Nat.shiftRight (w.length + 2 ^ 24 * pkb 256 (w.map (sCode amap))) (nat_lit 24) =
        pkb 256 (w.map (sCode amap)) := by
      change (w.length + 2 ^ 24 * pkb 256 (w.map (sCode amap))) >>> 24 = _
      rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt (by omega), zero_add]
    rw [hn, hP, pkb_rep _ hcodes _ rfl k]
    change ((w.map (sCode amap)).length * k) |||
      (pkb 256 (List.replicate k (w.map (sCode amap))).flatten <<< 24) = _
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by rw [hll]; exact hlen), Nat.shiftLeft_eq,
      hll]
    ring
  rw [hpow] at h
  obtain ⟨r, hr, hrok, hre⟩ := hasRel_spec h
  have hrlen := hrl r hr
  obtain ⟨hr1, hr2⟩ := sEnc_spec amap r (by omega)
  rw [hr2 hrok] at hre
  have hrin : ∀ x ∈ r, inAlpha amap x.1 := fun x hx => sCode_lt (hr1.1 hrok x hx)
  have hrcodes : ∀ d ∈ r.map (sCode amap), d < 256 := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact hr1.1 hrok x hx
  have hrepc : ∀ d ∈ (List.replicate k (w.map (sCode amap))).flatten, d < 256 := by
    intro d hd
    simp only [List.mem_flatten, List.mem_replicate] at hd
    obtain ⟨_, ⟨-, rfl⟩, hd⟩ := hd
    exact hcodes d hd
  have hm : r.length = w.length * k ∧ pkb 256 (r.map (sCode amap)) =
      pkb 256 (List.replicate k (w.map (sCode amap))).flatten := by
    generalize w.length * k = n at hre hlen
    generalize pkb 256 (r.map (sCode amap)) = A at hre
    generalize pkb 256 (List.replicate k (w.map (sCode amap))).flatten = B at hre
    norm_num at hre hlen
    omega
  have hlists : r.map (sCode amap) = (List.replicate k (w.map (sCode amap))).flatten := by
    have e1 := bytes_pkb _ hrcodes
    have e2 := bytes_pkb _ hrepc
    rw [List.length_map, hm.1, hm.2] at e1
    rw [length_rep, hll] at e2
    rw [← e1, e2]
  have := hrels r hr
  rw [← lv_codes gen hA hL r hrin, hlists, lv_rep, lv_codes gen hA hL w hwin] at this
  exact this

theorem card_le_step {G : Type*} [Group G] {H K : Subgroup G} {N M : ℕ}
    (h : H ≤ K ∧ H.relIndex K ≠ 0 ∧ H.relIndex K ≤ N) (hH : Nat.card H ≠ 0 ∧ Nat.card H ≤ M) :
    Nat.card K ≠ 0 ∧ Nat.card K ≤ N * M := by
  obtain ⟨hHK, h0, hN⟩ := h
  have hc : Nat.card H * H.relIndex K = Nat.card K := by
    rw [← Subgroup.relIndex_bot_left, ← Subgroup.relIndex_bot_left,
      Subgroup.relIndex_mul_relIndex ⊥ H K bot_le hHK]
  rw [← hc]
  exact ⟨Nat.mul_ne_zero hH.1 h0, by rw [Nat.mul_comm]; exact Nat.mul_le_mul hN hH.2⟩

theorem card_bot_le {G : Type*} [Group G] : Nat.card (⊥ : Subgroup G) ≠ 0 ∧
    Nat.card (⊥ : Subgroup G) ≤ 1 := by
  rw [Subgroup.card_bot]
  exact ⟨one_ne_zero, le_rfl⟩

theorem wordSub_nil {G : Type*} [Group G] (gen : ℕ → G) : wordSub gen [] = ⊥ := by
  simp [wordSub]

theorem card_wordSub_single_le {G : Type*} [Group G] (gen : ℕ → G) {w : List (ℕ × Bool)} {k : ℕ}
    (hk : 0 < k) (hw : sword gen w ^ k = 1) :
    Nat.card (wordSub gen [w]) ≠ 0 ∧ Nat.card (wordSub gen [w]) ≤ k := by
  have hz : wordSub gen [w] = Subgroup.zpowers (sword gen w) := by
    simp [wordSub, Subgroup.zpowers_eq_closure]
  rw [hz, Nat.card_zpowers]
  have hd : orderOf (sword gen w) ∣ k := orderOf_dvd_of_pow_eq_one hw
  exact ⟨(Nat.pos_of_dvd_of_pos hd hk).ne', Nat.le_of_dvd hk hd⟩

theorem finite_card_le_of_top {G : Type*} [Group G] {K : Subgroup G} {n : ℕ} (hK : K = ⊤)
    (h : Nat.card K ≠ 0 ∧ Nat.card K ≤ n) : Finite G ∧ Nat.card G ≤ n := by
  subst hK
  rw [Subgroup.card_top] at h
  exact ⟨Nat.finite_of_card_ne_zero h.1, h.2⟩

@[expose] noncomputable def tcGen (P : TauCeti.GroupPresentation) (g : ℕ) : P.Group :=
  if h : g < P.generatorCount then PresentedGroup.of ⟨g, h⟩ else 1

theorem sword_tcGen (P : TauCeti.GroupPresentation) (w : List (Fin P.generatorCount × Bool)) :
    sword (tcGen P) (w.map fun l => (l.1.val, l.2)) =
      PresentedGroup.mk P.relatorSet (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, sword, List.map_cons, List.prod_cons, ← sword, ih,
      show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
    congr 1
    obtain ⟨j, b⟩ := l
    have hj : tcGen P j.val = PresentedGroup.of j := by simp [tcGen, j.isLt]
    cases b
    · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv]
      simp only [Bool.false_eq_true, ↓reduceIte, hj]
      rfl
    · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl]
      simp only [↓reduceIte, hj]
      rfl

theorem sword_relatorLetters (P : TauCeti.GroupPresentation) :
    ∀ r ∈ P.relatorLetters, sword (tcGen P) r = 1 := by
  intro r hr
  rw [TauCeti.GroupPresentation.relatorLetters_def, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [sword_tcGen]
  apply PresentedGroup.one_of_mem
  rw [CFSG.Sporadic.Presentation.relatorSet_eq]
  exact List.mem_map_of_mem hw

theorem closure_tcGen (P : TauCeti.GroupPresentation) :
    Subgroup.closure (tcGen P '' {g | g < P.generatorCount}) = ⊤ := by
  rw [← PresentedGroup.closure_range_of]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, by simp [tcGen, hg]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, j.isLt, by simp [tcGen, j.isLt]⟩

theorem alphaSub_top (P : TauCeti.GroupPresentation) {amap : ℕ} (hn : P.generatorCount < 256)
    (h : topOk amap P.generatorCount = true) : alphaSub (tcGen P) amap = ⊤ := by
  rw [alphaSub, ← closure_tcGen P]
  congr 2
  ext g
  exact topOk_sound hn h g

theorem sword_rels (P : TauCeti.GroupPresentation) {rels : List (List (ℕ × Bool))}
    (h : P.relatorLetters = rels) : ∀ r ∈ rels, sword (tcGen P) r = 1 := by
  rw [← h]
  exact sword_relatorLetters P

theorem finite_card_le_of_route (P : TauCeti.GroupPresentation) {amap n N : ℕ}
    (hn : P.generatorCount = n) (h256 : n < 256) (htop : topOk amap n = true)
    (h : Nat.card (alphaSub (tcGen P) amap) ≠ 0 ∧ Nat.card (alphaSub (tcGen P) amap) ≤ N) :
    Finite P.Group ∧ Nat.card P.Group ≤ N := by
  subst hn
  exact finite_card_le_of_top (alphaSub_top P h256 htop) h

end CFSG.Certificates.KB
