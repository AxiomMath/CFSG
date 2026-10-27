module

public import Certificates.Data.Kernel.ChengHeldAutK
public import CFSG.Certificates.Kernel.ChengHeldPropsAutSound
public import CFSG.Certificates.Kernel.ChengHeldSec2Twin

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel
open CFSG.OddStandard.ChengHeld.Model
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.ChengHeldS2

variable {M : RegModel} {n : ℕ} {m : ℕ → ℕ → ℕ} {inv g : ℕ → ℕ}

theorem foldl_or_testBit (l : List ℕ) (b z : ℕ) :
    (l.foldl (fun b y => b ||| (1 <<< y)) b).testBit z = (b.testBit z || l.contains z) := by
  have h := testBit_foldl_or l id b z
  simp only [id_eq] at h
  rw [Bool.eq_iff_iff, h, Bool.or_eq_true, List.contains_iff_mem]
  constructor
  · rintro (h | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr hy
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨z, h, rfl⟩

theorem foldl_set_get' (l : List ℕ) (B : Array Bool) {z : ℕ} (hz : z < B.size) :
    (l.foldl (fun b y => b.set! y true) B)[z]! = (B[z]! || l.contains z) := by
  induction l generalizing B with
  | nil => simp
  | cons y l ih =>
    rw [List.foldl_cons, ih _ (by rw [Array.size_set!]; exact hz), List.contains_cons]
    by_cases hy : z = y
    · subst hy
      rw [Array.getElem!_set!_self _ _ _ hz]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hy), beq_false_of_ne hy, Bool.false_or]

theorem card_eq {B : Array Bool} {f : ℕ → Bool} (hs : B.size = n) (hf : ∀ i, B[i]! = f i) :
    card B = cardW n f := by
  unfold RegModel.card cardW
  rw [elems_eq hs hf]

theorem fixedPts_size'' (hN : M.N = n) (a : Array ℕ) : (M.fixedPts a).size = n := by
  simp [RegModel.fixedPts, hN]

theorem fixedPts_fix (hN : M.N = n) {a : Array ℕ} {af : ℕ → ℕ} (ha : ∀ x, a[x]! = af x) (x : ℕ) :
    (M.fixedPts a)[x]! = fixW n af x := by
  rw [fixedPts_get hN, ha]
  rfl

theorem bSubset_eq {A B : Array Bool} {f h : ℕ → Bool} (hA : A.size = n)
    (hf : ∀ i, A[i]! = f i) (hh : ∀ i, B[i]! = h i) :
    bSubset A B = (List.range n).all fun x => !f x || h x := by
  unfold bSubset
  rw [hA]
  simp only [hf, hh]

theorem twInvs_eq (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) {a : Array ℕ} {af : ℕ → ℕ}
    (ha : ∀ x, a[x]! = af x) : M.twInvs a = twInvsK n m af := by
  unfold RegModel.twInvs twInvsK
  rw [hN]
  exact List.filter_congr fun s _ => by rw [hm, ha]

theorem twOrb_eq (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) (hinv : ∀ a, M.inv[a]! = inv a)
    {a : Array ℕ} {af : ℕ → ℕ} (ha : ∀ x, a[x]! = af x) (s : ℕ) :
    ((List.range M.N).map fun x => M.m (M.m M.inv[x]! s) a[x]!).eraseDups = twOrbK n m inv af s := by
  unfold twOrbK
  rw [hN]
  congr 1
  exact List.map_congr_left fun x _ => by rw [hm, hm, hinv, ha]

theorem twOrbits_eq (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) (hinv : ∀ a, M.inv[a]! = inv a)
    {a : Array ℕ} {af : ℕ → ℕ} (ha : ∀ x, a[x]! = af x) :
    M.twOrbits a = twOrbitsK n m inv af := by
  rw [twOrbits_eq_foldl]
  unfold twOrbitsK
  have hmem : ∀ s ∈ M.twInvs a, s < n := by
    intro s hs
    unfold RegModel.twInvs at hs
    rw [← hN]
    exact List.mem_range.1 (List.mem_filter.1 hs).1
  rw [twInvs_eq hN hm ha] at hmem ⊢
  refine (List.foldl_rel (r := fun (st : Array Bool × List (List ℕ)) (st' : ℕ × List (List ℕ)) =>
    st.1.size = n ∧ (∀ i < n, st.1[i]! = st'.1.testBit i) ∧ st.2 = st'.2) ?_ ?_).2.2
  · refine ⟨by rw [Array.size_replicate, hN], fun i hi => ?_, rfl⟩
    rw [getElem!_pos _ _ (by rw [Array.size_replicate, hN]; exact hi), Array.getElem_replicate,
      Nat.zero_testBit]
  · rintro s hs ⟨B, out⟩ ⟨b, out'⟩ ⟨h1, h2, h3⟩
    have hsn := hmem s hs
    dsimp only at h1 h2 h3 ⊢
    unfold twStepK
    dsimp only
    rw [h2 s hsn, twOrb_eq hN hm hinv ha s]
    by_cases hc : (!b.testBit s) = true
    · rw [if_pos hc, if_pos hc]
      refine ⟨by rw [foldl_set_size, h1], fun i hi => ?_, by rw [h3]⟩
      rw [foldl_set_get' _ _ (by rw [h1]; exact hi), h2 i hi, foldl_or_testBit]
    · rw [if_neg hc, if_neg hc]
      exact ⟨h1, h2, h3⟩

theorem closure_bit (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) (hn : 0 < n)
    (hmlt : ∀ x y, x < n → y < n → m x y < n) {gs : List ℕ} {K : ℕ} (hc : clW n m gs K = true) :
    (M.closure gs).size = n ∧ ∀ z, (M.closure gs)[z]! = bitW n (clIterK n m gs K) z := by
  unfold clW at hc
  rw [Bool.and_eq_true, List.all_eq_true] at hc
  have hgs : ∀ g ∈ gs, g < n := fun g hg => by simpa [Nat.blt_eq] using hc.1 g hg
  have hmf : M.m = m := funext fun a => funext fun b => hm a b
  have := closure_get (M := M) (K := K) (by rw [hN]; exact hgs)
    (fun g hg y hy => by rw [hN, hm]; rw [hN] at hy; exact hmlt y g hy (hgs g hg))
    (by rw [hN]; exact hn) (by rw [hN, hmf]; exact Nat.eq_of_beq_eq_true hc.2)
  rw [hN, hmf] at this
  exact this

theorem gMapW_lt (hmlt : ∀ x y, x < n → y < n → m x y < n) (hinvlt : ∀ x < n, inv x < n)
    {af : ℕ → ℕ} (hlt : ∀ y < n, af y < n) (hg : ∀ j < 7, g j < n) {j y : ℕ} (hj : j < 8)
    (hy : y < n) : gMapW m inv g af j y < n := by
  cases j with
  | zero => exact hlt y hy
  | succ j =>
    have hgj := hg j (by omega)
    exact hmlt _ _ (hmlt _ _ (hinvlt _ hgj) hy) hgj

theorem testBit_orbIter_self (af : ℕ → ℕ) (x : ℕ) :
    ∀ k, (orbIterW n m inv g af x k).testBit x = true := by
  intro k
  induction k with
  | zero =>
    change (1 <<< x).testBit x = true
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp
  | succ k ih => exact (testBit_clStepK _ _ _ _ _).2 (Or.inl ih)

theorem orbitOf_bit (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) (hinv : ∀ a, M.inv[a]! = inv a)
    (hmlt : ∀ x y, x < n → y < n → m x y < n) (hinvlt : ∀ x < n, inv x < n)
    {a : Array ℕ} {af : ℕ → ℕ} (ha : ∀ x, a[x]! = af x) (hlt : ∀ y < n, af y < n)
    {x K : ℕ} (ho : orbW n m inv g af x K = true) :
    (∀ z, (M.orbitOf (a :: (List.range 7).map fun j => M.conjArr (g j)) x).contains z =
      bitW n (orbIterW n m inv g af x K) z) ∧
    (M.orbitOf (a :: (List.range 7).map fun j => M.conjArr (g j)) x).length =
      cardW n (bitW n (orbIterW n m inv g af x K)) := by
  unfold orbW at ho
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq] at ho
  obtain ⟨⟨hx, hg⟩, hfix⟩ := ho
  have hfix' := Nat.eq_of_beq_eq_true hfix
  set O := orbIterW n m inv g af x K
  set maps := a :: (List.range 7).map fun j => M.conjArr (g j)
  have hconj : ∀ s y, y < n → (M.conjArr s)[y]! = cjK m inv y s := by
    intro s y hy
    unfold RegModel.conjArr
    rw [getElem!_pos _ _ (by simp [hN, hy]), Array.getElem_map, Array.getElem_range,
      cj_eq hm hinv]
  have hmaps : ∀ f ∈ maps, ∀ y < n, ∃ j < 8, f[y]! = gMapW m inv g af j y := by
    intro f hf y hy
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨0, by omega, ha y⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
      exact ⟨j + 1, by rw [List.mem_range] at hj; omega, hconj _ y hy⟩
  have hmaps' : ∀ j < 8, ∀ y < n, ∃ f ∈ maps, f[y]! = gMapW m inv g af j y := by
    intro j hj y hy
    cases j with
    | zero => exact ⟨a, List.mem_cons_self, ha y⟩
    | succ j =>
      exact ⟨M.conjArr (g j), List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, List.mem_range.2
        (by omega), rfl⟩), hconj _ y hy⟩
  have hbd : ∀ f ∈ maps, ∀ y < M.N, f[y]! < M.N := by
    intro f hf y hy
    rw [hN] at hy ⊢
    obtain ⟨j, hj, e⟩ := hmaps f hf y hy
    rw [e]
    exact gMapW_lt hmlt hinvlt hlt hg hj hy
  obtain ⟨hnd, hlt', hx', hcl, hmin⟩ := orbitOf_spec maps (by rw [hN]; exact hx) hbd
  have reach : ∀ k z, (orbIterW n m inv g af x k).testBit z = true → z ∈ M.orbitOf maps x := by
    intro k
    induction k with
    | zero =>
      intro z hz
      change (1 <<< x).testBit z = true at hz
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hz
      rw [← of_decide_eq_true hz]
      exact hx'
    | succ k ih =>
      intro z hz
      rcases (testBit_clStepK _ _ _ _ _).1 hz with h | ⟨y, hy, hby, j, hj, rfl⟩
      · exact ih z h
      · obtain ⟨f, hf, e⟩ := hmaps' j (List.mem_range.1 hj) y hy
        rw [← e]
        exact hcl y (ih y hby) f hf
  have marked : ∀ z ∈ M.orbitOf maps x, z < n ∧ O.testBit z = true := by
    refine hmin (fun z => z < n ∧ O.testBit z = true) ⟨hx, testBit_orbIter_self af x K⟩ ?_
    rintro f hf y ⟨hy, hb⟩
    obtain ⟨j, hj, e⟩ := hmaps f hf y hy
    rw [e]
    refine ⟨gMapW_lt hmlt hinvlt hlt hg hj hy, ?_⟩
    rw [← hfix']
    exact (testBit_clStepK _ _ _ _ _).2 (Or.inr ⟨y, hy, hb, j, List.mem_range.2 hj, rfl⟩)
  have hiff : ∀ z, z ∈ M.orbitOf maps x ↔ bitW n O z = true := by
    intro z
    unfold bitW
    rw [Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨marked z, fun h => reach K z h.2⟩
  refine ⟨fun z => ?_, ?_⟩
  · rw [Bool.eq_iff_iff, List.contains_iff_mem]
    exact hiff z
  · unfold cardW elemsK
    have hp : (M.orbitOf maps x).Perm ((List.range n).filter (bitW n O)) := by
      rw [List.perm_ext_iff_of_nodup hnd ((List.nodup_range).filter _)]
      intro z
      rw [hiff, List.mem_filter, List.mem_range]
      constructor
      · intro h
        refine ⟨?_, h⟩
        unfold bitW at h
        rw [Bool.and_eq_true, decide_eq_true_iff] at h
        exact h.1
      · exact fun h => h.2
    exact hp.length_eq

theorem autOK_of {α K : ℕ} {A : ℕ → ℕ → ℕ} (hN : (mkReg α).N = n)
    (hm : ∀ a b, (mkReg α).m a b = m a b) (hinv : ∀ a, (mkReg α).inv[a]! = inv a)
    (hg : ∀ j, (mkReg α).g j = g j) (hn : 0 < n) (hmlt : ∀ x y, x < n → y < n → m x y < n)
    (hA0 : ∀ x, ((mkReg α).autMap ((mkReg α).tabImgs α 0))[x]! = A 0 x)
    (hA1 : ∀ x, ((mkReg α).autMap ((mkReg α).tabImgs α 1))[x]! = A 1 x)
    (hA2 : ∀ x, ((mkReg α).autMap ((mkReg α).tabImgs α 2))[x]! = A 2 x)
    (hI0 : (mkReg α).isInvolAut ((mkReg α).autMap ((mkReg α).tabImgs α 0)) = true)
    (hI1 : (mkReg α).isInvolAut ((mkReg α).autMap ((mkReg α).tabImgs α 1)) = true)
    (hI2 : (mkReg α).isInvolAut ((mkReg α).autMap ((mkReg α).tabImgs α 2)) = true)
    (hcl : (clW n m [g 0, g 1, m (g 3) (g 4), g 6] K && clW n m [g 0, g 1, g 2] K &&
      clW n m [g 0, m (m (m (g 3) (g 4)) (g 6)) (g 2)] K) = true)
    (hr : autRestW n m inv g α K A = true) : autOK α = true := by
  simp only [Bool.and_eq_true] at hcl
  obtain ⟨⟨cF, cG⟩, cU⟩ := hcl
  obtain ⟨sF, gF⟩ := closure_bit hN hm hn hmlt cF
  obtain ⟨sG, gG⟩ := closure_bit hN hm hn hmlt cG
  obtain ⟨sU, gU⟩ := closure_bit hN hm hn hmlt cU
  rw [← hr]
  unfold autOK autRestW
  simp only [List.all_cons, List.all_nil, Bool.and_true, hI0, hI1, hI2, Bool.true_and,
    card_eq (fixedPts_size'' hN _) (fixedPts_fix hN hA0),
    card_eq (fixedPts_size'' hN _) (fixedPts_fix hN hA1),
    card_eq (fixedPts_size'' hN _) (fixedPts_fix hN hA2),
    twInvs_eq hN hm hA0, twInvs_eq hN hm hA1, twInvs_eq hN hm hA2,
    twOrbits_eq hN hm hinv hA0, twOrbits_eq hN hm hinv hA1, twOrbits_eq hN hm hinv hA2,
    hg, pw_eq hm, hm,
    beq_bitmap (fixedPts_size'' hN _) sF (fixedPts_fix hN hA0) gF,
    beq_bitmap (fixedPts_size'' hN _) sG (fixedPts_fix hN hA1) gG,
    beq_bitmap (fixedPts_size'' hN _) sU (fixedPts_fix hN hA2) gU,
    bSubset_eq (fixedPts_size'' hN _) (fixedPts_fix hN hA0) gF,
    bSubset_eq (fixedPts_size'' hN _) (fixedPts_fix hN hA1) gG,
    bSubset_eq (fixedPts_size'' hN _) (fixedPts_fix hN hA2) gU]
  rfl

theorem gAutOK_of {α K : ℕ} {af : ℕ → ℕ} (hN : (mkReg α).N = n)
    (hm : ∀ a b, (mkReg α).m a b = m a b) (hinv : ∀ a, (mkReg α).inv[a]! = inv a)
    (hg : ∀ j, (mkReg α).g j = g j) (hn : 0 < n) (hmlt : ∀ x y, x < n → y < n → m x y < n)
    (hinvlt : ∀ x < n, inv x < n)
    (ha : ∀ x, ((mkReg α).autMap ((mkReg α).gImgs α))[x]! = af x) (hlt : ∀ y < n, af y < n)
    (hH : (mkReg α).isHom ((mkReg α).autMap ((mkReg α).gImgs α)) = true)
    (hBj : (mkReg α).isBij ((mkReg α).autMap ((mkReg α).gImgs α)) = true)
    (hP : (mkReg α).permOrd ((mkReg α).autMap ((mkReg α).gImgs α)) = 3)
    (hcl : (clW n m [g 0] K && clW n m [g 0, g 1, g 2] K) = true)
    (hV : α ≠ 2 → clW n m [pwK m (g 0) 2, g 1, m (g 0) (g 2)] K = true)
    (hop : orbW n m inv g af (g 1) K = true) (hot : α = 2 → orbW n m inv g af (g 2) K = true)
    (hoq : α = 2 → orbW n m inv g af (g 0) K = true)
    (hr : gRestW n m inv g α K af = true) : gAutOK α = true := by
  simp only [Bool.and_eq_true] at hcl
  obtain ⟨cZ, cD⟩ := hcl
  obtain ⟨sZ, gZ⟩ := closure_bit hN hm hn hmlt cZ
  obtain ⟨sD, gD⟩ := closure_bit hN hm hn hmlt cD
  obtain ⟨op1, op2⟩ := orbitOf_bit hN hm hinv hmlt hinvlt ha hlt hop
  rw [← hr]
  by_cases hα : α = 2
  · obtain ⟨ot1, ot2⟩ := orbitOf_bit hN hm hinv hmlt hinvlt ha hlt (hot hα)
    obtain ⟨oq1, oq2⟩ := orbitOf_bit hN hm hinv hmlt hinvlt ha hlt (hoq hα)
    subst hα
    unfold gAutOK gRestW
    simp only [hH, hBj, hP, Bool.true_and, beq_self_eq_true, hN, hm, hinv, ha, hg,
      ↓reduceIte, card_eq sZ gZ, card_eq sD gD, elems_eq sD gD, gZ, gD, op1, op2, ot1, ot2, oq1,
      oq2]
  · obtain ⟨sV, gV⟩ := closure_bit hN hm hn hmlt (hV hα)
    unfold gAutOK gRestW
    simp only [hH, hBj, hP, Bool.true_and, beq_self_eq_true, hN, hm, hinv, ha, hg, hα,
      if_false, pw_eq hm, card_eq sZ gZ, card_eq sD gD, elems_eq sD gD, gZ, gD, op1, op2,
      card_eq sV gV, elems_eq sV gV, gV]

theorem autMap_size' (M : RegModel) (img : Array ℕ) : (M.autMap img).size = M.N := by
  rw [autMap_eq_foldl]
  suffices h : ∀ (l : List ℕ) (b : Array ℕ), (l.foldl (fun a i => a.set! M.order[i]!
      (M.m img[M.label[i]!]! a[M.parent[i]!]!)) b).size = b.size by
    rw [h, Array.size_replicate]
  intro l
  induction l with
  | nil => intro b; rfl
  | cons i l ih => intro b; rw [List.foldl_cons, ih, Array.size_set!]

variable {w : ℕ} {T PL G : ℕ → ℕ} {IXP IVP : ℕ}

theorem autOK_bound {α K : ℕ} {A : ℕ → ℕ} (hB : Bound (mkReg α) n w T PL G IXP IVP) (hn : 0 < n)
    (hmlt : ∀ x y, x < n → y < n → mW n w T IXP x y < n)
    (hrec : ∀ k < 3, autRecW n w (mW n w T IXP) T PL (imgL (mW n w T IXP) (iW n w IVP) (gW w G)
      (if α = 2 then act2Rels k else actRels α k)) (A k) = true)
    (hlt : ∀ k < 3, ltW n w (A k) = true) (hhom : ∀ k < 3, homW n w T IXP (A k) = true)
    (hinvo : ∀ k < 3, invoW n w (A k) = true)
    (hcl : (clW n (mW n w T IXP) [gW w G 0, gW w G 1, mW n w T IXP (gW w G 3) (gW w G 4), gW w G 6] K &&
      clW n (mW n w T IXP) [gW w G 0, gW w G 1, gW w G 2] K &&
      clW n (mW n w T IXP) [gW w G 0, mW n w T IXP (mW n w T IXP (mW n w T IXP (gW w G 3)
        (gW w G 4)) (gW w G 6)) (gW w G 2)] K) = true)
    (hr : autRestW n (mW n w T IXP) (iW n w IVP) (gW w G) α K (fun k => aW n w (A k)) = true) :
    autOK α = true := by
  have hA : ∀ k < 3, ∀ x, ((mkReg α).autMap ((mkReg α).tabImgs α k))[x]! = aW n w (A k) x :=
    fun k hk => autMap_of hB hn (fun j hj => tabImgs_eq hB α k hj) (hrec k hk)
  have hI : ∀ k < 3, (mkReg α).isInvolAut ((mkReg α).autMap ((mkReg α).tabImgs α k)) = true :=
    fun k hk => isInvolAut_of hB (by rw [autMap_size', hB.N_eq]) (hA k hk) (hlt k hk) (hhom k hk)
      (hinvo k hk)
  exact autOK_of (A := fun k => aW n w (A k)) hB.N_eq hB.m_eq hB.inv_eq hB.g_eq hn hmlt
    (hA 0 (by norm_num)) (hA 1 (by norm_num)) (hA 2 (by norm_num)) (hI 0 (by norm_num))
    (hI 1 (by norm_num)) (hI 2 (by norm_num)) hcl hr

theorem gAutOK_bound {α K P x0 : ℕ} (hB : Bound (mkReg α) n w T PL G IXP IVP) (hn : 0 < n)
    (hmlt : ∀ x y, x < n → y < n → mW n w T IXP x y < n) (hb : bindW n w T PL IXP IVP = true)
    (hrec : autRecW n w (mW n w T IXP) T PL (imgL (mW n w T IXP) (iW n w IVP) (gW w G)
      (gRels α)) P = true)
    (hlt : ltW n w P = true) (hhom : homW n w T IXP P = true) (h3 : ord3W n w P x0 = true)
    (hcl : (clW n (mW n w T IXP) [gW w G 0] K &&
      clW n (mW n w T IXP) [gW w G 0, gW w G 1, gW w G 2] K) = true)
    (hV : α ≠ 2 → clW n (mW n w T IXP) [pwK (mW n w T IXP) (gW w G 0) 2, gW w G 1,
      mW n w T IXP (gW w G 0) (gW w G 2)] K = true)
    (hop : orbW n (mW n w T IXP) (iW n w IVP) (gW w G) (aW n w P) (gW w G 1) K = true)
    (hot : α = 2 → orbW n (mW n w T IXP) (iW n w IVP) (gW w G) (aW n w P) (gW w G 2) K = true)
    (hoq : α = 2 → orbW n (mW n w T IXP) (iW n w IVP) (gW w G) (aW n w P) (gW w G 0) K = true)
    (hr : gRestW n (mW n w T IXP) (iW n w IVP) (gW w G) α K (aW n w P) = true) :
    gAutOK α = true := by
  have ha := autMap_of hB hn (fun j hj => gImgs_eq hB α hj) hrec
  exact gAutOK_of hB.N_eq hB.m_eq hB.inv_eq hB.g_eq hn hmlt
    (fun x hx => (bindW_parts hb hx).2.2.1) ha (fun y hy => ltW_spec hlt hy)
    (isHom_of hB (by rw [autMap_size', hB.N_eq]) ha hlt hhom) (isBij_of hB ha hlt h3)
    (permOrd_of hB ha h3) hcl hV hop hot hoq hr

end CFSG.KC.ChengHeldP

end
