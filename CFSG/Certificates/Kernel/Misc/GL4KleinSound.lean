module

public import Certificates.Data.Kernel.Misc.GL4Klein
public import CFSG.Certificates.Kernel.Misc.GL4F3Sound
public import CFSG.Certificates.Kernel.Misc.GL4EltSound

public section

namespace CFSG.KC.Misc.GL4

open Matrix Certificates.A5GL42

@[expose] def vc (x : ℕ) : Vec4 := fun i => ofCode x i 0

@[expose] def ColC (x : ℕ) : Prop := x < 65536 ∧ ∀ i j : Fin 4, j ≠ 0 → ofCode x i j = 0

abbrev vs (L : List ℕ) : Finset Vec4 := (L.map vc).toFinset

abbrev ms (L : List ℕ) : Finset Mat4 := (L.map ofCode).toFinset

theorem vc_mul (c x : ℕ) : vc (mul4F c x) = ofCode c *ᵥ vc x := by
  funext i
  simp only [vc, mul4F_ofCode, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem vc_xor (x y : ℕ) : vc (x ^^^ y) = vc x + vc y := by
  have e : ofCode (x ^^^ y) = ofCode x + ofCode y := ofCode_xor x y
  funext i
  simp only [vc, e, Matrix.add_apply, Pi.add_apply]

theorem vc_zero : vc 0 = 0 := by
  funext i
  simp [vc, ofCode_zero]

theorem sub2 (v w : Vec4) : v - w = v + w := by
  have h : ∀ a b : ZMod 2, a - b = a + b := by decide
  funext i
  exact h (v i) (w i)

theorem vc_comm (a x : ℕ) : vc (x ^^^ mul4F a x) = vc x - ofCode a *ᵥ vc x := by
  rw [vc_xor, vc_mul, sub2]

theorem colC_bits : ∀ u < 16, ∀ i < 4, ∀ j < 4,
    (colC u).testBit (4 * i + j) = (decide (j = 0) && u.testBit i) := by decide +kernel

theorem colC_col {u : ℕ} (hu : u < 16) (i j : Fin 4) (hj : j ≠ 0) : ofCode (colC u) i j = 0 := by
  have hj' : j.val ≠ 0 := fun e => hj (Fin.ext e)
  simp [ofCode, colC_bits u hu i i.2 j j.2, hj']

theorem vc_colC {u : ℕ} (hu : u < 16) : vc (colC u) = vecOfCode u := by
  funext i
  have h := colC_bits u hu i i.2 0 (by norm_num)
  simp only [add_zero, decide_true, Bool.true_and] at h
  simp [vc, ofCode, vecOfCode, h]

theorem colC_isCol {u : ℕ} (hu : u < 16) : ColC (colC u) := ⟨colC_lt u hu, colC_col hu⟩

theorem zero_col : ColC 0 := ⟨by norm_num, fun i j _ => by simp [ofCode_zero]⟩

theorem mul_col (c : ℕ) {x : ℕ} (hx : ColC x) : ColC (mul4F c x) := by
  refine ⟨mul4F_lt _ _, fun i j hj => ?_⟩
  rw [mul4F_ofCode, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => by rw [hx.2 k j hj, mul_zero]

theorem xor_lt {x y : ℕ} (hx : x < 65536) (hy : y < 65536) : x ^^^ y < 65536 := by
  have h : (65536 : ℕ) = 2 ^ 16 := by norm_num
  rw [h] at hx hy ⊢
  exact Nat.xor_lt_two_pow hx hy

theorem xor_col {x y : ℕ} (hx : ColC x) (hy : ColC y) : ColC (x ^^^ y) := by
  have e : ofCode (x ^^^ y) = ofCode x + ofCode y := ofCode_xor x y
  refine ⟨xor_lt hx.1 hy.1, fun i j hj => ?_⟩
  rw [e, Matrix.add_apply, hx.2 i j hj, hy.2 i j hj, add_zero]

theorem col_eq {x y : ℕ} (hx : ColC x) (hy : ColC y) (h : vc x = vc y) : x = y := by
  refine ofCode_inj hx.1 hy.1 (Matrix.ext fun i j => ?_)
  by_cases hj : j = 0
  · subst hj
    exact congrFun h i
  · rw [hx.2 i j hj, hy.2 i j hj]

theorem col_iff {x y : ℕ} (hx : ColC x) (hy : ColC y) : x = y ↔ vc x = vc y :=
  ⟨fun h => h ▸ rfl, col_eq hx hy⟩

theorem fix_iff' (a : ℕ) {x : ℕ} (hx : ColC x) : mul4F a x = x ↔ ofCode a *ᵥ vc x = vc x := by
  rw [col_iff (mul_col a hx) hx, vc_mul]

theorem V16_col : ∀ x ∈ V16, ColC x := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
  exact colC_isCol (List.mem_range.1 hu)

theorem vc_surj (v : Vec4) : ∃ x ∈ V16, vc x = v := by
  obtain ⟨u, hu, rfl⟩ := vec_surj v
  exact ⟨colC u, List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩, vc_colC hu⟩

theorem mem_vs {L : List ℕ} {v : Vec4} : v ∈ vs L ↔ ∃ x ∈ L, vc x = v := by
  rw [List.mem_toFinset, List.mem_map]

theorem mem_ms {L : List ℕ} {g : Mat4} : g ∈ ms L ↔ ∃ x ∈ L, ofCode x = g := by
  rw [List.mem_toFinset, List.mem_map]

theorem vc_mem_vs {L : List ℕ} (hL : ∀ x ∈ L, ColC x) {y : ℕ} (hy : ColC y) :
    vc y ∈ vs L ↔ y ∈ L := by
  rw [mem_vs]
  constructor
  · rintro ⟨x, hx, e⟩
    rwa [← col_eq (hL x hx) hy e]
  · intro h
    exact ⟨y, h, rfl⟩

theorem univ_eq : (Finset.univ : Finset Vec4) = vs V16 :=
  (Finset.eq_univ_iff_forall.2 fun v => mem_vs.2 (vc_surj v)).symm

theorem vs_zero : vs [0] = {0} := by
  simp [vs, vc_zero]

theorem vs_eq_of {l m : List ℕ} (h : SameL l m) : vs l = vs m := by
  ext v
  simp only [mem_vs]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, h.1 x hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, h.2 x hx, e⟩⟩

theorem ms_eq_of {l m : List ℕ} (h : SameL l m) : ms l = ms m := by
  ext v
  simp only [mem_ms]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, h.1 x hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, h.2 x hx, e⟩⟩

theorem card_vs {L : List ℕ} (hL : ∀ x ∈ L, ColC x) : (vs L).card = L.dedup.length := by
  have e : vs L = L.toFinset.image vc := by
    ext v
    simp [vs]
  rw [e, Finset.card_image_of_injOn, List.card_toFinset]
  intro x hx y hy h
  exact col_eq (hL x (List.mem_toFinset.1 hx)) (hL y (List.mem_toFinset.1 hy)) h

theorem card_ms {S : List ℕ} (hS : ∀ c ∈ S, c < 65536) : (ms S).card = S.dedup.length := by
  have e : ms S = S.toFinset.image ofCode := by
    ext v
    simp [ms]
  rw [e, Finset.card_image_of_injOn, List.card_toFinset]
  intro x hx y hy h
  exact ofCode_inj (hS x (List.mem_toFinset.1 hx)) (hS y (List.mem_toFinset.1 hy)) h

theorem span_of {Fc : List ℕ} {n : ℕ} (hF : ∀ x ∈ Fc, ColC x) (h : SpanC Fc n) :
    0 ∈ vs Fc ∧ (∀ u ∈ vs Fc, ∀ w ∈ vs Fc, u + w ∈ vs Fc) ∧ (vs Fc).card = n := by
  obtain ⟨h0, hx, hc⟩ := h
  refine ⟨mem_vs.2 ⟨0, h0, vc_zero⟩, ?_, (card_vs hF).trans hc⟩
  intro u hu w hw
  obtain ⟨x, hxm, rfl⟩ := mem_vs.1 hu
  obtain ⟨y, hym, rfl⟩ := mem_vs.1 hw
  exact mem_vs.2 ⟨_, hx x hxm y hym, vc_xor x y⟩

theorem mem_commL {Ac Sc : List ℕ} {z : ℕ} :
    z ∈ commL Ac Sc ↔ ∃ a ∈ Ac, ∃ x ∈ Sc, x ^^^ mul4F a x = z := by
  simp [commL, List.mem_dedup, List.mem_flatMap, List.mem_map]

theorem commL_col {Ac Sc : List ℕ} (hS : ∀ x ∈ Sc, ColC x) : ∀ z ∈ commL Ac Sc, ColC z := by
  intro z hz
  obtain ⟨a, -, x, hx, rfl⟩ := mem_commL.1 hz
  exact xor_col (hS x hx) (mul_col a (hS x hx))

theorem commSet_eq (Ac Sc : List ℕ) : commSet (ms Ac) (vs Sc) = vs (commL Ac Sc) := by
  ext v
  simp only [commSet, Finset.mem_image, Finset.mem_product, mem_ms, mem_vs, mem_commL]
  constructor
  · rintro ⟨⟨g, w⟩, ⟨⟨a, ha, rfl⟩, ⟨x, hx, rfl⟩⟩, rfl⟩
    exact ⟨_, ⟨a, ha, x, hx, rfl⟩, vc_comm a x⟩
  · rintro ⟨z, ⟨a, ha, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨ofCode a, vc x⟩, ⟨⟨a, ha, rfl⟩, ⟨x, hx, rfl⟩⟩, (vc_comm a x).symm⟩

theorem mem_fixL {Ac : List ℕ} {x : ℕ} : x ∈ fixL Ac ↔ x ∈ V16 ∧ ∀ a ∈ Ac, mul4F a x = x := by
  simp [fixL, List.mem_filter, List.all_eq_true, Nat.beq_eq]

theorem fixL_col {Ac : List ℕ} : ∀ x ∈ fixL Ac, ColC x := fun x hx => V16_col x (mem_fixL.1 hx).1

theorem fixSet_eq (Ac : List ℕ) : fixSet (ms Ac) = vs (fixL Ac) := by
  ext v
  obtain ⟨x, hx, rfl⟩ := vc_surj v
  have hc := V16_col x hx
  rw [vc_mem_vs fixL_col hc, mem_fixL]
  simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and, mem_ms]
  constructor
  · intro h
    exact ⟨hx, fun a ha => (fix_iff' a hc).2 (h _ ⟨a, ha, rfl⟩)⟩
  · rintro ⟨-, h⟩ g ⟨a, ha, rfl⟩
    exact (fix_iff' a hc).1 (h a ha)

theorem mat_eq_iff (M N : Mat4) : (∀ v : Vec4, M *ᵥ v = N *ᵥ v) ↔ M = N :=
  ⟨fun h => Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using h v),
    fun h v => h ▸ rfl⟩

theorem mem_normL {Hc Ac : List ℕ} {h : ℕ} :
    h ∈ normL Hc Ac ↔ h ∈ Hc ∧ ∀ x ∈ Ac, ∃ y ∈ Ac, mul4F h x = mul4F y h := by
  simp [normL, List.mem_filter, List.all_eq_true, List.any_eq_true, Nat.beq_eq]

theorem normSet_eq (Hc Ac : List ℕ) : normSet (ms Hc) (ms Ac) = ms (normL Hc Ac) := by
  ext g
  simp only [normSet, Finset.mem_filter, mem_ms]
  constructor
  · rintro ⟨⟨h, hh, rfl⟩, hn⟩
    refine ⟨h, mem_normL.2 ⟨hh, fun x hx => ?_⟩, rfl⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, e⟩ := hn _ ⟨x, hx, rfl⟩
    refine ⟨y, hy, ofCode_inj (mul4F_lt _ _) (mul4F_lt _ _) ?_⟩
    rw [mul4F_ofCode, mul4F_ofCode]
    refine (mat_eq_iff _ _).1 fun v => ?_
    have e' := e v
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at e'
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hh, hn⟩ := mem_normL.1 hh
    refine ⟨⟨h, hh, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := hn x hx
    refine ⟨ofCode y, ⟨y, hy, rfl⟩, fun v => ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mul4F_ofCode, ← mul4F_ofCode, e]

theorem stabC_of {c : ℕ} {s : List ℕ} (hlt : ∀ x ∈ s, x < 16)
    (h : ∀ w ∈ (s.map vecOfCode).toFinset, ofCode c *ᵥ w ∈ (s.map vecOfCode).toFinset) :
    StabC c s := by
  intro x hx
  have h' := h (vecOfCode x) (List.mem_toFinset.2 (List.mem_map_of_mem hx))
  obtain ⟨y, hy, e⟩ := List.mem_map.1 (List.mem_toFinset.1 h')
  refine ⟨y, hy, col_eq (mul_col c (colC_isCol (hlt x hx))) (colC_isCol (hlt y hy)) ?_⟩
  rw [vc_mul, vc_colC (hlt x hx), vc_colC (hlt y hy), e]

theorem invSub_eq (hsc : SubspacesComplete) (hlt : ∀ s ∈ subspaceCodes, ∀ x ∈ s, x < 16)
    {Bc : List ℕ} {Ls : List (List ℕ)} (hc : LatC Bc Ls) :
    invSubspaces (ms Bc) = (Ls.map vs).toFinset := by
  obtain ⟨h1, h2⟩ := hc
  ext W
  simp only [invSubspaces, Finset.mem_filter, List.mem_toFinset, List.mem_map, mem_ms]
  constructor
  · rintro ⟨hW, hinv⟩
    unfold subspaces at hW
    rw [List.mem_toFinset, List.mem_map] at hW
    obtain ⟨l, hl, rfl⟩ := hW
    have hl16 := hlt l hl
    obtain ⟨m, hm, hs⟩ := h2 l hl fun h hh => stabC_of hl16 (hinv _ ⟨h, hh, rfl⟩)
    refine ⟨m, hm, ?_⟩
    ext v
    rw [mem_vs, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hs.2 x hx)
      exact ⟨u, hu, (vc_colC (hl16 u hu)).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨colC u, hs.1 _ (List.mem_map_of_mem hu), vc_colC (hl16 u hu)⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨h0, hx, hB⟩ := h1 m hm
    refine ⟨hsc _ (mem_vs.2 ⟨0, h0, vc_zero⟩) ?_, ?_⟩
    · intro v hv w hw
      obtain ⟨x, hxm, rfl⟩ := mem_vs.1 hv
      obtain ⟨y, hym, rfl⟩ := mem_vs.1 hw
      exact mem_vs.2 ⟨_, hx x hxm y hym, vc_xor x y⟩
    · rintro _ ⟨h, hh, rfl⟩ v hv
      obtain ⟨x, hxm, rfl⟩ := mem_vs.1 hv
      exact mem_vs.2 ⟨_, hB h hh x hxm, vc_mul h x⟩

theorem sub_ms {Ac : List ℕ} {A' : Finset Mat4} (h : A' ⊆ ms Ac) :
    ∃ S ∈ Ac.sublists, A' = ms S := by
  classical
  refine ⟨Ac.filter fun c => decide (ofCode c ∈ A'), List.mem_sublists.2 List.filter_sublist, ?_⟩
  ext g
  simp only [mem_ms, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hg
    obtain ⟨c, hc, rfl⟩ := mem_ms.1 (h hg)
    exact ⟨c, ⟨hc, hg⟩, rfl⟩
  · rintro ⟨c, ⟨-, hc⟩, rfl⟩
    exact hc

theorem mulC_of {S : List ℕ} (hS : ∀ c ∈ S, c < 65536) (h : IsMulSet (ms S)) : MulC S := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun c hc d hd => ?_⟩
  · obtain ⟨c, hc, e⟩ := mem_ms.1 h1
    rwa [← (ofCode_eq_one (hS c hc)).1 e]
  · obtain ⟨e, he, ee⟩ := mem_ms.1 (h2 _ (mem_ms.2 ⟨c, hc, rfl⟩) _ (mem_ms.2 ⟨d, hd, rfl⟩))
    rwa [← ofCode_inj (hS e he) (mul4F_lt c d) (ee.trans (mul4F_ofCode c d).symm)]

theorem offC_of {S : List ℕ} (hS : ∀ c ∈ S, c < 65536) (h : Offender (ms S)) : OffC S := by
  obtain ⟨⟨_, hg, hne⟩, hq, hcard⟩ := h
  obtain ⟨c, hc, rfl⟩ := mem_ms.1 hg
  refine ⟨⟨c, hc, fun e => hne (by rw [e, ofCode_id4])⟩, fun c hc d hd x hx => ?_, ?_⟩
  · have hx' := V16_col x hx
    have h1 := xor_col hx' (mul_col c hx')
    refine col_eq (xor_col h1 (mul_col d h1)) zero_col ?_
    rw [vc_zero, vc_comm, vc_comm]
    exact hq _ (mem_ms.2 ⟨c, hc, rfl⟩) _ (mem_ms.2 ⟨d, hd, rfl⟩) (vc x)
  · rwa [fixSet_eq, card_vs fixL_col, card_ms hS] at hcard

theorem kAc_lt {a b : ℕ} (ha : a < 65536) (hb : b < 65536) : ∀ c ∈ kAc a b, c < 65536 := by
  intro c hc
  simp only [kAc, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · change id4 < 65536
    decide
  · exact ha
  · exact hb
  · exact mul4F_lt _ _

theorem klein_eq (a b : ℕ) : klein (ofCode a) (ofCode b) = ms (kAc a b) := by
  simp [klein, kAc, ms, mul4F_ofCode, ofCode_id4]

theorem kleinC_of {a b : ℕ} (ha : a < 65536) (hb : b < 65536)
    (h : IsKlein (ofCode a) (ofCode b)) : KleinC a b := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun e => h1 (by rw [e, ofCode_id4]), fun e => h2 (by rw [e, ofCode_id4]),
    fun e => h3 (by rw [e]), ?_, ?_, ?_⟩
  · exact (ofCode_eq_one (mul4F_lt a a)).1 (by rw [mul4F_ofCode, h4])
  · exact (ofCode_eq_one (mul4F_lt b b)).1 (by rw [mul4F_ofCode, h5])
  · exact ofCode_inj (mul4F_lt _ _) (mul4F_lt _ _) (by rw [mul4F_ofCode, mul4F_ofCode, h6])

theorem klein_mem {Hc : List ℕ} (hH : ∀ c ∈ Hc, c < 65536) {A : Finset Mat4}
    (hA : A ∈ kleinGroups (ms Hc)) : ∃ a ∈ Hc, ∃ b ∈ Hc, KleinC a b ∧ A = ms (kAc a b) := by
  simp only [kleinGroups, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hA
  obtain ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hk⟩, rfl⟩ := hA
  obtain ⟨a, ha, rfl⟩ := mem_ms.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_ms.1 hy
  exact ⟨a, ha, b, hb, kleinC_of (hH a ha) (hH b hb) hk, klein_eq a b⟩

theorem natFacts_of (hsc : SubspacesComplete) (hlt : ∀ s ∈ subspaceCodes, ∀ x ∈ s, x < 16)
    {Hc Ac : List ℕ} (hA : ∀ c ∈ Ac, c < 65536) (h : NatC Hc Ac (commL Ac V16)) :
    NatFacts (ms Hc) (ms Ac) (commSet (ms Ac) Finset.univ) := by
  have hF : ∀ x ∈ commL Ac V16, ColC x := commL_col V16_col
  have eF : commSet (ms Ac) Finset.univ = vs (commL Ac V16) := by rw [univ_eq, commSet_eq]
  unfold NatFacts NatSpan NatLattice
  rw [eF]
  obtain ⟨hs, hfix, hone, hlat, hoff⟩ := h
  obtain ⟨h0, hadd, hcard⟩ := span_of hF hs
  refine ⟨⟨h0, hadd, hcard, by rw [fixSet_eq, vs_eq_of hfix], ?_⟩, ?_, ?_⟩
  · intro g hg hne v hv
    obtain ⟨a, ha, rfl⟩ := mem_ms.1 hg
    obtain ⟨x, hx, rfl⟩ := vc_surj v
    exact (vc_mem_vs hF (V16_col x hx)).2 (hone a ha (fun e => hne (by rw [e, ofCode_id4])) x hx
      ((fix_iff' a (V16_col x hx)).2 hv))
  · rw [normSet_eq, invSub_eq hsc hlt hlat, univ_eq]
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, vs_zero,
      LawfulSingleton.insert_empty_eq]
  · intro A' hA' hmul hof
    obtain ⟨S, hS, rfl⟩ := sub_ms (Finset.mem_powerset.1 hA')
    have hSl : ∀ c ∈ S, c < 65536 := fun c hc => hA c ((List.mem_sublists.1 hS).subset hc)
    exact ms_eq_of (hoff S hS (mulC_of hSl hmul) (offC_of hSl hof))

theorem orthFacts_of (hsc : SubspacesComplete) (hlt : ∀ s ∈ subspaceCodes, ∀ x ∈ s, x < 16)
    {Hc Ac : List ℕ} (hA : ∀ c ∈ Ac, c < 65536)
    (h : OrthC Hc Ac (commL Ac V16) (commL Ac (commL Ac V16))) :
    OrthFacts (ms Hc) (ms Ac) (commSet (ms Ac) Finset.univ)
      (commSet (ms Ac) (commSet (ms Ac) Finset.univ)) := by
  have hF2 : ∀ x ∈ commL Ac V16, ColC x := commL_col V16_col
  have hF1 : ∀ x ∈ commL Ac (commL Ac V16), ColC x := commL_col hF2
  have e2 : commSet (ms Ac) Finset.univ = vs (commL Ac V16) := by rw [univ_eq, commSet_eq]
  unfold OrthFacts OrthSpan OrthLattice
  rw [e2, commSet_eq]
  obtain ⟨hs2, hs1, hfix, hlat, hd, hoff⟩ := h
  obtain ⟨a0, a1, a2⟩ := span_of hF2 hs2
  obtain ⟨b0, b1, b2⟩ := span_of hF1 hs1
  refine ⟨⟨a0, a1, a2, b0, b1, b2, by rw [fixSet_eq, vs_eq_of hfix]⟩, ?_, ?_, ?_⟩
  · rw [normSet_eq, invSub_eq hsc hlt hlat, univ_eq]
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, vs_zero,
      LawfulSingleton.insert_empty_eq]
  · intro g hg hne h3 f hf hf1
    rw [normSet_eq] at hg
    obtain ⟨d, hd', rfl⟩ := mem_ms.1 hg
    obtain ⟨x, hx, rfl⟩ := mem_vs.1 hf
    have hxc := hF2 x hx
    have h3' : mul4F (mul4F d d) d = id4 :=
      (ofCode_eq_one (mul4F_lt _ _)).1 (by rw [mul4F_ofCode, mul4F_ofCode, h3])
    rw [← vc_comm, vc_mem_vs hF1 (xor_col hxc (mul_col d hxc))] at hf1
    exact (vc_mem_vs hF1 hxc).2
      (hd d hd' (fun e => hne (by rw [e, ofCode_id4])) h3' x hx hf1)
  · intro A' hA' hmul hof
    obtain ⟨S, hS, rfl⟩ := sub_ms (Finset.mem_powerset.1 hA')
    have hSl : ∀ c ∈ S, c < 65536 := fun c hc => hA c ((List.mem_sublists.1 hS).subset hc)
    exact hoff S hS (mulC_of hSl hmul) (offC_of hSl hof)

end CFSG.KC.Misc.GL4

end
