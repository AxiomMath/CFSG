module

public import CFSG.Certificates.Kernel.M3BFib.WordSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBLocal
public import Certificates.Data.Kernel.M3BFib.FibRoot
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFibre

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.M3BF

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open CFSG.Monster.Generated
open Timmesfeld.M3B (WT B0 LA adOf sigW fT fLam fpt unpack nPts fRootV repD tD nfD eOf AD vget aget)

theorem goodPD_of_goodPDb {D : PD} (h : goodPDb D = true) : GoodPD D := by
  unfold goodPDb at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, fun r hr => h.1.2 r hr, h.2⟩

theorem eq_of_pdEq {D D' : PD} (h : pdEq D D' = true) : D = D' := by
  unfold pdEq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)

@[expose] noncomputable def encW (w : Fin 12 → ZMod 3) : ℕ := enc (List.ofFn fun j => (w j).val)

theorem encW_spec (w : Fin 12 → ZMod 3) : GoodRow (encW w) ∧ vz (encW w) = w := by
  have hl : (List.ofFn fun j => (w j).val).length = 12 := List.length_ofFn
  have h3 : ∀ d ∈ List.ofFn (fun j => (w j).val), d < 3 := by
    intro d hd
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hd
    exact ZMod.val_lt (w j)
  refine ⟨goodRow_enc hl h3, funext fun k => ?_⟩
  rw [encW, vz_enc hl h3, List.getD_eq_getElem _ _ (by rw [hl]; exact k.isLt), List.getElem_ofFn]
  exact ZMod.natCast_zmod_val (w k)

@[expose] noncomputable def affV (M : AffK) (w : Fin 12 → ZMod 3) : Fin 12 → ZMod 3 :=
  fun i => vz M.2 i + ∑ j : Fin 12, w j * vz (M.1.getD j 0) i

@[expose] def GoodAff (M : AffK) : Prop := M.1.length = 12 ∧ (∀ r ∈ M.1, GoodRow r) ∧ GoodRow M.2

theorem vz_applyK {M : AffK} (hM : GoodAff M) (p : ℕ) : vz (applyK M p) = affV M (vz p) := by
  obtain ⟨hl, hg, hq⟩ := hM
  set u := dig3 p with hu
  have hul : u.length = 12 := dig3_length p
  have hu3 : ∀ a ∈ u, a < 3 := dig3_lt p
  obtain ⟨hd1, hd2⟩ := dig_vm u M.1 hul hu3 hl hg
  have hvl : (vmD u (M.1.map dig3)).length = 12 := by rw [← hd1, dig_length]
  have hsum : Nat.add (vm u M.1) M.2 =
      enc (List.zipWith (fun x y => 1 * x + y) (dig3 M.2) (vmD u (M.1.map dig3))) := by
    rw [← enc_zipWith 1 _ _ (by rw [dig3_length, hvl]), hq, ← vm_eq u M.1 hg, Nat.add_eq,
      one_mul, Nat.add_comm]
  have hzl : (List.zipWith (fun x y => 1 * x + y) (dig3 M.2) (vmD u (M.1.map dig3))).length = 12 := by
    rw [List.length_zipWith, dig3_length, hvl, min_self]
  have hz : ∀ k < 12, (List.zipWith (fun x y => 1 * x + y) (dig3 M.2)
      (vmD u (M.1.map dig3))).getD k 0 =
      1 * (dig3 M.2).getD k 0 + ∑ j : Fin 12, u.getD j 0 * (dig3 (M.1.getD j 0)).getD k 0 := by
    intro k hk
    rw [getD_zipWith _ _ _ _ (by rw [dig3_length]; exact hk) (by rw [hvl]; exact hk), hd2 k hk]
  have hlt : ∀ d ∈ List.zipWith (fun x y => 1 * x + y) (dig3 M.2) (vmD u (M.1.map dig3)), d < 64 := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have hk12 : k < 12 := by rwa [hzl] at hk
    rw [← List.getD_eq_getElem _ 0 hk, hz k hk12]
    have hb : ∀ j : Fin 12, u.getD j 0 * (dig3 (M.1.getD j 0)).getD k 0 ≤ 4 := by
      intro j
      have h1 : u.getD j 0 < 3 := getD_mem_lt hu3 (by norm_num) _
      have h2 : (dig3 (M.1.getD j 0)).getD k 0 < 3 := getD_mem_lt (dig3_lt _) (by norm_num) _
      have : u.getD j 0 ≤ 2 := by omega
      have : (dig3 (M.1.getD j 0)).getD k 0 ≤ 2 := by omega
      calc _ ≤ 2 * 2 := Nat.mul_le_mul ‹_› ‹_›
        _ = 4 := rfl
    have hs : ∑ j : Fin 12, u.getD j 0 * (dig3 (M.1.getD j 0)).getD k 0 ≤ ∑ _j : Fin 12, 4 :=
      Finset.sum_le_sum fun j _ => hb j
    have h3 : (dig3 M.2).getD k 0 < 3 := getD_mem_lt (dig3_lt _) (by norm_num) _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
    omega
  funext k
  rw [applyK, vz_red, hsum, vz, dig3_getD _ k.isLt, dig_enc hzl hlt, hz k k.isLt, cast_mod3, affV]
  push_cast
  rw [one_mul]
  rfl

theorem f13S_zipWith_lt {f : ℕ → ℕ → ℕ} (hf : ∀ a b, f a b < 3) :
    ∀ (l l' : List ℕ), ∀ x ∈ List.zipWith f l l', x < 3
  | [], _, x, hx => by simp at hx
  | _ :: _, [], x, hx => by simp at hx
  | a :: l, b :: l', x, hx => by
    rw [List.zipWith_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf a b
    · exact f13S_zipWith_lt hf l l' x hx

theorem f13S_enc_map_mul (c : ℕ) : ∀ ds : List ℕ, Nat.mul c (enc ds) = enc (ds.map (c * ·))
  | [] => Nat.mul_zero c
  | d :: ds => by
    rw [List.map_cons, enc_cons, enc_cons, ← f13S_enc_map_mul c ds]
    change c * (d + 64 * enc ds) = c * d + 64 * (c * enc ds)
    ring

theorem f13S_vz_enc64 {ds : List ℕ} (hl : ds.length = 12) (h : ∀ d ∈ ds, d < 64) (k : Fin 12) :
    vz (enc ds) k = ((ds.getD k 0 : ℕ) : ZMod 3) := by
  rw [vz, dig3_getD _ k.isLt, dig_enc hl h, cast_mod3]

theorem conjOK_spec {T G Gi : PD} {M : AffK} (hT : GoodPD T) (hG : GoodPD G) (hGi : GoodPD Gi)
    (hlG : G.2.2 < 3) (h : conjOK LpM T G Gi M = true) :
    (img0K LpM T G Gi).1 = T.1 ∧ (img0K LpM T G Gi).2.2 = T.2.2 ∧ GoodAff M ∧
      (∀ j i : Fin 12, vz (M.1.getD j 0) i = (G.2.2 : ZMod 3) * vz (Gi.1.getD i 0) j) ∧
      ∀ i : Fin 12, vz M.2 i = (((img0K LpM T G Gi).2.1.getD i 0 : ℕ) : ZMod 3) := by
  have hI : GoodPD (img0K LpM T G Gi) :=
    (compK_sound lpM_ok (compK_sound lpM_ok hGi
      (⟨hT.1, hT.2.1, List.length_replicate⟩ : GoodPD (pt0 T))).1 hG).1
  have h3 : ∀ d ∈ (img0K LpM T G Gi).2.1, d < 3 := by
    obtain ⟨f, A, B, e, hf⟩ : ∃ (f : ℕ → ℕ → ℕ) (A B : List ℕ),
        (img0K LpM T G Gi).2.1 = List.zipWith f A B ∧ ∀ a b, f a b < 3 :=
      ⟨_, _, _, rfl, fun _ _ => Nat.mod_lt _ (by norm_num)⟩
    rw [e]
    exact f13S_zipWith_lt hf A B
  unfold conjOK at h
  beta_reduce at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, rfl⟩ := h
  have hd3 : ∀ q ∈ Gi.1.map dig3, q.length = 12 := by
    intro q hq
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 hq
    exact dig3_length r
  have hlen : (affA G Gi).length = 12 := by
    unfold affA
    rw [List.length_map, colsK_length _ hd3]
  refine ⟨h1, h2, ⟨hlen, fun r hr => ?_, goodRow_enc hI.2.2 h3⟩, fun j i => ?_,
    fun i => vz_enc hI.2.2 h3 i⟩
  · unfold affA at hr
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hr
    exact goodRow_red _
  · have hj : (j : ℕ) < (colsK (Gi.1.map dig3)).length := by
      rw [colsK_length _ hd3]
      exact j.isLt
    change vz (((colsK (Gi.1.map dig3)).map fun col => red (Nat.mul G.2.2 col)).getD j 0) i = _
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map, vz_red,
      ← List.getD_eq_getElem _ 0 hj, colsK_getD _ hd3 j j.isLt, f13S_enc_map_mul]
    have hGl : Gi.1.length = 12 := hGi.1
    have hi : (i : ℕ) < Gi.1.length := by
      rw [hGl]
      exact i.isLt
    rw [f13S_vz_enc64 (by simp [hGl]) ?_ i]
    · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_map,
        List.getElem_map, ← List.getD_eq_getElem _ 0 hi, Nat.cast_mul, vz_dig3]
    · intro d hd
      simp only [List.map_map, List.mem_map, Function.comp] at hd
      obtain ⟨r, _, rfl⟩ := hd
      have hr3 : (dig3 r).getD j 0 < 3 := by
        rw [List.getD_eq_getElem _ _ (by rw [dig3_length]; exact j.isLt)]
        exact dig3_lt r _ (List.getElem_mem _)
      have : G.2.2 * (dig3 r).getD j 0 ≤ 2 * 2 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega

theorem f13S_enc_ofFn : ∀ (n : ℕ) (f : Fin n → ℕ), enc (List.ofFn f) = ∑ k : Fin n, f k * 64 ^ (k : ℕ)
  | 0, f => by
    rw [List.ofFn_zero, Finset.univ_eq_empty, Finset.sum_empty]
    rfl
  | n + 1, f => by
    rw [List.ofFn_succ, enc_cons, f13S_enc_ofFn n, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem f13S_goodRow_sum {r : ℕ} (h : GoodRow r) :
    r = ∑ k : Fin 12, (dig3 r).getD k 0 * 64 ^ (k : ℕ) := by
  have e := f13S_enc_ofFn 12 (fun k : Fin 12 => (dig3 r).getD k 0)
  rw [← e]
  conv_lhs => rw [← h]
  refine congrArg enc (List.ext_getElem (by rw [dig3_length, List.length_ofFn]) fun i h1 _ => ?_)
  rw [List.getElem_ofFn]
  exact (List.getD_eq_getElem _ _ h1).symm

theorem f13S_vz_sum {L : Fin 12 → ℕ} (h : ∀ k, L k < 64) (k : Fin 12) :
    vz (∑ k : Fin 12, L k * 64 ^ (k : ℕ)) k = (L k : ZMod 3) := by
  rw [← f13S_enc_ofFn 12 L, f13S_vz_enc64 List.length_ofFn ?_ k]
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.isLt), List.getElem_ofFn]
  · intro d hd
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hd
    exact h j

theorem f13S_digN_getD : ∀ (n x p : ℕ), p < n → (digN n x).getD p 0 = x / 64 ^ p % 64
  | 0, _, _, hp => absurd hp (Nat.not_lt_zero _)
  | n + 1, x, 0, _ => by
    rw [digN_succ]
    simp
  | n + 1, x, p + 1, hp => by
    rw [digN_succ, List.getD_cons_succ, f13S_digN_getD n (x / 64) p (by omega),
      Nat.div_div_eq_div_mul, pow_succ']

theorem f13S_lane_eq {r : ℕ} (h : GoodRow r) {p : ℕ} (hp : p < 12) :
    lane r p = (dig3 r).getD p 0 := by
  rw [← h.dig_eq]
  exact (f13S_digN_getD 12 r p hp).symm

theorem f13S_enc_lt : ∀ ds : List ℕ, (∀ d ∈ ds, d < 64) → enc ds < 64 ^ ds.length
  | [], _ => Nat.one_pos
  | d :: ds, h => by
    have h1 := h d List.mem_cons_self
    have h2 := f13S_enc_lt ds fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    rw [enc_cons, List.length_cons, pow_succ]
    omega

theorem f13S_lane_big {r : ℕ} (h : GoodRow r) {p : ℕ} (hp : 12 ≤ p) : lane r p = 0 := by
  have hlt : r < 64 ^ p := by
    have e := f13S_enc_lt (dig3 r) fun d hd => lt_trans (dig3_lt r d hd) (by norm_num)
    rw [h, dig3_length] at e
    exact lt_of_lt_of_le e (Nat.pow_le_pow_right (by norm_num) hp)
  change r / 64 ^ p % 64 = 0
  rw [Nat.div_eq_of_lt hlt]

theorem f13S_cnt (j : ℕ) : ∀ l : List ℕ, cnt j l = l.count j
  | [] => by
    rw [List.count_nil]
    rfl
  | a :: l => by
    change (bif a == j then Nat.succ (cnt j l) else cnt j l) = _
    rw [List.count_cons, f13S_cnt j l]
    by_cases h : a = j <;> simp [h]

theorem f13S_sum_piv (g : BasK → ℕ) {b : BasK} : ∀ l : List BasK, (l.map Prod.fst).Nodup → b ∈ l →
    (l.map fun b' => g b' * if b.1 = b'.1 then 1 else 0).sum = g b
  | [], _, hb => absurd hb List.not_mem_nil
  | a :: l, hn, hb => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hb with e | hb
    · rw [← e] at hn ⊢
      have hz : (l.map fun b' => g b' * if b.1 = b'.1 then 1 else 0).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hx
        have hne : b.1 ≠ b'.1 := fun e' => hn.1 (by rw [e']; exact List.mem_map.2 ⟨b', hb', rfl⟩)
        rw [if_neg hne, mul_zero]
      rw [hz, if_pos rfl, mul_one, add_zero]
    · have hne : b.1 ≠ a.1 := fun e' => hn.1 (by rw [← e']; exact List.mem_map.2 ⟨b, hb, rfl⟩)
      rw [if_neg hne, mul_zero, zero_add, f13S_sum_piv g l hn.2 hb]

theorem f13S_fold (c : ℕ) (hc : GoodRow c) : ∀ bs : List BasK, (∀ b ∈ bs, GoodRow b.2.1) →
    List.rec (motive := fun _ => ℕ) c
      (fun b _ acc => Nat.add acc (Nat.mul (Nat.mod (Nat.sub 3 (lane c b.1)) 3) b.2.1)) bs =
    ∑ k : Fin 12, ((dig3 c).getD k 0 +
      (bs.map fun b => (3 - lane c b.1) % 3 * (dig3 b.2.1).getD k 0).sum) * 64 ^ (k : ℕ)
  | [], _ => by
    simp only [List.map_nil, List.sum_nil, add_zero]
    exact f13S_goodRow_sum hc
  | b :: bs, hb => by
    have ih := f13S_fold c hc bs fun b' h' => hb b' (List.mem_cons_of_mem _ h')
    have hg := f13S_goodRow_sum (hb b List.mem_cons_self)
    change List.rec (motive := fun _ => ℕ) c
      (fun b _ acc => Nat.add acc (Nat.mul (Nat.mod (Nat.sub 3 (lane c b.1)) 3) b.2.1)) bs +
      (3 - lane c b.1) % 3 * b.2.1 = _
    rw [ih]
    conv_lhs => rw [hg]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [List.map_cons, List.sum_cons]
    ring

theorem f13S_sum_swap {β : Type} (l : List β) (x : β → ZMod 3) (y : β → Fin 12 → ZMod 3)
    (v : Fin 12 → ZMod 3) :
    (l.map fun b => x b * ∑ j, y b j * v j).sum = ∑ j, (l.map fun b => x b * y b j).sum * v j := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc]

theorem f13S_ptQ (w : Fin 12 → ZMod 3) : ∀ fr : List ℕ, fr.Nodup → (∀ f ∈ fr, f < 12) →
    ∃ i < 3 ^ fr.length,
      ptQ fr i = ∑ k : Fin 12, (if (k : ℕ) ∈ fr then (w k).val else 0) * 64 ^ (k : ℕ)
  | [], _, _ => ⟨0, by norm_num, by simp [ptQ]⟩
  | f :: fr, hn, h12 => by
    rw [List.nodup_cons] at hn
    have hf : f < 12 := h12 f List.mem_cons_self
    obtain ⟨i', hi', e⟩ := f13S_ptQ w fr hn.2 fun g hg => h12 g (List.mem_cons_of_mem _ hg)
    have hv : (w ⟨f, hf⟩).val < 3 := ZMod.val_lt _
    refine ⟨(w ⟨f, hf⟩).val + 3 * i', ?_, ?_⟩
    · rw [List.length_cons, pow_succ]
      omega
    · change ((w ⟨f, hf⟩).val + 3 * i') % 3 * 64 ^ f + ptQ fr (((w ⟨f, hf⟩).val + 3 * i') / 3) = _
      have e1 : ((w ⟨f, hf⟩).val + 3 * i') % 3 = (w ⟨f, hf⟩).val := by omega
      have e2 : ((w ⟨f, hf⟩).val + 3 * i') / 3 = i' := by omega
      rw [e1, e2, e]
      have hk : ∀ k : Fin 12, (if (k : ℕ) ∈ f :: fr then (w k).val else 0) * 64 ^ (k : ℕ) =
          (if k = ⟨f, hf⟩ then (w ⟨f, hf⟩).val * 64 ^ f else 0) +
            (if (k : ℕ) ∈ fr then (w k).val else 0) * 64 ^ (k : ℕ) := by
        intro k
        by_cases hkf : k = ⟨f, hf⟩
        · subst hkf
          simp [hn.1]
        · have hne : (k : ℕ) ≠ f := fun e' => hkf (Fin.ext e')
          simp [hne, hkf]
      rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp

theorem basisChk_spec {ms : List AffK} {bs : List BasK} {fr : List ℕ}
    (h : basisChk ms bs fr = true) (hd : ∀ j < 12, GoodRow ((transK ms).getD j 0)) :
    (∀ j < 12, (ms.getD (2 * j) ([], 0)).1 = idRows) ∧
    (∀ c, GoodRow c → ∃ a : Fin 12 → ZMod 3,
      vz (redW bs c) = vz c + ∑ j : Fin 12, a j • vz ((transK ms).getD j 0)) ∧
    ∀ c, GoodRow c → ∃ i < 3 ^ fr.length, vz (ptQ fr i) = vz (redW bs c) := by
  unfold basisChk at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, Nat.blt_eq,
    cond_eq_if] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hbg : ∀ b ∈ bs, GoodRow b.2.1 := fun b hb => by
    rw [(h4 b hb).1.2]
    exact goodRow_red _
  have hp12 : ∀ b ∈ bs, b.1 < 12 := by
    intro b hb
    by_contra hc
    have e := (h4 b hb).2 b hb
    rw [if_pos rfl, f13S_lane_big (hbg b hb) (by omega)] at e
    exact absurd e (by decide)
  have hcnt : ∀ j < 12, fr.count j + (bs.map Prod.fst).count j = 1 := fun j hj => by
    rw [← f13S_cnt, ← f13S_cnt]
    exact h2 j hj
  have hpn : (bs.map Prod.fst).Nodup := by
    refine List.nodup_iff_count_le_one.2 fun a => ?_
    by_cases ha : a < 12
    · have := hcnt a ha
      omega
    · rw [List.count_eq_zero.2 fun hm => ?_]
      · omega
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hm
      exact ha (hp12 b hb)
  have hfn : fr.Nodup := by
    refine List.nodup_iff_count_le_one.2 fun a => ?_
    by_cases ha : a < 12
    · have := hcnt a ha
      omega
    · rw [List.count_eq_zero.2 fun hm => ha (h3 a hm)]
      omega
  have hlen : bs.length ≤ 12 := by
    have h' := List.toFinset_card_of_nodup hpn
    rw [List.length_map] at h'
    rw [← h']
    calc _ ≤ (Finset.range 12).card := Finset.card_le_card fun a ha => by
            rw [List.mem_toFinset] at ha
            obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
            exact Finset.mem_range.2 (hp12 b hb)
      _ = 12 := Finset.card_range 12
  have hdl : (transK ms).length = 12 := by
    unfold transK
    rw [List.length_map, List.length_range]
  have hdg : ∀ p ∈ transK ms, GoodRow p := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    rw [← List.getD_eq_getElem _ 0 hj]
    exact hd j (by rwa [hdl] at hj)
  have hvb : ∀ b ∈ bs, ∀ k : Fin 12,
      vz b.2.1 k = ∑ j : Fin 12, (b.2.2.getD j 0 : ZMod 3) * vz ((transK ms).getD j 0) k := by
    intro b hb k
    obtain ⟨⟨⟨hl, he⟩, hv⟩, -⟩ := h4 b hb
    rw [hv, vz_red]
    exact vz_vm _ _ hl he hdl hdg k
  have hL : ∀ c, GoodRow c → ∀ k : Fin 12,
      (dig3 c).getD k 0 + (bs.map fun b => (3 - lane c b.1) % 3 * (dig3 b.2.1).getD k 0).sum < 64 := by
    intro c hc k
    have e1 : (dig3 c).getD k 0 < 3 := getD_mem_lt (dig3_lt c) (by norm_num) _
    have e2 : (bs.map fun b => (3 - lane c b.1) % 3 * (dig3 b.2.1).getD k 0).sum ≤
        (bs.map fun b => (3 - lane c b.1) % 3 * (dig3 b.2.1).getD k 0).length • 4 := by
      refine List.sum_le_card_nsmul _ _ fun x hx => ?_
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
      have e3 : (3 - lane c b.1) % 3 ≤ 2 := by omega
      have e4 : (dig3 b.2.1).getD k 0 ≤ 2 := by
        have := getD_mem_lt (dig3_lt b.2.1) (by norm_num : 0 < 3) k
        omega
      calc _ ≤ 2 * 2 := Nat.mul_le_mul e3 e4
        _ = 4 := rfl
    rw [List.length_map, smul_eq_mul] at e2
    omega
  have hR : ∀ c, GoodRow c → ∀ k : Fin 12, vz (redW bs c) k =
      (((dig3 c).getD k 0 + (bs.map fun b => (3 - lane c b.1) % 3 * (dig3 b.2.1).getD k 0).sum : ℕ) :
        ZMod 3) := by
    intro c hc k
    have e : redW bs c = red (∑ k : Fin 12, ((dig3 c).getD k 0 +
        (bs.map fun b => (3 - lane c b.1) % 3 * (dig3 b.2.1).getD k 0).sum) * 64 ^ (k : ℕ)) :=
      congrArg red (f13S_fold c hc bs hbg)
    rw [e, vz_red]
    exact f13S_vz_sum (hL c hc) k
  refine ⟨fun j hj => h1 j hj, fun c hc => ?_, fun c hc => ?_⟩
  · refine ⟨fun j => (bs.map fun b => (((3 - lane c b.1) % 3 : ℕ) : ZMod 3) *
      (b.2.2.getD j 0 : ZMod 3)).sum, ?_⟩
    funext k
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hR c hc k, Nat.cast_add, Nat.cast_list_sum, List.map_map, vz_dig3]
    refine congrArg (vz c k + ·) ?_
    refine Eq.trans ?_ (f13S_sum_swap bs (fun b => (((3 - lane c b.1) % 3 : ℕ) : ZMod 3))
      (fun b j => (b.2.2.getD j 0 : ZMod 3)) (fun j => vz ((transK ms).getD j 0) k))
    refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
    simp only [Function.comp_apply, Nat.cast_mul]
    rw [vz_dig3, hvb b hb k]
  · have hpiv : ∀ b ∈ bs, ∀ hb12 : b.1 < 12, vz (redW bs c) ⟨b.1, hb12⟩ = 0 := by
      intro b hb hb12
      rw [hR c hc ⟨b.1, hb12⟩]
      have hs : (bs.map fun b' => (3 - lane c b'.1) % 3 * (dig3 b'.2.1).getD b.1 0).sum =
          (3 - lane c b.1) % 3 := by
        refine Eq.trans ?_ (f13S_sum_piv (fun b' => (3 - lane c b'.1) % 3) bs hpn hb)
        refine congrArg List.sum (List.map_congr_left fun b' hb' => ?_)
        beta_reduce
        rw [← f13S_lane_eq (hbg b' hb') hb12, (h4 b' hb').2 b hb]
      have hl3 : lane c b.1 < 3 := by
        rw [f13S_lane_eq hc hb12]
        exact getD_mem_lt (dig3_lt c) (by norm_num) _
      simp only [Fin.val_mk]
      rw [hs, ← f13S_lane_eq hc hb12, ← cast_mod3]
      have e : (lane c b.1 + (3 - lane c b.1) % 3) % 3 = 0 := by omega
      rw [e, Nat.cast_zero]
    obtain ⟨i, hi, hiq⟩ := f13S_ptQ (vz (redW bs c)) fr hfn h3
    refine ⟨i, hi, ?_⟩
    have h64 : ∀ k : Fin 12, (if (k : ℕ) ∈ fr then (vz (redW bs c) k).val else 0) < 64 := by
      intro k
      split_ifs
      · exact lt_trans (ZMod.val_lt _) (by norm_num)
      · norm_num
    funext k
    rw [hiq, f13S_vz_sum h64 k]
    by_cases hk : (k : ℕ) ∈ fr
    · rw [if_pos hk, ZMod.natCast_zmod_val]
    · rw [if_neg hk, Nat.cast_zero]
      have hc1 := hcnt k k.isLt
      rw [List.count_eq_zero.2 hk, zero_add] at hc1
      obtain ⟨b, hb, hbk⟩ := List.mem_map.1
        (List.count_pos_iff.1 (by omega : 0 < (bs.map Prod.fst).count (k : ℕ)))
      have ek : k = ⟨b.1, hp12 b hb⟩ := Fin.ext hbk.symm
      rw [ek]
      exact (hpiv b hb (hp12 b hb)).symm

theorem f13S_bit (m i : ℕ) : bit m i = m.testBit i := by
  have e : m.testBit i = (m >>> i).testBit 0 := by rw [Nat.testBit_shiftRight, Nat.add_zero]
  rw [e, Nat.testBit_zero, Nat.shiftRight_eq_div_pow]
  unfold bit
  change (m / 2 ^ i % 2 == 1) = _
  cases h : (m / 2 ^ i % 2 == 1)
  · exact (decide_eq_false fun h' => by rw [beq_iff_eq.2 h'] at h; exact Bool.noConfusion h).symm
  · exact (decide_eq_true (beq_iff_eq.1 h)).symm

theorem f13S_testBit_lor_pow (m q i : ℕ) :
    (Nat.lor m (Nat.pow 2 q)).testBit i = true ↔ m.testBit i = true ∨ q = i := by
  change (m ||| 2 ^ q).testBit i = true ↔ _
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_iff]

theorem f13S_rootMask (rs : List (ℕ × ℕ)) (i : ℕ) :
    (rootMask rs).testBit i = true → ∃ r ∈ rs, r.2 = i := by
  induction rs with
  | nil => intro h; rw [rootMask, Nat.zero_testBit] at h; exact absurd h Bool.false_ne_true
  | cons r rs ih =>
    intro h
    change (Nat.lor (rootMask rs) (Nat.pow 2 r.2)).testBit i = true at h
    rcases (f13S_testBit_lor_pow _ _ _).1 h with h | h
    · obtain ⟨r', hr', e⟩ := ih h
      exact ⟨r', List.mem_cons_of_mem _ hr', e⟩
    · exact ⟨r, List.mem_cons_self, h⟩

theorem f13S_rowsK {ms : List AffK} {bs : List BasK} {fr : List ℕ} {n : ℕ} {P : ℕ → Prop}
    (hstep : ∀ i j m, m < ms.length → redW bs (applyK (ms.getD m ([], 0)) (ptQ fr i)) = ptQ fr j →
      P j → P i) :
    ∀ (rows : List (ℕ × ℕ × ℕ)) (m M : ℕ), (∀ i, m.testBit i = true → P i) →
      rowsK ms bs fr n rows m = some M → ∀ i, M.testBit i = true → P i
  | [], m, M, hm, h => by
    change some m = some M at h
    cases h
    exact hm
  | r :: rows, m, M, hm, h => by
    unfold rowsK at h
    dsimp only at h
    rw [cond_eq_if] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, f13S_bit] at hc
    obtain ⟨⟨⟨-, hb⟩, hlen⟩, he⟩ := hc
    have hr : P r.1 := hstep _ _ _ hlen he (hm _ hb)
    refine f13S_rowsK hstep rows (Nat.lor m (Nat.pow 2 r.1)) M ?_ h
    intro i hi
    rcases (f13S_testBit_lor_pow _ _ _).1 hi with hi | rfl
    · exact hm i hi
    · exact hr

theorem forestChk_spec {ms : List AffK} {bs : List BasK} {fr : List ℕ} {rs : List (ℕ × ℕ)}
    {rows : List (ℕ × ℕ × ℕ)} (h : forestChk ms bs fr rs rows = true) :
    (∀ r ∈ rs, GoodRow r.1 ∧ redW bs r.1 = ptQ fr r.2) ∧
    ∀ P : ℕ → Prop, (∀ r ∈ rs, P r.2) →
      (∀ i j m, m < ms.length → redW bs (applyK (ms.getD m ([], 0)) (ptQ fr i)) = ptQ fr j →
        P j → P i) →
      ∀ i < 3 ^ fr.length, P i := by
  unfold forestChk at h
  beta_reduce at h
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hr, hrows⟩ := h
  refine ⟨fun r hr' => ?_, fun P hP hstep i hi => ?_⟩
  · have := hr r hr'
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1.2, this.2⟩
  · refine f13S_rowsK hstep rows _ _ ?_ hrows i ?_
    · intro i hi
      obtain ⟨r, hr', rfl⟩ := f13S_rootMask rs i hi
      exact hP r hr'
    · change (2 ^ 3 ^ fr.length - 1).testBit i = true
      rw [Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
      exact hi

theorem transK_getD (ms : List AffK) {j : ℕ} (hj : j < 12) :
    (transK ms).getD j 0 = (ms.getD (2 * j) ([], 0)).2 := by
  unfold transK
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  rfl

theorem getD_finRange_map {α : Type} (f : Fin 12 → α) (d : α) (i : Fin 12) :
    ((List.finRange 12).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
  rfl

theorem pdOf_spec (D : AD) : GoodPD (pdOf D) ∧ dK (pdOf D) = toD D := by
  have hl : ∀ i : Fin 12, ((List.finRange 12).map fun j => (vget (aget D i).1 j).val).length = 12 :=
    fun i => by simp
  have h3 : ∀ i : Fin 12, ∀ d ∈ (List.finRange 12).map (fun j => (vget (aget D i).1 j).val), d < 3 := by
    intro i d hd
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hd
    exact (vget (aget D i).1 j).isLt
  refine ⟨⟨by simp [pdOf], fun r hr => ?_, by simp [pdOf]⟩, ?_⟩
  · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
    exact goodRow_enc (hl i) (h3 i)
  · have L1 : ∀ i j, ((dK (pdOf D)).1 i).1 j = vz ((pdOf D).1.getD i 0) j := fun _ _ => rfl
    have L2 : ∀ i, ((dK (pdOf D)).1 i).2 = (((pdOf D).2.1.getD i 0 : ℕ) : ZMod 3) := fun _ => rfl
    have L3 : (dK (pdOf D)).2 = ((D.2.val : ℕ) : ZMod 3) := rfl
    have R1 : ∀ i j, ((toD D).1 i).1 j =
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.toZ (vget (aget D i).1 j) :=
      fun _ _ => rfl
    have R2 : ∀ i, ((toD D).1 i).2 =
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.toZ (aget D i).2 := fun _ => rfl
    have R3 : (toD D).2 = CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.toZ D.2 := rfl
    have P1 : ∀ i : Fin 12, (pdOf D).1.getD i 0 =
        enc ((List.finRange 12).map fun j => (vget (aget D i).1 j).val) := fun i =>
      getD_finRange_map (fun i => enc ((List.finRange 12).map fun j => (vget (aget D i).1 j).val)) 0 i
    have P2 : ∀ i : Fin 12, (pdOf D).2.1.getD i 0 = (aget D i).2.val := fun i =>
      getD_finRange_map (fun i => (aget D i).2.val) 0 i
    refine Prod.ext (funext fun i => Prod.ext (funext fun j => ?_) ?_) ?_
    · rw [L1, R1, P1, vz_enc (hl i) (h3 i), getD_finRange_map]
      exact ZMod.natCast_zmod_val (n := 3) (vget (aget D i).1 j)
    · rw [L2, R2, P2]
      exact ZMod.natCast_zmod_val (n := 3) (aget D i).2
    · rw [L3, R3]
      exact ZMod.natCast_zmod_val (n := 3) D.2

section Fibre

theorem dK_oneK : dK oneK = idD 12 := by rw [one_sound.2, toD_adOne]

@[expose] def FibAct (T : PD) (y : Gmat) (w : Fin 12 → ZMod 3) : Prop :=
  IsAct tbSys y (fptM (fun i => ((dK T).1 i).1) (dK T).2 w)

theorem dK_pt0 (T : PD) : dK (pt0 T) = fptM (fun i => ((dK T).1 i).1) (dK T).2 0 := by
  refine Prod.ext (funext fun i => Prod.ext rfl ?_) rfl
  have e : ((dK (pt0 T)).1 i).2 = (((List.replicate 12 0).getD i 0 : ℕ) : ZMod 3) := rfl
  rw [e, List.getD_replicate]
  · rfl
  · exact i.isLt

theorem goodPD_pt0 {T : PD} (hT : GoodPD T) : GoodPD (pt0 T) :=
  ⟨hT.1, hT.2.1, List.length_replicate⟩

theorem fibAct_conj {T G Gi : PD} {M : AffK} {g y : Gmat} {w : Fin 12 → ZMod 3}
    (hT : GoodPD T) (hG : GoodPD G) (hGi : GoodPD Gi) (hlG : G.2.2 < 3)
    (hgG : IsAct tbSys g (dK G)) (hgGi : IsAct tbSys g⁻¹ (dK Gi))
    (hok : conjOK LpM T G Gi M = true) (hy : FibAct T y w) :
    FibAct T (g⁻¹ * y * g) (affV M w) := by
  obtain ⟨hI1, hI2, -, hM1, hM2⟩ := conjOK_spec hT hG hGi hlG hok
  have h1 := (hgGi.mul tbSys_good hy).mul tbSys_good hgG
  obtain ⟨hA, eA⟩ := compK_sound lpM_ok hGi (goodPD_pt0 hT)
  obtain ⟨-, eI⟩ := compK_sound lpM_ok hA hG
  have hD0 : comp tbSys.B (comp tbSys.B (dK Gi) (fptM (fun i => ((dK T).1 i).1) (dK T).2 0))
      (dK G) = dK (img0K LpM T G Gi) := by
    rw [tbSys_B, ← dK_pt0, ← eA, ← eI]
    rfl
  rw [comp_fptM tbSys.B _ _ (dK G) (dK Gi) (fun i => by
      rw [hD0]
      change vz ((img0K LpM T G Gi).1.getD i 0) = vz (T.1.getD i 0)
      rw [hI1]) (by
      rw [hD0]
      change (((img0K LpM T G Gi).2.2 : ℕ) : ZMod 3) = ((T.2.2 : ℕ) : ZMod 3)
      rw [hI2])] at h1
  unfold FibAct
  convert h1 using 2
  funext i
  rw [affV, hM2 i, hD0]
  change _ = (((img0K LpM T G Gi).2.1.getD i 0 : ℕ) : ZMod 3) +
    ((G.2.2 : ℕ) : ZMod 3) * ∑ j, vz (Gi.1.getD i 0) j * w j
  rw [Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [hM1]
  ring

@[expose] def Reach (T : PD) (w w' : Fin 12 → ZMod 3) : Prop :=
  ∀ y, FibAct T y w → ∃ h ∈ tbL, FibAct T (h⁻¹ * y * h) w'

theorem Reach.refl (T : PD) (w : Fin 12 → ZMod 3) : Reach T w w :=
  fun y hy => ⟨1, tbL.one_mem, by simpa using hy⟩

theorem Reach.trans {T : PD} {w w' w'' : Fin 12 → ZMod 3} (h1 : Reach T w w')
    (h2 : Reach T w' w'') : Reach T w w'' := by
  intro y hy
  obtain ⟨a, ha, hya⟩ := h1 y hy
  obtain ⟨b, hb, hyb⟩ := h2 _ hya
  refine ⟨a * b, tbL.mul_mem ha hb, ?_⟩
  have e : (a * b)⁻¹ * y * (a * b) = b⁻¹ * (a⁻¹ * y * a) * b := by group
  rw [e]
  exact hyb

theorem reach_smul {T : PD} {d : Fin 12 → ZMod 3} {g : Gmat} (hg : g ∈ tbL)
    (hmv : ∀ y w, FibAct T y w → FibAct T (g⁻¹ * y * g) (w + d)) (w : Fin 12 → ZMod 3) :
    ∀ a : ZMod 3, Reach T w (w + a • d) := by
  have hn : ∀ n : ℕ, Reach T w (w + n • d) := by
    intro n
    induction n with
    | zero => simpa using Reach.refl T w
    | succ n ih =>
      refine ih.trans fun y hy => ⟨g, hg, ?_⟩
      have e : w + (n + 1) • d = w + n • d + d := by rw [succ_nsmul, add_assoc]
      rw [e]
      exact hmv y _ hy
  intro a
  have e : a • d = a.val • d := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [e]
  exact hn a.val

theorem reach_span {T : PD} {d : Fin 12 → Fin 12 → ZMod 3}
    (hd : ∀ j, ∃ g ∈ tbL, ∀ y w, FibAct T y w → FibAct T (g⁻¹ * y * g) (w + d j))
    (w : Fin 12 → ZMod 3) (a : Fin 12 → ZMod 3) : Reach T w (w + ∑ j, a j • d j) := by
  suffices h : ∀ s : Finset (Fin 12), Reach T w (w + ∑ j ∈ s, a j • d j) from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using Reach.refl T w
  | insert j s hj ih =>
    obtain ⟨g, hg, hmv⟩ := hd j
    rw [Finset.sum_insert hj, add_comm (a j • d j), ← add_assoc]
    exact ih.trans (reach_smul hg hmv _ (a j))

@[expose] def GenOK (T : PD) (g : GenK) : Prop :=
  g.2.1 = adOfK LpM LK (slpWT g.1) ∧ goodPDb g.2.2.1 = true ∧
    pdEq (compK LpM g.2.2.1 g.2.1) oneK = true ∧ conjOK LpM T g.2.1 g.2.2.1 g.2.2.2.1 = true ∧
    conjOK LpM T g.2.2.1 g.2.1 g.2.2.2.2 = true ∧ g.2.1.2.2 < 3 ∧ g.2.2.1.2.2 < 3

theorem genOK_of_checks {T : PD} {gs : List GenK} {lk : List PD} (hlk : LK = lk) (hw : wordChk LpM lk gs = true)
    (hg : genChk LpM T gs = true) (hl : lamChk gs = true) : ∀ g ∈ gs, GenOK T g := by
  induction gs with
  | nil => intro g hg; exact absurd hg List.not_mem_nil
  | cons g gs ih =>
    change (pdEq (adOfK LpM lk (slpWT g.1)) g.2.1 && wordChk LpM lk gs) = true at hw
    change (genOne LpM T g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 && genChk LpM T gs) = true at hg
    unfold lamChk at hl
    simp only [List.all_cons, Bool.and_eq_true] at hw hg hl
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · unfold genOne at hg
      simp only [Bool.and_eq_true] at hg
      refine ⟨by rw [hlk]; exact (eq_of_pdEq hw.1).symm, hg.1.1.1.1, hg.1.1.1.2, hg.1.1.2, hg.1.2,
        by simpa [Nat.blt_eq] using hl.1.1, by simpa [Nat.blt_eq] using hl.1.2⟩
    · exact ih hw.2 hg.2 (by unfold lamChk; simpa using hl.2) g' hg'

theorem genOK_moves (hinv : letterInvCheck () = true) {T : PD} (hT : GoodPD T) {g : GenK}
    (h : GenOK T g) :
    GoodAff g.2.2.2.1 ∧ GoodAff g.2.2.2.2 ∧
      (∃ x ∈ tbL, ∀ y w, FibAct T y w → FibAct T (x⁻¹ * y * x) (affV g.2.2.2.1 w)) ∧
      (∃ x ∈ tbL, ∀ y w, FibAct T y w → FibAct T (x⁻¹ * y * x) (affV g.2.2.2.2 w)) := by
  obtain ⟨hG, hGib, hc, hok, hok', hl, hl'⟩ := h
  have hGi := goodPD_of_goodPDb hGib
  obtain ⟨hGg, hGd⟩ := adOfK_sound (slpWT g.1)
  rw [← hG] at hGg hGd
  have hx : IsAct tbSys (evalG letterG (slpWT g.1)) (dK g.2.1) := by
    rw [hGd]
    exact isAct_evalG hinv _
  have hxi : IsAct tbSys (evalG letterG (slpWT g.1))⁻¹ (dK g.2.2.1) := by
    refine hx.inv_of_comp tbSys_good ?_
    rw [tbSys_B, ← (compK_sound lpM_ok hGi hGg).2, eq_of_pdEq hc, dK_oneK]
  have hmem := tbL_mem_evalG (slpWT g.1)
  refine ⟨(conjOK_spec hT hGg hGi hl hok).2.2.1, (conjOK_spec hT hGi hGg hl' hok').2.2.1,
    ⟨_, hmem, fun y w hy => fibAct_conj hT hGg hGi hl hx hxi hok hy⟩,
    ⟨_, tbL.inv_mem hmem, fun y w hy => fibAct_conj hT hGi hGg hl' hxi (by rwa [inv_inv]) hok' hy⟩⟩

theorem maps_move (hinv : letterInvCheck () = true) {T : PD} (hT : GoodPD T) {gs : List GenK}
    (h : ∀ g ∈ gs, GenOK T g) : ∀ M ∈ mapsOf gs, GoodAff M ∧
      ∃ x ∈ tbL, ∀ y w, FibAct T y w → FibAct T (x⁻¹ * y * x) (affV M w) := by
  induction gs with
  | nil => intro M hM; exact absurd hM List.not_mem_nil
  | cons g gs ih =>
    intro M hM
    have hg := genOK_moves hinv hT (h g List.mem_cons_self)
    change M ∈ g.2.2.2.1 :: g.2.2.2.2 :: mapsOf gs at hM
    rcases List.mem_cons.1 hM with rfl | hM
    · exact ⟨hg.1, hg.2.2.1⟩
    rcases List.mem_cons.1 hM with rfl | hM
    · exact ⟨hg.2.1, hg.2.2.2⟩
    exact ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) M hM

theorem vz_idRows (j i : Fin 12) : vz (idRows.getD j 0) i = if j = i then 1 else 0 := by
  revert j i
  decide +kernel

theorem fibre_roots_of_checks (hinv : letterInvCheck () = true) {k : ℕ} (hk : k ≠ 0)
    {t : PD} {gs : List GenK} {bs : List BasK} {fr : List ℕ} {rs : List (ℕ × ℕ)}
    {rows : List (ℕ × ℕ × ℕ)} {lk : List PD} (hlk : LK = lk)
    (hsig : sigW[k - 1]! = sigW.getD (k - 1) (WT.gen 0))
    (ht : adOfK LpM lk (sigW.getD (k - 1) (WT.gen 0)) = t)
    (hw : wordChk LpM lk gs = true) (hg : genChk LpM t gs = true) (hl : lamChk gs = true)
    (hb : basisChk (mapsOf gs) bs fr = true) (hf : forestChk (mapsOf gs) bs fr rs rows = true)
    (hrc : rootVChk LpM t k rs = true) :
    ∀ p < nPts, ∀ x : Gmat, IsAct tbSys x (toD (fpt (fT k) (fLam k) (unpack p))) →
      ∃ g ∈ tbL, ∃ v ∈ fRootV k, IsAct tbSys (g⁻¹ * x * g) (toD (repD k v)) := by
  have htk : GoodPD t ∧ dK t = toD (tD k) := by
    rw [← ht, ← hlk, tD, hsig]
    exact adOfK_sound _
  obtain ⟨hT, hTd⟩ := htk
  set ms := mapsOf gs with hms
  have hgen := genOK_of_checks hlk hw hg hl
  have hmv := maps_move hinv hT hgen
  have hmvD : ∀ m, m < ms.length → GoodAff (ms.getD m ([], 0)) ∧
      ∃ x ∈ tbL, ∀ y w, FibAct t y w → FibAct t (x⁻¹ * y * x) (affV (ms.getD m ([], 0)) w) :=
    fun m hm => hmv _ (getD_mem hm)
  have hlen : ∀ j < 12, 2 * j < ms.length := by
    intro j hj
    by_contra hc
    have e := (basisChk_spec hb (fun j' hj' => by
      rw [transK_getD ms hj']
      by_cases h' : 2 * j' < ms.length
      · exact (hmvD _ h').1.2.2
      · rw [List.getD_eq_default _ _ (by omega)]
        rfl)).1 j hj
    rw [List.getD_eq_default _ _ (by omega)] at e
    exact absurd e (by decide)
  have hdgood : ∀ j < 12, GoodRow ((transK ms).getD j 0) := by
    intro j hj
    rw [transK_getD ms hj]
    exact (hmvD _ (hlen j hj)).1.2.2
  obtain ⟨hid, hred, hidx⟩ := basisChk_spec hb hdgood
  have htr : ∀ j : Fin 12, ∃ g ∈ tbL, ∀ y w, FibAct t y w →
      FibAct t (g⁻¹ * y * g) (w + vz ((transK ms).getD j 0)) := by
    intro j
    obtain ⟨-, x, hx, hxm⟩ := hmvD _ (hlen j j.isLt)
    refine ⟨x, hx, fun y w hy => ?_⟩
    have e : affV (ms.getD (2 * j) ([], 0)) w = w + vz ((transK ms).getD j 0) := by
      funext i
      rw [affV, hid j j.isLt, transK_getD ms j.isLt, Pi.add_apply]
      simp only [vz_idRows, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      ring
    rw [← e]
    exact hxm y w hy
  have hredR : ∀ c, GoodRow c → Reach t (vz c) (vz (redW bs c)) ∧ Reach t (vz (redW bs c)) (vz c) := by
    intro c hc
    obtain ⟨a, ha⟩ := hred c hc
    refine ⟨by rw [ha]; exact reach_span htr _ a, ?_⟩
    have e : vz c = vz (redW bs c) + ∑ j, (-a j) • vz ((transK ms).getD j 0) := by
      rw [ha]
      simp only [neg_smul, Finset.sum_neg_distrib]
      abel
    rw [e]
    exact reach_span htr _ _
  obtain ⟨hroots, hforest⟩ := forestChk_spec hf
  have hall := hforest (fun i => ∀ y, FibAct t y (vz (ptQ fr i)) →
      ∃ h ∈ tbL, ∃ r ∈ rs, FibAct t (h⁻¹ * y * h) (vz r.1))
    (fun r hr y hy => by
      obtain ⟨hg1, he⟩ := hroots r hr
      have hR := (hredR r.1 hg1).2
      rw [he] at hR
      obtain ⟨h, hh, hyh⟩ := hR y hy
      exact ⟨h, hh, r, hr, hyh⟩)
    (fun i j m hm he hj y hy => by
      obtain ⟨hgA, x, hx, hxm⟩ := hmvD m hm
      have h1 := hxm y _ hy
      rw [← vz_applyK hgA] at h1
      have hR' : Reach t (vz (applyK (ms.getD m ([], 0)) (ptQ fr i))) (vz (ptQ fr j)) := by
        have := (hredR (applyK (ms.getD m ([], 0)) (ptQ fr i)) (goodRow_red _)).1
        rwa [he] at this
      obtain ⟨h2, hh2, hy2⟩ := hR' _ h1
      obtain ⟨h3, hh3, r, hr, hy3⟩ := hj _ hy2
      refine ⟨x * h2 * h3, tbL.mul_mem (tbL.mul_mem hx hh2) hh3, r, hr, ?_⟩
      have e : (x * h2 * h3)⁻¹ * y * (x * h2 * h3) = h3⁻¹ * (h2⁻¹ * (x⁻¹ * y * x) * h2) * h3 := by
        group
      rw [e]
      exact hy3)
  intro p _ x hx
  have hfib : FibAct t x (vfun (unpack p)) := by
    unfold FibAct
    rw [toD_fpt] at hx
    convert hx using 2
    · funext i
      rw [hTd, fT, if_neg hk, toMat_adMat_row]
    · rw [hTd, fLam, if_neg hk]
      rfl
  obtain ⟨hcg, hcv⟩ := encW_spec (vfun (unpack p))
  rw [← hcv] at hfib
  obtain ⟨i, hi, hie⟩ := hidx _ hcg
  obtain ⟨h1, hh1, hy1⟩ := (hredR _ hcg).1 x hfib
  rw [← hie] at hy1
  obtain ⟨h2, hh2, r, hr, hy2⟩ := hall i hi _ hy1
  obtain ⟨v, hv, hvr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hrc r hr)
  obtain ⟨hNg, hNd⟩ := pdOf_spec (nfD (B0 ()) (eOf v 0))
  have e := (compK_sound lpM_ok hT hNg).2
  rw [eq_of_pdEq hvr, hTd, hNd, ← toD_comp] at e
  have hrep : repD k v = Timmesfeld.M3B.comp (B0 ()) (tD k) (nfD (B0 ()) (eOf v 0)) := by
    unfold repD
    exact if_neg hk
  refine ⟨h1 * h2, tbL.mul_mem hh1 hh2, v, hv, ?_⟩
  have e2 : (h1 * h2)⁻¹ * x * (h1 * h2) = h2⁻¹ * (h1⁻¹ * x * h1) * h2 := by group
  rw [e2, hrep, ← e]
  exact hy2

end Fibre

end CFSG.KC.M3BF

end
