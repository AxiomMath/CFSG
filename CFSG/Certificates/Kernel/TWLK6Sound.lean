module

public import CFSG.LocalAnalysis.StandardType.GGTWLowOutE6
public import Certificates.Data.Kernel.TWLK6

public section

namespace CFSG.StandardType.TWLK

open Certificates.TWLK Certificates.DepASmall Certificates.TwoDepSmall
open Certificates.TwoDepSmallLow CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem k6_toZ_refl {p d : ℕ} [Fact p.Prime] {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = d) (hq2 : q.2.length = d) (hv : v.length = d) :
    ggDepANToZ p d (ggTWNRefl p q v) =
      ggDepARefl (ggDepANToZ p d q.1) (ggDepANToZ p d q.2) (ggDepANToZ p d v) := by
  have hlen : (ggDepANSmul p (ggDepANDot p q.2 v) q.1).length = d := l05nNC_smul_length hq1
  change ggDepANToZ p d (ggDepANSub p v (ggDepANSmul p (ggDepANDot p q.2 v) q.1)) = _
  rw [l05nNC_toZ_sub hv hlen, l05nNC_toZ_smul hq1, ggDepANDot_cast q.2 v hq2 hv,
    l05nPT_refl_apply]

theorem k6_refl_length {p d : ℕ} {q : GGDepANPair} {v : List ℕ} (hq1 : q.1.length = d)
    (hv : v.length = d) : (ggTWNRefl p q v).length = d :=
  l05nNC_sub_length hv (l05nNC_smul_length hq1)

theorem k6_toZ_of_veceq {p d : ℕ} {a b : List ℕ} (h : ggTWLVecEq p a b = true) :
    ggDepANToZ p d a = ggDepANToZ p d b := by
  rw [ggTWLVecEq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  funext j
  simp only [ggDepANToZ]
  by_cases hj : j.val < a.length
  · have hjb : j.val < b.length := hlen ▸ hj
    have hz : j.val < (List.zipWith (fun x y => x % p == y % p) a b).length := by
      rw [List.length_zipWith, ← hlen, min_self]; exact hj
    have hm := hall _ (List.getElem_mem hz)
    rw [List.getElem_zipWith, id_eq, beq_iff_eq] at hm
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hjb]
    exact (ZMod.natCast_eq_natCast_iff' _ _ p).mpr hm
  · have hjb : ¬ j.val < b.length := hlen ▸ hj
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem k6_refl_neg {p d : ℕ} (c f : GGDepAE p d) : ggDepARefl (-c) (-f) = ggDepARefl c f := by
  apply LinearMap.ext
  intro v
  rw [l05nPT_refl_apply, l05nPT_refl_apply]
  have h : ggDepAdot (-f) v = -ggDepAdot f v := by
    simp [ggDepAdot, Finset.sum_neg_distrib]
  rw [h, neg_smul_neg]

theorem kPairEq_rfl {p N : ℕ} [Fact p.Prime] {q r : GGDepANPair} (h : kPairEq p q r = true) :
    ggTWNRflOf p N q = ggTWNRflOf p N r := by
  have hneg : ∀ a : List ℕ, ggDepANToZ p (N - 1) (ggDepANSmul p (p - 1) a) =
      -ggDepANToZ p (N - 1) a := by
    intro a
    funext j
    have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    simp only [ggDepANToZ, ggDepANSmul, Pi.neg_apply]
    by_cases hj : j.val < a.length
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
        List.getD_eq_getElem _ _ hj, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_sub hp,
        ZMod.natCast_self, Nat.cast_one]
      ring
    · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
        List.getD_eq_default _ _ (by omega)]
      simp
  simp only [kPairEq, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [ggTWNRflOf, ggTWNToZ]
    rw [k6_toZ_of_veceq h1, k6_toZ_of_veceq h2]
  · simp only [ggTWNRflOf, ggTWNToZ]
    rw [k6_toZ_of_veceq h1, k6_toZ_of_veceq h2, hneg, hneg]
    exact k6_refl_neg _ _

theorem k6_dot_of_valid {p N : ℕ} [Fact p.Prime] {q : GGDepANPair} (h : GGTWNValid p N q) :
    ggDepAdot (ggDepANToZ p (N - 1) q.2) (ggDepANToZ p (N - 1) q.1) = 2 := by
  rw [← ggDepANDot_cast q.2 q.1 h.2.1 h.1, h.2.2, ZMod.natCast_mod]
  norm_num

theorem k6_valid_of_dot {p N : ℕ} [Fact p.Prime] {q : GGDepANPair} (h1 : q.1.length = N - 1)
    (h2 : q.2.length = N - 1)
    (h : ggDepAdot (ggDepANToZ p (N - 1) q.2) (ggDepANToZ p (N - 1) q.1) = 2) :
    GGTWNValid p N q := by
  refine ⟨h1, h2, ?_⟩
  have hc := ggDepANDot_cast (p := p) q.2 q.1 h2 h1
  rw [h] at hc
  have h2' : ((ggDepANDot p q.2 q.1 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) := by
    rw [hc]; norm_num
  rw [ZMod.natCast_eq_natCast_iff'] at h2'
  simpa [ggDepANDot, Nat.mod_mod] using h2'

theorem kEWord_valid_mem {p N : ℕ} [Fact p.Prime] {e : List GGDepANPair}
    {S : Submonoid (Module.End (ZMod p) (GGTWE p N))}
    (he : ∀ q ∈ e, GGTWNValid p N q ∧ ggTWNRflOf p N q ∈ S) :
    ∀ (u : List ℕ), (∀ k ∈ u, k < e.length) → ∀ q : GGDepANPair, GGTWNValid p N q →
      ggTWNRflOf p N q ∈ S →
      GGTWNValid p N (kEWord p e q u) ∧ ggTWNRflOf p N (kEWord p e q u) ∈ S := by
  intro u
  induction u with
  | nil => intro _ q hq hqS; exact ⟨hq, hqS⟩
  | cons k u ih =>
    intro hu q hq hqS
    have hk : k < e.length := hu k List.mem_cons_self
    obtain ⟨ihV, ihS⟩ := ih (fun k' hk' => hu k' (List.mem_cons_of_mem k hk')) q hq hqS
    have hgm : e.getD k ([], []) ∈ e := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    obtain ⟨hG, hGS⟩ := he _ hgm
    have hcons : kEWord p e q (k :: u) = ggDepANConj p (kEWord p e q u) (e.getD k ([], [])) := by
      simp [kEWord]
    rw [hcons]
    set Q := kEWord p e q u
    set g := e.getD k ([], [])
    have hdq := k6_dot_of_valid ihV
    have hdg := k6_dot_of_valid hG
    have hlen := l05nNC_conj_length (p := p) ihV.1 ihV.2.1 hG.1 hG.2.1
    obtain ⟨hc1, hc2⟩ := l05nNC_toZ_conj (p := p) ihV.1 ihV.2.1 hG.1 hG.2.1
    refine ⟨k6_valid_of_dot hlen.1 hlen.2 ?_, ?_⟩
    · rw [hc1, hc2]
      exact l05nNC_conj_dot _ _ _ _ hdq hdg
    · simp only [ggTWNRflOf, ggTWRefl, ggTWNToZ]
      rw [hc1, hc2, ← l05nNC_refl_conj _ _ _ _ hdg]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hGS ihS) hGS

noncomputable def kFrameEnd (p N : ℕ) (w : List ℕ) : Module.End (ZMod p) (GGTWE p N) :=
  (w.map fun g => ggTWNRflOf p N (ggTWNH p N g, ggTWNA p N g)).prod

theorem kFrameEnd_mem {p N : ℕ} [Fact p.Prime] {w : List ℕ} (hw : ∀ g ∈ w, g + 1 < N) :
    kFrameEnd p N w ∈ Submonoid.closure (ggTWFrameGens p N) := by
  refine Submonoid.list_prod_mem _ ?_
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  have hg' : g < N - 1 := by have := hw g hg; omega
  refine Submonoid.subset_closure ⟨⟨g, hg'⟩, ?_⟩
  simp only [ggTWNRflOf]
  rw [ggTWNH_toZ ⟨g, hg'⟩, ggTWNA_toZ ⟨g, hg'⟩]

theorem kFrameEnd_apply {p N : ℕ} [Fact p.Prime] (w : List ℕ) {v : List ℕ}
    (hv : v.length = N - 1) :
    (ggTWNApply p N w v).length = N - 1 ∧
      ggTWNToZ p N (ggTWNApply p N w v) = kFrameEnd p N w (ggTWNToZ p N v) := by
  induction w with
  | nil => exact ⟨hv, by simp [ggTWNApply, kFrameEnd]⟩
  | cons g w ih =>
    obtain ⟨ihl, ihv⟩ := ih
    have hstep : ggTWNApply p N (g :: w) v =
        ggTWNRefl p (ggTWNH p N g, ggTWNA p N g) (ggTWNApply p N w v) := by
      simp [ggTWNApply]
    rw [hstep]
    refine ⟨k6_refl_length (ggTWNH_length p N g) ihl, ?_⟩
    rw [ggTWNToZ, k6_toZ_refl (ggTWNH_length p N g) (ggTWNA_length p N g) ihl]
    simp only [kFrameEnd, List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [kFrameEnd] at ihv
    rw [← ihv]

theorem k6_mod_of_toZ {p n : ℕ} {u v : List ℕ} (hu : u.length = n) (hv : v.length = n)
    (h : ggDepANToZ p n u = ggDepANToZ p n v) : u.map (· % p) = v.map (· % p) := by
  apply List.ext_getElem (by simp [hu, hv])
  intro i h1 h2
  have hiu : i < u.length := by simpa using h1
  have hiv : i < v.length := by simpa using h2
  have hc := congrFun h ⟨i, hu ▸ hiu⟩
  simp only [ggDepANToZ] at hc
  rw [List.getD_eq_getElem _ _ hiu, List.getD_eq_getElem _ _ hiv] at hc
  simp only [List.getElem_map]
  exact (ZMod.natCast_eq_natCast_iff' _ _ p).mp hc

theorem kVKey_mod (p : ℕ) (L : List (List ℕ)) :
    kVKey p L = kVKey p (L.map (List.map (· % p))) := by
  unfold kVKey
  rw [List.foldl_map]
  congr 1
  funext k v
  rw [List.foldl_map]
  simp only [Nat.mod_mod]

theorem kIncr_pairwise : ∀ l : List ℕ, kIncr l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [kIncr, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := kIncr_pairwise (b :: l) h.2
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem kFrameOK_sound {p N : ℕ} [Fact p.Prime] {vs ws : List (List ℕ)}
    (h : kFrameOK p N vs ws = true) :
    720 ≤ Nat.card ↥(Submonoid.closure (ggTWFrameGens p N)) := by
  simp only [kFrameOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hlen, hvs⟩, hws⟩, hinc⟩ := h
  have hpw := kIncr_pairwise _ hinc
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : Finite (Module.End (ZMod p) (GGTWE p N)) :=
    Finite.of_injective (fun f : Module.End (ZMod p) (GGTWE p N) => (f : GGTWE p N → GGTWE p N))
      (fun a b hab => LinearMap.ext (congrFun hab))
  let F : Fin 720 → Submonoid.closure (ggTWFrameGens p N) := fun k =>
    ⟨kFrameEnd p N (ws[k.val]'(by rw [hlen]; exact k.isLt)),
      kFrameEnd_mem (hws _ (List.getElem_mem _))⟩
  have hkey : ∀ (i j : ℕ) (hi : i < ws.length) (hj : j < ws.length),
      kFrameEnd p N ws[i] = kFrameEnd p N ws[j] →
      kVKey p (vs.map (ggTWNApply p N ws[i])) = kVKey p (vs.map (ggTWNApply p N ws[j])) := by
    intro i j hi hj heq
    rw [kVKey_mod, kVKey_mod p (vs.map _), List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro v hv
    have hvl := hvs v hv
    obtain ⟨hl1, he1⟩ := kFrameEnd_apply (p := p) ws[i] hvl
    obtain ⟨hl2, he2⟩ := kFrameEnd_apply (p := p) ws[j] hvl
    exact k6_mod_of_toZ hl1 hl2 (by rw [ggTWNToZ] at he1 he2; rw [he1, he2, heq])
  have hF : Function.Injective F := by
    intro i j hij
    have heq : kFrameEnd p N (ws[i.val]'(by rw [hlen]; exact i.isLt)) =
        kFrameEnd p N (ws[j.val]'(by rw [hlen]; exact j.isLt)) := congrArg Subtype.val hij
    have hk := hkey i.val j.val _ _ heq
    by_contra hne
    have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hil : i.val < (ws.map fun w => kVKey p (vs.map (ggTWNApply p N w))).length := by
      rw [List.length_map, hlen]; exact i.isLt
    have hjl : j.val < (ws.map fun w => kVKey p (vs.map (ggTWNApply p N w))).length := by
      rw [List.length_map, hlen]; exact j.isLt
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
    · have := List.pairwise_iff_getElem.mp hpw i.val j.val hil hjl hlt
      simp only [List.getElem_map] at this
      omega
    · have := List.pairwise_iff_getElem.mp hpw j.val i.val hjl hil hgt
      simp only [List.getElem_map] at this
      omega
  have hle := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_fin] at hle

theorem kE6Test_sound {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid 3 6 q)
    {vs ws : List (List ℕ)} (hf : kFrameOK 3 6 vs ws = true) (w : KE6)
    (h : kE6Test 3 6 news w = true) :
    GGTWLowE6Outcome (ggTWGens 3 6 (ggTWNNews 3 6 news)) := by
  obtain ⟨s0, gw, sw, ot⟩ := w
  simp only [kE6Test, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc, beq_iff_eq] at h
  obtain ⟨hsl, hgl, hswl, hotl, hsV, hotV, hgw, hsw, hcox, hpar, hnodup⟩ := h
  set Sg := ggTWGens 3 6 (ggTWNNews 3 6 news) with hSg
  set V : List (List ℕ) := ggTWLOrbitPts 3 6 news ot with hV
  let s : Fin 6 → Module.End (ZMod 3) (GGTWE 3 6) := fun i => ggTWNRflOf 3 6 (s0.getD i.val ([], []))
  have hs_getD (k : ℕ) (hk : k < s0.length) : s0.getD k ([], []) ∈ s0 := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hs_valq : ∀ q ∈ s0, GGTWNValid 3 6 q := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hsV q hq
    exact ⟨h1, h2, by simpa [ggDepANDot, Nat.mod_mod] using h3⟩
  have hs_val (i : Fin 6) : GGTWNValid 3 6 (s0.getD i.val ([], [])) :=
    hs_valq _ (hs_getD i.val (by rw [hsl]; exact i.isLt))
  have hs_refl : ∀ i, GGTWIsRefl (s i) := fun i =>
    ⟨_, _, l05nL6_dot_of_valid (hs_val i), rfl⟩
  have hgen_valid : ∀ g, g < 6 - 1 + news.length → GGTWNValid 3 6 (ggTWNGen 3 6 news g) :=
    fun g hg => ggTWNGen_valid (p := 3) (N := 6) (by norm_num) (by norm_num) hnews hg
  have hs_mem : ∀ i, s i ∈ Submonoid.closure Sg := by
    intro i
    obtain ⟨hu1, hu2, hpe⟩ := hsw i.val i.isLt
    have hword := ggTWNWord_valid_mem (p := 3) (N := 6) (by norm_num) (by norm_num) hnews
      (hgen_valid _ (by omega))
      (ggTWNGen_mem (p := 3) (N := 6) (by norm_num) (by norm_num) (by omega))
      (fun g hg => by have := hu2 g hg; omega)
    change ggTWNRflOf 3 6 (s0.getD i.val ([], [])) ∈ _
    rw [← kPairEq_rfl hpe]
    exact hword.2
  have hS_mem : ∀ g, g < 6 - 1 + news.length →
      ggTWNRflOf 3 6 (ggTWNGen 3 6 news g) ∈ Submonoid.closure (Set.range s) := by
    intro g hg
    obtain ⟨hu1, hu2, hpe⟩ := hgw g (by omega)
    have he : ∀ q ∈ s0, GGTWNValid 3 6 q ∧
        ggTWNRflOf 3 6 q ∈ Submonoid.closure (Set.range s) := by
      intro q hq
      refine ⟨hs_valq q hq, ?_⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
      refine Submonoid.subset_closure ⟨⟨k, by rw [← hsl]; exact hk⟩, ?_⟩
      change ggTWNRflOf 3 6 (s0.getD k ([], [])) = _
      rw [List.getD_eq_getElem _ _ hk]
    have hstart := hs_getD _ (by rw [hsl]; exact hu1)
    have hw := kEWord_valid_mem he _ (fun k hk => by rw [hsl]; exact hu2 k hk) _
      (hs_valq _ hstart) (he _ hstart).2
    rw [← kPairEq_rfl hpe]
    exact hw.2
  have hgen_lin : ∀ x ∈ Sg, x ∈ Submonoid.closure (Set.range s) := by
    intro x hx
    rw [hSg, ggTWGens] at hx
    rcases hx with hx | hx
    · obtain ⟨i, rfl⟩ := hx
      have hiv : i.val + 1 < 6 := by have := i.isLt; omega
      have hgen : ggTWNGen 3 6 news i.val = (ggTWNH 3 6 i.val, ggTWNA 3 6 i.val) := by
        simp only [ggTWNGen, if_pos hiv]
      have h1 := hS_mem i.val (by have := i.isLt; omega)
      rw [hgen] at h1
      simp only [ggTWNRflOf] at h1
      rwa [ggTWNH_toZ, ggTWNA_toZ] at h1
    · obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := ht
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
      have hgen : ggTWNGen 3 6 news (5 + k) = news[k] := by
        rw [ggTWNGen, if_neg (by omega), show 5 + k + 1 - 6 = k by omega,
          List.getD_eq_getElem _ _ hk]
      have h1 := hS_mem (5 + k) (by omega)
      rw [hgen] at h1
      exact h1
  have hclosure : Submonoid.closure (Set.range s) = Submonoid.closure Sg := by
    refine le_antisymm ?_ ?_
    · rw [Submonoid.closure_le]
      rintro x ⟨i, rfl⟩
      exact hs_mem i
    · rw [Submonoid.closure_le]
      exact hgen_lin
  have hTs (i : Fin 6) : (List.map (ggTWLMatOfPair 3 (6 - 1)) s0).getD i.val [] =
      ggTWLMatOfPair 3 (6 - 1) (s0.getD i.val ([], [])) := by
    have hi : i.val < s0.length := by rw [hsl]; exact i.isLt
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi),
      List.getD_eq_getElem _ _ hi, List.getElem_map]
  have hcoxrel : ∀ i j : Fin 6, (s i * s j) ^ (CoxeterMatrix.E₆.M i j) = 1 := by
    intro i j
    have hA := (ggTWLMatOfPair_lin (hs_val i)).1
    have hB := (ggTWLMatOfPair_lin (hs_val j)).1
    obtain ⟨hAB, hmul⟩ := ggTWLMatMul_lin (p := 3) (d := 5) hA hB
    obtain ⟨hP, hpow⟩ := ggTWLMatPow_lin (p := 3) (d := 5) hAB (ggTWLE6M i.val j.val)
    obtain ⟨hOne, hOneLin⟩ := ggTWLMatOne_lin (p := 3) (d := 5)
    have hc := hcox i.val i.isLt j.val j.isLt
    rw [hTs i, hTs j] at hc
    have heq := (ggTWLMatEq_iff hP hOne).mp hc
    have hmain : (s i * s j) ^ (ggTWLE6M i.val j.val) = 1 := by
      calc (s i * s j) ^ (ggTWLE6M i.val j.val)
          = (ggTWLMatLin 3 5 (ggTWLMatOfPair 3 5 (s0.getD i.val ([], []))) *
              ggTWLMatLin 3 5 (ggTWLMatOfPair 3 5 (s0.getD j.val ([], [])))) ^
                (ggTWLE6M i.val j.val) := by
            rw [(ggTWLMatOfPair_lin (hs_val i)).2, (ggTWLMatOfPair_lin (hs_val j)).2]
        _ = (ggTWLMatLin 3 5 (ggTWLMatMul 3 5 (ggTWLMatOfPair 3 5 (s0.getD i.val ([], [])))
              (ggTWLMatOfPair 3 5 (s0.getD j.val ([], []))))) ^ (ggTWLE6M i.val j.val) := by
            rw [hmul]
        _ = ggTWLMatLin 3 5 (ggTWLMatPow 3 5
              (ggTWLMatMul 3 5 (ggTWLMatOfPair 3 5 (s0.getD i.val ([], [])))
                (ggTWLMatOfPair 3 5 (s0.getD j.val ([], [])))) (ggTWLE6M i.val j.val)) :=
            hpow.symm
        _ = ggTWLMatLin 3 5 (ggTWLMatOne 5) := heq
        _ = 1 := hOneLin
    rwa [l05nL6_e6M i j] at hmain
  have : Finite (Module.End (ZMod 3) (GGTWE 3 6)) :=
    Finite.of_injective (fun f : Module.End (ZMod 3) (GGTWE 3 6) => (f : GGTWE 3 6 → GGTWE 3 6))
      (fun a b hab => LinearMap.ext (congrFun hab))
  have hframe_card : 720 ≤ Nat.card (Submonoid.closure (ggTWFrameGens 3 6)) :=
    kFrameOK_sound hf
  have hFfix : ∀ f ∈ Submonoid.closure (ggTWFrameGens 3 6), f (ggTWx 3 6) = ggTWx 3 6 := by
    intro f hf
    induction hf using Submonoid.closure_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact l05nL6_frame_gen_fixes i
    | one => rfl
    | mul x y _ _ ihx ihy => rw [Module.End.mul_apply, ihy, ihx]
  have hFle : Submonoid.closure (ggTWFrameGens 3 6) ≤ Submonoid.closure Sg := by
    rw [Submonoid.closure_le]
    intro x hx
    exact Submonoid.subset_closure (Or.inl hx)
  have hsim := l05nL6_sim_orbit hnews ot hpar
    (by
      intro j hj
      exact hotV (ot.getD j (0, 0)) (by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _))
  obtain ⟨hVlen, hVptlen, hVapply, hVmem⟩ := hsim
  have hfoldlen : ∀ (L0 : List (List ℕ)) (l : List (Nat × Nat)),
      (l.foldl (fun L e => L ++ [ggTWNRefl 3 (ggTWNGen 3 6 news e.2) (L.getD e.1 [])]) L0).length
        = l.length + L0.length := by
    intro L0 l
    induction l generalizing L0 with
    | nil => simp
    | cons e l ih =>
        rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
        omega
  have hVlen72 : V.length = 72 := by
    rw [hV, ggTWLOrbitPts, hfoldlen, hotl]
    norm_num
  let Gf : Fin 72 → Module.End (ZMod 3) (GGTWE 3 6) :=
    fun k => (l05nL6_endFold news ot).getD k.val 1
  have hGfapply (k : Fin 72) : Gf k (ggTWx 3 6) = ggTWNToZ 3 6 (V.getD k.val []) := by
    have hk : k.val < (ggTWLOrbitPts 3 6 news ot).length := by rw [← hV, hVlen72]; exact k.isLt
    exact hVapply k.val hk
  have hGfmem (k : Fin 72) : Gf k ∈ Submonoid.closure Sg :=
    hVmem k.val (by rw [hVlen, ← hV, hVlen72]; exact k.isLt)
  have hGfptlen (k : Fin 72) : (V.getD k.val []).length = 5 :=
    hVptlen k.val (by rw [← hV, hVlen72]; exact k.isLt)
  have hinv : ∀ g ∈ Submonoid.closure Sg, ∃ h ∈ Submonoid.closure Sg, h * g = 1 :=
    l05nL6_closure_inv (l05nL6_S_invol hnews)
  have hdistinct : ∀ i j : Fin 72, i ≠ j → ggTWNToZ 3 6 (V.getD i.val []) ≠
      ggTWNToZ 3 6 (V.getD j.val []) := by
    intro i j hij htoZ
    have hnod : ggTWLNodup 3 (List.map (fun v => [v]) V) = true := hnodup
    have hi : i.val < V.length := by rw [hVlen72]; exact i.isLt
    have hj : j.val < V.length := by rw [hVlen72]; exact j.isLt
    have key : ∀ a b : Fin 72, a.val < b.val →
        ggTWNToZ 3 6 (V.getD a.val []) = ggTWNToZ 3 6 (V.getD b.val []) → False := by
      intro a b hab hab'
      have ha : a.val < V.length := by rw [hVlen72]; exact a.isLt
      have hb : b.val < V.length := by rw [hVlen72]; exact b.isLt
      have hveq : ggTWLVecEq 3 (V.getD a.val []) (V.getD b.val []) = true :=
        l05nL6_veceq_of_toZ (hGfptlen a) (hGfptlen b) hab'
      have hmat : ggTWLMatEq 3 [V.getD a.val []] [V.getD b.val []] = true := by
        simpa [ggTWLMatEq] using hveq
      have h := l05nL6_nodup_getD hnod a.val b.val hab (by rw [List.length_map]; exact hb)
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact ha), List.getElem_map,
        List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hb), List.getElem_map,
        ← List.getD_eq_getElem V [] ha, ← List.getD_eq_getElem V [] hb] at h
      rw [h] at hmat
      exact Bool.false_ne_true hmat
    rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with hlt | hgt
    · exact key i j hlt htoZ
    · exact key j i hgt htoZ.symm
  let φ : (Submonoid.closure (ggTWFrameGens 3 6)) × Fin 72 → Submonoid.closure Sg := fun x =>
    ⟨Gf x.2 * (x.1 : Module.End (ZMod 3) (GGTWE 3 6)),
      Submonoid.mul_mem _ (hGfmem x.2) (hFle x.1.2)⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨f1, k1⟩ ⟨f2, k2⟩ heq
    have hx : Gf k1 (ggTWx 3 6) = Gf k2 (ggTWx 3 6) := by
      have h := congrArg (fun z : Submonoid.closure Sg =>
        (z : Module.End (ZMod 3) (GGTWE 3 6)) (ggTWx 3 6)) heq
      simpa only [φ, Module.End.mul_apply, hFfix f1 f1.2, hFfix f2 f2.2] using h
    have hk : k1 = k2 := by
      by_contra hne
      exact hdistinct k1 k2 hne (by rw [← hGfapply k1, ← hGfapply k2]; exact hx)
    subst hk
    obtain ⟨h, _, hhg⟩ := hinv (Gf k1) (hGfmem k1)
    have hfe : (f1 : Module.End (ZMod 3) (GGTWE 3 6)) = f2 := by
      have h2 : Gf k1 * (f1 : Module.End (ZMod 3) (GGTWE 3 6)) =
          Gf k1 * (f2 : Module.End (ZMod 3) (GGTWE 3 6)) := by
        simpa only [φ] using congrArg
          (fun z : Submonoid.closure Sg => (z : Module.End (ZMod 3) (GGTWE 3 6))) heq
      have h3 := congrArg (fun z : Module.End (ZMod 3) (GGTWE 3 6) => h * z) h2
      rwa [← mul_assoc, hhg, one_mul, ← mul_assoc, hhg, one_mul] at h3
    exact Prod.ext (Subtype.ext hfe) rfl
  have hcard : 51840 ≤ Nat.card (Submonoid.closure Sg) := by
    have hle := Nat.card_le_card_of_injective φ hφinj
    rw [Nat.card_prod, Nat.card_fin] at hle
    calc 51840 = 720 * 72 := by norm_num
      _ ≤ Nat.card (Submonoid.closure (ggTWFrameGens 3 6)) * 72 :=
          Nat.mul_le_mul_right 72 hframe_card
      _ ≤ Nat.card (Submonoid.closure Sg) := hle
  exact ⟨hcard, s, hs_refl, hclosure, hcoxrel⟩

end CFSG.StandardType.TWLK

end
