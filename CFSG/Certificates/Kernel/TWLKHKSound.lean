module

public import Certificates.Data.Kernel.TWLK
public import CFSG.LocalAnalysis.StandardType.GGTWNatLine

public section

namespace CFSG.StandardType.TWLK

open Certificates.TWLK Certificates.TwoDepSmall Certificates.DepASmall
open Certificates.TwoDepSmallLow CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma kHK_cast_sub (p : ℕ) [Fact p.Prime] (x y : ℕ) :
    (((x + (p - y % p)) % p : ℕ) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (Nat.mod_lt y hp)),
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

private lemma kHK_sub_length {p N : ℕ} {a b : List ℕ} (ha : a.length = N) (hb : b.length = N) :
    (ggDepANSub p a b).length = N := by
  simp only [ggDepANSub, List.length_zipWith, ha, hb, min_self]

private lemma kHK_smul_length {p N k : ℕ} {a : List ℕ} (ha : a.length = N) :
    (ggDepANSmul p k a).length = N := by
  simp only [ggDepANSmul, List.length_map, ha]

private lemma kHK_add_length {p N : ℕ} {a b : List ℕ} (ha : a.length = N) (hb : b.length = N) :
    (ggTWNAdd p a b).length = N := by
  simp only [ggTWNAdd, List.length_zipWith, ha, hb, min_self]

private lemma kHK_refl_length {p N : ℕ} {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = N) (hv : v.length = N) :
    (ggTWNRefl p q v).length = N := by
  rw [ggTWNRefl]
  exact kHK_sub_length hv (kHK_smul_length hq1)

private lemma kHK_toZ_sub {p N : ℕ} [Fact p.Prime] {a b : List ℕ} (ha : a.length = N)
    (hb : b.length = N) :
    ggDepANToZ p N (ggDepANSub p a b) = ggDepANToZ p N a - ggDepANToZ p N b := by
  funext j
  have hj : j.val < N := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjb : j.val < b.length := by rw [hb]; exact hj
  have hjl : j.val < (a.zipWith (fun x y => (x + (p - y % p)) % p) b).length := by
    rw [List.length_zipWith, ha, hb, min_self]; exact hj
  simp only [ggDepANToZ, ggDepANSub, Pi.sub_apply]
  rw [List.getD_eq_getElem (l := a.zipWith _ b) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja,
    List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hjb]
  rw [List.getElem_zipWith]
  exact kHK_cast_sub p _ _

private lemma kHK_toZ_smul {p N : ℕ} [Fact p.Prime] {a : List ℕ} (ha : a.length = N)
    (k : ℕ) :
    ggDepANToZ p N (ggDepANSmul p k a) = (k : ZMod p) • ggDepANToZ p N a := by
  funext j
  have hj : j.val < N := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjl : j.val < (a.map (fun x => k * x % p)).length := by
    rw [List.length_map, ha]; exact hj
  simp only [ggDepANToZ, ggDepANSmul, Pi.smul_apply, smul_eq_mul]
  rw [List.getD_eq_getElem (l := a.map _) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja]
  rw [List.getElem_map, ZMod.natCast_mod, Nat.cast_mul]

private lemma kHK_toZ_add {p N : ℕ} [Fact p.Prime] {a b : List ℕ} (ha : a.length = N)
    (hb : b.length = N) :
    ggDepANToZ p N (ggTWNAdd p a b) = ggDepANToZ p N a + ggDepANToZ p N b := by
  funext j
  have hj : j.val < N := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjb : j.val < b.length := by rw [hb]; exact hj
  have hjl : j.val < (a.zipWith (fun x y => (x + y) % p) b).length := by
    rw [List.length_zipWith, ha, hb, min_self]; exact hj
  simp only [ggDepANToZ, ggTWNAdd, Pi.add_apply]
  rw [List.getD_eq_getElem (l := a.zipWith _ b) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja,
    List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hjb]
  rw [List.getElem_zipWith, ZMod.natCast_mod, Nat.cast_add]

private lemma kHK_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

private lemma kHK_refl_apply {p N : ℕ} (c f v : GGDepAE p N) :
    ggDepARefl c f v = v - ggDepAdot f v • c := by
  simp [ggDepARefl, kHK_form_apply]

private lemma kHK_toZ_refl {p N : ℕ} [Fact p.Prime] {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = N - 1) (hq2 : q.2.length = N - 1) (hv : v.length = N - 1) :
    ggTWNToZ p N (ggTWNRefl p q v) =
      ggTWRefl (ggTWNToZ p N q.1) (ggTWNToZ p N q.2) (ggTWNToZ p N v) := by
  unfold ggTWNRefl ggTWNToZ ggTWRefl
  rw [kHK_toZ_sub hv (kHK_smul_length hq1), kHK_toZ_smul hq1,
    ggDepANDot_cast q.2 v hq2 hv]
  rw [kHK_refl_apply]

private lemma kHK_mod_eq_of_cast_eq {p : ℕ} {x y : ℕ} (h : (x : ZMod p) = (y : ZMod p)) :
    x % p = y % p := (ZMod.natCast_eq_natCast_iff' x y p).mp h

private lemma kHK_cast_eq_of_mod_eq {p : ℕ} {x y : ℕ} (h : x % p = y % p) :
    (x : ZMod p) = (y : ZMod p) := (ZMod.natCast_eq_natCast_iff' x y p).mpr h

private lemma kHK_cast_eq_zero_of_mod_eq {p : ℕ} {x : ℕ} (h : x % p = 0) :
    (x : ZMod p) = 0 :=
  (ZMod.natCast_eq_zero_iff x p).mpr (Nat.dvd_of_mod_eq_zero h)

private lemma kHK_length_of_veceq {p : ℕ} {a b : List ℕ} (h : ggTWLVecEq p a b = true) :
    a.length = b.length := by
  rw [ggTWLVecEq, Bool.and_eq_true] at h
  exact decide_eq_true_eq.mp h.1

private lemma kHK_toZ_of_veceq {p N : ℕ} {a b : List ℕ} (h : ggTWLVecEq p a b = true) :
    ggTWNToZ p N a = ggTWNToZ p N b := by
  rw [ggTWLVecEq, Bool.and_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hlen' : a.length = b.length := decide_eq_true_eq.mp hlen
  funext j
  simp only [ggTWNToZ, ggDepANToZ]
  by_cases hj : j.val < a.length
  · have hkb : j.val < b.length := by rw [← hlen']; exact hj
    have hzip : j.val < (List.zipWith (fun x y => x % p == y % p) a b).length := by
      rw [List.length_zipWith, ← hlen', min_self]; exact hj
    have hcoord := (List.all_eq_true.mp hall) _ (List.getElem_mem hzip)
    simp only [id_eq] at hcoord
    rw [List.getElem_zipWith, beq_iff_eq] at hcoord
    rw [List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hj,
      List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hkb]
    exact kHK_cast_eq_of_mod_eq hcoord
  · rw [List.getD_eq_default (l := a) (d := 0) (n := j.val) (by omega),
      List.getD_eq_default (l := b) (d := 0) (n := j.val) (by omega)]

private lemma kHK_veceq_of_toZ_eq {p N : ℕ} {a b : List ℕ} (ha : a.length = N - 1)
    (hb : b.length = N - 1) (h : ggTWNToZ p N a = ggTWNToZ p N b) :
    ggTWLVecEq p a b = true := by
  rw [ggTWLVecEq, Bool.and_eq_true]
  refine ⟨decide_eq_true_eq.mpr (by rw [ha, hb]), ?_⟩
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  change (List.zipWith (fun x y => x % p == y % p) a b)[k] = true
  rw [List.getElem_zipWith, beq_iff_eq]
  apply kHK_mod_eq_of_cast_eq
  have hka : k < a.length := by rw [List.length_zipWith] at hk; omega
  have hkb : k < b.length := by rw [List.length_zipWith] at hk; omega
  have hkN : k < N - 1 := by rw [← ha]; exact hka
  have hcong := congrFun h ⟨k, hkN⟩
  simp only [ggTWNToZ, ggDepANToZ] at hcong
  rw [List.getD_eq_getElem (l := a) (d := 0) (n := k) hka,
    List.getD_eq_getElem (l := b) (d := 0) (n := k) hkb] at hcong
  exact hcong

private lemma kHK_jgens_mem {p N : ℕ} (pos : GGTWPos) {news : List GGDepANPair} {c : ℕ}
    (hc : c < N - 1) (hinj : ggTWNInJ N (ggTWPosNat pos) c = true) :
    (ggTWNH p N c, ggTWNA p N c) ∈ ggTWLOGens p N (ggTWPosNat pos) news :=
  List.mem_append.mpr (Or.inl
    (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨List.mem_range.mpr hc, hinj⟩, rfl⟩))

private lemma kHK_news_mem {p N : ℕ} (pos : GGTWPos) {news : List GGDepANPair}
    {q : GGDepANPair} (hq : q ∈ news) : q ∈ ggTWLOGens p N (ggTWPosNat pos) news :=
  List.mem_append.mpr (Or.inr hq)

private lemma kHK_news_mem_fst {p N : ℕ} (pos : GGTWPos) {news : List GGDepANPair}
    {q : GGDepANPair} (hq : q ∈ news) : q.1 ∈ (ggTWLOGens p N (ggTWPosNat pos) news).map (·.1) :=
  List.mem_map.mpr ⟨q, kHK_news_mem pos hq, rfl⟩

private lemma kHK_H_mem_fst {p N : ℕ} (pos : GGTWPos) {news : List GGDepANPair}
    (i : {i : Fin (N - 1) // ggTWInJ N pos i.val}) :
    ggTWNH p N i.1.val ∈ (ggTWLOGens p N (ggTWPosNat pos) news).map (·.1) :=
  List.mem_map.mpr ⟨(ggTWNH p N i.1.val, ggTWNA p N i.1.val),
    kHK_jgens_mem pos i.1.isLt ((ggTWNInJ_iff pos i.1.val).mpr i.2), rfl⟩

private lemma kHK_og_lengths {p N : ℕ} (pos : GGTWPos) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) {q : GGDepANPair}
    (hq : q ∈ ggTWLOGens p N (ggTWPosNat pos) news) :
    q.1.length = N - 1 ∧ q.2.length = N - 1 := by
  rw [ggTWLOGens, List.mem_append] at hq
  rcases hq with hq | hq
  · rcases List.mem_map.mp hq with ⟨c, _, rfl⟩
    exact ⟨ggTWNH_length p N c, ggTWNA_length p N c⟩
  · exact ⟨(hnews q hq).1, (hnews q hq).2.1⟩

private lemma kHK_getD_og {α : Type*} (l : List α) (d : α) {k : ℕ} (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem (l := l) (d := d) (n := k) hk]
  exact List.getElem_mem hk

private lemma kHK_stable_implies {p : ℕ} {og : List GGDepANPair} {cs R : List (List ℕ)}
    (h : ggTWLStable p og cs R = true) :
    (∀ c ∈ cs, ∃ r ∈ R, ggTWLVecEq p c r = true) ∧
      (∀ u ∈ R, ∀ g ∈ og, ∃ r ∈ R, ggTWLVecEq p (ggTWNRefl p g u) r = true) := by
  rw [ggTWLStable, Bool.and_eq_true] at h
  refine ⟨fun c hc => List.any_eq_true.mp (List.all_eq_true.mp h.1 c hc),
    fun u hu g hg => List.any_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h.2 u hu) g hg)⟩

private lemma kHK_gen_mem {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) {news : List GGDepANPair}
    {q : GGDepANPair} (hq : q ∈ ggTWLOGens p N (ggTWPosNat pos) news) :
    ggTWRefl (ggTWNToZ p N q.1) (ggTWNToZ p N q.2) ∈
      ggTWOGens p N pos (ggTWNNews p N news) := by
  rw [ggTWLOGens, List.mem_append] at hq
  rcases hq with hq | hq
  · rcases List.mem_map.mp hq with ⟨c, hc, rfl⟩
    rcases List.mem_filter.mp hc with ⟨hcR, hinj⟩
    rw [List.mem_range] at hcR
    have hcfin : c < N - 1 := hcR
    rw [ggTWNH_toZ (p := p) (N := N) ⟨c, hcfin⟩, ggTWNA_toZ (p := p) (N := N) ⟨c, hcfin⟩]
    exact Or.inl ⟨⟨⟨c, hcfin⟩, (ggTWNInJ_iff pos c).mp hinj⟩, Set.mem_univ _, rfl⟩
  · exact Or.inr ⟨(ggTWNToZ p N q.1, ggTWNToZ p N q.2), ⟨q, hq, rfl⟩, rfl⟩

private lemma kHK_getD_centre {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) {news : List GGDepANPair}
    {k : ℕ} (hk : k < (ggTWLOGens p N (ggTWPosNat pos) news).length) :
    ggTWNToZ p N ((ggTWLOGens p N (ggTWPosNat pos) news).getD k ([], [])).1 ∈
      ggTWOCentres p N pos (ggTWNNews p N news) := by
  set q : GGDepANPair := (ggTWLOGens p N (ggTWPosNat pos) news).getD k ([], []) with hqdef
  have hqmem : q ∈ ggTWLOGens p N (ggTWPosNat pos) news := by
    rw [hqdef]; exact kHK_getD_og _ _ hk
  rw [ggTWLOGens, List.mem_append] at hqmem
  rcases hqmem with hq | hq
  · rcases List.mem_map.mp hq with ⟨c, hc, hceq⟩
    rw [← hceq]
    rcases List.mem_filter.mp hc with ⟨hcR, hinj⟩
    rw [List.mem_range] at hcR
    have hcfin : c < N - 1 := hcR
    rw [ggTWNH_toZ (p := p) (N := N) ⟨c, hcfin⟩]
    exact Or.inl ⟨⟨⟨c, hcfin⟩, (ggTWNInJ_iff pos c).mp hinj⟩, Set.mem_univ _, rfl⟩
  · exact Or.inr ⟨(ggTWNToZ p N q.1, ggTWNToZ p N q.2), ⟨q, hq, rfl⟩, rfl⟩

private lemma kHK_isRefl {p N : ℕ} [Fact p.Prime] {q : GGDepANPair} (hq : GGTWNValid p N q) :
    GGTWIsRefl (ggTWNRflOf p N q) := by
  refine ⟨ggTWNToZ p N q.1, ggTWNToZ p N q.2, ?_, rfl⟩
  have h := ggDepANDot_cast (p := p) (N := N - 1) q.2 q.1 hq.2.1 hq.1
  rw [hq.2.2, ZMod.natCast_mod] at h
  exact h.symm

private abbrev kHK_P {p N : ℕ} (Rl : List (List ℕ)) (v : GGTWE p N) : Prop :=
  ∃ u0 ∈ Rl, ggTWNToZ p N u0 = v ∧ u0.length = N - 1

private lemma kHK_P_centres {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) {Rl : List (List ℕ)}
    (hcontains : ∀ a ∈ (ggTWLOGens p N (ggTWPosNat pos) news).map (·.1), ∃ r ∈ Rl,
      ggTWLVecEq p a r = true) :
    ∀ c ∈ ggTWOCentres p N pos (ggTWNNews p N news), kHK_P Rl c := by
  intro c hc
  rw [ggTWOCentres, Set.mem_union] at hc
  rcases hc with hc | hc
  · rcases hc with ⟨i, -, rfl⟩
    obtain ⟨r, hrR, hveq⟩ := hcontains (ggTWNH p N i.1.val) (kHK_H_mem_fst pos i)
    refine ⟨r, hrR, ?_, ?_⟩
    · rw [← kHK_toZ_of_veceq hveq, ggTWNH_toZ]
    · rw [← kHK_length_of_veceq hveq]; exact ggTWNH_length p N i.1.val
  · rcases hc with ⟨t, ht, rfl⟩
    rcases ht with ⟨q, hq, rfl⟩
    obtain ⟨r, hrR, hveq⟩ := hcontains q.1 (kHK_news_mem_fst pos hq)
    refine ⟨r, hrR, ?_, ?_⟩
    · rw [← kHK_toZ_of_veceq hveq]
    · rw [← kHK_length_of_veceq hveq]; exact (hnews q hq).1

private lemma kHK_P_step_q {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) {Rl : List (List ℕ)}
    (hstep : ∀ u ∈ Rl, ∀ g ∈ ggTWLOGens p N (ggTWPosNat pos) news,
      ∃ r ∈ Rl, ggTWLVecEq p (ggTWNRefl p g u) r = true)
    {q : GGDepANPair} (hq : q ∈ ggTWLOGens p N (ggTWPosNat pos) news) {v : GGTWE p N}
    (hv : kHK_P Rl v) :
    kHK_P Rl (ggTWRefl (ggTWNToZ p N q.1) (ggTWNToZ p N q.2) v) := by
  obtain ⟨u0, hu0R, hu0eq, hu0len⟩ := hv
  obtain ⟨r, hrR, hveq⟩ := hstep u0 hu0R q hq
  obtain ⟨hq1, hq2⟩ := kHK_og_lengths pos hnews hq
  refine ⟨r, hrR, ?_, ?_⟩
  · rw [← kHK_toZ_of_veceq hveq, kHK_toZ_refl hq1 hq2 hu0len, hu0eq]
  · rw [← kHK_length_of_veceq hveq]
    exact kHK_refl_length hq1 hu0len

private lemma kHK_P_gen {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) {Rl : List (List ℕ)}
    (hstep : ∀ u ∈ Rl, ∀ g ∈ ggTWLOGens p N (ggTWPosNat pos) news,
      ∃ r ∈ Rl, ggTWLVecEq p (ggTWNRefl p g u) r = true)
    {g : Module.End (ZMod p) (GGTWE p N)}
    (hg : g ∈ ggTWOGens p N pos (ggTWNNews p N news)) {v : GGTWE p N} (hv : kHK_P Rl v) :
    kHK_P Rl (g v) := by
  rw [ggTWOGens, Set.mem_union] at hg
  rcases hg with hg | hg
  · rcases hg with ⟨i, -, rfl⟩
    have hq : (ggTWNH p N i.1.val, ggTWNA p N i.1.val) ∈ ggTWLOGens p N (ggTWPosNat pos) news :=
      kHK_jgens_mem pos i.1.isLt ((ggTWNInJ_iff pos i.1.val).mpr i.2)
    have h := kHK_P_step_q pos hnews hstep hq hv
    rwa [ggTWNH_toZ (p := p) (N := N) i.1, ggTWNA_toZ (p := p) (N := N) i.1] at h
  · rcases hg with ⟨t, ht, rfl⟩
    rcases ht with ⟨q, hqnews, rfl⟩
    exact kHK_P_step_q pos hnews hstep (kHK_news_mem pos hqnews) hv

private lemma kHK_P_closure {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) {Rl : List (List ℕ)}
    (hstep : ∀ u ∈ Rl, ∀ g ∈ ggTWLOGens p N (ggTWPosNat pos) news,
      ∃ r ∈ Rl, ggTWLVecEq p (ggTWNRefl p g u) r = true)
    {W : Module.End (ZMod p) (GGTWE p N)}
    (hW : W ∈ Submonoid.closure (ggTWOGens p N pos (ggTWNNews p N news))) :
    ∀ (v : GGTWE p N), kHK_P Rl v → kHK_P Rl (W v) := by
  induction hW using Submonoid.closure_induction with
  | mem x hx => intro v hv; exact kHK_P_gen pos hnews hstep hx hv
  | one => intro v hv; simpa using hv
  | mul x y hx hy ihx ihy => intro v hv; exact ihx (y v) (ihy v hv)

private lemma kHK_roots_repr {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) {Rl : List (List ℕ)}
    (hcontains : ∀ a ∈ (ggTWLOGens p N (ggTWPosNat pos) news).map (·.1), ∃ r ∈ Rl,
      ggTWLVecEq p a r = true)
    (hstep : ∀ u ∈ Rl, ∀ g ∈ ggTWLOGens p N (ggTWPosNat pos) news,
      ∃ r ∈ Rl, ggTWLVecEq p (ggTWNRefl p g u) r = true)
    {v : GGTWE p N}
    (hv : v ∈ ggTWRoots (ggTWOGens p N pos (ggTWNNews p N news))
      (ggTWOCentres p N pos (ggTWNNews p N news))) : kHK_P Rl v := by
  rw [ggTWRoots] at hv
  rcases hv with ⟨W, hW, c, hc, rfl⟩
  exact kHK_P_closure pos hnews hstep hW c (kHK_P_centres pos hnews hcontains c hc)

private lemma kHK_foldr_length {p N : ℕ} (og : List GGDepANPair) (ow : List ℕ) (v0 : List ℕ)
    (hL : ∀ q ∈ og, q.1.length = N - 1) (how : ∀ k ∈ ow, k < og.length)
    (hv0 : v0.length = N - 1) :
    (ow.foldr (fun k acc => ggTWNRefl p (og.getD k ([], [])) acc) v0).length = N - 1 := by
  induction ow with
  | nil => simpa using hv0
  | cons k ow ih =>
      rw [List.foldr_cons]
      exact kHK_refl_length (hL _ (kHK_getD_og og ([], []) (how k (List.mem_cons_self ..))))
        (ih (fun k' hk' => how k' (List.mem_cons_of_mem k hk')))

private lemma kHK_foldr_roots {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) (ow : List ℕ) (v0 : List ℕ)
    (how : ∀ k ∈ ow, k < (ggTWLOGens p N (ggTWPosNat pos) news).length) (hv0 : v0.length = N - 1) :
    ∃ W ∈ Submonoid.closure (ggTWOGens p N pos (ggTWNNews p N news)),
      ggTWNToZ p N
          (ow.foldr (fun k acc =>
            ggTWNRefl p ((ggTWLOGens p N (ggTWPosNat pos) news).getD k ([], [])) acc) v0)
        = W (ggTWNToZ p N v0) := by
  let og := ggTWLOGens p N (ggTWPosNat pos) news
  induction ow with
  | nil => exact ⟨1, Submonoid.one_mem _, by simp⟩
  | cons k ow ih =>
      have hk : k < og.length := how k (List.mem_cons_self ..)
      have how' : ∀ k' ∈ ow, k' < og.length := fun k' hk' => how k' (List.mem_cons_of_mem k hk')
      obtain ⟨W, hWmem, hWeq⟩ := ih how'
      set q : GGDepANPair := og.getD k ([], []) with hqdef
      have hqmem : q ∈ og := kHK_getD_og og ([], []) hk
      have hqlen := kHK_og_lengths pos hnews hqmem
      have hlen := kHK_foldr_length (p := p) og ow v0
        (fun q hq => (kHK_og_lengths pos hnews hq).1) how' hv0
      refine ⟨ggTWRefl (ggTWNToZ p N q.1) (ggTWNToZ p N q.2) * W, ?_, ?_⟩
      · exact Submonoid.mul_mem _ (Submonoid.subset_closure (kHK_gen_mem pos hqmem)) hWmem
      · rw [List.foldr_cons, kHK_toZ_refl hqlen.1 hqlen.2 hlen, hWeq]
        rfl

theorem kHKTest_sound {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) (pos : GGTWPos)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q) (y : List ℕ)
    (hy : y.length = N - 1) (w : KHK)
    (h : kHKTest p N (ggTWPosNat pos) news y w = true) :
    GGTWKill .other p N pos (ggTWNNews p N news) (ggTWNToZ p N y) := by
  classical
  obtain ⟨⟨g, ww, oc, ow⟩, Rl⟩ := w
  let og := ggTWLOGens p N (ggTWPosNat pos) news
  let sp := ggTWNWord p N news (ggTWNGen p N news g) ww
  let vlist := ow.foldr (fun k acc => ggTWNRefl p (og.getD k ([], [])) acc)
    (og.getD oc ([], [])).1
  let sv := ggTWNRefl p sp vlist
  have hh := h
  dsimp only [kHKTest] at hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hh
  obtain ⟨⟨⟨⟨⟨⟨hg1, hw1⟩, hoc⟩, how⟩, hstab⟩, hdot⟩, hpar⟩ := hh
  have hstab' : ggTWLStable p og (og.map (·.1)) Rl = true := hstab
  have hword := ggTWNWord_valid_mem (p := p) (N := N) hp hN hnews
    (ggTWNGen_valid (p := p) (N := N) hp hN hnews hg1)
    (ggTWNGen_mem (p := p) (N := N) hp hN hg1) hw1
  have hsp : GGTWNValid p N sp := hword.1
  refine Or.inr ⟨ggTWNRflOf p N sp, hword.2, kHK_isRefl hsp, ?_, ?_⟩
  · have hdy : ggDepAdot (ggTWNToZ p N sp.2) (ggTWNToZ p N y) = 0 := by
      have hcast := ggDepANDot_cast (p := p) (N := N - 1) sp.2 y hsp.2.1 hy
      rw [kHK_cast_eq_zero_of_mod_eq hdot] at hcast
      exact hcast.symm
    change ggTWNRflOf p N sp (ggTWNToZ p N y) = ggTWNToZ p N y
    rw [kHK_refl_apply, hdy, zero_smul, sub_zero]
  · obtain ⟨hcontains, hstep⟩ := kHK_stable_implies hstab'
    have hv0 : ((og.getD oc ([], [])).1).length = N - 1 :=
      (kHK_og_lengths pos hnews (kHK_getD_og og ([], []) hoc)).1
    have hvlen : vlist.length = N - 1 :=
      kHK_foldr_length (p := p) og ow (og.getD oc ([], [])).1
        (fun q hq => (kHK_og_lengths pos hnews hq).1) how hv0
    refine ⟨ggTWNToZ p N vlist, ?_, ?_⟩
    · obtain ⟨W, hWmem, hWeq⟩ :=
        kHK_foldr_roots pos hnews ow (og.getD oc ([], [])).1 how hv0
      exact ⟨W, hWmem, ggTWNToZ p N (og.getD oc ([], [])).1,
        kHK_getD_centre pos hoc, hWeq⟩
    · intro w' hw' c d hc heq
      obtain ⟨u0, hu0R, hu0eq, hu0len⟩ := kHK_roots_repr pos hnews hcontains hstep hw'
      have hsv : ggTWNToZ p N sv = ggTWNRflOf p N sp (ggTWNToZ p N vlist) := by
        change ggTWNToZ p N (ggTWNRefl p sp vlist) =
          ggTWRefl (ggTWNToZ p N sp.1) (ggTWNToZ p N sp.2) (ggTWNToZ p N vlist)
        exact kHK_toZ_refl hsp.1 hsp.2.1 hvlen
      rw [← hsv] at heq
      rw [← hu0eq] at heq
      have hR : ggTWNToZ p N sv =
          ggTWNToZ p N (ggTWNAdd p (ggDepANSmul p c.val u0) (ggDepANSmul p d.val y)) := by
        rw [heq]
        simp only [ggTWNToZ]
        rw [kHK_toZ_add (p := p) (N := N - 1)
              (kHK_smul_length (p := p) (N := N - 1) hu0len)
              (kHK_smul_length (p := p) (N := N - 1) hy),
            kHK_toZ_smul (p := p) (N := N - 1) hu0len c.val,
            kHK_toZ_smul (p := p) (N := N - 1) hy d.val,
            ZMod.natCast_zmod_val c, ZMod.natCast_zmod_val d]
      have hveceq : ggTWLVecEq p sv
          (ggTWNAdd p (ggDepANSmul p c.val u0) (ggDepANSmul p d.val y)) = true :=
        kHK_veceq_of_toZ_eq (p := p) (kHK_refl_length hsp.1 hvlen)
          (kHK_add_length (kHK_smul_length hu0len) (kHK_smul_length hy)) hR
      have hcval : c.val ≠ 0 := by
        intro h0
        apply hc
        rw [← ZMod.natCast_zmod_val c, h0, Nat.cast_zero]
      have hpar_true : ggTWLParMod p y u0 sv = true := by
        rw [ggTWLParMod]
        refine List.any_eq_true.mpr ⟨c.val, List.mem_range.mpr (ZMod.val_lt c), ?_⟩
        rw [Bool.and_eq_true]
        refine ⟨decide_eq_true_eq.mpr hcval, ?_⟩
        exact List.any_eq_true.mpr ⟨d.val, List.mem_range.mpr (ZMod.val_lt d), hveceq⟩
      have hh2 := hpar u0 hu0R
      rw [hpar_true] at hh2
      exact Bool.false_ne_true hh2

end CFSG.StandardType.TWLK

end
