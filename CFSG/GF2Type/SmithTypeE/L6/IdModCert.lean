module

public import CFSG.Certificates.Kernel.SmithL6KGSound
public import Certificates.Certificate38604
public import Certificates.Certificate38654
public import Certificates.Certificate38655
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod CFSG.LargeExtraspecial.S14
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V decode decode_two_pow eq_of_decode_eq linearEquiv_ext_single)

attribute [local irreducible] planeImg meetCard tvIdxTab tvTab tvImg tvList wtIdx planePtsArr
  flagArr

theorem idWtCheck_holds : idChkWt = true :=
  Certificates.certificate38654.1

theorem idWtInjCheck_holds : idChkWtInj = true :=
  Certificates.certificate38654.2.1

theorem idQaCheck_holds :
    ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
      (∀ s, ∃ p : Fin 1953, p ∈ planeSet 0 ∧ ∃ k : Fin 1395, ¬ Opp 0 k ∧
        v s = tvLin p.val (wtV k) + wtV k) ∧
      ∀ j : Fin 1395, wtV j ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW 0 j = true :=
  Certificates.certificate38654.2.2

theorem idCvCheck_holds :
    ∀ v : V, (∀ p ∈ planeSet 0, tvLin p.val v = v) ↔ v = 0 ∨ v = wtV 0 :=
  Certificates.certificate38655

theorem wt_lt {i : ℕ} (hi : i < 1395) : wt i < 2 ^ 20 := by
  have h := idWtCheck_holds
  simp only [idChkWt, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  have := (h i hi).1
  rwa [wtArr_get hi] at this

theorem idWt_ne_zero {i : ℕ} (hi : i < 1395) : wt i ≠ 0 := by
  have h := idWtCheck_holds
  simp only [idChkWt, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at h
  have := (h i hi).2
  rwa [wtArr_get hi] at this

theorem idWt_injective {i j : ℕ} (hi : i < 1395)
    (hj : j < 1395) (h : wt i = wt j) : i = j := by
  have hc := idWtInjCheck_holds
  simp only [idChkWtInj, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at hc
  rcases hc i hi j hj with h1 | h1
  · exact h1
  · rw [wtArr_get hi, wtArr_get hj] at h1
    exact absurd h h1

theorem idAdjM_eq_adjW {i j : ℕ} (hi : i < 1395) (hj : j < 1395) : adjM i j = adjW i j := by
  have hm : ∀ {k : ℕ}, k < 1395 → maskArr[k]! = wMask k := fun hk => by
    simp [maskArr, getElem!_pos, hk]
  simp only [adjM, adjW, hm hi, hm hj]

section Transport


theorem tvEquiv_self_apply {k : ℕ} (hk : k < 1953) (v : V) : tvEquiv k (tvEquiv k v) = v := by
  rw [← LinearEquiv.mul_apply, tvEquiv_mul_self hk]
  rfl

theorem tvEquiv_tvImg {k a : ℕ} (hk : k < 1953) (ha : a < 1953) :
    tvEquiv (tvImg k a) = tvEquiv k * tvEquiv a * tvEquiv k := by
  apply linearEquiv_ext_single
  intro m
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← decode_two_pow,
    tvEquiv_decode (CFSG.SmithL6.K.tvImg_lt hk ha), tvEquiv_decode hk, tvEquiv_decode ha,
    tvEquiv_decode hk,
    CFSG.SmithL6.K.tvCols_tvImg hk ha _ (Nat.pow_lt_pow_right (by norm_num) m.2)]

theorem tvEquiv_tvImg_apply {k a : ℕ} (hk : k < 1953) (ha : a < 1953) (w : V) :
    tvEquiv (tvImg k a) w = tvEquiv k (tvEquiv a (tvEquiv k w)) := by
  rw [tvEquiv_tvImg hk ha, LinearEquiv.mul_apply, LinearEquiv.mul_apply]

theorem exists_fin_val {n x : ℕ} (h : x < n) : ∃ q : Fin n, q.val = x :=
  ⟨⟨x, h⟩, Fin.val_mk h⟩

theorem meetCard_le_planeImg {k u j : ℕ} (hk : k < 1953) (hu : u < 1395) (hj : j < 1395) :
    meetCard u j ≤ meetCard (planeImg k u) (planeImg k j) := by
  rw [meetCard_eq_card hu hj, meetCard_eq_card (tw_parts hk hu).1 (tw_parts hk hj).1]
  refine Finset.card_le_card_of_injOn
    (fun a => ⟨tvImg k a.val, CFSG.SmithL6.K.tvImg_lt hk a.2⟩) (fun a ha => ?_) ?_
  · rw [Finset.mem_coe, Finset.mem_inter, mem_planeSet, mem_planeSet] at ha ⊢
    exact ⟨((tw_parts hk hu).2.2 a a.2 ha.1).2, ((tw_parts hk hj).2.2 a a.2 ha.2).2⟩
  · intro a _ b _ hab
    have e : tvImg k a.val = tvImg k b.val := Fin.mk.inj hab
    exact Fin.ext (by rw [← CFSG.SmithL6.K.tvImg_tvImg hk a.2, e,
      CFSG.SmithL6.K.tvImg_tvImg hk b.2])


theorem planeImg_planeImg {k u : ℕ} (hk : k < 1953) (hu : u < 1395) :
    planeImg k (planeImg k u) = u := by
  obtain ⟨h1, h2, -⟩ := tw_parts hk hu
  obtain ⟨h3, h4, -⟩ := tw_parts hk h1
  refine idWt_injective h3 hu (eq_of_decode_eq (wt_lt h3) (wt_lt hu) ?_)
  rw [h4, h2, ← tvEquiv_decode hk, ← tvEquiv_decode hk, tvEquiv_self_apply hk]

theorem meetCard_planeImg {k u j : ℕ} (hk : k < 1953) (hu : u < 1395) (hj : j < 1395) :
    meetCard (planeImg k u) (planeImg k j) = meetCard u j := by
  refine le_antisymm ?_ (meetCard_le_planeImg hk hu hj)
  have h := meetCard_le_planeImg hk (tw_parts hk hu).1 (tw_parts hk hj).1
  rwa [planeImg_planeImg hk hu, planeImg_planeImg hk hj] at h

theorem adjW_planeImg {k u j : ℕ} (hk : k < 1953) (hu : u < 1395) (hj : j < 1395) :
    adjW (planeImg k u) (planeImg k j) = adjW u j := by
  have hu' := (tw_parts hk hu).1
  have hj' := (tw_parts hk hj).1
  rw [← idAdjM_eq_adjW hu' hj', ← idAdjM_eq_adjW hu hj, (pairs_parts hu' hj').2.2.2,
    (pairs_parts hu hj).2.2.2, meetCard_planeImg hk hu hj]

theorem opp_planeImg {k u j : ℕ} (hk : k < 1953) (hu : u < 1395) (hj : j < 1395) :
    Opp (planeImg k u) (planeImg k j) ↔ Opp u j := by
  rw [opp_iff_meetCard (tw_parts hk hu).1 (tw_parts hk hj).1, opp_iff_meetCard hu hj,
    meetCard_planeImg hk hu hj]

@[expose] def QaAt (i : ℕ) : Prop :=
  ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
    (∀ s, ∃ p : Fin 1953, p ∈ planeSet i ∧ ∃ k : Fin 1395, ¬ Opp i k ∧
      v s = tvEquiv p (wtV k) + wtV k) ∧
    ∀ j : Fin 1395, wtV j ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW i j = true

@[expose] def CvAt (i : ℕ) : Prop :=
  ∀ v : V, (∀ p ∈ planeSet i, tvEquiv p.val v = v) ↔ v = 0 ∨ v = wtV i

theorem qaAt_zero : QaAt 0 := by
  obtain ⟨v, hli, hgen, hspan⟩ := idQaCheck_holds
  refine ⟨v, hli, fun s => ?_, hspan⟩
  obtain ⟨p, hp, k, hk, he⟩ := hgen s
  exact ⟨p, hp, k, hk, by rw [he, tvEquiv_apply p.2]⟩

theorem cvAt_zero : CvAt 0 := fun v => by
  rw [← idCvCheck_holds v]
  exact forall₂_congr fun p _ => by rw [tvEquiv_apply p.2]

theorem linearIndependent_tvEquiv {k : ℕ} {v : Fin 10 → V}
    (hli : LinearIndependent (ZMod 2) v) :
    LinearIndependent (ZMod 2) fun s => tvEquiv k (v s) :=
  hli.map' (tvEquiv k).toLinearMap (tvEquiv k).ker

theorem mem_span_tvEquiv {k : ℕ} (hk : k < 1953) {v : Fin 10 → V} (w : V) :
    w ∈ Submodule.span (ZMod 2) (Set.range fun s => tvEquiv k (v s)) ↔
      tvEquiv k w ∈ Submodule.span (ZMod 2) (Set.range v) := by
  rw [Submodule.mem_span_range_iff_exists_fun, Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h]
    simp only [map_sum, map_smul, tvEquiv_self_apply hk]
  · have h' := congrArg (tvEquiv k) h
    simpa only [map_sum, map_smul, tvEquiv_self_apply hk] using h'

theorem gen_tvEquiv {k u : ℕ} (hk : k < 1953) (hu : u < 1395) {p : Fin 1953}
    (hp : p ∈ planeSet u) (w : V) :
    ∃ q : Fin 1953, q ∈ planeSet (planeImg k u) ∧
      tvEquiv k (tvEquiv p.val w + w) = tvEquiv q.val (tvEquiv k w) + tvEquiv k w := by
  obtain ⟨hq, hqi⟩ := (tw_parts hk hu).2.2 p p.2 (mem_planeSet.1 hp)
  obtain ⟨q, hqv⟩ := exists_fin_val hq
  refine ⟨q, mem_planeSet.2 (by rw [hqv]; exact hqi), ?_⟩
  rw [map_add, hqv, tvEquiv_tvImg_apply hk p.2, tvEquiv_self_apply hk]

theorem qaAt_step {k u : ℕ} (hk : k < 1953) (hu : u < 1395) (hQ : QaAt u) :
    QaAt (planeImg k u) := by
  obtain ⟨v, hli, hgen, hspan⟩ := hQ
  refine ⟨fun s => tvEquiv k (v s), linearIndependent_tvEquiv hli, fun s => ?_, fun j => ?_⟩
  · obtain ⟨p, hp, kk, hkk, he⟩ := hgen s
    obtain ⟨q, hq, e⟩ := gen_tvEquiv hk hu hp (wtV kk)
    obtain ⟨m, hmv⟩ := exists_fin_val (tw_parts hk kk.2).1
    refine ⟨q, hq, m, fun ho => hkk ((opp_planeImg hk hu kk.2).1 (by rw [← hmv]; exact ho)), ?_⟩
    beta_reduce
    rw [hmv, ← tvEquiv_wtV hk kk.2, he, e]
  · obtain ⟨m, hmv⟩ := exists_fin_val (tw_parts hk j.2).1
    rw [mem_span_tvEquiv hk, tvEquiv_wtV hk j.2, ← hmv, hspan m, hmv,
      ← adjW_planeImg hk hu (tw_parts hk j.2).1, planeImg_planeImg hk j.2]

theorem fix_conj_of {k u : ℕ} (hk : k < 1953) (hu : u < 1395) {v : V}
    (h : ∀ p ∈ planeSet (planeImg k u), tvEquiv p.val v = v) :
    ∀ q ∈ planeSet u, tvEquiv q.val (tvEquiv k v) = tvEquiv k v := by
  intro q hq
  obtain ⟨hq', hqi⟩ := (tw_parts hk hu).2.2 q q.2 (mem_planeSet.1 hq)
  obtain ⟨r, hrv⟩ := exists_fin_val hq'
  have h1 := h r (mem_planeSet.2 (by rw [hrv]; exact hqi))
  rw [hrv, tvEquiv_tvImg_apply hk q.2] at h1
  calc tvEquiv q.val (tvEquiv k v) =
      tvEquiv k (tvEquiv k (tvEquiv q.val (tvEquiv k v))) := (tvEquiv_self_apply hk _).symm
    _ = tvEquiv k v := by rw [h1]

theorem fix_of_conj {k u : ℕ} (hk : k < 1953) (hu : u < 1395) {v : V}
    (h : ∀ q ∈ planeSet u, tvEquiv q.val (tvEquiv k v) = tvEquiv k v) :
    ∀ p ∈ planeSet (planeImg k u), tvEquiv p.val v = v := by
  intro p hp
  obtain ⟨hq', hqi⟩ := (tw_parts hk (tw_parts hk hu).1).2.2 p p.2 (mem_planeSet.1 hp)
  rw [planeImg_planeImg hk hu] at hqi
  obtain ⟨r, hrv⟩ := exists_fin_val hq'
  have h1 := h r (mem_planeSet.2 (by rw [hrv]; exact hqi))
  rw [hrv, tvEquiv_tvImg_apply hk p.2, tvEquiv_self_apply hk] at h1
  exact (tvEquiv k).injective h1

theorem cvAt_step {k u : ℕ} (hk : k < 1953) (hu : u < 1395) (hQ : CvAt u) :
    CvAt (planeImg k u) := by
  intro v
  rw [← tvEquiv_wtV hk hu]
  refine ⟨fun h => ?_, fun h => fix_of_conj hk hu ((hQ (tvEquiv k v)).2 ?_)⟩
  · rcases (hQ (tvEquiv k v)).1 (fix_conj_of hk hu h) with h0 | h1
    · exact Or.inl ((LinearEquiv.map_eq_zero_iff _).1 h0)
    · exact Or.inr (by rw [← h1, tvEquiv_self_apply hk])
  · rcases h with h0 | h1
    · exact Or.inl (by rw [h0, map_zero])
    · exact Or.inr (by rw [h1, tvEquiv_self_apply hk])

end Transport

theorem exists_qaBasis
    {i : ℕ} (hi : i < 1395) :
    ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
      (∀ s, ∃ p : Fin 1953, p ∈ planeSet i ∧ ∃ k : Fin 1395, ¬ Opp i k ∧
        v s = tvEquiv p (wtV k) + wtV k) ∧
      ∀ j : Fin 1395, wtV j ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW i j = true :=
  Certificates.certificate38604.1 QaAt
    (fun u _ hu => by
      rw [show u = 0 by simpa using hu]
      exact qaAt_zero)
    (fun k hk u hu w _ he hQ => by
      rw [← show planeImg k u = w by simpa using he]
      exact qaAt_step hk hu hQ) i hi

theorem fixed_iff
    {i : ℕ} (hi : i < 1395)
    (v : V) : (∀ p ∈ planeSet i, tvEquiv p.val v = v) ↔ v = 0 ∨ v = wtV i :=
  Certificates.certificate38604.1 CvAt
    (fun u _ hu => by
      rw [show u = 0 by simpa using hu]
      exact cvAt_zero)
    (fun k hk u hu w _ he hQ => by
      rw [← show planeImg k u = w by simpa using he]
      exact cvAt_step hk hu hQ) i hi v

theorem tvEquiv_wtV_self
    {i : ℕ} (hi : i < 1395)
    {p : Fin 1953} (hp : p ∈ planeSet i) : tvEquiv p.val (wtV i) = wtV i :=
  (fixed_iff hi (wtV i)).2 (Or.inr rfl) p hp

end CFSG.GF2Type.SmithTypeE.L6
