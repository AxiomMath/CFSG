module

public import Certificates.Data.Kernel.Ivk8Norm
public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CFSG.KS.Ivk8Norm

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.PK CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : Nat}

theorem eq_of_vals {l₁ l₂ : List (VP n)} (h : (l₁.map Subtype.val == l₂.map Subtype.val) = true) :
    l₁ = l₂ :=
  List.map_injective_iff.2 Subtype.val_injective (beq_iff_eq.1 h)

theorem pkp_eq_iff (a b : VP n) :
    pkp a = pkp b ↔ ∀ i < n, fd (wd n) a.1.1 i = fd (wd n) b.1.1 i := by
  constructor
  · intro h i hi
    have h1 := congrArg (fun σ : Equiv.Perm (Fin n) => (σ ⟨i, hi⟩ : Nat)) h
    simpa only [pkp_apply] using h1
  · intro h
    ext i
    rw [pkp_apply, pkp_apply]
    exact h i i.2

theorem difV_eq_false_iff (a b : VP n) : difV a b = false ↔ pkp a = pkp b := by
  unfold difV
  rw [List.any_eq_false, pkp_eq_iff]
  apply forall_congr'
  intro i
  rw [List.mem_range]
  apply imp_congr_right
  intro _
  cases hb : Nat.beq (fd (wd n) a.1.1 i) (fd (wd n) b.1.1 i) with
  | false => exact ⟨fun h => absurd rfl h, fun h => absurd h (Nat.ne_of_beq_eq_false hb)⟩
  | true => exact ⟨fun _ => Nat.eq_of_beq_eq_true hb, fun _ => Bool.false_ne_true⟩

theorem difV_eq_true_iff (a b : VP n) : difV a b = true ↔ pkp a ≠ pkp b := by
  rw [Ne, ← difV_eq_false_iff]
  cases difV a b <;> simp

theorem eq_of_not_difV {a b : VP n} (h : (!difV a b) = true) : pkp a = pkp b := by
  apply (difV_eq_false_iff a b).1
  cases hd : difV a b
  · rfl
  · rw [hd] at h
    exact absurd h Bool.false_ne_true

theorem pkp_conjV (c y : VP n) : pkp (conjV c y) = pkp c * pkp y * (pkp c)⁻¹ := by
  simp only [conjV, pkp_mulV, pkp_invV]

theorem pkp_letV (S : List (VP n)) (z : Int) :
    pkp (letV S z) = if 0 < z then (S.map pkp).getD (z.toNat - 1) 1
      else ((S.map pkp).getD ((-z).toNat - 1) 1)⁻¹ := by
  have h : ∀ m, (S.map pkp).getD m 1 = pkp (S.getD m (oneV n)) := by
    intro m
    rw [← pkp_oneV n, List.getD_map]
  by_cases hz : 0 < z
  · rw [if_pos hz, h, letV, if_pos hz]
  · rw [if_neg hz, h, letV, if_neg hz, pkp_invV]

theorem pkp_evV (S : List (VP n)) (w : List Int) : pkp (evV S w) = evalCodes (S.map pkp) w := by
  induction w with
  | nil => exact pkp_oneV n
  | cons z w ih =>
    change pkp (mulV (letV S z) (evV S w)) = _
    rw [pkp_mulV, ih, pkp_letV, evalCodes]

theorem map_evalCodes (G : List (VP n)) (ws : List (List Int)) :
    ws.map (evalCodes (G.map pkp)) = (ws.map (evV G)).map pkp := by
  rw [List.map_map]
  exact List.map_congr_left fun w _ => (pkp_evV G w).symm

theorem buildStrong_map (S : List (VP n)) (ws : List (List Int)) :
    buildStrong (S.map pkp) ws = (buildV S ws).map pkp := by
  induction ws generalizing S with
  | nil => rfl
  | cons w ws ih =>
    rw [buildStrong, buildV, ← ih, List.map_append, List.map_singleton, pkp_evV, tab_eq]

theorem certificate_strong_eq (hn : 1 ≤ n) (S : List (VP n)) (words : List (List Int)) {k : Nat}
    (base : Vector (Fin n) k) (hbase : base.toList.Nodup) (Sc : List (VP n))
    (h : buildV S words = Sc) :
    (certificate hn (S.map pkp) words base hbase).strong.toList = Sc.map pkp := by
  rw [certificate_strong_toList, buildStrong_map, h]

theorem sch_of_schV (Q : RawSchreierDatum n) (Sc : List (VP n))
    (hS : Q.strong.toList = Sc.map pkp) (h : schV Sc Q.base = true) :
    (∀ s ∈ Q.levelGenerators Q.baseCount, s = 1) ∧
      (∀ (i : Fin Q.baseCount) (x : Fin n) (tx : Equiv.Perm (Fin n)),
        (Q.orbitTables.get i).transversal? x = some tx →
        ∀ s ∈ Q.levelSteps i.val, ∃ ty : Equiv.Perm (Fin n),
          (Q.orbitTables.get i).transversal? (s x) = some ty ∧
          schreierSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1)) (ty⁻¹ * s * tx) = true) := by
  unfold schV at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨hterm, hsch⟩ := h
  refine ⟨?_, ?_⟩
  · intro s hs
    unfold RawSchreierDatum.levelGenerators at hs
    rw [hS, List.mem_filter, List.mem_map] at hs
    obtain ⟨⟨v, hv, rfl⟩, hfix⟩ := hs
    have h1 := hterm v (List.mem_filter.2 ⟨hv, by
      rw [List.take_of_length_le (by simp)] at hfix
      exact hfix⟩)
    exact (schreierPermEq_eq_true_iff _ _).1 h1
  · intro i x tx htx s hs
    rw [RawSchreierDatum.orbitTables_get, orbitSearch_eq Q _ hS, toSt_transversal] at htx ⊢
    obtain ⟨tv, htv, rfl⟩ := Option.map_eq_some_iff.1 htx
    rw [levelSteps_eq Q _ hS, List.mem_map] at hs
    obtain ⟨sv, hsv, rfl⟩ := hs
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 (hsch i (List.mem_finRange i)) (x, tv)
      (lookup_mem htv)) sv hsv
    simp only at h1
    revert h1
    cases hl : (levelV Sc Q.base i).entries.lookup (pkp sv x) with
    | none => simp
    | some ty =>
      intro h1
      refine ⟨pkp ty, rfl, ?_⟩
      rw [siftLevels_eq Q _ hS, ← pkp_invV, ← pkp_mulV, ← pkp_mulV, sift_map]
      exact h1

theorem check_of_schV (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n))) (words : List (List ℤ))
    {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup) (Sc : List (VP n))
    (hS : (certificate hn gens words base hbase).strong.toList = Sc.map pkp)
    (h : schV Sc base = true) : (certificate hn gens words base hbase).check = true := by
  rw [RawSchreierDatum.check_eq_true_iff]
  exact ⟨CFSG.KS.PK.certificate_initial hn gens words base hbase,
    CFSG.KS.PK.certificate_words hn gens words base hbase, (sch_of_schV _ Sc hS h).1,
    (sch_of_schV _ Sc hS h).2⟩

theorem orderCertificate_eq_ordV (Q : RawSchreierDatum n) (Sc : List (VP n))
    (hS : Q.strong.toList = Sc.map pkp) : Q.orderCertificate = ordV Sc Q.base := by
  unfold RawSchreierDatum.orderCertificate RawSchreierDatum.orbitSize ordV
  congr 1
  apply List.map_congr_left
  intro i _
  rw [orbitSearch_eq Q Sc hS]
  simp [SchreierOrbitState.keys, toSt]

theorem kleinOK_spec {A B : VP n} (h : kleinOK A B = true) :
    pkp A * pkp A = 1 ∧ pkp B * pkp B = 1 ∧ pkp A * pkp B = pkp B * pkp A ∧ pkp A ≠ 1 ∧
      pkp B ≠ 1 ∧ pkp A ≠ pkp B := by
  simp only [kleinOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, (difV_eq_true_iff _ _).1 h6⟩
  · rw [← pkp_mulV, ← pkp_oneV n]
    exact eq_of_not_difV h1
  · rw [← pkp_mulV, ← pkp_oneV n]
    exact eq_of_not_difV h2
  · rw [← pkp_mulV, ← pkp_mulV]
    exact eq_of_not_difV h3
  · rw [← pkp_oneV n]
    exact (difV_eq_true_iff _ _).1 h4
  · rw [← pkp_oneV n]
    exact (difV_eq_true_iff _ _).1 h5

theorem conjOK_spec {r : VP n} {ps : List (VP n × VP n)} (h : conjOK r ps = true) :
    ∀ p ∈ ps, pkp p.1 * pkp r * (pkp p.1)⁻¹ = pkp p.2 := by
  intro p hp
  rw [← pkp_conjV]
  exact eq_of_not_difV (List.all_eq_true.1 h p hp)

theorem commOK_spec {r : VP n} {S : List (VP n)} (h : commOK r S = true) :
    ∀ s ∈ S, pkp s * pkp r = pkp r * pkp s := by
  intro s hs
  rw [← pkp_mulV, ← pkp_mulV]
  exact eq_of_not_difV (List.all_eq_true.1 h s hs)

theorem conj_eq_or_of_mem_normalizer {G : Type*} [Group G] {x h : G} (hx : orderOf x = 3)
    (hh : h ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    h * x * h⁻¹ = x ∨ h * x * h⁻¹ = x⁻¹ := by
  have hmem : h * x * h⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.1 hh x).1 (Subgroup.mem_zpowers x)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have e : h * x * h⁻¹ = x ^ (k % 3) := by
    rw [← hk, ← zpow_mod_orderOf, hx]
    norm_num
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at e
    have hx1 : x = 1 := conj_eq_one_iff.1 e
    rw [hx1, orderOf_one] at hx
    omega
  · left
    rw [e, h1, zpow_one]
  · right
    have hx3 : x ^ 3 = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    rw [e, h2, eq_inv_iff_mul_eq_one, zpow_two, ← pow_three', hx3]

theorem moves_of_movesV {h x : VP n} (hm : movesV h x = true) :
    pkp h * pkp x * (pkp h)⁻¹ ≠ pkp x ∧ pkp h * pkp x * (pkp h)⁻¹ ≠ (pkp x)⁻¹ := by
  simp only [movesV, neV, Bool.and_eq_true] at hm
  rw [← pkp_conjV, ← pkp_invV]
  exact ⟨(difV_eq_true_iff _ _).1 hm.1, (difV_eq_true_iff _ _).1 hm.2⟩

theorem chk_spec {A B : VP n} {cs K : List (VP n)} (h : chk A B cs K = true) :
    ∀ y ∈ K, ∀ c ∈ cs, orderOf (pkp y) = 3 →
      ¬ (pkp A ∈ Subgroup.normalizer
          (Subgroup.zpowers (pkp c * pkp y * (pkp c)⁻¹) : Set (Equiv.Perm (Fin n))) ∧
        pkp B ∈ Subgroup.normalizer
          (Subgroup.zpowers (pkp c * pkp y * (pkp c)⁻¹) : Set (Equiv.Perm (Fin n)))) := by
  intro y hy c hc ho ⟨hA, hB⟩
  have hx : orderOf (pkp c * pkp y * (pkp c)⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ho
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h c hc) y hy
  simp only [okY, Bool.or_eq_true] at h1
  rcases h1 with (h1 | h1) | h1
  · apply (difV_eq_true_iff _ _).1 h1
    rw [pkp_mulV, pkp_mulV, pkp_oneV, ← pow_three, ← ho]
    exact pow_orderOf_eq_one _
  · have hy1 : pkp y = 1 := by
      rw [← pkp_oneV n]
      exact eq_of_not_difV h1
    rw [hy1, orderOf_one] at ho
    omega
  · simp only [movesAB, Bool.or_eq_true] at h1
    rcases h1 with hm | hm
    · have hm' := moves_of_movesV hm
      rw [pkp_conjV] at hm'
      rcases conj_eq_or_of_mem_normalizer hx hA with e | e
      · exact hm'.1 e
      · exact hm'.2 e
    · have hm' := moves_of_movesV hm
      rw [pkp_conjV] at hm'
      rcases conj_eq_or_of_mem_normalizer hx hB with e | e
      · exact hm'.1 e
      · exact hm'.2 e

theorem chk_spec_perm {A B : VP n} {cs K : List (VP n)} (h : chk A B cs K = true) :
    ∀ σ ∈ K.map pkp, ∀ c ∈ cs, orderOf σ = 3 →
      ¬ (pkp A ∈ Subgroup.normalizer
          (Subgroup.zpowers (pkp c * σ * (pkp c)⁻¹) : Set (Equiv.Perm (Fin n))) ∧
        pkp B ∈ Subgroup.normalizer
          (Subgroup.zpowers (pkp c * σ * (pkp c)⁻¹) : Set (Equiv.Perm (Fin n)))) := by
  intro σ hσ
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hσ
  exact chk_spec h y hy

end CFSG.KS.Ivk8Norm

end
