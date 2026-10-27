module

public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.Certificates.Kernel.Spor.PK.CertBridge

public section

namespace CFSG.Certificates.Kernel.PkEnum

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.KS.PK CFSG.GH74.KGroups

theorem pkp_apply {n : Nat} (a : VP n) (i : Fin n) : (pkp a i : Nat) = fd (wd n) a.1.1 i := rfl

theorem pkp_mulV {n : Nat} (a b : VP n) : pkp (mulV a b) = pkp a * pkp b := by
  ext i
  have h1 : ∀ j < n, fd (wd n) a.1.1 (fd (wd n) b.1.1 j) < n :=
    fun j hj => (a.2 _ (b.2 j hj).1).1
  rw [Equiv.Perm.mul_apply, pkp_apply, pkp_apply, pkp_apply]
  exact fd_pk h1 i.2

theorem pkp_oneV (n : Nat) : pkp (oneV n) = 1 := by
  ext i
  rw [pkp_apply]
  exact fd_pk (fun j hj => hj) i.2

theorem pkp_invV {n : Nat} (a : VP n) : pkp (invV a) = (pkp a)⁻¹ := rfl

theorem pkp_codeV {n : Nat} (σ : Equiv.Perm (Fin n)) : pkp (codeV σ) = σ := by
  ext i
  have h1 : ∀ j < n, (if h : j < n then (σ ⟨j, h⟩ : Nat) else 0) < n := by
    intro j hj
    rw [dif_pos hj]
    exact (σ _).2
  rw [pkp_apply]
  simp only [codeV]
  rw [fd_pk h1 i.2, dif_pos i.2]

theorem strongV_map {n : Nat} (Q : RawSchreierDatum n) : Q.strong.toList = (strongV Q).map pkp := by
  rw [strongV, List.map_map]
  have h : (pkp ∘ codeV : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) = id := funext pkp_codeV
  rw [h, List.map_id]

@[expose] def toSt {n : Nat} (q : StV n) : SchreierOrbitState n :=
  ⟨q.entries.map fun e => (e.1, pkp e.2), q.queue⟩

theorem lookup_map_snd {n : Nat} {β γ : Type*} (f : β → γ) (l : List (Fin n × β)) (x : Fin n) :
    (l.map fun e => (e.1, f e.2)).lookup x = (l.lookup x).map f := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.map_cons, List.lookup_cons]
    split <;> simp_all

theorem toSt_transversal {n : Nat} (q : StV n) (x : Fin n) :
    (toSt q).transversal? x = (q.entries.lookup x).map pkp :=
  lookup_map_snd pkp q.entries x

theorem toSt_discoverV {n : Nat} (q : StV n) (y : Fin n) (t : VP n) :
    toSt (discoverV q y t) = (toSt q).discover y (pkp t) := by
  unfold discoverV SchreierOrbitState.discover
  rw [toSt_transversal, Option.isSome_map]
  split
  · rfl
  · simp [toSt]

theorem toSt_stepV {n : Nat} (steps : List (VP n)) (q : StV n) :
    toSt (stepV steps q) = (toSt q).step (steps.map pkp) := by
  obtain ⟨es, qu⟩ := q
  cases qu with
  | nil => rfl
  | cons x pending =>
    change toSt (steps.foldl (fun st s => discoverV st (pkp s x) (mulV s ((es.lookup x).getD
        (oneV n)))) ⟨es, pending⟩) = (steps.map pkp).foldl (fun state s => state.discover (s x)
        (s * (((toSt ⟨es, x :: pending⟩).transversal? x).getD 1)))
        ⟨(toSt ⟨es, x :: pending⟩).entries, pending⟩
    rw [toSt_transversal, List.foldl_map]
    have htx : ((es.lookup x).map pkp).getD 1 = pkp ((es.lookup x).getD (oneV n)) := by
      cases es.lookup x <;> simp [pkp_oneV]
    rw [htx]
    generalize (es.lookup x).getD (oneV n) = tx
    have key : ∀ (st : StV n),
        toSt (steps.foldl (fun st s => discoverV st (pkp s x) (mulV s tx)) st) =
          steps.foldl (fun state s => state.discover (pkp s x) (pkp s * pkp tx)) (toSt st) := by
      induction steps with
      | nil => intro st; rfl
      | cons s steps ih =>
        intro st
        rw [List.foldl_cons, List.foldl_cons, ih, toSt_discoverV, pkp_mulV]
    exact key ⟨es, pending⟩

theorem toSt_runV {n : Nat} (steps : List (VP n)) (fuel : Nat) (q : StV n) :
    toSt (runV steps fuel q) = SchreierOrbitState.run (steps.map pkp) fuel (toSt q) := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih => rw [runV, SchreierOrbitState.run, ih, toSt_stepV]

theorem levelSteps_eq {n : Nat} (Q : RawSchreierDatum n) (Sc : List (VP n))
    (hS : Q.strong.toList = Sc.map pkp) (i : Nat) :
    Q.levelSteps i = (stepsV Sc Q.base i).map pkp := by
  unfold RawSchreierDatum.levelSteps RawSchreierDatum.levelGenerators stepsV
  rw [hS, List.filter_map, List.map_append, List.map_map, List.map_map]
  rfl

theorem orbitSearch_eq {n : Nat} (Q : RawSchreierDatum n) (Sc : List (VP n))
    (hS : Q.strong.toList = Sc.map pkp) (i : Fin Q.baseCount) :
    Q.orbitSearch i = toSt (levelV Sc Q.base i) := by
  rw [levelV, toSt_runV, ← levelSteps_eq Q Sc hS]
  unfold RawSchreierDatum.orbitSearch SchreierOrbitState.initial
  simp [toSt, pkp_oneV]

theorem products_map_pkp {n : Nat} (Ts : List (List (VP n))) :
    products (Ts.map (List.map pkp)) = (productsV Ts).map pkp := by
  induction Ts with
  | nil => simp [products, productsV, pkp_oneV]
  | cons T Ts ih =>
    simp only [List.map_cons, products, productsV, ih, List.flatMap_map, List.map_flatMap,
      List.map_map]
    congr 1
    funext t
    apply List.map_congr_left
    intro u _
    simp [pkp_mulV]

theorem enumeration_eq_enumV {n : Nat} (Q : RawSchreierDatum n) (Sc : List (VP n))
    (hS : Q.strong.toList = Sc.map pkp) : enumeration Q = (enumV Sc Q.base).map pkp := by
  unfold enumeration enumV
  rw [← products_map_pkp, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  unfold levelTransversals
  simp only [Function.comp_apply]
  rw [orbitSearch_eq Q Sc hS]
  generalize levelV Sc Q.base i = q
  unfold transV SchreierOrbitState.keys
  have he : (toSt q).entries = q.entries.map fun e => (e.1, pkp e.2) := rfl
  simp only [List.map_map, he]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, toSt_transversal]
  cases List.lookup e.1 q.entries <;> simp [pkp_oneV]

theorem elemsT_eq_elemsV {n : Nat} (Q : RawSchreierDatum n) : elemsT Q = elemsV Q := by
  rw [elemsT_eq, enumeration_eq_enumV Q _ (strongV_map Q)]
  rfl

theorem orderCertificate_eq_orderV {n : Nat} (Q : RawSchreierDatum n) :
    Q.orderCertificate = orderV Q := by
  unfold RawSchreierDatum.orderCertificate RawSchreierDatum.orbitSize orderV
  congr 1
  apply List.map_congr_left
  intro i _
  rw [orbitSearch_eq Q _ (strongV_map Q)]
  simp [SchreierOrbitState.keys, toSt]

theorem siftRes_map {n : Nat} (levels : List (Fin n × StV n)) (h : VP n) :
    schreierSiftResidual (levels.map fun e => (e.1, toSt e.2)) (pkp h) =
      (siftResV levels h).map pkp := by
  induction levels generalizing h with
  | nil => rfl
  | cons e levels ih =>
    obtain ⟨b, q⟩ := e
    simp only [List.map_cons, schreierSiftResidual, siftResV, toSt_transversal]
    cases q.entries.lookup (pkp h b) with
    | none => rfl
    | some t =>
      simp only [Option.map_some]
      rw [← ih, pkp_mulV, pkp_invV]

theorem sift_map {n : Nat} (levels : List (Fin n × StV n)) (h : VP n) :
    schreierSiftSucceeds (levels.map fun e => (e.1, toSt e.2)) (pkp h) = siftV levels h := by
  unfold schreierSiftSucceeds siftV
  rw [siftRes_map]
  cases siftResV levels h <;> rfl

theorem siftLevels_eq {n : Nat} (Q : RawSchreierDatum n) (Sc : List (VP n))
    (hS : Q.strong.toList = Sc.map pkp) (i : Nat) :
    Q.siftLevels Q.orbitTables i = (levelsV Sc Q.base i).map fun e => (e.1, toSt e.2) := by
  unfold RawSchreierDatum.siftLevels levelsV
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, RawSchreierDatum.orbitTables_get, orbitSearch_eq Q Sc hS]

theorem sift_eq_siftP {n : Nat} (Q : RawSchreierDatum n) (σ : Equiv.Perm (Fin n)) (i : Nat) :
    Q.sift σ i = siftP Q σ i := by
  have h := sift_map (levelsV (strongV Q) Q.base i) (codeV σ)
  rw [pkp_codeV] at h
  rw [RawSchreierDatum.sift, siftLevels_eq Q _ (strongV_map Q), h]
  rfl

theorem lookup_mem {n : Nat} {β : Type*} {l : List (Fin n × β)} {x : Fin n} {b : β}
    (h : l.lookup x = some b) : (x, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨a, c⟩ := e
    rw [List.lookup_cons] at h
    by_cases hxa : x = a
    · subst hxa
      simp only [beq_self_eq_true] at h
      cases h
      exact List.mem_cons_self
    · have : (x == a) = false := beq_eq_false_iff_ne.2 hxa
      rw [this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem sch_of_schP {n : Nat} (Q : RawSchreierDatum n) (h : schP Q = true) :
    (∀ s ∈ Q.levelGenerators Q.baseCount, s = 1) ∧
      (∀ (i : Fin Q.baseCount) (x : Fin n) (tx : Equiv.Perm (Fin n)),
        (Q.orbitTables.get i).transversal? x = some tx →
        ∀ s ∈ Q.levelSteps i.val, ∃ ty : Equiv.Perm (Fin n),
          (Q.orbitTables.get i).transversal? (s x) = some ty ∧
          schreierSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1)) (ty⁻¹ * s * tx) = true) := by
  have hS := strongV_map Q
  unfold schP schV at h
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
    cases hl : (levelV (strongV Q) Q.base i).entries.lookup (pkp sv x) with
    | none => simp
    | some ty =>
      intro h1
      refine ⟨pkp ty, rfl, ?_⟩
      rw [siftLevels_eq Q _ hS, ← pkp_invV, ← pkp_mulV, ← pkp_mulV, sift_map]
      exact h1

theorem check_certificate_of {n : Nat} (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List ℤ)) {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup)
    (h : schP (certificate hn gens words base hbase) = true) :
    (certificate hn gens words base hbase).check = true := by
  rw [RawSchreierDatum.check_eq_true_iff]
  exact ⟨CFSG.KS.PK.certificate_initial hn gens words base hbase,
    CFSG.KS.PK.certificate_words hn gens words base hbase, (sch_of_schP _ h).1,
    (sch_of_schP _ h).2⟩

theorem all_of_chunks {α : Type*} (l : List α) (p : α → Bool) (c m : Nat)
    (hlen : l.length ≤ m * c) (h : ∀ j < m, ((l.drop (j * c)).take c).all p = true) :
    l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0
      rw [Nat.mul_zero] at hlen
      omega
    · exact h0
  have hj : i / c < m := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  have h1 := List.all_eq_true.1 (h (i / c) hj)
  apply h1
  have hmod : i % c < c := Nat.mod_lt _ hc
  have hi' : i / c * c + i % c = i := Nat.div_add_mod' i c
  have hlt : i % c < ((l.drop (i / c * c)).take c).length := by
    simp only [List.length_take, List.length_drop]
    omega
  rw [List.mem_iff_getElem]
  refine ⟨i % c, hlt, ?_⟩
  simp only [List.getElem_take, List.getElem_drop, hi']

end CFSG.Certificates.Kernel.PkEnum

end
