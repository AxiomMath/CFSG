module

public import CFSG.GH74.KGroups.CoverJ3Check
public import CFSG.GH74.KGroups.CoverE16
public import CFSG.GH74.KGroups.CoverRank
import all CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Generic.Fusion

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.KGroups.J3

theorem conj_of_odd_pow {G : Type*} [Group G] {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    {n : ℕ} (hn : n % 2 = 1) (h : (s * t) ^ n = 1) : ∃ g : G, g * s * g⁻¹ = t := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set u := s * t with hu
  have hsu : s * u * s⁻¹ = u⁻¹ := by
    rw [hu, mul_inv_rev, ht', hs']
    calc s * (s * t) * s = (s * s) * t * s := by simp only [mul_assoc]
      _ = t * s := by rw [hs, one_mul]
  have hk : s * u ^ k * s⁻¹ = (u⁻¹) ^ k := by
    have := map_pow (MulAut.conj s) u k
    simpa [MulAut.conj_apply, hsu] using this
  refine ⟨u ^ k, ?_⟩
  have h1 : u ^ k * s = s * (u ^ k)⁻¹ := by
    have h2 : s * u ^ k * s⁻¹ = (u ^ k)⁻¹ := by rw [hk, inv_pow]
    calc u ^ k * s = s * (s⁻¹ * u ^ k * s) := by group
      _ = s * (s * u ^ k * s⁻¹) := by rw [hs']
      _ = s * (u ^ k)⁻¹ := by rw [h2]
  have h3 : u ^ (2 * k + 1) = 1 := h
  calc u ^ k * s * (u ^ k)⁻¹ = s * (u ^ k)⁻¹ * (u ^ k)⁻¹ := by rw [h1]
    _ = s * u * (u ^ (2 * k + 1))⁻¹ := by group
    _ = s * u := by rw [h3]; simp
    _ = t := by rw [hu, ← mul_assoc, hs, one_mul]

theorem prod_ofFn_mul_self {G : Type*} [Group G] : ∀ (n : ℕ) (x : Fin n → G) (a : Fin n → ℕ),
    (∀ i, x i * x i = 1) → (∀ i j, x i * x j = x j * x i) →
      (List.ofFn fun i => x i ^ a i).prod * (List.ofFn fun i => x i ^ a i).prod = 1
  | 0, x, a, _, _ => by simp
  | n + 1, x, a, hsq, hcomm => by
    rw [List.ofFn_succ, List.prod_cons]
    set Q := (List.ofFn fun i : Fin n => x i.succ ^ a i.succ).prod with hQ
    have hQ2 : Q * Q = 1 :=
      prod_ofFn_mul_self n (fun i => x i.succ) (fun i => a i.succ) (fun i => hsq _)
        (fun i j => hcomm _ _)
    have hc : Commute (x 0 ^ a 0) Q := by
      refine Commute.list_prod_right _ _ (fun y hy => ?_)
      obtain ⟨z, hz⟩ := List.mem_ofFn.1 hy
      rw [← hz]
      exact Commute.pow_pow (hcomm 0 z.succ) _ _
    have hx : x 0 ^ a 0 * x 0 ^ a 0 = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      have : x 0 ^ 2 = 1 := by rw [pow_two]; exact hsq 0
      rw [this, one_pow]
    calc x 0 ^ a 0 * Q * (x 0 ^ a 0 * Q) = x 0 ^ a 0 * (Q * x 0 ^ a 0) * Q := by
          simp only [mul_assoc]
      _ = x 0 ^ a 0 * (x 0 ^ a 0 * Q) * Q := by rw [← hc.eq]
      _ = (x 0 ^ a 0 * x 0 ^ a 0) * (Q * Q) := by simp only [mul_assoc]
      _ = 1 := by rw [hx, hQ2, one_mul]

theorem prod_ofFn_four_eq {G : Type*} [Group G] (e : Fin 4 → G) (a : Fin 4 → Fin 2) :
    (List.ofFn fun i => e i ^ (a i : ℕ)).prod =
      e 0 ^ (a 0 : ℕ) * (e 1 ^ (a 1 : ℕ) * (e 2 ^ (a 2 : ℕ) * e 3 ^ (a 3 : ℕ))) := by
  simp [List.ofFn_succ, List.prod_cons]

structure FusData where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  o0 : Nat
  o1 : Nat
  o2 : Nat
  o3 : Nat
  sregs : List Nat
  n1s : List Nat
  n2s : List Nat
  tests : List Nat

section Check

variable {M V : Type} (O : Ops M V)

@[expose] def fusTest (x0 y s : M) (n1 n2 : Nat) : Bool :=
  O.eq (O.mul s s) O.one && decide (n1 % 2 = 1) && decide (n2 % 2 = 1) &&
    O.eq (O.pow (O.mul s x0) n1) O.one && O.eq (O.pow (O.mul s y) n2) O.one

@[expose] def fusCheck [Inhabited M] (D : FusData) : Bool :=
  let R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs)
  let xs := [R[D.o0]!, R[D.o1]!, R[D.o2]!, R[D.o3]!]
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.o0 < D.nregs) &&
    decide (D.o1 < D.nregs) && decide (D.o2 < D.nregs) && decide (D.o3 < D.nregs) &&
    xs.all (fun X => O.eq (O.mul X X) O.one) && O.commsOK xs &&
    O.kerModOK O.one xs D.tests &&
    (List.range 15).all fun k =>
      decide (D.sregs.getD k 0 < D.nregs) &&
        fusTest O R[D.o0]! (prodBase2 O xs (k + 1)) R[D.sregs.getD k 0]! (D.n1s.getD k 0)
          (D.n2s.getD k 0)

end Check

section Spec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem exists_of_fusCheck [Inhabited M] (D : FusData) (h : fusCheck O D = true) :
    ∃ e : Fin 4 → (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      (∀ i, e i * e i = 1) ∧ (∀ i j, e i * e j = e j * e i) ∧
      (∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => e i ^ (a i : ℕ)).prod ≠ 1) ∧
      ∀ a : Fin 4 → Fin 2, a ≠ 0 →
        ∃ g : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
          g * e 0 * g⁻¹ = (List.ofFn fun i => e i ^ (a i : ℕ)).prod := by
  classical
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  have hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  unfold fusCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hprog⟩, hlt0⟩, hlt1⟩, hlt2⟩, hlt3⟩, hsq⟩, hcomm⟩, hker⟩, hfus⟩ := h
  obtain ⟨hs0, hok0⟩ := Sp.initRegs_ok S hA hB D.nregs
  obtain ⟨hs, hok⟩ := Sp.run_ok S D.prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs) with hR
  rw [hs0] at hs
  have hreg : ∀ r, r < D.nregs → Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S :=
    fun r hr => hok r (by rw [hs]; exact hr)
  set xs : List M := [R[D.o0]!, R[D.o1]!, R[D.o2]!, R[D.o3]!] with hxs
  have hxsWF : ∀ X ∈ xs, Sp.WF X := by
    intro X hX
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact (hreg _ hlt0).1
    · exact (hreg _ hlt1).1
    · exact (hreg _ hlt2).1
    · exact (hreg _ hlt3).1
  have hxsS : ∀ X ∈ xs, Sp.toMat X ∈ S := by
    intro X hX
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact (hreg _ hlt0).2
    · exact (hreg _ hlt1).2
    · exact (hreg _ hlt2).2
    · exact (hreg _ hlt3).2
  have hlen4 : xs.length = 4 := rfl
  have hlt : ∀ i : Fin 4, (i : ℕ) < xs.length := fun i => by rw [hlen4]; exact i.isLt
  let m : Fin 4 → Matrix (Fin d) (Fin d) (ZMod p) := fun i => Sp.toMat (xs[(i : ℕ)]'(hlt i))
  have hmS : ∀ i, m i ∈ S := fun i => hxsS _ (List.getElem_mem _)
  have hsqm : ∀ i, m i * m i = 1 := by
    intro i
    have hX := hxsWF _ (List.getElem_mem (hlt i))
    have := Sp.toMat_eq (Sp.mul_wf hX hX) Sp.one_wf
      (List.all_eq_true.1 hsq _ (List.getElem_mem (hlt i)))
    rwa [Sp.toMat_mul hX hX, Sp.toMat_one] at this
  have h2 : ∀ i, (⟨m i, hmS i⟩ : S) ^ 2 = 1 := fun i =>
    Subtype.ext (by simpa [sq] using hsqm i)
  let e : Fin 4 → Sˣ := fun i => Units.ofPowEqOne _ 2 (h2 i) (by norm_num)
  let f : Sˣ →* Matrix (Fin d) (Fin d) (ZMod p) := S.subtype.comp (Units.coeHom S)
  have hfinj : ∀ a b : Sˣ, f a = f b → a = b := fun a b hab => Units.ext (Subtype.ext hab)
  have hfe : ∀ i, f (e i) = m i := fun i => rfl
  have hsq' : ∀ i, e i * e i = 1 := by
    intro i
    have := Units.pow_ofPowEqOne (h2 i) (by norm_num : 2 ≠ 0)
    rwa [sq] at this
  have hpair := Sp.pairwise_of_commsOK hxsWF hcomm
  have hcomm' : ∀ i j, e i * e j = e j * e i := by
    intro i j
    apply hfinj
    rw [map_mul, map_mul, hfe, hfe]
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact List.pairwise_iff_getElem.1 hpair i j (hlt i) (hlt j) hij
    · rfl
    · exact (List.pairwise_iff_getElem.1 hpair j i (hlt j) (hlt i) hij).symm
  have hlist : ∀ a : Fin 4 → Fin 2, f (List.ofFn fun i => e i ^ (a i : ℕ)).prod =
      (List.ofFn fun i : Fin xs.length => Sp.toMat xs[i] ^ (a i : ℕ)).prod := fun a =>
    map_prod_ofFn_pow f (fun i : Fin xs.length => e i)
      (fun i : Fin xs.length => Sp.toMat xs[i]) (fun i => hfe i) a
  refine ⟨e, hsq', hcomm', ?_, ?_⟩
  · intro a ha h1
    have key := (Sp.ne_of_kerModOK Sp.one_wf hxsWF hker a ha).1
    apply key
    rw [← hlist a, h1, map_one]
  · intro a ha
    have hn0 : enc2 _ (a : Fin xs.length → Fin 2) ≠ 0 :=
      fun h0 => ha (eq_zero_of_enc2_eq_zero _ _ h0)
    have hnlt := enc2_lt _ (a : Fin xs.length → Fin 2)
    have hn16 : enc2 _ (a : Fin xs.length → Fin 2) < 16 := by
      simpa [hlen4] using hnlt
    set k : ℕ := enc2 _ (a : Fin xs.length → Fin 2) - 1 with hk
    have hk15 : k < 15 := by omega
    have hk1 : k + 1 = enc2 _ (a : Fin xs.length → Fin 2) := by omega
    have hk' := List.all_eq_true.1 hfus k (List.mem_range.2 hk15)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk'
    obtain ⟨hsr, htest⟩ := hk'
    unfold fusTest at htest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
    obtain ⟨⟨⟨⟨hss, hodd1⟩, hodd2⟩, hp1⟩, hp2⟩ := htest
    obtain ⟨wS, mS⟩ := hreg _ hsr
    have hX0 := hxsWF _ (List.getElem_mem (hlt 0))
    obtain ⟨wP, hP⟩ := prodBase2_spec Sp xs hxsWF a
    rw [hk1] at hp2
    have hx0 : Sp.toMat R[D.o0]! = m 0 := rfl
    have hwx0 : Sp.WF R[D.o0]! := (hreg _ hlt0).1
    have hSS : Sp.toMat R[D.sregs.getD k 0]! * Sp.toMat R[D.sregs.getD k 0]! = 1 := by
      have := Sp.toMat_eq (Sp.mul_wf wS wS) Sp.one_wf hss
      rwa [Sp.toMat_mul wS wS, Sp.toMat_one] at this
    have h2s : (⟨Sp.toMat R[D.sregs.getD k 0]!, mS⟩ : S) ^ 2 = 1 :=
      Subtype.ext (by simpa [sq] using hSS)
    let us : Sˣ := Units.ofPowEqOne _ 2 h2s (by norm_num)
    have hfus' : f us = Sp.toMat R[D.sregs.getD k 0]! := rfl
    have hus : us * us = 1 := by
      have := Units.pow_ofPowEqOne h2s (by norm_num : 2 ≠ 0)
      rwa [sq] at this
    set y : Sˣ := (List.ofFn fun i => e i ^ (a i : ℕ)).prod with hy
    have hyy : y * y = 1 := prod_ofFn_mul_self 4 e (fun i => (a i : ℕ)) hsq' hcomm'
    have hfy : f y = Sp.toMat (prodBase2 O xs (enc2 _ (a : Fin xs.length → Fin 2))) := by
      rw [hy, hlist a]
      exact hP.symm
    obtain ⟨wp1, mp1⟩ := Sp.pow_spec (Sp.mul_wf wS hwx0) (D.n1s.getD k 0)
    have e1 := Sp.toMat_eq wp1 Sp.one_wf hp1
    rw [mp1, Sp.toMat_mul wS hwx0, Sp.toMat_one] at e1
    obtain ⟨wp2, mp2⟩ := Sp.pow_spec (Sp.mul_wf wS wP) (D.n2s.getD k 0)
    have e2 := Sp.toMat_eq wp2 Sp.one_wf hp2
    rw [mp2, Sp.toMat_mul wS wP, Sp.toMat_one] at e2
    have hu1 : (us * e 0) ^ (D.n1s.getD k 0) = 1 := by
      apply hfinj
      rw [map_pow, map_mul, hfus', hfe, map_one]
      exact e1
    have hu2 : (us * y) ^ (D.n2s.getD k 0) = 1 := by
      apply hfinj
      rw [map_pow, map_mul, hfus', hfy, map_one]
      exact e2
    obtain ⟨g1, hg1⟩ := conj_of_odd_pow hus (hsq' 0) hodd1 hu1
    obtain ⟨g2, hg2⟩ := conj_of_odd_pow hus hyy hodd2 hu2
    refine ⟨g2 * g1⁻¹, ?_⟩
    rw [← hg2, ← hg1]
    group

end Spec

open CFSG CFSG.GH74 CFSG.GH74.KGroups Subgroup in
theorem not_gen4_cover_of_fused_E16 {J : Type} [Group J]
    (hE : ∃ e : Fin 4 → J, (∀ i, e i * e i = 1) ∧ (∀ i j, e i * e j = e j * e i) ∧
      (∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => e i ^ (a i : ℕ)).prod ≠ 1) ∧
      ∀ a : Fin 4 → Fin 2, a ≠ 0 →
        ∃ g : J, g * e 0 * g⁻¹ = (List.ofFn fun i => e i ^ (a i : ℕ)).prod)
    (K : Type) [Group K] [Finite K] (hK : IsQuasisimple K) (hZ2 : IsPGroup 2 ↥(center K))
    (h : Nonempty (K ⧸ center K ≃* J)) (hZ : center K ≠ ⊥) : ¬ Gen4 K := by
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  have hJ := center_quotient_eq_bot hperf hsimple
  obtain ⟨eJ⟩ := h
  obtain ⟨e, hsq, hcomm, hker, hconj⟩ := hE
  obtain ⟨E, hEcard, hE2, heE, hEconj⟩ := exists_E16 (G := J) e hsq hcomm hker hconj
  have hk : ∀ a : Fin 4 → Fin 2, a ≠ 0 →
      e 0 ^ (a 0 : ℕ) * (e 1 ^ (a 1 : ℕ) * (e 2 ^ (a 2 : ℕ) * e 3 ^ (a 3 : ℕ))) ≠ 1 :=
    fun a ha => by
      rw [← prod_ofFn_four_eq]
      exact hker a ha
  exact not_genLE4_of_double_cover hperf hZ2 hZ hJ (fun C _ _ hC ⟨eC⟩ =>
    not_genLE4_double_cover hC (⊤ : Subgroup J) ((eC.trans eJ).trans Subgroup.topEquiv.symm) E
      le_top hEcard hE2 (e 0)
      (fun x hx hx1 => let ⟨g, hg⟩ := hEconj x hx hx1; ⟨g, Subgroup.mem_top g, hg⟩)
      (e 0) (e 1) (e 2) (heE 0) (heE 1) (heE 2)
      (by simpa using hk ![1, 0, 0, 0] (by decide))
      (by simpa using hk ![0, 1, 0, 0] (by decide))
      (by simpa using hk ![0, 0, 1, 0] (by decide))
      (by simpa using hk ![1, 1, 0, 0] (by decide))
      (by simpa using hk ![1, 0, 1, 0] (by decide))
      (by simpa using hk ![0, 1, 1, 0] (by decide))
      (by simpa using hk ![1, 1, 1, 0] (by decide)))

end CFSG.GH74.Generic.Fusion
