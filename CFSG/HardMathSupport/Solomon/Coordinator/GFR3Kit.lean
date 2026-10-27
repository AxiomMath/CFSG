module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Subgroup CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem gfr3_oPrime_bot_of_class {G : Type*} [Group G] [Finite G] {C : Subgroup G} {a e f : ℕ}
    (hC : Nat.card C = 3 ^ a * (2 ^ e * 5 ^ f))
    (h2 : ∀ w ∈ C, orderOf w = 2 →
      Nat.card ↥(C ⊓ Subgroup.centralizer ({w} : Set G)) * 2 ^ e < Nat.card C)
    (h5 : ∀ w ∈ C, orderOf w = 5 →
      Nat.card ↥(C ⊓ Subgroup.centralizer ({w} : Set G)) * (2 ^ e * 5 ^ f) < Nat.card C) :
    GLAPPrimeCoreOf 3 C = ⊥ := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  by_contra hL
  set L := GLAPPrimeCoreOf 3 C with hLdef
  have hLC : L ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime 3 (Nat.card L) := coprime_card_GLAPPrimeCoreOf hp3 C
  have hLr : Nat.card L ∣ 2 ^ e * 5 ^ f := by
    have h1 : Nat.card L ∣ 3 ^ a * (2 ^ e * 5 ^ f) := hC ▸ Subgroup.card_dvd_of_le hLC
    exact (Nat.Coprime.pow_left a hcop).symm.dvd_of_dvd_mul_left h1
  have hLne : Nat.card L ≠ 1 := fun h => hL (Subgroup.card_eq_one.1 h)
  have key : ∀ w ∈ L, Nat.card C ≤
      Nat.card ↥(C ⊓ Subgroup.centralizer ({w} : Set G)) * Nat.card L := by
    intro w hwL
    have hcls : conjClass C w ⊆ (L : Set G) := by
      rintro _ ⟨g, hg, rfl⟩
      exact GLAPPrimeCoreOf_conj_mem g hg w hwL
    have hncard : (conjClass C w).ncard ≤ Nat.card L := by
      calc (conjClass C w).ncard ≤ (L : Set G).ncard :=
            Set.ncard_le_ncard hcls (Set.toFinite _)
        _ = Nat.card L := (Nat.card_coe_set_eq (L : Set G)).symm
    have horb := ncard_conjClass_mul_card C w
    rw [← horb, mul_comm]
    exact Nat.mul_le_mul_left _ hncard
  have hLpos : 0 < 2 ^ e * 5 ^ f := by positivity
  have hLle : Nat.card L ≤ 2 ^ e * 5 ^ f := Nat.le_of_dvd hLpos hLr
  by_cases h5L : 5 ∣ Nat.card L
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 5 h5L
    have hwo : orderOf (x : G) = 5 := by rw [Subgroup.orderOf_coe, hx]
    have hwL : (x : G) ∈ L := x.2
    have h1 := key _ hwL
    have h2' := h5 _ (hLC hwL) hwo
    have h3 : Nat.card ↥(C ⊓ Subgroup.centralizer ({(x : G)} : Set G)) * Nat.card L ≤
        Nat.card ↥(C ⊓ Subgroup.centralizer ({(x : G)} : Set G)) * (2 ^ e * 5 ^ f) :=
      Nat.mul_le_mul_left _ hLle
    omega
  · have hc5 : Nat.Coprime (Nat.card L) (5 ^ f) :=
      Nat.Coprime.pow_right f ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).2
        h5L).symm
    have hL2 : Nat.card L ∣ 2 ^ e := hc5.dvd_of_dvd_mul_right hLr
    have hL2le : Nat.card L ≤ 2 ^ e := Nat.le_of_dvd (by positivity) hL2
    obtain ⟨k, hk, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hL2
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hLne (by simpa using hk2)
    have h2L : 2 ∣ Nat.card L := by
      rw [hk2]
      exact dvd_pow_self 2 hk0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 h2L
    have hwo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe, hx]
    have hwL : (x : G) ∈ L := x.2
    have h1 := key _ hwL
    have h2' := h2 _ (hLC hwL) hwo
    have h3 : Nat.card ↥(C ⊓ Subgroup.centralizer ({(x : G)} : Set G)) * Nat.card L ≤
        Nat.card ↥(C ⊓ Subgroup.centralizer ({(x : G)} : Set G)) * 2 ^ e :=
      Nat.mul_le_mul_left _ hL2le
    omega

@[expose] def gfr3CommCount (n : ℕ) (pts : Array (Array ℕ)) (w : Array ℕ) : ℕ :=
  ((Finset.range pts.size).filter fun j => commA n pts[j]! w = true).card

@[expose] def gfr3ClassOK (n : ℕ) (pts : Array (Array ℕ)) (N e f : ℕ) : Bool :=
  allLt pts.size fun i =>
    (!(eqA n (powArr n pts[i]! 2) (idA n)) || eqA n pts[i]! (idA n) ||
      decide (gfr3CommCount n pts pts[i]! * 2 ^ e < N)) &&
    (!(eqA n (powArr n pts[i]! 5) (idA n)) || eqA n pts[i]! (idA n) ||
      decide (gfr3CommCount n pts pts[i]! * (2 ^ e * 5 ^ f) < N))

theorem gfr3_classOK_spec {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {N e f : ℕ}
    (hps : ∀ q ∈ ps, q < n) (hc : enumOK n gs ps c = true) (h : gfr3ClassOK n c.pts N e f = true)
    {w : Equiv.Perm (Fin n)} (hw : w ∈ Subgroup.closure (permsA n gs)) :
    (orderOf w = 2 → Nat.card ↥(Subgroup.closure (permsA n gs) ⊓
        Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin n)))) * 2 ^ e < N) ∧
    (orderOf w = 5 → Nat.card ↥(Subgroup.closure (permsA n gs) ⊓
        Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin n)))) * (2 ^ e * 5 ^ f) < N) := by
  obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep hps hc hw
  have hle := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.card_closure_inf_centralizer_le hps hc hrep
  have hcc : ((Finset.range c.pts.size).filter fun j =>
      commA n c.pts[j]! c.pts[i]! = true).card = gfr3CommCount n c.pts c.pts[i]! := rfl
  rw [hcc] at hle
  have h1 := allLt_spec h hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h1
  obtain ⟨h2, h5⟩ := h1
  constructor
  · intro ho
    have hw1 : w ≠ 1 := fun h' => by rw [h', orderOf_one] at ho; omega
    have hw2 : w ^ 2 = 1 := by rw [← ho]; exact pow_orderOf_eq_one w
    rcases h2 with (h2 | h2) | h2
    · exact absurd ((eqA_iff (rep_powArr hrep 2) rep_idA).2 hw2) (by simp [h2])
    · exact absurd ((eqA_iff hrep rep_idA).1 h2) hw1
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) h2
  · intro ho
    have hw1 : w ≠ 1 := fun h' => by rw [h', orderOf_one] at ho; omega
    have hw5 : w ^ 5 = 1 := by rw [← ho]; exact pow_orderOf_eq_one w
    rcases h5 with (h5 | h5) | h5
    · exact absurd ((eqA_iff (rep_powArr hrep 5) rep_idA).2 hw5) (by simp [h5])
    · exact absurd ((eqA_iff hrep rep_idA).1 h5) hw1
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) h5

theorem gfr3_oPrime_subtype {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) (s : ↥P)
    (C : Subgroup (Equiv.Perm (Fin n)))
    (hC : C = Subgroup.centralizer ({(s : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n))) ⊓ P)
    (hO : GLAPPrimeCoreOf 3 C = ⊥) :
    Nat.card ↥(Subgroup.centralizer ({s} : Set ↥P)) = Nat.card C ∧
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set ↥P)) = ⊥ := by
  have hmapC : (Subgroup.centralizer ({s} : Set ↥P)).map P.subtype = C := by
    have hc := map_inf_centralizer_of_injective P.subtype P.subtype_injective ⊤ s
    rw [top_inf_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hc
    rw [hc, hC, inf_comm]
    rfl
  refine ⟨by rw [← hmapC, Subgroup.card_map_of_injective P.subtype_injective], ?_⟩
  have hmap := map_glaPPrimeCoreOf_of_injective 3 P.subtype P.subtype_injective
    (Subgroup.centralizer ({s} : Set ↥P))
  rw [hmapC, hO, ← Subgroup.map_bot P.subtype] at hmap
  exact Subgroup.map_injective P.subtype_injective hmap

theorem gfr3_kit {n : ℕ} (hn : 1 ≤ n) {S : Array (Array ℕ)} (hk : 2 ≤ S.size) {bs : List (Fin n)}
    (hb : bs.Nodup) {W : Array (List ℤ)} {a b : Array ℕ} {A B : Equiv.Perm (Fin n)}
    (ha : Rep n a A) (hb' : Rep n b B) (Q : Subgroup (Equiv.Perm (Fin n)))
    (hQ : Subgroup.closure {A, B} = Q)
    (hchain : caseChainOK2P n S (bs.map Fin.val).toArray W a b = true)
    {rels : List (ℕ × ℕ × ℕ)} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {N e f : ℕ}
    (hps : ∀ q ∈ ps, q < n) (hg0 : 0 < gs.size)
    (hcent : centOKP 3 n S (bs.map Fin.val).toArray gs[0]! rels gs ps c N = true)
    (hord : eqA n (powArr n gs[0]! 3) (idA n) = true) (hne : eqA n gs[0]! (idA n) = false)
    (hN : N = 3 ^ 3 * (2 ^ e * 5 ^ f)) (hclass : gfr3ClassOK n c.pts N e f = true) :
    ∃ (z : Equiv.Perm (Fin n)) (hz : z ∈ Q), orderOf z = 3 ∧
      3 ^ 3 ∣ Nat.card ↥(Subgroup.centralizer ({(⟨z, hz⟩ : ↥Q)} : Set ↥Q)) ∧
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({(⟨z, hz⟩ : ↥Q)} : Set ↥Q)) = ⊥ := by
  subst hQ
  set P : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure {A, B} with hP
  have hv : validA n gs[0]! = true := enumOK_gens_valid (centOKP_enum hcent) hg0
  have hx : Rep n gs[0]! (permOfArr n gs[0]!) := rep_of_validA hv
  set X := permOfArr n gs[0]! with hX
  obtain ⟨hCeq, hCcard⟩ := case_centralizer2P hn hk hb ha hb' hchain hx hps hcent
  have hXC : X ∈ Subgroup.closure (permsA n gs) := Subgroup.subset_closure (mem_permsA hg0)
  have hXP : X ∈ P := (Subgroup.mem_inf.1 (hCeq ▸ hXC)).2
  have hX3 : X ^ 3 = 1 := (eqA_iff (rep_powArr hx 3) rep_idA).1 hord
  have hX1 : X ≠ 1 := fun h => by
    have := (eqA_iff hx rep_idA).2 h
    rw [hne] at this
    exact absurd this (by simp)
  have hXo : orderOf X = 3 := orderOf_eq_prime hX3 hX1
  refine ⟨X, hXP, hXo, ?_⟩
  set s : ↥P := ⟨X, hXP⟩ with hs
  have hOC : GLAPPrimeCoreOf 3 (Subgroup.closure (permsA n gs)) = ⊥ := by
    have hcl : Nat.card ↥(Subgroup.closure (permsA n gs)) = 3 ^ 3 * (2 ^ e * 5 ^ f) := by
      rw [hCcard, hN]
    have hcs := fun {w : Equiv.Perm (Fin n)} (hw : w ∈ Subgroup.closure (permsA n gs)) =>
      gfr3_classOK_spec hps (centOKP_enum hcent) hclass hw
    refine gfr3_oPrime_bot_of_class (a := 3) hcl (fun w hw ho => ?_) (fun w hw ho => ?_)
    · have := (hcs hw).1 ho
      rwa [hCcard]
    · have := (hcs hw).2 ho
      rwa [hCcard]
  obtain ⟨hcardC, hOs⟩ := gfr3_oPrime_subtype P s _ hCeq hOC
  refine ⟨?_, ?_⟩
  · rw [hcardC, hCcard, hN]
    exact Dvd.intro _ rfl
  · exact hOs

end CFSG.HardMathSupport.Solomon.Coordinator
