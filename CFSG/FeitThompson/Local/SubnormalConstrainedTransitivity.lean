module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.IsPerfect
public import CFSG.FeitThompson.Local.ConstrainedTransitivityPrimeIndexExtension
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreOvergroups
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsOfPGroups

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G]

private theorem normal_subgroupOf_map_subtype {P : Subgroup G} {X Y : Subgroup ↥P} (hXY : X ≤ Y)
    (h : (X.subgroupOf Y).Normal) :
    ((X.map P.subtype).subgroupOf (Y.map P.subtype)).Normal := by
  have hYX : Y ≤ normalizer (X : Set ↥P) := (normal_subgroupOf_iff_le_normalizer hXY).1 h
  refine (normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hXY)).2 ?_
  rintro g ⟨y, hy, rfl⟩
  have hyn := Subgroup.mem_normalizer_iff.1 (hYX hy)
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨y * x * y⁻¹, (hyn x).1 hx, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  · rintro ⟨x, hx, hxe⟩
    refine ⟨y⁻¹ * x * y, ?_, ?_⟩
    · refine (hyn (y⁻¹ * x * y)).2 ?_
      have hg : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
      rwa [hg]
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hxe ⊢
      rw [hxe]
      group

private theorem normal_subgroupOf_subgroupOf {B X Y : Subgroup G} (hXY : X ≤ Y)
    (h : (X.subgroupOf Y).Normal) :
    ((X.subgroupOf B).subgroupOf (Y.subgroupOf B)).Normal := by
  have hY : Y ≤ normalizer (X : Set G) := (normal_subgroupOf_iff_le_normalizer hXY).1 h
  refine (normal_subgroupOf_iff_le_normalizer
    (fun x hx => Subgroup.mem_subgroupOf.2 (hXY (Subgroup.mem_subgroupOf.1 hx)))).2 ?_
  intro y hy
  have hyG : (y : G) ∈ normalizer (X : Set G) := hY (Subgroup.mem_subgroupOf.1 hy)
  rw [Subgroup.mem_normalizer_iff] at hyG ⊢
  intro b
  simpa [Subgroup.mem_subgroupOf] using hyG (b : G)

theorem le_of_chain_le_succ {m : ℕ} {C : ℕ → Subgroup G} (hmono : ∀ i < m, C i ≤ C (i + 1)) :
    ∀ b ≤ m, ∀ a ≤ b, C a ≤ C b := by
  intro b
  induction b with
  | zero => intro _ a ha; simp [Nat.le_zero.1 ha]
  | succ b ih =>
    intro hb a ha
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ha) with h | h
    · exact (ih (Nat.le_of_succ_le hb) a (Nat.lt_succ_iff.1 h)).trans
        (hmono b (Nat.lt_of_succ_le hb))
    · exact h ▸ le_rfl

theorem isSubnormal_subgroupOf_of_chain {A P : Subgroup G} {m : ℕ} {C : ℕ → Subgroup G}
    (hC0 : C 0 = A) (hCm : C m = P) (hmono : ∀ i < m, C i ≤ C (i + 1))
    (hnorm : ∀ i < m, ((C i).subgroupOf (C (i + 1))).Normal) :
    (A.subgroupOf P).IsSubnormal := by
  have hle := le_of_chain_le_succ hmono
  refine Subgroup.IsSubnormal.isSubnormal_iff.2
    ⟨m, fun i => (C (min i m)).subgroupOf P, ?_, ?_, ?_, ?_⟩
  · intro i j hij x hx
    exact Subgroup.mem_subgroupOf.2
      (hle _ (min_le_right _ _) _ (min_le_min hij le_rfl) (Subgroup.mem_subgroupOf.1 hx))
  · intro i
    rcases lt_or_ge i m with hi | hi
    · change (((C (min i m)).subgroupOf P).subgroupOf
        ((C (min (i + 1) m)).subgroupOf P)).Normal
      rw [min_eq_left hi.le, min_eq_left (Nat.succ_le_of_lt hi)]
      exact normal_subgroupOf_subgroupOf (hmono i hi) (hnorm i hi)
    · change (((C (min i m)).subgroupOf P).subgroupOf
        ((C (min (i + 1) m)).subgroupOf P)).Normal
      rw [min_eq_right hi, min_eq_right (hi.trans (Nat.le_succ i)), Subgroup.subgroupOf_self]
      infer_instance
  · change (C (min 0 m)).subgroupOf P = A.subgroupOf P
    rw [Nat.zero_min, hC0]
  · change (C (min m m)).subgroupOf P = ⊤
    rw [min_self, hCm, Subgroup.subgroupOf_self]

theorem exists_chain_of_isSubnormal_subgroupOf {A P : Subgroup G} (hAP : A ≤ P)
    (h : (A.subgroupOf P).IsSubnormal) :
    ∃ (m : ℕ) (C : ℕ → Subgroup G), C 0 = A ∧ C m = P ∧ (∀ i < m, C i ≤ C (i + 1)) ∧
      (∀ i ≤ m, C i ≤ P) ∧ ∀ i < m, ((C i).subgroupOf (C (i + 1))).Normal := by
  obtain ⟨n, f, hmono, hnorm, hf0, hfn⟩ := Subgroup.IsSubnormal.isSubnormal_iff.1 h
  refine ⟨n, fun i => (f i).map P.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · change (f 0).map P.subtype = A
    rw [hf0, Subgroup.map_subgroupOf_eq_of_le hAP]
  · change (f n).map P.subtype = P
    rw [hfn, ← Subgroup.subgroupOf_self P, Subgroup.map_subgroupOf_eq_of_le le_rfl]
  · exact fun i _ => Subgroup.map_mono (hmono (Nat.le_succ i))
  · exact fun i _ => Subgroup.map_subtype_le _
  · exact fun i _ => normal_subgroupOf_map_subtype (hmono (Nat.le_succ i)) (hnorm i)

theorem isSubnormal_subgroupOf_iff_exists_chain {A P : Subgroup G} (hAP : A ≤ P) :
    (A.subgroupOf P).IsSubnormal ↔
      ∃ (m : ℕ) (C : ℕ → Subgroup G), C 0 = A ∧ C m = P ∧ (∀ i < m, C i ≤ C (i + 1)) ∧
        ∀ i < m, ((C i).subgroupOf (C (i + 1))).Normal :=
  ⟨fun h => by
      obtain ⟨m, C, h0, hm, hmono, -, hnorm⟩ := exists_chain_of_isSubnormal_subgroupOf hAP h
      exact ⟨m, C, h0, hm, hmono, hnorm⟩,
    fun ⟨_, _, h0, hm, hmono, hnorm⟩ => isSubnormal_subgroupOf_of_chain h0 hm hmono hnorm⟩

private theorem normal_subgroupOf_of_le_of_le {A B D : Subgroup G} (hAD : A ≤ D) (hDB : D ≤ B)
    (h : (A.subgroupOf B).Normal) : (A.subgroupOf D).Normal :=
  (normal_subgroupOf_iff_le_normalizer hAD).2
    (hDB.trans ((normal_subgroupOf_iff_le_normalizer (hAD.trans hDB)).1 h))

variable [Finite G]

private theorem natCard_lt_natCard_of_lt {H K : Subgroup G} (h : H < K) :
    Nat.card H < Nat.card K := by
  rcases lt_or_eq_of_le (Subgroup.card_le_of_le h.le) with h2 | h2
  · exact h2
  · exact absurd (Subgroup.eq_of_le_of_card_ge h.le h2.ge) h.ne

theorem exists_normal_index_prime (T : Type*) [Group T] [Finite T] [Nontrivial T]
    [Group.IsSolvable T] : ∃ M : Subgroup T, M.Normal ∧ (M.index).Prime := by
  have hC : commutator T ≠ ⊤ := fun h => by
    have : Group.IsPerfect T := ⟨h⟩
    exact Group.IsPerfect.not_isSolvable (G := T) inferInstance
  obtain ⟨M, hM, hCM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (commutator T)).resolve_left hC
  have hMn : M.Normal := Subgroup.Normal.of_commutator_le T hCM
  have _ : IsMulCommutative (T ⧸ M) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.2 hCM
  exact ⟨M, hMn, Subgroup.index_eq_card M ▸
    Group.is_simple_iff_prime_card.1 (isSimpleGroup_quotient_of_isCoatom hM)⟩

theorem exists_normal_relIndex_prime {B P : Subgroup G} [Group.IsSolvable ↥P]
    (hBP : B ≤ P) (hne : B ≠ P) (hn : (B.subgroupOf P).Normal) :
    ∃ E : Subgroup G, B ≤ E ∧ E ≤ P ∧ (E.subgroupOf P).Normal ∧ (E.relIndex P).Prime := by
  have hDtop : B.subgroupOf P ≠ ⊤ :=
    fun h => hne (le_antisymm hBP (Subgroup.subgroupOf_eq_top.1 h))
  have hnt : Nontrivial (↥P ⧸ B.subgroupOf P) := QuotientGroup.nontrivial_iff.mpr hDtop
  obtain ⟨M, hMn, hMp⟩ := exists_normal_index_prime (↥P ⧸ B.subgroupOf P)
  set N : Subgroup ↥P := M.comap (QuotientGroup.mk' (B.subgroupOf P)) with hN
  have hNn : N.Normal := hMn.comap _
  have hDN : B.subgroupOf P ≤ N := fun x hx => by
    simp only [hN, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).2 hx, one_mem]
  have hNi : N.index = M.index :=
    Subgroup.index_comap_of_surjective M (QuotientGroup.mk'_surjective _)
  have hself : (N.map P.subtype).subgroupOf P = N :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective N
  refine ⟨N.map P.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · calc B = (B.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le hBP).symm
      _ ≤ _ := Subgroup.map_mono hDN
  · rw [hself]; exact hNn
  · change ((N.map P.subtype).subgroupOf P).index.Prime
    rw [hself, hNi]; exact hMp

private theorem constrainedTransitive_normal_aux [IsSimpleGroup G] (hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A : Subgroup G} {q : ℕ}
    (hAbot : ⊥ < A) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    ∀ n : ℕ, ∀ B : Subgroup G, Nat.card B ≤ n → A ≤ B → B < ⊤ →
      IsPiSubgroup (subgroupPrimeSupport A) B → (A.subgroupOf B).Normal →
      maximalNormalizedPSubgroups B q ⊆ maximalNormalizedPSubgroups A q ∧
        ∀ Q₁ ∈ maximalNormalizedPSubgroups B q, ∀ Q₂ ∈ maximalNormalizedPSubgroups B q,
          ∃ c ∈ constrainedCentralizerCore B, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂ := by
  intro n
  induction n with
  | zero =>
    intro B hcard
    have := Nat.card_pos (α := ↥B)
    omega
  | succ n ih =>
    intro B hcard hAB hBtop hB hn
    rcases eq_or_ne A B with rfl | hne
    · exact ⟨subset_rfl, hconj⟩
    have hsolvB : Group.IsSolvable ↥B := hsolv B hBtop.ne
    obtain ⟨E, hAE, hEB, hEn, hEp⟩ := exists_normal_relIndex_prime hAB hne hn
    have hEneB : E ≠ B := fun h => by
      rw [h, Subgroup.relIndex_self] at hEp
      exact hEp.one_lt.ne' rfl
    have hEltB : E < B := lt_of_le_of_ne hEB hEneB
    have hEtop : E < ⊤ := hEltB.trans hBtop
    have hEπ : IsPiSubgroup (subgroupPrimeSupport A) E := hB.of_le hEB
    have hπE : subgroupPrimeSupport E = subgroupPrimeSupport A :=
      subgroupPrimeSupport_eq_of_isPiSubgroup hAE hEπ
    have hconE : IsConstrained E := hcon.of_le_of_isPiSubgroup hAE hEπ
    have hEbot : ⊥ < E := hAbot.trans_le hAE
    obtain ⟨hsubE, hconjE⟩ := ih E (Nat.lt_succ_iff.1
      (lt_of_lt_of_le (natCard_lt_natCard_of_lt hEltB) hcard)) hAE hEtop hEπ
      (normal_subgroupOf_of_le_of_le hAE hEB hn)
    have hrπ : E.relIndex B ∈ subgroupPrimeSupport E := by
      rw [hπE, ← subgroupPrimeSupport_eq_of_isPiSubgroup hAB hB]
      exact mem_subgroupPrimeSupport_iff.2 (Nat.mem_primeFactors.2
        ⟨hEp, Subgroup.index_dvd_card (E.subgroupOf B), Nat.card_pos.ne'⟩)
    have hBπE : IsPiSubgroup (subgroupPrimeSupport E) B := hπE ▸ hB
    have hqπE : q ∉ subgroupPrimeSupport E := hπE ▸ hqπ
    exact ⟨(maximalNormalizedPSubgroups_subset_of_normal_of_relIndex_prime hG hsolv hconE hq
        hqπE hEB hBπE hEn rfl hrπ hconjE).trans hsubE,
      exists_mem_constrainedCentralizerCore_conj_smul_eq hG hsolv hEbot hEtop hconE hq
        hqπE hEB hBπE hEn rfl hrπ hconjE⟩

theorem isConstrainedTransitive_of_normal [IsSimpleGroup G] (hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A B : Subgroup G} {q : ℕ}
    (hAbot : ⊥ < A) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAB : A ≤ B) (hBtop : B < ⊤)
    (hB : IsPiSubgroup (subgroupPrimeSupport A) B) (hn : (A.subgroupOf B).Normal)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    maximalNormalizedPSubgroups B q ⊆ maximalNormalizedPSubgroups A q ∧
      ∀ Q₁ ∈ maximalNormalizedPSubgroups B q, ∀ Q₂ ∈ maximalNormalizedPSubgroups B q,
        ∃ c ∈ constrainedCentralizerCore B, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂ :=
  constrainedTransitive_normal_aux hG hsolv hAbot hcon hq hqπ hconj (Nat.card B) B le_rfl hAB
    hBtop hB hn

private theorem constrainedTransitive_subnormal_aux [IsSimpleGroup G] (hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A P : Subgroup G} {q : ℕ}
    (hAbot : ⊥ < A) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P) (hPtop : P < ⊤)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hsn : (A.subgroupOf P).IsSubnormal)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    maximalNormalizedPSubgroups P q ⊆ maximalNormalizedPSubgroups A q ∧
      ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
        ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂ := by
  obtain ⟨m, C, hC0, hCm, hmono, hCP, hnorm⟩ := exists_chain_of_isSubnormal_subgroupOf hAP hsn
  have hAC : ∀ i ≤ m, A ≤ C i :=
    fun i hi => hC0 ▸ le_of_chain_le_succ hmono i hi 0 (Nat.zero_le i)
  have key : ∀ i ≤ m,
      maximalNormalizedPSubgroups (C i) q ⊆ maximalNormalizedPSubgroups A q ∧
        ∀ Q₁ ∈ maximalNormalizedPSubgroups (C i) q, ∀ Q₂ ∈ maximalNormalizedPSubgroups (C i) q,
          ∃ c ∈ constrainedCentralizerCore (C i),
            (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂ := by
    intro i
    induction i with
    | zero => intro _; rw [hC0]; exact ⟨subset_rfl, hconj⟩
    | succ i ih =>
      intro hi
      have hi' : i ≤ m := Nat.le_of_succ_le hi
      obtain ⟨hsub, hcj⟩ := ih hi'
      have hAi : A ≤ C i := hAC i hi'
      have hCiπ : IsPiSubgroup (subgroupPrimeSupport A) (C i) := hP.of_le (hCP i hi')
      have hπi : subgroupPrimeSupport (C i) = subgroupPrimeSupport A :=
        subgroupPrimeSupport_eq_of_isPiSubgroup hAi hCiπ
      obtain ⟨h1, h2⟩ := isConstrainedTransitive_of_normal hG hsolv (hAbot.trans_le hAi)
        (hcon.of_le_of_isPiSubgroup hAi hCiπ) hq (hπi ▸ hqπ)
        (hmono i (Nat.lt_of_succ_le hi)) (lt_of_le_of_lt (hCP (i + 1) hi) hPtop)
        (hπi ▸ hP.of_le (hCP (i + 1) hi)) (hnorm i (Nat.lt_of_succ_le hi)) hcj
      exact ⟨h1.trans hsub, h2⟩
  rw [← hCm]
  exact key m le_rfl

theorem maximalNormalizedPSubgroups_subset_of_isSubnormal [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {A P : Subgroup G} {q : ℕ} (hAbot : ⊥ < A) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P) (hPtop : P < ⊤)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hsn : (A.subgroupOf P).IsSubnormal)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    maximalNormalizedPSubgroups P q ⊆ maximalNormalizedPSubgroups A q :=
  (constrainedTransitive_subnormal_aux hG hsolv hAbot hcon hq hqπ hAP hPtop hP hsn hconj).1

theorem exists_mem_constrainedCentralizerCore_conj_smul_eq_of_isSubnormal [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {A P : Subgroup G} {q : ℕ} (hAbot : ⊥ < A) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P) (hPtop : P < ⊤)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hsn : (A.subgroupOf P).IsSubnormal)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
      ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂ :=
  (constrainedTransitive_subnormal_aux hG hsolv hAbot hcon hq hqπ hAP hPtop hP hsn hconj).2

theorem isConstrainedTransitive_of_isSubnormal
    (_hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A P : Subgroup G} {q : ℕ}
    (hAbot : ⊥ < A) (_hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P) (hPtop : P < ⊤)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hsn : (A.subgroupOf P).IsSubnormal)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    maximalNormalizedPSubgroups P q ⊆ maximalNormalizedPSubgroups A q ∧
      ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
        ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂ :=
  have := hsimple
  constrainedTransitive_subnormal_aux hG hsolv hAbot hcon hq hqπ hAP hPtop hP hsn hconj

end

end CFSG.FeitThompson
