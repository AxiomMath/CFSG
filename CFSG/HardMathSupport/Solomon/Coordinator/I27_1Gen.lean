module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

set_option linter.unusedSectionVars false

structure I271Hyp (p : ℕ) {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  core : GLAPPrimeCore p X = ⊥
  comp : GLAPComponent p ⊤ K
  catalog : IsCatalogGroup (↥K ⧸ Subgroup.center ↥K)
  scp : IsSCp p ⊤ B
  centralized : B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥
  rank_four : 4 ≤ CFSG.Open.pRank p B
  rank_local : GLATwoLocalRank p X ≤ CFSG.Open.pRank p B

@[expose] def I271CaseA (p : ℕ) {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop :=
  4 ≤ CFSG.Open.pRank p B ∧ IsInGOne p B K

@[expose] def I271CaseC {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop :=
  IsLThreeFour (↥K ⧸ Subgroup.center ↥K) ∧ CFSG.Open.pRank 3 B = 4 ∧ autOrderIn B K = 9 ∧
    InducesInnerIn B K

@[expose] def I271CaseD {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop :=
  IsHatON ↥K ∧ CFSG.Open.pRank 3 B = 4 ∧ autOrderIn B K = 27

@[expose] def I271CaseE {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop :=
  IsFiTwentyTwo ↥K ∧ CFSG.Open.pRank 5 B = 4

@[expose] def I271Concl (p : ℕ) {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop :=
  I271CaseA p K B ∨ IsStronglyBalancedIn p B K ∨ (p = 3 ∧ I271CaseC K B) ∨
    (p = 3 ∧ I271CaseD K B) ∨ (p = 5 ∧ I271CaseE K B)

theorem input27_1At_of_concl {X : Type} [Group X] [Finite X]
    (h : ∀ (p : ℕ) (K B : Subgroup X), I271Hyp p K B → I271Concl p K B) : Input27_1At X :=
  fun p hp hp2 hO K hK hcat B hB hCB h4 hrk =>
    h p K B ⟨hp, hp2, hO, hK, hcat, hB, hCB, h4, hrk⟩

section Elementary

variable {X : Type*} [Group X] [Finite X]

theorem i271_isElemAbelian_of_le {p : ℕ} {A B : Subgroup X} (hB : IsElemAbelian p B) (h : A ≤ B) :
    IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB h

theorem i271_exists_card_eq {p : ℕ} (hp : p.Prime) {B : Subgroup X} (hB : IsElemAbelian p B) :
    ∃ k, Nat.card B = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p B := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hB.2 g g.2)⟩
  exact IsPGroup.iff_card.1 hpg

theorem i271_pRank_eq {p k : ℕ} (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ k) : CFSG.Open.pRank p E = k :=
  le_antisymm (CFSG.SectionRank.pRank_le hp.one_lt fun _ hE' _ =>
      hcard ▸ Subgroup.card_le_of_le hE')
    (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hcard)

theorem exists_pow_autOrderIn {p : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    ∃ r, autOrderIn B K = p ^ r := by
  obtain ⟨m, hm⟩ := i271_exists_card_eq hp hB
  have hd : autOrderIn B K ∣ p ^ m := by
    unfold autOrderIn
    rw [inf_of_le_left hBN, ← hm]
    exact Subgroup.relIndex_dvd_card (H := Subgroup.centralizer (K : Set X)) (K := B)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hd
  exact ⟨k, hk⟩

theorem pRank_le_centralizer_add {p r : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (h : autOrderIn B K ≤ p ^ r) :
    CFSG.Open.pRank p B ≤
      CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) + r := by
  have hE : IsElemAbelian p (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hB inf_le_left
  obtain ⟨m, hm⟩ := i271_exists_card_eq hp hB
  obtain ⟨j, hj⟩ := i271_exists_card_eq hp hE
  have hmul := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (K : Set X)) (K := B)
  have hrel : autOrderIn B K = (Subgroup.centralizer (K : Set X)).relIndex B := by
    unfold autOrderIn
    rw [inf_of_le_left hBN]
  rw [inf_comm, hj, hm, ← hrel] at hmul
  rw [i271_pRank_eq hp hB hm, i271_pRank_eq hp hE hj]
  have h1 : p ^ m ≤ p ^ (r + j) := by
    rw [← hmul, pow_add]
    exact Nat.mul_le_mul_right _ h
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  omega

end Elementary

section GOne

variable {X : Type*} [Group X] [Finite X]

theorem bClosure_eq_of_le_normalizer {B K : Subgroup X}
    (h : B ≤ Subgroup.normalizer (K : Set X)) : bClosure B K = K := by
  apply le_antisymm
  · refine iSup₂_le fun b hb => ?_
    rw [(mem_normalizer_iff_gLBConj_eq.1 (h hb))]
  · refine le_iSup₂_of_le (1 : X) B.one_mem ?_
    intro y hy
    rw [mem_gLBConj]
    simpa using hy

theorem isInGOne_of_centralizing {p : ℕ} {B K E : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hEB : E ≤ B)
    (hEK : E ≤ Subgroup.centralizer (K : Set X)) (h3 : 3 ≤ CFSG.Open.pRank p E) :
    IsInGOne p B K := by
  unfold IsInGOne
  rw [bClosure_eq_of_le_normalizer hBN]
  unfold coreIn
  apply le_antisymm
  · have hK : K ≤ Subgroup.normalizer (E : Set X) := by
      refine fun k hk => Subgroup.centralizer_le_normalizer (s := (E : Set X)) ?_
      exact Subgroup.mem_centralizer_iff.2 fun e he =>
        (Subgroup.mem_centralizer_iff.1 (hEK he) k hk).symm
    exact le_iSup₂_of_le (f := fun (Q : Subgroup X) (_ : Q ≤ B ∧ 3 ≤ CFSG.Open.pRank p Q) =>
      K ⊓ Subgroup.normalizer (Q : Set X)) E ⟨hEB, h3⟩ (le_inf le_rfl hK)
  · exact iSup₂_le fun Q _ => inf_le_left

theorem isInGOne_of_autOrderIn_le {p r : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (h : autOrderIn B K ≤ p ^ r) (hr : r + 3 ≤ CFSG.Open.pRank p B) : IsInGOne p B K := by
  refine isInGOne_of_centralizing hBN inf_le_left inf_le_right ?_
  have := pRank_le_centralizer_add hp hB hBN h
  omega

end GOne

section Aut

variable {X : Type*} [Group X] [Finite X]

theorem autOrderIn_le_pow_of_pRank {p r : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hr : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ r) : autOrderIn B K ≤ p ^ r := by
  let f : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hker : f.ker = (Subgroup.centralizer (K : Set X)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 := Subgroup.normalizerMonoidHom_ker (H := K)
    have h2 : Subgroup.inclusion hBN b ∈ K.normalizerMonoidHom.ker ↔
        ((Subgroup.inclusion hBN b : ↥(Subgroup.normalizer (K : Set X))) : X) ∈
          Subgroup.centralizer (K : Set X) := by
      rw [h1, Subgroup.mem_subgroupOf]
    exact (MonoidHom.mem_ker (f := K.normalizerMonoidHom)
      (x := Subgroup.inclusion hBN b)).symm.trans h2
  have hcard : autOrderIn B K = Nat.card f.range := by
    rw [← Subgroup.index_ker, hker]
    unfold autOrderIn
    rw [inf_of_le_left hBN]
    rfl
  have hR : IsElemAbelian p f.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : MulAut ↥K) * b = b * a
      rw [← hx, ← hz, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (congrArg Subtype.val (hB.1.is_comm.comm x z))
    · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (hB.2 x x.2)
      rw [this, map_one]
  obtain ⟨j, hj⟩ := i271_exists_card_eq hp hR
  have hj' := i271_pRank_eq hp hR hj
  have hle : CFSG.Open.pRank p f.range ≤ r :=
    (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hr
  rw [hcard, hj]
  exact Nat.pow_le_pow_right hp.pos (by omega)

end Aut

section Bridge

variable {X : Type*} [Group X]

@[expose] noncomputable def i271Act (K : Subgroup X) {S : Type*} [Group S]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) : ↥(Subgroup.normalizer (K : Set X)) →* MulAut S :=
  (MulAut.congr e).toMonoidHom.comp
    ((CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot ↥K).comp K.normalizerMonoidHom)

theorem ker_i271Act {K : Subgroup X} (hperf : commutator ↥K = ⊤) {S : Type*} [Group S]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) :
    (i271Act K e).ker =
      (Subgroup.centralizer (K : Set X)).subgroupOf (Subgroup.normalizer (K : Set X)) := by
  rw [← Subgroup.normalizerMonoidHom_ker (H := K)]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : (CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot ↥K)
        (K.normalizerMonoidHom x) = 1 :=
      (map_eq_one_iff (MulAut.congr e) (MulAut.congr e).injective).1 h
    exact (map_eq_one_iff _
      (CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf)).1 h1
  · intro h
    show (MulAut.congr e) ((CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot ↥K)
      (K.normalizerMonoidHom x)) = 1
    rw [h, map_one, map_one]

theorem i271_isElemAbelian_subgroupOf {p : ℕ} {B : Subgroup X} (N : Subgroup X)
    (hB : IsElemAbelian p B) : IsElemAbelian p (B.subgroupOf N) :=
  CFSG.Open.IsElemAbelian.subgroupOf hB N

theorem isStronglyBalancedIn_of_autBalanced [Finite X] {p n₀ : ℕ} {B K : Subgroup X}
    (hB : IsElemAbelian p B) (hperf : commutator ↥K = ⊤) {S : Type*} [Group S]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) (hn : n₀ ≤ autOrderIn B K)
    (hbal : ∀ A : Subgroup (MulAut S), IsElemAbelian p A → n₀ ≤ Nat.card A →
      ∀ T : Subgroup (MulAut S), Nat.Coprime p (Nat.card T) →
        A ≤ Subgroup.normalizer (T : Set (MulAut S)) → T = ⊥) :
    IsStronglyBalancedIn p B K := by
  intro S0 hS0N hcop hnorm
  set N : Subgroup X := Subgroup.normalizer (K : Set X) with hN
  set θ := i271Act K e with hθ
  have hNbB : B ⊓ N ≤ B := inf_le_left
  have hNbel : IsElemAbelian p (B ⊓ N) := i271_isElemAbelian_of_le hB hNbB
  set A : Subgroup (MulAut S) := ((B ⊓ N).subgroupOf N).map θ with hA
  have hAel : IsElemAbelian p A :=
    CFSG.SectionRank.isElemAbelian_map (i271_isElemAbelian_subgroupOf N hNbel) θ
  have hAcard : Nat.card A = autOrderIn B K := by
    rw [hA, ← Subgroup.relIndex_ker, hθ, ker_i271Act hperf e,
      Subgroup.relIndex_subgroupOf (inf_le_right : B ⊓ N ≤ N)]
    rfl
  set T : Subgroup (MulAut S) := (S0.subgroupOf N).map θ with hT
  have hTcop : Nat.Coprime p (Nat.card T) := by
    have hcard : Nat.card (S0.subgroupOf N) = Nat.card S0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0N).toEquiv
    refine Nat.Coprime.coprime_dvd_right ?_ (hcard ▸ hcop)
    exact Subgroup.card_map_dvd _ _
  have hAT : A ≤ Subgroup.normalizer (T : Set (MulAut S)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ∈ Subgroup.normalizer ((S0.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hx' : (x : X) ∈ B ⊓ N := hx
      have := Subgroup.mem_normalizer_iff.1 (hnorm hx') (h : X)
      simpa [Subgroup.mem_subgroupOf] using this
    exact Subgroup.le_normalizer_map θ (Subgroup.mem_map_of_mem θ hxn)
  have hTbot : T = ⊥ := hbal A hAel (hAcard ▸ hn) T hTcop hAT
  intro s hs
  have hsN : s ∈ N := hS0N hs
  have h1 : θ ⟨s, hsN⟩ ∈ T := Subgroup.mem_map_of_mem θ ((Subgroup.mem_subgroupOf).2 hs)
  rw [hTbot, Subgroup.mem_bot] at h1
  have h2 : (⟨s, hsN⟩ : ↥N) ∈ θ.ker := h1
  rw [hθ, ker_i271Act hperf e, Subgroup.mem_subgroupOf] at h2
  exact h2

end Bridge

theorem exists_noncomm_of_isQuasisimple {K : Type*} [Group K] (hq : CFSG.Open.IsQuasisimple K) :
    ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
  obtain ⟨hperf, hsimple⟩ := hq
  by_contra hab
  push Not at hab
  have hcomm : ∀ a b : K, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center K := by
    intro a b
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hab (a : K ⧸ Subgroup.center K) b]
    group
  have hle : commutator K ≤ Subgroup.center K := by
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hcomm a b
  rw [hperf, top_le_iff] at hle
  have hall : ∀ q : K ⧸ Subgroup.center K, q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => exact (QuotientGroup.eq_one_iff x).2 (hle ▸ Subgroup.mem_top x)
  have := hsimple
  obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ Subgroup.center K)
  exact hab ((hall a).trans (hall b).symm)

@[expose] def IsLTwoTwentySeven (S : Type*) [Group S] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 27 ∧
    Nonempty (S ≃* StatedProj (StatedSL 2 F))

end CFSG.HardMathSupport.Solomon.Coordinator
