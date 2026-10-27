module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed4
import CFSG.RankThree.PartOne.S9.Planes.Basic
import all CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13a

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

namespace Lemma1314c

@[expose] def uConjJoin {G : Type} [Group G] (U L : Subgroup G) : Subgroup G := ⨆ u ∈ U, GLBConj u L

@[expose] def Input23_24Fi23Loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (C L U : Subgroup G),
    GLAPComponent 5 C L → IsSporType .Fi23 (barOf 5 L) → U ≤ C → IsElemAbelian 5 U →
      Nat.card U = 5 ^ 2 → U ≤ Subgroup.normalizer (L : Set G) → centBar 5 U L = ⊥ →
      (barX 5 C L ≤ barX 5 C (⨆ z ∈ U, ⨆ (_ : z ≠ 1), ⨆ (H : Subgroup G)
          (_ : GLAPComponent 5 (C ⊓ Subgroup.centralizer ({z} : Set G)) H ∧ H ≤ L), H)) ∧
      ∀ z ∈ U, z ≠ 1 → ∀ H : Subgroup G,
        GLAPComponent 5 (C ⊓ Subgroup.centralizer ({z} : Set G)) H → H ≤ L →
          IsAltType 7 (barOf 5 H)

@[expose] def FiFaithBlock : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139a p M D → ∀ {U : Subgroup G},
    IsU1312 p B M D L0 d U → U ≤ centerOf R → ∀ {b : G},
    b ∈ centBar p U (L1of p M D L0) → b ≠ 1 → p = 5 →
    IsSporType .Fi23 (barOf p (Lemma1314.LOf p L0 d b)) →
      centBar p U (Lemma1314.LOf p L0 d b) = ⊥

@[expose] def Chev3Block : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139a p M D → ∀ {U : Subgroup G},
    IsU1312 p B M D L0 d U → U ≤ centerOf R → ∀ {b : G},
    b ∈ centBar p U (L1of p M D L0) → b ≠ 1 → p = 5 →
    IsLieChar (· = 3) (barOf p (Lemma1314.LOf p L0 d b)) →
      ¬ ∃ Q : ℕ, (IsLpType p Q (barOf p (Lemma1314.LOf p L0 d b) ⧸
            Subgroup.center (barOf p (Lemma1314.LOf p L0 d b))) ∧ p ∣ Q - 1) ∨
          (IsUpType p Q (barOf p (Lemma1314.LOf p L0 d b) ⧸
            Subgroup.center (barOf p (Lemma1314.LOf p L0 d b))) ∧ p ∣ Q + 1)

@[expose] def ChevGenBlock : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139a p M D → ∀ {U : Subgroup G},
    IsU1312 p B M D L0 d U → U ≤ centerOf R → ∀ {b : G},
    b ∈ centBar p U (L1of p M D L0) → b ≠ 1 → CFSG.Open.pRank p A = 3 →
    (¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1) →
    IsLieChar (· = 2) (barOf p (Lemma1314.LOf p L0 d b)) →
    (p = 5 → ¬ Lemma1314.I2310Exc5 (barX p (Cg d) (Lemma1314.LOf p L0 d b))) →
      (barX p (Cg d) (Lemma1314.LOf p L0 d b) ≤ barX p (Cg d)
        (⨆ z ∈ U, ⨆ (_ : z ≠ 1),
          (GLAPPrimeCoreOf p (uConjJoin U (Lemma1314.LOf p L0 d b) ⊓ Cg z) ⊔
            ⨆ (H : Subgroup G) (_ : GLAPComponent p (Cg2 d z) H ∧
              H ≤ uConjJoin U (Lemma1314.LOf p L0 d b)), H))) ∧
      (∀ z ∈ U, z ≠ 1 → ∀ H : Subgroup G, GLAPComponent p (Cg2 d z) H →
        H ≤ uConjJoin U (Lemma1314.LOf p L0 d b) →
          Prop95Iv.InChevTwo (barOf p H))

@[expose] def ChevOpMBlock : Prop :=
  Prop112Statement →
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139a p M D →
    (R = (R ⊓ Iof p M D) ⊔ centBar p R (Iof p M D) ∧ (R ⊓ Iof p M D) ⊓ centBar p R (Iof p M D) = ⊥ ∧
        CFSG.Open.pRank p (R ⊓ Iof p M D) = 1) → ∀ {U : Subgroup G},
    IsU1312 p B M D L0 d U → U ≤ centerOf R → ∀ {b : G},
    b ∈ centBar p U (L1of p M D L0) → b ≠ 1 → (¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1) →
    IsLieChar (· = 2) (barOf p (Lemma1314.LOf p L0 d b)) →
      ∀ z ∈ U, z ≠ 1 → GLAPPrimeCoreOf p (uConjJoin U (Lemma1314.LOf p L0 d b) ⊓ Cg z) ≤ M

@[expose] def PiTypeClauseBlock : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139a p M D → IsPiTypeGroup p (barOf p (Iof p M D))

theorem piTypeClauseBlock_holds : PiTypeClauseBlock := by
  intro G _ _ m p B M E A D T R L0 d _ h139a
  obtain ⟨-, -, L, -, hIL, -, htype⟩ := h139a
  subst hIL
  unfold IsPiTypeGroup
  rcases htype with hA | ⟨ε, n, hn, hO, hF⟩
  · refine Or.inl ⟨1, ?_⟩
    rw [one_mul]
    exact hA
  · exact Or.inr (Or.inl ⟨n, ε, hn, hO, hF⟩)

theorem cg2_eq_inf {G : Type} [Group G] (d z : G) : Cg2 d z = Cg d ⊓ Cg z := by
  ext x
  simp only [Subgroup.mem_inf, Cg, Cg2, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩
  · rintro ⟨h1, h2⟩ g (rfl | rfl)
    exacts [h1 _ rfl, h2 _ rfl]

theorem le_of_barX_le_of_le {G : Type} [Group G] [Finite G] {p : ℕ} {C L X M : Subgroup G}
    (hLC : L ≤ C) (hcore : GLAPPrimeCoreOf p C ≤ M) (hX : X ≤ M)
    (hle : barX p C L ≤ barX p C X) : L ≤ M := by
  intro l hl
  obtain ⟨j, hj, hjl⟩ := exists_of_barX_le hle hl (hLC hl)
  have e : l = j * (j⁻¹ * l) := by group
  rw [e]
  exact M.mul_mem (hX hj) (hcore hjl)

theorem isLieChar_mono {P Q : ℕ → Prop} (hPQ : ∀ q, P q → Q q) {X : Type*} [Group X]
    (h : IsLieChar P X) : IsLieChar Q X := by
  obtain ⟨idx, e, hP⟩ := h
  exact ⟨idx, e, hPQ _ hP⟩

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem gLBConj_iSup_le_of_mem_normalizer {S I : Subgroup G} {u : G}
    (hS : u ∈ Subgroup.normalizer (S : Set G)) (hI : u ∈ Subgroup.normalizer (I : Set G)) :
    GLBConj u (⨆ h ∈ S, GLBConj h I) ≤ ⨆ h ∈ S, GLBConj h I := by
  refine (le_of_eq (gLBConj_iSup_eq u (fun h : G => ⨆ (_ : h ∈ S), GLBConj h I))).trans ?_
  refine iSup_le fun h => ?_
  refine (le_of_eq (gLBConj_iSup_eq u (fun _ : h ∈ S => GLBConj h I))).trans ?_
  refine iSup_le fun hh => ?_
  rw [gLBConj_gLBConj]
  have hh' : u⁻¹ * h * u ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (S : Set G)).inv_mem hS) h).1 hh
    rwa [inv_inv] at this
  have e : GLBConj (h * u) I = GLBConj (u⁻¹ * h * u) I := by
    ext y
    rw [mem_gLBConj, mem_gLBConj,
      Subgroup.mem_normalizer_iff.1 hI ((u⁻¹ * h * u) * y * (u⁻¹ * h * u)⁻¹)]
    rw [show u * ((u⁻¹ * h * u) * y * (u⁻¹ * h * u)⁻¹) * u⁻¹ = h * u * y * (h * u)⁻¹ by group]
  rw [e]
  exact le_iSup₂_of_le (u⁻¹ * h * u) hh' le_rfl

theorem mem_normalizer_iSup_conj {S I : Subgroup G} {u : G}
    (hS : u ∈ Subgroup.normalizer (S : Set G)) (hI : u ∈ Subgroup.normalizer (I : Set G)) :
    u ∈ Subgroup.normalizer ((⨆ h ∈ S, GLBConj h I : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (gLBConj_iSup_le_of_mem_normalizer hS hI) ?_
  have h1 := gLBConj_iSup_le_of_mem_normalizer ((Subgroup.normalizer (S : Set G)).inv_mem hS)
    ((Subgroup.normalizer (I : Set G)).inv_mem hI)
  have h2 := gLBConj_mono u h1
  rwa [gLBConj_gLBConj_inv] at h2

theorem mem_normalizer_LOf {p : ℕ} {L0 : Subgroup G} {d b u : G} (hu : u ∈ Cg d)
    (hI : u ∈ Subgroup.normalizer (Lemma1314.L0bOf p L0 b : Set G)) :
    u ∈ Subgroup.normalizer (Lemma1314.LOf p L0 d b : Set G) :=
  mem_normalizer_iSup_conj (S := GLAPLayer p (Cg d)) (I := Lemma1314.L0bOf p L0 b)
    (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_normalizer_glaPLayer
      (Subgroup.le_normalizer hu)) hI

theorem mem_normalizer_L0bOf_of_mem {p : ℕ} {L0 : Subgroup G} {b x : G} (hx : x ∈ L0)
    (hxb : x * b = b * x) :
    x ∈ Subgroup.normalizer (Lemma1314.L0bOf p L0 b : Set G) := by
  refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_normalizer_glaPLayer ?_
  refine mem_normalizer_inf (Subgroup.le_normalizer hx) (Subgroup.le_normalizer ?_)
  exact Subgroup.mem_centralizer_singleton_iff.2 hxb

theorem mem_normalizer_L0bOf_self {p : ℕ} {L0 : Subgroup G} {b : G} :
    b ∈ Subgroup.normalizer (Lemma1314.L0bOf p L0 b : Set G) := by
  refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_normalizer_glaPLayer ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hc : ∀ z ∈ L0 ⊓ Subgroup.centralizer ({b} : Set G), b * z * b⁻¹ = z := by
    intro z hz
    have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hz).2
    rw [← this]
    group
  constructor
  · intro hy
    rw [hc y hy]
    exact hy
  · intro hy
    have h1 := hc _ hy
    have h2 : b * y * b⁻¹ = y := by
      calc b * y * b⁻¹ = b⁻¹ * (b * (b * y * b⁻¹) * b⁻¹) * b := by group
        _ = b⁻¹ * (b * y * b⁻¹) * b := by rw [h1]
        _ = y := by group
    rwa [h2] at hy

theorem mem_core_iff {p : ℕ} {L : Subgroup G} {y : G} :
    y ∈ GLAPPrimeCoreOf p L ↔ ∃ h : y ∈ L, (⟨y, h⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

theorem eq_one_of_mem_centBar_of_mem {p : ℕ} (hp : p.Prime) {U L0 L1 : Subgroup G}
    (hL01 : L0 ≤ L1) (hZ : Subgroup.center (barOf p L0) = ⊥) {b : G}
    (hb : b ∈ centBar p U L1) (hbL0 : b ∈ L0) (hbp : b ^ p = 1) : b = 1 := by
  obtain ⟨hbc, -⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨hbN, hbar⟩ := mem_centK_iff.1 hbc
  have hbL1 : b ∈ L1 := hL01 hbL0
  have hcomm : ∀ l : ↥L0, b * (l : G) * b⁻¹ * (l : G)⁻¹ ∈ GLAPPrimeCoreOf p L0 := by
    intro l
    have hl1 : ((l⁻¹ : ↥L0) : G) ∈ L1 := hL01 (l⁻¹).2
    have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk p L1 ⟨b, hbN⟩
      ⟨((l⁻¹ : ↥L0) : G), hl1⟩
    rw [hbar, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.1 h1
    have hmemL1 : b * (l : G) * b⁻¹ * (l : G)⁻¹ ∈ L1 :=
      L1.mul_mem (L1.mul_mem (L1.mul_mem hbL1 (hL01 l.2)) (L1.inv_mem hbL1)) (L1.inv_mem (hL01 l.2))
    have h3 : (⟨b * (l : G) * b⁻¹ * (l : G)⁻¹, hmemL1⟩ : ↥L1) ∈ GLAPPrimeCore p ↥L1 := by
      have h2' := (GLAPPrimeCore p ↥L1).inv_mem h2
      convert h2' using 1
      apply Subtype.ext
      show b * (l : G) * b⁻¹ * (l : G)⁻¹ = (((l⁻¹ : ↥L0) : G)⁻¹ * (b * ((l⁻¹ : ↥L0) : G) * b⁻¹))⁻¹
      simp only [Subgroup.coe_inv, inv_inv]
      group
    have h3' : b * (l : G) * b⁻¹ * (l : G)⁻¹ ∈ GLAPPrimeCoreOf p L1 := mem_core_iff.2 ⟨hmemL1, h3⟩
    have h4 : b * (l : G) * b⁻¹ * (l : G)⁻¹ ∈ L0 :=
      L0.mul_mem (L0.mul_mem (L0.mul_mem hbL0 l.2) (L0.inv_mem hbL0)) (L0.inv_mem l.2)
    have h5 := CFSG.HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp L1 L0 ⟨h3', h4⟩
    rwa [inf_eq_right.2 hL01] at h5
  have hβ : (QuotientGroup.mk (⟨b, hbL0⟩ : ↥L0) : barOf p L0) ∈ Subgroup.center (barOf p L0) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨hcL, hcN⟩ := mem_core_iff.1 (hcomm l)
    have hq : (QuotientGroup.mk (⟨b * (l : G) * b⁻¹ * (l : G)⁻¹, hcL⟩ : ↥L0) : barOf p L0) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hcN
    have e : (⟨b * (l : G) * b⁻¹ * (l : G)⁻¹, hcL⟩ : ↥L0) = ⟨b, hbL0⟩ * l * (⟨b, hbL0⟩ : ↥L0)⁻¹ * l⁻¹ :=
      rfl
    rw [e] at hq
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hq
    have h1 := mul_inv_eq_one.1 hq
    have h2 := mul_inv_eq_iff_eq_mul.1 h1
    exact h2.symm
  rw [hZ, Subgroup.mem_bot] at hβ
  have hbO : b ∈ GLAPPrimeCoreOf p L0 :=
    mem_core_iff.2 ⟨hbL0, (QuotientGroup.eq_one_iff _).1 hβ⟩
  by_contra hb1
  have hord : orderOf b = p :=
    ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hbp)).resolve_left
      (fun h => hb1 (orderOf_eq_one_iff.1 h))
  have hle : Subgroup.zpowers b ≤ GLAPPrimeCoreOf p L0 := Subgroup.zpowers_le.2 hbO
  have hdvd : p ∣ Nat.card (GLAPPrimeCoreOf p L0) := by
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hord] at h1
  exact not_dvd_card_glaPPrimeCoreOf hp L0 hdvd

theorem center_barOf_L0_eq_bot {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    (hL133 : Lemma133Statement) (hcomp : Sec13g.Lemma133_compStatement) :
    Subgroup.center (barOf p L0) = ⊥ := by
  have hp : p.Prime := h.standing.prime
  have hp2 : p ≠ 2 := h.standing.ne_two
  obtain ⟨-, hIstar, L, hLc, hIL, -, -⟩ := h139a
  rw [← hIL] at hLc
  have hIc : GLAPComponent p (Istar p M D) (Iof p M D) := by
    rw [← hIstar]
    exact hLc
  have hbl : IsGLBlock M (Iof p M D) := ((hL133 h.toSec13).2 _ hIc).1.1
  have hcompM : GLAPComponent p M (Iof p M D) := hcomp h.toSec13 hIc
  have hZ : Subgroup.center (barOf p (Iof p M D)) = ⊥ :=
    center_quotient_eq_bot_of_block hp hp2 hcompM hbl
  obtain ⟨e⟩ := h.hL0iso _ hIc
  have hcen : (Subgroup.center (barOf p L0)).map (e : barOf p L0 →* barOf p (Iof p M D)) =
      Subgroup.center (barOf p (Iof p M D)) := Subgroup.map_center_eq e
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center (barOf p (Iof p M D)) := by
    rw [← hcen]
    exact ⟨x, hx, rfl⟩
  rw [hZ, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.2 (e.injective (hex.trans (map_one e).symm))

theorem closure_pair_eq_of_card {p : ℕ} (hp : p.Prime) {B U : Subgroup G}
    (hU : CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn p 2 B U) {x b : G} (hxU : x ∈ U)
    (hbU : b ∈ U) (hx1 : x ≠ 1) (hbx : b ∉ Subgroup.zpowers x) :
    Subgroup.closure ({x, b} : Set G) = U := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hUel : IsElemAbelian p U := hU.2.1
  have hcard : Nat.card U = p ^ 2 := hU.2.2
  have hxp : x ^ p = 1 := hUel.2 x hxU
  have hbp : b ^ p = 1 := hUel.2 b hbU
  have hcomm : x * b = b * x := elemAbelian_comm hUel hxU hbU
  have hc := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.card_closure_pair_eq_sq
    hxp hbp hcomm hx1 hbx
  have hle : Subgroup.closure ({x, b} : Set G) ≤ U :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxU, Set.singleton_subset_iff.2 hbU⟩)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hcard])

theorem U_le_normalizer_LOf {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    (hL133 : Lemma133Statement) (hcomp : Sec13g.Lemma133_compStatement)
    {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) {b : G}
    (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1) :
    U ≤ Subgroup.normalizer (Lemma1314.LOf p L0 d b : Set G) := by
  have hp : p.Prime := h.standing.prime
  have hbU : b ∈ U := (Subgroup.mem_inf.1 hb).2
  obtain ⟨⟨x, hxmem⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU.2.2.1
  have hxU : x ∈ U := (Subgroup.mem_inf.1 hxmem).1
  have hxL0 : x ∈ L0 := (Subgroup.mem_inf.1 hxmem).2
  have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  have hbp : b ^ p = 1 := hU.1.2.1.2 b hbU
  have hZ := center_barOf_L0_eq_bot h h139a hL133 hcomp
  have hbx : b ∉ Subgroup.zpowers x := by
    intro hbz
    exact hb1 (eq_one_of_mem_centBar_of_mem hp (Sec13g.le_L1of (p := p) (M := M) (D := D)) hZ hb
      ((Subgroup.zpowers_le.2 hxL0) hbz) hbp)
  have hUeq := closure_pair_eq_of_card hp hU.1 hxU hbU hx1' hbx
  have hxb : x * b = b * x := elemAbelian_comm hU.1.2.1 hxU hbU
  have hUC : U ≤ Cg d := hU.2.1
  rw [← hUeq]
  refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩)
  · exact mem_normalizer_LOf (hUC hxU) (mem_normalizer_L0bOf_of_mem hxL0 hxb)
  · exact mem_normalizer_LOf (hUC hbU) mem_normalizer_L0bOf_self

end Normalizer

section Conn

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_core_of_mem_centBar {p : ℕ} {X I : Subgroup G} {c l : G}
    (hc : c ∈ centBar p X I) (hl : l ∈ I) : c * l * c⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p I := by
  obtain ⟨hcK, -⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨hcN, hbar⟩ := mem_centK_iff.1 hcK
  have hl' : l⁻¹ ∈ I := I.inv_mem hl
  have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk p I ⟨c, hcN⟩ ⟨l⁻¹, hl'⟩
  rw [hbar, MulAut.one_apply] at h1
  have h2 := QuotientGroup.eq.1 h1
  have hmem : c * l * c⁻¹ * l⁻¹ ∈ I := I.mul_mem ((Subgroup.mem_normalizer_iff.1 hcN l).1 hl) hl'
  have h3 : (⟨c * l * c⁻¹ * l⁻¹, hmem⟩ : ↥I) ∈ GLAPPrimeCore p ↥I := by
    have h2' := (GLAPPrimeCore p ↥I).inv_mem h2
    convert h2' using 1
    apply Subtype.ext
    show c * l * c⁻¹ * l⁻¹ = (((⟨l⁻¹, hl'⟩ : ↥I) : G)⁻¹ * (c * ((⟨l⁻¹, hl'⟩ : ↥I) : G) * c⁻¹))⁻¹
    simp only [inv_inv]
    group
  exact mem_core_iff.2 ⟨hmem, h3⟩

theorem comm_of_mem_centBar {p : ℕ} (hp : p.Prime) {R I : Subgroup G} (hRp : IsPGroup p ↥R)
    {c l : G} (hc : c ∈ centBar p R I) (hl : l ∈ R ⊓ I) : c * l = l * c := by
  have hcR : c ∈ R := (Subgroup.mem_inf.1 hc).2
  obtain ⟨hlR, hlI⟩ := Subgroup.mem_inf.1 hl
  have h1 := comm_mem_core_of_mem_centBar hc hlI
  have h2 : c * l * c⁻¹ * l⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hcR hlR) (R.inv_mem hcR)) (R.inv_mem hlR)
  have h3 : c * l * c⁻¹ * l⁻¹ ∈ R ⊓ GLAPPrimeCoreOf p I := Subgroup.mem_inf.2 ⟨h2, h1⟩
  rw [isPGroup_inf_eq_bot_of_not_dvd hp hRp (not_dvd_card_glaPPrimeCoreOf hp I),
    Subgroup.mem_bot] at h3
  calc c * l = (c * l * c⁻¹ * l⁻¹) * (l * c) := by group
    _ = l * c := by rw [h3, one_mul]

theorem isElemAbelian_zpowers_of_pow {p : ℕ} {x : G} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    change (a : G) * b = b * a
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self x i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem isEkIn_sup_zpowers {p k : ℕ} (hp : p.Prime) {X W : Subgroup G} {z : G}
    (hW : CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn p k X W) (hzp : z ^ p = 1) (hzW : z ∉ W)
    (hcomm : ∀ w ∈ W, w * z = z * w) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn p (k + 1) ⊤ (W ⊔ Subgroup.zpowers z) := by
  refine ⟨le_top, CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute hW.2.1
    (isElemAbelian_zpowers_of_pow hzp) ?_, ?_⟩
  · intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((show Commute w z from hcomm w hw).zpow_right i).eq.symm
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp W hzp hzW hcomm, hW.2.2, pow_succ]

theorem sup_zpowers_le_centralizer {W₁ W₂ : Subgroup G} {z : G}
    (h12 : W₁ ≤ Subgroup.centralizer (W₂ : Set G)) (hz1 : ∀ w ∈ W₁, w * z = z * w)
    (hz2 : ∀ w ∈ W₂, w * z = z * w) :
    W₁ ⊔ Subgroup.zpowers z ≤
      Subgroup.centralizer ((W₂ ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := by
  have hle : W₂ ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.2 (hz2 w hw)) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzc : z ∈ Subgroup.centralizer ((W₂ ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  have h1 : W₁ ≤ Subgroup.centralizer ((W₂ ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le (Subgroup.le_centralizer_iff.1 h12) ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro w hw
    exact hz1 w hw
  exact sup_le h1 (Subgroup.zpowers_le.2 hzc)

theorem isKConnected_of_part_i {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d)
    (hi : R = (R ⊓ Iof p M D) ⊔ centBar p R (Iof p M D) ∧
      (R ⊓ Iof p M D) ⊓ centBar p R (Iof p M D) = ⊥ ∧ CFSG.Open.pRank p (R ⊓ Iof p M D) = 1)
    (hA4 : 4 ≤ CFSG.Open.pRank p A) : IsKConnectedIn p 3 ⊤ A B := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨hRdec, hRbot, hRrk⟩ := hi
  set I : Subgroup G := Iof p M D with hIdef
  set C : Subgroup G := centBar p R I with hCdef
  obtain ⟨⟨hRM, hRp, -⟩, hABR⟩ := h.hR
  have hAR : A ≤ R := le_sup_left.trans hABR
  have hBR : B ≤ R := le_sup_right.trans hABR
  have hCR : C ≤ R := inf_le_right
  have hCp : IsPGroup p ↥C := hRp.to_le hCR
  have hpgrp : ∀ {Y : Subgroup G}, IsElemAbelian p Y → IsPGroup p ↥Y := fun hY g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hY.2 g.1 g.2)⟩
  have hAsc : IsSCp p M A := h.pair.1.2.1.1.1
  have hBsc : IsSCp p M B := (lemma101_ii_holds h.toSec13.toSec11.toSec10Fails).1.1
  have hAel : IsElemAbelian p A := hAsc.2.1
  have hBel : IsElemAbelian p B := hBsc.2.1
  have hcomm : ∀ c ∈ C, ∀ l ∈ R ⊓ I, c * l = l * c := fun c hc l hl =>
    comm_of_mem_centBar hp hRp hc hl
  have hRIC : R ⊓ I ≤ Subgroup.centralizer (C : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact hcomm c hc l hl
  have hRIp : IsPGroup p ↥(R ⊓ I) := hRp.to_le inf_le_left
  obtain ⟨E1, hE1, -, hE1c⟩ := CFSG.SectionRank.exists_pRank hp1 (R ⊓ I)
  rw [hRrk, pow_one] at hE1c
  have hRIne : R ⊓ I ≠ ⊥ := by
    intro hbot
    rw [hbot, le_bot_iff] at hE1
    rw [hE1, Subgroup.card_bot] at hE1c
    exact hp.one_lt.ne hE1c
  haveI : Nontrivial ↥(R ⊓ I) := (Subgroup.nontrivial_iff_ne_bot _).2 hRIne
  have hZnt : Nontrivial ↥(Subgroup.center ↥(R ⊓ I)) := hRIp.center_nontrivial
  have hZp : IsPGroup p ↥(Subgroup.center ↥(R ⊓ I)) := hRIp.to_subgroup _
  obtain ⟨n0, hn0, hn0c⟩ := hZp.nontrivial_iff_card.1 hZnt
  have hdvd : p ∣ Nat.card ↥(Subgroup.center ↥(R ⊓ I)) := by
    rw [hn0c]
    exact dvd_pow_self p (by omega)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set z : G := ((w : ↥(R ⊓ I)) : G) with hzdef
  have hzRI : z ∈ R ⊓ I := (w : ↥(R ⊓ I)).2
  have hzR : z ∈ R := (Subgroup.mem_inf.1 hzRI).1
  have hzord : orderOf z = p := by
    rw [hzdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hzp : z ^ p = 1 := hzord ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro hz
    rw [hz, orderOf_one] at hzord
    exact hp.one_lt.ne hzord
  have hzcen : ∀ y ∈ R ⊓ I, y * z = z * y := by
    intro y hy
    have h1 := Subgroup.mem_center_iff.1 w.2 ⟨y, hy⟩
    exact congrArg Subtype.val h1
  have hΩ : ∀ x ∈ R ⊓ I, x ^ p = 1 → x ∈ Subgroup.zpowers z := by
    intro x hx hxp
    by_contra hxz
    have hczx : ∀ e ∈ Subgroup.zpowers z, e * x = x * e := by
      intro e he
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      exact ((show Commute x z from hzcen x hx).zpow_right i).eq.symm
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (Subgroup.zpowers z) hxp hxz hczx
    rw [Nat.card_zpowers, hzord] at hcard
    have hel : IsElemAbelian p (Subgroup.zpowers z ⊔ Subgroup.zpowers x) := by
      refine CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute
        (isElemAbelian_zpowers_of_pow hzp) (isElemAbelian_zpowers_of_pow hxp) ?_
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((show Commute e x from hczx e he).zpow_right j).eq.symm
    have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers x ≤ R ⊓ I :=
      sup_le (Subgroup.zpowers_le.2 hzRI) (Subgroup.zpowers_le.2 hx)
    have h2 := CFSG.SectionRank.le_pRank hp1 hle hel (k := 2) (by rw [hcard]; ring)
    omega
  have hRz : R ≤ Subgroup.centralizer ({z} : Set G) := by
    intro r hr
    rw [hRdec] at hr
    obtain ⟨l, hl, c, hc, rfl⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_mul_of_mem_sup hRIC hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : l * z = z * l := hzcen l hl
    have h2 : c * z = z * c := hcomm c hc z hzRI
    calc l * c * z = l * (c * z) := by group
      _ = l * (z * c) := by rw [h2]
      _ = l * z * c := by group
      _ = z * l * c := by rw [h1]
      _ = z * (l * c) := by group
  have hzW : ∀ W : Subgroup G, W ≤ R → ∀ x ∈ W, x * z = z * x := fun W hW x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (hRz (hW hx))
  have hz_in : ∀ X : Subgroup G, IsSCp p M X → X ≤ R → z ∈ X := by
    intro X hXsc hXR
    have hle : X ⊔ Subgroup.zpowers z ≤ M := sup_le hXsc.1 (Subgroup.zpowers_le.2 (hRM hzR))
    have hel : IsElemAbelian p (X ⊔ Subgroup.zpowers z) := by
      refine CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute hXsc.2.1
        (isElemAbelian_zpowers_of_pow hzp) ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((show Commute x z from hzW X hXR x hx).zpow_right i).eq.symm
    have heq := hXsc.2.2 _ hle hel le_sup_left
    have hmem : z ∈ X ⊔ Subgroup.zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    rwa [heq] at hmem
  have hzA : z ∈ A := hz_in A hAsc hAR
  have hzB : z ∈ B := hz_in B hBsc hBR
  have hzC : z ∉ C := by
    intro hzc
    have hmem : z ∈ (R ⊓ I) ⊓ C := Subgroup.mem_inf.2 ⟨hzRI, hzc⟩
    rw [hRbot, Subgroup.mem_bot] at hmem
    exact hz1 hmem
  have hkey : ∀ X : Subgroup G, X ≤ R → IsElemAbelian p X → z ∈ X →
      Nat.card X ≤ p * Nat.card ↥(X ⊓ C) := by
    intro X hXR hXel hzX
    let f : ↥(Subgroup.zpowers z) × ↥(X ⊓ C) → ↥X := fun q =>
      ⟨(q.1 : G) * (q.2 : G),
        X.mul_mem (Subgroup.zpowers_le.2 hzX q.1.2) (Subgroup.mem_inf.1 q.2.2).1⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨a, haX⟩
      have haR : a ∈ (R ⊓ I) ⊔ C := by
        rw [← hRdec]
        exact hXR haX
      obtain ⟨l, hl, c, hc, hlc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_mul_of_mem_sup hRIC haR
      have hap : a ^ p = 1 := hXel.2 a haX
      have hcl : Commute l c := (hcomm c hc l hl).symm
      rw [hlc, hcl.mul_pow] at hap
      have hlp : l ^ p = 1 := by
        have h1 : l ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hap
        have h2 : l ^ p ∈ (R ⊓ I) ⊓ C := by
          refine Subgroup.mem_inf.2 ⟨pow_mem hl p, ?_⟩
          rw [h1]
          exact C.inv_mem (pow_mem hc p)
        rw [hRbot, Subgroup.mem_bot] at h2
        exact h2
      have hlz : l ∈ Subgroup.zpowers z := hΩ l hl hlp
      have hcX : c ∈ X := by
        have e : c = l⁻¹ * a := by rw [hlc]; group
        rw [e]
        exact X.mul_mem (X.inv_mem (Subgroup.zpowers_le.2 hzX hlz)) haX
      exact ⟨(⟨l, hlz⟩, ⟨c, Subgroup.mem_inf.2 ⟨hcX, hc⟩⟩), Subtype.ext hlc.symm⟩
    have h1 := Nat.card_le_card_of_surjective f hsurj
    rwa [Nat.card_prod, Nat.card_zpowers, hzord] at h1
  have hsub : ∀ X : Subgroup G, X ≤ R → IsElemAbelian p X → z ∈ X → p ^ 4 ≤ Nat.card X →
      ∃ X' : Subgroup G, X' ≤ X ⊓ C ∧ IsElemAbelian p X' ∧ Nat.card X' = p ^ 3 := by
    intro X hXR hXel hzX hX4
    have h1 := hkey X hXR hXel hzX
    have hXCel : IsElemAbelian p (X ⊓ C) := CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_mono hXel inf_le_left
    obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_card_eq_pow (hpgrp hXCel)
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have hk2 : k ≤ 2 := by omega
      have h2 : Nat.card ↥(X ⊓ C) ≤ p ^ 2 := by
        rw [hk]
        exact Nat.pow_le_pow_right hp.pos hk2
      have h3 : p ^ 4 ≤ p ^ 3 := by
        calc p ^ 4 ≤ Nat.card X := hX4
          _ ≤ p * Nat.card ↥(X ⊓ C) := h1
          _ ≤ p * p ^ 2 := Nat.mul_le_mul_left p h2
          _ = p ^ 3 := by ring
      have h4 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp1 (by norm_num)
      omega
    exact CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hXCel
      (by rw [hk]; exact pow_dvd_pow p hk3)
  have hAcard : p ^ 4 ≤ Nat.card A := by
    obtain ⟨E0, hE0A, -, hE0c⟩ := CFSG.SectionRank.exists_pRank hp1 A
    calc p ^ 4 ≤ p ^ CFSG.Open.pRank p A := Nat.pow_le_pow_right hp.pos hA4
      _ = Nat.card E0 := hE0c.symm
      _ ≤ Nat.card A := Subgroup.card_le_of_le hE0A
  have hBcard : p ^ 4 ≤ Nat.card B := by
    have hBc : Nat.card B = p ^ GLATwoLocalRank p G := h.bOne.1.2.1
    rw [hBc, hS.rank_eq]
    exact Nat.pow_le_pow_right hp.pos hS.four_le
  obtain ⟨A', hA'AC, hA'el, hA'c⟩ := hsub A hAR hAel hzA hAcard
  obtain ⟨B', hB'BC, hB'el, hB'c⟩ := hsub B hBR hBel hzB hBcard
  have hA'C : A' ≤ C := hA'AC.trans inf_le_right
  have hB'C : B' ≤ C := hB'BC.trans inf_le_right
  have hA'A : A' ≤ A := hA'AC.trans inf_le_left
  have hB'B : B' ≤ B := hB'BC.trans inf_le_left
  have hconn2 : IsKConnectedIn p 2 C A' B' :=
    (input31_6_holds G p hp hp2 C hCp).2 A' B' ⟨hA'C, hA'el, hA'c⟩ ⟨hB'C, hB'el, hB'c⟩
  have hEk3 : ∀ W : Subgroup G, CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn p 2 C W →
      CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn p 3 ⊤ (W ⊔ Subgroup.zpowers z) := fun W hW =>
    isEkIn_sup_zpowers hp hW hzp (fun hzw => hzC (hW.1 hzw)) (hzW W (hW.1.trans hCR))
  have hA'3 : CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn p 3 ⊤ A' := ⟨le_top, hA'el, hA'c⟩
  have hB'3 : CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn p 3 ⊤ B' := ⟨le_top, hB'el, hB'c⟩
  have hAA' : A ≤ Subgroup.centralizer (A' : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact elemAbelian_comm hAel (hA'A hy) ha
  have hB'B' : B' ≤ Subgroup.centralizer (B : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact elemAbelian_comm hBel hb (hB'B hy)
  obtain ⟨-, -, -, -, -, -, hor⟩ := hconn2
  refine ⟨le_top, hAel, ?_, le_top, hBel, ?_, Or.inr ⟨A', B', hA'3, hB'3, hAA', ?_, hB'B'⟩⟩
  · exact le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hAcard
  · exact le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hBcard
  · rcases hor with hAB' | ⟨U, V, hU, hV, hA'U, hUV, hVB'⟩
    · exact Relation.ReflTransGen.single ⟨hA'3, hB'3, hAB'⟩
    · have hstep1 : IsKConnStep p 3 ⊤ A' (U ⊔ Subgroup.zpowers z) :=
        ⟨hA'3, hEk3 U hU, le_sup_left.trans (sup_zpowers_le_centralizer hA'U
          (hzW A' (hA'A.trans hAR)) (hzW U (hU.1.trans hCR)))⟩
      have hchain : Relation.ReflTransGen (IsKConnStep p 3 ⊤) (U ⊔ Subgroup.zpowers z)
          (V ⊔ Subgroup.zpowers z) :=
        hUV.lift (fun W => W ⊔ Subgroup.zpowers z) (fun W₁ W₂ hW => ⟨hEk3 W₁ hW.1, hEk3 W₂ hW.2.1,
          sup_zpowers_le_centralizer hW.2.2 (hzW W₁ (hW.1.1.trans hCR)) (hzW W₂ (hW.2.1.1.trans hCR))⟩)
      have hstep2 : IsKConnStep p 3 ⊤ (V ⊔ Subgroup.zpowers z) B' :=
        ⟨hEk3 V hV, hB'3, (sup_zpowers_le_centralizer hVB' (hzW V (hV.1.trans hCR))
          (hzW B' (hB'B.trans hBR))).trans
          (Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_left hx))⟩
      exact Relation.ReflTransGen.head hstep1 (hchain.tail hstep2)

end Conn

theorem connBlock_of_inputs (hI71 : Input7_1Inn) (hL133 : Lemma133Statement)
    (hcomp : Sec13g.Lemma133_compStatement) (hPiI : PiTypeClauseBlock) : Lemma1314.ConnBlock :=
  fun h h139a hA4 =>
    isKConnected_of_part_i h (Sec13g.lemma1314_i_of_inputs hI71 hL133 hcomp h h139a (hPiI h h139a)) hA4

end Lemma1314c

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
