module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF4
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

local instance e7ClassUF4PerfectNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem uPair_commutator_mul_mul {G : Type*} [Group G] {X X' Y Y' Z Z' : G}
    (h1 : Commute X' Y) (h2 : Commute X Y') (hZ : ⁅X, Y⁆ = Z) (hZ' : ⁅X', Y'⁆ = Z')
    (h3 : Commute Z' X) (h4 : Commute Z' Y) (h5 : Commute Z Z') :
    ⁅X * X', Y * Y'⁆ = Z * Z' := by
  rw [commutatorElement_def] at hZ hZ' ⊢
  have e1 : X' * Y' * X'⁻¹ = Z' * Y' := by rw [← hZ']; group
  have e2 : Y' * X⁻¹ = X⁻¹ * Y' := by
    calc Y' * X⁻¹ = X⁻¹ * (X * Y') * X⁻¹ := by group
      _ = X⁻¹ * (Y' * X) * X⁻¹ := by rw [h2.eq]
      _ = X⁻¹ * Y' := by group
  have e3 : X * Y * Z' = Z' * (X * Y) := by
    rw [mul_assoc, ← h4.eq, ← mul_assoc, ← h3.eq, mul_assoc]
  calc X * X' * (Y * Y') * (X * X')⁻¹ * (Y * Y')⁻¹ =
        X * (X' * Y) * Y' * X'⁻¹ * X⁻¹ * Y'⁻¹ * Y⁻¹ := by group
    _ = X * Y * (X' * Y' * X'⁻¹) * X⁻¹ * Y'⁻¹ * Y⁻¹ := by rw [h1.eq]; group
    _ = X * Y * Z' * (Y' * X⁻¹) * Y'⁻¹ * Y⁻¹ := by rw [e1]; group
    _ = X * Y * Z' * X⁻¹ * Y⁻¹ := by rw [e2]; group
    _ = Z' * (X * Y * X⁻¹ * Y⁻¹) := by rw [e3]; group
    _ = Z * Z' := by rw [hZ]; exact h5.eq.symm

@[expose] def commB (a b : Fin Tag.E7.rank → ℤ) : Bool :=
  isRootB .E7 a && isRootB .E7 b && isRootB .E7 (a + b) && (a != b) && (a + b != 0)

@[expose] def commuteB (a b : Fin Tag.E7.rank → ℤ) : Bool :=
  isRootB .E7 a && isRootB .E7 b && !isRootB .E7 (a + b) && (a + b != 0)

@[expose] def pairCommB (a a' b b' : Fin Tag.E7.rank → ℤ) : Bool :=
  commB a b && commB a' b' && commuteB a' b && commuteB a b' && commuteB (a' + b') a &&
    commuteB (a' + b') b && commuteB (a + b) (a' + b')

@[expose] def e7e (i : Fin Tag.E7.rank) : Fin Tag.E7.rank → ℤ := Pi.single i 1

theorem perfect_check :
    (commB (e7e 1) (e7e 3) ∧ commB (e7e 1 + e7e 3) (-e7e 3) ∧
      commB (e7e 3) (e7e 1) ∧ commB (e7e 3 + e7e 1) (-e7e 1) ∧
      commB (-e7e 1) (-e7e 3) ∧ commB (-e7e 1 + -e7e 3) (e7e 3) ∧
      commB (-e7e 3) (-e7e 1) ∧ commB (-e7e 3 + -e7e 1) (e7e 1)) ∧
    (pairCommB (e7e 2) (e7e 4) (e7e 0) (e7e 5) ∧
      pairCommB (e7e 2 + e7e 0) (e7e 4 + e7e 5) (-e7e 0) (-e7e 5) ∧
      pairCommB (e7e 0) (e7e 5) (e7e 2) (e7e 4) ∧
      pairCommB (e7e 0 + e7e 2) (e7e 5 + e7e 4) (-e7e 2) (-e7e 4) ∧
      pairCommB (-e7e 2) (-e7e 4) (-e7e 0) (-e7e 5) ∧
      pairCommB (-e7e 2 + -e7e 0) (-e7e 4 + -e7e 5) (e7e 0) (e7e 5) ∧
      pairCommB (-e7e 0) (-e7e 5) (-e7e 2) (-e7e 4) ∧
      pairCommB (-e7e 0 + -e7e 2) (-e7e 5 + -e7e 4) (e7e 2) (e7e 4)) ∧
    (e7e 1 + e7e 3 + -e7e 3 = e7e 1 ∧ e7e 3 + e7e 1 + -e7e 1 = e7e 3 ∧
      -e7e 1 + -e7e 3 + e7e 3 = -e7e 1 ∧ -e7e 3 + -e7e 1 + e7e 1 = -e7e 3 ∧
      e7e 2 + e7e 0 + -e7e 0 = e7e 2 ∧ e7e 4 + e7e 5 + -e7e 5 = e7e 4 ∧
      e7e 0 + e7e 2 + -e7e 2 = e7e 0 ∧ e7e 5 + e7e 4 + -e7e 4 = e7e 5 ∧
      -e7e 2 + -e7e 0 + e7e 0 = -e7e 2 ∧ -e7e 4 + -e7e 5 + e7e 5 = -e7e 4 ∧
      -e7e 0 + -e7e 2 + e7e 2 = -e7e 0 ∧ -e7e 5 + -e7e 4 + e7e 4 = -e7e 5) := by
  decide +kernel

variable {K : Type} [Field K]


theorem commutator_pinnedX_of_commB [CharP K 2] {a b : Fin Tag.E7.rank → ℤ}
    (h : commB a b = true) (c d : K) :
    ⁅pinnedX .E7 K a c, pinnedX .E7 K b d⁆ = pinnedX .E7 K (a + b) (c * d) := by
  simp only [commB, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hab⟩, hne⟩, h0⟩ := h
  refine CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced CharTwo.two_eq_zero
    (CFSG.SeitzReduction.oddDerivLacedCheck_of_simplyLaced (Or.inr (Or.inr (Or.inl rfl))))
    (isRootB_iff.1 ha) (isRootB_iff.1 hb) hne (fun e => h0 (by rw [e, neg_add_cancel]))
    (isRootB_iff.1 hab) c d

theorem commute_pinnedX_of_commuteB {a b : Fin Tag.E7.rank → ℤ} (h : commuteB a b = true)
    (s t : K) : Commute (pinnedX .E7 K a s) (pinnedX .E7 K b t) := by
  simp only [commuteB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne] at h
  obtain ⟨⟨⟨ha, hb⟩, hab⟩, h0⟩ := h
  exact CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (isRootB_iff.1 ha) (isRootB_iff.1 hb)
    (fun e => h0 (by rw [e, neg_add_cancel])) (not_isRoot_of_isRootB_false hab) s t

theorem commutator_pair_pair [CharP K 2] {a a' b b' : Fin Tag.E7.rank → ℤ}
    (h : pairCommB a a' b b' = true) (c : K) :
    ⁅pinnedX .E7 K a c * pinnedX .E7 K a' c, pinnedX .E7 K b 1 * pinnedX .E7 K b' 1⁆ =
      pinnedX .E7 K (a + b) c * pinnedX .E7 K (a' + b') c := by
  simp only [pairCommB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine uPair_commutator_mul_mul (commute_pinnedX_of_commuteB h3 c 1)
    (commute_pinnedX_of_commuteB h4 c 1) ?_ ?_ (commute_pinnedX_of_commuteB h5 c c)
    (commute_pinnedX_of_commuteB h6 c 1) (commute_pinnedX_of_commuteB h7 c c)
  · rw [commutator_pinnedX_of_commB h1, mul_one]
  · rw [commutator_pinnedX_of_commB h2, mul_one]

theorem commutator_commutator_pinnedX [CharP K 2] {a b : Fin Tag.E7.rank → ℤ}
    (h1 : commB a b = true) (h2 : commB (a + b) (-b) = true) (h3 : a + b + -b = a) (c : K) :
    ⁅⁅pinnedX .E7 K a c, pinnedX .E7 K b 1⁆, pinnedX .E7 K (-b) 1⁆ = pinnedX .E7 K a c := by
  rw [commutator_pinnedX_of_commB h1, commutator_pinnedX_of_commB h2, h3, mul_one, mul_one]

theorem commutator_commutator_pair [CharP K 2] {a a' b b' : Fin Tag.E7.rank → ℤ}
    (h1 : pairCommB a a' b b' = true) (h2 : pairCommB (a + b) (a' + b') (-b) (-b') = true)
    (h3 : a + b + -b = a) (h4 : a' + b' + -b' = a') (c : K) :
    ⁅⁅pinnedX .E7 K a c * pinnedX .E7 K a' c, pinnedX .E7 K b 1 * pinnedX .E7 K b' 1⁆,
        pinnedX .E7 K (-b) 1 * pinnedX .E7 K (-b') 1⁆ =
      pinnedX .E7 K a c * pinnedX .E7 K a' c := by
  rw [commutator_pair_pair h1, commutator_pair_pair h2, h3, h4]

variable (K) in
@[expose] noncomputable def uGX (j : Fin 4) (c : K) : adjointGroup .E7 K :=
  ⟨uOrbitX K j c, uOrbitX_mem_adjointGroup j c⟩

variable (K) in
@[expose] noncomputable def uGY (j : Fin 4) (c : K) : adjointGroup .E7 K :=
  ⟨uOrbitY K j c, uOrbitY_mem_adjointGroup j c⟩

theorem uGX_mem (j : Fin 4) (c : K) : uGX K j c ∈ uF4AS K :=
  subset_closure ⟨j, c, Or.inl rfl⟩

theorem uGY_mem (j : Fin 4) (c : K) : uGY K j c ∈ uF4AS K :=
  subset_closure ⟨j, c, Or.inr rfl⟩

theorem commutator_commutator_mem {G : Type*} [Group G] {H : Subgroup G} {a b d : G}
    (ha : a ∈ H) (hb : b ∈ H) (hd : d ∈ H) : ⁅⁅a, b⁆, d⁆ ∈ ⁅H, H⁆ :=
  commutator_mem_commutator (H.commutator_le_self (commutator_mem_commutator ha hb)) hd

theorem coe_commutator_adjointGroup (a b : adjointGroup .E7 K) :
    ((⁅a, b⁆ : adjointGroup .E7 K) : ModGL .E7 K) = ⁅(a : ModGL .E7 K), (b : ModGL .E7 K)⁆ :=
  map_commutatorElement (adjointGroup .E7 K).subtype a b

theorem uGX_uGY_mem_commutator [CharP K 2] (j : Fin 4) (c : K) :
    uGX K j c ∈ ⁅uF4AS K, uF4AS K⁆ ∧ uGY K j c ∈ ⁅uF4AS K, uF4AS K⁆ := by
  obtain ⟨⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩,
    ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩⟩ := perfect_check
  have ex : ∀ (j : Fin 4) (c : K), (uGX K j c : ModGL .E7 K) = uOrbitX K j c := fun _ _ => rfl
  have ey : ∀ (j : Fin 4) (c : K), (uGY K j c : ModGL .E7 K) = uOrbitY K j c := fun _ _ => rfl
  have key : ∀ {g a b d : adjointGroup .E7 K}, a ∈ uF4AS K → b ∈ uF4AS K → d ∈ uF4AS K →
      ((⁅⁅a, b⁆, d⁆ : adjointGroup .E7 K) : ModGL .E7 K) = g → g ∈ ⁅uF4AS K, uF4AS K⁆ := by
    intro g a b d ha hb hd h
    rw [show g = ⁅⁅a, b⁆, d⁆ from Subtype.ext h.symm]
    exact commutator_commutator_mem ha hb hd
  have cc : ∀ a b d : adjointGroup .E7 K, ((⁅⁅a, b⁆, d⁆ : adjointGroup .E7 K) : ModGL .E7 K) =
      ⁅⁅(a : ModGL .E7 K), (b : ModGL .E7 K)⁆, (d : ModGL .E7 K)⁆ := fun a b d => by
    rw [coe_commutator_adjointGroup, coe_commutator_adjointGroup]
  obtain ⟨x0, x1, x2, x3⟩ := uOrbitX_eq (K := K) c
  obtain ⟨y0, y1, y2, y3⟩ := uOrbitY_eq (K := K) c
  obtain ⟨x0', x1', x2', x3'⟩ := uOrbitX_eq (K := K) 1
  obtain ⟨y0', y1', y2', y3'⟩ := uOrbitY_eq (K := K) 1
  fin_cases j
  · refine ⟨key (uGX_mem 0 c) (uGX_mem 1 1) (uGY_mem 1 1) ?_,
      key (uGY_mem 0 c) (uGY_mem 1 1) (uGX_mem 1 1) ?_⟩
    · rw [cc, ex, ex, ey, x1', y1', ex, show ((⟨0, by decide⟩ : Fin 4)) = 0 from rfl, x0]
      exact commutator_commutator_pinnedX l1 l2 r1 c
    · rw [cc, ey, ey, ex, x1', y1', ey, show ((⟨0, by decide⟩ : Fin 4)) = 0 from rfl, y0]
      have := commutator_commutator_pinnedX (K := K) l5 l6 (by rw [neg_neg]; exact r3) c
      rwa [neg_neg] at this
  · refine ⟨key (uGX_mem 1 c) (uGX_mem 0 1) (uGY_mem 0 1) ?_,
      key (uGY_mem 1 c) (uGY_mem 0 1) (uGX_mem 0 1) ?_⟩
    · rw [cc, ex, ex, ey, x0', y0', ex, show ((⟨1, by decide⟩ : Fin 4)) = 1 from rfl, x1]
      exact commutator_commutator_pinnedX l3 l4 r2 c
    · rw [cc, ey, ey, ex, x0', y0', ey, show ((⟨1, by decide⟩ : Fin 4)) = 1 from rfl, y1]
      have := commutator_commutator_pinnedX (K := K) l7 l8 (by rw [neg_neg]; exact r4) c
      rwa [neg_neg] at this
  · refine ⟨key (uGX_mem 2 c) (uGX_mem 3 1) (uGY_mem 3 1) ?_,
      key (uGY_mem 2 c) (uGY_mem 3 1) (uGX_mem 3 1) ?_⟩
    · rw [cc, ex, ex, ey, x3', y3', ex, show ((⟨2, by decide⟩ : Fin 4)) = 2 from rfl, x2]
      exact commutator_commutator_pair p1 p2 r5 r6 c
    · rw [cc, ey, ey, ex, x3', y3', ey, show ((⟨2, by decide⟩ : Fin 4)) = 2 from rfl, y2]
      have := commutator_commutator_pair (K := K) p5 p6 (by rw [neg_neg]; exact r9)
        (by rw [neg_neg]; exact r10) c
      rwa [neg_neg, neg_neg] at this
  · refine ⟨key (uGX_mem 3 c) (uGX_mem 2 1) (uGY_mem 2 1) ?_,
      key (uGY_mem 3 c) (uGY_mem 2 1) (uGX_mem 2 1) ?_⟩
    · rw [cc, ex, ex, ey, x2', y2', ex, show ((⟨3, by decide⟩ : Fin 4)) = 3 from rfl, x3]
      exact commutator_commutator_pair p3 p4 r7 r8 c
    · rw [cc, ey, ey, ex, x2', y2', ey, show ((⟨3, by decide⟩ : Fin 4)) = 3 from rfl, y3]
      have := commutator_commutator_pair (K := K) p7 p8 (by rw [neg_neg]; exact r11)
        (by rw [neg_neg]; exact r12) c
      rwa [neg_neg, neg_neg] at this

theorem commutator_uF4AS [CharP K 2] : ⁅uF4AS K, uF4AS K⁆ = uF4AS K := by
  refine le_antisymm (Subgroup.commutator_le_self _) ((closure_le _).2 ?_)
  rintro g ⟨j, c, h | h⟩
  · rw [show g = uGX K j c from Subtype.ext h]
    exact (uGX_uGY_mem_commutator j c).1
  · rw [show g = uGY K j c from Subtype.ext h]
    exact (uGX_uGY_mem_commutator j c).2

theorem commutator_uF4 [CharP K 2] : ⁅uF4 K, uF4 K⁆ = uF4 K := by
  rw [uF4, ← Subgroup.map_commutator, commutator_uF4AS]

theorem uF4_le_perfectCore_centralizer [CharP K 2] :
    uF4 K ≤ perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) :=
  CFSG.Quasithin.le_perfectCore_of_perfect uF4_le_centralizer commutator_uF4

theorem uF4_le_perfectCore_leviU_inf_centralizer [CharP K 2] :
    uF4 K ≤ perfectCore (leviU K ⊓ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) :=
  CFSG.Quasithin.le_perfectCore_of_perfect uF4_le_leviU_inf_centralizer commutator_uF4

theorem commutator_radicalU_uF4 [CharP K 2] :
    ⁅radicalU K, uF4 K⁆ ≤ perfectCore (centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) := by
  set C := centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))
  have hN := CFSG.Quasithin.perfectCore_normal C
  rw [Subgroup.commutator_le]
  intro r hr f hf
  have hrC : r ∈ C := radicalU_le_centralizer hr
  have hfP : f ∈ perfectCore C := uF4_le_perfectCore_centralizer hf
  have hfC : f ∈ C := CFSG.Quasithin.perfectCore_le C hfP
  have hconj : r * f * r⁻¹ ∈ perfectCore C := by
    have h := hN.conj_mem ⟨f, hfC⟩ (mem_subgroupOf.2 hfP) ⟨r, hrC⟩
    rw [mem_subgroupOf] at h
    exact h
  rw [commutatorElement_def]
  exact mul_mem hconj (inv_mem hfP)

end CFSG.SeitzReduction.E7Pilot
