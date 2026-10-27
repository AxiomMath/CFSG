module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCMax
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCType
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

section Generic

variable {G X : Type*} [Group G] [MulAction G X]

theorem not_mem_zpowers_of_apply_eq {t g : G} {x : X} (ht : t • x = x) (hg : g • x ≠ x) :
    g ∉ Subgroup.zpowers t := by
  intro hmem
  have hst : t ∈ MulAction.stabilizer G x := (MulAction.mem_stabilizer_iff).2 ht
  have : g ∈ MulAction.stabilizer G x :=
    (Subgroup.zpowers_le (H := MulAction.stabilizer G x)).2 hst hmem
  exact hg ((MulAction.mem_stabilizer_iff).1 this)

theorem not_mem_zpowers_of_apply_ne {t g : G} {x : X} (ht3 : t ^ 3 = 1) (htx : t • x ≠ x)
    (hg1 : g ≠ 1) (hgx : g • x = x) : g ∉ Subgroup.zpowers t := by
  intro hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h3z : t ^ (3 : ℤ) = 1 := by exact_mod_cast ht3
  have hk : t ^ k = t ^ (k % 3) := by
    have hk' : k = k % 3 + 3 * (k / 3) := by omega
    conv_lhs => rw [hk']
    rw [zpow_add, zpow_mul, h3z, one_zpow, mul_one]
  rw [hk] at hgx hg1
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · rw [h] at hg1
    exact hg1 (zpow_zero t)
  · rw [h, zpow_one] at hgx
    exact htx hgx
  · rw [h] at hgx
    apply htx
    have e : t * t ^ (2 : ℤ) = 1 := by
      rw [← h3z]
      group
    calc t • x = t • (t ^ (2 : ℤ) • x) := by rw [hgx]
      _ = (t * t ^ (2 : ℤ)) • x := (mul_smul _ _ _).symm
      _ = x := by rw [e, one_smul]

theorem coe_mem_zpowers_of_mem {K : Subgroup G} {r d : ↥K} (h : r ∈ Subgroup.zpowers d) :
    (r : G) ∈ Subgroup.zpowers (d : G) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simp⟩

end Generic

section Torus

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

structure FrameOf (Q : QuadraticForm (ZMod 2) V) (Bb : Subgroup ↥(orthDerived Q)) (m : ℕ)
    (l : List (V × V)) : Prop where
  isFrame : IsFrame Q l
  length_eq : l.length = m
  map_eq : Bb.map (orthDerived Q).subtype = torus Q l

variable {Bb : Subgroup ↥(orthDerived Q)} {m : ℕ} {l : List (V × V)}

theorem FrameOf.mem_torus (h : FrameOf Q Bb m l) {b : ↥(orthDerived Q)} (hb : b ∈ Bb) :
    (b : V ≃ₗ[ZMod 2] V) ∈ torus Q l := by
  rw [← h.map_eq]
  exact Subgroup.mem_map_of_mem _ hb

theorem FrameOf.exists_mem_rot (h : FrameOf Q Bb m l) {p : V × V} (hp : p ∈ l) :
    ∃ b ∈ Bb, (b : V ≃ₗ[ZMod 2] V) = rot Q p.1 p.2 := by
  have := rot_mem_torus (Q := Q) hp
  rw [← h.map_eq] at this
  obtain ⟨b, hb, hbp⟩ := Subgroup.mem_map.1 this
  exact ⟨b, hb, hbp⟩

end Torus

section Frame

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_frame_of_card (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hbound : ∀ E : Subgroup ↥(orthDerived Q), CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3 ^ (n - 1))
    {Bb : Subgroup ↥(orthDerived Q)} (hBb : CFSG.Open.IsElemAbelian 3 Bb)
    (hcard : Nat.card Bb = 3 ^ (n - 1)) : ∃ l : List (V × V), FrameOf Q Bb (n - 1) l := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have hE : CFSG.Open.IsElemAbelian 3 (Bb.map (orthDerived Q).subtype) :=
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.isElemAbelian_map_subtype_iff Bb).2 hBb
  have hEΩ : Bb.map (orthDerived Q).subtype ≤ orthDerived Q :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.map_subtype_le Bb
  have hmax : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V), E' ≤ orthDerived Q →
      CFSG.Open.IsElemAbelian 3 E' → Nat.card E' ≤ Nat.card (Bb.map (orthDerived Q).subtype) := by
    intro E' hE' hE'ab
    have h := hbound (E'.subgroupOf (orthDerived Q))
      ((CFSG.LocalAnalysis.GLTheoremA.Y10F.isElemAbelian_subgroupOf_iff hE').2 hE'ab)
    rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.card_subgroupOf hE'] at h
    rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.card_map_subtype, hcard]
    exact h
  obtain ⟨l, hl, hEq, -⟩ := exists_frame_max hQ hEΩ hE hmax
  refine ⟨l, ⟨hl, ?_, hEq⟩⟩
  have hc : Nat.card (torus Q l) = 3 ^ l.length := card_torus hl
  rw [← hEq, CFSG.LocalAnalysis.GLTheoremA.Y10F.card_map_subtype, hcard] at hc
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hc).symm

theorem finrank_perpL_eq_two {l : List (V × V)} (hl : IsFrame Q l) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hlen : l.length = n - 1) (hn : 1 ≤ n) :
    finrank (ZMod 2) (perpL Q l) = 2 := by
  have h := Submodule.finrank_add_eq_of_isCompl hl.isCompl
  rw [hl.finrank_Wspan] at h
  omega

theorem finrank_perpPlane (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : V × V}
    (hp : MinusPair Q p.1 p.2) : finrank (ZMod 2) (perpPlane Q p) = finrank (ZMod 2) V - 2 := by
  rw [perpPlane, LinearMap.BilinForm.finrank_orthogonal hQ, hp.finrank_planeSpan]

private theorem torus_apply_planeSpan_cases_aux1 {l : List (V × V)} (hl : IsFrame Q l)
    {p : V × V} (hp : p ∈ l) : ∀ t ∈ torus Q l, ∀ x ∈ planeSpan p, t x ∈ planeSpan p := by
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨q, hq, rfl⟩ := hg
      intro x hx
      by_cases hqp : q = p
      · subst q
        have h1 : rot Q p.1 p.2 x - x ∈ planeSpan p := rot_sub_mem_span (hl.pair p hp) x
        have h2 : rot Q p.1 p.2 x = (rot Q p.1 p.2 x - x) + x := by abel
        rw [h2]
        exact Submodule.add_mem _ h1 hx
      · have hperp : PairPerp Q p q := hl.perp_of_mem_of_ne hp hq (fun h => hqp h.symm)
        obtain ⟨e1, e2, e3, e4⟩ := hperp
        have hpol1 : polar Q x q.1 = 0 := by
          obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p x).1 hx
          rw [polar_add_left, polar_smul_left, polar_smul_left, e1, e3]; simp
        have hpol2 : polar Q x q.2 = 0 := by
          obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p x).1 hx
          rw [polar_add_left, polar_smul_left, polar_smul_left, e2, e4]; simp
        rw [rot_apply_of_perp (hl.pair q hq) hpol1 hpol2]
        exact hx
  | one => intro x hx; simpa using hx
  | mul s u hs hu ihs ihu =>
      intro x hx
      rw [LinearEquiv.mul_apply]
      exact ihs (u x) (ihu x hx)
  | inv t ht iht =>
      intro x hx
      show t.symm x ∈ planeSpan p
      have ht3 : t ^ 3 = 1 := torus_pow_three hl t ht
      have hx3 : t (t (t x)) = x := by
        have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) ht3
        simpa [pow_succ, pow_two, LinearEquiv.mul_apply] using h
      have hsymm : t.symm x = t (t x) := by
        conv_lhs => rw [← hx3]
        exact LinearEquiv.symm_apply_apply t (t (t x))
      rw [hsymm]
      exact iht (t x) (iht x hx)

private theorem torus_apply_planeSpan_cases_aux2 {l : List (V × V)} (hl : IsFrame Q l)
    {p : V × V} (hp : p ∈ l) :
    ∀ t ∈ torus Q l, ∃ k : ℕ, ∀ x ∈ planeSpan p, t x = (rot Q p.1 p.2 ^ k) x := by
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨q, hq, rfl⟩ := hg
      by_cases hqp : q = p
      · subst q
        exact ⟨1, fun x hx => by rw [pow_one]⟩
      · refine ⟨0, fun x hx => ?_⟩
        have hperp : PairPerp Q p q := hl.perp_of_mem_of_ne hp hq (fun h => hqp h.symm)
        obtain ⟨e1, e2, e3, e4⟩ := hperp
        have hpol1 : polar Q x q.1 = 0 := by
          obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p x).1 hx
          rw [polar_add_left, polar_smul_left, polar_smul_left, e1, e3]; simp
        have hpol2 : polar Q x q.2 = 0 := by
          obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p x).1 hx
          rw [polar_add_left, polar_smul_left, polar_smul_left, e2, e4]; simp
        rw [rot_apply_of_perp (hl.pair q hq) hpol1 hpol2]
        simp
  | one => exact ⟨0, fun x hx => by simp⟩
  | mul s u hs hu ihs ihu =>
      obtain ⟨j, hj⟩ := ihs
      obtain ⟨i, hi⟩ := ihu
      refine ⟨j + i, fun x hx => ?_⟩
      have hux : u x ∈ planeSpan p := torus_apply_planeSpan_cases_aux1 hl hp u hu x hx
      rw [LinearEquiv.mul_apply, hj (u x) hux, hi x hx, ← LinearEquiv.mul_apply, ← pow_add]
  | inv t ht iht =>
      obtain ⟨k, hk⟩ := iht
      refine ⟨k + k, fun x hx => ?_⟩
      show t.symm x = (rot Q p.1 p.2 ^ (k + k)) x
      have ht3 : t ^ 3 = 1 := torus_pow_three hl t ht
      have hx3 : t (t (t x)) = x := by
        have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) ht3
        simpa [pow_succ, pow_two, LinearEquiv.mul_apply] using h
      have hsymm : t.symm x = t (t x) := by
        conv_lhs => rw [← hx3]
        exact LinearEquiv.symm_apply_apply t (t (t x))
      have htx : t x ∈ planeSpan p := torus_apply_planeSpan_cases_aux1 hl hp t ht x hx
      rw [hsymm]
      have h1 : t (t x) = (rot Q p.1 p.2 ^ k) ((rot Q p.1 p.2 ^ k) x) := by
        rw [hk (t x) htx, hk x hx]
      rw [h1, ← LinearEquiv.mul_apply, ← pow_add]

private theorem torus_apply_planeSpan_cases_aux3 {p : V × V} (h : MinusPair Q p.1 p.2) :
    ∀ x ∈ planeSpan p, rot Q p.1 p.2 (rot Q p.1 p.2 x) + rot Q p.1 p.2 x + x = 0 := by
  intro x hx
  have hρ3 : rot Q p.1 p.2 ^ 3 = 1 := rot_pow_three h
  obtain ⟨y, hy⟩ := exists_rot_sub_eq h hx
  have hpow : rot Q p.1 p.2 (rot Q p.1 p.2 (rot Q p.1 p.2 y)) = y := by
    have hh := congrArg (fun e : V ≃ₗ[ZMod 2] V => e y) hρ3
    simpa [pow_succ, pow_two, LinearEquiv.mul_apply] using hh
  rw [← hy]
  simp only [map_sub]
  rw [hpow]
  abel

private theorem torus_apply_planeSpan_cases_aux4 {p : V × V} (h : MinusPair Q p.1 p.2) :
    ∀ x ∈ planeSpan p, rot Q p.1 p.2 x = x → x = 0 := by
  intro x hx hfix
  have hh := torus_apply_planeSpan_cases_aux3 h x hx
  have h1 : x + x + x = 0 := by simpa only [hfix] using hh
  have h2 : x + x = 0 := vec_add_self x
  calc x = (x + x + x) - (x + x) := by abel
    _ = 0 := by rw [h1, h2, sub_zero]

private theorem torus_apply_planeSpan_cases_aux5 {p : V × V} (h : MinusPair Q p.1 p.2) :
    (rot Q p.1 p.2 ^ 2) p.1 ≠ p.1 := by
  intro hcon
  rw [pow_two, LinearEquiv.mul_apply, rot_apply_left h, rot_apply_right h] at hcon
  have hz : p.2 = 0 := by simpa using hcon
  have hq := h.qb
  rw [hz, QuadraticMap.map_zero] at hq
  exact zero_ne_one hq

private theorem torus_apply_planeSpan_cases_aux6 {l : List (V × V)} (hl : IsFrame Q l) {p : V × V}
    (hp : p ∈ l) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ torus Q l) {ρ : V ≃ₗ[ZMod 2] V}
    (hρ : ρ = rot Q p.1 p.2) (ht_eq : ∀ x ∈ planeSpan p, t x = ρ x) :
    t p.1 ≠ p.1 ∧ (∀ x ∈ planeSpan p, t (t x) + t x + x = 0) ∧
      ∀ x ∈ planeSpan p, t x = x → x = 0 := by
  have hpoly : ∀ x ∈ planeSpan p, ρ (ρ x) + ρ x + x = 0 := by
    intro x hx; rw [hρ]; exact torus_apply_planeSpan_cases_aux3 (hl.pair p hp) x hx
  have hzero : ∀ x ∈ planeSpan p, ρ x = x → x = 0 := by
    intro x hx hx'; rw [hρ] at hx'
    exact torus_apply_planeSpan_cases_aux4 (hl.pair p hp) x hx hx'
  refine ⟨?_, ?_, ?_⟩
  · rw [ht_eq p.1 (left_mem_planeSpan p), hρ, rot_apply_left (hl.pair p hp)]
    exact fun h => (hl.pair p hp).ne h.symm
  · intro x hx
    have htx : t x ∈ planeSpan p := torus_apply_planeSpan_cases_aux1 hl hp t ht x hx
    rw [ht_eq (t x) htx, ht_eq x hx]
    simpa [add_comm, add_left_comm, add_assoc] using hpoly x hx
  · intro x hx hx'
    exact hzero x hx (by rw [← ht_eq x hx]; exact hx')

private theorem torus_apply_planeSpan_cases_aux7 {l : List (V × V)} (hl : IsFrame Q l) {p : V × V}
    (hp : p ∈ l) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ torus Q l) {ρ : V ≃ₗ[ZMod 2] V}
    (hρ : ρ = rot Q p.1 p.2) (hρ3 : ρ ^ 3 = 1) (ht_eq : ∀ x ∈ planeSpan p, t x = (ρ ^ 2) x) :
    t p.1 ≠ p.1 ∧ (∀ x ∈ planeSpan p, t (t x) + t x + x = 0) ∧
      ∀ x ∈ planeSpan p, t x = x → x = 0 := by
  have hpoly : ∀ x ∈ planeSpan p, ρ (ρ x) + ρ x + x = 0 := by
    intro x hx; rw [hρ]; exact torus_apply_planeSpan_cases_aux3 (hl.pair p hp) x hx
  have hzero : ∀ x ∈ planeSpan p, ρ x = x → x = 0 := by
    intro x hx hx'; rw [hρ] at hx'
    exact torus_apply_planeSpan_cases_aux4 (hl.pair p hp) x hx hx'
  have hρ4 : ρ ^ 4 = ρ := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hρ3, one_mul, pow_one]
  have hcomb : ∀ x, (ρ ^ 2) ((ρ ^ 2) x) = ρ x := by
    intro x
    rw [← LinearEquiv.mul_apply, ← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, hρ4]
  have hsq : ∀ x, (ρ ^ 2) x = ρ (ρ x) := by
    intro x; rw [pow_two, LinearEquiv.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [ht_eq p.1 (left_mem_planeSpan p)]
    intro hcon
    refine torus_apply_planeSpan_cases_aux5 (hl.pair p hp) ?_
    rwa [hρ] at hcon
  · intro x hx
    have htx : t x ∈ planeSpan p := torus_apply_planeSpan_cases_aux1 hl hp t ht x hx
    rw [ht_eq (t x) htx, ht_eq x hx, hcomb x]
    simpa [hsq x, add_comm, add_left_comm, add_assoc] using hpoly x hx
  · intro x hx hx'
    have hρ2x : (ρ ^ 2) x = x := by rw [← ht_eq x hx]; exact hx'
    have hL : ρ ((ρ ^ 2) x) = x := by
      rw [← LinearEquiv.mul_apply, ← pow_succ', show (2 : ℕ) + 1 = 3 by norm_num, hρ3]
      rfl
    have hρx : ρ x = x := by
      have h := congrArg (fun v => ρ v) hρ2x
      rw [hL] at h
      exact h.symm
    exact hzero x hx hρx

theorem torus_apply_planeSpan_cases {l : List (V × V)} (hl : IsFrame Q l) {p : V × V} (hp : p ∈ l)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ torus Q l) :
    (∀ x ∈ planeSpan p, t x = x) ∨
      (t p.1 ≠ p.1 ∧ (∀ x ∈ planeSpan p, t (t x) + t x + x = 0) ∧
        ∀ x ∈ planeSpan p, t x = x → x = 0) := by
  obtain ⟨k, hk⟩ := torus_apply_planeSpan_cases_aux2 hl hp t ht
  set ρ := rot Q p.1 p.2 with hρ
  have hρ3 : ρ ^ 3 = 1 := by rw [hρ]; exact rot_pow_three (hl.pair p hp)
  have hkmod : ∀ x ∈ planeSpan p, t x = (ρ ^ (k % 3)) x := by
    intro x hx; rw [hk x hx, pow_eq_pow_mod k hρ3]
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · left
    intro x hx
    rw [hkmod x hx, h0]
    simp
  · right
    refine torus_apply_planeSpan_cases_aux6 hl hp ht hρ ?_
    intro x hx; rw [hkmod x hx, h1, pow_one]
  · right
    refine torus_apply_planeSpan_cases_aux7 hl hp ht hρ hρ3 ?_
    intro x hx; rw [hkmod x hx, h2]

theorem fixes_planeSpan_of_apply_left {l : List (V × V)} (hl : IsFrame Q l) {p : V × V} (hp : p ∈ l)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ torus Q l) (h1 : t p.1 = p.1) : ∀ x ∈ planeSpan p, t x = x := by
  rcases torus_apply_planeSpan_cases hl hp ht with h | h
  · exact h
  · exact absurd h1 h.1

theorem apply_sq_add_apply_add_self_of_apply_left_ne {l : List (V × V)} (hl : IsFrame Q l) {p : V × V}
    (hp : p ∈ l) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ torus Q l) (h1 : t p.1 ≠ p.1) :
    ∀ x ∈ planeSpan p, t (t x) + t x + x = 0 := by
  rcases torus_apply_planeSpan_cases hl hp ht with h | h
  · exact absurd (h p.1 (left_mem_planeSpan p)) h1
  · exact h.2.1

theorem eq_zero_of_apply_eq_of_apply_left_ne {l : List (V × V)} (hl : IsFrame Q l) {p : V × V}
    (hp : p ∈ l) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ torus Q l) (h1 : t p.1 ≠ p.1) :
    ∀ x ∈ planeSpan p, t x = x → x = 0 := by
  rcases torus_apply_planeSpan_cases hl hp ht with h | h
  · exact absurd (h p.1 (left_mem_planeSpan p)) h1
  · exact h.2.2

private theorem eq_one_of_forall_apply_left_aux1 {l : List (V × V)} (hl : IsFrame Q l)
    {t : V ≃ₗ[ZMod 2] V} (h : ∀ p ∈ l, ∀ x ∈ planeSpan p, t x = x) :
    ∀ x ∈ Wspan l, t x = x := by
  induction l with
  | nil =>
    intro x hx
    rw [Wspan_nil, Submodule.mem_bot] at hx
    subst hx
    simp
  | cons p l ih =>
    intro x hx
    obtain ⟨-, -, hl'⟩ := isFrame_cons.1 hl
    rw [Wspan_cons, Submodule.mem_sup] at hx
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    rw [map_add, h p (List.mem_cons_self) u hu,
      ih hl' (fun q hq => h q (List.mem_cons_of_mem _ hq)) w hw]

theorem eq_one_of_forall_apply_left {l : List (V × V)} (hl : IsFrame Q l) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ torus Q l) (h : ∀ p ∈ l, t p.1 = p.1) : t = 1 := by
  have hW : ∀ x ∈ Wspan l, t x = x :=
    eq_one_of_forall_apply_left_aux1 hl
      (fun p hp => fixes_planeSpan_of_apply_left hl hp ht (h p hp))
  have hP : ∀ x ∈ perpL Q l, t x = x := by
    intro x hx
    rw [mem_perpL_iff] at hx
    refine torus_fixes hl (fun p hp => ⟨?_, ?_⟩) t ht
    · rw [← polar_comm Q p.1 x]
      exact (hx p hp).1
    · rw [← polar_comm Q p.2 x]
      exact (hx p hp).2
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ Wspan l ⊔ perpL Q l := by
    rw [hl.isCompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, v', hv', rfl⟩ := Submodule.mem_sup.1 hv
  calc t (w + v') = t w + t v' := map_add t w v'
    _ = w + v' := by rw [hW w hw, hP v' hv']
    _ = (1 : V ≃ₗ[ZMod 2] V) (w + v') := rfl

theorem fixedSpace_eq_perpL {l : List (V × V)} (hl : IsFrame Q l) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ torus Q l) (h : ∀ p ∈ l, t p.1 ≠ p.1) : fixedSpace t = perpL Q l := by
  apply le_antisymm
  · intro v hv
    rw [mem_perpL_iff]
    rw [mem_fixedSpace] at hv
    have hiso : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := torus_le_orthogonalGroup l ht
    let φ : V →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => polar Q x v
        map_add' := fun x y => by simp only [polar_add_left]
        map_smul' := fun c x => by simp only [polar_smul_left, RingHom.id_apply] }
    have hφt : ∀ y : V, φ (t y) = φ y := by
      intro y
      show polar Q (t y) v = polar Q y v
      have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hiso y v
      rwa [hv] at this
    intro p hp
    rcases torus_apply_planeSpan_cases hl hp ht with hcase | hcase
    · exact absurd (hcase p.1 (left_mem_planeSpan p)) (h p hp)
    · have key : ∀ x ∈ planeSpan p, polar Q x v = 0 := by
        intro x hx
        have hsum : φ x + φ x + φ x = 0 := by
          have := congrArg φ (hcase.2.1 x hx)
          simpa only [map_add, hφt, map_zero] using this
        have h2 : φ x + φ x = 0 := CharTwo.add_self_eq_zero (φ x)
        rw [h2, zero_add] at hsum
        exact hsum
      exact ⟨key p.1 (left_mem_planeSpan p), key p.2 (right_mem_planeSpan p)⟩
  · intro v hv
    rw [mem_fixedSpace]
    exact torus_fixes hl (fun p hp => by
      obtain ⟨e1, e2⟩ := (mem_perpL_iff l v).1 hv p hp
      exact ⟨(polar_comm Q v p.1).trans e1, (polar_comm Q v p.2).trans e2⟩) t ht

private theorem fixedSpace_eq_perpPlane_aux1 {l₁ l₂ : List (V × V)} (h : l₁.Sublist l₂) :
    Wspan l₁ ≤ Wspan l₂ := by
  induction h with
  | slnil => exact le_rfl
  | cons a h ih => exact ih.trans le_sup_right
  | cons_cons a h ih =>
      rw [Wspan_cons, Wspan_cons]
      exact sup_le le_sup_left (ih.trans le_sup_right)

private theorem fixedSpace_eq_perpPlane_aux2 [DecidableEq V] (p : V × V) (l : List (V × V)) :
    Wspan l ≤ planeSpan p ⊔ Wspan (l.filter (fun r => decide (r ≠ p))) := by
  induction l with
  | nil => exact bot_le
  | cons q l ih =>
      by_cases hq : decide (q ≠ p) = true
      · rw [List.filter_cons_of_pos (p := fun r => decide (r ≠ p)) (a := q) (l := l) hq,
          Wspan_cons]
        have h1 : planeSpan q ≤
            planeSpan p ⊔ (planeSpan q ⊔ Wspan (l.filter (fun r => decide (r ≠ p)))) :=
          le_trans le_sup_left le_sup_right
        have h2 : planeSpan p ⊔ Wspan (l.filter (fun r => decide (r ≠ p))) ≤
            planeSpan p ⊔ (planeSpan q ⊔ Wspan (l.filter (fun r => decide (r ≠ p)))) :=
          sup_le le_sup_left (le_trans le_sup_right le_sup_right)
        exact sup_le h1 (ih.trans h2)
      · rw [List.filter_cons_of_neg (p := fun r => decide (r ≠ p)) (a := q) (l := l) hq,
          Wspan_cons]
        have hqp : q = p := by
          by_contra hne
          exact hq (decide_eq_true hne)
        subst hqp
        exact sup_le le_sup_left ih

private theorem fixedSpace_eq_perpPlane_aux3 [DecidableEq V] (p : V × V) {l : List (V × V)}
    (hp : p ∈ l) :
    Wspan l = planeSpan p ⊔ Wspan (l.filter (fun q => decide (q ≠ p))) := by
  refine le_antisymm (fixedSpace_eq_perpPlane_aux2 p l) ?_
  exact sup_le (planeSpan_le_Wspan hp) (fixedSpace_eq_perpPlane_aux1 List.filter_sublist)

private theorem fixedSpace_eq_perpPlane_aux4 [DecidableEq V] {l : List (V × V)} {p : V × V}
    (hl : IsFrame Q l) (hp : p ∈ l) :
    ∀ q ∈ l.filter (fun r => decide (r ≠ p)), PairPerp Q p q := by
  intro q hq
  rw [List.mem_filter] at hq
  obtain ⟨hql, hqne⟩ := hq
  exact hl.perp_of_mem_of_ne hp hql (fun heq => (of_decide_eq_true hqne) heq.symm)

private theorem fixedSpace_eq_perpPlane_aux5 [DecidableEq V] {l : List (V × V)} {p : V × V}
    (hl : IsFrame Q l) (hp : p ∈ l) :
    Wspan (l.filter (fun r => decide (r ≠ p))) ≤ perpPlane Q p := by
  intro w hw
  obtain ⟨h1, h2⟩ := polar_Wspan_eq_zero (l := l.filter (fun r => decide (r ≠ p)))
    (p := p) (fixedSpace_eq_perpPlane_aux4 hl hp) hw
  exact (mem_perpPlane_iff p w).2 ⟨h1, h2⟩

private theorem fixedSpace_eq_perpPlane_aux6 {l : List (V × V)} {p : V × V} (hp : p ∈ l) :
    perpL Q l ≤ perpPlane Q p := by
  intro x hx
  exact (mem_perpPlane_iff p x).2 ((mem_perpL_iff l x).1 hx p hp)

private theorem fixedSpace_eq_perpPlane_aux7 {l : List (V × V)} {t : V ≃ₗ[ZMod 2] V} :
    (∀ q ∈ l, ∀ x ∈ planeSpan q, t x = x) → ∀ w ∈ Wspan l, t w = w := by
  induction l with
  | nil =>
      intro h w hw
      rw [Wspan_nil, Submodule.mem_bot] at hw
      rw [hw, map_zero]
  | cons q l ih =>
      intro h w hw
      rw [Wspan_cons] at hw
      obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add, h q List.mem_cons_self u hu,
        ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) w' hw']

private theorem fixedSpace_eq_perpPlane_aux8 [DecidableEq V] {l : List (V × V)} {p₀ : V × V}
    {t : V ≃ₗ[ZMod 2] V} (hl : IsFrame Q l) (ht : t ∈ torus Q l)
    (h : ∀ p ∈ l, p ≠ p₀ → t p.1 = p.1) :
    ∀ w ∈ Wspan (l.filter (fun q => decide (q ≠ p₀))), t w = w := by
  refine fixedSpace_eq_perpPlane_aux7 (fun q hq x hx => ?_)
  rw [List.mem_filter] at hq
  exact fixes_planeSpan_of_apply_left hl hq.1 ht (h q hq.1 (of_decide_eq_true hq.2)) x hx

private theorem fixedSpace_eq_perpPlane_aux9 {l : List (V × V)} {t : V ≃ₗ[ZMod 2] V}
    (hl : IsFrame Q l) (ht : t ∈ torus Q l) : ∀ x ∈ perpL Q l, t x = x := by
  intro x hx
  exact torus_fixes hl
    (fun p hp => (mem_perpPlane_iff' p x).1 (fixedSpace_eq_perpPlane_aux6 hp hx)) t ht

private theorem fixedSpace_eq_perpPlane_aux10 [DecidableEq V] {l : List (V × V)} {p : V × V}
    (hl : IsFrame Q l) (hp : p ∈ l) (x : V) :
    ∃ xp ∈ planeSpan p,
      ∃ x' ∈ Wspan (l.filter (fun q => decide (q ≠ p))) ⊔ perpL Q l, x = xp + x' := by
  have hx : x ∈ Wspan l ⊔ perpL Q l := by rw [hl.isCompl.sup_eq_top]; trivial
  obtain ⟨w, hw, v', hv', rfl⟩ := Submodule.mem_sup.1 hx
  have hw' : w ∈ planeSpan p ⊔ Wspan (l.filter (fun q => decide (q ≠ p))) := by
    rw [← fixedSpace_eq_perpPlane_aux3 p hp]; exact hw
  obtain ⟨xp, hxp, y, hy, rfl⟩ := Submodule.mem_sup.1 hw'
  exact ⟨xp, hxp, y + v', Submodule.add_mem_sup hy hv', by abel⟩

private theorem fixedSpace_eq_perpPlane_aux11 [DecidableEq V] {l : List (V × V)} {p : V × V}
    (hl : IsFrame Q l) (hp : p ∈ l) {x' : V}
    (hx' : x' ∈ Wspan (l.filter (fun q => decide (q ≠ p))) ⊔ perpL Q l) :
    x' ∈ perpPlane Q p := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx'
  exact Submodule.add_mem _ (fixedSpace_eq_perpPlane_aux5 hl hp ha)
    (fixedSpace_eq_perpPlane_aux6 hp hb)

private theorem fixedSpace_eq_perpPlane_aux12 [DecidableEq V] {l : List (V × V)} {p₀ : V × V}
    {t : V ≃ₗ[ZMod 2] V} (hl : IsFrame Q l) (ht : t ∈ torus Q l)
    (h : ∀ p ∈ l, p ≠ p₀ → t p.1 = p.1) {x' : V}
    (hx' : x' ∈ Wspan (l.filter (fun q => decide (q ≠ p₀))) ⊔ perpL Q l) : t x' = x' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx'
  rw [map_add, fixedSpace_eq_perpPlane_aux8 hl ht h a ha, fixedSpace_eq_perpPlane_aux9 hl ht b hb]

theorem fixedSpace_eq_perpPlane {l : List (V × V)} (hl : IsFrame Q l) {p₀ : V × V} (hp₀ : p₀ ∈ l)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ torus Q l) (h0 : t p₀.1 ≠ p₀.1)
    (h : ∀ p ∈ l, p ≠ p₀ → t p.1 = p.1) : fixedSpace t = perpPlane Q p₀ := by
  classical
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_fixedSpace] at hx
    obtain ⟨xp, hxp, x', hx', rfl⟩ := fixedSpace_eq_perpPlane_aux10 hl hp₀ x
    have htx' : t x' = x' := fixedSpace_eq_perpPlane_aux12 hl ht h hx'
    have htxp : t xp = xp := by
      have h1 : t xp + x' = xp + x' := by
        simpa only [map_add, htx'] using hx
      exact add_right_cancel h1
    have hxp0 : xp = 0 :=
      eq_zero_of_apply_eq_of_apply_left_ne hl hp₀ ht h0 xp hxp htxp
    rw [hxp0, zero_add]
    exact fixedSpace_eq_perpPlane_aux11 hl hp₀ hx'
  · intro x hx
    rw [mem_fixedSpace]
    obtain ⟨xp, hxp, x', hx', rfl⟩ := fixedSpace_eq_perpPlane_aux10 hl hp₀ x
    have hxp_perp : xp ∈ perpPlane Q p₀ := by
      have hmem : (xp + x') - x' ∈ perpPlane Q p₀ :=
        Submodule.sub_mem _ hx (fixedSpace_eq_perpPlane_aux11 hl hp₀ hx')
      rwa [add_sub_cancel_right] at hmem
    have hxp0 : xp = 0 :=
      MinusPair.eq_zero_of_mem_planeSpan_of_mem_perp (hl.pair p₀ hp₀) hxp hxp_perp
    rw [map_add, hxp0, fixedSpace_eq_perpPlane_aux12 hl ht h hx']
    simp

end Frame

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
