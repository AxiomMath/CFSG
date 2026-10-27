module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResDD
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResDB

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer
open CFSG.GH74.GLS.Stage2.Final.Thm6.L20 (PairShape)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

structure DiagAt (z : G) (k : Stage12.Kind) (S : Subgroup G) (s : G) (I O O' : Subgroup G) :
    Prop where
  ctx : Stage2Ctx G z k S
  two : ¬ TypeOneCase G k
  s_mem : s ∈ S
  s_ne : s ≠ z
  s_conj : IsConj z s
  s_not : ¬ IsConj z (z * s)
  I_C : I ≤ Cen z
  I_s : I ≤ centralizer ({s} : Set G)
  I_perf : ⁅I, I⁆ = I
  O_C : O ≤ Cen z
  O_odd : Odd (Nat.card ↥O)
  O_norm : ∀ l ∈ Ixz z (s * z), ∀ o ∈ O, l * o * l⁻¹ ∈ O
  cov : ∀ l ∈ Ixz z (s * z), ∃ i ∈ I, ∃ o ∈ O, l = i * o
  O'_C : O' ≤ Cen z
  O'_odd : Odd (Nat.card ↥O')
  O'_norm : ∀ i ∈ I, ∀ o ∈ O', i * o * i⁻¹ ∈ O'

variable {k : Stage12.Kind} {S : Subgroup G} {s : G} {I O O' : Subgroup G}

omit [Finite G] in
theorem odd_card_barOf {A : Subgroup G} (hAC : A ≤ Cen z) (hA : Odd (Nat.card ↥A)) :
    Odd (Nat.card ↥(barOf z A)) := by
  have h1 := Subgroup.card_map_dvd (A.subgroupOf (Cen z)) (toBar z)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv] at h1
  exact Odd.of_dvd_nat hA h1

theorem DiagAt.comm_diag (hA : DiagAt z k S s I O O') {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hP : Stage1Pair G z S q L₁ L₂)
    (hsw : Swaps z s L₁ L₂) (hsC : s ∈ Cen z) {x : G} (hxC : x ∈ Cen z)
    (hxI : ∀ i ∈ I, ⁅x, i⁆ ∈ O') :
    ∀ a ∈ L₁, toBar z ⟨x, hxC⟩ * (a * (toBar z ⟨s, hsC⟩ * a * (toBar z ⟨s, hsC⟩)⁻¹)) =
      (a * (toBar z ⟨s, hsC⟩ * a * (toBar z ⟨s, hsC⟩)⁻¹)) * toBar z ⟨x, hxC⟩ := by
  have h := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.PairShape.of_stage1Pair hP
  obtain ⟨hs₁, hs₂⟩ := swaps_conj hsC hsw
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hA.ctx.central.1, pow_two] at this
  have hss : s * s = 1 := mul_self_eq_one_of_isConj hz2 hA.s_conj
  have hsb2 : toBar z ⟨s, hsC⟩ * toBar z ⟨s, hsC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨s, hsC⟩ : ↥(Cen z)) * ⟨s, hsC⟩ = 1 := Subtype.ext hss
    rw [this, map_one]
  have hΔ := diag_le_barOf hA.ctx.central hA.ctx.sylow hP hA.s_mem hA.s_conj hsw hsC hA.I_C
    hA.I_s hA.I_perf hA.O_C hA.O_odd hA.O_norm hA.cov
  have hΔO : ∀ a ∈ L₁, ∀ o ∈ barOf z O',
      (a * (toBar z ⟨s, hsC⟩ * a * (toBar z ⟨s, hsC⟩)⁻¹)) * o *
        (a * (toBar z ⟨s, hsC⟩ * a * (toBar z ⟨s, hsC⟩)⁻¹))⁻¹ ∈ barOf z O' := by
    intro a ha o ho
    obtain ⟨i, hi, hie⟩ := hΔ a ha
    obtain ⟨o', ho', rfl⟩ := ho
    rw [← hie, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hA.O'_norm i hi o' ho', rfl⟩
  have hxO : ∀ a ∈ L₁,
      ⁅toBar z ⟨x, hxC⟩, a * (toBar z ⟨s, hsC⟩ * a * (toBar z ⟨s, hsC⟩)⁻¹)⁆ ∈ barOf z O' := by
    intro a ha
    obtain ⟨i, hi, hie⟩ := hΔ a ha
    rw [← hie, ← map_commutatorElement]
    exact ⟨_, hxI i hi, rfl⟩
  exact comm_diag_of_odd h hsb2 hs₁ hs₂ (mem_normalizer_sup h _)
    (odd_card_barOf hA.O'_C hA.O'_odd) hΔO hxO

theorem DiagAt.swaps (hA : DiagAt z k S s I O O') :
    ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (x₀ : G) (hsC : s ∈ Cen z),
      Stage1Pair G z S q L₁ L₂ ∧ TwoClassData G z S L₁ L₂ q x₀ ∧ Swaps z s L₁ L₂ ∧
        toBar z ⟨s, hsC⟩ * toBar z ⟨s, hsC⟩ = 1 := by
  obtain ⟨q, L₁, L₂, x₀, hP, hx, crit⟩ := swap_criterion hA.ctx hA.two
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hA.ctx.central.1, pow_two] at this
  have hss : s * s = 1 := mul_self_eq_one_of_isConj hz2 hA.s_conj
  have hsw := crit s hA.s_mem hss hA.s_ne hA.s_conj hA.s_not
  refine ⟨q, L₁, L₂, x₀, hsw.1, hP, hx, hsw, ?_⟩
  rw [← map_mul]
  have : (⟨s, hsw.1⟩ : ↥(Cen z)) * ⟨s, hsw.1⟩ = 1 := Subtype.ext hss
  rw [this, map_one]

theorem DiagAt.eq_bot (hA : DiagAt z k S s I O O') {D : Subgroup G} (hDC : D ≤ Cen z)
    (hDp : ⁅D, D⁆ = D) (hDI : ∀ d ∈ D, ∀ i ∈ I, ⁅d, i⁆ ∈ O') : D = ⊥ := by
  obtain ⟨q, L₁, L₂, x₀, hsC, hP, -, hsw, hsb2⟩ := hA.swaps
  have h := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.PairShape.of_stage1Pair hP
  obtain ⟨hs₁, hs₂⟩ := swaps_conj hsC hsw
  have hDp' := barOf_perfect hDC hDp
  have hDle := h.perfect_le hDp'
  have hcen : ∀ x ∈ barOf z D, L₁ ⊔ L₂ ≤ centralizer ({x} : Set (CentralizerBar z)) := by
    rintro _ ⟨⟨d, hdC⟩, hd, rfl⟩
    have hxK := hDle ⟨⟨d, hdC⟩, hd, rfl⟩
    have hn₁ := sup_le_normalizer_left h.comm hxK
    have hn₂ := sup_le_normalizer_left (fun a ha b hb => (h.comm b hb a ha).symm)
      ((sup_comm L₁ L₂).le hxK)
    have hc := centralizes_of_comm_diag h hsb2 hs₁ hs₂
      (fun a ha => (Subgroup.mem_normalizer_iff.mp hn₁ a).mp ha)
      (fun b hb => (Subgroup.mem_normalizer_iff.mp hn₂ b).mp hb)
      (hA.comm_diag hP hsw hsC hdC fun i hi => hDI d hd i hi)
    exact sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hc.1 a ha).symm)
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hc.2 b hb).symm)
  have hab : ⁅barOf z D, barOf z D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcen x hx (hDle hy))
  have hDbot : barOf z D = ⊥ := hDp'.symm.trans hab
  have hker : D.subgroupOf (Cen z) ≤ pPrimeCore 2 ↥(Cen z) := by
    have h1 : (D.subgroupOf (Cen z)).map (toBar z) = ⊥ := hDbot
    have h2 : (toBar z).ker = pPrimeCore 2 ↥(Cen z) := QuotientGroup.ker_mk' _
    rwa [Subgroup.map_eq_bot_iff, h2] at h1
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hle := CFSG.GH74.GLS.Stage2.Signalizer.L52Two.I1.le_of_perfect_of_le_sup_odd (E := ⊥)
    (perfect_subgroupOf hDC hDp) hodd (hker.trans le_sup_right)
  rw [eq_bot_iff]
  intro d hd
  have h1 := hle (show (⟨d, hDC hd⟩ : ↥(Cen z)) ∈ D.subgroupOf (Cen z) from hd)
  rw [Subgroup.mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

theorem DiagAt.not_conj (hA : DiagAt z k S s I O O') {y : G} (hyC : y ∈ Cen z)
    (hy2 : orderOf y = 2) (hyc : IsConj z y) (hyz : y ≠ z) (hyI : ∀ i ∈ I, ⁅y, i⁆ ∈ O') :
    ¬ IsConj z (y * z) := by
  obtain ⟨q, L₁, L₂, x₀, hsC, hP, hx, hsw, hsb2⟩ := hA.swaps
  have hz := hA.ctx.central
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at this
  have h := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.PairShape.of_stage1Pair hP
  obtain ⟨hs₁, hs₂⟩ := swaps_conj hsC hsw
  have hyΔ := hA.comm_diag hP hsw hsC hyC hyI
  rcases conjugate_dichotomy h (toBar z ⟨y, hyC⟩) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    exfalso
    have hc := centralizes_of_comm_diag h hsb2 hs₁ hs₂ (conj_mem_of_conjugate_eq h1)
      (conj_mem_of_conjugate_eq h2) hyΔ
    have hle : L₁ ⊔ L₂ ≤ centralizer ({toBar z ⟨y, hyC⟩} : Set (CentralizerBar z)) :=
      sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hc.1 a ha).symm)
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hc.2 b hb).symm)
    have hmem : toBar z ⟨y, hyC⟩ ∈ generalizedFitting (CentralizerBar z) := by
      refine CFSG.centralizer_generalizedFitting_le (CentralizerBar z) ?_
      rw [h.fitting, Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
    rw [hP.fitting] at hmem
    exact not_mem_LC_of_isConj hz hx hyy hyz hyc
      (mem_LC_of_toBar_mem z hyC ⟨1, by simpa using hy2⟩ hmem)
  ·
    obtain ⟨d, hdC, hdS⟩ := exists_conj_mem_of_sylow hA.ctx.sylow hyC hyy
    have hsw' := swaps_conj_of_mem h ⟨hyC, h1, h2⟩ hdC
    have hc' : IsConj z (d * y * d⁻¹) := hyc.trans (isConj_iff.mpr ⟨d, rfl⟩)
    obtain ⟨hxc, -⟩ := hx.swap_conseq _ hdS hc' hsw'
    intro hzy
    have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
    have e : d * y * d⁻¹ * z = d * (y * z) * d⁻¹ := by
      calc d * y * d⁻¹ * z = d * y * d⁻¹ * (z * d) * d⁻¹ := by group
        _ = d * y * d⁻¹ * (d * z) * d⁻¹ := by rw [hdz]
        _ = d * (y * z) * d⁻¹ := by group
    rw [e] at hxc
    have hxc' : IsConj x₀ (y * z) := hxc.trans (isConj_iff.mpr ⟨d⁻¹, by group⟩)
    exact hx.x_nonCentral
      (P27.Psp4Stage1.isCentralInvolution_of_isConj hz (hzy.trans hxc'.symm))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD
