module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneInnerBasic

public section

namespace CFSG.SeitzReduction

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def InvolutionCriterion {C : Type*} [Group C] (x : MulAut C) : Prop :=
  ∀ β : MulAut C, β * x = x * β → (∀ c : C, x c = c → Odd (orderOf c) → β c = c) → β ^ 2 = 1

theorem apply_eq_self_of_mem_closure {C : Type*} [Group C] {β : MulAut C} {S : Set C}
    (hS : ∀ c ∈ S, β c = c) {d : C} (hd : d ∈ closure S) : β d = d := by
  induction hd using closure_induction with
  | mem c hc => exact hS c hc
  | one => exact map_one β
  | mul c d _ _ hc hd => rw [map_mul, hc, hd]
  | inv c _ hc => rw [map_inv, hc]

theorem conj_mul_eq_mul_conj_of_apply_eq {C : Type*} [Group C] {x : MulAut C} {c : C}
    (hc : x c = c) : MulAut.conj c * x = x * MulAut.conj c := by
  have h := mul_conj_mul_inv_eq_conj x c
  rw [hc, mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem apply_eq_of_mul_conj_eq {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {β : MulAut C} {c : C}
    (hc : β * MulAut.conj c = MulAut.conj c * β) : β c = c :=
  hinj (by rw [← mul_conj_mul_inv_eq_conj, hc, mul_inv_cancel_right])

theorem InvolutionCriterion.noNormalZ4OrZ2xZ4 {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {x : MulAut C}
    (h : InvolutionCriterion x) {H : Subgroup (MulAut C)} (hH : inner C ≤ H) :
    NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({x} : Set (MulAut C))) := by
  have hmem : ∀ c : C, x c = c →
      MulAut.conj c ∈ H ⊓ centralizer ({x} : Set (MulAut C)) := fun c hc =>
    mem_inf.2 ⟨hH ⟨c, rfl⟩, mem_centralizer_singleton_iff.2 (conj_mul_eq_mul_conj_of_apply_eq hc)⟩
  refine noNormalZ4OrZ2xZ4_of_forall_commute
    (S := {y | ∃ c : C, x c = c ∧ Odd (orderOf c) ∧ (y : MulAut C) = MulAut.conj c}) ?_ ?_
  · rintro y ⟨c, -, hc, hy⟩
    rw [← Subgroup.orderOf_coe, hy]
    exact hc.of_dvd_nat (orderOf_map_dvd _ c)
  · intro β hβ hβ4
    have hβx : (β : MulAut C) * x = x * β := mem_centralizer_singleton_iff.1 (mem_inf.1 β.2).2
    have hfix : ∀ c : C, x c = c → Odd (orderOf c) → (β : MulAut C) c = c := fun c hxc hc =>
      apply_eq_of_mul_conj_eq hinj
        (congrArg Subtype.val (hβ ⟨MulAut.conj c, hmem c hxc⟩ ⟨c, hxc, hc, rfl⟩))
    have hdvd : orderOf (β : MulAut C) ∣ 2 := orderOf_dvd_of_pow_eq_one (h β hβx hfix)
    rw [Subgroup.orderOf_coe, hβ4] at hdvd
    exact absurd hdvd (by norm_num)

theorem InvolutionCriterion.innerCentralizerCriterion {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {t : C}
    (h : InvolutionCriterion (MulAut.conj t)) : InnerCentralizerCriterion t := by
  refine innerCentralizerCriterion_of_fix hinj fun β hβt hβc => h β ?_ fun c hc hco => ?_
  · have h1 := mul_conj_mul_inv_eq_conj β t
    rw [hβt, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · refine hβc c ?_ hco
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hc
    exact hc.symm

theorem InvolutionCriterion.conj {C : Type*} [Group C] {x : MulAut C}
    (h : InvolutionCriterion x) (ψ : MulAut C) : InvolutionCriterion (ψ * x * ψ⁻¹) := by
  intro β hβx hβc
  have h1 : ψ⁻¹ * β * ψ * x = x * (ψ⁻¹ * β * ψ) :=
    calc ψ⁻¹ * β * ψ * x = ψ⁻¹ * (β * (ψ * x * ψ⁻¹)) * ψ := by group
      _ = ψ⁻¹ * ((ψ * x * ψ⁻¹) * β) * ψ := by rw [hβx]
      _ = x * (ψ⁻¹ * β * ψ) := by group
  have h2 : ∀ c : C, x c = c → Odd (orderOf c) → (ψ⁻¹ * β * ψ) c = c := by
    intro c hxc hc
    have hψc : (ψ * x * ψ⁻¹) (ψ c) = ψ c := by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hxc]
    have hβψ := hβc (ψ c) hψc (by rwa [MulEquiv.orderOf_eq])
    rw [MulAut.mul_apply, MulAut.mul_apply, hβψ, MulAut.inv_apply_self]
  calc β ^ 2 = ψ * (ψ⁻¹ * β * ψ) ^ 2 * ψ⁻¹ := by simp only [pow_two]; group
    _ = 1 := by rw [h _ h1 h2, mul_one, mul_inv_cancel]

theorem InvolutionCriterion.congr {C C' : Type*} [Group C] [Group C'] (e : C ≃* C')
    {x : MulAut C} (h : InvolutionCriterion x) : InvolutionCriterion (MulAut.congr e x) := by
  intro β hβx hβc
  have hβ : MulAut.congr e ((MulAut.congr e).symm β) = β := (MulAut.congr e).apply_symm_apply β
  have h1 : (MulAut.congr e).symm β * x = x * (MulAut.congr e).symm β :=
    (MulAut.congr e).injective (by rw [map_mul, map_mul, hβ, hβx])
  have h2 : ∀ c : C, x c = c → Odd (orderOf c) → (MulAut.congr e).symm β c = c := by
    intro c hxc hc
    have hc' : MulAut.congr e x (e c) = e c := by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hxc]
    have hβc' := hβc (e c) hc' (by rwa [MulEquiv.orderOf_eq])
    simp only [MulAut.congr_symm_apply, MulEquiv.trans_apply, hβc', MulEquiv.symm_apply_apply]
  rw [← hβ, ← map_pow, h _ h1 h2, map_one]

theorem involutionCriterion_of_fixes {C : Type*} [Group C] {x : MulAut C} {D : Subgroup C}
    (hD : D ≤ closure {c : C | x c = c ∧ Odd (orderOf c)})
    (h : ∀ β : MulAut C, β * x = x * β → (∀ d ∈ D, β d = d) → β ^ 2 = 1) :
    InvolutionCriterion x := fun β hβx hβc =>
  h β hβx fun _ hd => apply_eq_self_of_mem_closure (fun c hc => hβc c hc.1 hc.2) (hD hd)

theorem involutionCriterion_of_le_zpowers {C : Type*} [Group C] {x : MulAut C} (hx : x ^ 2 = 1)
    {N : Subgroup C} (hN : N ≤ closure {c : C | x c = c ∧ Odd (orderOf c)})
    (h : ∀ β : MulAut C, β * x = x * β → (∀ n ∈ N, β n = n) → β ∈ zpowers x) :
    InvolutionCriterion x :=
  involutionCriterion_of_fixes hN fun β hβx hβN => by
    rcases eq_one_or_eq_of_mem_zpowers hx (h β hβx hβN) with rfl | rfl
    · exact one_pow 2
    · exact hx

theorem le_closure_odd_mem_of_le_commutator {G : Type*} [Group G] [Finite G]
    {F A P : Subgroup G} (hAP : A ≤ P) (hPF : P ≤ F) (hA : A ≤ ⁅A, P⁆) :
    A ≤ closure {c : G | c ∈ F ∧ Odd (orderOf c)} := by
  classical
  set M := closure {c : G | c ∈ F ∧ Odd (orderOf c)} with hM
  have hconj : ∀ g ∈ P, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hg m hm
    induction hm using closure_induction with
    | mem c hc =>
      refine subset_closure ⟨F.mul_mem (F.mul_mem (hPF hg) hc.1) (F.inv_mem (hPF hg)), ?_⟩
      rw [show g * c * g⁻¹ = MulAut.conj g c from rfl, MulEquiv.orderOf_eq]
      exact hc.2
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx
  let N : Subgroup P := M.subgroupOf P
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hconj g g.2 n hn⟩
  have h2 : IsPGroup 2 (P ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H p =>
      obtain ⟨k, m, hm, hpm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos p).ne'
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine subset_closure ⟨?_, ?_⟩
      · rw [Subgroup.coe_pow]
        exact F.pow_mem (hPF p.2) _
      · rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd (by positivity) (Dvd.intro m hpm.symm), hpm,
          Nat.mul_div_cancel_left _ (by positivity)]
        exact hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 h2.isNilpotent
  let π : P →* P ⧸ N := QuotientGroup.mk' N
  let A' : Subgroup (P ⧸ N) := (A.subgroupOf P).map π
  have hA'' : A.subgroupOf P ≤ ⁅A.subgroupOf P, ⊤⁆ := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    have e : ⁅A, P⁆ = Subgroup.map P.subtype ⁅A.subgroupOf P, (⊤ : Subgroup P)⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAP, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have h1 := hA ha
    rw [e] at h1
    obtain ⟨b, hb, hba⟩ := h1
    rwa [show a = b from Subtype.ext hba.symm]
  have hA' : A' ≤ ⁅A', ⊤⁆ :=
    calc A' ≤ Subgroup.map π ⁅A.subgroupOf P, (⊤ : Subgroup P)⁆ := Subgroup.map_mono hA''
      _ = ⁅A', (⊤ : Subgroup P).map π⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅A', ⊤⁆ := Subgroup.commutator_mono le_rfl le_top
  have hlcs : ∀ n, A' ≤ (⊤ : Subgroup (P ⧸ N)).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact hA'.trans (Subgroup.commutator_mono ih le_rfl)
  intro a ha
  have hmem : π ⟨a, hAP ha⟩ ∈ A' :=
    ⟨⟨a, hAP ha⟩, by simpa [Subgroup.mem_subgroupOf] using ha, rfl⟩
  have h1 := hlcs n hmem
  rw [hn, Subgroup.mem_bot] at h1
  have h3 := (QuotientGroup.eq_one_iff _).1 h1
  rwa [Subgroup.mem_subgroupOf] at h3

theorem le_closure_odd_fixed_of_le_commutator {C : Type*} [Group C] [Finite C] {x : MulAut C}
    {A P : Subgroup C} (hAP : A ≤ P) (hP : ∀ p ∈ P, x p = p) (hA : A ≤ ⁅A, P⁆) :
    A ≤ closure {c : C | x c = c ∧ Odd (orderOf c)} :=
  (le_closure_odd_mem_of_le_commutator (F := x.toMonoidHom.eqLocus (MonoidHom.id C)) hAP
    (fun p hp => hP p hp) hA).trans (closure_mono fun _ hc => ⟨hc.1, hc.2⟩)

theorem le_closure_odd_fixed_of_perfect {C : Type*} [Group C] [Finite C] {x : MulAut C}
    {P : Subgroup C} (hP : ∀ p ∈ P, x p = p) (hperf : ⁅P, P⁆ = P) :
    P ≤ closure {c : C | x c = c ∧ Odd (orderOf c)} :=
  le_closure_odd_fixed_of_le_commutator le_rfl hP hperf.ge

theorem hypothesisOne_of_involutionCriterion {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    (hcore : ∀ H : Subgroup (MulAut C), inner C ≤ H → ∀ α ∈ H, orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ centralizer ({α} : Set (MulAut C))) = ⊥)
    (h : ∀ x : MulAut C, orderOf x = 2 → InvolutionCriterion x) : HypothesisOne C :=
  hypothesisOne_of_centralizers fun M hM x hxM hx2 =>
    ⟨hcore M hM x hxM hx2, (h x hx2).noNormalZ4OrZ2xZ4 hinj hM⟩

end CFSG.SeitzReduction
