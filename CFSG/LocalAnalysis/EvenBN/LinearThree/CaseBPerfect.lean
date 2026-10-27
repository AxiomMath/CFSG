module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBSylow
public import CFSG.ClassicalInvolution.GenericLocal.SL2Automorphisms

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open
open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.LieType.Chevalley (SL2 uSL vSL)
open scoped commutatorElement

theorem eq_bot_of_commutator_eq_of_isSolvable {G : Type*} [Group G] {B : Subgroup G}
    (hB : ⁅B, B⁆ = B) [Group.IsSolvable B] : B = ⊥ := by
  have htop : commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries B n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := B)
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

theorem commutatorElement_eq_mul_squares {G : Type*} [Group G] (a b : G) :
    ⁅a, b⁆ = (a * b) * (a * b) * ((b⁻¹ * a⁻¹ * b) * (b⁻¹ * a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
  rw [commutatorElement_def]; group

theorem le_normalizer_of_forall_mul_self {G : Type*} [Group G] {X H : Subgroup G}
    (hX : ⁅X, X⁆ = X) (hsq : ∀ g ∈ X, g * g ∈ normalizer (H : Set G)) :
    X ≤ normalizer (H : Set G) := by
  rw [← hX, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_eq_mul_squares]
  have hb' : b⁻¹ * a⁻¹ * b ∈ X := mul_mem (mul_mem (inv_mem hb) (inv_mem ha)) hb
  exact mul_mem (mul_mem (hsq _ (mul_mem ha hb)) (hsq _ hb')) (hsq _ (inv_mem hb))

namespace CaseBNotation

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}
  {K : Type} [Field K] [Finite K] [CharP K 2] {w : WData d Vi q} {D : LeviData A Vi K}

theorem mem_normalizer_of_map_conj_eq {H' : Type*} [Group H'] {H : Subgroup H'} {g : H'}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set H') := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simpa [MulAut.conj_apply] using hyx
    rwa [← this]

theorem le_normalizer_Pbar_Qbar (N : CaseBNotation w D) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) {X : Subgroup w.Nbar} (hX : ⁅X, X⁆ = X) :
    X ≤ normalizer (N.Pbar : Set w.Nbar) ∧ X ≤ normalizer (N.Qbar : Set w.Nbar) :=
  ⟨le_normalizer_of_forall_mul_self hX fun g _ =>
      mem_normalizer_of_map_conj_eq (N.map_conj_mul_self_Pbar hf hKc g).1,
    le_normalizer_of_forall_mul_self hX fun g _ =>
      mem_normalizer_of_map_conj_eq (N.map_conj_mul_self_Pbar hf hKc g).2⟩

omit [Finite G] [CharP K 2] in
theorem exists_conj_eq_Pbar (N : CaseBNotation w D) (hK4 : 4 ≤ Nat.card K)
    {X : Subgroup w.Nbar} (hX : ⁅X, X⁆ = X) (hXN : X ≤ normalizer (N.Pbar : Set w.Nbar))
    {x : w.Nbar} (hx : x ∈ X) : ∃ p ∈ N.Pbar, ∀ a ∈ N.Pbar, x * a * x⁻¹ = p * a * p⁻¹ := by
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.2 hX
  let e : N.Pbar ≃* SL2 K := (MonoidHom.ofInjective N.σ_injective).symm
  let ψ : X →* MulAut N.Pbar := (normalizerMonoidHom N.Pbar).comp (inclusion hXN)
  obtain ⟨p, hp⟩ := CFSG.ClassicalInvolution.perfect_action_inner_of_equiv_sl2 hK4 e ψ ⟨x, hx⟩
  refine ⟨p, p.2, fun a ha => ?_⟩
  have h := congrArg (fun φ : MulAut N.Pbar => ((φ ⟨a, ha⟩ : N.Pbar) : w.Nbar)) hp
  exact h

omit [Finite G] [CharP K 2] in
theorem exists_conj_eq_Qbar (N : CaseBNotation w D) (hK4 : 4 ≤ Nat.card K)
    {X : Subgroup w.Nbar} (hX : ⁅X, X⁆ = X) (hXN : X ≤ normalizer (N.Qbar : Set w.Nbar))
    {x : w.Nbar} (hx : x ∈ X) : ∃ p ∈ N.Qbar, ∀ a ∈ N.Qbar, x * a * x⁻¹ = p * a * p⁻¹ := by
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.2 hX
  let e : N.Qbar ≃* SL2 K :=
    (MulEquiv.subgroupMap (MulAut.conj w.tbar) N.Pbar).symm.trans
      (MonoidHom.ofInjective N.σ_injective).symm
  let ψ : X →* MulAut N.Qbar := (normalizerMonoidHom N.Qbar).comp (inclusion hXN)
  obtain ⟨p, hp⟩ := CFSG.ClassicalInvolution.perfect_action_inner_of_equiv_sl2 hK4 e ψ ⟨x, hx⟩
  refine ⟨p, p.2, fun a ha => ?_⟩
  have h := congrArg (fun φ : MulAut N.Qbar => ((φ ⟨a, ha⟩ : N.Qbar) : w.Nbar)) hp
  exact h

omit [Finite G] [Finite K] [CharP K 2] in
theorem mem_oddCore_of_centralizes (hB : w.CaseB D.lev.range) {y : w.Nbar}
    (hy : ∀ e ∈ w.Ebar D.lev.range, y * e = e * y) : y ∈ standardComponentOddCore w.Nbar := by
  obtain ⟨-, -, -, -, hC, -, -⟩ := hB.layer
  have hmap : (w.Ebar D.lev.range).map w.projTil =
      normalClosure ((w.Ltil D.lev.range : Subgroup w.Ntil) : Set w.Ntil) := by
    rw [Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), ← Subgroup.coe_map]
  have hyC : w.projTil y ∈ centralizer
      (normalClosure ((w.Ltil D.lev.range : Subgroup w.Ntil) : Set w.Ntil) : Set w.Ntil) := by
    rw [mem_centralizer_iff, ← hmap]
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, ← map_mul, hy e he]
  rw [hC, mem_bot] at hyC
  exact (QuotientGroup.eq_one_iff _).1 hyC

theorem perfect_le_Ebar (N : CaseBNotation w D) (hB : w.CaseB D.lev.range) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) {X : Subgroup w.Nbar} (hX : ⁅X, X⁆ = X) :
    X ≤ w.Ebar D.lev.range := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK3 : 3 ≤ Nat.card K := by omega
  obtain ⟨hXP, hXQ⟩ := N.le_normalizer_Pbar_Qbar hf hKc hX
  set E := w.Ebar D.lev.range with hE
  set O := standardComponentOddCore w.Nbar with hO
  have hEn : E.Normal := normalClosure_normal
  have hXEO : X ≤ E ⊔ O := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := N.exists_conj_eq_Pbar hK4 hX hXP hx
    obtain ⟨p', hp', hpx'⟩ := N.exists_conj_eq_Qbar hK4 hX hXQ hx
    have hpQ : ∀ a ∈ N.Qbar, p * a = a * p := fun a ha => N.Pbar_Qbar_comm p hp a ha
    have hpP : ∀ a ∈ N.Pbar, p' * a = a * p' := fun a ha => (N.Pbar_Qbar_comm a ha p' hp').symm
    set c := p * p' with hc
    set y := c⁻¹ * x with hy
    have key : ∀ a, x * a * x⁻¹ = c * a * c⁻¹ → y * a = a * y := by
      intro a h
      calc y * a = c⁻¹ * (x * a * x⁻¹) * x := by rw [hy]; group
        _ = c⁻¹ * (c * a * c⁻¹) * x := by rw [h]
        _ = a * y := by rw [hy]; group
    have hyP : ∀ a ∈ N.Pbar, y * a = a * y := by
      intro a ha
      refine key a ?_
      have h2 : p' * a * p'⁻¹ = a := by rw [hpP a ha, mul_inv_cancel_right]
      rw [hpx a ha, hc, show p * p' * a * (p * p')⁻¹ = p * (p' * a * p'⁻¹) * p⁻¹ by group, h2]
    have hyQ : ∀ a ∈ N.Qbar, y * a = a * y := by
      intro a ha
      refine key a ?_
      have hmem : p' * a * p'⁻¹ ∈ N.Qbar := mul_mem (mul_mem hp' ha) (inv_mem hp')
      have h2 : p * (p' * a * p'⁻¹) * p⁻¹ = p' * a * p'⁻¹ := by
        rw [hpQ _ hmem, mul_inv_cancel_right]
      rw [hpx' a ha, hc, show p * p' * a * (p * p')⁻¹ = p * (p' * a * p'⁻¹) * p⁻¹ by group, h2]
    have hyE : ∀ e ∈ E, y * e = e * y := by
      have hle : E ≤ centralizer ({y} : Set w.Nbar) := by
        rw [hE, N.Ebar_eq hK3]
        refine sup_le (fun a ha => ?_) fun a ha => ?_
        · exact mem_centralizer_singleton_iff.2 (hyP a ha).symm
        · exact mem_centralizer_singleton_iff.2 (hyQ a ha).symm
      exact fun e he => (mem_centralizer_singleton_iff.1 (hle he)).symm
    have hyO : y ∈ O := mem_oddCore_of_centralizes hB hyE
    have hppE : c ∈ E := by
      rw [hE, N.Ebar_eq hK3, hc]
      exact mul_mem (mem_sup_left hp) (mem_sup_right hp')
    rw [show x = c * y by rw [hy]; group]
    exact mul_mem (mem_sup_left hppE) (mem_sup_right hyO)
  set π := QuotientGroup.mk' E with hπ
  have hXπ : X.map π ≤ O.map π := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨e, he, o, ho, rfl⟩ := mem_sup_of_normal_left.1 (hXEO hx)
    refine ⟨o, ho, ?_⟩
    have he1 : π e = 1 := (QuotientGroup.eq_one_iff e).2 he
    rw [map_mul, he1, one_mul]
  have hodd : Odd (Nat.card (X.map π)) := by
    have h1 := Subgroup.card_dvd_of_le hXπ
    have h2 := Subgroup.card_map_dvd O π
    exact Odd.of_dvd_nat (GMSK.odd_card_standardComponentOddCore w.Nbar) (h1.trans h2)
  have : Group.IsSolvable (X.map π) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hperf : ⁅X.map π, X.map π⁆ = X.map π := by rw [← map_commutator, hX]
  have hbot := eq_bot_of_commutator_eq_of_isSolvable hperf
  intro x hx
  have h : π x ∈ X.map π := ⟨x, hx, rfl⟩
  rw [hbot, mem_bot] at h
  exact (QuotientGroup.eq_one_iff x).1 h

theorem perfect_le_M_sup (N : CaseBNotation w D) (hB : w.CaseB D.lev.range) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) {X : Subgroup G} (hXN : X ≤ w.N) (hX : ⁅X, X⁆ = X) :
    X ≤ N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom := by
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set Xb := (X.subgroupOf w.N).map w.projBar with hXb
  have hXs : ⁅X.subgroupOf w.N, X.subgroupOf w.N⁆ = X.subgroupOf w.N := by
    apply Subgroup.map_injective w.N.subtype_injective
    rw [map_commutator, Subgroup.map_subgroupOf_eq_of_le hXN, hX]
  have hXbp : ⁅Xb, Xb⁆ = Xb := by rw [hXb, ← map_commutator, hXs]
  have hle := N.perfect_le_Ebar hB hf hKc hXbp
  rw [N.Ebar_eq hK3] at hle
  rw [N.M_sup]
  intro x hx
  exact (CaseBModule.mem_preim w _).2 ⟨hXN hx, hle ⟨⟨x, hXN hx⟩, hx, rfl⟩⟩

end CaseBNotation

end CFSG.LocalAnalysis.EvenBN.LinearThree
