module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2Three
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs11

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Gen

variable {Y : Type} [Group Y]

@[expose] def KANoP (α : MulAut Y) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ N : Subgroup Y, N ≤ fixSub α →
    (∀ c ∈ fixSub α, ∀ n ∈ N, c * n * c⁻¹ ∈ N) → IsPGroup p ↥N → N = ⊥

@[expose] def kaOddHull (α : MulAut Y) : Subgroup Y :=
  Subgroup.closure {x : Y | x ∈ fixSub α ∧ Odd (orderOf x)}

theorem kaOddHull_le (α : MulAut Y) : kaOddHull α ≤ fixSub α :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem mem_kaOddHull_of_odd {α : MulAut Y} {c : Y} (hc : c ∈ fixSub α) (hodd : Odd (orderOf c)) :
    c ∈ kaOddHull α :=
  Subgroup.subset_closure ⟨hc, hodd⟩

theorem kaOddHull_gen (α : MulAut Y) :
    Subgroup.closure {x : Y | x ∈ kaOddHull α ∧ Odd (orderOf x)} = kaOddHull α := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun _ hx => hx.1) ?_
  exact Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩

theorem kaOddHull_normalized {α : MulAut Y} {c : Y} (hc : c ∈ fixSub α) :
    ∀ y ∈ kaOddHull α, c * y * c⁻¹ ∈ kaOddHull α := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · exact (fixSub α).mul_mem ((fixSub α).mul_mem hc hx.1) ((fixSub α).inv_mem hc)
    · have h1 := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      have h2 : orderOf (c * x * c⁻¹) = orderOf x := by simpa [MulAut.conj_apply] using h1
      rw [h2]
      exact hx.2
  | one => simp
  | mul x y _ _ hx hy =>
    have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem ka_hRp_of_noP [Finite Y] {α : MulAut Y} (hNoP : KANoP α) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup Y, IsPGroup p ↥X → X ≤ kaOddHull α →
      (∀ r ∈ kaOddHull α, r ∈ normalizer (X : Set Y)) → X = ⊥ := by
  intro p hp hp2 X hX hXR hXN
  have hOpN : ∀ c ∈ fixSub α, c ∈ normalizer ((Op p (kaOddHull α) : Subgroup Y) : Set Y) := by
    intro c hc
    have hRN : c ∈ normalizer ((kaOddHull α : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨kaOddHull_normalized hc y, fun hy => ?_⟩
      have := kaOddHull_normalized ((fixSub α).inv_mem hc) _ hy
      simpa [mul_assoc] using this
    have h1 : (kaOddHull α).map (MulAut.conj c).toMonoidHom = kaOddHull α :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hRN
    have h2 := Op_map p (MulAut.conj c) (kaOddHull α)
    rw [h1] at h2
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2.symm
  have hXOp : X ≤ Op p (kaOddHull α) := le_Op_of_normal hXR (fun r hr => hXN r hr) hX
  have hbot : Op p (kaOddHull α) = ⊥ :=
    hNoP p hp hp2 _ ((Op_le p _).trans (kaOddHull_le α))
      (fun c hc n hn => (Subgroup.mem_normalizer_iff.1 (hOpN c hc) n).1 hn)
      (isPGroup_Op p hp _)
  exact eq_bot_iff.2 (hXOp.trans hbot.le)

theorem ka_all_of_noP [Finite Y] (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (hNoP : KANoP α) (hOutCyc : KAOutCyc Y)
    (hOut : ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) : KAAll α :=
  ka_all_of_oddcore hinj (kaOddHull α) (kaOddHull_le α) (kaOddHull_gen α)
    (fun _ hc hodd => mem_kaOddHull_of_odd hc hodd)
    (fun p hp hp2 X hX hXR hXN => ka_hRp_of_noP hNoP p hp hp2 X hX hXR hXN) hOutCyc hOut

end Gen

section Out

variable {Y E : Type} [Group Y] [Group E]

theorem ka_hOut_of_hom [IsCyclic E] (Θ : MulAut Y →* E)
    (hker : Θ.ker = innSub Y) (α : MulAut Y) : ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y := by
  intro x
  rw [← hker, MonoidHom.mem_ker, commutatorElement_def]
  simp only [map_mul, map_inv]
  have : IsMulCommutative E := IsCyclic.isMulCommutative
  have hc : Θ x * Θ α = Θ α * Θ x := mul_comm' _ _
  calc Θ x * Θ α * (Θ x)⁻¹ * (Θ α)⁻¹ = Θ α * Θ x * (Θ x)⁻¹ * (Θ α)⁻¹ := by rw [hc]
    _ = 1 := by group

theorem kaOutCyc_of_hom [IsCyclic E] (Θ : MulAut Y →* E) (hker : Θ.ker = innSub Y) :
    KAOutCyc Y := by
  intro p _ _ P _ hP
  refine isCyclic_of_injective (Θ.comp P.subtype) ?_
  intro a b hab
  have h1 : Θ ((a : MulAut Y)⁻¹ * (b : MulAut Y)) = 1 := by
    have : Θ (a : MulAut Y) = Θ (b : MulAut Y) := hab
    rw [map_mul, map_inv, this, inv_mul_cancel]
  have h2 : (a : MulAut Y)⁻¹ * (b : MulAut Y) ∈ innSub Y := by
    rw [← hker]
    exact h1
  have h3 : (a : MulAut Y)⁻¹ * (b : MulAut Y) = 1 := hP _ (P.mul_mem (P.inv_mem a.2) b.2) h2
  exact Subtype.ext (inv_mul_eq_one.1 h3)

end Out

section Reduce

variable {Y : Type} [Group Y]

theorem kaNoP_of_fixOddFree [Finite Y] {α : MulAut Y} (h : FixOddFree α) : KANoP α := by
  intro p hp hp2 N hN hNn hNp
  have : Fact p.Prime := ⟨hp⟩
  exact h N hN hNn (odd_card_of_isPGroup_odd_prime hp2 hNp)

theorem kn_fixSub_conj (g : Y) : fixSub (MulAut.conj g) = centralizer ({g} : Set Y) := by
  ext s
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_apply]
  constructor
  · intro h1
    calc s * g = (g * s * g⁻¹) * g := by rw [h1]
      _ = g * s := by group
  · intro h1
    calc g * s * g⁻¹ = (s * g) * g⁻¹ := by rw [← h1]
      _ = s := by group

theorem kaNoP_of_simple [Finite Y] {α : MulAut Y} (hs : IsSimpleGroup ↥(fixSub α))
    (hnab : ∃ a b : ↥(fixSub α), a * b ≠ b * a) : KANoP α := by
  intro p hp hp2 N hN hNn hNp
  have : Fact p.Prime := ⟨hp⟩
  have hnorm : (N.subgroupOf (fixSub α)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hNn g g.2 x hx
  have := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal (N.subgroupOf (fixSub α)) with h | h
  · rw [eq_bot_iff]
    intro n hn
    have hn' : (⟨n, hN hn⟩ : ↥(fixSub α)) ∈ N.subgroupOf (fixSub α) := hn
    rw [h, Subgroup.mem_bot] at hn'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hn')
  · exfalso
    have hpg : IsPGroup p ↥(N.subgroupOf (fixSub α)) :=
      hNp.of_injective (Subgroup.subgroupOfEquivOfLe hN).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hN).injective
    rw [h] at hpg
    have hpC : IsPGroup p ↥(fixSub α) := hpg.of_equiv Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnab
    have : Nontrivial ↥(fixSub α) := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have := hpC.center_nontrivial
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(fixSub α)) with hc | hc
    · obtain ⟨x, hx⟩ := exists_ne (1 : ↥(Subgroup.center ↥(fixSub α)))
      apply hx
      have h1 : (x : ↥(fixSub α)) ∈ (⊥ : Subgroup ↥(fixSub α)) := hc ▸ x.2
      exact Subtype.ext (Subgroup.mem_bot.1 h1)
    · have ha : a ∈ Subgroup.center ↥(fixSub α) := by
        rw [hc]
        exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm

end Reduce

section Transport

variable {Y Γ E : Type} [Group Y] [Group Γ] [Group E]

theorem kn_mem_innSub {Y : Type} [Group Y] {x : MulAut Y} :
    x ∈ innSub Y ↔ ∃ y : Y, MulAut.conj y = x :=
  MonoidHom.mem_range

theorem kn_congr_conj (e : Y ≃* Γ) (y : Y) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  apply MulEquiv.ext
  intro g
  change e (y * e.symm g * y⁻¹) = e y * g * (e y)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem kn_hom_of_mulEquiv (e : Y ≃* Γ) (Θ : MulAut Γ →* E) (hker : Θ.ker = innSub Γ) :
    ∃ Θ' : MulAut Y →* E, Θ'.ker = innSub Y := by
  refine ⟨Θ.comp (MulAut.congr e).toMonoidHom, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
  rw [kn_mem_innSub, kn_mem_innSub]
  constructor
  · rintro ⟨g, hg⟩
    have hg' : MulAut.conj g = MulAut.congr e x := hg
    refine ⟨e.symm g, ?_⟩
    apply (MulAut.congr e).injective
    show MulAut.congr e (MulAut.conj (e.symm g)) = MulAut.congr e x
    rw [kn_congr_conj, e.apply_symm_apply]
    exact hg'
  · rintro ⟨y, rfl⟩
    exact ⟨e y, (kn_congr_conj e y).symm⟩

theorem kn_fixSub_congr (e : Y ≃* Γ) (α : MulAut Y) :
    Nonempty (↥(fixSub α) ≃* ↥(fixSub (MulAut.congr e α))) := by
  have hmap : (fixSub α).map e.toMonoidHom = fixSub (MulAut.congr e α) := by
    ext z
    rw [Subgroup.mem_map, mem_fixSub]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : α y = y := mem_fixSub.1 hy
      change e (α (e.symm (e y))) = e y
      rw [e.symm_apply_apply, hy']
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      rw [mem_fixSub]
      have hz' : e (α (e.symm z)) = z := hz
      apply e.injective
      rw [hz', e.apply_symm_apply]
  exact ⟨(Subgroup.equivMapOfInjective _ _ e.injective).trans (MulEquiv.subgroupCongr hmap)⟩

theorem kn_conj_injective_of_center_bot (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := congrArg (fun φ : MulAut Y => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * g = (g * x * g⁻¹) * g := by rw [h1]
      _ = g * x := by group
  rw [hZ] at hmem
  exact Subgroup.mem_bot.mp hmem

end Transport

theorem kay_of_kaAll {F : (Y : Type) → [Group Y] → Prop}
    (h : ∀ (Y : Type) [Group Y] [Finite Y], F Y → IsSimpleGroup Y → ∀ α : MulAut Y,
      α * α = 1 → α ≠ 1 → KAAll α) : KAY F := by
  intro Y _ _ hF hs α hα2 hα1 p hp hp2 P hPp hP1 hcomm hnorm
  have hc := h Y hF hs α hα2 hα1 p hp hp2 P ⟨hPp, hP1, hcomm, hnorm⟩
  exact ⟨hc.1, Or.inl hc.2⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
