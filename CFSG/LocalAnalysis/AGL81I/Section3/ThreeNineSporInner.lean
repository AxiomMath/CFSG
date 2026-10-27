module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltInner
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Sporadic.Schreier.TitsAutD
import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicTable
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)

private theorem exists_conjMulAut_pow {L : Type} [Group L] {Y J : Subgroup L} (hJY : J ≤ Y)
    (hJn : (J.subgroupOf Y).Normal) {x : L} (hxY : x ∈ Y) {p : ℕ} (hxp : x ^ p = 1) :
    ∃ α : MulAut ↥J, α ^ p = 1 ∧ ∀ j : ↥J, (α j : L) = x * (j : L) * x⁻¹ := by
  have hmem : ∀ (y : L), y ∈ Y → ∀ j : ↥J, y * (j : L) * y⁻¹ ∈ J := by
    intro y hy j
    have hj : (⟨(j : L), hJY j.2⟩ : Y) ∈ J.subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      exact j.2
    have h := hJn.conj_mem (⟨(j : L), hJY j.2⟩ : Y) hj (⟨y, hy⟩ : Y)
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  let α : MulAut ↥J :=
    { toFun := fun j => ⟨x * (j : L) * x⁻¹, hmem x hxY j⟩
      invFun := fun j => ⟨x⁻¹ * (j : L) * x, by simpa using hmem x⁻¹ (Y.inv_mem hxY) j⟩
      left_inv := by intro j; ext; group
      right_inv := by intro j; ext; group
      map_mul' := by intro j k; ext; simp [mul_assoc] }
  have happly : ∀ j : ↥J, (α j : L) = x * (j : L) * x⁻¹ := fun j => rfl
  have hpow : ∀ n : ℕ, ∀ j : ↥J,
      ((α ^ n) j : L) = x ^ n * (j : L) * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro j; simp
    | succ n ih =>
        intro j
        rw [pow_succ, MulAut.mul_apply, ih (α j), happly j, pow_succ]
        group
  refine ⟨α, ?_, happly⟩
  ext j
  rw [hpow p j, hxp]
  simp

private theorem eq_of_conj_eq_conj {L : Type} [Group L] {Y J : Subgroup L} (hJY : J ≤ Y)
    (hC : Subgroup.centralizer (J : Set L) ⊓ Y = ⊥) {x : L} (hxY : x ∈ Y) {j₀ : ↥J}
    (h : ∀ j : ↥J, x * (j : L) * x⁻¹ = (j₀ : L) * (j : L) * (j₀ : L)⁻¹) :
    x = (j₀ : L) := by
  have hyY : (j₀ : L)⁻¹ * x ∈ Y := Y.mul_mem (Y.inv_mem (hJY j₀.2)) hxY
  have hconj : ∀ j : ↥J,
      ((j₀ : L)⁻¹ * x) * (j : L) * ((j₀ : L)⁻¹ * x)⁻¹ = (j : L) := by
    intro j
    calc (j₀ : L)⁻¹ * x * (j : L) * ((j₀ : L)⁻¹ * x)⁻¹
        = (j₀ : L)⁻¹ * (x * (j : L) * x⁻¹) * (j₀ : L) := by group
      _ = (j₀ : L)⁻¹ * ((j₀ : L) * (j : L) * (j₀ : L)⁻¹) * (j₀ : L) := by rw [h j]
      _ = (j : L) := by group
  have hcent : ((j₀ : L)⁻¹ * x) ∈ Subgroup.centralizer (J : Set L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    calc (j : L) * ((j₀ : L)⁻¹ * x)
        = (((j₀ : L)⁻¹ * x) * (j : L) * ((j₀ : L)⁻¹ * x)⁻¹) * ((j₀ : L)⁻¹ * x) := by
          rw [hconj ⟨j, hj⟩]
      _ = ((j₀ : L)⁻¹ * x) * (j : L) := by group
  have hbot : ((j₀ : L)⁻¹ * x) ∈ (⊥ : Subgroup L) := by
    have hy : ((j₀ : L)⁻¹ * x) ∈ Subgroup.centralizer (J : Set L) ⊓ Y := ⟨hcent, hyY⟩
    rwa [hC] at hy
  have hone : (j₀ : L)⁻¹ * x = 1 := Subgroup.mem_bot.mp hbot
  exact ((inv_mul_eq_one (a := (j₀ : L)) (b := x)).mp hone).symm

theorem closure_le_of_pow_eq_one {L : Type} [Group L] [Finite L] {p : ℕ} {Y J : Subgroup L}
    (hJY : J ≤ Y) (hJn : (J.subgroupOf Y).Normal)
    (hC : Subgroup.centralizer (J : Set L) ⊓ Y = ⊥)
    (hinn : ∀ α : MulAut ↥J, α ^ p = 1 → α ∈ inner ↥J) {S : Set L} (hSY : S ⊆ Y)
    (hS : ∀ x ∈ S, x ^ p = 1) : Subgroup.closure S ≤ J := by
  rw [Subgroup.closure_le]
  intro x hxS
  obtain ⟨α, hαp, hαapply⟩ := exists_conjMulAut_pow hJY hJn (hSY hxS) (hS x hxS)
  obtain ⟨j₀, hj₀⟩ := hinn α hαp
  have hconj : ∀ j : ↥J, x * (j : L) * x⁻¹ = (j₀ : L) * (j : L) * (j₀ : L)⁻¹ := by
    intro j
    have h := congrArg (fun f : MulAut ↥J => (f j : L)) hj₀
    rw [MulAut.conj_apply] at h
    rw [← hαapply j]
    simpa using h.symm
  have hx : x = (j₀ : L) := eq_of_conj_eq_conj hJY hC (hSY hxS) hconj
  rw [hx]
  exact j₀.2

theorem mem_inner_of_card_outer_le_two {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hT : Nat.card (Outer T) ≤ 2) {α : MulAut T} (hα : α ^ p = 1) :
    α ∈ inner T := by
  haveI : Nonempty (Outer T) := ⟨1⟩
  haveI : Finite (Outer T) := inferInstance
  let β : Outer T := QuotientGroup.mk' (inner T) α
  have hβp : β ^ p = 1 := by
    change (QuotientGroup.mk' (inner T) α) ^ p = 1
    rw [← map_pow, hα, map_one]
  have hpdvd : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one hβp
  have hcdvd : orderOf β ∣ Nat.card (Outer T) := orderOf_dvd_natCard β
  have hle : orderOf β ≤ 2 := (Nat.le_of_dvd Nat.card_pos hcdvd).trans hT
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hd : orderOf β = 1 := by
    rcases (Nat.dvd_prime hp).mp hpdvd with h | h
    · exact h
    · omega
  exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp hd)

theorem mem_inner_of_mulEquiv_alternating {T : Type} [Group T] {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 5 ≤ n) (e : T ≃* alternatingGroup (Fin n)) {α : MulAut T}
    (hα : α ^ p = 1) : α ∈ inner T := by
  have hα' : (MulAut.congr e α) ^ p = 1 := by rw [← map_pow, hα, map_one]
  obtain ⟨x, hx⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Inner.exists_unique_inner (n := n) hp hp2 hn hα'
  refine (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp ?_
  rw [hx]
  exact ⟨x, rfl⟩

section LieInner


theorem mem_inner_of_lieModel {T : Type} [Group T] [Finite T] {t : StatedLieTag}
    {n ℓ f p : ℕ} (h : CFSG.Blueprint.LieModel T t n ℓ f) (ht : t ≠ .Tits) (hp : p.Prime)
    (hp2 : p ≠ 2) (h4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3)) (h3 : ¬ (t = .trialityD4 ∧ p = 3))
    (hf : ¬ p ∣ f) (hdv : ¬ p ∣ lieOrderDivisor t n (ℓ ^ f)) {α : MulAut T} (hα : α ^ p = 1) :
    α ∈ inner T := by
  by_contra hαin
  obtain ⟨f₀, hf₀, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds T t n ℓ f
      h.admissible h ht p hp hp2 hdv h4 h3 α hα hαin
  exact hf ⟨f₀, hf₀⟩

end LieInner

section TitsInner


theorem mem_inner_of_reeTitsModel_Tits {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (h : CFSG.Blueprint.ReeTitsModel T .Tits ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut T} (hα : α ^ p = 1) : α ∈ inner T := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv T ℓ f h
  have hα' : (MulAut.congr e α) ^ p = 1 := by rw [← map_pow, hα, map_one]
  have hout : Nat.card (Outer CFSG.Sporadic.Schreier.Tits.titsD) ≤ 2 :=
    CFSG.Sporadic.Schreier.Tits.card_outer_titsD.le
  have hmem : MulAut.congr e α ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        CFSG.Sporadic.Schreier.Tits.titsD :=
    mem_inner_of_card_outer_le_two hp hp2 hout hα'
  exact (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp hmem

end TitsInner

section CarrierInner


theorem mem_inner_of_mulEquiv_carrier {T : Type} [Group T] [Finite T]
    {s : TauCeti.SporadicName} (e : T ≃* Carrier s) (hs : s ≠ .M) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {α : MulAut T} (hα : α ^ p = 1) : α ∈ inner T := by
  haveI : Finite (Carrier s) := Finite.of_equiv T e.toEquiv
  have hα' : (MulAut.congr e α) ^ p = 1 := by rw [← map_pow, hα, map_one]
  have hmem := mem_inner_of_card_outer_le_two hp hp2
    (CFSG.AGLEmbeddingD2.card_outer_carrier_le_two_of_ne_M s hs) hα'
  exact (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp hmem

end CarrierInner

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
