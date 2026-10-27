module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Normal

variable {Y : Type} [Group Y] [Finite Y]

theorem ka_all_of_normal_comm (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (L : Subgroup Y) (hLC : L ≤ fixSub α) (hLperf : ⁅L, L⁆ = L)
    (hLn : ∀ x ∈ fixSub α, x ∈ normalizer (L : Set Y))
    (hLp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup Y, M ≤ L → IsPGroup p ↥M →
      (∀ l ∈ L, l ∈ normalizer (M : Set Y)) → ∀ m ∈ M, ∀ l ∈ L, m * l = l * m)
    (hrig : KARigidComm α L) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  exfalso
  have hLN : ∀ l ∈ L, MulAut.conj l ∈ normalizer (P : Set (MulAut Y)) := by
    let H : Subgroup Y := (normalizer (P : Set (MulAut Y))).comap (MulAut.conj : Y →* MulAut Y)
    have hle : L ≤ H := ka_perfect_le_of_odd L hLperf H fun x hx hodd' => hnorm x (hLC hx) hodd'
    exact fun l hl => hle hl
  have hX0p : IsPGroup p ↥(kaInner P) := kaInner_isPGroup hinj hPp
  have hX0C : kaInner P ≤ fixSub α := kaInner_le_fixSub hinj hcomm
  have hX0c : ∀ x ∈ kaInner P, ∀ l ∈ L, x * l = l * x :=
    ka_centralizes_of_perfect L (kaInner P) hLperf (fun l hl => mem_normalizer_kaInner (hLN l hl))
      (fun x hx => hLn x (hX0C hx)) hX0p (hLp p hp hp2)
  have hfix := ka_fix_of_perfect hinj hp hPp L hLperf hLN hX0c
  apply hP1
  rw [eq_bot_iff]
  intro e he
  have h1 : e = 1 :=
    hrig p hp hp2 e (IsPGroup.to_le hPp ((Subgroup.zpowers_le).2 he)) (hcomm e he) (hfix e he)
  rw [h1]
  exact Subgroup.one_mem _

theorem ka_all_of_torus_fix_comm (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (R₀ L : Subgroup Y) (hR₀C : R₀ ≤ fixSub α)
    (hodd : ∀ c ∈ fixSub α, Odd (orderOf c) → c ∈ R₀) (hLR₀ : L ≤ R₀)
    (hLn : ∀ x ∈ R₀, x ∈ normalizer (L : Set Y)) (hLperf : ⁅L, L⁆ = L)
    (hLp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup Y, M ≤ L → IsPGroup p ↥M →
      (∀ l ∈ L, l ∈ normalizer (M : Set Y)) → ∀ m ∈ M, ∀ l ∈ L, m * l = l * m)
    (hfix : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P' : Subgroup (MulAut Y), IsPGroup p ↥P' →
      (∀ e ∈ P', e * α = α * e) → (∀ e ∈ P', ∀ r ∈ L, e r = r) → IsCyclic ↥P')
    (hOut : ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, -, hcomm, hnorm⟩ := hP
  have hLC : L ≤ fixSub α := hLR₀.trans hR₀C
  have hLN : ∀ l ∈ L, MulAut.conj l ∈ normalizer (P : Set (MulAut Y)) := by
    let H : Subgroup Y := (normalizer (P : Set (MulAut Y))).comap (MulAut.conj : Y →* MulAut Y)
    have hle : L ≤ H := ka_perfect_le_of_odd L hLperf H fun x hx hodd' => hnorm x (hLC hx) hodd'
    exact fun l hl => hle hl
  have hX0p : IsPGroup p ↥(kaInner P) := kaInner_isPGroup hinj hPp
  have hX0C : kaInner P ≤ fixSub α := kaInner_le_fixSub hinj hcomm
  have hX0R : kaInner P ≤ R₀ := fun x hx =>
    hodd x (hX0C hx) (ka_odd_of_mem_pGroup hp hp2 hX0p hx)
  have hX0c : ∀ x ∈ kaInner P, ∀ l ∈ L, x * l = l * x :=
    ka_centralizes_of_perfect L (kaInner P) hLperf (fun l hl => mem_normalizer_kaInner (hLN l hl))
      (fun x hx => hLn x (hX0R hx)) hX0p (hLp p hp hp2)
  have hfixL := ka_fix_of_perfect hinj hp hPp L hLperf hLN hX0c
  exact ⟨hOut, hfix p hp hp2 P hPp hcomm hfixL⟩

end Normal

section Odd

variable {Y : Type} [Group Y]

theorem ka_all_of_oddcore_triv (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (R : Subgroup Y) (hRC : R ≤ fixSub α)
    (hRgen : Subgroup.closure {x : Y | x ∈ R ∧ Odd (orderOf x)} = R)
    (hodd : ∀ c ∈ fixSub α, Odd (orderOf c) → c ∈ R)
    (hRp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup Y, IsPGroup p ↥X → X ≤ R →
      (∀ r ∈ R, r ∈ normalizer (X : Set Y)) → X = ⊥)
    (hOutTriv : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), IsPGroup p ↥P →
      (∀ e ∈ P, e ∈ innSub Y → e = 1) → P = ⊥) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  exfalso
  have hbot := ka_kaInner_eq_bot hinj hp hp2 hPp hcomm hnorm R hRC hRgen hodd (hRp p hp hp2)
  apply hP1
  refine hOutTriv p hp hp2 P hPp ?_
  rintro e he ⟨y, rfl⟩
  have hy : y ∈ kaInner P := he
  rw [hbot, Subgroup.mem_bot] at hy
  rw [hy, map_one]

end Odd

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
