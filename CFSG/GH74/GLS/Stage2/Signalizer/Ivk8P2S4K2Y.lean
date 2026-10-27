module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KACover

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Transport

variable {Y Y' : Type} [Group Y] [Group Y']

theorem congr_conj_mem (e : Y ≃* Y') (y : Y) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := ka_congr_conj e y

theorem congr_congr_symm (e : Y ≃* Y') (α : MulAut Y') :
    MulAut.congr e (MulAut.congr e.symm α) = α := by
  ext y
  simp [MulAut.congr_apply]

theorem kaHyp_of_congr (e : Y ≃* Y') {α : MulAut Y} {p : ℕ} {P' : Subgroup (MulAut Y')}
    (h : KAHyp (MulAut.congr e α) p P') :
    KAHyp α p (P'.comap (MulAut.congr e).toMonoidHom) := by
  let f : MulAut Y →* MulAut Y' := (MulAut.congr e).toMonoidHom
  have hfinj : Function.Injective f := (MulAut.congr e).injective
  have hfsurj : Function.Surjective f := (MulAut.congr e).surjective
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := h
  refine ⟨IsPGroup.comap_of_injective hPp f hfinj, ?_, ?_, ?_⟩
  · intro hbot
    apply hP1
    have := Subgroup.map_comap_eq_self_of_surjective hfsurj P'
    rw [← this]
    change Subgroup.map f (P'.comap f) = ⊥
    rw [hbot, Subgroup.map_bot]
  · intro x hx
    apply hfinj
    have h1 := hcomm (f x) hx
    show (MulAut.congr e) (x * α) = (MulAut.congr e) (α * x)
    rw [map_mul, map_mul]
    exact h1
  · intro c hc hodd
    have h1 : (MulAut.congr e α) (e c) = e (α c) := by simp [MulAut.congr_apply]
    have hc' : e c ∈ fixSub (MulAut.congr e α) := by
      rw [mem_fixSub, h1, (mem_fixSub.1 hc)]
    have h2 : orderOf (e c) = orderOf c := orderOf_injective e.toMonoidHom e.injective c
    have hN := hnorm (e c) hc' (by rw [h2]; exact hodd)
    have hconj : f (MulAut.conj c) = MulAut.conj (e c) := ka_congr_conj e c
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro x
    show f x ∈ P' ↔ f (MulAut.conj c * x * (MulAut.conj c)⁻¹) ∈ P'
    rw [map_mul, map_mul, map_inv, hconj]
    exact hN _

end Transport

section Statement

@[expose] def KATwoY (Y : Type) [Group Y] : Prop :=
  ∀ (α β : MulAut Y), α * α = 1 → α ≠ 1 → β * β = 1 → β ≠ 1 →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ P Q : Subgroup (MulAut Y),
      KAHyp α p P → KAHyp β p Q → α * β ∈ innSub Y

variable {Y Y' : Type} [Group Y] [Group Y']

theorem KATwoY.of_mulEquiv (e : Y ≃* Y') (h : KATwoY Y) : KATwoY Y' := by
  intro α' β' hα2 hα1 hβ2 hβ1 p hp hp2 P' Q' hP' hQ'
  set α : MulAut Y := MulAut.congr e.symm α' with hαdef
  set β : MulAut Y := MulAut.congr e.symm β' with hβdef
  have hαα : MulAut.congr e α = α' := congr_congr_symm e α'
  have hββ : MulAut.congr e β = β' := congr_congr_symm e β'
  have hα2' : α * α = 1 := by rw [hαdef, ← map_mul, hα2, map_one]
  have hβ2' : β * β = 1 := by rw [hβdef, ← map_mul, hβ2, map_one]
  have hα1' : α ≠ 1 := fun h1 => hα1 (by rw [← hαα, h1, map_one])
  have hβ1' : β ≠ 1 := fun h1 => hβ1 (by rw [← hββ, h1, map_one])
  have hP : KAHyp α p (P'.comap (MulAut.congr e).toMonoidHom) :=
    kaHyp_of_congr e (by rw [hαα]; exact hP')
  have hQ : KAHyp β p (Q'.comap (MulAut.congr e).toMonoidHom) :=
    kaHyp_of_congr e (by rw [hββ]; exact hQ')
  obtain ⟨y, hy⟩ := h α β hα2' hα1' hβ2' hβ1' p hp hp2 _ _ hP hQ
  refine ⟨e y, ?_⟩
  rw [← congr_conj_mem, hy, map_mul, hαα, hββ]

end Statement

section Inner

theorem kaInner_ne_bot {Y : Type} [Group Y] {P : Subgroup (MulAut Y)} (hP1 : P ≠ ⊥)
    (hinn : ∀ e ∈ P, e ∈ innSub Y) : kaInner P ≠ ⊥ := by
  intro hbot
  apply hP1
  rw [eq_bot_iff]
  intro e' he'
  obtain ⟨y, hy⟩ := hinn e' he'
  have hyX : y ∈ kaInner P := by rw [mem_kaInner, hy]; exact he'
  rw [hbot, Subgroup.mem_bot] at hyX
  rw [← hy, hyX, map_one]
  exact Subgroup.one_mem _

end Inner

section NoConfig

variable {Y : Type} [Group Y] [Finite Y]

theorem ka_false_of_normal_comm (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (L : Subgroup Y) (hLC : L ≤ fixSub α) (hLperf : ⁅L, L⁆ = L)
    (hLn : ∀ x ∈ fixSub α, x ∈ normalizer (L : Set Y))
    (hLp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup Y, M ≤ L → IsPGroup p ↥M →
      (∀ l ∈ L, l ∈ normalizer (M : Set Y)) → ∀ m ∈ M, ∀ l ∈ L, m * l = l * m)
    (hrig : KARigidComm α L) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), KAHyp α p P → False := by
  intro p hp hp2 P hP
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
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

variable {S : Type} [Group S]

theorem ka_false_of_cover (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (π : S →* Y) (hπ : Function.Surjective π) (hker : ∀ z ∈ π.ker, ∀ g : S, g * z = z * g)
    (θ : S →* S) {α : MulAut Y} (hθα : ∀ g, α (π g) = π (θ g)) (L : Subgroup S)
    (hLθ : L ≤ kaFix θ) (hLperf : ⁅L, L⁆ = L)
    (hLn : ∀ g ∈ normalizer (kaFix θ : Set S), g ∈ normalizer (L : Set S))
    (hLq : CFSG.IsQuasisimple ↥L) (hrig : KARigidComm α (L.map π)) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), KAHyp α p P → False :=
  ka_false_of_normal_comm hinj (L.map π) (ka_cover_map_le π θ hθα hLθ)
    (ka_cover_map_perfect π hLperf) (ka_cover_normalizer_of π hπ hker θ hθα hLn)
    (ka_cover_central π hLq) hrig

end NoConfig

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2
