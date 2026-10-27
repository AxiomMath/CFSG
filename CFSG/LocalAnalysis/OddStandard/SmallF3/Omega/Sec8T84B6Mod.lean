module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B4Norm

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace B89

open Subgroup CFSG.Blueprint

@[expose] def RestrictsTo {G : Type} [Group G] (B E : Subgroup G) (σ : MulAut ↥E)
    (α : MulAut ↥B) : Prop :=
  ∀ (e : ↥E) (he : (e : G) ∈ B), ((σ e : ↥E) : G) = ((α ⟨e, he⟩ : ↥B) : G)

namespace RestrictsTo

variable {G : Type} [Group G] {B E : Subgroup G} {σ τ : MulAut ↥E} {α β : MulAut ↥B}

theorem mem (h : RestrictsTo B E σ α) {e : ↥E} (he : (e : G) ∈ B) : ((σ e : ↥E) : G) ∈ B := by
  rw [h e he]
  exact (α ⟨e, he⟩).2

theorem mul (h : RestrictsTo B E σ α) (h' : RestrictsTo B E τ β) :
    RestrictsTo B E (σ * τ) (α * β) := by
  intro e he
  have h1 : ((τ e : ↥E) : G) ∈ B := h'.mem he
  have h2 : (⟨((τ e : ↥E) : G), h1⟩ : ↥B) = β ⟨e, he⟩ := Subtype.ext (h' e he)
  rw [MulAut.mul_apply, h (τ e) h1, MulAut.mul_apply, h2]

theorem fix_iff (h : RestrictsTo B E σ α) {e : ↥E} (he : (e : G) ∈ B) :
    σ e = e ↔ α ⟨e, he⟩ = ⟨e, he⟩ := by
  constructor
  · intro hσ
    apply Subtype.ext
    rw [← h e he, hσ]
  · intro hα
    apply Subtype.ext
    rw [h e he, hα]

theorem apply_eq_of_eq_one (h : RestrictsTo B E σ α) (hα : α = 1) {e : ↥E} (he : (e : G) ∈ B) :
    σ e = e :=
  Subtype.ext (by rw [h e he, hα, MulAut.one_apply])

theorem comm_apply (h : RestrictsTo B E σ α) (h' : RestrictsTo B E τ β) (hc : α * β = β * α)
    {e : ↥E} (he : (e : G) ∈ B) : σ (τ e) = τ (σ e) := by
  have h1 := (h.mul h') e he
  have h2 := (h'.mul h) e he
  rw [hc] at h1
  exact Subtype.ext (h1.trans h2.symm)

theorem card_fix (h : RestrictsTo B E σ α) (hBE : B ≤ E) :
    Nat.card {e : ↥E // (e : G) ∈ B ∧ σ e = e} = Nat.card {b : ↥B // α b = b} :=
  Nat.card_congr
    { toFun := fun e => ⟨⟨e.1, e.2.1⟩, (h.fix_iff e.2.1).mp e.2.2⟩
      invFun := fun b => ⟨⟨b.1.1, hBE b.1.2⟩, b.1.2, (h.fix_iff b.1.2).mpr b.2⟩
      left_inv := fun e => rfl
      right_inv := fun b => rfl }

end RestrictsTo

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem RestrictsTo.of_induces (hE : Sec8E G t L S z g B E) {n : G}
    (hn : n ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G)) {α : MulAut ↥B}
    (h : Induces B n α) : RestrictsTo B E (rhoG hE n) α := by
  intro e he
  rw [rhoG_apply_X hE (XCt_le_N hE hn) (Subgroup.mem_inf.mp hn).1 e]
  exact (h ⟨e, he⟩).symm

theorem induces_t (hE : Sec8E G t L S z g B E) : Induces B t 1 := by
  intro b
  have h1 : t * (b : G) = (b : G) * t := sec8t84a1_t_comm hE.ctx b.2
  rw [MulAut.one_apply]
  calc (b : G) = ((b : G) * t) * t⁻¹ := by group
    _ = (t * (b : G)) * t⁻¹ := by rw [h1]

theorem exists_y (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) (hMod : Sec8T84FactModB)
    (hnorm : ∀ h ∈ autIn (centralizer ({t} : Set G)) B, ∀ a ∈ autIn L B,
      h * a * h⁻¹ ∈ autIn L B)
    {x0 : MulAut ↥B} (hx0sq : x0 * x0 = 1) (hx0card : Nat.card {b : ↥B // x0 b = b} = 8)
    {x : G} (hx : x ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G))
    (hxB : Induces B x x0) :
    ∃ y ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G), Induces B y x0 ∧
      rhoG hE y * rhoG hE y = 1 ∧ Nat.card {e : ↥E // rhoG hE y e = e} = 64 ∧
      ∀ {w0 : MulAut ↥B}, x0 * w0 = w0 * x0 →
        ∀ w ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G), Induces B w w0 →
          rhoG hE w * rhoG hE y = rhoG hE y * rhoG hE w := by
  have hxN : x ∈ Nsub8 t B := XCt_le_N hE hx
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have htmem : t ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G) :=
    Subgroup.mem_inf.mpr ⟨t_mem_X hE, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hRx := RestrictsTo.of_induces hE hx hxB
  have hxu : rhoG hE x * rhoG hE t = rhoG hE t * rhoG hE x := by
    rw [← rhoG_mul hE hxN t_mem_N, ← rhoG_mul hE t_mem_N hxN, hxt]
  obtain ⟨h', hcase, hsq, hcard, hcomm⟩ := hMod G E B hE.elem hE.ctx.B_e16 (B_le_E hE)
    (rhoG hE t) (Abar hE) (rhoG hE x) (rhoG_t_mul_self hE) (rhoG_t_fix_iff hE)
    (rhoG_t_onto hE) (Abar_equiv_A6 F hE) (fun a ha => Abar_comm_u hE ha)
    (fun a ha h => Abar_faithful F hE ha h) hxu
    (fun a ha => rhoG_conj_mem_Abar F hE hnorm hx ha)
    (fun e he => (hRx.mul hRx).apply_eq_of_eq_one hx0sq he)
    (by rw [hRx.card_fix (B_le_E hE)]; exact hx0card)
  obtain ⟨y, hy, hyB, hyρ⟩ : ∃ y ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G),
      Induces B y x0 ∧ rhoG hE y = h' := by
    rcases hcase with hh | hh
    · exact ⟨x, hx, hxB, hh.symm⟩
    · refine ⟨x * t, mul_mem hx htmem, ?_, ?_⟩
      · have h1 := hxB.mul (induces_t hE)
        rwa [mul_one] at h1
      · rw [rhoG_mul hE hxN t_mem_N, hh]
  refine ⟨y, hy, hyB, by rw [hyρ]; exact hsq, by rw [hyρ]; exact hcard, ?_⟩
  intro w0 hxw w hw hwB
  have hwN : w ∈ Nsub8 t B := XCt_le_N hE hw
  have hwt : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
  have hRw := RestrictsTo.of_induces hE hw hwB
  rw [hyρ]
  refine hcomm (rhoG hE w) ?_ (fun a ha => rhoG_conj_mem_Abar F hE hnorm hw ha) ?_
  · rw [← rhoG_mul hE hwN t_mem_N, ← rhoG_mul hE t_mem_N hwN, hwt]
  · intro e he
    exact RestrictsTo.comm_apply hRw hRx hxw.symm he

end B89

end CFSG.OddStandard.SmallF3.Omega
