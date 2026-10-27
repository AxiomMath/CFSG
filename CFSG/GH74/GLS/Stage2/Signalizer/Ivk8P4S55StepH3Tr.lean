module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG

@[expose] def Ord3Concl (r : ℕ) (Y : Type) [Group Y] (b : MulAut Y) : Prop :=
  (∃ E : Subgroup Y, E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, b x ∈ E) ∨
    ∃ s : ℕ, HHObsAt 3 s Y b ∧ (s = 2 → NoR 2 Y)

theorem NoR.of_mulEquiv {r : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : NoR r Y') : NoR r Y :=
  fun K _ _ hK ⟨f⟩ => h K hK ⟨f.trans e⟩

theorem Ord3Concl.of_mulEquiv {r : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    {b : MulAut Y} (h : Ord3Concl r Y' (MulAut.congr e b)) : Ord3Concl r Y b := by
  have hb : ∀ x : Y, MulAut.congr e b (e x) = e (b x) := fun x => by
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hcomap : ∀ E' : Subgroup Y', (∀ x ∈ E', MulAut.congr e b x ∈ E') →
      ∀ x ∈ E'.comap e.toMonoidHom, b x ∈ E'.comap e.toMonoidHom := by
    intro E' hE' x hx
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hx ⊢
    rw [← hb]
    exact hE' _ hx
  rcases h with ⟨E', hE'0, hE'p, hE'i⟩ | ⟨s, ⟨hs, hs3, E', hE'p, hab, hE'i, x', hx', hbx'⟩, hN⟩
  · refine Or.inl ⟨E'.comap e.toMonoidHom, ?_, hE'p.comap_of_injective _ e.injective,
      hcomap E' hE'i⟩
    intro hbot
    apply hE'0
    rw [eq_bot_iff]
    intro y hy
    have hy' : e.symm y ∈ E'.comap e.toMonoidHom := by
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hy
    rw [hbot, Subgroup.mem_bot] at hy'
    rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply e y, hy', map_one]
  · refine Or.inr ⟨s, ⟨hs, hs3, E'.comap e.toMonoidHom, hE'p.comap_of_injective _ e.injective,
      fun hs2 x hx y hy => ?_, hcomap E' hE'i, e.symm x', ?_, ?_⟩,
      fun hs2 => NoR.of_mulEquiv e (hN hs2)⟩
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hx hy
      apply e.injective
      rw [map_mul, map_mul]
      exact hab hs2 _ hx _ hy
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hx'
    · intro h
      apply hbx'
      rw [← MulEquiv.apply_symm_apply e x', hb, h]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
