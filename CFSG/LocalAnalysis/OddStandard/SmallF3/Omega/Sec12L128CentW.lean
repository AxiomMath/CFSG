module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Schur

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec128_isEven_permVec (σ : Equiv.Perm (Fin 5)) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    IsEvenVec (permVec σ v) := by
  unfold IsEvenVec permVec at *
  rw [show (∑ i, (v ∘ ⇑σ.symm) i) = ∑ i, v i from Equiv.sum_comp σ.symm v]
  exact hv

@[expose] def evenSub : Submodule (ZMod 2) (Fin 5 → ZMod 2) where
  carrier := {v | IsEvenVec v}
  add_mem' := by
    intro a b ha hb
    have ha' : IsEvenVec a := ha
    have hb' : IsEvenVec b := hb
    show IsEvenVec (a + b)
    unfold IsEvenVec at *
    simp [Finset.sum_add_distrib, ha', hb']
  zero_mem' := by simp [IsEvenVec]
  smul_mem' := by
    intro c v hv
    have hv' : IsEvenVec v := hv
    show IsEvenVec (c • v)
    unfold IsEvenVec at *
    simp [← Finset.mul_sum, hv']

abbrev EvW : Type := ↥evenSub

@[expose] def permW (σ : Equiv.Perm (Fin 5)) : EvW →+ EvW where
  toFun a := ⟨permVec σ a.1, sec128_isEven_permVec σ a.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem permW_val (σ : Equiv.Perm (Fin 5)) (a : EvW) :
    ((permW σ a : EvW) : Fin 5 → ZMod 2) = permVec σ a := rfl

theorem sec128_schurW (g : EvW →+ EvW)
    (h : ∀ σ ∈ alternatingGroup (Fin 5), ∀ a, g (permW σ a) = permW σ (g a)) :
    g = 0 ∨ g = AddMonoidHom.id EvW := by
  classical
  have hmem : ∀ v, IsEvenVec v → v ∈ evenSub := fun v hv => hv
  have hmem' : ∀ v, v ∈ evenSub → IsEvenVec v := fun v hv => hv
  let δ : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) := fun v =>
    if hv : v ∈ evenSub then ((g ⟨v, hv⟩ : EvW) : Fin 5 → ZMod 2) else 0
  have hδ : ∀ (v) (hv : v ∈ evenSub), δ v = ((g ⟨v, hv⟩ : EvW) : Fin 5 → ZMod 2) :=
    fun v hv => by simp only [δ, dif_pos hv]
  rcases sec122_schur δ
    (fun v hv => by
      rw [hδ v (hmem v hv)]
      exact hmem' _ (g _).2)
    (fun v w hv hw => by
      have hvw : v + w ∈ evenSub := evenSub.add_mem (hmem v hv) (hmem w hw)
      rw [hδ v (hmem v hv), hδ w (hmem w hw), hδ (v + w) hvw]
      have : (⟨v + w, hvw⟩ : EvW) = ⟨v, hmem v hv⟩ + ⟨w, hmem w hw⟩ := rfl
      rw [this, map_add]
      rfl)
    (fun σ hσ v hv => by
      have hpv : permVec σ v ∈ evenSub := sec128_isEven_permVec σ hv
      rw [hδ (permVec σ v) hpv, hδ v (hmem v hv)]
      have : (⟨permVec σ v, hpv⟩ : EvW) = permW σ ⟨v, hmem v hv⟩ := rfl
      rw [this, h σ hσ]
      rfl) with h0 | h1
  · left
    refine AddMonoidHom.ext fun a => Subtype.ext ?_
    have := h0 a.1 (hmem' _ a.2)
    rw [hδ a.1 a.2] at this
    exact this
  · right
    refine AddMonoidHom.ext fun a => Subtype.ext ?_
    have := h1 a.1 (hmem' _ a.2)
    rw [hδ a.1 a.2] at this
    exact this

theorem sec128_orbit_wvec :
    ∀ v : Fin 5 → ZMod 2, IsEvenVec v → v ≠ 0 → ∀ i : Fin 5,
      (∃ σ : Equiv.Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ permVec σ v = wvec i) ∨
      (∃ σ τ : Equiv.Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ τ ∈ alternatingGroup (Fin 5) ∧
        permVec σ v + permVec τ v = wvec i) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  unfold IsEvenVec wvec permVec
  decide +kernel

theorem sec128_irredW (U : AddSubgroup EvW)
    (hU : ∀ σ ∈ alternatingGroup (Fin 5), ∀ a ∈ U, permW σ a ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨a, haU, ha0⟩ : ∃ a ∈ U, a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((AddSubgroup.eq_bot_iff_forall U).mpr hcon)
  have ha0' : a.1 ≠ 0 := fun h => ha0 (Subtype.ext h)
  have hw : ∀ i, (⟨wvec i, wvec_even i⟩ : EvW) ∈ U := by
    intro i
    rcases sec128_orbit_wvec a.1 a.2 ha0' i with ⟨σ, hσ, h⟩ | ⟨σ, τ, hσ, hτ, h⟩
    · have := hU σ hσ a haU
      rwa [show permW σ a = ⟨wvec i, wvec_even i⟩ from Subtype.ext h] at this
    · have := U.add_mem (hU σ hσ a haU) (hU τ hτ a haU)
      rwa [show permW σ a + permW τ a = ⟨wvec i, wvec_even i⟩ from Subtype.ext h] at this
  refine eq_top_iff.mpr fun w _ => ?_
  obtain ⟨a, b, c, d, hd⟩ := even_eq_four_wvec w.2
  have : w = ((⟨wvec a, wvec_even a⟩ + ⟨wvec b, wvec_even b⟩) +
      (⟨wvec c, wvec_even c⟩ + ⟨wvec d, wvec_even d⟩) : EvW) := Subtype.ext hd
  rw [this]
  exact U.add_mem (U.add_mem (hw a) (hw b)) (U.add_mem (hw c) (hw d))

section Twisted

variable {ι : Type*} (s1 s2 : ι → EvW →+ EvW)

@[expose] def OntoAct (s : ι → EvW →+ EvW) : Prop :=
  ∀ σ ∈ alternatingGroup (Fin 5), ∃ i, s i = permW σ

variable {s1 s2}

theorem sec128_tw_dich (h1 : OntoAct s1) (h2 : OntoAct s2) (g : EvW →+ EvW)
    (hg : ∀ i a, g (s2 i a) = s1 i (g a)) : g = 0 ∨ Function.Bijective g := by
  have hk : g.ker = ⊥ ∨ g.ker = ⊤ := by
    refine sec128_irredW g.ker fun σ hσ a ha => ?_
    obtain ⟨i, hi⟩ := h2 σ hσ
    rw [AddMonoidHom.mem_ker] at ha ⊢
    rw [← hi, hg, ha, map_zero]
  have hr : g.range = ⊥ ∨ g.range = ⊤ := by
    refine sec128_irredW g.range fun σ hσ a ha => ?_
    obtain ⟨i, hi⟩ := h1 σ hσ
    obtain ⟨b, rfl⟩ := ha
    rw [← hi, ← hg]
    exact ⟨_, rfl⟩
  rcases hk with hk | hk
  · rcases hr with hr | hr
    · left
      refine AddMonoidHom.ext fun a => ?_
      have : g a ∈ g.range := ⟨a, rfl⟩
      rw [hr] at this
      exact AddSubgroup.mem_bot.mp this
    · exact Or.inr ⟨(AddMonoidHom.ker_eq_bot_iff g).mp hk, AddMonoidHom.range_eq_top.mp hr⟩
  · left
    refine AddMonoidHom.ext fun a => ?_
    have : a ∈ g.ker := by rw [hk]; exact AddSubgroup.mem_top a
    exact AddMonoidHom.mem_ker.mp this

theorem sec128_tw_symm (g : EvW →+ EvW) (hb : Function.Bijective g)
    (hg : ∀ i a, g (s2 i a) = s1 i (g a)) :
    ∃ g' : EvW →+ EvW, Function.Bijective g' ∧ ∀ i a, g' (s1 i a) = s2 i (g' a) := by
  let e : EvW ≃+ EvW := AddEquiv.ofBijective g hb
  refine ⟨e.symm.toAddMonoidHom, e.symm.bijective, fun i a => ?_⟩
  have h1 : g (e.symm a) = a := e.apply_symm_apply a
  have h2 : e.symm (s1 i a) = s2 i (e.symm a) := by
    rw [e.symm_apply_eq]
    show s1 i a = g (s2 i (e.symm a))
    rw [hg, h1]
  exact h2

end Twisted

end CFSG.OddStandard.SmallF3.Omega
