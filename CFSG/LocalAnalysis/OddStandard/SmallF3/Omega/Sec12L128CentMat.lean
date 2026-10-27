module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128CentW

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def thetaW (e : Matrix (Fin 2) (Fin 2) (ZMod 2)) : (EvW × EvW) →+ (EvW × EvW) where
  toFun p := (e 0 0 • p.1 + e 0 1 • p.2, e 1 0 • p.1 + e 1 1 • p.2)
  map_zero' := by simp
  map_add' p q := by
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, smul_add] <;> abel

theorem sec128_thetaW_apply (e : Matrix (Fin 2) (Fin 2) (ZMod 2)) (p : EvW × EvW) :
    thetaW e p = (e 0 0 • p.1 + e 0 1 • p.2, e 1 0 • p.1 + e 1 1 • p.2) := rfl

theorem sec128_thetaW_mul (e e' : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    thetaW (e * e') = (thetaW e).comp (thetaW e') := by
  refine AddMonoidHom.ext fun p => ?_
  simp only [AddMonoidHom.comp_apply, sec128_thetaW_apply, Matrix.mul_apply, Fin.sum_univ_two]
  refine Prod.ext ?_ ?_ <;> simp only [smul_add, smul_smul, add_smul] <;> abel

theorem sec128_thetaW_one : thetaW 1 = AddMonoidHom.id (EvW × EvW) := by
  refine AddMonoidHom.ext fun p => ?_
  simp [sec128_thetaW_apply]

@[expose] def w0 : EvW := ⟨wvec 0, wvec_even 0⟩

theorem sec128_w0_ne : w0 ≠ 0 := by
  intro h
  have h1 : wvec 0 = 0 := congrArg Subtype.val h
  have h2 := congrFun h1 1
  revert h2
  unfold wvec
  decide

theorem sec128_smul_w0_inj {x y : ZMod 2} (h : x • w0 = y • w0) : x = y := by
  have h0 := sec128_w0_ne
  have hxy : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hxy x with rfl | rfl <;> rcases hxy y with rfl | rfl
  · rfl
  · exfalso
    apply h0
    simpa using h.symm
  · exfalso
    apply h0
    simpa using h
  · rfl

theorem sec128_thetaW_injective : Function.Injective thetaW := by
  intro e e' h
  have h1 := congrArg (fun f => f (w0, 0)) h
  have h2 := congrArg (fun f => f (0, w0)) h
  simp only [sec128_thetaW_apply, smul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  ext i j
  fin_cases i <;> fin_cases j
  · exact sec128_smul_w0_inj h1.1
  · exact sec128_smul_w0_inj h2.1
  · exact sec128_smul_w0_inj h1.2
  · exact sec128_smul_w0_inj h2.2

theorem sec128_order3_matrix (e : Matrix (Fin 2) (Fin 2) (ZMod 2)) (h3 : e * e * e = 1)
    (hne : e ≠ 1) :
    (e 0 0 = 0 ∧ e 0 1 = 1 ∧ e 1 0 = 1 ∧ e 1 1 = 1) ∨
      (e 0 0 = 1 ∧ e 0 1 = 1 ∧ e 1 0 = 1 ∧ e 1 1 = 0) := by
  revert h3 hne e
  decide +kernel

theorem sec128_theta_fix (e : Matrix (Fin 2) (Fin 2) (ZMod 2)) (h3 : e * e * e = 1) (hne : e ≠ 1)
    (p : EvW × EvW) (hp : thetaW e p = p) : p = 0 := by
  rw [sec128_thetaW_apply] at hp
  obtain ⟨hp1, hp2⟩ := Prod.mk.inj hp
  rcases sec128_order3_matrix e h3 hne with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · rw [a, b] at hp1
    rw [c, d] at hp2
    simp only [zero_smul, one_smul, zero_add] at hp1 hp2
    have h1 : p.1 = 0 := by
      have := hp2
      have h3' : p.1 + p.2 = p.2 := hp2
      simpa using h3'
    have h2 : p.2 = 0 := by
      rw [h1] at hp1
      exact hp1
    exact Prod.ext h1 h2
  · rw [a, b] at hp1
    rw [c, d] at hp2
    simp only [zero_smul, one_smul, add_zero] at hp1 hp2
    have h2 : p.2 = 0 := by
      have h3' : p.1 + p.2 = p.1 := hp1
      simpa using h3'
    have h1 : p.1 = 0 := by
      rw [h2] at hp2
      exact hp2
    exact Prod.ext h1 h2

theorem sec128_card_GL2 : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def ent11 (f : EvW × EvW →+ EvW × EvW) : EvW →+ EvW :=
  (AddMonoidHom.fst EvW EvW).comp (f.comp (AddMonoidHom.inl EvW EvW))

@[expose] def ent12 (f : EvW × EvW →+ EvW × EvW) : EvW →+ EvW :=
  (AddMonoidHom.fst EvW EvW).comp (f.comp (AddMonoidHom.inr EvW EvW))

@[expose] def ent21 (f : EvW × EvW →+ EvW × EvW) : EvW →+ EvW :=
  (AddMonoidHom.snd EvW EvW).comp (f.comp (AddMonoidHom.inl EvW EvW))

@[expose] def ent22 (f : EvW × EvW →+ EvW × EvW) : EvW →+ EvW :=
  (AddMonoidHom.snd EvW EvW).comp (f.comp (AddMonoidHom.inr EvW EvW))

theorem sec128_ent_apply (f : EvW × EvW →+ EvW × EvW) (p : EvW × EvW) :
    f p = (ent11 f p.1 + ent12 f p.2, ent21 f p.1 + ent22 f p.2) := by
  have hp : p = (p.1, 0) + (0, p.2) := by simp
  conv_lhs => rw [hp, map_add]
  rfl

theorem sec128_ent11_apply (f : EvW × EvW →+ EvW × EvW) (a : EvW) :
    ent11 f a = (f (a, 0)).1 := rfl

theorem sec128_ent12_apply (f : EvW × EvW →+ EvW × EvW) (b : EvW) :
    ent12 f b = (f (0, b)).1 := rfl

theorem sec128_ent21_apply (f : EvW × EvW →+ EvW × EvW) (a : EvW) :
    ent21 f a = (f (a, 0)).2 := rfl

theorem sec128_ent22_apply (f : EvW × EvW →+ EvW × EvW) (b : EvW) :
    ent22 f b = (f (0, b)).2 := rfl

theorem sec128_ent_comm {ι : Type*} {s1 s2 : ι → EvW →+ EvW} (f : EvW × EvW →+ EvW × EvW)
    (hf : ∀ i p, f (s1 i p.1, s2 i p.2) = (s1 i (f p).1, s2 i (f p).2)) (i : ι) :
    (∀ a, ent11 f (s1 i a) = s1 i (ent11 f a)) ∧ (∀ a, ent21 f (s1 i a) = s2 i (ent21 f a)) ∧
      (∀ b, ent12 f (s2 i b) = s1 i (ent12 f b)) ∧ (∀ b, ent22 f (s2 i b) = s2 i (ent22 f b)) := by
  refine ⟨fun a => ?_, fun a => ?_, fun b => ?_, fun b => ?_⟩
  · have h := congrArg Prod.fst (hf i (a, 0))
    simpa [sec128_ent11_apply] using h
  · have h := congrArg Prod.snd (hf i (a, 0))
    simpa [sec128_ent21_apply] using h
  · have h := congrArg Prod.fst (hf i (0, b))
    simpa [sec128_ent12_apply] using h
  · have h := congrArg Prod.snd (hf i (0, b))
    simpa [sec128_ent22_apply] using h

theorem sec128_exists_theta {ι : Type*} {s : ι → EvW →+ EvW} (hs : OntoAct s)
    (f : EvW × EvW →+ EvW × EvW)
    (hf : ∀ i p, f (s i p.1, s i p.2) = (s i (f p).1, s i (f p).2)) :
    ∃ e : Matrix (Fin 2) (Fin 2) (ZMod 2), f = thetaW e := by
  have key : ∀ g : EvW →+ EvW, (∀ i a, g (s i a) = s i (g a)) →
      ∃ c : ZMod 2, ∀ a, g a = c • a := by
    intro g hg
    rcases sec128_schurW g (fun σ hσ a => by
      obtain ⟨i, hi⟩ := hs σ hσ
      rw [← hi]
      exact hg i a) with h | h
    · exact ⟨0, fun a => by rw [h]; simp⟩
    · exact ⟨1, fun a => by rw [h]; simp⟩
  obtain ⟨c11, h11⟩ := key (ent11 f) fun i a => (sec128_ent_comm f hf i).1 a
  obtain ⟨c21, h21⟩ := key (ent21 f) fun i a => (sec128_ent_comm f hf i).2.1 a
  obtain ⟨c12, h12⟩ := key (ent12 f) fun i a => (sec128_ent_comm f hf i).2.2.1 a
  obtain ⟨c22, h22⟩ := key (ent22 f) fun i a => (sec128_ent_comm f hf i).2.2.2 a
  refine ⟨Matrix.of ![![c11, c12], ![c21, c22]], AddMonoidHom.ext fun p => ?_⟩
  rw [sec128_ent_apply f p, h11, h12, h21, h22]
  rfl

theorem sec128_noiso_id {ι : Type*} {s1 s2 : ι → EvW →+ EvW} (h1 : OntoAct s1) (h2 : OntoAct s2)
    (hno : ¬ ∃ g : EvW →+ EvW, Function.Bijective g ∧ ∀ i a, g (s2 i a) = s1 i (g a))
    (f : EvW × EvW →+ EvW × EvW)
    (hf : ∀ i p, f (s1 i p.1, s2 i p.2) = (s1 i (f p).1, s2 i (f p).2))
    (hinj : Function.Injective f) : f = AddMonoidHom.id (EvW × EvW) := by
  have c := sec128_ent_comm f hf
  have e12 : ent12 f = 0 := by
    rcases sec128_tw_dich h1 h2 (ent12 f) (fun i b => (c i).2.2.1 b) with h | h
    · exact h
    · exact absurd ⟨ent12 f, h, fun i b => (c i).2.2.1 b⟩ hno
  have e21 : ent21 f = 0 := by
    rcases sec128_tw_dich (s1 := s2) (s2 := s1) h2 h1 (ent21 f) (fun i a => (c i).2.1 a) with h | h
    · exact h
    · exfalso
      obtain ⟨g', hb, hg'⟩ := sec128_tw_symm (s1 := s2) (s2 := s1) (ent21 f) h
        (fun i a => (c i).2.1 a)
      exact hno ⟨g', hb, hg'⟩
  have d11 : ent11 f = 0 ∨ ent11 f = AddMonoidHom.id EvW :=
    sec128_schurW _ fun σ hσ a => by
      obtain ⟨i, hi⟩ := h1 σ hσ
      rw [← hi]
      exact (c i).1 a
  have d22 : ent22 f = 0 ∨ ent22 f = AddMonoidHom.id EvW :=
    sec128_schurW _ fun σ hσ a => by
      obtain ⟨i, hi⟩ := h2 σ hσ
      rw [← hi]
      exact (c i).2.2.2 a
  have f11 : ent11 f = AddMonoidHom.id EvW := by
    rcases d11 with h | h
    · exfalso
      have hz : f (w0, 0) = f 0 := by
        rw [sec128_ent_apply f (w0, 0), map_zero, h, e21]
        simp
      exact sec128_w0_ne (congrArg Prod.fst (hinj hz))
    · exact h
  have f22 : ent22 f = AddMonoidHom.id EvW := by
    rcases d22 with h | h
    · exfalso
      have hz : f (0, w0) = f 0 := by
        rw [sec128_ent_apply f (0, w0), map_zero, h, e12]
        simp
      exact sec128_w0_ne (congrArg Prod.snd (hinj hz))
    · exact h
  refine AddMonoidHom.ext fun p => ?_
  rw [sec128_ent_apply f p, f11, f22, e12, e21]
  simp

end CFSG.OddStandard.SmallF3.Omega
