module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eCtx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eShape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

namespace A6eCtx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem hKt : K ∈ twinSet Ω[R] K := mem_twinSet_self C.H.ex.1.datum.mem C.H.ex.1.datum.hz

include C in
theorem hK't : K' ∈ twinSet Ω[R] K := C.H.ex.1.datum.hK'

include C in
theorem hK₃t : K₃ ∈ twinSet Ω[R] K := C.H.ex.1.datum.hK₃

include C in
theorem hK₄t : K₄ ∈ twinSet Ω[R] K := C.H.ex.2.1.1

include C in
theorem twins_ne : K ≠ K' ∧ K ≠ K₃ ∧ K ≠ K₄ ∧ K' ≠ K₃ ∧ K' ≠ K₄ ∧ K₃ ≠ K₄ :=
  ⟨C.H.ex.1.datum.hne.symm, C.H.ex.1.datum.hK₃K.symm, C.H.ex.2.1.2.1.symm,
    C.H.ex.1.datum.hK₃K'.symm, C.H.ex.2.1.2.2.1.symm, C.H.ex.2.1.2.2.2.1.symm⟩

include C in
theorem uniq {J : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K) : IsUniqueInvolution J t :=
  Asc77.isUniqueInvolution_of_mem_twinSet C.H.ex.1.datum.hz hJ

include C in
theorem twin_comm {J J' : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K) (hJ' : J' ∈ twinSet Ω[R] K)
    (hne : J ≠ J') : ∀ x ∈ J, ∀ x' ∈ J', x * x' = x' * x :=
  TC.Thin.twin_comm (CoreData.of_S C.H.ex.1.perp.core).hyp C.H.ex.2.2.2.1 hJ.1 hJ'.1 hne
    (C.uniq hJ) (C.uniq hJ')

include C in
theorem twin_q8 {J : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K) : WF.Q8Facts J t := by
  obtain ⟨e⟩ := members_q8_of_isPGroup C.H.ex.1.perp C.H.ex.2.2.2.1 J hJ.1
  exact WF.q8Facts_of_iso (C.uniq hJ) e

include C in
theorem twin_mem_fam {J : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K) : J ∈ ae6ConjIn C.I K := by
  obtain ⟨m, hm, hmK⟩ := A6jB.exists_M_conj_of_twin C.H hJ
  exact ⟨m, Subgroup.mem_sup_left hm, hmK⟩

include C in
theorem twin_le_I {J : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K) : J ≤ C.I := by
  obtain ⟨m, hm, rfl⟩ := A6jB.exists_M_conj_of_twin C.H hJ
  have hKM : K ≤ MGrp Ω[R] W := by
    unfold MGrp
    exact le_iSup₂_of_le K C.H.hK le_rfl
  have hmI : m ∈ C.I := Subgroup.mem_sup_left hm
  have hKI : K ≤ C.I := le_trans hKM le_sup_left
  calc conjSub m K ≤ conjSub m C.I := conjSub_mono hKI
    _ = C.I := conjSub_eq_self_of_mem hmI

include C in
theorem t_mem_I : t ∈ C.I := C.twin_le_I C.hKt (C.uniq C.hKt).mem

include C in
theorem K_le_I : K ≤ C.I := C.twin_le_I C.hKt

include C in
theorem lab_ph {J : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K) :
    ∃ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool),
      ∀ k ∈ C.I, k ∈ J ↔ C.P.ph k ∈ memBar α h b := by
  obtain ⟨α, h, b, hl⟩ := C.lab J (C.twin_mem_fam hJ)
  exact ⟨α, h, b, fun k hk => by rw [C.P.ph_of_mem hk]; exact hl ⟨k, hk⟩⟩

include C in
theorem ph_t_eq {J : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K) {α : Finset (Fin 8)} {h : α.card = 4}
    {b : Bool} (hl : ∀ k ∈ C.I, k ∈ J ↔ C.P.ph k ∈ memBar α h b) : C.P.ph t = vq α := by
  have hz := C.uniq hJ
  have htI := C.t_mem_I
  have hx : C.P.ph t ∈ memBar α h b := (hl t htI).1 hz.mem
  have h2 : C.P.ph t * C.P.ph t = 1 := by
    rw [← C.P.ph_mul htI htI, hz.sq, C.P.ph_one]
  have hne : C.P.ph t ≠ 1 := fun e =>
    hz.ne_one (C.P.ph_inj htI C.I.one_mem (by rw [e, C.P.ph_one]))
  rcases eq_of_mem_memBar_mul_self (by norm_num) hx h2 with h1 | h1
  · exact absurd h1 hne
  · rw [h1, zBar_eq_vq]


include C in
theorem kk_ne {J J' : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K) (hJ' : J' ∈ twinSet Ω[R] K) (hne : J ≠ J')
    {k k' : Y} (hk : k ∈ J) (hk' : k' ∈ J') (hk2 : k * k = t) (hk'2 : k' * k' = t) :
    k * k' ≠ 1 ∧ k * k' ≠ t := by
  have hz := C.uniq hJ
  have key : k' ∉ J := by
    intro hk'J
    rcases (C.twin_q8 hJ').center k' hk' (fun g hg => C.twin_comm hJ hJ' hne k' hk'J g hg) with h | h
    · rw [h, mul_one] at hk'2
      exact hz.ne_one hk'2.symm
    · rw [h, hz.sq] at hk'2
      exact hz.ne_one hk'2.symm
  refine ⟨fun h => key ?_, fun h => key ?_⟩
  · rw [eq_inv_of_mul_eq_one_right h]
    exact J.inv_mem hk
  · have : k' = k⁻¹ * t := by rw [← h]; group
    rw [this]
    exact J.mul_mem (J.inv_mem hk) hz.mem

end A6eCtx

theorem bool3 : ∀ b₁ b₂ b : Bool, b₁ ≠ b₂ → b = b₁ ∨ b = b₂ := by decide

theorem card_compl_four {a : Finset (Fin 8)} (ha : a.card = 4) : aᶜ.card = 4 := by
  rw [Finset.card_compl]
  simp [ha]

namespace E8Pkg

variable {Y : Type} [Group Y] {I D : Subgroup Y} (P : E8Pkg I D)

theorem eq_of_lab {J J' : Subgroup Y} (hJI : J ≤ I) (hJ'I : J' ≤ I) {α : Finset (Fin 8)}
    {h : α.card = 4} {b : Bool} (hl : ∀ k ∈ I, k ∈ J ↔ P.ph k ∈ memBar α h b)
    (hl' : ∀ k ∈ I, k ∈ J' ↔ P.ph k ∈ memBar α h b) : J = J' := by
  ext g
  constructor
  · intro hg
    exact (hl' g (hJI hg)).2 ((hl g (hJI hg)).1 hg)
  · intro hg
    exact (hl g (hJ'I hg)).2 ((hl' g (hJ'I hg)).1 hg)

end E8Pkg

namespace A6eCtx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem sides : ∃ (a : Finset (Fin 8)) (ha : a.card = 4) (b₁ b₂ b₃ b₄ : Bool),
    C.P.ph t = vq a ∧
    (∀ k ∈ C.I, k ∈ K ↔ C.P.ph k ∈ memBar a ha b₁) ∧
    (∀ k ∈ C.I, k ∈ K' ↔ C.P.ph k ∈ memBar a ha b₂) ∧
    (∀ k ∈ C.I, k ∈ K₃ ↔ C.P.ph k ∈ memBar aᶜ (card_compl_four ha) b₃) ∧
    (∀ k ∈ C.I, k ∈ K₄ ↔ C.P.ph k ∈ memBar aᶜ (card_compl_four ha) b₄) := by
  have hd := C.H.ex.1.datum
  obtain ⟨α₁, h₁, b₁, hl₁⟩ := C.lab_ph C.hKt
  obtain ⟨α₂, h₂, b₂, hl₂⟩ := C.lab_ph C.hK't
  obtain ⟨α₃, h₃, b₃, hl₃⟩ := C.lab_ph C.hK₃t
  obtain ⟨α₄, h₄, b₄, hl₄⟩ := C.lab_ph C.hK₄t
  have e₁ := C.ph_t_eq C.hKt hl₁
  have e₂ := C.ph_t_eq C.hK't hl₂
  have e₃ := C.ph_t_eq C.hK₃t hl₃
  have e₄ := C.ph_t_eq C.hK₄t hl₄
  obtain ⟨hKK', hKK₃, hKK₄, hK'K₃, hK'K₄, hK₃K₄⟩ := C.twins_ne
  have hKI := C.twin_le_I C.hKt
  have hK'I := C.twin_le_I C.hK't
  have hK₃I := C.twin_le_I C.hK₃t
  have hK₄I := C.twin_le_I C.hK₄t
  have hu₁ : u₁ ∈ K := hd.hu₁.1
  have hu₂ : u₂ ∈ K' := hd.hu₂.1
  have hu₁I : u₁ ∈ C.I := hKI hu₁
  have hu₂I : u₂ ∈ C.I := hK'I hu₂
  have hz := C.uniq C.hKt
  have hside : α₂ = α₁ := by
    have hr₁ : C.P.rho u₁ ∈ V4set α₁ h₁ := permQ_mem_V4set ((hl₁ u₁ hu₁I).1 hu₁)
    have hr₂ : C.P.rho u₂ ∈ V4set α₂ h₂ := permQ_mem_V4set ((hl₂ u₂ hu₂I).1 hu₂)
    have hn₁ : C.P.rho u₁ ≠ 1 := fun e => by
      have hD := (C.P.mem_D_iff hu₁I).2 e
      have := C.hDsq u₁ hD
      rw [hd.sq₁] at this
      exact hz.ne_one this
    have hn₂ : C.P.rho u₂ ≠ 1 := fun e => by
      have hD := (C.P.mem_D_iff hu₂I).2 e
      have := C.hDsq u₂ hD
      rw [hd.sq₂] at this
      exact hz.ne_one this
    obtain ⟨hs₁, hf₁⟩ := V4set_fpf hr₁ hn₁
    obtain ⟨hs₂, hf₂⟩ := V4set_fpf hr₂ hn₂
    have hu12 : C.P.rho u₁ * C.P.rho u₂ = 1 := by
      rw [← C.P.rho_mul hu₁I hu₂I]
      exact C.P.rho_eq_one_of_mem_D C.u_mem_D
    have heq : C.P.rho u₂ = C.P.rho u₁ :=
      (eq_inv_of_mul_eq_one_right hu12).trans (inv_eq_of_mul_eq_one_right hs₁)
    ext z
    rw [hf₂ z, hf₁ z, heq]
  have hside' : α₁ = α₂ := hside.symm
  subst hside'
  have hb₁₂ : b₁ ≠ b₂ := fun e => by
    subst e
    exact hKK' (C.P.eq_of_lab hKI hK'I hl₁ hl₂)
  have hα₃ : α₃ = α₁ᶜ := by
    rcases vq_eq_iff.mp (e₁.symm.trans e₃) with c | c
    · exfalso
      subst c
      rcases bool3 b₁ b₂ b₃ hb₁₂ with e | e
      · subst e
        exact hKK₃ (C.P.eq_of_lab hKI hK₃I hl₁ hl₃)
      · subst e
        exact hK'K₃ (C.P.eq_of_lab hK'I hK₃I hl₂ hl₃)
    · exact c
  have hα₄ : α₄ = α₁ᶜ := by
    rcases vq_eq_iff.mp (e₁.symm.trans e₄) with c | c
    · exfalso
      subst c
      rcases bool3 b₁ b₂ b₄ hb₁₂ with e | e
      · subst e
        exact hKK₄ (C.P.eq_of_lab hKI hK₄I hl₁ hl₄)
      · subst e
        exact hK'K₄ (C.P.eq_of_lab hK'I hK₄I hl₂ hl₄)
    · exact c
  subst hα₃
  subst hα₄
  exact ⟨α₁, h₁, b₁, b₂, b₃, b₄, e₁, hl₁, hl₂, hl₃, hl₄⟩

end A6eCtx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
