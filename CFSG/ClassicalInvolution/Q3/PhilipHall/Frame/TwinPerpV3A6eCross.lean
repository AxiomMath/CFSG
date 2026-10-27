module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eStep4

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

theorem card_symmDiff_four {a B : Finset (Fin 8)} (ha : a.card = 4) (hB : B.card = 4) :
    (symmDiff a B).card = 8 - 2 * (a ∩ B).card := by
  have h1 := Finset.card_sdiff_add_card_inter a B
  have h2 := Finset.card_sdiff_add_card_inter B a
  rw [Finset.inter_comm] at h2
  have hd : Disjoint (a \ B) (B \ a) := disjoint_sdiff_sdiff
  have e : symmDiff a B = (a \ B) ∪ (B \ a) := by
    ext z
    simp [Finset.mem_symmDiff]
  rw [e, Finset.card_union_of_disjoint hd]
  omega

namespace A6eCtx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem frame_sq : a₁ * a₁ = t ∧ a₂ * a₂ = t ∧ a₃ * a₃ = t ∧ a₄ * a₄ = t :=
  ⟨Asc77.sq_eq_of_orderOf_four (C.uniq C.hKt) C.fr.h₁.1 C.fr.o₁,
    Asc77.sq_eq_of_orderOf_four (C.uniq C.hK't) C.fr.h₂.1 C.fr.o₂,
    Asc77.sq_eq_of_orderOf_four (C.uniq C.hK₃t) C.fr.h₃.1 C.fr.o₃,
    Asc77.sq_eq_of_orderOf_four (C.uniq C.hK₄t) C.fr.h₄.1 C.fr.o₄⟩

include C in
theorem u_ne : u₁ * u₂ ≠ t ∧ u₁ * u₂ ≠ y * t * y⁻¹ ∧ u₁ * u₂ ≠ t * (y * t * y⁻¹) := by
  obtain ⟨hKK', hKK₃, hKK₄, hK'K₃, hK'K₄, hK₃K₄⟩ := C.twins_ne
  obtain ⟨s₁, s₂, s₃, s₄⟩ := C.frame_sq
  obtain ⟨h12, h12t⟩ := C.kk_ne C.hKt C.hK't hKK' C.fr.h₁.1 C.fr.h₂.1 s₁ s₂
  obtain ⟨h34, h34t⟩ := C.kk_ne C.hK₃t C.hK₄t hK₃K₄ C.fr.h₃.1 C.fr.h₄.1 s₃ s₄
  have hu : u₁ * u₂ = a₁ * a₂ := C.fr.hu.symm
  have hy : y * t * y⁻¹ = (a₁ * a₂) * (a₃ * a₄) := by rw [C.fr.hy]; group
  have hz := C.uniq C.hKt
  refine ⟨fun h => h12t (hu ▸ h), fun h => h34 ?_, fun h => h34t ?_⟩
  · rw [hu, hy] at h
    have h' : (a₁ * a₂) * 1 = (a₁ * a₂) * (a₃ * a₄) := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  · rw [hu, hy] at h
    have e1 : t * a₁ = a₁ * t := (C.twin_q8 C.hKt).z_central a₁ C.fr.h₁.1
    have e2 : t * a₂ = a₂ * t := (C.twin_q8 C.hK't).z_central a₂ C.fr.h₂.1
    have htP : t * (a₁ * a₂) = (a₁ * a₂) * t := by
      calc t * (a₁ * a₂) = (t * a₁) * a₂ := by group
        _ = (a₁ * t) * a₂ := by rw [e1]
        _ = a₁ * (t * a₂) := by group
        _ = a₁ * (a₂ * t) := by rw [e2]
        _ = (a₁ * a₂) * t := by group
    have h' : (a₁ * a₂) * 1 = (a₁ * a₂) * (t * (a₃ * a₄)) := by
      calc (a₁ * a₂) * 1 = a₁ * a₂ := mul_one _
        _ = t * ((a₁ * a₂) * (a₃ * a₄)) := h
        _ = (t * (a₁ * a₂)) * (a₃ * a₄) := by group
        _ = ((a₁ * a₂) * t) * (a₃ * a₄) := by rw [htP]
        _ = (a₁ * a₂) * (t * (a₃ * a₄)) := by group
    have h3 : 1 = t * (a₃ * a₄) := mul_left_cancel h'
    have h4 : a₃ * a₄ = t⁻¹ := eq_inv_of_mul_eq_one_right h3.symm
    rw [inv_eq_of_mul_eq_one_right hz.sq] at h4
    exact h4

include C in
theorem u_weight2 {a : Finset (Fin 8)} {ha : a.card = 4} {b₁ b₂ : Bool}
    (hta : C.P.ph t = vq a) (hl₁ : ∀ k ∈ C.I, k ∈ K ↔ C.P.ph k ∈ memBar a ha b₁)
    (hl₂ : ∀ k ∈ C.I, k ∈ K' ↔ C.P.ph k ∈ memBar a ha b₂) :
    ∃ S : Finset (Fin 8), S.card = 2 ∧ C.P.ph (u₁ * u₂) = vq S := by
  have hd := C.H.ex.1.datum
  have hKI := C.K_le_I
  have hK'I := C.twin_le_I C.hK't
  have huI : u₁ * u₂ ∈ C.I := C.I.mul_mem (hKI hd.hu₁.1) (hK'I hd.hu₂.1)
  obtain ⟨hune1, hunet⟩ := C.kk_ne C.hKt C.hK't C.twins_ne.1 hd.hu₁.1 hd.hu₂.1 hd.sq₁ hd.sq₂
  have hphu : C.P.ph (u₁ * u₂) ≠ vq a := fun e =>
    hunet (C.P.ph_inj huI C.t_mem_I (by rw [e, hta]))
  obtain ⟨S, -, hS2, hS⟩ := C.P.w2 hKI hK'I hl₁ hl₂ hd.hu₁.1 hd.hu₂.1 C.u_mem_D hune1 hphu
  exact ⟨S, hS2, hS⟩

include C in
theorem u_weight2' : ∃ S : Finset (Fin 8), S.card = 2 ∧ C.P.ph (u₁ * u₂) = vq S := by
  obtain ⟨a, ha, β₁, β₂, β₃, β₄, hta, hl₁, hl₂, -, -⟩ := C.sides
  exact C.u_weight2 hta hl₁ hl₂

include C in
theorem hno2 : ∀ d ∈ C.D, ∀ S : Finset (Fin 8), S.card = 2 → C.P.ph d = vq S →
    ∀ g : Y, g * t * g⁻¹ ≠ d := by
  intro d hd S hS hph g hg
  have hd' := C.H.ex.1.datum
  obtain ⟨Su, hSu2, hSu⟩ := C.u_weight2'
  have huI : u₁ * u₂ ∈ C.I := C.I.mul_mem (C.K_le_I hd'.hu₁.1) (C.twin_le_I C.hK't hd'.hu₂.1)
  obtain ⟨i, hi, hiu⟩ := C.P.exists_conj_two huI (C.P.le hd) hSu2 hS hSu hph
  have hug : (i⁻¹ * g) * t * (i⁻¹ * g)⁻¹ = u₁ * u₂ := by
    have : g * t * g⁻¹ = d := hg
    calc (i⁻¹ * g) * t * (i⁻¹ * g)⁻¹ = i⁻¹ * (g * t * g⁻¹) * i := by group
      _ = i⁻¹ * d * i := by rw [this]
      _ = u₁ * u₂ := by rw [← hiu]; group
  have huW : u₁ * u₂ ∈ W := W.mul_mem C.H.hu₁ C.H.hu₂
  rcases A6Wt.mem_tG_W C.H C.fr huW hug with h | h | h
  · exact C.u_ne.1 h
  · exact C.u_ne.2.1 h
  · exact C.u_ne.2.2 h

include C in
theorem tt_conj : ∃ g : Y, g * t * g⁻¹ = t * (y * t * y⁻¹) := by
  obtain ⟨s₁, s₂, s₃, s₄⟩ := C.frame_sq
  obtain ⟨hKK', hKK₃, hKK₄, hK'K₃, hK'K₄, hK₃K₄⟩ := C.twins_ne
  have hz := C.uniq C.hKt
  have hq := C.twin_q8 C.hKt
  have hne1 : a₁ ≠ 1 := fun e => hz.ne_one (by rw [← s₁, e, mul_one])
  have hnet : a₁ ≠ t := fun e => hz.ne_one (by
    have : t * t = t := by rw [e] at s₁; exact s₁
    have h2 : t * t = t * 1 := by rw [this, mul_one]
    exact mul_left_cancel h2)
  obtain ⟨j, hjK, hj⟩ := hq.exists_noncomm a₁ C.fr.h₁.1 hne1 hnet
  have hcomm := hq.comm_eq a₁ C.fr.h₁.1 j hjK hj
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hz.sq
  have h1 : j * a₁ * j⁻¹ * a₁⁻¹ = t := by
    calc j * a₁ * j⁻¹ * a₁⁻¹ = (a₁ * j * a₁⁻¹ * j⁻¹)⁻¹ := by group
      _ = t⁻¹ := by rw [hcomm]
      _ = t := htinv
  have hja : j * a₁ * j⁻¹ = t * a₁ := by
    calc j * a₁ * j⁻¹ = (j * a₁ * j⁻¹ * a₁⁻¹) * a₁ := by group
      _ = t * a₁ := by rw [h1]
  have c2 := C.twin_comm C.hKt C.hK't hKK' j hjK a₂ C.fr.h₂.1
  have c3 := C.twin_comm C.hKt C.hK₃t hKK₃ j hjK a₃ C.fr.h₃.1
  have c4 := C.twin_comm C.hKt C.hK₄t hKK₄ j hjK a₄ C.fr.h₄.1
  have hj2 : j * a₂ * j⁻¹ = a₂ := by rw [c2]; group
  have hj3 : j * a₃ * j⁻¹ = a₃ := by rw [c3]; group
  have hj4 : j * a₄ * j⁻¹ = a₄ := by rw [c4]; group
  refine ⟨j * y, ?_⟩
  calc (j * y) * t * (j * y)⁻¹ = j * (y * t * y⁻¹) * j⁻¹ := by group
    _ = j * (a₁ * a₂ * a₃ * a₄) * j⁻¹ := by rw [C.fr.hy]
    _ = (j * a₁ * j⁻¹) * (j * a₂ * j⁻¹) * (j * a₃ * j⁻¹) * (j * a₄ * j⁻¹) := by group
    _ = (t * a₁) * a₂ * a₃ * a₄ := by rw [hja, hj2, hj3, hj4]
    _ = t * (a₁ * a₂ * a₃ * a₄) := by group
    _ = t * (y * t * y⁻¹) := by rw [C.fr.hy]

include C in
theorem tau_cross {a : Finset (Fin 8)} (ha : a.card = 4) (hta : C.P.ph t = vq a) :
    ∃ β : Finset (Fin 8), C.P.ph (y * t * y⁻¹) = vq β ∧ β.card = 4 ∧ (a ∩ β).card = 2 := by
  have hz := C.uniq C.hKt
  have hτD := C.tau_mem_D
  have hτne := A6Hx.tau_ne_t C.H C.fr
  have hτ1 : y * t * y⁻¹ ≠ 1 := fun e => hz.ne_one (by
    have := congrArg (fun z => y⁻¹ * z * y) e
    simpa [mul_assoc] using this)
  obtain ⟨-, β, hβ, hphβ⟩ := C.P.w4_of_conj C.hno2 hτD hτ1 ⟨y, rfl⟩
  obtain ⟨g, hg⟩ := C.tt_conj
  have htτD : t * (y * t * y⁻¹) ∈ C.D := C.D.mul_mem C.t_mem_D hτD
  have htτ1 : t * (y * t * y⁻¹) ≠ 1 := fun e => hτne (by
    have h1 : y * t * y⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hz.sq)
  obtain ⟨-, γ, hγ, hphγ⟩ := C.P.w4_of_conj C.hno2 htτD htτ1 ⟨g, hg⟩
  have hvq : vq (symmDiff a β) = vq γ := by
    rw [← vq_mul, ← hta, ← hphβ, ← C.P.ph_mul C.t_mem_I (C.P.le hτD), hphγ]
  have hcard : (symmDiff a β).card = 4 := by
    have hle : (symmDiff a β).card ≤ 8 := by
      have := Finset.card_le_univ (symmDiff a β)
      simpa using this
    rcases vq_eq_iff.mp hvq with h | h
    · rw [← h]
      exact hγ
    · have h2 := congrArg Finset.card h
      rw [Finset.card_compl] at h2
      simp only [Fintype.card_fin] at h2
      omega
  rw [card_symmDiff_four ha hβ] at hcard
  exact ⟨β, hphβ, hβ, by omega⟩

end A6eCtx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
