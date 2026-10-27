module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eN

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

theorem V4_preserve {σ : Equiv.Perm (Fin 8)} {α : Finset (Fin 8)} (hs : σ * σ = 1)
    (hf : ∀ z, z ∈ α ↔ σ z ≠ z) : ∀ z, σ z ∈ α ↔ z ∈ α := by
  have hss : ∀ w, σ (σ w) = w := fun w => by
    have := congrArg (fun p : Equiv.Perm (Fin 8) => p w) hs
    simpa [Equiv.Perm.mul_apply] using this
  intro z
  rw [hf (σ z), hss, hf z]
  exact ⟨fun h e => h e.symm, fun h e => h e.symm⟩

theorem fpf_of_V4 {a : Finset (Fin 8)} {ha : a.card = 4} {σ σ' : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ V4set a ha) (hσ' : σ' ∈ V4set aᶜ (card_compl_four ha)) (h1 : σ ≠ 1) (h1' : σ' ≠ 1) :
    (∀ z, (σ * σ') z ≠ z) ∧ (∀ z, (σ * σ') z ∈ a ↔ z ∈ a) := by
  obtain ⟨hs, hf⟩ := V4set_fpf hσ h1
  obtain ⟨hs', hf'⟩ := V4set_fpf hσ' h1'
  have hp := V4_preserve hs hf
  have hp' := V4_preserve hs' hf'
  have hfixσ : ∀ z, z ∉ a → σ z = z := fun z hz => by
    by_contra h
    exact hz ((hf z).2 h)
  have hfixσ' : ∀ z, z ∈ a → σ' z = z := fun z hz => by
    by_contra h
    exact (Finset.mem_compl.mp ((hf' z).2 h)) hz
  refine ⟨fun z => ?_, fun z => ?_⟩
  · by_cases hz : z ∈ a
    · rw [Equiv.Perm.mul_apply, hfixσ' z hz]
      exact (hf z).1 hz
    · have hzc : z ∈ aᶜ := Finset.mem_compl.mpr hz
      rw [Equiv.Perm.mul_apply]
      have h2 : σ' z ∉ a := fun h => (Finset.mem_compl.mp ((hp' z).2 hzc)) h
      rw [hfixσ _ h2]
      exact (hf' z).1 hzc
  · by_cases hz : z ∈ a
    · rw [Equiv.Perm.mul_apply, hfixσ' z hz]
      exact hp z
    · have hzc : z ∈ aᶜ := Finset.mem_compl.mpr hz
      rw [Equiv.Perm.mul_apply]
      have h2 : σ' z ∉ a := fun h => (Finset.mem_compl.mp ((hp' z).2 hzc)) h
      rw [hfixσ _ h2]
      exact ⟨fun h => absurd h h2, fun h => absurd h hz⟩

namespace A6eCtx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem P_le_I : ae6P Ω[R] t ≤ C.I := by
  unfold ae6P
  refine iSup₂_le fun J hJ => ?_
  exact C.twin_le_I ⟨hJ.1, t, C.uniq C.hKt, hJ.2⟩

include C in
theorem rho_gen {W' : Subgroup Y} (hW' : W' ∈ WSet Ω[R]) (htW' : t ∈ W') {J : Subgroup Y}
    (hJ : J ∈ twinSet Ω[R] K) {b c' : Y} (hb : b ∈ J ⊓ W') (hc : c' ∈ J ⊓ W') (ob : orderOf b = 4)
    (oc : orderOf c' = 4) : C.P.rho c' = C.P.rho b := by
  have hStd := C.H.ex.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := C.H.ex.2.2.2.1
  have hz := C.uniq hJ
  have hJD : J ∈ DSet Ω[R] W' := twin_mem_DSet hP h2g hW' htW' hJ.1 hz
  have hcyc : IsCyclic ↥(J ⊓ W') :=
    (Q3CL.Thompson.inf_W_of_mem_D hd.hyp hW' hJD hJ.1
      ⟨le_rfl, h2g _ hJ.1, fun _ hV' _ h => le_antisymm hV' h⟩).2.2.1
  have hbb : b * b = t := Asc77.sq_eq_of_orderOf_four hz hb.1 ob
  rcases Asc77.eq_or_eq_inv_of_orderOf_four_of_cyclic hcyc hb hc ob oc with h | h
  · rw [h]
  · have : c' = b * t := by
      rw [h]
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, hbb, hz.sq]
    have hbI : b ∈ C.I := C.twin_le_I hJ hb.1
    rw [this, C.P.rho_mul hbI C.t_mem_I, C.P.rho_eq_one_of_mem_D C.t_mem_D, mul_one]

include C in
theorem step4 {c : Y} (hc : c * t * c⁻¹ = t) (hx : c * (y * t * y⁻¹) * c⁻¹ ∉ C.D) :
    ∃ (a : Finset (Fin 8)) (ha : a.card = 4), C.P.ph t = vq a ∧
      c * (y * t * y⁻¹) * c⁻¹ ∈ C.I ∧ (∀ z, C.P.rho (c * (y * t * y⁻¹) * c⁻¹) z ≠ z) ∧
      (∀ z, C.P.rho (c * (y * t * y⁻¹) * c⁻¹) z ∈ a ↔ z ∈ a) := by
  have hStd := C.H.ex.1
  have hd := hStd.datum
  have hinv := conjInvariant_conjClass (tightCore R)
  obtain ⟨hKK', hKK₃, hKK₄, hK'K₃, hK'K₄, hK₃K₄⟩ := C.twins_ne
  set τ := y * t * y⁻¹ with hτdef
  set x := c * τ * c⁻¹ with hxdef
  have htt : t * t = 1 := hd.hz.sq
  obtain ⟨-, hτP⟩ := A6Hx.t_tau_mem_ae6P C.H C.fr
  have hxP : x ∈ ae6P Ω[R] t := A6Hx.conj_mem_ae6P hinv hc hτP
  have hxI : x ∈ C.I := C.P_le_I hxP
  have hxne : x ≠ t := fun e => hx (by rw [e]; exact C.t_mem_D)
  obtain ⟨hW', htW'⟩ := C.conj_W_mem hc
  set W' := conjSub c W with hW'def
  have hτW : τ ∈ W := by
    rw [hτdef, C.fr.hy]
    exact W.mul_mem (W.mul_mem (W.mul_mem C.fr.h₁.2 C.fr.h₂.2) C.fr.h₃.2) C.fr.h₄.2
  have hxW' : x ∈ W' := conj_mem_conjSub hτW
  obtain ⟨b₁, b₂, b₃, b₄, y', fr', hyc', -⟩ := C.frame_at hW' htW'
  have hxcases := C.mem_tG_W' hW' htW' fr' hxW' (g := c * y)
    (by rw [hxdef, hτdef]; group)
  have key : y' * t * y'⁻¹ ∈ C.D → False := by
    intro h
    rcases hxcases with h1 | h1 | h1
    · exact hxne h1
    · exact hx (by rw [h1]; exact h)
    · exact hx (by rw [h1]; exact C.D.mul_mem C.t_mem_D h)
  obtain ⟨a, ha, β₁, β₂, β₃, β₄, hta, hl₁, hl₂, hl₃, hl₄⟩ := C.sides
  have hac := card_compl_four ha
  have hKI := C.K_le_I
  have hK'I := C.twin_le_I C.hK't
  have hK₃I := C.twin_le_I C.hK₃t
  have hK₄I := C.twin_le_I C.hK₄t
  have hb₁I : b₁ ∈ C.I := hKI fr'.h₁.1
  have hb₂I : b₂ ∈ C.I := hK'I fr'.h₂.1
  have hb₃I : b₃ ∈ C.I := hK₃I fr'.h₃.1
  have hb₄I : b₄ ∈ C.I := hK₄I fr'.h₄.1
  have hb₁sq : b₁ * b₁ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hKt) fr'.h₁.1 fr'.o₁
  have hb₂sq : b₂ * b₂ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hK't) fr'.h₂.1 fr'.o₂
  have hb₃sq : b₃ * b₃ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hK₃t) fr'.h₃.1 fr'.o₃
  have hb₄sq : b₄ * b₄ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hK₄t) fr'.h₄.1 fr'.o₄
  have huI : u₁ * u₂ ∈ C.I := C.I.mul_mem (hKI hd.hu₁.1) (hK'I hd.hu₂.1)
  obtain ⟨hune1, hunet⟩ := C.kk_ne C.hKt C.hK't hKK' hd.hu₁.1 hd.hu₂.1 hd.sq₁ hd.sq₂
  have hphu : C.P.ph (u₁ * u₂) ≠ vq a := fun e =>
    hunet (C.P.ph_inj huI C.t_mem_I (by rw [e, hta]))
  obtain ⟨S_u, -, hSu2, hSu⟩ := C.P.w2 hKI hK'I hl₁ hl₂ hd.hu₁.1 hd.hu₂.1 C.u_mem_D hune1 hphu
  have hσ : C.P.rho b₁ * C.P.rho b₂ ≠ 1 := by
    intro h1
    have hw'I : b₁ * b₂ ∈ C.I := C.I.mul_mem hb₁I hb₂I
    have hw'D : b₁ * b₂ ∈ C.D :=
      (C.P.mem_D_iff hw'I).2 (by rw [C.P.rho_mul hb₁I hb₂I]; exact h1)
    obtain ⟨hne1, hnet⟩ := C.kk_ne C.hKt C.hK't hKK' fr'.h₁.1 fr'.h₂.1 hb₁sq hb₂sq
    have hphne : C.P.ph (b₁ * b₂) ≠ vq a := fun e =>
      hnet (C.P.ph_inj hw'I C.t_mem_I (by rw [e, hta]))
    obtain ⟨S, -, hS2, hS⟩ := C.P.w2 hKI hK'I hl₁ hl₂ fr'.h₁.1 fr'.h₂.1 hw'D hne1 hphne
    obtain ⟨i, hi, hiu⟩ := C.P.exists_conj_two huI hw'I hSu2 hS2 hSu hS
    have hK₃C : K₃ ≤ Subgroup.centralizer ({i * (u₁ * u₂) * i⁻¹} : Set Y) := by
      rw [hiu]
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 := C.twin_comm C.hK₃t C.hKt hKK₃.symm g hg b₁ fr'.h₁.1
      have e2 := C.twin_comm C.hK₃t C.hK't hK'K₃.symm g hg b₂ fr'.h₂.1
      calc g * (b₁ * b₂) = (g * b₁) * b₂ := by group
        _ = (b₁ * g) * b₂ := by rw [e1]
        _ = b₁ * (g * b₂) := by group
        _ = b₁ * (b₂ * g) := by rw [e2]
        _ = (b₁ * b₂) * g := by group
    have hy'C : y' ∈ Subgroup.centralizer ({i * (u₁ * u₂) * i⁻¹} : Set Y) := by
      rw [hiu]
      exact hyc'
    exact key (C.fuse_mem_D hi C.hK₃t hK₃C hy'C)
  have hσ' : C.P.rho b₃ * C.P.rho b₄ ≠ 1 := by
    intro h1
    obtain ⟨c₁, c₂, y'', hc₁, oc₁, hc₂, oc₂, hy''C, hy''W, hy''ne⟩ := C.rot_frame hW' htW'
    have hρ₁ : C.P.rho c₁ = C.P.rho b₃ := C.rho_gen hW' htW' C.hK₃t fr'.h₃ hc₁ fr'.o₃ oc₁
    have hρ₂ : C.P.rho c₂ = C.P.rho b₄ := C.rho_gen hW' htW' C.hK₄t fr'.h₄ hc₂ fr'.o₄ oc₂
    have hc₁I : c₁ ∈ C.I := hK₃I hc₁.1
    have hc₂I : c₂ ∈ C.I := hK₄I hc₂.1
    have hw''I : c₁ * c₂ ∈ C.I := C.I.mul_mem hc₁I hc₂I
    have hw''D : c₁ * c₂ ∈ C.D :=
      (C.P.mem_D_iff hw''I).2 (by rw [C.P.rho_mul hc₁I hc₂I, hρ₁, hρ₂]; exact h1)
    have hc₁sq : c₁ * c₁ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hK₃t) hc₁.1 oc₁
    have hc₂sq : c₂ * c₂ = t := Asc77.sq_eq_of_orderOf_four (C.uniq C.hK₄t) hc₂.1 oc₂
    obtain ⟨hne1, hnet⟩ := C.kk_ne C.hK₃t C.hK₄t hK₃K₄ hc₁.1 hc₂.1 hc₁sq hc₂sq
    have hphne : C.P.ph (c₁ * c₂) ≠ vq aᶜ := fun e =>
      hnet (C.P.ph_inj hw''I C.t_mem_I (by rw [e, vq_compl, hta]))
    obtain ⟨S, -, hS2, hS⟩ := C.P.w2 hK₃I hK₄I hl₃ hl₄ hc₁.1 hc₂.1 hw''D hne1 hphne
    obtain ⟨i, hi, hiu⟩ := C.P.exists_conj_two huI hw''I hSu2 hS2 hSu hS
    have hKC : K ≤ Subgroup.centralizer ({i * (u₁ * u₂) * i⁻¹} : Set Y) := by
      rw [hiu]
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 := C.twin_comm C.hKt C.hK₃t hKK₃ g hg c₁ hc₁.1
      have e2 := C.twin_comm C.hKt C.hK₄t hKK₄ g hg c₂ hc₂.1
      calc g * (c₁ * c₂) = (g * c₁) * c₂ := by group
        _ = (c₁ * g) * c₂ := by rw [e1]
        _ = c₁ * (g * c₂) := by group
        _ = c₁ * (c₂ * g) := by rw [e2]
        _ = (c₁ * c₂) * g := by group
    have hy''C' : y'' ∈ Subgroup.centralizer ({i * (u₁ * u₂) * i⁻¹} : Set Y) := by
      rw [hiu]
      exact hy''C
    have hD'' := C.fuse_mem_D hi C.hKt hKC hy''C'
    rcases C.mem_tG_W' hW' htW' fr' hy''W (g := y'') rfl with h | h | h
    · exact hy''ne h
    · exact key (by rw [← h]; exact hD'')
    · apply key
      have h2 : t * (y' * t * y'⁻¹) ∈ C.D := by rw [← h]; exact hD''
      have h3 := C.D.mul_mem (C.D.inv_mem C.t_mem_D) h2
      simpa using h3
  have hτ'I : y' * t * y'⁻¹ ∈ C.I := by
    rw [fr'.hy]
    exact C.I.mul_mem (C.I.mul_mem (C.I.mul_mem hb₁I hb₂I) hb₃I) hb₄I
  have hρτ' : C.P.rho (y' * t * y'⁻¹) =
      (C.P.rho b₁ * C.P.rho b₂) * (C.P.rho b₃ * C.P.rho b₄) := by
    rw [fr'.hy, C.P.rho_mul (C.I.mul_mem (C.I.mul_mem hb₁I hb₂I) hb₃I) hb₄I,
      C.P.rho_mul (C.I.mul_mem hb₁I hb₂I) hb₃I, C.P.rho_mul hb₁I hb₂I]
    group
  have hρx : C.P.rho x = (C.P.rho b₁ * C.P.rho b₂) * (C.P.rho b₃ * C.P.rho b₄) := by
    rcases hxcases with h1 | h1 | h1
    · exact absurd h1 hxne
    · rw [h1, hρτ']
    · rw [h1, C.P.rho_mul C.t_mem_I hτ'I, C.P.rho_eq_one_of_mem_D C.t_mem_D, one_mul, hρτ']
  have hσV : C.P.rho b₁ * C.P.rho b₂ ∈ V4set a ha :=
    V4set_mul (permQ_mem_V4set ((hl₁ b₁ hb₁I).1 fr'.h₁.1))
      (permQ_mem_V4set ((hl₂ b₂ hb₂I).1 fr'.h₂.1))
  have hσ'V : C.P.rho b₃ * C.P.rho b₄ ∈ V4set aᶜ hac :=
    V4set_mul (permQ_mem_V4set ((hl₃ b₃ hb₃I).1 fr'.h₃.1))
      (permQ_mem_V4set ((hl₄ b₄ hb₄I).1 fr'.h₄.1))
  obtain ⟨hfix, hpres⟩ := fpf_of_V4 hσV hσ'V hσ hσ'
  exact ⟨a, ha, hta, hxI, by rw [hρx]; exact hfix, by rw [hρx]; exact hpres⟩

end A6eCtx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
