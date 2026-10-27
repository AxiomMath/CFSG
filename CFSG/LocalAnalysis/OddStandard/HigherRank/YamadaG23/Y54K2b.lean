module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y54_phi_mt (s : Setting3 G L) (m : G) :
    f3phi s (m * s.t) = f3phi s m := by
  unfold f3phi
  group

private theorem y54_K_inf_P (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    centIn (M2 c.s) c.s.fr.F ⊓ f3P c.s = c.s.fr.F := by
  apply le_antisymm
  · intro k hk
    rw [Subgroup.mem_inf] at hk
    obtain ⟨hkK, hkP⟩ := hk
    have hkM2 : k ∈ M2 c.s := hkK.1
    rcases f3_mem_P k hkP with hkB | ⟨b, hbB, hkbt⟩
    · have hmem : k ∈ centIn (M2 c.s) c.s.fr.F ⊓ c.s.fr.B := ⟨hkK, hkB⟩
      rwa [y54_K_inf_B hH] at hmem
    · exfalso
      have hbM2 : b ∈ M2 c.s := y54_B_le_M2 c.s hbB
      have h1 : b⁻¹ * k ∈ M2 c.s := Subgroup.mul_mem _ (Subgroup.inv_mem _ hbM2) hkM2
      have h2 : b⁻¹ * k = c.s.t := by rw [hkbt]; group
      exact y54_t_notin_M2 c hH (h2 ▸ h1)
  · intro f hf
    exact ⟨y54_F_le_K hH hf, Subgroup.mem_sup_left (y54_F_le_B hH hf)⟩

theorem y54_K_phi_mem (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ k ∈ centIn (M2 c.s) c.s.fr.F, f3phi c.s k ∈ cen c.s.fr.B := by
  intro k hk
  exact f3_phi_mem hH k (f3_C₂_le_Y hH (y54_M2_le_C2 c hH hk.1))

theorem y54_K_phi_onto (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ v ∈ cen c.s.fr.B, ∃ k ∈ centIn (M2 c.s) c.s.fr.F, f3phi c.s k = v := by
  obtain ⟨f, hfval, hfsurj, hfker⟩ := f3_phiHom hH
  intro v hv
  obtain ⟨x, hx⟩ := hfsurj ⟨v, hv⟩
  have hxφ : f3phi c.s (x : G) = v := by
    rw [← hfval x]; exact congrArg Subtype.val hx
  have hmain : ∃ m ∈ M2 c.s, f3phi c.s m = v := by
    rcases y54_C2_cases c hH (x : G) x.2 with hxM2 | ⟨m, hmM2, hmx⟩
    · exact ⟨x, hxM2, hxφ⟩
    · refine ⟨m, hmM2, ?_⟩
      calc f3phi c.s m = f3phi c.s (m * c.s.t) := (y54_phi_mt c.s m).symm
        _ = f3phi c.s (x : G) := by rw [hmx]
        _ = v := hxφ
  obtain ⟨m, hmM2, hmφ⟩ := hmain
  obtain ⟨b, hbB, hbK⟩ := y54_B_cover c hH m hmM2
  have hbY : b ∈ f3Y c.s :=
    f3_C₂_le_Y hH (y54_M2_le_C2 c hH (y54_B_le_M2 c.s hbB))
  have hbX0 : b ∈ f3X0 c.s := f3_P_le_X0 c.s (Subgroup.mem_sup_left hbB)
  have hbYinv : b⁻¹ ∈ f3Y c.s := Subgroup.inv_mem _ hbY
  have hmY : m ∈ f3Y c.s := f3_C₂_le_Y hH (y54_M2_le_C2 c hH hmM2)
  have hbinv1 : f3phi c.s b⁻¹ = 1 :=
    (f3_phi_eq_one hH b⁻¹ hbYinv).2 (Subgroup.inv_mem _ hbX0)
  refine ⟨b⁻¹ * m, hbK, ?_⟩
  calc f3phi c.s (b⁻¹ * m) = f3phi c.s b⁻¹ * f3phi c.s m := f3_phi_mul hH b⁻¹ hbYinv m hmY
    _ = 1 * v := by rw [hbinv1, hmφ]
    _ = v := one_mul v

theorem y54_K_inf_X0 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    centIn (M2 c.s) c.s.fr.F ⊓ f4X0 c.s = c.s.fr.F := by
  apply le_antisymm
  · intro k hk
    rw [Subgroup.mem_inf] at hk
    obtain ⟨hkK, hkX0⟩ := hk
    have hkH : k ∈ c.s.H := hkX0.1
    have hkcentV : k ∈ centralizer (cen c.s.fr.B : Set G) :=
      Subgroup.mem_centralizer_iff.mpr
        (fun v hv => hkX0.2 v (y54_V_le_F hH hv))
    have hkC2 : k ∈ c.s.C₂ := y54_M2_le_C2 c hH hkK.1
    have hkP : k ∈ f3P c.s := by
      have hmem : k ∈ c.s.C₂ ⊓ f3X0 c.s := ⟨hkC2, ⟨hkH, hkcentV⟩⟩
      rwa [f3_C₂_inf_X0 hH] at hmem
    have hmem : k ∈ centIn (M2 c.s) c.s.fr.F ⊓ f3P c.s := ⟨hkK, hkP⟩
    rwa [y54_K_inf_P c hH] at hmem
  · intro f hf
    refine ⟨y54_F_le_K hH hf, ?_⟩
    refine ⟨f3_P_le_H c.s (Subgroup.mem_sup_left (y54_F_le_B hH hf)), ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun f' hf' => (y54_F_comm hH f hf f' hf').symm)

theorem y54_K_relIndex (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.s.fr.F.relIndex (centIn (M2 c.s) c.s.fr.F) = 4 := by
  obtain ⟨f, hfval, hfsurj, hfker⟩ := f3_phiHom hH
  let K : Subgroup G := centIn (M2 c.s) c.s.fr.F
  have hKle : K ≤ c.s.C₂ := fun k hk => y54_M2_le_C2 c hH hk.1
  let ψ : ↥K →* ↥(cen c.s.fr.B) := f.comp (Subgroup.inclusion hKle)
  have hψapply : ∀ k : ↥K, ψ k = f ⟨(k : G), hKle k.2⟩ := fun k => rfl
  have hψ : ∀ k : ↥K, ((ψ k : ↥(cen c.s.fr.B)) : G) = f3phi c.s (k : G) := by
    intro k; rw [hψapply k]; exact hfval ⟨(k : G), hKle k.2⟩
  have hsurj : Function.Surjective ψ := by
    intro v
    obtain ⟨k, hkK, hkφ⟩ := y54_K_phi_onto c hH (v : G) v.2
    refine ⟨⟨k, hkK⟩, ?_⟩
    apply Subtype.ext
    rw [hψ]
    exact hkφ
  have hker : (c.s.fr.F).subgroupOf K = ψ.ker := by
    ext k
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hkF
      rw [hψapply k]
      exact (hfker ⟨(k : G), hKle k.2⟩).2 (Subgroup.mem_sup_left (y54_F_le_B hH hkF))
    · intro hk1
      rw [hψapply k] at hk1
      have hP : (k : G) ∈ f3P c.s := (hfker ⟨(k : G), hKle k.2⟩).1 hk1
      have hmem : (k : G) ∈ centIn (M2 c.s) c.s.fr.F ⊓ f3P c.s := ⟨k.2, hP⟩
      rwa [y54_K_inf_P c hH] at hmem
  change (c.s.fr.F).relIndex K = 4
  calc (c.s.fr.F).relIndex K = ((c.s.fr.F).subgroupOf K).index := rfl
    _ = ψ.ker.index := by rw [hker]
    _ = Nat.card ψ.range := Subgroup.index_ker ψ
    _ = Nat.card (⊤ : Subgroup ↥(cen c.s.fr.B)) := by
        rw [MonoidHom.range_eq_top.mpr hsurj]
    _ = Nat.card ↥(cen c.s.fr.B) := Subgroup.card_top
    _ = 4 := by
        have h := (f3_V_isE2 hH).2
        norm_num at h
        exact h

end CFSG.OddStandard.HigherRank.YamadaG23
