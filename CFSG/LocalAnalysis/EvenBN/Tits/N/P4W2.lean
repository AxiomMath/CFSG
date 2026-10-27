module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4W1

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section W2

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


@[expose] noncomputable def W1s (hz : d.S56Z0 z₀) : Subgroup (MulAut ↥d.s56V) :=
  (MulAction.stabilizer ↥(W0s d) (z0V hz)).map (W0s d).subtype

theorem mem_W1s_iff (hz : d.S56Z0 z₀) {w : MulAut ↥d.s56V} :
    w ∈ W1s hz ↔ w ∈ W0s d ∧ w (z0V hz) = z0V hz := by
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact ⟨w'.2, hw'⟩
  · rintro ⟨hw, hwz⟩
    exact ⟨⟨w, hw⟩, hwz, rfl⟩

theorem W1s_le_W0s (hz : d.S56Z0 z₀) : W1s hz ≤ W0s d := fun _ hw => ((mem_W1s_iff hz).1 hw).1

theorem star_t_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    star d d.t (z0V hz) = zV h49 hd * z0V hz := by
  apply Subtype.ext
  show ((star d d.t (z0V hz) : ↥d.s56V) : G) = d.z * z₀
  rw [star_eq, actFun_apply_coe d.s56V (t_mem_Hg h49 hd)]
  exact t_conj_z0 hd hz

theorem Ks_z0_cases (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) (h18 : Node18 d) {k : MulAut ↥d.s56V} (hk : k ∈ Ks d) :
    k (z0V hz) = z0V hz ∨ k (z0V hz) = zV h49 hd * z0V hz := by
  have hzz : d.z * d.z = 1 := hd.s56_z_sq
  have hz₀z₀ : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
  have hzz₀ : d.z * z₀ = z₀ * d.z := (hz.cen hd.s56_z_mem_E).symm
  have hmem : ((k (z0V hz) : ↥d.s56V) : G) ∈ Zz d z₀ :=
    Ks_Zzs_forward h49 hd hz h10 h17 h18 hk (z0V hz) (mem_sup_right (mem_zpowers z₀))
  have hkz : k (zV h49 hd) = zV h49 hd := Ks_fixes_z h49 hd hz h10 h17 hk
  rcases (CFSG.LocalAnalysis.EvenBN.Tits.N.mem_sup_zpowers_iff hzz hz₀z₀ hzz₀ _).1 hmem with
    h | h | h | h
  · exfalso
    have h1 : k (z0V hz) = 1 := Subtype.ext h
    have h2 : z0V hz = 1 := by
      have := congrArg (fun y => k⁻¹ y) h1
      simpa using this
    exact z0_ne_one' h49 hd hz (congrArg Subtype.val h2)
  · exfalso
    have h1 : k (z0V hz) = zV h49 hd := Subtype.ext h
    have h2 : z0V hz = zV h49 hd := by
      apply k.injective
      rw [h1, hkz]
    have h3 : z₀ = d.z := congrArg Subtype.val h2
    exact z0_not_mem_E h49 hd hz (by rw [h3]; exact hd.s56_z_mem_E)
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem card_W1s (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) :
    Nat.card ↥(W1s hz) = 256 := by
  obtain ⟨hKcard, hWK, hWst, hW2, hU0W, hWcard, hWcomm, hWsq, hWreg, hWtr⟩ :=
    node19_W0 h49 hd hz h09 h10 h17s h17 h18
  have hmap : Nat.card ↥(W1s hz) = Nat.card ↥(MulAction.stabilizer ↥(W0s d) (z0V hz)) :=
    Subgroup.card_map_of_injective (W0s d).subtype_injective
  have horb : MulAction.orbit ↥(W0s d) (z0V hz) = {z0V hz, zV h49 hd * z0V hz} := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      rcases Ks_z0_cases h49 hd hz h10 h17 h18 (hWK w.2) with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨1, one_smul _ _⟩
      · exact ⟨⟨star d d.t, hU0W (mem_sup_right (mem_zpowers _))⟩, star_t_z0 h49 hd hz⟩
  have hne : z0V hz ≠ zV h49 hd * z0V hz := by
    intro h
    have : zV h49 hd = 1 := by
      have h' := congrArg (fun y => y * (z0V hz)⁻¹) h
      simpa using h'.symm
    exact hd.s56_z_ne_one (congrArg Subtype.val this)
  have hidx : (MulAction.stabilizer ↥(W0s d) (z0V hz)).index = 2 := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_pair hne]
  have h := Subgroup.card_mul_index (MulAction.stabilizer ↥(W0s d) (z0V hz))
  rw [hidx] at h
  rw [hmap]
  omega

end W2

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
