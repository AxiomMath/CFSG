module

public import CFSG.CGT.Foote82.T66.MC1Steps
public import CFSG.CGT.Foote82.T66.CitedBA
import CFSG.CGT.Foote82.T66.BranchAGen
import CFSG.CGT.Foote82.T66.BranchARecog
import CFSG.CGT.Foote82.T66.SymModule
import CFSG.CGT.Foote82.Lemma61

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

theorem lemma52 : Lemma52 := by
  intro V _ _ _ G L z h hrank hA
  exact ⟨h, hrank, hA, BranchAAux.oddTransp h hrank hA, BranchAAux.eq_classClosure h,
    BranchAAux.commutator_eq_layerIn h⟩

private theorem false_of_altNatural {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {G L : Subgroup (GLV V)} {z : GLV V} (hc : OddTranspConf G L z) {n : ℕ} (hn : 7 ≤ n)
    (hL : IsAltNaturalModule L n) : False := by
  have h := hc.std
  obtain ⟨α, hαs, β, hβs, hβk, hR⟩ := hL
  have hαi := BranchAAux.injective_of_altNatural h.extremal.faithful α β hβk hR
  let ε : ↥L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective α ⟨hαi, hαs⟩
  obtain ⟨φ, hφz, hφL⟩ := BranchAAux.exists_perm_equiv hc hn ε
  obtain ⟨c, hc3, hc0, hc1, hcβ⟩ :=
    BranchAAux.exists_threeCycle hc hn φ hφL α hαi β hβs hβk hR
  have hzsymm : φ.symm (Equiv.swap 0 1) = ⟨z, BranchAAux.z_mem_G h⟩ := by
    rw [← hφz, MulEquiv.symm_apply_apply]
  have hα' : ∀ g : ↥G, φ g ∈ altOn {k | k ≠ 0 ∧ k ≠ 1} →
      ∀ w ∈ commSpace (Subgroup.zpowers ((φ.symm (Equiv.swap 0 1) : ↥G) : GLV V)) ⊤,
        (g : GLV V) w = w := by
    intro g hg w hw
    rw [hzsymm] at hw
    rw [← hφL, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hg
    exact (h.extremal.setup.toSetup6.lemma61 (Subgroup.mem_zpowers z)).1 g
      (Subgroup.mem_subgroupOf.1 hg) w hw
  have hheart := (isAltHeartFor_of_perm (N := n + 2) (by omega) φ h.extremal.setup.irr
    (i := 0) (j := 1) (by simp [Fin.ext_iff]) hα' hc3 hc0 hc1 hcβ).1
  rw [BranchAAux.layerIn_eq_comap hc (by omega) φ] at hheart
  exact h.extremal.not_concl (Or.inr (Or.inl ⟨n, 1, by omega, le_rfl, ⟨ε⟩, by simpa using hheart⟩))

theorem branchAAlt (hG8 : G8) : BranchAAlt := by
  intro V _ _ _ G L z hc hF
  have h := hc.std
  rcases hF with ⟨n, hn, hL⟩ | ⟨⟨α, hαs⟩, h4⟩ | hL
  · exact false_of_altNatural hc hn hL
  ·
    have hαi := BranchAAux.injective_of_a7Four (BranchAAux.quasisimple_L h) h.extremal.faithful
      h.extremal.setup.irrTilde α hαs h4
    let ε : ↥L ≃* alternatingGroup (Fin 7) := MulEquiv.ofBijective α ⟨hαi, hαs⟩
    obtain ⟨φ, hφz, hφL⟩ := BranchAAux.exists_perm_equiv hc (le_refl 7) ε
    have hL : ((altOn {k : Fin 9 | k ≠ 0 ∧ k ≠ 1}).comap φ.toMonoidHom).map G.subtype = L := by
      rw [← hφL, Subgroup.comap_map_eq_self_of_injective φ.injective,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (BranchAAux.L_le_G h)]
    have hzsymm : φ.symm (Equiv.swap 0 1) = ⟨z, BranchAAux.z_mem_G h⟩ := by
      rw [← hφz, MulEquiv.symm_apply_apply]
    have hα' : ∀ g : ↥G, φ g ∈ altOn {k | k ≠ 0 ∧ k ≠ 1} →
        ∀ w ∈ commSpace (Subgroup.zpowers ((φ.symm (Equiv.swap 0 1) : ↥G) : GLV V)) ⊤,
          (g : GLV V) w = w := by
      intro g hg w hw
      rw [hzsymm] at hw
      rw [← hφL, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hg
      exact (h.extremal.setup.toSetup6.lemma61 (Subgroup.mem_zpowers z)).1 g
        (Subgroup.mem_subgroupOf.1 hg) w hw
    apply hG8 V G φ h.extremal.setup.irr hα' (hL ▸ h.extremal.setup.irrTilde)
    rw [hL]
    exact h4
  · exact false_of_altNatural hc (by norm_num) (BranchAAux.altNatural_of_omegaPlus hL)

theorem branchAFalse_of (h52 : Lemma52) (hAlt : BranchAAlt) (hSmall : BranchASmall) :
    BranchAFalse := by
  intro V _ _ _ G L z h hrank hA
  have hc := h52 V G L z h hrank hA
  rcases h.extremal.fmod with ⟨n, hn, hL⟩ | hL | hL | hL | hL | hL
  · rcases Nat.lt_or_ge n 7 with hn7 | hn7
    · obtain rfl : n = 6 := by omega
      exact hSmall V G L z hc (Or.inl hL)
    · exact hAlt V G L z hc (Or.inl ⟨n, hn7, hL⟩)
  · exact hAlt V G L z hc (Or.inr (Or.inl hL))
  · exact hAlt V G L z hc (Or.inr (Or.inr hL))
  · exact hSmall V G L z hc (Or.inr (Or.inl hL))
  · exact hSmall V G L z hc (Or.inr (Or.inr (Or.inl hL)))
  · exact hSmall V G L z hc (Or.inr (Or.inr (Or.inr hL)))

end CFSG.CGT.Foote82
