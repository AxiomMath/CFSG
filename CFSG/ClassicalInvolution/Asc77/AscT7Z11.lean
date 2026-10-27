module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z10
public import CFSG.ClassicalInvolution.Asc77.AscT7L1
public import CFSG.ClassicalInvolution.Asc77.AscT7Z1
public import CFSG.ClassicalInvolution.Asc77.AscT7Z5

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open scoped commutatorElement MatrixGroups

namespace T7Z

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}


theorem ySide5 [IsSimpleGroup G] (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hex : ExactMembers Ω)
    (hOY : classicalInvolutionOddCore ↥(exactLayer Ω u) = ⊥)
    (hY : LayerOrthType p f Ω u 5 true) {i : GaloisField p f} (hi : i * i = -1) :
    ∃ J₁ K₃ : Subgroup G, (J₁ = conjSub g K ∨ J₁ = conjSub g K') ∧
      (∃ V, SymplecticBlockPair (GaloisField p f) V J₁ K₃) ∧
      K₃ ≤ Subgroup.centralizer ({z} : Set G) ∧ K₃ ≤ Subgroup.centralizer ({u} : Set G) ∧
      K₃ ≤ ⁅K₃, K₃⁆ ∧ exactLayer Ω u ≤ J₁ ⊔ K₃ ∧ conjSub g K ≤ exactLayer Ω u ∧
      conjSub g K' ≤ exactLayer Ω u := by
  classical
  have hst := hs.stand
  have hp2 : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hcls := hst.hyp.classical
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R₂, R₂', a₂, b₂, v', hJt, hJ't, hR₂, hR₂', hcomm₂, ha₂, hb₂, haa, hbb, hv', hz⟩ :=
    T7L.exists_uFrame hs hd
  have hJΩ : conjSub g K ∈ Ω := hst.hyp.conjInvariant g K hKΩ
  have hJ'Ω : conjSub g K' ∈ Ω := hst.hyp.conjInvariant g K' hK'Ω
  have hJu : conjSub g K ≤ Subgroup.centralizer ({u} : Set G) :=
    ((tqMembers_eq_centMembers_of_exact (c := u) hex) ▸ hJt).2
  have hJ'u : conjSub g K' ≤ Subgroup.centralizer ({u} : Set G) :=
    ((tqMembers_eq_centMembers_of_exact (c := u) hex) ▸ hJ't).2
  have hJΦ : conjSub g K ∈ exactFamily Ω u := centMembers_subset_exactFamily hcls ⟨hJΩ, hJu⟩
  have hJ'Φ : conjSub g K' ∈ exactFamily Ω u := centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'u⟩
  have htJ : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have htJ' : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have ht2 := t_sq hd hs
  have hexeq : ∀ L ∈ Ω, Nonempty (↥L ≃* SL(2, GaloisField p f)) := by
    intro L hL
    obtain ⟨zL, hzL⟩ := hcls L hL
    exact hzL.nonempty_equiv_sl2 (hex L hL)
  have haJ : a₂ ∈ conjSub g K := exactCore_le_left u _ (hR₂.1 ha₂)
  have hbJ' : b₂ ∈ conjSub g K' := exactCore_le_left u _ (hR₂'.1 hb₂)
  have hab : a₂ * b₂ = b₂ * a₂ := hcomm₂ a₂ ha₂ b₂ hb₂
  obtain ⟨t', n', ht', D, hcard, i', hit, hir⟩ := T7Z.exists_omegaLie_of_layerOrth hOY hY
  have htn : t' = .PSp ∧ n' = 2 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i' = f := by
    rcases D.exp_eq i' with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  obtain ⟨P⟩ := nonempty_modelLayer_of_omegaLie D hcard i' (hit.trans htn.1) (hir.trans htn.2) hie
  obtain ⟨a', ha', ha'a, hva⟩ : ∃ a' ∈ conjSub g K, a' * a' = u * e ∧ v' = a' * b₂ := by
    rcases hv' with h | h
    · exact ⟨a₂, haJ, haa, h⟩
    · refine ⟨a₂⁻¹, (conjSub g K).inv_mem haJ, ?_, ?_⟩
      · have : a₂⁻¹ * a₂⁻¹ = (a₂ * a₂)⁻¹ := by group
        rw [this, haa]
        exact inv_eq_of_mul_eq_one_right ht2
      · rw [h]
        have h4 : a₂ * a₂ * (a₂ * a₂) = 1 := by rw [haa]; exact ht2
        calc a₂ * b₂ * (u * e) = a₂ * b₂ * (a₂ * a₂) := by rw [haa]
          _ = a₂ * a₂ * a₂ * b₂ := by
            calc a₂ * b₂ * (a₂ * a₂) = a₂ * (b₂ * a₂) * a₂ := by group
              _ = a₂ * (a₂ * b₂) * a₂ := by rw [hab]
              _ = a₂ * a₂ * (b₂ * a₂) := by group
              _ = a₂ * a₂ * (a₂ * b₂) := by rw [hab]
              _ = a₂ * a₂ * a₂ * b₂ := by group
          _ = a₂⁻¹ * (a₂ * a₂ * (a₂ * a₂)) * b₂ := by group
          _ = a₂⁻¹ * b₂ := by rw [h4]; group
  have hJJ' : conjSub g K ≠ conjSub g K' := fun h => hs.hne ((conjSub_inj g).mp h).symm
  obtain ⟨J₁, K₃, hJ₁, hpair, hcent, hperf, hgen, hK₃le⟩ := ySide_model hp2 hq hi P hJΦ hJ'Φ
    (hexeq _ hJΩ) (hexeq _ hJ'Ω) hJJ' ((twin_commutes hs hex).conjSub g) htJ htJ' ha' hbJ' ha'a
    hbb
  have hK₃u : K₃ ≤ Subgroup.centralizer ({u} : Set G) := by
    refine hK₃le.trans ?_
    rw [← exactLayer_eq_omegaGen]
    exact exactLayer_le_centralizer Ω u
  have hK₃v : K₃ ≤ Subgroup.centralizer ({v'} : Set G) := hva ▸ hcent
  have hK₃z : K₃ ≤ Subgroup.centralizer ({z} : Set G) := by
    rcases hz with h | h
    · rw [h]
      exact hK₃v
    · intro x hx
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hK₃u hx)
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hK₃v hx)
      rw [Subgroup.mem_centralizer_singleton_iff, h]
      calc x * (u * v') = (x * u) * v' := by group
        _ = (u * x) * v' := by rw [h1]
        _ = u * (x * v') := by group
        _ = u * (v' * x) := by rw [h2]
        _ = (u * v') * x := by group
  refine ⟨J₁, K₃, hJ₁, hpair, hK₃z, hK₃u, hperf, ?_, ?_, ?_⟩
  · rw [exactLayer_eq_omegaGen]
    exact hgen
  · rw [exactLayer_eq_omegaGen]
    exact le_omegaGen hJΦ
  · rw [exactLayer_eq_omegaGen]
    exact le_omegaGen hJ'Φ

end T7Z

end CFSG.ClassicalInvolution.Asc77
