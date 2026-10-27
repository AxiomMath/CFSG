module

public import CFSG.ClassicalInvolution.Asc77.AscB3C5
public import CFSG.ClassicalInvolution.Asc77.AscB3C3
public import CFSG.ClassicalInvolution.Asc77.AscSCH28

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace B3C

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}


theorem ySide5tw [IsSimpleGroup G] (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hex : ExactMembers Ω)
    (hOY : classicalInvolutionOddCore ↥(exactLayer Ω u) = ⊥)
    (hY : LayerOrthType p f Ω u 5 true) :
    ∃ J₁ K₃ : Subgroup G, (J₁ = conjSub g K ∨ J₁ = conjSub g K') ∧
      SymplecticPhanPair (GaloisField p f) (ModelFacts.two_ne_zero_galoisField f hs.stand.odd)
        (exactLayer Ω u) J₁ K₃ ∧
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
  have ht2 := T7Z.t_sq hd hs
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
  obtain ⟨P⟩ := T7Z.nonempty_modelLayer_of_omegaLie D hcard i' (hit.trans htn.1)
    (hir.trans htn.2) hie
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
  obtain ⟨J₁, K₃, hJ₁, hpair, hcent, hperf, hgen, hK₃le⟩ := ySide_model_tw hp2 hq P hJΦ hJ'Φ
    (hexeq _ hJΩ) (hexeq _ hJ'Ω) hJJ' ((T7Z.twin_commutes hs hex).conjSub g) htJ htJ' ha' hbJ'
    ha'a hbb
  have hK₃u : K₃ ≤ Subgroup.centralizer ({u} : Set G) := by
    refine hK₃le.trans ?_
    rw [← T7Z.exactLayer_eq_omegaGen]
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
  refine ⟨J₁, K₃, hJ₁, ?_, hK₃z, hK₃u, hperf, ?_, ?_, ?_⟩
  · rw [T7Z.exactLayer_eq_omegaGen]
    exact hpair
  · rw [T7Z.exactLayer_eq_omegaGen]
    exact hgen
  · rw [T7Z.exactLayer_eq_omegaGen]
    exact le_omegaGen hJΦ
  · rw [T7Z.exactLayer_eq_omegaGen]
    exact le_omegaGen hJ'Φ

theorem c23_phanChainB3_of_hodd (hodd : T7Z.OddCenterClassical) : C23_phanChainB3 p f := by
  intro hq3 G _ _ _ Ω K K' W z u e g hs hd hα hE hY
  classical
  have hst := hs.stand
  have hp2 : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hKΩ : K ∈ Ω := hst.mem
  have hpi : piSign p f = false := by simp [piSign, hq3]
  have hE0 : LayerOrthType p f Ω e 6 false := by simpa [hpi] using hE
  obtain ⟨hOE, hOY⟩ := T7Z.oddCore_layers_eq_bot hodd hs hd hα.1 hE (Or.inl hY)
  have hex : ExactMembers Ω := T7Z.exactMembers_of_layer hs hd hα.1 hd.he2 hOE hE
  obtain ⟨hpJ, hpJ', hEle⟩ := eSideU hs hd hα.1 hex hOE hE0
  obtain ⟨J₁, K₃, hJ₁, hpair, hK₃z, hK₃u, hK₃perf, hYle, hJle, hJ'le⟩ :=
    ySide5tw hs hd hex hOY hY
  have hcomm : Commutes K K₃ :=
    T7Z.commutes_of_perfect_centralizer hs hd hex hK₃z hK₃u hK₃perf
  have hpJ₁ : ∃ W', UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W' K J₁ := by
    rcases hJ₁ with rfl | rfl
    · exact hpJ
    · exact hpJ'
  refine ⟨![K, J₁, K₃], hKΩ, hcomm, hpJ₁, ⟨_, hpair⟩, ?_⟩
  have hsup : (⨆ k, (![K, J₁, K₃] : Fin 3 → Subgroup G) k) = K ⊔ J₁ ⊔ K₃ := by
    refine le_antisymm (iSup_le fun k => ?_) (sup_le (sup_le ?_ ?_) ?_)
    · fin_cases k
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact le_iSup (fun k => (![K, J₁, K₃] : Fin 3 → Subgroup G) k) 0
    · exact le_iSup (fun k => (![K, J₁, K₃] : Fin 3 → Subgroup G) k) 1
    · exact le_iSup (fun k => (![K, J₁, K₃] : Fin 3 → Subgroup G) k) 2
  have hYH : exactLayer Ω u ≤ K ⊔ J₁ ⊔ K₃ :=
    hYle.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hEH : exactLayer Ω e ≤ K ⊔ J₁ ⊔ K₃ :=
    hEle.trans (sup_le (sup_le (hJ'le.trans hYH) (le_sup_left.trans le_sup_left))
      (hJle.trans hYH))
  rw [hsup]
  refine eq_top_iff.mpr ?_
  rw [← hα.2, rLayer_eq_exactLayer hp2 hq hst.hyp hd.he2,
    rLayer_eq_exactLayer hp2 hq hst.hyp hd.hu2]
  exact sup_le hEH hYH

theorem c23_phanChainB3_proved : C23_phanChainB3 p f :=
  c23_phanChainB3_of_hodd SCH.oddCenterClassical

theorem c23_recogB3_of_phanB3 (hP : PhanB3Recognition p f) : R31.C23_recogB3 p f :=
  c23_recogB3_of_phan hP c23_phanChainB3_proved

end B3C

end CFSG.ClassicalInvolution.Asc77
