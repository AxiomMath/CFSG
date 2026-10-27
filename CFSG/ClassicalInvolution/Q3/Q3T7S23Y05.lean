module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y02
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y04
public import CFSG.ClassicalInvolution.Q3.Q3T7S23A03

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.B3C (SymplecticPhanPair)
open scoped commutatorElement MatrixGroups

noncomputable def slEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S] (r : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) where
  toFun := Matrix.SpecialLinearGroup.map (r : R →+* S)
  invFun := Matrix.SpecialLinearGroup.map (r.symm : S →+* R)
  left_inv x := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv x := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' x y := map_mul _ x y

theorem nonempty_ringEquiv_gf3 : Nonempty (ZMod 3 ≃+* GaloisField 3 1) := by
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite (GaloisField 3 1)
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [ZMod.card, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 one_ne_zero]
  norm_num

theorem nonempty_equiv_galoisField3 {X : Type} [Group X] (h : Nonempty (X ≃* SL(2, ZMod 3))) :
    Nonempty (X ≃* SL(2, GaloisField 3 1)) := by
  obtain ⟨e⟩ := h
  obtain ⟨r⟩ := nonempty_ringEquiv_gf3
  exact ⟨e.trans (slEquivOfRingEquiv r)⟩


section YSide

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem ySide5tw3 [IsSimpleGroup G] (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g) (hex : ExactMembers Ω)
    (hOY : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥)
    (hY : Q3T8.Asc77.LayerOrthType Ω u 5 true) :
    ∃ J₁ J₂ K₃ : Subgroup G,
      ((J₁ = conjSub g K ∧ J₂ = conjSub g K') ∨ (J₁ = conjSub g K' ∧ J₂ = conjSub g K)) ∧
      SymplecticPhanPair (GaloisField 3 1)
        (ModelFacts.two_ne_zero_galoisField 1 (by norm_num))
        (Q3T8.Asc77.ExactLayer.exactLayer Ω u) J₁ K₃ ∧
      K₃ ≤ Subgroup.centralizer ({z} : Set G) ∧ K₃ ≤ Subgroup.centralizer ({u} : Set G) ∧
      Q3W.Pow3 K₃ ∧ Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ J₁ ⊔ K₃ ∧
      conjSub g K ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω u ∧
      conjSub g K' ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω u ∧
      ∃ w ∈ K₃, conjSub w J₁ = J₂ := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hcls : ∀ M ∈ Ω, ∃ z', Q3T8.Generic.IsClassicalMember M z' := hΩ.classical
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R₂, R₂', a₂, b₂, v', hJt, hJ't, hR₂, hR₂', hcomm₂, ha₂, hb₂, haa, hbb, hv', hz⟩ :=
    Q3T8.Asc77.T7L.exists_uFrame hs hd
  have hJΩ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hKΩ
  have hJ'Ω : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hJu : conjSub g K ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJt).2
  have hJ'u : conjSub g K' ≤ Subgroup.centralizer ({u} : Set G) :=
    ((Q3NL.tqMembers3_eq_centralizingMembers_of_exact (c := u) hex).subset hJ't).2
  have hJΦ : conjSub g K ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJΩ, hJu⟩
  have hJ'Φ : conjSub g K' ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'u⟩
  have htJ : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have htJ' : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have ht2 : (u * e) * (u * e) = 1 := by
    rw [← hd.hgt]
    exact (hs.hz.conj g).sq
  have hexeq : ∀ L ∈ Ω, Nonempty (↥L ≃* SL(2, GaloisField 3 1)) := by
    intro L hL
    obtain ⟨zL, hzL⟩ := hcls L hL
    exact nonempty_equiv_galoisField3 ((hzL.toQ3 (by norm_num)).nonempty_equiv_sl2 (hex L hL))
  have haJ : a₂ ∈ conjSub g K := Q3T8.Asc77.ExactLayer.exactCore_le_left u _ (hR₂.1 ha₂)
  have hbJ' : b₂ ∈ conjSub g K' := Q3T8.Asc77.ExactLayer.exactCore_le_left u _ (hR₂'.1 hb₂)
  have hab : a₂ * b₂ = b₂ * a₂ := hcomm₂ a₂ ha₂ b₂ hb₂
  obtain ⟨t', n', ht', D, hcard, i', hit, hir⟩ :=
    Q3T8.Asc77.T7Z.exists_omegaLie_of_layerOrth hOY hY
  have htn : t' = .PSp ∧ n' = 2 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i' = 1 := by
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
  have hJJ' : conjSub g K ≠ conjSub g K' := fun h => hs.hne (conjSub_injective g h).symm
  obtain ⟨J₁, J₂, K₃, hJ₁, hpair, hcent, hpow, hgen, hK₃le, w, hwK₃, hw⟩ :=
    ySide_model_tw3 P hJΦ hJ'Φ (hexeq _ hJΩ) (hexeq _ hJ'Ω) hJJ'
      ((twins_commute_of_exact hs hex).conjSub g) htJ htJ' ha' hbJ' ha'a hbb
  have hK₃u : K₃ ≤ Subgroup.centralizer ({u} : Set G) := by
    refine hK₃le.trans ?_
    rw [← Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen]
    exact Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u
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
  refine ⟨J₁, J₂, K₃, hJ₁, ?_, hK₃z, hK₃u, hpow, ?_, ?_, ?_, ⟨w, hwK₃, hw⟩⟩
  · rw [Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen]
    exact hpair
  · rw [Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen]
    exact hgen
  · rw [Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen]
    exact le_omegaGen hJΦ
  · rw [Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen]
    exact le_omegaGen hJ'Φ

end YSide

end CFSG.ClassicalInvolution.Q3.Q3T7S23
