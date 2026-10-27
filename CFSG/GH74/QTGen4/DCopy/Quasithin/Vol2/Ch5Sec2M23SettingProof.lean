module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23SettingProof
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Setting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def Stmt5_2_11_four_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (K' : Subgroup G),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T → oTwoUpper H < K' →
    quasithinIsMaximalLocal T K' → CFSG.Quasithin.IsExcA7Block K' → InM T K'

theorem stmt5_2_10_setting_of_F4 (h528 : Stmt5_2_8_F4) (h5211 : Stmt5_2_11_four_F4) :
    Stmt5_2_10_setting_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp hM23
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h528 G T M L V H B D L₂ n hyp with hK | ⟨-, K', hKK', hmax, hexc⟩
  · exact absurd hK hM23.2
  have hTK : T ≤ K' := (h5211 G T M L V H B D L₂ n K' hyp hM23 hKK' hmax hexc).2
  obtain ⟨hshort, ⟨α, hαs, hαk⟩, hidx⟩ := hexc

  have hTs : IsSylowTwoOf T K' := isSylowTwoOf_of_isSylowTwo hyp.sylow hTK
  have hTK2 : IsPGroup 2 (T.subgroupOf K') :=
    hTs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  set PT : Sylow 2 ↥K' := hTK2.toSylow hTs.2.2 with hPT
  set P := PT.mapSurjective hαs with hP
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) P m23T0Sylow

  set π : ↥K' →* Equiv.Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp ((MulAut.conj c).toMonoidHom.comp α) with hπ
  have hπapp : ∀ g : ↥K', π g = ((c * α g * c⁻¹ : alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7)) := fun g => rfl
  refine ⟨K', π, ⟨hKK', hmax, ⟨hshort, ⟨α, hαs, hαk⟩, hidx⟩, hTK, ?_, ?_, ?_⟩⟩
  ·
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact (c * α g * c⁻¹).2
    · intro hσ
      obtain ⟨g, hg⟩ := hαs (c⁻¹ * ⟨σ, hσ⟩ * c)
      refine ⟨g, ?_⟩
      rw [hπapp, hg]
      simp [mul_assoc]
  ·
    ext g
    rw [MonoidHom.mem_ker, hπapp]
    have hk : g ∈ α.ker ↔ g ∈ (pCoreOf 2 K').subgroupOf K' := by
      rw [hαk, CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore, Subgroup.mem_subgroupOf]
      exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨g', hg', hgg'⟩ => (Subtype.ext hgg' : g' = g) ▸ hg'⟩
    rw [← hk, MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : c * α g * c⁻¹ = 1 := Subtype.ext h
      have : α g = 1 := by
        have := congrArg (fun x => c⁻¹ * x * c) h'
        simpa [mul_assoc] using this
      exact this
    · intro h
      rw [h]
      simp
  ·
    intro i j
    rw [← m23T0List_orbits]
    constructor
    · rintro ⟨g, hgT, hgij⟩
      refine ⟨π g, ?_, hgij⟩
      have hmem : c * α g * c⁻¹ ∈ (m23T0Sylow : Subgroup (alternatingGroup (Fin 7))) := by
        rw [← hc, Sylow.coe_subgroup_smul]
        refine Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mpr ⟨α g, ?_, ?_⟩
        · rw [hP, Sylow.coe_mapSurjective]
          exact ⟨g, (show g ∈ (PT : Subgroup ↥K') from hgT), rfl⟩
        · simp [MulAut.smul_def]
      exact hmem
    · rintro ⟨σ, hσ, hσij⟩
      have hσA : σ ∈ alternatingGroup (Fin 7) := m23T0List_alt σ hσ
      have hmem : (⟨σ, hσA⟩ : alternatingGroup (Fin 7)) ∈
          (m23T0Sylow : Subgroup (alternatingGroup (Fin 7))) := hσ
      rw [← hc, Sylow.coe_subgroup_smul] at hmem
      obtain ⟨τ, hτ, hτσ⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hmem
      rw [hP, Sylow.coe_mapSurjective] at hτ
      obtain ⟨g, hgT, rfl⟩ := hτ
      refine ⟨g, hgT, ?_⟩
      rw [hπapp]
      have : c * α g * c⁻¹ = ⟨σ, hσA⟩ := by
        rw [← hτσ]
        simp [MulAut.smul_def]
      rw [this]
      exact hσij

end CFSG.Quasithin.H13
