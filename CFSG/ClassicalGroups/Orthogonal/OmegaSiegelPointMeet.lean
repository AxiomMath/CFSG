module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreePoint
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeFlag

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
theorem OmegaSetting.map_iSup_movedSpace_rhoE (g : ↥(elementaryGroup QN)) (a : N) :
    (⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)).map (ρ g : V →ₗ[K] V) =
      ⨆ (w : N) (_ : polar QN ((g : N ≃ₗ[K'] N) a) w = 0),
        movedSpace (rhoE ρ ((g : N ≃ₗ[K'] N) a) w) := by
  have hgO : (g : N ≃ₗ[K'] N) ∈ TauCeti.QuadraticMap.orthogonalGroup QN :=
    elementaryGroup_le_orthogonalGroup QN g.2
  refine le_antisymm ?_ (iSup₂_le fun w hw => ?_)
  · rw [Submodule.map_le_iff_le_comap]
    refine iSup₂_le fun w hw => ?_
    rw [← Submodule.map_le_iff_le_comap, ← movedSpace_rhoE_apply]
    exact le_iSup₂_of_le _ (by rw [polar_map_of_mem hgO]; exact hw) le_rfl
  · have hgw : (g : N ≃ₗ[K'] N) ((g : N ≃ₗ[K'] N).symm w) = w :=
      LinearEquiv.apply_symm_apply _ w
    have hw' : polar QN a ((g : N ≃ₗ[K'] N).symm w) = 0 := by
      rw [← polar_map_of_mem hgO, hgw]
      exact hw
    have h := movedSpace_rhoE_apply (ρ := ρ) g a ((g : N ≃ₗ[K'] N).symm w)
    rw [hgw] at h
    rw [h]
    exact Submodule.map_mono (le_iSup₂_of_le _ hw' le_rfl)

theorem OmegaSetting.orthogonal_iSup_movedSpace_rhoE (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {a : N} (ha : QN a = 0) (ha0 : a ≠ 0) :
    LinearMap.BilinForm.orthogonal (polarBilin Qf)
        (⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)) =
      ⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w) := by
  have hfin := hs.finrank_iSup_movedSpace_rhoE_eq_four htop hfix hK hF h8 ha ha0
  have hle := le_orthogonal_of_totallySingular fun y hy =>
    hs.qf_eq_zero_of_mem_iSup_movedSpace_rhoE htop hfix hK hF h8 ha ha0 hy
  have hperp := finrank_orthogonal_polar hs.nd
    (⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w))
  rw [h8, hfin] at hperp
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hperp, hfin])).symm

theorem OmegaSetting.rhoE_apply_eq_iff_mem_iSup (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {a w : N} (ha : QN a = 0) (ha0 : a ≠ 0) (haw : polar QN a w = 0)
    (hw : QN w ≠ 0) (x : V) :
    rhoE ρ a w x = x ↔ x ∈ ⨆ (y : N) (_ : polar QN a y = 0), movedSpace (rhoE ρ a y) := by
  have hker := ker_sub_one_eq_orthogonal_movedSpace hs.nd (s := rhoE ρ a w) (fun v => hs.iso _ v)
  rw [hs.movedSpace_rhoE_eq_iSup htop hfix hK hF h8 ha ha0 haw hw,
    hs.orthogonal_iSup_movedSpace_rhoE htop hfix hK hF h8 ha ha0] at hker
  rw [← hker, LinearMap.mem_ker]
  simp [sub_eq_zero]

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
theorem OmegaSetting.finrank_movedSpace_rhoE (hs : OmegaSetting QN Qf ρ) {a b : N}
    (ha : QN a = 0) (hb : QN b = 0) (hab : polar QN a b = 0)
    (hli : LinearIndependent K' ![a, b]) : finrank K (movedSpace (rhoE ρ a b)) = 2 :=
  (hs.isLongRootElement_rhoE ha hb hab hli).finrank_movedSpace hs.nd

theorem OmegaSetting.iSup_inf_iSup_eq_bot (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {a b : N} (ha : QN a = 0) (hb : QN b = 0) (hab : polar QN a b ≠ 0) :
    (⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)) ⊓
        (⨆ (w : N) (_ : polar QN b w = 0), movedSpace (rhoE ρ b w)) = ⊥ := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hab (polar_zero_left QN b)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hab (polar_zero_right QN a)
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hza, hzb⟩ := Submodule.mem_inf.mp hz
  have hfa := (hs.forall_rhoE_apply_eq_iff_mem_iSup htop hfix hK hF h8 ha ha0 z).mpr hza
  have hfb := (hs.forall_rhoE_apply_eq_iff_mem_iSup htop hfix hK hF h8 hb hb0 z).mpr hzb
  have hle : rootGroup QN a ⊔ rootGroup QN b ≤
      ((MulAction.stabilizer (V ≃ₗ[K] V) z).comap ρ).map (elementaryGroup QN).subtype := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
      exact ⟨⟨eichler QN a w, eichler_mem_elementaryGroup QN a w⟩, hfa w hw, rfl⟩
    · intro g hg
      obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
      exact ⟨⟨eichler QN b w, eichler_mem_elementaryGroup QN b w⟩, hfb w hw, rfl⟩
  have hall : ∀ g : ↥(elementaryGroup QN), ρ g z = z := by
    intro g
    have hg : (g : N ≃ₗ[K'] N) ∈ rootGroup QN a ⊔ rootGroup QN b := by
      rw [rootGroup_sup_eq_elementaryGroup hs.ndN ha hb hab]
      exact g.2
    obtain ⟨h, hh, hhg⟩ := hle hg
    obtain rfl : h = g := Subtype.ext hhg
    exact hh
  rw [Submodule.mem_bot]
  exact hfix z hall

theorem OmegaSetting.iSup_inf_iSup_eq_movedSpace (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) :
    (⨆ (w : N) (_ : polar QN e w = 0), movedSpace (rhoE ρ e w)) ⊓
        (⨆ (w : N) (_ : polar QN p w = 0), movedSpace (rhoE ρ p w)) =
      movedSpace (rhoE ρ e p) := by
  have hII := hs.caseII_of_six_lt_finrank htop hF (by omega)
  have hpe : polar QN p e = 0 := by rw [polar_comm]; exact hF.ep
  have hpf : polar QN p f = 0 := by rw [polar_comm]; exact hF.fp
  have hcomm : rhoE ρ e p = rhoE ρ p e := rhoE_comm hF.e_sing hF.p_sing hF.ep
  have hcomm' : rhoE ρ p f = rhoE ρ f p := rhoE_comm hF.p_sing hF.f_sing hpf
  have hWp := hs.iSup_movedSpace_rhoE_eq_of_caseII hfix hK hF.swapPairs hII
  have hle1 : movedSpace (rhoE ρ e p) ≤
      ⨆ (w : N) (_ : polar QN e w = 0), movedSpace (rhoE ρ e w) :=
    le_iSup₂_of_le p hF.ep le_rfl
  have hle2 : movedSpace (rhoE ρ e p) ≤
      ⨆ (w : N) (_ : polar QN p w = 0), movedSpace (rhoE ρ p w) := by
    rw [hcomm]
    exact le_iSup₂_of_le e hpe le_rfl
  have hle3 : movedSpace (rhoE ρ p f) ≤
      ⨆ (w : N) (_ : polar QN f w = 0), movedSpace (rhoE ρ f w) := by
    rw [hcomm']
    exact le_iSup₂_of_le p hF.fp le_rfl
  refine le_antisymm (fun z hz => ?_) (le_inf hle1 hle2)
  obtain ⟨hze, hzp⟩ := Submodule.mem_inf.mp hz
  rw [hWp] at hzp
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hzp
  have hz₁e := hle1 (hcomm ▸ hz₁)
  have hz₂e : z₂ ∈ ⨆ (w : N) (_ : polar QN e w = 0), movedSpace (rhoE ρ e w) := by
    simpa using Submodule.sub_mem _ hze hz₁e
  have hbot := hs.iSup_inf_iSup_eq_bot htop hfix hK hF h8 hF.e_sing hF.f_sing
    (by rw [hF.ef]; exact one_ne_zero)
  have hz₂0 : z₂ = 0 := by
    have : z₂ ∈ (⨆ (w : N) (_ : polar QN e w = 0), movedSpace (rhoE ρ e w)) ⊓
        (⨆ (w : N) (_ : polar QN f w = 0), movedSpace (rhoE ρ f w)) :=
      Submodule.mem_inf.mpr ⟨hz₂e, hle3 hz₂⟩
    rwa [hbot, Submodule.mem_bot] at this
  rw [hz₂0, add_zero, hcomm]
  exact hz₁

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
