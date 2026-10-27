module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTheta
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarRLevel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.IndexTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard
open scoped commutatorElement Pointwise

section Sylow


theorem exists_conj_le_hsS {X : Subgroup (Equiv.Perm (Fin 3850))} (hXR : X ≤ hsR)
    (hX : IsPGroup 2 X) : ∃ r ∈ hsR, X ≤ hsS.map (MulAut.conj r).toMonoidHom := by
  obtain ⟨-, -, ⟨T, hT⟩, -⟩ := hs_involution_centralizers
  have hY : IsPGroup 2 (X.subgroupOf hsR) := hX.comap_subtype
  obtain ⟨Q, hQ⟩ := hY.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥hsR) T Q
  refine ⟨(g : Equiv.Perm (Fin 3850)), g.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hXR hx⟩ : ↥hsR) ∈ (Q : Subgroup ↥hsR) := hQ (by rwa [mem_subgroupOf])
  rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have hxT : g⁻¹ * (⟨x, hXR hx⟩ : ↥hsR) * g ∈ (T : Subgroup ↥hsR) := by
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hxQ
  rw [hT, mem_subgroupOf] at hxT
  refine ⟨(g : Equiv.Perm (Fin 3850))⁻¹ * x * g, hxT, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
  group


theorem commutator_le_conj_harD {X : Subgroup (Equiv.Perm (Fin 3850))} (hXR : X ≤ hsR)
    (hX : IsPGroup 2 X) : ∃ r ∈ hsR, ⁅X, X⁆ ≤ harD.map (MulAut.conj r).toMonoidHom := by
  obtain ⟨r, hr, hle⟩ := exists_conj_le_hsS hXR hX
  refine ⟨r, hr, ?_⟩
  calc ⁅X, X⁆ ≤ ⁅hsS.map (MulAut.conj r).toMonoidHom, hsS.map (MulAut.conj r).toMonoidHom⁆ :=
        Subgroup.commutator_mono hle hle
    _ = ⁅hsS, hsS⁆.map (MulAut.conj r).toMonoidHom := (Subgroup.map_commutator hsS hsS _).symm
    _ = harD.map (MulAut.conj r).toMonoidHom := by rw [commutator_hsS_eq_harD]

end Sylow

section Derived

theorem commutator_le_of_index_dvd_two {Y : Type*} [Group Y] {N : Subgroup Y}
    (h : N.index ∣ 2) : commutator Y ≤ N := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact le_top
  · exact commutator_le_of_index_eq_two h2

variable
  {H : Type} [Group H] [Finite H] {E : Subgroup H} [E.Normal]

theorem ThetaData.commutator_eq (hE : IsHSCover H E) (M : CoverModel ↥E)
    (D : ThetaData E M.toCoverMaps) {S : Subgroup H} (hS : IsPGroup 2 S)
    (hT : M.T0.map E.subtype ≤ S) : ⁅S, S⁆ = M.T0'.map E.subtype := by
  have hZ := hE.card_center
  let Θ : H →* Equiv.Perm (Fin 3850) := hsR.subtype.comp D.θ
  have hXR : S.map Θ ≤ hsR := by
    rintro _ ⟨s, -, rfl⟩
    exact (D.θ s).2
  obtain ⟨r, -, hXD⟩ := commutator_le_conj_harD hXR (hS.map Θ)
  have hΘπ : ∀ x : ↥E, Θ (x : H) = ((M.π x : ↥hsP) : Equiv.Perm (Fin 3850)) :=
    fun x => D.theta_inner x
  have h1 : M.T0'.map (hsP.subtype.comp M.π) ≤ harD.map (MulAut.conj r).toMonoidHom := by
    rw [Subgroup.map_le_iff_le_comap, CoverMaps.T0', Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := M.cgens_comm hx
    show (hsP.subtype.comp M.π) ⁅a, b⁆ ∈ harD.map (MulAut.conj r).toMonoidHom
    rw [map_commutatorElement]
    apply hXD
    have ha' : (hsP.subtype.comp M.π) a = Θ (a : H) := (hΘπ a).symm
    have hb' : (hsP.subtype.comp M.π) b = Θ (b : H) := (hΘπ b).symm
    rw [ha', hb']
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_map_of_mem Θ (hT (Subgroup.mem_map_of_mem E.subtype ha)))
      (Subgroup.mem_map_of_mem Θ (hT (Subgroup.mem_map_of_mem E.subtype hb)))
  have hcardD : Nat.card (harD.map (MulAut.conj r).toMonoidHom) = 64 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj r).injective, harD_card]
  have hcardT : Nat.card ↥(M.T0'.map (hsP.subtype.comp M.π)) = 64 := by
    rw [← Subgroup.map_map, Subgroup.card_map_of_injective hsP.subtype_injective,
      M.card_map_pi_T0' hZ]
  have heq : M.T0'.map (hsP.subtype.comp M.π) = harD.map (MulAut.conj r).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge h1 (by rw [hcardD, hcardT])
  apply le_antisymm
  · intro y hy
    have hyE : y ∈ E := commutator_le_of_index_dvd_two hE.index_dvd_two
      (Subgroup.commutator_mono le_top le_top (hy : y ∈ ⁅S, S⁆))
    have hyD : Θ y ∈ harD.map (MulAut.conj r).toMonoidHom := by
      apply hXD
      have : Θ y ∈ ⁅S, S⁆.map Θ := Subgroup.mem_map_of_mem Θ hy
      rwa [Subgroup.map_commutator] at this
    rw [← heq] at hyD
    obtain ⟨x, hx, hxy⟩ := hyD
    have hxy' : M.π x = M.π ⟨y, hyE⟩ := Subtype.ext (hxy.trans (hΘπ ⟨y, hyE⟩))
    have hker : x⁻¹ * (⟨y, hyE⟩ : ↥E) ∈ M.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy', inv_mul_cancel]
    have hkerT := M.ker_le_of_tE_mem hZ M.tE_mem_T0' hker
    have hmem : (⟨y, hyE⟩ : ↥E) ∈ M.T0' := by
      have := M.T0'.mul_mem hx hkerT
      simpa using this
    exact ⟨⟨y, hyE⟩, hmem, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h2 : (⁅M.T0, M.T0⁆).map E.subtype ≤ ⁅S, S⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hT hT
    exact h2 (Subgroup.mem_map_of_mem _ (M.T0'_le_commutator hx))

end Derived

end CFSG.EvenSporadicStandard.TwoHS
