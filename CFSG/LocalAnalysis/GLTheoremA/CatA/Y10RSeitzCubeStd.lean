module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeCore
public import CFSG.LieType.ChevTwo.OppositeFixedExcBase
public import CFSG.GH74.GLS.Stage2.OddAut.BTCanon

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.GH74.GLS.Stage2.OddAut CFSG.LieType.ChevTwo

theorem seitzTwoGen_of_family {K : Type} [Group K] [Finite K] {ι : Type} (QJ PJ : ι → Subgroup K)
    (hQJ2 : ∀ j, IsPGroup 2 ↥(QJ j))
    (hPJ : ∀ j, PJ j ≤ Subgroup.normalizer (QJ j : Set K))
    (hstd : ∀ Q : Subgroup K, Q ≠ ⊥ → IsPGroup 2 ↥Q → ∃ (g : K) (j : ι),
      (∀ x ∈ Subgroup.normalizer (Q : Set K), g⁻¹ * x * g ∈ PJ j) ∧
        ∀ y ∈ Q, g⁻¹ * y * g ∈ QJ j)
    (hcore : ∀ j (p : ℕ), p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut K), IsPGroup p ↥R →
      (∀ α ∈ R, (QJ j).map α.toMonoidHom = QJ j) →
      Subgroup.normalizer (QJ j : Set K) = PJ j →
      ∃ V : Subgroup K, IsPGroup 2 ↥V ∧ (∀ α ∈ R, V.map α.toMonoidHom = V) ∧
        QJ j ⊔ V = ⊤) : SeitzTwoGen K := by
  intro q hq hq2 E hE ⟨U, hU0, hU2, hUinv⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hQn, hstab⟩ := exists_radSeq_stable (p := 2) hU2
  set Q : Subgroup K := radInf 2 U with hQ
  have hQ2 : IsPGroup 2 Q := by
    rw [hQn]
    exact radSeq_isPGroup (p := 2) hU2 n
  have hQcore : pCoreOf 2 (Subgroup.normalizer (Q : Set K)) = Q := by
    rw [hQn]
    exact hstab
  have hUQ : U ≤ Q := (le_radInf (p := 2) U).trans (le_of_eq hQ.symm)
  have hQ0 : Q ≠ ⊥ := fun h => hU0 (le_bot_iff.mp (hUQ.trans h.le))
  have hQinv : ∀ α ∈ E, Q.map α.toMonoidHom = Q := by
    intro α hα
    have hUmap : U.map α.toMonoidHom = U := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        exact hUinv α hα u hu
      · intro u hu
        exact ⟨α⁻¹ u, hUinv α⁻¹ (E.inv_mem hα) u hu, by simp⟩
    exact radInf_map_eq (p := 2) (α : K ≃* K) hUmap
  obtain ⟨g, j, hN, hQstd⟩ := hstd Q hQ0 hQ2
  obtain ⟨hQmap, hNQ⟩ := std_position g hQcore (hQJ2 j) (hPJ j) hN hQstd
  set γ : MulAut K := MulAut.conj g⁻¹ with hγ
  set R : Subgroup (MulAut K) := E.map (MulAut.conj γ).toMonoidHom with hR
  have hRp : IsPGroup q ↥R := by
    rw [hR]
    exact hE.map _
  have hRinv : ∀ α' ∈ R, (QJ j).map α'.toMonoidHom = QJ j := by
    intro α' hα'
    rw [hR] at hα'
    obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.1 hα'
    have hcomp : (((MulAut.conj γ) α).toMonoidHom.comp γ.toMonoidHom) =
        γ.toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
        MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    calc (QJ j).map ((MulAut.conj γ) α).toMonoidHom
        = (Q.map γ.toMonoidHom).map ((MulAut.conj γ) α).toMonoidHom := by rw [hQmap]
      _ = Q.map (((MulAut.conj γ) α).toMonoidHom.comp γ.toMonoidHom) :=
          Subgroup.map_map Q (((MulAut.conj γ) α).toMonoidHom) γ.toMonoidHom
      _ = Q.map (γ.toMonoidHom.comp α.toMonoidHom) := by rw [hcomp]
      _ = (Q.map α.toMonoidHom).map γ.toMonoidHom :=
          (Subgroup.map_map Q γ.toMonoidHom α.toMonoidHom).symm
      _ = Q.map γ.toMonoidHom := by rw [hQinv α hα]
      _ = QJ j := hQmap
  obtain ⟨V, hV2, hVinv, hVgen⟩ := hcore j q hq hq2 R hRp hRinv hNQ
  have hVinv' : ∀ α ∈ E, ∀ u ∈ V.map (MulAut.conj g).toMonoidHom,
      α u ∈ V.map (MulAut.conj g).toMonoidHom := by
    intro α hα u hu
    have hα' : (MulAut.conj γ) α ∈ R := by
      rw [hR]
      exact Subgroup.mem_map_of_mem _ hα
    have hVα : V.map ((MulAut.conj γ) α).toMonoidHom = V := hVinv _ hα'
    have hcomp : α.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp ((MulAut.conj γ) α).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, hγ, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
        MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [show (MulEquiv.symm (MulAut.conj g⁻¹)) x = g * x * g⁻¹ by
        simp [MulAut.conj_apply]]
      group
    have hmap : (V.map (MulAut.conj g).toMonoidHom).map α.toMonoidHom =
        V.map (MulAut.conj g).toMonoidHom := by
      calc (V.map (MulAut.conj g).toMonoidHom).map α.toMonoidHom
          = V.map (α.toMonoidHom.comp (MulAut.conj g).toMonoidHom) :=
            Subgroup.map_map V α.toMonoidHom (MulAut.conj g).toMonoidHom
        _ = V.map ((MulAut.conj g).toMonoidHom.comp ((MulAut.conj γ) α).toMonoidHom) := by
            rw [hcomp]
        _ = (V.map ((MulAut.conj γ) α).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
            (Subgroup.map_map V (MulAut.conj g).toMonoidHom ((MulAut.conj γ) α).toMonoidHom).symm
        _ = V.map (MulAut.conj g).toMonoidHom := by rw [hVα]
    have hu' := Subgroup.mem_map_of_mem α.toMonoidHom hu
    rwa [hmap] at hu'
  have hQinv' : ∀ α ∈ E, ∀ u ∈ Q, α u ∈ Q := by
    intro α hα u hu
    have h := Subgroup.mem_map_of_mem α.toMonoidHom hu
    rwa [hQinv α hα] at h
  have hQJQ : (QJ j).map (MulAut.conj g).toMonoidHom = Q := by
    rw [← hQmap, Subgroup.map_map]
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id K := by
      ext x
      simp only [MonoidHom.comp_apply, MulAut.conj_apply, MonoidHom.id_apply,
        MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.inv_apply,
        MulEquiv.symm_apply_apply]
      group
    rw [hcomp, Subgroup.map_id]
  have hsup : Q ⊔ V.map (MulAut.conj g).toMonoidHom = ⊤ := by
    rw [← hQJQ, ← Subgroup.map_sup, hVgen, Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 (MulAut.conj g).surjective
  exact ⟨Q, V.map (MulAut.conj g).toMonoidHom, hQ2, hV2.map _, hQinv', hVinv', hsup⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
