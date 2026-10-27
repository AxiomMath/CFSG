module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU6Model

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GU6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.SFM12
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section


theorem U6Cent_holds : CFSG.LocalAnalysis.GLTheoremA.Y10F.U6Cent := by
  classical
  unfold CFSG.LocalAnalysis.GLTheoremA.Y10F.U6Cent
  intro L _ _ hL y J hord hlay hJlab α hαJ
  have hZ : Subgroup.center L = ⊥ := u6Center_holds L hL
  obtain ⟨-, -, hM6⟩ := hasLabel_model hL
  have hLM6 := i61_model_psu hM6 (lab := ⟨.twA, 5, 2⟩) rfl rfl
  have hsc6 : CFSG.Open.StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 6 2 2 := by
    rcases hLM6 with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals omega
  obtain ⟨-, F, hFi, hFf, hF, ⟨e⟩⟩ := hsc6
  have hF' : Nat.card F = (2 ^ 2) ^ 2 := hF
  haveI : CharP F 2 := charP_two_of_card hF'
  haveI : Finite F := hFf
  let Φ1 : CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 2) F) ≃*
      ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F) :=
    projIso hF'
  let Φ0 : L ≃* L ⧸ Subgroup.center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let Φ : L ≃* ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F) := Φ0.trans (e.trans Φ1)
  have hgord : orderOf (Φ y) = 5 := (orderOf_injective Φ.toMonoidHom Φ.injective y).trans hord
  have hg5 : (Φ y) ^ 5 = 1 := by
    rw [← hgord]
    exact pow_orderOf_eq_one _
  have hg1 : Φ y ≠ 1 := by
    intro h
    have hy1 : y = 1 := Φ.injective (h.trans (map_one Φ).symm)
    rw [hy1, orderOf_one] at hord
    norm_num at hord
  have hCy : Subgroup.centralizer ({Φ y} : Set ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F)) =
      (Subgroup.centralizer ({y} : Set L)).map Φ.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx
      have hx' : Φ y * x = x * Φ y := hx _ (Set.mem_singleton _)
      refine ⟨Φ.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      apply Φ.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hx'
    · rintro ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      show Φ y * Φ c = Φ c * Φ y
      rw [← map_mul, ← map_mul, hc y (Set.mem_singleton _)]
  have hJsub : J ≤ Subgroup.centralizer ({y} : Set L) := by
    rw [← hlay]
    exact glaLayer_le _
  have hJ'lab : HasLabel ↥(J.map Φ.toMonoidHom) (fun lab : GLALabel => lab = ⟨.twA, 4, 2⟩) :=
    (hasLabel_congr (Subgroup.equivMapOfInjective J Φ.toMonoidHom Φ.injective) _).1 hJlab
  obtain ⟨hJ'q, h41⟩ := forty_one_dvd_of_label hJ'lab
  have hJC : J.map Φ.toMonoidHom ≤
      Subgroup.centralizer ({Φ y} : Set ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F)) := by
    rw [hCy]
    exact Subgroup.map_mono hJsub
  have hnorm : ∀ c ∈ Subgroup.centralizer ({Φ y} : Set ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F)),
      ∀ j ∈ J.map Φ.toMonoidHom, c * j * c⁻¹ ∈ J.map Φ.toMonoidHom := by
    intro c hc j hj
    rw [hCy, Subgroup.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    obtain ⟨j0, hj0, rfl⟩ := Subgroup.mem_map.1 hj
    have hmem : (MulAut.conj c0).toMonoidHom j0 ∈ J := by
      rw [← hlay]
      exact glaLayer_conj_le _ hc0 (Subgroup.mem_map_of_mem _ (hlay ▸ hj0))
    have e' : Φ.toMonoidHom c0 * Φ.toMonoidHom j0 * (Φ.toMonoidHom c0)⁻¹ =
        Φ.toMonoidHom ((MulAut.conj c0).toMonoidHom j0) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    rw [e']
    exact Subgroup.mem_map_of_mem _ hmem
  let αS : MulAut ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F) := Φ.symm.trans (α.trans Φ)
  have hαS : ∀ s ∈ J.map Φ.toMonoidHom, αS s = s := by
    intro s hs
    obtain ⟨j', hj', rfl⟩ := Subgroup.mem_map.1 hs
    show Φ (α (Φ.symm (Φ j'))) = Φ j'
    rw [MulEquiv.symm_apply_apply, hαJ j' hj']
  obtain ⟨n, hn⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GU6.model_fix hF' hg5 hg1 hJ'q hJC hnorm h41 αS hαS
  have key : ∀ l : L, Φ (α l) = (Φ y) ^ n * Φ l * ((Φ y) ^ n)⁻¹ := by
    intro l
    have h1 := hn (Φ l)
    have h2 : αS (Φ l) = Φ (α l) := by
      show Φ (α (Φ.symm (Φ l))) = Φ (α l)
      rw [MulEquiv.symm_apply_apply]
    rw [← h2]
    exact h1
  refine ⟨(y ^ n)⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) n), fun l => ?_⟩
  apply Φ.injective
  rw [key l]
  simp only [inv_inv, map_mul, map_pow, map_inv]

end

end CFSG.LocalAnalysis.GLTheoremA.Y10GU6
