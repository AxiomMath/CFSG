module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxSign
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUType
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyLy

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

theorem sect8InputLy_of_signTheoremXW (hS : SignTheoremXW)
    (hF : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G)
      (n : G), Sect7Hyps G L f s y S₀ n → FyModelFacts L f y) : Sect8InputLy := by
  intro G _ _ L f s y S₀ n hH w hw hwf ⟨g, hg⟩
  have hM := hF G L f s y S₀ n hH
  obtain ⟨r0, Θ0, hconf0, hcos0⟩ := hM.conf
  have hf4 : f ^ 2 * f ^ 2 = 1 := by
    rw [← pow_add]; exact hH.f_pow_four
  have hww : w * w = 1 := by
    rw [hg]
    calc g⁻¹ * f ^ 2 * g * (g⁻¹ * f ^ 2 * g) = g⁻¹ * (f ^ 2 * f ^ 2) * g := by group
      _ = 1 := by rw [hf4]; group
  have hyN : y ∈ centralizer ({f ^ 2} : Set G) := by
    rw [hH.cent_eq]
    exact Subgroup.mem_sup_right (mem_zpowers y)
  have hy_comm : y * f ^ 2 = f ^ 2 * y :=
    ((mem_centralizer_iff.1 hyN (f ^ 2) (Set.mem_singleton _))).symm
  obtain ⟨ry, hryL, hry3, hryy⟩ := hM.outer3 y hH.yy hy_comm hH.y_not
  have hry_t : ry * f ^ 2 = f ^ 2 * ry := hH.comm_t hryL
  obtain ⟨m, hm_t, hm⟩ := hconf0.one_class ry hry_t hry3
  have hmt' : m⁻¹ * f ^ 2 = f ^ 2 * m⁻¹ := by
    calc m⁻¹ * f ^ 2 = m⁻¹ * f ^ 2 * m * m⁻¹ := by group
      _ = m⁻¹ * (f ^ 2 * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * f ^ 2) * m⁻¹ := by rw [hm_t]
      _ = f ^ 2 * m⁻¹ := by group
  have hmr : m⁻¹ * r0 * m⁻¹⁻¹ = ry := by
    calc m⁻¹ * r0 * m⁻¹⁻¹ = m⁻¹ * (m * ry * m⁻¹) * m := by rw [hm]; group
      _ = ry := by group
  have hconf : FyConf (f ^ 2) ry (confConj m⁻¹ Θ0) := by
    have := hconf0.conj m⁻¹ hmt'
    rwa [hmr] at this
  have hcos : FyCoset L f y (confConj m⁻¹ Θ0) :=
    hcos0.conj m⁻¹ (hH.normalizes_f hmt') (hH.normalizes_y hmt')
  obtain ⟨k₀, σ₀, hy₀, -, hpar₀⟩ := hconf.ly_coords hcos hy_comm hryy.symm hH.yy hH.y_not
    (Subgroup.mem_sup_right (mem_zpowers y))
  obtain ⟨g₀, hg₀r, hg₀⟩ := hconf.exists_conj_cent hryy.symm hH.y_conj
  obtain ⟨χ, b, hχ, hinsp⟩ := hS G (f ^ 2) ry (confConj m⁻¹ Θ0) hconf k₀ σ₀ hpar₀
    ⟨g₀, hg₀r, by rw [← hy₀]; exact hg₀⟩
  have hχv := fun {x : G} (hx : x ∈ centralizer ({ry} : Set G)) {d : DihedralGroup 4} {c : Z3}
    {σ : Equiv.Perm (Fin 5)} (hxe : confConj m⁻¹ Θ0 (d, c, σ) = x) =>
    chi_val (Θ := confConj m⁻¹ Θ0) χ b hχ hx hxe
  have ht_cent : f ^ 2 ∈ centralizer ({ry} : Set G) := mem_cent_of_comm hry_t.symm
  have hχt : χ ⟨f ^ 2, ht_cent⟩ = 1 := by
    have := hχv ht_cent (d := DihedralGroup.r 2) (c := 1) (σ := 1) hconf.t_eq
    rw [this, dihChar_r_two]
    simp
  have hchi_conj : ∀ u : G, u * ry = ry * u → (∃ g' : G, u = g' * f ^ 2 * g'⁻¹) →
      ∀ hu : u ∈ centralizer ({ry} : Set G), χ ⟨u, hu⟩ = 1 := by
    intro u hur hu' hu
    obtain ⟨g1, hg1, hug1⟩ := hconf.exists_conj_cent hur hu'
    have hg1C : g1 ∈ centralizer ({ry} : Set G) := mem_cent_of_comm hg1
    have : (⟨u, hu⟩ : ↥(centralizer ({ry} : Set G))) =
        ⟨g1, hg1C⟩ * ⟨f ^ 2, ht_cent⟩ * ⟨g1, hg1C⟩⁻¹ := Subtype.ext hug1
    rw [this, chi_conj, hχt]
  have hy_range : y ∈ (confConj m⁻¹ Θ0).range := (hconf.mem_range y).1 ⟨hy_comm, hryy.symm⟩
  obtain ⟨⟨d, c, σ⟩, hdcσ⟩ := hy_range
  have hyC : y ∈ centralizer ({ry} : Set G) := mem_cent_of_comm hryy.symm
  have hy1 : χ ⟨y, hyC⟩ = 1 := by
    refine hchi_conj y hryy.symm ?_ hyC
    obtain ⟨gy, hgy⟩ := hH.y_conj
    exact ⟨gy, hgy⟩
  have hyv := hχv hyC hdcσ
  have hsr : ∃ k : ZMod 4, d = DihedralGroup.sr k := by
    refine exists_sr_of_not_mem hcos (c := c) (σ := σ) ?_
    rw [hdcσ]
    exact hH.y_not
  obtain ⟨k, rfl⟩ := hsr
  have hyB : (confConj m⁻¹ Θ0) (DihedralGroup.sr k, c, σ) ∈ L ⊔ zpowers y := by
    rw [hdcσ]
    exact Subgroup.mem_sup_right (mem_zpowers y)
  have hyB' := (hcos.mem_y _ c σ).1 hyB
  have hb : b = 1 := by
    rw [hyv, dihChar_sr_eq, mul_assoc, hyB', mul_one] at hy1
    exact hy1
  have key : ∀ u : G, u * f ^ 2 = f ^ 2 * u → u * ry = ry * u → u * u = 1 →
      u ∉ L ⊔ zpowers f → (∃ g' : G, u = g' * f ^ 2 * g'⁻¹) →
      ∃ nn : G, nn * f ^ 2 = f ^ 2 * nn ∧
        u = nn * (confConj m⁻¹ Θ0) (DihedralGroup.sr 0, 1, 1) * nn⁻¹ := by
    intro u hut hur huu huf hu'
    obtain ⟨⟨d, c, σ⟩, hdcσ⟩ := (hconf.mem_range u).1 ⟨hut, hur⟩
    have huC : u ∈ centralizer ({ry} : Set G) := mem_cent_of_comm hur
    have hu1 : χ ⟨u, huC⟩ = 1 := hchi_conj u hur hu' huC
    have huv := hχv huC hdcσ
    obtain ⟨k, rfl⟩ := exists_sr_of_not_mem hcos (c := c) (σ := σ) (by rw [hdcσ]; exact huf)
    have hsq : ((DihedralGroup.sr k, c, σ) : HModel) * (DihedralGroup.sr k, c, σ) = 1 := by
      apply hconf.inj
      rw [map_mul, hdcσ, huu, map_one]
    have hc1 : c = 1 := by
      apply z3_sq_eq_one
      have := congrArg (fun p : HModel => p.2.1) hsq
      simpa using this
    have hσ2 : σ * σ = 1 := by
      have := congrArg (fun p : HModel => p.2.2) hsq
      simpa using this
    subst hc1
    rw [huv, hb, dihChar_sr_eq, ] at hu1
    have hpar : dihChar 1 (DihedralGroup.sr k) * Equiv.Perm.sign σ = 1 := by
      rw [one_mul] at hu1
      exact hu1
    have hno : ¬ (σ ≠ 1 ∧ Equiv.Perm.sign σ = 1 ∧ dihChar 1 (DihedralGroup.sr k) = 1) := by
      rintro ⟨h1, h2, h3⟩
      refine hinsp k σ h1 hσ2 h2 (by rw [hb]; exact h3) ?_
      obtain ⟨g1, hg1, hug1⟩ := hconf.exists_conj_cent hur hu'
      exact ⟨g1, hg1, by rw [hdcσ]; exact hug1⟩
    obtain ⟨gm, hgm⟩ := hmodel_class k σ hσ2 hpar hno
    have hcomm_gm : (confConj m⁻¹ Θ0) gm * f ^ 2 = f ^ 2 * (confConj m⁻¹ Θ0) gm :=
      hconf.comm_t gm
    rcases hgm with hgm | hgm
    · refine ⟨(confConj m⁻¹ Θ0) gm, hcomm_gm, ?_⟩
      rw [← hdcσ, hgm, map_mul, map_mul, map_inv]
    · obtain ⟨nf, hnf, hnf'⟩ := hconf.fusion
      refine ⟨(confConj m⁻¹ Θ0) gm * nf, ?_, ?_⟩
      · calc (confConj m⁻¹ Θ0) gm * nf * f ^ 2 = (confConj m⁻¹ Θ0) gm * (nf * f ^ 2) := by group
          _ = (confConj m⁻¹ Θ0) gm * (f ^ 2 * nf) := by rw [hnf]
          _ = ((confConj m⁻¹ Θ0) gm * f ^ 2) * nf := by group
          _ = (f ^ 2 * (confConj m⁻¹ Θ0) gm) * nf := by rw [hcomm_gm]
          _ = f ^ 2 * ((confConj m⁻¹ Θ0) gm * nf) := by group
      · rw [← hdcσ, hgm, map_mul, map_mul, map_inv, ← hnf']
        group
  obtain ⟨ny, hny_t, hny⟩ := key y hy_comm hryy.symm hH.yy hH.y_not hH.y_conj
  obtain ⟨rw, hrwL, hrw3, hrwy⟩ := hM.outer3 w hww hw hwf
  have hrw_t : rw * f ^ 2 = f ^ 2 * rw := hH.comm_t hrwL
  obtain ⟨mw, hmw_t, hmw⟩ := hconf.one_class rw hrw_t hrw3
  have hmwt' : mw⁻¹ * f ^ 2 = f ^ 2 * mw⁻¹ := by
    calc mw⁻¹ * f ^ 2 = mw⁻¹ * f ^ 2 * mw * mw⁻¹ := by group
      _ = mw⁻¹ * (f ^ 2 * mw) * mw⁻¹ := by group
      _ = mw⁻¹ * (mw * f ^ 2) * mw⁻¹ := by rw [hmw_t]
      _ = f ^ 2 * mw⁻¹ := by group
  set w' : G := mw * w * mw⁻¹ with hw'
  have hw't : w' * f ^ 2 = f ^ 2 * w' := by
    calc w' * f ^ 2 = mw * w * (mw⁻¹ * f ^ 2) := by rw [hw']; group
      _ = mw * w * (f ^ 2 * mw⁻¹) := by rw [hmwt']
      _ = mw * (w * f ^ 2) * mw⁻¹ := by group
      _ = mw * (f ^ 2 * w) * mw⁻¹ := by rw [hw]
      _ = (mw * f ^ 2) * w * mw⁻¹ := by group
      _ = (f ^ 2 * mw) * w * mw⁻¹ := by rw [hmw_t]
      _ = f ^ 2 * w' := by rw [hw']; group
  have hw'r : w' * ry = ry * w' := by
    have hrw : mw⁻¹ * ry * mw = rw := by
      calc mw⁻¹ * ry * mw = mw⁻¹ * (mw * rw * mw⁻¹) * mw := by rw [hmw]
        _ = rw := by group
    calc w' * ry = mw * w * (mw⁻¹ * ry * mw) * mw⁻¹ := by rw [hw']; group
      _ = mw * w * rw * mw⁻¹ := by rw [hrw]
      _ = mw * (w * rw) * mw⁻¹ := by group
      _ = mw * (rw * w) * mw⁻¹ := by rw [← hrwy]
      _ = (mw * rw * mw⁻¹) * (mw * w * mw⁻¹) := by group
      _ = ry * w' := by rw [hmw, hw']
  have hw'w' : w' * w' = 1 := by
    calc w' * w' = mw * (w * w) * mw⁻¹ := by rw [hw']; group
      _ = 1 := by rw [hww]; group
  have hw'f : w' ∉ L ⊔ zpowers f := fun h =>
    hwf ((hH.normalizes_f hmw_t w).2 h)
  have hw'conj : ∃ g' : G, w' = g' * f ^ 2 * g'⁻¹ :=
    ⟨mw * g⁻¹, by rw [hw', hg]; group⟩
  obtain ⟨nw, hnw_t, hnw⟩ := key w' hw't hw'r hw'w' hw'f hw'conj
  refine ⟨mw⁻¹ * nw * ny⁻¹, ?_, ?_⟩
  · have hny' : ny⁻¹ * f ^ 2 = f ^ 2 * ny⁻¹ := by
      calc ny⁻¹ * f ^ 2 = ny⁻¹ * f ^ 2 * ny * ny⁻¹ := by group
        _ = ny⁻¹ * (f ^ 2 * ny) * ny⁻¹ := by group
        _ = ny⁻¹ * (ny * f ^ 2) * ny⁻¹ := by rw [hny_t]
        _ = f ^ 2 * ny⁻¹ := by group
    calc mw⁻¹ * nw * ny⁻¹ * f ^ 2 = mw⁻¹ * nw * (ny⁻¹ * f ^ 2) := by group
      _ = mw⁻¹ * nw * (f ^ 2 * ny⁻¹) := by rw [hny']
      _ = mw⁻¹ * (nw * f ^ 2) * ny⁻¹ := by group
      _ = mw⁻¹ * (f ^ 2 * nw) * ny⁻¹ := by rw [hnw_t]
      _ = (mw⁻¹ * f ^ 2) * nw * ny⁻¹ := by group
      _ = (f ^ 2 * mw⁻¹) * nw * ny⁻¹ := by rw [hmwt']
      _ = f ^ 2 * (mw⁻¹ * nw * ny⁻¹) := by group
  · have e1 : w = mw⁻¹ * w' * mw := by rw [hw']; group
    have e2 : (confConj m⁻¹ Θ0) (DihedralGroup.sr 0, 1, 1) = ny⁻¹ * y * ny := by
      rw [hny]; group
    rw [e1, hnw, e2]
    group

end CFSG.EvenSporadicStandard.TwoHS
