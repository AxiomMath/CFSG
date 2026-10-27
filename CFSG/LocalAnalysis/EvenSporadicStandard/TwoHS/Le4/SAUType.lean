module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyAssembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignA

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

theorem d8_sq : ∀ d : DihedralGroup 4, d * d = 1 ∨ d * d = DihedralGroup.r 2 := by decide

theorem d8_cube : ∀ d : DihedralGroup 4, d ^ 3 = 1 → d = 1 := by decide

set_option maxRecDepth 100000 in
theorem s5_even_four :
    ∀ σ : Equiv.Perm (Fin 5), σ ^ 4 = 1 → Equiv.Perm.sign σ = 1 → σ * σ = 1 := by decide

set_option maxRecDepth 100000 in
theorem s5_cent3 : ∀ σ ρ : Equiv.Perm (Fin 5), σ * σ = 1 → ρ ^ 3 = 1 → ρ ≠ 1 → σ * ρ = ρ * σ →
    σ = 1 ∨ Equiv.Perm.sign σ = -1 := by decide

section Coords

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f y t r : G} {Θ : HModel →* G}

omit [Finite G] in
theorem FyConf.ly_coords (hconf : FyConf t r Θ) (hcos : FyCoset L f y Θ) {u : G}
    (hut : u * t = t * u) (hur : u * r = r * u) (huu : u * u = 1) (hnf : u ∉ L ⊔ zpowers f)
    (hy : u ∈ L ⊔ zpowers y) :
    ∃ (k : ZMod 4) (σ : Equiv.Perm (Fin 5)), u = Θ (DihedralGroup.sr k, 1, σ) ∧ σ * σ = 1 ∧
      dihChar 1 (DihedralGroup.sr k) * Equiv.Perm.sign σ = 1 := by
  obtain ⟨⟨d, c, σ⟩, hdcσ⟩ := (hconf.mem_range u).1 ⟨hut, hur⟩
  obtain ⟨k, rfl⟩ := exists_sr_of_not_mem hcos (c := c) (σ := σ) (by rw [hdcσ]; exact hnf)
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
  have hpar : dihChar 1 (DihedralGroup.sr k) * Equiv.Perm.sign σ = 1 :=
    (hcos.mem_y _ 1 σ).1 (by rw [hdcσ]; exact hy)
  exact ⟨k, σ, hdcσ.symm, hσ2, hpar⟩

theorem FyConf.ly_class (hconf : FyConf t r Θ) {k : ZMod 4} {σ : Equiv.Perm (Fin 5)}
    (hσ2 : σ * σ = 1) (hpar : dihChar 1 (DihedralGroup.sr k) * Equiv.Perm.sign σ = 1)
    (hsig : σ = 1 ∨ Equiv.Perm.sign σ = -1) :
    ∃ nn : G, nn * t = t * nn ∧
      Θ (DihedralGroup.sr k, 1, σ) = nn * Θ (DihedralGroup.sr 0, 1, 1) * nn⁻¹ := by
  have hno : ¬ (σ ≠ 1 ∧ Equiv.Perm.sign σ = 1 ∧ dihChar 1 (DihedralGroup.sr k) = 1) := by
    rintro ⟨h1, h2, -⟩
    rcases hsig with h | h
    · exact h1 h
    · rw [h2] at h
      exact absurd h (by decide)
  obtain ⟨gm, hgm⟩ := hmodel_class k σ hσ2 hpar hno
  have hcomm_gm : Θ gm * t = t * Θ gm := hconf.comm_t gm
  rcases hgm with hgm | hgm
  · refine ⟨Θ gm, hcomm_gm, ?_⟩
    rw [hgm, map_mul, map_mul, map_inv]
  · obtain ⟨nf, hnf, hnf'⟩ := hconf.fusion
    refine ⟨Θ gm * nf, ?_, ?_⟩
    · calc Θ gm * nf * t = Θ gm * (nf * t) := by group
        _ = Θ gm * (t * nf) := by rw [hnf]
        _ = (Θ gm * t) * nf := by group
        _ = (t * Θ gm) * nf := by rw [hcomm_gm]
        _ = t * (Θ gm * nf) := by group
    · rw [hgm, map_mul, map_mul, map_inv, ← hnf']
      group

omit [Finite G] in
theorem FyConf.t_comm_r (h : FyConf t r Θ) : t * r = r * t := by
  rw [← h.t_eq, ← h.r_eq, ← map_mul, ← map_mul]
  congr 1

omit [Finite G] in
theorem FyConf.sig_ne_one (hconf : FyConf t r Θ) {a : HModel} {u e : G} (hu : u = Θ a)
    (ha : a.2.2 = 1) (het : e * t = t * e) (her : e * r = r * e)
    (hinv : e * u * e = u) (h1 : e * e ≠ 1) (h2 : e * e ≠ t) : False := by
  obtain ⟨e', he⟩ := (hconf.mem_range e).1 ⟨het, her⟩
  have h3 : Θ (e' * a * e') = Θ a := by
    rw [map_mul, map_mul, he, ← hu]
    exact hinv
  have h4 := hconf.inj h3
  have hc : e'.2.1 * e'.2.1 = 1 := by
    have := congrArg (fun p : HModel => p.2.1) h4
    simp only [Prod.snd_mul, Prod.fst_mul] at this
    have h5 : e'.2.1 * a.2.1 * e'.2.1 = a.2.1 * (e'.2.1 * e'.2.1) := by
      rw [mul_comm e'.2.1 a.2.1, mul_assoc]
    rw [h5] at this
    exact mul_left_cancel (a := a.2.1) (by rw [mul_one]; exact this)
  have hσ₀ : e'.2.2 * e'.2.2 = 1 := by
    have := congrArg (fun p : HModel => p.2.2) h4
    simpa [ha] using this
  have hc1 : e'.2.1 = 1 := z3_sq_eq_one _ hc
  have hee : e * e = Θ (e'.1 * e'.1, 1, 1) := by
    rw [← he, ← map_mul]
    congr 1
    refine Prod.ext rfl (Prod.ext (by simp [hc1]) ?_)
    simpa using hσ₀
  rcases d8_sq e'.1 with hd | hd
  · rw [hd, show ((1 : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) = 1 from rfl,
      map_one] at hee
    exact h1 hee
  · rw [hd, hconf.t_eq] at hee
    exact h2 hee

omit [Finite G] in
theorem FyConf.sig_of_three (hconf : FyConf t r Θ) {k : ZMod 4} {σ : Equiv.Perm (Fin 5)}
    {u ρ : G} (hu : u = Θ (DihedralGroup.sr k, 1, σ)) (hσ2 : σ * σ = 1) (hρ3 : ρ ^ 3 = 1)
    (hρt : ρ * t = t * ρ) (hρr : ρ * r = r * ρ) (hρn : ρ ∉ zpowers r) (hρu : ρ * u = u * ρ) :
    σ = 1 ∨ Equiv.Perm.sign σ = -1 := by
  obtain ⟨⟨d, c, σ'⟩, hρ⟩ := (hconf.mem_range ρ).1 ⟨hρt, hρr⟩
  have hρ3' : ((d, c, σ') : HModel) ^ 3 = 1 := by
    apply hconf.inj
    rw [map_pow, hρ, hρ3, map_one]
  have hd : d = 1 := d8_cube d (by simpa using congrArg (fun p : HModel => p.1) hρ3')
  have hσ'3 : σ' ^ 3 = 1 := by simpa using congrArg (fun p : HModel => p.2.2) hρ3'
  have hσ'1 : σ' ≠ 1 := by
    intro h1
    apply hρn
    rw [mem_zpowers_iff]
    refine ⟨((Multiplicative.toAdd c).val : ℤ), ?_⟩
    have hpow : (((1 : DihedralGroup 4), Multiplicative.ofAdd (1 : ZMod 3),
        (1 : Equiv.Perm (Fin 5))) : HModel) ^ (Multiplicative.toAdd c).val = (1, c, 1) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show (1 : DihedralGroup 4) ^ (Multiplicative.toAdd c).val = 1
        exact one_pow _
      · show (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd c).val = c
        rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
        rfl
      · show (1 : Equiv.Perm (Fin 5)) ^ (Multiplicative.toAdd c).val = 1
        exact one_pow _
    rw [zpow_natCast, ← hconf.r_eq, ← map_pow, hpow, ← hρ, hd, h1]
  have hcomm : Θ ((d, c, σ') * (DihedralGroup.sr k, 1, σ)) =
      Θ ((DihedralGroup.sr k, 1, σ) * (d, c, σ')) := by
    rw [map_mul, map_mul, hρ, ← hu]
    exact hρu
  have h5 := congrArg (fun p : HModel => p.2.2) (hconf.inj hcomm)
  simp only [Prod.mk_mul_mk] at h5
  exact s5_cent3 σ σ' hσ2 hσ'3 hσ'1 h5.symm

omit [Finite G] in
theorem FyConf.sq_eq_one_of_odd (hconf : FyConf t r Θ) {a b : HModel} {u w : G} (hu : u = Θ a)
    (hw : w = Θ b) (hc₁ : a.2.1 = 1) (hc₂ : b.2.1 = 1) (hs₁ : Equiv.Perm.sign a.2.2 = -1)
    (hs₂ : Equiv.Perm.sign b.2.2 = -1) (hx4 : (u⁻¹ * w) ^ 4 = 1)
    (hxt : (u⁻¹ * w) * (u⁻¹ * w) ≠ t) : (u⁻¹ * w) * (u⁻¹ * w) = 1 := by
  have hmul : Θ (a⁻¹ * b) = Θ a⁻¹ * Θ b := map_mul Θ _ _
  have hinv : Θ a⁻¹ = (Θ a)⁻¹ := map_inv Θ a
  have hxh : u⁻¹ * w = Θ (a⁻¹ * b) := by rw [hmul, hinv, ← hu, ← hw]
  have h4 : (a⁻¹ * b) ^ 4 = 1 := by
    apply hconf.inj
    rw [map_pow, ← hxh, hx4, map_one]
  have hσ4 : (a.2.2⁻¹ * b.2.2) ^ 4 = 1 := by
    have := congrArg (fun p : HModel => p.2.2) h4
    exact this
  have hsg : Equiv.Perm.sign (a.2.2⁻¹ * b.2.2) = 1 := by
    rw [map_mul, map_inv, hs₁, hs₂]
    decide
  have hσ2 : (a.2.2⁻¹ * b.2.2) * (a.2.2⁻¹ * b.2.2) = 1 := s5_even_four _ hσ4 hsg
  have hhh : (a⁻¹ * b) * (a⁻¹ * b) = ((a⁻¹ * b).1 * (a⁻¹ * b).1, 1, 1) := by
    refine Prod.ext rfl (Prod.ext ?_ hσ2)
    show (a.2.1⁻¹ * b.2.1) * (a.2.1⁻¹ * b.2.1) = 1
    rw [hc₁, hc₂]
    decide
  have hxx : (u⁻¹ * w) * (u⁻¹ * w) = Θ ((a⁻¹ * b) * (a⁻¹ * b)) := by
    rw [hxh]
    exact (map_mul Θ _ _).symm
  rcases d8_sq (a⁻¹ * b).1 with hd | hd
  · rw [hxx, hhh, hd]
    exact map_one Θ
  · exfalso
    apply hxt
    rw [hxx, hhh, hd, hconf.t_eq]

end Coords

end CFSG.EvenSporadicStandard.TwoHS
