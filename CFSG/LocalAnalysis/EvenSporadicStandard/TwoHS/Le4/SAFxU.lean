module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxSign
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUCl
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUKnot
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUStd
public import Certificates.Certificate26820

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

section Coords

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f y t r : G} {Θ : HModel →* G}

theorem FyConf.sig_of_tconjW (hS : SignTheoremXW) (hconf : FyConf t r Θ)
    (hcos : FyCoset L f y Θ) {u : G} (hut : u * t = t * u) (hur : u * r = r * u)
    (huu : u * u = 1) (hnf : u ∉ L ⊔ zpowers f) (hy : u ∈ L ⊔ zpowers y)
    (hconj : ∃ g : G, u = g * t * g⁻¹) :
    ∃ (k : ZMod 4) (σ : Equiv.Perm (Fin 5)), u = Θ (DihedralGroup.sr k, 1, σ) ∧ σ * σ = 1 ∧
      dihChar 1 (DihedralGroup.sr k) * Equiv.Perm.sign σ = 1 ∧
      (σ = 1 ∨ Equiv.Perm.sign σ = -1) := by
  obtain ⟨k, σ, hu, hσ2, hpar⟩ := hconf.ly_coords hcos hut hur huu hnf hy
  obtain ⟨g1, hg1, hug1⟩ := hconf.exists_conj_cent hur hconj
  obtain ⟨χ, b, hχ, hinsp⟩ := hS G t r Θ hconf k σ hpar ⟨g1, hg1, by rw [← hu]; exact hug1⟩
  have htC : t ∈ centralizer ({r} : Set G) := mem_cent_of_comm hconf.t_comm_r
  have hχt : χ ⟨t, htC⟩ = 1 := by
    have := chi_val (Θ := Θ) χ b hχ htC (d := DihedralGroup.r 2) (c := 1) (σ := 1) hconf.t_eq
    rw [this, dihChar_r_two]
    simp
  have huC : u ∈ centralizer ({r} : Set G) := mem_cent_of_comm hur
  have hg1C : g1 ∈ centralizer ({r} : Set G) := mem_cent_of_comm hg1
  have hu1 : χ ⟨u, huC⟩ = 1 := by
    have : (⟨u, huC⟩ : ↥(centralizer ({r} : Set G))) =
        ⟨g1, hg1C⟩ * ⟨t, htC⟩ * ⟨g1, hg1C⟩⁻¹ := Subtype.ext hug1
    rw [this, chi_conj, hχt]
  have hχu := chi_val (Θ := Θ) χ b hχ huC (d := DihedralGroup.sr k) (c := 1) (σ := σ) hu.symm
  have hb : b = 1 := by
    rw [hχu, dihChar_sr_eq, mul_assoc, hpar, mul_one] at hu1
    exact hu1
  refine ⟨k, σ, hu, hσ2, hpar, ?_⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · left
    by_contra hσ1
    have hd : dihChar 1 (DihedralGroup.sr k) = 1 := by
      rw [hs, mul_one] at hpar
      exact hpar
    exact hinsp k σ hσ1 hσ2 hs (by rw [hb]; exact hd) ⟨g1, hg1, by rw [← hu]; exact hug1⟩
  · right
    exact hs

end Coords

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}
  {C : ECoord G}

section Std

variable {r0 : G} {Θ0 : HModel →* G}

theorem std_of_tconjW (hS : SignTheoremXW) (H : Sect7Hyps G L f s y S₀ n)
    (hc0 : FyConf (f ^ 2) r0 Θ0) (hs0 : FyCoset L f y Θ0) {r u : G} (hr : r * f ^ 2 = f ^ 2 * r)
    (hr3 : orderOf r = 3) (hut : u * f ^ 2 = f ^ 2 * u) (hur : u * r = r * u) (huu : u * u = 1)
    (hnf : u ∉ L ⊔ zpowers f) (hy : u ∈ L ⊔ zpowers y) (hconj : ∃ g : G, u = g * f ^ 2 * g⁻¹) :
    ∃ c : G, c * f ^ 2 = f ^ 2 * c ∧ u = c * Θ0 (DihedralGroup.sr 0, 1, 1) * c⁻¹ := by
  obtain ⟨m, hm_t, hconf, hcos⟩ := exists_conf_at H hc0 hs0 hr hr3
  obtain ⟨k, σ, hu, hσ2, hpar, hsig⟩ := hconf.sig_of_tconjW hS hcos hut hur huu hnf hy hconj
  obtain ⟨nn, hnn, hcl⟩ := hconf.ly_class hσ2 hpar hsig
  have hmt' : m⁻¹ * f ^ 2 = f ^ 2 * m⁻¹ := by
    calc m⁻¹ * f ^ 2 = m⁻¹ * f ^ 2 * m * m⁻¹ := by group
      _ = m⁻¹ * (f ^ 2 * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * f ^ 2) * m⁻¹ := by rw [hm_t]
      _ = f ^ 2 * m⁻¹ := by group
  refine ⟨nn * m⁻¹, ?_, ?_⟩
  · calc nn * m⁻¹ * f ^ 2 = nn * (m⁻¹ * f ^ 2) := by group
      _ = nn * (f ^ 2 * m⁻¹) := by rw [hmt']
      _ = (nn * f ^ 2) * m⁻¹ := by group
      _ = (f ^ 2 * nn) * m⁻¹ := by rw [hnn]
      _ = f ^ 2 * (nn * m⁻¹) := by group
  · rw [hu, hcl, confConj_apply]
    group

variable (h : Sect8Hyp C f n S₀) (hQ : Q0Facts) (hU : UFactsQ)
include h hQ hU

theorem same_cosetW (hS : SignTheoremXW) (H : Sect7Hyps G L f s y S₀ n)
    (hc0 : FyConf (f ^ 2) r0 Θ0) (hs0 : FyCoset L f y Θ0) {r e₀ u w₀ ρ : G}
    (hr : r * f ^ 2 = f ^ 2 * r) (hr3 : orderOf r = 3) (he₀ : e₀ ∈ C.E) (he₀r : r * e₀ = e₀ * r)
    (he1 : e₀ * e₀ ≠ 1) (he2 : e₀ * e₀ ≠ f ^ 2) (hu : SAU.IsW C f L y u) (huu : u * u = 1)
    (hur : r * u = u * r) (hut : ∃ g : G, u = g * f ^ 2 * g⁻¹) (hw : SAU.IsW C f L y w₀)
    (hww : w₀ * w₀ = 1) (hwr : r * w₀ = w₀ * r) (hρ3 : ρ ^ 3 = 1)
    (hρt : ρ * f ^ 2 = f ^ 2 * ρ) (hρn : ρ ∉ zpowers r) (hρr : ρ * r = r * ρ)
    (hρw : ρ * w₀ = w₀ * ρ) : ∃ e ∈ C.E, e * e = 1 ∧ w₀ = u * e := by
  obtain ⟨m, hm_t, hconf, hcos⟩ := exists_conf_at H hc0 hs0 hr hr3
  have hf2E : f ^ 2 ∈ C.E := pow_mem h.f_mem 2
  have he₀t : e₀ * f ^ 2 = f ^ 2 * e₀ := C.comm he₀ hf2E
  have hinv : ∀ {v : G}, SAU.IsW C f L y v → e₀ * v * e₀ = v := by
    intro v hv
    have h1 := hv.2.1 e₀ he₀
    have hve : v * e₀ = e₀⁻¹ * v := by
      calc v * e₀ = (v * e₀ * v⁻¹) * v := by group
        _ = e₀⁻¹ * v := by rw [h1]
    calc e₀ * v * e₀ = e₀ * (v * e₀) := by group
      _ = e₀ * (e₀⁻¹ * v) := by rw [hve]
      _ = v := by group
  obtain ⟨k₁, σ₁, hu_eq, hσ₁2, hpar₁, hsig₁⟩ := hconf.sig_of_tconjW hS hcos
    (hu.comm_t) hur.symm huu (hu.not_mem_LF H h) hu.2.2 hut
  have hσ₁ne : σ₁ ≠ 1 := fun h1 =>
    hconf.sig_ne_one (a := (DihedralGroup.sr k₁, 1, σ₁)) hu_eq (by simpa using h1) he₀t he₀r.symm
      (hinv hu) he1 he2
  have hs₁ : Equiv.Perm.sign σ₁ = -1 := hsig₁.resolve_left hσ₁ne
  obtain ⟨k₂, σ₂, hw_eq, hσ₂2, hpar₂⟩ := hconf.ly_coords hcos hw.comm_t hwr.symm hww
    (hw.not_mem_LF H h) hw.2.2
  have hsig₂ := hconf.sig_of_three hw_eq hσ₂2 hρ3 hρt hρr hρn hρw
  have hσ₂ne : σ₂ ≠ 1 := fun h1 =>
    hconf.sig_ne_one (a := (DihedralGroup.sr k₂, 1, σ₂)) hw_eq (by simpa using h1) he₀t he₀r.symm
      (hinv hw) he1 he2
  have hs₂ : Equiv.Perm.sign σ₂ = -1 := hsig₂.resolve_left hσ₂ne
  have hxE : u⁻¹ * w₀ ∈ C.E := SAU.IsW.inv_mul_mem_E h hu hw
  have hxH : u⁻¹ * w₀ ∈ L ⊔ zpowers y :=
    (L ⊔ zpowers y).mul_mem ((L ⊔ zpowers y).inv_mem hu.2.2) hw.2.2
  have hxE1 := Sect8Hyp.mem_E1sub_of_mem_H1 h hQ H hU hxE hxH
  have hxt : (u⁻¹ * w₀) * (u⁻¹ * w₀) ≠ f ^ 2 := by
    intro h1
    have h2 := hxE1.2
    rw [h1] at h2
    have h3 := ((C.mem_Fsub hQ).1 h2).2
    rw [h.vec_f2 hQ] at h3
    exact hU.tnot h3
  have hx4 : (u⁻¹ * w₀) ^ 4 = 1 := C.pow_four hxE
  have hxx := hconf.sq_eq_one_of_odd (a := (DihedralGroup.sr k₁, 1, σ₁))
    (b := (DihedralGroup.sr k₂, 1, σ₂)) hu_eq hw_eq rfl rfl hs₁ hs₂ hx4 hxt
  exact ⟨u⁻¹ * w₀, hxE, hxx, by group⟩

end Std

section Cl16


theorem cl16OfClass_of_modelZW (hS : SignTheoremXW)
    (hF : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G)
      (n : G), Sect7Hyps G L f s y S₀ n → FyModelFacts L f y) (hZ : ModelZ) :
    ∀ hQ : Q0Facts, Cl16OfClass hQ := by
  intro hQ G _ _ L f s y S₀ n H C h T K hT w hwT hwE hwc hwy ⟨m₁, hm₁c, hwy'⟩
  obtain ⟨sl, hUS, hSl⟩ := exists_UFactsOf H hQ h
  have hUQ : UFactsQ := Certificates.certificate26820
  have hf2E : f ^ 2 ∈ C.E := pow_mem h.f_mem 2
  have hff : f ^ 2 * f ^ 2 = 1 := by
    rw [← pow_add]; exact H.f_pow_four
  have hwn : w ∈ normalizer (C.E : Set G) := hT.sylow.mem_normalizer_E hwT
  have hwt : w * f ^ 2 = f ^ 2 * w := hwc _ hf2E hff
  have hmat := h.mat_neg_of_comm hUS hwn (hSl w hwn) hwE hwc
  have hwW : SAU.IsW C f L y w :=
    ⟨SAU.mem_M0.2 ⟨hwt, hwn⟩, fun e he => h.inv_of_mat_neg hwn hmat he, hwy⟩
  obtain ⟨gy, hgy⟩ := H.y_conj
  have hwconj : ∃ g : G, w = g * f ^ 2 * g⁻¹ := ⟨m₁ * gy, by rw [hwy', hgy]; group⟩
  have hww : w * w = 1 := by
    obtain ⟨g, hg⟩ := hwconj
    rw [hg]
    calc g * f ^ 2 * g⁻¹ * (g * f ^ 2 * g⁻¹) = g * (f ^ 2 * f ^ 2) * g⁻¹ := by group
      _ = 1 := by rw [hff]; group
  obtain ⟨r, v₀, w₀, ρ, e₀, hr, hr3, hr1, hv, hv7, hvfix, he₀, he₀r, he1, he2, hw₀, hw₀w₀, hcl,
    hrw₀, hρ3, hρt, hρn, hρr, hρw₀⟩ := hZ G L f s y S₀ n H C h
  obtain ⟨m, hm, hrfix⟩ := SAU.exists_fixed_conj h hQ hUQ H hwW hr hr3 hv hv7 hvfix
  have huW : SAU.IsW C f L y (m * w * m⁻¹) := hwW.conj H hm
  have huu : (m * w * m⁻¹) * (m * w * m⁻¹) = 1 := by
    calc (m * w * m⁻¹) * (m * w * m⁻¹) = m * (w * w) * m⁻¹ := by group
      _ = 1 := by rw [hww]; group
  have hut : ∃ g : G, m * w * m⁻¹ = g * f ^ 2 * g⁻¹ := by
    obtain ⟨g, hg⟩ := hwconj
    exact ⟨m * g, by rw [hg]; group⟩
  have hrord : orderOf r = 3 := orderOf_eq_prime hr3 hr1
  obtain ⟨r0, Θ0, hc0, hs0⟩ := (hF G L f s y S₀ n H).conf
  obtain ⟨e, heE, hee, hw₀u⟩ := same_cosetW h hQ hUQ hS H hc0 hs0 (SAU.mem_M0.1 hr).1 hrord he₀
    he₀r he1 he2 huW huu hrfix hut hw₀ hw₀w₀ hrw₀ hρ3 hρt hρn hρr hρw₀
  exact Cl16.of_conj hm (Cl16.of_coset hcl ⟨heE, hee⟩ hw₀u)

theorem sect8InputK_of_modelZW (hS : SignTheoremXW)
    (hF : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G)
      (n : G), Sect7Hyps G L f s y S₀ n → FyModelFacts L f y) (hZ : ModelZ) :
    ∀ hQ : Q0Facts, Sect8InputK hQ := by
  intro hQ G _ _ L f s y S₀ n H C h T K hT
  have hf2E : f ^ 2 ∈ C.E := pow_mem h.f_mem 2
  have hff : f ^ 2 * f ^ 2 = 1 := by
    rw [← pow_add]; exact H.f_pow_four
  obtain ⟨r, v₀, w₀, ρ, e₀, hr, hr3, hr1, hv, hv7, hvfix, he₀, he₀r, he1, he2, hw₀, hw₀w₀, hcl,
    hrw₀, hρ3, hρt, hρn, hρr, hρw₀⟩ := hZ G L f s y S₀ n H C h
  have hrord : orderOf r = 3 := orderOf_eq_prime hr3 hr1
  obtain ⟨r0, Θ0, hc0, hs0⟩ := (hF G L f s y S₀ n H).conf
  have hyN : y ∈ centralizer ({f ^ 2} : Set G) := by
    rw [H.cent_eq]
    exact Subgroup.mem_sup_right (mem_zpowers y)
  have hyt : y * f ^ 2 = f ^ 2 * y := mem_centralizer_singleton_iff.1 hyN
  obtain ⟨ry, hryL, hry3, hryy⟩ := (hF G L f s y S₀ n H).outer3 y H.yy hyt H.y_not
  have hryt : ry * f ^ 2 = f ^ 2 * ry := H.comm_t hryL
  obtain ⟨c₁, hc₁t, hy⟩ := std_of_tconjW hS H hc0 hs0 hryt hry3 hyt hryy.symm H.yy H.y_not
    (Subgroup.mem_sup_right (mem_zpowers y)) H.y_conj
  obtain ⟨c₂, hc₂t, hw⟩ := std_of_three H hc0 hs0 (SAU.mem_M0.1 hr).1 hrord hw₀.comm_t hrw₀.symm
    hw₀w₀ (hw₀.not_mem_LF H h) hw₀.2.2 hρ3 hρt hρr hρn hρw₀
  have hrel : w₀ = (c₂ * c₁⁻¹) * y * (c₂ * c₁⁻¹)⁻¹ := by
    rw [hw, hy]
    group
  obtain ⟨gy, hgy⟩ := H.y_conj
  have hnegS : (-1 : M4) ∈ shatList := by
    set_option maxRecDepth 100000 in decide
  obtain ⟨x₁, hx₁S, hx₁m⟩ := h.actS' _ hnegS
  have hx₁n := h.S₀_norm _ hx₁S
  have hw₀n := hw₀.normalizes
  have hmatw₀ : C.mat w₀ = -1 := ECoord.mat_eq_neg_one_of_inv hw₀n hw₀.2.1
  have hx₁inv : C.mat x₁⁻¹ = -1 := by
    calc C.mat x₁⁻¹ = C.mat x₁⁻¹ * (C.mat x₁ * C.mat x₁) := by rw [hx₁m]; simp
      _ = (C.mat x₁⁻¹ * C.mat x₁) * C.mat x₁ := by rw [mul_assoc]
      _ = -1 := by rw [ECoord.mat_inv_mul hx₁n, one_mul, hx₁m]
  have hq : C.mat (w₀ * x₁⁻¹) = 1 := by
    rw [C.mat_mul hw₀n (inv_mem hx₁n), hmatw₀, hx₁inv]
    simp
  have hqE : w₀ * x₁⁻¹ ∈ C.E := h.mem_E_of_mat_eq_one (mul_mem hw₀n (inv_mem hx₁n)) hq
  have hw₀S : w₀ ∈ S₀ := by
    have : w₀ = (w₀ * x₁⁻¹) * x₁ := by group
    rw [this]
    exact S₀.mul_mem (h.E_le hqE) hx₁S
  refine ⟨w₀, hT.S₀_le hw₀S, ?_, ?_, ⟨(c₂ * c₁⁻¹ * gy)⁻¹, ?_⟩⟩
  · intro hE
    have h1 := hw₀.2.1 f h.f_mem
    have hc := C.comm hE h.f_mem
    rw [hc] at h1
    have h2 : f = f⁻¹ := by
      calc f = f * w₀ * w₀⁻¹ := by group
        _ = f⁻¹ := h1
    have h3 : f ^ 2 = 1 := by
      calc f ^ 2 = f * f := sq f
        _ = f * f⁻¹ := by rw [← h2]
        _ = 1 := by group
    have := orderOf_dvd_of_pow_eq_one h3
    rw [H.four.order] at this
    omega
  · intro a ha haa
    have h1 := hw₀.2.1 a ha
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    rw [hainv] at h1
    calc w₀ * a = (w₀ * a * w₀⁻¹) * w₀ := by group
      _ = a * w₀ := by rw [h1]
  · rw [hrel, hgy]
    group

end Cl16

end CFSG.EvenSporadicStandard.TwoHS
