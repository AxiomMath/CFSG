module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Gen

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

theorem mul_mul_self_of_commute {X : Type*} [Group X] {a b : X} (hab : a * b = b * a) :
    (a * b) * (a * b) = (a * a) * (b * b) := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

theorem DBar.conj_mul_eq (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {d e : NBar (sec4W Ω S)}
    (hd : d ∈ DBar Ω (sec4W Ω S)) (he : e ∈ DBar Ω (sec4W Ω S)) (hne : e * d ≠ d * e) :
    (e * d)⁻¹ * d * (e * d) = e := by
  have hd2 := DBar.mul_self H.hΩ hS hd
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (DBar.mul_self H.hΩ hS he)
  have hbr := DBar.braid H hS he hd hne
  calc (e * d)⁻¹ * d * (e * d) = d * (e * d * e) * d := by
        rw [mul_inv_rev, hdinv, heinv]; group
    _ = (d * d) * e * (d * d) := by rw [hbr]; group
    _ = e := by rw [hd2, one_mul, mul_one]

theorem inv_mul_conj_inv_mul_conj (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    {P V₀ T V : Subgroup G} {d₀ g : NBar (sec4W Ω S)} {t₀ t : normalizer (sec4W Ω S : Set G)}
    (h₀ : ReflData Ω (sec4W Ω S) d₀ P V₀ t₀) (h : ReflData Ω (sec4W Ω S) g T V t)
    (hne : g * d₀ ≠ d₀ * g) {v : G} (hv : v ∈ V₀) :
    (v⁻¹ * ((t : G)⁻¹ * v * t))⁻¹ * ((t₀ : G)⁻¹ * (v⁻¹ * ((t : G)⁻¹ * v * t)) * t₀) = v := by
  have hΩ := H.hΩ
  obtain ⟨c, hc⟩ : ∃ c, c = v⁻¹ * ((t : G)⁻¹ * v * t) := ⟨_, rfl⟩
  rw [← hc]
  have hvW : v ∈ sec4W Ω S := h₀.rot_le hΩ hS hv
  have hcV : c ∈ V := hc ▸ h.inv_mul_conj_mem H hS hvW
  have hcW : c ∈ sec4W Ω S := h.rot_le hΩ hS hcV
  obtain ⟨c₀, hc₀⟩ : ∃ y, y = c⁻¹ * ((t₀ : G)⁻¹ * c * t₀) := ⟨_, rfl⟩
  rw [← hc₀]
  have hc₀V : c₀ ∈ V₀ := hc₀ ▸ h₀.inv_mul_conj_mem H hS hcW
  have hP : P ∈ DSet Ω (sec4W Ω S) := h₀.mem
  have hPy : AschbacherTightEmbedding.rightConjugate P ((t * t₀ : normalizer _) : G) ∈
      DSet Ω (sec4W Ω S) := DSet.rightConjugate_mem hΩ hP (t * t₀).2
  have hPybar := h₀.bar.rightConjugate (t * t₀)
  rw [QuotientGroup.mk_mul, h.eq, h₀.eq,
    DBar.conj_mul_eq H hS h₀.mem_dBar h.mem_dBar hne] at hPybar
  have hrot := DSet.rot_eq_of_bar_eq H hS hPy h.mem (h₀.rot.rightConjugate _) h.rot hPybar h.bar
  have hmem : ((t * t₀ : normalizer _) : G)⁻¹ * v * ((t * t₀ : normalizer _) : G) ∈ V := by
    rw [← hrot, mem_rightConjugate_iff]
    have e : ((t * t₀ : normalizer _) : G) * (((t * t₀ : normalizer _) : G)⁻¹ * v *
        ((t * t₀ : normalizer _) : G)) * ((t * t₀ : normalizer _) : G)⁻¹ = v := by group
    rw [e]
    exact hv
  have e1 : ((t * t₀ : normalizer _) : G)⁻¹ * v * ((t * t₀ : normalizer _) : G) =
      ((t₀ : G)⁻¹ * v * t₀) * ((t₀ : G)⁻¹ * c * t₀) := by
    rw [hc]
    simp only [coe_mul]
    group
  have hv₀ : (t₀ : G)⁻¹ * v * t₀ = v⁻¹ := h₀.conj_rot hv
  have hct : (t₀ : G)⁻¹ * c * t₀ = c * c₀ := by rw [hc₀]; group
  rw [e1, hv₀, hct] at hmem
  have hcomm : c * (v⁻¹ * c₀) = v⁻¹ * (c * c₀) := by
    rw [← mul_assoc, sec4W_comm hΩ hS hcW (inv_mem hvW), mul_assoc]
  have hmem' : v⁻¹ * c₀ ∈ V := by
    have : v⁻¹ * c₀ = c⁻¹ * (v⁻¹ * (c * c₀)) := by rw [← hcomm]; group
    rw [this]
    exact mul_mem (inv_mem hcV) hmem
  have hmem₀ : v⁻¹ * c₀ ∈ V₀ := mul_mem (inv_mem hv) hc₀V
  obtain ⟨⟨J₀, hJ₀, hPJ₀⟩, hPW⟩ := hP
  obtain ⟨⟨J, hJ, hTJ⟩, hTW⟩ := h.mem
  have hJJ : J₀ ≠ J := by
    rintro rfl
    apply hne
    rw [bar_eq_of_same H hS hJ₀ hPJ₀ hTJ hPW hTW h₀.bar h.bar]
  have hbot := Assumption41.inf_eq_bot hΩ hJ₀ hJ hJJ (h₀.rot.isPGroup.to_le h₀.rot.le)
    (h₀.rot.le.trans hPJ₀.le) (h.rot.le.trans hTJ.le)
  have h1 : v⁻¹ * c₀ = 1 := by
    have := mem_inf.mpr ⟨hmem₀, hmem'⟩
    rwa [hbot, mem_bot] at this
  calc c₀ = v * (v⁻¹ * c₀) := by group
    _ = v := by rw [h1, mul_one]

theorem ReflData.rot_inf_eq_bot {T V T' V' : Subgroup G} {g g' : NBar (sec4W Ω S)}
    {t t' : normalizer (sec4W Ω S : Set G)} (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (h : ReflData Ω (sec4W Ω S) g T V t) (h' : ReflData Ω (sec4W Ω S) g' T' V' t')
    (hne : g ≠ g') : V ⊓ V' = ⊥ := by
  obtain ⟨⟨J, hJ, hTJ⟩, hTW⟩ := h.mem
  obtain ⟨⟨J', hJ', hT'J'⟩, hT'W⟩ := h'.mem
  have hJJ : J ≠ J' := by
    rintro rfl
    exact hne (bar_eq_of_same H hS hJ hTJ hT'J' hTW hT'W h.bar h'.bar)
  exact Assumption41.inf_eq_bot H.hΩ hJ hJ' hJJ (h.rot.isPGroup.to_le h.rot.le)
    (h.rot.le.trans hTJ.le) (h'.rot.le.trans hT'J'.le)

theorem indep_three (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {P V₀ R U Tb Vb : Subgroup G}
    {d₀ r b : NBar (sec4W Ω S)} {t₀ tr tb : normalizer (sec4W Ω S : Set G)}
    (h₀ : ReflData Ω (sec4W Ω S) d₀ P V₀ t₀) (hr : ReflData Ω (sec4W Ω S) r R U tr)
    (hb : ReflData Ω (sec4W Ω S) b Tb Vb tb) (hrd : r * d₀ ≠ d₀ * r) (hbd : b * d₀ ≠ d₀ * b)
    (hbr : b * r = r * b) (hbne : b ≠ r) {z₀ z zb : G} (hz₀ : IsZOf P z₀) (hz : IsZOf R z)
    (hzb : IsZOf Tb zb) {x u v : G} (hx : x ∈ V₀) (hu : u ∈ U) (hv : v ∈ Vb)
    (h : x * u * v = 1) : x = 1 ∧ u = 1 ∧ v = 1 := by
  have hΩ := H.hΩ
  have hxW : x ∈ sec4W Ω S := h₀.rot_le hΩ hS hx
  have huW : u ∈ sec4W Ω S := hr.rot_le hΩ hS hu
  have hvW : v ∈ sec4W Ω S := hb.rot_le hΩ hS hv
  have hW := fun {a c : G} (ha : a ∈ sec4W Ω S) (hc : c ∈ sec4W Ω S) => sec4W_comm hΩ hS ha hc
  obtain ⟨cr, hcr⟩ : ∃ y, y = x⁻¹ * ((tr : G)⁻¹ * x * tr) := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ y, y = x⁻¹ * ((tb : G)⁻¹ * x * tb) := ⟨_, rfl⟩
  obtain ⟨cu, hcu⟩ : ∃ y, y = u⁻¹ * ((t₀ : G)⁻¹ * u * t₀) := ⟨_, rfl⟩
  obtain ⟨cv, hcv⟩ : ∃ y, y = v⁻¹ * ((t₀ : G)⁻¹ * v * t₀) := ⟨_, rfl⟩
  have hcrU : cr ∈ U := hcr ▸ hr.inv_mul_conj_mem H hS hxW
  have hcbV : cb ∈ Vb := hcb ▸ hb.inv_mul_conj_mem H hS hxW
  have hcu₀ : cu ∈ V₀ := hcu ▸ h₀.inv_mul_conj_mem H hS huW
  have hcv₀ : cv ∈ V₀ := hcv ▸ h₀.inv_mul_conj_mem H hS hvW
  have hcrW := hr.rot_le hΩ hS hcrU
  have hcbW := hb.rot_le hΩ hS hcbV
  have hcuW := h₀.rot_le hΩ hS hcu₀
  have hcvW := h₀.rot_le hΩ hS hcv₀
  have hconj : ∀ y : G, y⁻¹ * (x * u * v) * y = (y⁻¹ * x * y) * (y⁻¹ * u * y) * (y⁻¹ * v * y) :=
    fun y => by group
  have hone : ∀ y : G, y⁻¹ * (x * u * v) * y = 1 := fun y => by rw [h]; group
  have hrv : (tr : G)⁻¹ * v * tr = v :=
    ReflData.conj_eq_of_commute (hr.commute hb H hS hbr.symm hbne.symm hv)
  have hcru : cr = u * u := by
    have h1 := hone tr
    rw [hconj, show (tr : G)⁻¹ * x * tr = x * cr by rw [hcr]; group, hr.conj_rot hu, hrv] at h1
    have h2 : x * cr * u⁻¹ * v = x * u * v := h1.trans h.symm
    have h3 : cr * u⁻¹ = u := mul_left_cancel (mul_right_cancel (by
      calc x * (cr * u⁻¹) * v = x * cr * u⁻¹ * v := by group
        _ = x * u * v := h2))
    calc cr = cr * u⁻¹ * u := by group
      _ = u * u := by rw [h3]
  have hbu : (tb : G)⁻¹ * u * tb = u :=
    ReflData.conj_eq_of_commute (hb.commute hr H hS hbr hbne hu)
  have hcbv : cb = v * v := by
    have h1 := hone tb
    rw [hconj, show (tb : G)⁻¹ * x * tb = x * cb by rw [hcb]; group, hbu, hb.conj_rot hv] at h1
    have h2 : x * cb * u * v⁻¹ = x * u * v := h1.trans h.symm
    have h3 : cb * v⁻¹ = v := by
      have h4 : x * u * (cb * v⁻¹) = x * u * v := by
        calc x * u * (cb * v⁻¹) = x * (u * cb) * v⁻¹ := by group
          _ = x * (cb * u) * v⁻¹ := by rw [hW huW hcbW]
          _ = x * u * v := by rw [← h2]; group
      exact mul_left_cancel h4
    calc cb = cb * v⁻¹ * v := by group
      _ = v * v := by rw [h3]
  have hcuv : cu * cv = x * x := by
    have h1 := hone t₀
    rw [hconj, h₀.conj_rot hx, show (t₀ : G)⁻¹ * u * t₀ = u * cu by rw [hcu]; group,
      show (t₀ : G)⁻¹ * v * t₀ = v * cv by rw [hcv]; group] at h1
    have huv : u * v = x⁻¹ := by
      calc u * v = x⁻¹ * (x * u * v) := by group
        _ = x⁻¹ := by rw [h, mul_one]
    have h2 : x⁻¹ * (u * v) * (cu * cv) = 1 := by
      calc x⁻¹ * (u * v) * (cu * cv) = x⁻¹ * u * (v * cu) * cv := by group
        _ = x⁻¹ * u * (cu * v) * cv := by rw [hW hvW hcuW]
        _ = 1 := by rw [← h1]; group
    rw [huv] at h2
    calc cu * cv = (x⁻¹ * x⁻¹)⁻¹ * (x⁻¹ * x⁻¹ * (cu * cv)) := by group
      _ = x * x := by rw [h2, mul_one, mul_inv_rev, inv_inv]
  have hnr := inv_mul_conj_inv_mul_conj H hS h₀ hr hrd hx
  have hnb := inv_mul_conj_inv_mul_conj H hS h₀ hb hbd hx
  rw [← hcr, hcru] at hnr
  rw [← hcb, hcbv] at hnb
  have hcu2 : cu * cu = x := by
    rw [← hnr, hcu]
    exact (inv_mul_conj_mul hΩ hS t₀.2 huW huW).symm
  have hcv2 : cv * cv = x := by
    rw [← hnb, hcv]
    exact (inv_mul_conj_mul hΩ hS t₀.2 hvW hvW).symm
  have hxx : x * x = 1 := by
    have h1 := mul_mul_self_of_commute (hW hcuW hcvW)
    rw [hcuv, hcu2, hcv2] at h1
    have h2 : (x * x) * (x * x) = (x * x) * 1 := by rw [mul_one, h1]
    exact mul_left_cancel h2
  rcases (hz₀.mem_rot h₀.rot).2 x hx hxx with hx1 | hx1
  ·
    have huv : u = v⁻¹ := by
      rw [hx1, one_mul] at h
      exact eq_inv_of_mul_eq_one_left h
    have hbot := ReflData.rot_inf_eq_bot H hS hr hb hbne.symm
    have hu1 : u = 1 := by
      have := mem_inf.mpr ⟨hu, huv ▸ inv_mem hv⟩
      rwa [hbot, mem_bot] at this
    refine ⟨hx1, hu1, ?_⟩
    rw [hu1] at huv
    rw [← inv_inv v, ← huv, inv_one]
  ·
    exfalso
    have hz₀r : (tr : G)⁻¹ * z₀ * tr = z₀ * z :=
      conj_z_of_not_commute H hS hr.mem h₀.mem hr.rot hz hz₀ hr.bar h₀.bar hrd hr.memT
        hr.not_mem
    have hz₀b : (tb : G)⁻¹ * z₀ * tb = z₀ * zb :=
      conj_z_of_not_commute H hS hb.mem h₀.mem hb.rot hzb hz₀ hb.bar h₀.bar hbd hb.memT
        hb.not_mem
    have huu : u * u = z := by rw [← hcru, hcr, hx1, hz₀r]; group
    have hvv : v * v = zb := by rw [← hcbv, hcb, hx1, hz₀b]; group
    have h1 := congrArg (fun y => y * y) h
    simp only [one_mul] at h1
    have h2 : (x * u * v) * (x * u * v) = (x * x) * (u * u) * (v * v) := by
      rw [mul_mul_self_of_commute (hW (mul_mem hxW huW) hvW),
        mul_mul_self_of_commute (hW hxW huW)]
    rw [h2, hx1, hz₀.mul_self, one_mul, huu, hvv] at h1
    have hzzb : z = zb := by
      rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hzb.mul_self]
    apply hbne
    exact DSet.bar_eq_of_zOf_eq H hS hb.mem hr.mem (hzzb ▸ hzb) hz hb.bar hr.bar

theorem indep_four (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    {P V₀ R U Tb Vb Tc Vc Tτ Vτ : Subgroup G} {d₀ r b c τ : NBar (sec4W Ω S)}
    {tr tb tc tτ : normalizer (sec4W Ω S : Set G)} (hP : P ∈ DSet Ω (sec4W Ω S))
    (hV₀ : IsDihedralRot V₀ P) (hd₀ : IsBarOf (sec4W Ω S) P d₀)
    (hr : ReflData Ω (sec4W Ω S) r R U tr) (hb : ReflData Ω (sec4W Ω S) b Tb Vb tb)
    (hc : ReflData Ω (sec4W Ω S) c Tc Vc tc) (hτ : ReflData Ω (sec4W Ω S) τ Tτ Vτ tτ)
    (hτd : τ * d₀ ≠ d₀ * τ) (hrb : r * b = b * r) (hrc : r * c = c * r) (hbc : b * c = c * b)
    (hrτ : r * τ = τ * r) (hbτ : b * τ = τ * b) (hcτ : c * τ = τ * c) (hrb' : r ≠ b)
    (hrc' : r ≠ c) (hbc' : b ≠ c) (hrτ' : r ≠ τ) (hbτ' : b ≠ τ) (hcτ' : c ≠ τ)
    {z zb zc zτ : G} (hz : IsZOf R z) (hzb : IsZOf Tb zb) (hzc : IsZOf Tc zc)
    (hzτ : IsZOf Tτ zτ) (hrel : z * zb * zc * zτ = 1) {x u v w : G} (hx : x ∈ V₀)
    (hu : u ∈ U) (hv : v ∈ Vb) (hw : w ∈ Vc) (h : x * u * v * w = 1) :
    x = 1 ∧ u = 1 ∧ v = 1 ∧ w = 1 := by
  have hΩ := H.hΩ
  have hxW : x ∈ sec4W Ω S := DSet.rot_le hΩ hS hP hV₀ hx
  have hconj : ∀ y : G, y⁻¹ * (x * u * v * w) * y =
      (y⁻¹ * x * y) * (y⁻¹ * u * y) * (y⁻¹ * v * y) * (y⁻¹ * w * y) := fun y => by group
  have hone : ∀ y : G, y⁻¹ * (x * u * v * w) * y = 1 := fun y => by rw [h]; group
  have hcen : ∀ {g g' : NBar (sec4W Ω S)} {T V T' V' : Subgroup G}
      {t t' : normalizer (sec4W Ω S : Set G)}, ReflData Ω (sec4W Ω S) g T V t →
      ReflData Ω (sec4W Ω S) g' T' V' t' → g * g' = g' * g → g ≠ g' → ∀ y ∈ V',
        (t : G)⁻¹ * y * t = y := fun h h' hgg hne y hy =>
    ReflData.conj_eq_of_commute (h.commute h' H hS hgg hne hy)
  have hx1 : x = 1 := by
    have h1 := hone tτ
    rw [hconj, hcen hτ hr hrτ.symm hrτ'.symm u hu, hcen hτ hb hbτ.symm hbτ'.symm v hv,
      hcen hτ hc hcτ.symm hcτ'.symm w hw] at h1
    have h2 : (tτ : G)⁻¹ * x * tτ = x :=
      mul_right_cancel (mul_right_cancel (mul_right_cancel (h1.trans h.symm)))
    obtain ⟨ρ, hρ, hρo⟩ := hV₀.exists_gen
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hρ ▸ hx : x ∈ zpowers ρ)
    obtain ⟨-, hoc⟩ := ReflData.zpowers_eq H hS hP hV₀ hd₀ hτ hτd hρ hρo
    have hρW : ρ ∈ sec4W Ω S := DSet.rot_le hΩ hS hP hV₀ (hρ ▸ mem_zpowers ρ)
    have h3 := inv_mul_conj_zpow hΩ hS tτ.2 hρW k
    rw [h2, inv_mul_cancel] at h3
    have hdvd : (orderOf (ρ⁻¹ * ((tτ : G)⁻¹ * ρ * tτ)) : ℤ) ∣ k :=
      orderOf_dvd_iff_zpow_eq_one.mpr h3.symm
    rw [hoc, DSet.card_rot_eq hΩ hτ.mem hP hτ.rot hV₀, ← hρo] at hdvd
    exact orderOf_dvd_iff_zpow_eq_one.mp hdvd
  rw [hx1, one_mul] at h
  refine ⟨hx1, ?_⟩
  have h' : ∀ y : G, y⁻¹ * (u * v * w) * y = (y⁻¹ * u * y) * (y⁻¹ * v * y) * (y⁻¹ * w * y) :=
    fun y => by group
  have hone' : ∀ y : G, y⁻¹ * (u * v * w) * y = 1 := fun y => by rw [h]; group
  have hu2 : u = u⁻¹ := by
    have h1 := hone' tr
    rw [h', hr.conj_rot hu, hcen hr hb hrb hrb' v hv, hcen hr hc hrc hrc' w hw] at h1
    exact (mul_right_cancel (mul_right_cancel (h1.trans h.symm))).symm
  have hv2 : v = v⁻¹ := by
    have h1 := hone' tb
    rw [h', hcen hb hr hrb.symm hrb'.symm u hu, hb.conj_rot hv, hcen hb hc hbc hbc' w hw] at h1
    exact (mul_left_cancel (mul_right_cancel (h1.trans h.symm))).symm
  have hw2 : w = w⁻¹ := by
    have h1 := hone' tc
    rw [h', hcen hc hr hrc.symm hrc'.symm u hu, hcen hc hb hbc.symm hbc'.symm v hv,
      hc.conj_rot hw] at h1
    exact (mul_left_cancel (h1.trans h.symm)).symm
  have hsq : ∀ {y : G}, y = y⁻¹ → y * y = 1 := fun hy => by
    calc _ = _ * _⁻¹ := by rw [← hy]
      _ = 1 := mul_inv_cancel _
  have hzne : ∀ {T T' : Subgroup G} {g g' : NBar (sec4W Ω S)} {V V' : Subgroup G}
      {t t' : normalizer (sec4W Ω S : Set G)} {y y' : G}, ReflData Ω (sec4W Ω S) g T V t →
      ReflData Ω (sec4W Ω S) g' T' V' t' → IsZOf T y → IsZOf T' y' → g ≠ g' → y * y' ≠ 1 :=
    fun h h' hy hy' hne hyy => hne (DSet.bar_eq_of_zOf_eq H hS h.mem h'.mem hy
      (by rwa [eq_inv_of_mul_eq_one_left hyy, inv_eq_of_mul_eq_one_right hy'.mul_self]) h.bar
      h'.bar)
  rcases (hz.mem_rot hr.rot).2 u hu (hsq hu2) with hu1 | hu1 <;>
    rcases (hzb.mem_rot hb.rot).2 v hv (hsq hv2) with hv1 | hv1 <;>
    rcases (hzc.mem_rot hc.rot).2 w hw (hsq hw2) with hw1 | hw1 <;>
    rw [hu1, hv1, hw1] at h <;> try simp only [one_mul, mul_one] at h
  · exact ⟨hu1, hv1, hw1⟩
  · exact absurd h hzc.ne_one
  · exact absurd h hzb.ne_one
  · exact absurd h (hzne hb hc hzb hzc hbc')
  · exact absurd h hz.ne_one
  · exact absurd h (hzne hr hc hz hzc hrc')
  · exact absurd h (hzne hr hb hz hzb hrb')
  · exfalso
    rw [h, one_mul] at hrel
    exact hzτ.ne_one hrel

theorem omegaOne_of_two (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤) {T₀ V₀ R U : Subgroup G}
    (hV₀ : IsDihedralRot V₀ T₀) (hU : IsDihedralRot U R) (hV₀W : V₀ ≤ sec4W Ω S)
    (hUW : U ≤ sec4W Ω S) (hbot : V₀ ⊓ U = ⊥) (hgen : sec4W Ω S ≤ V₀ ⊔ U) {z₀ z : G}
    (hz₀ : IsZOf T₀ z₀) (hz : IsZOf R z) {w : G} (hw : w ∈ sec4W Ω S) (hww : w * w = 1) :
    ∃ x u : G, (x = 1 ∨ x = z₀) ∧ (u = 1 ∨ u = z) ∧ w = x * u := by
  have hW := fun {a c : G} (ha : a ∈ sec4W Ω S) (hc : c ∈ sec4W Ω S) => sec4W_comm hΩ hS ha hc
  obtain ⟨x, hx, u, hu, rfl⟩ :=
    (mem_sup_iff_of_commute fun a ha b hb => hW (hV₀W ha) (hUW hb)).mp (hgen hw)
  rw [mul_mul_self_of_commute (hW (hV₀W hx) (hUW hu))] at hww
  have hxx : x * x = 1 := by
    have h1 : x * x = (u * u)⁻¹ := eq_inv_of_mul_eq_one_left hww
    have := mem_inf.mpr ⟨mul_mem hx hx, h1 ▸ inv_mem (mul_mem hu hu)⟩
    rwa [hbot, mem_bot] at this
  rw [hxx, one_mul] at hww
  exact ⟨x, u, (hz₀.mem_rot hV₀).2 x hx hxx, (hz.mem_rot hU).2 u hu hww, rfl⟩

theorem omegaOne_of_three (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤)
    {T₀ V₀ R U Tb Vb : Subgroup G} (hV₀ : IsDihedralRot V₀ T₀) (hU : IsDihedralRot U R)
    (hVb : IsDihedralRot Vb Tb) (hV₀W : V₀ ≤ sec4W Ω S) (hUW : U ≤ sec4W Ω S)
    (hVbW : Vb ≤ sec4W Ω S) (hgen : sec4W Ω S ≤ V₀ ⊔ U ⊔ Vb)
    (hind : ∀ x ∈ V₀, ∀ u ∈ U, ∀ v ∈ Vb, x * u * v = 1 → x = 1 ∧ u = 1 ∧ v = 1)
    {z₀ z zb : G} (hz₀ : IsZOf T₀ z₀) (hz : IsZOf R z) (hzb : IsZOf Tb zb) {w : G}
    (hw : w ∈ sec4W Ω S) (hww : w * w = 1) :
    ∃ x u v : G, (x = 1 ∨ x = z₀) ∧ (u = 1 ∨ u = z) ∧ (v = 1 ∨ v = zb) ∧ w = x * u * v := by
  have hW := fun {a c : G} (ha : a ∈ sec4W Ω S) (hc : c ∈ sec4W Ω S) => sec4W_comm hΩ hS ha hc
  have h01 : V₀ ⊔ U ≤ sec4W Ω S := sup_le hV₀W hUW
  obtain ⟨y, hy, v, hv, rfl⟩ :=
    (mem_sup_iff_of_commute fun a ha b hb => hW (h01 ha) (hVbW hb)).mp (hgen hw)
  obtain ⟨x, hx, u, hu, rfl⟩ :=
    (mem_sup_iff_of_commute fun a ha b hb => hW (hV₀W ha) (hUW hb)).mp hy
  rw [mul_mul_self_of_commute (hW (h01 hy) (hVbW hv)),
    mul_mul_self_of_commute (hW (hV₀W hx) (hUW hu))] at hww
  obtain ⟨h1, h2, h3⟩ := hind _ (mul_mem hx hx) _ (mul_mem hu hu) _ (mul_mem hv hv) hww
  exact ⟨x, u, v, (hz₀.mem_rot hV₀).2 x hx h1, (hz.mem_rot hU).2 u hu h2,
    (hzb.mem_rot hVb).2 v hv h3, rfl⟩

theorem omegaOne_of_four (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤)
    {T₀ V₀ R U Tb Vb Tc Vc : Subgroup G} (hV₀ : IsDihedralRot V₀ T₀) (hU : IsDihedralRot U R)
    (hVb : IsDihedralRot Vb Tb) (hVc : IsDihedralRot Vc Tc) (hV₀W : V₀ ≤ sec4W Ω S)
    (hUW : U ≤ sec4W Ω S) (hVbW : Vb ≤ sec4W Ω S) (hVcW : Vc ≤ sec4W Ω S)
    (hgen : sec4W Ω S ≤ V₀ ⊔ U ⊔ Vb ⊔ Vc)
    (hind : ∀ x ∈ V₀, ∀ u ∈ U, ∀ v ∈ Vb, ∀ y ∈ Vc, x * u * v * y = 1 →
      x = 1 ∧ u = 1 ∧ v = 1 ∧ y = 1)
    {z₀ z zb zc : G} (hz₀ : IsZOf T₀ z₀) (hz : IsZOf R z) (hzb : IsZOf Tb zb)
    (hzc : IsZOf Tc zc) {w : G} (hw : w ∈ sec4W Ω S) (hww : w * w = 1) :
    ∃ x u v y : G, (x = 1 ∨ x = z₀) ∧ (u = 1 ∨ u = z) ∧ (v = 1 ∨ v = zb) ∧
      (y = 1 ∨ y = zc) ∧ w = x * u * v * y := by
  have hW := fun {a c : G} (ha : a ∈ sec4W Ω S) (hc : c ∈ sec4W Ω S) => sec4W_comm hΩ hS ha hc
  have h01 : V₀ ⊔ U ≤ sec4W Ω S := sup_le hV₀W hUW
  have h012 : V₀ ⊔ U ⊔ Vb ≤ sec4W Ω S := sup_le h01 hVbW
  obtain ⟨y', hy', y, hy, rfl⟩ :=
    (mem_sup_iff_of_commute fun a ha b hb => hW (h012 ha) (hVcW hb)).mp (hgen hw)
  obtain ⟨y'', hy'', v, hv, rfl⟩ :=
    (mem_sup_iff_of_commute fun a ha b hb => hW (h01 ha) (hVbW hb)).mp hy'
  obtain ⟨x, hx, u, hu, rfl⟩ :=
    (mem_sup_iff_of_commute fun a ha b hb => hW (hV₀W ha) (hUW hb)).mp hy''
  rw [mul_mul_self_of_commute (hW (h012 hy') (hVcW hy)),
    mul_mul_self_of_commute (hW (h01 hy'') (hVbW hv)),
    mul_mul_self_of_commute (hW (hV₀W hx) (hUW hu))] at hww
  obtain ⟨h1, h2, h3, h4⟩ :=
    hind _ (mul_mem hx hx) _ (mul_mem hu hu) _ (mul_mem hv hv) _ (mul_mem hy hy) hww
  exact ⟨x, u, v, y, (hz₀.mem_rot hV₀).2 x hx h1, (hz.mem_rot hU).2 u hu h2,
    (hzb.mem_rot hVb).2 v hv h3, (hzc.mem_rot hVc).2 y hy h4, rfl⟩

end CFSG.ComponentClassification.Asc76.Sec4
