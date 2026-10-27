module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S5Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S5Wreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S5A6

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup Wreath Open Equiv

@[expose] def S5FusionA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → ∀ a : PA0 L t E z,
      ∀ g ∈ normalizer ((Vsub t a.u : Subgroup G) : Set G),
        ∃ ā ∈ a.Abar, ∃ g' ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) ⊓
          normalizer ((Vsub t a.u : Subgroup G) : Set G), g = ā * g'

@[expose] def S5FusionB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G),
    PAB G L t E W z → ∀ a : PA0 L t E z, ∀ x : G, (x = a.u ∨ x = t * a.u) →
      (IsConj t x ↔ ∃ h ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G),
        h * t * h⁻¹ = x)

namespace S5

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem u_mem_L (a : PA0 L t E z) : a.u ∈ L := (a.K₀_le a.u_mem).1

theorem u_mem_Cen (a : PA0 L t E z) : a.u ∈ Cen a.y := (a.K₀_le a.u_mem).2

theorem u_sq (a : PA0 L t E z) : a.u * a.u = 1 := by
  obtain ⟨i, j, hij, h⟩ := a.u_swap
  have h1 : a.eK₀ ((⟨a.u, a.u_mem⟩ : ↥a.K₀) * ⟨a.u, a.u_mem⟩) = 1 := by
    rw [map_mul, h, swap_mul_self]
  have h2 := a.eK₀.injective (h1.trans (map_one _).symm)
  exact congrArg Subtype.val h2

theorem u_comm_t (hb : PAB G L t E W z) (a : PA0 L t E z) : a.u * t = t * a.u :=
  mem_centralizer_iff.1 hb.t_cent a.u (u_mem_L a)

theorem J_le_L (a : PA0 L t E z) : derivedIn a.Abar ≤ L := fun _ hj =>
  (a.Abar_le (derivedIn_le _ hj)).1

theorem Abar_comm (hb : PAB G L t E W z) (a : PA0 L t E z) {x : G} (hx : x ∈ a.Abar) :
    x * t = t * x ∧ x * a.u = a.u * x :=
  ⟨mem_centralizer_iff.1 hb.t_cent x (a.Abar_le hx).1, mem_Cen.1 (a.Abar_le hx).2⟩

theorem t_mem_cent_J (hb : PAB G L t E W z) (a : PA0 L t E z) :
    t ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) :=
  mem_centralizer_iff.2 fun j hj => mem_centralizer_iff.1 hb.t_cent j (J_le_L a hj)

theorem cent_J_le_Cen_y (a : PA0 L t E z) {h : G}
    (hh : h ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G)) : h ∈ Cen a.y :=
  mem_Cen.2 (mem_centralizer_iff.1 hh a.y a.y_J).symm

theorem cent_cent_t_mem_V (hb : PAB G L t E W z) (a : PA0 L t E z) {g : G}
    (hgJ : g ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G)) (hgt : g * t = t * g) :
    g ∈ Vsub t a.u := by
  have hg : g ∈ L ⊔ zpowers t := by
    rw [← hb.inner]
    exact mem_centralizer_singleton_iff.2 hgt
  rw [sup_comm] at hg
  obtain ⟨n, l, hl, rfl⟩ := exists_zpow_mul_of_mem_sup' (A := L)
    (fun x hx => mem_centralizer_iff.1 hb.t_cent x hx) hg
  have hlJ : l ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) := by
    refine mem_centralizer_iff.2 fun j hj => ?_
    have h1 := mem_centralizer_iff.1 hgJ j hj
    have h2 : j * t ^ n = t ^ n * j :=
      ((show Commute j t from mem_centralizer_iff.1 hb.t_cent j (J_le_L a hj)).zpow_right n)
    have h3 : t ^ n * (j * l) = t ^ n * (l * j) := by
      calc t ^ n * (j * l) = (t ^ n * j) * l := (mul_assoc _ _ _).symm
        _ = (j * t ^ n) * l := by rw [h2]
        _ = j * (t ^ n * l) := mul_assoc _ _ _
        _ = (t ^ n * l) * j := h1
        _ = t ^ n * (l * j) := mul_assoc _ _ _
    exact mul_left_cancel h3
  have hl' : l ∈ L ⊓ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) := ⟨hl, hlJ⟩
  rw [a.C_L_J] at hl'
  exact mul_mem (zpow_mem (mem_sup_left (mem_zpowers t)) n) (mem_sup_right hl')

theorem exists_u₁_of_d (hb : PAB G L t E W z) (a : PA0 L t E z)
    (hA : ∀ g ∈ normalizer ((Vsub t a.u : Subgroup G) : Set G),
      ∃ ā ∈ a.Abar, ∃ g' ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) ⊓
        normalizer ((Vsub t a.u : Subgroup G) : Set G), g = ā * g')
    {ub d : G} (hub : ub = a.u ∨ ub = t * a.u) (hub1 : ub ≠ 1) (hdub : d * ub = ub * d)
    (hdt : d * t * d⁻¹ = t * ub) :
    ∃ u₁ : G, u₁ * u₁ = 1 ∧ u₁ * ub = ub * u₁ ∧
      u₁ ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) ∧ t * u₁ * t⁻¹ = ub * u₁ := by
  have htt : t * t = 1 := hb.t_mul_t
  have huu : a.u * a.u = 1 := u_sq a
  have hut : a.u * t = t * a.u := u_comm_t hb a
  have hubt : ub * t = t * ub := by
    rcases hub with rfl | rfl
    · exact hut
    · calc t * a.u * t = t * (a.u * t) := mul_assoc _ _ _
        _ = t * (t * a.u) := by rw [hut]
  have hubub : ub * ub = 1 := by
    rcases hub with rfl | rfl
    · exact huu
    · calc t * a.u * (t * a.u) = t * (a.u * t) * a.u := by simp only [mul_assoc]
        _ = t * (t * a.u) * a.u := by rw [hut]
        _ = (t * t) * (a.u * a.u) := by simp only [mul_assoc]
        _ = 1 := by rw [htt, huu, mul_one]
  have hubV : ub ∈ Vsub t a.u := by
    rcases hub with rfl | rfl
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  have hdu : d * a.u * d⁻¹ ∈ Vsub t a.u := by
    rcases hub with h | h
    · have e : d * a.u * d⁻¹ = ub := by
        rw [← h, hdub, mul_assoc, mul_inv_cancel, mul_one]
      rw [e]
      exact hubV
    · have hu : a.u = t * ub := by rw [h, ← mul_assoc, htt, one_mul]
      have : d * a.u * d⁻¹ = (d * t * d⁻¹) * (d * ub * d⁻¹) := by rw [hu]; group
      rw [this, hdt, hdub, mul_assoc ub, mul_inv_cancel, mul_one, mul_assoc, hubub, mul_one]
      exact mem_sup_left (mem_zpowers _)
  have hdt' : d * t * d⁻¹ ∈ Vsub t a.u := by
    rw [hdt]
    exact mul_mem (mem_sup_left (mem_zpowers _)) hubV
  have hdN : d ∈ normalizer ((Vsub t a.u : Subgroup G) : Set G) := by
    apply mem_normalizer_fintype
    intro n hn
    have hn' : n ∈ Vsub t a.u := hn
    rcases (mem_V_iff htt huu hut.symm).1 hn' with h | h | h | h <;> rw [SetLike.mem_coe, h]
    · simp
    · exact hdt'
    · exact hdu
    · have : d * (t * a.u) * d⁻¹ = (d * t * d⁻¹) * (d * a.u * d⁻¹) := by group
      rw [this]
      exact mul_mem hdt' hdu
  obtain ⟨ā, hā, g', ⟨hgJ, -⟩, hdg⟩ := hA d hdN
  have hh : g' = ā⁻¹ * d := eq_inv_mul_of_mul_eq hdg.symm
  obtain ⟨hāt, hāu⟩ := Abar_comm hb a hā
  have hāub : Commute ā ub := by
    rcases hub with rfl | rfl
    · exact hāu
    · exact (show Commute ā t from hāt).mul_right (show Commute ā a.u from hāu)
  have hāt' : Commute ā t := hāt
  have hhub : g' * ub = ub * g' := by
    rw [hh]
    calc ā⁻¹ * d * ub = ā⁻¹ * (d * ub) := mul_assoc _ _ _
      _ = ā⁻¹ * (ub * d) := by rw [hdub]
      _ = (ā⁻¹ * ub) * d := (mul_assoc _ _ _).symm
      _ = (ub * ā⁻¹) * d := by rw [hāub.inv_left.eq]
      _ = ub * (ā⁻¹ * d) := mul_assoc _ _ _
  have hht : g' * t * g'⁻¹ = t * ub := by
    have hc : Commute ā (t * ub) := hāt'.mul_right hāub
    rw [hh]
    calc ā⁻¹ * d * t * (ā⁻¹ * d)⁻¹ = ā⁻¹ * (d * t * d⁻¹) * ā := by group
      _ = ā⁻¹ * (t * ub) * ā := by rw [hdt]
      _ = t * ub := by rw [hc.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hgt : g' * g' * t = t * (g' * g') := by
    have h1 : g' * t = t * ub * g' := by
      rw [mul_inv_eq_iff_eq_mul] at hht
      exact hht
    calc g' * g' * t = g' * (g' * t) := mul_assoc _ _ _
      _ = g' * (t * ub * g') := by rw [h1]
      _ = (g' * t) * ub * g' := by simp only [mul_assoc]
      _ = (t * ub * g') * ub * g' := by rw [h1]
      _ = t * ub * (g' * ub) * g' := by simp only [mul_assoc]
      _ = t * ub * (ub * g') * g' := by rw [hhub]
      _ = t * (ub * ub) * (g' * g') := by simp only [mul_assoc]
      _ = t * (g' * g') := by rw [hubub, mul_one]
  have hV2 : g' * g' ∈ Vsub t a.u :=
    cent_cent_t_mem_V hb a (mul_mem hgJ hgJ) hgt
  have hmem : g' * g' = 1 ∨ g' * g' = t ∨ g' * g' = ub ∨ g' * g' = t * ub := by
    rcases (mem_V_iff htt huu hut.symm).1 hV2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hub with h' | h'
      · exact Or.inr (Or.inr (Or.inl (h.trans h'.symm)))
      · have : a.u = t * ub := by rw [h', ← mul_assoc, htt, one_mul]
        exact Or.inr (Or.inr (Or.inr (h.trans this)))
    · rcases hub with h' | h'
      · exact Or.inr (Or.inr (Or.inr (by rw [h, h'])))
      · exact Or.inr (Or.inr (Or.inl (by rw [h, h'])))
  have hsq := sq_cases hubub hub1 hhub hht hmem
  obtain ⟨u₁, hu₁, hu₁sq, hu₁ub, hu₁t⟩ := u₁_algebra htt hubub hubt hhub hht hsq
  refine ⟨u₁, hu₁sq, hu₁ub, ?_, hu₁t⟩
  rcases hu₁ with rfl | rfl
  · exact hgJ
  · exact mul_mem hgJ (t_mem_cent_J hb a)

end Local

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

abbrev phi (a : PA4 L t E z) : ↥(Cen a.y) →* Wr2 (Perm (Fin 5)) := a.ι.comp (oMk (Cen a.y))

theorem phi_t (a : PA4 L t E z) : phi a ⟨t, a.t_cy⟩ = tau := a.ι_t

theorem sign_swap_ne_one {σ : Perm (Fin 5)} (hσ : σ.IsSwap) : σ ≠ 1 := by
  rintro rfl
  exact S5W.sign_ne_one_of_isSwap hσ (map_one _)

theorem swap_sq {σ : Perm (Fin 5)} (hσ : σ.IsSwap) : σ * σ = 1 := by
  obtain ⟨i, j, hij, rfl⟩ := hσ
  exact swap_mul_self i j

theorem exists_ub (a : PA4 L t E z) : ∃ ub : G, (ub = a.u ∨ ub = t * a.u) ∧
    ∃ hc : ub ∈ Cen a.y, ∃ σ : Perm (Fin 5), σ.IsSwap ∧ phi a ⟨ub, hc⟩ = base σ σ := by
  obtain ⟨σ, hσ, h | h⟩ := a.ι_u
  · exact ⟨a.u, Or.inl rfl, u_mem_Cen a.toPA0, σ, hσ, h⟩
  · refine ⟨t * a.u, Or.inr rfl, mul_mem a.t_cy (u_mem_Cen a.toPA0), σ, hσ, ?_⟩
    have e : (⟨t * a.u, mul_mem a.t_cy (u_mem_Cen a.toPA0)⟩ : ↥(Cen a.y)) =
        ⟨t, a.t_cy⟩ * ⟨a.u, u_mem_Cen a.toPA0⟩ := rfl
    rw [e, map_mul, phi_t]
    have h' : phi a ⟨a.u, u_mem_Cen a.toPA0⟩ = base σ σ * tau := h
    rw [h', ← mul_assoc, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]

theorem ub_sq (hb : PAB G L t E W z) (a : PA0 L t E z) {ub : G} (hub : ub = a.u ∨ ub = t * a.u) :
    ub * ub = 1 ∧ ub * t = t * ub := by
  have htt : t * t = 1 := hb.t_mul_t
  have huu : a.u * a.u = 1 := u_sq a
  have hut : a.u * t = t * a.u := u_comm_t hb a
  rcases hub with rfl | rfl
  · exact ⟨huu, hut⟩
  · refine ⟨?_, ?_⟩
    · calc t * a.u * (t * a.u) = t * (a.u * t) * a.u := by simp only [mul_assoc]
        _ = t * (t * a.u) * a.u := by rw [hut]
        _ = (t * t) * (a.u * a.u) := by simp only [mul_assoc]
        _ = 1 := by rw [htt, huu, mul_one]
    · calc t * a.u * t = t * (a.u * t) := mul_assoc _ _ _
        _ = t * (t * a.u) := by rw [hut]

theorem ub_comm_Abar (hb : PAB G L t E W z) (a : PA0 L t E z) {ub : G}
    (hub : ub = a.u ∨ ub = t * a.u) {x : G} (hx : x ∈ a.Abar) : x * ub = ub * x := by
  obtain ⟨hxt, hxu⟩ := Abar_comm hb a hx
  rcases hub with rfl | rfl
  · exact hxu
  · exact (show Commute x t from hxt).mul_right (show Commute x a.u from hxu)

theorem ub_ne_one (a : PA4 L t E z) {ub : G} {hc : ub ∈ Cen a.y} {σ : Perm (Fin 5)}
    (hσ : σ.IsSwap) (hphi : phi a ⟨ub, hc⟩ = base σ σ) : ub ≠ 1 := by
  rintro rfl
  have h1 : phi a ⟨1, hc⟩ = 1 := map_one (phi a)
  rw [h1, ← base_one, eq_comm, base_injective] at hphi
  exact sign_swap_ne_one hσ hphi.1

theorem exists_conj_phi (a : PA4 L t E z)
    (hB : ∀ x : G, (x = a.u ∨ x = t * a.u) →
      (IsConj t x ↔ ∃ h ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G),
        h * t * h⁻¹ = x))
    {x : G} (hx : x = a.u ∨ x = t * a.u) (hxc : x ∈ Cen a.y) (hconj : IsConj t x) :
    ∃ d : ↥(Cen a.y), phi a d * tau * (phi a d)⁻¹ = phi a ⟨x, hxc⟩ := by
  obtain ⟨h, hhJ, hhx⟩ := (hB x hx).1 hconj
  refine ⟨⟨h, cent_J_le_Cen_y a.toPA0 hhJ⟩, ?_⟩
  rw [← phi_t a, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by simpa using hhx)

theorem exists_d (hb : PAB G L t E W z) (a : PA4 L t E z) (hrange : a.ι.range = ⊤) {ub : G}
    (hcy : ub ∈ Cen a.y) {σ : Perm (Fin 5)} (hσ : σ.IsSwap) (hphi : phi a ⟨ub, hcy⟩ = base σ σ)
    (hub2 : ub * ub = 1) (hubt : ub * t = t * ub) :
    ∃ d : G, d * ub = ub * d ∧ d * t * d⁻¹ = t * ub := by
  have hσ2 : σ * σ = 1 := swap_sq hσ
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  set H : Subgroup G := Cen a.y with hH
  obtain ⟨e, he⟩ : ∃ e : ↥H, phi a e = base σ 1 := by
    have : base σ 1 ∈ a.ι.range := by rw [hrange]; trivial
    obtain ⟨x, hx⟩ := this
    obtain ⟨e, rfl⟩ := oMk_surjective _ x
    exact ⟨e, hx⟩
  set ubH : ↥H := ⟨ub, hcy⟩ with hubH
  set tH : ↥H := ⟨t, a.t_cy⟩ with htH
  have hubH2 : ubH * ubH = 1 := Subtype.ext hub2
  have htH2 : tH * tH = 1 := Subtype.ext hb.t_mul_t
  have hcomm_tub : tH * ubH = ubH * tH := Subtype.ext hubt.symm
  have hcommE : QuotientGroup.mk' (Open.fusionOddCore ↥H) e ∈
      centralizer ({QuotientGroup.mk' (Open.fusionOddCore ↥H) ubH} :
        Set (↥H ⧸ Open.fusionOddCore ↥H)) := by
    rw [mem_centralizer_singleton_iff]
    apply a.ι_inj
    rw [map_mul, map_mul]
    show phi a e * phi a ubH = phi a ubH * phi a e
    rw [he, hphi, base_mul_base, base_mul_base, mul_one, one_mul]
  have hT2 := map_centralizer_eq_of_odd (Open.fusionOddCore ↥H) odd_fusionOddCore hubH2
  rw [← hT2] at hcommE
  obtain ⟨d₁, hd₁c, hd₁⟩ := hcommE
  have hphid₁ : phi a d₁ = base σ 1 := by
    rw [← he]
    show a.ι (QuotientGroup.mk' _ d₁) = a.ι (QuotientGroup.mk' _ e)
    rw [hd₁]
  have hd₁ub : d₁ * ubH = ubH * d₁ := mem_centralizer_singleton_iff.1 hd₁c
  have hab : (d₁ * tH * d₁⁻¹)⁻¹ * (tH * ubH) ∈ Open.fusionOddCore ↥H := by
    rw [← QuotientGroup.eq]
    apply a.ι_inj
    show phi a (d₁ * tH * d₁⁻¹) = phi a (tH * ubH)
    rw [map_mul, map_mul, map_mul, map_inv, hphid₁, show phi a tH = tau from phi_t a, hphi,
      conj_base_tau, tau_mul_base, inv_one, mul_one, one_mul, hσi]
  have c1 : Commute d₁ ubH := hd₁ub
  have c2 : Commute tH ubH := hcomm_tub
  have hac : (d₁ * tH * d₁⁻¹) * ubH = ubH * (d₁ * tH * d₁⁻¹) :=
    ((c1.mul_left c2).mul_left c1.inv_left).eq
  have hbc : (tH * ubH) * ubH = ubH * (tH * ubH) := (c2.mul_left (Commute.refl ubH)).eq
  have ha2 : d₁ * tH * d₁⁻¹ * (d₁ * tH * d₁⁻¹) = 1 := by
    calc d₁ * tH * d₁⁻¹ * (d₁ * tH * d₁⁻¹) = d₁ * (tH * tH) * d₁⁻¹ := by group
      _ = 1 := by rw [htH2]; group
  have hb2 : tH * ubH * (tH * ubH) = 1 := by
    calc tH * ubH * (tH * ubH) = tH * (ubH * tH) * ubH := by simp only [mul_assoc]
      _ = tH * (tH * ubH) * ubH := by rw [← hcomm_tub]
      _ = (tH * tH) * (ubH * ubH) := by simp only [mul_assoc]
      _ = 1 := by rw [htH2, hubH2, mul_one]
  obtain ⟨o, ho, hoc, hoa⟩ := exists_conj_cent_of_odd (Open.fusionOddCore ↥H) odd_fusionOddCore
    ha2 hb2 hac hbc hab
  have hdub : (o * d₁) * ubH = ubH * (o * d₁) :=
    ((show Commute o ubH from hoc).mul_left c1).eq
  have hdt : (o * d₁) * tH * (o * d₁)⁻¹ = tH * ubH := by
    calc (o * d₁) * tH * (o * d₁)⁻¹ = o * (d₁ * tH * d₁⁻¹) * o⁻¹ := by group
      _ = tH * ubH := hoa
  refine ⟨((o * d₁ : ↥H) : G), congrArg Subtype.val hdub, ?_⟩
  have := congrArg Subtype.val hdt
  simpa using this

theorem u₁_form (hb : PAB G L t E W z) (a : PA4 L t E z) {ub : G} (hub : ub = a.u ∨ ub = t * a.u)
    (hcy : ub ∈ Cen a.y) {σ : Perm (Fin 5)} (hσ : σ.IsSwap) (hphi : phi a ⟨ub, hcy⟩ = base σ σ)
    {u₁ : G} (hu₁cy : u₁ ∈ Cen a.y) (hu₁sq : u₁ * u₁ = 1) (hu₁ub : u₁ * ub = ub * u₁)
    (hu₁J : u₁ ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G))
    (hu₁t : t * u₁ * t⁻¹ = ub * u₁) :
    phi a ⟨u₁, hu₁cy⟩ = base σ 1 ∨ phi a ⟨u₁, hu₁cy⟩ = base 1 σ := by
  obtain ⟨w, hwJ, hwy, hwn, hw3⟩ := S5A6.exists_third a.Abar a.eAbar a.y_ord a.y_J
  have hwcy : w ∈ Cen a.y := mem_Cen.2 hwy
  have hwt : w * t = t * w := mem_centralizer_iff.1 hb.t_cent w (J_le_L a.toPA0 hwJ)
  have hwne : phi a ⟨w, hwcy⟩ ≠ 1 := by
    intro h1
    have h2 : oMk (Cen a.y) ⟨w, hwcy⟩ = 1 := by
      apply a.ι_inj
      rw [map_one]
      exact h1
    have h3 : (⟨w, hwcy⟩ : ↥(Cen a.y)) ∈ Open.fusionOddCore ↥(Cen a.y) :=
      (QuotientGroup.eq_one_iff _).1 h2
    have h4 : w ∈ fusionOddCoreOf (Cen a.y) := ⟨_, h3, rfl⟩
    exact hwn (by rw [← a.O_cent_t]; exact ⟨h4, mem_Cen.2 hwt⟩)
  have hwtau : phi a ⟨w, hwcy⟩ * tau = tau * phi a ⟨w, hwcy⟩ := by
    rw [← phi_t a, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hwt)
  have hw3' : phi a ⟨w, hwcy⟩ * phi a ⟨w, hwcy⟩ * phi a ⟨w, hwcy⟩ = 1 := by
    rw [← map_mul, ← map_mul]
    have : (⟨w, hwcy⟩ : ↥(Cen a.y)) * ⟨w, hwcy⟩ * ⟨w, hwcy⟩ = 1 := Subtype.ext hw3
    rw [this, map_one]
  have hwub : phi a ⟨w, hwcy⟩ * base σ σ = base σ σ * phi a ⟨w, hwcy⟩ := by
    rw [← hphi, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (ub_comm_Abar hb a.toPA0 hub (derivedIn_le _ hwJ)))
  obtain ⟨c, hc, hc1, hc3, hσc⟩ := S5W.exists_diag_of_commute hwtau hw3' hwne hwub
  have hv1 : phi a ⟨u₁, hu₁cy⟩ * base σ σ = base σ σ * phi a ⟨u₁, hu₁cy⟩ := by
    rw [← hphi, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hu₁ub)
  have hv2 : phi a ⟨u₁, hu₁cy⟩ * base c c = base c c * phi a ⟨u₁, hu₁cy⟩ := by
    rw [← hc, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (mem_centralizer_iff.1 hu₁J w hwJ).symm)
  have hv3 : tau * phi a ⟨u₁, hu₁cy⟩ * tau = base σ σ * phi a ⟨u₁, hu₁cy⟩ := by
    have h := congrArg (phi a) (Subtype.ext hu₁t :
      (⟨t, a.t_cy⟩ : ↥(Cen a.y)) * ⟨u₁, hu₁cy⟩ * (⟨t, a.t_cy⟩ : ↥(Cen a.y))⁻¹ =
        ⟨ub, hcy⟩ * ⟨u₁, hu₁cy⟩)
    rw [map_mul, map_mul, map_mul, map_inv, phi_t a, hphi, tau_inv] at h
    exact h
  have hv4 : phi a ⟨u₁, hu₁cy⟩ * phi a ⟨u₁, hu₁cy⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u₁, hu₁cy⟩ : ↥(Cen a.y)) * ⟨u₁, hu₁cy⟩ = 1 := Subtype.ext hu₁sq
    rw [this, map_one]
  exact S5W.eq_of_commute_conj hσ hc1 hc3 hσc hv1 hv2 hv3 hv4

end Main

end S5

open S5 in
theorem s5 (hA : S5FusionA) (hB : S5FusionB) : StepS5 := by
  intro G _ _ L t E W z hb a
  have hA' := hA G L t E W z hb a.toPA0
  have hB' := hB G L t E W z hb a.toPA0
  obtain ⟨ub, hub, hcy, σ, hσ, hphi⟩ := exists_ub a
  obtain ⟨hub2, hubt⟩ := ub_sq hb a.toPA0 hub
  have hub1 : ub ≠ 1 := ub_ne_one a hσ hphi
  have hord : orderOf ub = 2 := orderOf_eq_prime (by rw [pow_two]; exact hub2) hub1
  have hnconj : ¬ IsConj t ub := by
    intro hc
    obtain ⟨d, hd⟩ := exists_conj_phi a hB' hub hcy hc
    rw [hphi] at hd
    have h1 : IsConj (base σ σ) (base (1 : Perm (Fin 5)) 1 * tau) := by
      rw [base_one, one_mul]
      exact (isConj_iff.2 ⟨phi a d, hd⟩).symm
    exact not_isConj_base_tau σ σ 1 1 h1
  by_cases hrange : a.ι.range = ⊤
  ·
    obtain ⟨d, hdub, hdt⟩ := exists_d hb a hrange hcy hσ hphi hub2 hubt
    obtain ⟨u₁, hu₁sq, hu₁ub, hu₁J, hu₁t⟩ :=
      exists_u₁_of_d hb a.toPA0 hA' hub hub1 hdub hdt
    have hu₁cy : u₁ ∈ Cen a.y := cent_J_le_Cen_y a.toPA0 hu₁J
    have hu₁1 : u₁ ≠ 1 := by
      rintro rfl
      apply hub1
      simpa using hu₁t.symm
    have hne : ub ≠ u₁ := by
      intro h
      subst h
      apply hub1
      have h1 : t * ub * t⁻¹ = ub := by rw [← hubt, mul_inv_cancel_right]
      have h3 : ub = ub * ub := h1.symm.trans hu₁t
      rw [hub2] at h3
      exact h3
    have hu₁2 : orderOf u₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu₁sq) hu₁1
    have hform := u₁_form hb a hub hcy hσ hphi hu₁cy hu₁sq hu₁ub hu₁J hu₁t
    have hzp : ∀ x ∈ zpowers ub, x = 1 ∨ x = ub := by
      intro x hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      rw [← zpow_mod_orderOf, hord]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left; simp [h]
      · right; simp [h]
    refine ⟨{ toPA4 := a
              ub := ub
              ub_cases := hub
              ub_ord := hord
              ub_cy := hcy
              ub_base := ⟨σ, hσ, hphi⟩
              ub_nconj := hnconj
              dcase := DCase.d8
              dcase_iff := by simp [hrange]
              F₀ := zpowers ub ⊔ zpowers u₁
              u₁ := u₁
              F₀_e4 := fun h => absurd h (by decide)
              d8_props := fun _ => ⟨hu₁2, mem_Cen.2 hu₁ub, hu₁J, hu₁t, rfl, ?_,
                σ, hσ, hu₁cy, hform⟩
              F₀_card := fun _ => card_V hub2 hu₁sq hu₁ub.symm hub1 hu₁1 hne }⟩
    intro hmem
    rcases hzp u₁ hmem with h | h
    · exact hu₁1 h
    · exact hne h.symm
  ·
    have hDE4 : a.ι.range = DE4 := a.ι_range.resolve_left hrange
    have hx : t * ub = a.u ∨ t * ub = t * a.u := by
      rcases hub with h | h
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h, ← mul_assoc, hb.t_mul_t, one_mul])
    have hxc : t * ub ∈ Cen a.y := mul_mem a.t_cy hcy
    have hnc : ¬ IsConj t (t * ub) := by
      intro hc
      obtain ⟨d, hd⟩ := exists_conj_phi a hB' hx hxc hc
      have e : phi a ⟨t * ub, hxc⟩ = base σ σ * tau := by
        have e1 : (⟨t * ub, hxc⟩ : ↥(Cen a.y)) = ⟨t, a.t_cy⟩ * ⟨ub, hcy⟩ := rfl
        rw [e1, map_mul, phi_t a, hphi, tau_mul_base]
      rw [e] at hd
      have hdD : phi a d ∈ DE4 := by
        rw [← hDE4]
        exact ⟨_, rfl⟩
      exact S5W.ne_conj_tau_of_sgnProd hσ (mem_DE4.1 hdD) hd
    exact ⟨{ toPA4 := a
             ub := ub
             ub_cases := hub
             ub_ord := hord
             ub_cy := hcy
             ub_base := ⟨σ, hσ, hphi⟩
             ub_nconj := hnconj
             dcase := DCase.e4
             dcase_iff := by simp [hrange]
             F₀ := zpowers ub
             u₁ := ub
             F₀_e4 := fun _ => ⟨rfl, hnc⟩
             d8_props := fun h => absurd h (by decide)
             F₀_card := fun h => absurd h (by decide) }⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
