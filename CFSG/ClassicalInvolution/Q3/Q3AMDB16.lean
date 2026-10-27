module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadLayer

public section

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open scoped commutatorElement

section Quotient

variable {Q : Type} [Group Q]

theorem comm_prod_aux {u u' v v' : Q} (h1 : Commute u u') (h2 : Commute u v')
    (h3 : Commute v u') (h4 : Commute v v') :
    (u * u') * (v * v') * (u * u')⁻¹ * (v * v')⁻¹ =
      (u * v * u⁻¹ * v⁻¹) * (u' * v' * u'⁻¹ * v'⁻¹) := by
  have hw : Commute u (u' * v' * u'⁻¹) := (h1.mul_right h2).mul_right h1.inv_right
  have e1 : u' * (v * v') * u'⁻¹ = v * (u' * v' * u'⁻¹) := by
    calc u' * (v * v') * u'⁻¹ = (u' * v * u'⁻¹) * (u' * v' * u'⁻¹) := by group
      _ = v * (u' * v' * u'⁻¹) := by rw [h3.symm.mul_inv_cancel]
  have e2 : u * (v * (u' * v' * u'⁻¹)) * u⁻¹ = (u * v * u⁻¹) * (u' * v' * u'⁻¹) := by
    calc u * (v * (u' * v' * u'⁻¹)) * u⁻¹
        = (u * v * u⁻¹) * (u * (u' * v' * u'⁻¹) * u⁻¹) := by group
      _ = (u * v * u⁻¹) * (u' * v' * u'⁻¹) := by rw [hw.mul_inv_cancel]
  have hvw : Commute v (u' * v' * u'⁻¹ * v'⁻¹) :=
    ((h3.mul_right h4).mul_right h3.inv_right).mul_right h4.inv_right
  calc (u * u') * (v * v') * (u * u')⁻¹ * (v * v')⁻¹
      = (u * (u' * (v * v') * u'⁻¹) * u⁻¹) * (v * v')⁻¹ := by group
    _ = (u * (v * (u' * v' * u'⁻¹)) * u⁻¹) * (v * v')⁻¹ := by rw [e1]
    _ = ((u * v * u⁻¹) * (u' * v' * u'⁻¹)) * (v * v')⁻¹ := by rw [e2]
    _ = (u * v * u⁻¹) * (u' * v' * u'⁻¹ * v'⁻¹) * v⁻¹ := by group
    _ = (u * v * u⁻¹) * (v⁻¹ * (u' * v' * u'⁻¹ * v'⁻¹)) := by
        rw [mul_assoc, hvw.inv_left.symm.eq]
    _ = (u * v * u⁻¹ * v⁻¹) * (u' * v' * u'⁻¹ * v'⁻¹) := by group

theorem swap_quot_aux {u u' v v' τ ζ : Q} (huu' : Commute u u') (huv' : Commute u v')
    (hvu' : Commute v u') (hvv' : Commute v v') (hu : u * u = τ) (hv : v * v = τ)
    (huv : u * v * u⁻¹ * v⁻¹ = τ) (hu' : u' * u' = ζ * τ) (hv' : v' * v' = ζ * τ)
    (huv'' : u' * v' * u'⁻¹ * v'⁻¹ = ζ * τ) (hζτ : ζ * τ = τ * ζ) (hττ : τ * τ = 1) :
    (u * u') * (u * u') = ζ ∧ (v * v') * (v * v') = ζ ∧
      (u * u') * (v * v') * (u * u')⁻¹ * (v * v')⁻¹ = ζ := by
  have key : ∀ p p' : Q, Commute p p' → p * p = τ → p' * p' = ζ * τ → (p * p') * (p * p') = ζ := by
    intro p p' hpp' hp hp'
    calc (p * p') * (p * p') = p * (p' * p) * p' := by group
      _ = p * (p * p') * p' := by rw [hpp'.symm.eq]
      _ = (p * p) * (p' * p') := by group
      _ = τ * (ζ * τ) := by rw [hp, hp']
      _ = (τ * ζ) * τ := by group
      _ = (ζ * τ) * τ := by rw [← hζτ]
      _ = ζ * (τ * τ) := by group
      _ = ζ := by rw [hττ, mul_one]
  refine ⟨key u u' huu' hu hu', key v v' hvv' hv hv', ?_⟩
  rw [comm_prod_aux huu' huv' hvu' hvv', huv, huv'']
  calc τ * (ζ * τ) = (τ * ζ) * τ := by group
    _ = (ζ * τ) * τ := by rw [← hζτ]
    _ = ζ * (τ * τ) := by group
    _ = ζ := by rw [hττ, mul_one]

end Quotient

section Lifts

variable {Γ : Type} [Group Γ] [Finite Γ] (𝒩 : Subgroup Γ) [𝒩.Normal]

theorem exists_lift_fixed (hodd : Odd (Nat.card 𝒩)) {e z a : Γ} (hee : e * e = 1)
    (hzz : z * z = 1) (hez : e * z = z * e) (hza : z * a = a * z)
    (hc : ⁅a, e * a * e⁻¹⁆ ∈ 𝒩) :
    ∃ m ∈ 𝒩, e * (a * (e * a * e⁻¹) * m) = (a * (e * a * e⁻¹) * m) * e ∧
      z * (a * (e * a * e⁻¹) * m) = (a * (e * a * e⁻¹) * m) * z := by
  have he1 : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  obtain ⟨a', ha'⟩ : ∃ a', a' = e * a * e⁻¹ := ⟨_, rfl⟩
  rw [← ha'] at hc ⊢
  have hea' : e * a' * e⁻¹ = a := by
    rw [ha', he1]
    calc e * (e * a * e) * e = (e * e) * a * (e * e) := by group
      _ = a := by rw [hee]; group
  have hza' : z * a' = a' * z := by
    rw [ha', he1]
    calc z * (e * a * e) = (z * e) * a * e := by group
      _ = (e * z) * a * e := by rw [← hez]
      _ = e * (z * a) * e := by group
      _ = e * (a * z) * e := by rw [hza]
      _ = e * a * (z * e) := by group
      _ = e * a * (e * z) := by rw [← hez]
      _ = (e * a * e) * z := by group
  have hzaz : z * a * z⁻¹ = a := by rw [hza]; group
  have hza'z : z * a' * z⁻¹ = a' := by rw [hza']; group
  have hnc : ∀ n ∈ 𝒩, ∀ g : Γ, g * n * g⁻¹ ∈ 𝒩 := fun n hn g =>
    Subgroup.Normal.conj_mem inferInstance n hn g
  have hex : e * (a * a') * e⁻¹ = a' * a := by
    calc e * (a * a') * e⁻¹ = (e * a * e⁻¹) * (e * a' * e⁻¹) := by group
      _ = a' * a := by rw [← ha', hea']
  have hx : (a * a')⁻¹ * (e * (a * a') * e⁻¹) ∈ 𝒩 := by
    have h1 : ⁅a', a⁆ ∈ 𝒩 := by
      rw [← commutatorElement_inv]
      exact 𝒩.inv_mem hc
    have h2 : (a * a')⁻¹ * (a' * a) = (a * a')⁻¹ * ⁅a', a⁆ * (a * a')⁻¹⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hex, h2]
    exact hnc _ h1 (a * a')⁻¹
  obtain ⟨n, hn, hen⟩ := exists_mul_centralizes_of_odd hee hodd (fun o ho => hnc o ho e) hx
  have hcomm_e : e * (a * a' * n) = (a * a' * n) * e := mul_inv_eq_iff_eq_mul.mp hen
  have hzC : z ∈ Subgroup.centralizer ({e} : Set Γ) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hez.symm
  have hhC : a * a' * n ∈ Subgroup.centralizer ({e} : Set Γ) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm_e.symm
  have hO'odd : Odd (Nat.card ↥(𝒩 ⊓ Subgroup.centralizer ({e} : Set Γ))) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hzO' : ∀ o ∈ 𝒩 ⊓ Subgroup.centralizer ({e} : Set Γ),
      z * o * z⁻¹ ∈ 𝒩 ⊓ Subgroup.centralizer ({e} : Set Γ) := fun o ho =>
    ⟨hnc o ho.1 z, (Subgroup.centralizer ({e} : Set Γ)).mul_mem
      ((Subgroup.centralizer ({e} : Set Γ)).mul_mem hzC ho.2)
      ((Subgroup.centralizer ({e} : Set Γ)).inv_mem hzC)⟩
  have hzh : z * (a * a' * n) * z⁻¹ = a * a' * (z * n * z⁻¹) := by
    calc z * (a * a' * n) * z⁻¹ = (z * a * z⁻¹) * (z * a' * z⁻¹) * (z * n * z⁻¹) := by group
      _ = a * a' * (z * n * z⁻¹) := by rw [hzaz, hza'z]
  have hy : (a * a' * n)⁻¹ * (z * (a * a' * n) * z⁻¹) ∈
      𝒩 ⊓ Subgroup.centralizer ({e} : Set Γ) := by
    refine ⟨?_, (Subgroup.centralizer ({e} : Set Γ)).mul_mem
      ((Subgroup.centralizer ({e} : Set Γ)).inv_mem hhC)
      ((Subgroup.centralizer ({e} : Set Γ)).mul_mem
        ((Subgroup.centralizer ({e} : Set Γ)).mul_mem hzC hhC)
        ((Subgroup.centralizer ({e} : Set Γ)).inv_mem hzC))⟩
    have : (a * a' * n)⁻¹ * (z * (a * a' * n) * z⁻¹) = n⁻¹ * (z * n * z⁻¹) := by
      rw [hzh]
      group
    rw [this]
    exact 𝒩.mul_mem (𝒩.inv_mem hn) (hnc n hn z)
  obtain ⟨o, ho, hzo⟩ := exists_mul_centralizes_of_odd hzz hO'odd hzO' hy
  refine ⟨n * o, 𝒩.mul_mem hn ho.1, ?_, ?_⟩
  · have hoe : o * e = e * o := Subgroup.mem_centralizer_singleton_iff.mp ho.2
    calc e * (a * a' * (n * o)) = (e * (a * a' * n)) * o := by group
      _ = ((a * a' * n) * e) * o := by rw [hcomm_e]
      _ = (a * a' * n) * (e * o) := by group
      _ = (a * a' * n) * (o * e) := by rw [hoe]
      _ = (a * a' * (n * o)) * e := by group
  · have := mul_inv_eq_iff_eq_mul.mp hzo
    calc z * (a * a' * (n * o)) = z * (a * a' * n * o) := by group
      _ = (a * a' * n * o) * z := this
      _ = (a * a' * (n * o)) * z := by group

theorem exists_swap_lifts (hodd : Odd (Nat.card 𝒩)) {e z t a b : Γ} (hee : e * e = 1)
    (hzz : z * z = 1) (hez : e * z = z * e) (hzt : z * t = t * z) (htt : t * t = 1)
    (het : e * t * e⁻¹ = z * t) (ha2 : a * a = t) (hb2 : b * b = t) (hab : a * b * a⁻¹ * b⁻¹ = t)
    (hza : z * a = a * z) (hzb : z * b = b * z) (hc₁ : ⁅a, e * a * e⁻¹⁆ ∈ 𝒩)
    (hc₂ : ⁅a, e * b * e⁻¹⁆ ∈ 𝒩) (hc₃ : ⁅b, e * a * e⁻¹⁆ ∈ 𝒩) (hc₄ : ⁅b, e * b * e⁻¹⁆ ∈ 𝒩) :
    ∃ ha hb ηa ηb ηc : Γ, e * ha = ha * e ∧ z * ha = ha * z ∧ e * hb = hb * e ∧
      z * hb = hb * z ∧ ηa ∈ 𝒩 ∧ ηb ∈ 𝒩 ∧ ηc ∈ 𝒩 ∧ ha * ha = z * ηa ∧ hb * hb = z * ηb ∧
        ha * hb * ha⁻¹ * hb⁻¹ = z * ηc := by
  obtain ⟨ma, hma, hea, hza_⟩ := exists_lift_fixed 𝒩 hodd hee hzz hez hza hc₁
  obtain ⟨mb, hmb, heb, hzb_⟩ := exists_lift_fixed 𝒩 hodd hee hzz hez hzb hc₄
  have he1 : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  obtain ⟨a', ha'⟩ : ∃ a', a' = e * a * e⁻¹ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = e * b * e⁻¹ := ⟨_, rfl⟩
  rw [← ha'] at hc₁ hc₃ hea hza_
  rw [← hb'] at hc₂ hc₄ heb hzb_
  have hπ : ∀ g : Γ, g ∈ 𝒩 ↔ QuotientGroup.mk' 𝒩 g = 1 := fun g =>
    (QuotientGroup.eq_one_iff g).symm
  have hcomm : ∀ x y : Γ, ⁅x, y⁆ ∈ 𝒩 →
      Commute (QuotientGroup.mk' 𝒩 x) (QuotientGroup.mk' 𝒩 y) := by
    intro x y hxy
    have h := (hπ _).mp hxy
    rw [map_commutatorElement] at h
    exact (commutatorElement_eq_one_iff_commute).mp h
  have ha'2 : a' * a' = z * t := by
    rw [ha']
    calc e * a * e⁻¹ * (e * a * e⁻¹) = e * (a * a) * e⁻¹ := by group
      _ = z * t := by rw [ha2, het]
  have hb'2 : b' * b' = z * t := by
    rw [hb']
    calc e * b * e⁻¹ * (e * b * e⁻¹) = e * (b * b) * e⁻¹ := by group
      _ = z * t := by rw [hb2, het]
  have hab' : a' * b' * a'⁻¹ * b'⁻¹ = z * t := by
    rw [ha', hb']
    calc e * a * e⁻¹ * (e * b * e⁻¹) * (e * a * e⁻¹)⁻¹ * (e * b * e⁻¹)⁻¹
        = e * (a * b * a⁻¹ * b⁻¹) * e⁻¹ := by group
      _ = z * t := by rw [hab, het]
  have hq := swap_quot_aux (hcomm a a' hc₁) (hcomm a b' hc₂) (hcomm b a' hc₃) (hcomm b b' hc₄)
    (by simpa only [map_mul] using congrArg (QuotientGroup.mk' 𝒩) ha2)
    (by simpa only [map_mul] using congrArg (QuotientGroup.mk' 𝒩) hb2)
    (by simpa only [map_mul, map_inv] using congrArg (QuotientGroup.mk' 𝒩) hab)
    (by simpa only [map_mul] using congrArg (QuotientGroup.mk' 𝒩) ha'2)
    (by simpa only [map_mul] using congrArg (QuotientGroup.mk' 𝒩) hb'2)
    (by simpa only [map_mul, map_inv] using congrArg (QuotientGroup.mk' 𝒩) hab')
    (by simpa only [map_mul] using congrArg (QuotientGroup.mk' 𝒩) hzt)
    (by simpa only [map_mul, map_one] using congrArg (QuotientGroup.mk' 𝒩) htt)
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hπha : QuotientGroup.mk' 𝒩 (a * a' * ma) =
      QuotientGroup.mk' 𝒩 a * QuotientGroup.mk' 𝒩 a' := by
    rw [map_mul, map_mul, (hπ ma).mp hma, mul_one]
  have hπhb : QuotientGroup.mk' 𝒩 (b * b' * mb) =
      QuotientGroup.mk' 𝒩 b * QuotientGroup.mk' 𝒩 b' := by
    rw [map_mul, map_mul, (hπ mb).mp hmb, mul_one]
  have hA : QuotientGroup.mk' 𝒩 ((a * a' * ma) * (a * a' * ma)) = QuotientGroup.mk' 𝒩 z := by
    rw [map_mul, hπha]
    exact hq1
  have hB : QuotientGroup.mk' 𝒩 ((b * b' * mb) * (b * b' * mb)) = QuotientGroup.mk' 𝒩 z := by
    rw [map_mul, hπhb]
    exact hq2
  have hC : QuotientGroup.mk' 𝒩 ((a * a' * ma) * (b * b' * mb) * (a * a' * ma)⁻¹ *
      (b * b' * mb)⁻¹) = QuotientGroup.mk' 𝒩 z := by
    simp only [map_mul, map_inv, hπha, hπhb]
    simpa only [map_mul, map_inv] using hq3
  have hzπ : QuotientGroup.mk' 𝒩 z * QuotientGroup.mk' 𝒩 z = 1 := by
    rw [← map_mul, hzz, map_one]
  refine ⟨a * a' * ma, b * b' * mb, z * ((a * a' * ma) * (a * a' * ma)),
    z * ((b * b' * mb) * (b * b' * mb)),
    z * ((a * a' * ma) * (b * b' * mb) * (a * a' * ma)⁻¹ * (b * b' * mb)⁻¹), hea, hza_, heb,
    hzb_, (hπ _).mpr (by rw [map_mul, hA, hzπ]), (hπ _).mpr (by rw [map_mul, hB, hzπ]),
    (hπ _).mpr (by rw [map_mul, hC, hzπ]), ?_, ?_, ?_⟩
  · rw [← mul_assoc z z, hzz, one_mul]
  · rw [← mul_assoc z z, hzz, one_mul]
  · rw [← mul_assoc z z, hzz, one_mul]

end Lifts

end CFSG.ClassicalInvolution.Q3.Q3AM
