module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoRho

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.AE

section Coset

theorem exists_fixed_in_coset {Y : Type} [Group Y] [Finite Y] (O : Subgroup Y)
    (hO : Odd (Nat.card O)) {x v : Y} (hv2 : v * v = 1) (hvO : ∀ o ∈ O, v * o * v⁻¹ ∈ O)
    (hvx : x⁻¹ * (v * x * v⁻¹) ∈ O) :
    ∃ o ∈ O, v * (x * o) * v⁻¹ = x * o := by
  classical
  haveI : Fintype Y := Fintype.ofFinite Y
  let S : Set Y := {z | x⁻¹ * z ∈ O}
  have hvS : ∀ z ∈ S, v * z * v⁻¹ ∈ S := by
    intro z hz
    have h1 : x⁻¹ * (v * z * v⁻¹) = (x⁻¹ * (v * x * v⁻¹)) * (v * (x⁻¹ * z) * v⁻¹) := by group
    show x⁻¹ * (v * z * v⁻¹) ∈ O
    rw [h1]
    exact O.mul_mem hvx (hvO _ hz)
  let f : Function.End S := fun z => ⟨v * z * v⁻¹, hvS z z.2⟩
  have hf2 : f ^ 2 ^ 1 = 1 := by
    funext z
    show f (f z) = z
    apply Subtype.ext
    show v * (v * (z : Y) * v⁻¹) * v⁻¹ = z
    calc v * (v * (z : Y) * v⁻¹) * v⁻¹ = (v * v) * (z : Y) * (v * v)⁻¹ := by group
      _ = z := by rw [hv2]; group
  haveI : Fintype S := Fintype.ofFinite S
  have hcard : Fintype.card S = Nat.card O := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun z => ⟨x⁻¹ * z, z.2⟩
        invFun := fun o => ⟨x * o, by
          show x⁻¹ * (x * (o : Y)) ∈ O
          rw [inv_mul_cancel_left]; exact o.2⟩
        left_inv := fun z => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf2
  rw [hcard] at hmod
  have hodd : Fintype.card (Function.fixedPoints f) % 2 = 1 := by
    have := hmod.symm
    unfold Nat.ModEq at this
    rw [this]
    exact Nat.odd_iff.mp hO
  have hne : Nonempty (Function.fixedPoints f) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Fintype.card (Function.fixedPoints f) = 0 := Fintype.card_eq_zero
    omega
  obtain ⟨⟨z, hz⟩⟩ := hne
  refine ⟨x⁻¹ * z, z.2, ?_⟩
  have hfz : f z = z := hz
  have := congrArg Subtype.val hfz
  simpa using this

end Coset

section KF


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem t_mem_zStar (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) {c' : Y}
    (hc'C : c' ∈ Subgroup.centralizer ({t} : Set Y)) :
    t ∈ zStarOf (Subgroup.centralizer ({t * (c' * e * c'⁻¹)} : Set Y)) := by
  have hd := hc.data
  have hZ' := R56.p23_zstar_cu hT hc hZ
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  have hgC : g ∈ Subgroup.centralizer ({e} : Set Y) := normalizer_le_centralizer_e hd hgN
  have hge : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have h1 : g⁻¹ * (u * e) * g⁻¹⁻¹ = t := by
    rw [← hd.hgt]
    group
  have he2 : e⁻¹ = e := inv_eq_of_mul_eq_one_right hd.he2
  have hge' : g⁻¹ * e * g⁻¹⁻¹ = e := by
    calc g⁻¹ * e * g⁻¹⁻¹ = g⁻¹ * (e * g) := by group
      _ = g⁻¹ * (g * e) := by rw [hge]
      _ = e := by group
  have h2 : g⁻¹ * u * g⁻¹⁻¹ = t * e := by
    calc g⁻¹ * u * g⁻¹⁻¹ = (g⁻¹ * (u * e) * g⁻¹⁻¹) * (g⁻¹ * e⁻¹ * g⁻¹⁻¹) := by group
      _ = t * e := by rw [h1, he2, hge']
  have h3 : t ∈ zStarOf (Subgroup.centralizer ({t * e} : Set Y)) := by
    have := C25V.conj_mem_zStarOf_conjSub' (Subgroup.centralizer ({u} : Set Y)) g⁻¹ hZ'
    rw [h1, ← C25V.centralizer_conj', h2] at this
    exact this
  have hct : c' * t * c'⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc'C]
    group
  have h4 : t * (c' * e * c'⁻¹) = c' * (t * e) * c'⁻¹ := by
    calc t * (c' * e * c'⁻¹) = (c' * t * c'⁻¹) * (c' * e * c'⁻¹) := by rw [hct]
      _ = c' * (t * e) * c'⁻¹ := by group
  rw [h4]
  exact (C25V.zStar_conj_iff hct).mpr h3

theorem exists_lift_fix (hc : P23Cfg n Y R S t K' W u e g) {v : Y}
    (hvC : v ∈ Subgroup.centralizer ({e} : Set Y)) (hv2 : v * v = 1) {q : SecQ R e}
    (hq : TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨v, hvC⟩ q = q) :
    ∃ a : ↥(rLayer (Om R) e), (a : Y) ∈ Subgroup.centralizer ({v} : Set Y) ∧ piE hc a = q := by
  obtain ⟨x, rfl⟩ := piE_surjective hc q
  have hvx : v * (x : Y) * v⁻¹ ∈ rLayer (Om R) e := by
    have := conj_mem_conjSub (n := v) x.2
    rwa [conjSub_rLayer_eq (hΩ_of hc) hvC] at this
  rw [secAut_piE hc hvC x hvx] at hq
  have hvx' : (x : Y)⁻¹ * (v * (x : Y) * v⁻¹) ∈ oddCoreOf (rLayer (Om R) e) :=
    (piE_eq_iff hc x ⟨v * (x : Y) * v⁻¹, hvx⟩).mp hq.symm
  have hvO : ∀ o ∈ oddCoreOf (rLayer (Om R) e), v * o * v⁻¹ ∈ oddCoreOf (rLayer (Om R) e) :=
    fun o ho => F7C.conj_mem_oddCoreOf_rLayer (hΩ_of hc) hvC ho
  obtain ⟨o, ho, hfix⟩ := exists_fixed_in_coset (oddCoreOf (rLayer (Om R) e))
    (oddCoreOf_odd_natCard (rLayer (Om R) e)) hv2 hvO hvx'
  have hoE : o ∈ rLayer (Om R) e := oddCoreOf_le_self _ ho
  refine ⟨x * ⟨o, hoE⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    show (x : Y) * o * v = v * ((x : Y) * o)
    calc (x : Y) * o * v = v * ((x : Y) * o) * v⁻¹ * v := by rw [hfix]
      _ = v * ((x : Y) * o) := by group
  · rw [map_mul]
    have : piE hc ⟨o, hoE⟩ = 1 := (piE_eq_one_iff hc ⟨o, hoE⟩).mpr ho
    rw [this, mul_one]


theorem exists_gamma : ∀ (β : Finset (Fin 6)) (c₀ : Fin 6), β.card = 4 → c₀ ∉ β →
    ∃ γ : Finset (Fin 6), γ.card = 4 ∧ c₀ ∉ γ ∧ γ ≠ β ∧ (β ∩ γ).Nonempty := by
  decide +kernel

theorem false_of_zv (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {c' : Y}
    (hc'C : c' ∈ Subgroup.centralizer ({t} : Set Y))
    (hyC : c' * e * c'⁻¹ ∈ Subgroup.centralizer ({e} : Set Y))
    (hy2 : (c' * e * c'⁻¹) * (c' * e * c'⁻¹) = 1)
    (hyt : (c' * e * c'⁻¹) * t = t * (c' * e * c'⁻¹))
    {β : Finset (Fin 6)} {hβ : β.card = 4} {w : Wr 6}
    (hw : D.toAEData.Acts
      (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨c' * e * c'⁻¹, hyC⟩) w)
    (hz : D.φ (tbar hc) = zBar β hβ) {c₀ : Fin 6} (hc₀ : c₀ ∉ β)
    (hcen : ∀ (γ : Finset (Fin 6)) (hγ : γ.card = 4), c₀ ∉ γ → ∀ b : Bool, ∀ x ∈ memBar γ hγ b,
      mkQ 6 (w * zOf (emb β hβ)) * x * (mkQ 6 (w * zOf (emb β hβ)))⁻¹ = x) : False := by
  classical
  set y := c' * e * c'⁻¹ with hydef
  have hC := CoreData.of_S hc.std.perp.core
  have hzt : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have htC : t ∈ Subgroup.centralizer ({e} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (e_comm_t hc).symm
  have hvC : y * t ∈ Subgroup.centralizer ({e} : Set Y) :=
    Subgroup.mul_mem _ hyC htC
  have hv2 : (y * t) * (y * t) = 1 := by
    calc (y * t) * (y * t) = y * (t * y) * t := by group
      _ = (y * y) * (t * t) := by rw [← hyt]; group
      _ = 1 := by rw [hy2, hzt.sq, mul_one]
  set σy := TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ with hσy
  set σv := TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y * t, hvC⟩ with hσv
  have hσv_apply : ∀ q, σv q = σy (tbar hc * q * (tbar hc)⁻¹) := by
    intro q
    have h1 : (⟨y * t, hvC⟩ : ↥(Subgroup.centralizer ({e} : Set Y))) = ⟨y, hyC⟩ * ⟨t, htC⟩ := rfl
    rw [hσv, h1, secAut_mul hc, secAut_t hc htC]
  have hAct : ∀ q, D.φ (σv q) =
      mkQ 6 (w * zOf (emb β hβ)) * D.φ q * (mkQ 6 (w * zOf (emb β hβ)))⁻¹ := by
    intro q
    rw [hσv_apply, hw, map_mul, map_mul, map_inv, hz]
    have : zBar β hβ = mkQ 6 (zOf (emb β hβ)) := rfl
    rw [this]
    simp only [map_mul, map_inv, mul_inv_rev]
    group
  obtain ⟨γ, hγ, hc₀γ, hγβ, hβγ⟩ := exists_gamma β c₀ hβ hc₀
  obtain ⟨L, hL, hLlab⟩ := D.label_surj γ hγ true
  have hLσ := secAut_preserves hc ⟨y * t, hvC⟩ hL
  have hφfix : ∀ q ∈ L, D.φ (σv q) = D.φ q := by
    intro q hq
    rw [hAct]
    exact hcen γ hγ hc₀γ true _ (by rw [← hLlab]; exact ⟨q, hq, rfl⟩)
  have himg : (L.map σv.toMonoidHom).map D.φ = L.map D.φ := by
    ext x
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, (hφfix q hq).symm⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨σv q, ⟨q, hq, rfl⟩, hφfix q hq⟩
  have hLeq : L.map σv.toMonoidHom = L := D.label_inj _ hLσ _ hL himg
  have hfixL : ∀ q ∈ L, σv q = q := by
    intro q hq
    have hmem : σv q ∈ L := by rw [← hLeq]; exact ⟨q, hq, rfl⟩
    exact D.inj L hL _ hmem q hq (hφfix q hq)
  have hne : (Set.range (emb β hβ) ∩ Set.range (emb γ hγ)).Nonempty := by
    obtain ⟨i, hi⟩ := hβγ
    refine ⟨i, ?_, ?_⟩
    · rw [range_emb]; exact (Finset.mem_inter.mp hi).1
    · rw [range_emb]; exact (Finset.mem_inter.mp hi).2
  have hneq : Set.range (emb β hβ) ≠ Set.range (emb γ hγ) := by
    rw [range_emb, range_emb]
    intro h
    exact hγβ (Finset.coe_injective h).symm
  obtain ⟨b₁, hb₁, hb₁nc⟩ := not_comm_mkQ_zOf_memK hne hneq
  have hx₀ : mkQ 6 b₁ ∈ memBar γ hγ true := ⟨b₁, hb₁, rfl⟩
  obtain ⟨q₀, hq₀L, hq₀⟩ : ∃ q₀ ∈ L, D.φ q₀ = mkQ 6 b₁ := by
    rw [← hLlab] at hx₀
    exact hx₀
  obtain ⟨a, haC, haq⟩ := exists_lift_fix hc hvC hv2 (hfixL q₀ hq₀L)
  have hzs := t_mem_zStar hT hc hZ hc'C
  rw [← hydef, ← hyt] at hzs
  have hκ := ((C25V.mem_zStarOf_iff' _).mp hzs).2 (a : Y) haC
  have htE := (t_e_mem_rLayer hc).1
  set tE : ↥(rLayer (Om R) e) := ⟨t, htE⟩ with htEdef
  set κ : ↥(rLayer (Om R) e) := tE⁻¹ * a⁻¹ * tE * a with hκdef
  have hκY : (κ : Y) = t⁻¹ * (a : Y)⁻¹ * t * (a : Y) := rfl
  have hodd : Odd (orderOf κ) := by
    have h1 : orderOf (κ : Y) ∣ Nat.card (oddCoreOf (Subgroup.centralizer ({y * t} : Set Y))) :=
      Subgroup.orderOf_dvd_natCard _ (hκY ▸ hκ)
    have h2 := (oddCoreOf_odd_natCard (Subgroup.centralizer ({y * t} : Set Y))).of_dvd_nat h1
    rwa [Subgroup.orderOf_coe] at h2
  have hpiκ : piE hc κ = (tbar hc)⁻¹ * q₀⁻¹ * tbar hc * q₀ := by
    rw [hκdef, map_mul, map_mul, map_mul, map_inv, map_inv, haq]
    rfl
  have hφκ : D.φ (piE hc κ) = mkQ 6 ((zOf (emb β hβ))⁻¹ * b₁⁻¹ * zOf (emb β hβ) * b₁) := by
    rw [hpiκ, map_mul, map_mul, map_mul, map_inv, map_inv, hz, hq₀]
    show _ = mkQ 6 _
    simp only [map_mul, map_inv]
    rfl
  have hsq : (D.φ (piE hc κ)) ^ 2 = 1 := by
    rw [hφκ, pow_two, ← map_mul]
    have h1 := zOf_comm_sq_eq_one (emb β hβ) b₁⁻¹
    have hX : (zOf (emb β hβ))⁻¹ * b₁⁻¹ * zOf (emb β hβ) * b₁ =
        zOf (emb β hβ) * b₁⁻¹ * (zOf (emb β hβ))⁻¹ * b₁⁻¹⁻¹ := by
      rw [zOf_inv, inv_inv]
    rw [hX, h1, map_one]
  have hoddφ : Odd (orderOf (D.φ (piE hc κ))) :=
    Odd.of_dvd_nat hodd ((orderOf_map_dvd D.φ (piE hc κ)).trans (orderOf_map_dvd (piE hc) κ))
  have hord1 : orderOf (D.φ (piE hc κ)) = 1 := by
    have hdvd : orderOf (D.φ (piE hc κ)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hoddφ
      exact absurd hoddφ (by decide)
  have hφκ1 : mkQ 6 ((zOf (emb β hβ))⁻¹ * b₁⁻¹ * zOf (emb β hβ) * b₁) = 1 := by
    rw [← hφκ]
    exact orderOf_eq_one_iff.mp hord1
  have h1 : (mkQ 6 (zOf (emb β hβ)))⁻¹ * (mkQ 6 b₁)⁻¹ * mkQ 6 (zOf (emb β hβ)) * mkQ 6 b₁ = 1 := by
    simpa only [map_mul, map_inv] using hφκ1
  apply hb₁nc
  calc mkQ 6 (zOf (emb β hβ)) * mkQ 6 b₁
      = mkQ 6 b₁ * ((mkQ 6 b₁)⁻¹ * mkQ 6 (zOf (emb β hβ)) * mkQ 6 b₁) := by group
    _ = mkQ 6 b₁ * mkQ 6 (zOf (emb β hβ)) := by
        congr 1
        calc (mkQ 6 b₁)⁻¹ * mkQ 6 (zOf (emb β hβ)) * mkQ 6 b₁
            = mkQ 6 (zOf (emb β hβ)) *
              ((mkQ 6 (zOf (emb β hβ)))⁻¹ * (mkQ 6 b₁)⁻¹ * mkQ 6 (zOf (emb β hβ)) * mkQ 6 b₁) := by
              group
          _ = mkQ 6 (zOf (emb β hβ)) := by rw [h1, mul_one]

end KF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
