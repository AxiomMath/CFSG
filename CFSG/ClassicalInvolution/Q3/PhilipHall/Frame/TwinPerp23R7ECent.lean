module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7N7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7E

variable {Y : Type} [Group Y]

theorem mem_normalizer_of_centMod {J : Subgroup Y} {a : Y} (h : CentMod J a) (ha : a * a = 1) :
    a ∈ Subgroup.normalizer (J : Set Y) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have key : ∀ b ∈ J, a * b * a⁻¹ ∈ J := by
    intro b hb
    have h1 := J.mul_mem ((oddCoreOf_le_self J) (h b hb)) hb
    simpa [mul_assoc] using h1
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key b, fun hb => ?_⟩
  have := key _ hb
  rw [hai] at this
  have e : a * (a * b * a) * a = b := by
    calc a * (a * b * a) * a = (a * a) * b * (a * a) := by group
      _ = b := by rw [ha]; group
  rwa [e] at this

theorem centMod_conjSub {J : Subgroup Y} {a g : Y} (h : CentMod J a) (hga : g⁻¹ * a * g = a) :
    CentMod (conjSub g J) a := by
  intro b hb
  rw [mem_conjSub_iff] at hb
  rw [Asc77.Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
  have h1 := h _ hb
  have e : g⁻¹ * (a * b * a⁻¹ * b⁻¹) * g =
      (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹ := by group
  rw [e, hga]
  exact h1

variable [Finite Y]

theorem exists_sylow_comm {J V : Subgroup Y} (hV2 : IsPGroup 2 V)
    (hVN : V ≤ Subgroup.normalizer (J : Set Y)) {X : Set Y} (hXV : X ⊆ V)
    (hX : ∀ x ∈ X, CentMod J x) : ∃ R' : Subgroup Y, IsSylow2In R' J ∧ ∀ x ∈ X, ∀ r ∈ R', r * x = x * r := by
  obtain ⟨T, hT, hVT⟩ := Asc77.IsSylow2In.exists_ge hV2 (le_sup_right : V ≤ J ⊔ V)
  have hTJ : IsSylow2In (T ⊓ J) J :=
    Asc77.isSylow2In_inf_of_le_normalizer hT le_sup_left (sup_le Subgroup.le_normalizer hVN)
  refine ⟨T ⊓ J, hTJ, fun x hx r hr => ?_⟩
  have hxT : x ∈ T := hVT (hXV hx)
  have hrT : r ∈ T := hr.1
  have hcT : x * r * x⁻¹ * r⁻¹ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem hxT hrT) (T.inv_mem hxT)) (T.inv_mem hrT)
  have h1 := Sec13.L94T.eq_one_of_isPGroup_of_odd hT.2.1 (odd_natCard_oddCoreOf J) hcT (hX x hx r hr.2)
  have := congrArg (· * (r * x)) h1
  simp only [one_mul] at this
  rw [← this]
  group

end F7E

section Steps


variable {n : ℕ}

@[expose] def P23EGen (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ R₀ R₀' R₁ : Subgroup Y, IsSylow2In R₀ (tightCore R) → IsSylow2In R₀' K' →
          IsSylow2In R₁ (conjSub g (tightCore R)) →
          R₀ ≤ Subgroup.centralizer ({e} : Set Y) → R₀' ≤ Subgroup.centralizer ({e} : Set Y) →
          R₁ ≤ Subgroup.centralizer ({e} : Set Y) →
            rLayer (Om R) e ≤ oddCoreOf (rLayer (Om R) e) ⊔ (R₀ ⊔ R₀' ⊔ R₁)

section Facts

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem P23Cfg.centMod_e (hc : P23Cfg n Y R S t K' W u e g) :
    CentMod (tightCore R) e ∧ CentMod K' e ∧ CentMod (conjSub g (tightCore R)) e := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have htC : t ∈ C := hWt hd.hzW
  have heC : e ∈ C := hWt heW
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hKC : tightCore R ≤ C := le_centralizer_of_unique hz
  have hK'C : K' ≤ C := le_centralizer_of_unique hz'
  obtain ⟨-, -, -, -, ⟨x, hx, y, hy, hxy⟩, -, hAB, heA, heB, -⟩ := p23_twin_q8 hc hCdef htC heC
  have hK : CentMod (tightCore R) e ∧ CentMod K' e := by
    rcases p23_conj_twins hc heC with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact ⟨F7M.centMod_of_comm_image hKC heC h1 heA, F7M.centMod_of_comm_image hK'C heC h2 heB⟩
    · exfalso
      have h3 := F7I.conjSub_map_piC (C := C) (H := tightCore R) ⟨e, heC⟩
      rw [F7M.conjSub_eq_self_of_comm heA] at h3
      have hyB : y ∈ (K'.subgroupOf C).map (F7I.piC C) := by
        rw [← h1]
        change y ∈ ((conjSub e (tightCore R)).subgroupOf C).map (F7I.piC C) at *
        rw [← h3]
        exact hy
      exact hxy (hAB x hx y hyB)
  refine ⟨hK.1, hK.2, F7E.centMod_conjSub hK.1 ?_⟩
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  rw [mul_assoc, ← T7K.comm_e hd hgN, inv_mul_cancel_left]

end Facts

theorem p23ECent_of_gen (hgen : P23EGen n) : P23ECent n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ a ha2 hae hKa hK'a hKga
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hd := hc.data
  have he2 : e * e = 1 := hd.he2
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK' : K' ∈ Om R := hc.std.hK'.1
  have hKg : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  obtain ⟨heK, heK', heKg⟩ := hc.centMod_e
  have hae' : a * e = e * a := Subgroup.mem_centralizer_singleton_iff.mp hae
  set V := Subgroup.closure ({a, e} : Set Y) with hVdef
  have hV2 : IsPGroup 2 V := by
    have hsq := F7I.closure_sq_of_comm (X := ({a, e} : Set Y))
      (by rintro x (rfl | rfl); exacts [ha2, he2])
      (by rintro x (rfl | rfl) y (rfl | rfl); exacts [rfl, hae', hae'.symm, rfl])
    intro x
    exact ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩
  have hXV : ({a, e} : Set Y) ⊆ V := Subgroup.subset_closure
  have hVN : ∀ J : Subgroup Y, CentMod J a → CentMod J e → V ≤ Subgroup.normalizer (J : Set Y) := by
    intro J hJa hJe
    rw [hVdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [F7E.mem_normalizer_of_centMod hJa ha2, F7E.mem_normalizer_of_centMod hJe he2]
  have hX : ∀ J : Subgroup Y, CentMod J a → CentMod J e → ∀ x ∈ ({a, e} : Set Y), CentMod J x := by
    rintro J hJa hJe x (rfl | rfl)
    exacts [hJa, hJe]
  obtain ⟨R₀, hR₀, hR₀c⟩ := F7E.exists_sylow_comm hV2 (hVN _ hKa heK) hXV (hX _ hKa heK)
  obtain ⟨R₀', hR₀', hR₀'c⟩ := F7E.exists_sylow_comm hV2 (hVN _ hK'a heK') hXV (hX _ hK'a heK')
  obtain ⟨R₁, hR₁, hR₁c⟩ := F7E.exists_sylow_comm hV2 (hVN _ hKga heKg) hXV (hX _ hKga heKg)
  have hcen : ∀ {R' : Subgroup Y}, (∀ x ∈ ({a, e} : Set Y), ∀ r ∈ R', r * x = x * r) →
      ∀ x ∈ ({a, e} : Set Y), R' ≤ Subgroup.centralizer ({x} : Set Y) := by
    intro R' h x hx r hr
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h x hx r hr)
  have he' : e ∈ ({a, e} : Set Y) := Or.inr rfl
  have ha' : a ∈ ({a, e} : Set Y) := Or.inl rfl
  have hcov := hgen hcit hP Y R S t K' W u e g hc hno hE hZ R₀ R₀' R₁ hR₀ hR₀' hR₁
    (hcen hR₀c e he') (hcen hR₀'c e he') (hcen hR₁c e he')
  set A := Subgroup.zpowers a with hAdef
  have hAe : A ≤ Subgroup.centralizer ({e} : Set Y) := Subgroup.zpowers_le.mpr hae
  have hleY : ∀ {J R' : Subgroup Y}, J ∈ Om R → IsSylow2In R' J →
      (∀ x ∈ ({a, e} : Set Y), ∀ r ∈ R', r * x = x * r) →
      R' ≤ rLayer (Om R) e ⊓ rLayerSub (Om R) A := by
    intro J R' hJ hR' h
    have hRS : R' ∈ RSet (Om R) := Asc77.mem_RSet_of_isSylow2In hJ hR'
    refine le_inf (F7C.le_rLayer hRS (hcen h e he')) (F7C.le_rLayerSub hRS ?_)
    rw [← Subgroup.le_centralizer_iff, hAdef, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro r hr
    exact h a ha' r hr
  have hcov' : rLayer (Om R) e ≤ oddCoreOf (rLayer (Om R) e) ⊔
      (rLayer (Om R) e ⊓ rLayerSub (Om R) A) :=
    hcov.trans (sup_le_sup_left (sup_le (sup_le (hleY hK hR₀ hR₀c) (hleY hK' hR₀' hR₀'c))
      (hleY hKg hR₁ hR₁c)) _)
  exact F7C.comm_mem_of_cover hΩ hAe hcov' a (Subgroup.mem_zpowers a)

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
