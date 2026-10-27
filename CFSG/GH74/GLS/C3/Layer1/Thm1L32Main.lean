module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Y
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Tables
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Glue
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Loc2
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32LocA7
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32M12Out
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Side
public import CFSG.GH74.GLS.C3.Layer1.Ivk79Pump
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Layer

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1
  CFSG.GH74.GLS.C3.Layer1.PumpCalc

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

open CFSG.GH74.GLS.IVK in
theorem no_l2_iso_alt7 {H : Type} [Group H] {F : Type} [Field F] [Finite F] (e : H ≃* L2 F)
    (hFodd : Odd (Nat.card F)) (e7 : H ≃* alternatingGroup (Fin 7)) : False := by
  have hF3 : 3 < Nat.card F := by
    by_contra hle
    push Not at hle
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨m, hm⟩ := hFodd
    have h3 : Nat.card F = 3 := by omega
    have hodd := Thm1.isOddPrimePower_of_odd F ⟨m, hm⟩
    have hcard : Nat.card H = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
      rw [Nat.card_congr (toPSL e).toEquiv]
      exact GorensteinWalter.psl2_card_formula F hodd
    have h2520 : Nat.card H = 2520 := by
      rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card, Nat.factorial]
    rw [h3] at hcard
    omega
  exact Th2Tstar.not_hasL2Model_alt7 (P := fun q => q = Nat.card F) (fun q hq => hq ▸ hFodd) e7
    (C3.Layer1.Thm1P31c.hasL2Model_of_l2 ⟨hFodd, hF3⟩ e)

end CFSG.GH74.GLS.C3.Layer1.Thm1L32

namespace CFSG.GH74.GLS

theorem b_thm1_L32'_rel_proved
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hGKF : GenericKnownFacts) (hE2 : E2ComponentFacts) (hP31c : B_thm1_P31c_rel) :
    B_thm1_L32'_rel := by
  classical
  have hU : B_thm1_P31_unique_rel := C3.Layer1.Thm1L3Uniq.thm1_P31_unique_of_rel hP31c
  have hcomp : B_thm1_P31_comp_rel := thm1_P31_comp_of_rel hU
  have hP31s : B_thm1_P31s_rel :=
    Thm1.thm1_P31s_of_rel h2hb hcomp (thm1_P31_layer_of_rel h2hb)
  have hTab : C3.Layer1.Thm1L32.StableTables := C3.Layer1.Thm1L32.stableTables_proved hGKF hE2
  have hC2 : C2Facts := Ivk79.c2Facts_of_facts hGKF hE2
  have hLoc2 : C3.Layer1.Thm1L32.LocL2 := fun Z _ _ F _ _ hF L e s hs2 hsL hmove P hPL hP hP1 hPs hsub =>
    C3.Layer1.Thm1L32.l2_fixed_classification hF L e s hs2 hsL hmove P hPL hP hP1 hPs hsub
  have hLocA7 : C3.Layer1.Thm1L32.LocA7 := fun Z _ _ L e7 s hs2 hsL hmove P hPL hP hP1 hPs hsub =>
    C3.Layer1.Thm1L32.a7_fixed_classification L e7 s hs2 hsL hmove P hPL hP hP1 hPs hsub
  have hO1 : C3.Layer1.Thm1L32.M12OuterProp := fun Z _ _ L h s hs2 hsL hout P hPL hP hP1 hPs g hgs hgL hgP =>
    C3.Layer1.Thm1L32.m12_outer_centralizer_inner L h s hs2 hsL hout P hPL hP hP1 hPs g hgs hgL hgP
  intro G _ _ hG hV x y K f hfm h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : Is2TerminalU2Triple x y K := hfm.1.1.1.1
  obtain ⟨T, hT, hfmem⟩ := hfm.1.1.1.2
  have hshape := Thm1.kBar_model_of_U2 hG h102 hL34 hu2
  obtain ⟨hKN, -, -⟩ := hP31s G hG hV x y K hu2 hshape h5
  have hKC : K ≤ centralizer ({x} : Set G) := hu2.1.1.2.1
  have hx2 : orderOf x = 2 := hu2.1.1.1
  obtain ⟨hfT, hf2, hfc, hfx, hlayer⟩ := hfmem
  have hfC : f ∈ centralizer ({x} : Set G) := hT.sylowT.le hfT
  obtain ⟨hfN, hFA'⟩ := thm1_FmemberF_of_rel h2hb G hG hV x y K hu2 hshape hKN T hT f
    ⟨hfT, hf2, hfc, hfx, hlayer⟩ h5
  have hFA : P34.IsFAutL2A7 (kBar K) (Back.actHom hKN ⟨f, hfC⟩) := hFA'
  have hxf : x * f = f * x := (mem_centralizer_singleton_iff.1 hfC).symm
  have hαα : Back.actHom hKN ⟨f, hfC⟩ * Back.actHom hKN ⟨f, hfC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f, hfC⟩ * ⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one f
      rwa [hf2, pow_two] at this
    rw [this, map_one]
  have hKcen : Subgroup.center (kBar K) = ⊥ := by
    rcases hshape with hL2 | h7
    · exact Stage1.Thm6.Glue.center_eq_bot_of_isL2Model
        (Stage1.Thm6.Glue.isL2Model_of_hasL2Model (Bk.B810.hasL2Model_gt_three' hL2))
    · exact Stage1.Thm6.Glue.center_eq_bot_of_isA7Model h7
  have tail : ∀ (r : ℕ) (Λ : Subgroup G), Odd r → 5 ≤ r →
      IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G)) Λ → Λ ≤ K →
      pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) = Λ →
      HasL2Model (kBar Λ) (fun q => q = r) →
      (∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G), ∀ a ∈ Λ, c * a * c⁻¹ ∈ Λ) →
      (r = 5 → C3.Layer1.Thm1L32.KSide K x f Λ) →
      (HasL2Model (kBar K) (fun q => q = r ^ 2) ∨
        (r = 5 ∧ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))) →
      IsPCompIn 2 (centralizer ({f} : Set G)) (pumpJ K f) ∧
        (∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ pumpJ K f, c * j * c⁻¹ ∈ pumpJ K f) ∧
        ∃ r : ℕ, Odd r ∧ 5 ≤ r ∧ HasL2Model (kBar (layerI K f)) (fun q => q = r) ∧
          (HasL2Model (kBar K) (fun q => q = r ^ 2) ∨
            (r = 5 ∧ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))) ∧
          (HasL2Model (kBar (pumpJ K f)) (fun q => q = r) ∨
            HasL2Model (kBar (pumpJ K f)) (fun q => q = r ^ 2) ∨
            Nonempty (kBar (pumpJ K f) ≃* alternatingGroup (Fin 7))) ∧
          (Nonempty (kBar (pumpJ K f) ≃* alternatingGroup (Fin 7)) →
            HasL2Model (kBar K) (fun q => q = 5 ^ 2) ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) := by
    intro r Λ hrodd hr5 hΛ hΛK hlay hΛmod hΛW hKS hKshape
    have hΛU : HasL2Model (kBar Λ) Odd := by
      obtain ⟨p, f', hp, hf', hq, hl⟩ := hΛmod
      exact ⟨p, f', hp, hf', hq ▸ hrodd, hl⟩
    let E : C3.Layer1.Thm1L32.YEnv G x f Λ := ⟨hx2, hf2, hxf, hΛ, hΛU⟩
    have hM12 : ∀ L : Subgroup (barQ ↥(centralizer ({f} : Set G))),
        ∀ S : C3.Layer1.Thm1L32.Stable32 E L, S.sigma ≠ 1 → Shape2M12 ↥L → False :=
      fun L S hσ h2M =>
        S.false_of_2M12 hO1 hG hσ h2M hKC hKcen hΛW hΛK hrodd hΛmod hKS
    obtain ⟨hJc, hJn, hJmod⟩ := C3.Layer1.Thm1L32.ylevel hTab hE2 hC2 hG hLoc2 hLocA7 E hlay hrodd
      hΛmod hM12
    refine ⟨hJc, hJn, r, hrodd, hr5, ?_, hKshape, ?_, ?_⟩
    · show HasL2Model (kBar (pLayerOf 2 (K ⊓ centralizer ({f} : Set G)))) (fun q => q = r)
      rw [hlay]
      exact hΛmod
    · rcases hJmod with h | h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · intro hJA7
      obtain ⟨eJ⟩ := hJA7
      have hr5' : r = 5 := by
        rcases hJmod with h | h | ⟨h, -⟩
        · exact (Th2Tstar.not_hasL2Model_alt7 (P := fun q => q = r) (fun q hq => hq ▸ hrodd) eJ h).elim
        · exact (Th2Tstar.not_hasL2Model_alt7 (P := fun q => q = r ^ 2) (fun q hq => hq ▸ hrodd.pow) eJ h).elim
        · exact h
      rcases hKshape with h | ⟨-, h⟩
      · left
        rwa [hr5'] at h
      · exact Or.inr h
  have hα1 : Back.actHom hKN ⟨f, hfC⟩ ≠ 1 := hFA.1
  rcases hshape with hL2 | h7
  · have h9 := not_hasL2Model_nine_of_noV2Fine hV hu2 h5
    obtain ⟨r, Λ, hrodd, hr5, hKq, hΛ, hΛK, hlay, hΛmod, hcen, hIL2, hΛW, hΛc, himg, F, _, _,
      eF, hF, hFcard, hαF⟩ := C3.Layer1.Thm1L32.layer_L2 hKC hKN hfC hf2 hL2 h9 hFA
    refine tail r Λ hrodd hr5 hΛ hΛK hlay hΛmod hΛW (fun hr => ?_) (Or.inl hKq)
    have hcardF : Nat.card F = 25 := by rw [hFcard, hr]; norm_num
    obtain ⟨hA, hB, hC⟩ := C3.Layer1.Thm1L32.kside_L2 hF hcardF eF _ hαα hα1 hαF
    exact C3.Layer1.Thm1L32.kside_of_data hKC hKN hfC hf2 hΛK himg hΛc hA hB hC
  · obtain ⟨e7⟩ := h7
    have hout : Back.actHom hKN ⟨f, hfC⟩ ∉ IVK.innAut (kBar K) := by
      rcases hFA.2 with ⟨F, _, _, e, hFodd, -⟩ | ⟨-, hout⟩
      · exact (C3.Layer1.Thm1L32.no_l2_iso_alt7 e hFodd e7).elim
      · exact hout
    obtain ⟨Λ, hΛ, hΛK, hlay, hΛmod, hcen, hct, himg, hΛW, hΛc⟩ :=
      C3.Layer1.Thm1L32.layer_A7 hKC hKN hfC hf2 e7 hout hlayer
    refine tail 5 Λ (by decide) le_rfl hΛ hΛK hlay hΛmod hΛW (fun _ => ?_) (Or.inr ⟨rfl, ⟨e7⟩⟩)
    obtain ⟨hA, hB, hC⟩ := C3.Layer1.Thm1L32.kside_A7 e7 _ hαα hct
    exact C3.Layer1.Thm1L32.kside_of_data hKC hKN hfC hf2 hΛK himg hΛc hA hB hC

end CFSG.GH74.GLS
