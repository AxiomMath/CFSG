module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Wr
public import CFSG.GH74.GLS.C3.Layer1.Thm1G35TV
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Rel

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1G33 CFSG.GH74.GLS.C3.Layer1.Thm1G35

namespace CFSG.GH74.GLS

theorem b_thm1_L35_rel_proved
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hL34r : B_thm1_L34_rel) (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel)
    (hL32 : B_thm1_L32'_rel) : B_thm1_L35_rel := by
  intro G _ _ hG hNo x y K T V W f z cfg hA7 h5
  by_contra hVW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPre : Pre35 x y K T V W f z := pre35_of_rel h2hb h102 hL34 hP31s hP31c hG hNo cfg hA7 h5
  by_cases hJ : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f)
  ·
    have E := env33_of_rel h2hb h102 hL34 hP31s hP31c hL32 hG hNo ⟨cfg, hJ⟩ h5
    rcases E.card_secD_cases with h4 | h8
    ·
      have hD4 := E.hDeq4 h4
      have hVT : V ≤ T := by
        intro v hv
        obtain ⟨p, hp, d, hd, rfl⟩ := E.hV_eq_PD hPre.card_P v hv
        rw [hD4] at hd
        exact T.mul_mem hp.1 (hPre.hXT hd)
      exact hPre.false_of_T_eq_V hVW (le_antisymm hPre.hTV hVT)
    · exact E.false_of_card8 hG hVW h8 hA7
  ·
    have hle : layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) ≤ pumpJ K f :=
      sup_le (Thm1.layerI_le_pumpJ K f) (Thm1.pPrimeCoreOf_le_self _)
    have hlt : layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) < pumpJ K f :=
      lt_of_le_of_ne hle (Ne.symm hJ)
    obtain ⟨⟨w, -, hw⟩, hS⟩ := hL34r G hG hNo x y K T f cfg.fmax cfg.setup cfg.mem hlt h5
    obtain ⟨hJc, hJn, r, hrodd, hr5, hI, hKshape, hJshape, -⟩ :=
      hL32 G hG hNo x y K f cfg.fmax h5
    have hr : r = 5 := by
      rcases hKshape with h | ⟨h, -⟩
      · exfalso
        exact Thm1L34.ordA_one_ne_2520 hrodd.pow
          ((Thm1L34.card_kBar_of_hasL2Model h).symm.trans (Thm1L34.card_kBar_of_alt7 hA7))
      · exact h
    subst hr
    have hIJ : layerI K f ≤ pumpJ K f := Thm1.layerI_le_pumpJ K f
    have hJA7 : Nonempty (kBar (pumpJ K f) ≃* alternatingGroup (Fin 7)) := by
      rcases hJshape with h | h | h
      · exact absurd (Thm1L34.sup_eq_of_hasL2Model hIJ hI h) (ne_of_lt hlt)
      · exfalso
        have hshapeJ := Thm1.kBar_model_of_U2 hG h102 hL34 hw
        have h5J : ¬ HasL2Model (kBar (pumpJ K f)) (fun q => q = 5) := by
          intro h'
          have := Thm1L34.ordA_one_inj (q := 5 ^ 2) (q' := 5) (by decide) (by decide)
            ((Thm1L34.card_kBar_of_hasL2Model h).symm.trans (Thm1L34.card_kBar_of_hasL2Model h'))
          omega
        obtain ⟨T', hT'⟩ := Thm1.exists_setup1D f (pumpJ K f)
        obtain ⟨-, -, -, hT⟩ := hP31s G hG hNo f w (pumpJ K f) hw hshapeJ h5J
        obtain ⟨⟨f', hf', -⟩, -, -⟩ := hT T' hT'
        have hle2 := cfg.fmax.1.1.2 f w (pumpJ K f) f' ⟨hw, T', hT', hf'⟩
        rw [Thm1L34.card_kBar_of_hasL2Model h, Thm1L34.card_kBar_of_alt7 hA7,
          show (5 : ℕ) ^ 2 = 25 by norm_num, Thm1L34.ordA_one_25] at hle2
        omega
      · exact h
    obtain ⟨eJ⟩ := hJA7
    have hV32 : Nat.card ↥V ≤ 32 :=
      Thm1L3A7.card_le_32_of_A7 cfg.hf2 cfg.sylowV.isPGroup cfg.sylowV.le hJc.1 hJn eJ hS
    have hTV : T = V := Subgroup.eq_of_le_of_card_ge hPre.hTV (by rw [hPre.card_T]; exact hV32)
    exact hPre.false_of_T_eq_V hVW hTV

end CFSG.GH74.GLS

end
