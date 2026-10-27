module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelBase
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3A7
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L3A7

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

theorem thm1_L36A7_of_rel
    (h34a : B_thm1_L34a_rel) (hP31c : B_thm1_P31c_rel) (hP31 : B_thm1_P31s_rel)
    (hL32 : B_thm1_L32'_rel) : B_thm1_L36A7_rel := by
  intro G _ _ hG hNo x y K T V W f z cfg hlt hJA7 hK25 h5
  obtain ⟨hJc, hJn, -⟩ := hL32 G hG hNo x y K f cfg.fmax h5
  obtain ⟨w, -, hw⟩ := h34a G hG hNo x y K T f cfg.fmax cfg.setup cfg.mem hlt h5
  have hS : IsSylowOf 2 (zpowers f) (CxK f (pumpJ K f)) :=
    hP31c G hG hNo f w _ hw (not_hasL2Model_five_of_alt7 hJA7)
  obtain ⟨e⟩ := hJA7
  have h32 : Nat.card ↥V ≤ 32 :=
    card_le_32_of_A7 cfg.hf2 cfg.sylowV.isPGroup cfg.sylowV.le hJc.1 hJn e hS
  refine h32.trans ?_
  have hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) :=
    Or.inl (Back.hasL2Model_mono (fun q hq => by subst hq; exact ⟨12, by norm_num⟩) hK25)
  obtain ⟨hKN, -, -, hTdata⟩ := hP31 G hG hNo x y K cfg.hu2 hshape h5
  obtain ⟨⟨f', hf'mem, hf'ind⟩, -⟩ := hTdata T cfg.setup
  have hKcomp : IsPCompIn 2 (centralizer ({x} : Set G)) K := cfg.hu2.1.1.2
  have hcen : center (kBar K) = ⊥ :=
    PumpCalc.center_eq_bot_of_isSimple (Back.isSimpleGroup_of_hasL2Model hK25)
      (TwoThin.isQuasisimple_hat hKcomp)
  have hKcard : Nat.card (kBar K) = 7800 := by
    rw [Thm1L34.card_kBar_of_hasL2Model hK25, show (5 : ℕ) ^ 2 = 25 by norm_num,
      Thm1L34.ordA_one_25]
  have hout : ∃ (f' : G) (hf' : f' ∈ T), Back.actHom hKN ⟨f', cfg.setup.sylowT.le hf'⟩ ∉
      IVK.innAut (kBar K) := by
    refine ⟨f', hf'mem.1, ?_⟩
    obtain ⟨hf, hα1, hα⟩ := hf'ind
    have hdef : Back.actHom hKN ⟨f', cfg.setup.sylowT.le hf'mem.1⟩ =
        inducedQuotAut K (pPrimeCore 2 ↥K) ⟨f', hf⟩ := rfl
    rw [hdef]
    rcases hα with ⟨F, _, _, e', -, hfield⟩ | ⟨hA7, -⟩
    · intro hin
      exact hα1 (C3.Layer1.Thm1.eq_one_of_mem_fieldAutSub_of_mem_innDiagSub e' hfield
        (IVK.innAut_le_innDiagSub e' hin))
    · exfalso
      have := Thm1L34.card_kBar_of_alt7 hA7
      omega
  exact card_ge_32_of_L2_25 cfg.hx2 cfg.hKx hKN cfg.setup.sylowT hK25 hcen hout

end CFSG.GH74.GLS.C3.Layer1.Thm1L3A7

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L36

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

theorem thm1_L36_of_rel
    (h34a : B_thm1_L34a_rel) (h35 : B_thm1_L35_rel) (h33c : B_thm1_L33c'_rel)
    (h33d : B_thm1_L33d_rel) (h33f : B_thm1_L33f_rel) (hL32 : B_thm1_L32'_rel)
    (hP31 : B_thm1_P31s_rel) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hA7 : B_thm1_L36A7_rel) : B_thm1_L36_rel := by
  intro G _ _ hG hNo x y K T V W f z cfg h5
  by_cases hVW : V = W
  · exact Or.inl hVW
  refine Or.inr ?_
  have hnotA7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := fun h =>
    hVW (h35 G hG hNo x y K T V W f z cfg h h5)
  obtain ⟨hJc, hJn, r, hrodd, hr5, hI, hKshape, hJshape, hA7'⟩ :=
    hL32 G hG hNo x y K f cfg.fmax h5
  have hKL2 : HasL2Model (kBar K) (fun q => q = r ^ 2) :=
    hKshape.resolve_right (fun h => hnotA7 h.2)
  by_cases hJeq : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f)
  ·
    have hyp : Hyp33 x y K T V W f z := ⟨cfg, hJeq⟩
    have h4 := cfg.four_le_card_secD hJeq hJn
    have hDp : IsPGroup 2 ↥(secD K f V) := cfg.sylowV.isPGroup.to_le inf_le_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hDp
    by_cases hD8 : 8 ≤ Nat.card ↥(secD K f V)
    · exfalso
      obtain ⟨hzf, -⟩ := h33c G hG hNo x y K T V W f z hyp hD8 hVW h5
      exact hnotA7 (h33f G hG hNo x y K T V W f z hyp hzf h5).2
    · have hD4 : Nat.card ↥(secD K f V) = 4 := by
        have hk3 : k < 3 := by
          by_contra hk3
          push Not at hk3
          have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
          omega
        have hk2 : k = 2 := by
          by_contra hne
          have hk1 : k ≤ 1 := by omega
          have : 2 ^ k ≤ 2 := calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
            _ = 2 := by norm_num
          omega
        rw [hk, hk2]
        norm_num
      obtain ⟨hxZ, -⟩ := h33d G hG hNo x y K T V W f z hyp hD4 (Or.inl hVW) h5
      have hVC : V ≤ centralizer ({x} : Set G) := fun v hv =>
        mem_centralizer_singleton_iff.2 (hxZ.2 v hv)
      exact Thm1L3.card_le_of_isPGroup_of_isSylowOf cfg.sylowV.isPGroup hVC cfg.setup.sylowT
  ·
    have hle : layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) ≤ pumpJ K f :=
      sup_le (Thm1.layerI_le_pumpJ K f) (Thm1.pPrimeCoreOf_le_self _)
    have hlt : layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) < pumpJ K f :=
      lt_of_le_of_ne hle (Ne.symm hJeq)
    have hIJ : layerI K f ≤ pumpJ K f := Thm1.layerI_le_pumpJ K f
    have hJshape' : HasL2Model (kBar (pumpJ K f)) (fun q => q = r ^ 2) ∨
        Nonempty (kBar (pumpJ K f) ≃* alternatingGroup (Fin 7)) := by
      rcases hJshape with h | h | h
      · exact absurd (Thm1L34.sup_eq_of_hasL2Model hIJ hI h) (ne_of_lt hlt)
      · exact Or.inl h
      · exact Or.inr h
    rcases hJshape' with hJ2 | hJA7
    ·
      obtain ⟨w, -, hw⟩ := h34a G hG hNo x y K T f cfg.fmax cfg.setup cfg.mem hlt h5
      have hshape := Thm1.kBar_model_of_U2 hG h102 hL34 hw
      obtain ⟨T', hT'⟩ := Thm1.exists_setup1D f (pumpJ K f)
      obtain ⟨-, -, -, hT⟩ := hP31 G hG hNo f w (pumpJ K f) hw hshape
        (not_hasL2Model_five_of_sq hrodd hr5 hJ2)
      obtain ⟨⟨f', hf', -⟩, -, -⟩ := hT T' hT'
      have hcards : Nat.card (kBar K) = Nat.card (kBar (pumpJ K f)) := by
        rw [Thm1L34.card_kBar_of_hasL2Model hKL2, Thm1L34.card_kBar_of_hasL2Model hJ2]
      have hF1 : FMax1 f w (pumpJ K f) f' :=
        ⟨⟨hw, T', hT', hf'⟩, fun x' y' K' f'' h'' => by
          have := cfg.fmax.1.1.2 x' y' K' f'' h''
          rw [hcards] at this
          exact this⟩
      have hle2 := cfg.fmax.1.2 f w (pumpJ K f) f' hF1
      calc Nat.card ↥V = twoPartCard (centralizer ({f} : Set G)) := cfg.sylowV.card_eq
        _ ≤ twoPartCard (centralizer ({x} : Set G)) := hle2
        _ = Nat.card ↥T := cfg.setup.sylowT.card_eq.symm
    ·
      rcases hA7' hJA7 with hK25 | hKA7
      · exact hA7 G hG hNo x y K T V W f z cfg hlt hJA7 hK25 h5
      · exact absurd hKA7 hnotA7

end CFSG.GH74.GLS.C3.Layer1.Thm1L36
