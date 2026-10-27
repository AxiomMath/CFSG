module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HeisLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TorusLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
public import CFSG.RankThree.PartOne.KS.HSMcL
public import CFSG.Sporadic.Presentation.McLExact
public import Certificates.Certificate19764
public import Certificates.Certificate19765
public import Certificates.Certificate19766
import CFSG.RankThree.PartOne.KP.SporadicDefs

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2
open CFSG.RankThree.Native CFSG.Sporadic.Schreier Certificates.MaxD2Heis
open CFSG.ComponentClassification.OuterAutomorphisms

theorem mcl_tabs_eq :
    mclStrongArrs[0]! = mclTabA ∧ mclStrongArrs[1]! = mclTabB ∧
      CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl =
        mclTabU ∧ mclTabA.size = 275 ∧ mclTabB.size = 275 ∧ mclTabU.size = 275 :=
  Certificates.certificate19766

theorem mcl_tab_a :
    TabRep mclTabA mcl275A := by
  have h := rep_mcl275A
  rw [mcl_tabs_eq.1] at h
  exact ⟨mcl_tabs_eq.2.2.2.1, fun i => h i⟩

theorem mcl_tab_b :
    TabRep mclTabB mcl275B := by
  have h := rep_mcl275B
  rw [mcl_tabs_eq.2.1] at h
  exact ⟨mcl_tabs_eq.2.2.2.2.1, fun i => h i⟩

theorem mcl_tab_u :
    TabRep mclTabU mcl275U := by
  have h := rep_mcl275U
  rw [mcl_tabs_eq.2.2.1] at h
  exact ⟨mcl_tabs_eq.2.2.2.2.2, fun i => h i⟩

theorem hS_two {a b : Tab} {A B : Equiv.Perm (Fin 275)} (ha : TabRep a A) (hb : TabRep b B) :
    ∀ j, TabRep ((#[a, b] : Array Tab).getD j (idTab 275)) ([A, B].getD j 1) :=
  rep_getD_of_forall (L := [a, b]) (P := [A, B]) rfl (by
    intro i hi
    have hi' : i < 2 := hi
    interval_cases i
    · exact ha
    · exact hb)

theorem hS_three {a b c : Tab} {A B C : Equiv.Perm (Fin 275)} (ha : TabRep a A)
    (hb : TabRep b B) (hc : TabRep c C) :
    ∀ j, TabRep ((#[a, b, c] : Array Tab).getD j (idTab 275)) ([A, B, C].getD j 1) :=
  rep_getD_of_forall (L := [a, b, c]) (P := [A, B, C]) rfl (by
    intro i hi
    have hi' : i < 3 := hi
    interval_cases i
    · exact ha
    · exact hb
    · exact hc)

theorem mclFiveDataP_hS :
    ∀ j, TabRep (mclFiveDataP.gT.getD j (idTab 275)) ([mcl275A, mcl275B].getD j 1) :=
  hS_two mcl_tab_a mcl_tab_b

theorem mclFiveDataR_hS :
    ∀ j, TabRep (mclFiveDataR.gT.getD j (idTab 275))
      ([mcl275A, mcl275B, mcl275U].getD j 1) :=
  hS_three mcl_tab_a mcl_tab_b mcl_tab_u

theorem mcl_five_check_P :
    checkHeis mclFiveDataP = true :=
  Certificates.certificate19764

theorem mcl_five_check_R :
    checkHeis mclFiveDataR = true :=
  Certificates.certificate19765

theorem mclP_closure_eq :
    Subgroup.closure {g | g ∈ [mcl275A, mcl275B]} = mcl275P := by
  unfold mcl275P
  congr 1
  ext g
  simp

theorem mclR_closure_eq :
    Subgroup.closure {g | g ∈ [mcl275A, mcl275B, mcl275U]} = mcl275R := by
  unfold mcl275R
  congr 1
  ext g
  simp

theorem mcl_heisData_P :
    ∃ R₀ : Subgroup (Equiv.Perm (Fin 275)), HeisData 5 2 3 12 mcl275P R₀ := by
  have h := heisData_of_check (S := [mcl275A, mcl275B]) (D := mclFiveDataP) rfl
    (by show Nat.Prime 5; norm_num) mclFiveDataP_hS
    (by
      have h1 : [mcl275A, mcl275B].length = 2 := rfl
      have h2 : mclFiveDataP.gT.size = 2 := rfl
      rw [h1, h2])
    (by rw [mclP_closure_eq]; exact card_mclP)
    ⟨3, 1, by show (3000 : ℕ) = 5 ^ 3 * (2 ^ 3 * 3 ^ 1); norm_num⟩ mcl_five_check_P
  rwa [mclP_closure_eq] at h

theorem mcl_heisData_R
    (hcard : Nat.card mcl275R = 1796256000) :
    ∃ R₀ : Subgroup (Equiv.Perm (Fin 275)), HeisData 5 2 3 12 mcl275R R₀ := by
  have h := heisData_of_check (S := [mcl275A, mcl275B, mcl275U]) (D := mclFiveDataR) rfl
    (by show Nat.Prime 5; norm_num) mclFiveDataR_hS
    (by
      have h1 : [mcl275A, mcl275B, mcl275U].length = 3 := rfl
      have h2 : mclFiveDataR.gT.size = 3 := rfl
      rw [h1, h2])
    (by rw [mclR_closure_eq]; exact hcard)
    ⟨4, 1, by show (6000 : ℕ) = 5 ^ 3 * (2 ^ 4 * 3 ^ 1); norm_num⟩ mcl_five_check_R
  rwa [mclR_closure_eq] at h

theorem orderOf_three_zmod_five : orderOf ((3 : ℕ) : ZMod 5) = 5 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

theorem card_mcl275R :
    Nat.card mcl275R = 1796256000 := by
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hcard⟩⟩ :=
    CTUC_HS_McL_full_automorphism_permutation_models
  exact hcard

theorem heisLocal_mclP
    {X : Type*} [Group X]
    [Finite X] (e : X ≃* mcl275P) (R : Sylow 5 X) : HeisLocal 5 (R : Subgroup X) := by
  obtain ⟨R₀, hR₀⟩ := mcl_heisData_P
  have hT := heisLocal_of_heisData hR₀ (le_refl 2) orderOf_three_zmod_five (by norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine heisLocal_sylow e hT ?_ R
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀.1).toEquiv, hR₀.2.1,
    factorization_card_mcl275P_five]

theorem heisLocal_mclR
    (hcard : Nat.card mcl275R = 1796256000) {X : Type*} [Group X] [Finite X]
    (e : X ≃* mcl275R) (R : Sylow 5 X) : HeisLocal 5 (R : Subgroup X) := by
  obtain ⟨R₀, hR₀⟩ := mcl_heisData_R hcard
  have hT := heisLocal_of_heisData hR₀ (le_refl 2) orderOf_three_zmod_five (by norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine heisLocal_sylow e hT ?_ R
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀.1).toEquiv, hR₀.2.1, hcard,
    factorization_eq_of_pow_dvd Nat.prime_five (k := 3) (by norm_num) (by norm_num)
      (by norm_num)]

theorem eq_or_eq_of_between {G : Type*} [Group G] [Finite G] {P B R : Subgroup G}
    (hPB : P ≤ B) (hBR : B ≤ R) (hcard : Nat.card R = 2 * Nat.card P) : B = P ∨ B = R := by
  have h1 : Nat.card P ∣ Nat.card B := Subgroup.card_dvd_of_le hPB
  have h2 : Nat.card B ∣ Nat.card R := Subgroup.card_dvd_of_le hBR
  obtain ⟨k, hk⟩ := h1
  have hpos : 0 < Nat.card P := Nat.card_pos
  rw [hk, hcard] at h2
  have hk2 : k ∣ 2 := by
    have : Nat.card P * k ∣ Nat.card P * 2 := by rwa [mul_comm 2] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hpos this
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hPB (by rw [hk, mul_one])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hBR (by rw [hcard, hk, mul_comm])

theorem d2HeisLocalAt_mcl :
    D2HeisLocalAt (.sporadic .McL) fun p => p = 5 := by
  intro X _ _ K hKn hC ⟨e⟩ p hp R
  have hp5 : p = 5 := hp
  subst hp5
  have : K.Normal := hKn
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let θ : K ≃* mcl275P := (e.trans eC.symm).trans mcl275Equiv
  refine ⟨?_, ?_⟩
  ·
    rw [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv θ]
    have h2 := outer_card_mcl275P
    have hpos : 0 < Nat.card (Outer mcl275P) := Nat.card_pos
    intro hdvd
    have := Nat.le_of_dvd hpos hdvd
    omega
  ·
    have hcardR := card_mcl275R
    have hmodel := CFSG.RankThree.PartOne.mcl_autModel
    have hinj := hmodel.embed_injective K θ hC
    set ι := hmodel.embed K θ with hι
    have hPB : mcl275P ≤ ι.range := fun y hy =>
      ⟨(θ.symm ⟨y, hy⟩ : K), by rw [hι, hmodel.embed_coe, MulEquiv.apply_symm_apply]⟩
    have hBR : ι.range ≤ mcl275R := by
      rintro _ ⟨x, rfl⟩
      exact hmodel.embed_mem K θ x
    have hcard2 : Nat.card mcl275R = 2 * Nat.card mcl275P := by
      rw [hcardR]
      have := card_mclP
      rw [mcl275P_eq, this]
    let eX : X ≃* ι.range := MonoidHom.ofInjective hinj
    rcases eq_or_eq_of_between hPB hBR hcard2 with hB | hB
    · exact heisLocal_mclP (eX.trans (MulEquiv.subgroupCongr hB)) R
    · exact heisLocal_mclR hcardR (eX.trans (MulEquiv.subgroupCongr hB)) R

end CFSG.AGLEmbeddingD2
