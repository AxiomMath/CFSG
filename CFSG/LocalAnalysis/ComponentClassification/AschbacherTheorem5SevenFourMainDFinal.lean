module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainDEndgame
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainDCommute
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainDCyclic

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_of_commute_of_pRank_le_one {P : Subgroup G} (hP : IsPGroup 2 P)
    (hr : CFSG.Open.pRank 2 P ≤ 1) (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : IsCyclic P := by
  rcases cyclic_or_quaternion_of_pRank_le_one hP hr with hcyc | ⟨n, hn, ⟨e⟩⟩
  · exact hcyc
  · exfalso
    have hm : 2 ≤ 2 ^ (n - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have htop : Subgroup.center (QuaternionGroup (2 ^ (n - 2))) = ⊤ := by
      rw [eq_top_iff]
      intro q _
      rw [Subgroup.mem_center_iff]
      intro q'
      obtain ⟨z, rfl⟩ := e.surjective q
      obtain ⟨z', rfl⟩ := e.surjective q'
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm _ z'.2 _ z.2)
    have h1 := CFSG.Semidihedral.QuaternionAutomorphismLifting.center_card _ hm
    rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, QuaternionGroup.card] at h1
    omega

theorem exists_orderOf_eq_of_isCyclic {P : Subgroup G} (hc : IsCyclic P) {n : ℕ}
    (hn : n ∣ Nat.card P) : ∃ x ∈ P, orderOf x = n := by
  obtain ⟨c, hcgen⟩ := IsCyclic.exists_generator (α := P)
  have hoc : orderOf c = Nat.card P := orderOf_eq_card_of_forall_mem_zpowers hcgen
  refine ⟨(c ^ (orderOf c / n) : P), (c ^ (orderOf c / n)).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_orderOf_div (orderOf_pos c).ne' (hoc ▸ hn)]

theorem two_pow_dvd_card {P : Subgroup G} (hP : IsPGroup 2 P) {k : ℕ}
    (hk : 2 ^ k ≤ Nat.card P) : 2 ^ k ∣ Nat.card P := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  rw [hm] at hk ⊢
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hk)

variable {D : Subgroup G} {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace FieldHyps

variable {t g : G}

theorem false_of_not_dihedral' (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g)
    (hnd : ∀ k : Fin 2, ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC' := hC.conj g
  obtain ⟨j, hj⟩ := hF.cent
  obtain ⟨m, hjm⟩ : ∃ m : Fin 2, j ≠ m := by
    by_cases hj0 : j = 0
    · exact ⟨1, by rw [hj0]; decide⟩
    · exact ⟨0, hj0⟩
  have hii' : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨e, heA, het, -, hr2, hrnorm, htm⟩ := hF.exists_config hin hC hii' (hnd 0) hjm hj
  set r := e * e with hrdef
  have hrA : r ∈ aschbacherThm5Preimage D (Abar 0) := Subgroup.mul_mem _ heA heA
  have hrt : r * t = t * r := by rw [hrdef, mul_assoc, het, ← mul_assoc, het, mul_assoc]
  have hr1 : r ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hr2
    omega
  have hnd' : ∀ k : Fin 2, ¬ AschbacherKnownGroup.HasDihedralSylowTwo (conjFactors D Abar g k) :=
    fun k => not_dihedral_conjFactor (hnd k) g
  have hCr : Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    centralizer_le_of_mem_factor hC hrA (two_power_of_orderOf hr2) hr1
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (Subgroup.centralizer ({r} : Set G) ⊓
    Subgroup.centralizer ({t} : Set G))
  have hS2 := hS.isPGroup
  obtain ⟨hrS, hRsyl⟩ := hF.isSylowOf_inf_factor hin hC hrA hr2 hrt hS
  have hF' := hF.mirror hC hii' hrA hr2 hrt hrnorm
  have hS' : IsSylowOf 2 S (Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({r} : Set G)) := by
    rw [inf_comm]
    exact hS
  obtain ⟨htS, hTsyl⟩ := hF'.isSylowOf_inf_factor hin hC' htm hF.two hrt.symm hS'
  have htnorm : ∀ k : Fin 2, (aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
      (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ k)).map
        (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
        (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ k) := by
    intro k
    rw [preimage_conjFactors_inv]
    exact hF.norm k
  have hrm : r ∈ aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
      (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ 0) := by
    rw [preimage_conjFactors_inv]
    exact hrA
  have hRL : ¬ S ⊓ aschbacherThm5Preimage D (Abar 0) ≤ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G) := fun h =>
    hF.false_of_le_normalizer hin hC hii' hnd hjm hrA hr2 hrt hrnorm htm hRsyl ⟨hrS, hrA⟩ h
  have hTA : ¬ S ⊓ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar 0) : Set G) := by
    intro h
    have hTA' : S ⊓ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) ≤
        Subgroup.normalizer ((aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
          (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ 0) : Subgroup G) :
            Set G) := by
      rw [preimage_conjFactors_inv]
      exact h
    exact hF'.false_of_le_normalizer hin hC' hjm.symm hnd' hii'.symm htm hF.two hrt.symm htnorm
      hrm hTsyl ⟨htS, htm⟩ hTA'
  obtain ⟨x, ⟨hxS, hxL⟩, hxA⟩ := Set.not_subset.mp hTA
  obtain ⟨y, ⟨hyS, hyA⟩, hyL⟩ := Set.not_subset.mp hRL
  have hR₀ := hF.inf_normalizer_le_other hin hC hii' (hnd 0) htm hrA hr2 hrt hrnorm hS hxS hxL
    hxA
  have hyA' : y ∈ aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
      (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ 0) := by
    rw [preimage_conjFactors_inv]
    exact hyA
  have hT₀' := hF'.inf_normalizer_le_other hin hC' hjm.symm (hnd' m) hrm htm hF.two hrt.symm
    htnorm hS' hyS hyA' hyL
  have hSK : S ≤ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := by
    intro s hs
    rw [normalizer_rightConjugate]
    exact (hF.hyp71 hC).centralizer_le (hS.le hs).2
  have hRcomm := FieldHyps.commute_of_le_other hC hii' hjm hS2 hSK hR₀
  have hSK' : S ≤ Subgroup.normalizer
      ((rightConjugate (rightConjugate D g) g⁻¹ : Subgroup G) : Set G) := by
    rw [rightConjugate_rightConjugate_inv]
    exact fun s hs => hCr (hS.le hs).1
  have hTcomm := FieldHyps.commute_of_le_other (D := rightConjugate D g)
    (Abar := conjFactors D Abar g) (g := g⁻¹) hC' hjm.symm hii'.symm hS2 hSK' hT₀'
  have hRr : CFSG.Open.pRank 2 (S ⊓ aschbacherThm5Preimage D (Abar 0)) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono one_lt_two hRsyl.le).trans
      (hF.pRank_factor_inf_centralizer_le_one hin hC 0)
  have hTr : CFSG.Open.pRank 2 (S ⊓ aschbacherThm5Preimage (rightConjugate D g)
      (conjFactors D Abar g m)) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono one_lt_two hTsyl.le).trans
      (hF'.pRank_factor_inf_centralizer_le_one hin hC' m)
  have hR2 := hRsyl.isPGroup
  have hT2 := hTsyl.isPGroup
  have hRcyc := isCyclic_of_commute_of_pRank_le_one hR2 hRr hRcomm
  have hTcyc := isCyclic_of_commute_of_pRank_le_one hT2 hTr hTcomm
  have hR4 : 2 ^ 2 ≤ Nat.card (S ⊓ aschbacherThm5Preimage D (Abar 0) : Subgroup G) := by
    obtain ⟨e', he'A, he't, he'4⟩ := hF.exists_orderOf_four hin hC hii' (hnd 0)
    have hle : Subgroup.zpowers e' ≤ aschbacherThm5Preimage D (Abar 0) ⊓
        Subgroup.centralizer ({t} : Set G) :=
      Subgroup.zpowers_le.mpr ⟨he'A, Subgroup.mem_centralizer_singleton_iff.mpr he't⟩
    have h2 : IsPGroup 2 (Subgroup.zpowers e') := by
      apply isPGroup_zpowers_two (k := 2)
      rw [show 2 ^ 2 = 4 by norm_num, ← he'4]
      exact pow_orderOf_eq_one e'
    have h3 := IsSylowOf.card_le_of_le hRsyl hle h2
    rw [Nat.card_zpowers, he'4] at h3
    simpa using h3
  have hT8 : 2 ^ 3 ≤ Nat.card (S ⊓ aschbacherThm5Preimage (rightConjugate D g)
      (conjFactors D Abar g m) : Subgroup G) := by
    obtain ⟨e', he'L, he'r, he'4⟩ := hF'.exists_orderOf_four hin hC' hjm.symm (hnd' m)
    have hle : Subgroup.zpowers e' ≤ aschbacherThm5Preimage (rightConjugate D g)
        (conjFactors D Abar g m) ⊓ Subgroup.centralizer ({r} : Set G) :=
      Subgroup.zpowers_le.mpr ⟨he'L, Subgroup.mem_centralizer_singleton_iff.mpr he'r⟩
    have h2 : IsPGroup 2 (Subgroup.zpowers e') := by
      apply isPGroup_zpowers_two (k := 2)
      rw [show 2 ^ 2 = 4 by norm_num, ← he'4]
      exact pow_orderOf_eq_one e'
    have h3 := IsSylowOf.card_le_of_le hTsyl hle h2
    rw [Nat.card_zpowers, he'4] at h3
    have hne4 := fun h4 => hF'.false_of_cyclic_four hin hC' m hTsyl hTcyc h4
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
    rw [hk] at h3 hne4 ⊢
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk3 : k ≠ 2 := by
      rintro rfl
      exact hne4 (by norm_num)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨ρ₁, hρ₁, hρ₁4⟩ := exists_orderOf_eq_of_isCyclic hRcyc (two_pow_dvd_card hR2 hR4)
  have hρ₁sq : ρ₁ ^ 2 = r := by
    have h1 : orderOf (ρ₁ ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hρ₁4]; norm_num), hρ₁4]
      norm_num
    exact eq_of_pRank_le_one hR2 hRr (Subgroup.pow_mem _ hρ₁ 2) ⟨hrS, hrA⟩ h1 hr2
  obtain ⟨h₈, hh₈, hh₈8⟩ := exists_orderOf_eq_of_isCyclic hTcyc (two_pow_dvd_card hT2 hT8)
  set f := h₈ * h₈ with hfdef
  have hf4 : orderOf f = 4 := by
    rw [hfdef, ← sq, orderOf_pow_of_dvd (by norm_num) (by rw [hh₈8]; norm_num), hh₈8]
    norm_num
  have hfT : f ∈ S ⊓ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) :=
    Subgroup.mul_mem _ hh₈ hh₈
  have hfA : f ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar 0) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (sq_map_factor hC.hyp (hCr (hS.le hh₈.1).1) 0)
  have hfsq : f ^ 2 = t := by
    have h1 : orderOf (f ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hf4]; norm_num), hf4]
    exact eq_of_pRank_le_one hT2 hTr (Subgroup.pow_mem _ hfT 2) ⟨htS, htm⟩ h1 hF.two
  set T₀ := S ⊓ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) ⊓
    Subgroup.normalizer (aschbacherThm5Preimage D (Abar 0) : Set G) with hT₀def
  have hT₀T : T₀ ≤ S ⊓ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) :=
    inf_le_left
  have htriv := eq_one_of_pRank_le_one hT2 hTr ⟨htS, htm⟩ hF.two
    (hF.not_mem_D hin hC hii' (hnd 0))
  have hT₀inf : T₀ ⊓ aschbacherThm5Preimage D (Abar 0) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzT, hzA⟩
    exact (Subgroup.mem_bot).mpr (htriv z (hT₀T hzT) (preimage_le D _ hzA))
  have hRT : ∀ a ∈ S ⊓ aschbacherThm5Preimage D (Abar 0), ∀ b ∈ T₀, a * b = b * a := by
    rintro a ⟨haS, haA⟩ b ⟨⟨hbS, hbL⟩, hbA⟩
    exact (hF.commute_sylow' hin hC hii' hnd hjm htm hrA hr2 hrt hrnorm hS hbS hbL hbA haS
      haA).symm
  have hA2 : 2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar 0)) :=
    hF.two_le_pRank hin hC 0
  obtain ⟨P, hP, hRP, hidx⟩ := exists_sylow_index_two hRsyl hRcomm hRr ⟨hrS, hrA⟩ hr2 hρ₁ hρ₁sq
    (hT2.to_le hT₀T) (fun z hz => (hS.le (hT₀T hz).1).2) inf_le_right hT₀inf
    (fun a ha b hb => hTcomm a (hT₀T ha) b (hT₀T hb))
    ((CFSG.SectionRank.pRank_mono one_lt_two hT₀T).trans hTr)
    ⟨⟨htS, htm⟩, Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hF.norm 0)⟩ hF.two
    ⟨hfT, hfA⟩ hfsq hRT hA2
  have hrN : r ∈ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hrnorm m)
  have hrA1 : r ∈ aschbacherThm5Preimage D (Abar 1) := hR₀ ⟨⟨hrS, hrA⟩, hrN⟩
  exact false_of_sylow_index_two hC hii' hP hRP hidx
    (fun s hs hs2 => eq_of_pRank_le_one hR2 hRr hs ⟨hrS, hrA⟩ hs2 hr2) hrA1 hA2

end FieldHyps

theorem caseDImpossible_holds (hin : SectionSevenBase) : CaseDImpossible := by
  intro G _ _ D Abar hC t g r htH ht2 hg hnorm hnd _ _ _ _ htc _
  have hF : FieldHyps D Abar t g := ⟨htH, ht2, hg, ⟨0, htc 0⟩, hnorm⟩
  exact hF.false_of_not_dihedral' hin hC hnd

theorem lemma_7_4_dihedral_holds_of_base (hin : SectionSevenBase) :
    ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
      {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
      Counterexample G D r Abar → ∀ t g : G, t ∈ Subgroup.normalizer (D : Set G) →
        orderOf t = 2 → g ∉ Subgroup.normalizer (D : Set G) →
        (∃ j : Fin r, aschbacherThm5Centralizes (aschbacherThm5Core D)
          (aschbacherThm5Preimage D (Abar j)) (g * t * g⁻¹)) →
        (∀ k : Fin r, (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
          aschbacherThm5Preimage D (Abar k)) →
        ∀ k : Fin r,
          IsSimpleGroup (Abar k) ∧ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k) :=
  lemma_7_4_dihedral_holds hin (caseDImpossible_holds hin)

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
