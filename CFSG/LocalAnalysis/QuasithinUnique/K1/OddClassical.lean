module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassicalAction
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassicalLift
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassicalPSL2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassicalDegreeThree
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups

section Closing

variable {G : Type} [Group G] {H S U L : Subgroup G}

theorem le_centralizer_of_conj_eq {w : G} (h : ∀ y ∈ L, w⁻¹ * y * w = y) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := h y hy
  calc y * w = w * (w⁻¹ * y * w) := by group
    _ = w * y := by rw [this]

variable [Finite G]

theorem centralizes_of_noStrongAb (hSC : StrongClosureComponent H S U L)
    (hsimple : IsSimpleGroup (L ⧸ Subgroup.center L))
    (hev : 2 ∣ Nat.card (L ⧸ Subgroup.center L))
    (hnonab : ∃ x y : L ⧸ Subgroup.center L, x * y ≠ y * x)
    (hN : NoStrongAb (⊤ : Subgroup (L ⧸ Subgroup.center L))) {w : G} (hwU : w ∈ U) :
    L ≤ Subgroup.centralizer ({w} : Set G) :=
  le_centralizer_of_conj_eq ((action_core hSC hsimple hev hnonab).1 hN w hwU)

theorem false_of_torus (hSC : StrongClosureComponent H S U L)
    (hsimple : IsSimpleGroup (L ⧸ Subgroup.center L))
    (hev : 2 ∣ Nat.card (L ⧸ Subgroup.center L))
    (hnonab : ∃ x y : L ⧸ Subgroup.center L, x * y ≠ y * x)
    (hSyl : ∀ Q : Subgroup (L ⧸ Subgroup.center L), IsSylowTwoOf Q ⊤ → Nat.card Q = 4)
    (hodd : OddTorusData (L ⧸ Subgroup.center L)) {w : G} (hwU : w ∈ U)
    (hwL : ¬ L ≤ Subgroup.centralizer ({w} : Set G))
    (hchar : CharTwo (L ⊓ Subgroup.centralizer ({w} : Set G))) : False := by
  obtain ⟨x, hxL, hx⟩ := (action_core hSC hsimple hev hnonab).2 hSyl w hwU
  have hw2 : w * w = 1 := by simpa [sq] using hSC.elem.2 w hwU
  have hsq := sq_central hw2 hxL hx
  have ht2 : (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) *
      QuotientGroup.mk (⟨x, hxL⟩ : L) = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    exact hsq
  have ht1 : (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ Subgroup.center L) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h
    apply hwL
    apply le_centralizer_of_conj_eq
    intro y hy
    rw [hx y hy]
    have h' : y * x = x * y := congrArg Subtype.val (h ⟨y, hy⟩)
    calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
      _ = x⁻¹ * (x * y) := by rw [h']
      _ = y := by group
  obtain ⟨T, hTt, hTn, hTcyc, hTodd, hT1⟩ := hodd _ ht2 ht1
  exact not_charTwo_of_torus hw2 hxL hx T hTt hTn hTcyc hTodd hT1 hchar

end Closing

theorem not_comm_of_simple_of_four_dvd {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h4 : 4 ∣ Nat.card X) : ∃ x y : X, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hcon }
  have hprime := IsSimpleGroup.prime_card (α := X)
  rcases hprime.eq_one_or_self_of_dvd 4 h4 with h | h
  · omega
  · rw [← h] at hprime
    exact absurd hprime (by norm_num)

theorem two_ne_zero_of_card {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcard : Nat.card K = p ^ f) : (2 : K) ≠ 0 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p := by
    refine charP_of_card_eq_prime_pow (f := f) ?_
    rw [← Nat.card_eq_fintype_card]; exact hcard
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

section Bender

theorem card_psl_two_galoisField_two : Nat.card PSL(2, GaloisField 2 2) = 60 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : CharP (GaloisField 2 2) 2 := inferInstance
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := GaloisField 2 2) (_root_.CharTwo.neg_eq 1)
  have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center
    (K := GaloisField 2 2)
  rw [hK, hcenter] at hcard
  norm_num at hcard
  exact hcard

theorem isSimpleGroup_psl_two_galoisField_two : IsSimpleGroup PSL(2, GaloisField 2 2) := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  exact CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl
    (Or.inr (by rw [hK]; norm_num)) (Or.inr (by rw [hK]; norm_num))

end Bender

section PSL2

theorem psl2_model_data {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel X .PSL 2 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : DecidableEq K) (_ : X ≃* PSL(2, K)),
      Fintype.card K = p ^ f ∧ ringChar K ≠ 2 ∧ 5 ≤ Fintype.card K := by
  obtain ⟨⟨hp, hf1, -, -, h23⟩, K, _, _, hcard, ⟨e⟩⟩ := hmodel
  have hfin : Fintype K := Fintype.ofFinite K
  have hqK : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow hqK
  have hF : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have h3 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := Nat.odd_iff.mp hpodd
    omega
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hodd' : p ^ f % 2 = 1 := Nat.odd_iff.mp hpodd.pow
  refine ⟨K, inferInstance, hfin, Classical.decEq K,
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm,
    hqK, hF, ?_⟩
  rw [hqK]
  omega

variable {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}

theorem centralizes_of_psl2_square (hSC : StrongClosureComponent H S U L) {p : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 2 p 2) {w : G} (hwU : w ∈ U) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  classical
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity (L ⧸ Subgroup.center L) 2 p 2 hmodel).2
  have hp : p.Prime := hmodel.1.1
  obtain ⟨K, _, _, _, e', hqK, hF, hq5⟩ := psl2_model_data hp2 hmodel
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hev4 : 4 ∣ Nat.card (L ⧸ Subgroup.center L) := by
    rw [Nat.card_congr e'.toEquiv]; exact psl2_four_dvd_card hF hq5
  have hev : 2 ∣ Nat.card (L ⧸ Subgroup.center L) := (by norm_num : (2 : ℕ) ∣ 4).trans hev4
  have hnonab : ∃ x y : L ⧸ Subgroup.center L, x * y ≠ y * x :=
    have := hsimple
    not_comm_of_simple_of_four_dvd hev4
  have hp8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have h3 : p % 2 = 1 := Nat.odd_iff.mp hpodd
    omega
  have hsq : p ^ 2 % 8 = 1 := by
    rcases hp8 with h | h | h | h <;> simp [Nat.pow_mod, h]
  have h8 : Fintype.card K % 8 = 1 ∨ Fintype.card K % 8 = 7 := Or.inl (by rw [hqK]; exact hsq)
  let e'top : (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≃* PSL(2, K) := Subgroup.topEquiv.trans e'
  exact centralizes_of_noStrongAb hSC hsimple hev hnonab
    (noStrongAb_of_mulEquiv _ e'top (psl2_nasc hF hq5 h8)) hwU

theorem psl2_survivor (hSC : StrongClosureComponent H S U L) {p : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 2 p 1) {w : G} (hwU : w ∈ U)
    (hwL : ¬ L ≤ Subgroup.centralizer ({w} : Set G))
    (hchar : CharTwo (L ⊓ Subgroup.centralizer ({w} : Set G))) :
    p = 5 ∧ IsSimpleGroup (L ⧸ Subgroup.center L) ∧
      (∃ x y : L ⧸ Subgroup.center L, x * y ≠ y * x) ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 2 2 2 ∧
      fusionIsBenderGroup (L ⧸ Subgroup.center L) := by
  classical
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity (L ⧸ Subgroup.center L) 2 p 1 hmodel).2
  have hp : p.Prime := hmodel.1.1
  have h23 : (2, p ^ 1) ≠ (2, 3) := hmodel.1.2.2.2.2
  obtain ⟨K, _, _, _, e', hqK, hF, hq5⟩ := psl2_model_data hp2 hmodel
  have hqp : Fintype.card K = p := by simpa using hqK
  have hp3 : p ≠ 3 := fun h => h23 (by simp [h])
  have hev4 : 4 ∣ Nat.card (L ⧸ Subgroup.center L) := by
    rw [Nat.card_congr e'.toEquiv]; exact psl2_four_dvd_card hF hq5
  have hev : 2 ∣ Nat.card (L ⧸ Subgroup.center L) := (by norm_num : (2 : ℕ) ∣ 4).trans hev4
  have hnonab : ∃ x y : L ⧸ Subgroup.center L, x * y ≠ y * x :=
    have := hsimple
    not_comm_of_simple_of_four_dvd hev4
  have hodd2 : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  let e'top : (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≃* PSL(2, K) := Subgroup.topEquiv.trans e'
  by_cases h8 : Fintype.card K % 8 = 1 ∨ Fintype.card K % 8 = 7
  · exact absurd (centralizes_of_noStrongAb hSC hsimple hev hnonab
      (noStrongAb_of_mulEquiv _ e'top (psl2_nasc hF hq5 h8)) hwU) hwL
  · have h8' : Fintype.card K % 8 = 3 ∨ Fintype.card K % 8 = 5 := by omega
    have hSyl4 : ∀ Q : Subgroup (L ⧸ Subgroup.center L), IsSylowTwoOf Q ⊤ → Nat.card Q = 4 :=
      card_sylow_of_mulEquiv _ e'top (psl2_card_sylow_four hF hq5 h8')
    have hp5 : p = 5 ∨ 11 ≤ p := by omega
    rcases hp5 with hp5 | hp11
    · have hcard5 : Fintype.card K = 5 := by rw [hqp, hp5]
      have hcard60 : Nat.card (L ⧸ Subgroup.center L) = 60 := by
        rw [Nat.card_congr e'.toEquiv]
        have h := psl2_card_mul_two hF hq5
        have h' : Nat.card PSL(2, K) * 2 = 120 := by rw [h, hcard5]; norm_num
        omega
      have := hsimple
      obtain ⟨e1⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
        (G := L ⧸ Subgroup.center L) hcard60
      have := isSimpleGroup_psl_two_galoisField_two
      obtain ⟨e2⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
        (G := PSL(2, GaloisField 2 2)) card_psl_two_galoisField_two
      let e12 : L ⧸ Subgroup.center L ≃* PSL(2, GaloisField 2 2) := e1.trans e2.symm
      refine ⟨hp5, hsimple, hnonab, ?_, Or.inl ⟨2, le_rfl, ⟨e12⟩⟩⟩
      refine ⟨⟨Nat.prime_two, by norm_num, le_rfl, by norm_num, by norm_num⟩, GaloisField 2 2,
        inferInstance, inferInstance, ?_, ⟨e12.trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
            (GaloisField 2 2))⟩⟩
      rw [GaloisField.card 2 2 (by norm_num)]
    · exact (false_of_torus hSC hsimple hev hnonab hSyl4
        (oddTorusData_of_mulEquiv e' (psl2_odd_torus hF (by omega) h8')) hwU hwL hchar).elim

end PSL2

section Degree3

variable {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}

theorem centralizes_of_psl3 (hSC : StrongClosureComponent H S U L) {p : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 p 1) {w : G} (hwU : w ∈ U) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity (L ⧸ Subgroup.center L) 3 p 1 hmodel).2
  obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hmodel
  obtain ⟨hN, hnonab', hev'⟩ := statedSL3_data (two_ne_zero_of_card hp hp2 hcard)
  have hev : 2 ∣ Nat.card (L ⧸ Subgroup.center L) := by
    rw [Nat.card_congr e.toEquiv]; exact hev'
  have hnonab : ∃ x y : L ⧸ Subgroup.center L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnonab'
    exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩
  exact centralizes_of_noStrongAb hSC hsimple hev hnonab
    (noStrongAb_of_mulEquiv _ (Subgroup.topEquiv.trans e) hN) hwU

theorem centralizes_of_psu3 (hSC : StrongClosureComponent H S U L) {p : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 3 p 1) {w : G} (hwU : w ∈ U) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity (L ⧸ Subgroup.center L) 3 p 1 hmodel).2
  obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hmodel
  have hcard' : Nat.card K = p ^ 2 := by rw [hcard, pow_one]
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hN, hnonab', hev'⟩ := statedSU3_data p (p ^ 1) (pow_one p) hp2 hcard'
  have hev : 2 ∣ Nat.card (L ⧸ Subgroup.center L) := by
    rw [Nat.card_congr e.toEquiv]; exact hev'
  have hnonab : ∃ x y : L ⧸ Subgroup.center L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnonab'
    exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩
  exact centralizes_of_noStrongAb hSC hsimple hev hnonab
    (noStrongAb_of_mulEquiv _ (Subgroup.topEquiv.trans e) hN) hwU

end Degree3

theorem k1_oddClassical : K1FamilyRecognition OddClassicalFamily := by
  intro G _ _ H S U L hSC hfam w hwU _ hwL hchar
  obtain ⟨p, hp, hp2, h⟩ := hfam
  rcases h with ⟨f, hf, hmodel⟩ | hmodel | hmodel
  · rcases hf with rfl | rfl
    · exact (psl2_survivor hSC hp2 hmodel hwU hwL hchar).2.2.2.2
    · exact (hwL (centralizes_of_psl2_square hSC hp2 hmodel hwU)).elim
  · exact (hwL (centralizes_of_psl3 hSC hp2 hmodel hwU)).elim
  · exact (hwL (centralizes_of_psu3 hSC hp2 hmodel hwU)).elim

end CFSG.QuasithinUnique.K1
