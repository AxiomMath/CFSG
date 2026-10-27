module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieL2
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourBasic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTransfer

public section

namespace CFSG.ComponentClassification.Asc76X.Thm3Four

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G]

@[expose] def IsSmall (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* PSU3 2 2) ∨ Nonempty (X ≃* PSL(2, ZMod 7)) ∨
    Nonempty (X ≃* alternatingGroup (Fin 5)) ∨ Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (X ≃* alternatingGroup (Fin 7))

theorem normal_of_simple [Finite G] {M N : Subgroup G} [hM : M.Normal] (hNM : N ≤ M)
    (hNn : ∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N) (hNs : IsSimpleGroup N)
    (hCN : ∀ c ∈ M, (∀ x ∈ N, c * x = x * c) → c = 1) : N.Normal := by
  constructor
  intro x hx g
  set N₁ := N.map (MulAut.conj g).toMonoidHom with hN₁
  have hN₁M : N₁ ≤ M := by
    rintro _ ⟨y, hy, rfl⟩
    exact hM.conj_mem y (hNM hy) g
  have hN₁n : ∀ m ∈ M, ∀ y ∈ N₁, m * y * m⁻¹ ∈ N₁ := by
    rintro m hm _ ⟨y, hy, rfl⟩
    have hm' : g⁻¹ * m * g ∈ M := by
      have h1 := hM.conj_mem m hm g⁻¹
      rwa [inv_inv] at h1
    refine ⟨g⁻¹ * m * g * y * (g⁻¹ * m * g)⁻¹, hNn _ hm' y hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hI : ((N ⊓ N₁).subgroupOf N).Normal := by
    constructor
    intro a ha b
    exact ⟨(b * a * b⁻¹).2, hN₁n b (hNM b.2) a ha.2⟩
  rcases hI.eq_bot_or_eq_top with hb | ht
  · exfalso
    have hcomm : ∀ y ∈ N₁, ∀ a ∈ N, a * y = y * a := fun y hy a ha => by
      have h1 : a * y * a⁻¹ * y⁻¹ ∈ N ⊓ N₁ := by
        refine mem_inf.mpr ⟨?_, ?_⟩
        · have h2 := hNn y (hN₁M hy) a⁻¹ (inv_mem ha)
          have e : a * y * a⁻¹ * y⁻¹ = a * (y * a⁻¹ * y⁻¹) := by group
          rw [e]
          exact mul_mem ha h2
        · exact mul_mem (hN₁n a (hNM ha) y hy) (inv_mem hy)
      have h2 : (⟨_, h1.1⟩ : N) ∈ (N ⊓ N₁).subgroupOf N := h1
      rw [hb, mem_bot] at h2
      have h3 : a * y * a⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h2
      calc a * y = a * y * a⁻¹ * y⁻¹ * (y * a) := by group
        _ = y * a := by rw [h3, one_mul]
    have hN₁bot : N₁ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [mem_bot]
      exact hCN y (hN₁M hy) fun a ha => (hcomm y hy a ha).symm
    have : Nontrivial N := hNs.toNontrivial
    obtain ⟨a, ha1⟩ := exists_ne (1 : N)
    have h4 : g * (a : G) * g⁻¹ ∈ N₁ := ⟨a, a.2, rfl⟩
    rw [hN₁bot, mem_bot] at h4
    apply ha1
    apply Subtype.ext
    calc (a : G) = g⁻¹ * (g * (a : G) * g⁻¹) * g := by group
      _ = 1 := by rw [h4]; group
  · have hle : N ≤ N₁ := fun y hy => by
      have h1 : (⟨y, hy⟩ : N) ∈ (N ⊓ N₁).subgroupOf N := by rw [ht]; exact mem_top _
      exact h1.2
    have hcard : Nat.card N₁ = Nat.card N := card_map_of_injective (MulAut.conj g).injective
    have heq : N = N₁ := eq_of_le_of_card_ge hle (by rw [hcard])
    have h1 : g * x * g⁻¹ ∈ N₁ := ⟨x, hx, rfl⟩
    rwa [← heq] at h1

theorem four_dvd_card_psl2 {F : Type} [Field F] [Finite F]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F)) :
    4 ∣ Nat.card (CFSG.GorensteinWalter.PSL2 F) := by
  rw [CFSG.GorensteinWalter.psl2_card_formula F hF]
  obtain ⟨p, n, -, hpodd, -, hq⟩ := hF
  have hqodd : Odd (Nat.card F) := hq ▸ hpodd.pow
  obtain ⟨k, hk⟩ := hqodd
  rw [hk]
  have h8 : 8 ∣ (2 * k + 1) ^ 2 - 1 := by
    have e : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      rw [show (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 by ring]
      omega
    rw [e]
    obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
    rw [hj]
    exact ⟨j, by ring⟩
  obtain ⟨m, hm⟩ := h8
  rw [hm, show (2 * k + 1) * (8 * m) = 2 * (4 * ((2 * k + 1) * m)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
  exact dvd_mul_right 4 _

namespace Setting

variable {K R S : Subgroup G} [Finite G]

theorem small_of_psl2
    (h : Setting K R S) (hKn : ¬ K.Normal) {M N : Subgroup G} [hMn : M.Normal]
    (hRM : R ≤ M) (hMR : M ≤ normalClosure (R : Set G)) (hSM : IsSylowOf 2 (S ⊓ M) M)
    (hmeet : ∀ V : Subgroup G, V ≤ S ⊓ M → 4 ≤ Nat.card V → V ⊓ R ≠ ⊥)
    {F : Type} [Field F] [Finite F] (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hNM : N ≤ M) (hNn : ∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N)
    (eN : N ≃* CFSG.GorensteinWalter.PSL2 F)
    (hCN : ∀ c ∈ M, (∀ x ∈ N, c * x = x * c) → c = 1) : IsSmall G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ Nat.card F := by omega
  have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hNs : IsSimpleGroup N := eN.isSimpleGroup
  have hNnG : N.Normal := normal_of_simple hNM hNn hNs hCN
  have hRN : R ⊓ N ≠ ⊥ := by
    have hP := hSM.inf_of_le_normalizer hNM (fun m hm => mem_normalizer_iff.mpr fun y =>
      ⟨fun hy => hNn m hm y hy, fun hy => by
        have h1 := hNn m⁻¹ (inv_mem hm) _ hy
        simpa [mul_assoc] using h1⟩)
    have hcard := (isSylowOf_iff_card.mp hP).2
    have hdvd : 4 ∣ Nat.card N := by
      rw [Nat.card_congr eN.toEquiv]
      exact four_dvd_card_psl2 hF
    have h2 : 2 ≤ (Nat.card N).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (by simpa using hdvd)
    have h4P : 4 ≤ Nat.card ↥(S ⊓ M ⊓ N) := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (Nat.card N).factorization 2 := Nat.pow_le_pow_right (by norm_num) h2
    have h5' := hmeet _ inf_le_left h4P
    intro hb
    apply h5'
    rw [eq_bot_iff]
    intro x hx
    have h6 : x ∈ R ⊓ N := ⟨hx.2, hx.1.2⟩
    rw [hb] at h6
    exact h6
  have hNK := h.not_le_normalizer hKn N hNs hRN
  have hgen : ¬ N ≤ CFSG.ComponentClassification.AschbacherKnownGroup.centralizerJoin R N := by
    intro hle
    apply hNK
    refine hle.trans (iSup_le fun u => iSup_le fun hu => iSup_le fun hu1 => ?_)
    have hu2 : u ^ 2 = 1 := h.elem.2 u hu
    exact inf_le_right.trans (CFSG.ComponentClassification.Asc75T4.centralizer_le_of_involution
      h.tight (h.R_le hu) (orderOf_eq_prime hu2 hu1))
  have hq : CFSG.Open.IsQuasisimple N :=
    CFSG.ComponentClassification.RankTwoOddLie.isQuasisimple_of_mulEquiv eN.symm
      (CFSG.ComponentClassification.RankTwoOddLie.isQuasisimple_psl2 h4)
  have hZ : center N = ⊥ := CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_psl2 h4 eN
  have hdP : CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo
      (CFSG.GorensteinWalter.PSL2 F) :=
    CFSG.ComponentClassification.RankTwoOddLie.hasDihedralSylowTwo_of_gw
      (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hF)
  set eZ : N ⧸ center N ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot with heZ
  have hd : CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo
      (N ⧸ center N) :=
    CFSG.ComponentClassification.RankTwoOddLie.hasDihedralSylowTwo_of_mulEquiv' (eZ.trans eN).symm
      hdP
  have hz : (Nat.card (center N)).factorization 2 ≤ 1 := by
    rw [hZ, card_bot, Nat.factorization_one]
    simp
  have hRnorm : R ≤ normalizer (N : Set G) := by
    rw [normalizer_eq_top_iff.mpr hNnG]
    exact le_top
  have hR4 : CFSG.ComponentClassification.AschbacherKnownGroup.IsFourGroup R := ⟨h.elem, h.card⟩
  obtain ⟨hsmall, hRNC⟩ :=
    CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.dihedral_cover_generation_holds G N
      R hq hd hz hRnorm hR4 hgen
  have hRle : R ≤ N := fun r hr => by
    have h1 : r ∈ ((N ⊔ centralizer (N : Set G) : Subgroup G) : Set G) := hRNC hr
    rw [normal_mul] at h1
    obtain ⟨a, ha, c, hc, hac⟩ := Set.mem_mul.mp h1
    have hcM : c ∈ M := by
      have e : c = a⁻¹ * r := by rw [← hac]; group
      rw [e]
      exact mul_mem (inv_mem (hNM ha)) (hRM hr)
    have hc1 : c = 1 := hCN c hcM fun x hx => (mem_centralizer_iff.mp hc x hx).symm
    rw [← hac, hc1, mul_one]
    exact ha
  have hcardN : Nat.card N = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eN.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F hF]
  have hcardQ : Nat.card (N ⧸ center N) = Nat.card N := Nat.card_congr eZ.toEquiv
  have hqodd : Odd (Nat.card F) := by
    obtain ⟨p, n, -, hpodd, -, hq⟩ := hF
    exact hq ▸ hpodd.pow
  have hq579 : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9 := by
    rcases hsmall with ⟨⟨eA⟩⟩ | ⟨p', f', hq', hmodel⟩
    · exfalso
      have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup]
        simp [Nat.factorial]
      have h1 := Nat.card_congr eA.toEquiv
      rw [hcardQ, hcardN, h7] at h1
      exact CFSG.ComponentClassification.RankTwoOddLie.card_psl2_ne_2520 h5 hqodd h1
    · have : Fact p'.Prime := ⟨hmodel.1.1⟩
      obtain ⟨e'⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField _ 2
        p' f' hmodel
      have hf' : f' ≠ 0 := by have := hmodel.1.2.1; omega
      have hp'odd : Odd p' := by
        refine (Fact.out : p'.Prime).odd_of_ne_two fun h2 => ?_
        subst h2
        have hev : Even (2 ^ f') := Nat.even_pow.mpr ⟨even_two, hf'⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
        rcases hq' with h1 | h1 | h1 <;> rw [h1] at hev <;> exact absurd hev (by decide)
      have hK'' : Nat.card (GaloisField p' f') = p' ^ f' := GaloisField.card p' f' hf'
      have hcard' : Nat.card (N ⧸ center N) = p' ^ f' * ((p' ^ f') ^ 2 - 1) / 2 := by
        rw [Nat.card_congr e'.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _
          ⟨p', f', Fact.out, hp'odd, by omega, hK''⟩, hK'']
      rw [hcardQ, hcardN] at hcard'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
      have hle9 : Nat.card F ≤ 9 := by
        by_contra hlt
        push Not at hlt
        have hmono : 10 * (10 ^ 2 - 1) / 2 ≤ Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
          Nat.div_le_div_right (Nat.mul_le_mul hlt (Nat.sub_le_sub_right
            (Nat.pow_le_pow_left hlt 2) 1))
        rcases hq' with h1 | h1 | h1 <;> rw [h1] at hcard' <;> norm_num at hcard' hmono <;>
          omega
      interval_cases hFc : Nat.card F <;> simp_all <;>
        rcases hq' with h1 | h1 | h1 <;> rw [h1] at hcard' <;> norm_num at hcard'
  have hout : Nat.card (Outer N) ∣ 2 ^ 2 := by
    obtain ⟨p, n, hp, hpodd, hn1, hpn⟩ := hF
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hp F hpn).2 N
      ⟨eN⟩
    have h3 : 3 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 3 with hlt | hge
      · have : p = 2 := by omega
        subst this
        exact absurd hpodd (by decide)
      · exact hge
    have hn2 : n ≤ 2 := by
      by_contra hn
      push Not at hn
      have : 3 ^ 3 ≤ p ^ n := (Nat.pow_le_pow_left h3 3).trans (Nat.pow_le_pow_right
        (by omega) hn)
      rcases hq579 with e | e | e <;> rw [hpn] at e <;> omega
    have hgcd : Nat.gcd 2 (p ^ n - 1) ∣ 2 := Nat.gcd_dvd_left 2 _
    refine h1.trans ?_
    interval_cases n
    · exact (Nat.mul_dvd_mul_left 1 hgcd).trans (by norm_num)
    · exact (Nat.mul_dvd_mul_left 2 hgcd).trans (by norm_num)
  have hMN : M = N := le_antisymm (hMR.trans (normalClosure_le_normal hRle)) hNM
  have hNtop : N = ⊤ := h.eq_top_of_normal N hRle hZ hout
  have eG : G ≃* CFSG.GorensteinWalter.PSL2 F :=
    (topEquiv.symm.trans (MulEquiv.subgroupCongr hNtop.symm)).trans eN
  rcases hq579 with h5 | h7 | h9
  · right; right; left
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inr h5)
    exact ⟨(eG.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)).trans e5⟩
  · right; left
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = Fintype.card (ZMod 7) := by
      rw [ZMod.card, ← Nat.card_eq_fintype_card, h7]
    exact ⟨eG.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
      (FiniteField.ringEquivOfCardEq hc) (Fin 2))⟩
  · right; right; right; left
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨e6⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism F
      (by rw [← Nat.card_eq_fintype_card, h9])
    exact ⟨eG.trans e6⟩

end Setting

end CFSG.ComponentClassification.Asc76X.Thm3Four
