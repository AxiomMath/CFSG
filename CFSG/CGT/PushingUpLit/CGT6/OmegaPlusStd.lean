module

public import CFSG.CGT.PushingUpLit.CGT6.Nine7Defs
public import CFSG.Open.StandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21L2

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.ComponentClassification CFSG.CGT.PushingUpLit.CGT6
open CFSG.ABGLocalTools (IsSylowOf)
open Subgroup

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem std_isSimpleGroup_sl2 {n : ℕ} (hn : 2 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm.isSimpleGroup

omit [Finite Γ] in
theorem std_tightlyEmbedded {D : Subgroup Γ} (hD : Open.standardIsStandardSubgroup D) :
    AschbacherTightEmbedding.TightlyEmbedded (centralizer (D : Set Γ)) :=
  (AschbacherTightEmbedding.tightlyEmbedded_iff_classical _).2 ⟨hD.2.1, hD.2.2.1⟩

omit [Finite Γ] in
theorem std_inf_eq_bot_of_odd {B N : Subgroup Γ} [IsSimpleGroup B]
    (hBN : B ≤ normalizer (N : Set Γ)) (hN : Odd (Nat.card N)) (hB : Even (Nat.card B)) :
    B ⊓ N = ⊥ := by
  have hn : (N.subgroupOf B).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    simpa using (mem_normalizer_iff.mp (hBN g.2) x).mp hx⟩
  rcases hn.eq_bot_or_eq_top with h | h
  · exact disjoint_iff.mp (subgroupOf_eq_bot.mp h).symm
  · exact absurd (hN.of_dvd_nat (card_dvd_of_le (subgroupOf_eq_top.mp h)))
      (Nat.not_odd_iff_even.mpr hB)

omit [Finite Γ] in
theorem std_le_twoPrimeLayerIn {B Q : Subgroup Γ} [IsSimpleGroup B] (hBQ : B ≤ Q)
    (hQB : Q ≤ normalizer (B : Set Γ)) (hnab : ∃ a b : B, a * b ≠ b * a)
    (hBO : B ⊓ AS76b.oddCoreIn Q = ⊥) : B ≤ AS76b.twoPrimeLayerIn Q := by
  set O := CFSG.Assembly.oddCore Q
  have hn : (B.subgroupOf Q).Normal := (normal_subgroupOf_iff_le_normalizer hBQ).mpr hQB
  have hq : CFSG.IsQuasisimple (B.subgroupOf Q) :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hBQ).symm
      (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  have hker : ¬ B.subgroupOf Q ≤ (QuotientGroup.mk' O).ker := by
    rw [QuotientGroup.ker_mk']
    intro h
    have hle : B ≤ AS76b.oddCoreIn Q := fun b hb =>
      ⟨⟨b, hBQ hb⟩, h (show (⟨b, hBQ hb⟩ : Q) ∈ B.subgroupOf Q from hb), rfl⟩
    exact (nontrivial_iff_ne_bot B).mp inferInstance ((inf_eq_left.mpr hle).symm.trans hBO)
  have hK : CFSG.IsComponent ((B.subgroupOf Q).map (QuotientGroup.mk' O)) :=
    ⟨LocalCores.isQuasisimple_map hq _ hker,
      (hn.map _ (QuotientGroup.mk'_surjective O)).isSubnormal⟩
  have hle := LocalCores.component_le_layer hK
  intro b hb
  exact ⟨⟨b, hBQ hb⟩, hle ⟨⟨b, hBQ hb⟩, hb, rfl⟩, rfl⟩

theorem std_two_pow_dvd_card {B Q T W : Subgroup Γ} [IsSimpleGroup B] (hBQ : B ≤ Q)
    (hQB : Q ≤ normalizer (B : Set Γ)) (hnab : ∃ a b : B, a * b ≠ b * a)
    (hBe : Even (Nat.card B)) (hBO : B ⊓ AS76b.oddCoreIn Q = ⊥)
    (hTN : T ≤ normalizer (Q : Set Γ)) (hW : W = AS76b.oUpperTwoPrime (Q ⊔ T)) {n : ℕ}
    (hn : 2 ≤ n)
    (φ : W →* Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ) (hker : φ.ker = (AS76b.oddCoreIn Q).subgroupOf W) :
    2 ^ n ∣ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWN : W ≤ normalizer (Q : Set Γ) := by
    rw [hW]
    exact (AS76b.oUpperTwoPrime_le _).trans (sup_le le_normalizer hTN)
  have hBW : B ≤ W := by
    have hBN : B ≤ normalizer (W : Set Γ) := by
      rw [hW]
      exact (hBQ.trans le_sup_left).trans
        (le_normalizer.trans (AS76b.normalizer_le_normalizer_oUpperTwoPrime _))
    have hWB : (W.subgroupOf B).Normal := ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      simpa using (mem_normalizer_iff.mp (hBN g.2) x).mp hx⟩
    rcases hWB.eq_bot_or_eq_top with h | h
    · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 (even_iff_two_dvd.mp hBe)
      have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
      have hxW : (x : Γ) ∈ W := by
        rw [hW]
        exact AS76b.mem_oUpperTwoPrime (mem_sup_left (hBQ x.2)) (n := 1)
          (by simpa using congrArg Subtype.val hx2)
      have hx1 : x = 1 := mem_bot.mp (h ▸ (show x ∈ W.subgroupOf B from hxW))
      rw [hx1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · exact subgroupOf_eq_top.mp h
  let ψ : W →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := (MonoidHom.snd _ _).comp φ
  have hψ : Function.Surjective ψ := fun s => by
    obtain ⟨y, hy⟩ := hφ (1, s)
    exact ⟨y, by simp [ψ, hy]⟩
  have hS := std_isSimpleGroup_sl2 hn
  have hQW : (Q.subgroupOf W).Normal := ⟨fun x hx w => by
    rw [mem_subgroupOf] at hx ⊢
    simpa using (mem_normalizer_iff.mp (hWN w.2) x).mp hx⟩
  have hM : (B.subgroupOf W).map ψ = ⊥ ∨ (B.subgroupOf W).map ψ = ⊤ := by
    rcases (hQW.map ψ hψ).eq_bot_or_eq_top with h | h
    · exact .inl (le_bot_iff.mp ((map_mono
        (fun x hx => hBQ hx : B.subgroupOf W ≤ Q.subgroupOf W)).trans h.le))
    · have hMn : ((B.subgroupOf W).map ψ).Normal := ⟨fun m hm s => by
        obtain ⟨b, hb, rfl⟩ := mem_map.mp hm
        obtain ⟨q, hq, rfl⟩ := mem_map.mp (h ▸ mem_top s : s ∈ (Q.subgroupOf W).map ψ)
        refine mem_map.mpr ⟨q * b * q⁻¹, ?_, by simp only [map_mul, map_inv]⟩
        rw [mem_subgroupOf] at hb hq ⊢
        simpa using (mem_normalizer_iff.mp (hQB hq) b).mp hb⟩
      exact hMn.eq_bot_or_eq_top
  rcases hM with h | h
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hψ1 : ∀ x : B, (φ ⟨x, hBW x.2⟩).2 = 1 := fun x => by
      have : ψ ⟨x, hBW x.2⟩ ∈ (B.subgroupOf W).map ψ := ⟨⟨x, hBW x.2⟩, x.2, rfl⟩
      rwa [h, mem_bot] at this
    have hc : φ (⟨a, hBW a.2⟩ * ⟨b, hBW b.2⟩) = φ (⟨b, hBW b.2⟩ * ⟨a, hBW a.2⟩) := by
      rw [map_mul, map_mul]
      refine Prod.ext (by simp only [Prod.fst_mul]; exact mul_comm _ _) ?_
      simp only [Prod.snd_mul, hψ1 a, hψ1 b]
    have hk : (⟨a, hBW a.2⟩ * ⟨b, hBW b.2⟩ * (⟨b, hBW b.2⟩ * ⟨a, hBW a.2⟩)⁻¹ : W) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact mul_inv_eq_one.mpr hc
    rw [hker, mem_subgroupOf] at hk
    simp only [coe_mul, coe_inv] at hk
    have hkB : (a : Γ) * b * ((b : Γ) * a)⁻¹ ∈ B :=
      mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))
    have h1 : (a : Γ) * b * ((b : Γ) * a)⁻¹ = 1 := by
      have := mem_inf.mpr ⟨hkB, hk⟩
      rwa [hBO, mem_bot] at this
    exact hab (Subtype.ext (by simpa using mul_inv_eq_one.mp h1))
  ·
    have hdvd := card_map_dvd (B.subgroupOf W) ψ
    rw [h, card_top, Nat.card_congr (subgroupOfEquivOfLe hBW).toEquiv,
      AS76b.card_sl2_even (by omega)] at hdvd
    exact (dvd_mul_right _ _).trans hdvd

theorem plus_factor_subnormal_of_standard (hT4 : AS76b.Asc75Theorem4) {D B C T : Subgroup Γ}
    (hBqs : Nine7.QS B) (hBp : 2 ≤ Open.pRank 2 B) (hBZ : Subgroup.center ↥B = ⊥)
    (hCB : ∀ c ∈ C, ∀ b ∈ B, c * b = b * c)
    (hcenD : Subgroup.centralizer (D : Set Γ) = B ⊔ C) (hBC : B ⊓ C = ⊥)
    (hT : T ≤ C) (hT1 : T ≠ ⊥) (hTsyl : IsSylowOf 2 T C)
    (hstdD : Open.standardIsStandardSubgroup D) : B.IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTE := std_tightlyEmbedded hstdD
  set Q := centralizer (D : Set Γ)
  have hB : IsSimpleGroup B := by
    have := hBqs.2
    exact ((QuotientGroup.quotientBot (G := B)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hBZ).symm).isSimpleGroup
  have hnab : ∃ a b : B, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hc : commutator B = ⊥ := by
      rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
      exact fun x _ => mem_centralizer_iff.mpr fun y _ => h y x
    exact top_ne_bot (hBqs.1.symm.trans hc)
  have hBe : Even (Nat.card B) := Nine7.even_card_of_qs hBqs
  have hCN : C ≤ normalizer (B : Set Γ) := fun c hc =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => (hCB c hc b hb).symm)
  have hBQ : B ≤ Q := by rw [hcenD]; exact le_sup_left
  have hQB : Q ≤ normalizer (B : Set Γ) := by rw [hcenD]; exact sup_le le_normalizer hCN
  have hBO : B ⊓ AS76b.oddCoreIn Q = ⊥ := std_inf_eq_bot_of_odd
    (hBQ.trans (AS76b.le_normalizer_oddCoreIn Q)) (AS76b.odd_card_oddCoreIn Q) hBe
  have hBL : B ≤ AS76b.twoPrimeLayerIn Q := std_le_twoPrimeLayerIn hBQ hQB hnab hBO
  have hne : AS76b.twoPrimeLayerIn Q ≠ AS76b.oddCoreIn Q := fun h =>
    (nontrivial_iff_ne_bot B).mp inferInstance ((inf_eq_left.mpr (h ▸ hBL)).symm.trans hBO)
  rcases hT4 Γ Q hTE hne with h1 | ⟨h2, -⟩ | ⟨g, hg, T', hT', hT'N, n, hn, φ, hφ, hker⟩
  ·
    obtain ⟨h1a, h1b⟩ := h1
    have hL : (AS76b.twoPrimeLayerIn (⊤ : Subgroup Γ)).Normal :=
      normalizer_eq_top_iff.mp (top_le_iff.mp (AS76b.le_normalizer_twoPrimeLayerIn ⊤))
    exact .step _ _ hBL (.step _ _ h1a hL.isSubnormal h1b)
      ((normal_subgroupOf_iff_le_normalizer hBL).mpr ((AS76b.twoPrimeLayerIn_le Q).trans hQB))
  ·
    have := CFSG.SectionRank.pRank_mono (p := 2) one_lt_two hBL
    omega
  ·
    exfalso
    have h1 := AS76b.factorization_le_of_caseD hTE hg hT' hT'N rfl (by omega) φ hφ hker
    have h2 : n ≤ (Nat.card B).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
        (std_two_pow_dvd_card hBQ hQB hnab hBe hBO hT'N rfl hn φ hφ hker)
    have h3 : (Nat.card Q).factorization 2 =
        (Nat.card B).factorization 2 + (Nat.card C).factorization 2 := by
      rw [hcenD, AschbacherTheorem3.card_sup_of_le_normalizer hCN hBC,
        Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
    have h4 : 1 ≤ (Nat.card C).factorization 2 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTsyl.isPGroup
      have hk0 : k ≠ 0 := fun h0 => hT1 (eq_bot_of_card_eq T (by rw [hk, h0, pow_zero]))
      exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
        ((pow_dvd_pow 2 (Nat.one_le_iff_ne_zero.mpr hk0)).trans (hk ▸ card_dvd_of_le hT))
    omega

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
