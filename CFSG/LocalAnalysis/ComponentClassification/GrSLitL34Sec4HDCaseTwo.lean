module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDConnB
public import CFSG.GroupTheory.ThompsonIndexTwo
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {X : Type} [Group X] [Finite X]

theorem card_inf_eq_of_isSylowTwoIn
    {M K T : Subgroup X} {a : X}
    (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He) (haa : a * a = 1) (haT : a ∈ T)
    (hKM : K ≤ M) (hKc : IsPComponent 2 (K.subgroupOf M))
    (honly : ∀ K₂ : Subgroup X, K₂ ≤ M → IsPComponent 2 (K₂.subgroupOf M) →
      K₂ = K ∨ K₂ = conjugate K a) (hTsyl : IsSylowTwoIn T M) :
    Nat.card ↥(T ⊓ K) = 1024 ∧ Nat.card ↥(T ⊓ conjugate K a) = 1024 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hT2 := hTsyl.isPGroup
  have hmap : (T ⊓ conjugate K a).map (MulAut.conj a).toMonoidHom = T ⊓ K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_inf.mpr ⟨mul_mem (mul_mem haT (mem_inf.mp hx).1) (inv_mem haT),
        mem_conjugate_iff.mp (mem_inf.mp hx).2⟩
    · intro hy
      refine ⟨a⁻¹ * y * a, mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem haT) (mem_inf.mp hy).1) haT,
        ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
      rw [mem_conjugate_iff, show a * (a⁻¹ * y * a) * a⁻¹ = y by group]
      exact (mem_inf.mp hy).2
  have hcard : Nat.card ↥(T ⊓ conjugate K a) = Nat.card ↥(T ⊓ K) := by
    rw [← hmap, card_map_of_injective (MulAut.conj a).injective]
  have hle : Nat.card ↥(T ⊓ K) ≤ 1024 := by
    rw [← card_imL (e := e₁) inf_le_right (hT2.to_le inf_le_left)]
    exact card_le_of_le_heP (imL_le_heP _) (isPGroup_imL e₁ inf_le_right (hT2.to_le inf_le_left))
  have hK : Nat.card K = Nat.card heP * Nat.card (pPrimeCore 2 ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K),
      Nat.card_congr (e₁.trans heEquivP).toEquiv]
  have hdvd : 2 ^ 10 ∣ Nat.card K := by
    rw [hK, card_heP]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set Q' : Subgroup X := Q.map K.subtype with hQ'
  have hQ'K : Q' ≤ K := map_subtype_le _
  have hQ'c : Nat.card Q' = 1024 := by
    rw [hQ', card_map_of_injective K.subtype_injective, hQ]
    norm_num
  have hQ'2 : IsPGroup 2 Q' := IsPGroup.of_card (n := 10) (by rw [hQ'c]; norm_num)
  obtain ⟨c, hcM, hcT⟩ := hTsyl.exists_conj_le (hQ'K.trans hKM) hQ'2
  have hge : ∀ {H : Subgroup X}, (H = K ∨ H = conjugate K a) →
      (∀ q ∈ Q', c * q * c⁻¹ ∈ H) → 1024 ≤ Nat.card ↥(T ⊓ H) := by
    intro H _ hH
    have h1 : Q'.map (MulAut.conj c).toMonoidHom ≤ T ⊓ H := by
      rintro _ ⟨q, hq, rfl⟩
      exact mem_inf.mpr ⟨hcT q hq, hH q hq⟩
    calc 1024 = Nat.card ↥(Q'.map (MulAut.conj c).toMonoidHom) := by
          rw [card_map_of_injective (MulAut.conj c).injective, hQ'c]
      _ ≤ Nat.card ↥(T ⊓ H) := card_le_of_le h1
  have hcK : ∀ q ∈ Q', c * q * c⁻¹ ∈ conjugate K c⁻¹ := fun q hq => by
    rw [mem_conjugate_iff, show c⁻¹ * (c * q * c⁻¹) * c⁻¹⁻¹ = q by group]
    exact hQ'K hq
  have hge' : 1024 ≤ Nat.card ↥(T ⊓ K) := by
    rcases honly _ (conjugate_le_of_mem hKM (inv_mem hcM))
        (isPComponent_conjugate_subgroupOf (inv_mem hcM) hKc) with h1 | h1
    · exact hge (Or.inl rfl) (h1 ▸ hcK)
    · rw [← hcard]
      exact hge (Or.inr rfl) (h1 ▸ hcK)
  exact ⟨le_antisymm hle hge', hcard.trans (le_antisymm hle hge')⟩

theorem false_of_swap
    [IsSimpleGroup X] (hnab : ∃ x y : X, x * y ≠ y * x)
    (hGWB : GWTwoBalanced X) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) {M K T A : Subgroup X} {a : X} (h : SwapData M K T a)
    (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
    (e₂ : (conjugate K a) ⧸ pPrimeCore 2 ↥(conjugate K a) ≃* Blueprint.NativeSporadic.He)
    (hAe : IsElemTwo A) (hA16 : 16 ≤ Nat.card A) (hMW : M = normalizer (wGroup A : Set X))
    (hTsyl : IsSylowTwoIn T M) (haext : IsExtremalIn T a) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := h.isThreeConnected e₁ e₂ h64 hOut
  obtain ⟨⟨P, hP⟩, hfus⟩ := sylow_and_fusion_of_threeConnected hGWB hAe hA16 (hMW ▸ hTsyl) h3
  set U := T ⊓ normalizer (K : Set X) with hU
  have hUidx : U.relIndex T = 2 := relIndex_inf_normalizer h.orderOf_eq h.le_M h.isPComponent
    h.conjugate_ne h.only h.T_le h.mem_T
  have haU : a ∉ U := fun ha => h.conjugate_ne
    (conjugate_eq_of_mem_normalizer (mem_inf.mp ha).2)
  by_cases hc : ∀ g : X, g⁻¹ * a * g ∉ U
  ·
    have hTidx : ¬ 2 ∣ T.index := by
      rw [← hP]
      exact P.not_dvd_index
    obtain ⟨N, hN, hNidx⟩ := ThompsonIndexTwo.exists_normal_index_two_of_thompson h.isPGroup
      hTidx inf_le_left hUidx h.mem_T haU (fun y hyT hyU => by
        rw [h.orderOf_eq]
        have hy1 : y ≠ 1 := fun h' => hyU (h' ▸ one_mem _)
        have hpos : 0 < orderOf y := orderOf_pos y
        have hne : orderOf y ≠ 1 := fun h' => hy1 (orderOf_eq_one_iff.mp h')
        omega) hc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
    · rw [hb, index_bot] at hNidx
      obtain ⟨x, y, hxy⟩ := hnab
      have hX : Nat.card X = 2 := hNidx
      have hcomm : ∀ u v : X, u * v = v * u := by
        have : Fact (Nat.Prime (Nat.card X)) := ⟨by rw [hX]; exact Nat.prime_two⟩
        have := isCyclic_of_prime_card (α := X) rfl
        exact fun u v => mul_comm u v
      exact hxy (hcomm x y)
    · rw [ht, index_top] at hNidx
      exact absurd hNidx (by norm_num)
  push Not at hc
  obtain ⟨g, hg⟩ := hc
  set b := g⁻¹ * a * g with hb
  have hbT : b ∈ T := (mem_inf.mp hg).1
  have hbb : b * b = 1 := by
    rw [hb, show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, h.mul_self]
    group
  obtain ⟨F, hFS, hFC, hFe, hF8⟩ := exists_eight_fixed e₁ h64 hOut (S := U) inf_le_right
    (h.isPGroup.to_le inf_le_left) (SwapData.card_left' h) hg hbb
  have hrank : 3 ≤ pRank 2 ↥(T ⊓ centralizer ({b} : Set X)) :=
    three_le_pRank_of_le hFe (by omega) (le_inf ((hFS.trans inf_le_left).trans inf_le_left) hFC)
  obtain ⟨m, hmM, hbm⟩ := hfus a b hbT haext ⟨g⁻¹, by rw [hb]; group⟩ hrank
  rw [← hMW] at hmM
  exact conj_not_mem_normalizer h.orderOf_eq h.le_M h.isPComponent h.conjugate_ne h.only hmM
    (hbm ▸ (mem_inf.mp hg).2)

end CFSG.ComponentClassification.GrSLit.HeDiag
