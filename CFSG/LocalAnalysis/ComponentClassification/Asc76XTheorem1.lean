module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma311

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_rightConjugate {E : Subgroup G} {p : ℕ} (h : IsElemAbelian p E) (g : G) :
    IsElemAbelian p (rightConjugate E g) :=
  isElemAbelian_of_mulEquiv (E.equivMapOfInjective _ (MulAut.conj g⁻¹).injective) h

omit [Finite G] in
theorem oUpperTwoPrime_rightConjugate (K : Subgroup G) (g : G) :
    oUpperTwoPrime (rightConjugate K g) = rightConjugate (oUpperTwoPrime K) g := by
  rw [oUpperTwoPrime, oUpperTwoPrime]
  change _ = (Subgroup.closure _).map (MulAut.conj g⁻¹).toMonoidHom
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hy, k, hk⟩
    refine ⟨g * y * g⁻¹, ⟨?_, k, ?_⟩, by group⟩
    · have h1 := (mem_rightConjugate_iff K g y).mp hy
      exact h1
    · rw [show g * y * g⁻¹ = (MulAut.conj g) y from rfl, ← map_pow, hk, map_one]
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    refine ⟨?_, k, ?_⟩
    · rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hx
    · rw [show g⁻¹ * x * g⁻¹⁻¹ = (MulAut.conj g⁻¹) x from rfl, ← map_pow, hk, map_one]

omit [Finite G] in
theorem rightConjugate_inf_normalizer (J K : Subgroup G) (g : G) :
    rightConjugate (J ⊓ normalizer (K : Set G)) g =
      rightConjugate J g ⊓ normalizer ((rightConjugate K g : Subgroup G) : Set G) := by
  ext x
  rw [mem_inf, mem_rightConjugate_iff, mem_inf, mem_rightConjugate_iff]
  refine and_congr_right fun _ => ?_
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
    have := h (g * y * g⁻¹)
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ by group]
      at this
    exact this
  · intro h y
    have := h (g⁻¹ * y * g)
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff,
      show g * (g⁻¹ * y * g) * g⁻¹ = y by group,
      show g * (x * (g⁻¹ * y * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ by group]
      at this
    exact this

omit [Finite G] in
theorem mem_normalizer_rightConjugate_iff {K : Subgroup G} {g x : G} :
    x ∈ normalizer ((rightConjugate K g : Subgroup G) : Set G) ↔
      g * x * g⁻¹ ∈ normalizer (K : Set G) := by
  have h := SetLike.ext_iff.mp (rightConjugate_inf_normalizer ⊤ K g) x
  simp only [mem_inf, mem_rightConjugate_iff, mem_top, true_and] at h
  exact h.symm

theorem sylowNormalizes_rightConjugate {J K : Subgroup G} (h : SylowNormalizes J K) (g : G) :
    SylowNormalizes (rightConjugate J g) (rightConjugate K g) := by
  obtain ⟨S, hS, hSK⟩ := h
  refine ⟨rightConjugate S g, isSylowOf_rightConjugate hS g, fun x hx => ?_⟩
  rw [mem_rightConjugate_iff] at hx
  exact mem_normalizer_rightConjugate_iff.mpr (hSK hx)

theorem sec3Setting_of_tightlyEmbedded {K : Subgroup G} (hK : TightlyEmbedded K)
    (hG : normalClosure (K : Set G) = ⊤) (hK2 : oUpperTwoPrime K = K)
    (hO : standardComponentOddCore G = ⊥)
    (hstar : ∀ g : G, Even (Nat.card (rightConjugate K g ⊓ normalizer (K : Set G) :
      Subgroup G)) → SylowNormalizes (rightConjugate K g) K)
    {R : Subgroup G} (hR : IsSylowOf 2 R K) (hm : 1 < Open.pRank 2 R)
    (hΦ : ¬ IsElemAbelian 2 R) : Sec3Setting (Set.range (rightConjugate K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ J ∈ Set.range (rightConjugate K), ∀ g : G,
      rightConjugate J g ∈ Set.range (rightConjugate K) := by
    rintro _ ⟨a, rfl⟩ g
    exact ⟨a * g, (rightConjugate_mul K a g).symm⟩
  have hsplit : ∀ a b : G, rightConjugate K b = rightConjugate (rightConjugate K (b * a⁻¹)) a :=
    fun a b => by rw [rightConjugate_mul, inv_mul_cancel_right]
  refine ⟨hO, hinv, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hn : (sSup (Set.range (rightConjugate K))).Normal := normal_sSup_of_invariant hinv
    rw [eq_top_iff, ← hG]
    refine normalClosure_le_normal fun k hk => ?_
    exact (le_sSup (show K ∈ Set.range (rightConjugate K) from ⟨1, rightConjugate_one K⟩)) hk
  ·
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne heven
    have heven' : Even (Nat.card (rightConjugate K (b * a⁻¹) ⊓ normalizer (K : Set G) :
        Subgroup G)) := by
      rw [hsplit a b, ← rightConjugate_inf_normalizer, rightConjugate_card] at heven
      exact heven
    rw [hsplit a b]
    exact sylowNormalizes_rightConjugate (hstar _ heven') a
  ·
    rintro _ ⟨a, rfl⟩ R' hR'
    obtain ⟨m, -, hm'⟩ := exists_conj_of_isSylowOf (isSylowOf_rightConjugate hR a) hR'
    rw [rightConjugate_mul] at hm'
    obtain ⟨E, hER, hE, hE4⟩ := exists_fourGroup_le hm
    refine ⟨one_lt_pRank_of_fourGroup (E := rightConjugate E (a * m)) ?_
      (isElemAbelian_rightConjugate hE _) (by rw [rightConjugate_card, hE4]), fun h => hΦ ?_⟩
    · rw [hm']
      intro x hx
      rw [mem_rightConjugate_iff] at hx ⊢
      exact hER hx
    · have h1 := isElemAbelian_rightConjugate h (a * m)⁻¹
      rwa [hm', rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
  ·
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    refine ⟨by rw [rightConjugate_card, rightConjugate_card], ?_⟩
    have hc : b * a⁻¹ ∉ normalizer (K : Set G) := by
      intro h
      apply hne
      rw [hsplit a b, (rightConjugate_eq_self_iff K _).mpr h]
    have h1 := hK.2 _ hc
    rw [hsplit a b]
    have e : rightConjugate K a ⊓ rightConjugate (rightConjugate K (b * a⁻¹)) a =
        rightConjugate (K ⊓ rightConjugate K (b * a⁻¹)) a := by
      ext x
      simp only [mem_inf, mem_rightConjugate_iff]
    rw [e, rightConjugate_card]
    exact h1
  ·
    rintro _ ⟨a, rfl⟩
    rw [oUpperTwoPrime_rightConjugate, hK2]

theorem asc76Theorem1_of_theorem4 (hB : BenderFacts) (h4 : Asc76Theorem4) : Asc76Theorem1 := by
  intro G _ _ K hK hG hK2 hO hstar R hR hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hΦ : IsElemAbelian 2 R
  · exact Or.inr (Or.inl hΦ)
  by_cases hKtop : K = ⊤
  · exact Or.inl hKtop
  right
  right
  have hΩ := sec3Setting_of_tightlyEmbedded hK hG hK2 hO hstar hR hm hΦ
  obtain ⟨-, hC⟩ := h4 G _ hΩ K ⟨1, rightConjugate_one K⟩
  have hKn : ¬ K.Normal := fun h => hKtop (by rw [← normalClosure_eq_self K]; exact hG)
  rcases hC with hn | ⟨hsz, hsyl⟩
  · exact absurd hn hKn
  rw [hG] at hsz hsyl
  have hRG := hsyl R hR
  have hR' := isSylowOf_iff_card.mp hR
  have hR2 : IsPGroup 2 R := IsPGroup.of_card hR'.2
  have hszG : IsSzOrU3 G := isSzOrU3_of_mulEquiv Subgroup.topEquiv.symm hsz
  have hKN : K ≤ normalizer (R : Set G) := by
    by_contra hcon
    have hall := hB.two_element_mem_of_not_le_normalizer hsz le_top hRG hR'.1 hcon
    apply hKn
    refine ⟨fun n hn g => ?_⟩
    have hKg : rightConjugate K g⁻¹ ≤ K := by
      have h1 : oUpperTwoPrime (rightConjugate K g⁻¹) = rightConjugate K g⁻¹ := by
        rw [oUpperTwoPrime_rightConjugate, hK2]
      rw [← h1]
      refine (closure_le _).mpr fun y hy => ?_
      obtain ⟨-, i, hyi⟩ := hy
      exact hall y (mem_top y) i hyi
    have h2 : g * n * g⁻¹ ∈ rightConjugate K g⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv]
      simpa [mul_assoc] using hn
    exact hKg h2
  have hKR : K = R := eq_of_le_normalizer_of_isSylowOf le_top hRG hR'.1 hKN hK2
  subst hKR
  obtain ⟨E, hEK, hE, hE4⟩ := exists_fourGroup_le hm
  have hK1 : K ≠ ⊥ := fun h => by
    have := card_le_of_le hEK
    rw [h, card_bot, hE4] at this
    norm_num at this
  refine ⟨hszG, fun h => hKn (normalizer_eq_top_iff.mp h), ?_, fun g hg => ?_⟩
  · obtain ⟨x, hx, hx2⟩ := exists_involution hR2 hK1
    rw [even_iff_two_dvd, ← hx2]
    exact orderOf_dvd_natCard _ (le_normalizer hx)
  · by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
    have hxo : orderOf (x : G) = 2 := by rw [orderOf_coe]; exact hx
    have hx2 : (x : G) ^ (2 ^ 1) = 1 := by rw [pow_one, ← hxo]; exact pow_orderOf_eq_one _
    obtain ⟨hxN, hxNg⟩ := mem_inf.mp x.2
    have hxK : (x : G) ∈ K := mem_of_mem_normalizer_of_isSylowOf hRG (mem_top _) hxN hx2
    have htop : rightConjugate (⊤ : Subgroup G) g = ⊤ := by
      apply (rightConjugate_eq_self_iff ⊤ g).mpr
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top g
    have hRGg : IsSylowOf 2 (rightConjugate K g) ⊤ := htop ▸ isSylowOf_rightConjugate hRG g
    have hxNg' : (x : G) ∈ normalizer ((rightConjugate K g : Subgroup G) : Set G) :=
      mem_normalizer_rightConjugate_iff.mpr ((mem_rightConjugate_iff _ g _).mp hxNg)
    have hxKg : (x : G) ∈ rightConjugate K g :=
      mem_of_mem_normalizer_of_isSylowOf hRGg (mem_top _) hxNg' hx2
    have hne : K ≠ rightConjugate K g := fun h =>
      hg ((rightConjugate_eq_self_iff K g).mp h.symm)
    have hinf := hB.inf_eq_bot_of_isSylowOf hsz hRG hRGg hne
    have h1 : (x : G) ∈ K ⊓ rightConjugate K g := mem_inf.mpr ⟨hxK, hxKg⟩
    rw [hinf, mem_bot] at h1
    rw [h1, orderOf_one] at hxo
    exact absurd hxo (by decide)

end CFSG.ComponentClassification.Asc76X
