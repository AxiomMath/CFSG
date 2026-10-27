module

public import CFSG.LieType.SeitzGeneration.SpFourThree
public import CFSG.LieType.SeitzGeneration.InnerSymplectic

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank

theorem three_ne_zero_of_card {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ f) (h : ℓ ≠ 3) : (3 : K) ≠ 0 := by
  intro h0
  have := Fintype.ofFinite K
  have hchar : CharP K 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).2 h0
  obtain ⟨n, -, hn⟩ := FiniteField.card K 3
  rw [← Nat.card_eq_fintype_card, hK] at hn
  have hf : f ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hn
    have := Nat.one_lt_pow n.ne_zero Nat.prime_three.one_lt
    omega
  have hdvd : ℓ ∣ 3 ^ (n : ℕ) := hn ▸ dvd_pow_self ℓ hf
  exact h ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (hℓ.dvd_of_dvd_pow hdvd))

theorem exists_ne_zero_one {K : Type} [Field K] [Finite K] (h : 3 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  have := Fintype.ofFinite K
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon x hx]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_two (a := (0 : K)) (b := 1)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  omega

theorem planeGen_inner_psp_four_three {d : TauCeti.ValidLieTypeIndex} {ℓ f : ℕ} {K : Type}
    [Field K] (e : Cat d ≃* StatedProj (StatedSp 2 K)) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hK : Nat.card K = ℓ ^ f) (h4 : 4 ≤ Nat.card K)
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hinner : InnerPlane d 3 E) : PlaneGen E := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card hℓ hK hℓ3
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by omega)
      (Or.inl (Or.inr h4))
  have : IsSimpleGroup (Cat d) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat d)
    (range_conj_ne_bot_of_inner Nat.prime_three hc hinner)
  refine planeGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  refine closure_centralizers_psp_four_three h3 (exists_ne_zero_one (by omega)) E₁
    (fun x hx y hy => congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hE₁.2 x hx) (by simpa using hcard₁)

theorem seitzInnerSymplecticFourThree :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .B 2 q := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, rfl, q, rfl⟩
  have hq : 3 ≠ q.p := by simpa using hpd
  have h4 : 4 ≤ q.p ^ q.exponent := by
    have := (TauCeti.TypeB2LieIndex.of q hv).four_le_fieldOrder
    simpa [TauCeti.ValidLieTypeIndex.fieldOrder] using this
  have hcard := CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv
  exact planeGen_inner_psp_four_three
    (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv) q.prime_p (Ne.symm hq) hcard
    (by rw [hcard]; exact h4) hE hc hinner

theorem seitzInnerSymplecticTwo :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ ∃ q : TauCeti.PrimePower, d.1 = .B 2 q :=
  SeitzPlanes.of_cover (S₁ := fun d p E => InnerPlane d p E ∧ p = 3 ∧
      ∃ q : TauCeti.PrimePower, d.1 = .B 2 q)
    (S₂ := fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ IsSymplecticIndex d.1)
    (fun d p hp hp2 E ⟨hi, q, hq⟩ => by
      have h2 := hp.two_le
      rcases (by omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h
      · exact Or.inl ⟨hi, h, q, hq⟩
      · subst h
        exact absurd hp (by norm_num)
      · exact Or.inr ⟨hi, h, Or.inl ⟨q, hq⟩⟩)
    seitzInnerSymplecticFourThree seitzInnerSymplectic

end CFSG.LieType.SeitzGeneration
