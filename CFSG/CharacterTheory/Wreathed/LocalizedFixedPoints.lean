module

public import CFSG.CharacterTheory.Semidihedral.StationaryOddLocalization

public section

namespace CFSG.Wreathed.LocalizedFixedPoints

open scoped Pointwise
open CFSG.SignalizerFunctor.Helpers CFSG.Wreathed.OriginalSylowNormalizerWitness
  CFSG.Semidihedral.StationaryOddLocalization

universe u

variable {G : Type u} [Group G]

theorem kleinFour_le_centralizer (T : Subgroup G) [IsKleinFour T] {x : G} (hxT : x ∈ T) :
    T ≤ Subgroup.centralizer ({x} : Set G) := by
  intro t ht
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := (IsKleinFour.isMulCommutative (G := T)).is_comm.comm ⟨t, ht⟩ ⟨x, hxT⟩
  exact congrArg Subtype.val h

theorem mem_normalizer_zpowers_of_inv {x v : G} (hv : x * v * x⁻¹ = v⁻¹) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (x * v * x⁻¹) = _
  rw [hv, Subgroup.zpowers_inv]

theorem scalar_of_not_centralized [Finite G] (T : Subgroup G) [IsKleinFour T] (x y : G)
    (hxT : x ∈ T) (hyT : y ∈ T) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x ≠ y)
    (R : Subgroup G)
    (hloc : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card R → ∀ F : Subgroup G, F ≠ ⊥ → F ≤ R →
      IsPGroup ell F → T ≤ Subgroup.normalizer (F : Set G) → ∀ B : Subgroup G,
        B ≤ Subgroup.normalizer (F : Set G) → IsPGroup ell B →
          x ∈ Subgroup.normalizer (B : Set G) → B ≤ Subgroup.centralizer ({x} : Set G))
    (O : Subgroup G) (hCO : O ⊓ Subgroup.centralizer ({x} : Set G) ≤ R)
    {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell) (W : Subgroup G) (hWO : W ≤ O)
    (hWp : IsPGroup ell W) (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hWnot : ¬ W ≤ Subgroup.centralizer ({x} : Set G)) :
    W ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ ∧ (∀ w ∈ W, x * w * x⁻¹ = w⁻¹) ∧
      IsMulCommutative W := by
  let : Fact ell.Prime := ⟨hell⟩
  have hx : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx2
    omega
  have hy : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy2
    omega
  have hWodd := odd_card_of_pgroup hell hellodd W hWp
  have hxW : x ∈ Subgroup.normalizer (W : Set G) := hTW hxT
  have hTC : T ≤ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :=
    (kleinFour_le_centralizer T hxT).trans (Subgroup.le_normalizer)
  have hFbot : W ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
    by_contra hF
    set F := W ⊓ Subgroup.centralizer ({x} : Set G) with hFdef
    have hFR : F ≤ R := (inf_le_inf_right _ hWO).trans hCO
    have hFp : IsPGroup ell F := hWp.to_le inf_le_left
    have hTF : T ≤ Subgroup.normalizer (F : Set G) :=
      (le_inf hTW hTC).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hellR : ell ∣ Nat.card R := by
      have h1 : ell ∣ Nat.card F := by
        rcases hFp.card_eq_or_dvd with h | h
        · exact absurd (Subgroup.card_eq_one.mp h) hF
        · exact h
      exact h1.trans (Subgroup.card_dvd_of_le hFR)
    let _action := conjugationAction T W hTW
    let a : T := ⟨x, hxT⟩
    let b : T := ⟨y, hyT⟩
    have ha : a ≠ 1 := fun h => hx (congrArg (fun z : T => (z : G)) h)
    have hb : b ≠ 1 := fun h => hy (congrArg (fun z : T => (z : G)) h)
    have hab : a ≠ b := fun h => hxy (congrArg (fun z : T => (z : G)) h)
    have hcent := original_actionCentralizer_eq T W hTW a
    have hFtop : actionCentralizer (X := W) a ≠ ⊤ := by
      intro htop
      apply hWnot
      intro w hw
      have hm : (⟨w, hw⟩ : W) ∈ actionCentralizer (X := W) a := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [hcent] at hm
      exact hm.2
    obtain ⟨-, -, v, hvord, hva, -, hvcomm⟩ :=
      four_group_odd_p_group_prime_order_witness hell hellodd hWp a b ha hb hab hFtop
    have hvinv : x * (v : G) * x⁻¹ = (v : G)⁻¹ := congrArg (fun z : W => (z : G)) hva
    have hord : orderOf (v : G) = ell :=
      (orderOf_injective W.subtype W.subtype_injective v).trans hvord
    have hvF : (v : G) ∈ Subgroup.centralizer (F : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro f hf
      have hfW : (⟨f, hf.1⟩ : W) ∈ actionCentralizer (X := W) a := by
        rw [hcent]
        exact hf
      exact (congrArg (fun z : W => (z : G)) (hvcomm ⟨f, hf.1⟩ hfW).eq).symm
    have hBN : Subgroup.zpowers (v : G) ≤ Subgroup.normalizer (F : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (F : Set G) hvF)
    have hBp : IsPGroup ell (Subgroup.zpowers (v : G)) :=
      hWp.to_le (Subgroup.zpowers_le.mpr v.property)
    have hBC := hloc ell hell hellR F hF hFR hFp hTF _ hBN hBp
      (mem_normalizer_zpowers_of_inv hvinv)
    exact prime_order_inverted_not_in_centralizer x (v : G) hell hellodd hord hvinv
      (hBC (Subgroup.mem_zpowers _))
  have hinv := inverted_of_trivial_fixed_subgroup x hx2 W hWodd hxW hFbot
  exact ⟨hFbot, hinv, abelian_of_inverted x W hinv⟩

theorem localized_fixed_points_force_scalar_action_and_an_inverted_sylow [Finite G]
    (T : Subgroup G) [IsKleinFour T] (x y : G) (hxT : x ∈ T) (hyT : y ∈ T)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x ≠ y)
    (R : Subgroup G) (_hRN : R ≤ Subgroup.centralizer ({x} : Set G))
    (_hRodd : Odd (Nat.card R)) (_hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hloc : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card R → ∀ F : Subgroup G, F ≠ ⊥ → F ≤ R →
      IsPGroup ell F → T ≤ Subgroup.normalizer (F : Set G) → ∀ B : Subgroup G,
        B ≤ Subgroup.normalizer (F : Set G) → IsPGroup ell B →
          x ∈ Subgroup.normalizer (B : Set G) → B ≤ Subgroup.centralizer ({x} : Set G))
    (O : Subgroup G) (hOodd : Odd (Nat.card O)) (hTO : T ≤ Subgroup.normalizer (O : Set G))
    (hCO : O ⊓ Subgroup.centralizer ({x} : Set G) ≤ R) :
    (∀ ell : ℕ, ell.Prime → Odd ell → ∀ W : Subgroup G, W ≤ O → IsPGroup ell W →
      T ≤ Subgroup.normalizer (W : Set G) →
        (W ≤ Subgroup.centralizer ({x} : Set G) ∨ ∀ w ∈ W, x * w * x⁻¹ = w⁻¹) ∧
        (¬ W ≤ Subgroup.centralizer ({x} : Set G) →
          W ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ ∧ IsMulCommutative W)) ∧
    (¬ O ≤ Subgroup.centralizer ({x} : Set G) →
      (∃ ell : ℕ, ell.Prime ∧ ell ∣ Nat.card O ∧ ∃ Q : Sylow ell O,
        T ≤ Subgroup.normalizer (((Q : Subgroup O).map O.subtype : Subgroup G) : Set G) ∧
          ¬ (Q : Subgroup O).map O.subtype ≤ Subgroup.centralizer ({x} : Set G)) ∧
      ∀ ell : ℕ, ell.Prime → ∀ Q : Sylow ell O,
        T ≤ Subgroup.normalizer (((Q : Subgroup O).map O.subtype : Subgroup G) : Set G) →
        ¬ (Q : Subgroup O).map O.subtype ≤ Subgroup.centralizer ({x} : Set G) →
          (Q : Subgroup O).map O.subtype ≠ ⊥ ∧
            IsMulCommutative ((Q : Subgroup O).map O.subtype) ∧
            ∀ w ∈ (Q : Subgroup O).map O.subtype, x * w * x⁻¹ = w⁻¹) := by
  refine ⟨fun ell hell hellodd W hWO hWp hTW => ?_, fun hOnot => ?_⟩
  · by_cases hWC : W ≤ Subgroup.centralizer ({x} : Set G)
    · exact ⟨Or.inl hWC, fun h => absurd hWC h⟩
    · obtain ⟨hF, hinv, hab⟩ := scalar_of_not_centralized T x y hxT hyT hx2 hy2 hxy R hloc O
        hCO hell hellodd W hWO hWp hTW hWC
      exact ⟨Or.inr hinv, fun _ => ⟨hF, hab⟩⟩
  have hevery : ∀ ell : ℕ, ell.Prime → ∀ Q : Sylow ell O,
      T ≤ Subgroup.normalizer (((Q : Subgroup O).map O.subtype : Subgroup G) : Set G) →
      ¬ (Q : Subgroup O).map O.subtype ≤ Subgroup.centralizer ({x} : Set G) →
        (Q : Subgroup O).map O.subtype ≠ ⊥ ∧
          IsMulCommutative ((Q : Subgroup O).map O.subtype) ∧
          ∀ w ∈ (Q : Subgroup O).map O.subtype, x * w * x⁻¹ = w⁻¹ := by
    intro ell hell Q hTQ hQC
    let : Fact ell.Prime := ⟨hell⟩
    have hQne : (Q : Subgroup O).map O.subtype ≠ ⊥ := fun h => hQC (h ▸ bot_le)
    have hQp : IsPGroup ell ((Q : Subgroup O).map O.subtype) := Q.isPGroup'.map O.subtype
    have hellodd : Odd ell := by
      have h1 : ell ∣ Nat.card ((Q : Subgroup O).map O.subtype) := by
        rcases hQp.card_eq_or_dvd with h | h
        · exact absurd (Subgroup.card_eq_one.mp h) hQne
        · exact h
      exact hOodd.of_dvd_nat (h1.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)))
    obtain ⟨-, hinv, hab⟩ := scalar_of_not_centralized T x y hxT hyT hx2 hy2 hxy R hloc O hCO
      hell hellodd _ (Subgroup.map_subtype_le _) hQp hTQ hQC
    exact ⟨hQne, hab, hinv⟩
  refine ⟨?_, hevery⟩
  by_contra hno
  apply hOnot
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hcop : Nat.Coprime 2 (Nat.card O) := hOodd.coprime_two_left
  have hall : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card O → ∃ Q : Sylow ell O,
      (Q : Subgroup O).map O.subtype ≤ O ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro ell hell hellO
    obtain ⟨Q, hQ⟩ := normalized_subgroup_invariant_sylow 2 ell Nat.prime_two hell T O hT2 hTO
      hcop
    refine ⟨Q, le_inf (Subgroup.map_subtype_le _) ?_⟩
    by_contra hQC
    exact hno ⟨ell, hell, hellO, Q, hQ, hQC⟩
  have hdvd : Nat.card O ∣ Nat.card (O ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p k hp hpk
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, pow_zero]
      exact one_dvd _
    · have hpO : p ∣ Nat.card O := (dvd_pow_self p hk.ne').trans hpk
      obtain ⟨Q, hQ⟩ := hall p hp hpO
      let : Fact p.Prime := ⟨hp⟩
      have h1 : p ^ k ∣ Nat.card (Q : Subgroup O) := Q.pow_dvd_card_of_pow_dvd_card hpk
      rw [← Subgroup.card_map_of_injective O.subtype_injective] at h1
      exact h1.trans (Subgroup.card_dvd_of_le hQ)
  have heq : O ⊓ Subgroup.centralizer ({x} : Set G) = O :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (Nat.le_of_dvd Nat.card_pos hdvd)
  rw [← heq]
  exact inf_le_right

end CFSG.Wreathed.LocalizedFixedPoints
