module

public import CFSG.CharacterTheory.Semidihedral.Principal.RegularityInvertedOddFactorSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOrdersSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem centralizer_involution_isConj_reflection {n : ℕ} (hn : 4 ≤ n) {S : Sylow 2 G}
    (e' : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}
    (hcent : (e' (r n) : G) ^ (modulus n / 2) = t) (x : C t) (hx2 : orderOf x = 2)
    (hxt : x ≠ tInC t) : IsConj x (centeredReflection hn e' hcent) := by
  have hSC := centered_sylow_le_centralizer hn e' hcent
  let φ : SemidihedralGroup n →* C t := (Subgroup.inclusion hSC).comp e'.toMonoidHom
  have hφ : ∀ a, ((φ a : C t) : G) = ((e' a : S) : G) := fun a => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply e'.injective
    apply Subtype.ext
    have := congrArg (fun y : C t => (y : G)) hab
    simpa [hφ] using this
  have hpx : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2]; norm_num)
  obtain ⟨y, hxy⟩ :=
    InvolutionFusion.exists_ambient_conjugate_mem_sylow (S.subtype hSC) x hpx
  have hyS : ((y : C t) : G) ∈ (S : Subgroup G) := by
    have hy : (y : C t) ∈ ((S.subtype hSC : Sylow 2 (C t)) : Subgroup (C t)) := y.2
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hy
    exact hy
  set a : SemidihedralGroup n := e'.symm ⟨((y : C t) : G), hyS⟩ with ha
  have hφa : φ a = (y : C t) := by
    apply Subtype.ext
    rw [hφ, ha, MulEquiv.apply_symm_apply]
  have ha2 : orderOf a = 2 := by
    rw [← orderOf_injective φ hφinj a, hφa, ← isConj_orderOf_eq hxy, hx2]
  rcases (involution_iff n (by omega) a).mp ha2 with hz | ⟨j, hj⟩
  · exfalso
    apply hxt
    have hyt : (y : C t) = tInC t := by
      rw [← hφa, hz]
      apply Subtype.ext
      rw [hφ, centered_z_eq hn e', hcent]
      rfl
    rw [hyt] at hxy
    obtain ⟨c, hc⟩ := hxy
    have hct : ((c : C t) : G) * t = t * ((c : C t) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (c : C t).2
    have hc' : ((c : C t) : G) * (x : G) = t * ((c : C t) : G) := by
      have := congrArg (fun w : C t => (w : G)) hc
      simpa [SemiconjBy, tInC] using this
    apply Subtype.ext
    have : ((c : C t) : G) * (x : G) = ((c : C t) : G) * t := by rw [hc', hct]
    simpa [tInC] using mul_left_cancel this
  · have hsj := (even_outside_conjugate n hn (j.val : ℤ))
    have hsj' : IsConj (s n) (r n ^ (2 * j.val) * s n) := by
      rw [show ((2 : ℤ) * (j.val : ℤ)) = ((2 * j.val : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast] at hsj
      exact hsj
    have h1 := φ.map_isConj hsj'
    rw [← hj, hφa] at h1
    exact hxy.trans h1.symm

theorem confined_normal_inverted_odd_subgroup_primes_do_not_divide_centralizer_index
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (U : Subgroup G) (hUC : U ≤ C t)
    (hUodd : Odd (Nat.card U)) (hUnormal : (U.subgroupOf (C t)).Normal)
    (hUinv : ∀ x ∈ U, (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = x⁻¹)
    (hconf : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ C t) :
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card U → ∀ P : Sylow ℓ U,
      (∀ Q : Subgroup G, Q ≤ C t → IsPGroup ℓ Q → (P : Subgroup U).map U.subtype ≤ Q →
        Subgroup.normalizer (Q : Set G) ≤ C t) ∧
      ∀ Q : Sylow ℓ (C t),
        ∃ T : Sylow ℓ G, (T : Subgroup G) = (Q : Subgroup (C t)).map (C t).subtype) ∧
      Nat.Coprime (Nat.card U) (C t).index := by
  obtain ⟨-, ht2, hcent, hsC, -, -⟩ := supplied_t_s_facts hn fS ht
  have hinv : ∀ w ∈ Subgroup.centralizer ({t} : Set G), orderOf w = 2 → w ≠ t →
      ∀ x ∈ U, w * x * w⁻¹ = x⁻¹ := by
    intro w hwC hw2 hwt x hxU
    have hw2' : orderOf (⟨w, hwC⟩ : C t) = 2 := by rw [← Subgroup.orderOf_coe]; exact hw2
    have hwt' : (⟨w, hwC⟩ : C t) ≠ tInC t := fun h => hwt (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := isConj_iff.mp
      (centralizer_involution_isConj_reflection hn fS hcent ⟨w, hwC⟩ hw2' hwt')
    have hc' : (c : G) * w * (c : G)⁻¹ = (fS (s n) : G) := by
      have := congrArg Subtype.val hc
      simpa [coe_centeredReflection] using this
    have hyU : (c : G) * x * (c : G)⁻¹ ∈ U := by
      have hx' : (⟨x, hUC hxU⟩ : C t) ∈ U.subgroupOf (C t) := hxU
      exact hUnormal.conj_mem _ hx' c
    have hys := hUinv _ hyU
    have hw : w = (c : G)⁻¹ * (fS (s n) : G) * c := by rw [← hc']; group
    calc w * x * w⁻¹
        = (c : G)⁻¹ * ((fS (s n) : G) * ((c : G) * x * (c : G)⁻¹) * (fS (s n) : G)⁻¹) * c := by
          rw [hw]; group
      _ = x⁻¹ := by rw [hys]; group
  have hlocal : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card U → ∀ P : Sylow ℓ U,
      (∀ Q : Subgroup G, Q ≤ C t → IsPGroup ℓ Q → (P : Subgroup U).map U.subtype ≤ Q →
        Subgroup.normalizer (Q : Set G) ≤ C t) ∧
      ∀ Q : Sylow ℓ (C t),
        ∃ T : Sylow ℓ G, (T : Subgroup G) = (Q : Subgroup (C t)).map (C t).subtype := by
    intro ℓ hℓ hℓU P
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hPbot : (P : Subgroup U).map U.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective]
      exact P.ne_bot_of_dvd_card hℓU
    have hN : ∀ Q : Subgroup G, Q ≤ C t → (P : Subgroup U).map U.subtype ≤ Q →
        Subgroup.normalizer (Q : Set G) ≤ C t := fun Q hQC hPQ =>
      normalizer_le_centralizer_of_confined ht2 hUodd hinv hconf (Subgroup.map_subtype_le _)
        hPbot hPQ hQC
    refine ⟨fun Q hQC _ hPQ => hN Q hQC hPQ, fun Q => ?_⟩
    have hPp : IsPGroup ℓ (((P : Subgroup U).map U.subtype).comap (C t).subtype) :=
      (P.isPGroup'.map U.subtype).comap_of_injective (C t).subtype Subtype.val_injective
    obtain ⟨Q₀, hQ₀⟩ := hPp.exists_le_sylow
    have hPQ₀ : (P : Subgroup U).map U.subtype ≤ (Q₀ : Subgroup (C t)).map (C t).subtype := by
      intro x hx
      exact ⟨⟨x, hUC (Subgroup.map_subtype_le _ hx)⟩, hQ₀ hx, rfl⟩
    obtain ⟨T₀, hT₀⟩ := exists_sylow_eq_map_of_normalizer_le Q₀
      (hN _ (Subgroup.map_subtype_le _) hPQ₀)
    have hcard : Nat.card ((Q : Subgroup (C t)).map (C t).subtype) = Nat.card T₀ := by
      rw [Subgroup.card_map_of_injective Subtype.val_injective, hT₀,
        Subgroup.card_map_of_injective Subtype.val_injective, Sylow.card_eq_multiplicity,
        Sylow.card_eq_multiplicity]
    have hcard' : Nat.card ((Q : Subgroup (C t)).map (C t).subtype) =
        ℓ ^ (Nat.card G).factorization ℓ := by
      rw [hcard, Sylow.card_eq_multiplicity]
    exact ⟨Sylow.ofCard _ hcard', Sylow.coe_ofCard _ _⟩
  refine ⟨hlocal, ?_⟩
  refine Nat.coprime_of_dvd fun ℓ hℓ hℓU hℓI => ?_
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow ℓ U))
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow ℓ (C t)))
  obtain ⟨T, hT⟩ := (hlocal ℓ hℓ hℓU P).2 Q
  have hTC : (T : Subgroup G) ≤ C t := by
    rw [hT]
    exact Subgroup.map_subtype_le _
  exact T.not_dvd_index (hℓI.trans (Subgroup.index_dvd_of_le hTC))

end CFSG.Semidihedral.Principal
