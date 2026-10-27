module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace F3L225

theorem isThetaBalanced_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsThetaBalanced A) : IsThetaBalanced B := by
  intro H _ _ ⟨eH⟩ t ht
  exact h H ⟨eH.trans e.symm⟩ t ht

theorem exists_pow_two_pow {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B) (x : A)
    {n : ℕ} (hx : f x ^ 2 ^ n = 1) : ∃ k : ℕ, (∃ m : ℕ, (x ^ k) ^ 2 ^ m = 1) ∧ f (x ^ k) = f x := by
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hx0
  have hcop : Nat.Coprime b (orderOf (f x)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx)
      ((Nat.coprime_two_right.mpr hb).pow_right n)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨b * m, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, show b * m * 2 ^ a = (2 ^ a * b) * m by ring, ← hab, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, pow_mul, hm]

variable {G : Type} [Group G] [Finite G]

theorem orderOf_mk_mbar_eq_two {w : G} {x : ↥(centralizer ({w} : Set G))} (hx : orderOf x = 2) :
    orderOf (QuotientGroup.mk x : MBar w) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxO : x ∉ pPrimeCore 2 ↥(centralizer ({w} : Set G)) := by
    intro h
    have h1 := orderOf_dvd_natCard (⟨x, h⟩ : ↥(pPrimeCore 2 ↥(centralizer ({w} : Set G))))
    rw [← Subgroup.orderOf_coe, hx] at h1
    exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two _)) (even_iff_two_dvd.mpr h1)
  have hxx : x ^ 2 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, hxx, QuotientGroup.mk_one]
  · intro h
    exact hxO ((QuotientGroup.eq_one_iff x).mp h)

theorem nonempty_fusionZStar_equiv_hatIn {w : G} {K : Subgroup G}
    (hK : IsTwoComponentIn K (centralizer {w})) :
    Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* ↥(hatIn w K) ⧸ center ↥(hatIn w K)) := by
  obtain ⟨-, -, ⟨E⟩⟩ := hatIn_spec hK
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥K
  exact ⟨eZ.trans (QuotientGroup.congr _ _ E (OuterAutomorphisms.center_map_equiv E))⟩

theorem oPrimeResidualOf_two_le_of_hatIn {w : G} {L₁ K : Subgroup G}
    (hK : IsTwoComponentIn K (centralizer {w})) (hL₁C : L₁ ≤ centralizer {w})
    (hall : ∀ s ∈ hatIn w L₁, (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ hatIn w K) :
    GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K := by
  unfold GH74.GLS.oPrimeResidualOf GH74.GLS.oPrimeResidual
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, ⟨n, hn⟩, rfl⟩
  have hxn : (x : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hxC : (x : G) ∈ centralizer ({w} : Set G) := hL₁C x.2
  have h1 : (⟨(x : G), hxC⟩ : ↥(centralizer ({w} : Set G))) ^ 2 ^ n = 1 :=
    Subtype.ext (by simpa using hxn)
  have h2 : (QuotientGroup.mk (⟨(x : G), hxC⟩ : ↥(centralizer ({w} : Set G))) : MBar w) ^
      2 ^ n = 1 := by
    rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  exact mem_of_mk_mem_hatIn hK hxC hxn (hall _ (mk_mem_hatIn x.2 hxC) ⟨n, h2⟩)

theorem commutator_le_of_centralizes {w : G} {L₁ K : Subgroup G} {p : ℕ}
    (hK : IsTwoComponentIn K (centralizer {w})) (hL₁C : L₁ ≤ centralizer {w})
    (hL₁N : L₁ ≤ normalizer (K : Set G))
    (key : ∀ y ∈ hatIn w L₁, (∃ n : ℕ, y ^ p ^ n = 1) → ∀ l ∈ hatIn w K, y * l = l * y) :
    ⁅K, GH74.GLS.oPrimeResidualOf p L₁⁆ ≤ (pPrimeCore 2 ↥K).map K.subtype := by
  set C := centralizer ({w} : Set G) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  let ψ : ↥L₁ →* MBar w := π.comp (inclusion hL₁C)
  have hψ : GH74.GLS.oPrimeResidual p ↥L₁ ≤
      (centralizer ((hatIn w K : Subgroup (MBar w)) : Set (MBar w))).comap ψ := by
    unfold GH74.GLS.oPrimeResidual
    rw [closure_le]
    rintro y ⟨n, hn⟩
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_iff]
    intro l hl
    have hyM : ψ y ∈ hatIn w L₁ := ⟨inclusion hL₁C y, y.2, rfl⟩
    have hyn : ψ y ^ p ^ n = 1 := by rw [← map_pow, hn, map_one]
    exact (key _ hyM ⟨n, hyn⟩ l hl).symm
  rw [Subgroup.commutator_le]
  intro k hk y hy
  obtain ⟨y', hy', rfl⟩ := hy
  have hkC : k ∈ C := hK.1 hk
  have hcy := mem_centralizer_iff.mp (hψ hy') (π ⟨k, hkC⟩) (mk_mem_hatIn hk hkC)
  have hkyK : k * (y' : G) * k⁻¹ * (y' : G)⁻¹ ∈ K := by
    have hy'N : (y' : G) ∈ normalizer (K : Set G) := hL₁N (map_subtype_le _ ⟨y', hy', rfl⟩)
    have h1 : (y' : G) * k⁻¹ * (y' : G)⁻¹ ∈ K := (mem_normalizer_iff.mp hy'N _).mp (inv_mem hk)
    rw [show k * (y' : G) * k⁻¹ * (y' : G)⁻¹ = k * ((y' : G) * k⁻¹ * (y' : G)⁻¹) by group]
    exact mul_mem hk h1
  have h1 : (⟨k * (y' : G) * k⁻¹ * (y' : G)⁻¹, hK.1 hkyK⟩ : ↥C) ∈ pPrimeCore 2 ↥C := by
    rw [← QuotientGroup.eq_one_iff]
    have h2 : (⟨k * (y' : G) * k⁻¹ * (y' : G)⁻¹, hK.1 hkyK⟩ : ↥C) =
        ⟨k, hkC⟩ * inclusion hL₁C y' * ⟨k, hkC⟩⁻¹ * (inclusion hL₁C y')⁻¹ := by
      apply Subtype.ext
      simp
    rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    have h3 : (QuotientGroup.mk (inclusion hL₁C y') : MBar w) = ψ y' := rfl
    have h4 : (QuotientGroup.mk ⟨k, hkC⟩ : MBar w) = π ⟨k, hkC⟩ := rfl
    rw [h3, h4, hcy]
    group
  have h5 := (F3L226.mem_pPrimeCore_iff hK hkyK).mpr h1
  rw [commutatorElement_def]
  exact ⟨_, h5, rfl⟩

end F3L225

end CFSG.ComponentClassification.HarrisLit.T1
