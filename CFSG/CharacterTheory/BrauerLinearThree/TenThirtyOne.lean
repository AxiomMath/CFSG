module

public import CFSG.CharacterTheory.BrauerLinearThree.TenIndex

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  CFSG.Semidihedral.Principal
open CFSG.Semidihedral (r s modulus)

namespace TenArith

theorem thirtyone_order {Gc f₁ c d q : ℕ} {δ₁ e : ℤ} (hc : c = 59520) (hd : d = 60)
    (he : e = -1) (hq : q = 31) (hne : (f₁ : ℚ) - e * δ₁ * q ≠ 0)
    (hG : (Gc : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 *
      ((f₁ : ℚ) * (f₁ + δ₁) / (f₁ - e * δ₁ * q) ^ 2) * ((q + e) / q)) :
    (Gc : ℤ) * ((f₁ : ℤ) + 31 * δ₁) ^ 2 = 56682086400 * ((f₁ : ℤ) * (f₁ + δ₁)) := by
  subst hc hd he hq
  have hs : ((f₁ : ℚ) - ((-1 : ℤ) : ℚ) * δ₁ * ((31 : ℕ) : ℚ)) = (f₁ : ℚ) + 31 * δ₁ := by
    push_cast
    ring
  rw [hs] at hne hG
  push_cast at hG
  set s : ℚ := (f₁ : ℚ) + 31 * δ₁ with hsdef
  have key : (Gc : ℚ) * s ^ 2 = 56682086400 * ((f₁ : ℚ) * (f₁ + δ₁)) := by
    rw [hG, show (59520 : ℚ) ^ 3 / 60 ^ 2 * ((f₁ : ℚ) * (f₁ + δ₁) / s ^ 2) * ((31 + -1) / 31) *
      s ^ 2 = 56682086400 * ((f₁ : ℚ) * (f₁ + δ₁)) * (s ^ 2 / s ^ 2) by ring,
      div_self (pow_ne_zero 2 hne), mul_one]
  rw [hsdef] at key
  exact_mod_cast key

theorem thirtyone_false {Gc f₁ f₂ f₃ : ℕ} {δ₁ δ₂ δ₃ : ℤ}
    (hsigns : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hsum : 1 + δ₁ * (f₁ : ℤ) + δ₂ * (f₂ : ℤ) + δ₃ * (f₃ : ℤ) = 0)
    (hprod : (f₁ : ℤ) * (f₂ : ℤ) = 31 ^ 2 * (f₃ : ℤ))
    (hc₁ : (128 : ℤ) ∣ f₁ - 33 * δ₁) (hc₂ : (128 : ℤ) ∣ f₂ - 31 * δ₂)
    (hG : (Gc : ℤ) * ((f₁ : ℤ) + 31 * δ₁) ^ 2 = 56682086400 * ((f₁ : ℤ) * (f₁ + δ₁)))
    (h25 : 25 ∣ Gc) : False := by
  have hδ₁ : δ₁ = 1 ∨ δ₁ = -1 := by omega
  have hδ₂ : δ₂ = 1 ∨ δ₂ = -1 := by omega
  have hδ₃ : δ₃ = δ₁ * δ₂ := by
    rcases hsigns with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;> norm_num
  rw [hδ₃] at hsum
  have h38 : (961 + δ₁ * (f₁ : ℤ)) * (961 + δ₂ * (f₂ : ℤ)) = 922560 := by
    linear_combination 961 * hsum + δ₁ * δ₂ * hprod
  obtain ⟨k₁, hk₁⟩ := hc₁
  obtain ⟨k₂, hk₂⟩ := hc₂
  obtain ⟨a, ha⟩ : ∃ a, a = δ₁ * k₁ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = δ₂ * k₂ := ⟨_, rfl⟩
  have hX : 961 + δ₁ * (f₁ : ℤ) = 2 * (497 + 64 * a) := by
    rw [ha]
    rcases hδ₁ with h | h <;> rw [h] at hk₁ ⊢ <;> linarith
  have hY : 961 + δ₂ * (f₂ : ℤ) = 32 * (31 + 4 * b) := by
    rw [hb]
    rcases hδ₂ with h | h <;> rw [h] at hk₂ ⊢ <;> linarith
  have hxy : (497 + 64 * a) * (31 + 4 * b) = 14415 := by
    rw [hX, hY] at h38
    have h : 64 * ((497 + 64 * a) * (31 + 4 * b)) = 64 * 14415 := by linear_combination h38
    exact mul_left_cancel₀ (by norm_num) h
  set x := 497 + 64 * a with hxdef
  have hdvd : x.natAbs ∣ 15 * 31 ^ 2 := Int.natAbs_dvd_natAbs.mpr ⟨_, hxy.symm⟩
  have hx : x = -15 ∨ x = -14415 := by
    obtain ⟨u, w, hu, hw, huw⟩ := Nat.dvd_mul.mp hdvd
    obtain ⟨u₁, u₂, hu₁, hu₂, rfl⟩ := Nat.dvd_mul.mp (show u ∣ 3 * 5 from hu)
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hw
    rcases (Nat.dvd_prime (by norm_num)).mp hu₁ with rfl | rfl <;>
      rcases (Nat.dvd_prime (by norm_num)).mp hu₂ with rfl | rfl <;>
      interval_cases k <;> norm_num at huw <;> omega
  have hf₁ : δ₁ = -1 ∧ ((f₁ : ℤ) = 991 ∨ (f₁ : ℤ) = 29791) := by
    rcases hx with h | h <;> rcases hδ₁ with h' | h' <;> rw [h'] at hX <;> omega
  obtain ⟨hδ₁', hf⟩ := hf₁
  rw [hδ₁'] at hG
  rcases hf with hf | hf <;> rw [hf] at hG <;> norm_num at hG <;> omega

end TenArith

theorem false_of_field_card_thirtyone
    {G : Type} [Group G] [Fintype G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq31 : p ^ f = 31)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    False := by
  set s₀ : G := (fS (s n) : G) with hs₀def
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ with hVdef
  set D : Subgroup G := Subgroup.centralizer (V : Set G) with hDdef
  set W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype with hWdef
  set K : Subgroup G := Subgroup.centralizer (W : Set G) with hKdef
  have hq : 3 < p ^ f := by omega
  have hq3 : p ^ f % 4 = 3 := by omega
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  have hdvd : Nat.card W ∣ (W.subgroupOf K).index :=
    card_torus_dvd_index n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hq3 hmodel hN hY
  obtain ⟨hC, -, hWcyc, hWodd, hWcard, ⟨hsup, hdisj, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, ⟨hcases, -⟩, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hWcyc : IsCyclic W := hWcyc
  have hWodd : Odd (Nat.card W) := hWodd
  have hsup : V ⊔ W = D := hsup
  have hdisj : Disjoint V W := hdisj
  have hW15 : Nat.card W = 15 := by
    have h : (Nat.card W : ℤ) = (((p ^ f : ℕ) : ℤ) + if p ^ f % 4 = 1 then 1 else -1) / 2 :=
      hWcard
    have h30 : ((31 : ℕ) : ℤ) + (if 31 % 4 = 1 then 1 else -1) = 30 := by norm_num
    rw [hq31, h30] at h
    omega
  have hcases : Nat.card K = 12 * Nat.card W ∨ Nat.card K = 60 * Nat.card W := by
    rcases hcases with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hWK : W ≤ K := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hWcomm x hx w hw
  have hindex : Nat.card K = (W.subgroupOf K).index * Nat.card W := by
    have h := Subgroup.card_mul_index (W.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv] at h
    rw [← h, mul_comm]
  have hK900 : Nat.card K = 900 := by
    rcases hcases with h | h
    · exfalso
      rw [h, hW15] at hindex
      have h12 : (W.subgroupOf K).index = 12 := by omega
      rw [h12, hW15] at hdvd
      norm_num at hdvd
    · rw [h, hW15]
  have h25 : 25 ∣ Nat.card G := by
    have h := Subgroup.card_subgroup_dvd_card K
    rw [hK900] at h
    exact (by norm_num : (25 : ℕ) ∣ 900).trans h
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  obtain ⟨hDcard, -⟩ := klein_centralizer_odd_core V W hV hWodd hWcomm hsup hdisj
  have hdD : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 60 := by
    rw [show (60 : ℕ) = 4 * Nat.card W by rw [hW15], ← hDcard]
    change _ = Nat.card (Subgroup.centralizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers (fS (s n) : G) : Subgroup G) : Set G))
    rw [centralizer_zpowers_sup_zpowers]
  have hCcard : Nat.card (C t) = 59520 := by
    rw [hC, hq31]
    norm_num
  obtain ⟨⟨ideal₂, hmax₂, h2mem⟩, hchar₂⟩ := CFSG.BlockBasics.residue_prime_existence 2
    Nat.prime_two
  have : ideal₂.IsMaximal := hmax₂
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2 := hchar₂ ideal₂ hmax₂ h2mem
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨F, hfield, hfinite, ρF, hFcard, -, -, -, hrest⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal₂ basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  obtain ⟨-, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ₂, ν₂, hfam, hdeg, -, hOFall⟩ := hrest
  obtain ⟨hne₁, -, hG₁, -⟩ := hOFall S fS hcent
  have hFq : Nat.card F = 31 := hFcard.trans hq31
  have hq3' : 3 ≤ Nat.card F := by omega
  have hqoddF : Odd (Nat.card F) := by rw [hFq]; decide
  have he1 : Nat.card F % 4 = 1 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 :=
    fun h => by simp [h]
  have he3 : Nat.card F % 4 = 3 → (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 :=
    fun h => by simp [show ¬ Nat.card F % 4 = 1 by omega]
  obtain ⟨F', hF', hF'fin, A', ρ', hdata⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht2
    hnonab hcentral hnc p f hp hpodd hf hmodel
  have hqM : 2 ^ padicValNat 2 (Nat.card F ^ 2 - 1) = modulus n := by
    have h := hdata.two_part
    rw [hdata.field_card, Nat.factorization_def _ Nat.prime_two] at h
    rw [hFcard, h]
    rfl
  obtain ⟨-, -, -, -, -, -, hsigns, hsum, hprod, hc₁, hc₂⟩ :=
    perfect_family_degree_data hn fS hcent ht2 hnonab basis ideal₂ principal hprincipal
      localBasis localPrincipal (Nat.card F) hq3' hqoddF hqM _ he1 he3 _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄
      ψ₂ ν₂ hfam hdeg
  have he : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 := by rw [hFq]; norm_num
  have hM : modulus n = 64 := by
    have h := hqM
    rw [hFq, modulus, show (31 ^ 2 - 1 : ℕ) = 2 ^ 6 * 15 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)] at h
    rw [modulus, ← h]
    norm_num
  have hc₁' : (128 : ℤ) ∣ (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) - 33 * δ₁ := by
    obtain ⟨k, hk⟩ := hc₁.symm.dvd
    rw [he, hFq, hM] at hk
    push_cast at hk
    exact ⟨k, by linear_combination hk⟩
  have hc₂' : (128 : ℤ) ∣ (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) - 31 * δ₂ := by
    obtain ⟨k, hk⟩ := hc₂.symm.dvd
    rw [he, hFq, hM] at hk
    push_cast at hk
    exact ⟨k, by linear_combination hk⟩
  rw [hFq] at hprod
  push_cast at hprod
  exact TenArith.thirtyone_false hsigns hsum hprod hc₁' hc₂'
    (TenArith.thirtyone_order hCcard hdD he hFq hne₁ hG₁) h25

end CFSG.BrauerLinearThree
