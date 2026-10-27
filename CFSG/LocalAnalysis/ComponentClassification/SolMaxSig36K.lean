module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem card_eq_card_map_mul_card_inf_ker' {R G : Type*} [Group R] [Group G] (φ : R →* G)
    (K : Subgroup R) :
    Nat.card K = Nat.card (K.map φ) * Nat.card (K ⊓ φ.ker : Subgroup R) := by
  let ψ : K →* G := φ.comp K.subtype
  have hrange : ψ.range = K.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ψ.ker = Nat.card (K ⊓ φ.ker : Subgroup R) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : K) : R), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker]

variable {M : Subgroup X} {m : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)}

theorem rho_eq_one_of_mem_oddCore (hρ : IsPermAction θ ρ) [Finite X] (hm : 9 ≤ m) {e₀ : X}
    (he₀N : e₀ ∈ normalizer (M : Set X)) (he₀2 : e₀ * e₀ = 1)
    (he₀4 : (ρ ⟨e₀, he₀N⟩).support.card = 4)
    (hON : (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype ≤ normalizer (M : Set X)) {o : X}
    (ho : o ∈ (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype) : ρ ⟨o, hON ho⟩ = 1 := by
  classical
  set O := (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
    (centralizer ({e₀} : Set X)).subtype with hOdef
  set τ := ρ ⟨e₀, he₀N⟩ with hτdef
  have hτ2 : τ * τ = 1 := by
    rw [hτdef, ← map_mul, show (⟨e₀, he₀N⟩ : ↥(normalizer (M : Set X))) * ⟨e₀, he₀N⟩ = 1 from
      Subtype.ext he₀2, map_one]
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, card_map_of_injective (centralizer ({e₀} : Set X)).subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  set I : Subgroup (Perm (Fin m)) := (O.subgroupOf (normalizer (M : Set X))).map ρ with hIdef
  have hIA : ∀ p ∈ I, p ∈ alternatingGroup (Fin m) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Perm.mem_alternatingGroup]
    refine sign_eq_one_of_odd_orderOf ?_
    have h1 : Odd (orderOf z) := by
      have h2 := orderOf_dvd_natCard (⟨(z : X), hz⟩ : ↥O)
      have h3 : orderOf (⟨(z : X), hz⟩ : ↥O) = orderOf z := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe z]
      rw [h3] at h2
      exact hOodd.of_dvd_nat h2
    exact h1.of_dvd_nat (orderOf_map_dvd ρ z)
  set Q : Subgroup (alternatingGroup (Fin m)) := I.comap (alternatingGroup (Fin m)).subtype
    with hQdef
  have hQodd : Odd (Nat.card Q) := by
    have h1 : Nat.card Q ∣ Nat.card I := by
      rw [← card_map_of_injective (alternatingGroup (Fin m)).subtype_injective]
      exact card_dvd_of_le (map_comap_le _ _)
    have h2 : Nat.card I ∣ Nat.card O := by
      have h3 := card_eq_card_map_mul_card_inf_ker' ρ (O.subgroupOf (normalizer (M : Set X)))
      rw [Nat.card_congr (subgroupOfEquivOfLe hON).toEquiv] at h3
      exact ⟨_, h3⟩
    exact hOodd.of_dvd_nat (h1.trans h2)
  have hQc : ∀ g ∈ Q, (g : Perm (Fin m)) * τ = τ * g := by
    intro g hg
    obtain ⟨z, hz, hzg⟩ := hg
    rw [show (g : Perm (Fin m)) = ρ z from hzg.symm, hτdef, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hzC : (z : X) ∈ centralizer ({e₀} : Set X) := map_subtype_le _ hz
    exact mem_centralizer_singleton_iff.mp hzC
  have hQn : ∀ b ∈ fixAlt τ, ∀ g ∈ Q, b * g * b⁻¹ ∈ Q := by
    intro b hb g hg
    obtain ⟨x, hxC, hx⟩ := hρ.exists_lift he₀N he₀2 (commute_of_mem_fixAlt hb)
    have hρx : ρ ⟨x, le_normalizer x.2⟩ = (b : Perm (Fin m)) := by
      rw [hρ.apply_of_mem (by omega) x, hx]
    obtain ⟨z, hz, hzg⟩ := hg
    have hzO : (z : X) ∈ O := hz
    have hxzO : (x : X) * z * (x : X)⁻¹ ∈ O :=
      (mem_normalizer_iff.mp (Sol78.le_normalizer_map_subtype _ hxC) z).mp hzO
    show ((b * g * b⁻¹ : alternatingGroup (Fin m)) : Perm (Fin m)) ∈ I
    refine ⟨⟨_, hON hxzO⟩, hxzO, ?_⟩
    have h1 : (⟨(x : X) * z * (x : X)⁻¹, hON hxzO⟩ : ↥(normalizer (M : Set X))) =
        ⟨x, le_normalizer x.2⟩ * z * (⟨x, le_normalizer x.2⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hρx, hzg]
    rfl
  have hτc : τ.support.card ≤ m := by
    have := Finset.card_le_univ τ.support
    rwa [Fintype.card_fin] at this
  have hQ := eq_bot_of_odd_of_commute hτ2 he₀4.le (by omega) hQodd hQc hQn
  have hmem : ρ ⟨o, hON ho⟩ ∈ I := ⟨⟨o, hON ho⟩, ho, rfl⟩
  have h1 : (⟨ρ ⟨o, hON ho⟩, hIA _ hmem⟩ : alternatingGroup (Fin m)) ∈ Q := hmem
  rw [hQ, mem_bot] at h1
  exact congrArg Subtype.val h1

theorem card_eq_of_alt [Finite X] {K : Subgroup X} {s : ℕ} (hs : 2 ≤ s)
    (θK : ↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin s)) :
    Nat.card K = (s.factorial / 2) * Nat.card (coreNOf K) := by
  have : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr hs
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K),
    Nat.card_congr θK.toEquiv, nat_card_alternatingGroup, Nat.card_fin, coreNOf,
    card_map_of_injective K.subtype_injective]

theorem mem_coreNOf_of_rho_eq_one (hρ : IsPermAction θ ρ) [Finite X] {H : Subgroup X}
    (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {K : Subgroup X} (hKH : K ≤ H) {z : X} (hzK : z ∈ K) (hz : ρ ⟨z, hHN (hKH hzK)⟩ = 1) :
    z ∈ coreNOf K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K₁ := K ⊓ ρ.ker.map (normalizer (M : Set X)).subtype with hK₁def
  have hmemK₁ : ∀ w : X, w ∈ K₁ ↔ ∃ hw : w ∈ K, ρ ⟨w, hHN (hKH hw)⟩ = 1 := by
    intro w
    constructor
    · rintro ⟨hwK, ⟨w', hw', rfl⟩⟩
      exact ⟨hwK, hw'⟩
    · rintro ⟨hwK, hw⟩
      exact ⟨hwK, ⟨_, hw, rfl⟩⟩
  have hnorm : K ≤ normalizer (K₁ : Set X) := by
    intro k hk
    refine mem_normalizer_of_map_conj_le' ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hwK, hw1⟩ := (hmemK₁ w).mp hw
    rw [hmemK₁]
    have hkwK : (MulAut.conj k).toMonoidHom w ∈ K := mul_mem (mul_mem hk hwK) (inv_mem hk)
    refine ⟨hkwK, ?_⟩
    have h1 : (⟨(MulAut.conj k).toMonoidHom w, hHN (hKH hkwK)⟩ : ↥(normalizer (M : Set X))) =
        ⟨k, hHN (hKH hk)⟩ * ⟨w, hHN (hKH hwK)⟩ * (⟨k, hHN (hKH hk)⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, hw1, mul_one, map_inv, mul_inv_cancel]
  have hcop : Nat.Coprime 2 (Nat.card K₁) := by
    rw [Nat.coprime_two_left]
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    obtain ⟨hwK, hw1⟩ := (hmemK₁ w).mp w.2
    have hodd := hker _ (hKH hwK) (hρ.mem_coreActionKernel _ hw1)
    rw [Subgroup.orderOf_coe, hw] at hodd
    exact absurd hodd (by decide)
  exact le_pPrimeCore_map inf_le_left hnorm hcop ((hmemK₁ z).mpr ⟨hzK, hz⟩)

theorem rho_mem_fixAlt_of_mem_oddGen [Finite X] {e₀ : X} (he₀N : e₀ ∈ normalizer (M : Set X))
    (he₀2 : e₀ * e₀ = 1) (he₀4 : (ρ ⟨e₀, he₀N⟩).support.card ≤ 4) {C : Subgroup X}
    (hCN : C ≤ normalizer (M : Set X)) (hCe : C ≤ centralizer ({e₀} : Set X)) {y : X}
    (hy : y ∈ oddGen C) :
    ∀ hyN : y ∈ normalizer (M : Set X),
      ρ ⟨y, hyN⟩ ∈ (fixAlt (ρ ⟨e₀, he₀N⟩)).map (alternatingGroup (Fin m)).subtype := by
  classical
  have hτ2 : ρ ⟨e₀, he₀N⟩ * ρ ⟨e₀, he₀N⟩ = 1 := by
    rw [← map_mul, show (⟨e₀, he₀N⟩ : ↥(normalizer (M : Set X))) * ⟨e₀, he₀N⟩ = 1 from
      Subtype.ext he₀2, map_one]
  change y ∈ Subgroup.closure _ at hy
  induction hy using closure_induction with
  | mem z hz =>
    intro hzN
    have h1 : Odd (orderOf (⟨z, hzN⟩ : ↥(normalizer (M : Set X)))) := by
      rw [Subgroup.orderOf_mk]
      exact hz.2
    have hodd := h1.of_dvd_nat (orderOf_map_dvd ρ _)
    have hcomm : ρ ⟨z, hzN⟩ * ρ ⟨e₀, he₀N⟩ = ρ ⟨e₀, he₀N⟩ * ρ ⟨z, hzN⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hCe hz.1))
    have hA : ρ ⟨z, hzN⟩ ∈ alternatingGroup (Fin m) :=
      Perm.mem_alternatingGroup.mpr (sign_eq_one_of_odd_orderOf hodd)
    refine ⟨⟨_, hA⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixAlt]
    intro w hw
    rw [Finset.mem_compl]
    intro hwτ
    exact (Perm.mem_support.mp hw) (apply_eq_of_odd_commute hτ2 he₀4 hcomm hodd hwτ)
  | one =>
    intro h
    have h1 : ρ ⟨1, h⟩ = 1 := map_one ρ
    rw [h1]
    exact one_mem _
  | mul z w hz hw ihz ihw =>
    intro hzwN
    have hzN : z ∈ normalizer (M : Set X) := hCN (oddGen_le C hz)
    have hwN : w ∈ normalizer (M : Set X) := hCN (oddGen_le C hw)
    have h1 : (⟨z * w, hzwN⟩ : ↥(normalizer (M : Set X))) = ⟨z, hzN⟩ * ⟨w, hwN⟩ := rfl
    rw [h1, map_mul]
    exact mul_mem (ihz hzN) (ihw hwN)
  | inv z hz ihz =>
    intro hzN'
    have hzN : z ∈ normalizer (M : Set X) := hCN (oddGen_le C hz)
    have h1 : (⟨z⁻¹, hzN'⟩ : ↥(normalizer (M : Set X))) = (⟨z, hzN⟩)⁻¹ := rfl
    rw [h1, map_inv]
    exact inv_mem (ihz hzN)

end CFSG.ComponentClassification.SolMax
