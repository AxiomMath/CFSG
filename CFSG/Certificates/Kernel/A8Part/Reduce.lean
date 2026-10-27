module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.KC.A8Part

open Equiv

@[expose] def partStab (S : Finset (Fin 8)) : Subgroup (Perm (Fin 8)) where
  carrier := {g | (∀ i, g i ∈ S ↔ i ∈ S) ∨ (∀ i, g i ∈ S ↔ i ∉ S)}
  mul_mem' := by
    rintro g h (hg | hg) (hh | hh)
    · exact Or.inl fun i => by rw [Perm.mul_apply, hg, hh]
    · exact Or.inr fun i => by rw [Perm.mul_apply, hg, hh]
    · exact Or.inr fun i => by rw [Perm.mul_apply, hg, hh]
    · exact Or.inl fun i => by rw [Perm.mul_apply, hg, hh, not_not]
  one_mem' := Or.inl fun _ => Iff.rfl
  inv_mem' := by
    rintro g (hg | hg)
    · refine Or.inl fun i => ?_
      have := hg (g⁻¹ i)
      rw [Perm.inv_def, Equiv.apply_symm_apply] at this
      rw [Perm.inv_def]
      exact this.symm
    · refine Or.inr fun i => ?_
      have := hg (g⁻¹ i)
      rw [Perm.inv_def, Equiv.apply_symm_apply] at this
      rw [Perm.inv_def]
      tauto

theorem card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem factorization_eq {q a b n : ℕ} (hq : q.Prime) (hn : n = q ^ a * b) (hb : ¬ q ∣ b) :
    n.factorization q = a := by
  subst hn
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (dvd_zero q)
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hb0, Finsupp.add_apply,
    hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hb,
    add_zero]

theorem alt8_fact2 : (Nat.card (alternatingGroup (Fin 8))).factorization 2 = 6 :=
  factorization_eq (b := 315) Nat.prime_two (card_alt8.trans (by norm_num)) (by norm_num)

theorem alt8_fact3 : (Nat.card (alternatingGroup (Fin 8))).factorization 3 = 2 :=
  factorization_eq (b := 2240) Nat.prime_three (card_alt8.trans (by norm_num)) (by norm_num)

variable {G : Type*} [Group G] [Finite G]

theorem exists_le_card_pow {p n : ℕ} [Fact p.Prime] {N : Subgroup G}
    (h : p ^ n ∣ Nat.card N) : ∃ K ≤ N, Nat.card K = p ^ n := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := N) p h
  refine ⟨K.map N.subtype, Subgroup.map_subtype_le K, ?_⟩
  rw [Subgroup.card_map_of_injective N.subtype_injective, hK]

theorem exists_conj_le {p : ℕ} [Fact p.Prime] {A S P : Subgroup G} (hSA : S ≤ A)
    (hS : Nat.card S = p ^ (Nat.card A).factorization p) (hPA : P ≤ A) (hP : IsPGroup p P) :
    ∃ g ∈ A, ∀ z ∈ P, g * z * g⁻¹ ∈ S := by
  have hS' : Nat.card (S.subgroupOf A) = p ^ (Nat.card A).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSA).toEquiv, hS]
  let S' : Sylow p A := Sylow.ofCard _ hS'
  have hP' : IsPGroup p (P.subgroupOf A) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPA).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A Q S'
  refine ⟨(g : G), g.2, fun z hz => ?_⟩
  have h1 : (⟨z, hPA hz⟩ : A) ∈ (Q : Subgroup A) := hQ (Subgroup.mem_subgroupOf.mpr hz)
  have h2 : g * ⟨z, hPA hz⟩ * g⁻¹ ∈ ((g • Q : Sylow p A) : Subgroup A) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨_, h1, rfl⟩
  rw [hg, Sylow.coe_ofCard] at h2
  exact Subgroup.mem_subgroupOf.mp h2

abbrev conjBy (g : G) (N : Subgroup G) : Subgroup G := N.map (MulAut.conj g).toMonoidHom

theorem mem_conjBy {g z : G} {N : Subgroup G} (hz : z ∈ N) : g * z * g⁻¹ ∈ conjBy g N :=
  ⟨z, hz, rfl⟩

theorem card_conjBy (g : G) (N : Subgroup G) : Nat.card (conjBy g N) = Nat.card N :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjBy_le {g : G} {N A : Subgroup G} (hg : g ∈ A) (hN : N ≤ A) : conjBy g N ≤ A := by
  rintro _ ⟨z, hz, rfl⟩
  exact A.mul_mem (A.mul_mem hg (hN hz)) (A.inv_mem hg)

theorem two_of_overgroups {A S₀ : Subgroup G} (hA2 : (Nat.card A).factorization 2 = 6)
    (hSA : S₀ ≤ A) (hS : Nat.card S₀ = 64)
    (hlat : ∀ K : Subgroup G, S₀ ≤ K → K ≤ A → Nat.card K = 64 ∨ Nat.card K = 192 ∨
      Nat.card K = 576 ∨ Nat.card K = 1344 ∨ Nat.card K = 20160) :
    ∀ J : Subgroup G, J ≤ A → 64 ∣ Nat.card J → Nat.card J = 64 ∨ Nat.card J = 192 ∨
      Nat.card J = 576 ∨ Nat.card J = 1344 ∨ Nat.card J = 20160 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro J hJA h64
  obtain ⟨P, hPJ, hP⟩ := exists_le_card_pow (p := 2) (n := 6) (N := J) (by norm_num [h64])
  obtain ⟨g, hgA, hg⟩ := exists_conj_le hSA (by rw [hS, hA2]; norm_num) (hPJ.trans hJA)
    (IsPGroup.of_card hP)
  have hPS : conjBy g P ≤ S₀ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hg z hz
  have hPeq : conjBy g P = S₀ :=
    Subgroup.eq_of_le_of_card_ge hPS (by rw [card_conjBy, hP, hS]; norm_num)
  have h := hlat (conjBy g J) (hPeq ▸ Subgroup.map_mono hPJ) (conjBy_le hgA hJA)
  rwa [card_conjBy] at h

theorem sylow3_cand {A S₀ Q₀ H N : Subgroup G} {T : ℕ → Subgroup G} {x r : ℕ → G} {nP nR : ℕ}
    (hA2 : (Nat.card A).factorization 2 = 6) (hA3 : (Nat.card A).factorization 3 = 2)
    (hSA : S₀ ≤ A) (hS : Nat.card S₀ = 64) (hQA : Q₀ ≤ A) (hQ : Nat.card Q₀ = 9)
    (hcov : ∀ σ ∈ A, ∃ s ∈ S₀, ∃ j < nR, ∃ y ∈ H, σ = s * r j * y)
    (hH : ∀ y ∈ H, ∀ q ∈ Q₀, y * q * y⁻¹ ∈ Q₀)
    (hcos : ∀ p < nP, ∀ s ∈ S₀, s ∈ T p ∨ s * (x p)⁻¹ ∈ T p)
    (hT : ∀ P ≤ S₀, Nat.card P = 32 → ∃ p < nP, T p ≤ P)
    (hNA : N ≤ A) (hN : 288 ∣ Nat.card N) :
    ∃ g ∈ A, ∃ p < nP, ∃ j < nR, ∃ c : G, (c = r j ∨ c = x p * r j) ∧
      T p ≤ conjBy g N ∧ ∀ q ∈ Q₀, c * q * c⁻¹ ∈ conjBy g N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPN, hP⟩ := exists_le_card_pow (p := 2) (n := 5) (N := N)
    ((by norm_num : 2 ^ 5 ∣ 288).trans hN)
  obtain ⟨Q, hQN, hQc⟩ := exists_le_card_pow (p := 3) (n := 2) (N := N)
    ((by norm_num : 3 ^ 2 ∣ 288).trans hN)
  obtain ⟨g, hgA, hg⟩ := exists_conj_le hSA (by rw [hS, hA2]; norm_num) (hPN.trans hNA)
    (IsPGroup.of_card hP)
  obtain ⟨p, hp, hTp⟩ := hT (conjBy g P) (by rintro _ ⟨z, hz, rfl⟩; exact hg z hz)
    (by rw [card_conjBy, hP]; norm_num)
  have hTN : T p ≤ conjBy g N := hTp.trans (Subgroup.map_mono hPN)
  have hQ'A : conjBy g Q ≤ A := conjBy_le hgA (hQN.trans hNA)
  obtain ⟨k, hkA, hk⟩ := exists_conj_le hQA (by rw [hQ, hA3]; norm_num) hQ'A
    (IsPGroup.of_card (n := 2) (by rw [card_conjBy, hQc]))
  have hkQ : conjBy k (conjBy g Q) = Q₀ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_conjBy, card_conjBy, hQc, hQ]; norm_num)
    rintro _ ⟨z, hz, rfl⟩
    exact hk z hz
  have hQ' : ∀ q ∈ Q₀, k⁻¹ * q * k ∈ conjBy g N := by
    intro q hq
    rw [← hkQ] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    have hz' : z ∈ conjBy g N := Subgroup.map_mono hQN hz
    have e : k⁻¹ * ((MulAut.conj k).toMonoidHom z) * k = z := by
      change k⁻¹ * (k * z * k⁻¹) * k = z
      group
    rw [e]
    exact hz'
  obtain ⟨s, hs, j, hj, y, hy, hky⟩ := hcov k⁻¹ (A.inv_mem hkA)
  have key : ∀ τ ∈ T p, ∀ c : G, k⁻¹ = τ * c * y → ∀ q ∈ Q₀, c * q * c⁻¹ ∈ conjBy g N := by
    intro τ hτ c hc q hq
    have hq' := hQ' _ (hH y⁻¹ (H.inv_mem hy) q hq)
    have hk' : k = (τ * c * y)⁻¹ := by rw [← hc, inv_inv]
    subst hk'
    have e : c * q * c⁻¹ = τ⁻¹ * ((τ * c * y)⁻¹⁻¹ * (y⁻¹ * q * y⁻¹⁻¹) * (τ * c * y)⁻¹) * τ := by
      group
    rw [e]
    exact (conjBy g N).mul_mem ((conjBy g N).mul_mem ((conjBy g N).inv_mem (hTN hτ)) hq')
      (hTN hτ)
  refine ⟨g, hgA, p, hp, j, hj, ?_⟩
  rcases hcos p hp s hs with h | h
  · exact ⟨r j, Or.inl rfl, hTN, key s h (r j) hky⟩
  · refine ⟨x p * r j, Or.inr rfl, hTN, key _ h _ ?_⟩
    rw [hky]
    group

theorem le_of_dcover {A B J K : Subgroup G} {ρ : ℕ → G} {nρ : ℕ} (hJ : J ≤ B)
    (hcov : ∀ σ ∈ A, ∃ i < nρ, ∃ π ∈ J, ∃ κ ∈ J, σ = π * ρ i * κ)
    (hρ : ∀ i < nρ, ρ i ∈ B ∨ A ≤ J ⊔ Subgroup.closure {ρ i})
    (hJK : J ≤ K) (hKA : K ≤ A) (hne : K ≠ A) : K ≤ B := by
  intro σ hσ
  obtain ⟨i, hi, π, hπ, κ, hκ, rfl⟩ := hcov σ (hKA hσ)
  have hρK : ρ i ∈ K := by
    have e : ρ i = π⁻¹ * (π * ρ i * κ) * κ⁻¹ := by group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.inv_mem (hJK hπ)) hσ) (K.inv_mem (hJK hκ))
  rcases hρ i hi with h | h
  · exact B.mul_mem (B.mul_mem (hJ hπ) h) (hJ hκ)
  · refine absurd (le_antisymm hKA (h.trans (sup_le hJK ?_))) hne
    rw [Subgroup.closure_le]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    exact hρK

theorem part_of_cands {S₀ Q₀ H : Subgroup (Perm (Fin 8))} {T : ℕ → Subgroup (Perm (Fin 8))}
    {x r : ℕ → Perm (Fin 8)} {nP nR : ℕ}
    (hSA : S₀ ≤ alternatingGroup (Fin 8)) (hS : Nat.card S₀ = 64)
    (hQA : Q₀ ≤ alternatingGroup (Fin 8)) (hQ : Nat.card Q₀ = 9)
    (hcov : ∀ σ ∈ alternatingGroup (Fin 8), ∃ s ∈ S₀, ∃ j < nR, ∃ y ∈ H, σ = s * r j * y)
    (hH : ∀ y ∈ H, ∀ q ∈ Q₀, y * q * y⁻¹ ∈ Q₀)
    (hcos : ∀ p < nP, ∀ s ∈ S₀, s ∈ T p ∨ s * (x p)⁻¹ ∈ T p)
    (hT : ∀ P ≤ S₀, Nat.card P = 32 → ∃ p < nP, T p ≤ P)
    (hcand : ∀ p < nP, ∀ j < nR, ∀ c : Perm (Fin 8), (c = r j ∨ c = x p * r j) →
      ∀ K : Subgroup (Perm (Fin 8)), T p ≤ K → (∀ q ∈ Q₀, c * q * c⁻¹ ∈ K) →
        K ≤ alternatingGroup (Fin 8) → K ≠ alternatingGroup (Fin 8) →
          ∃ S : Finset (Fin 8), S.card = 4 ∧ K ≤ partStab S) :
    ∀ N : Subgroup (Perm (Fin 8)), N ≤ alternatingGroup (Fin 8) → 288 ∣ Nat.card N →
      N ≠ alternatingGroup (Fin 8) → ∃ S : Finset (Fin 8), S.card = 4 ∧
        ∀ g ∈ N, (∀ i, g i ∈ S ↔ i ∈ S) ∨ (∀ i, g i ∈ S ↔ i ∉ S) := by
  intro N hNA h288 hne
  obtain ⟨g, hgA, p, hp, j, hj, c, hc, hTN, hQN⟩ :=
    sylow3_cand alt8_fact2 alt8_fact3 hSA hS hQA hQ hcov hH hcos hT hNA h288
  have hne' : conjBy g N ≠ alternatingGroup (Fin 8) := by
    intro h
    refine hne (Subgroup.eq_of_le_of_card_ge hNA ?_)
    rw [← card_conjBy g N, h]
  obtain ⟨S', hS', hst⟩ := hcand p hp j hj c hc _ hTN hQN (conjBy_le hgA hNA) hne'
  refine ⟨S'.map (Equiv.toEmbedding g⁻¹), by rw [Finset.card_map, hS'], fun y hy => ?_⟩
  have hy₁ : g * y * g⁻¹ ∈ partStab S' := hst (mem_conjBy hy)
  have hmemS : ∀ i : Fin 8, i ∈ S'.map (Equiv.toEmbedding g⁻¹) ↔ g i ∈ S' := by
    intro i
    rw [Finset.mem_map_equiv, Perm.inv_def, Equiv.symm_symm]
  have hyi : ∀ i : Fin 8, (g * y * g⁻¹) (g i) = g (y i) := by
    intro i
    simp [Perm.mul_apply]
  rcases hy₁ with h | h
  · exact Or.inl fun i => by rw [hmemS, hmemS, ← hyi, h]
  · exact Or.inr fun i => by rw [hmemS, hmemS, ← hyi, h]

end CFSG.KC.A8Part
