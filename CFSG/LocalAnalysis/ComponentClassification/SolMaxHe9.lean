module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe9A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36W

public section

namespace CFSG.ComponentClassification.SolMax.He9

open CFSG Subgroup Equiv CFSG.Sporadic.HeldB

variable {X : Type} [Group X]

theorem false_of_le_normalizer_of_held
    [Finite X]
    {M : Subgroup X} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {N : Subgroup X}
    (hNM : N ≤ normalizer (M : Set X))
    (hN : Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* Blueprint.NativeSporadic.He)) {x : X} (hxN : x ∈ N)
    (hxM : x ∈ M) (hx2 : x * x = 1) (hx1 : x ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψb⟩ := hN
  set O := pPrimeCore 2 ↥N with hOdef
  set φ : ↥N →* Perm (Fin 9) := ρ.comp (inclusion hNM) with hφdef
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hφx : φ ⟨x, hxN⟩ ≠ 1 := by
    intro h
    have hxK : x ∈ UnbalancedLayer.coreActionKernel M := hρ.mem_coreActionKernel (hNM hxN) h
    obtain ⟨o, ho, rfl⟩ := mem_core_of_mem_coreActionKernel hρ (by norm_num) hxM hxK
    have h1 : Odd (orderOf (⟨o, ho⟩ : ↥(pPrimeCore 2 ↥M))) :=
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat (orderOf_dvd_natCard _)
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at h1
    change Odd (orderOf (M.subtype o)) at h1
    rw [hxo] at h1
    exact absurd h1 (by decide)
  have : IsSimpleGroup heP := heP_simple
  set Θ : ↥N ⧸ O ≃* heP := ψb.trans heEquivP with hΘdef
  set π : ↥N →* heP := Θ.toMonoidHom.comp (QuotientGroup.mk' O) with hπdef
  have hπs : Function.Surjective π := Θ.surjective.comp (QuotientGroup.mk'_surjective O)
  have hπ : ∀ n, π n = 1 ↔ n ∈ O := fun n => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have : (φ.ker.map π).Normal := Normal.map φ.normal_ker π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map π) with h | h
  ·
    have hkO : φ.ker ≤ O := fun k hk => by
      have h1 : π k ∈ φ.ker.map π := mem_map_of_mem _ hk
      rw [h, mem_bot] at h1
      exact (hπ k).mp h1
    have h1 : Nat.card ↥N = Nat.card (↥N ⧸ O) * Nat.card O :=
      card_eq_card_quotient_mul_card_subgroup O
    have h2 : Nat.card ↥N = Nat.card φ.range * Nat.card φ.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      exact card_eq_card_quotient_mul_card_subgroup _
    obtain ⟨q, hq⟩ : Nat.card φ.ker ∣ Nat.card O := card_dvd_of_le hkO
    have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
    have h3 : Nat.card φ.range = Nat.card (↥N ⧸ O) * q := by
      rw [hq, h2] at h1
      have h4 : Nat.card φ.range * Nat.card φ.ker = Nat.card (↥N ⧸ O) * q * Nat.card φ.ker := by
        rw [h1]
        ring
      exact Nat.eq_of_mul_eq_mul_right hkpos h4
    have h17 : 17 ∣ Nat.card φ.range := by
      rw [h3, Nat.card_congr Θ.toEquiv, card_heP]
      exact Dvd.dvd.mul_right (by norm_num) _
    have h5 : Nat.card φ.range ∣ Nat.card (Perm (Fin 9)) := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_perm, Nat.card_fin] at h5
    have h6 := h17.trans h5
    exact absurd h6 (by decide)
  ·
    obtain ⟨k, hk, hkx⟩ : π ⟨x, hxN⟩ ∈ φ.ker.map π := by
      rw [h]
      exact mem_top _
    have hko : k⁻¹ * ⟨x, hxN⟩ ∈ O := (hπ _).mp (by rw [map_mul, map_inv, hkx, inv_mul_cancel])
    have hφ : φ ⟨x, hxN⟩ = φ (k⁻¹ * ⟨x, hxN⟩) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
    have hodd : Odd (orderOf (φ ⟨x, hxN⟩)) := by
      rw [hφ]
      have h1 : Odd (orderOf (⟨_, hko⟩ : O)) :=
        (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat (orderOf_dvd_natCard _)
      rw [Subgroup.orderOf_mk] at h1
      exact h1.of_dvd_nat (orderOf_map_dvd φ _)
    have h2 : orderOf (φ ⟨x, hxN⟩) ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow, sq, show (⟨x, hxN⟩ : ↥N) * ⟨x, hxN⟩ = 1 from Subtype.ext hx2, map_one]
    have h3 : orderOf (φ ⟨x, hxN⟩) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h4 | h4
      · exact h4
      · rw [h4] at hodd
        exact absurd hodd (by decide)
    exact hφx (orderOf_eq_one_iff.mp h3)

theorem false_of_held_pump_outer
    [Finite X] {M : Subgroup X}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {H : Subgroup X}
    (hHN : H ≤ normalizer (M : Set X)) {c s : X} (hs2 : s * s = 1)
    (hCs : centralizer ({s} : Set X) ≤ H) (hOC : coreNOf (centralizer ({c} : Set X)) ≤ H)
    {Jc N F : Subgroup X} (hJcC : Jc ≤ centralizer ({s} : Set X) ⊓ centralizer ({c} : Set X))
    (eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 7))
    (hNC : N ≤ centralizer ({c} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({c} : Set X))))
    (hJcN : Jc ≤ N ⊔ N.map (MulAut.conj s).toMonoidHom)
    (hfix : N.map (MulAut.conj s).toMonoidHom = N)
    (hJcNpc : IsPComponent 2 (Jc.subgroupOf (N ⊓ centralizer ({s} : Set X))))
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* Blueprint.NativeSporadic.He) (hFJc : F ≤ Jc) (hFM : F ≤ M)
    (hF4 : Nat.card F = 4) (hFsq : ∀ x ∈ F, x * x = 1) (hFH : normalizer (F : Set X) ≤ H)
    {DY : Finset (Fin 7)} (hDY : DY.card = 4)
    (hFY : ∀ x : ↥Jc, (x : X) ∈ F → ∀ y ∉ DY,
      ((eJc (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup (Fin 7)) : Perm (Fin 7)) y = y) :
    False := by
  have hsN : s ∈ normalizer (N : Set X) := mem_normalizer_iff_map_conj_eq.2 hfix
  have hNperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNC hNpc
  have hJcN' : Jc ≤ N := by
    have h1 := hJcN
    rwa [hfix, sup_idem] at h1
  have hJc : Jc ≤ N ⊓ centralizer ({s} : Set X) := le_inf hJcN' (hJcC.trans inf_le_left)
  have hOH : coreNOf N ≤ H := (pPrimeCore_le_of_isPComponent hNC hNpc).trans hOC
  have hNH := le_of_held_pump hs2 hsN hNperf (inf_le_right.trans hCs) hOH hJc hJcNpc eJc hFJc hF4
    hFsq hFH hDY hFY ψ
  obtain ⟨x, hxF, hx1⟩ : ∃ x ∈ F, x ≠ 1 := by
    rcases F.bot_or_exists_ne_one with h | h
    · rw [h, Subgroup.card_bot] at hF4
      exact absurd hF4 (by norm_num)
    · exact h
  have hNc : commutator ↥N = ⊤ := by
    apply map_injective N.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hNperf
  exact false_of_le_normalizer_of_held hρ (hNH.trans hHN) (nonempty_coreQuot_held hNc ψ)
    (hJcN' (hFJc hxF)) (hFM hxF) (hFsq x hxF) hx1

end CFSG.ComponentClassification.SolMax.He9
