module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36K
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36P
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36S

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem card_support_coreImage_of_four [Finite X] {J : Subgroup X} {n : ℕ}
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {x : X} (hxJ : x ∈ J)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) {D : Finset (Fin n)} (hD : D.card = 4)
    (hs : ∀ ω ∉ D, coreImage e hxJ ω = ω) : (coreImage e hxJ).support.card = 4 := by
  classical
  have hsub : (coreImage e hxJ).support ⊆ D := by
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (hs ω hωD)
  refine le_antisymm ((Finset.card_le_card hsub).trans hD.le) ?_
  refine four_le_card_support_of_mem_alternatingGroup (coreImage_mem e hxJ) ?_ ?_
  · have h1 : (⟨x, hxJ⟩ : ↥J) * ⟨x, hxJ⟩ = 1 := Subtype.ext hx2
    have h2 : e ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
        e ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
    exact congrArg Subtype.val h2
  · intro h
    have h1 : e ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := Subtype.ext h
    rw [← map_one e] at h1
    have h2 := e.injective h1
    rw [QuotientGroup.eq_one_iff] at h2
    have hodd : Odd (orderOf x) := by
      have h3 := orderOf_dvd_natCard (⟨⟨x, hxJ⟩, h2⟩ : ↥(pPrimeCore 2 ↥J))
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h3
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h3 pPrimeCore_coprime_card)
    have h4 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
    · exact hx1 (orderOf_eq_one_iff.mp h5)
    · rw [h5] at hodd
      exact absurd hodd (by decide)

theorem card_support_rho_eq_of_sup [Finite X] {J : Subgroup X} {n : ℕ} (hn : 7 ≤ n)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {M : Subgroup X} (hJM : J ≤ M)
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {x : X}
    (hxJ : x ∈ J) :
    (ρ ⟨x, le_normalizer (hJM hxJ)⟩).support.card = (coreImage e hxJ).support.card := by
  classical
  obtain ⟨θJ, hθJ⟩ := exists_coreQuot_of_sup hJM hsup θ
  obtain ⟨ε, hε⟩ := exists_equiv_of_mulEquiv_alt (Fintype.card_fin n) (Fintype.card_fin n) hn
    (e.symm.trans θJ)
  have h1 := hρ.apply_of_mem (by omega) ⟨x, hJM hxJ⟩
  have h2 : θ ((⟨x, hJM hxJ⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
      (e.symm.trans θJ) (e ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) := by
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hθJ]
  have h3 : ρ ⟨x, le_normalizer (hJM hxJ)⟩ =
      (ε : Perm (Fin n)) * coreImage e hxJ * (ε : Perm (Fin n))⁻¹ := by
    rw [h1, h2, hε]
    ext ω
    simp [coreImage, Perm.mul_apply, Perm.inv_def]
  rw [h3, Perm.card_support_conj]

variable {M : Subgroup X} {m : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)}

theorem mem_coreNOf_of_rho_eq_one_of_not_le (hρ : IsPermAction θ ρ) [Finite X]
    {N : Subgroup X} (hNN : N ≤ normalizer (M : Set X)) {r : ℕ} (hr : 5 ≤ r)
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)) (hperf : ⁅N, N⁆ = N)
    (hNK : ¬ N ≤ UnbalancedLayer.coreActionKernel M) :
    ∀ (z : X) (hz : z ∈ N), ρ ⟨z, hNN hz⟩ = 1 → z ∈ coreNOf N := by
  classical
  set U : Subgroup X := N ⊓ ρ.ker.map (normalizer (M : Set X)).subtype with hUdef
  have hmemU : ∀ w : X, w ∈ U ↔ ∃ hw : w ∈ N, ρ ⟨w, hNN hw⟩ = 1 := by
    intro w
    constructor
    · rintro ⟨hwN, ⟨w', hw', rfl⟩⟩
      exact ⟨hwN, hw'⟩
    · rintro ⟨hwN, hw⟩
      exact ⟨hwN, ⟨_, hw, rfl⟩⟩
  have hnorm : N ≤ normalizer (U : Set X) := by
    intro k hk
    refine mem_normalizer_of_map_conj_le' ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hwN, hw1⟩ := (hmemU w).mp hw
    rw [hmemU]
    have hkwN : (MulAut.conj k).toMonoidHom w ∈ N := mul_mem (mul_mem hk hwN) (inv_mem hk)
    refine ⟨hkwN, ?_⟩
    have h1 : (⟨(MulAut.conj k).toMonoidHom w, hNN hkwN⟩ : ↥(normalizer (M : Set X))) =
        ⟨k, hNN hk⟩ * ⟨w, hNN hwN⟩ * (⟨k, hNN hk⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, hw1, mul_one, map_inv, mul_inv_cancel]
  rcases le_core_or_eq_of_normal hr θN hperf inf_le_left hnorm with h | h
  · intro z hz hz1
    exact h ((hmemU z).mpr ⟨hz, hz1⟩)
  · exfalso
    apply hNK
    intro z hz
    obtain ⟨hz', hz1⟩ := (hmemU z).mp (h.ge hz)
    exact hρ.mem_coreActionKernel (hNN hz') hz1

theorem le_coreActionKernel_of_le_centralizer (hρ : IsPermAction θ ρ) [Finite X] (hm : 9 ≤ m)
    {x : X} (hxN : x ∈ normalizer (M : Set X)) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, hxN⟩).support.card = 4) {L : Subgroup X} (hLN : L ≤ normalizer (M : Set X))
    (hLx : L ≤ centralizer ({x} : Set X))
    (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin m)) (hperf : ⁅L, L⁆ = L) :
    L ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  by_contra hLK
  have hk := mem_coreNOf_of_rho_eq_one_of_not_le hρ hLN (by omega) θL hperf hLK
  set A := (L.subgroupOf (normalizer (M : Set X))).map ρ with hAdef
  set K₀ := (fixAlt (ρ ⟨x, hxN⟩)).map (alternatingGroup (Fin m)).subtype with hK₀def
  have hAK₀ : A ≤ K₀ := by
    rintro _ ⟨y, hy, rfl⟩
    have hyo : (y : X) ∈ oddGen L := by rw [oddGen_eq_of_perfect hperf]; exact hy
    exact rho_mem_fixAlt_of_mem_oddGen hxN hx2 hx4.le hLN hLx hyo y.2
  have hτc : (ρ ⟨x, hxN⟩).support.card ≤ m := by
    have := Finset.card_le_univ (ρ ⟨x, hxN⟩).support
    rwa [Fintype.card_fin] at this
  have hK₀card : Nat.card K₀ = (m - 4).factorial / 2 := by
    rw [hK₀def, card_map_of_injective (alternatingGroup (Fin m)).subtype_injective,
      card_fixAlt (by omega), hx4]
  have hAle : Nat.card A ≤ (m - 4).factorial / 2 := hK₀card ▸ Subgroup.card_le_of_le hAK₀
  have hcardL := card_eq_of_alt (by omega) θL
  have hk₁ := card_eq_card_map_mul_card_inf_ker' ρ (L.subgroupOf (normalizer (M : Set X)))
  have hLs : Nat.card (L.subgroupOf (normalizer (M : Set X))) = Nat.card L :=
    Nat.card_congr (subgroupOfEquivOfLe hLN).toEquiv
  have hinf : Nat.card (L.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker : Subgroup _) ≤
      Nat.card (coreNOf L) := by
    have h1 : L.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker ≤
        (coreNOf L).subgroupOf (normalizer (M : Set X)) := by
      rintro z ⟨hz, hzk⟩
      exact hk _ hz hzk
    rw [← Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le _).trans hLN)).toEquiv]
    exact Subgroup.card_le_of_le h1
  have hOpos : 0 < Nat.card (coreNOf L) := Nat.card_pos
  have h1 : (m.factorial / 2) * Nat.card (coreNOf L) ≤
      ((m - 4).factorial / 2) * Nat.card (coreNOf L) := by
    calc (m.factorial / 2) * Nat.card (coreNOf L) = Nat.card L := hcardL.symm
      _ = Nat.card A * Nat.card (L.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker : Subgroup _) := by
          rw [← hLs, hk₁]
      _ ≤ ((m - 4).factorial / 2) * Nat.card (coreNOf L) := Nat.mul_le_mul hAle hinf
  have h2 := Nat.le_of_mul_le_mul_right h1 hOpos
  have h4 : (m - 4).factorial * 2 ≤ m.factorial := by
    have h5 : (m - 3).factorial = (m - 3) * (m - 4).factorial := by
      rw [show m - 3 = (m - 4) + 1 by omega, Nat.factorial_succ]
    have h6 : (m - 3).factorial ≤ m.factorial := Nat.factorial_le (by omega)
    have h9 : 2 ≤ m - 3 := by omega
    calc (m - 4).factorial * 2 ≤ (m - 4).factorial * (m - 3) := Nat.mul_le_mul_left _ h9
      _ = (m - 3).factorial := by rw [h5, mul_comm]
      _ ≤ m.factorial := h6
  have h8 := Nat.factorial_pos (m - 4)
  omega

end CFSG.ComponentClassification.SolMax
