module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115dC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Sec11dPsi {K1 K2 T R : Subgroup G} (hTR : T ≤ R)
    (ρ : ↥R →* MulAut ↥(K1 ⊔ K2)) : Subgroup (MulAut ↥(K1 ⊔ K2)) :=
  (ρ.comp (Subgroup.inclusion hTR)).range

section Psi

variable {K1 K2 T R D : Subgroup G} {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)}

theorem sec11dPsi_mem (hTR : T ≤ R) {y : ↥R} (hy : (y : G) ∈ T) :
    ρ y ∈ Sec11dPsi hTR ρ :=
  ⟨⟨(y : G), hy⟩, rfl⟩

theorem sec11dPsi_le (hTR : T ≤ R) : Sec11dPsi hTR ρ ≤ ρ.range := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, rfl⟩

theorem sec11dPhi_pgroup (hR : IsPGroup 2 ↥R) : IsPGroup 2 ↥ρ.range :=
  hR.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective

theorem sec11dPsi_mem_of_mem_sup (hTR : T ≤ R) (hDR : D ≤ R)
    (hTN : ∀ a ∈ T, ∀ n ∈ D, a * n * a⁻¹ ∈ D) (hker : ∀ y : ↥R, (y : G) ∈ D → ρ y = 1)
    {y : ↥R} (hy : (y : G) ∈ T ⊔ D) : ρ y ∈ Sec11dPsi hTR ρ := by
  obtain ⟨s, hs, d, hd, hsd⟩ := sec11d_mem_sup hTN _ hy
  have e : y = ⟨s, hTR hs⟩ * ⟨d, hDR hd⟩ := Subtype.ext hsd
  rw [e, map_mul, hker ⟨d, hDR hd⟩ hd, mul_one]
  exact sec11dPsi_mem hTR (y := ⟨s, hTR hs⟩) hs

theorem sec11dPsi_relIndex (hTR : T ≤ R) (hDR : D ≤ R)
    (hTN : ∀ a ∈ T, ∀ n ∈ D, a * n * a⁻¹ ∈ D) (hker : ∀ y : ↥R, (y : G) ∈ D → ρ y = 1)
    (hker' : ∀ y : ↥R, ρ y = 1 → (y : G) ∈ D) {x0 : G} (hx0R : x0 ∈ R) (hx0 : x0 ∉ T ⊔ D)
    (hone : ∀ k ∈ R, k ∉ T ⊔ D → x0⁻¹ * k ∈ T ⊔ D) :
    (Sec11dPsi hTR ρ).relIndex ρ.range = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
  have hx0i : x0⁻¹ ∈ R := R.inv_mem hx0R
  refine ⟨ρ ⟨x0⁻¹, hx0i⟩, ⟨_, rfl⟩, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    have hs' : ρ (Subgroup.inclusion hTR s) = ρ ⟨x0⁻¹, hx0i⟩ := hs
    have h1 : ρ ((⟨x0⁻¹, hx0i⟩ : ↥R)⁻¹ * Subgroup.inclusion hTR s) = 1 := by
      rw [map_mul, map_inv, hs', inv_mul_cancel]
    have hD : x0 * (s : G) ∈ D := by simpa using hker' _ h1
    apply hx0
    have e : x0 = (x0 * (s : G)) * (s : G)⁻¹ := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup hD (T.inv_mem s.2)
  · rintro _ ⟨y, rfl⟩
    by_cases hy : (y : G) ∈ T ⊔ D
    · exact Or.inr (sec11dPsi_mem_of_mem_sup hTR hDR hTN hker hy)
    · left
      have := sec11dPsi_mem_of_mem_sup hTR hDR hTN hker (hone y y.2 hy)
        (y := ⟨x0⁻¹, hx0i⟩ * y)
      rwa [map_mul] at this

theorem sec11dPsi_card [Finite G] {C : Subgroup G} (hTR : T ≤ R) (hT512 : 512 ≤ Nat.card ↥T)
    (hC : Nat.card ↥C ≤ 8)
    (hkerC : ∀ s : ↥T, ρ ⟨(s : G), hTR s.2⟩ = 1 → (s : G) ∈ C) :
    64 ≤ Nat.card ↥(Sec11dPsi hTR ρ) := by
  classical
  let fT : ↥T →* MulAut ↥(K1 ⊔ K2) := ρ.comp (Subgroup.inclusion hTR)
  have hker : Nat.card ↥fT.ker ≤ 8 := by
    have hinj : Function.Injective (fun u : ↥fT.ker =>
        (⟨((u : ↥T) : G), hkerC (u : ↥T) u.2⟩ : ↥C)) := by
      intro u v huv
      have h' := congrArg Subtype.val huv
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.card_le_card_of_injective _ hinj).trans hC
  have h1 := Subgroup.card_ker_mul_card_range fT
  have hPsi : Nat.card ↥(Sec11dPsi hTR ρ) = Nat.card ↥fT.range := rfl
  by_contra hlt
  have hlt' : Nat.card ↥fT.range ≤ 63 := by omega
  have := Nat.mul_le_mul hker hlt'
  omega

end Psi

namespace Sec11dRho

variable {t z : G} {K1 K2 T R : Subgroup G} {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)}

theorem conj_mem_psi [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hS : Sec11cSplit t z K1 K2)
    (hTR : T ≤ R) (hQT : secQ K1 K2 ≤ T) :
    ∀ q : ↥(K1 ⊔ K2), (q : G) ∈ twoCoreIn (K1 ⊔ K2) → MulAut.conj q ∈ Sec11dPsi hTR ρ := by
  intro q hq
  have hqT : (q : G) ∈ T := hQT hq
  have hρq := hρ.conj_of_mem hS (y := ⟨(q : G), hTR hqT⟩) q.2
  have e : (⟨(q : G), q.2⟩ : ↥(K1 ⊔ K2)) = q := Subtype.ext rfl
  rw [e] at hρq
  rw [← hρq]
  exact sec11dPsi_mem hTR (y := ⟨(q : G), hTR hqT⟩) hqT

theorem swap_mem_psi [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hS : Sec11cSplit t z K1 K2)
    (hTR : T ≤ R) {s : G} (hsT : s ∈ T)
    (hsN : ∀ n ∈ oddCoreIn (secK0 t z), s * n * s⁻¹ ∈ oddCoreIn (secK0 t z))
    (hsw : ∀ k ∈ K1, s * k * s⁻¹ ∈ K2) :
    ∃ σ ∈ Sec11dPsi hTR ρ, ∀ k : ↥(K1 ⊔ K2), (k : G) ∈ K1 → ((σ k : ↥(K1 ⊔ K2)) : G) ∈ K2 := by
  refine ⟨ρ ⟨s, hTR hsT⟩, sec11dPsi_mem hTR (y := ⟨s, hTR hsT⟩) hsT, fun k hk => ?_⟩
  have hk2 : s * (k : G) * s⁻¹ ∈ K2 := hsw (k : G) hk
  have h := hρ.apply_conj hS (y := ⟨s, hTR hsT⟩) hsN (κ := k) (Subgroup.mem_sup_right hk2)
  rw [h]
  exact hk2

end Sec11dRho

theorem sec11d_card_T [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec10Z G t L S z) {T : Subgroup G} (hT : IsSylow2Of T (secM t S L))
    (h6 : Nonempty (↥(secMstar t S L) ≃* Equiv.Perm (Fin 6))) : 512 ≤ Nat.card ↥T := by
  obtain ⟨-, -, hA5⟩ := sec126_isElemAb2_secA hp hctx
  have hstar : Nat.card ↥(secMstar t S L) = 720 := by
    obtain ⟨e⟩ := h6
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have hrange : secMstar t S L = (secA t S L).normalizerMonoidHom.range := by
    unfold secMstar autIn secM
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  have hker : 32 ∣ Nat.card ↥(secA t S L).normalizerMonoidHom.ker := by
    have hAN : secA t S L ≤ normalizer ((secA t S L : Subgroup G) : Set G) :=
      Subgroup.le_normalizer
    have hle : (secA t S L).subgroupOf (normalizer ((secA t S L : Subgroup G) : Set G)) ≤
        (secA t S L).normalizerMonoidHom.ker := by
      intro x hx
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro a ha
      exact sec10A2_elem_comm hA5.1 ha (Subgroup.mem_subgroupOf.mp hx)
    have h1 : Nat.card ↥((secA t S L).subgroupOf
        (normalizer ((secA t S L : Subgroup G) : Set G))) = 32 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA5.2]
      norm_num
    have h2 := Subgroup.card_dvd_of_le hle
    rwa [h1] at h2
  have hMcard : Nat.card ↥(secM t S L) =
      Nat.card ↥(secA t S L).normalizerMonoidHom.ker * 720 := by
    have h := Subgroup.card_ker_mul_card_range (secA t S L).normalizerMonoidHom
    rw [← hrange, hstar] at h
    exact h.symm
  have h512M : 512 ∣ Nat.card ↥(secM t S L) := by
    rw [hMcard]
    have := mul_dvd_mul hker (show 16 ∣ 720 by norm_num)
    simpa using this
  have h1 := Subgroup.relIndex_mul_card (H := T) (K := secM t S L)
  rw [inf_of_le_left hT.1] at h1
  have hcop : Nat.Coprime 512 (T.relIndex (secM t S L)) := by
    have h2 : Nat.Coprime 2 (T.relIndex (secM t S L)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hT.2.2
    simpa using Nat.Coprime.pow_left 9 h2
  have hdvd : 512 ∣ Nat.card ↥T := by
    have h3 : 512 ∣ T.relIndex (secM t S L) * Nat.card ↥T := by
      rw [h1]
      exact h512M
    exact hcop.dvd_of_dvd_mul_left h3
  exact Nat.le_of_dvd Nat.card_pos hdvd

end CFSG.OddStandard.SmallF3.Omega
