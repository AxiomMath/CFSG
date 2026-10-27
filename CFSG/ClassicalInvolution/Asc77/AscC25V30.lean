module

public import CFSG.ClassicalInvolution.Asc77.AscC25V29

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Abstract

open MulAction Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_sylow {C : Subgroup G} (S : Sylow 2 G) (hSC : (S : Subgroup G) ≤ C)
    {n : G} (hnC : n ∈ C) {i : ℕ} (hn : orderOf n = 2 ^ i) :
    ∃ c ∈ C, c * n * c⁻¹ ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let n' : ↥C := ⟨n, hnC⟩
  have hn' : orderOf n' = 2 ^ i := by rw [← hn, ← Subgroup.orderOf_coe]
  have hA : IsPGroup 2 ↥(Subgroup.zpowers n') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hn']
    exact ⟨i, rfl⟩
  obtain ⟨P, hP⟩ := hA.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C P (S.subtype hSC)
  refine ⟨(c : G), c.2, ?_⟩
  have h1 : n' ∈ (P : Subgroup ↥C) := hP (Subgroup.mem_zpowers n')
  have h2 : (c * n' * c⁻¹ : ↥C) ∈ ((c • P : Sylow 2 ↥C) : Subgroup ↥C) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨n', h1, rfl⟩
  rw [hc] at h2
  have h3 : (c * n' * c⁻¹ : ↥C) ∈ (S : Subgroup G).subgroupOf C := by
    simpa using h2
  exact Subgroup.mem_subgroupOf.mp h3

theorem odd_orderOf_delta {C N : Subgroup G} (S : Sylow 2 G) (hSC : (S : Subgroup G) ≤ C)
    {t' : G} (ht2 : t' * t' = 1) (hNC : N ≤ C) (hconj : ∀ n ∈ N, t' * n * t' ∈ N)
    (hnorm : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hcov : ∀ c ∈ C, c ∈ N ∨ c * t' ∈ N)
    {Γ : Type*} [CommGroup Γ] (χ : N →* Γ)
    (hcorr : ∀ (m : G) (hm : m ∈ N), m ∈ (S : Subgroup G) →
      χ ⟨t' * m * t', hconj m hm⟩ = χ ⟨m, hm⟩)
    (n : G) (hn : n ∈ N) :
    Odd (orderOf (χ ⟨n, hn⟩ * (χ ⟨t' * n * t', hconj n hn⟩)⁻¹)) := by
  classical
  let δ : N →* Γ := MonoidHom.mk' (fun n => χ n * (χ ⟨t' * n * t', hconj n n.2⟩)⁻¹) (by
    intro n m
    have e2 : (⟨t' * ((n * m : N) : G) * t', hconj _ (n * m).2⟩ : N) =
        ⟨t' * n * t', hconj n n.2⟩ * ⟨t' * m * t', hconj m m.2⟩ := by
      apply Subtype.ext
      show t' * ((n : G) * m) * t' = (t' * n * t') * (t' * m * t')
      calc t' * ((n : G) * m) * t' = t' * n * (t' * t') * m * t' := by rw [ht2]; group
        _ = (t' * n * t') * (t' * m * t') := by group
    rw [map_mul, e2, map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hδ : ∀ (n : G) (hn : n ∈ N),
      δ ⟨n, hn⟩ = χ ⟨n, hn⟩ * (χ ⟨t' * n * t', hconj n hn⟩)⁻¹ := fun n hn => rfl
  have hδswap : ∀ (n : G) (hn : n ∈ N), δ ⟨t' * n * t', hconj n hn⟩ = (δ ⟨n, hn⟩)⁻¹ := by
    intro n hn
    have e3 : (⟨t' * (t' * n * t') * t', hconj _ (hconj n hn)⟩ : N) = ⟨n, hn⟩ := by
      apply Subtype.ext
      show t' * (t' * n * t') * t' = n
      calc t' * (t' * n * t') * t' = (t' * t') * n * (t' * t') := by group
        _ = n := by rw [ht2]; group
    rw [hδ (t' * n * t') (hconj n hn), e3, hδ n hn, mul_inv, inv_inv, mul_comm]
  have hδconj : ∀ c n : N, δ (c * n * c⁻¹) = δ n := by
    intro c n
    rw [map_mul, map_mul, map_inv, mul_comm (δ c) (δ n), mul_assoc, mul_inv_cancel, mul_one]
  have hA : ∀ (x : N) (i : ℕ), orderOf (x : G) = 2 ^ i → δ x = 1 := by
    intro x i hx
    obtain ⟨c, hcC, hcS⟩ := exists_conj_mem_sylow S hSC (hNC x.2) hx
    have hmN : c * (x : G) * c⁻¹ ∈ N := hnorm c hcC x x.2
    have hδm : δ ⟨c * (x : G) * c⁻¹, hmN⟩ = 1 := by
      rw [hδ _ hmN, hcorr _ hmN hcS, mul_inv_cancel]
    rcases hcov c hcC with hcN | hct
    · have e : (⟨c * (x : G) * c⁻¹, hmN⟩ : N) = ⟨c, hcN⟩ * x * ⟨c, hcN⟩⁻¹ := rfl
      rw [e, hδconj] at hδm
      exact hδm
    · have hc0 : c * t' ∈ N := hct
      have e : (⟨c * (x : G) * c⁻¹, hmN⟩ : N) =
          ⟨c * t', hc0⟩ * ⟨t' * (x : G) * t', hconj x x.2⟩ * ⟨c * t', hc0⟩⁻¹ := by
        apply Subtype.ext
        show c * (x : G) * c⁻¹ = (c * t') * (t' * (x : G) * t') * (c * t')⁻¹
        have hti : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
        rw [mul_inv_rev, hti]
        calc c * (x : G) * c⁻¹ = c * (t' * t') * (x : G) * (t' * t') * c⁻¹ := by rw [ht2]; group
          _ = (c * t') * (t' * (x : G) * t') * (t' * c⁻¹) := by group
      rw [e, hδconj, hδswap x x.2] at hδm
      exact inv_eq_one.mp hδm
  rw [← hδ n hn]
  have hord0 : orderOf n ≠ 0 := (orderOf_pos n).ne'
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd hord0
  have hno : orderOf (n ^ o) = 2 ^ k := by
    have h1 : o ∣ orderOf n := ⟨2 ^ k, by rw [hko, mul_comm]⟩
    rw [orderOf_pow_of_dvd ho.pos.ne' h1, hko, Nat.mul_div_cancel _ ho.pos]
  let nN : N := ⟨n, hn⟩
  have h2 : δ (nN ^ o) = 1 := by
    apply hA (nN ^ o) k
    rw [Subgroup.coe_pow]
    exact hno
  rw [map_pow] at h2
  have h3 : orderOf (δ nN) ∣ o := orderOf_dvd_of_pow_eq_one h2
  exact Odd.of_dvd_nat ho h3

end Abstract

section Defs

variable (p f : ℕ) [Fact p.Prime]


@[expose] def GCS25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ∀ t' : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → (∃ g : G, g * z * g⁻¹ = t') →
          (¬ ∃ y : G, y * z * y⁻¹ = t' * z) → a * t' = t' * a →
          ∀ (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
            (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (n : G),
            n ∈ (S : Subgroup G) → ∀ (hn : n ∈ Subgroup.normalizer (K : Set G))
            (hn' : t' * n * t' ∈ Subgroup.normalizer (K : Set G)),
              fieldChar hp hq e ⟨t' * n * t', hn'⟩ = fieldChar hp hq e ⟨n, hn⟩

end Defs

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem gc25_of_gcs25 (hgcs : GCS25 p f) : GC25 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat hp hq e n hn
    hnz hn'
  classical
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have ht'z : t' * z = z * t' := t'_comm_z h
  have ht'C : t' ∈ C := (hmemC t').mpr ht'z
  have hSC : (S : Subgroup G) ≤ C := fun s hs => (hmemC s).mpr (hyp.hzS s hs)
  set N : Subgroup G := C ⊓ Subgroup.normalizer (K : Set G) with hN
  have hconjN : ∀ m ∈ N, t' * m * t' ∈ N := by
    intro m hm
    have hmz : m * z = z * m := (hmemC m).mp hm.1
    have hmK : conjSub m K = K := mem_normalizer_iff_conjSub_eq.mp hm.2
    have hmK' : conjSub m K' = K' := (cz_fix_iff h hmz).mp hmK
    have hK2 : conjSub (t' * m * t') K = K := by
      rw [conjSub_mul, conjSub_mul, conjSub_t'_K h, hmK', conjSub_t'_K' h]
    exact ⟨C.mul_mem (C.mul_mem ht'C hm.1) ht'C, mem_normalizer_iff_conjSub_eq.mpr hK2⟩
  have hnormN : ∀ c ∈ C, ∀ m ∈ N, c * m * c⁻¹ ∈ N := by
    intro c hc m hm
    have hcz : c * z = z * c := (hmemC c).mp hc
    have hmz : m * z = z * m := (hmemC m).mp hm.1
    have hmK : conjSub m K = K := mem_normalizer_iff_conjSub_eq.mp hm.2
    have hcmK : conjSub (c * m * c⁻¹) K = K :=
      (twinCtx_of_hyp25 h).conj_normalizer hcz hmz hmK
    exact ⟨C.mul_mem (C.mul_mem hc hm.1) (C.inv_mem hc), mem_normalizer_iff_conjSub_eq.mpr hcmK⟩
  have hcov : ∀ c ∈ C, c ∈ N ∨ c * t' ∈ N := by
    intro c hc
    have hcz : c * z = z * c := (hmemC c).mp hc
    rcases cz_cover h hcz with h1 | h1
    · exact Or.inl ⟨hc, mem_normalizer_iff_conjSub_eq.mpr h1⟩
    · exact Or.inr ⟨C.mul_mem hc ht'C, mem_normalizer_iff_conjSub_eq.mpr h1⟩
  let χ : N →* (GaloisField p f ≃+* GaloisField p f) :=
    (fieldChar hp hq e).comp (Subgroup.inclusion inf_le_right)
  have hnN : n ∈ N := ⟨(hmemC n).mpr hnz, hn⟩
  exact odd_orderOf_delta S hSC h.ht'2 inf_le_left hconjN hnormN hcov χ
    (fun m hm hmS => hgcs G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat
      hp hq e m hmS hm.2 (hconjN m hm).2) n hnN

theorem c25_16inv_of_gcs (h11 : C25_11 p f) (hmix : Mix25 p f) (hgcs : GCS25 p f) :
    T7U.C25_16inv p f :=
  c25_16inv_of_gc h11 hmix (gc25_of_gcs25 hgcs)

theorem c25_16invEven_of_gcs (h11 : C25_11 p f) (hmix : Mix25 p f) (hgcs : GCS25 p f) :
    Even f → T7U.C25_16inv p f :=
  fun _ => c25_16inv_of_gcs h11 hmix hgcs

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
