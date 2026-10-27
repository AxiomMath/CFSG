module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCore
import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup

@[expose] def IsWClosedIn {X : Type*} [Group X] (S A Y : Subgroup X) : Prop :=
  A ≤ S ∧ ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ≤ S →
    A.map (MulAut.conj g).toMonoidHom = A

@[expose] def GammaZeroIn {X : Type*} [Group X] (S Y : Subgroup X) : Prop :=
  S ≤ Y ∧ ∀ R : Subgroup X, R ≤ S → ¬ IsCyclic R → normalizer (R : Set X) ≤ Y

variable {B : Type} [Group B] [Finite B] {K : Subgroup B} [K.Normal]

theorem exists_inner_of_wclosedIn (hZ : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1)
    (hinnT : ∀ (T : Sylow 3 K) (φ : MulAut K), φ ^ 3 = 1 →
      (∀ t ∈ (T : Subgroup K), φ t = t) → ∃ g : K, ∀ x : K, φ x = g * x * g⁻¹)
    (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
    (A : Subgroup (MulAut.conjNormal (H := K)).range) (hA3 : Nat.card A = 3)
    (Y : Subgroup (MulAut.conjNormal (H := K)).range)
    (hSY : (S : Subgroup (MulAut.conjNormal (H := K)).range) ≤ Y)
    (hwc : IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y) :
    ∃ g : K, g ∈ (S : Subgroup (MulAut.conjNormal (H := K)).range).comap (innHom K) ∧
      orderOf g = 3 ∧
      (∀ t ∈ (S : Subgroup (MulAut.conjNormal (H := K)).range).comap (innHom K),
        t * g * t⁻¹ = g) ∧ A = zpowers (innHom K g) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ι := innHom K
  have hι := innHom_injective hZ
  have hN : (ι.range).Normal := by
    constructor
    rintro _ ⟨k, rfl⟩ r
    refine ⟨(r : MulAut K) k, Subtype.ext (MulEquiv.ext fun x => ?_)⟩
    apply Subtype.ext
    obtain ⟨y, rfl⟩ := (r : MulAut K).surjective x
    simp [ι, innHom_apply, MulAut.mul_apply]
  set T₀ := (S : Subgroup (MulAut.conjNormal (H := K)).range).comap ι
  have hmap : T₀.map ι = ι.range ⊓ S := Subgroup.map_comap_eq ι _
  have hcardT₀ : Nat.card T₀ = 3 ^ (Nat.card K).factorization 3 := by
    rw [← Subgroup.card_map_of_injective hι, hmap,
      CFSG.Quasithin.card_inf_normal_of_sylow (S : Subgroup _) ι.range S.card_eq_multiplicity,
      ← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv]
  let T : Sylow 3 K := Sylow.ofCard T₀ hcardT₀
  have hAS : A ≤ S := hwc.1
  obtain ⟨α, hαA, hα1⟩ : ∃ α ∈ A, α ≠ 1 := by
    by_contra! h
    have : A = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx)
    rw [this, Subgroup.card_bot] at hA3
    omega
  have hα3 : orderOf α = 3 := by
    have hdvd : orderOf α ∣ 3 := hA3 ▸ Subgroup.orderOf_dvd_natCard A hαA
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hα1
    · exact h
  have hAz : A = zpowers α := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hαA) ?_
    rw [Nat.card_zpowers, hα3, hA3]
  have hαc : ∀ s ∈ (S : Subgroup (MulAut.conjNormal (H := K)).range), s * α * s⁻¹ = α := by
    intro s hs
    obtain ⟨m, hm⟩ := S.isPGroup' ⟨s, hs⟩
    have hm' : s ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine conj_eq_of_mem_zpowers hα3 hm' ?_
    have hle : A.map (MulAut.conj s).toMonoidHom ≤ S := by
      rintro _ ⟨x, hx, rfl⟩
      show s * x * s⁻¹ ∈ (S : Subgroup (MulAut.conjNormal (H := K)).range)
      exact (S : Subgroup (MulAut.conjNormal (H := K)).range).mul_mem
        ((S : Subgroup (MulAut.conjNormal (H := K)).range).mul_mem hs (hAS hx))
        ((S : Subgroup (MulAut.conjNormal (H := K)).range).inv_mem hs)
    rw [← hAz, ← hwc.2 s (hSY hs) hle]
    exact Subgroup.mem_map_of_mem _ hαA
  have hfix : ∀ t ∈ (T : Subgroup K), (α : MulAut K) t = t := by
    intro t ht
    have hcomm : ι t * α = α * ι t := mul_inv_eq_iff_eq_mul.mp (hαc (ι t) ht)
    have h' : ∀ y : K, (α : MulAut K) t * y * ((α : MulAut K) t)⁻¹ = t * y * t⁻¹ := by
      intro y
      obtain ⟨x, rfl⟩ := (α : MulAut K).surjective y
      have h1 := congrArg (fun β : (MulAut.conjNormal (H := K)).range => (β : MulAut K) x) hcomm
      simp only [Subgroup.coe_mul, MulAut.mul_apply, ι, innHom_apply] at h1
      rw [map_mul, map_mul, map_inv] at h1
      exact h1.symm
    have hc : t⁻¹ * (α : MulAut K) t = 1 := by
      apply hZ
      intro y
      have := h' y
      calc t⁻¹ * (α : MulAut K) t * y
          = t⁻¹ * ((α : MulAut K) t * y * ((α : MulAut K) t)⁻¹) * (α : MulAut K) t := by group
        _ = t⁻¹ * (t * y * t⁻¹) * (α : MulAut K) t := by rw [this]
        _ = y * (t⁻¹ * (α : MulAut K) t) := by group
    rw [← mul_left_cancel_iff (a := t⁻¹), hc, inv_mul_cancel]
  have hα3' : (α : MulAut K) ^ 3 = 1 := by
    have := congrArg (fun t : (MulAut.conjNormal (H := K)).range => (t : MulAut K))
      (pow_orderOf_eq_one α)
    simpa [hα3] using this
  obtain ⟨g, hg⟩ := hinnT T α hα3' hfix
  have hαg : ι g = α := Subtype.ext (MulEquiv.ext fun x => by rw [innHom_apply, hg])
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · show ι g ∈ (S : Subgroup _)
    rw [hαg]
    exact hAS hαA
  · rw [← orderOf_injective ι hι g, hαg, hα3]
  · intro t ht
    apply hι
    rw [map_mul, map_mul, map_inv, hαg]
    exact hαc (ι t) ht
  · rw [hAz, hαg]

theorem false_of_fuse_gamma (hZ : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1)
    (hinnT : ∀ (T : Sylow 3 K) (φ : MulAut K), φ ^ 3 = 1 →
      (∀ t ∈ (T : Subgroup K), φ t = t) → ∃ g : K, ∀ x : K, φ x = g * x * g⁻¹)
    (hfuse : ∀ (T : Sylow 3 K) (a : K), a ∈ (T : Subgroup K) → orderOf a = 3 →
      (∀ t ∈ (T : Subgroup K), t * a * t⁻¹ = a) →
      ∃ (R : Subgroup K) (n : K), R ≤ (T : Subgroup K) ∧ ¬ IsCyclic R ∧
        n ∈ normalizer (R : Set K) ∧ n * a * n⁻¹ ∈ (T : Subgroup K) ∧ n * a * n⁻¹ ∉ zpowers a)
    (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
    (A : Subgroup (MulAut.conjNormal (H := K)).range) (hA3 : Nat.card A = 3)
    (Y : Subgroup (MulAut.conjNormal (H := K)).range)
    (hY : GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y)
    (hwc : IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hι := innHom_injective hZ
  obtain ⟨g, hgT, hg3, hgc, hAg⟩ := exists_inner_of_wclosedIn hZ hinnT S A hA3 Y hY.1 hwc
  set T₀ := (S : Subgroup (MulAut.conjNormal (H := K)).range).comap (innHom K)
  have hcardT₀ : Nat.card T₀ = 3 ^ (Nat.card K).factorization 3 := by
    have hN : ((innHom K).range).Normal := by
      constructor
      rintro _ ⟨k, rfl⟩ r
      refine ⟨(r : MulAut K) k, Subtype.ext (MulEquiv.ext fun x => ?_)⟩
      apply Subtype.ext
      obtain ⟨y, rfl⟩ := (r : MulAut K).surjective x
      simp [innHom_apply, MulAut.mul_apply]
    rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq,
      CFSG.Quasithin.card_inf_normal_of_sylow (S : Subgroup _) (innHom K).range
        S.card_eq_multiplicity, ← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv]
  let T : Sylow 3 K := Sylow.ofCard T₀ hcardT₀
  obtain ⟨R, n, hRT, hRc, hnR, hbT, hba⟩ := hfuse T g hgT hg3 hgc
  set b := n * g * n⁻¹ with hbdef
  set ι := innHom K
  have hnY : ι n ∈ Y := by
    refine hY.2 (R.map ι) ?_ ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact hRT hr
    · intro hcyc
      exact hRc (isCyclic_of_injective ((R.equivMapOfInjective ι hι).toMonoidHom)
        (R.equivMapOfInjective ι hι).injective)
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨r, hr, rfl⟩
        refine ⟨n * r * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnR r).mp hr, ?_⟩
        simp only [map_mul, map_inv]
      · rintro ⟨r, hr, hry⟩
        refine ⟨n⁻¹ * r * n, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp hnR (n⁻¹ * r * n)).mpr
            (by simpa [mul_assoc] using hr)
          exact this
        · rw [map_mul, map_mul, map_inv, hry]
          group
  have hconj : (MulAut.conj (ι n)).toMonoidHom (ι g) = ι b := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, hbdef]
  have hmapA : A.map (MulAut.conj (ι n)).toMonoidHom = zpowers (ι b) := by
    rw [hAg, MonoidHom.map_zpowers, hconj]
  have hle : A.map (MulAut.conj (ι n)).toMonoidHom ≤ S := by
    rw [hmapA, Subgroup.zpowers_le]
    exact hbT
  have heq := hwc.2 (ι n) hnY hle
  have hbα : ι b ∈ zpowers (ι g) := by
    rw [← hAg, ← heq, hmapA]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbα
  apply hba
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, hι ?_⟩
  rw [map_zpow, hk]

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
