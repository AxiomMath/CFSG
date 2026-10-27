module

public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.GH74.GLS.TwoThin.Equivariance

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.DPrime

open CFSG Subgroup GH74.GLS
open scoped commutatorElement

theorem typ_of_mulEquiv {Typ : ∀ (K : Type) [Group K], Prop} (hCI : CoreInvariant Typ)
    {A B : Type} [Group A] [Group B] (e : A ≃* B) (hA : Typ A) : Typ B :=
  hCI A B ⟨Sol78.coreQuotCongr e⟩ hA

theorem isSLTwoOver_of_coreEquiv {q₀ : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B)
    (h : HarrisLit.IsSLTwoOver q₀ (A ⧸ pPrimeCore 2 A)) :
    HarrisLit.IsSLTwoOver q₀ (B ⧸ pPrimeCore 2 B) := by
  obtain ⟨F, hF, hFt, hq, ⟨f⟩⟩ := h
  exact ⟨F, hF, hFt, hq, ⟨e.symm.trans f⟩⟩

theorem isSLTwoOver_of_mulEquiv {q₀ : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : HarrisLit.IsSLTwoOver q₀ (A ⧸ pPrimeCore 2 A)) :
    HarrisLit.IsSLTwoOver q₀ (B ⧸ pPrimeCore 2 B) :=
  isSLTwoOver_of_coreEquiv (Sol78.coreQuotCongr e) h

theorem nonempty_coreQuotEquiv_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (f : A →* B) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker)) :
    Nonempty (A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : (pPrimeCore 2 B).comap f = pPrimeCore 2 A :=
    (prime_complement_kernel_core_preimage f hf fun h =>
      (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)).1
  let g : A →* B ⧸ pPrimeCore 2 B := (QuotientGroup.mk' _).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker : g.ker = pPrimeCore 2 A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hc]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

theorem nonempty_centerQuotEquiv_of_surjective {P Q : Type*} [Group P] [Group Q]
    (hP : IsQuasisimple P) (hQ : IsQuasisimple Q) (f : P →* Q) (hf : Function.Surjective f) :
    Nonempty (P ⧸ center P ≃* Q ⧸ center Q) := by
  have hPo : Open.IsQuasisimple P := ⟨hP.1.commutator_eq_top, hP.2.1⟩
  have hker : f.ker ≤ center P := by
    refine Quasisimple.normal_le_center_of_ne_top hPo _ fun htop => ?_
    obtain ⟨a, b, hab⟩ := hQ.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (center Q) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (center Q) b
    obtain ⟨x, rfl⟩ := hf a'
    have hx : f x = 1 := (MonoidHom.mem_ker).mp (htop ▸ mem_top x)
    apply hab
    rw [hx]
    simp
  have hcomap := LocalCores.comap_center_eq_of_perfect hP.1 f hf hker
  have hc : center P = ((QuotientGroup.mk' (center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

variable {X : Type} [Group X]

theorem mem_centralizerSection_of_mem_fusionZStar {K : Subgroup X} {k : X}
    (hk : k ∈ (Open.fusionZStar ↥K).map K.subtype) :
    k ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
  obtain ⟨k', hk', rfl⟩ := hk
  rw [SetLike.mem_coe, Sol78.fusionZStar_eq_comap, mem_comap, mem_center_iff] at hk'
  have hkN : (k' : X) ∈ normalizer (K : Set X) := le_normalizer k'.2
  refine ⟨hkN, TwoThin.mem_normalizer_pPrimeCoreOf hkN, fun a ha => ?_⟩
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⁅(⟨a, ha⟩ : ↥K), k'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hk' _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem mem_fusionZStar_of_mem_centralizerSection {K : Subgroup X} {k : X} (hkK : k ∈ K)
    (hk : k ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    k ∈ (Open.fusionZStar ↥K).map K.subtype := by
  refine ⟨⟨k, hkK⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Sol78.fusionZStar_eq_comap, mem_comap, mem_center_iff]
  intro g
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) g
  obtain ⟨o, ho, hoe⟩ := hk.2.2 a ha
  have ho' : ⁅(⟨a, ha⟩ : ↥K), ⟨k, hkK⟩⁆ ∈ pPrimeCore 2 ↥K := by
    have : o = ⁅(⟨a, ha⟩ : ↥K), ⟨k, hkK⟩⁆ := Subtype.ext hoe
    rwa [← this]
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact ho'

theorem mem_fusionZStar_of_commute {M : Subgroup X} {w : X} (hwM : w ∈ M)
    (hw : ∀ m ∈ M, w * m = m * w) : w ∈ (Open.fusionZStar ↥M).map M.subtype := by
  refine ⟨⟨w, hwM⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Sol78.fusionZStar_eq_comap, mem_comap, mem_center_iff]
  intro g
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) g
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hw a ha).symm

end CFSG.ComponentClassification.GS82PumpInputs.DPrime
