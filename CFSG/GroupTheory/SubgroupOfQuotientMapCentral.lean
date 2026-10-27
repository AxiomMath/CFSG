module

public import CFSG.GroupTheory.SubgroupOfQuotientMap
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.SubgroupOfQuotientMapConj
import CFSG.Holt.Induced
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open

variable {G Γ : Type*} [Group G] [Group Γ] {X D : Subgroup G} {ψ : ↥X →* Γ}

theorem map_subgroupOf_lt_map_subgroupOf_iff (hker : ψ.ker = D.subgroupOf X) {K K' : Subgroup G}
    (hKX : K ≤ X) (hK'X : K' ≤ X) (hDK : D ≤ K) (hDK' : D ≤ K') :
    (K.subgroupOf X).map ψ < (K'.subgroupOf X).map ψ ↔ K < K' := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, map_subgroupOf_le_map_subgroupOf_iff hker hKX hDK',
    map_subgroupOf_le_map_subgroupOf_iff hker hK'X hDK]

theorem inf_normalizer_map_subgroupOf [Finite G] (hψ : Function.Surjective ψ)
    (hker : ψ.ker = D.subgroupOf X) (hDX : D ≤ X) {L S : Subgroup G} (hLX : L ≤ X)
    (hDL : D ≤ L) (hSX : S ≤ X) (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.relIndex D) :
    (L.subgroupOf X).map ψ ⊓ normalizer (((S.subgroupOf X).map ψ : Subgroup Γ) : Set Γ) =
      ((L ⊓ normalizer (S : Set G)).subgroupOf X).map ψ := by
  rw [normalizer_map_subgroupOf hψ hker hDX hSX hS hodd]
  have hinf : (X ⊓ normalizer (S : Set G)) ⊓ L = L ⊓ normalizer (S : Set G) := by
    rw [inf_comm (X ⊓ normalizer (S : Set G)) L, ← inf_assoc, inf_eq_left.mpr hLX]
  rw [inf_comm ((L.subgroupOf X).map ψ),
    ← map_subgroupOf_inf hker (X ⊓ normalizer (S : Set G)) hDL, hinf]

private lemma mem_of_map_mem_map_of_isPGroup {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    {P : Subgroup ↥X} (hker : ψ.ker = D.subgroupOf X) (hPX : P ≤ K.subgroupOf X)
    (hP : IsPGroup p P) (hDK : D ≤ centralizer (K : Set G)) (hD : Nat.Coprime (Nat.card D) p)
    {y : ↥X} (hy : ψ y ∈ P.map ψ) {n : ℕ} (hyn : y ^ p ^ n = 1) : y ∈ P := by
  obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
  have hwker : q⁻¹ * y ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqy, inv_mul_cancel]
  have hwD : ((q⁻¹ * y : ↥X) : G) ∈ D := by
    rw [hker] at hwker
    exact Subgroup.mem_subgroupOf.mp hwker
  obtain ⟨m, hm⟩ := hP ⟨q, hq⟩
  have hqm : q ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcomm : Commute q (q⁻¹ * y) :=
    Subtype.ext (mem_centralizer_iff.mp (hDK hwD) (q : G)
      (Subgroup.mem_subgroupOf.mp (hPX hq)))
  have hpow : (q⁻¹ * y) ^ p ^ (m + n) = 1 := by
    have hqN : q ^ p ^ (m + n) = 1 := by rw [pow_add, pow_mul, hqm, one_pow]
    have hyN : y ^ p ^ (m + n) = 1 := by rw [pow_add, mul_comm, pow_mul, hyn, one_pow]
    have h := hcomm.mul_pow (p ^ (m + n))
    rw [show q * (q⁻¹ * y) = y from by group, hyN, hqN, one_mul] at h
    exact h.symm
  have hdvd : orderOf (q⁻¹ * y) ∣ Nat.card D := by
    rw [← Subgroup.orderOf_coe (q⁻¹ * y)]
    exact Subgroup.orderOf_dvd_natCard D hwD
  have hord : orderOf (q⁻¹ * y) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left hdvd (hD.pow_right (m + n)))
      (orderOf_dvd_of_pow_eq_one hpow)
  have hyq : y = q := by
    rw [← mul_inv_cancel_left q y, orderOf_eq_one_iff.mp hord, mul_one]
  rw [hyq]
  exact hq

private lemma map_pCoreOf_le_pCoreOf [Finite G] {p : ℕ} [Fact p.Prime] {K : Subgroup G} :
    ((pCoreOf p K).subgroupOf X).map ψ ≤ pCoreOf p ((K.subgroupOf X).map ψ) := by
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer p ?_ ?_ ?_
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono X (LieType.BorelTits.pCoreOf_le p K))
  · rw [Subgroup.map_le_iff_le_comap]
    intro k hk
    rw [Subgroup.mem_comap, Subgroup.mem_normalizer_iff_map_conj_eq]
    change (((pCoreOf p K).subgroupOf X).map ψ).map (MulAut.conj (ψ k)).toMonoidHom =
      ((pCoreOf p K).subgroupOf X).map ψ
    rw [← map_subgroupOf_map_conj (ψ := ψ) k (pCoreOf p K)]
    have hconj : (pCoreOf p K).map (MulAut.conj (k : G)).toMonoidHom = pCoreOf p K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (LieType.BorelTits.le_normalizer_pCoreOf p K
        (Subgroup.mem_subgroupOf.mp hk))
    rw [hconj]
  · exact ((LieType.BorelTits.pCoreOf_isPGroup p K).comap_subtype (K := X)).map ψ

private lemma pCoreOf_le_map_pCoreOf [Finite G] {p : ℕ} [Fact p.Prime]
    (hψ : Function.Surjective ψ) (hker : ψ.ker = D.subgroupOf X) {K : Subgroup G}
    (hKX : K ≤ X) (hDK : D ≤ centralizer (K : Set G)) (hD : Nat.Coprime (Nat.card D) p) :
    pCoreOf p ((K.subgroupOf X).map ψ) ≤ ((pCoreOf p K).subgroupOf X).map ψ := by
  have hΓ : Finite Γ := Finite.of_surjective ψ hψ
  obtain ⟨P₀, -, hP₀K, hP₀, hP₀map⟩ :=
    CFSG.Holt.exists_isPGroup_map_eq_of_map_le (p := p) ψ
      (LieType.BorelTits.pCoreOf_isPGroup p ((K.subgroupOf X).map ψ))
      (LieType.BorelTits.pCoreOf_le p ((K.subgroupOf X).map ψ))
      IsPGroup.of_bot bot_le (by rw [Subgroup.map_bot]; exact bot_le)
  let P₁ : Subgroup G := P₀.map X.subtype
  have hP₁K : P₁ ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hP₀K hy)
  have hP₁ : IsPGroup p P₁ := hP₀.map X.subtype
  have hnorm : K ≤ Subgroup.normalizer (P₁ : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg x hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    have hgX : g ∈ X := hKX hg
    let g' : ↥X := ⟨g, hgX⟩
    have hg'K : g' ∈ K.subgroupOf X := Subgroup.mem_subgroupOf.mpr hg
    let y : ↥X := g' * x₀ * g'⁻¹
    have hy : ψ y ∈ P₀.map ψ := by
      have hnormK := LieType.BorelTits.le_normalizer_pCoreOf p ((K.subgroupOf X).map ψ)
      have hg'Kbar : ψ g' ∈ (K.subgroupOf X).map ψ := Subgroup.mem_map.mpr ⟨g', hg'K, rfl⟩
      have hx₀Q : ψ x₀ ∈ pCoreOf p ((K.subgroupOf X).map ψ) :=
        hP₀map ▸ Subgroup.mem_map.mpr ⟨x₀, hx₀, rfl⟩
      have hmem := Subgroup.le_normalizer_iff.mp hnormK (ψ g') hg'Kbar (ψ x₀) hx₀Q
      rw [hP₀map]
      change ψ (g' * x₀ * g'⁻¹) ∈ pCoreOf p ((K.subgroupOf X).map ψ)
      simpa only [map_mul, map_inv] using hmem
    obtain ⟨m, hm⟩ := hP₀ ⟨x₀, hx₀⟩
    have hx₀m : x₀ ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hym : y ^ p ^ m = 1 := by
      change (g' * x₀ * g'⁻¹) ^ p ^ m = 1
      rw [conj_pow, hx₀m, mul_one, mul_inv_cancel]
    have hyP₀ : y ∈ P₀ := mem_of_map_mem_map_of_isPGroup hker hP₀K hP₀ hDK hD hy hym
    exact Subgroup.mem_map.mpr ⟨y, hyP₀, rfl⟩
  have hle : P₁ ≤ pCoreOf p K :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer p hP₁K hnorm hP₁
  rw [← hP₀map]
  exact Subgroup.map_mono (Subgroup.map_le_iff_le_comap.mp hle)

theorem pCoreOf_map_subgroupOf_of_le_centralizer [Finite G] {p : ℕ} [Fact p.Prime]
    (hψ : Function.Surjective ψ) (hker : ψ.ker = D.subgroupOf X) (hDX : D ≤ X) {K : Subgroup G}
    (hKX : K ≤ X) (hDK : D ≤ centralizer (K : Set G)) (hD : Nat.Coprime (Nat.card D) p) :
    pCoreOf p ((K.subgroupOf X).map ψ) = ((pCoreOf p K).subgroupOf X).map ψ := by
  have _hDX := hDX
  exact le_antisymm (pCoreOf_le_map_pCoreOf hψ hker hKX hDK hD) map_pCoreOf_le_pCoreOf

end CFSG.GroupTheory
