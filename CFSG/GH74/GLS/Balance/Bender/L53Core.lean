module

public import CFSG.GH74.GLS.Balance.Bender.Aux2
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.GH74.GLS.Balance.BenderExt

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime]

theorem ext_central {Y Z : Type} [Group Y] [Finite Y] [Group Z] (π : Y →* Z)
    (hπ : Function.Surjective π) (hZ : IsPStar p Z) (hY : oResidual p Y = ⊤)
    (hN : IsPGroup p ↥π.ker) (hNc : π.ker ≤ center Y) : IsPStar p Y := by
  have hp : p.Prime := Fact.out
  have : Finite Z := Finite.of_surjective π hπ
  rw [isPStar_iff_T] at hZ ⊢
  refine ⟨hY, fun M hM T hTM hT => ?_⟩
  obtain ⟨hZ1, hZ2⟩ := hZ
  have hMn : (M.map π).Normal := hM.map π hπ
  have h1 := hZ2 (M.map π) hMn (T.map π) (Subgroup.map_mono hTM) (hT.map π)
  have h2 : (M.map π) ⊔ oResOf p (centralizer ((T.map π : Subgroup Z) : Set Z)) = ⊤ :=
    sup_oResOf_eq_top hp hZ1 h1
  have h3 := oResOf_centralizer_map_le hp π hπ hN hNc T
  have h4 : (M ⊔ centralizer (T : Set Y)).map π = ⊤ := by
    rw [eq_top_iff, ← h2, Subgroup.map_sup]
    exact sup_le_sup_left h3 _
  rw [eq_top_iff]
  intro y _
  have hy : π y ∈ (M ⊔ centralizer (T : Set Y)).map π := by rw [h4]; exact mem_top _
  obtain ⟨w, hw, hwy⟩ := hy
  have hk : w⁻¹ * y ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hwy]; group
  have hkc : w⁻¹ * y ∈ centralizer (T : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t _
    exact (Subgroup.mem_center_iff.mp (hNc hk)) t
  have : y = w * (w⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ hw ((le_sup_right : centralizer (T : Set Y) ≤ M ⊔ centralizer (T : Set Y)) hkc)

theorem ext_primeN {Y Z : Type} [Group Y] [Finite Y] [Group Z] (π : Y →* Z)
    (hπ : Function.Surjective π) (hZ : IsPStar p Z) (hY : oResidual p Y = ⊤)
    (hN : ¬ p ∣ Nat.card ↥π.ker) : IsPStar p Y := by
  have hp : p.Prime := Fact.out
  rw [isPStar_iff_T] at hZ ⊢
  refine ⟨hY, fun M hM T hTM hT => ?_⟩
  obtain ⟨hZ1, hZ2⟩ := hZ
  have h1 := hZ2 (M.map π) (hM.map π hπ) (T.map π) (Subgroup.map_mono hTM) (hT.map π)
  have hcent := CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
    p hp π hπ hN T hT
  have h4 : (M ⊔ centralizer (T : Set Y)).map π = ⊤ := by
    rw [Subgroup.map_sup, hcent]; exact h1
  have hNT : π.ker = ⁅π.ker, T⁆ ⊔ (π.ker ⊓ centralizer (T : Set Y)) :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization p hp T π.ker hT hN
      Subgroup.le_normalizer_of_normal
  have hcomm : ⁅π.ker, T⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro n _ t ht
    have h1 : n * t * n⁻¹ ∈ M := hM.conj_mem t (hTM ht) n
    rw [commutatorElement_def]
    exact M.mul_mem h1 (M.inv_mem (hTM ht))
  have h5 : π.ker ≤ M ⊔ centralizer (T : Set Y) := by
    rw [hNT]
    exact sup_le (hcomm.trans le_sup_left) (inf_le_right.trans le_sup_right)
  rw [eq_top_iff]
  intro y _
  have hy : π y ∈ (M ⊔ centralizer (T : Set Y)).map π := by rw [h4]; exact mem_top _
  obtain ⟨w, hw, hwy⟩ := hy
  have hk : w⁻¹ * y ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hwy]; group
  have : y = w * (w⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ hw (h5 hk)


omit [Fact p.Prime] in
theorem isPStar_T_ambient {G : Type} [Group G] {X M T : Subgroup G} (hX : IsPStar p ↥X) (hMX : M ≤ X)
    (hMn : (M.subgroupOf X).Normal) (hTM : T ≤ M) (hT : IsPGroup p ↥T) :
    X ≤ M ⊔ (X ⊓ centralizer (T : Set G)) := by
  rw [isPStar_iff_T] at hX
  have hT' : IsPGroup p ↥(T.subgroupOf X) := hT.comap_of_injective X.subtype X.subtype_injective
  have h := hX.2 (M.subgroupOf X) hMn (T.subgroupOf X) (fun t ht => hTM ht) hT'
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥X) ∈ M.subgroupOf X ⊔ centralizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [h]; exact mem_top _
  obtain ⟨n, hn, c, hc, hnc⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
  have hxe : x = (n : G) * (c : G) := (congrArg Subtype.val hnc).symm
  rw [hxe]
  refine Subgroup.mul_mem_sup hn ⟨c.2, ?_⟩
  show (c : G) ∈ centralizer (T : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have htX : t ∈ X := hMX (hTM ht)
  have := Subgroup.mem_centralizer_iff.mp hc ⟨t, htX⟩ ht
  exact congrArg Subtype.val this

end CFSG.GH74.GLS.Balance.BenderExt
