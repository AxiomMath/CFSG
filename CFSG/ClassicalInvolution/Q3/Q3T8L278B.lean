module

public import CFSG.ClassicalInvolution.Q3.Q3T8Defs
public import CFSG.ClassicalInvolution.Q3.Q3T8L274A
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Layer

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T7
  CFSG.ClassicalInvolution.Q3.Disc3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8
open scoped commutatorElement

section Twins

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}


theorem isSylow2In_exactCore3_of_le_cenZ {K P : Subgroup G} (hP : IsSylow2In P K)
    (hPx : P ≤ cenZ x) : IsSylow2In P (exactCore3 x K) :=
  isSylow2In_of_le_of_le hP (le_inf hP.1 ((cenZ_eq_centralizer x) ▸ hPx)) inf_le_left

theorem noTwins_layerFam3 (L : LayerHyp Ω x)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) :
    ∀ M ∈ layerFam3 Ω x, ∀ M' ∈ twinSet (layerFam3 Ω x) M, M' = M := by
  have hodd := odd_natCard_oddCore_exactLayer3 (Ω := Ω) (x := x)
  have hmem : ∀ M ∈ layerFam3 Ω x, ∃ K ∈ tqMembers3 Ω x, layerImg3 Ω x K = M := by
    rintro M ⟨_, ⟨L₀, ⟨⟨K, hK, rfl⟩, -⟩, hLY, rfl⟩, hb⟩
    exact ⟨K, hK, hb⟩
  rintro M hM M' ⟨hM', w, hwM, hwM'⟩
  obtain ⟨K, hK, rfl⟩ := hmem M hM
  obtain ⟨J, hJ, rfl⟩ := hmem M' hM'
  obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution L.gen hK.1
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution L.gen hJ.1
  have hzKL := isUniqueInvolution_exactCore3 hK.2.1 hzK
  have hzJL := isUniqueInvolution_exactCore3 hJ.2.1 hzJ
  have hzKY := isUniqueInvolution_subgroupOf hzKL (exactCore3_le_exactLayer3 hK)
  have hzJY := isUniqueInvolution_subgroupOf hzJL (exactCore3_le_exactLayer3 hJ)
  have hzKb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _) hzKY
  have hzJb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _) hzJY
  have hmk := (hwM.eq hzKb).symm.trans (hwM'.eq hzJb)
  obtain ⟨n, hn, hnz⟩ := exists_conj_eq_of_map_eq hodd hzKY.sq hzJY.sq hmk
  have hnO : (n : G) ∈ oddCoreOf (exactLayer3 Ω x) := ⟨n, hn, rfl⟩
  have hnzG : (n : G) * zJ * (n : G)⁻¹ = zK := congrArg Subtype.val hnz
  have hJn : conjSub (n : G) J ∈ Ω := L.gen.conjInvariant (n : G) J hJ.1
  have hzJn : IsUniqueInvolution (conjSub (n : G) J) zK := by
    have := hzJ.conj (n : G)
    rwa [hnzG] at this
  have heq : conjSub (n : G) J = K := hnt K hK.1 _ ⟨hJn, zK, hzK, hzJn⟩
  exact (layerImg3_conj_of_mem_oddCore hnO).symm.trans (by rw [heq])

theorem layerImg3_ne_of_involutions (L : LayerHyp Ω x) {K J : Subgroup G}
    (hK : XMem Ω x K) (hJ : XMem Ω x J) {zK zJ : G}
    (hzK : IsUniqueInvolution K zK) (hzJ : IsUniqueInvolution J zJ) (hcomm : zK * zJ = zJ * zK)
    (hne : zK ≠ zJ) : layerImg3 Ω x K ≠ layerImg3 Ω x J := by
  intro h
  have hKt : K ∈ tqMembers3 Ω x := hK.mem_tqMembers3 L.gen L.sq
  have hJt : J ∈ tqMembers3 Ω x := hJ.mem_tqMembers3 L.gen L.sq
  obtain ⟨n, hn, hnK⟩ := exists_oddCore_conj_of_layerImg3_eq L hKt hJt h
  have hzn : IsUniqueInvolution J (n * zK * n⁻¹) := hnK ▸ hzK.conj n
  have hzJn : zJ = n * zK * n⁻¹ := hzJ.eq hzn
  obtain ⟨R₀, hR₀, hR₀x⟩ := hK.2.2
  have hR₀L : IsSylow2In R₀ (exactCore3 x K) :=
    isSylow2In_exactCore3_of_le_cenZ hR₀ (fun r hr => mem_cenZ_iff.mpr (hR₀x r hr))
  have h8 := Sec6Gen.eight_le_of_mem_RSet L.gen (mem_RSet_of_isSylow2In hK.1 hR₀)
  have hzR₀ : zK ∈ R₀ := T3.mem_of_isPGroup hzK hR₀.1 hR₀.2.1 (by omega)
  have hzY : zK ∈ exactLayer3 Ω x := exactCore3_le_exactLayer3 hKt (hR₀L.1 hzR₀)
  have hnorm := mem_normalizer_oddCoreOf hzY
  have hzi : zK⁻¹ = zK := inv_eq_of_mul_eq_one_right hzK.sq
  have hprod : zK * zJ ∈ oddCoreOf (exactLayer3 Ω x) := by
    have h1 : zK * n * zK⁻¹ ∈ oddCoreOf (exactLayer3 Ω x) :=
      (Subgroup.mem_normalizer_iff.mp hnorm n).mp hn
    have h2 := (oddCoreOf (exactLayer3 Ω x)).mul_mem h1
      ((oddCoreOf (exactLayer3 Ω x)).inv_mem hn)
    have e : zK * zJ = zK * n * zK⁻¹ * n⁻¹ := by rw [hzJn, hzi]; group
    rw [e]
    exact h2
  have hsq : (zK * zJ) * (zK * zJ) = 1 := by
    calc zK * zJ * (zK * zJ) = zK * (zJ * zK) * zJ := by group
      _ = zK * (zK * zJ) * zJ := by rw [hcomm]
      _ = (zK * zK) * (zJ * zJ) := by group
      _ = 1 := by rw [hzK.sq, hzJ.sq, one_mul]
  have h1 : zK * zJ ≠ 1 := mul_ne_one_of_ne hzK.sq hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (zK * zJ) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) h1
  have hodd := odd_natCard_oddCoreOf (exactLayer3 Ω x)
  have hdvd : orderOf (⟨zK * zJ, hprod⟩ : oddCoreOf (exactLayer3 Ω x)) ∣
      Nat.card (oddCoreOf (exactLayer3 Ω x)) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end Twins

end CFSG.ClassicalInvolution.Q3.Q3T8.Layer
