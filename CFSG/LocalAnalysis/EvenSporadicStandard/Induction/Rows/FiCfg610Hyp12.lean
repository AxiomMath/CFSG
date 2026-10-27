module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCfg610Comp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCfg610D

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def Fi24Cfg610Hyp12 : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ (N L : Subgroup H) (t u : H), CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
      OddCover .Fi24Prime L → Cfg610_2 H N L t u →
        ∀ (K Lu Lut : Subgroup H), Cfg610_2Data H L t u K Lu Lut →
          ∀ u₀ : H, u₀ ∈ K → Fi23Transposition K u₀ →
            ∀ M : Subgroup H, IsCompIn M (centralizer ({u₀} : Set H)) →
              K ⊓ centralizer ({u₀} : Set H) ≤ M → CFSG.conjugate M t = M →
                CFSG.conjugate M u = M → M = K ⊓ centralizer ({u₀} : Set H)

section Certificates


theorem normal_of_fiIn24_layer {H : Type} [Group H] [Finite H] {A K₀ : Subgroup H} {x u₀ : H}
    (hA : OddCover .Fi24Prime A) (hloc : fiLoc (2 * 64561751654400) H A K₀ u₀)
    (hxA : x ∈ centralizer (A : Set H)) (hx2 : orderOf x = 2) (hSol : SolStd A) :
    (K₀.subgroupOf (centralizer ({u₀} : Set H) ⊓ centralizer ({x} : Set H))).Normal := by
  obtain ⟨huA, hbase, -⟩ := fi24in_data hA hloc
  obtain ⟨-, -, hKA, hKu, hKq, -⟩ := id hloc
  have hchar := fi24in_characteristic_of_base hKq huA hKA hKu hbase
  have hCx := hSol.centralizer_le_normalizer hxA hx2
  have hKX : K₀ ≤ A ⊓ centralizer ({u₀} : Set H) := fun k hk =>
    ⟨hKA hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  exact normal_subgroupOf_of_characteristic hxA hCx hKX hchar

theorem fi24Cfg610Comp_of_hyp12 (h : Fi24Cfg610Hyp12) : Fi24Cfg610Comp := by
  intro lit H _ _ ih N L t u hKP hcov hcfg K u₀ hKL hKC hKs hu₀K hT
  obtain ⟨K₁, Lu, Lut, hd⟩ := hcfg.exists_data
  obtain rfl : K = K₁ := hd.unique K hKL hKC hKs
  have hu₀2 : orderOf u₀ = 2 := hT.2.1
  have hloc := fiLoc_of_transposition hKs hKL hT
  have hlocU := fiLoc_of_transposition hKs hd.le_Lu hT
  have hlocUt := fiLoc_of_transposition hKs hd.le_Lut hT
  obtain ⟨-, -, -, -, hKq, -⟩ := id hloc
  have ht2 := hcfg.t_order
  have hu2 := hcfg.u_order
  have htL := hcfg.t_mem
  have hut := hcfg.u_comm_t
  have hu1 : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have ht1 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht2
  have hutt : u * t * (u * t) = 1 := by
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [← hut]
      _ = (u * u) * (t * t) := by group
      _ = 1 := by rw [hu1, ht1]; group
  have hut1 : u * t ≠ 1 := by
    intro h1
    apply hcfg.u_not_mem
    have : u = t⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Subgroup.mem_sup_right (Subgroup.inv_mem _ htL)
  have hut2 : orderOf (u * t) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hutt) hut1
  have htX : t ∈ centralizer ({u₀} : Set H) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL u₀ (hKL hu₀K)).symm
  have huX : u ∈ centralizer ({u₀} : Set H) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (hKC hu₀K)).symm
  have hK₀X : K ⊓ centralizer ({u₀} : Set H) ≤ centralizer ({u₀} : Set H) := inf_le_right
  have hK₀t : K ⊓ centralizer ({u₀} : Set H) ≤ centralizer ({t} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL k (hKL hk.1))
  have hK₀u : K ⊓ centralizer ({u₀} : Set H) ≤ centralizer ({u} : Set H) := fun k hk => hKC hk.1
  have hK₀ut : K ⊓ centralizer ({u₀} : Set H) ≤ centralizer ({u * t} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.2 (by
      have h1 := mem_centralizer_singleton_iff.1 (hK₀u hk)
      have h2 := mem_centralizer_singleton_iff.1 (hK₀t hk)
      calc k * (u * t) = (k * u) * t := by rw [mul_assoc]
        _ = (u * k) * t := by rw [h1]
        _ = u * (k * t) := by rw [mul_assoc]
        _ = u * (t * k) := by rw [h2]
        _ = (u * t) * k := by rw [mul_assoc])
  have hnt := normal_of_fiIn24_layer hcov hloc htL ht2 hcfg.standardL
  have hnu := normal_of_fiIn24_layer hd.Lu_cover hlocU
    (mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hd.Lu_comp.1 hl)) hu2
    hd.Lu_std
  have hnut := normal_of_fiIn24_layer hd.Lut_cover hlocUt
    (mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hd.Lut_comp.1 hl)) hut2
    hd.Lut_std
  have hB : BTheoremAt u₀ := lit.bthm H ih.uHered hKP hcfg.fstar.oddCore_eq_bot u₀ hu₀2
  exact isCompIn_of_alternative_A hKP hcfg.fstar.center_eq_bot hu₀2 hB hKq hK₀X ht2 hu2 hut2 hut
    htX huX hK₀t hK₀u hK₀ut hnt hnu hnut fun M hM hle hMt hMu =>
      h lit H ih N L t u hKP hcov hcfg K Lu Lut hd u₀ hu₀K hT M hM hle hMt hMu

end Certificates

end CFSG.EvenSporadicStandard.Induction
