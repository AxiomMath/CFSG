module

public import CFSG.GH74.Filter.ElemAbelian
public import CFSG.GH74.Filter.Witness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import CFSG.Monster.B.Final.Simple
public import CFSG.Monster.B.Final.Max2Nodes
public import CFSG.Monster.B.Rep4371.ExactActions
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin CFSG.Monster.B.Pinned MulOpposite

@[expose] def max2Five : Fin 5 → Fin 22 := ![7, 10, 11, 19, 21]

theorem max2Five_injective : Function.Injective max2Five := by decide

theorem gram_max2Five (k l : Fin 5) :
    Max2.decMat CFSG.Monster.B.gramRows (max2Five k) (max2Five l) = 0 := by
  revert k l
  decide

theorem psiBar_prod_ne_one {β : Cbar →* GL (Fin 4370) (ZMod 2)}
    (hβ : IsExplicitBinary β) (a : Fin 5 → Fin 2) (ha : a ≠ 0) :
    (List.ofFn fun k => eE (max2Five k) ^ (a k : ℕ)).reverse.prod ≠ 1 := by
  intro h
  have hind := (linearIndependent_eE hβ).comp max2Five max2Five_injective
  have hψ := congrArg (fun y => Multiplicative.toAdd (psiBar y)) h
  simp only [map_list_prod, List.map_reverse, List.prod_reverse, List.map_ofFn, Function.comp_def, map_pow, List.prod_ofFn,
    toAdd_prod, toAdd_pow, map_one, toAdd_one] at hψ
  simp only [← Nat.cast_smul_eq_nsmul (ZMod 2)] at hψ
  have h0 := Fintype.linearIndependent_iff.1 hind _ hψ
  apply ha
  funext k
  have hk := h0 k
  rw [ZMod.natCast_eq_zero_iff] at hk
  have := (a k).isLt
  exact Fin.ext (by simp only [Pi.zero_apply, Fin.val_zero]; omega)

theorem exists_max2_involutions :
    ∃ x : Fin 5 → NativeSporadic.B, (∀ k, x k * x k = 1) ∧ (∀ k l, x k * x l = x l * x k) ∧
      ∀ a : Fin 5 → Fin 2, a ≠ 0 → (List.ofFn fun k => x k ^ (a k : ℕ)).prod ≠ 1 := by
  obtain ⟨β, hβ⟩ : ∃ β : Cbar →* GL (Fin 4370) (ZMod 2), IsExplicitBinary β :=
    ⟨_, betaS_explicit⟩
  obtain ⟨ι, hιinj, hιβ, -⟩ := iota_facts hβ
  obtain ⟨-, -, -, hle⟩ := pinned_B_max2_full_native_centralizer_and_two_part hβ ι hιβ
  set u := uS gSeq ι
  set e : Fin 5 → Sbp := fun k => eS gSeq (max2Five k) with he
  have hy : ∀ k, ∃ x : NativeSporadic.B, ι x = u * e k * u⁻¹ := by
    intro k
    have hmem : e k ∈ Jbar.op :=
      Subgroup.mem_op.2 (Ebar_le_Jbar (eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar _))
    obtain ⟨x, hx⟩ := hle (Subgroup.mem_map_of_mem _ hmem)
    exact ⟨x, by rw [hx]; rfl⟩
  choose x hx using hy
  have h0 : op (gSeq 0) * op (gSeq 0) = 1 := by rw [← op_mul, gSeq_zero_mul_self, op_one]
  have he2 : ∀ k, e k * e k = 1 := by
    intro k
    simp only [he, eS]
    generalize wordS gSeq (basisWord.take (basisLens.getD (max2Five k) 0)) = P
    calc P⁻¹ * op (gSeq 0) * P * (P⁻¹ * op (gSeq 0) * P) = P⁻¹ * (op (gSeq 0) * op (gSeq 0)) * P := by
          group
      _ = 1 := by rw [h0, mul_one, inv_mul_cancel]
  have hec : ∀ k l, e k * e l = e l * e k := by
    intro k l
    have h := commutator_eS hβ (max2Five k) (max2Five l)
    rw [gram_max2Five k l, ZMod.val_zero, pow_zero] at h
    calc e k * e l = e l * e k * ((e k)⁻¹ * (e l)⁻¹ * e k * e l) := by group
      _ = e l * e k := by rw [h, mul_one]
  have hsq : ∀ k, x k * x k = 1 := by
    intro k
    apply hιinj
    rw [map_mul, hx, map_one]
    calc u * e k * u⁻¹ * (u * e k * u⁻¹) = u * (e k * e k) * u⁻¹ := by group
      _ = 1 := by rw [he2, mul_one, mul_inv_cancel]
  have hcomm : ∀ k l, x k * x l = x l * x k := by
    intro k l
    apply hιinj
    rw [map_mul, map_mul, hx, hx]
    calc u * e k * u⁻¹ * (u * e l * u⁻¹) = u * (e k * e l) * u⁻¹ := by group
      _ = u * (e l * e k) * u⁻¹ := by rw [hec]
      _ = u * e l * u⁻¹ * (u * e k * u⁻¹) := by group
  have hprod : ∀ a : Fin 5 → Fin 2, ι (List.ofFn fun k => x k ^ (a k : ℕ)).prod =
      MulAut.conj u (List.ofFn fun k => e k ^ (a k : ℕ)).prod := by
    intro a
    rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    simp only [Function.comp_apply, map_pow, hx, MulAut.conj_apply]
  have hE : ∀ a : Fin 5 → Fin 2, (List.ofFn fun k => e k ^ (a k : ℕ)).prod =
      op ((((List.ofFn fun k => eE (max2Five k) ^ (a k : ℕ)).reverse.prod : Ebar)) : Cbar) := by
    intro a
    rw [Subgroup.val_list_prod, MulOpposite.op_list_prod]
    simp only [List.map_reverse, List.reverse_reverse, List.map_map, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    simp only [Function.comp_apply, Subgroup.coe_pow, op_pow, he]
    rfl
  have hne : ∀ a : Fin 5 → Fin 2, a ≠ 0 → (List.ofFn fun k => x k ^ (a k : ℕ)).prod ≠ 1 := by
    intro a ha h
    have h1 := congrArg ι h
    rw [hprod, map_one, MulEquiv.map_eq_one_iff, hE, op_eq_one_iff, OneMemClass.coe_eq_one] at h1
    exact psiBar_prod_ne_one hβ a ha h1
  exact ⟨x, hsq, hcomm, hne⟩

theorem exists_E32_of_five_involutions {G : Type*} [Group G] (x : Fin 5 → G)
    (hsq : ∀ k, x k * x k = 1) (hcomm : ∀ k l, x k * x l = x l * x k)
    (hne : ∀ a : Fin 5 → Fin 2, a ≠ 0 → (List.ofFn fun k => x k ^ (a k : ℕ)).prod ≠ 1) :
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 32 := by
  obtain ⟨f, hf⟩ := exists_injective_of_commuting_involutions x
    (fun k => by rw [sq]; exact hsq k) (fun k l => hcomm k l) hne
  have hpow : ∀ a : Fin 5 → Multiplicative (ZMod 2), a ^ 2 = 1 := by
    intro a
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    generalize Multiplicative.toAdd (a i) = z
    revert z
    decide
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.exists_isElemAbelian_of_injective (p := 2)
    (fun a b => mul_comm a b) hpow (card_pi_zmod_two 5) f hf
  exact ⟨E, hE, by rw [hc]; norm_num⟩

theorem exists_E32_B_of_max2 :
    ∃ E : Subgroup NativeSporadic.B, CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 32 := by
  obtain ⟨x, hsq, hcomm, hne⟩ := exists_max2_involutions
  exact exists_E32_of_five_involutions x hsq hcomm hne

theorem not_gen4_B_of_max2 :
    ¬ Gen4 NativeSporadic.B := by
  obtain ⟨E, hE, hc⟩ := exists_E32_B_of_max2
  exact not_gen4_of_elemAbelian E hE (by rw [hc]; norm_num)

end CFSG.GH74.Filter
