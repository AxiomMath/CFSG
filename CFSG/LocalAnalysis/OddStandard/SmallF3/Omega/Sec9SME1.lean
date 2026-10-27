module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B E1 : Subgroup G}

theorem sec9m_card_E16 : Nat.card E16 = 16 := by
  rw [E16, Nat.card_pi]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  simp [h2]

theorem sec9m_E1_card (hctx : Sec9E1 G t L S z g B t₀ E1) :
    Nat.card E1 = 16 * Nat.card (Asub9 t t₀ B) := by
  obtain ⟨φ, hsurj, hker⟩ := hctx.quot
  have hcard := Subgroup.card_ker_mul_card_of_surjective (f := φ) hsurj
  have hker_card : Nat.card φ.ker = Nat.card (Asub9 t t₀ B) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hctx.A_le).toEquiv
  rw [← hcard, hker_card, sec9m_card_E16]
  exact Nat.mul_comm _ _

theorem sec9m_E1_pgroup (hctx : Sec9E1 G t L S z g B t₀ E1) : IsPGroup 2 ↥E1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : CFSG.Open.IsElemAbelian 2 (Asub9 t t₀ B) :=
    sec9n_A_elem hctx.choice.toSec9Ctx
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hA).exists_card_eq
  refine IsPGroup.of_card (p := 2) (n := n + 4) ?_
  rw [sec9m_E1_card hctx, hn, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
  congr 1
  omega

theorem sec9m_E1_comm_mem_A (hctx : Sec9E1 G t L S z g B t₀ E1) {e e' : G} (he : e ∈ E1)
    (he' : e' ∈ E1) : e * e' * e⁻¹ * e'⁻¹ ∈ Asub9 t t₀ B := by
  obtain ⟨φ, hsurj, hker⟩ := hctx.quot
  have hmemE1 : e * e' * e⁻¹ * e'⁻¹ ∈ E1 :=
    E1.mul_mem (E1.mul_mem (E1.mul_mem he he') (E1.inv_mem he)) (E1.inv_mem he')
  have hker_mem : (⟨e * e' * e⁻¹ * e'⁻¹, hmemE1⟩ : ↥E1) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have hdecomp : (⟨e * e' * e⁻¹ * e'⁻¹, hmemE1⟩ : ↥E1)
        = ⟨e, he⟩ * ⟨e', he'⟩ * ⟨e, he⟩⁻¹ * ⟨e', he'⟩⁻¹ := rfl
    rw [hdecomp, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [← commutatorElement_def]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [hker] at hker_mem
  exact Subgroup.mem_subgroupOf.mp hker_mem

theorem sec9m_E1_not_le_A (hctx : Sec9E1 G t L S z g B t₀ E1) : ¬ E1 ≤ Asub9 t t₀ B := by
  obtain ⟨φ, hsurj, hker⟩ := hctx.quot
  intro hle
  have hsub : (Asub9 t t₀ B).subgroupOf E1 = ⊤ := by
    rw [eq_top_iff]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hle x.2)
  have htop : φ.ker = ⊤ := by rw [hker, hsub]
  have hsingle : Subsingleton E16 := ⟨fun a b => by
    obtain ⟨x, hx⟩ := hsurj a
    obtain ⟨y, hy⟩ := hsurj b
    have hx1 : φ x = 1 := by
      have : x ∈ φ.ker := by rw [htop]; exact Subgroup.mem_top x
      simpa [MonoidHom.mem_ker] using this
    have hy1 : φ y = 1 := by
      have : y ∈ φ.ker := by rw [htop]; exact Subgroup.mem_top y
      simpa [MonoidHom.mem_ker] using this
    rw [← hx, ← hy, hx1, hy1]⟩
  exact (not_subsingleton_iff_nontrivial.mpr inferInstance) hsingle

theorem sec9m_E1_inf_O (hctx : Sec9E1 G t L S z g B t₀ E1) :
    ∀ x ∈ E1, x ∈ oddCoreIn (centMod (Asub9 t t₀ B) B) → x = 1 := by
  intro x hx hxO
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (sec9m_E1_pgroup hctx).exists_orderOf_eq_pow (⟨x, hx⟩ : ↥E1)
  have hx2 : orderOf x = 2 ^ k := (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥E1)).trans hk
  have hodd : Odd (orderOf x) := odd_orderOf_of_mem_oddCoreIn hxO
  rw [hx2] at hodd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hodd) (Even.pow_of_ne_zero even_two hk0)
  rw [hk0, pow_zero] at hx2
  exact orderOf_eq_one_iff.mp hx2

theorem sec9m_O_cent_A
    (hv : centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) =
      oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B) :
    ∀ o ∈ oddCoreIn (centMod (Asub9 t t₀ B) B), ∀ a ∈ Asub9 t t₀ B, o * a = a * o := by
  intro o ho a ha
  have ho' : o ∈ centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) := by
    rw [hv]
    exact Subgroup.mem_sup_left ho
  exact (Subgroup.mem_centralizer_iff.mp ho'.2 a ha).symm

theorem sec9m_E1_cent_A (hctx : Sec9E1 G t L S z g B t₀ E1)
    (hv : centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) =
      oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B) :
    ∀ e ∈ E1, e ∈ centralizer (Asub9 t t₀ B : Set G) → e ∈ Asub9 t t₀ B := by
  intro e he hcent
  have hmemN : e ∈ centMod (Asub9 t t₀ B) B := hctx.le_N he
  have hsup : e ∈ oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B := by
    rw [← hv]
    exact ⟨hmemN, hcent⟩
  obtain ⟨o, ho, a, ha, heoa⟩ :=
    exists_mul_of_mem_sup_of_commute (sec9m_O_cent_A hv) hsup
  have hoE1 : o ∈ E1 := by
    have ho_eq : o = e * a⁻¹ := by rw [heoa]; group
    rw [ho_eq]
    exact E1.mul_mem he (hctx.A_le ((Asub9 t t₀ B).inv_mem ha))
  have ho1 : o = 1 := sec9m_E1_inf_O hctx o hoE1 ho
  rw [heoa, ho1, one_mul]
  exact ha

end CFSG.OddStandard.SmallF3.Omega
