module

public import CFSG.GH74.GLS.Stage1.Thm4.P92Rank
public import CFSG.GH74.GLS.Stage1.Thm4.P92Pump

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.P92

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {n : ℕ}

structure ExtData (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z : G) (J T : Subgroup G) :
    Prop where
  rigid : IsRigidOfType Lh z J
  mem : z ∈ J
  sylow : IsSylowOf 2 T ⊤
  zT : z ∈ T
  central : ∀ t ∈ T, t * z = z * t

theorem exists_ext (E : Env G Lh n) (h0 : ∃ (x : G) (K : Subgroup G), IsRigidOfType Lh x K) :
    ∃ (z : G) (J T : Subgroup G), ExtData G Lh z J T := by
  classical
  let X : Set G := {x | ∃ K, IsRigidOfType Lh x K}
  let v : G → ℕ := fun x => (Nat.card ↥(centralizer ({x} : Set G))).factorization 2
  obtain ⟨x₀, K₀, hK₀⟩ := h0
  obtain ⟨x, ⟨K, hK⟩, hmax⟩ := Set.exists_max_image X v (Set.toFinite X) ⟨x₀, K₀, hK₀⟩
  have hxo : orderOf x = 2 := rig_ord hK
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo, sq] at this
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hxo; omega
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨T, hT, hxT⟩ := exists_sylow_mem hxC hxx
  obtain ⟨S, hS, hTS⟩ := exists_sylow_ge (C := ⊤) hT.isPGroup le_top
  have hSne : S ≠ ⊥ := fun h => hx1 (by
    have := hTS hxT
    rw [h, Subgroup.mem_bot] at this
    exact this)
  obtain ⟨x', hx'S, hx'o, hx'c⟩ := exists_involution_normal_center (T := S) (N := S) hS.isPGroup
    le_rfl (fun t ht n hn => S.mul_mem (S.mul_mem ht hn) (S.inv_mem ht)) hSne
  have hx'x' : x' * x' = 1 := by
    have := pow_orderOf_eq_one x'
    rwa [hx'o, sq] at this
  have hx'C : x' ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hx'c x (hTS hxT)).symm
  have hP : IsSylowOf 2 (T ⊓ K) K := sylow_inf hK hT
  have hyP : ∀ p ∈ T ⊓ K, x' * p = p * x' := fun p hp => (hx'c p (hTS hp.1)).symm
  obtain ⟨e⟩ := hK.2
  obtain ⟨-, hz⟩ := a4n E.rank4 E.n8 E.n11 E.hL e hP hx'x' hyP
  obtain ⟨J, hJ, hx'J⟩ := exists_rigid_pumpUp E hK hx'C hx'o hz
  have hv : v x' ≤ v x := hmax x' ⟨J, hJ⟩
  have hSC' : S ≤ centralizer ({x'} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hx'c s hs)
  obtain ⟨T', hT', hST'⟩ := exists_sylow_ge hS.isPGroup hSC'
  have hcardT' : Nat.card T' = 2 ^ v x' := hT'.card_eq
  have hcardT : Nat.card T = 2 ^ v x := hT.card_eq
  have hTA : Nat.card S ≤ Nat.card T :=
    calc Nat.card S ≤ Nat.card T' := Subgroup.card_le_of_le hST'
      _ = 2 ^ v x' := hcardT'
      _ ≤ 2 ^ v x := Nat.pow_le_pow_right (by norm_num) hv
      _ = Nat.card T := hcardT.symm
  have hTeq : T = S := Subgroup.eq_of_le_of_card_ge hTS hTA
  subst hTeq
  exact ⟨x', J, T, ⟨hJ, hx'J, hS, hx'S, hx'c⟩⟩

end CFSG.GH74.GLS.Stage1.Thm4.P92
