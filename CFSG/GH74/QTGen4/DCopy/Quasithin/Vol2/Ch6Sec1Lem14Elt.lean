module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem14Cmp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem commutator_mem_centralizer_of_le_F4 (h432 : Stmt4_3_2_F4) (h6110 : Stmt6_1_10_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)))
    (hn4 : 4 ≤ n) {g : G}
    (hA : conjSubgroup V g ≤
      Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G)) :
    ∀ a ∈ conjSubgroup V g, ∀ x ∈ lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)),
      a * x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set LU := lOne L U with hLU
  set A := conjSubgroup V g with hAdef
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have h1 := h.lemma_6_1_14_one_F4 h432 htT ht hSyl
  have hAN : A ≤ Subgroup.normalizer (LU : Set G) :=
    hA.trans (h.centralizer_le_normalizer_lOne_fix_F4 h432 h6110 h37 h39 htT ht hSyl hn4)
  have hRTU : R ≤ T ⊓ Subgroup.normalizer (U : Set G) :=
    le_inf (sup_le inf_le_left (Subgroup.zpowers_le.mpr htT))
      (h1.1.le.trans (Subgroup.centralizer_le_normalizer _))
  have hRX : R ≤ Subgroup.centralizer (U : Set G) ⊓ Subgroup.normalizer (LU : Set G) :=
    le_inf h1.1.le (hRTU.trans h.le_normalizer_lOne_fix)
  have hRsyl : IsSylowTwoOf R (Subgroup.centralizer (U : Set G) ⊓
      Subgroup.normalizer (LU : Set G)) := E6.isSylowIn_of_le h1.1 hRX inf_le_left
  have hA2 : IsPGroup 2 A :=
    isPGroup_conjSubgroup (F7.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian) g
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_isSylowTwoOf hRsyl (le_inf hA hAN) hA2

  have heq : cjSub y A = conjSubgroup V (g * y⁻¹) := by
    ext x
    rw [mem_cjSub, hAdef, mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    constructor <;> intro hx <;> simpa [mul_assoc] using hx
  have hyAQ : cjSub y A ≤ ch6Q T V := by
    have hmem : cjSub y A ∈ gammaSet V 0 R :=
      ⟨hyA, g * y⁻¹, heq.le, by rw [heq, mQuot_self]⟩
    exact (le_wClos hmem).trans (h.lemma_6_1_14_three_F4 h6110 htT ht).1

  have hQ := h.toHyp611.centralizer_eq
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLUL : LU ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hLUQ : LU ≤ Subgroup.normalizer (ch6Q T V : Set G) := hLUL.trans (le_sup_left.trans hLTQ)
  have hQLU : ch6Q T V ⊓ LU ≤ pCoreOf 2 LU := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right (fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hLUQ hx, Subgroup.le_normalizer hx⟩)
      ((h.sylow.1.to_le inf_le_left).to_le inf_le_left)
  have hQN : ch6Q T V ≤ Subgroup.normalizer (LU : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans ((Subgroup.centralizer_le inf_le_left).trans
      (Subgroup.centralizer_le_normalizer _)))).trans h.le_normalizer_lOne_fix
  have hO := h.pCoreOf_lOne_fix_le htT ht hn4
  intro a ha x hx
  have hq : y * a * y⁻¹ ∈ ch6Q T V := hyAQ (mem_cjSub.mpr (by simpa [mul_assoc] using ha))
  have hx' : y * x * y⁻¹ ∈ LU := (Subgroup.mem_normalizer_iff.mp hy.2 x).mp hx
  have hc : (y * a * y⁻¹) * (y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹ ∈
      ch6Q T V ⊓ LU := by
    refine ⟨?_, ?_⟩
    · have h2 : (y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹ ∈ ch6Q T V :=
        (Subgroup.mem_normalizer_iff.mp (hLUQ hx') _).mp (Subgroup.inv_mem _ hq)
      have e : (y * a * y⁻¹) * (y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹ =
          (y * a * y⁻¹) * ((y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hq h2
    · exact LU.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQN hq) _).mp hx') (LU.inv_mem hx')
  have hc' := hQLU hc
  have hyO : y⁻¹ ∈ Subgroup.normalizer ((pCoreOf 2 LU : Subgroup G) : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 LU (Subgroup.inv_mem _ hy.2)
  have e : a * x * a⁻¹ * x⁻¹ = y⁻¹ * ((y * a * y⁻¹) * (y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ *
      (y * x * y⁻¹)⁻¹) * y⁻¹⁻¹ := by group
  rw [e]
  exact hO ((Subgroup.mem_normalizer_iff.mp hyO _).mp hc')

end Hyp611Nat

end CFSG.Quasithin.H13
