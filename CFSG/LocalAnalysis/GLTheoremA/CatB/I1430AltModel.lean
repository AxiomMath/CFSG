module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430AltModel

open CFSG.Open Equiv

def altP : Perm (Fin 10) := swap 0 1 * swap 2 3

def altQ : Perm (Fin 10) := swap 0 2 * swap 1 3

def altA : Perm (Fin 10) := swap 1 2 * swap 2 3

def altB : Perm (Fin 10) := swap 4 5 * swap 5 6

def altC : Perm (Fin 10) := swap 7 8 * swap 8 9

theorem altP_mem : altP ∈ alternatingGroup (Fin 10) := by
  rw [Equiv.Perm.mem_alternatingGroup, altP, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  norm_num

theorem altQ_mem : altQ ∈ alternatingGroup (Fin 10) := by
  rw [Equiv.Perm.mem_alternatingGroup, altQ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  norm_num

theorem altA_mem : altA ∈ alternatingGroup (Fin 10) := by
  rw [Equiv.Perm.mem_alternatingGroup, altA, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  norm_num

theorem altB_mem : altB ∈ alternatingGroup (Fin 10) := by
  rw [Equiv.Perm.mem_alternatingGroup, altB, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  norm_num

theorem altC_mem : altC ∈ alternatingGroup (Fin 10) := by
  rw [Equiv.Perm.mem_alternatingGroup, altC, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  norm_num

def aP : alternatingGroup (Fin 10) := ⟨altP, altP_mem⟩

def aQ : alternatingGroup (Fin 10) := ⟨altQ, altQ_mem⟩

def aA : alternatingGroup (Fin 10) := ⟨altA, altA_mem⟩

def aB : alternatingGroup (Fin 10) := ⟨altB, altB_mem⟩

def aC : alternatingGroup (Fin 10) := ⟨altC, altC_mem⟩

def tripF (x : ZMod 3 × ZMod 3 × ZMod 3) : alternatingGroup (Fin 10) :=
  aA ^ x.1.val * (aB ^ x.2.1.val * aC ^ x.2.2.val)

def duoF (x : ZMod 2 × ZMod 2) : alternatingGroup (Fin 10) :=
  aP ^ x.1.val * aQ ^ x.2.val

theorem tripF_mul : ∀ x y : ZMod 3 × ZMod 3 × ZMod 3, tripF (x + y) = tripF x * tripF y := by
  decide

theorem tripF_eq_one : ∀ x : ZMod 3 × ZMod 3 × ZMod 3, tripF x = 1 → x = 0 := by
  decide

set_option maxRecDepth 10000 in
theorem tripF_pow_three : ∀ x : ZMod 3 × ZMod 3 × ZMod 3, tripF x ^ 3 = 1 := by
  decide

theorem duoF_mul : ∀ x y : ZMod 2 × ZMod 2, duoF (x + y) = duoF x * duoF y := by
  decide

theorem duoF_eq_one : ∀ x : ZMod 2 × ZMod 2, duoF x = 1 → x = 0 := by
  decide

theorem conjA_duoF : ∀ x : ZMod 2 × ZMod 2, aA * duoF x * aA⁻¹ = duoF (x.2, x.1 + x.2) := by
  decide

theorem conjA_inv_duoF : ∀ x : ZMod 2 × ZMod 2, aA⁻¹ * duoF x * aA = duoF (x.1 + x.2, x.1) := by
  decide

theorem commB_duoF : ∀ x : ZMod 2 × ZMod 2, aB * duoF x = duoF x * aB := by
  decide

theorem commC_duoF : ∀ x : ZMod 2 × ZMod 2, aC * duoF x = duoF x * aC := by
  decide

def tripHom : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* alternatingGroup (Fin 10) :=
  MonoidHom.mk' (fun x => tripF (Multiplicative.toAdd x))
    fun x y => tripF_mul (Multiplicative.toAdd x) (Multiplicative.toAdd y)

def duoHom : Multiplicative (ZMod 2 × ZMod 2) →* alternatingGroup (Fin 10) :=
  MonoidHom.mk' (fun x => duoF (Multiplicative.toAdd x))
    fun x y => duoF_mul (Multiplicative.toAdd x) (Multiplicative.toAdd y)

theorem tripHom_injective : Function.Injective tripHom := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h := tripF_eq_one (Multiplicative.toAdd x) hx
  exact Multiplicative.toAdd.injective (h.trans toAdd_one.symm)

theorem duoHom_injective : Function.Injective duoHom := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h := duoF_eq_one (Multiplicative.toAdd x) hx
  exact Multiplicative.toAdd.injective (h.trans toAdd_one.symm)

abbrev E3 : Subgroup (alternatingGroup (Fin 10)) := tripHom.range

abbrev V4 : Subgroup (alternatingGroup (Fin 10)) := duoHom.range

theorem card_E3 : Nat.card E3 = 3 ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective tripHom_injective).toEquiv]
  rw [Nat.card_eq_fintype_card]
  rfl

theorem card_V4 : Nat.card V4 = 2 ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective duoHom_injective).toEquiv]
  rw [Nat.card_eq_fintype_card]
  rfl

theorem aA_mem_normalizer_V4 :
    aA ∈ Subgroup.normalizer ((V4 : Subgroup (alternatingGroup (Fin 10))) : Set (alternatingGroup (Fin 10))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hh
    refine MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd ((Multiplicative.toAdd x).2,
      (Multiplicative.toAdd x).1 + (Multiplicative.toAdd x).2), ?_⟩
    exact (conjA_duoF (Multiplicative.toAdd x)).symm
  · intro hh
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 hh
    refine MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd ((Multiplicative.toAdd w).1 +
      (Multiplicative.toAdd w).2, (Multiplicative.toAdd w).1), ?_⟩
    have h1 := conjA_inv_duoF (Multiplicative.toAdd w)
    have h2 : duoF (Multiplicative.toAdd w) = aA * h * aA⁻¹ := hw
    show duoF ((Multiplicative.toAdd w).1 + (Multiplicative.toAdd w).2, (Multiplicative.toAdd w).1) = h
    rw [← h1, h2]
    group

theorem aB_mem_normalizer_V4 :
    aB ∈ Subgroup.normalizer ((V4 : Subgroup (alternatingGroup (Fin 10))) : Set (alternatingGroup (Fin 10))) := by
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 (SetLike.mem_coe.1 hh)
  exact (commB_duoF (Multiplicative.toAdd x)).symm

theorem aC_mem_normalizer_V4 :
    aC ∈ Subgroup.normalizer ((V4 : Subgroup (alternatingGroup (Fin 10))) : Set (alternatingGroup (Fin 10))) := by
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 (SetLike.mem_coe.1 hh)
  exact (commC_duoF (Multiplicative.toAdd x)).symm

theorem E3_le_normalizer_V4 :
    E3 ≤ Subgroup.normalizer ((V4 : Subgroup (alternatingGroup (Fin 10))) : Set (alternatingGroup (Fin 10))) := by
  rintro _ ⟨x, rfl⟩
  show tripF (Multiplicative.toAdd x) ∈ _
  unfold tripF
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ aA_mem_normalizer_V4 _)
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ aB_mem_normalizer_V4 _)
      (Subgroup.pow_mem _ aC_mem_normalizer_V4 _))

theorem E3_isElemAbelian : IsElemAbelian 3 E3 := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    change a.1 * b.1 = b.1 * a.1
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    exact tripF_pow_three _

theorem i1430TwoLocal_altTen : I1430TwoLocal (alternatingGroup (Fin 10)) 3 := by
  refine ⟨V4, E3, ?_, ?_, E3_le_normalizer_V4, E3_isElemAbelian, card_E3⟩
  · intro h
    have h4 := card_V4
    rw [h, Subgroup.card_bot] at h4
    norm_num at h4
  · exact IsPGroup.of_card (n := 2) card_V4

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.I1430AltModel
