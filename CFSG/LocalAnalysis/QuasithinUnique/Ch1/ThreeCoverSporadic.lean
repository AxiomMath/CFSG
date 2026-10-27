module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverSporadicInputs
public import Certificates.Certificate4103
public import Certificates.Certificate3120
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public meta import CFSG.Open.Defs
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public import Certificates.Certificate8026Base
public meta import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.SectionRank

theorem M11_sylow3_square_witness_hx :
    mathieuWord m11LocA m11LocB m11WordX.toList ^ 3 = 1 :=
  Certificates.certificate4103.1

theorem M11_sylow3_square_witness_hy :
    mathieuWord m11LocA m11LocB m11WordY.toList ^ 3 = 1 :=
  Certificates.certificate4103.2.1

theorem M11_sylow3_square_witness_hxy :
    mathieuWord m11LocA m11LocB m11WordX.toList * mathieuWord m11LocA m11LocB m11WordY.toList =
      mathieuWord m11LocA m11LocB m11WordY.toList *
        mathieuWord m11LocA m11LocB m11WordX.toList :=
  Certificates.certificate4103.2.2.1

theorem M11_sylow3_square_witness_hinj :
    Function.Injective fun t : Fin 3 × Fin 3 =>
      mathieuWord m11LocA m11LocB m11WordX.toList ^ (t.1 : ℕ) *
        mathieuWord m11LocA m11LocB m11WordY.toList ^ (t.2 : ℕ) :=
  Certificates.certificate4103.2.2.2.1

theorem M11_sylow3_square_witness_hhx :
    mathieuWord m11LocA m11LocB m11WordH.toList * mathieuWord m11LocA m11LocB m11WordX.toList *
        (mathieuWord m11LocA m11LocB m11WordH.toList)⁻¹ =
      mathieuWord m11LocA m11LocB m11WordX.toList ^ 2 *
        mathieuWord m11LocA m11LocB m11WordY.toList ^ 0 :=
  Certificates.certificate4103.2.2.2.2.1

theorem M11_sylow3_square_witness_hhy :
    mathieuWord m11LocA m11LocB m11WordH.toList * mathieuWord m11LocA m11LocB m11WordY.toList *
        (mathieuWord m11LocA m11LocB m11WordH.toList)⁻¹ =
      mathieuWord m11LocA m11LocB m11WordX.toList ^ 2 *
        mathieuWord m11LocA m11LocB m11WordY.toList ^ 1 :=
  Certificates.certificate4103.2.2.2.2.2.1

theorem M11_sylow3_square_witness :
    ∃ x y h : NativeSporadic.M11,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.M11)) = 3 ^ 2 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 0 ∧ h * y * h⁻¹ = x ^ 2 * y ^ 1 := by
  set x := mathieuWord m11LocA m11LocB m11WordX.toList
  set y := mathieuWord m11LocA m11LocB m11WordY.toList
  set h := mathieuWord m11LocA m11LocB m11WordH.toList
  have hx : x ^ 3 = 1 := M11_sylow3_square_witness_hx
  have hy : y ^ 3 = 1 := M11_sylow3_square_witness_hy
  have hxy : x * y = y * x := M11_sylow3_square_witness_hxy
  have hinj : Function.Injective fun t : Fin 3 × Fin 3 => x ^ (t.1 : ℕ) * y ^ (t.2 : ℕ) :=
    M11_sylow3_square_witness_hinj
  exact ⟨x, y, h, hx, hy, hxy, LocalWitness.card_closure_eq_sq (by norm_num) hx hy hxy hinj,
    M11_sylow3_square_witness_hhx, M11_sylow3_square_witness_hhy⟩

theorem M11_perfect_odd_cover_trivial {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* NativeSporadic.M11) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hcard := CFSG.Sporadic.Mathieu.card_M11
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := M11_sylow3_square_witness
    exact sylow_kernel_eq_bot_of_square_witness π hπ hC hx hy hxy hQ (by rw [hcard]; decide) hhx
      hhy (by decide +revert) Cp
  · exfalso
    exact (small_sporadic_order_conditions (n := 7920) (by norm_num)).2 r hr hr2 h3 (hcard ▸ hsq)

theorem M23_sylow3_square_witness_hx :
    mathieuWord m23LocA m23LocB m23WordX.toList ^ 3 = 1 :=
  Certificates.certificate4103.2.2.2.2.2.2.1

theorem M23_sylow3_square_witness_hy :
    mathieuWord m23LocA m23LocB m23WordY.toList ^ 3 = 1 :=
  Certificates.certificate4103.2.2.2.2.2.2.2.1

theorem M23_sylow3_square_witness_hxy :
    mathieuWord m23LocA m23LocB m23WordX.toList * mathieuWord m23LocA m23LocB m23WordY.toList =
      mathieuWord m23LocA m23LocB m23WordY.toList *
        mathieuWord m23LocA m23LocB m23WordX.toList :=
  Certificates.certificate4103.2.2.2.2.2.2.2.2.1

theorem M23_sylow3_square_witness_hinj :
    Function.Injective fun t : Fin 3 × Fin 3 =>
      mathieuWord m23LocA m23LocB m23WordX.toList ^ (t.1 : ℕ) *
        mathieuWord m23LocA m23LocB m23WordY.toList ^ (t.2 : ℕ) :=
  Certificates.certificate4103.2.2.2.2.2.2.2.2.2.1

theorem M23_sylow3_square_witness_hhx :
    mathieuWord m23LocA m23LocB m23WordH.toList * mathieuWord m23LocA m23LocB m23WordX.toList *
        (mathieuWord m23LocA m23LocB m23WordH.toList)⁻¹ =
      mathieuWord m23LocA m23LocB m23WordX.toList ^ 1 *
        mathieuWord m23LocA m23LocB m23WordY.toList ^ 2 :=
  Certificates.certificate4103.2.2.2.2.2.2.2.2.2.2.1

theorem M23_sylow3_square_witness_hhy :
    mathieuWord m23LocA m23LocB m23WordH.toList * mathieuWord m23LocA m23LocB m23WordY.toList *
        (mathieuWord m23LocA m23LocB m23WordH.toList)⁻¹ =
      mathieuWord m23LocA m23LocB m23WordX.toList ^ 0 *
        mathieuWord m23LocA m23LocB m23WordY.toList ^ 2 :=
  Certificates.certificate4103.2.2.2.2.2.2.2.2.2.2.2

theorem M23_sylow3_square_witness :
    ∃ x y h : NativeSporadic.M23,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.M23)) = 3 ^ 2 ∧
      h * x * h⁻¹ = x ^ 1 * y ^ 2 ∧ h * y * h⁻¹ = x ^ 0 * y ^ 2 := by
  set x := mathieuWord m23LocA m23LocB m23WordX.toList
  set y := mathieuWord m23LocA m23LocB m23WordY.toList
  set h := mathieuWord m23LocA m23LocB m23WordH.toList
  have hx : x ^ 3 = 1 := M23_sylow3_square_witness_hx
  have hy : y ^ 3 = 1 := M23_sylow3_square_witness_hy
  have hxy : x * y = y * x := M23_sylow3_square_witness_hxy
  have hinj : Function.Injective fun t : Fin 3 × Fin 3 => x ^ (t.1 : ℕ) * y ^ (t.2 : ℕ) :=
    M23_sylow3_square_witness_hinj
  exact ⟨x, y, h, hx, hy, hxy, LocalWitness.card_closure_eq_sq (by norm_num) hx hy hxy hinj,
    M23_sylow3_square_witness_hhx, M23_sylow3_square_witness_hhy⟩

theorem M23_perfect_odd_cover_trivial {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* NativeSporadic.M23) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hcard : Nat.card NativeSporadic.M23 = 10200960 := by
    rw [CFSG.Sporadic.Mathieu.nativeM23_eq, Nat.card_eq_fintype_card]
    exact CFSG.M23.M23Group.card_M23
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := M23_sylow3_square_witness
    exact sylow_kernel_eq_bot_of_square_witness π hπ hC hx hy hxy hQ (by rw [hcard]; decide) hhx
      hhy (by decide +revert) Cp
  · exfalso
    exact (small_sporadic_order_conditions (n := 10200960) (by norm_num)).2 r hr hr2 h3
      (hcard ▸ hsq)

end CFSG.QuasithinUnique.Ch1
