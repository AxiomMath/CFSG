module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersThData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignTori
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusPointwiseAut

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def nodePermPow (m : ℕ) (J : Finset (Fin (Tag.rank .F4))) :
    Finset (Fin (Tag.rank .F4)) :=
  if Even m then J else J.map Fin.revPerm.toEmbedding

theorem map_rev_map_rev_F4 (J : Finset (Fin (Tag.rank .F4))) :
    (J.map Fin.revPerm.toEmbedding).map Fin.revPerm.toEmbedding = J := by
  ext i
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, Fin.revPerm_apply]
  constructor
  · rintro ⟨j, ⟨k, hk, rfl⟩, rfl⟩
    rwa [Fin.rev_rev]
  · intro hi
    exact ⟨Fin.rev i, ⟨i, hi, rfl⟩, Fin.rev_rev i⟩

theorem card_nodePermPow (m : ℕ) (J : Finset (Fin (Tag.rank .F4))) :
    (nodePermPow m J).card = J.card := by
  unfold nodePermPow
  split_ifs
  · rfl
  · exact Finset.card_map _

theorem nodePermPow_nodePermPow (m : ℕ) (J : Finset (Fin (Tag.rank .F4))) :
    nodePermPow m (nodePermPow m J) = J := by
  unfold nodePermPow
  split_ifs
  · rfl
  · exact map_rev_map_rev_F4 J

theorem nodePermPow_succ (m : ℕ) (J : Finset (Fin (Tag.rank .F4))) :
    nodePermPow (m + 1) J = (nodePermPow m J).map Fin.revPerm.toEmbedding := by
  unfold nodePermPow
  by_cases hm : Even m
  · have h1 : ¬ Even (m + 1) := Nat.not_even_iff_odd.2 hm.add_one
    simp only [hm, h1, ite_true, ite_false]
  · have h1 : Even (m + 1) := (Nat.not_even_iff_odd.1 hm).add_one
    simp only [hm, h1, ite_true, ite_false]
    exact (map_rev_map_rev_F4 J).symm

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem finiteExceptionalAut_mem_leviTorus {J : Finset (Fin (Tag.rank .F4))}
    {x : adjointGroup .F4 K} (hx : (x : ModGL .F4 K) ∈ leviTorus K J) :
    ((graphAutF4 K x : adjointGroup .F4 K) : ModGL .F4 K) ∈
      leviTorus K (J.map Fin.revPerm.toEmbedding) := by
  obtain ⟨b, hb, hbx⟩ := mem_leviTorus.1 hx
  obtain rfl : x = ⟨rootDiagUnit .F4 b, f4RootDiagUnit_mem_adjointGroup b⟩ := Subtype.ext hbx.symm
  have h := CFSG.RankThree.Chevalley.EvenF4QPlus.finiteExceptionalAut_rootDiagUnit (L := K) b
    (f4RootDiagUnit_mem_adjointGroup b)
  refine mem_leviTorus.2 ⟨fun j => b (ReeTag.F4.perm j) ^ ReeTag.F4.exponent (ReeTag.F4.perm j),
    fun j hj => ?_, h.symm⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
  change b (ReeTag.F4.perm (Fin.rev i)) ^ ReeTag.F4.exponent (ReeTag.F4.perm (Fin.rev i)) = 1
  have hp : ReeTag.F4.perm (Fin.rev i) = i := by fin_cases i <;> rfl
  rw [hp, hb i hi, one_pow]

theorem finiteExceptionalAut_pow_mem_leviTorus (m : ℕ) {J : Finset (Fin (Tag.rank .F4))}
    {x : adjointGroup .F4 K} (hx : (x : ModGL .F4 K) ∈ leviTorus K J) :
    (((graphAutF4 K ^ m) x : adjointGroup .F4 K) : ModGL .F4 K) ∈
      leviTorus K (nodePermPow m J) := by
  induction m with
  | zero => simpa [nodePermPow] using hx
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, nodePermPow_succ]
    exact finiteExceptionalAut_mem_leviTorus ih

end Torus

end CFSG.SeitzReduction.F4Pilot
