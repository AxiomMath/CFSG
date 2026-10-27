module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open scoped commutatorElement

@[expose] def I1422Char2At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K J : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    y ∈ Subgroup.normalizer (K : Set G) → y ^ 3 = 1 → ¬ CentMod 3 K y →
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J → IsAltPType 3 J 8 →
    IsChevSimple 2 (PSimple 3 K) → Nonempty (↥(imageMod 3 K J) ≃* ↥(alternatingGroup (Fin 8)))

section MainCerts

theorem up7a8_closure
    {G : Type} [Group G] [Finite G] {X K J : Subgroup G} {y : G} {r : ℕ}
    (hr : r.Prime) (hX : CFSG.Open.IsKGroup ↥X) (hK : GLAPComponent 3 X K)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyp : y ^ 3 = 1)
    (hKr : IsChevSimple r (PSimple 3 K))
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J) :
    IsChevSimple r (PSimple 3 J) := by
  have hyN' : Subgroup.zpowers y ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.2 hyN
  have hA' : IsElemAbelian 3 (Subgroup.zpowers y) := up7a8_zpowers_elemAb hyp
  have hcen : Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      exact h y (Subgroup.mem_zpowers y)
    · intro h z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (Commute.zpow_left (show Commute y g from h) m).eq
  exact (chevClosureQAt_of_lieComp_lieComps (G := G) lieComp_holds
    (fun _ hq' h5 => lieCompsOn_holds hq' h5) Nat.prime_three (by norm_num))
    Nat.prime_three (by norm_num) r hr X K (Subgroup.zpowers y) hX hK hKr hA' hyN' J
    (by rw [hcen]; exact hJ)

end MainCerts

end CFSG.LocalAnalysis.GLTheoremA
