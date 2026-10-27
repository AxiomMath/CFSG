module

public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.QTGen4.U42.PairExtension
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.QTGen4.U42

open Subgroup in
theorem amalgam_iso_of_coords {G Y' : Type} [Group G] [Finite G] [Group Y'] [Finite Y']
    {H M T U : Subgroup G} {P1' P2' T' U' : Subgroup Y'} {R : Subgroup (Equiv.Perm (Fin 5))}
    {Bsub Tsub : Subgroup Mc} (hU0R : U0 ≤ Mof R)
    (e : ↥M ≃* Mof R) (eY : ↥P2' ≃* Mof R)
    (hB : ∀ m : ↥M, (m : G) ∈ H ↔ ((e m : Mof R) : Mc) ∈ Bsub)
    (hBY : ∀ g : ↥P2', (g : Y') ∈ P1' ↔ ((eY g : Mof R) : Mc) ∈ Bsub)
    (hT : ∀ m : ↥M, (m : G) ∈ T ↔ ((e m : Mof R) : Mc) ∈ Tsub)
    (hTY : ∀ g : ↥P2', (g : Y') ∈ T' ↔ ((eY g : Mof R) : Mc) ∈ Tsub)
    (hU : ∀ m : ↥M, (m : G) ∈ U ↔ ((e m : Mof R) : Mc) ∈ U0)
    (hUY : ∀ g : ↥P2', (g : Y') ∈ U' ↔ ((eY g : Mof R) : Mc) ∈ U0)
    (hH : PairCore H (H ⊓ M) T U) (hP : PairCore P1' (P1' ⊓ P2') T' U')
    (hUB : U ≤ ⁅H ⊓ M, H ⊓ M⁆) :
    Nonempty ((CFSG.Quasithin.RankTwoAmalgam.ofSubgroups H M).Iso
      (CFSG.Quasithin.RankTwoAmalgam.ofSubgroups P1' P2')) := by
  classical
  have hBM : H ⊓ M ≤ M := inf_le_right
  let φ2 : ↥M ≃* ↥P2' := e.trans eY.symm
  have hφ : ∀ m : ↥M, ((eY (φ2 m) : Mof R) : Mc) = ((e m : Mof R) : Mc) := fun m => by
    simp [φ2]
  have hHiff : ∀ m : ↥M, (m : G) ∈ H ↔ ((φ2 m : ↥P2') : Y') ∈ P1' := fun m => by
    rw [hB m, hBY (φ2 m), hφ m]
  let lam : ↥(H ⊓ M) ≃* ↥(P1' ⊓ P2') :=
    { toFun := fun b => ⟨((φ2 ⟨b, hBM b.2⟩ : ↥P2') : Y'),
        (hHiff ⟨b, hBM b.2⟩).1 b.2.1, (φ2 ⟨b, hBM b.2⟩).2⟩
      invFun := fun g => ⟨((φ2.symm ⟨(g : Y'), g.2.2⟩ : ↥M) : G),
        (hHiff (φ2.symm ⟨(g : Y'), g.2.2⟩)).2 (by simpa using g.2.1),
        (φ2.symm ⟨(g : Y'), g.2.2⟩).2⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext
        (congrArg (fun z : ↥P2' => (z : Y')) (map_mul φ2 ⟨a, hBM a.2⟩ ⟨b, hBM b.2⟩)) }
  have hlamT : ∀ b : ↥(H ⊓ M), (b : G) ∈ T ↔ ((lam b : ↥(P1' ⊓ P2')) : Y') ∈ T' := fun b => by
    show (b : G) ∈ T ↔ ((φ2 ⟨b, hBM b.2⟩ : ↥P2') : Y') ∈ T'
    rw [hT ⟨b, hBM b.2⟩, hTY (φ2 ⟨b, hBM b.2⟩), hφ]
  have hlamU : ∀ b : ↥(H ⊓ M), (b : G) ∈ U ↔ ((lam b : ↥(P1' ⊓ P2')) : Y') ∈ U' := fun b => by
    show (b : G) ∈ U ↔ ((φ2 ⟨b, hBM b.2⟩ : ↥P2') : Y') ∈ U'
    rw [hU ⟨b, hBM b.2⟩, hUY (φ2 ⟨b, hBM b.2⟩), hφ]
  have hUM : U ≤ M := hH.U_le_T.trans (hH.T_le_B.trans hBM)
  let fU : ↥U →* ↥U0 :=
    { toFun := fun u => ⟨((e ⟨u, hUM u.2⟩ : Mof R) : Mc), (hU ⟨u, hUM u.2⟩).1 u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext
        (congrArg (fun z : Mof R => (z : Mc)) (map_mul e ⟨a, hUM a.2⟩ ⟨b, hUM b.2⟩)) }
  have fU_bij : Function.Bijective fU := by
    constructor
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      have h2 : e ⟨a, hUM a.2⟩ = e ⟨b, hUM b.2⟩ := Subtype.ext h1
      have h3 := e.injective h2
      exact Subtype.ext (by simpa using congrArg (fun z : ↥M => (z : G)) h3)
    · intro v
      refine ⟨⟨((e.symm ⟨(v : Mc), hU0R v.2⟩ : ↥M) : G), ?_⟩, Subtype.ext ?_⟩
      · exact (hU _).2 (by simpa using v.2)
      · simp [fU]
  obtain ⟨θ, hθ⟩ := pair_extension hH hP hUB (MulEquiv.ofBijective fU fU_bij) lam hlamT hlamU
  refine ⟨{ φ1 := θ, φ12 := lam, φ2 := φ2, comm1 := ?_, comm2 := ?_ }⟩
  · intro g
    exact Subtype.ext (hθ g).symm
  · intro g
    exact Subtype.ext rfl

end CFSG.GH74.QTGen4.U42
