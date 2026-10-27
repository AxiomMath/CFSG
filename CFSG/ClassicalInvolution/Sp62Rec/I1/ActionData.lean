module

public import CFSG.ClassicalInvolution.Sp62Rec.PkgNoHat
public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec.I1

@[expose] def ActsOnE {G : Type} [Group G] {E : Subgroup G} (f : ↥E →* Wr 6) (h : G) (w : Wr 6) :
    Prop :=
  ∀ (x : G) (hx : x ∈ E) (hx' : h * x * h⁻¹ ∈ E),
    f ⟨h * x * h⁻¹, hx'⟩ = w * f ⟨x, hx⟩ * w⁻¹


structure I1Action {G : Type} [Group G] [Finite G] (z e : G) (E B : Subgroup G)
    (f : ↥E →* Wr 6) (Θ : ↥Wsub ≃* ↥Hhat) (φ : ↥B →* ↥Hhat) : Prop where
  E_le_B : E ≤ B
  B_le : B ≤ Subgroup.centralizer ({e} : Set G)
  E_normal : ∀ g ∈ Subgroup.centralizer ({e} : Set G), E.map (MulAut.conj g).toMonoidHom = E
  e_mem : e ∈ E
  z_mem : z ∈ B
  f_range : f.range = aeSub 6
  f_ker : f.ker = (oddCoreIn E).subgroupOf E
  Θ_pi : Θ ⟨allOnes 6, allOnes_mem_Wsub⟩ = ⟨alpha, alpha_mem_Hhat⟩
  φ_surj : Function.Surjective φ
  φ_ker : φ.ker = (oddCoreIn E).subgroupOf B
  φ_E : (E.subgroupOf B).map φ = E0.subgroupOf Hhat
  φ_e : φ ⟨e, E_le_B e_mem⟩ = ⟨alpha, alpha_mem_Hhat⟩
  φ_odd : Odd (Subgroup.centralizer ({φ ⟨z, z_mem⟩} : Set ↥Hhat)).index
  φ_f : ∀ (x : G) (hx : x ∈ E), ∃ hm : f ⟨x, hx⟩ ∈ Wsub,
    φ ⟨x, E_le_B hx⟩ = Θ ⟨f ⟨x, hx⟩, hm⟩
  kappa : ∀ h ∈ Subgroup.centralizer ({e} : Set G), ∃ w : Wr 6, ActsOnE f h w

theorem I1Action.toI1Six {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G}
    {f : ↥E →* Wr 6} {Θ : ↥Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat} (D : I1Action z e E B f Θ φ) :
    I1Six z e E B :=
  ⟨D.E_le_B, D.B_le, D.E_normal, D.e_mem, D.z_mem,
    ⟨φ, D.φ_surj, D.φ_ker, D.φ_E, D.φ_e, D.φ_odd⟩⟩

end CFSG.ClassicalInvolution.Sp62Rec
