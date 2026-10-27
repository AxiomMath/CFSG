module

public import CFSG.ClassicalInvolution.Sp62Rec.Pkg

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open


structure E8ZPkgNoHat {G : Type} [Group G] [Finite G] (z e : G) (E B : Subgroup G) (T : Sylow 2 G)
    (A X : Subgroup G) : Prop where
  T_le : (T : Subgroup G) ≤ B
  z_center : z ∈ (T : Subgroup G) ∧ ∀ x ∈ (T : Subgroup G), z * x = x * z
  z_sq : z * z = 1
  z_ne_one : z ≠ 1
  z_ne_e : z ≠ e
  A_le : A ≤ (T : Subgroup G)
  e64 : IsE64 A
  oddC_z : oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥
  e_mem_O2 : e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))).map
    (Subgroup.centralizer ({z} : Set G)).subtype
  gen : ∀ n : G, E.map (MulAut.conj n).toMonoidHom ≠ E →
    E ⊔ E.map (MulAut.conj n).toMonoidHom = ⊤
  X_le : X ≤ Subgroup.normalizer (A : Set G)
  thm2 : ∃ ψ : ↥X →* ↥N0, Function.Surjective ψ ∧ ψ.ker = (oddCoreIn X).subgroupOf X

theorem E8ZPkgNoHat.toPkg {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G}
    {T : Sylow 2 G} {A X : Subgroup G} (N : E8ZPkgNoHat z e E B T A X) (hEB : E ≤ B)
    (hBe : B ≤ Subgroup.centralizer ({e} : Set G))
    (hEn : ∀ g ∈ Subgroup.centralizer ({e} : Set G), E.map (MulAut.conj g).toMonoidHom = E)
    (he : e ∈ E) (hz : z ∈ B)
    (hat : ∃ φ : ↥B →* ↥Hhat, Function.Surjective φ ∧
      φ.ker = (oddCoreIn E).subgroupOf B ∧ (E.subgroupOf B).map φ = E0.subgroupOf Hhat ∧
      φ ⟨e, hEB he⟩ = ⟨alpha, alpha_mem_Hhat⟩) : E8ZPkg z e E B T A X :=
  { E_le_B := hEB, B_le := hBe, E_normal := hEn, e_mem := he, z_mem := hz, hat := hat,
    T_le := N.T_le, z_center := N.z_center, z_sq := N.z_sq, z_ne_one := N.z_ne_one,
    z_ne_e := N.z_ne_e, A_le := N.A_le, e64 := N.e64, oddC_z := N.oddC_z,
    e_mem_O2 := N.e_mem_O2, gen := N.gen, X_le := N.X_le, thm2 := N.thm2 }

structure I1Six {G : Type} [Group G] [Finite G] (z e : G) (E B : Subgroup G) : Prop where
  E_le_B : E ≤ B
  B_le : B ≤ Subgroup.centralizer ({e} : Set G)
  E_normal : ∀ g ∈ Subgroup.centralizer ({e} : Set G), E.map (MulAut.conj g).toMonoidHom = E
  e_mem : e ∈ E
  z_mem : z ∈ B
  hat : ∃ φ : ↥B →* ↥Hhat, Function.Surjective φ ∧
    φ.ker = (oddCoreIn E).subgroupOf B ∧ (E.subgroupOf B).map φ = E0.subgroupOf Hhat ∧
    φ ⟨e, E_le_B e_mem⟩ = ⟨alpha, alpha_mem_Hhat⟩ ∧
    Odd (Subgroup.centralizer ({φ ⟨z, z_mem⟩} : Set ↥Hhat)).index

theorem E8ZPkgNoHat.toPkg' {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G}
    {T : Sylow 2 G} {A X : Subgroup G} (N : E8ZPkgNoHat z e E B T A X) (H : I1Six z e E B) :
    E8ZPkg z e E B T A X :=
  N.toPkg H.E_le_B H.B_le H.E_normal H.e_mem H.z_mem (by
    obtain ⟨φ, h1, h2, h3, h4, -⟩ := H.hat
    exact ⟨φ, h1, h2, h3, h4⟩)

end CFSG.ClassicalInvolution.Sp62Rec
