module

public import CFSG.ClassicalInvolution.Solomon73.YamakiModel
public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open


@[expose] def E0 : Subgroup (StatedSp 3 (ZMod 2)) := ⁅Hhat, Hhat⁆

theorem alpha_mem_Hhat : alpha ∈ Hhat := yamakiSp_mem_Hhat (Or.inl (by decide))

structure E8ZPkg {G : Type} [Group G] [Finite G] (z e : G) (E B : Subgroup G) (T : Sylow 2 G)
    (A X : Subgroup G) : Prop where
  E_le_B : E ≤ B
  B_le : B ≤ Subgroup.centralizer ({e} : Set G)
  E_normal : ∀ g ∈ Subgroup.centralizer ({e} : Set G), E.map (MulAut.conj g).toMonoidHom = E
  e_mem : e ∈ E
  z_mem : z ∈ B
  hat : ∃ φ : ↥B →* ↥Hhat, Function.Surjective φ ∧
    φ.ker = (oddCoreIn E).subgroupOf B ∧ (E.subgroupOf B).map φ = E0.subgroupOf Hhat ∧
    φ ⟨e, E_le_B e_mem⟩ = ⟨alpha, alpha_mem_Hhat⟩
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

end CFSG.ClassicalInvolution.Sp62Rec
