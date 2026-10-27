
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Lattice
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Lattice
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoInputs
public import Certificates.Certificate4082

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.Seven

open Matrix Equiv CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a

section Alt

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Alt

theorem rho8_mem : ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    (elts (latGens.getD 8 [])).contains (rhoRaw vec8 g) = true :=
  Certificates.certificate4082.1

theorem rho9_mem : ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    (elts (latGens.getD 9 [])).contains (rhoRaw vec9 g) = true :=
  Certificates.certificate4082.2

theorem card_Z {i : ℕ} (hi : i < 12) :
    Nat.card (Z i) = [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
  have hlen : latGens.length = 12 := rfl
  have hG : latGens.getD i [] ∈ latGens := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  rw [Z, card_closure_of_closedH rawIsEnc7 _ depth (List.all_eq_true.mp closed_lat _ hG)]
  have hi' : i < latGens.length := by omega
  have h2 : (latGens.map (fun G => (elts G).size)).getD i 0 = (elts (latGens.getD i [])).size := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getD_eq_getElem _ _ hi',
      List.getElem_map]
  show (elts (latGens.getD i [])).size = _
  rw [← h2, sizes_lat]

theorem rho8_range : (rho lab8).range = Z 8 := by
  have hG : latGens.getD 8 [] ∈ latGens := by simp [latGens]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨g, rfl⟩
    rw [Z, mem_closure_lat hG, enc_rho8]
    exact Std.HashSet.contains_iff_mem.mp (rho8_mem g)
  · rw [card_Z (by norm_num : 8 < 12),
      ← Nat.card_congr (MonoidHom.ofInjective (rho_injective lab8)).toEquiv, card_slThree]
    simp

theorem rho9_range : (rho lab9).range = Z 9 := by
  have hG : latGens.getD 9 [] ∈ latGens := by simp [latGens]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨g, rfl⟩
    rw [Z, mem_closure_lat hG, enc_rho9]
    exact Std.HashSet.contains_iff_mem.mp (rho9_mem g)
  · rw [card_Z (by norm_num : 9 < 12),
      ← Nat.card_congr (MonoidHom.ofInjective (rho_injective lab9)).toEquiv, card_slThree]
    simp

noncomputable def z8Equiv : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ↥(Z 8) :=
  (MonoidHom.ofInjective (rho_injective lab8)).trans (MulEquiv.subgroupCongr rho8_range)

noncomputable def z9Equiv : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ↥(Z 9) :=
  (MonoidHom.ofInjective (rho_injective lab9)).trans (MulEquiv.subgroupCongr rho9_range)

end CFSG.QuasithinUnique.Vol2Native.A312L.Seven
