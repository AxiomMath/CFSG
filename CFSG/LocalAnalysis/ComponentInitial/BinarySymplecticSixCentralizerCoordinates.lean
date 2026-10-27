module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCongruenceOrbits

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix Subgroup CFSG.Assembly.LowTwoRank SymplecticTorusWeyl
open scoped commutatorElement

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem exists_commutator_map (φ : G ≃* H) {x : G}
    (hx : ∃ g ∈ centralizer ({x} : Set G), ∃ h ∈ centralizer ({x} : Set G), ⁅g, h⁆ = x) :
    ∃ g ∈ centralizer ({φ x} : Set H), ∃ h ∈ centralizer ({φ x} : Set H), ⁅g, h⁆ = φ x := by
  obtain ⟨g, hg, h, hh, rfl⟩ := hx
  refine ⟨φ g, ?_, φ h, ?_, (map_commutatorElement φ.toMonoidHom g h).symm⟩
  · rw [mem_centralizer_singleton_iff] at hg ⊢
    rw [← map_mul, ← map_mul, hg]
  · rw [mem_centralizer_singleton_iff] at hh ⊢
    rw [← map_mul, ← map_mul, hh]

theorem exists_sq_map (φ : G ≃* H) {x : G} (hx : ∃ m ∈ centralizer ({x} : Set G), m ^ 2 = x) :
    ∃ m ∈ centralizer ({φ x} : Set H), m ^ 2 = φ x := by
  obtain ⟨m, hm, rfl⟩ := hx
  refine ⟨φ m, ?_, (map_pow φ m 2).symm⟩
  rw [mem_centralizer_singleton_iff] at hm ⊢
  rw [← map_mul, ← map_mul, hm]

end Transport

@[expose] def spOfMat (A A' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    (h₁ : A * A' = 1) (h₂ : A' * A = 1)
    (hA : Aᵀ * fromBlocks 0 1 (-1) 0 * A = fromBlocks 0 1 (-1) 0) : StatedSp 3 (ZMod 2) :=
  ⟨⟨A, A', h₁, h₂⟩, mem_statedSp_iff.2 hA⟩

theorem coe_spOfMat (A A' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    (h₁ : A * A' = 1) (h₂ : A' * A = 1)
    (hA : Aᵀ * fromBlocks 0 1 (-1) 0 * A = fromBlocks 0 1 (-1) 0) :
    ((spOfMat A A' h₁ h₂ hA : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = A :=
  rfl

theorem coe_spOfMat_inv (A A' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    (h₁ : A * A' = 1) (h₂ : A' * A = 1)
    (hA : Aᵀ * fromBlocks 0 1 (-1) 0 * A = fromBlocks 0 1 (-1) 0) :
    (((spOfMat A A' h₁ h₂ hA)⁻¹ : StatedSp 3 (ZMod 2)) : GL (Fin 3 ⊕ Fin 3) (ZMod 2)).val = A' :=
  rfl

@[expose] noncomputable def tauBits (x : SixBits) : StatedSp 3 (ZMod 2) :=
  tauSym 3 (Multiplicative.ofAdd ⟨symMat x, symMat_transpose x⟩)

theorem coe_tauBits (x : SixBits) :
    ((tauBits x : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
      fromBlocks 1 (symMat x) 0 1 :=
  coe_tauSym _

@[expose] def wit₁ : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![1, 0, 0; 0, 0, 0; 0, 0, 0] !![0, 1, 0; 0, 0, 1; 0, 1, 0]
      !![0, 0, 0; 0, 0, 1; 0, 1, 0] !![1, 0, 0; 0, 0, 0; 1, 0, 0])
    (fromBlocks !![1, 0, 1; 0, 0, 0; 0, 0, 0] !![0, 0, 0; 1, 0, 1; 0, 1, 0]
      !![0, 0, 0; 0, 0, 1; 0, 1, 0] !![1, 0, 0; 0, 0, 0; 0, 0, 0])
    (by decide) (by decide) (by decide)

@[expose] def wit₂ : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![1, 0, 0; 0, 1, 0; 0, 1, 1] !![0, 0, 1; 0, 0, 0; 1, 0, 1]
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] !![1, 0, 0; 0, 1, 1; 0, 0, 1])
    (fromBlocks !![1, 0, 0; 0, 1, 0; 0, 1, 1] !![0, 0, 1; 0, 0, 0; 1, 0, 1]
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] !![1, 0, 0; 0, 1, 1; 0, 0, 1])
    (by decide) (by decide) (by decide)

@[expose] def sqrtAlt : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![1, 1, 0; 0, 1, 0; 0, 0, 1] !![0, 0, 0; 0, 0, 1; 1, 1, 0]
      !![0, 0, 0; 0, 0, 0; 0, 0, 0] !![1, 0, 0; 1, 1, 0; 0, 0, 1])
    (fromBlocks !![1, 1, 0; 0, 1, 0; 0, 0, 1] !![0, 0, 1; 0, 0, 1; 0, 1, 0]
      !![0, 0, 0; 0, 0, 0; 0, 0, 0] !![1, 0, 0; 1, 1, 0; 0, 0, 1])
    (by decide) (by decide) (by decide)

@[expose] def sqrtNonalt : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![1, 1, 0; 0, 1, 0; 0, 0, 1] !![0, 0, 0; 1, 1, 0; 0, 0, 0]
      !![0, 0, 0; 0, 0, 0; 0, 0, 0] !![1, 0, 0; 1, 1, 0; 0, 0, 1])
    (fromBlocks !![1, 1, 0; 0, 1, 0; 0, 0, 1] !![0, 1, 0; 0, 1, 0; 0, 0, 0]
      !![0, 0, 0; 0, 0, 0; 0, 0, 0] !![1, 0, 0; 1, 1, 0; 0, 0, 1])
    (by decide) (by decide) (by decide)

theorem wit₁_mem : wit₁ ∈ centralizer ({tauBits repOne} : Set (StatedSp 3 (ZMod 2))) := by
  rw [mem_centralizer_singleton_iff]
  apply statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_tauBits, wit₁,
    coe_spOfMat]
  decide

theorem wit₂_mem : wit₂ ∈ centralizer ({tauBits repOne} : Set (StatedSp 3 (ZMod 2))) := by
  rw [mem_centralizer_singleton_iff]
  apply statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_tauBits, wit₂,
    coe_spOfMat]
  decide

theorem commutator_wit : ⁅wit₁, wit₂⁆ = tauBits repOne := by
  apply statedSp_ext
  rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    Units.val_mul, Units.val_mul, Units.val_mul, coe_tauBits, wit₁, wit₂, coe_spOfMat_inv,
    coe_spOfMat_inv, coe_spOfMat, coe_spOfMat]
  decide

theorem sqrtAlt_sq : sqrtAlt ^ 2 = tauBits repAlt := by
  apply statedSp_ext
  rw [pow_two, Subgroup.coe_mul, Units.val_mul, coe_tauBits, sqrtAlt, coe_spOfMat]
  decide

theorem sqrtNonalt_sq : sqrtNonalt ^ 2 = tauBits repNonalt := by
  apply statedSp_ext
  rw [pow_two, Subgroup.coe_mul, Units.val_mul, coe_tauBits, sqrtNonalt, coe_spOfMat]
  decide

theorem tauSym_eq_conj {D : GL (Fin 3) (ZMod 2)} {x : SixBits} {B : binarySymMatrices 3}
    (h : (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) * symMat x * (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ =
      B) :
    tauSym 3 (Multiplicative.ofAdd B) = MulAut.conj (leviSp D) (tauBits x) := by
  rw [MulAut.conj_apply, tauBits, leviSp_mul_tauSym_mul_inv]
  congr 1
  exact congrArg Multiplicative.ofAdd (Subtype.ext h.symm)

abbrev symOf (x : SixBits) : binarySymMatrices 3 :=
  ⟨symMat x, symMat_transpose x⟩

theorem rank_repOne : (symMat repOne).rank = 1 :=
  (rank_symMat_eq_iff _ 1).2 (by decide +kernel)

theorem rank_repAlt : (symMat repAlt).rank = 2 :=
  (rank_symMat_eq_iff _ 2).2 (by decide +kernel)

theorem rank_repNonalt : (symMat repNonalt).rank = 2 :=
  (rank_symMat_eq_iff _ 2).2 (by decide +kernel)

theorem exists_commutator_tauSym_of_rank_one (B : binarySymMatrices 3)
    (hB : (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1) :
    ∃ g ∈ centralizer ({tauSym 3 (Multiplicative.ofAdd B)} : Set (StatedSp 3 (ZMod 2))),
      ∃ h ∈ centralizer ({tauSym 3 (Multiplicative.ofAdd B)} : Set (StatedSp 3 (ZMod 2))),
        ⁅g, h⁆ = tauSym 3 (Multiplicative.ofAdd B) := by
  obtain ⟨D, hD⟩ := (sym_congruent_iff (symOf repOne) B).2
    ⟨by rw [rank_repOne, hB], fun h => absurd h (by rw [rank_repOne]; omega)⟩
  rw [tauSym_eq_conj hD]
  exact exists_commutator_map _ ⟨wit₁, wit₁_mem, wit₂, wit₂_mem, commutator_wit⟩

theorem exists_sq_tauSym_of_rank_two (B : binarySymMatrices 3)
    (hB : (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2) :
    ∃ m ∈ centralizer ({tauSym 3 (Multiplicative.ofAdd B)} : Set (StatedSp 3 (ZMod 2))),
      m ^ 2 = tauSym 3 (Multiplicative.ofAdd B) := by
  by_cases ha : ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0
  · have hAlt : ∀ i, symMat repAlt i i = 0 := by decide
    obtain ⟨D, hD⟩ := (sym_congruent_iff (symOf repAlt) B).2
      ⟨by rw [rank_repAlt, hB], fun _ => ⟨fun _ => ha, fun _ => hAlt⟩⟩
    rw [tauSym_eq_conj hD]
    refine exists_sq_map _ ⟨sqrtAlt, ?_, sqrtAlt_sq⟩
    rw [← sqrtAlt_sq]
    exact mem_centralizer_singleton_iff.2 (pow_mul_comm' sqrtAlt 2).symm
  · have hNon : ¬ ∀ i, symMat repNonalt i i = 0 := by decide
    obtain ⟨D, hD⟩ := (sym_congruent_iff (symOf repNonalt) B).2
      ⟨by rw [rank_repNonalt, hB], fun _ => ⟨fun h => absurd h hNon, fun h => absurd h ha⟩⟩
    rw [tauSym_eq_conj hD]
    refine exists_sq_map _ ⟨sqrtNonalt, ?_, sqrtNonalt_sq⟩
    rw [← sqrtNonalt_sq]
    exact mem_centralizer_singleton_iff.2 (pow_mul_comm' sqrtNonalt 2).symm

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
