module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutWitCommon

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

namespace WitSp

open Matrix

section SpSix

def orderNineMat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks !![0, 0, 0; 1, 0, 0; 0, 1, 0] !![0, 0, 1; 0, 0, 0; 0, 0, 0]
    !![0, 0, 1; 0, 0, 0; 0, 0, 0] !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem orderNineMat_pow_nine : orderNineMat ^ 9 = 1 := by decide +kernel

theorem orderNineMat_pow_three : orderNineMat ^ 3 ≠ 1 := by decide +kernel

theorem orderNineMat_symplectic :
    orderNineMatᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *
      orderNineMat = fromBlocks 0 1 (-1) 0 := by
  decide +kernel

def orderNineGL : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨orderNineMat, orderNineMat ^ 8, by rw [← pow_succ']; exact orderNineMat_pow_nine,
    by rw [← pow_succ]; exact orderNineMat_pow_nine⟩

theorem orderOf_orderNineGL : orderOf orderNineGL = 9 := by
  have h3 : ¬orderNineGL ^ 3 ^ 1 = 1 := by
    intro h
    apply orderNineMat_pow_three
    have := congrArg Units.val h
    simpa [orderNineGL] using this
  have h9 : orderNineGL ^ 3 ^ (1 + 1) = 1 := by
    apply Units.ext
    have := orderNineMat_pow_nine
    simpa [orderNineGL] using this
  have := orderOf_eq_prime_pow (p := 3) h3 h9
  simpa using this

theorem orderNineGL_mem : orderNineGL ∈ StatedSp 3 (ZMod 2) :=
  StatedAPI.mem_statedSp_iff.2 orderNineMat_symplectic

end SpSix

section General

variable {K : Type} [Field K]

theorem exists_orderOf_eq_nine_statedSp_three [Finite K] (hK : Nat.card K = 2) :
    ∃ g : StatedSp 3 K, orderOf g = 9 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime hcard
  let φ : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hφ : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 3 ⊕ Fin 3) φ) :=
    Units.map_injective (fun _ _ h => Matrix.map_injective φ.injective h)
  refine ⟨⟨Matrix.GeneralLinearGroup.map φ orderNineGL,
    StatedAPI.map_mem_statedSp φ orderNineGL_mem⟩, ?_⟩
  rw [Subgroup.orderOf_mk, orderOf_injective _ hφ, orderOf_orderNineGL]

theorem exists_orderOf_eq_nine_statedSp [Finite K] (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n) :
    ∃ g : StatedSp n K, orderOf g = 9 := by
  obtain ⟨g, hg⟩ := exists_orderOf_eq_nine_statedSp_three hK
  refine ⟨CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbed (Fin.castLE hn)
    (Fin.castLE_injective hn) g, ?_⟩
  rw [orderOf_injective _ (CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbed_injective
    (Fin.castLE_injective hn)), hg]

end General

end WitSp

theorem exists_orderOf_eq_nine_psp_two {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSp n 2 1) : ∃ x : X, orderOf x = 9 := by
  obtain ⟨⟨-, -, hn, hne⟩, K, hKfield, hKfin, hcard, ⟨e⟩⟩ := h
  have h3 : 3 ≤ n := by
    by_contra h3
    have h2 : n = 2 := by omega
    exact hne (by rw [h2]; rfl)
  have hK : Nat.card K = 2 := by simpa using hcard
  obtain ⟨g, hg⟩ := WitSp.exists_orderOf_eq_nine_statedSp hK h3
  exact exists_orderOf_eq_of_equiv_statedProj hK e g hg

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
