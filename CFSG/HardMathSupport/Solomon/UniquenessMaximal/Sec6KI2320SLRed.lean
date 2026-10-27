module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Red
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320L
public import CFSG.Quasithin.Background.P4SL34Core

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts.L34

local notation "conjAut'" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
local notation "slConj" => CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation

variable {k : Type} [Field k]

theorem descend_conj (g : SpecialLinearGroup (Fin 3) k) :
    descendAut 3 k (MulAut.conj g) = MulAut.conj (proj 3 k g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective 3 k x
  rw [descendAut_proj]
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem descend_slConj (B : GL (Fin 3) k) : descendAut 3 k (slConj 3 k B) = conjAut' 3 k B := rfl

theorem isElemAbelian_map_hom {G H : Type*} [Group G] [Group H] (f : G →* H) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) : CFSG.Open.IsElemAbelian 3 (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', haa⟩ := a.2
    obtain ⟨b', hb', hbb⟩ := b.2
    apply Subtype.ext
    have hc : a' * b' = b' * a' :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨a', ha'⟩ : E) ⟨b', hb'⟩)
    show (a : H) * (b : H) = (b : H) * (a : H)
    rw [← haa, ← hbb, ← map_mul, ← map_mul, hc]
  · rintro _ ⟨y, hy, rfl⟩
    show f y ^ 3 = 1
    rw [← map_pow, hE.2 y hy, map_one]

theorem map_conj_inv_cancel {G : Type*} [Group G] (B : Subgroup G) (c : G) :
    (B.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = B := by
  rw [Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : ((MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom) y = y := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem exists_lift (hk : Nat.card k = 4) {A : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k))}
    (hA : CFSG.Open.IsElemAbelian 3 A) (h9 : Nat.card A = 9)
    (hinn : ¬ A ≤ (MulAut.conj : SpecialLinearGroup (Fin 3) k →*
      MulAut (SpecialLinearGroup (Fin 3) k)).range) :
    ∃ (u : kˣ) (_ : u ≠ 1) (g : GL (Fin 3) k) (i : Fin 4), (i = 0 ∨ i = 2) ∧
      ∃ M' : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k)),
        M'.map (descendAut 3 k) = pglSylowMax u i ∧
        A = M'.map (MulAut.congr (slConj 3 k g)).toMonoidHom := by
  have hDinj : Function.Injective (descendAut 3 k) :=
    CFSG.Quasithin.G11.P4SL34.descendAut_injective k
  have hAbar : CFSG.Open.IsElemAbelian 3 (A.map (descendAut 3 k)) :=
    isElemAbelian_map_hom _ hA
  have h9bar : Nat.card (A.map (descendAut 3 k)) = 9 := by
    rw [Subgroup.card_map_of_injective hDinj, h9]
  have hinnbar : ¬ A.map (descendAut 3 k) ≤
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
    intro hle
    apply hinn
    intro a ha
    obtain ⟨p, hp⟩ := hle ⟨a, ha, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective 3 k p
    refine ⟨g, hDinj ?_⟩
    rw [descend_conj]
    exact hp
  obtain ⟨u, hu, g, i, hi, hAeq⟩ := exists_conj_pglSylowMax hk hAbar h9bar hinnbar
  refine ⟨u, hu, g, i, hi, A.map (MulAut.conj (slConj 3 k g)⁻¹).toMonoidHom, ?_, ?_⟩
  · have hcomp : (descendAut 3 k).comp (MulAut.conj (slConj 3 k g)⁻¹).toMonoidHom =
        (MulAut.conj (conjAut' 3 k g)⁻¹).toMonoidHom.comp (descendAut 3 k) := by
      ext a x
      simp [map_mul, map_inv, descend_slConj]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hAeq, ← map_inv]
    exact map_conj_inv_cancel _ _
  · rw [Subgroup.map_map]
    ext a
    constructor
    · intro ha
      refine ⟨a, ha, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        congr_apply_eq]
      group
    · rintro ⟨b, hb, rfl⟩
      have : ((MulAut.congr (slConj 3 k g)).toMonoidHom.comp
          (MulAut.conj (slConj 3 k g)⁻¹).toMonoidHom) b = b := by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          congr_apply_eq]
        group
      rw [this]
      exact hb

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
