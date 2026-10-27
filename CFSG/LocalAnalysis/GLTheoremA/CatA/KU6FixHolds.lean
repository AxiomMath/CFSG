module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6FixNine
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KU6Fix

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6 CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem fixComp_S6 (A : Subgroup (MulAut S6)) (hA : IsElemAbelian 3 A) (hcard : 3 ^ 3 ≤ Nat.card A)
    (T : Subgroup S6) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hAT : ∀ α ∈ A, ∀ x ∈ T, α x ∈ T)
    (α : MulAut S6) (hα : α ∈ A) (hα1 : α ≠ 1) {N : Subgroup S6}
    (hN : GLAPComponent 3 (fixSubgroup α) N) :
    catalogIs (PSimple 3 N) (fun i => S9.isU4two i ∨ S9.isU5two i) := by
  haveI := isSimple_S6
  obtain ⟨B, hB, ⟨c, hBc⟩, hβB⟩ := exists_unitary_of_pow_three α (hA.2 α hα)
  by_cases hsc : ∃ c : F4ˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 6) c
  · exfalso
    apply hα1
    obtain ⟨c₀, hc₀⟩ := hsc
    ext x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.one_apply]
    refine hβB u u ?_
    rw [hc₀, ← (commute_scalar c₀ (u : GL (Fin 6) F4)).eq, mul_inv_cancel_right]
  · obtain ⟨J, hJ, ⟨e⟩⟩ := exists_component_transfer α ⟨B, hB⟩ hβB hN
    refine HSubT.catalogIs_of_mulEquiv e.symm ?_
    by_cases h3B : (B : GL (Fin 6) F4) ^ 3 = 1
    · exact HSubT.typed_cube_one ⟨B, hB⟩ (Subtype.ext h3B) hsc hJ
    · have hc1 : c ≠ 1 := fun h => h3B (by rw [hBc, h, map_one])
      have hBA : Psi0 ⟨B, hB⟩ ∈ A := by
        rw [Psi0_eq_of α ⟨B, hB⟩ hβB]
        exact hα
      exact (false_of_nine A hA hcard T hT hT1 hAT ⟨B, hB⟩ hc1 hBc hBA).elim

private theorem isU6two_of_isU6n_one (i : TauCeti.CFSGIndex) (h : S10.isU6n 1 i) :
    S9.isU6two i := by
  cases i with
  | cyclic p hp => simp [S10.isU6n, onLie] at h
  | alternating n hn => simp [S10.isU6n, onLie] at h
  | sporadic s => simp [S10.isU6n, onLie] at h
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r <;> simp [S10.isU6n, onLie] at h
      show q.card = 2
      rw [TauCeti.PrimePower.card_def, h.1, h.2, pow_one]
    | _ => simp [S10.isU6n, onLie] at h

private theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (f : G →* H) : IsElemAbelian 3 (E.map f) := by
  obtain ⟨hc', hp'⟩ := hE
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', hae⟩ := a.2
    obtain ⟨b', hb', hbe⟩ := b.2
    have h1 := congrArg Subtype.val (hc'.is_comm.comm (⟨a', ha'⟩ : E) ⟨b', hb'⟩)
    change (a : H) * b = b * a
    rw [← hae, ← hbe, ← map_mul, ← map_mul]
    exact congrArg f h1
  · obtain ⟨x', hx', rfl⟩ := hx
    rw [← map_pow, hp' x' hx', map_one]

theorem fixComp_of_catalogIs (S : Type) [Group S] [Finite S] (hS : catalogIs S (S10.isU6n 1))
    (A : Subgroup (MulAut S)) (T : Subgroup S) (hA : IsElemAbelian 3 A) (hcard : 3 ^ 3 ≤ Nat.card A)
    (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hAT : ∀ α ∈ A, ∀ x ∈ T, α x ∈ T)
    (α : MulAut S) (hα : α ∈ A) (hα1 : α ≠ 1) (N : Subgroup S)
    (hN : GLAPComponent 3 (fixSubgroup α) N) :
    catalogIs (PSimple 3 N) (fun i => S9.isU4two i ∨ S9.isU5two i) := by
  have hS6 : catalogIs S S9.isU6two := by
    obtain ⟨i, hi, he⟩ := hS
    exact ⟨i, isU6two_of_isU6n_one i hi, he⟩
  obtain ⟨e⟩ := HSubT.nonempty_S6_of_isU6two hS6
  have hA₆ : IsElemAbelian 3 (A.map (autTr e)) := isElemAbelian_map hA (autTr e)
  have hcard₆ : 3 ^ 3 ≤ Nat.card (A.map (autTr e)) := by
    rw [Subgroup.card_map_of_injective (autTr_injective e)]
    exact hcard
  have hT₆ : IsPGroup 2 (T.map e.toMonoidHom) := hT.map _
  have hT₆1 : T.map e.toMonoidHom ≠ ⊥ := fun h =>
    hT1 ((Subgroup.map_eq_bot_iff_of_injective T e.injective).1 h)
  have hAT₆ : ∀ β ∈ A.map (autTr e), ∀ y ∈ T.map e.toMonoidHom, β y ∈ T.map e.toMonoidHom := by
    rintro _ ⟨β, hβ, rfl⟩ _ ⟨x, hx, rfl⟩
    refine ⟨β x, hAT β hβ x hx, ?_⟩
    rw [autTr_apply]
    simp
  have hα₆ : autTr e α ∈ A.map (autTr e) := ⟨α, hα, rfl⟩
  have hα₆1 : autTr e α ≠ 1 := fun h => hα1 (autTr_injective e (h.trans (map_one (autTr e)).symm))
  have hfix : (fixSubgroup α).map e.toMonoidHom = fixSubgroup (autTr e α) := by
    ext y
    rw [Subgroup.mem_map_equiv, mem_fixSubgroup, mem_fixSubgroup, autTr_apply]
    constructor
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
    · intro h
      have h1 := congrArg e.symm h
      simpa using h1
  have hN₆ : GLAPComponent 3 (fixSubgroup (autTr e α)) (N.map e.toMonoidHom) := by
    rw [← hfix]
    exact glaPComponent_map_mulEquiv Nat.prime_three e hN
  have h6 := fixComp_S6 _ hA₆ hcard₆ _ hT₆ hT₆1 hAT₆ _ hα₆ hα₆1 hN₆
  exact (T123C.catalogIs_pSimple_map_iff (f := e.toMonoidHom) e.injective 3 N _).1 h6

end CFSG.LocalAnalysis.GLTheoremA.KU6Fix

namespace CFSG.LocalAnalysis.GLTheoremA

theorem kU6FixCompFact_holds : KU6FixCompFact := by
  intro S _ _ hS A T hA hcard hT hT1 hAT α hα hα1 N hN
  exact KU6Fix.fixComp_of_catalogIs S hS A T hA hcard hT hT1 hAT α hα hα1 N hN

end CFSG.LocalAnalysis.GLTheoremA

end
