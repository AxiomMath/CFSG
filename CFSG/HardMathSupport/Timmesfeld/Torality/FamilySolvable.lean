module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyOrder

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K] {ι : Type}

theorem familyCentralizer_le_normalizer_familyGroup (a : ι → Fin τ.rank → Kˣ) :
    familyCentralizer τ K a ≤ Subgroup.normalizer (familyGroup (K := K) a : Set (ModGL τ K)) := by
  intro g hg
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ K a hg
  exact mul_mem (Subgroup.le_normalizer hm) (canonicalRep_mem_normalizer_familyGroup hw)

theorem canonicalRep_mem_familyCentralizer {a : ι → Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : w ∈ familyStabilizer a) :
    canonicalRep (coxeterSystem τ) K w ∈ familyCentralizer τ K a :=
  mem_familyCentralizer.2 ⟨canonicalRep_mem_adjointGroup _ K w,
    fun i => (conj_canonicalRep_eq_iff (a i) w).2 (hw i)⟩

theorem isSolvable_of_le_familyCentralizer (a : ι → Fin τ.rank → Kˣ)
    [Group.IsSolvable (familyStabilizerSubgroup a)] {Q : Subgroup (ModGL τ K)}
    (hQ : Q ≤ familyCentralizer τ K a) [Group.IsSolvable ↥(Q ⊓ familyGroup (K := K) a)] :
    Group.IsSolvable Q := by
  classical
  set F := familyCentralizer τ K a with hF
  set M := familyGroup (K := K) a with hM
  have hMF : M ≤ F := familyGroup_le_familyCentralizer a
  have : (M.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMF).2
      (familyCentralizer_le_normalizer_familyGroup a)
  have hone : ∀ m : F, (m : ModGL τ K) ∈ M → (QuotientGroup.mk m : F ⧸ M.subgroupOf F) = 1 :=
    fun m hm => (QuotientGroup.eq_one_iff m).2 (Subgroup.mem_subgroupOf.2 hm)
  let θ : familyStabilizerSubgroup a →* F ⧸ M.subgroupOf F :=
    { toFun := fun w => QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) K w,
        canonicalRep_mem_familyCentralizer (mem_familyStabilizerSubgroup.1 w.2)⟩
      map_one' := by
        refine hone _ ?_
        change canonicalRep (coxeterSystem τ) K 1 ∈ M
        rw [canonicalRep_one]
        exact one_mem M
      map_mul' := by
        intro w w'
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := K) (w : WeylGroup τ) w'
        have hkF : k ∈ F := hMF (Subgroup.mem_sup_left hk)
        have h1 : (QuotientGroup.mk ⟨k, hkF⟩ : F ⧸ M.subgroupOf F) = 1 :=
          hone _ (Subgroup.mem_sup_left hk)
        change (QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) K ((w : WeylGroup τ) * w'), _⟩ :
            F ⧸ M.subgroupOf F) = QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) K w, _⟩ *
          QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) K w', _⟩
        rw [← QuotientGroup.mk_mul, ← one_mul (QuotientGroup.mk _ : F ⧸ M.subgroupOf F), ← h1,
          ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext hkk.symm }
  have hθ : Function.Surjective θ := by
    intro x
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ K a hg
    refine ⟨⟨w, mem_familyStabilizerSubgroup.2 hw⟩, ?_⟩
    have hmF : m ∈ F := hMF hm
    have hnF : canonicalRep (coxeterSystem τ) K w ∈ F := canonicalRep_mem_familyCentralizer hw
    change (QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) K w, _⟩ : F ⧸ M.subgroupOf F) =
      QuotientGroup.mk ⟨m * canonicalRep (coxeterSystem τ) K w, hg⟩
    have e : (⟨m * canonicalRep (coxeterSystem τ) K w, hg⟩ : F) =
        ⟨m, hmF⟩ * ⟨canonicalRep (coxeterSystem τ) K w, hnF⟩ := rfl
    rw [e, QuotientGroup.mk_mul, hone ⟨m, hmF⟩ hm, one_mul]
  have : Group.IsSolvable (F ⧸ M.subgroupOf F) := solvable_of_surjective hθ
  let g : Q →* F ⧸ M.subgroupOf F := (QuotientGroup.mk' _).comp (Subgroup.inclusion hQ)
  refine solvable_of_ker_le_range (Subgroup.inclusion (inf_le_left : Q ⊓ M ≤ Q)) g
    fun x hx => ?_
  have hxM : (x : ModGL τ K) ∈ M := by
    have h := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
    exact Subgroup.mem_subgroupOf.1 h
  exact ⟨⟨x, x.2, hxM⟩, rfl⟩

end CFSG.HardMathSupport.Timmesfeld.Torality
