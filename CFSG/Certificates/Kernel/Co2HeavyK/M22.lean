module

public import CFSG.Certificates.Kernel.Co2InvS.Mat
public import CFSG.Sporadic.Co2M22
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Mathieu.M22
public import Certificates.Data.CFSGNative.Co2Heavy.Core
public import Certificates.Data.Kernel.Co2HeavyK

public section

namespace CFSG.KC.Co2HeavyK

open CFSG.KC.Co2InvS CFSG.KC.Co1F2 CFSG.Sporadic.Co2Inv CFSG.Sporadic.Co2Heavy
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert CFSG.KC.Loop CFSG.Blueprint CFSG.Sporadic.SmallF2

theorem m22RelsK_eq : TauCeti.SporadicName.M22.presentation.relatorLetters = m22RelsK := by
  have e : TauCeti.SporadicName.M22.presentation = TauCeti.Sporadic.m22Presentation := rfl
  rw [e, TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.m22Presentation_transcribed]
  simp [FreeGroup.invRev, m22RelsK]

theorem unpack_letterP (A B Ai Bi : ℕ) (l : ℕ × Bool) :
    unpackR 22 (letterP A B Ai Bi l) = (if l.1 = 0 then
      (if l.2 then unpackR 22 A else unpackR 22 Ai) else
      (if l.2 then unpackR 22 B else unpackR 22 Bi)) := by
  obtain ⟨i, s⟩ := l
  unfold letterP
  by_cases hi : i = 0
  · subst hi
    cases s <;> rfl
  · rw [beq_false hi]
    cases s <;> simp only [selN_eq, hi, if_false, if_true, Bool.false_eq_true]

theorem wordP_cons (A B Ai Bi : ℕ) (l : ℕ × Bool) (w : List (ℕ × Bool)) (acc : ℕ) :
    wordP A B Ai Bi (l :: w) acc = wordP A B Ai Bi w (mulV acc (letterP A B Ai Bi l)) :=
  strictN_eq' _ _

theorem unpack_wordP (A B Ai Bi : ℕ) (w : List (ℕ × Bool)) :
    ∀ acc, unpackR 22 (wordP A B Ai Bi w acc) =
      w.foldl (fun acc l => mulRows 22 acc (if l.1 = 0 then
        (if l.2 then unpackR 22 A else unpackR 22 Ai) else
        (if l.2 then unpackR 22 B else unpackR 22 Bi))) (unpackR 22 acc) := by
  induction w with
  | nil => intro acc; rfl
  | cons l w ih =>
    intro acc
    rw [wordP_cons, ih, List.foldl_cons, ← mulRows_unpack, unpack_letterP]

theorem wordRows_unpack (A B Ai Bi : ℕ) (w : List (ℕ × Bool)) :
    wordRows (unpackR 22 A) (unpackR 22 B) (unpackR 22 Ai) (unpackR 22 Bi) w =
      unpackR 22 (wordP A B Ai Bi w IDP) := by
  rw [unpack_wordP, ← idRows_eq]
  rfl

theorem exists_m22_of_rows
    {T : Set NativeSporadic.Co2} {A B Ai Bi : Array ℕ}
    (hA : rowCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable A = true)
    (hB : rowCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable B = true)
    (hAi : mulRows 22 A Ai = idRows 22) (hBi : mulRows 22 B Bi = idRows 22)
    (hB1 : B ≠ idRows 22)
    (hrel : ∀ v ∈ TauCeti.SporadicName.M22.presentation.relatorLetters,
      wordRows A B Ai Bi v = idRows 22)
    (hnA : ∀ x : NativeSporadic.Co2, x.val.val = rowsMatrix 22 A → ∀ s ∈ T, x * s * x⁻¹ ∈ T)
    (hnB : ∀ x : NativeSporadic.Co2, x.val.val = rowsMatrix 22 B → ∀ s ∈ T, x * s * x⁻¹ ∈ T) :
    ∃ H : Subgroup NativeSporadic.Co2,
      H ≤ Subgroup.normalizer ((Subgroup.closure T : Subgroup NativeSporadic.Co2) :
          Set NativeSporadic.Co2) ∧
      IsSimpleGroup H ∧ ¬ IsMulCommutative H ∧ Nat.card H = 443520 := by
  obtain ⟨a, ha⟩ := m22_exists_elt hA
  obtain ⟨b, hb⟩ := m22_exists_elt hB
  have hai := m22_val_inv ha hAi
  have hbi := m22_val_inv hb hBi
  have hb1 : b ≠ 1 := by
    intro hb1
    apply hB1
    apply eq_of_rowsMatrix_eq (m22_rowCheck_wf hB) wfRows_idRows
    rw [← hb, hb1, val_val_one, CFSG.Sporadic.SmallF2.rowsMatrix_idRows]
  have hrel' : ∀ v ∈ TauCeti.SporadicName.M22.presentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 a b) v = 1 := by
    intro v hv
    apply eq_of_val_val
    rw [m22_wordRows_val ha hb hai hbi v, hrel v hv, CFSG.Sporadic.SmallF2.rowsMatrix_idRows,
      val_val_one]
  have hgen : 1 < TauCeti.SporadicName.M22.presentation.generatorCount := by
    rw [m22_generatorCount]
    norm_num
  obtain ⟨φ, hφ⟩ : ∃ φ : TauCeti.SporadicName.M22.Group →* NativeSporadic.Co2,
      ∀ i < TauCeti.SporadicName.M22.presentation.generatorCount,
        φ (CFSG.Sporadic.Bridge.presGen TauCeti.SporadicName.M22.presentation i) =
          CFSG.Sporadic.Bridge.TwoGen.img2 a b i :=
    ⟨CFSG.Sporadic.Bridge.presHom _ _ hrel', fun i hi =>
      CFSG.Sporadic.Bridge.presHom_presGen _ _ hrel' hi⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have hsimpleM : IsSimpleGroup NativeSporadic.M22 :=
    (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  have hsimpleP : IsSimpleGroup TauCeti.SporadicName.M22.Group := e.symm.isSimpleGroup
  have hcardP : Nat.card TauCeti.SporadicName.M22.Group = 443520 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  have hinj : Function.Injective φ := by
    refine m22_injective_of_ne_one φ
      (x := CFSG.Sporadic.Bridge.presGen TauCeti.SporadicName.M22.presentation 1) ?_
    rw [hφ 1 hgen]
    simpa [CFSG.Sporadic.Bridge.TwoGen.img2] using hb1
  obtain ⟨hsimpleH, hncomm, hcardH⟩ := m22_range_facts hcardP (by norm_num) hinj
  have haN := m22_mem_normalizer (S := T) (hnA a ha)
  have hbN := m22_mem_normalizer (S := T) (hnB b hb)
  refine ⟨φ.range, ?_, hsimpleH, hncomm, hcardH⟩
  refine m22_range_le φ m22_closure_presGen ?_
  rintro t (rfl | rfl)
  · rw [hφ 0 (by omega)]
    simpa [CFSG.Sporadic.Bridge.TwoGen.img2] using haN
  · rw [hφ 1 hgen]
    simpa [CFSG.Sporadic.Bridge.TwoGen.img2] using hbN

end CFSG.KC.Co2HeavyK

end
