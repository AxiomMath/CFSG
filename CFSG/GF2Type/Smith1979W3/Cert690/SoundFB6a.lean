module

public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB1
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 Module

def SpanInv (B : Array ℕ) : Prop :=
  B.toList.Nodup ∧ (∀ a ∈ B.toList, ∀ b ∈ B.toList, a ^^^ b ∈ B.toList) ∧
    ∀ b ∈ B.toList, b < 64

theorem spanInv_zero : SpanInv #[0] := by
  refine ⟨by simp, ?_, ?_⟩
  · intro a ha b hb
    simp only [List.mem_singleton] at ha hb
    subst ha; subst hb
    simp
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    norm_num

theorem spanInv_step {B : Array ℕ} (hB : SpanInv B) {x : ℕ} (hxlt : x < 64) :
    SpanInv (spanStep B x) := by
  rcases hB with ⟨hnd, hcl, hlt⟩
  by_cases hx : B.contains x = true
  · have hmem : x ∈ B.toList :=
      Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hx)
    have hxB : SpanInv B := ⟨hnd, hcl, hlt⟩
    rw [spanStep, if_pos hx]
    exact hxB
  · have hxfalse : B.contains x = false := by simpa using hx
    have hxnot : x ∉ B.toList := by
      intro hmem
      have hc : B.contains x = true :=
        Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hmem)
      rw [hc] at hxfalse
      exact Bool.noConfusion hxfalse
    have hinj : Function.Injective (fun y : ℕ => y ^^^ x) := by
      intro a b h
      simpa [Nat.xor_assoc, Nat.xor_left_comm, Nat.xor_comm] using
        congrArg (fun z => z ^^^ x) h
    have hmapnd : (B.map (fun y => y ^^^ x)).toList.Nodup := by
      rw [Array.toList_map]
      exact List.Nodup.map hinj hnd
    have hdisj : ∀ a ∈ B.toList, a ∉ (B.map (fun y => y ^^^ x)).toList := by
      intro a ha hb
      rw [Array.toList_map] at hb
      obtain ⟨b, hb, hba⟩ := List.mem_map.mp hb
      have hxeq : x = a ^^^ b := by
        calc x = (b ^^^ x) ^^^ b := by
              simp [Nat.xor_assoc, Nat.xor_left_comm, Nat.xor_comm]
          _ = a ^^^ b := by rw [hba]
      exact hxnot (hxeq ▸ hcl a ha b hb)
    have hnd' : (B.toList ++ (B.map (fun y => y ^^^ x)).toList).Nodup :=
      hnd.append hmapnd hdisj
    have hcl' : ∀ a ∈ (spanStep B x).toList, ∀ b ∈ (spanStep B x).toList,
        a ^^^ b ∈ (spanStep B x).toList := by
      intro a ha b hb
      rw [spanStep, if_neg hx, Array.toList_append, Array.toList_map] at ha hb ⊢
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp hb with hb | hb
        · exact List.mem_append_left _ (hcl a ha b hb)
        · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
          rw [show a ^^^ (b0 ^^^ x) = (a ^^^ b0) ^^^ x by
            simp [Nat.xor_assoc, Nat.xor_left_comm, Nat.xor_comm]]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨a ^^^ b0, hcl a ha b0 hb0, rfl⟩)
      · obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
        rcases List.mem_append.mp hb with hb | hb
        · rw [show (a0 ^^^ x) ^^^ b = (a0 ^^^ b) ^^^ x by
            simp [Nat.xor_assoc, Nat.xor_left_comm, Nat.xor_comm]]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨a0 ^^^ b, hcl a0 ha0 b hb, rfl⟩)
        · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
          rw [show (a0 ^^^ x) ^^^ (b0 ^^^ x) = a0 ^^^ b0 by
            simp [Nat.xor_assoc, Nat.xor_left_comm, Nat.xor_comm]]
          exact List.mem_append_left _ (hcl a0 ha0 b0 hb0)
    have hlt' : ∀ b ∈ (spanStep B x).toList, b < 64 := by
      intro b hb
      rw [spanStep, if_neg hx, Array.toList_append, Array.toList_map] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hlt b hb
      · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
        exact Nat.xor_lt_two_pow (n := 6) (by simpa using hlt b0 hb0) (by simpa using hxlt)
    refine ⟨?_, ?_, hlt'⟩
    · have hxmem : ¬ x ∈ B := fun hmem => hx (Array.contains_iff_mem.mpr hmem)
      rw [spanStep, if_neg hx, Array.toList_append, Array.toList_map]
      simpa only [Array.toList_map] using hnd'
    · exact hcl'

theorem foldl_spanStep_spanInv (S : List ℕ) (hS : ∀ x ∈ S, x < 64) (B : Array ℕ)
    (hB : SpanInv B) : SpanInv (S.foldl spanStep B) := by
  induction S generalizing B with
  | nil => simpa using hB
  | cons x S ih =>
    have hxlt : x < 64 := hS x (by simp)
    have hS' : ∀ y ∈ S, y < 64 := fun y hy => hS y (by simp [hy])
    simpa [List.foldl_cons] using ih hS' (spanStep B x) (spanInv_step hB hxlt)

theorem spanArr_spanInv (S : List ℕ) (hS : ∀ x ∈ S, x < 64) : SpanInv (spanArr S) := by
  rw [spanArr_eq_foldl]
  exact foldl_spanStep_spanInv S hS #[0] spanInv_zero

theorem spanArr_nodup (S : List ℕ) (hS : ∀ x ∈ S, x < 64) :
    (spanArr S).toList.Nodup :=
  (spanArr_spanInv S hS).1

theorem spanArr_closed (S : List ℕ) (hS : ∀ x ∈ S, x < 64) :
    ∀ a ∈ (spanArr S).toList, ∀ b ∈ (spanArr S).toList, a ^^^ b ∈ (spanArr S).toList :=
  (spanArr_spanInv S hS).2.1

theorem spanArr_lt (S : List ℕ) (hS : ∀ x ∈ S, x < 64) :
    ∀ b ∈ (spanArr S).toList, b < 64 :=
  (spanArr_spanInv S hS).2.2

theorem spanOfList_eq_of_sameSet {B : Array ℕ} {L : List ℕ}
    (h : sameSet B L = true) : spanOfList B.toList = spanOfList L := by
  apply spanOfList_eq_of_mem_iff
  intro x
  simp only [sameSet, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Array.all_eq_true] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  have h2' : ∀ i (hi : i < B.size), L.contains (B[i]'hi) = true := h2
  constructor
  · intro hx
    rw [Array.mem_toList_iff] at hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    exact List.contains_iff_mem.mp (h2' i hi)
  · intro hx
    exact Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp (h1 x hx))


theorem natCard_fixed_filter {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    {w : V₀ ≃ₗ[ZMod 2] V₀} (hw : w ∈ KPGL) :
    Nat.card {v : V₀ // w v = v} =
      ((List.range 64).filter (fun n => Code.act (hK.code w) n == n)).length := by
  classical
  let P : ℕ → Bool := fun n => Code.act (hK.code w) n == n
  have hsub : Nat.card {v : V₀ // w v = v} =
      Nat.card {n : ℕ // n < 64 ∧ P n = true} := by
    apply Nat.card_congr
    refine
      { toFun := fun v =>
          ⟨Classical.choose (exists_vec v.1),
            (Classical.choose_spec (exists_vec v.1)).1, ?_⟩
        invFun := fun n => ⟨Code.vec n.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hn := (Classical.choose_spec (exists_vec v.1))
      have hv : w (Code.vec (Classical.choose (exists_vec v.1))) =
          Code.vec (Classical.choose (exists_vec v.1)) := by
        rw [hn.2]; exact v.2
      rw [apply_vec_of_hasCode (hK.hasCode_code hw) (Classical.choose (exists_vec v.1))] at hv
      have hfix : Code.act (hK.code w) (Classical.choose (exists_vec v.1)) =
          Classical.choose (exists_vec v.1) := by
        apply vec_injective_of_lt
        · exact Code.act_lt _ _
        · exact hn.1
        · exact hv
      simp only [P, beq_iff_eq]
      exact hfix
    · have hv : w (Code.vec n.1) = Code.vec n.1 := by
        rw [apply_vec_of_hasCode (hK.hasCode_code hw) n.1]
        have h := n.2.2
        simp only [P, beq_iff_eq] at h
        rw [h]
      exact hv
    · intro v
      apply Subtype.ext
      exact (Classical.choose_spec (exists_vec v.1)).2
    · intro n
      apply Subtype.ext
      apply vec_injective_of_lt
      · exact (Classical.choose_spec (exists_vec (Code.vec n.1))).1
      · exact n.2.1
      · exact (Classical.choose_spec (exists_vec (Code.vec n.1))).2
  have hcount : Nat.card {n : ℕ // n < 64 ∧ P n = true} =
      ((List.range 64).filter P).length := by
    let e : {n : ℕ // n < 64 ∧ P n = true} ≃
        {n : ℕ // n ∈ (List.range 64).filter P} :=
      { toFun := fun n => ⟨n.1, List.mem_filter.mpr ⟨List.mem_range.mpr n.2.1, n.2.2⟩⟩
        invFun := fun n => ⟨n.1, ⟨List.mem_range.mp (List.mem_filter.mp n.2).1,
          (List.mem_filter.mp n.2).2⟩⟩
        left_inv := fun n => by apply Subtype.ext; rfl
        right_inv := fun n => by apply Subtype.ext; rfl }
    rw [Nat.card_congr e]
    rw [Nat.card_congr (List.Nodup.getEquiv ((List.range 64).filter P)
      (List.nodup_range.filter P)).symm]
    simp
  rw [hsub, hcount]

theorem natCard_centralizer_filter {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    {w : V₀ ≃ₗ[ZMod 2] V₀} (hw : w ∈ KPGL) :
    Nat.card ↥(KPGL ⊓ Subgroup.centralizer {w}) =
      (D.elems.filter (fun k => Code.mul k (hK.code w) == Code.mul (hK.code w) k)).size := by
  classical
  let c := hK.code w
  let P : ℕ → Bool := fun k => Code.mul k c == Code.mul c k
  have hKmem : (KPGL ⊓ Subgroup.centralizer {w}) ≤ KPGL := inf_le_left
  have hequiv : Nat.card ↥(KPGL ⊓ Subgroup.centralizer {w}) =
      Nat.card {g : KPGL // P (hK.code g) = true} := by
    apply Nat.card_congr
    refine
      { toFun := fun x =>
          ⟨⟨x.1, x.2.1⟩, ?_⟩
        invFun := fun g =>
          ⟨g.1.1, ⟨g.1.2, ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx : x.1 ∈ Subgroup.centralizer ({w} : Set (V₀ ≃ₗ[ZMod 2] V₀)) := x.2.2
      have hcomm : w * x.1 = x.1 * w := Subgroup.mem_centralizer_iff.mp hx w (by simp)
      have hcode : Code.mul (hK.code x.1) c = Code.mul c (hK.code x.1) := by
        have h1 : hK.code (x.1 * w) = Code.mul (hK.code x.1) c :=
          hK.code_mul x.2.1 hw
        have h2 : hK.code (w * x.1) = Code.mul c (hK.code x.1) :=
          hK.code_mul hw x.2.1
        rw [← h1, ← h2, hcomm]
      simp only [P, beq_iff_eq]
      exact hcode
    · have hg : g.1.1 ∈ Subgroup.centralizer ({w} : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hh' : h = w := by simpa using hh
        subst h
        have hcode := g.2
        simp only [P, beq_iff_eq] at hcode
        have h1 : hK.code (g.1.1 * w) = Code.mul (hK.code g.1.1) c :=
          hK.code_mul g.1.2 hw
        have h2 : hK.code (w * g.1.1) = Code.mul c (hK.code g.1.1) :=
          hK.code_mul hw g.1.2
        have hmul : g.1.1 * w = w * g.1.1 := by
          apply hK.eq_of_code_eq
          · exact Subgroup.mul_mem (H := KPGL) g.1.2 hw
          · exact Subgroup.mul_mem (H := KPGL) hw g.1.2
          · rw [h1, h2]
            exact hcode
        exact hmul.symm
      exact hg
    · intro x
      apply Subtype.ext
      rfl
    · intro g
      apply Subtype.ext
      rfl
  rw [hequiv]
  change Nat.card {g : codeSubgroup kPGLGens // P (hK.code g) = true} =
    (D.elems.filter (fun k => Code.mul k (hK.code w) == Code.mul (hK.code w) k)).size
  have hfilter := hK.natCard_filter P
  rw [hfilter]
  rw [← Array.length_toList, Array.toList_filter]

end CFSG.GF2Type.Smith1979W3.Cert690
