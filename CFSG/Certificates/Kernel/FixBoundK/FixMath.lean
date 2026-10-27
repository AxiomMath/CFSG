module

public import CFSG.Certificates.Kernel.FixBoundK.Conj
public import Certificates.Data.Kernel.FixBoundK.Fix
public import CFSG.Quasithin.Background.HMathieuMask

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.FixBoundK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Quasithin.H.Mathieu

theorem withN_eq {α : Type} (y : Nat) (k : Nat → α) : withN y k = k y := by
  cases y <;> rfl

theorem nIf_eq (b : Bool) (t e : Nat) : nIf(b, t, e) = if b then t else e := by
  cases b <;> rfl

theorem bitS_eq (x : Nat) : bitS x = decide (x % 2 = 1) := by
  change Nat.beq (x &&& 1) 1 = _
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> decide

theorem shiftRight_one (x : Nat) : Nat.shiftRight x 1 = x / 2 := by
  have h := Nat.shiftRight_eq_div_pow x 1
  rw [pow_one] at h
  exact h

theorem actM_zero : ∀ cs : List Nat, actM cs 0 = 0
  | [] => rfl
  | c :: cs => by
    rw [actM, actM_zero cs]
    simp

theorem actS_eq : ∀ (cs : List Nat) (x : Nat), actS cs x = actM cs x
  | [], _ => rfl
  | c :: cs, x => by
    have e : actS (c :: cs) x = nIf(Nat.beq x 0, 0,
        Nat.xor (nIf(bitS x, c, 0)) (actS cs (Nat.shiftRight x 1))) := rfl
    rw [e, actS_eq cs, actM]
    cases hb : Nat.beq x 0
    · change Nat.xor (nIf(bitS x, c, 0)) (actM cs (Nat.shiftRight x 1)) = _
      rw [nIf_eq, bitS_eq, shiftRight_one]
      simp only [decide_eq_true_eq]
      rfl
    · have hx : x = 0 := Nat.eq_of_beq_eq_true hb
      subst hx
      change (0 : Nat) = _
      simp [actM_zero]

theorem permS_eq : ∀ (g : List Nat) (x : Nat), permS g x = actM (g.map (2 ^ ·)) x
  | [], _ => rfl
  | a :: g, x => by
    have e : permS (a :: g) x = nIf(Nat.beq x 0, 0,
        Nat.xor (nIf(bitS x, Nat.shiftLeft 1 a, 0)) (permS g (Nat.shiftRight x 1))) := rfl
    rw [e, permS_eq g, List.map_cons, actM]
    cases hb : Nat.beq x 0
    · change Nat.xor (nIf(bitS x, Nat.shiftLeft 1 a, 0))
        (actM (g.map (2 ^ ·)) (Nat.shiftRight x 1)) = _
      rw [nIf_eq, bitS_eq, shiftRight_one]
      simp only [decide_eq_true_eq]
      change (if x % 2 = 1 then 1 <<< a else 0) ^^^ _ = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    · have hx : x = 0 := Nat.eq_of_beq_eq_true hb
      subst hx
      change (0 : Nat) = _
      simp [actM_zero]

theorem synS_eq (x : Nat) : synS x = syndM x := by
  rw [synS, actS_eq]
  rfl

theorem synS_eq_zero_iff (x : Nat) : synS x = 0 ↔ bvec 24 x ∈ C := by
  rw [synS_eq, bvec_mem_C_iff]

theorem actS_xor (cs : List Nat) (a b : Nat) : actS cs (a ^^^ b) = actS cs a ^^^ actS cs b := by
  rw [actS_eq, actS_eq, actS_eq, actM_xor cs a b]

@[expose] def ImgL (σ : Equiv.Perm (Fin 24)) (g : List Nat) : Prop :=
  g.length = 24 ∧ HasArr σ g.toArray

theorem map_pow_eq_permCols {g : List Nat} (hg : g.length = 24) :
    g.map (2 ^ ·) = permCols g.toArray := by
  apply List.ext_getElem
  · simp [permCols, hg]
  · intro j h1 h2
    have hj : j < g.toArray.size := by simpa [hg] using (by simpa using h1 : j < g.length)
    simp only [permCols, List.getElem_map, List.getElem_range]
    rw [getElem!_pos g.toArray j hj, List.getElem_toArray]

theorem bvec_permS {σ : Equiv.Perm (Fin 24)} {g : List Nat} (h : ImgL σ g) (x : Nat) :
    bvec 24 (permS g x) = permWord σ (bvec 24 x) := by
  rw [permS_eq, map_pow_eq_permCols h.1]
  exact (permWord_bvec h.2 x).symm

theorem bvec_permS_xor {σ : AutPerm} {g : List Nat} (h : ImgL σ g) {b : Nat}
    (hb : bvec 24 b ∈ C) :
    bvec 24 (permS g b ^^^ b) =
      ((permC σ ⟨bvec 24 b, hb⟩ - ⟨bvec 24 b, hb⟩ : C) : Fin 24 → ZMod 2) := by
  change _ = permWord σ (bvec 24 b) - bvec 24 b
  rw [bvec_xor, bvec_permS h, CharTwo.sub_eq_add]

theorem bvec_omK : bvec 24 omK = Ω := by
  decide +kernel

@[expose] def GenSet (gens : List (List Nat)) : Set AutPerm :=
  {σ | ∃ g ∈ gens, ImgL (σ : Equiv.Perm (Fin 24)) g}

theorem mem_fixModΩ_closure {S : Set AutPerm} {c : C} :
    c ∈ fixModΩ (Subgroup.closure S) ↔ ∀ s ∈ S, permC s c - c ∈ ΩLine := by
  constructor
  · intro h s hs
    exact h s (Subgroup.subset_closure hs)
  · intro h
    let H : Subgroup AutPerm :=
      { carrier := {p | permC p c - c ∈ ΩLine}
        one_mem' := by
          change permC 1 c - c ∈ ΩLine
          rw [permC_one, sub_self]
          exact ΩLine.zero_mem
        mul_mem' := fun {a b} ha hb => by
          have e : permC (a * b) c - c = permC a (permC b c - c) + (permC a c - c) := by
            rw [permC_mul, map_sub]
            abel
          change permC (a * b) c - c ∈ ΩLine
          rw [e]
          exact ΩLine.add_mem ((permC_mem_ΩLine_iff a _).2 hb) ha
        inv_mem' := fun {a} ha => by
          have e : permC a⁻¹ c - c = -(permC a⁻¹ (permC a c - c)) := by
            rw [map_sub, ← permC_mul, inv_mul_cancel, permC_one]
            abel
          change permC a⁻¹ c - c ∈ ΩLine
          rw [e]
          exact ΩLine.neg_mem ((permC_mem_ΩLine_iff _ _).2 ha) }
    have hle : Subgroup.closure S ≤ H := (Subgroup.closure_le H).2 fun s hs => h s hs
    exact fun p hp => hle hp

theorem fixS_sound {σ : AutPerm} {g : List Nat} (h : ImgL σ g) {b : Nat} (hb : bvec 24 b ∈ C)
    (hf : fixS g b = true) : permC σ ⟨bvec 24 b, hb⟩ - ⟨bvec 24 b, hb⟩ ∈ ΩLine := by
  unfold fixS at hf
  rw [withN_eq] at hf
  rw [mem_ΩLine_iff]
  cases h0 : Nat.beq (Nat.xor (permS g b) b) 0
  · rw [h0] at hf
    have hΩ : Nat.xor (permS g b) b = omK := Nat.eq_of_beq_eq_true hf
    right
    apply Subtype.ext
    rw [← bvec_permS_xor h hb]
    change bvec 24 (Nat.xor (permS g b) b) = Ω
    rw [hΩ, bvec_omK]
  · have h0' : Nat.xor (permS g b) b = 0 := Nat.eq_of_beq_eq_true h0
    left
    apply Subtype.ext
    rw [← bvec_permS_xor h hb]
    change bvec 24 (Nat.xor (permS g b) b) = 0
    rw [h0', bvec_zero]

theorem actM_mem {V : Submodule (ZMod 2) C} :
    ∀ {B : List Nat}, (∀ b ∈ B, ∃ hb : bvec 24 b ∈ C, (⟨bvec 24 b, hb⟩ : C) ∈ V) →
      ∀ j, ∃ h : bvec 24 (actM B j) ∈ C, (⟨bvec 24 (actM B j), h⟩ : C) ∈ V
  | [], _, j => by
    have h0 : bvec 24 (actM [] j) = 0 := bvec_zero 24
    have hC : bvec 24 (actM [] j) ∈ C := by
      rw [h0]
      exact C.zero_mem
    refine ⟨hC, ?_⟩
    have e : (⟨bvec 24 (actM [] j), hC⟩ : C) = 0 := Subtype.ext h0
    rw [e]
    exact V.zero_mem
  | b :: B, hB, j => by
    obtain ⟨hb, hbV⟩ := hB b List.mem_cons_self
    obtain ⟨h', h'V⟩ := actM_mem (fun c hc => hB c (List.mem_cons_of_mem b hc)) (j / 2)
    by_cases hj : j % 2 = 1
    · have hv : bvec 24 (actM (b :: B) j) = bvec 24 b + bvec 24 (actM B (j / 2)) := by
        rw [actM, if_pos hj, bvec_xor]
      have hC : bvec 24 (actM (b :: B) j) ∈ C := by
        rw [hv]
        exact C.add_mem hb h'
      refine ⟨hC, ?_⟩
      have e : (⟨bvec 24 (actM (b :: B) j), hC⟩ : C) =
          ⟨bvec 24 b, hb⟩ + ⟨bvec 24 (actM B (j / 2)), h'⟩ := Subtype.ext hv
      rw [e]
      exact V.add_mem hbV h'V
    · have hv : actM (b :: B) j = actM B (j / 2) := by
        rw [actM, if_neg hj, Nat.zero_xor]
      have hC : bvec 24 (actM (b :: B) j) ∈ C := by
        rw [hv]
        exact h'
      refine ⟨hC, ?_⟩
      have e : (⟨bvec 24 (actM (b :: B) j), hC⟩ : C) = ⟨bvec 24 (actM B (j / 2)), h'⟩ :=
        Subtype.ext (congrArg (bvec 24) hv)
      rw [e]
      exact h'V

theorem actS_mem_fixModΩ {gens : List (List Nat)} {B : List Nat}
    (hB : ∀ b ∈ B, synS b = 0) (hfix : ∀ g ∈ gens, ∀ b ∈ B, fixS g b = true) (j : Nat) :
    ∃ h : bvec 24 (actS B j) ∈ C,
      (⟨bvec 24 (actS B j), h⟩ : C) ∈ fixModΩ (Subgroup.closure (GenSet gens)) := by
  rw [actS_eq]
  refine actM_mem (fun b hbB => ?_) j
  have hb : bvec 24 b ∈ C := (synS_eq_zero_iff b).1 (hB b hbB)
  refine ⟨hb, mem_fixModΩ_closure.2 fun s hs => ?_⟩
  obtain ⟨g, hg, himg⟩ := hs
  exact fixS_sound himg hb (hfix g hg b hbB)

theorem famBil {K : Nat} {F bs : Nat → Nat}
    (hF : ∀ j z, j < 2 ^ K → z < 2 ^ K → F (j ^^^ z) = F j ^^^ F z)
    (hbit : ∀ j < 2 ^ K, ∀ k,
      (bs j).testBit k = true ↔ k < 2 ^ K ∧ bvec 24 (F k) * bvec 24 (F j) ∈ C)
    (A z j : Nat) (hz : z < 2 ^ K) (hj : j < 2 ^ K) (hA : A &&& bs z = A) :
    A &&& bs (j ^^^ z) = A &&& bs j := by
  have hjz : j ^^^ z < 2 ^ K := Nat.xor_lt_two_pow hj hz
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_and]
  cases hAk : A.testBit k
  · rfl
  · have hzk : (bs z).testBit k = true := by
      have := congrArg (fun x => Nat.testBit x k) hA
      simp only [Nat.testBit_and, hAk, Bool.true_and] at this
      exact this
    obtain ⟨hk, hkz⟩ := (hbit z hz k).1 hzk
    simp only [Bool.true_and]
    rw [Bool.eq_iff_iff, hbit (j ^^^ z) hjz k, hbit j hj k, hF j z hj hz, bvec_xor, mul_add]
    exact and_congr_right fun _ => C.add_mem_iff_left hkz

theorem famB0 {K : Nat} {F bs : Nat → Nat} (hF0 : F 0 = 0)
    (hbit : ∀ j < 2 ^ K, ∀ k,
      (bs j).testBit k = true ↔ k < 2 ^ K ∧ bvec 24 (F k) * bvec 24 (F j) ∈ C)
    {A : Nat} (hA : A < 2 ^ (2 ^ K)) : A &&& bs 0 = A := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  cases hAk : A.testBit k
  · rfl
  · have hk : k < 2 ^ K := by
      by_contra hk
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_of_not_lt hk)))
      rw [hAk] at this
      exact absurd this (by simp)
    rw [Bool.true_and, hbit 0 (Nat.two_pow_pos K) k, hF0, bvec_zero, mul_zero]
    exact ⟨hk, C.zero_mem⟩

theorem actS_famF (B : List Nat) (K : Nat) :
    ∀ j z, j < 2 ^ K → z < 2 ^ K → actS B (j ^^^ z) = actS B j ^^^ actS B z :=
  fun j z _ _ => actS_xor B j z

theorem actS_zero (B : List Nat) : actS B 0 = 0 := by
  rw [actS_eq, actM_zero]

theorem mem_remS {d x : Nat} : ∀ {l : List Nat}, x ∈ remS d l ↔ x ∈ l ∧ x ≠ d
  | [] => by simp [remS]
  | y :: l => by
    have e : remS d (y :: l) =
        Bool.rec (motive := fun _ => List Nat) (y :: remS d l) (remS d l) (Nat.beq y d) := rfl
    rw [e]
    cases hb : Nat.beq y d
    · have hyd : y ≠ d := fun h => by rw [h, Nat.beq_refl] at hb; exact absurd hb (by simp)
      change x ∈ y :: remS d l ↔ _
      rw [List.mem_cons, List.mem_cons, mem_remS]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hyd⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩
    · have hyd : y = d := Nat.eq_of_beq_eq_true hb
      change x ∈ remS d l ↔ _
      rw [mem_remS, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact absurd hyd h2
        · exact ⟨h1, h2⟩

@[expose] def innerR (g : List Nat) (bs rem : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun rem => rem)
    (fun b _ ih2 rem => ih2 (withN (Nat.xor (permS g b) b) (fun d => remS d rem))) bs rem

@[expose] def outerR (gens : List (List Nat)) (rem : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun rem => rem)
    (fun g _ ih rem => ih (innerR g bmK rem)) gens rem

theorem mem_innerR {g : List Nat} {x : Nat} :
    ∀ {bs rem : List Nat}, x ∈ rem → (∀ b ∈ bs, x ≠ Nat.xor (permS g b) b) → x ∈ innerR g bs rem
  | [], _, hx, _ => hx
  | b :: bs, rem, hx, hne => by
    have e : innerR g (b :: bs) rem =
        innerR g bs (withN (Nat.xor (permS g b) b) (fun d => remS d rem)) := rfl
    rw [e, withN_eq]
    exact mem_innerR (mem_remS.2 ⟨hx, hne b List.mem_cons_self⟩)
      fun c hc => hne c (List.mem_cons_of_mem b hc)

theorem mem_outerR {x : Nat} :
    ∀ {gens : List (List Nat)} {rem : List Nat}, x ∈ rem →
      (∀ g ∈ gens, ∀ b ∈ bmK, x ≠ Nat.xor (permS g b) b) → x ∈ outerR gens rem
  | [], _, hx, _ => hx
  | g :: gens, rem, hx, hne => by
    have e : outerR (g :: gens) rem = outerR gens (innerR g bmK rem) := rfl
    rw [e]
    exact mem_outerR (mem_innerR hx (hne g List.mem_cons_self))
      fun h hh => hne h (List.mem_cons_of_mem g hh)

theorem mwsRem_nil {gens : List (List Nat)} {Mws : List Nat} (h : mwsRem gens Mws = []) :
    ∀ w ∈ Mws, w = omK ∨ ∃ g ∈ gens, ∃ b ∈ bmK, w = permS g b ^^^ b := by
  intro w hw
  by_contra hne
  push Not at hne
  have hmem : w ∈ outerR gens (remS omK Mws) :=
    mem_outerR (mem_remS.2 ⟨hw, hne.1⟩) fun g hg b hb => hne.2 g hg b hb
  have e : mwsRem gens Mws = outerR gens (remS omK Mws) := rfl
  rw [← e, h] at hmem
  exact absurd hmem List.not_mem_nil

theorem bmK_syn : ∀ b ∈ bmK, synS b = 0 := by
  decide +kernel

theorem mws_mem_commΩ {P : Subgroup AutPerm} {gens : List (List Nat)} {Mws : List Nat}
    (hgen : ∀ g ∈ gens, ∃ σ ∈ P, ImgL (σ : Equiv.Perm (Fin 24)) g) (h : mwsRem gens Mws = []) :
    ∀ w ∈ Mws, ∃ hw : bvec 24 w ∈ C, (⟨bvec 24 w, hw⟩ : C) ∈ commΩ P := by
  intro w hw
  rcases mwsRem_nil h w hw with rfl | ⟨g, hg, b, hb, rfl⟩
  · have hC : bvec 24 omK ∈ C := by
      rw [bvec_omK]
      exact Ω_mem_C
    refine ⟨hC, ?_⟩
    have e : (⟨bvec 24 omK, hC⟩ : C) = ΩC := Subtype.ext bvec_omK
    rw [e]
    exact ΩC_mem_commΩ P
  · obtain ⟨σ, hσP, himg⟩ := hgen g hg
    have hbC : bvec 24 b ∈ C := (synS_eq_zero_iff b).1 (bmK_syn b hb)
    have hv := bvec_permS_xor himg hbC
    have hC : bvec 24 (permS g b ^^^ b) ∈ C := by
      rw [hv]
      exact Subtype.property _
    refine ⟨hC, ?_⟩
    have e : (⟨bvec 24 (permS g b ^^^ b), hC⟩ : C) =
        permC σ ⟨bvec 24 b, hbC⟩ - ⟨bvec 24 b, hbC⟩ := Subtype.ext hv
    rw [e]
    exact permC_sub_mem_commΩ hσP _

end CFSG.KC.FixBoundK

end
