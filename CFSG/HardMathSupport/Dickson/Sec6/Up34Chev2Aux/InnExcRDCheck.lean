module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDDefs
public import CFSG.RankThree.Lattice.SteinbergBIRoots

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

namespace RD

@[expose] def maskOf : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * maskOf l

theorem testBit_maskOf : ∀ (l : List Bool) (k : ℕ), (maskOf l).testBit k = l.getD k false
  | [], k => by simp [maskOf]
  | b :: l, 0 => by
    cases b <;> simp [maskOf, Nat.testBit_zero] <;> omega
  | b :: l, k + 1 => by
    rw [Nat.testBit_succ]
    have : ((if b then 1 else 0) + 2 * maskOf l) / 2 = maskOf l := by cases b <;> simp <;> omega
    simp only [maskOf, this]
    rw [testBit_maskOf l k]
    simp

@[expose] def newNb (nb K vis : ℕ) : ℕ := (nb &&& K) ^^^ ((nb &&& K) &&& vis)

theorem testBit_newNb (nb K vis y : ℕ) :
    (newNb nb K vis).testBit y = (nb.testBit y && K.testBit y && !vis.testBit y) := by
  simp only [newNb, Nat.testBit_xor, Nat.testBit_and]
  cases nb.testBit y <;> cases K.testBit y <;> cases vis.testBit y <;> rfl

@[expose] def Reach (row : ℕ → ℕ) (K b : ℕ) : ℕ → Prop :=
  Relation.ReflTransGen (fun u v => K.testBit v = true ∧ (row u).testBit v = true) b

@[expose] def bfs (row : ℕ → ℕ) (K : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | f + 1, vis, fr =>
    if (fr == 0 || vis == K) = true then some vis
    else
      bfs row K f (vis ||| newNb (row fr.log2) K vis)
        ((fr ^^^ 2 ^ fr.log2) ||| newNb (row fr.log2) K vis)

structure BInv (row : ℕ → ℕ) (K b vis fr : ℕ) : Prop where
  fr_sub : ∀ x, fr.testBit x = true → vis.testBit x = true
  reach : ∀ x, vis.testBit x = true → K.testBit x = true ∧ Reach row K b x
  expanded : ∀ x, vis.testBit x = true → fr.testBit x = false → ∀ y, K.testBit y = true →
    (row x).testBit y = true → vis.testBit y = true

theorem BInv.step {row : ℕ → ℕ} {K b vis fr : ℕ} (h : BInv row K b vis fr) (hfr : fr ≠ 0) :
    BInv row K b (vis ||| newNb (row fr.log2) K vis)
      ((fr ^^^ 2 ^ fr.log2) ||| newNb (row fr.log2) K vis) := by
  have hx : fr.testBit fr.log2 = true := Nat.testBit_log2 hfr
  have hxv := h.fr_sub _ hx
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy hy' z hz hyz => ?_⟩
  · simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow, Bool.or_eq_true] at hy ⊢
    rcases hy with hy | hy
    · left
      have : fr.testBit y = true := by
        cases h1 : fr.testBit y
        · simp [h1] at hy
          subst hy
          simp_all
        · rfl
      exact h.fr_sub y this
    · exact Or.inr hy
  · simp only [Nat.testBit_or, Bool.or_eq_true] at hy
    rcases hy with hy | hy
    · exact h.reach y hy
    · rw [testBit_newNb] at hy
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy
      obtain ⟨⟨hrow, hK⟩, -⟩ := hy
      exact ⟨hK, Relation.ReflTransGen.tail (h.reach _ hxv).2 ⟨hK, hrow⟩⟩
  · simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow, Bool.or_eq_true,
      Bool.or_eq_false_iff] at hy hy' ⊢
    obtain ⟨hy1, hy2⟩ := hy'
    rcases hy with hy | hy
    · by_cases hfy : fr.testBit y = true
      · have hxy : fr.log2 = y := by
          by_contra hne
          simp [hfy, hne] at hy1
        subst hxy
        by_cases hzv : vis.testBit z = true
        · exact Or.inl hzv
        · right
          rw [testBit_newNb]
          simp [hz, hyz, hzv]
      · have hfy' : fr.testBit y = false := by simpa using hfy
        exact Or.inl (h.expanded y hy hfy' z hz hyz)
    · rw [hy] at hy2
      exact absurd hy2 (by simp)

theorem BInv.closed_of_exit {row : ℕ → ℕ} {K b vis fr : ℕ} (h : BInv row K b vis fr)
    (hexit : fr = 0 ∨ vis = K) :
    ∀ y z, vis.testBit y = true → K.testBit z = true → (row y).testBit z = true →
      vis.testBit z = true := by
  intro y z hy hz hyz
  rcases hexit with rfl | rfl
  · exact h.expanded y hy (by simp) z hz hyz
  · exact hz

theorem bfs_sound (row : ℕ → ℕ) (K b : ℕ) :
    ∀ (f vis fr V : ℕ), BInv row K b vis fr → bfs row K f vis fr = some V →
      (∀ x, vis.testBit x = true → V.testBit x = true) ∧
      (∀ x, V.testBit x = true → K.testBit x = true ∧ Reach row K b x) ∧
      (∀ y z, V.testBit y = true → K.testBit z = true → (row y).testBit z = true →
        V.testBit z = true)
  | 0, vis, fr, V, h, hb => by simp [bfs] at hb
  | f + 1, vis, fr, V, h, hb => by
    unfold bfs at hb
    split_ifs at hb with hc
    · obtain rfl := Option.some.inj hb
      have hexit : fr = 0 ∨ vis = K := by simpa using hc
      exact ⟨fun _ hx => hx, h.reach, h.closed_of_exit hexit⟩
    · have hfr : fr ≠ 0 := by
        intro h0
        apply hc
        simp [h0]
      obtain ⟨h1, h2, h3⟩ := bfs_sound row K b f _ _ V (h.step hfr) hb
      refine ⟨fun x hx => h1 x ?_, h2, h3⟩
      simp [Nat.testBit_or, hx]

structure IsComp (row : ℕ → ℕ) (K V b : ℕ) : Prop where
  base : K.testBit b = true
  mem : V.testBit b = true
  reach : ∀ x, V.testBit x = true → K.testBit x = true ∧ Reach row K b x
  closed : ∀ y z, V.testBit y = true → K.testBit z = true → (row y).testBit z = true →
    V.testBit z = true

theorem BInv.init {row : ℕ → ℕ} {K b : ℕ} (hb : K.testBit b = true) :
    BInv row K b (2 ^ b) (2 ^ b) :=
  ⟨fun _ h => h, fun x hx => by
    rw [Nat.testBit_two_pow] at hx
    have : b = x := by simpa using hx
    subst this
    exact ⟨hb, Relation.ReflTransGen.refl⟩, fun x hx hx' => by
    rw [hx] at hx'
    exact absurd hx' (by simp)⟩

theorem isComp_of_bfs {row : ℕ → ℕ} {K b f V : ℕ} (hb : K.testBit b = true)
    (h : bfs row K f (2 ^ b) (2 ^ b) = some V) : IsComp row K V b := by
  obtain ⟨h1, h2, h3⟩ := bfs_sound row K b f _ _ V (BInv.init hb) h
  exact ⟨hb, h1 b Nat.testBit_two_pow_self, h2, h3⟩

@[expose] def compLoop (row : ℕ → ℕ) (K : ℕ) (bf : ℕ) (okC : ℕ → ℕ → Bool) : ℕ → ℕ → Bool
  | 0, rem => rem == 0
  | f + 1, rem =>
    if rem == 0 then true
    else
      match bfs row K bf (2 ^ rem.log2) (2 ^ rem.log2) with
      | none => false
      | some V => okC V rem.log2 && compLoop row K bf okC f (rem ^^^ (rem &&& V))

theorem compLoop_sound (row : ℕ → ℕ) (K : ℕ) (bf : ℕ) (okC : ℕ → ℕ → Bool) :
    ∀ (f rem : ℕ), compLoop row K bf okC f rem = true →
      (∀ x, rem.testBit x = true → K.testBit x = true) →
      ∀ x, rem.testBit x = true → ∃ V b, V.testBit x = true ∧ IsComp row K V b ∧ okC V b = true
  | 0, rem, h, hK, x, hx => by
    simp only [compLoop, beq_iff_eq] at h
    subst h
    simp at hx
  | f + 1, rem, h, hK, x, hx => by
    unfold compLoop at h
    have hrem : rem ≠ 0 := by
      rintro rfl
      simp at hx
    simp only [beq_iff_eq, hrem, if_false] at h
    have hb : rem.testBit rem.log2 = true := Nat.testBit_log2 hrem
    cases hbfs : bfs row K bf (2 ^ rem.log2) (2 ^ rem.log2) with
    | none => simp [hbfs] at h
    | some V =>
      rw [hbfs] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hok, hrest⟩ := h
      have hcomp := isComp_of_bfs (hK _ hb) hbfs
      by_cases hxV : V.testBit x = true
      · exact ⟨V, _, hxV, hcomp, hok⟩
      · have hxV' : V.testBit x = false := by simpa using hxV
        refine compLoop_sound row K bf okC f _ hrest (fun y hy => ?_) x ?_
        · simp only [Nat.testBit_xor, Nat.testBit_and] at hy
          apply hK
          cases h1 : rem.testBit y <;> simp_all
        · simp [Nat.testBit_xor, Nat.testBit_and, hx, hxV']

section Algebra

variable {L : Type} [Field L]

theorem eq_one_or_eq_or_eq_sq {ω x : Lˣ} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hx : x ^ 3 = 1) :
    x = 1 ∨ x = ω ∨ x = ω ^ 2 := by
  have hω' : (ω : L) ^ 3 = 1 := by simpa using congrArg Units.val hω
  have hx' : (x : L) ^ 3 = 1 := by simpa using congrArg Units.val hx
  have hω1' : (ω : L) ≠ 1 := fun h => hω1 (Units.ext h)
  have hq : (ω : L) ^ 2 + ω + 1 = 0 := by
    have : ((ω : L) - 1) * ((ω : L) ^ 2 + ω + 1) = 0 := by linear_combination hω'
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hω1'
    · exact h
  by_cases hx1 : (x : L) = 1
  · exact Or.inl (Units.ext hx1)
  · have hqx : (x : L) ^ 2 + x + 1 = 0 := by
      have : ((x : L) - 1) * ((x : L) ^ 2 + x + 1) = 0 := by linear_combination hx'
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hx1
      · exact h
    have : ((x : L) - ω) * ((x : L) + ω + 1) = 0 := by linear_combination hqx - hq
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inr (Or.inl (Units.ext (sub_eq_zero.1 h)))
    · refine Or.inr (Or.inr (Units.ext ?_))
      push_cast
      linear_combination h - hq

theorem exists_exps {n : ℕ} (a : Fin n → Lˣ) (ha : ∀ j, a j ^ 3 = 1) :
    ∃ (ω₀ : Lˣ) (e : Fin n → ℕ), ω₀ ^ 3 = 1 ∧ (∀ j, e j < 3) ∧ (∀ j, a j = ω₀ ^ e j) ∧
      (ω₀ = 1 → ∀ j, e j = 0) := by
  by_cases h : ∀ j, a j = 1
  · exact ⟨1, fun _ => 0, one_pow _, fun _ => by norm_num, fun j => by simp [h j], fun _ _ => rfl⟩
  · obtain ⟨j₀, hj₀⟩ := not_forall.1 h
    classical
    refine ⟨a j₀, fun j => if a j = 1 then 0 else if a j = a j₀ then 1 else 2, ha j₀, ?_, ?_, ?_⟩
    · intro j
      dsimp only
      split_ifs <;> omega
    · intro j
      dsimp only
      rcases eq_one_or_eq_or_eq_sq (ha j₀) hj₀ (ha j) with h1 | h1 | h1
      · simp [h1]
      · simp [h1]
      · by_cases h2 : a j = 1
        · simp [h2]
        · by_cases h3 : a j = a j₀
          · simp [h3]
          · rw [if_neg h2, if_neg h3]
            exact h1
    · intro h1 j
      exact absurd h1 hj₀

theorem prod_zpow_eq {G : Type*} [CommGroup G] (g : G) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, g ^ f i = g ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem rootChar_eq_zpow_sum {τ : Tag} (a : Fin τ.rank → Lˣ) (ω₀ : Lˣ) (e : Fin τ.rank → ℕ)
    (hae : ∀ j, a j = ω₀ ^ e j) (α : Fin τ.rank → ℤ) :
    rootChar a α = ω₀ ^ (∑ j, (e j : ℤ) * α j) := by
  unfold rootChar
  rw [← prod_zpow_eq]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hae j, ← zpow_natCast, ← zpow_mul]

theorem mem_kernelRoots_iff {τ : Tag} (a : Fin τ.rank → Lˣ) (ω₀ : Lˣ) (e : Fin τ.rank → ℕ)
    (hω₀ : ω₀ ^ 3 = 1) (hae : ∀ j, a j = ω₀ ^ e j) (hprim : ω₀ ≠ 1 ∨ ∀ j, e j = 0)
    (α : Fin τ.rank → ℤ) :
    α ∈ kernelRoots (rootCharHom a) ↔ IsRoot τ α ∧ (3 : ℤ) ∣ ∑ j, (e j : ℤ) * α j := by
  change IsRoot τ α ∧ rootChar a α = 1 ↔ _
  rw [rootChar_eq_zpow_sum a ω₀ e hae]
  refine and_congr_right fun _ => ?_
  rcases hprim with h | h
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have ho : orderOf ω₀ = 3 := orderOf_eq_prime hω₀ h
    rw [← orderOf_dvd_iff_zpow_eq_one, ho]
    norm_num
  · simp [h]

end Algebra

section Classes

variable {τ : Tag}

@[expose] def rt (τ : Tag) (k : ℕ) : Fin τ.rank → ℤ := toVec τ.rank (τ.artifactRoots.getD k [])

theorem isRoot_iff_exists_rt {v : Fin τ.rank → ℤ} :
    IsRoot τ v ↔ ∃ k, k < τ.artifactRoots.length ∧ v = rt τ k := by
  rw [isRoot_iff_exists_mem]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
    exact ⟨k, hk, by simp [rt, hk]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, List.getElem_mem hk, by simp [rt, hk]⟩

theorem isRoot_rt {k : ℕ} (hk : k < τ.artifactRoots.length) :
    IsRoot τ (rt τ k) :=
  isRoot_iff_exists_rt.2 ⟨k, hk, rfl⟩

theorem rt_injOn {k l : ℕ} (hk : k < τ.artifactRoots.length)
    (hl : l < τ.artifactRoots.length) (h : rt τ k = rt τ l) : k = l := by
  have hk' : τ.artifactRoots.getD k [] ∈ τ.artifactRoots := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hl' : τ.artifactRoots.getD l [] ∈ τ.artifactRoots := by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  have := toVec_injOn_artifactRoots τ hk' hl' h
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hl] at this
  exact (List.Nodup.getElem_inj_iff (nodup_artifactRoots τ)).1 this

end Classes

section ClassBridge

variable {τ : Tag} {M : Type*} [CommGroup M]

@[expose] def bitsSet (V : ℕ) : Set ℕ := {x | V.testBit x = true}

theorem Reach.testBit {row : ℕ → ℕ} {K b y : ℕ} (hb : K.testBit b = true) (h : Reach row K b y) :
    K.testBit y = true := by
  induction h with
  | refl => exact hb
  | tail _ hstep _ => exact hstep.1

structure Spec (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (row : ℕ → ℕ) (K : ℕ) : Prop where
  row_iff : ∀ k l, (row k).testBit l = true ↔
    k < τ.artifactRoots.length ∧ l < τ.artifactRoots.length ∧ iform (rt τ k) (rt τ l) ≠ 0
  K_iff : ∀ l, K.testBit l = true ↔ l < τ.artifactRoots.length ∧ rt τ l ∈ kernelRoots χ

theorem componentRoots_eq_image {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {row : ℕ → ℕ}
    {K : ℕ} (hS : Spec χ row K) {V b : ℕ} (hV : IsComp row K V b) {k : ℕ}
    (hk : V.testBit k = true) (hkκ : rt τ k ∈ kernelRoots χ) :
    componentRoots χ (Quotient.mk (kernelRootSetoid χ) ⟨rt τ k, hkκ⟩) = rt τ '' bitsSet V := by
  classical
  have hbκ : rt τ b ∈ kernelRoots χ := (hS.K_iff b).1 hV.base |>.2
  have hclosed : ∀ u ∈ rt τ '' bitsSet V, ∀ v ∈ kernelRoots χ, iform u v ≠ 0 →
      v ∈ rt τ '' bitsSet V := by
    rintro _ ⟨x, hx, rfl⟩ v hv hne
    obtain ⟨z, hz, rfl⟩ := isRoot_iff_exists_rt.1 hv.1
    have hKz : K.testBit z = true := (hS.K_iff z).2 ⟨hz, hv⟩
    have hxN : x < τ.artifactRoots.length := ((hS.K_iff x).1 (hV.reach x hx).1).1
    have hrow : (row x).testBit z = true := (hS.row_iff x z).2 ⟨hxN, hz, hne⟩
    exact ⟨z, hV.closed x z hx hKz hrow, rfl⟩
  have hconn : ∀ y, Reach row K b y → ∀ hy : rt τ y ∈ kernelRoots χ,
      (Quotient.mk (kernelRootSetoid χ) ⟨rt τ y, hy⟩ : KernelComponent χ) =
        Quotient.mk (kernelRootSetoid χ) ⟨rt τ b, hbκ⟩ := by
    intro y hy
    induction hy with
    | refl => intro _; rfl
    | @tail y z hby hyz ih =>
      intro hz
      have hKy : K.testBit y = true := Reach.testBit hV.base hby
      have hyκ : rt τ y ∈ kernelRoots χ := ((hS.K_iff y).1 hKy).2
      have hyN : y < τ.artifactRoots.length := ((hS.K_iff y).1 hKy).1
      have hzN : z < τ.artifactRoots.length := ((hS.K_iff z).1 hyz.1).1
      have hne : iform (rt τ y) (rt τ z) ≠ 0 := ((hS.row_iff y z).1 hyz.2).2.2
      exact (mk_eq_of_iform_ne_zero (α := ⟨rt τ y, hyκ⟩) (β := ⟨rt τ z, hz⟩) hne).symm.trans (ih hyκ)
  have hkb : (Quotient.mk (kernelRootSetoid χ) ⟨rt τ k, hkκ⟩ : KernelComponent χ) =
      Quotient.mk (kernelRootSetoid χ) ⟨rt τ b, hbκ⟩ := hconn k (hV.reach k hk).2 hkκ
  ext β
  constructor
  · rintro ⟨hβ, hβk⟩
    have hEq := Quotient.exact hβk
    have key : ∀ x y : kernelRoots χ, Relation.EqvGen
        (fun α β : kernelRoots χ => (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y →
        ((x : Fin τ.rank → ℤ) ∈ rt τ '' bitsSet V ↔ (y : Fin τ.rank → ℤ) ∈ rt τ '' bitsSet V) := by
      intro x y h
      induction h with
      | rel x y hxy =>
        rw [dotProduct_mulVec_eq_iform] at hxy
        exact ⟨fun hx => hclosed _ hx _ y.2 hxy, fun hy =>
          hclosed _ hy _ x.2 (by rwa [iform_comm])⟩
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact (key ⟨β, hβ⟩ ⟨rt τ k, hkκ⟩ hEq).2 ⟨k, hk, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hxκ : rt τ x ∈ kernelRoots χ := ((hS.K_iff x).1 (hV.reach x hx).1).2
    exact ⟨hxκ, (hconn x (hV.reach x hx).2 hxκ).trans hkb.symm⟩

theorem ncard_componentRoots_eq {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {row : ℕ → ℕ}
    {K : ℕ} (hS : Spec χ row K) {V b : ℕ} (hV : IsComp row K V b) {k : ℕ}
    (hk : V.testBit k = true) (hkκ : rt τ k ∈ kernelRoots χ) :
    (componentRoots χ (Quotient.mk (kernelRootSetoid χ) ⟨rt τ k, hkκ⟩)).ncard =
      (bitsSet V).ncard := by
  rw [componentRoots_eq_image hS hV hk hkκ]
  refine Set.InjOn.ncard_image fun x hx y hy h => ?_
  exact rt_injOn ((hS.K_iff x).1 (hV.reach x hx).1).1 ((hS.K_iff y).1 (hV.reach y hy).1).1 h

end ClassBridge

section Count

theorem bitsSet_finite (V : ℕ) : (bitsSet V).Finite := by
  refine (Set.finite_Iio V).subset fun x hx => ?_
  by_contra h
  have hVx : V ≤ x := by simpa using h
  have h1 : V < 2 ^ x := lt_of_lt_of_le V.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hVx)
  have := Nat.testBit_lt_two_pow h1
  exact absurd hx (by simp [bitsSet, this])

theorem bitsSet_clear {V : ℕ} (hV : V ≠ 0) :
    bitsSet (V ^^^ 2 ^ V.log2) = bitsSet V \ {V.log2} := by
  ext x
  simp only [bitsSet, Set.mem_setOf_eq, Nat.testBit_xor, Nat.testBit_two_pow, Set.mem_diff,
    Set.mem_singleton_iff]
  have hx := Nat.testBit_log2 hV
  by_cases hxe : V.log2 = x
  · subst hxe
    simp [hx]
  · cases h : V.testBit x <;> simp [hxe, h, Ne.symm hxe]

theorem ncard_bitsSet_clear {V : ℕ} (hV : V ≠ 0) :
    (bitsSet V).ncard = (bitsSet (V ^^^ 2 ^ V.log2)).ncard + 1 := by
  rw [bitsSet_clear hV]
  exact (Set.ncard_diff_singleton_add_one (show V.log2 ∈ bitsSet V from Nat.testBit_log2 hV)
    (bitsSet_finite V)).symm

@[expose] def cnt : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, V => if V == 0 then 0 else cnt f (V ^^^ 2 ^ V.log2) + 1

theorem cnt_spec : ∀ (f V : ℕ), (cnt f V = f → f ≤ (bitsSet V).ncard) ∧
    (cnt f V < f → (bitsSet V).ncard = cnt f V)
  | 0, V => by simp [cnt]
  | f + 1, V => by
    by_cases hV : V = 0
    · subst hV
      simp [cnt, bitsSet]
    · have hc : cnt (f + 1) V = cnt f (V ^^^ 2 ^ V.log2) + 1 := by simp [cnt, hV]
      obtain ⟨h1, h2⟩ := cnt_spec f (V ^^^ 2 ^ V.log2)
      rw [hc, ncard_bitsSet_clear hV]
      exact ⟨fun h => by have := h1 (by omega); omega, fun h => by have := h2 (by omega); omega⟩

end Count

section Gram

@[expose] def dotR : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + dotR as bs
  | _, _ => 0

theorem dotR_eq_sum : ∀ (n : ℕ) (u v : List ℤ), u.length = n → v.length = n →
    dotR u v = ∑ i : Fin n, vget u i * vget v i
  | 0, u, v, hu, hv => by
    obtain rfl : u = [] := List.length_eq_zero_iff.1 hu
    obtain rfl : v = [] := List.length_eq_zero_iff.1 hv
    simp [dotR]
  | n + 1, u, v, hu, hv => by
    obtain ⟨a, u', rfl⟩ := List.exists_cons_of_length_eq_add_one hu
    obtain ⟨b, v', rfl⟩ := List.exists_cons_of_length_eq_add_one hv
    rw [Fin.sum_univ_succ, dotR, dotR_eq_sum n u' v' (by simpa using hu) (by simpa using hv)]
    simp [vget]

@[expose] def gramList (τ : Tag) : List (List ℤ) :=
  lofFn τ.rank fun i j => τ.symmetrizedCartan i j

@[expose] def mulVecR (G : List (List ℤ)) (v : List ℤ) : List ℤ := G.map fun row => dotR row v

theorem length_mulVecR (G : List (List ℤ)) (v : List ℤ) : (mulVecR G v).length = G.length := by
  simp [mulVecR]

theorem iform_toVec_eq_dotR (τ : Tag) {u v : List ℤ} (hu : u.length = τ.rank)
    (hv : v.length = τ.rank) :
    iform (toVec τ.rank u) (toVec τ.rank v) = dotR u (mulVecR (gramList τ) v) := by
  have hG : (gramList τ).length = τ.rank := by simp [gramList, lofFn]
  rw [dotR_eq_sum τ.rank u _ hu (by rw [length_mulVecR, hG])]
  unfold iform
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : vget (mulVecR (gramList τ) v) i = ∑ j : Fin τ.rank, τ.symmetrizedCartan i j * vget v j := by
    have hi : (i : ℕ) < (mulVecR (gramList τ) v).length := by rw [length_mulVecR, hG]; exact i.2
    have hi' : (i : ℕ) < (gramList τ).length := by rw [hG]; exact i.2
    rw [vget, List.getD_eq_getElem _ _ hi]
    simp only [mulVecR, List.getElem_map]
    have hrow : (gramList τ)[(i : ℕ)] =
        List.ofFn (fun j : Fin τ.rank => τ.symmetrizedCartan i j) := by
      simp [gramList, lofFn]
    rw [hrow, dotR_eq_sum τ.rank _ v (by simp) hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [vget]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [toVec]
  ring

end Gram

section RootGram

variable {τ : Tag}

@[expose] def rl (τ : Tag) (k : ℕ) : List ℤ := τ.artifactRoots.getD k []

theorem rl_mem {k : ℕ} (hk : k < τ.artifactRoots.length) : rl τ k ∈ τ.artifactRoots := by
  rw [rl, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

theorem length_rl {k : ℕ} (hk : k < τ.artifactRoots.length) : (rl τ k).length = τ.rank :=
  length_of_mem_artifactRoots (rl_mem hk)

theorem rt_eq (τ : Tag) (k : ℕ) : rt τ k = toVec τ.rank (rl τ k) := rfl

theorem iform_rt_rt {k l : ℕ} (hk : k < τ.artifactRoots.length) (hl : l < τ.artifactRoots.length) :
    iform (rt τ k) (rt τ l) = dotR (rl τ k) (mulVecR (gramList τ) (rl τ l)) :=
  iform_toVec_eq_dotR τ (length_rl hk) (length_rl hl)

theorem iform_rt_single {k : ℕ} (hk : k < τ.artifactRoots.length) (j : Fin τ.rank) :
    iform (rt τ k) (Pi.single j 1) = (mulVecR (gramList τ) (rl τ k)).getD j 0 := by
  have hu : (List.ofFn (Pi.single j 1 : Fin τ.rank → ℤ)).length = τ.rank := List.length_ofFn
  rw [iform_comm, ← toVec_ofFn (Pi.single j 1 : Fin τ.rank → ℤ), rt_eq,
    iform_toVec_eq_dotR τ hu (length_rl hk),
    dotR_eq_sum τ.rank _ _ hu (by rw [length_mulVecR]; simp [gramList, lofFn])]
  rw [Finset.sum_eq_single j]
  · simp [vget, Pi.single_apply, List.getD_eq_getElem?_getD]
  · intro i _ hij
    simp [vget, Pi.single_apply, hij]
  · simp

end RootGram

section Rows

variable {τ : Tag}

@[expose] def bRoots (τ : Tag) : List (List ℤ) := τ.artifactRoots.map (mulVecR (gramList τ))

@[expose] def rowsList (τ : Tag) : List ℕ :=
  τ.artifactRoots.map fun u => maskOf ((bRoots τ).map fun w => dotR u w != 0)

@[expose] def rowOf (τ : Tag) (k : ℕ) : ℕ := (rowsList τ).getD k 0

theorem getD_map_lt {α β : Type*} (f : α → β) (l : List α) {k : ℕ} (hk : k < l.length) (d : α)
    (d' : β) : (l.map f).getD k d' = f (l.getD k d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk, List.getElem_map]

theorem rowOf_spec (k l : ℕ) :
    (rowOf τ k).testBit l = true ↔ k < τ.artifactRoots.length ∧ l < τ.artifactRoots.length ∧
      iform (rt τ k) (rt τ l) ≠ 0 := by
  by_cases hk : k < τ.artifactRoots.length
  · have e1 : rowOf τ k = maskOf ((bRoots τ).map fun w => dotR (rl τ k) w != 0) :=
      getD_map_lt _ τ.artifactRoots hk [] 0
    rw [e1, testBit_maskOf]
    by_cases hl : l < τ.artifactRoots.length
    · have hl' : l < (bRoots τ).length := by simpa [bRoots] using hl
      rw [getD_map_lt _ (bRoots τ) hl' [] false, iform_rt_rt hk hl]
      have : (bRoots τ).getD l [] = mulVecR (gramList τ) (rl τ l) :=
        getD_map_lt _ τ.artifactRoots hl [] []
      rw [this]
      simp [hk, hl]
    · rw [List.getD_eq_default _ _ (by simpa [bRoots] using hl)]
      simp [hl]
  · rw [rowOf, List.getD_eq_default _ _ (by simpa [rowsList] using hk)]
    simp [hk]

end Rows

section Kernel

variable {τ : Tag}

@[expose] def digDot (r : List ℤ) (d : List ℕ) : ℤ := dotR r (d.map Int.ofNat)

@[expose] def kerMask (τ : Tag) (d : List ℕ) : ℕ :=
  maskOf (τ.artifactRoots.map fun r => digDot r d % 3 == 0)

@[expose] def allVecs : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (allVecs n).flatMap fun v => [0 :: v, 1 :: v, 2 :: v]

theorem ofFn_mem_allVecs : ∀ (n : ℕ) (e : Fin n → ℕ), (∀ j, e j < 3) → List.ofFn e ∈ allVecs n
  | 0, e, _ => by simp [allVecs]
  | n + 1, e, he => by
    rw [List.ofFn_succ]
    have ih := ofFn_mem_allVecs n (fun j => e j.succ) (fun j => he _)
    have h0 := he 0
    simp only [allVecs, List.mem_flatMap]
    refine ⟨_, ih, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq, and_true]
    omega

theorem digDot_ofFn {l : ℕ} (hl : l < τ.artifactRoots.length)
    (e : Fin τ.rank → ℕ) :
    digDot (rl τ l) (List.ofFn e) = ∑ j, (e j : ℤ) * (rt τ l) j := by
  unfold digDot
  rw [dotR_eq_sum τ.rank _ _ (length_rl hl) (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : vget ((List.ofFn e).map Int.ofNat) j = (e j : ℤ) := by
    simp [vget, List.getD_eq_getElem?_getD]
  rw [this, mul_comm]
  rfl

theorem kerMask_spec
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ω₀ : Lˣ) (e : Fin τ.rank → ℕ)
    (hω₀ : ω₀ ^ 3 = 1) (hae : ∀ j, a j = ω₀ ^ e j) (hprim : ω₀ ≠ 1 ∨ ∀ j, e j = 0) (l : ℕ) :
    (kerMask τ (List.ofFn e)).testBit l = true ↔
      l < τ.artifactRoots.length ∧ rt τ l ∈ kernelRoots (rootCharHom a) := by
  unfold kerMask
  rw [testBit_maskOf]
  by_cases hl : l < τ.artifactRoots.length
  · rw [getD_map_lt _ τ.artifactRoots hl [] false, mem_kernelRoots_iff a ω₀ e hω₀ hae hprim]
    have := digDot_ofFn hl e
    change (digDot (rl τ l) (List.ofFn e) % 3 == 0) = true ↔ _
    rw [this]
    simp only [beq_iff_eq]
    exact ⟨fun h => ⟨hl, isRoot_rt hl, Int.dvd_of_emod_eq_zero h⟩,
      fun h => Int.emod_eq_zero_of_dvd h.2.2⟩
  · rw [List.getD_eq_default _ _ (by simpa using hl)]
    simp [hl]

end Kernel

section Glue

variable {τ : Tag}

@[expose] def memb : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, V => if V == 0 then [] else V.log2 :: memb f (V ^^^ 2 ^ V.log2)

theorem testBit_of_mem_memb : ∀ (f V x : ℕ), x ∈ memb f V → V.testBit x = true
  | 0, V, x, h => by simp [memb] at h
  | f + 1, V, x, h => by
    unfold memb at h
    split_ifs at h with h0
    · simp at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Nat.testBit_log2 (by simpa using h0)
      · have := testBit_of_mem_memb f _ x h
        simp only [Nat.testBit_xor, Nat.testBit_two_pow] at this
        by_contra hne
        have hf : V.testBit x = false := by simpa using hne
        simp [hf] at this
        subst this
        exact hne (Nat.testBit_log2 (by simpa using h0))

@[expose] def gramAt (τ : Tag) (k l : ℕ) : ℤ := dotR (rl τ k) ((bRoots τ).getD l [])

@[expose] def a2Wit (τ : Tag) (d : List ℕ) (k₁ k₂ : ℕ) : Bool :=
  gramAt τ k₁ k₁ == gramAt τ k₂ k₂ && 2 * gramAt τ k₁ k₂ == -gramAt τ k₁ k₁ &&
    ((List.range τ.rank).all (fun j => ((d.getD j 0 : ℕ) : ℤ) % 3 ==
        (2 * ((bRoots τ).getD k₁ []).getD j 0 / gramAt τ k₁ k₁ +
          2 * (2 * ((bRoots τ).getD k₂ []).getD j 0 / gramAt τ k₂ k₂)) % 3) ||
      (List.range τ.rank).all (fun j => (((d.getD j 0 : ℕ) : ℤ) +
        (2 * ((bRoots τ).getD k₁ []).getD j 0 / gramAt τ k₁ k₁ +
          2 * (2 * ((bRoots τ).getD k₂ []).getD j 0 / gramAt τ k₂ k₂))) % 3 == 0))

@[expose] def glue (τ : Tag) (d : List ℕ) (V : ℕ) : Bool :=
  match memb 6 V with
  | [] => false
  | k₁ :: ks => ks.any (fun k₂ => a2Wit τ d k₁ k₂)

@[expose] def okC (τ : Tag) (cap : ℕ) (okS : ℕ → Bool) (d : List ℕ) (V : ℕ) (_b : ℕ) : Bool :=
  okS (cnt cap V) && (cnt cap V != 6 || glue τ d V)

@[expose] def eCheck (τ : Tag) (cap : ℕ) (okS : ℕ → Bool) (d : List ℕ) : Bool :=
  compLoop (rowOf τ) (kerMask τ d) (τ.artifactRoots.length + 1) (okC τ cap okS d)
    τ.artifactRoots.length (kerMask τ d)

@[expose] def rdCheck (τ : Tag) (cap : ℕ) (okS : ℕ → Bool) : Bool :=
  (allVecs τ.rank).all (eCheck τ cap okS)

end Glue

section GlueSound

variable {τ : Tag}

theorem gramAt_eq {k l : ℕ} (hk : k < τ.artifactRoots.length) (hl : l < τ.artifactRoots.length) :
    gramAt τ k l = iform (rt τ k) (rt τ l) := by
  rw [iform_rt_rt hk hl, gramAt]
  have : (bRoots τ).getD l [] = mulVecR (gramList τ) (rl τ l) :=
    getD_map_lt _ τ.artifactRoots hl [] []
  rw [this]

theorem bRoots_getD {k : ℕ} (hk : k < τ.artifactRoots.length) :
    (bRoots τ).getD k [] = mulVecR (gramList τ) (rl τ k) :=
  getD_map_lt _ τ.artifactRoots hk [] []

theorem a2Wit_spec {k₁ k₂ : ℕ} (hk₁ : k₁ < τ.artifactRoots.length)
    (hk₂ : k₂ < τ.artifactRoots.length) (e : Fin τ.rank → ℕ)
    (h : a2Wit τ (List.ofFn e) k₁ k₂ = true) :
    IsA2Pair τ (rt τ k₁) (rt τ k₂) ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ j : Fin τ.rank, (3 : ℤ) ∣ (e j : ℤ) - ε * a2Exp τ (rt τ k₁) (rt τ k₂) j := by
  unfold a2Wit at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hgg, hg12⟩, hexp⟩ := h
  simp only [gramAt_eq hk₁ hk₁, gramAt_eq hk₂ hk₂, gramAt_eq hk₁ hk₂] at hgg hg12 hexp
  have hM : ∀ j : Fin τ.rank, a2Exp τ (rt τ k₁) (rt τ k₂) j =
      2 * ((bRoots τ).getD k₁ []).getD j 0 / iform (rt τ k₁) (rt τ k₁) +
        2 * (2 * ((bRoots τ).getD k₂ []).getD j 0 / iform (rt τ k₂) (rt τ k₂)) := by
    intro j
    unfold a2Exp cop
    rw [iform_rt_single hk₁, iform_rt_single hk₂, bRoots_getD hk₁, bRoots_getD hk₂]
  have hd : ∀ j : Fin τ.rank, (List.ofFn e).getD j 0 = e j := by
    intro j
    simp [List.getD_eq_getElem?_getD]
  refine ⟨⟨isRoot_rt hk₁, isRoot_rt hk₂, hgg, hg12⟩, ?_⟩
  rcases hexp with hexp | hexp
  · refine ⟨1, Or.inl rfl, fun j => ?_⟩
    have := hexp j j.2
    rw [hd j] at this
    rw [hM j]
    omega
  · refine ⟨-1, Or.inr rfl, fun j => ?_⟩
    have := hexp j j.2
    rw [hd j] at this
    rw [hM j]
    omega

end GlueSound

section A2

variable {τ : Tag}

theorem iform_neg_left' (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left]; ring

theorem a2_six_ncard {γ₁ γ₂ : Fin τ.rank → ℤ} (h : IsA2Pair τ γ₁ γ₂) :
    ({γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)} : Set (Fin τ.rank → ℤ)).ncard = 6 := by
  classical
  obtain ⟨h1, h2, hc, hg⟩ := h
  have hcpos : 0 < iform γ₁ γ₁ := iform_self_pos h1.ne_zero
  have hcomm : iform γ₂ γ₁ = iform γ₁ γ₂ := iform_comm _ _
  let φ : (Fin τ.rank → ℤ) → ℤ × ℤ := fun v => (iform v γ₁, iform v γ₂)
  have hφ : [φ γ₁, φ γ₂, φ (γ₁ + γ₂), φ (-γ₁), φ (-γ₂), φ (-(γ₁ + γ₂))].Nodup := by
    simp only [φ, iform_add_left, iform_neg_left', hcomm, ← hc]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, not_or,
      List.nodup_nil, and_true, not_and, not_false_eq_true]
    omega
  have hnd : [γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)].Nodup := List.Nodup.of_map φ hφ
  have hset : ({γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)} : Set (Fin τ.rank → ℤ)) =
      ↑([γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)].toFinset) := by
    ext x
    simp
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  rfl

theorem a2_six_subset {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {γ₁ γ₂ : Fin τ.rank → ℤ}
    (h : IsA2Pair τ γ₁ γ₂) (h₁ : γ₁ ∈ Ψ) (h₂ : γ₂ ∈ Ψ) :
    ({γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)} : Set (Fin τ.rank → ℤ)) ⊆ Ψ := by
  obtain ⟨hr1, hr2, hc, hg⟩ := h
  have hcpos : 0 < iform γ₁ γ₁ := iform_self_pos hr1.ne_zero
  have hne : γ₁ ≠ -γ₂ := by
    intro heq
    have := congrArg (fun v => iform v γ₂) heq
    simp only [iform_neg_left'] at this
    omega
  have hlt : iform γ₁ γ₂ < 0 := by omega
  have hsum : γ₁ + γ₂ ∈ Ψ := hΨ.add_mem _ h₁ _ h₂ (isRoot_add_of_iform_neg hr1 hr2 hne hlt)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact hsum
  · exact hΨ.neg_mem _ h₁
  · exact hΨ.neg_mem _ h₂
  · exact hΨ.neg_mem _ hsum

end A2

section Assembly

theorem cnt_le : ∀ (f V : ℕ), cnt f V ≤ f
  | 0, V => by simp [cnt]
  | f + 1, V => by
    unfold cnt
    split_ifs
    · omega
    · have := cnt_le f (V ^^^ 2 ^ V.log2)
      omega

section GlueAlgebra

variable {L : Type} [Field L]

theorem zpow_eq_of_dvd {ω : Lˣ} (hω : ω ^ 3 = 1) {x y : ℤ} (h : (3 : ℤ) ∣ x - y) :
    ω ^ x = ω ^ y := by
  obtain ⟨t, ht⟩ := h
  have hx : x = y + 3 * t := by omega
  have h3 : ω ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]; exact hω
  rw [hx, zpow_add, zpow_mul, h3, one_zpow, mul_one]

theorem glue_algebra {n : ℕ} (a : Fin n → Lˣ) (ω₀ : Lˣ) (e : Fin n → ℕ) (m : Fin n → ℤ)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hω₀ : ω₀ ^ 3 = 1) (hae : ∀ j, a j = ω₀ ^ e j)
    (he0 : ω₀ = 1 → ∀ j, e j = 0) (hdvd : ∀ j, (3 : ℤ) ∣ (e j : ℤ) - ε * m j) :
    ∀ ω : Lˣ, ω ^ 3 = 1 → ω ≠ 1 →
      ∃ ε' : ℤ, (ε' = 1 ∨ ε' = -1) ∧ ∀ j, a j = ω ^ (ε' * m j) := by
  intro ω hω hω1
  rcases eq_one_or_eq_or_eq_sq hω hω1 hω₀ with h1 | h1 | h1
  · refine ⟨ε, hε, fun j => ?_⟩
    have he := he0 h1 j
    have hd := hdvd j
    rw [hae j, he, pow_zero]
    rw [zpow_eq_of_dvd hω (y := 0) (by rw [he] at hd; push_cast at hd; omega), zpow_zero]
  · refine ⟨ε, hε, fun j => ?_⟩
    rw [hae j, h1, ← zpow_natCast]
    exact zpow_eq_of_dvd hω (hdvd j)
  · refine ⟨-ε, ?_, fun j => ?_⟩
    · rcases hε with rfl | rfl <;> simp
    · rw [hae j, h1, ← pow_mul, ← zpow_natCast]
      refine zpow_eq_of_dvd hω ?_
      have hd := hdvd j
      rcases hε with rfl | rfl <;> push_cast <;> omega

end GlueAlgebra

end Assembly

section Extract

variable {τ : Tag}

theorem class_extract (cap : ℕ) (okS : ℕ → Bool) (h : rdCheck τ cap okS = true)
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (ω₀ : Lˣ) (e : Fin τ.rank → ℕ) (V b k : ℕ) (hkκ : rt τ k ∈ kernelRoots (rootCharHom a)),
      ω₀ ^ 3 = 1 ∧ (∀ j, e j < 3) ∧ (∀ j, a j = ω₀ ^ e j) ∧ (ω₀ = 1 → ∀ j, e j = 0) ∧
      i = Quotient.mk (kernelRootSetoid (rootCharHom a)) ⟨rt τ k, hkκ⟩ ∧ V.testBit k = true ∧
      IsComp (rowOf τ) (kerMask τ (List.ofFn e)) V b ∧
      okC τ cap okS (List.ofFn e) V b = true ∧
      Spec (rootCharHom a) (rowOf τ) (kerMask τ (List.ofFn e)) := by
  obtain ⟨ω₀, e, hω₀, he3, hae, he0⟩ := exists_exps a ha
  have hprim : ω₀ ≠ 1 ∨ ∀ j, e j = 0 := by
    by_cases h1 : ω₀ = 1
    · exact Or.inr (he0 h1)
    · exact Or.inl h1
  have hSpec : Spec (rootCharHom a) (rowOf τ) (kerMask τ (List.ofFn e)) :=
    ⟨rowOf_spec, kerMask_spec a ω₀ e hω₀ hae hprim⟩
  induction i using Quotient.inductionOn with
  | _ x =>
    obtain ⟨α, hα⟩ := x
    obtain ⟨k, hk, rfl⟩ := isRoot_iff_exists_rt.1 hα.1
    have hKk : (kerMask τ (List.ofFn e)).testBit k = true := (hSpec.K_iff k).2 ⟨hk, hα⟩
    have hd := List.all_eq_true.1 h _ (ofFn_mem_allVecs _ e he3)
    obtain ⟨V, b, hkV, hV, hok⟩ := compLoop_sound _ _ _ _ _ _ hd (fun x hx => hx) k hKk
    exact ⟨ω₀, e, V, b, k, hα, hω₀, he3, hae, he0, rfl, hkV, hV, hok, hSpec⟩

theorem size_of_check (cap : ℕ) (okS : ℕ → Bool) (h : rdCheck τ cap okS = true)
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ∃ s, okS s = true ∧ ((s < cap ∧ (componentRoots (rootCharHom a) i).ncard = s) ∨
      (s = cap ∧ cap ≤ (componentRoots (rootCharHom a) i).ncard)) := by
  obtain ⟨ω₀, e, V, b, k, hkκ, -, -, -, -, rfl, hkV, hV, hok, hSpec⟩ :=
    class_extract cap okS h a ha i
  rw [ncard_componentRoots_eq hSpec hV hkV hkκ]
  simp only [okC, Bool.and_eq_true] at hok
  obtain ⟨hs, -⟩ := hok
  obtain ⟨h1, h2⟩ := cnt_spec cap V
  refine ⟨cnt cap V, hs, ?_⟩
  by_cases hlt : cnt cap V < cap
  · exact Or.inl ⟨hlt, h2 hlt⟩
  · have : cnt cap V = cap := le_antisymm (cnt_le cap V) (not_lt.1 hlt)
    exact Or.inr ⟨this, h1 this⟩

theorem glue_of_check (cap : ℕ) (okS : ℕ → Bool) (hcap : 6 < cap)
    (h : rdCheck τ cap okS = true) {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (ha : ∀ j, a j ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (hi : (componentRoots (rootCharHom a) i).ncard = 6) :
    ∃ γ₁ γ₂ : Fin τ.rank → ℤ, IsA2Pair τ γ₁ γ₂ ∧
      componentRoots (rootCharHom a) i = {γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)} ∧
      ∀ ω : Lˣ, ω ^ 3 = 1 → ω ≠ 1 →
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ j, a j = ω ^ (ε * a2Exp τ γ₁ γ₂ j) := by
  obtain ⟨ω₀, e, V, b, k, hkκ, hω₀, he3, hae, he0, rfl, hkV, hV, hok, hSpec⟩ :=
    class_extract cap okS h a ha i
  have hn := ncard_componentRoots_eq hSpec hV hkV hkκ
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a)
    (Quotient.mk (kernelRootSetoid (rootCharHom a)) ⟨rt τ k, hkκ⟩)
  have himg := componentRoots_eq_image hSpec hV hkV hkκ
  rw [hn] at hi
  obtain ⟨h1, h2⟩ := cnt_spec cap V
  have hc6 : cnt cap V = 6 := by
    by_cases hlt : cnt cap V < cap
    · rw [← h2 hlt, hi]
    · have := h1 (le_antisymm (cnt_le cap V) (not_lt.1 hlt))
      omega
  simp only [okC, hc6, Bool.and_eq_true, bne_self_eq_false, Bool.false_or] at hok
  have hglue := hok.2
  unfold glue at hglue
  rcases hm : memb 6 V with _ | ⟨k₁, ks⟩
  · rw [hm] at hglue; simp at hglue
  · rw [hm] at hglue
    obtain ⟨k₂, hk₂ks, hwit⟩ := List.any_eq_true.1 hglue
    have hk₁V : V.testBit k₁ = true := testBit_of_mem_memb _ _ _ (by rw [hm]; simp)
    have hk₂V : V.testBit k₂ = true :=
      testBit_of_mem_memb _ _ _ (by rw [hm]; exact List.mem_cons_of_mem _ hk₂ks)
    have hk₁N := ((hSpec.K_iff k₁).1 (hV.reach k₁ hk₁V).1).1
    have hk₂N := ((hSpec.K_iff k₂).1 (hV.reach k₂ hk₂V).1).1
    obtain ⟨hA2, ε, hε, hdvd⟩ := a2Wit_spec hk₁N hk₂N e hwit
    have hmem : ∀ {x : ℕ}, V.testBit x = true → rt τ x ∈
        componentRoots (rootCharHom a) (Quotient.mk (kernelRootSetoid (rootCharHom a)) ⟨rt τ k, hkκ⟩) :=
      fun hx => by rw [himg]; exact ⟨_, hx, rfl⟩
    refine ⟨rt τ k₁, rt τ k₂, hA2, ?_, glue_algebra a ω₀ e _ ε hε hω₀ hae he0 hdvd⟩
    symm
    refine Set.eq_of_subset_of_ncard_le (a2_six_subset hΨ hA2 (hmem hk₁V) (hmem hk₂V)) ?_
      (Set.finite_of_ncard_pos (by rw [hn, hi]; norm_num))
    rw [a2_six_ncard hA2, hn, hi]

end Extract

end RD

end CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
