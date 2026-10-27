module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice
open scoped Matrix

set_option linter.unusedSectionVars false


@[expose] def orbL (n : ℕ) (M : List (List ℤ)) (b : List ℤ) : ℕ → List ℤ
  | 0 => b
  | k + 1 => lmulVec n M (orbL n M b k)

@[expose] def lform (n : ℕ) (C : List (List ℤ)) (u v : List ℤ) : ℤ :=
  (List.ofFn fun a : Fin n => vget u a * (List.ofFn fun b : Fin n => lget C a b * vget v b).sum).sum

@[expose] def reflL (n : ℕ) (C : List (List ℤ)) (a c : List ℤ) : List ℤ :=
  vadd n c (vsmul n (-(2 * lform n C a c / lform n C a a)) a)

@[expose] def RankOneChk (n : ℕ) (C M : List (List ℤ)) (R : List (List ℤ)) (b : List ℤ)
    (m : ℕ) : Prop :=
  0 < m ∧ b ∈ R ∧ (orbL n M b m = b ∨ orbL n M b m = vsmul n (-1) b) ∧
    ∀ j < m, ∀ k < m, j < k → lform n C (orbL n M b j) (orbL n M b k) = 0 ∧
      R.contains (vadd n (orbL n M b j) (orbL n M b k)) = false ∧
      R.contains (vadd n (orbL n M b j) (vsmul n (-1) (orbL n M b k))) = false

instance (n : ℕ) (C M : List (List ℤ)) (R : List (List ℤ)) (b : List ℤ) (m : ℕ) :
    Decidable (RankOneChk n C M R b m) := by
  unfold RankOneChk
  infer_instance

@[expose] def goodM (n : ℕ) (C M : List (List ℤ)) (R : List (List ℤ)) (b : List ℤ) (e : ℕ) :
    Option ℕ :=
  ((List.range 4).map (· + 1)).find? fun m => decide (RankOneChk n C M R b m) && decide (e ∣ 2 * m)

@[expose] def certStep (n : ℕ) (C : List (List ℤ)) (R : List (List ℤ)) :
    List (ℕ × ℕ × ℕ) → List ℕ → Option (List ℕ)
  | [], kn => some kn
  | (g, a, c) :: rest, kn =>
    if (decide (g < R.length) && kn.contains a && kn.contains c &&
        R.getD g [] == reflL n C (R.getD a []) (R.getD c [])) = true then
      certStep n C R rest (g :: kn)
    else none

@[expose] def classCheck (n : ℕ) (C M : List (List ℤ)) (R : List (List ℤ)) (e : ℕ)
    (cert : List (ℕ × ℕ × ℕ)) : Bool :=
  R.all (fun r => r.length == n) &&
    match certStep n C R cert ((List.range R.length).filter fun i =>
        (goodM n C M R (R.getD i []) e).isSome) with
    | some kn => (List.range R.length).all kn.contains
    | none => false

section Sound

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem ofFn_toVec {n : ℕ} {u : List ℤ} (hu : u.length = n) : List.ofFn (toVec n u) = u := by
  apply List.ext_getElem
  · simp [hu]
  · intro i h1 h2
    simp [toVec, vget, List.getD_eq_getElem?_getD, h2]

theorem isRoot_toVec_iff {u : List ℤ} (hu : u.length = τ.rank) :
    IsRoot τ (toVec τ.rank u) ↔ u ∈ τ.artifactRoots := by
  rw [isRoot_iff_mem_artifactRoots, ofFn_toVec hu]

theorem length_vadd (n : ℕ) (u v : List ℤ) : (vadd n u v).length = n := by simp [vadd, vofFn]

theorem length_vsmul (n : ℕ) (c : ℤ) (v : List ℤ) : (vsmul n c v).length = n := by
  simp [vsmul, vofFn]

theorem length_lmulVec (n : ℕ) (A : List (List ℤ)) (v : List ℤ) : (lmulVec n A v).length = n := by
  simp [lmulVec, vofFn]

theorem length_orbL {n : ℕ} (M : List (List ℤ)) {b : List ℤ} (hb : b.length = n) (k : ℕ) :
    (orbL n M b k).length = n := by
  cases k with
  | zero => exact hb
  | succ k => exact length_lmulVec n M _

theorem iform_toVec_eq_lform (hτ : SimplyLacedTag τ) {C : List (List ℤ)}
    (hC : toMat τ.rank C = τ.cartan) (u v : List ℤ) :
    iform (toVec τ.rank u) (toVec τ.rank v) = lform τ.rank C u v := by
  have hB : τ.symmetrizedCartan = τ.cartan := by
    rcases hτ with rfl | rfl | rfl | rfl <;> simp [Tag.symmetrizedCartan, Tag.symmetrizer]
  rw [← dotProduct_mulVec_eq_iform, hB, ← hC]
  simp only [lform, dotProduct, Matrix.mulVec, List.sum_ofFn]
  rfl

theorem toVec_orbL {M : List (List ℤ)} (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = toMat τ.rank M *ᵥ γ)
    {b : List ℤ} (hb : IsRoot τ (toVec τ.rank b)) (k : ℕ) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[k] (toVec τ.rank b) = toVec τ.rank (orbL τ.rank M b k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, orbL, toVec_lmulVec, ← hρ]
    rw [← ih]
    exact S.iterate_isRoot k hb

theorem rankOneOrbit_of_check (hτ : SimplyLacedTag τ) {C M : List (List ℤ)}
    (hC : toMat τ.rank C = τ.cartan)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = toMat τ.rank M *ᵥ γ)
    (hR : ∀ r ∈ τ.artifactRoots, r.length = τ.rank) {b : List ℤ} {m : ℕ}
    (h : RankOneChk τ.rank C M τ.artifactRoots b m) :
    RankOneOrbit S.ρ (toVec τ.rank b) m := by
  obtain ⟨hm0, hbR, hper, horth⟩ := h
  have hblen := hR b hbR
  have hbroot : IsRoot τ (toVec τ.rank b) := (isRoot_toVec_iff hblen).2 hbR
  refine ⟨hbroot, hm0, ?_, ?_⟩
  · rw [toVec_orbL S hρ hbroot]
    rcases hper with h | h
    · left; rw [h]
    · right
      rw [h, toVec_vsmul, neg_one_smul]
  · intro j k hjk hkm
    obtain ⟨hform, hp, hm'⟩ := horth j (by omega) k hkm hjk
    rw [toVec_orbL S hρ hbroot, toVec_orbL S hρ hbroot]
    refine ⟨by rw [iform_toVec_eq_lform hτ hC, hform], ?_, ?_⟩
    · intro hroot
      have hl : (vadd τ.rank (orbL τ.rank M b j) (orbL τ.rank M b k)).length = τ.rank :=
        length_vadd _ _ _
      have : toVec τ.rank (orbL τ.rank M b j) + toVec τ.rank (orbL τ.rank M b k) =
          toVec τ.rank (vadd τ.rank (orbL τ.rank M b j) (orbL τ.rank M b k)) :=
        (toVec_vadd _ _ _).symm
      rw [this, isRoot_toVec_iff hl] at hroot
      have := List.contains_iff_mem.2 hroot
      rw [this] at hp
      exact Bool.noConfusion hp
    · intro hroot
      have hl : (vadd τ.rank (orbL τ.rank M b j)
          (vsmul τ.rank (-1) (orbL τ.rank M b k))).length = τ.rank := length_vadd _ _ _
      have : toVec τ.rank (orbL τ.rank M b j) - toVec τ.rank (orbL τ.rank M b k) =
          toVec τ.rank (vadd τ.rank (orbL τ.rank M b j)
            (vsmul τ.rank (-1) (orbL τ.rank M b k))) := by
        rw [toVec_vadd, toVec_vsmul, neg_one_smul, sub_eq_add_neg]
      rw [this, isRoot_toVec_iff hl] at hroot
      have := List.contains_iff_mem.2 hroot
      rw [this] at hm'
      exact Bool.noConfusion hm'

theorem goodM_spec {n : ℕ} {C M : List (List ℤ)} {R : List (List ℤ)} {b : List ℤ} {e m : ℕ}
    (h : goodM n C M R b e = some m) : RankOneChk n C M R b m ∧ e ∣ 2 * m := by
  have := List.find?_some h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

theorem dvd_pow_sub_one_of_orderOf {p q e k : ℕ} (hp : p.Prime) (hq : 0 < q)
    (he : orderOf ((q : ℕ) : ZMod p) = e) (hk : e ∣ k) : p ∣ q ^ k - 1 := by
  have h1 : ((q : ℕ) : ZMod p) ^ k = 1 := orderOf_dvd_iff_pow_eq_one.1 (he ▸ hk)
  have h2 : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h2, Nat.cast_pow, h1, Nat.cast_one, sub_self]

theorem isGoodRoot_of_goodM (hτ : SimplyLacedTag τ) {C M : List (List ℤ)}
    (hC : toMat τ.rank C = τ.cartan)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = toMat τ.rank M *ᵥ γ)
    (hR : ∀ r ∈ τ.artifactRoots, r.length = τ.rank) (hq3 : 3 ≤ S.D.q) (hp7 : 7 ≤ p) {e : ℕ}
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) {b : List ℤ} {m : ℕ}
    (h : goodM τ.rank C M τ.artifactRoots b e = some m) : IsGoodRoot S (toVec τ.rank b) := by
  obtain ⟨hchk, hdvd⟩ := goodM_spec h
  exact isGoodRoot_of_rankOneOrbit S hτ (rankOneOrbit_of_check S hτ hC hρ hR hchk) hq3 hp7
    (dvd_pow_sub_one_of_orderOf S.hp (by omega) he hdvd)

theorem certStep_sound (hτ : SimplyLacedTag τ) {C : List (List ℤ)}
    (hC : toMat τ.rank C = τ.cartan) (hR : ∀ r ∈ τ.artifactRoots, r.length = τ.rank)
    {G : Set (Fin τ.rank → ℤ)} :
    ∀ (cert : List (ℕ × ℕ × ℕ)) (kn kn' : List ℕ),
      (∀ i ∈ kn, i < τ.artifactRoots.length ∧
        ReflClosure τ G (toVec τ.rank (τ.artifactRoots.getD i []))) →
      certStep τ.rank C τ.artifactRoots cert kn = some kn' →
      ∀ i ∈ kn', i < τ.artifactRoots.length ∧
        ReflClosure τ G (toVec τ.rank (τ.artifactRoots.getD i [])) := by
  intro cert
  induction cert with
  | nil =>
    intro kn kn' hkn h
    simp only [certStep, Option.some.injEq] at h
    subst h
    exact hkn
  | cons t rest ih =>
    obtain ⟨g, a, c⟩ := t
    intro kn kn' hkn h
    simp only [certStep] at h
    split_ifs at h with hcond
    · simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq] at hcond
      obtain ⟨⟨⟨hg, ha⟩, hc⟩, hgeq⟩ := hcond
      refine ih (g :: kn) kn' ?_ h
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨hg, ?_⟩
        obtain ⟨haR, haC⟩ := hkn a ha
        obtain ⟨hcR, hcC⟩ := hkn c hc
        have haM : τ.artifactRoots.getD a [] ∈ τ.artifactRoots := by
          rw [List.getD_eq_getElem _ _ haR]
          exact List.getElem_mem haR
        have hαroot : IsRoot τ (toVec τ.rank (τ.artifactRoots.getD a [])) :=
          (isRoot_toVec_iff (hR _ haM)).2 haM
        have := ReflClosure.refl hαroot haC hcC
        rw [hgeq, reflL, toVec_vadd, toVec_vsmul, ← iform_toVec_eq_lform hτ hC,
          ← iform_toVec_eq_lform hτ hC, neg_smul, ← sub_eq_add_neg]
        exact this
      · exact hkn i hi

theorem goodRootsGenerate_of_classCheck (hτ : SimplyLacedTag τ) {C M : List (List ℤ)}
    (hC : toMat τ.rank C = τ.cartan)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = toMat τ.rank M *ᵥ γ) (hq3 : 3 ≤ S.D.q) (hp7 : 7 ≤ p)
    {e : ℕ} (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) {cert : List (ℕ × ℕ × ℕ)}
    (h : classCheck τ.rank C M τ.artifactRoots e cert = true) : GoodRootsGenerate S := by
  unfold classCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hR, h⟩ := h
  split at h
  · rename_i kn' hkn'
    intro γ hγ
    have hγR : List.ofFn γ ∈ τ.artifactRoots := (isRoot_iff_mem_artifactRoots).1 hγ
    obtain ⟨i, hi, hiγ⟩ := List.getElem_of_mem hγR
    have hmem := List.all_eq_true.1 h i (List.mem_range.2 hi)
    have hbase : ∀ i ∈ (List.range τ.artifactRoots.length).filter (fun i =>
        (goodM τ.rank C M τ.artifactRoots (τ.artifactRoots.getD i []) e).isSome),
        i < τ.artifactRoots.length ∧
          ReflClosure τ {β | IsGoodRoot S β} (toVec τ.rank (τ.artifactRoots.getD i [])) := by
      intro i hi
      rw [List.mem_filter, List.mem_range] at hi
      obtain ⟨hiR, hi⟩ := hi
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (by simpa using hi)
      exact ⟨hiR, ReflClosure.base (isGoodRoot_of_goodM S hτ hC hρ hR hq3 hp7 he hm)⟩
    obtain ⟨-, hcl⟩ := certStep_sound hτ hC hR _ _ _ hbase hkn' i (List.contains_iff_mem.1 hmem)
    have : toVec τ.rank (τ.artifactRoots.getD i []) = γ := by
      rw [List.getD_eq_getElem _ _ hi, hiγ]
      exact toVec_vofFn γ
    rwa [this] at hcl
  · exact absurd h (by simp)

end Sound

end CFSG.HardMathSupport.Timmesfeld.LangTorus
