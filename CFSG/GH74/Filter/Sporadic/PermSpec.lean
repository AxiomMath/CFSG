module

public import CFSG.GH74.Filter.Sporadic.Spec
public import Certificates.Data.CFSGNative.Filter.PermSec

public section

namespace CFSG.SectionRank

open CFSG.GH74 CFSG.GH74.Filter CFSG.SectionRank.Native

@[expose] def PermRel (n : ℕ) (X : Array ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  X.size = n ∧ ∀ i : Fin n, X[i.val]! = (σ i : ℕ)

instance (n : ℕ) (X : Array ℕ) (σ : Equiv.Perm (Fin n)) : Decidable (PermRel n X σ) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem permMul_getElem! (n : ℕ) (P Q : Array ℕ) {i : ℕ} (hi : i < n) :
    (permMul n P Q)[i]! = P[Q[i]!]! := by
  rw [permMul, getElem!_pos (Array.ofFn _) i (by simpa using hi), Array.getElem_ofFn]

theorem PermRel.mul {n : ℕ} {A B : Array ℕ} {σ τ : Equiv.Perm (Fin n)} (hA : PermRel n A σ)
    (hB : PermRel n B τ) : PermRel n (permMul n A B) (σ * τ) := by
  refine ⟨by simp [permMul], fun i => ?_⟩
  rw [permMul_getElem! n A B i.isLt, hB.2 i, hA.2 (τ i)]
  rfl

theorem PermRel.one (n : ℕ) : PermRel n (permId n) 1 := by
  refine ⟨by simp [permId], fun i => ?_⟩
  rw [permId, getElem!_pos (Array.ofFn _) i.val (by simp), Array.getElem_ofFn]
  rfl

theorem PermRel.eq_iff {n : ℕ} {A B : Array ℕ} {σ τ : Equiv.Perm (Fin n)} (hA : PermRel n A σ)
    (hB : PermRel n B τ) : A = B ↔ σ = τ := by
  constructor
  · rintro rfl
    ext i
    have h1 := hA.2 i
    have h2 := hB.2 i
    rw [h1] at h2
    exact h2
  · rintro rfl
    refine Array.ext (hA.1.trans hB.1.symm) fun i hi₁ hi₂ => ?_
    have h1 := hA.2 ⟨i, hA.1 ▸ hi₁⟩
    have h2 := hB.2 ⟨i, hA.1 ▸ hi₁⟩
    rw [getElem!_pos A i hi₁] at h1
    rw [getElem!_pos B i hi₂] at h2
    exact h1.trans h2.symm

section Generic

variable {M V G : Type} [Group G] {O : Ops M V} {rel : M → G → Prop}

theorem pow_rel (hmul : ∀ {X Y g h}, rel X g → rel Y h → rel (O.mul X Y) (g * h))
    (hone : rel O.one 1) {X : M} {g : G} (hX : rel X g) (e : ℕ) : rel (O.pow X e) (g ^ e) := by
  induction e using Nat.strong_induction_on generalizing X g with
  | _ e ih =>
    rw [Ops.pow]
    by_cases he : e = 0
    · rw [ite_eq_left he, he, pow_zero]
      exact hone
    rw [ite_eq_right he]
    by_cases he1 : e = 1
    · rw [ite_eq_left he1, he1, pow_one]
      exact hX
    rw [ite_eq_right he1]
    have hY := ih (e / 2) (by omega) (hmul hX hX)
    rw [← sq, ← pow_mul] at hY
    by_cases ho : e % 2 = 1
    · rw [ite_eq_left ho]
      have := hmul hX hY
      rwa [← pow_succ', show 2 * (e / 2) + 1 = e by omega] at this
    · rw [ite_eq_right ho]
      rwa [show 2 * (e / 2) = e by omega] at hY

theorem pairwise_of_commsOK_rel
    (hmul : ∀ {X Y g h}, rel X g → rel Y h → rel (O.mul X Y) (g * h))
    (heq : ∀ {X Y g h}, rel X g → rel Y h → O.eq X Y = true → g = h) :
    ∀ {xs : List M}, O.commsOK xs = true →
      xs.Pairwise fun X Y => ∀ g h, rel X g → rel Y h → g * h = h * g
  | [], _ => List.Pairwise.nil
  | X :: xs, h => by
    rw [Ops.commsOK, Bool.and_eq_true, List.all_eq_true] at h
    refine List.pairwise_cons.2 ⟨fun Y hY g g' hg hg' => ?_,
      pairwise_of_commsOK_rel hmul heq h.2⟩
    exact heq (hmul hg hg') (hmul hg' hg) (h.1 Y hY)

theorem prodDigits_rel (hmul : ∀ {X Y g h}, rel X g → rel Y h → rel (O.mul X Y) (g * h))
    (hone : rel O.one 1) :
    ∀ (xs : List M) (gs : Fin xs.length → G), (∀ i, rel xs[i] (gs i)) →
      ∀ a : Fin xs.length → Fin 2,
        rel (O.prodDigits 2 xs (enc2 _ a)) (List.ofFn fun i => gs i ^ (a i : ℕ)).prod
  | [], gs, _, a => by simpa [Ops.prodDigits, enc2] using hone
  | X :: xs, gs, hg, a => by
    have h0 := (a 0).isLt
    have hd : (enc2 (xs.length + 1) a) % 2 = (a 0 : ℕ) := by rw [enc2]; omega
    have hq : (enc2 (xs.length + 1) a) / 2 = enc2 xs.length (Fin.tail a) := by rw [enc2]; omega
    have h1 := pow_rel hmul hone (hg 0) (a 0 : ℕ)
    have h2 := prodDigits_rel hmul hone xs (fun i => gs i.succ) (fun i => hg i.succ)
      (Fin.tail a)
    change rel (O.mul (O.pow X (enc2 (xs.length + 1) a % 2))
      (O.prodDigits 2 xs (enc2 (xs.length + 1) a / 2))) _
    rw [hd, hq, List.ofFn_succ, List.prod_cons]
    exact hmul h1 h2

variable [Inhabited M]

def RegsRel (rel : M → G → Prop) (R : Array M) : Prop := ∀ r < R.size, ∃ g, rel R[r]! g

theorem step_rel (hmul : ∀ {X Y g h}, rel X g → rel Y h → rel (O.mul X Y) (g * h))
    (hone : rel O.one 1) {R : Array M} (hR : RegsRel rel R) {op : Op}
    (hop : op.lt R.size = true) :
    (O.step R op).size = R.size ∧ RegsRel rel (O.step R op) := by
  cases op with
  | mul i j k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨⟨hi, hj⟩, hk⟩ := hop
    have hs : (O.step R (.mul i j k)).size = R.size := by
      simp [Ops.step, Array.set!]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    simp only [Ops.step, Array.set!]
    rw [OpsSpec.getElem!_setIfInBounds_of_lt hr]
    split
    · obtain ⟨gi, mi⟩ := hR i hi
      obtain ⟨gj, mj⟩ := hR j hj
      exact ⟨gi * gj, hmul mi mj⟩
    · exact hR r hr
  | pow e i k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨hi, hk⟩ := hop
    have hs : (O.step R (.pow e i k)).size = R.size := by
      simp [Ops.step, Array.set!]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    simp only [Ops.step, Array.set!]
    rw [OpsSpec.getElem!_setIfInBounds_of_lt hr]
    split
    · obtain ⟨gi, mi⟩ := hR i hi
      exact ⟨gi ^ e, pow_rel hmul hone mi e⟩
    · exact hR r hr

theorem run_rel (hmul : ∀ {X Y g h}, rel X g → rel Y h → rel (O.mul X Y) (g * h))
    (hone : rel O.one 1) (prog : List Op) {R : Array M} (hR : RegsRel rel R)
    (hprog : prog.all (Op.lt R.size) = true) :
    (O.run prog R).size = R.size ∧ RegsRel rel (O.run prog R) := by
  induction prog generalizing R with
  | nil => exact ⟨rfl, hR⟩
  | cons op prog ih =>
    rw [List.all_cons, Bool.and_eq_true] at hprog
    obtain ⟨hs, hok⟩ := step_rel hmul hone hR hprog.1
    have := ih hok (by rw [hs]; exact hprog.2)
    simp only [Ops.run, List.foldl_cons] at this ⊢
    rw [this.1, hs]
    exact ⟨rfl, this.2⟩

theorem initRegs_rel (hone : rel O.one 1) {A B : M} {gA gB : G} (hA : rel A gA)
    (hB : rel B gB) (n : ℕ) : (O.initRegs A B n).size = n ∧ RegsRel rel (O.initRegs A B n) := by
  have hs : (O.initRegs A B n).size = n := by simp [Ops.initRegs]
  refine ⟨hs, fun r hr => ?_⟩
  rw [hs] at hr
  unfold Ops.initRegs
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
  split
  · exact ⟨gA, hA⟩
  split
  · exact ⟨gB, hB⟩
  · exact ⟨1, hone⟩

theorem exists_of_invsCheck
    (hmul : ∀ {X Y g h}, rel X g → rel Y h → rel (O.mul X Y) (g * h))
    (hone : rel O.one 1)
    (heq : ∀ {X Y g h}, rel X g → rel Y h → O.eq X Y = true → g = h)
    (hne : ∀ {X Y g h}, rel X g → rel Y h → O.eq X Y = false → g ≠ h)
    {A B : M} {gA gB : G} (hA : rel A gA) (hB : rel B gB) {nregs : ℕ} {prog : List Op}
    {outs : List ℕ} (h : O.invsCheck A B nregs prog outs = true) :
    ∃ r : ℕ, r = outs.length ∧ ∃ x : Fin r → G, (∀ i, x i ^ 2 = 1) ∧
      (∀ i j, Commute (x i) (x j)) ∧
      ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1 := by
  unfold Ops.invsCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hprog⟩, houts⟩, hinv⟩ := h
  obtain ⟨hs0, hok0⟩ := initRegs_rel hone hA hB nregs
  obtain ⟨hs, hok⟩ := run_rel hmul hone prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run prog (O.initRegs A B nregs)
  rw [hs0] at hs
  set xs := outs.map fun r => R[r]! with hxsdef
  have hxs : ∀ X ∈ xs, ∃ g, rel X g := by
    intro X hX
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact hok r (by rw [hs]; exact of_decide_eq_true (List.all_eq_true.1 houts r hr))
  choose gs hgs using fun i : Fin xs.length => hxs xs[i] (List.getElem_mem i.isLt)
  unfold Ops.invsOK at hinv
  simp only [Bool.and_eq_true] at hinv
  obtain ⟨⟨hsq, hcomm⟩, hker⟩ := hinv
  have hpair := pairwise_of_commsOK_rel hmul heq hcomm
  refine ⟨xs.length, List.length_map _, gs, fun i => ?_, fun i j => ?_, fun a ha => ?_⟩
  · have h1 := List.all_eq_true.1 hsq xs[i] (List.getElem_mem i.isLt)
    have := heq (hmul (hgs i) (hgs i)) hone h1
    rwa [← sq] at this
  · rcases lt_trichotomy i j with hij | rfl | hij
    · exact List.pairwise_iff_getElem.1 hpair i j i.isLt j.isLt hij _ _ (hgs i) (hgs j)
    · exact Commute.refl _
    · exact (List.pairwise_iff_getElem.1 hpair j i j.isLt i.isLt hij _ _ (hgs j) (hgs i)).symm
  · have hlt := enc2_lt _ a
    have hpos : enc2 _ a ≠ 0 := fun h0 => ha (eq_zero_of_enc2_eq_zero _ a h0)
    unfold Ops.prodKerOK at hker
    rw [List.all_eq_true] at hker
    have h1 := hker (enc2 _ a - 1) (List.mem_range.2 (by omega))
    rw [show enc2 _ a - 1 + 1 = enc2 _ a by omega] at h1
    have h2 : O.eq (O.prodDigits 2 xs (enc2 _ a)) O.one = false := by simpa using h1
    exact hne (prodDigits_rel hmul hone xs gs hgs a) hone h2

end Generic

theorem exists_of_permCheck {n : ℕ} (D : PermData) {σA σB : Equiv.Perm (Fin n)}
    (hA : PermRel n D.seedA σA) (hB : PermRel n D.seedB σB) (h : permCheck n D = true) :
    ∃ r : ℕ, r = D.outs.length ∧
      ∃ x : Fin r → (Subgroup.closure {σA, σB} : Subgroup (Equiv.Perm (Fin n))),
        (∀ i, x i ^ 2 = 1) ∧ (∀ i j, Commute (x i) (x j)) ∧
        ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1 := by
  let rel : Array ℕ → (Subgroup.closure {σA, σB} : Subgroup (Equiv.Perm (Fin n))) → Prop :=
    fun X g => PermRel n X (g : Equiv.Perm (Fin n))
  have hmul : ∀ {X Y g h}, rel X g → rel Y h → rel ((permOps n).mul X Y) (g * h) :=
    fun hX hY => hX.mul hY
  have hone : rel (permOps n).one 1 := PermRel.one n
  have heq : ∀ {X Y g h}, rel X g → rel Y h → (permOps n).eq X Y = true → g = h := by
    intro X Y g h hX hY hXY
    exact Subtype.ext ((hX.eq_iff hY).1 (beq_iff_eq.1 hXY))
  have hne : ∀ {X Y g h}, rel X g → rel Y h → (permOps n).eq X Y = false → g ≠ h := by
    intro X Y g h hX hY hXY hgh
    have : X = Y := (hX.eq_iff hY).2 (congrArg Subtype.val hgh)
    subst this
    simp [permOps] at hXY
  exact exists_of_invsCheck hmul hone heq hne
    (gA := ⟨σA, Subgroup.subset_closure (Set.mem_insert _ _)⟩)
    (gB := ⟨σB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩) hA hB h

theorem not_gen4_of_permCheck {n : ℕ} (D : PermData) {σA σB : Equiv.Perm (Fin n)}
    (hA : PermRel n D.seedA σA) (hB : PermRel n D.seedB σB) (h : permCheck n D = true)
    (hr : 5 ≤ D.outs.length) :
    ¬ Gen4 (Subgroup.closure {σA, σB} : Subgroup (Equiv.Perm (Fin n))) := by
  obtain ⟨r, hrr, x, hsq, hcomm, hker⟩ := exists_of_permCheck D hA hB h
  exact not_gen4_of_commuting_involutions (by omega) x hsq hcomm hker

end CFSG.SectionRank
