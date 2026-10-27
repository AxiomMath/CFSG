module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeSound

public section

namespace CFSG.AGLEmbedding.R3

@[expose] def toMatL (p n : ℕ) (L : List ℕ) : Matrix (Fin n) (Fin n) (ZMod p) :=
  fun k i => ((L.getD (n * k.val + i.val) 0 : ℕ) : ZMod p)

theorem actMatN_eq_toMatL (p n : ℕ) (g : NAct) : actMatN p n g = toMatL p n g.mat := rfl

theorem foldl_add_range (f : ℕ → ℕ) (n a : ℕ) :
    (List.range n).foldl (fun acc j => acc + f j) a = a + ∑ j ∈ Finset.range n, f j := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp [add_assoc]

theorem idx_div (n i j : ℕ) (hj : j < n) : (n * i + j) / n = i := by
  have hn : 0 < n := by omega
  rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hj, add_zero]

theorem idx_mod (n i j : ℕ) (hj : j < n) : (n * i + j) % n = j := by
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hj

theorem getD_map_range {α : Type*} [Zero α] (f : ℕ → α) (N idx : ℕ) (h : idx < N) :
    ((List.range N).map f).getD idx 0 = f idx := by
  simp [List.getD_eq_getElem?_getD, h]

theorem toMatL_mmulL (p n : ℕ) (A B : List ℕ) :
    toMatL p n (mmulL p n A B) = toMatL p n A * toMatL p n B := by
  ext i j
  have hi : i.val < n := i.2
  have hj : j.val < n := j.2
  have hidx : n * i.val + j.val < n * n := by nlinarith
  simp only [toMatL, mmulL, Matrix.mul_apply]
  rw [getD_map_range _ _ _ hidx, idx_div n i.val j.val hj, idx_mod n i.val j.val hj,
    foldl_add_range, ZMod.natCast_mod, zero_add, Nat.cast_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

theorem toMatL_midL (p n : ℕ) : toMatL p n (midL p n) = 1 := by
  ext i j
  have hi : i.val < n := i.2
  have hj : j.val < n := j.2
  have hidx : n * i.val + j.val < n * n := by nlinarith
  simp only [toMatL, midL]
  rw [getD_map_range _ _ _ hidx, idx_div n i.val j.val hj, idx_mod n i.val j.val hj,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [ZMod.natCast_mod]
  · have : i.val ≠ j.val := fun h' => h (Fin.ext h')
    simp [this, h]

theorem toMatL_mpowL (p n : ℕ) (A : List ℕ) :
    ∀ e : ℕ, toMatL p n (mpowL p n A e) = toMatL p n A ^ e
  | 0 => by rw [mpowL, toMatL_midL, pow_zero]
  | e + 1 => by rw [mpowL, toMatL_mmulL, toMatL_mpowL p n A e, pow_succ']

theorem length_mmulL (p n : ℕ) (A B : List ℕ) : (mmulL p n A B).length = n * n := by
  simp [mmulL]

theorem lt_mmulL (p n : ℕ) (hp : 0 < p) (A B : List ℕ) : ∀ x ∈ mmulL p n A B, x < p := by
  intro x hx
  simp only [mmulL, List.mem_map] at hx
  obtain ⟨idx, -, rfl⟩ := hx
  exact Nat.mod_lt _ hp

theorem length_midL (p n : ℕ) : (midL p n).length = n * n := by
  simp [midL]

theorem lt_midL (p n : ℕ) (hp : 1 < p) : ∀ x ∈ midL p n, x < p := by
  intro x hx
  simp only [midL, List.mem_map] at hx
  obtain ⟨idx, -, rfl⟩ := hx
  split_ifs
  · exact Nat.mod_lt _ (by omega)
  · omega

theorem length_mpowL (p n : ℕ) (A : List ℕ) : ∀ e : ℕ, (mpowL p n A e).length = n * n
  | 0 => length_midL p n
  | _ + 1 => length_mmulL p n A _

theorem wordsL_spec (p n : ℕ) (hp : 1 < p) :
    ∀ (As : List (List ℕ)), ∀ M ∈ wordsL p n As, M.length = n * n ∧ ∀ x ∈ M, x < p
  | [] => by
    intro M hM
    simp only [wordsL, List.mem_singleton] at hM
    subst hM
    exact ⟨length_midL p n, lt_midL p n hp⟩
  | A :: As => by
    intro M hM
    simp only [wordsL, List.mem_flatMap, List.mem_map, List.mem_range] at hM
    obtain ⟨M', -, a, -, rfl⟩ := hM
    exact ⟨length_mmulL p n _ _, lt_mmulL p n (by omega) _ _⟩

theorem toMatL_inj (p n : ℕ) {A B : List ℕ} (hA : A.length = n * n) (hB : B.length = n * n)
    (hAp : ∀ x ∈ A, x < p) (hBp : ∀ x ∈ B, x < p) (h : toMatL p n A = toMatL p n B) : A = B := by
  refine List.ext_getElem (hA.trans hB.symm) fun idx h1 h2 => ?_
  have hn : idx < n * n := hA ▸ h1
  have hdiv : idx / n < n := Nat.div_lt_of_lt_mul hn
  have hmod : idx % n < n := Nat.mod_lt _ (by nlinarith)
  have h3 := congrFun (congrFun h ⟨idx / n, hdiv⟩) ⟨idx % n, hmod⟩
  simp only [toMatL] at h3
  have hidx : n * (idx / n) + idx % n = idx := Nat.div_add_mod idx n
  rw [hidx] at h3
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at h3
  have h4 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h3
  rwa [Nat.mod_eq_of_lt (hAp _ (List.getElem_mem h1)),
    Nat.mod_eq_of_lt (hBp _ (List.getElem_mem h2))] at h4

section Acts

variable {X : Type} [Group X] {p : ℕ} [Fact p.Prime]

def ActsBy (D : ModuleSpec X p) (g : X) (A : Matrix (Fin D.n) (Fin D.n) (ZMod p)) : Prop :=
  ∀ i, g * D.a i * g⁻¹ = D.elt (fun k => A k i)

theorem elt_nsmul (D : ModuleSpec X p) (c : Fin D.n → ZMod p) (m : ℕ) :
    D.elt (m • c) = D.elt c ^ m := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  induction m with
  | zero => rw [zero_smul, D.elt_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, D.elt_add, ih, pow_succ]

theorem elt_list_sum (D : ModuleSpec X p) (v : Fin D.n → (Fin D.n → ZMod p)) :
    ∀ l : List (Fin D.n), (l.map fun k => D.elt (v k)).prod = D.elt (l.map v).sum
  | [] => by simp [D.elt_zero]
  | k :: l => by
    have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    simp only [List.map_cons, List.prod_cons, List.sum_cons, D.elt_add, elt_list_sum D v l]

theorem conj_elt (D : ModuleSpec X p) {g : X} {A : Matrix (Fin D.n) (Fin D.n) (ZMod p)}
    (hg : ActsBy D g A) (c : Fin D.n → ZMod p) : g * D.elt c * g⁻¹ = D.elt (A.mulVec c) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : g * D.elt c * g⁻¹ = (MulAut.conj g) (D.elt c) := (MulAut.conj_apply g _).symm
  rw [h1, ModuleSpec.elt, map_list_prod, List.map_map]
  set w : Fin D.n → (Fin D.n → ZMod p) := fun k => (c k).val • fun r => A r k with hw
  have h2 : ∀ k : Fin D.n, ((MulAut.conj g) ∘ fun k => D.a k ^ (c k).val) k = D.elt (w k) := by
    intro k
    rw [hw, elt_nsmul, ← hg k]
    simp [Function.comp_apply, MulAut.conj_apply]
  rw [List.map_congr_left (fun k _ => h2 k), elt_list_sum D w]
  congr 1
  rw [← Fin.sum_univ_def]
  funext r
  have hw' : ∀ k, w k r = c k * A r k := by
    intro k
    rw [hw]
    show ((c k).val • fun r => A r k) r = _
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [Finset.sum_apply]
  simp only [hw', Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem actsBy_one (D : ModuleSpec X p) : ActsBy D 1 1 := by
  intro i
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [inv_one, one_mul, mul_one, ← D.elt_single i]
  congr 1
  funext k
  simp [Matrix.one_apply, Pi.single_apply]

theorem actsBy_mul (D : ModuleSpec X p) {g h : X} {A B : Matrix (Fin D.n) (Fin D.n) (ZMod p)}
    (hg : ActsBy D g A) (hh : ActsBy D h B) : ActsBy D (g * h) (A * B) := by
  intro i
  have e1 : g * h * D.a i * (g * h)⁻¹ = g * (h * D.a i * h⁻¹) * g⁻¹ := by group
  rw [e1, hh i, conj_elt D hg]
  congr 1

theorem actsBy_pow (D : ModuleSpec X p) {g : X} {A : Matrix (Fin D.n) (Fin D.n) (ZMod p)}
    (hg : ActsBy D g A) : ∀ e : ℕ, ActsBy D (g ^ e) (A ^ e)
  | 0 => by rw [pow_zero, pow_zero]; exact actsBy_one D
  | e + 1 => by rw [pow_succ', pow_succ']; exact actsBy_mul D hg (actsBy_pow D hg e)

omit [Fact p.Prime] in
theorem actsBy_g (D : ModuleSpec X p) (j : Fin D.m) : ActsBy D (D.g j) (D.M j) :=
  fun i => (D.elt_col j i).symm

theorem card_ge_of_actsBy [Finite X] (D : ModuleSpec X p) (P : Subgroup X) (hEP : D.span ≤ P)
    {k : ℕ} (g : Fin k → X) (A : Fin k → Matrix (Fin D.n) (Fin D.n) (ZMod p))
    (hg : ∀ a, g a ∈ P) (hA : ∀ a, ActsBy D (g a) (A a))
    (hd : ∀ a b : Fin k, a ≠ b → A a ≠ A b) : k * Nat.card D.span ≤ Nat.card P := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let f : Fin k × D.span → P := fun x =>
    ⟨g x.1 * (x.2 : X), P.mul_mem (hg x.1) (hEP x.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, e⟩ ⟨b, e'⟩ h
    have h' : g a * (e : X) = g b * (e' : X) := congrArg Subtype.val h
    have hab : a = b := by
      by_contra hne
      apply hd a b hne
      ext r i
      have hcol : g a * D.a i * (g a)⁻¹ = g b * D.a i * (g b)⁻¹ := by
        have hga : g a = g b * ((e' : X) * (e : X)⁻¹) := by
          rw [← mul_assoc]
          exact eq_mul_inv_of_mul_eq h'
        have hc : ((e' : X) * (e : X)⁻¹) * D.a i = D.a i * ((e' : X) * (e : X)⁻¹) :=
          D.mul_comm_of_mem (D.span.mul_mem e'.2 (D.span.inv_mem e.2)) (D.a_mem_span i)
        calc g a * D.a i * (g a)⁻¹
            = g b * (((e' : X) * (e : X)⁻¹) * D.a i * ((e' : X) * (e : X)⁻¹)⁻¹) *
                (g b)⁻¹ := by rw [hga]; group
          _ = g b * D.a i * (g b)⁻¹ := by rw [hc]; group
      have := D.elt_injective (show D.elt (fun r => A a r i) = D.elt (fun r => A b r i) from by
        rw [← hA a i, ← hA b i, hcol])
      exact congrFun this r
    subst hab
    have : (e : X) = e' := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext this)
  calc k * Nat.card D.span = Nat.card (Fin k × D.span) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
    _ ≤ Nat.card P := Nat.card_le_card_of_injective f hf

theorem exists_mem_wordsL (D : ModuleSpec X p) (P : Subgroup X) :
    ∀ (As : List (List ℕ)), (∀ A ∈ As, ∃ q ∈ P, ActsBy D q (toMatL p D.n A)) →
      ∀ M ∈ wordsL p D.n As, ∃ g ∈ P, ActsBy D g (toMatL p D.n M)
  | [], _, M, hM => by
    simp only [wordsL, List.mem_singleton] at hM
    subst hM
    exact ⟨1, P.one_mem, by rw [toMatL_midL]; exact actsBy_one D⟩
  | A :: As, hA, M, hM => by
    simp only [wordsL, List.mem_flatMap, List.mem_map, List.mem_range] at hM
    obtain ⟨M', hM', a, -, rfl⟩ := hM
    obtain ⟨q, hq, hqA⟩ := hA A List.mem_cons_self
    obtain ⟨g, hg, hgM⟩ := exists_mem_wordsL D P As
      (fun A' hA' => hA A' (List.mem_cons_of_mem _ hA')) M' hM'
    refine ⟨q ^ a * g, P.mul_mem (P.pow_mem hq a) hg, ?_⟩
    rw [toMatL_mmulL, toMatL_mpowL]
    exact actsBy_mul D (actsBy_pow D hqA a) hgM

end Acts

theorem pairwise_lt_of_zip : ∀ S : List ℕ, (∀ x ∈ S.zip S.tail, x.1 < x.2) → S.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    have hab : a < b := h (a, b) (by simp)
    have ih : (b :: rest).Pairwise (· < ·) :=
      pairwise_lt_of_zip (b :: rest) fun x hx => by
        have hx' : x ∈ (b :: rest).zip rest := by simpa using hx
        exact h x (by rw [List.tail_cons, List.zip_cons_cons]; exact List.mem_cons_of_mem _ hx')
    refine List.Pairwise.cons (fun y hy => ?_) ih
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hab
    · exact hab.trans (List.rel_of_pairwise_cons ih hy)

theorem pairwise_codes_of_wChk {p n s : ℕ} {L : List (List ℕ)} (h : wChk p n s L = true) :
    L.Pairwise (fun A B => codeL p A ≠ codeL p B) ∧ p ^ s ≤ L.length * p ^ n := by
  unfold wChk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  have hS := pairwise_lt_of_zip _ h1
  have hperm := List.mergeSort_perm (L.map (codeL p)) (fun a b => decide (a ≤ b))
  have h3 : (L.map (codeL p)).Pairwise (· ≠ ·) :=
    (hperm.pairwise_iff Ne.symm).1 (hS.imp fun hab => Nat.ne_of_lt hab)
  exact List.pairwise_map.1 h3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

section Main

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {p : ℕ} {m : NMod} {tops : List Pc}
  {tidx : List ℕ} {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
  {ct : ℕ → ℕ → ℕ → ℕ → ℤ}

include Sp in
theorem moduleDatum_of_modCheckW [Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ] (hp : p.Prime)
    {N s : ℕ} (hN : Nat.card (NativeSporadic.seedMonoid c d 1 sA sB)ˣ = N)
    (hv : p ^ s ∣ N ∧ ¬ p ^ (s + 1) ∣ N)
    (h : modCheckW O sA sB nregs prog p m tops tidx s cf ci ct = true) :
    ModuleDatum (NativeSporadic.seedMonoid c d 1 sA sB)ˣ p := by
  have : Fact p.Prime := ⟨hp⟩
  unfold modCheckW at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hw⟩, hpcwf⟩, hacts⟩, hwok⟩, hrank⟩, hfun⟩, halt⟩ := h
  let C : MCert := ⟨nregs, prog, m.modFactsW p tops⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.facts p, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFactsW p tops
    simp only [NMod.modFactsW, List.mem_append]
    exact Or.inl hf
  have hpcf : ∀ q ∈ tops ++ m.basisPc p, ∀ f ∈ q.facts p, f ∈ C.facts := by
    intro q hq f hqf
    show f ∈ m.modFactsW p tops
    unfold NMod.modFactsW
    refine List.mem_append.2 (Or.inr ?_)
    exact List.mem_flatMap.2 ⟨q, hq, hqf⟩
  let DS := NMod.spec Sp hC' m hf hw
  let P : Subgroup (certMonoid c d sA sB)ˣ :=
    Subgroup.closure {u | ∃ q ∈ tops ++ m.basisPc p, u = regUnit Sp hC' q.reg}
  have hPgrp : IsPGroup p P := chain_isPGroup Sp hC' (tops ++ m.basisPc p) hpcwf hpcf
  let qs : List (certMonoid c d sA sB)ˣ := tops.map fun q => regUnit Sp hC' q.reg
  let P' : Subgroup (certMonoid c d sA sB)ˣ := Subgroup.closure ((DS.span : Set _) ∪ {x | x ∈ qs})
  have hspanP : DS.span ≤ P := by
    rw [ModuleSpec.span, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨q, hq, hqreg⟩ : ∃ q ∈ m.basisPc p, q.reg = m.basis.getD i.val 0 :=
      ⟨_, List.mem_map.2 ⟨i.val, List.mem_range.2 i.2, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨q, List.mem_append.2 (Or.inr hq), by rw [hqreg]; rfl⟩
  have hqsP : ∀ x ∈ qs, x ∈ P := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨q, List.mem_append.2 (Or.inl hq), rfl⟩
  have hP'le : P' ≤ P := (Subgroup.closure_le P).2 (Set.union_subset hspanP hqsP)
  have hP'grp : IsPGroup p P' := IsPGroup.to_le hPgrp hP'le
  have hqsP' : ∀ x ∈ qs, x ∈ P' := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hspanP' : DS.span ≤ P' := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hP'norm : P' ≤ Subgroup.normalizer (DS.span : Set _) := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.le_normalizer hx
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      obtain ⟨g, hg, hgq⟩ := List.any_eq_true.1 (List.all_eq_true.1 hacts q hq)
      have hgq' : g.reg = q.reg := beq_iff_eq.1 hgq
      obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hg
      have := DS.g_mem_normalizer j
      show regUnit Sp hC' q.reg ∈ _
      rw [← hgq']
      exact this
  unfold NMod.wOK at hwok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwok
  obtain ⟨hidx, hchk⟩ := hwok
  obtain ⟨hcodes, hs⟩ := pairwise_codes_of_wChk hchk
  set L : List (List ℕ) :=
    wordsL p m.basis.length (tidx.map fun i => (m.acts.getD i default).mat) with hL
  have hget : ∀ i (hi : i < m.acts.length), m.acts.getD i default = m.acts.get ⟨i, hi⟩ := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rfl
  have hgen : ∀ A ∈ tidx.map (fun i => (m.acts.getD i default).mat),
      ∃ q ∈ P', ActsBy DS q (toMatL p DS.n A) := by
    intro A hA
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hA
    obtain ⟨hi1, hi2⟩ := hidx i hi
    obtain ⟨q, hq, hqreg⟩ := List.any_eq_true.1 hi2
    have hqreg' : q.reg = (m.acts.getD i default).reg := beq_iff_eq.1 hqreg
    refine ⟨DS.g ⟨i, hi1⟩, ?_, ?_⟩
    · have hgreg : DS.g ⟨i, hi1⟩ = regUnit Sp hC' (m.acts.get ⟨i, hi1⟩).reg := rfl
      rw [hgreg, ← hget i hi1, ← hqreg']
      exact hqsP' _ (List.mem_map.2 ⟨q, hq, rfl⟩)
    · have := actsBy_g DS ⟨i, hi1⟩
      rw [hget i hi1]
      exact this
  have hall := exists_mem_wordsL DS P' _ hgen
  have hex : ∀ a : Fin L.length, ∃ g ∈ P', ActsBy DS g (toMatL p DS.n (L.get a)) :=
    fun a => hall _ (List.get_mem L a)
  choose g hgP hgA using hex
  have hlen : ∀ a : Fin L.length, (L.get a).length = DS.n * DS.n ∧ ∀ x ∈ L.get a, x < p :=
    fun a => wordsL_spec p DS.n hp.one_lt _ _ (List.get_mem L a)
  have hdiff : ∀ a b : Fin L.length, a.val < b.val →
      toMatL p DS.n (L.get a) ≠ toMatL p DS.n (L.get b) := by
    intro a b hab hM
    have hcode := List.pairwise_iff_getElem.1 hcodes a.val b.val a.2 b.2 hab
    apply hcode
    have := toMatL_inj p DS.n (hlen a).1 (hlen b).1 (hlen a).2 (hlen b).2 hM
    show codeL p (L.get a) = codeL p (L.get b)
    rw [this]
  have hdist : ∀ a b : Fin L.length, a ≠ b →
      toMatL p DS.n (L.get a) ≠ toMatL p DS.n (L.get b) := by
    intro a b hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hdiff a b hlt
    · exact (hdiff b a hlt).symm
  have hlow : L.length * p ^ m.basis.length ≤ Nat.card P' := by
    have h := card_ge_of_actsBy DS P' hspanP' g (fun a => toMatL p DS.n (L.get a)) hgP hgA hdist
    rw [DS.card_span hp] at h
    exact h
  have hN0 : N ≠ 0 := by
    rw [← hN]
    exact Nat.card_pos.ne'
  obtain ⟨k, hk⟩ := hP'grp.exists_card_eq
  have hdvd : Nat.card P' ∣ N := hN ▸ Subgroup.card_subgroup_dvd_card P'
  have hs1 : s ≤ k := by
    have : p ^ s ≤ p ^ k := by
      rw [← hk]
      exact hs.trans hlow
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
  have hs2 : k ≤ s := by
    by_contra hlt
    apply hv.2
    exact (Nat.pow_dvd_pow p (not_le.1 hlt)).trans (hk ▸ hdvd)
  have hkeq : k = s := le_antisymm hs2 hs1
  have hfact : N.factorization p = s := by
    have h1 := (hp.pow_dvd_iff_le_factorization hN0).1 hv.1
    have h2 : ¬ s + 1 ≤ N.factorization p :=
      fun h => hv.2 ((hp.pow_dvd_iff_le_factorization hN0).2 h)
    omega
  have hcard : Nat.card P' = p ^ (Nat.card (certMonoid c d sA sB)ˣ).factorization p := by
    rw [hN, hfact, hk, hkeq]
  exact ⟨DS, hrank, fun B hB hinv => noAlt_of_altOK halt B hB hinv,
    fun v hv' => noFun_of_funOK hfun v hv', Sylow.ofCard P' hcard, hP'norm⟩

end Main

end CFSG.AGLEmbedding.R3
