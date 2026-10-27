module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalElt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
public import CFSG.Quasithin.H13.L32NKGSp6Search

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.Quasithin.H13 CFSG.Quasithin.G2U CFSG.KGroups.Sp6

theorem decodeC_mulC_all (A B : List ℕ) :
    KGCert.decodeC (mulC A B) = KGCert.decodeC A * KGCert.decodeC B := by
  ext i j
  by_cases hj : (j : ℕ) < B.length
  · have hget : (mulC A B).getD j 0 = mulVecC A (B.getD j 0) := by
      simp only [mulC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some]
    simp only [KGCert.decodeC, Matrix.of_apply, Matrix.mul_apply]
    rw [hget, show mulVecC A (B.getD j 0) = KGCert.mulVecC A (B.getD j 0) from rfl,
      ← KGCert.decodeC_mulVec]
    simp only [Matrix.mulVec, dotProduct, KGCert.decodeC, Matrix.of_apply]
  · have h1 : (mulC A B).getD j 0 = 0 := by
      have : ¬ (j : ℕ) < (mulC A B).length := by simpa [mulC] using hj
      rw [List.getD_eq_default _ _ (by omega)]
    have h2 : B.getD j 0 = 0 := by
      rw [List.getD_eq_default _ _ (by omega)]
    simp only [KGCert.decodeC, Matrix.of_apply, Matrix.mul_apply, h1, h2, KGCert.vec6_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem validB_iff {c : List ℕ} : validB c = true ↔ KGCert.ValidC c := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    KGCert.ValidC]

theorem validC_invC (c : List ℕ) : KGCert.ValidC (invC c) := by
  refine ⟨by simp [invC], fun x hx => ?_⟩
  simp only [invC, List.mem_map, List.mem_range] at hx
  obtain ⟨k, -, rfl⟩ := hx
  cases h : (List.range 64).find? fun y => mulVecC c y == 2 ^ k with
  | none => simp
  | some y =>
    have := List.mem_of_find?_eq_some h
    simpa using List.mem_range.1 this

@[expose] def Rep (g : H6) (t : List ℕ) : Prop := KGCert.ValidC t ∧ mat6 g = KGCert.decodeC t

theorem Rep.mul {g h : H6} {t s : List ℕ} (hg : Rep g t) (hh : Rep h s) :
    Rep (g * h) (mulC t s) :=
  ⟨KGCert.validC_mulC hg.1 hh.1, by rw [map_mul, hg.2, hh.2, decodeC_mulC_all]⟩

theorem Rep.one : Rep 1 oneC :=
  ⟨KGCert.validC_oneC, by rw [map_one]; exact KGCert.decodeC_oneC.symm⟩

theorem Rep.eq_iff {g h : H6} {t s : List ℕ} (hg : Rep g t) (hh : Rep h s) :
    g = h ↔ t = s := by
  constructor
  · rintro rfl
    exact KGCert.decodeC_injOn hg.1 hh.1 (hg.2.symm.trans hh.2)
  · rintro rfl
    exact mat6_injective (hg.2.trans hh.2.symm)

theorem Rep.eq {g h : H6} {t : List ℕ} (hg : Rep g t) (hh : Rep h t) : g = h :=
  (hg.eq_iff hh).2 rfl

theorem Rep.comm_iff {g h : H6} {t s : List ℕ} (hg : Rep g t) (hh : Rep h s) :
    g * h = h * g ↔ mulC t s = mulC s t :=
  (hg.mul hh).eq_iff (hh.mul hg)

theorem Rep.eq_one_iff {g : H6} {t : List ℕ} (hg : Rep g t) : g = 1 ↔ t = oneC :=
  hg.eq_iff Rep.one

theorem Rep.pow_three {g : H6} {t : List ℕ} (hg : Rep g t) :
    g ^ 3 = 1 ↔ mulC t (mulC t t) = oneC := by
  rw [_root_.pow_three]
  exact (hg.mul (hg.mul hg)).eq_one_iff

theorem Rep.inv_rep {g : H6} {t s : List ℕ} (hg : Rep g t) (hs : KGCert.ValidC s)
    (h : mulC t s = oneC) : Rep g⁻¹ s := by
  refine ⟨hs, ?_⟩
  have h1 : mat6 g * KGCert.decodeC s = 1 := by
    rw [hg.2, ← decodeC_mulC_all, h]
    exact KGCert.decodeC_oneC
  calc mat6 g⁻¹ = mat6 g⁻¹ * (mat6 g * KGCert.decodeC s) := by rw [h1, mul_one]
    _ = (mat6 g⁻¹ * mat6 g) * KGCert.decodeC s := by rw [mul_assoc]
    _ = KGCert.decodeC s := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

theorem isoMat_of_isoB {c : List ℕ} (h : isoB c = true) : IsoMat (KGCert.decodeC c) := by
  simp only [isoB, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨-, hc⟩ := h
  rw [IsoMat, ← KGSp6.cols_iff]
  intro i j
  have := hc i i.isLt j j.isLt
  simpa [KGSp6.jb] using this

open Classical in
@[irreducible] noncomputable def elt (c : List ℕ) : H6 :=
  if h : IsoMat (KGCert.decodeC c) then ofIso _ h else 1

theorem validC_of_isoB {c : List ℕ} (h : isoB c = true) : KGCert.ValidC c :=
  validB_iff.1 (by simp only [isoB, Bool.and_eq_true] at h; exact h.1)

theorem rep_elt {c : List ℕ} (h : isoB c = true) : Rep (elt c) c := by
  refine ⟨validC_of_isoB h, ?_⟩
  unfold elt
  rw [dite_eq_left_of_eq_true (eq_true (isoMat_of_isoB h))]
  exact mat6_ofIso _ _

theorem rep_elt_inv {c : List ℕ} (h : genB c = true) : Rep (elt c)⁻¹ (invC c) := by
  simp only [genB, Bool.and_eq_true, beq_iff_eq] at h
  exact (rep_elt h.1.1).inv_rep (validC_invC c) h.1.2

theorem genB_isoB {c : List ℕ} (h : genB c = true) : isoB c = true := by
  simp only [genB, Bool.and_eq_true] at h
  exact h.1.1

theorem rep_conj_elt {g x : List ℕ} {y : H6} (hg : genB g = true) (hy : Rep y x) :
    Rep (elt g * y * (elt g)⁻¹) (conjC g x) := by
  rw [mul_assoc]
  exact (rep_elt (genB_isoB hg)).mul (hy.mul (rep_elt_inv hg))

@[expose] def genSet (gens : List (List ℕ)) : Set H6 := {g | ∃ c ∈ gens, g = elt c}

@[expose] def Hgen (gens : List (List ℕ)) : Subgroup H6 := Subgroup.closure (genSet gens)

theorem elt_mem_Hgen {gens : List (List ℕ)} {c : List ℕ} (hc : c ∈ gens) : elt c ∈ Hgen gens :=
  Subgroup.subset_closure ⟨c, hc, rfl⟩

theorem mem_tabOf_iff {tab : Array (List ℕ)} {t : List ℕ} :
    t ∈ tab ↔ ∃ i < tab.size, tab.getD i [] = t := by
  rw [Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
      Option.getD_some]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
      Option.getD_some]⟩

theorem tabCheck_spec {gens : List (List ℕ)} {n : ℕ} {P : Array (List ℕ) → Bool}
    (h : tabCheck gens n P = true) :
    (∀ g : H6, g ∈ Hgen gens ↔ ∃ t ∈ tabOf gens n, Rep g t) ∧
    (∀ t ∈ tabOf gens n, ∃ g ∈ Hgen gens, Rep g t) ∧
    Nat.card (Hgen gens) = n ∧ P (tabOf gens n) = true ∧ (∀ c ∈ gens, genB c = true) := by
  simp only [tabCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hgens, hsize⟩, hclosed⟩, hdist⟩, hvalid⟩, hP⟩ := h
  have hS : mat6 '' genSet gens = {y | ∃ c ∈ gens, KGCert.decodeC c = y} := by
    ext y
    constructor
    · rintro ⟨g, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, ((rep_elt (genB_isoB (hgens c hc))).2).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨elt c, ⟨c, hc, rfl⟩, (rep_elt (genB_isoB (hgens c hc))).2⟩
  have himg : mat6 '' (Subgroup.closure (genSet gens) : Set H6) = {y | ∃ t < (tabOf gens n).size,
      KGCert.decodeC ((tabOf gens n).getD t []) = y} :=
    image_closure_eq KGCert.decodeC oneC mulC gens mat6 KGCert.decodeC_oneC
      decodeC_mulC_all (genSet gens) hS (bfsParents oneC mulC gens n) hclosed
  have hval : ∀ i < (tabOf gens n).size, KGCert.ValidC ((tabOf gens n).getD i []) := fun i hi =>
    validB_iff.1 (allCheck_spec hvalid hi)
  have hvalid' : ∀ t ∈ tabOf gens n, KGCert.ValidC t := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := mem_tabOf_iff.1 ht
    exact hval i hi
  refine ⟨fun g => ⟨fun hg => ?_, fun ⟨t, ht, hrep⟩ => ?_⟩, fun t ht => ?_, ?_, hP, hgens⟩
  · have hmem : mat6 g ∈ mat6 '' (Subgroup.closure (genSet gens) : Set H6) := ⟨g, hg, rfl⟩
    rw [himg] at hmem
    obtain ⟨i, hi, hie⟩ := hmem
    exact ⟨_, mem_tabOf_iff.2 ⟨i, hi, rfl⟩, hval i hi, hie.symm⟩
  · obtain ⟨i, hi, rfl⟩ := mem_tabOf_iff.1 ht
    have hmem : mat6 g ∈ {y | ∃ t < (tabOf gens n).size,
        KGCert.decodeC ((tabOf gens n).getD t []) = y} := ⟨i, hi, hrep.2.symm⟩
    rw [← himg] at hmem
    obtain ⟨g', hg', hgg'⟩ := hmem
    rw [← mat6_injective hgg']
    exact hg'
  · obtain ⟨i, hi, rfl⟩ := mem_tabOf_iff.1 ht
    have hmem : KGCert.decodeC ((tabOf gens n).getD i []) ∈ {y | ∃ t < (tabOf gens n).size,
        KGCert.decodeC ((tabOf gens n).getD t []) = y} := ⟨i, hi, rfl⟩
    rw [← himg] at hmem
    obtain ⟨g', hg', hgg'⟩ := hmem
    exact ⟨g', hg', hval i hi, hgg'⟩
  · have hd : ∀ t < (tabOf gens n).size, ∀ t' < (tabOf gens n).size,
        KGCert.decodeC ((tabOf gens n).getD t []) = KGCert.decodeC ((tabOf gens n).getD t' []) →
          (tabOf gens n).getD t [] = (tabOf gens n).getD t' [] := fun t ht t' ht' e =>
      KGCert.decodeC_injOn (hval t ht) (hval t' ht') e
    have := card_closure_eq KGCert.decodeC oneC mulC gens mat6 mat6_injective
      KGCert.decodeC_oneC decodeC_mulC_all (genSet gens) hS (bfsParents oneC mulC gens n)
      hclosed hdist hd
    exact this.trans hsize

theorem inTab_iff {tab : Array (List ℕ)} {c : List ℕ} : inTab tab c = true ↔ c ∈ tab := by
  simp [inTab]

theorem forall_of_allCheck {tab : Array (List ℕ)} {Q : List ℕ → Bool}
    (h : allCheck Q tab = true) : ∀ t ∈ tab, Q t = true := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := mem_tabOf_iff.1 ht
  exact allCheck_spec h hi

section Generic

variable {gens : List (List ℕ)} {n : ℕ} {P : Array (List ℕ) → Bool}

theorem Hgen_rep (h : tabCheck gens n P = true) {g : H6} (hg : g ∈ Hgen gens) :
    ∃ t ∈ tabOf gens n, Rep g t :=
  ((tabCheck_spec h).1 g).1 hg

theorem mem_Hgen_of_rep (h : tabCheck gens n P = true) {g : H6} {t : List ℕ}
    (ht : t ∈ tabOf gens n) (hg : Rep g t) : g ∈ Hgen gens :=
  ((tabCheck_spec h).1 g).2 ⟨t, ht, hg⟩

theorem elt_mem_Hgen_of_inTab (h : tabCheck gens n P = true) {c : List ℕ}
    (hc : isoB c = true) (ht : c ∈ tabOf gens n) : elt c ∈ Hgen gens :=
  mem_Hgen_of_rep h ht (rep_elt hc)

theorem Hgen_le_of_inTab {gens₁ gens₂ : List (List ℕ)} {n₂ : ℕ} {P₂ : Array (List ℕ) → Bool}
    (h₂ : tabCheck gens₂ n₂ P₂ = true) (h₁ : ∀ c ∈ gens₁, genB c = true)
    (hin : ∀ c ∈ gens₁, c ∈ tabOf gens₂ n₂) : Hgen gens₁ ≤ Hgen gens₂ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, hc, rfl⟩
  exact elt_mem_Hgen_of_inTab h₂ (genB_isoB (h₁ c hc)) (hin c hc)

theorem forall_Hgen (h : tabCheck gens n P = true) {Q : List ℕ → Bool}
    (hQ : allCheck Q (tabOf gens n) = true) {g : H6} (hg : g ∈ Hgen gens) :
    ∃ t, Rep g t ∧ Q t = true := by
  obtain ⟨t, ht, hrep⟩ := Hgen_rep h hg
  exact ⟨t, hrep, forall_of_allCheck hQ t ht⟩

end Generic

section Subgroups

variable {gens : List (List ℕ)} {n : ℕ} {P : Array (List ℕ) → Bool}

theorem comm_Hgen_of_gens {g : H6} {t : List ℕ} (hg : Rep g t)
    (hgens : ∀ c ∈ gens, genB c = true) (hc : ∀ c ∈ gens, commB t c = true) :
    ∀ h ∈ Hgen gens, g * h = h * g := by
  have hle : Hgen gens ≤ Subgroup.centralizer {g} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hcg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hg.comm_iff (rep_elt (genB_isoB (hgens c hcg)))).2 (beq_iff_eq.1 (hc c hcg))
  intro h hh
  exact Subgroup.mem_centralizer_iff.1 (hle hh) g rfl

theorem pow_three_Hgen (h : tabCheck gens n P = true)
    (hQ : allCheck cubeB (tabOf gens n) = true) : ∀ x ∈ Hgen gens, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨t, hrep, ht⟩ := forall_Hgen h hQ hx
  exact hrep.pow_three.2 (beq_iff_eq.1 ht)

theorem isMulCommutative_Hgen (h : tabCheck gens n P = true)
    (hQ : allCheck (fun x => gens.all (commB x)) (tabOf gens n) = true) :
    IsMulCommutative (Hgen gens) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨t, hrep, ht⟩ := forall_Hgen h hQ a.2
  rw [List.all_eq_true] at ht
  exact Subtype.ext (comm_Hgen_of_gens hrep (tabCheck_spec h).2.2.2.2 ht b b.2)

theorem elt_mem_normalizer_Hgen (h : tabCheck gens n P = true) {g : List ℕ}
    (hg : genB g = true) (hconj : ∀ c ∈ gens, conjC g c ∈ tabOf gens n) :
    elt g ∈ Subgroup.normalizer (Hgen gens : Set H6) := by
  have hgens := (tabCheck_spec h).2.2.2.2
  have hle : ∀ y ∈ Hgen gens, elt g * y * (elt g)⁻¹ ∈ Hgen gens := by
    intro y hy
    have hcl : Hgen gens ≤ (Hgen gens).comap (MulAut.conj (elt g)).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_Hgen_of_rep h (hconj c hc) (rep_conj_elt hg (rep_elt (genB_isoB (hgens c hc))))
    have := hcl hy
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  exact Subgroup.mem_normalizer_fintype fun y hy => hle y hy

theorem commB_gens_of_centralizes {gens : List (List ℕ)} (hgens : ∀ c ∈ gens, genB c = true)
    {x : H6} {t : List ℕ} (hx : Rep x t)
    (hxc : x ∈ Subgroup.centralizer (Hgen gens : Set H6)) : gens.all (commB t) = true := by
  rw [List.all_eq_true]
  intro c hc
  have h := Subgroup.mem_centralizer_iff.1 hxc (elt c) (elt_mem_Hgen hc)
  exact beq_iff_eq.2 ((hx.comm_iff (rep_elt (genB_isoB (hgens c hc)))).1 h.symm)

end Subgroups

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
