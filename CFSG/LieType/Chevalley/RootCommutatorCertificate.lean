module

public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Chevalley.RootCommutatorPairCheck
public import CFSG.LieType.Chevalley.RootCommutatorPairCheckE7
public import CFSG.LieType.Chevalley.RootCommutatorPairCheckE8

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk RootOps

namespace RootOps

theorem closureOK : ∀ τ : Tag, ClosureOK τ
  | .G2 => closureOK_of_closureCheckAll closureCheckAll_G2
  | .F4 => closureOK_of_closureCheckAll closureCheckAll_F4
  | .D4 => closureOK_of_closureCheckAll closureCheckAll_D4
  | .E6 => closureOK_of_closureCheckAll closureCheckAll_E6
  | .E7 => closureOK_E7
  | .E8 => closureOK_E8

theorem negCheck_eq : ∀ τ : Tag, negCheck τ = true
  | .G2 => negCheck_G2
  | .F4 => negCheck_F4
  | .D4 => negCheck_D4
  | .E6 => negCheck_E6
  | .E7 => negCheck_E7
  | .E8 => negCheck_E8

theorem tableCheck_eq
    : ∀ τ : Tag, tableCheck τ = true
  | .G2 => tableCheck_G2
  | .F4 => tableCheck_F4
  | .D4 => tableCheck_D4
  | .E6 => tableCheck_E6
  | .E7 => tableCheck_E7
  | .E8 => tableCheck_E8

theorem sizesOK : ∀ τ : Tag, SizesOK τ
  | .G2 => sizesOK_of_all sizeCheck_G2
  | .F4 => sizesOK_of_all sizeCheck_F4
  | .D4 => sizesOK_of_all sizeCheck_D4
  | .E6 => sizesOK_of_all sizeCheck_E6
  | .E7 => sizesOK_of_all sizeCheck_E7
  | .E8 => sizesOK_E8

variable {τ : Tag}

theorem pairLab_image
    (i : Fin τ.rank) {m n : ℕ} (hm : m < τ.rootCertificate.roots.length)
    (hn : n < τ.rootCertificate.roots.length) :
    pairLab τ (τ.rootCertificate.image m i) (τ.rootCertificate.image n i) = pairLab τ m n := by
  have h := closureOK τ i m n hm hn
  rwa [imgPar_div_two (RootOps.dataChecks τ).tab hm,
    imgPar_div_two (RootOps.dataChecks τ).tab hn] at h

theorem negCheck_spec
    {m : ℕ} (hm : m < τ.rootCertificate.roots.length) :
    (negPos τ).getD m 0 < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root ((negPos τ).getD m 0) = -τ.rootCertificate.root m ∧
      (repsOf τ).length ≤ pairLab τ m m ∧
        (repsOf τ).length ≤ pairLab τ m ((negPos τ).getD m 0) := by
  have h := negCheck_eq τ
  simp only [negCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq,
    Nat.ble_eq, CFSG.LieType.Ree.vecBEq_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h m hm
  exact ⟨h1, h2, h3, h4⟩

theorem tableCheck_spec :
    (pairTable τ).map (fun r => (r.1, r.2.1, r.2.2.2)) = (repsOf τ).map (convertRow τ) ∧
      (repsOf τ).map (fun x => pairLab τ x.1 x.2.1) = List.range (repsOf τ).length ∧
      (∀ r ∈ pairTable τ, ∀ f ∈ r.2.2.2, 1 ≤ |f.2.2.2| ∧ |f.2.2.2| ≤ 3) ∧
      τ.witnesses.roots.Nodup := by
  have h := tableCheck_eq τ
  simp only [tableCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.ble_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun r hr f hf => ?_, h4⟩
  obtain ⟨h5, h6⟩ := h3 r hr f hf
  rw [Int.abs_eq_natAbs]
  exact ⟨by exact_mod_cast h5, by exact_mod_cast h6⟩

theorem length_pairTable
    : (pairTable τ).length = (repsOf τ).length := by
  simpa using congrArg List.length (tableCheck_spec (τ := τ)).1

theorem pairLab_rep
    {r : ℕ} (hr : r < (repsOf τ).length) :
    pairLab τ (repsOf τ)[r].1 (repsOf τ)[r].2.1 = r := by
  have h := congrArg (fun l => l[r]?) (tableCheck_spec (τ := τ)).2.1
  simpa [hr] using h

theorem pairTable_getElem
    {r : ℕ} (hr : r < (pairTable τ).length) :
    ((pairTable τ)[r].1, (pairTable τ)[r].2.1, (pairTable τ)[r].2.2.2) =
      convertRow τ ((repsOf τ)[r]'(length_pairTable (τ := τ) ▸ hr)) := by
  have h := congrArg (fun l => l[r]?) (tableCheck_spec (τ := τ)).1
  simpa [hr, length_pairTable (τ := τ) ▸ hr] using h

theorem length_labPairs (l : ℕ) : (labPairs τ l).length = countLab τ l := by
  simp only [labPairs, countLab, SProd.sprod, List.product, List.filter_flatMap,
    List.length_flatMap, List.filter_map, List.length_map, Function.comp_def]

theorem nodup_labPairs (l : ℕ) : (labPairs τ l).Nodup :=
  ((List.nodup_range).product List.nodup_range).filter _

theorem mem_labPairs {l : ℕ} {mn : ℕ × ℕ} :
    mn ∈ labPairs τ l ↔ mn.1 < τ.rootCertificate.roots.length ∧
      mn.2 < τ.rootCertificate.roots.length ∧ pairLab τ mn.1 mn.2 = l := by
  obtain ⟨m, n⟩ := mn
  simp only [labPairs, List.mem_filter, List.mem_product, List.mem_range, beq_iff_eq, and_assoc]

theorem sizeCheck_spec {r : ℕ} (hr : r < (pairTable τ).length) :
    (pairTable τ)[r].2.2.1 = (labPairs τ r).length := by
  have h := sizesOK τ r hr
  simp only [sizeCheck, beq_iff_eq, List.getD_eq_getElem _ _ hr] at h
  rw [h, length_labPairs]

theorem exists_smul_pairLab
    (w : WeylGroup τ) {m n : ℕ}
    (hm : m < τ.rootCertificate.roots.length) (hn : n < τ.rootCertificate.roots.length) :
    ∃ m' n', m' < τ.rootCertificate.roots.length ∧ n' < τ.rootCertificate.roots.length ∧
      w • τ.rootCertificate.root m = τ.rootCertificate.root m' ∧
      w • τ.rootCertificate.root n = τ.rootCertificate.root n' ∧
      pairLab τ m' n' = pairLab τ m n := by
  induction w using (coxeterSystem τ).simple_induction_left with
  | one => exact ⟨m, n, hm, hn, one_smul _ _, one_smul _ _, rfl⟩
  | mul_simple_left w i ih =>
    obtain ⟨m', n', hm', hn', h1, h2, h3⟩ := ih
    refine ⟨τ.rootCertificate.image m' i, τ.rootCertificate.image n' i,
      rootCertificate_image_lt hm' i, rootCertificate_image_lt hn' i, ?_, ?_, ?_⟩
    · rw [mul_smul, h1, simple_smul, rootCertificate_root_image hm']
    · rw [mul_smul, h2, simple_smul, rootCertificate_root_image hn']
    · rw [pairLab_image i hm' hn', h3]

theorem ne_of_pairLab_lt
    {m n : ℕ} (hm : m < τ.rootCertificate.roots.length)
    (hn : n < τ.rootCertificate.roots.length) (hl : pairLab τ m n < (repsOf τ).length) :
    τ.rootCertificate.root m ≠ τ.rootCertificate.root n ∧
      τ.rootCertificate.root m ≠ -τ.rootCertificate.root n := by
  obtain ⟨hneg, hnegr, h1, h2⟩ := negCheck_spec hm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← rootCertificate_root_injOn hm hn h] at hl
    omega
  · have h' : τ.rootCertificate.root n = τ.rootCertificate.root ((negPos τ).getD m 0) := by
      rw [hnegr, h, neg_neg]
    rw [rootCertificate_root_injOn hn hneg h'] at hl
    omega

theorem orbit_rep_eq
    {r : ℕ} (hr : r < (repsOf τ).length) :
    MulAction.orbit (WeylGroup τ)
        (τ.rootCertificate.root (repsOf τ)[r].1, τ.rootCertificate.root (repsOf τ)[r].2.1) =
      (fun mn : ℕ × ℕ => (τ.rootCertificate.root mn.1, τ.rootCertificate.root mn.2)) ''
        {mn | mn ∈ labPairs τ r} := by
  have hx := lt_length_of_mem_repsOf (List.getElem_mem hr)
  ext ⟨α, β⟩
  constructor
  · intro h
    obtain ⟨w, hw⟩ := MulAction.mem_orbit_iff.1 h
    obtain ⟨m', n', hm', hn', h1, h2, h3⟩ := exists_smul_pairLab w hx.1 hx.2
    rw [Prod.smul_mk, h1, h2] at hw
    refine ⟨(m', n'), ?_, hw⟩
    rw [Set.mem_ofPred_eq, mem_labPairs]
    exact ⟨hm', hn', h3.trans (pairLab_rep hr)⟩
  · rintro ⟨⟨m, n⟩, hmn, hαβ⟩
    rw [Set.mem_ofPred_eq, mem_labPairs] at hmn
    obtain ⟨hm, hn, hl⟩ := hmn
    simp only [Prod.mk.injEq] at hαβ
    obtain ⟨rfl, rfl⟩ := hαβ
    obtain ⟨hne, hne'⟩ := ne_of_pairLab_lt hm hn (hl ▸ hr)
    obtain ⟨x, hxmem, w, hw1, hw2⟩ := exists_smul_rep (isRoot_rootCertificate_root hm)
      (isRoot_rootCertificate_root hn) hne hne'
    obtain ⟨r', hr', rfl⟩ := List.mem_iff_getElem.1 hxmem
    have hx' := lt_length_of_mem_repsOf hxmem
    obtain ⟨m', n', hm', hn', h1, h2, h3⟩ := exists_smul_pairLab w hx'.1 hx'.2
    have e1 := rootCertificate_root_injOn hm' hm (h1.symm.trans hw1)
    have e2 := rootCertificate_root_injOn hn' hn (h2.symm.trans hw2)
    subst e1 e2
    have hrr : r' = r := by rw [← pairLab_rep hr', ← h3, hl]
    subst hrr
    exact MulAction.mem_orbit_iff.2 ⟨w, by rw [Prod.smul_mk, hw1, hw2]⟩

theorem ncard_orbit_rep
    {r : ℕ} (hr : r < (repsOf τ).length) :
    (MulAction.orbit (WeylGroup τ)
        (τ.rootCertificate.root (repsOf τ)[r].1,
          τ.rootCertificate.root (repsOf τ)[r].2.1)).ncard = (labPairs τ r).length := by
  rw [orbit_rep_eq hr, Set.InjOn.ncard_image]
  · rw [show {mn | mn ∈ labPairs τ r} = ((labPairs τ r).toFinset : Set (ℕ × ℕ)) by
      ext; simp, Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_labPairs r)]
  · rintro ⟨m, n⟩ hmn ⟨m', n'⟩ hmn' h
    rw [Set.mem_ofPred_eq, mem_labPairs] at hmn hmn'
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rootCertificate_root_injOn hmn.1 hmn'.1 h.1)
      (rootCertificate_root_injOn hmn.2.1 hmn'.2.1 h.2)

theorem orbitCertRoot_certWitnessPos
    {a : ℕ} (ha : a < τ.rootCertificate.roots.length) :
    orbitCertRoot τ (certWitnessPos τ a) = τ.rootCertificate.root a :=
  decodeVec_certWitnessPos ha

theorem orbitCertRoot_injOn
    {k k' : ℕ} (hk : k < τ.witnesses.roots.length)
    (hk' : k' < τ.witnesses.roots.length) (h : orbitCertRoot τ k = orbitCertRoot τ k') :
    k = k' := by
  have hcode := eq_of_decodeVec_eq hk' hk h
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk'] at hcode
  exact ((tableCheck_spec (τ := τ)).2.2.2.getElem_inj_iff).1 hcode

theorem pairTable_getElem_eq
    {r : ℕ} (hr : r < (pairTable τ).length) :
    (pairTable τ)[r].1 = certWitnessPos τ ((repsOf τ)[r]'(length_pairTable (τ := τ) ▸ hr)).1 ∧
      (pairTable τ)[r].2.1 =
        certWitnessPos τ ((repsOf τ)[r]'(length_pairTable (τ := τ) ▸ hr)).2.1 ∧
      (pairTable τ)[r].2.2.2 =
        (convertRow τ ((repsOf τ)[r]'(length_pairTable (τ := τ) ▸ hr))).2.2 := by
  have h := pairTable_getElem hr
  simp only [convertRow, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem linearIndependent_rat_of_linIndepPair {α β : Fin τ.rank → ℤ}
    (h : CFSG.LieType.Steinberg.LinIndepPair α β) :
    LinearIndependent ℚ ![fun j => (α j : ℚ), fun j => (β j : ℚ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have key : (s.num * t.den) • α + (t.num * s.den) • β = 0 := by
    funext j
    have hj := congrFun hst j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
    have hs : (s.num : ℚ) = s * s.den := (Rat.mul_den_eq_num s).symm
    have ht : (t.num : ℚ) = t * t.den := (Rat.mul_den_eq_num t).symm
    have : ((s.num * t.den * α j + t.num * s.den * β j : ℤ) : ℚ) = 0 := by
      push_cast
      rw [hs, ht]
      linear_combination (s.den * t.den : ℚ) * hj
    exact_mod_cast this
  obtain ⟨h1, h2⟩ := h _ _ key
  have hsd : (s.den : ℤ) ≠ 0 := by exact_mod_cast s.den_nz
  have htd : (t.den : ℤ) ≠ 0 := by exact_mod_cast t.den_nz
  exact ⟨Rat.num_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right htd),
    Rat.num_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hsd)⟩

end RootOps

open MvPolynomial in
theorem rank_two_pair_certificate
    (τ : Tag) :
    (∀ α β : Fin τ.rank → ℤ, IsRoot τ α → IsRoot τ β → α ≠ β → α ≠ -β →
      ∃! r, r ∈ pairTable τ ∧
        (α, β) ∈ MulAction.orbit (WeylGroup τ) (orbitCertRoot τ r.1, orbitCertRoot τ r.2.1)) ∧
    ∀ r ∈ pairTable τ,
      r.1 < τ.witnesses.roots.length ∧ r.2.1 < τ.witnesses.roots.length ∧
      IsRoot τ (orbitCertRoot τ r.1) ∧ IsRoot τ (orbitCertRoot τ r.2.1) ∧
      orbitCertRoot τ r.1 ≠ orbitCertRoot τ r.2.1 ∧ orbitCertRoot τ r.1 ≠ -orbitCertRoot τ r.2.1 ∧
      (MulAction.orbit (WeylGroup τ) (orbitCertRoot τ r.1, orbitCertRoot τ r.2.1)).ncard =
        r.2.2.1 ∧
      LinearIndependent ℚ
        ![fun j => (orbitCertRoot τ r.1 j : ℚ), fun j => (orbitCertRoot τ r.2.1 j : ℚ)] ∧
      (∀ p q k : ℕ, (∃ C, (p, q, k, C) ∈ r.2.2.2) ↔
        0 < p ∧ 0 < q ∧ k < τ.witnesses.roots.length ∧
          orbitCertRoot τ k = p • orbitCertRoot τ r.1 + q • orbitCertRoot τ r.2.1) ∧
      r.2.2.2.Pairwise (fun f g =>
        f.1 + f.2.1 < g.1 + g.2.1 ∨ (f.1 + f.2.1 = g.1 + g.2.1 ∧ f.1 < g.1)) ∧
      (∀ f ∈ r.2.2.2, 1 ≤ |f.2.2.2| ∧ |f.2.2.2| ≤ 3) ∧
      pinnedX τ (MvPolynomial (Fin 2) ℤ) (orbitCertRoot τ r.1) (X 0) *
          pinnedX τ (MvPolynomial (Fin 2) ℤ) (orbitCertRoot τ r.2.1) (X 1) *
          pinnedX τ (MvPolynomial (Fin 2) ℤ) (orbitCertRoot τ r.1) (-X 0) *
          pinnedX τ (MvPolynomial (Fin 2) ℤ) (orbitCertRoot τ r.2.1) (-X 1) =
        (r.2.2.2.map fun f => pinnedX τ (MvPolynomial (Fin 2) ℤ) (orbitCertRoot τ f.2.2.1)
          ((f.2.2.2 : MvPolynomial (Fin 2) ℤ) * X 0 ^ f.1 * X 1 ^ f.2.1)).prod := by
  refine ⟨fun α β hα hβ hne hne' => ?_, fun r hr => ?_⟩
  ·
    obtain ⟨x, hxmem, w, hw1, hw2⟩ := exists_smul_rep hα hβ hne hne'
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hxmem
    have hi' : i < (pairTable τ).length := length_pairTable (τ := τ) ▸ hi
    have hx := lt_length_of_mem_repsOf hxmem
    obtain ⟨e1, e2, -⟩ := pairTable_getElem_eq hi'
    refine ⟨(pairTable τ)[i], ⟨List.getElem_mem hi', ?_⟩, ?_⟩
    · rw [e1, e2, orbitCertRoot_certWitnessPos hx.1, orbitCertRoot_certWitnessPos hx.2]
      exact MulAction.mem_orbit_iff.2 ⟨w, by rw [Prod.smul_mk, hw1, hw2]⟩
    · rintro t ⟨ht, hmem⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ht
      have hj' : j < (repsOf τ).length := length_pairTable (τ := τ) ▸ hj
      have hy := lt_length_of_mem_repsOf (List.getElem_mem hj')
      obtain ⟨f1, f2, -⟩ := pairTable_getElem_eq hj
      rw [f1, f2, orbitCertRoot_certWitnessPos hy.1, orbitCertRoot_certWitnessPos hy.2,
        orbit_rep_eq hj'] at hmem
      have hmem2 : (α, β) ∈ MulAction.orbit (WeylGroup τ)
          (τ.rootCertificate.root (repsOf τ)[i].1, τ.rootCertificate.root (repsOf τ)[i].2.1) :=
        MulAction.mem_orbit_iff.2 ⟨w, by rw [Prod.smul_mk, hw1, hw2]⟩
      rw [orbit_rep_eq hi] at hmem2
      obtain ⟨⟨m, n⟩, hmn, hmn'⟩ := hmem
      obtain ⟨⟨m', n'⟩, hmn2, hmn2'⟩ := hmem2
      rw [Set.mem_ofPred_eq, mem_labPairs] at hmn hmn2
      simp only [Prod.mk.injEq] at hmn' hmn2'
      have em := rootCertificate_root_injOn hmn.1 hmn2.1 (hmn'.1.trans hmn2'.1.symm)
      have en := rootCertificate_root_injOn hmn.2.1 hmn2.2.1 (hmn'.2.trans hmn2'.2.symm)
      subst em en
      have hji : j = i := hmn.2.2.symm.trans hmn2.2.2
      subst hji
      rfl
  ·
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
    have hi' : i < (repsOf τ).length := length_pairTable (τ := τ) ▸ hi
    set x := (repsOf τ)[i]
    have hxmem : x ∈ repsOf τ := List.getElem_mem hi'
    have hx := lt_length_of_mem_repsOf hxmem
    obtain ⟨e1, e2, e3⟩ := pairTable_getElem_eq hi
    have hα : orbitCertRoot τ (pairTable τ)[i].1 = τ.rootCertificate.root x.1 := by
      rw [e1, orbitCertRoot_certWitnessPos hx.1]
    have hβ : orbitCertRoot τ (pairTable τ)[i].2.1 = τ.rootCertificate.root x.2.1 := by
      rw [e2, orbitCertRoot_certWitnessPos hx.2]
    have hlab : pairLab τ x.1 x.2.1 < (repsOf τ).length := (pairLab_rep hi').symm ▸ hi'
    obtain ⟨hne, hne'⟩ := ne_of_pairLab_lt hx.1 hx.2 hlab
    have hrα := isRoot_rootCertificate_root hx.1
    have hrβ := isRoot_rootCertificate_root hx.2
    have hcone := coneOk_of_mem_repsOf hxmem
    have hkeys := (repShape_spec hxmem).2.2.1
    have hnd := keys_nodup_of_mem_repsOf hxmem
    rw [hα, hβ, e3]
    refine ⟨e1 ▸ certWitnessPos_lt hx.1, e2 ▸ certWitnessPos_lt hx.2, hrα, hrβ, hne, hne', ?_,
      linearIndependent_rat_of_linIndepPair
        (CFSG.LieType.Steinberg.Adjoint.linIndepPair_of_ne hrα hrβ hne hne'),
      fun p q k => ?_, ?_, ?_, ?_⟩
    · rw [ncard_orbit_rep hi', sizeCheck_spec hi]
    ·
      simp only [convertRow, List.mem_map]
      constructor
      · rintro ⟨C, f, hf, hfe⟩
        simp only [Prod.mk.injEq] at hfe
        obtain ⟨rfl, rfl, rfl, -⟩ := hfe
        have hc := hcone f hf
        simp only [coneOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
          CFSG.LieType.Ree.vecBEq_iff] at hc
        obtain ⟨⟨⟨hg, h1⟩, h2⟩, h3⟩ := hc
        exact ⟨h1, h2, certWitnessPos_lt hg, by rw [orbitCertRoot_certWitnessPos hg, h3]⟩
      · rintro ⟨hp, hq, hk, hkr⟩
        have hroot : IsRoot τ (p • τ.rootCertificate.root x.1 + q • τ.rootCertificate.root x.2.1) :=
          hkr ▸ isRoot_decodeVec_witness hk
        have hpq : (p, q) ∈ commPairs τ (τ.rootCertificate.root x.1)
            (τ.rootCertificate.root x.2.1) := (mem_commPairs_rep hxmem (p, q)).2 ⟨hp, hq, hroot⟩
        rw [← hkeys, List.mem_map] at hpq
        obtain ⟨f, hf, hfpq⟩ := hpq
        simp only [Prod.mk.injEq] at hfpq
        obtain ⟨rfl, rfl⟩ := hfpq
        have hc := hcone f hf
        simp only [coneOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
          CFSG.LieType.Ree.vecBEq_iff] at hc
        obtain ⟨⟨⟨hg, -⟩, -⟩, h3⟩ := hc
        have hkk : certWitnessPos τ f.2.2.1 = k := orbitCertRoot_injOn (certWitnessPos_lt hg) hk
          (by rw [orbitCertRoot_certWitnessPos hg, h3, hkr])
        exact ⟨_, f, hf, by rw [hkk]⟩
    ·
      rw [convertRow, List.pairwise_map]
      have := commPairs_pairwise (τ.rootCertificate.root x.1) (τ.rootCertificate.root x.2.1)
      rw [← hkeys, List.pairwise_map] at this
      exact this
    ·
      have := (tableCheck_spec (τ := τ)).2.2.1 _ (List.getElem_mem hi)
      rwa [e3] at this
    ·
      rw [pinnedX_commFormula_of_commFormula hrα hrβ (commFormula_rep hxmem), ← hkeys,
        List.map_map, convertRow, List.map_map]
      refine congrArg List.prod (List.map_congr_left fun f hf => ?_)
      have hc := hcone f hf
      simp only [coneOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
        CFSG.LieType.Ree.vecBEq_iff] at hc
      obtain ⟨⟨⟨hg, -⟩, -⟩, h3⟩ := hc
      simp only [Function.comp_apply]
      rw [orbitCertRoot_certWitnessPos hg, h3, factorConst_of_mem hnd hf,
        pinnedSignW_eq (certWitnessPos_lt hg), pinnedSignW_eq (certWitnessPos_lt hx.1),
        pinnedSignW_eq (certWitnessPos_lt hx.2), decodeVec_certWitnessPos hg,
        decodeVec_certWitnessPos hx.1, decodeVec_certWitnessPos hx.2, h3]

end CFSG.LieType.Chevalley
