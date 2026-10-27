module

public import Certificates.Certificate27822
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped Pointwise

@[expose] def finOf (S : Array ℕ) : Finset (Fin 128) :=
  Finset.univ.filter fun p => S.contains (p : ℕ)

@[expose] def x45Fin (i : ℕ) : Finset (Fin 128) := finOf x45Sets[i]!

@[expose] def A0 : Finset (Fin 128) := x45Fin 0

@[expose] abbrev X45 : Type := ↥(MulAction.orbit ↥Pg A0)

noncomputable instance : Fintype X45 := Fintype.ofFinite X45

@[expose] noncomputable def delta : ↥Pg →* ℤˣ :=
  Equiv.Perm.sign.comp (MulAction.toPermHom ↥Pg X45)

theorem mem_finOf {S : Array ℕ} {p : Fin 128} : p ∈ finOf S ↔ (p : ℕ) ∈ S := by
  simp [finOf]

theorem sameSet_iff {S T : Array ℕ} :
    sameSet S T = true ↔ (∀ x ∈ S, x ∈ T) ∧ (∀ x ∈ T, x ∈ S) ∧ S.size = T.size := by
  simp only [sameSet, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem,
    Array.contains_iff_mem, and_assoc]

theorem smul_finOf_iff {t S T : Array ℕ} {G : Equiv.Perm (Fin 128)} (hR : Rep 128 t G)
    (hS : ∀ x ∈ S, x < 128) (hT : ∀ x ∈ T, x < 128) (hsz : S.size = T.size) :
    G • finOf S = finOf T ↔ sameSet (imgSet t S) T = true := by
  have hval : ∀ p : Fin 128, t[(p : ℕ)]! = (G p : ℕ) := fun p => hR p
  rw [sameSet_iff]
  constructor
  · intro he
    refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
    · simp only [imgSet, Array.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      have hq : G ⟨a, hS a ha⟩ ∈ finOf T := by
        rw [← he]
        exact Finset.mem_smul_finset.2 ⟨⟨a, hS a ha⟩, mem_finOf.2 ha, rfl⟩
      have hv : t[a]! = (G ⟨a, hS a ha⟩ : ℕ) := hval ⟨a, hS a ha⟩
      rw [hv]
      exact mem_finOf.1 hq
    · have hy : (⟨x, hT x hx⟩ : Fin 128) ∈ finOf T := mem_finOf.2 hx
      rw [← he] at hy
      obtain ⟨p, hp, hpy⟩ := Finset.mem_smul_finset.1 hy
      simp only [imgSet, Array.mem_map]
      refine ⟨(p : ℕ), mem_finOf.1 hp, ?_⟩
      rw [hval p]
      exact congrArg Fin.val hpy
    · simpa [imgSet] using hsz
  · rintro ⟨h1, h2, -⟩
    ext y
    rw [Finset.mem_smul_finset]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hmem : ((G p : Fin 128) : ℕ) ∈ imgSet t S := by
        simp only [imgSet, Array.mem_map]
        exact ⟨(p : ℕ), mem_finOf.1 hp, hval p⟩
      exact mem_finOf.2 (h1 _ hmem)
    · intro hy
      have hyI := h2 _ (mem_finOf.1 hy)
      simp only [imgSet, Array.mem_map] at hyI
      obtain ⟨a, ha, hav⟩ := hyI
      refine ⟨⟨a, hS a ha⟩, mem_finOf.2 ha, ?_⟩
      apply Fin.ext
      exact (hval ⟨a, hS a ha⟩).symm.trans hav

theorem sameSet_of_finOf_eq {S T : Array ℕ} (hS : ∀ x ∈ S, x < 128) (hT : ∀ x ∈ T, x < 128)
    (hsz : S.size = T.size) (h : finOf S = finOf T) : sameSet S T = true := by
  rw [sameSet_iff]
  refine ⟨fun x hx => ?_, fun x hx => ?_, hsz⟩
  · have h1 : (⟨x, hS x hx⟩ : Fin 128) ∈ finOf S := mem_finOf.2 hx
    rw [h] at h1
    exact mem_finOf.1 h1
  · have h1 : (⟨x, hT x hx⟩ : Fin 128) ∈ finOf T := mem_finOf.2 hx
    rw [← h] at h1
    exact mem_finOf.1 h1

theorem card_range_filter_eq (Q : ℕ → Bool) (n : ℕ) :
    ((Finset.range n).filter fun i => Q i = true).card = ((List.range n).filter Q).length := by
  have hfun : (fun i => decide (Q i = true)) = Q := funext fun i => by cases Q i <;> rfl
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card, hfun]

theorem gen_mem {gi : ℕ} (hgi : gi < 36) : permOfArr 128 sgsArr[gi]! ∈ Pg :=
  Subgroup.subset_closure (RawSchreierDatum.mem_ofArrays_original.2 ⟨gi, hgi, rfl⟩)

theorem mem_closure_of_mem_Pg {h : Equiv.Perm (Fin 128)} (hh : h ∈ Pg) :
    h ∈ Submonoid.closure {g : Equiv.Perm (Fin 128) | g ∈ QPg.original.toList} := by
  rw [← Subgroup.closure_toSubmonoid_of_finite]
  exact hh


theorem x45_facts :
    (∀ i < 45, x45Sets[i]!.size = 8) ∧ (∀ i < 45, ∀ x ∈ x45Sets[i]!, x < 128) ∧
    (∀ i < 45, ∀ i' < 45, i ≠ i' → sameSet x45Sets[i]! x45Sets[i']! = false) ∧
    (∀ k, k + 1 < 45 → x45Par[k + 1]!.1 < k + 1 ∧ x45Par[k + 1]!.2 < 36 ∧
      sameSet (imgSet sgsArr[x45Par[k + 1]!.2]! x45Sets[x45Par[k + 1]!.1]!) x45Sets[k + 1]! = true) ∧
    (∀ gi < 36, ∀ i < 45, ∃ i' < 45,
      sameSet (imgSet sgsArr[gi]! x45Sets[i]!) x45Sets[i']! = true) ∧
    (∀ j < 9, ((List.range 45).filter fun i =>
      sameSet (imgSet repArrs[j]! x45Sets[i]!) x45Sets[i]!).length = fix45Tab[j]!) := by
  have h := Certificates.certificate27822.1
  simp only [x45Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, beq_iff_eq, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hA⟩, hB⟩, hC⟩, hD⟩, hE⟩ := h
  refine ⟨fun i hi => (hA i hi).1.1, fun i hi x hx => (hA i hi).1.2 x hx,
    fun i hi i' hi' hne => ?_, fun k hk => ?_, fun gi hgi i hi => hD gi hgi i hi,
    fun j hj => hE j hj⟩
  · simpa [hne] using hB i hi i' hi'
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hC k (by omega)
    exact ⟨h1, h2, h3⟩

theorem rep_gen {gi : ℕ} (hgi : gi < 36) : Rep 128 sgsArr[gi]! (permOfArr 128 sgsArr[gi]!) := by
  have hs : sgsArr.size = 36 := by decide
  exact (rep_permOfArr ((chainCheckFacts chain_check).strong_inv gi (hgi.trans_eq hs.symm))).1

theorem gen_smul {gi i : ℕ} (hgi : gi < 36) (hi : i < 45) :
    ∃ j < 45, permOfArr 128 sgsArr[gi]! • x45Fin i = x45Fin j := by
  obtain ⟨hsz, hlt, -, -, hcl, -⟩ := x45_facts
  obtain ⟨j, hj, h⟩ := hcl gi hgi i hi
  exact ⟨j, hj, (smul_finOf_iff (rep_gen hgi) (hlt i hi) (hlt j hj)
    ((hsz i hi).trans (hsz j hj).symm)).2 h⟩

theorem closure_stable {h : Equiv.Perm (Fin 128)}
    (hh : h ∈ Submonoid.closure {g : Equiv.Perm (Fin 128) | g ∈ QPg.original.toList}) :
    ∀ i, i < 45 → ∃ j < 45, h • x45Fin i = x45Fin j := by
  induction hh using Submonoid.closure_induction with
  | mem g hg =>
    obtain ⟨gi, hgi, rfl⟩ := RawSchreierDatum.mem_ofArrays_original.1 hg
    exact fun i hi => gen_smul hgi hi
  | one => exact fun i hi => ⟨i, hi, one_smul _ _⟩
  | mul x y _ _ hx hy =>
    intro i hi
    obtain ⟨j, hj, hyj⟩ := hy i hi
    obtain ⟨k, hk, hxk⟩ := hx j hj
    exact ⟨k, hk, by rw [mul_smul, hyj, hxk]⟩

theorem orbit_sub : MulAction.orbit ↥Pg A0 ⊆ {S | ∃ i < 45, S = x45Fin i} := by
  rintro S ⟨g, rfl⟩
  obtain ⟨j, hj, hjA⟩ := closure_stable (mem_closure_of_mem_Pg g.2) 0 (by norm_num)
  exact ⟨j, hj, hjA⟩

theorem x45Fin_mem : ∀ i, i < 45 → x45Fin i ∈ MulAction.orbit ↥Pg A0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact MulAction.mem_orbit_self A0
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      obtain ⟨hsz, hlt, -, htree, -, -⟩ := x45_facts
      obtain ⟨hp, hg, hs⟩ := htree k hi
      have hpi : x45Par[k + 1]!.1 < 45 := by omega
      obtain ⟨g', hg'⟩ := MulAction.mem_orbit_iff.1 (ih _ hp hpi)
      have hγ : permOfArr 128 sgsArr[x45Par[k + 1]!.2]! ∈ Pg := gen_mem hg
      have hsm := (smul_finOf_iff (rep_gen hg) (hlt _ hpi) (hlt _ hi)
        ((hsz _ hpi).trans (hsz _ hi).symm)).2 hs
      refine MulAction.mem_orbit_iff.2 ⟨⟨_, hγ⟩ * g', ?_⟩
      rw [mul_smul, hg']
      exact hsm

theorem orbit_eq : MulAction.orbit ↥Pg A0 = {S | ∃ i < 45, S = x45Fin i} := by
  refine Set.Subset.antisymm orbit_sub ?_
  rintro S ⟨i, hi, rfl⟩
  exact x45Fin_mem i hi

theorem x45Fin_inj {i j : ℕ} (hi : i < 45) (hj : j < 45) (h : x45Fin i = x45Fin j) : i = j := by
  obtain ⟨hsz, hlt, hdis, -, -, -⟩ := x45_facts
  by_contra hne
  have h1 : sameSet x45Sets[i]! x45Sets[j]! = true :=
    sameSet_of_finOf_eq (hlt i hi) (hlt j hj) ((hsz i hi).trans (hsz j hj).symm) h
  rw [hdis i hi j hj hne] at h1
  exact Bool.false_ne_true h1

theorem card_X45 : Nat.card X45 = 45 := by
  let f : Fin 45 → X45 := fun i => ⟨x45Fin i, x45Fin_mem i i.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j hij => Fin.ext (x45Fin_inj i.2 j.2 (congrArg Subtype.val hij)), ?_⟩
    rintro ⟨S, hS⟩
    have hS' := hS
    rw [orbit_eq] at hS'
    obtain ⟨i, hi, rfl⟩ := hS'
    exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

theorem delta_of_involution (g : ↥Pg) (hg : g * g = 1) :
    delta g = (-1) ^ ((45 - Nat.card {x : X45 // g • x = x}) / 2) := by
  have hσ : (MulAction.toPermHom ↥Pg X45 g) ^ 2 = 1 := by
    rw [sq, ← map_mul, hg, map_one]
  have hc : Fintype.card X45 = 45 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_X45
  show Equiv.Perm.sign (MulAction.toPermHom ↥Pg X45 g) = _
  rw [Equiv.Perm.sign_of_pow_two_eq_one hσ, hc, ← Nat.card_eq_fintype_card]
  rfl

theorem card_fixed_aux (g : ↥Pg) (Q : ℕ → Bool)
    (hQ : ∀ i < 45, (g • x45Fin i = x45Fin i) ↔ Q i = true) :
    (Finset.univ.filter fun x : X45 => g • x = x).card =
      ((Finset.range 45).filter fun i => Q i = true).card := by
  symm
  refine Finset.card_bij (fun a ha => (⟨x45Fin a, x45Fin_mem a (Finset.mem_range.1
    (Finset.mem_filter.1 ha).1)⟩ : X45)) ?_ ?_ ?_
  · intro a ha
    have ha' := Finset.mem_filter.1 ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact (hQ a (Finset.mem_range.1 ha'.1)).2 ha'.2
  · intro a₁ ha₁ a₂ ha₂ h
    exact x45Fin_inj (Finset.mem_range.1 (Finset.mem_filter.1 ha₁).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 ha₂).1) (congrArg Subtype.val h)
  · intro b hb
    rw [Finset.mem_filter] at hb
    have hfix : g • b.1 = b.1 := congrArg Subtype.val hb.2
    have hb1 : (b : Finset (Fin 128)) ∈ {S : Finset (Fin 128) | ∃ i < 45, S = x45Fin i} := by
      rw [← orbit_eq]
      exact b.2
    obtain ⟨a, ha, hba⟩ := hb1
    rw [hba] at hfix
    refine ⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, (hQ a ha).1 hfix⟩, ?_⟩
    exact Subtype.ext hba.symm

theorem card_fixed_eq (r : Array ℕ) (G : Equiv.Perm (Fin 128)) (hR : Rep 128 r G)
    (hG : G ∈ Pg) :
    Nat.card {x : X45 // (⟨G, hG⟩ : ↥Pg) • x = x} =
      ((List.range 45).filter fun i => sameSet (imgSet r x45Sets[i]!) x45Sets[i]!).length := by
  obtain ⟨hsz, hlt, -, -, -, -⟩ := x45_facts
  have hQ : ∀ i < 45, ((⟨G, hG⟩ : ↥Pg) • x45Fin i = x45Fin i) ↔
      (sameSet (imgSet r x45Sets[i]!) x45Sets[i]! = true) :=
    fun i hi => smul_finOf_iff hR (hlt i hi) (hlt i hi) rfl
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_fixed_aux ⟨G, hG⟩ (fun i => sameSet (imgSet r x45Sets[i]!) x45Sets[i]!) hQ,
    card_range_filter_eq]

theorem delta_of_table (r : Array ℕ) (G : Equiv.Perm (Fin 128)) (hR : Rep 128 r G)
    (hG : G ∈ Pg) (hG2 : G * G = 1) :
    delta ⟨G, hG⟩ = (-1 : ℤˣ) ^ ((45 - ((List.range 45).filter fun i =>
      sameSet (imgSet r x45Sets[i]!) x45Sets[i]!).length) / 2) := by
  rw [delta_of_involution ⟨G, hG⟩ (Subtype.ext hG2), card_fixed_eq r G hR hG]

theorem delta_rep (j : ℕ) (hj : j < 9) (G : Equiv.Perm (Fin 128)) (hG : G ∈ Pg)
    (hR : Rep 128 repArrs[j]! G) (hG2 : G * G = 1) :
    delta ⟨G, hG⟩ = if j = 4 ∨ j = 7 ∨ j = 8 then (-1 : ℤˣ) else 1 := by
  obtain ⟨-, -, -, -, -, hcount⟩ := x45_facts
  rw [delta_of_table repArrs[j]! G hR hG hG2, hcount j hj]
  interval_cases j <;> decide

end CFSG.EvenSporadicStandard.Fin76b.W16
