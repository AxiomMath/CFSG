module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrobPair
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open KFactsSmall

namespace K21cProof

open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

theorem not_isConj_c1_c12 : ¬ IsConj (c1 7) (c1 7 * c2 7) := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have h1 := Equiv.Perm.card_support_conj (σ := g) (τ := c1 7)
  rw [hg] at h1
  have h6 : (c1 7 * c2 7).support.card = 6 := by decide
  have h3 : (c1 7).support.card = 3 := by decide
  omega

theorem orderOf_c1 : orderOf (c1 7) = 3 :=
  orderOf_eq_prime (by decide) (by decide)

theorem orderOf_c12 : orderOf (c1 7 * c2 7) = 3 :=
  orderOf_eq_prime (by decide) (by decide)

theorem case_alt7 {J : Type} [Group J] (e : J ≃* alternatingGroup (Fin 7))
    (E : Subgroup (MulAut J)) (hc : Nat.card E = 9) :
    ∃ x ∈ E, ∃ y ∈ E, orderOf x = 3 ∧ orderOf y = 3 ∧ ¬ IsConj x y := by
  let Θ : Equiv.Perm (Fin 7) ≃* MulAut J :=
    (CFSG.RankThree.PartOne.alternatingConjEquiv (n := 7) (Or.inr le_rfl)).trans
      (MulAut.congr e).symm
  let E' : Subgroup (Equiv.Perm (Fin 7)) := E.map Θ.symm.toMonoidHom
  have hE'card : Nat.card E' = 9 := by
    rw [Subgroup.card_map_of_injective Θ.symm.injective, hc]
  have hE'p : IsPGroup 3 E' := IsPGroup.of_card (n := 2) (by rw [hE'card]; norm_num)
  obtain ⟨g, hg⟩ := exists_eq_map_conj_F0 f0Facts_seven factorization_seven hE'p hE'card
  have hmem : ∀ z : Equiv.Perm (Fin 7), z ∈ F0 7 → Θ (MulAut.conj g z) ∈ E := by
    intro z hz
    have h1 : MulAut.conj g z ∈ E' := by
      rw [hg]
      exact Subgroup.mem_map_of_mem _ hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp h1
    have : Θ (MulAut.conj g z) = w := by
      rw [← hwz]
      exact Θ.apply_symm_apply w
    rw [this]
    exact hw
  have hc1 : c1 7 ∈ F0 7 := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hc12 : c1 7 * c2 7 ∈ F0 7 :=
    Subgroup.mul_mem _ hc1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  refine ⟨Θ (MulAut.conj g (c1 7)), hmem _ hc1, Θ (MulAut.conj g (c1 7 * c2 7)), hmem _ hc12,
    ?_, ?_, ?_⟩
  · rw [Θ.orderOf_eq, (MulAut.conj g).orderOf_eq]
    exact orderOf_c1
  · rw [Θ.orderOf_eq, (MulAut.conj g).orderOf_eq]
    exact orderOf_c12
  · intro h
    have h1 : IsConj (MulAut.conj g (c1 7)) (MulAut.conj g (c1 7 * c2 7)) := by
      have := (Θ.symm.toMonoidHom).map_isConj h
      simpa using this
    have h2 := (MulAut.conj g⁻¹ : MulAut (Equiv.Perm (Fin 7))).toMonoidHom.map_isConj h1
    apply not_isConj_c1_c12
    simpa [MulAut.conj_apply, mul_assoc] using h2

theorem inf_eq_bot_or_le {G : Type} [Group G] (N M : Subgroup G) [N.Normal] [IsSimpleGroup M] :
    N ⊓ M = ⊥ ∨ M ≤ N := by
  haveI hn : (N.subgroupOf M).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf M) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hxM : x ∈ M := hx.2
    have h1 : (⟨x, hxM⟩ : M) ∈ N.subgroupOf M := hx.1
    rw [h] at h1
    have h2 : (⟨x, hxM⟩ : M) = 1 := h1
    have h3 : x = 1 := congrArg Subtype.val h2
    rw [h3]
    exact Subgroup.one_mem _
  · right
    intro x hx
    have h1 : (⟨x, hx⟩ : M) ∈ N.subgroupOf M := by rw [h]; trivial
    exact h1

structure Fam {J : Type} [Group J] {k : ℕ} (F : Fin k → Subgroup J) : Prop where
  normal : ∀ i, (F i).Normal
  simple : ∀ i, IsSimpleGroup (F i)
  nonab : ∀ i, ∃ a b : F i, a * b ≠ b * a
  comm : ∀ i j, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, a * b = b * a
  gen : ⨆ i, F i = ⊤
  cent : ∀ j : J, (∀ i, ∀ a ∈ F i, a * j = j * a) → j = 1
  aut : ∀ i, Nat.card (MulAut (F i)) = 336

variable {J : Type} [Group J] {k : ℕ} {F : Fin k → Subgroup J}

theorem Fam.exists_map_eq (hF : Fam F) (φ : MulAut J) (i : Fin k) :
    ∃ j, (F i).map φ.toMonoidHom = F j := by
  haveI := hF.normal
  haveI := hF.simple
  set N := (F i).map φ.toMonoidHom with hN
  haveI hNn : N.Normal := (hF.normal i).map φ.toMonoidHom φ.surjective
  haveI hNs : IsSimpleGroup N := (MulEquiv.subgroupMap φ (F i)).symm.isSimpleGroup
  have hFne : ∀ l, F l ≠ ⊥ := fun l => by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    exact (hF.simple l).toNontrivial
  by_cases hex : ∃ l, F l ≤ N
  · obtain ⟨l, hl⟩ := hex
    refine ⟨l, le_antisymm ?_ hl⟩
    rcases inf_eq_bot_or_le (F l) N with h | h
    · exact absurd (by rwa [inf_eq_left.mpr hl] at h) (hFne l)
    · exact h
  · exfalso
    push Not at hex
    have hbot : ∀ l, N ⊓ F l = ⊥ := fun l =>
      (inf_eq_bot_or_le N (F l)).resolve_right (hex l)
    have hNbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro n hn
      have : n = 1 := by
        apply hF.cent
        intro l a ha
        have h1 : n * a * n⁻¹ * a⁻¹ ∈ N ⊓ F l := by
          refine ⟨?_, ?_⟩
          · have h3 := hNn.conj_mem n⁻¹ (N.inv_mem hn) a
            have h4 := N.mul_mem hn h3
            rwa [← mul_assoc, ← mul_assoc] at h4
          · exact (F l).mul_mem ((hF.normal l).conj_mem a ha n) ((F l).inv_mem ha)
        rw [hbot l, Subgroup.mem_bot] at h1
        exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
      rw [this]
      exact Subgroup.one_mem _
    exact (Subgroup.nontrivial_iff_ne_bot N).mp hNs.toNontrivial hNbot

theorem Fam.F_injective (hF : Fam F) : Function.Injective F := by
  intro i j hij
  by_contra hne
  obtain ⟨a, b, hab⟩ := hF.nonab i
  apply hab
  apply Subtype.ext
  exact hF.comm i j hne a.1 a.2 b.1 (by rw [← hij]; exact b.2)

noncomputable def Fam.idx (hF : Fam F) (φ : MulAut J) (i : Fin k) : Fin k :=
  Classical.choose (hF.exists_map_eq φ i)

theorem Fam.map_idx (hF : Fam F) (φ : MulAut J) (i : Fin k) :
    (F i).map φ.toMonoidHom = F (hF.idx φ i) :=
  Classical.choose_spec (hF.exists_map_eq φ i)

theorem Fam.idx_eq_iff (hF : Fam F) (φ : MulAut J) (i j : Fin k) :
    hF.idx φ i = j ↔ (F i).map φ.toMonoidHom = F j :=
  ⟨fun h => by rw [hF.map_idx φ i, h], fun h => hF.F_injective (by rw [← hF.map_idx φ i, h])⟩

theorem Fam.idx_one (hF : Fam F) (i : Fin k) : hF.idx 1 i = i := by
  rw [hF.idx_eq_iff]
  ext x
  simp [Subgroup.mem_map]

theorem Fam.idx_mul (hF : Fam F) (φ ψ : MulAut J) (i : Fin k) :
    hF.idx (φ * ψ) i = hF.idx φ (hF.idx ψ i) := by
  rw [hF.idx_eq_iff]
  have h : (φ * ψ).toMonoidHom = φ.toMonoidHom.comp ψ.toMonoidHom := rfl
  rw [h, ← Subgroup.map_map, hF.map_idx ψ i, hF.map_idx φ]

@[expose] noncomputable def Fam.sigma (hF : Fam F) : MulAut J →* Equiv.Perm (Fin k) where
  toFun φ :=
    { toFun := hF.idx φ
      invFun := hF.idx φ⁻¹
      left_inv := fun i => by rw [← hF.idx_mul, inv_mul_cancel, hF.idx_one]
      right_inv := fun i => by rw [← hF.idx_mul, mul_inv_cancel, hF.idx_one] }
  map_one' := Equiv.ext fun i => hF.idx_one i
  map_mul' φ ψ := Equiv.ext fun i => hF.idx_mul φ ψ i

@[expose] def fixIdx (F : Fin k → Subgroup J) (φ : MulAut J) : Set (Fin k) :=
  {i | ∀ a ∈ F i, φ a = a}

@[expose] noncomputable def ufun (F : Fin k → Subgroup J) (φ : MulAut J) : ℕ :=
  Nat.card (fixIdx F φ)

theorem Fam.mem_fixIdx_conj (hF : Fam F) (g φ : MulAut J) (i : Fin k) :
    i ∈ fixIdx F φ ↔ hF.sigma g i ∈ fixIdx F (g * φ * g⁻¹) := by
  have hmap := hF.map_idx g i
  have key : ∀ b, b ∈ F (hF.idx g i) ↔ ∃ a ∈ F i, g a = b := by
    intro b
    rw [← hmap]
    simp [Subgroup.mem_map]
  constructor
  · intro h b hb
    obtain ⟨a, ha, rfl⟩ := (key b).mp hb
    show g (φ (g.symm (g a))) = g a
    rw [g.symm_apply_apply, h a ha]
  · intro h a ha
    have h1 := h (g a) ((key _).mpr ⟨a, ha, rfl⟩)
    change g (φ (g.symm (g a))) = g a at h1
    rw [g.symm_apply_apply] at h1
    exact g.injective h1

theorem Fam.ufun_conj (hF : Fam F) (g φ : MulAut J) : ufun F (g * φ * g⁻¹) = ufun F φ := by
  unfold ufun
  exact (Nat.card_congr (Equiv.subtypeEquiv (hF.sigma g) (hF.mem_fixIdx_conj g φ))).symm

theorem Fam.ufun_eq_of_isConj (hF : Fam F) {x y : MulAut J} (h : IsConj x y) :
    ufun F x = ufun F y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (hF.ufun_conj g x).symm

theorem Fam.sigma_ne_one_of_isConj (hF : Fam F) {x y : MulAut J} (h : IsConj x y)
    (hx : hF.sigma x ≠ 1) : hF.sigma y ≠ 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  intro h1
  apply hx
  rw [map_mul, map_mul] at h1
  have := congrArg (fun z => (hF.sigma g)⁻¹ * z * hF.sigma g) h1
  simpa [mul_assoc] using this

theorem exists_ne_count {E : Type} [Group E] {k : ℕ} (hk : k = 2 ∨ k = 3) (hE : Nat.card E = 9)
    (K : Fin k → Subgroup E) (hK : ∀ i, Nat.card (K i) = 3 ∨ Nat.card (K i) = 9)
    (hbot : ∀ x : E, (∀ i, x ∈ K i) → x = 1) :
    ∃ x y : E, x ≠ 1 ∧ y ≠ 1 ∧ Nat.card {i // x ∈ K i} ≠ Nat.card {i // y ∈ K i} := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = 9 := by rw [← Nat.card_eq_fintype_card]; exact hE
  have hc : ∀ x : E, Nat.card {i // x ∈ K i} =
      (Finset.univ.filter fun i : Fin k => x ∈ K i).card := by
    intro x
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcK : ∀ i, Nat.card (K i) = (Finset.univ.filter fun x : E => x ∈ K i).card := by
    intro i
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [hc]
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0⟩ : ∃ x0 : E, x0 ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card E = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨1, fun x => h x⟩
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = (Finset.univ.filter fun i : Fin k => x0 ∈ K i).card := ⟨_, rfl⟩
  have hconst : ∀ x : E, x ≠ 1 → (Finset.univ.filter fun i : Fin k => x ∈ K i).card = m :=
    fun x hx => by rw [hm]; exact hcon x x0 hx hx0
  have hone : (Finset.univ.filter fun i : Fin k => (1 : E) ∈ K i).card = k := by
    simp
  have hmk : m < k := by
    have hle : m ≤ k := by
      rw [hm]
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k)) (fun i => x0 ∈ K i)
    refine lt_of_le_of_ne hle fun h => hx0 (hbot x0 fun i => ?_)
    have h1 : (Finset.univ.filter fun i : Fin k => x0 ∈ K i) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [← hm, h]; simp)
    have h2 : i ∈ Finset.univ.filter fun i : Fin k => x0 ∈ K i := by rw [h1]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp h2).2
  have hsum1 : ∑ x : E, (Finset.univ.filter fun i : Fin k => x ∈ K i).card = k + 8 * m := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : E)), hone,
      Finset.sum_congr rfl (fun x hx => hconst x (Finset.ne_of_mem_erase hx)), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardE]
    simp
  have hsum2 : ∑ x : E, (Finset.univ.filter fun i : Fin k => x ∈ K i).card =
      ∑ i : Fin k, Nat.card (K i) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcK i, Finset.card_filter]
  rw [hsum2] at hsum1
  rcases hk with rfl | rfl
  · rw [Fin.sum_univ_two] at hsum1
    rcases hK 0 with h0 | h0 <;> rcases hK 1 with h1 | h1 <;> omega
  · rw [Fin.sum_univ_three] at hsum1
    rcases hK 0 with h0 | h0 <;> rcases hK 1 with h1 | h1 <;> rcases hK 2 with h2 | h2 <;> omega

@[expose] def restr (H : Subgroup J) (φ : MulAut J) (h : H.map φ.toMonoidHom = H) : MulAut H :=
  (MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr h)

@[expose] noncomputable def resHom (E : Subgroup (MulAut J))
    (hE : ∀ φ ∈ E, ∀ i, (F i).map φ.toMonoidHom = F i) (i : Fin k) : E →* MulAut (F i) where
  toFun φ := restr (F i) φ.1 (hE φ.1 φ.2 i)
  map_one' := by
    ext a
    rfl
  map_mul' φ ψ := by
    ext a
    rfl

theorem mem_ker_resHom (E : Subgroup (MulAut J))
    (hE : ∀ φ ∈ E, ∀ i, (F i).map φ.toMonoidHom = F i) (i : Fin k) (φ : E) :
    φ ∈ (resHom E hE i).ker ↔ ∀ a ∈ F i, φ.1 a = a := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h a ha
    exact congrArg (fun ψ : MulAut (F i) => ((ψ ⟨a, ha⟩ : F i) : J)) h
  · intro h
    ext a
    exact h a.1 a.2

theorem card_ker_resHom (hF : Fam F) (E : Subgroup (MulAut J)) (hc : Nat.card E = 9)
    (hE : ∀ φ ∈ E, ∀ i, (F i).map φ.toMonoidHom = F i) (i : Fin k) :
    Nat.card (resHom E hE i).ker = 3 ∨ Nat.card (resHom E hE i).ker = 9 := by
  have h1 := Subgroup.card_ker_mul_card_range (resHom E hE i)
  have h2 : Nat.card (resHom E hE i).range ∣ 336 := by
    rw [← hF.aut i]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hc] at h1
  generalize Nat.card (resHom E hE i).range = r at h1 h2
  generalize Nat.card (resHom E hE i).ker = q at h1 ⊢
  have h3 : r ∣ 9 := Dvd.intro_left _ h1
  have h4 : r ∣ 3 := by
    have h5 := Nat.dvd_gcd h2 h3
    have e : Nat.gcd 336 9 = 3 := by norm_num
    rwa [e] at h5
  rcases (Nat.dvd_prime Nat.prime_three).mp h4 with h | h <;> subst h <;> omega

theorem eq_one_of_forall_fixed (hF : Fam F) (φ : MulAut J) (h : ∀ i, ∀ a ∈ F i, φ a = a) :
    φ = 1 := by
  ext j
  have hj : j ∈ ⨆ i, F i := by rw [hF.gen]; trivial
  refine Subgroup.iSup_induction F (C := fun x => φ x = x) hj (fun i x hx => h i x hx) ?_ ?_
  · exact map_one φ
  · intro x y hx hy
    rw [map_mul, hx, hy]

theorem case_sigma_trivial (hF : Fam F) (hk : k = 2 ∨ k = 3) (E : Subgroup (MulAut J))
    (hc : Nat.card E = 9) (hσ : ∀ φ ∈ E, hF.sigma φ = 1) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧ ufun F x ≠ ufun F y := by
  have hE : ∀ φ ∈ E, ∀ i, (F i).map φ.toMonoidHom = F i := by
    intro φ hφ i
    have h1 : hF.idx φ i = i := congrArg (fun τ : Equiv.Perm (Fin k) => τ i) (hσ φ hφ)
    exact (hF.idx_eq_iff φ i i).mp h1
  let K : Fin k → Subgroup E := fun i => (resHom E hE i).ker
  have hK : ∀ i, Nat.card (K i) = 3 ∨ Nat.card (K i) = 9 := fun i => card_ker_resHom hF E hc hE i
  have hbot : ∀ x : E, (∀ i, x ∈ K i) → x = 1 := by
    intro x hx
    apply Subtype.ext
    exact eq_one_of_forall_fixed hF x.1 fun i a ha => (mem_ker_resHom E hE i x).mp (hx i) a ha
  obtain ⟨x, y, hx, hy, hne⟩ := exists_ne_count hk hc K hK hbot
  have hu : ∀ z : E, ufun F z.1 = Nat.card {i // z ∈ K i} := by
    intro z
    unfold ufun
    exact Nat.card_congr (Equiv.subtypeEquivRight fun i => (mem_ker_resHom E hE i z).symm)
  refine ⟨x.1, x.2, y.1, y.2, fun h => hx (Subtype.ext h), fun h => hy (Subtype.ext h), ?_⟩
  rw [hu, hu]
  exact hne

theorem case_sigma_nontrivial (hF : Fam F) (hk : k = 2 ∨ k = 3) (E : Subgroup (MulAut J))
    (hc : Nat.card E = 9) (hσ : ∃ φ ∈ E, hF.sigma φ ≠ 1) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧ hF.sigma x ≠ 1 ∧ hF.sigma y = 1 := by
  obtain ⟨x, hxE, hx1⟩ := hσ
  have hnotinj : ¬ Function.Injective (hF.sigma.comp E.subtype) := by
    intro hinj
    have h := Nat.card_le_card_of_injective _ hinj
    rw [hc, Nat.card_perm, Nat.card_fin] at h
    rcases hk with rfl | rfl <;> norm_num [Nat.factorial] at h
  rw [injective_iff_map_eq_one] at hnotinj
  push Not at hnotinj
  obtain ⟨b, hb1, hb⟩ := hnotinj
  refine ⟨x, hxE, b.1, b.2, ?_, ?_, hx1, hb1⟩
  · intro h
    apply hx1
    rw [h, map_one]
  · intro h
    exact hb (Subtype.ext h)

theorem Fam.main (hF : Fam F) (hk : k = 2 ∨ k = 3) (E : Subgroup (MulAut J))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    ∃ x ∈ E, ∃ y ∈ E, orderOf x = 3 ∧ orderOf y = 3 ∧ ¬ IsConj x y := by
  have hord : ∀ z ∈ E, z ≠ 1 → orderOf z = 3 := fun z hz hz1 =>
    orderOf_eq_prime (hE.2 z hz) hz1
  by_cases hσ : ∀ φ ∈ E, hF.sigma φ = 1
  · obtain ⟨x, hxE, y, hyE, hx1, hy1, hne⟩ := case_sigma_trivial hF hk E hc hσ
    exact ⟨x, hxE, y, hyE, hord x hxE hx1, hord y hyE hy1,
      fun h => hne (hF.ufun_eq_of_isConj h)⟩
  · push Not at hσ
    obtain ⟨x, hxE, y, hyE, hx1, hy1, hxs, hys⟩ := case_sigma_nontrivial hF hk E hc hσ
    exact ⟨x, hxE, y, hyE, hord x hxE hx1, hord y hyE hy1,
      fun h => hF.sigma_ne_one_of_isConj h hxs hys⟩

theorem center_eq_bot_of_simple {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  haveI := hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center S := by rw [h]; trivial
    exact ((Subgroup.mem_center_iff.mp ha) b).symm

@[expose] def piFactor (S : Type) [Group S] (k : ℕ) (i : Fin k) : Subgroup (Fin k → S) :=
  (MonoidHom.mulSingle (fun _ : Fin k => S) i).range

noncomputable def piFactorEquiv (S : Type) [Group S] (k : ℕ) (i : Fin k) :
    S ≃* piFactor S k i :=
  MonoidHom.ofInjective (f := MonoidHom.mulSingle (fun _ : Fin k => S) i)
    (Pi.mulSingle_injective (M := fun _ : Fin k => S) i)

theorem piFam {S : Type} [Group S] (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hAut : Nat.card (MulAut S) = 336) (k : ℕ) : Fam (piFactor S k) where
  normal i := by
    refine ⟨?_⟩
    rintro _ ⟨s, rfl⟩ g
    refine ⟨g i * s * (g i)⁻¹, ?_⟩
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Pi.mulSingle_eq_of_ne hl]
  simple i := (piFactorEquiv S k i).symm.isSimpleGroup
  nonab i := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨piFactorEquiv S k i a, piFactorEquiv S k i b, fun h => hab ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact (piFactorEquiv S k i).injective h
  comm i j hij := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact (Pi.mulSingle_commute (f := fun _ : Fin k => S) hij s t).eq
  gen := by
    rw [eq_top_iff]
    intro j _
    rw [← Finset.noncommProd_mulSingle j]
    exact Subgroup.noncommProd_mem _ _ fun i _ => Subgroup.mem_iSup_of_mem i ⟨j i, rfl⟩
  cent j hj := by
    funext i
    have hz : j i ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      have h1 := congrFun (hj i (Pi.mulSingle i s) ⟨s, rfl⟩) i
      simpa using h1
    rw [center_eq_bot_of_simple hS hnab] at hz
    exact hz
  aut i := by
    rw [← Nat.card_congr (MulAut.congr (piFactorEquiv S k i)).toEquiv]
    exact hAut

theorem lThreeTwo_facts {S : Type} [Group S]
    (h : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsLThreeTwo S) :
    IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧ Nat.card (MulAut S) = 336 := by
  obtain ⟨e⟩ := CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.nonempty_mulEquiv_GL_of_isLThreeTwo h
  refine ⟨CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_simple h, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ :=
      CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.exists_mul_ne_mul_GL_three_zmod_two
    refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
    have h1 := congrArg e h'
    simpa using h1
  · rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32

theorem case_prod {J : Type} [Group J] {k : ℕ} (hk : k = 2 ∨ k = 3) {S : Type} [Group S]
    (hS : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsLThreeTwo S)
    (e : J ≃* (Fin k → S)) (E : Subgroup (MulAut J))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    ∃ x ∈ E, ∃ y ∈ E, orderOf x = 3 ∧ orderOf y = 3 ∧ ¬ IsConj x y := by
  obtain ⟨hs, hn, ha⟩ := lThreeTwo_facts hS
  let Θ : MulAut J ≃* MulAut (Fin k → S) := MulAut.congr e
  let E' : Subgroup (MulAut (Fin k → S)) := E.map Θ.toMonoidHom
  have hE' : CFSG.Open.IsElemAbelian 3 E' := by
    haveI := hE.1
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hc' : Nat.card E' = 9 := by
    rw [Subgroup.card_map_of_injective Θ.injective, hc]
  obtain ⟨x', hx', y', hy', hox, hoy, hnc⟩ := (piFam hs hn ha k).main hk E' hE' hc'
  obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.mp hx'
  obtain ⟨y, hyE, rfl⟩ := Subgroup.mem_map.mp hy'
  refine ⟨x, hxE, y, hyE, ?_, ?_, fun h => hnc (Θ.toMonoidHom.map_isConj h)⟩
  · rw [← hox]
    exact (Θ.orderOf_eq x).symm
  · rw [← hoy]
    exact (Θ.orderOf_eq y).symm

end K21cProof

theorem K21c_holds : K21c := by
  intro J _ _ hJ E hE hc
  rcases hJ with hJ | hJ | hJ
  · obtain ⟨e⟩ := hJ
    exact K21cProof.case_alt7 e E hc
  · obtain ⟨S, _, hS, ⟨e⟩⟩ := hJ
    exact K21cProof.case_prod (Or.inl rfl) hS e E hE hc
  · obtain ⟨S, _, hS, ⟨e⟩⟩ := hJ
    exact K21cProof.case_prod (Or.inr rfl) hS e E hE hc

end CFSG.LocalAnalysis.RankThreeUC.S15
