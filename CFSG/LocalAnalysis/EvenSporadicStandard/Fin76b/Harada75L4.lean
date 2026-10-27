module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

@[expose] def GenLE4 (S : Type) [Group S] : Prop :=
  ∀ U : Subgroup S, ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U

section TwoGroups

theorem coatom_index_eq_two {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) {M : Subgroup Q}
    (hM : IsCoatom M) : M.index = 2 := by
  haveI := IsPGroup.isNilpotent hQ
  exact (IsPGroup.isCoatom_iff_index_eq_prime hQ).mp hM

theorem coatom_props {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) {M : Subgroup Q}
    (hM : IsCoatom M) : (∀ x : Q, x ^ 2 ∈ M) ∧ (∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ M) := by
  have hidx := coatom_index_eq_two hQ hM
  haveI : M.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (Q ⧸ M) = 2 := by rw [← Subgroup.index_eq_card, hidx]
  haveI : IsCyclic (Q ⧸ M) := isCyclic_of_prime_card hcard
  letI : CommGroup (Q ⧸ M) := IsCyclic.commGroup
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · have h := Subgroup.pow_index_mem M x
    rwa [hidx] at h
  · rw [← QuotientGroup.eq_one_iff]
    have hc : (x : Q ⧸ M) * (y : Q ⧸ M) = (y : Q ⧸ M) * (x : Q ⧸ M) := mul_comm _ _
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hc, mul_inv_cancel_right, mul_inv_cancel]

theorem mem_frattini_of_forall {Q : Type} [Group Q] {z : Q}
    (h : ∀ M : Subgroup Q, IsCoatom M → z ∈ M) : z ∈ frattini Q := by
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  exact fun M hM => h M hM

theorem comm_mem_frattini {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) (x y : Q) :
    x * y * x⁻¹ * y⁻¹ ∈ frattini Q :=
  mem_frattini_of_forall fun _ hM => (coatom_props hQ hM).2 x y

theorem commute_sq_of_frattini_bot {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (h : frattini Q = ⊥) : (∀ x y : Q, x * y = y * x) ∧ (∀ x : Q, x ^ 2 = 1) := by
  constructor
  · intro x y
    have h1 := comm_mem_frattini hQ x y
    rw [h, Subgroup.mem_bot] at h1
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  · intro x
    have h1 : x ^ 2 ∈ frattini Q :=
      mem_frattini_of_forall fun M hM => (coatom_props hQ hM).1 x
    rw [h, Subgroup.mem_bot] at h1
    exact h1

theorem rank_le_of_card_le_two_pow : ∀ (k : ℕ) (Q : Type) [Group Q] [Finite Q],
    IsPGroup 2 Q → Nat.card Q ≤ 2 ^ k → Group.rank Q ≤ k := by
  intro k
  induction k with
  | zero =>
    intro Q _ _ hQ hcard
    have hsub : Subsingleton Q := (Finite.card_le_one_iff_subsingleton).mp (by simpa using hcard)
    rw [Group.rank_eq_zero Q]
  | succ k ih =>
    intro Q _ _ hQ hcard
    by_cases hsub : Subsingleton Q
    · rw [Group.rank_eq_zero Q]
      exact Nat.zero_le _
    rcases eq_top_or_exists_le_coatom (⊥ : Subgroup Q) with htop | ⟨M, hM, -⟩
    · exfalso
      apply hsub
      constructor
      intro x y
      have hx : x ∈ (⊥ : Subgroup Q) := by rw [htop]; exact Subgroup.mem_top x
      have hy : y ∈ (⊥ : Subgroup Q) := by rw [htop]; exact Subgroup.mem_top y
      rw [Subgroup.mem_bot] at hx hy
      rw [hx, hy]
    · have hidx := coatom_index_eq_two hQ hM
      have hMcard : Nat.card M * 2 = Nat.card Q := by
        rw [← hidx]; exact Subgroup.card_mul_index M
      have hMle : Nat.card M ≤ 2 ^ k := by
        have h2 : Nat.card M * 2 ≤ 2 ^ k * 2 := by
          rw [hMcard, ← pow_succ]; exact hcard
        exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
      have hMrank : Group.rank M ≤ k := ih M (hQ.to_subgroup M) hMle
      obtain ⟨Y, hYcard, hYcl⟩ := Group.rank_spec M
      classical
      have hX₀card : (Y.image (fun y : M => (y : Q))).card ≤ k :=
        (Finset.card_image_le (s := Y) (f := fun y : M => (y : Q))).trans (hYcard.le.trans hMrank)
      set X₀ : Finset Q := Y.image (fun y : M => (y : Q)) with hX₀
      have hMtop : M = Subgroup.map M.subtype (⊤ : Subgroup M) := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hX₀cl : Subgroup.closure (X₀ : Set Q) = M := by
        have h1 : Subgroup.closure (X₀ : Set Q) =
            Subgroup.map M.subtype (Subgroup.closure (Y : Set M)) := by
          rw [MonoidHom.map_closure]
          congr 1
          ext q
          simp [X₀]
        rw [h1, hYcl, ← hMtop]
      obtain ⟨g, hgM⟩ : ∃ g : Q, g ∉ M := by
        by_contra hcon
        exact hM.1 (eq_top_iff.mpr fun g _ => Classical.byContradiction fun hg => hcon ⟨g, hg⟩)
      have hgen : Subgroup.closure ((insert g X₀ : Finset Q) : Set Q) = ⊤ := by
        have hle : M ≤ Subgroup.closure ((insert g X₀ : Finset Q) : Set Q) := by
          rw [← hX₀cl]
          apply Subgroup.closure_mono
          intro x hx
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
          exact Or.inr hx
        have hmem : g ∈ Subgroup.closure ((insert g X₀ : Finset Q) : Set Q) :=
          Subgroup.subset_closure (by simp)
        have hlt : M < Subgroup.closure ((insert g X₀ : Finset Q) : Set Q) :=
          lt_of_le_of_ne hle (fun h => hgM (h ▸ hmem))
        exact hM.2 _ hlt
      calc Group.rank Q ≤ (insert g X₀).card := Group.rank_le hgen
        _ ≤ X₀.card + 1 := Finset.card_insert_le _ _
        _ ≤ k + 1 := by omega

theorem rank_le_of_card_le_mul_frattini {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (m : ℕ) (h : Nat.card Q ≤ 2 ^ m * Nat.card (frattini Q)) : Group.rank Q ≤ m := by
  classical
  haveI : (frattini Q).Normal := inferInstance
  have hPp : IsPGroup 2 (Q ⧸ frattini Q) := hQ.to_quotient (frattini Q)
  have hidx : (frattini Q).index * Nat.card (frattini Q) = Nat.card Q :=
    Subgroup.index_mul_card _
  rw [Subgroup.index_eq_card] at hidx
  have hpos : 0 < Nat.card (frattini Q) := Nat.card_pos
  have hcardP : Nat.card (Q ⧸ frattini Q) ≤ 2 ^ m := by
    apply Nat.le_of_mul_le_mul_right _ hpos
    rw [hidx]
    exact h
  have hrank : Group.rank (Q ⧸ frattini Q) ≤ m := rank_le_of_card_le_two_pow m _ hPp hcardP
  obtain ⟨Y, hYcard, hYcl⟩ := Group.rank_spec (Q ⧸ frattini Q)
  set f : Q ⧸ frattini Q → Q := Function.surjInv (QuotientGroup.mk_surjective (s := frattini Q))
    with hf_def
  have hf : ∀ p : Q ⧸ frattini Q, ((f p : Q) : Q ⧸ frattini Q) = p := fun p =>
    Function.surjInv_eq _ p
  have hXcard : (Y.image f).card ≤ m :=
    (Finset.card_image_le (s := Y) (f := f)).trans (hYcard.le.trans hrank)
  set X : Finset Q := Y.image f with hX_def
  have himage : (QuotientGroup.mk' (frattini Q)) '' (X : Set Q) = (Y : Set (Q ⧸ frattini Q)) := by
    rw [hX_def, Finset.coe_image, Set.image_image]
    simp [hf]
  have hmap : Subgroup.map (QuotientGroup.mk' (frattini Q)) (Subgroup.closure (X : Set Q)) = ⊤ := by
    rw [MonoidHom.map_closure, himage, hYcl]
  have hclX : Subgroup.closure (X : Set Q) ⊔ frattini Q = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (QuotientGroup.mk g : Q ⧸ frattini Q) ∈
        Subgroup.map (QuotientGroup.mk' (frattini Q)) (Subgroup.closure (X : Set Q)) := by
      rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
    rw [QuotientGroup.mk'_apply] at hxg
    have hφ : x⁻¹ * g ∈ frattini Q := QuotientGroup.eq.mp hxg
    have hgx : g = x * (x⁻¹ * g) := by group
    rw [hgx]
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hφ)
  have hgen : Subgroup.closure (X : Set Q) = ⊤ := frattini_nongenerating hclX
  calc Group.rank Q ≤ X.card := Group.rank_le hgen
    _ ≤ m := hXcard


end TwoGroups

section Aux

theorem exists_fixed_ne_of_even {G α : Type} [Group G] [MulAction G α] [Finite α]
    (hG : IsPGroup 2 G) (hα : Nat.card α % 2 = 0) (e : α) (he : ∀ g : G, g • e = e) :
    ∃ x : α, x ≠ e ∧ ∀ g : G, g • x = x := by
  have hmod := hG.card_modEq_card_fixedPoints α
  have hF : Nat.card (MulAction.fixedPoints G α) % 2 = 0 := by
    unfold Nat.ModEq at hmod
    omega
  have he' : e ∈ MulAction.fixedPoints G α := MulAction.mem_fixedPoints.mpr he
  haveI : Nonempty (MulAction.fixedPoints G α) := ⟨⟨e, he'⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints G α) := Nat.card_pos
  have h2 : 1 < Nat.card (MulAction.fixedPoints G α) := by omega
  rw [Finite.one_lt_card_iff_nontrivial] at h2
  obtain ⟨y, hy⟩ := exists_ne (⟨e, he'⟩ : MulAction.fixedPoints G α)
  exact ⟨y.1, fun h => hy (Subtype.ext h), fun g => MulAction.mem_fixedPoints.mp y.2 g⟩

theorem normal_of_comm_group {G : Type} [Group G] (hG : ∀ x y : G, x * y = y * x)
    (N : Subgroup G) : N.Normal :=
  ⟨fun n hn g => by
    have h : g * n * g⁻¹ = n := by rw [hG g n, mul_inv_cancel_right]
    rw [h]
    exact hn⟩

theorem zpow_eq_one_or_self {G : Type} [Group G] (g : G) (hg : g * g = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have hg2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, hg2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hg2, one_zpow, one_mul]

theorem mem_zpowers_iff_two {G : Type} [Group G] {a : G} (ha2 : a * a = 1) (x : G) :
    x ∈ Subgroup.zpowers a ↔ x = 1 ∨ x = a := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact zpow_eq_one_or_self a ha2 k
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem coset_pair {A : Type} [Group A] (hAc : ∀ x y : A, x * y = y * x) {a : A}
    (ha2 : a * a = 1) (g y : A) (h : y⁻¹ * g = 1 ∨ y⁻¹ * g = a) : y = g ∨ y = a * g := by
  rcases h with h | h
  · left
    exact inv_mul_eq_one.mp h
  · right
    have h1 : y⁻¹ = a * g⁻¹ := eq_mul_inv_of_mul_eq h
    have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    calc y = (y⁻¹)⁻¹ := (inv_inv y).symm
      _ = (a * g⁻¹)⁻¹ := by rw [h1]
      _ = g * a⁻¹ := by group
      _ = a * g := by rw [h2, hAc g a]

end Aux

section Conj

variable {S : Type} [Group S]

@[expose] def cj {A : Subgroup S} (hN : A.Normal) (s : S) (x : A) : A :=
  ⟨s * x * s⁻¹, hN.conj_mem x.1 x.2 s⟩

theorem cj_one {A : Subgroup S} (hN : A.Normal) (x : A) : cj hN 1 x = x :=
  Subtype.ext (by simp [cj])

theorem cj_mul_apply {A : Subgroup S} (hN : A.Normal) (s t : S) (x : A) :
    cj hN (s * t) x = cj hN s (cj hN t x) :=
  Subtype.ext (by simp [cj, mul_assoc])

theorem cj_mul {A : Subgroup S} (hN : A.Normal) (s : S) (x y : A) :
    cj hN s (x * y) = cj hN s x * cj hN s y :=
  Subtype.ext (by simp [cj, mul_assoc])

theorem cj_one_elem {A : Subgroup S} (hN : A.Normal) (s : S) : cj hN s 1 = 1 :=
  Subtype.ext (by simp [cj])

abbrev conjMulAction {A : Subgroup S} (hN : A.Normal) : MulAction S A where
  smul s x := cj hN s x
  one_smul x := cj_one hN x
  mul_smul s t x := cj_mul_apply hN s t x

@[expose] def cjHom {A : Subgroup S} (hN : A.Normal) (s : S) : A →* A where
  toFun := cj hN s
  map_one' := cj_one_elem hN s
  map_mul' := cj_mul hN s

theorem cjHom_le {A : Subgroup S} (hN : A.Normal) (N : Subgroup A)
    (hNinv : ∀ s : S, ∀ x ∈ N, cj hN s x ∈ N) (s : S) : N ≤ N.comap (cjHom hN s) := by
  intro x hx
  exact hNinv s x hx

abbrev quotMulAction {A : Subgroup S} (hN : A.Normal) (N : Subgroup A) [N.Normal]
    (hNinv : ∀ s : S, ∀ x ∈ N, cj hN s x ∈ N) : MulAction S (A ⧸ N) where
  smul s q := QuotientGroup.map N N (cjHom hN s) (cjHom_le hN N hNinv s) q
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      show QuotientGroup.map N N (cjHom hN 1) (cjHom_le hN N hNinv 1) (x : A ⧸ N) = x
      rw [QuotientGroup.map_mk]
      congr 1
      exact cj_one hN x
  mul_smul s t q := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      show QuotientGroup.map N N (cjHom hN (s * t)) (cjHom_le hN N hNinv (s * t)) (x : A ⧸ N) =
        QuotientGroup.map N N (cjHom hN s) (cjHom_le hN N hNinv s)
          (QuotientGroup.map N N (cjHom hN t) (cjHom_le hN N hNinv t) (x : A ⧸ N))
      simp only [QuotientGroup.map_mk]
      congr 1
      exact cj_mul_apply hN s t x

end Conj


section Structure

theorem exists_block {S : Type} [Group S] [Finite S] {A : Subgroup S} (hS : IsPGroup 2 S)
    (hN : A.Normal) (hAc : ∀ x y : A, x * y = y * x) (hcard : Nat.card A = 8) (a : A)
    (ha1 : a ≠ 1) (ha2 : a * a = 1) (ha : ∀ s : S, cj hN s a = a) :
    ∃ b : A, b ∉ Subgroup.zpowers a ∧ ∀ s : S, cj hN s b = b ∨ cj hN s b = a * b := by
  classical
  haveI hNN : (Subgroup.zpowers a).Normal := normal_of_comm_group hAc _
  have hNinv : ∀ s : S, ∀ x ∈ Subgroup.zpowers a, cj hN s x ∈ Subgroup.zpowers a := by
    intro s x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : cj hN s (a ^ k) = a ^ k := by
      have h2 : cjHom hN s (a ^ k) = (cjHom hN s a) ^ k := map_zpow (cjHom hN s) a k
      have h3 : cjHom hN s a = a := ha s
      rw [h3] at h2
      exact h2
    rw [h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) k
  have hQcard : Nat.card (A ⧸ Subgroup.zpowers a) = 4 := by
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers a)
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1, hcard] at h1
    rw [← Subgroup.index_eq_card]
    omega
  letI := quotMulAction hN (Subgroup.zpowers a) hNinv
  obtain ⟨q, hq1, hqfix⟩ := exists_fixed_ne_of_even hS (by rw [hQcard])
    (1 : A ⧸ Subgroup.zpowers a)
    (fun g => map_one (QuotientGroup.map _ _ (cjHom hN g) (cjHom_le hN _ hNinv g)))
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨b, fun hb => hq1 ((QuotientGroup.eq_one_iff b).mpr hb), fun s => ?_⟩
  have hfix := hqfix s
  change QuotientGroup.map _ _ (cjHom hN s) (cjHom_le hN _ hNinv s)
    (b : A ⧸ Subgroup.zpowers a) = (b : A ⧸ Subgroup.zpowers a) at hfix
  rw [QuotientGroup.map_mk] at hfix
  have hmem : (cjHom hN s b)⁻¹ * b ∈ Subgroup.zpowers a := QuotientGroup.eq.mp hfix
  rw [mem_zpowers_iff_two ha2] at hmem
  exact coset_pair hAc ha2 b (cj hN s b) hmem

open Classical in
theorem exists_third {B : Type} [Group B] [Finite B] (hB8 : Nat.card B = 8) (a b : B) :
    ∃ c : B, c ∉ ({1, a, b, a * b} : Finset B) := by
  classical
  by_contra hcon
  have h' : ∀ c : B, c ∈ ({1, a, b, a * b} : Finset B) := fun c =>
    Classical.byContradiction fun hc => hcon ⟨c, hc⟩
  haveI := Fintype.ofFinite B
  have hsub : (Finset.univ : Finset B) ⊆ {1, a, b, a * b} := fun c _ => h' c
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ : Finset B).card = 8 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hB8]
  have h3 : ({1, a, b, a * b} : Finset B).card ≤ 4 := Finset.card_le_four
  omega

theorem coords_of_card {B : Type} [Group B] [Finite B] (hBc : ∀ x y : B, x * y = y * x)
    (hB8 : Nat.card B = 8) (a b c : B) (ha1 : a ≠ 1) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hb1 : b ≠ 1) (hba : b ≠ a) (hc1 : c ≠ 1) (hca : c ≠ a) (hcb : c ≠ b) (hcab : c ≠ a * b) :
    ∀ x : B, x = 1 ∨ x = a ∨ x = b ∨ x = a * b ∨ x = c ∨ x = a * c ∨ x = b * c ∨
      x = a * (b * c) := by
  classical
  haveI hNN : (Subgroup.zpowers a).Normal := normal_of_comm_group hBc _
  have hcos : ∀ x y : B, ((x : B ⧸ Subgroup.zpowers a) = (y : B ⧸ Subgroup.zpowers a)) ↔
      (y = x ∨ y = a * x) := by
    intro x y
    rw [QuotientGroup.eq, mem_zpowers_iff_two ha2]
    constructor
    · rintro (h | h)
      · exact Or.inl (inv_mul_eq_one.mp h).symm
      · right
        calc y = x * (x⁻¹ * y) := by group
          _ = x * a := by rw [h]
          _ = a * x := hBc x a
    · rintro (h | h)
      · subst h
        left
        exact inv_mul_cancel y
      · subst h
        right
        rw [hBc a x, ← mul_assoc, inv_mul_cancel, one_mul]
  have hne : ∀ x y : B, y ≠ x → y ≠ a * x → (x : B ⧸ Subgroup.zpowers a) ≠ y := by
    intro x y h1 h2 e
    rcases (hcos x y).mp e with h | h
    · exact h1 h
    · exact h2 h
  have n01 : ((1 : B) : B ⧸ Subgroup.zpowers a) ≠ (b : B ⧸ Subgroup.zpowers a) :=
    hne 1 b (fun h => hb1 h) (fun h => hba (h.trans (mul_one a)))
  have n02 : ((1 : B) : B ⧸ Subgroup.zpowers a) ≠ (c : B ⧸ Subgroup.zpowers a) :=
    hne 1 c (fun h => hc1 h) (fun h => hca (h.trans (mul_one a)))
  have hcbc : c = b * (b * c) := by rw [← mul_assoc, hb2, one_mul]
  have n03 : ((1 : B) : B ⧸ Subgroup.zpowers a) ≠ ((b * c : B) : B ⧸ Subgroup.zpowers a) := by
    apply hne 1 (b * c)
    · intro h
      apply hcb
      calc c = b * (b * c) := hcbc
        _ = b * 1 := by rw [h]
        _ = b := mul_one b
    · intro h
      apply hcab
      calc c = b * (b * c) := hcbc
        _ = b * (a * 1) := by rw [h]
        _ = a * b := by rw [mul_one, hBc b a]
  have n12 : (b : B ⧸ Subgroup.zpowers a) ≠ (c : B ⧸ Subgroup.zpowers a) :=
    hne b c hcb hcab
  have n13 : (b : B ⧸ Subgroup.zpowers a) ≠ ((b * c : B) : B ⧸ Subgroup.zpowers a) := by
    apply hne b (b * c)
    · intro h
      apply hc1
      exact mul_left_cancel (h.trans (mul_one b).symm)
    · intro h
      apply hca
      exact mul_left_cancel (h.trans (hBc a b))
  have n23 : (c : B ⧸ Subgroup.zpowers a) ≠ ((b * c : B) : B ⧸ Subgroup.zpowers a) := by
    apply hne c (b * c)
    · intro h
      apply hb1
      exact mul_right_cancel (h.trans (one_mul c).symm)
    · intro h
      apply hba
      exact mul_right_cancel h
  have hQcard : Nat.card (B ⧸ Subgroup.zpowers a) = 4 := by
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers a)
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1, hB8] at h1
    rw [← Subgroup.index_eq_card]
    omega
  haveI := Fintype.ofFinite (B ⧸ Subgroup.zpowers a)
  let R : Finset (B ⧸ Subgroup.zpowers a) :=
    {((1 : B) : B ⧸ Subgroup.zpowers a), (b : B ⧸ Subgroup.zpowers a),
      (c : B ⧸ Subgroup.zpowers a), ((b * c : B) : B ⧸ Subgroup.zpowers a)}
  have hRcard : R.card = 4 := by
    have h1 : ((1 : B) : B ⧸ Subgroup.zpowers a) ∉
        ({(b : B ⧸ Subgroup.zpowers a), (c : B ⧸ Subgroup.zpowers a),
          ((b * c : B) : B ⧸ Subgroup.zpowers a)} : Finset _) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨n01, n02, n03⟩
    have h2 : (b : B ⧸ Subgroup.zpowers a) ∉
        ({(c : B ⧸ Subgroup.zpowers a), ((b * c : B) : B ⧸ Subgroup.zpowers a)} : Finset _) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨n12, n13⟩
    simp only [R]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_pair n23]
  have hRall : R = Finset.univ := Finset.eq_univ_of_card R (by rw [hRcard, Nat.card_eq_fintype_card.symm, hQcard])
  intro x
  have hx : (x : B ⧸ Subgroup.zpowers a) ∈ R := by
    rw [hRall]
    exact Finset.mem_univ _
  simp only [R, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h
  · rcases (hcos 1 x).mp h.symm with h' | h' <;> subst h' <;> simp
  · rcases (hcos b x).mp h.symm with h' | h' <;> subst h' <;> simp
  · rcases (hcos c x).mp h.symm with h' | h' <;> subst h' <;> simp
  · rcases (hcos (b * c) x).mp h.symm with h' | h' <;> subst h' <;> simp


structure Frame {S : Type} [Group S] (A : Subgroup S) where
  hN : A.Normal
  a : A
  b : A
  c : A
  hAc : ∀ x y : A, x * y = y * x
  ha1 : a ≠ 1
  ha2 : a * a = 1
  hb1 : b ≠ 1
  hba : b ≠ a
  hb2 : b * b = 1
  hc1 : c ≠ 1
  hca : c ≠ a
  hcb : c ≠ b
  hcab : c ≠ a * b
  ha : ∀ s : S, cj hN s a = a
  hblk : ∀ s : S, cj hN s b = b ∨ cj hN s b = a * b
  hcoords : ∀ x : A, x = 1 ∨ x = a ∨ x = b ∨ x = a * b ∨ x = c ∨ x = a * c ∨ x = b * c ∨
    x = a * (b * c)

section Frame

variable {S : Type} [Group S] {A : Subgroup S}

theorem cj_inv_cancel {A : Subgroup S} (hN : A.Normal) (s : S) (x : A) :
    cj hN s⁻¹ (cj hN s x) = x := by
  rw [← cj_mul_apply, inv_mul_cancel, cj_one]

theorem cj_of_mem' {A : Subgroup S} (hN : A.Normal) (hc : ∀ x y : A, x * y = y * x)
    (z : S) (hz : z ∈ A) (w : A) : cj hN z w = w := by
  apply Subtype.ext
  have h : z * (w : S) = (w : S) * z := congrArg Subtype.val (hc ⟨z, hz⟩ w)
  show z * (w : S) * z⁻¹ = (w : S)
  rw [h, mul_inv_cancel_right]

theorem mem_of_cj_fix {A : Subgroup S} (hC : Subgroup.centralizer (A : Set S) ≤ A)
    (hN : A.Normal) (u : S) (h : ∀ x : A, cj hN u x = x) : u ∈ A := by
  apply hC
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hx : cj hN u ⟨g, hg⟩ = ⟨g, hg⟩ := h ⟨g, hg⟩
  have hx' : u * g * u⁻¹ = g := congrArg Subtype.val hx
  calc g * u = u * g * u⁻¹ * u := by rw [hx', ← hx', ← hx']
    _ = u * g := by group

theorem Frame.ab_ne_one (F : Frame A) : F.a * F.b ≠ 1 := by
  intro h
  have hb : F.b = F.a := by
    calc F.b = F.a * (F.a * F.b) := by rw [← mul_assoc, F.ha2, one_mul]
      _ = F.a * 1 := by rw [h]
      _ = F.a := mul_one F.a
  exact F.hba hb

theorem Frame.ab_ne_b (F : Frame A) : F.a * F.b ≠ F.b := fun h =>
  F.ha1 (mul_right_cancel ((one_mul F.b).trans h.symm)).symm

theorem Frame.cj_fix (F : Frame A) (u : S) (ha : cj F.hN u F.a = F.a)
    (hb : cj F.hN u F.b = F.b) (hc : cj F.hN u F.c = F.c) (x : A) : cj F.hN u x = x := by
  rcases F.hcoords x with h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [cj_mul, cj_one_elem, ha, hb, hc]

theorem Frame.c_form (F : Frame A) (s : S) : cj F.hN s F.c = F.c ∨ cj F.hN s F.c = F.a * F.c ∨
    cj F.hN s F.c = F.b * F.c ∨ cj F.hN s F.c = F.a * (F.b * F.c) := by
  rcases F.hcoords (cj F.hN s F.c) with h | h | h | h | h | h | h | h
  · exfalso
    have key := (cj_inv_cancel F.hN s F.c).symm
    rw [h, cj_one_elem] at key
    exact F.hc1 key
  · exfalso
    have key := (cj_inv_cancel F.hN s F.c).symm
    rw [h, F.ha] at key
    exact F.hca key
  · exfalso
    have key := (cj_inv_cancel F.hN s F.c).symm
    rw [h] at key
    rcases F.hblk s⁻¹ with h1 | h1
    · rw [h1] at key
      exact F.hcb key
    · rw [h1] at key
      exact F.hcab key
  · exfalso
    have key := (cj_inv_cancel F.hN s F.c).symm
    rw [h, cj_mul, F.ha] at key
    rcases F.hblk s⁻¹ with h1 | h1
    · rw [h1] at key
      exact F.hcab key
    · rw [h1, ← mul_assoc, F.ha2, one_mul] at key
      exact F.hcb key
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem Frame.four_ne (F : Frame A) :
    F.c ≠ F.a * F.c ∧ F.c ≠ F.b * F.c ∧ F.c ≠ F.a * (F.b * F.c) ∧ F.a * F.c ≠ F.b * F.c ∧
    F.a * F.c ≠ F.a * (F.b * F.c) ∧ F.b * F.c ≠ F.a * (F.b * F.c) := by
  have d1 : F.c ≠ F.a * F.c := fun h => F.ha1 (mul_right_cancel ((one_mul F.c).trans h)).symm
  have d2 : F.c ≠ F.b * F.c := fun h => F.hb1 (mul_right_cancel ((one_mul F.c).trans h)).symm
  have d3 : F.c ≠ F.a * (F.b * F.c) := fun h =>
    F.ab_ne_one (mul_right_cancel ((one_mul F.c).trans (h.trans (mul_assoc F.a F.b F.c).symm)).symm)
  have d4 : F.a * F.c ≠ F.b * F.c := fun h => F.hba (mul_right_cancel h).symm
  have d5 : F.a * F.c ≠ F.a * (F.b * F.c) := fun h => d2 (mul_left_cancel h)
  have d6 : F.b * F.c ≠ F.a * (F.b * F.c) := fun h =>
    F.ha1 (mul_right_cancel ((one_mul (F.b * F.c)).trans h)).symm
  exact ⟨d1, d2, d3, d4, d5, d6⟩

open Classical in
noncomputable def Frame.code (F : Frame A) (s : S) : Bool × Bool × Bool :=
  (decide (cj F.hN s F.b = F.b),
    decide (cj F.hN s F.c = F.b * F.c ∨ cj F.hN s F.c = F.a * (F.b * F.c)),
    decide (cj F.hN s F.c = F.a * F.c ∨ cj F.hN s F.c = F.a * (F.b * F.c)))

theorem Frame.code_eq (F : Frame A) (s t : S) (h : F.code s = F.code t) :
    cj F.hN s F.b = cj F.hN t F.b ∧ cj F.hN s F.c = cj F.hN t F.c := by
  simp only [Frame.code, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := decide_eq_decide.mp h1
  have e2 := decide_eq_decide.mp h2
  have e3 := decide_eq_decide.mp h3
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := F.four_ne
  have hb : cj F.hN s F.b = cj F.hN t F.b := by
    rcases F.hblk s with hs | hs <;> rcases F.hblk t with ht | ht
    · rw [hs, ht]
    · exact absurd ((e1.mp hs).symm.trans ht).symm F.ab_ne_b
    · exact absurd ((e1.mpr ht).symm.trans hs).symm F.ab_ne_b
    · rw [hs, ht]
  have hc : cj F.hN s F.c = cj F.hN t F.c := by
    have hsym1 := d1.symm
    have hsym2 := d2.symm
    have hsym3 := d3.symm
    have hsym4 := d4.symm
    have hsym5 := d5.symm
    have hsym6 := d6.symm
    rcases F.c_form s with hs | hs | hs | hs <;> rcases F.c_form t with ht | ht | ht | ht <;>
      rw [hs, ht] at e2 e3 ⊢ <;>
      simp only [d1, d2, d3, d4, d5, d6, hsym1, hsym2, hsym3, hsym4, hsym5, hsym6, true_or,
        or_true, or_false, false_or, iff_self, iff_true, true_iff, false_iff, not_true_eq_false,
        eq_self_iff_true, and_self, and_true, true_and] at e2 e3 <;>
      simp_all
  exact ⟨hb, hc⟩

theorem Frame.code_inj_of (F : Frame A) (hC : Subgroup.centralizer (A : Set S) ≤ A)
    (r : S ⧸ A → S) (hr : ∀ q, ((r q : S) : S ⧸ A) = q) :
    Function.Injective (fun q => F.code (r q)) := by
  intro q q' h
  have h' : F.code (r q) = F.code (r q') := h
  obtain ⟨h1, h2⟩ := F.code_eq _ _ h'
  have hub : cj F.hN ((r q)⁻¹ * r q') F.b = F.b := by
    rw [cj_mul_apply, ← h1, cj_inv_cancel]
  have huc : cj F.hN ((r q)⁻¹ * r q') F.c = F.c := by
    rw [cj_mul_apply, ← h2, cj_inv_cancel]
  have hu : (r q)⁻¹ * r q' ∈ A :=
    mem_of_cj_fix hC F.hN _ (fun z => F.cj_fix _ (F.ha _) hub huc z)
  rw [← hr q, ← hr q']
  exact QuotientGroup.eq.mpr hu

theorem Frame.card_quot_le (F : Frame A) (hC : Subgroup.centralizer (A : Set S) ≤ A) :
    Nat.card (S ⧸ A) ≤ 8 := by
  obtain ⟨r, hr⟩ : ∃ r : S ⧸ A → S, ∀ q, ((r q : S) : S ⧸ A) = q :=
    ⟨fun q => Function.surjInv (QuotientGroup.mk_surjective (s := A)) q,
      fun q => Function.surjInv_eq _ q⟩
  have hinj := F.code_inj_of hC r hr
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [← h8]
  exact Nat.card_le_card_of_injective _ hinj

theorem Frame.exists_code (F : Frame A) (hC : Subgroup.centralizer (A : Set S) ≤ A)
    (hcard : Nat.card (S ⧸ A) = 8) (τ : Bool × Bool × Bool) : ∃ s : S, F.code s = τ := by
  obtain ⟨r, hr⟩ : ∃ r : S ⧸ A → S, ∀ q, ((r q : S) : S ⧸ A) = q :=
    ⟨fun q => Function.surjInv (QuotientGroup.mk_surjective (s := A)) q,
      fun q => Function.surjInv_eq _ q⟩
  have hinj := F.code_inj_of hC r hr
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hbij := (Nat.bijective_iff_injective_and_card (fun q => F.code (r q))).mpr
    ⟨hinj, by rw [hcard, h8]⟩
  obtain ⟨q, hq⟩ := hbij.2 τ
  exact ⟨r q, hq⟩

theorem Frame.exists_comm_not_mem (F : Frame A) (hC : Subgroup.centralizer (A : Set S) ≤ A)
    (hcard : Nat.card (S ⧸ A) = 8) : ∃ s t : S, s * t * s⁻¹ * t⁻¹ ∉ A := by
  classical
  obtain ⟨s₁, hs₁⟩ := F.exists_code hC hcard (false, false, false)
  obtain ⟨s₂, hs₂⟩ := F.exists_code hC hcard (true, true, false)
  refine ⟨s₁, s₂, fun hz => ?_⟩
  have h1 : decide (cj F.hN s₁ F.b = F.b) = false := congrArg Prod.fst hs₁
  have h2 : decide (cj F.hN s₁ F.c = F.b * F.c ∨ cj F.hN s₁ F.c = F.a * (F.b * F.c)) = false :=
    congrArg (fun p => p.2.1) hs₁
  have h3 : decide (cj F.hN s₁ F.c = F.a * F.c ∨ cj F.hN s₁ F.c = F.a * (F.b * F.c)) = false :=
    congrArg (fun p => p.2.2) hs₁
  have g1 : cj F.hN s₁ F.b = F.a * F.b := by
    rcases F.hblk s₁ with h | h
    · exact (decide_eq_false_iff_not.mp h1 h).elim
    · exact h
  have g2 := not_or.mp (decide_eq_false_iff_not.mp h2)
  have g3 := not_or.mp (decide_eq_false_iff_not.mp h3)
  have hc1' : cj F.hN s₁ F.c = F.c := by
    rcases F.c_form s₁ with h | h | h | h
    · exact h
    · exact (g3.1 h).elim
    · exact (g2.1 h).elim
    · exact (g2.2 h).elim
  have k2 : decide (cj F.hN s₂ F.c = F.b * F.c ∨ cj F.hN s₂ F.c = F.a * (F.b * F.c)) = true :=
    congrArg (fun p => p.2.1) hs₂
  have k3 : decide (cj F.hN s₂ F.c = F.a * F.c ∨ cj F.hN s₂ F.c = F.a * (F.b * F.c)) = false :=
    congrArg (fun p => p.2.2) hs₂
  have l3 := not_or.mp (decide_eq_false_iff_not.mp k3)
  have hc2' : cj F.hN s₂ F.c = F.b * F.c := by
    rcases decide_eq_true_iff.mp k2 with h | h
    · exact h
    · exact (l3.2 h).elim
  have L : cj F.hN (s₁ * s₂) F.c = F.a * F.b * F.c := by
    rw [cj_mul_apply, hc2', cj_mul, g1, hc1']
  have R : cj F.hN (s₂ * s₁) F.c = F.b * F.c := by
    rw [cj_mul_apply, hc1', hc2']
  have hzs : s₁ * s₂ = (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) * (s₂ * s₁) := by group
  have key : cj F.hN (s₁ * s₂) F.c = cj F.hN (s₂ * s₁) F.c := by
    rw [hzs, cj_mul_apply F.hN (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) (s₂ * s₁) F.c,
      cj_of_mem' F.hN F.hAc _ hz]
  rw [L, R] at key
  exact F.ab_ne_b (mul_right_cancel key)

end Frame

end Structure



theorem exists_frame {S : Type} [Group S] [Finite S] {A : Subgroup S} (hS : IsPGroup 2 S)
    (hN : A.Normal) (hAc : ∀ x y : A, x * y = y * x) (hexp : ∀ x : A, x * x = 1)
    (hcard : Nat.card A = 8) : Nonempty (Frame A) := by
  classical
  letI := conjMulAction hN
  obtain ⟨a, ha1, hafix⟩ := exists_fixed_ne_of_even hS (by rw [hcard]) (1 : A)
    (fun g => cj_one_elem hN g)
  have ha : ∀ s : S, cj hN s a = a := fun s => hafix s
  obtain ⟨b, hb, hblk⟩ := exists_block hS hN hAc hcard a ha1 (hexp a) ha
  have hb1 : b ≠ 1 := by
    intro h
    apply hb
    rw [h]
    exact Subgroup.one_mem _
  have hba : b ≠ a := by
    intro h
    apply hb
    rw [h]
    exact Subgroup.mem_zpowers a
  obtain ⟨c, hc⟩ := exists_third hcard a b
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hc1, hca, hcb, hcab⟩ := hc
  have hcoords := coords_of_card hAc hcard a b c ha1 (hexp a) (hexp b) hb1 hba hc1 hca hcb hcab
  exact ⟨⟨hN, a, b, c, hAc, ha1, hexp a, hb1, hba, hexp b, hc1, hca, hcb, hcab, ha, hblk,
    hcoords⟩⟩

theorem card_eq_ker_mul_range {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H) :
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_eq_card]
  congr 1
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv

theorem comm_subgroup_card_le {S : Type} [Group S] [Finite S] {A : Subgroup S}
    (hS : IsPGroup 2 S) (F : Frame A) (hC : Subgroup.centralizer (A : Set S) ≤ A)
    (hcard : Nat.card A = 8) (U : Subgroup S) (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) :
    Nat.card U ≤ 16 := by
  classical
  haveI : A.Normal := F.hN
  by_contra hlt
  have hlt' : 16 < Nat.card U := not_le.mp hlt
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (hS.to_subgroup U)
  have h32 : 32 ≤ Nat.card U := by
    rw [hm] at hlt' ⊢
    by_contra hcon
    have hcon' : 2 ^ m < 32 := not_le.mp hcon
    have hm5 : m < 5 := by
      by_contra h5
      have h5' : 5 ≤ m := not_lt.mp h5
      have h6 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h5'
      norm_num at h6
      omega
    interval_cases m <;> norm_num at hlt'
  have hidx : Nat.card (S ⧸ A) ≤ 8 := F.card_quot_le hC
  obtain ⟨pr, hpr⟩ : ∃ pr : U →* S ⧸ A, pr = (QuotientGroup.mk' A).comp U.subtype :=
    ⟨_, rfl⟩
  have hsplit : Nat.card U = Nat.card pr.ker * Nat.card pr.range := by
    rw [hpr]
    exact card_eq_ker_mul_range _
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup S, K' = pr.ker.map U.subtype := ⟨_, rfl⟩
  have hK'card : Nat.card K' = Nat.card pr.ker := by
    rw [hK']
    exact Subgroup.card_map_of_injective U.subtype_injective
  have hK'A : K' ≤ A := by
    intro x hx
    rw [hK'] at hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : pr u = 1 := MonoidHom.mem_ker.mp hu
    rw [hpr] at h1
    exact (QuotientGroup.eq_one_iff (u : S)).mp h1
  have hK'U : K' ≤ U := by
    intro x hx
    rw [hK'] at hx
    obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact u.2
  have hdiv : Nat.card K' ∣ 8 := by
    have := Subgroup.card_dvd_of_le hK'A
    rwa [hcard] at this
  have hrS : Nat.card pr.range ≤ Nat.card (S ⧸ A) := Subgroup.card_le_card_group _
  obtain ⟨k, hk⟩ : ∃ k, Nat.card K' = k := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, Nat.card pr.range = r := ⟨_, rfl⟩
  rw [hk] at hdiv
  have hKk : Nat.card pr.ker = k := by rw [← hK'card, hk]
  rw [hKk, hr] at hsplit
  rw [hr] at hrS
  have hr8 : r ≤ 8 := hrS.trans hidx
  have hk8 : k ≤ 8 := Nat.le_of_dvd (by norm_num) hdiv
  have hk4 : 4 ≤ k := by
    by_contra h
    have h3 : k * r ≤ 3 * 8 := Nat.mul_le_mul (by omega) hr8
    omega
  have hk_cases : k = 4 ∨ k = 8 := by
    have hmem : k ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdiv, by norm_num⟩
    have hdv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  rcases hk_cases with rfl | rfl
  ·
    have hr8' : r = 8 := by omega
    have hSA : Nat.card (S ⧸ A) = 8 := by omega
    have hrange : pr.range = ⊤ := Subgroup.eq_top_of_card_eq pr.range (by rw [hr, hr8', hSA])
    obtain ⟨s, t, hst⟩ := F.exists_comm_not_mem hC hSA
    apply hst
    have hsurj : ∀ q : S ⧸ A, ∃ u : U, pr u = q := by
      intro q
      have hq : q ∈ pr.range := by
        rw [hrange]
        exact Subgroup.mem_top q
      exact MonoidHom.mem_range.mp hq
    obtain ⟨u, hu⟩ := hsurj (QuotientGroup.mk s)
    obtain ⟨v, hv⟩ := hsurj (QuotientGroup.mk t)
    have hus : (QuotientGroup.mk (u : S) : S ⧸ A) = QuotientGroup.mk s := by
      rw [← hu, hpr]
      rfl
    have hvt : (QuotientGroup.mk (v : S) : S ⧸ A) = QuotientGroup.mk t := by
      rw [← hv, hpr]
      rfl
    have hc : (u : S) * v = v * u := hU u u.2 v v.2
    have key : (u : S) * v * (u : S)⁻¹ * (v : S)⁻¹ = 1 := by
      rw [hc]
      group
    apply (QuotientGroup.eq_one_iff _).mp
    have e : (QuotientGroup.mk (s * t * s⁻¹ * t⁻¹) : S ⧸ A) =
        QuotientGroup.mk ((u : S) * v * (u : S)⁻¹ * (v : S)⁻¹) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hus, hvt]
    rw [e, key]
    rfl
  ·
    have hK'eq : K' = A := Subgroup.eq_of_le_of_card_ge hK'A (le_of_eq (by rw [hcard, hk]))
    have hAU : A ≤ U := (le_of_eq hK'eq.symm).trans hK'U
    have hUA : U ≤ A := by
      intro u hu
      apply hC
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hU h (hAU hh) u hu
    have := Subgroup.card_le_of_le hUA
    omega

theorem rank_le_four_of_index {S : Type} [Group S] [Finite S] {A : Subgroup S}
    (hS : IsPGroup 2 S) (F : Frame A) (hC : Subgroup.centralizer (A : Set S) ≤ A)
    (hcard : Nat.card A = 8) (hidx : Nat.card (S ⧸ A) = 8) : Group.rank S ≤ 4 := by
  classical
  haveI : A.Normal := F.hN
  obtain ⟨s₁, s₂, hz⟩ := F.exists_comm_not_mem hC hidx
  have hS64 : Nat.card S = 64 := by
    rw [← Subgroup.card_mul_index A, hcard, Subgroup.index_eq_card, hidx]
  obtain ⟨s, hs⟩ : ∃ s : S, s ∉ A := by
    by_contra hcon
    have hall : ∀ s : S, s ∈ A := fun s => Classical.byContradiction fun h => hcon ⟨s, h⟩
    have htop : A = ⊤ := eq_top_iff.mpr fun s _ => hall s
    have h1 := Subgroup.card_top (G := S)
    rw [← htop, hcard] at h1
    omega
  obtain ⟨a'', ha''A, hsa⟩ : ∃ a'' ∈ A, s * a'' ≠ a'' * s := by
    by_contra hcon
    have hcomm : ∀ h ∈ A, s * h = h * s := fun h hh =>
      Classical.byContradiction fun hne => hcon ⟨h, hh, hne⟩
    exact hs (hC (Subgroup.mem_centralizer_iff.mpr fun h hh => (hcomm h hh).symm))
  obtain ⟨x, hxdef⟩ : ∃ x : S, x = s * a'' * s⁻¹ * a''⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : S, z = s₁ * s₂ * s₁⁻¹ * s₂⁻¹ := ⟨_, rfl⟩
  have hxΦ : x ∈ frattini S := by
    rw [hxdef]
    exact comm_mem_frattini hS s a''
  have hzΦ : z ∈ frattini S := by
    rw [hzdef]
    exact comm_mem_frattini hS s₁ s₂
  have hxA : x ∈ A := by
    rw [hxdef]
    exact A.mul_mem (F.hN.conj_mem a'' ha''A s) (A.inv_mem ha''A)
  have hx1 : x ≠ 1 := by
    intro h
    apply hsa
    calc s * a'' = (s * a'' * s⁻¹ * a''⁻¹) * (a'' * s) := by group
      _ = a'' * s := by rw [← hxdef, h, one_mul]
  have hzA : z ∉ A := by
    rw [hzdef]
    exact hz
  have hz1 : z ≠ 1 := fun h => hzA (h ▸ A.one_mem)
  have hzxA : z * x ∉ A := by
    intro h
    apply hzA
    have h2 := A.mul_mem h (A.inv_mem hxA)
    rwa [mul_inv_cancel_right] at h2
  have hzx1 : z * x ≠ 1 := fun h => hzxA (h ▸ A.one_mem)
  have hzxΦ : z * x ∈ frattini S := Subgroup.mul_mem _ hzΦ hxΦ
  have hxz : x ≠ z := fun h => hzA (h ▸ hxA)
  have hxzx : x ≠ z * x := fun h => hz1 (mul_right_cancel ((one_mul x).trans h)).symm
  have hzzx : z ≠ z * x := fun h => hx1 (mul_left_cancel ((mul_one z).trans h)).symm
  have e1 : (1 : S) ∉ ({x, z, z * x} : Set S) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1.symm, hz1.symm, hzx1.symm⟩
  have e2 : x ∉ ({z, z * x} : Set S) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxz, hxzx⟩
  have hT : ({1, x, z, z * x} : Set S).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem e1, Set.ncard_insert_of_notMem e2, Set.ncard_pair hzzx]
  have hsub : ({1, x, z, z * x} : Set S) ⊆ (frattini S : Set S) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxΦ
    · exact hzΦ
    · exact hzxΦ
  have hcardΦ : 4 ≤ Nat.card (frattini S) := by
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hT] at hle
    rw [← Nat.card_coe_set_eq] at hle
    exact hle
  apply rank_le_of_card_le_mul_frattini hS 4
  rw [hS64]
  norm_num
  omega

theorem harada_lemma4 {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {A : Subgroup S}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hC : Subgroup.centralizer (A : Set S) ≤ A) (hN : A.Normal) : GenLE4 S := by
  classical
  have hAc : ∀ x y : A, x * y = y * x := fun x y => hA.1.is_comm.comm x y
  have hexp : ∀ x : A, x * x = 1 := fun x => Subtype.ext (by
    show (x : S) * x = 1
    rw [← pow_two]
    exact hA.2 x x.2)
  obtain ⟨F⟩ := exists_frame hS hN hAc hexp hA8
  have hidx : Nat.card (S ⧸ A) ≤ 8 := F.card_quot_le hC
  have hS_le : Nat.card S ≤ 64 := by
    have h := Subgroup.card_mul_index A
    rw [hA8, Subgroup.index_eq_card] at h
    omega
  have hrank : ∀ U : Subgroup S, Group.rank U ≤ 4 := by
    intro U
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (hS.to_subgroup U)
    have hUle : Nat.card U ≤ Nat.card S := Subgroup.card_le_card_group U
    by_cases hU32 : Nat.card U ≤ 32
    · apply rank_le_of_card_le_mul_frattini (hS.to_subgroup U) 4
      by_cases hΦ : Nat.card (frattini U) = 1
      · have hbot : frattini U = ⊥ := (Subgroup.eq_bot_iff_card _).mpr hΦ
        have hcomm := commute_sq_of_frattini_bot (hS.to_subgroup U) hbot
        have hcommU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
          congrArg Subtype.val (hcomm.1 ⟨x, hx⟩ ⟨y, hy⟩)
        have h16 := comm_subgroup_card_le hS F hC hA8 U hcommU
        rw [hΦ]
        norm_num
        omega
      · have hpos : 0 < Nat.card (frattini U) := Nat.card_pos
        have h2 : 2 ≤ Nat.card (frattini U) := by omega
        have h4 : 2 ^ 4 * 2 ≤ 2 ^ 4 * Nat.card (frattini U) := Nat.mul_le_mul_left _ h2
        norm_num at h4 ⊢
        omega
    ·
      have hU64 : Nat.card U = 64 := by
        have hm6 : m ≤ 6 := by
          by_contra h
          have h7 : 128 ≤ 2 ^ m := by
            calc (128 : ℕ) = 2 ^ 7 := by norm_num
              _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hm5 : 5 < m := by
          by_contra h
          have h5 : 2 ^ m ≤ 32 := by
            calc 2 ^ m ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
              _ = 32 := by norm_num
          omega
        have hm6eq : m = 6 := by omega
        rw [hm, hm6eq]
        norm_num
      have hS64 : Nat.card S = 64 := by omega
      have htop : U = ⊤ := Subgroup.eq_top_of_card_eq U (by rw [hU64, hS64])
      subst htop
      rw [Group.rank_congr Subgroup.topEquiv]
      have hidx8 : Nat.card (S ⧸ A) = 8 := by
        have h := Subgroup.card_mul_index A
        rw [hA8, hS64] at h
        rw [← Subgroup.index_eq_card]
        omega
      exact rank_le_four_of_index hS F hC hA8 hidx8
  intro U
  obtain ⟨Y, hYcard, hYcl⟩ := Group.rank_spec ↥U
  refine ⟨Y.map (Function.Embedding.subtype (fun x : S => x ∈ U)), ?_, ?_⟩
  · rw [Finset.card_map, hYcard]
    exact hrank U
  · rw [Finset.coe_map]
    calc Subgroup.closure ((Function.Embedding.subtype (fun x : S => x ∈ U)) '' (Y : Set U))
        = Subgroup.closure (U.subtype '' (Y : Set U)) := rfl
      _ = Subgroup.map U.subtype (Subgroup.closure (Y : Set U)) :=
          (MonoidHom.map_closure _ _).symm
      _ = Subgroup.map U.subtype ⊤ := by rw [hYcl]
      _ = U := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.EvenSporadicStandard.Fin76b
