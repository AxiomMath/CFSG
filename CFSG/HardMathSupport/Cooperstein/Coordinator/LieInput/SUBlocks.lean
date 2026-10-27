module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUCent
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUEmbed

public section

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.AGLEmbedding.LieOut
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.RootSystem CFSG.LieType.BorelTits
  CFSG.AGLEmbedding.LeviBlock

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section MemLevi

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}

theorem coord_eq_zero_of_cum {γ : Fin (n / 2) → ℤ} {j : Fin (n / 2)}
    (h : cumE (Unitary.toStd n γ) j = 0) : γ j = 0 := by
  rw [cumE_toStd] at h
  split_ifs at h <;> omega

theorem rootHom_mem_leviM (hn : 2 ≤ n) {i k : Fin n} (hik : i ≠ k) (hi : i ≠ Fin.rev i)
    (hk : k ≠ Fin.rev k) (hki : k ≠ Fin.rev i) {J : Set (Fin (n / 2))}
    (hsupp : ∀ j, j ∉ J → phi j i = phi j k) (c : Multiplicative F) :
    rootHom (unitaryInvolution F p f) (unitaryInvolution_involutive hF) hik hi hk c ∈
      leviM (rootDatum hF n) J := by
  obtain ⟨γ, hγ⟩ := exists_gamma_toStd (n := n) (weight n i - weight n k) (by
    intro l hn' _
    rw [cumE_sub, cumE_weight, cumE_weight]
    rcases phi_last_odd hn' ‹_› i with h1 | h1 <;> rcases phi_last_odd hn' ‹_› k with h2 | h2 <;>
      rw [h1, h2] <;> norm_num)
  have hw : weight n i - weight n k = Unitary.toStd n γ := hγ.symm
  have hroot := mem_roots_of_weight_sub hik hw
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hct := isCTGroupDatum hF n hn ζ hζ
  have hs : ∀ j, j ∉ J → γ j = 0 := by
    intro j hj
    apply coord_eq_zero_of_cum
    rw [hγ, cumE_sub, cumE_weight, cumE_weight, hsupp j hj, sub_self]
  exact rootGroup_le_leviM (D := rootDatum hF n) hct hroot hs (rootHom_mem _ hik hi hk hki hw c)


theorem longRootHom_mem_leviM (hn : 2 ≤ n) {i : Fin n} (hi : i ≠ Fin.rev i) {J : Set (Fin (n / 2))}
    (hsupp : ∀ j, j ∉ J → phi j i = 0) (c : Multiplicative (traceZero (unitaryInvolution F p f))) :
    longRootHom (unitaryInvolution F p f) hi c ∈ leviM (rootDatum hF n) J := by
  have h2 : (2 : ℕ) • weight n i = weight n i + weight n i := two_nsmul _
  obtain ⟨γ, hγ⟩ := exists_gamma_toStd (n := n) (weight n i + weight n i) (by
    intro l hn' _
    rw [cumE_add, cumE_weight]
    rcases phi_last_odd hn' ‹_› i with h1 | h1 <;> rw [h1] <;> norm_num)
  have hw : 2 • weight n i = Unitary.toStd n γ := by rw [h2, hγ]
  have hroot : γ ∈ roots (isFiniteType_cartan n) (divisible n) := by
    rw [roots_eq]; exact Or.inr (Or.inl ⟨i, hi, hw.symm⟩)
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hct := isCTGroupDatum hF n hn ζ hζ
  have hs : ∀ j, j ∉ J → γ j = 0 := by
    intro j hj
    apply coord_eq_zero_of_cum
    rw [hγ, cumE_add, cumE_weight, hsupp j hj]; norm_num
  exact rootGroup_le_leviM (D := rootDatum hF n) hct hroot hs (longRootHom_mem _ hi hw c)

theorem heisenberg_mem_leviM (hn : 2 ≤ n) {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (hodd : ¬ Even n) {J : Set (Fin (n / 2))}
    (hsupp : ∀ j, j ∉ J → phi j i = 0)
    {x : SU (unitaryInvolution F p f) n}
    (hx : x ∈ heisenbergSubgroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) hi hik hk) :
    x ∈ leviM (rootDatum hF n) J := by
  obtain ⟨γ, hγ⟩ := exists_gamma_toStd (n := n) (weight n i) (fun l hn' _ => absurd hn' hodd)
  have hw : weight n i = Unitary.toStd n γ := hγ.symm
  have hroot : γ ∈ roots (isFiniteType_cartan n) (divisible n) := by
    rw [roots_eq]; exact Or.inr (Or.inr ⟨hodd, i, hi, hw.symm⟩)
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hct := isCTGroupDatum hF n hn ζ hζ
  have hs : ∀ j, j ∉ J → γ j = 0 := by
    intro j hj
    apply coord_eq_zero_of_cum
    rw [hγ, cumE_weight, hsupp j hj]
  exact rootGroup_le_leviM (D := rootDatum hF n) hct hroot hs (heisenberg_le _ hi hik hk hw hx)

end MemLevi

theorem phi_lowIdx {n : ℕ} (j a : Fin (n / 2)) :
    phi j (lowIdx (n := n) a) = if a.val ≤ j.val then 1 else 0 := by
  have hj := j.isLt
  have ha := a.isLt
  simp only [phi, val_lowIdx]
  split_ifs <;> omega

theorem phi_rev_lowIdx {n : ℕ} (j a : Fin (n / 2)) :
    phi j (Fin.rev (lowIdx (n := n) a)) = - (if a.val ≤ j.val then 1 else 0) := by
  have hj := j.isLt
  have ha := a.isLt
  simp only [phi, Fin.val_rev, val_lowIdx]
  split_ifs <;> omega

theorem phi_mid {n : ℕ} (j : Fin (n / 2)) {x : Fin n} (hx : Fin.rev x = x) : phi j x = 0 := by
  have hj := j.isLt
  have := congrArg Fin.val hx
  simp only [Fin.val_rev] at this
  simp only [phi]
  split_ifs <;> omega


section Positions

variable {n : ℕ}

@[expose] def ePos (S : Finset (Fin (n / 2))) : Finset (Fin n) :=
  S.image lowIdx ∪ S.image (Fin.rev ∘ lowIdx) ∪ Finset.univ.filter (fun x => Fin.rev x = x)

theorem mem_ePos {S : Finset (Fin (n / 2))} {x : Fin n} :
    x ∈ ePos S ↔ (∃ a ∈ S, x = lowIdx a ∨ x = Fin.rev (lowIdx a)) ∨ Fin.rev x = x := by
  simp only [ePos, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Function.comp_apply]
  constructor
  · rintro ((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | h)
    · exact Or.inl ⟨a, ha, Or.inl rfl⟩
    · exact Or.inl ⟨a, ha, Or.inr rfl⟩
    · exact Or.inr h
  · rintro (⟨a, ha, rfl | rfl⟩ | h)
    · exact Or.inl (Or.inl ⟨a, ha, rfl⟩)
    · exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
    · exact Or.inr h

theorem rev_mem_ePos {S : Finset (Fin (n / 2))} {x : Fin n} : Fin.rev x ∈ ePos S ↔ x ∈ ePos S := by
  rw [mem_ePos, mem_ePos]
  constructor
  · rintro (⟨a, ha, h | h⟩ | h)
    · exact Or.inl ⟨a, ha, Or.inr (by rw [← h, Fin.rev_rev])⟩
    · exact Or.inl ⟨a, ha, Or.inl (Fin.rev_injective h)⟩
    · exact Or.inr (by rw [Fin.rev_rev] at h; exact h.symm)
  · rintro (⟨a, ha, h | h⟩ | h)
    · exact Or.inl ⟨a, ha, Or.inr (by rw [h])⟩
    · exact Or.inl ⟨a, ha, Or.inl (by rw [h, Fin.rev_rev])⟩
    · exact Or.inr (by rw [Fin.rev_rev]; exact h.symm)

@[expose] noncomputable def eTau (S : Finset (Fin (n / 2))) : Fin (ePos S).card → Fin n :=
  fun i => (ePos S).orderEmbOfFin rfl i

theorem eTau_strictMono (S : Finset (Fin (n / 2))) : StrictMono (eTau S) :=
  ((ePos S).orderEmbOfFin rfl).strictMono

theorem eTau_injective (S : Finset (Fin (n / 2))) : Function.Injective (eTau S) :=
  (eTau_strictMono S).injective

theorem eTau_mem (S : Finset (Fin (n / 2))) (i : Fin (ePos S).card) : eTau S i ∈ ePos S :=
  Finset.orderEmbOfFin_mem _ _ _

theorem exists_eTau {S : Finset (Fin (n / 2))} {x : Fin n} (hx : x ∈ ePos S) :
    ∃ i, eTau S i = x := by
  have := Finset.range_orderEmbOfFin (ePos S) rfl
  have hx' : x ∈ Set.range ((ePos S).orderEmbOfFin rfl) := by rw [this]; exact hx
  exact hx'

theorem eTau_rev (S : Finset (Fin (n / 2))) (i : Fin (ePos S).card) :
    eTau S (Fin.rev i) = Fin.rev (eTau S i) := by
  have hmono : StrictMono (fun i : Fin (ePos S).card => Fin.rev (eTau S (Fin.rev i))) := by
    intro a b hab
    have := eTau_strictMono S (Fin.rev_lt_rev.mpr hab)
    exact Fin.rev_lt_rev.mpr this
  have huniq := Finset.orderEmbOfFin_unique (s := ePos S) rfl
    (f := fun i : Fin (ePos S).card => Fin.rev (eTau S (Fin.rev i)))
    (fun i => rev_mem_ePos.mpr (eTau_mem S _)) hmono
  have h1 : (fun i : Fin (ePos S).card => Fin.rev (eTau S (Fin.rev i))) = eTau S := by
    rw [huniq]; rfl
  have h2 := congrFun h1 (Fin.rev i)
  simp only [Fin.rev_rev] at h2
  rw [← h2]


theorem card_mid (n : ℕ) :
    (Finset.univ.filter (fun x : Fin n => Fin.rev x = x)).card = if Even n then 0 else 1 := by
  split_ifs with he
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have := congrArg Fin.val hx
    simp only [Fin.val_rev] at this
    obtain ⟨r, hr⟩ := he
    have := x.isLt
    omega
  · rw [Finset.card_eq_one]
    have hodd : n % 2 = 1 := by
      rcases Nat.even_or_odd n with h | h
      · exact absurd h he
      · exact Nat.odd_iff.mp h
    refine ⟨⟨n / 2, by omega⟩, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_rev] at this
      exact Fin.ext (by simp only; omega)
    · rintro rfl
      exact Fin.ext (by simp only [Fin.val_rev]; omega)

theorem ePos_card (S : Finset (Fin (n / 2))) :
    (ePos S).card = 2 * S.card + (if Even n then 0 else 1) := by
  unfold ePos
  have hA : (S.image (lowIdx (n := n))).card = S.card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa [val_lowIdx] using congrArg Fin.val h))
  have hB : (S.image (Fin.rev ∘ lowIdx (n := n))).card = S.card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by
      have := Fin.rev_injective h
      simpa [val_lowIdx] using congrArg Fin.val this))
  have hAB : Disjoint (S.image (lowIdx (n := n))) (S.image (Fin.rev ∘ lowIdx (n := n))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image, Function.comp_apply] at hx hx'
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hx'
    exact lowIdx_ne_rev a b hb.symm
  have hC : Disjoint (S.image (lowIdx (n := n)) ∪ S.image (Fin.rev ∘ lowIdx (n := n)))
      (Finset.univ.filter (fun x : Fin n => Fin.rev x = x)) := by
    rw [Finset.disjoint_right]
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_union, Finset.mem_image, Function.comp_apply, not_or, not_exists, not_and]
    constructor
    · intro a _ h
      exact lowIdx_ne_rev a a (by rw [h, hx])
    · intro a _ h
      apply lowIdx_ne_rev a a
      rw [← h] at hx
      rw [Fin.rev_rev] at hx
      exact hx
  rw [Finset.card_union_of_disjoint hC, Finset.card_union_of_disjoint hAB, hA, hB, card_mid]
  ring

end Positions


section Groups

open CFSG.AGLEmbeddingD2.ParabLevi

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

@[expose] def aIdx (S : Finset (Fin (n / 2))) : ↥S → Fin n := fun s => lowIdx s.1

theorem aIdx_injective (S : Finset (Fin (n / 2))) : Function.Injective (aIdx S) :=
  fun a b h => Subtype.ext (Fin.ext (by simpa [aIdx, val_lowIdx] using congrArg Fin.val h))

theorem aIdx_disj (S : Finset (Fin (n / 2))) (i j : ↥S) : aIdx S i ≠ Fin.rev (aIdx S j) :=
  lowIdx_ne_rev _ _

@[expose] noncomputable def GAu (S : Finset (Fin (n / 2))) : Subgroup (SU (unitaryInvolution F 2 f) n) :=
  (levSU (σ := unitaryInvolution F 2 f) (aIdx_injective S) (aIdx_disj S)
    (unitaryInvolution_involutive hF)).range

@[expose] noncomputable def GEu (_hF : Nat.card F = (2 ^ f) ^ 2) (S : Finset (Fin (n / 2))) :
    Subgroup (SU (unitaryInvolution F 2 f) n) :=
  (suEmbed (unitaryInvolution F 2 f) (eTau_injective S) (eTau_rev S)).range

theorem su_exists_norm_eq (hF : Nat.card F = (2 ^ f) ^ 2) {x : F}
    (hx : unitaryInvolution F 2 f x = x) : ∃ a, unitaryInvolution F 2 f a * a = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  · exact CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hF hx h0

theorem phi_eq_zero_of_ePos {S : Finset (Fin (n / 2))} {j : Fin (n / 2)}
    (hj : ∀ a ∈ S, j.val < a.val) {x : Fin n} (hx : x ∈ ePos S) : phi j x = 0 := by
  rcases mem_ePos.mp hx with ⟨a, ha, rfl | rfl⟩ | hmid
  · rw [phi_lowIdx, if_neg (by have := hj a ha; omega)]
  · rw [phi_rev_lowIdx, if_neg (by have := hj a ha; omega)]; simp
  · exact phi_mid j hmid


theorem GEu_le_leviM (hn : 2 ≤ n) {S : Finset (Fin (n / 2))} (hS : S.Nonempty)
    {J : Set (Fin (n / 2))} (hJ : ∀ j, j ∉ J → ∀ a ∈ S, j.val < a.val) :
    GEu hF S ≤ leviM (rootDatum hF n) J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := unitaryInvolution_involutive (K := F) (p := 2) (f := f) hF
  have hcard : 2 ≤ (ePos S).card := by
    rw [ePos_card]
    obtain ⟨a, ha⟩ := hS
    have := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  have hτ := eTau_injective S
  have hr := eTau_rev S
  have hsupp : ∀ j, j ∉ J → ∀ i : Fin (ePos S).card, phi j (eTau S i) = 0 := fun j hj i =>
    phi_eq_zero_of_ePos (hJ j hj) (eTau_mem S i)
  have htop : ((leviM (rootDatum hF n) J).comap
      (suEmbed (unitaryInvolution F 2 f) hτ hr)) = ⊤ := by
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
    refine eq_top_of_rootElements_le hσ ⟨ζ, hζ, ζ.2⟩
      (fun _ hx => exists_add_unitaryInvolution_eq hF hx) (fun _ hx => su_exists_norm_eq hF hx) hcard _
      ?_ ?_ ?_
    · intro i j hij hi hj hji c
      rw [Subgroup.mem_comap]
      rw [suEmbed_rootHom hσ hτ hr]
      refine rootHom_mem_leviM hF hn _ _ _ ?_ ?_ _
      · intro e
        apply hji
        apply hτ
        rw [hr, e]
      · intro j' hj'
        rw [hsupp j' hj' i, hsupp j' hj' j]
    · intro i hi c
      rw [Subgroup.mem_comap]
      rw [suEmbed_longRootHom hτ hr]
      exact longRootHom_mem_leviM hF hn _ (fun j' hj' => hsupp j' hj' i) c
    · intro i k hi hik hk x hx
      rw [Subgroup.mem_comap]
      have hk' : Fin.rev (eTau S k) = eTau S k := by rw [← hr, hk]
      have hodd : ¬ Even n := by
        rintro ⟨r, hr'⟩
        have := congrArg Fin.val hk'
        simp only [Fin.val_rev] at this
        have := (eTau S k).isLt
        omega
      exact heisenberg_mem_leviM hF hn _ _ hk' hodd (fun j' hj' => hsupp j' hj' i)
        (suEmbed_mem_heisenbergSubgroup hσ hτ hr hi hik hk hx)
  rintro _ ⟨g, rfl⟩
  have : g ∈ (leviM (rootDatum hF n) J).comap (suEmbed (unitaryInvolution F 2 f) hτ hr) := by
    rw [htop]; trivial
  exact this


theorem GAu_le_leviM (hn : 2 ≤ n) {S : Finset (Fin (n / 2))} {J : Set (Fin (n / 2))}
    (hJ : ∀ j, j ∉ J → ∀ a ∈ S, ∀ b ∈ S, (a.val ≤ j.val ↔ b.val ≤ j.val)) :
    GAu hF S ≤ leviM (rootDatum hF n) J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := unitaryInvolution_involutive (K := F) (p := 2) (f := f) hF
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct ↥S F → Matrix.SpecialLinearGroup ↥S F)) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top _
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨u, v, huv, c⟩ := t
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      levSU_transvection hσ (aIdx_injective S) (aIdx_disj S) huv]
    refine rootHom_mem_leviM hF hn _ _ _ (lowIdx_ne_rev _ _) ?_ _
    intro j hj
    show phi j (lowIdx u.1) = phi j (lowIdx v.1)
    rw [phi_lowIdx, phi_lowIdx]
    have := hJ j hj u.1 u.2 v.1 v.2
    simp only [this]
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

end Groups


section Support

variable {F : Type} [Field F] {σ : F ≃+* F} {n' n : ℕ} {τ : Fin n' → Fin n}
  (hτ : Function.Injective τ) (hr : ∀ i, τ (Fin.rev i) = Fin.rev (τ i))

include hr in
theorem antidiag_mul_extendMat (M : Matrix (Fin n') (Fin n') F) :
    (antidiag n : Matrix (Fin n) (Fin n) F) * extendMat hτ M =
      extendMat hτ (M.submatrix Fin.rev Fin.rev) * antidiag n := by
  have := extendMat_mul_antidiag hτ hr (M.submatrix Fin.rev Fin.rev)
  rw [Matrix.submatrix_submatrix] at this
  simp only [Function.comp_def, Fin.rev_rev] at this
  exact this.symm

include hr in
theorem mem_range_suEmbed_of_support (hσ : ∀ c, σ (σ c) = c) {x : SU σ n}
    (hx : ∀ u v, ¬ (u ∈ Set.range τ ∧ v ∈ Set.range τ) →
      mat σ n x u v = (1 : Matrix (Fin n) (Fin n) F) u v) :
    x ∈ (suEmbed σ hτ hr).range := by
  set A := mat σ n x with hA
  set R : Matrix (Fin n') (Fin n') F := A.submatrix τ τ with hR
  have hAR : A = extendMat hτ R := by
    ext u v
    by_cases h : u ∈ Set.range τ ∧ v ∈ Set.range τ
    · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
      rw [extendMat_apply_map]
      rfl
    · have h' : u ∉ Set.range τ ∨ v ∉ Set.range τ := by
        by_contra hc
        push Not at hc
        exact h hc
      rw [extendMat_apply_of_not_mem hτ R h', hx u v h]
  have hdet : R.det = 1 := by
    have := x.2.1
    rw [← mat_apply, ← hA, hAR, det_extendMat] at this
    exact this
  have hunit : conjTr σ R * antidiag n' * R = antidiag n' := by
    have h1 := x.2.2
    rw [← mat_apply, ← hA, hAR, conjTr_extendMat hτ R, Matrix.mul_assoc,
      antidiag_mul_extendMat hτ hr R, ← Matrix.mul_assoc, ← extendMat_mul] at h1
    have h2 : extendMat hτ ((R.map σ)ᵀ * R.submatrix Fin.rev Fin.rev) = 1 := by
      have := congrArg (fun P => P * (antidiag n : Matrix (Fin n) (Fin n) F)) h1
      simp only [Matrix.mul_assoc, antidiag_mul_self, Matrix.mul_one] at this
      exact this
    have h3 : (R.map σ)ᵀ * R.submatrix Fin.rev Fin.rev = 1 := by
      have := congrArg (fun P => P.submatrix τ τ) h2
      simp only [submatrix_extendMat] at this
      rw [this]
      exact Matrix.submatrix_one _ hτ
    rw [← antidiag_conj R] at h3
    have := congrArg (fun P => P * (antidiag n' : Matrix (Fin n') (Fin n') F)) h3
    simp only [Matrix.mul_assoc, antidiag_mul_self, Matrix.mul_one, Matrix.one_mul] at this
    show (R.map σ)ᵀ * antidiag n' * R = antidiag n'
    rw [Matrix.mul_assoc]
    exact this
  have hunit' : IsUnit R.det := by rw [hdet]; exact isUnit_one
  let M : SU σ n' :=
    ⟨⟨R, R⁻¹, Matrix.mul_nonsing_inv _ hunit', Matrix.nonsing_inv_mul _ hunit'⟩, hdet, hunit⟩
  refine ⟨M, ?_⟩
  apply mat_injective
  rw [mat_suEmbed]
  exact hAR.symm


theorem mem_range_eTau_iff {n : ℕ} (S : Finset (Fin (n / 2))) (s : Fin n) :
    s ∈ Set.range (eTau S) ↔ s ∈ ePos S :=
  ⟨fun ⟨i, hi⟩ => hi ▸ eTau_mem S i, fun h => exists_eTau h⟩

theorem blkShort_ne_zero_mem_ePos {n : ℕ} {S : Finset (Fin (n / 2))} {k : Fin (n / 2)}
    (hk : k.val + 1 < n / 2) (h1 : k ∈ S) (h2 : (⟨k.val + 1, hk⟩ : Fin (n / 2)) ∈ S) {u : Fin n}
    (hu : blkShort k hk u ≠ 0) : u ∈ ePos S := by
  unfold blkShort at hu
  rw [mem_ePos]
  split_ifs at hu with c1 c2
  · rcases c1 with rfl | rfl
    · exact Or.inl ⟨k, h1, Or.inl rfl⟩
    · exact Or.inl ⟨_, h2, Or.inl rfl⟩
  · rcases c2 with rfl | rfl
    · exact Or.inl ⟨k, h1, Or.inr rfl⟩
    · exact Or.inl ⟨_, h2, Or.inr rfl⟩
  · exact absurd rfl hu

theorem blkLast_ne_zero_mem_ePos {n : ℕ} {S : Finset (Fin (n / 2))} {k : Fin (n / 2)}
    (h1 : k ∈ S) {u : Fin n} (hu : blkLast k u ≠ 0) : u ∈ ePos S := by
  have : ¬ ¬ (u = lowIdx k ∨ u = Fin.rev (lowIdx k) ∨ Fin.rev u = u) := fun h =>
    hu ((blkLast_eq_zero_iff u).2 h)
  push Not at this
  rw [mem_ePos]
  rcases this with rfl | rfl | h
  · exact Or.inl ⟨k, h1, Or.inl rfl⟩
  · exact Or.inl ⟨k, h1, Or.inr rfl⟩
  · exact Or.inr h

end Support

section RankOneLe

open CFSG.LieType.CurtisTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

theorem rankOne_le_GEu {S : Finset (Fin (n / 2))} {i : Fin (n / 2)} (hi : i ∈ S)
    (hnext : ∀ h : i.val + 1 < n / 2, (⟨i.val + 1, h⟩ : Fin (n / 2)) ∈ S) :
    rankOne (rootDatum hF n).rootGroup i ≤ GEu hF S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := unitaryInvolution_involutive (K := F) (p := 2) (f := f) hF
  intro x hx
  refine mem_range_suEmbed_of_support (eTau_injective S) (eTau_rev S) hσ ?_
  intro u v huv
  by_cases hs : i.val + 1 < n / 2
  · have hblk := (isBlk_short_of_mem (hσ := hσ) hs hx).1
    apply hblk u v
    rintro ⟨h1, h2⟩
    apply huv
    have hu : u ∈ ePos S := blkShort_ne_zero_mem_ePos hs hi (hnext hs) h2
    have hv : v ∈ ePos S := blkShort_ne_zero_mem_ePos hs hi (hnext hs) (h1 ▸ h2)
    exact ⟨(mem_range_eTau_iff S u).2 hu, (mem_range_eTau_iff S v).2 hv⟩
  · have hblk := isBlk_last_of_mem (hσ := hσ) hs hx
    apply hblk u v
    rintro ⟨h1, h2⟩
    apply huv
    have hu : u ∈ ePos S := blkLast_ne_zero_mem_ePos hi h2
    have hv : v ∈ ePos S := blkLast_ne_zero_mem_ePos hi (h1 ▸ h2)
    exact ⟨(mem_range_eTau_iff S u).2 hu, (mem_range_eTau_iff S v).2 hv⟩


theorem rankOne_le_GAu {S : Finset (Fin (n / 2))} {k : Fin (n / 2)} (hk : k.val + 1 < n / 2)
    (h1 : k ∈ S) (h2 : (⟨k.val + 1, hk⟩ : Fin (n / 2)) ∈ S) :
    rankOne (rootDatum hF n).rootGroup k ≤ GAu hF S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := unitaryInvolution_involutive (K := F) (p := 2) (f := f) hF
  set p : Fin n := lowIdx k with hp
  set q : Fin n := lowIdx (n := n) ⟨k.val + 1, hk⟩ with hq
  have hpq : p ≠ q := lowIdx_ne_succ hk
  have hpr : p ≠ Fin.rev p := lowIdx_ne_rev k k
  have hqr : q ≠ Fin.rev q := lowIdx_ne_rev _ _
  have hqp : q ≠ Fin.rev p := lowIdx_ne_rev _ _
  have hpq' : p ≠ Fin.rev q := lowIdx_ne_rev _ _
  let u : ↥S := ⟨k, h1⟩
  let v : ↥S := ⟨⟨k.val + 1, hk⟩, h2⟩
  have huv : u ≠ v := fun e => hpq (by
    have := congrArg (fun z : ↥S => (lowIdx (n := n) z.1)) e
    exact this)
  refine sup_le ?_ ?_
  · intro x hx
    set c := mat (unitaryInvolution F 2 f) n x p q with hc
    let y := rootHom (unitaryInvolution F 2 f) hσ hpq hpr hqr (Multiplicative.ofAdd c)
    have hy : y ∈ rootGroup (unitaryInvolution F 2 f) hσ n (Pi.single k 1) :=
      rootHom_mem hσ hpq hpr hqr hqp (toStd_short hk).symm _
    have hxy : x = y := by
      refine eq_of_toBlock_short hk (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_left hy) ?_
      rw [toBlock_of_mem_pos hk hx, toBlock_of_mem_pos hk hy]
      congr 1
      rw [mat_rootHom hσ hpq hpr hqr, rootMatrix_apply_pq hpq hqp]
    rw [hxy]
    have := levSU_transvection hσ (aIdx_injective S) (aIdx_disj S) huv c
    exact ⟨_, this⟩
  · intro x hx
    set c := mat (unitaryInvolution F 2 f) n x q p with hc
    let y := rootHom (unitaryInvolution F 2 f) hσ hpq.symm hqr hpr (Multiplicative.ofAdd c)
    have hy : y ∈ rootGroup (unitaryInvolution F 2 f) hσ n (-Pi.single k 1) :=
      rootHom_mem hσ hpq.symm hqr hpr hpq' (toStd_short_neg hk).symm _
    have hxy : x = y := by
      refine eq_of_toBlock_short hk (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_right hy) ?_
      rw [toBlock_of_mem_neg hk hx, toBlock_of_mem_neg hk hy]
      congr 1
      rw [mat_rootHom hσ hpq.symm hqr hpr, rootMatrix_apply_pq hpq.symm hpq']
    rw [hxy]
    have := levSU_transvection hσ (aIdx_injective S) (aIdx_disj S) huv.symm c
    exact ⟨_, this⟩

end RankOneLe


section GbU

open Classical CFSG.LieType.CurtisTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ} {I : Set (Fin (n / 2))}

@[expose] noncomputable def GbU (B : Finset (Fin (n / 2 + 1))) :
    Subgroup (SU (unitaryInvolution F 2 f) n) :=
  if Fin.last (n / 2) ∈ B then GEu hF (coordsOf B) else GAu hF (coordsOf B)

theorem GbU_eq (hn : 2 ≤ n) {B : Finset (Fin (n / 2 + 1))} {p : Fin (n / 2 + 1)}
    (hB : B = blkSet I p) (hne : (nodesOf B).Nonempty) :
    GbU hF B = leviM (rootDatum hF n) (nodesOf B) := by
  unfold GbU
  split_ifs with hl
  · obtain ⟨i0, hi0⟩ := hne
    have hS : (coordsOf B).Nonempty := ⟨i0, mem_coordsOf.mpr hi0.1⟩
    refine le_antisymm (GEu_le_leviM hF hn hS ?_) (iSup₂_le fun i hi => ?_)
    · intro j hj a ha
      by_contra hcon
      push Not at hcon
      apply hj
      subst hB
      exact mem_nodesOf_of_ge (mem_coordsOf.mp ha) hl hcon
    · refine rankOne_le_GEu hF (mem_coordsOf.mpr hi.1) fun hs => mem_coordsOf.mpr ?_
      have : (⟨i.val + 1, hs⟩ : Fin (n / 2)).castSucc = i.succ := Fin.ext (by simp)
      rw [this]; exact hi.2
  · refine le_antisymm (GAu_le_leviM hF hn ?_) (iSup₂_le fun i hi => ?_)
    · intro j hj a ha b hb
      by_contra hcon
      apply hj
      subst hB
      have ha' := mem_coordsOf.mp ha
      have hb' := mem_coordsOf.mp hb
      by_cases hab : a.val ≤ j.val
      · have hbj : ¬ b.val ≤ j.val := fun h => hcon ⟨fun _ => h, fun _ => hab⟩
        exact mem_nodesOf_of_between ha' hb' (by omega) (by omega)
      · have hbj : b.val ≤ j.val := by
          by_contra h
          exact hcon ⟨fun h' => absurd h' hab, fun h' => absurd h' h⟩
        exact mem_nodesOf_of_between ha' hb' (by omega) (by omega)
    · have hs : i.val + 1 < n / 2 := by
        by_contra h
        have hilt : i.val < n / 2 := i.isLt
        apply hl
        have : i.succ = Fin.last (n / 2) := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        rw [← this]
        exact hi.2
      have hsucc : (⟨i.val + 1, hs⟩ : Fin (n / 2)) ∈ coordsOf B := by
        have : (⟨i.val + 1, hs⟩ : Fin (n / 2)).castSucc = i.succ := Fin.ext (by simp)
        rw [mem_coordsOf, this]; exact hi.2
      exact rankOne_le_GAu hF hs (mem_coordsOf.mpr hi.1) hsucc


end GbU

section Supp

variable {F : Type} [Field F] {n : ℕ}

@[expose] def SuppOn (P : Set (Fin n)) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ u v, ¬ (u ∈ P ∧ v ∈ P) → M u v = (1 : Matrix (Fin n) (Fin n) F) u v

theorem SuppOn.sub_one_ne {P : Set (Fin n)} {M : Matrix (Fin n) (Fin n) F} (h : SuppOn P M)
    {u v : Fin n} (hne : (M - 1) u v ≠ 0) : u ∈ P ∧ v ∈ P := by
  by_contra hc
  apply hne
  rw [Matrix.sub_apply, h u v hc, sub_self]

theorem SuppOn.mul {P Q : Set (Fin n)} {M N : Matrix (Fin n) (Fin n) F} (hM : SuppOn P M)
    (hN : SuppOn Q N) : SuppOn (P ∪ Q) (M * N) := by
  intro u v huv
  have key : (M - 1) * (N - 1) = 0 ∨ True := Or.inr trivial
  have e : M * N = 1 + (M - 1) * (N - 1) + (M - 1) + (N - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e]
  have h1 : ((M - 1) * (N - 1)) u v = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases h2 : (M - 1) u t = 0
    · rw [h2, zero_mul]
    · by_cases h3 : (N - 1) t v = 0
      · rw [h3, mul_zero]
      · exact absurd ⟨Or.inl (hM.sub_one_ne h2).1, Or.inr (hN.sub_one_ne h3).2⟩ huv
  have h2 : (M - 1) u v = 0 := by
    by_contra h
    exact huv ⟨Or.inl (hM.sub_one_ne h).1, Or.inl (hM.sub_one_ne h).2⟩
  have h3 : (N - 1) u v = 0 := by
    by_contra h
    exact huv ⟨Or.inr (hN.sub_one_ne h).1, Or.inr (hN.sub_one_ne h).2⟩
  simp only [Matrix.add_apply, h1, h2, h3, add_zero]

theorem SuppOn.mono {P Q : Set (Fin n)} {M : Matrix (Fin n) (Fin n) F} (h : SuppOn P M)
    (hPQ : P ⊆ Q) : SuppOn Q M := fun u v huv => h u v (fun ⟨a, b⟩ => huv ⟨hPQ a, hPQ b⟩)

theorem SuppOn.comm {P Q : Set (Fin n)} {M N : Matrix (Fin n) (Fin n) F} (hM : SuppOn P M)
    (hN : SuppOn Q N) (hd : Disjoint P Q) : M * N = N * M := by
  have h1 : (M - 1) * (N - 1) = 0 := by
    ext u v
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases h2 : (M - 1) u t = 0
    · rw [h2, zero_mul]
    · by_cases h3 : (N - 1) t v = 0
      · rw [h3, mul_zero]
      · exact absurd (hd.le_bot ⟨(hM.sub_one_ne h2).2, (hN.sub_one_ne h3).1⟩) (by simp)
  have h2 : (N - 1) * (M - 1) = 0 := by
    ext u v
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases h2 : (N - 1) u t = 0
    · rw [h2, zero_mul]
    · by_cases h3 : (M - 1) t v = 0
      · rw [h3, mul_zero]
      · exact absurd (hd.le_bot ⟨(hM.sub_one_ne h3).1, (hN.sub_one_ne h2).2⟩) (by simp)
  have e1 : M * N = 1 + (M - 1) * (N - 1) + (M - 1) + (N - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
    abel
  have e2 : N * M = 1 + (N - 1) * (M - 1) + (N - 1) + (M - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e1, e2, h1, h2]
  abel


theorem suppOn_extendMat {ι : Type} [Fintype ι] [DecidableEq ι] {φ : ι → Fin n}
    (hφ : Function.Injective φ) (A : Matrix ι ι F) : SuppOn (Set.range φ) (extendMat hφ A) := by
  intro u v huv
  apply extendMat_apply_of_not_mem hφ A
  by_contra hc
  push Not at hc
  exact huv hc

end Supp

section GbSupp

open Classical

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ} {I : Set (Fin (n / 2))}

@[expose] def posGb (B : Finset (Fin (n / 2 + 1))) : Set (Fin n) :=
  {x | ∃ a ∈ coordsOf B, x = lowIdx a ∨ x = Fin.rev (lowIdx a)} ∪
    {x | Fin.rev x = x ∧ Fin.last (n / 2) ∈ B}

theorem GbU_supp (B : Finset (Fin (n / 2 + 1))) {x : SU (unitaryInvolution F 2 f) n}
    (hx : x ∈ GbU hF B) : SuppOn (posGb B) (mat (unitaryInvolution F 2 f) n x) := by
  unfold GbU at hx
  split_ifs at hx with hl
  · obtain ⟨M, rfl⟩ := hx
    rw [mat_suEmbed]
    refine (suppOn_extendMat (eTau_injective _) _).mono ?_
    rintro _ ⟨i, rfl⟩
    rcases mem_ePos.mp (eTau_mem (coordsOf B) i) with ⟨a, ha, h⟩ | h
    · exact Or.inl ⟨a, ha, h⟩
    · exact Or.inr ⟨h, hl⟩
  · obtain ⟨g, rfl⟩ := hx
    rw [mat_levSU]
    unfold levMat
    refine ((suppOn_extendMat (aIdx_injective _) _).mul
      (suppOn_extendMat (rev_comp_injective (aIdx_injective _)) _)).mono ?_
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl ⟨i.1, i.2, Or.inl rfl⟩
    · exact Or.inl ⟨i.1, i.2, Or.inr rfl⟩

theorem posGb_disjoint {p q : Fin (n / 2 + 1)} (h : blkSet I p ≠ blkSet I q) :
    Disjoint (posGb (blkSet I p)) (posGb (blkSet I q)) := by
  have hd := disjoint_blkSet h
  rw [Set.disjoint_left]
  rintro x (⟨a, ha, hx⟩ | ⟨hx1, hx2⟩) (⟨b, hb, hy⟩ | ⟨hy1, hy2⟩)
  · have hab : a ≠ b := fun e => Finset.disjoint_left.mp hd (mem_coordsOf.mp ha)
      (mem_coordsOf.mp (e ▸ hb))
    rcases hx with rfl | rfl <;> rcases hy with h' | h'
    · exact hab (Fin.ext (by simpa [val_lowIdx] using congrArg Fin.val h'))
    · exact lowIdx_ne_rev a b h'
    · exact lowIdx_ne_rev b a h'.symm
    · exact hab (Fin.ext (by
        have := Fin.rev_injective h'
        simpa [val_lowIdx] using congrArg Fin.val this))
  · rcases hx with rfl | rfl
    · exact lowIdx_ne_rev a a hy1.symm
    · apply lowIdx_ne_rev a a
      rw [Fin.rev_rev] at hy1
      exact hy1
  · rcases hy with rfl | rfl
    · exact lowIdx_ne_rev b b hx1.symm
    · apply lowIdx_ne_rev b b
      rw [Fin.rev_rev] at hx1
      exact hx1
  · exact Finset.disjoint_left.mp hd hx2 hy2


theorem GbU_commute {p q : Fin (n / 2 + 1)} (h : blkSet I p ≠ blkSet I q) :
    GbU hF (blkSet I p) ≤ Subgroup.centralizer (GbU hF (blkSet I q) : Set (SU (unitaryInvolution F 2 f) n)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply mat_injective
  rw [map_mul, map_mul]
  exact ((GbU_supp hF _ hy).comm (GbU_supp hF _ hx) (posGb_disjoint h).symm)

end GbSupp

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
