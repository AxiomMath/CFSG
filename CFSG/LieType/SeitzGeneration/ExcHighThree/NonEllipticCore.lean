module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.LieType.SeitzGeneration.ExcHighThree.RootDegreeInj
public import CFSG.LieType.SeitzGeneration.ExcHighThree.MaxRootPairing
public import CFSG.HardMathSupport.Foote.ModuleExclusions.ExcSigns

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint

section NonElliptic


variable {τ : Tag}

@[expose] def pairDeg (τ : Tag) (l : Fin τ.rank → ℤ) : (Fin τ.rank → ℤ) →+ ℤ :=
  AddMonoidHom.mk' (fun α => ∑ i, l i * α i) fun a b => by
    simp [mul_add, Finset.sum_add_distrib]

theorem pairDeg_apply (l α : Fin τ.rank → ℤ) : pairDeg τ l α = ∑ i, l i * α i := rfl

@[expose] def rootLevel (τ : Tag) (L : Type) [Field L] (l : Fin τ.rank → ℤ) (m : ℤ) :
    Subgroup (ModGL τ L) :=
  Subgroup.closure {g | ∃ β, IsRoot τ β ∧ ∑ i, l i * β i = m ∧ ∃ t : L, g = pinnedX τ L β t}

theorem pinnedX_mem_rootLevel {L : Type} [Field L] {l : Fin τ.rank → ℤ} {m : ℤ}
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hm : ∑ i, l i * β i = m) (t : L) :
    pinnedX τ L β t ∈ rootLevel τ L l m :=
  Subgroup.subset_closure ⟨β, hβ, hm, t, rfl⟩

theorem rootLevel_commute {L : Type} [Field L] {l : Fin τ.rank → ℤ} {m : ℤ}
    (hcomm : ∀ β γ, IsRoot τ β → IsRoot τ γ → ∑ i, l i * β i = m → ∑ i, l i * γ i = m →
      ∀ s t : L, pinnedX τ L β s * pinnedX τ L γ t = pinnedX τ L γ t * pinnedX τ L β s)
    {x y : ModGL τ L} (hx : x ∈ rootLevel τ L l m) (hy : y ∈ rootLevel τ L l m) :
    x * y = y * x := by
  set S : Set (ModGL τ L) :=
    {g | ∃ β, IsRoot τ β ∧ ∑ i, l i * β i = m ∧ ∃ t : L, g = pinnedX τ L β t} with hS
  have hSS : S ⊆ Subgroup.centralizer S := by
    rintro _ ⟨β, hβ, hβm, s, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨γ, hγ, hγm, t, rfl⟩
    exact (hcomm β γ hβ hγ hβm hγm s t).symm
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).2 hSS
  have h2 : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have hxS : S ⊆ Subgroup.centralizer ({x} : Set (ModGL τ L)) := by
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.1 hz]
      exact (Subgroup.mem_centralizer_iff.1 (h1 hx) g hg).symm
    have h3 : Subgroup.closure S ≤ Subgroup.centralizer ({x} : Set (ModGL τ L)) :=
      (Subgroup.closure_le _).2 hxS
    exact Subgroup.mem_centralizer_iff.1 (h3 hy) x (Set.mem_singleton x)
  exact h2 x hx y hy

theorem rootLevel_pow {L : Type} [Field L] (p : ℕ) [CharP L p] {l : Fin τ.rank → ℤ} {m : ℤ}
    (hcomm : ∀ β γ, IsRoot τ β → IsRoot τ γ → ∑ i, l i * β i = m → ∑ i, l i * γ i = m →
      ∀ s t : L, pinnedX τ L β s * pinnedX τ L γ t = pinnedX τ L γ t * pinnedX τ L β s)
    {g : ModGL τ L} (hg : g ∈ rootLevel τ L l m) : g ^ p = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, -, -, t, rfl⟩ := hx
    exact pinnedX_pow_char p β t
  | one => exact one_pow p
  | mul x y hx hy hx1 hy1 =>
    have hc : Commute x y := rootLevel_commute hcomm hx hy
    rw [hc.mul_pow, hx1, hy1, mul_one]
  | inv x hx hx1 => rw [inv_pow, hx1, inv_one]

theorem rootLevel_conj_diag {L : Type} [Field L] {l : Fin τ.rank → ℤ} {m : ℤ}
    (a : Fin τ.rank → Lˣ) {g : ModGL τ L} (hg : g ∈ rootLevel τ L l m) :
    rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ ∈ rootLevel τ L l m := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, hβm, t, rfl⟩ := hx
    rw [rootDiagUnit_conj_pinnedX a hβ t]
    exact pinnedX_mem_rootLevel hβ hβm _
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have : rootDiagUnit τ a * (x * y) * (rootDiagUnit τ a)⁻¹ =
        (rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹) *
          (rootDiagUnit τ a * y * (rootDiagUnit τ a)⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : rootDiagUnit τ a * x⁻¹ * (rootDiagUnit τ a)⁻¹ =
        (rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem rootLevel_le_adjoint {L : Type} [Field L] (l : Fin τ.rank → ℤ) (m : ℤ) :
    rootLevel τ L l m ≤ adjointGroup τ L := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨β, -, -, t, rfl⟩
  exact pinnedX_mem_adjointGroup β t

theorem exists_root_orbit (w : WeylGroup τ) (α₀ : Fin τ.rank → ℤ) :
    ∃ n : ℕ, 0 < n ∧ (w ^ n) • α₀ = α₀ ∧ ∀ k, 0 < k → k < n → (w ^ k) • α₀ ≠ α₀ := by
  classical
  obtain ⟨N, hNpos, hNeq⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite w)
  have hex : ∃ m, 0 < m ∧ (w ^ m) • α₀ = α₀ := ⟨N, hNpos, by rw [hNeq, one_smul]⟩
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun k hk0 hkn hk => Nat.find_min hex hkn ⟨hk0, hk⟩⟩

@[expose] def cycSeqE {L : Type} [Field L] (s : ℕ → L) (q : ℕ) (t₀ : L) : ℕ → L
  | 0 => t₀
  | k + 1 => s k * (cycSeqE s q t₀ k) ^ q

theorem cycSeqE_affine {L : Type} [Field L] (s : ℕ → L) (hs : ∀ k, s k * s k = 1) (q : ℕ) :
    ∀ n : ℕ, ∃ S : L, S * S = 1 ∧ ∀ t₀ : L, cycSeqE s q t₀ n = S * t₀ ^ (q ^ n)
  | 0 => ⟨1, by simp, fun t₀ => by simp [cycSeqE]⟩
  | n + 1 => by
    obtain ⟨S, hS, hf⟩ := cycSeqE_affine s hs q n
    refine ⟨s n * S ^ q, ?_, fun t₀ => ?_⟩
    · calc (s n * S ^ q) * (s n * S ^ q) = (s n * s n) * (S * S) ^ q := by rw [mul_pow]; ring
        _ = 1 := by rw [hs n, hS, one_pow, mul_one]
    · simp only [cycSeqE]
      rw [hf, mul_pow, ← pow_mul, pow_succ]
      ring

theorem exists_cycSeqE_fixed {L : Type} [Field L] [IsAlgClosed L] (s : ℕ → L)
    (hs : ∀ k, s k * s k = 1) {q n : ℕ} (hq : 2 ≤ q) (hn : 0 < n) :
    ∃ t₀ : L, t₀ ≠ 0 ∧ cycSeqE s q t₀ n = t₀ := by
  obtain ⟨S, hS, hf⟩ := cycSeqE_affine s hs q n
  have hqn : 2 ≤ q ^ n := le_trans hq (Nat.le_self_pow hn.ne' q)
  obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_pow_nat_eq S (show 0 < q ^ n - 1 by omega)
  have hS0 : S ≠ 0 := fun h => by rw [h, zero_mul] at hS; exact zero_ne_one hS
  have ht0 : t₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at ht₀
    exact hS0 ht₀.symm
  refine ⟨t₀, ht0, ?_⟩
  rw [hf, show q ^ n = (q ^ n - 1) + 1 by omega, pow_succ, ht₀, ← mul_assoc, hS, one_mul]

theorem exists_cycle_element_deg {L : Type} [Field L] [IsAlgClosed L] (p e : ℕ) [Fact p.Prime]
    [CharP L p] (he : 1 ≤ e) (g : WeylGroup τ) (n : ℕ) (hn : 0 < n)
    (β : ℕ → Fin τ.rank → ℤ) (φ : (Fin τ.rank → ℤ) →+ ℤ)
    (hper : ∀ k, β (k + n) = β k) (hroot : ∀ k, IsRoot τ (β k)) (hpos : ∀ k, 0 < φ (β k))
    (hne : ∀ k l, k < n → l < n → k ≠ l → β k ≠ β l)
    (hcomm : ∀ k l, k < n → l < n → ∀ s t : L,
      pinnedX τ L (β k) s * pinnedX τ L (β l) t = pinnedX τ L (β l) t * pinnedX τ L (β k) s)
    (hgβ : ∀ k, g • β k = β (k + 1)) (S : Set (Fin τ.rank → ℤ)) (hS : ∀ k, β k ∈ S) :
    ∃ v : ModGL τ L, v ∈ rootSpan τ L S ∧
      frobTwistGL τ L p e (canonicalRep (coxeterSystem τ) L g) v = v ∧ v ≠ 1 ∧ v ^ p = 1 := by
  obtain ⟨s0, hs0⟩ := exists_sign_family (L := L) (τ := τ) g
  obtain ⟨Q, hQ⟩ : ∃ Q : ModGL τ L, Q = canonicalRep (coxeterSystem τ) L g := ⟨_, rfl⟩
  rw [← hQ]
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ p ^ e := le_trans hp2 (Nat.le_self_pow (by omega) p)
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → L, ∀ k, s k = s0 (β k) := ⟨fun k => s0 (β k), fun k => rfl⟩
  have hs : ∀ k, s k * s k = 1 := fun k => by rw [hsdef k]; exact (hs0 (β k) (hroot k)).1
  obtain ⟨t₀, ht₀, hfix⟩ := exists_cycSeqE_fixed s hs hq2 hn
  obtain ⟨t, ht⟩ : ∃ t : ℕ → L, t = cycSeqE s (p ^ e) t₀ := ⟨_, rfl⟩
  have ht0 : t 0 = t₀ := by rw [ht]; simp [cycSeqE]
  have htsucc : ∀ k, t (k + 1) = s k * (t k) ^ (p ^ e) := fun k => by rw [ht]; simp [cycSeqE]
  have htn : t n = t₀ := by rw [ht]; exact hfix
  obtain ⟨f, hf⟩ : ∃ f : ℕ → (Module.End L (RootModule τ L))ˣ,
      ∀ k, f k = pinnedX τ L (β k) (t k) := ⟨fun k => pinnedX τ L (β k) (t k), fun k => rfl⟩
  have hG : ∀ k, frobTwistGL τ L p e Q (f k) = f (k + 1) := by
    intro k
    rw [frobTwistGL_apply, hf, entrywiseFrobGL_pinnedX p e (β k) (t k), iterateFrobenius_def, hQ,
      (hs0 (β k) (hroot k)).2 (t k ^ (p ^ e)), hgβ k, hf, htsucc k, hsdef k]
  have hGv : frobTwistGL τ L p e Q (((List.range n).map f).prod) =
      ((List.range n).map (fun k => f (k + 1))).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hG k
  have hcommf : ∀ i j, i < n → j < n → i ≠ j → Commute (f i) (f j) := by
    intro i j hi hj _
    rw [hf, hf]
    exact hcomm i j hi hj (t i) (t j)
  have hcomm0 : ∀ k, k < n → Commute (f 0) (f k) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      exact Commute.refl _
    · exact hcommf 0 k hn hk (Ne.symm hk0)
  have hPcomm : Commute (f 0) ((List.range n).map f).prod := by
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hcomm0 k (List.mem_range.1 hk)
  have hL1 : ((List.range (n + 1)).map f).prod =
      f 0 * ((List.range n).map (fun k => f (k + 1))).prod := by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    rfl
  have hL2 : ((List.range (n + 1)).map f).prod = ((List.range n).map f).prod * f n := by
    rw [List.range_succ, List.map_append, List.prod_append]
    simp
  have hfn : f n = f 0 := by
    rw [hf, hf]
    have hβn : β n = β 0 := by simpa using hper 0
    have htn' : t n = t 0 := by rw [htn, ht0]
    rw [hβn, htn']
  have hP' : ((List.range n).map (fun k => f (k + 1))).prod = ((List.range n).map f).prod := by
    have key : f 0 * ((List.range n).map (fun k => f (k + 1))).prod =
        f 0 * ((List.range n).map f).prod := by
      rw [← hL1, hL2, hfn, hPcomm.eq]
    exact mul_left_cancel key
  have hmem : ((List.range n).map f).prod ∈ rootSpan τ L S := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    rw [hf]
    have hle : rootSubgroup τ L (β k) ≤ rootSpan τ L S :=
      le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup τ L α) (β k) (hS k) le_rfl
    exact hle (Subgroup.subset_closure ⟨t k, rfl⟩)
  have hconv : ∀ g' : ℕ → (Module.End L (RootModule τ L))ˣ,
      (List.range n).map g' = List.ofFn (fun i : Fin n => g' i.val) := by
    intro g'
    apply List.ext_getElem <;> simp
  have hv_eq : ((List.range n).map f).prod =
      (List.ofFn fun i : Fin n => pinnedX τ L (β i.val) (t i.val)).prod := by
    rw [hconv f]
    simp only [hf]
  have hv_ne : ((List.range n).map f).prod ≠ 1 := by
    rw [hv_eq]
    have hinj : Function.Injective (fun i : Fin n => β i.val) := by
      intro i j hij
      by_contra hne'
      exact hne i.val j.val i.2 j.2 (fun h => hne' (Fin.ext h)) hij
    exact prod_ne_one_of_degree_pos φ (fun i : Fin n => β i.val) hinj
      (fun i => ⟨hroot i.val, hpos i.val⟩) (fun i : Fin n => t i.val) ⟨0, hn⟩
      (show t 0 ≠ 0 by rw [ht0]; exact ht₀)
  have hvp : ((List.range n).map f).prod ^ p = 1 :=
    pow_prod_range_eq_one p f n hcommf (fun i _ => by rw [hf]; exact pinnedX_pow_char p _ _)
  refine ⟨((List.range n).map f).prod, hmem, ?_, hv_ne, hvp⟩
  rw [hGv, hP']

theorem E6_level_comm {L : Type} [Field L] (l : Fin 6 → ℤ) {m : ℤ} (hm : 0 < m)
    (hmax : ∀ γ, IsRoot Tag.E6 γ → ∑ i, l i * γ i ≤ m) :
    ∀ β γ, IsRoot Tag.E6 β → IsRoot Tag.E6 γ → ∑ i, l i * β i = m → ∑ i, l i * γ i = m →
      ∀ s t : L, pinnedX Tag.E6 L β s * pinnedX Tag.E6 L γ t =
        pinnedX Tag.E6 L γ t * pinnedX Tag.E6 L β s := by
  intro β γ hβ hγ hβm hγm s t
  by_cases h : β = γ
  · subst h
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · exact CFSG.HardMathSupport.Foote.ModuleExclusions.pinnedX_commute_of_iform_nonneg L hβ hγ h
      (iform_nonneg_of_max_pairing l hm hmax hβ hγ hβm hγm h)
      (not_isRoot_add_of_max_pairing l hm hmax hβ hγ hβm hγm) s t

theorem exists_nonelliptic_cycle_element {L : Type} [Field L] [IsAlgClosed L] (p e : ℕ)
    [Fact p.Prime] [CharP L p] (he : 1 ≤ e) (w : WeylGroup Tag.E6) (l : Fin Tag.E6.rank → ℤ)
    (hl : l ≠ 0) (hfix : ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, l i * (w • v) i = ∑ i, l i * v i) :
    ∃ m : ℤ, 0 < m ∧
      (∀ x ∈ rootLevel Tag.E6 L l m, ∀ y ∈ rootLevel Tag.E6 L l m, x * y = y * x) ∧
      (∀ x ∈ rootLevel Tag.E6 L l m, x ^ p = 1) ∧
      ∃ v ∈ rootLevel Tag.E6 L l m,
        frobTwistGL Tag.E6 L p e (canonicalRep (coxeterSystem Tag.E6) L w) v = v ∧ v ≠ 1 := by
  obtain ⟨m, hm, ⟨α₀, hα₀, hα₀m⟩, hmax⟩ := exists_max_root_pairing l hl
  have hcomm := E6_level_comm (L := L) l hm hmax
  refine ⟨m, hm, fun x hx y hy => rootLevel_commute hcomm hx hy,
    fun x hx => rootLevel_pow p hcomm hx, ?_⟩
  obtain ⟨n, hn, hwn, hmin⟩ := exists_root_orbit w α₀
  set β : ℕ → Fin Tag.E6.rank → ℤ := fun k => (w ^ k) • α₀ with hβdef
  have hroot : ∀ k, IsRoot Tag.E6 (β k) := fun k => IsRoot.smul hα₀ (w ^ k)
  have hpair : ∀ k, ∑ i, l i * β k i = m := by
    intro k
    induction k with
    | zero =>
      have h0 : β 0 = α₀ := by simp [hβdef]
      rw [h0]
      exact hα₀m
    | succ k ih =>
      have h1 : β (k + 1) = w • β k := by
        simp only [hβdef, pow_succ', mul_smul]
      rw [h1, hfix, ih]
  have hper : ∀ k, β (k + n) = β k := by
    intro k
    simp only [hβdef, pow_add, mul_smul, hwn]
  have hgβ : ∀ k, w • β k = β (k + 1) := by
    intro k
    simp only [hβdef, pow_succ', mul_smul]
  have hne : ∀ k j, k < n → j < n → k ≠ j → β k ≠ β j := by
    intro k j hk hj hkj hkj'
    rcases Nat.lt_or_gt_of_ne hkj with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.le
      have hd : 0 < d := by omega
      apply hmin d hd (by omega)
      have h2 : (w ^ k) • α₀ = (w ^ k) • ((w ^ d) • α₀) := by
        simp only [hβdef, pow_add, mul_smul] at hkj'
        simpa [mul_smul] using hkj'
      exact (MulAction.injective (w ^ k) h2).symm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.le
      have hd : 0 < d := by omega
      apply hmin d hd (by omega)
      have h2 : (w ^ j) • α₀ = (w ^ j) • ((w ^ d) • α₀) := by
        simp only [hβdef, pow_add, mul_smul] at hkj'
        simpa [mul_smul] using hkj'.symm
      exact (MulAction.injective (w ^ j) h2).symm
  obtain ⟨v, hvS, hvF, hv1, -⟩ := exists_cycle_element_deg (L := L) p e he w n hn β
    (pairDeg Tag.E6 l) hper hroot (fun k => by rw [pairDeg_apply, hpair k]; exact hm) hne
    (fun k j _ _ s t => hcomm (β k) (β j) (hroot k) (hroot j) (hpair k) (hpair j) s t) hgβ
    {γ | IsRoot Tag.E6 γ ∧ ∑ i, l i * γ i = m} (fun k => ⟨hroot k, hpair k⟩)
  refine ⟨v, ?_, hvF, hv1⟩
  have hle : rootSpan Tag.E6 L {γ | IsRoot Tag.E6 γ ∧ ∑ i, l i * γ i = m} ≤
      rootLevel Tag.E6 L l m := by
    unfold rootSpan
    refine iSup₂_le fun γ hγ => ?_
    unfold rootSubgroup
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_rootLevel hγ.1 hγ.2 c
  exact hle hvS

end NonElliptic

end CFSG.LieType.SeitzGeneration.ExcHighThree
