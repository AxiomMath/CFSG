module

public import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints
public import CFSG.GH74.GLS.IVK.Defs
import CFSG.CharacterTheory.PSL2Table.Tori

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup

section RankBound

private theorem frobRank_field_aux {F : Type} [Field F] {H M : Type} [Group H] [Finite H]
    [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (ρ : Representation F H M) (K B : Subgroup H) [K.Normal]
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hchar : ¬ ringChar F ∣ Nat.card K)
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ k ∈ K, b * k = k * b → k = 1)
    (hmove : ∃ k ∈ K, ∃ v : M, ρ k v ≠ v) : Nat.card B ≤ Module.finrank F M := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let ρK : Representation F K M := ρ.comp K.subtype
  let N : Module.End F M := Representation.norm ρK
  have hNapply : ∀ x : M, N x = ∑ k : K, ρ k x := by
    intro x
    simp [N, Representation.norm, ρK, LinearMap.sum_apply]
  have hNcomm : ∀ (h : H) (x : M), N (ρ h x) = ρ h (N x) := by
    intro h x
    rw [hNapply, hNapply, map_sum]
    let e : K ≃ K := (MulAut.conjNormal (H := K) h⁻¹).toEquiv
    rw [← Equiv.sum_comp e (fun k => ρ h (ρ k x))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hek : ((e k : K) : H) = h⁻¹ * k * h := by
      simp [e]
    rw [hek, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  let W : Submodule F M := LinearMap.ker N
  have hW : ∀ h : H, W ≤ W.comap (ρ h) := by
    intro h w hw
    simp only [W, Submodule.mem_comap, LinearMap.mem_ker] at hw ⊢
    rw [hNcomm, hw, map_zero]
  let ρW : Representation F H W := ρ.subrepresentation W hW
  have hcard : ((Nat.card K : ℕ) : F) ≠ 0 := fun h => hchar ((ringChar.spec F _).mp h)
  have hNfix : ∀ x : M, (∀ k : K, ρ k x = x) → N x = (Nat.card K : F) • x := by
    intro x hx
    rw [hNapply]
    simp only [hx, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul F, Nat.card_eq_fintype_card]
  have hfix : Representation.invariants (ρW.comp K.subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Representation.mem_invariants] at hw
    have h1 : ∀ k : K, ρ k (w : M) = w := fun k => congrArg Subtype.val (hw k)
    have h2 : N (w : M) = (Nat.card K : F) • (w : M) := hNfix _ h1
    have h3 : N (w : M) = 0 := w.2
    rw [Submodule.mem_bot]
    have h4 : (Nat.card K : F) • (w : M) = 0 := h2.symm.trans h3
    exact Subtype.ext ((smul_eq_zero.mp h4).resolve_left hcard)
  obtain ⟨k₀, hk₀, v, hv⟩ := hmove
  have hWpos : 0 < Module.finrank F W := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨v - ρ k₀ v, ?_⟩, ?_⟩
    · show N (v - ρ k₀ v) = 0
      rw [map_sub]
      have := Representation.norm_self_apply ρK ⟨k₀, hk₀⟩ v
      exact sub_eq_zero.mpr this.symm
    · intro h
      apply hv
      have h' : v - ρ k₀ v = 0 := congrArg Subtype.val h
      exact (sub_eq_zero.mp h').symm
  have hmain := CFSG.ABGLocalTools.finrank_invariants_mul_card_of_fixedPointFree ρW
    (K := K) (B := B) ⟨⟨fun a b => Subtype.ext (hK a a.2 b b.2)⟩⟩
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hfpf hchar hfix
  have hle : Nat.card B ≤ Module.finrank F W :=
    Nat.le_of_dvd hWpos (hmain ▸ Dvd.intro_left _ rfl)
  exact hle.trans (Submodule.finrank_le W)

private theorem frobRank_field {F : Type} [Field F] {G M : Type} [Group G] [Finite G]
    [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (ρ : Representation F G M) (K B : Subgroup G)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hchar : ¬ ringChar F ∣ Nat.card K)
    (hB : B ≤ normalizer (K : Set G))
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ k ∈ K, b * k = k * b → k = 1)
    (hmove : ∃ k ∈ K, ∃ v : M, ρ k v ≠ v) : Nat.card B ≤ Module.finrank F M := by
  have hKH : K ≤ normalizer (K : Set G) := Subgroup.le_normalizer
  have : (K.subgroupOf (normalizer (K : Set G))).Normal := Subgroup.normal_in_normalizer
  have hKcard : Nat.card (K.subgroupOf (normalizer (K : Set G))) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hBcard : Nat.card (B.subgroupOf (normalizer (K : Set G))) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  rw [← hBcard]
  refine frobRank_field_aux (ρ.comp (normalizer (K : Set G)).subtype)
    (K.subgroupOf (normalizer (K : Set G))) (B.subgroupOf (normalizer (K : Set G))) ?_ ?_ ?_ ?_
  · intro a ha b hb
    exact Subtype.ext (hK a (mem_subgroupOf.mp ha) b (mem_subgroupOf.mp hb))
  · rwa [hKcard]
  · intro b hb hb1 k hk hbk
    refine Subtype.ext ?_
    have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    simpa using hfpf b (mem_subgroupOf.mp hb) hb1' k (mem_subgroupOf.mp hk)
      (congrArg Subtype.val hbk)
  · obtain ⟨a, ha, v, hv⟩ := hmove
    exact ⟨⟨a, hKH ha⟩, mem_subgroupOf.mpr ha, v, hv⟩

end RankBound

section Torsion

private theorem fixed_of_torsion_fixed {A : Type} [CommGroup A] [Finite A] {q : ℕ}
    (hAq : Nat.Coprime (Nat.card A) q) (σ : MulAut A) (hσ : σ ^ q = 1)
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card A → ∀ a : A, a ^ r = 1 → σ a = a) :
    ∀ a : A, σ a = a := by
  intro a
  induction' hn : orderOf a using Nat.strong_induction_on with n ih generalizing a
  by_cases hn1 : n = 1
  · subst hn1
    have : a = 1 := orderOf_eq_one_iff.mp hn
    rw [this, map_one]
  · have hrp : n.minFac.Prime := Nat.minFac_prime hn1
    have hrn : n.minFac ∣ n := Nat.minFac_dvd n
    have hnA : n ∣ Nat.card A := hn ▸ orderOf_dvd_natCard a
    have hrA : n.minFac ∣ Nat.card A := hrn.trans hnA
    have hrq : Nat.Coprime n.minFac q := Nat.Coprime.coprime_dvd_left hrA hAq
    have hord : orderOf (a ^ n.minFac) = n / n.minFac := by
      rw [orderOf_pow_of_dvd hrp.ne_zero (hn ▸ hrn), hn]
    have hn0 : 0 < n := by
      rw [← hn]
      exact orderOf_pos a
    have hlt : n / n.minFac < n := Nat.div_lt_self hn0 hrp.one_lt
    have hfix : σ (a ^ n.minFac) = a ^ n.minFac := ih (n / n.minFac) hlt (a ^ n.minFac) hord
    set b := σ a * a⁻¹ with hb
    have hbr : b ^ n.minFac = 1 := by
      rw [hb, mul_pow, inv_pow, ← map_pow, hfix, mul_inv_cancel]
    have hσb : σ b = b := h n.minFac hrp hrA b hbr
    have hσa : σ a = b * a := by rw [hb, inv_mul_cancel_right]
    have hpow : ∀ j : ℕ, (σ ^ j) a = a * b ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        rw [pow_succ', MulAut.mul_apply, ihj, map_mul, map_pow, hσb, hσa, pow_succ]
        rw [mul_comm b a, mul_assoc, mul_comm b (b ^ j)]
    have hbq : b ^ q = 1 := by
      have h1 := hpow q
      rw [hσ] at h1
      have h2 : a * b ^ q = a * 1 := by
        rw [mul_one, ← h1]
        rfl
      exact mul_left_cancel h2
    have hb1 : b = 1 := by
      have h1 : orderOf b ∣ n.minFac := orderOf_dvd_of_pow_eq_one hbr
      have h2 : orderOf b ∣ q := orderOf_dvd_of_pow_eq_one hbq
      have h3 : orderOf b ∣ Nat.gcd n.minFac q := Nat.dvd_gcd h1 h2
      rw [hrq] at h3
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    rw [hσa, hb1, one_mul]

private def torsionBy (r : ℕ) (A : Type) [CommGroup A] : Subgroup A :=
  (powMonoidHom r : A →* A).ker

private theorem mem_torsionBy {r : ℕ} {A : Type} [CommGroup A] {a : A} :
    a ∈ torsionBy r A ↔ a ^ r = 1 := by
  simp [torsionBy, MonoidHom.mem_ker]

private instance torsionBy.instModule (r : ℕ) [NeZero r] (A : Type) [CommGroup A] :
    Module (ZMod r) (Additive ↥(torsionBy r A)) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (mem_torsionBy.mp (Additive.toMul x).2))

private theorem natCard_torsionBy {A : Type} [CommGroup A] [Finite A] (r : ℕ) :
    Nat.card (torsionBy r A) = ((powMonoidHom r : A →* A).range).index := by
  set f : A →* A := powMonoidHom r with hf
  have h1 := Subgroup.card_mul_index f.ker
  have h2 := Subgroup.card_mul_index f.range
  rw [Subgroup.index_ker] at h1
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have h3 : Nat.card f.range * Nat.card f.ker = Nat.card f.range * f.range.index := by
    rw [mul_comm, h1, h2]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

private theorem index_range_pow_le {A : Type} [CommGroup A] [Finite A] (r : ℕ) [Fact r.Prime]
    {a₁ a₂ a₃ : A} (hgen : closure ({a₁, a₂, a₃} : Set A) = ⊤) :
    ((powMonoidHom r : A →* A).range).index ≤ r ^ 3 := by
  classical
  set R := (powMonoidHom r : A →* A).range with hR
  have hQ : ∀ y : A ⧸ R, y ^ r = 1 := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨a, rfl⟩
  have instQ : Module (ZMod r) (Additive (A ⧸ R)) := AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hQ _)
  have : Module.Finite (ZMod r) (Additive (A ⧸ R)) := Module.Finite.of_finite
  let S : Finset (Additive (A ⧸ R)) :=
    {Additive.ofMul (QuotientGroup.mk a₁), Additive.ofMul (QuotientGroup.mk a₂),
      Additive.ofMul (QuotientGroup.mk a₃)}
  have key : ∀ a : A, Additive.ofMul (QuotientGroup.mk a : A ⧸ R) ∈
      Submodule.span (ZMod r) (S : Set (Additive (A ⧸ R))) := by
    intro a
    have ha : a ∈ closure ({a₁, a₂, a₃} : Set A) := hgen ▸ Subgroup.mem_top a
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      apply Submodule.subset_span
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    | one =>
      exact Submodule.zero_mem _
    | mul x y _ _ hx hy =>
      exact Submodule.add_mem _ hx hy
    | inv x _ hx =>
      exact Submodule.neg_mem _ hx
  have hspan : Submodule.span (ZMod r) (S : Set (Additive (A ⧸ R))) =
      (⊤ : Submodule (ZMod r) (Additive (A ⧸ R))) := by
    refine eq_top_iff.mpr ?_
    intro y _
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    have : y = Additive.ofMul (QuotientGroup.mk a : A ⧸ R) := by
      rw [ha]
      rfl
    rw [this]
    exact key a
  have hfin : Module.finrank (ZMod r) (Additive (A ⧸ R)) ≤ 3 := by
    have h1 := finrank_span_finset_le_card (R := ZMod r) S
    unfold Set.finrank at h1
    rw [hspan, finrank_top] at h1
    exact h1.trans Finset.card_le_three
  have hcard : Nat.card (Additive (A ⧸ R)) =
      r ^ Module.finrank (ZMod r) (Additive (A ⧸ R)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod]
  calc R.index = Nat.card (A ⧸ R) := Subgroup.index_eq_card R
    _ = Nat.card (Additive (A ⧸ R)) := (Nat.card_congr Additive.toMul).symm
    _ = r ^ Module.finrank (ZMod r) (Additive (A ⧸ R)) := hcard
    _ ≤ r ^ 3 := Nat.pow_le_pow_right (Fact.out : r.Prime).pos hfin

private theorem finrank_torsionBy_le {A : Type} [CommGroup A] [Finite A] (r : ℕ) [Fact r.Prime]
    {a₁ a₂ a₃ : A} (hgen : closure ({a₁, a₂, a₃} : Set A) = ⊤) :
    Module.finrank (ZMod r) (Additive ↥(torsionBy r A)) ≤ 3 := by
  have : Module.Finite (ZMod r) (Additive ↥(torsionBy r A)) := Module.Finite.of_finite
  have h1 : r ^ Module.finrank (ZMod r) (Additive ↥(torsionBy r A)) =
      Nat.card ↥(torsionBy r A) := by
    rw [← Nat.card_congr (Additive.toMul : Additive ↥(torsionBy r A) ≃ ↥(torsionBy r A)),
      Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod]
  have h2 : Nat.card ↥(torsionBy r A) ≤ r ^ 3 :=
    (natCard_torsionBy r).trans_le (index_range_pow_le r hgen)
  have h3 : r ^ Module.finrank (ZMod r) (Additive ↥(torsionBy r A)) ≤ r ^ 3 := h1 ▸ h2
  exact (Nat.pow_le_pow_iff_right (Fact.out : r.Prime).one_lt).mp h3

private def torsionActHom (r : ℕ) {A : Type} [CommGroup A] (σ : MulAut A) :
    ↥(torsionBy r A) →* ↥(torsionBy r A) where
  toFun x := ⟨σ (x : A), by rw [mem_torsionBy, ← map_pow, mem_torsionBy.mp x.2, map_one]⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' x y := Subtype.ext (map_mul σ (x : A) (y : A))

private def torsionRep (r : ℕ) [NeZero r] {A : Type} [CommGroup A] {G : Type} [Group G]
    (ρ : G →* MulAut A) : Representation (ZMod r) G (Additive ↥(torsionBy r A)) where
  toFun g := (MonoidHom.toAdditive (torsionActHom r (ρ g))).toZModLinearMap r
  map_one' := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [torsionActHom]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [torsionActHom]

private theorem card_le_three_of_torsion_move {G A : Type} [Group G] [Finite G] [CommGroup A]
    [Finite A] (ρ : G →* MulAut A) (r : ℕ) [Fact r.Prime] (K B : Subgroup G)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hchar : ¬ r ∣ Nat.card K)
    (hB : B ≤ normalizer (K : Set G))
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ k ∈ K, b * k = k * b → k = 1)
    {a₁ a₂ a₃ : A} (hgen : closure ({a₁, a₂, a₃} : Set A) = ⊤)
    (hmove : ∃ k ∈ K, ∃ a : A, a ^ r = 1 ∧ ρ k a ≠ a) : Nat.card B ≤ 3 := by
  have : Module.Finite (ZMod r) (Additive ↥(torsionBy r A)) := Module.Finite.of_finite
  have h1 := frobRank_field (torsionRep r ρ) K B hK
    (by rw [ZMod.ringChar_zmod_n]; exact hchar) hB hfpf (by
      obtain ⟨k, hk, a, ha, hka⟩ := hmove
      refine ⟨k, hk, Additive.ofMul ⟨a, mem_torsionBy.mpr ha⟩, fun h => hka ?_⟩
      have := congrArg (fun v => (Additive.toMul v : ↥(torsionBy r A)).1) h
      simpa [torsionRep, torsionActHom] using this)
  exact h1.trans (finrank_torsionBy_le r hgen)

end Torsion

section PSL

open CFSG.PSL2Table
open scoped MatrixGroups

variable {F : Type} [Field F]

private theorem unipotent_conj_mem_of_splitTorus {b x : PSL(2, F)} (hb : b ∈ splitTorus F)
    (hx : x ∈ unipotent F) : b * x * b⁻¹ ∈ unipotent F := by
  obtain ⟨a, rfl⟩ := (mem_splitTorus_iff_exists b).mp hb
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
  rw [mk_conj, diag_conj_unip]
  exact mk_unip_mem_unipotent _

private theorem splitTorus_le_normalizer_unipotent :
    splitTorus F ≤ normalizer (unipotent F : Set PSL(2, F)) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => unipotent_conj_mem_of_splitTorus hb hx, fun hx => ?_⟩
  have := unipotent_conj_mem_of_splitTorus (inv_mem hb) hx
  simpa [mul_assoc] using this

private theorem splitTorus_fixedPointFree (h2 : (2 : F) ≠ 0) :
    ∀ b ∈ splitTorus F, b ≠ 1 → ∀ k ∈ unipotent F, b * k = k * b → k = 1 := by
  intro b hb hb1 k hk hbk
  obtain ⟨a, rfl⟩ := (mem_splitTorus_iff_exists b).mp hb
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists k).mp hk
  have ha : (a : F) ^ 2 ≠ 1 := fun h => hb1 ((mk_diag_eq_one_iff a).mpr h)
  have hconj : mk (diag a) * mk (unip t) * (mk (diag a))⁻¹ = mk (unip t) := by
    rw [hbk, mul_inv_cancel_right]
  rw [mk_conj, diag_conj_unip, mk_unip_eq_mk_unip_iff h2] at hconj
  have h3 : ((a : F) ^ 2 - 1) * t = 0 := by linear_combination hconj
  have ht : t = 0 := (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha)
  rw [ht]
  exact (mk_unip_eq_one_iff h2 0).mpr rfl

private theorem natCard_unipotent [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (unipotent F) = Nat.card F := by
  have := Fintype.ofFinite F
  rw [card_unipotent h2, Nat.card_eq_fintype_card]

private theorem natCard_splitTorus [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (splitTorus F) * 2 = Nat.card F - 1 := by
  have := Fintype.ofFinite F
  rw [card_splitTorus h2, Nat.card_eq_fintype_card]

private theorem psl2_acts_trivially [Finite F] (hq : 9 ≤ Nat.card F) (hodd : Odd (Nat.card F))
    {A : Type} [instA : CommGroup A] [Finite A] (hAq : Nat.Coprime (Nat.card A) (Nat.card F))
    {a₁ a₂ a₃ : A} (hgen : closure ({a₁, a₂, a₃} : Set A) = ⊤) (ρ : PSL(2, F) →* MulAut A) :
    ∀ g, ρ g = 1 := by
  have h2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    refine Ring.two_ne_zero fun hc => ?_
    have h0 := FiniteField.even_card_iff_char_two.mp hc
    rw [← Nat.card_eq_fintype_card] at h0
    exact absurd (Nat.odd_iff.mp hodd) (by omega)
  by_contra hne
  have hne' : ∃ g, ρ g ≠ 1 := not_forall.mp hne
  have hsimple : IsSimpleGroup (PSL(2, F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hker : ρ.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · obtain ⟨g, hg⟩ := hne'
      exact absurd (by rw [← MonoidHom.mem_ker, h]; exact mem_top g) hg
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
  have hkX : mk (unip (1 : F)) ∈ unipotent F := mk_unip_mem_unipotent 1
  have hk1 : mk (unip (1 : F)) ≠ 1 := fun h => one_ne_zero ((mk_unip_eq_one_iff h2 1).mp h)
  have hρk : ρ (mk (unip (1 : F))) ≠ 1 := fun h => hk1 (hinj (h.trans (map_one ρ).symm))
  have hkq : (mk (unip (1 : F))) ^ Nat.card F = 1 := by
    have h1 : orderOf (mk (unip (1 : F))) ∣ Nat.card (unipotent F) :=
      Subgroup.orderOf_dvd_natCard _ hkX
    rw [natCard_unipotent h2] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hσq : (ρ (mk (unip (1 : F)))) ^ Nat.card F = 1 := by rw [← map_pow, hkq, map_one]
  have hmove : ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card A ∧ ∃ a : A, a ^ r = 1 ∧
      ρ (mk (unip (1 : F))) a ≠ a := by
    by_contra hcon
    refine hρk (MulEquiv.ext (fixed_of_torsion_fixed hAq _ hσq fun r hr hrA a ha => ?_))
    by_contra hne''
    exact hcon ⟨r, hr, hrA, a, ha, hne''⟩
  obtain ⟨r, hr, hrA, a, ha, hρa⟩ := hmove
  have : Fact r.Prime := ⟨hr⟩
  have hrq : ¬ r ∣ Nat.card (unipotent F) := by
    rw [natCard_unipotent h2]
    intro hrF
    have h1 : r ∣ Nat.gcd (Nat.card A) (Nat.card F) := Nat.dvd_gcd hrA hrF
    rw [hAq] at h1
    exact hr.one_lt.ne' (Nat.dvd_one.mp h1)
  have hle := card_le_three_of_torsion_move ρ r (unipotent F) (splitTorus F)
    (fun x hx y hy => unipotent_mul_comm hx hy) hrq splitTorus_le_normalizer_unipotent
    (splitTorus_fixedPointFree h2) hgen ⟨_, hkX, a, ha, hρa⟩
  have hT := natCard_splitTorus h2
  omega

end PSL

private abbrev commGroupOfComm {A : Type} [Group A] (h : ∀ a b : A, a * b = b * a) :
    CommGroup A :=
  { ‹Group A› with mul_comm := h }

open Subgroup in
theorem L2_acts_trivially {I A : Type} [Group I] [Finite I] [Group A] [Finite A] {q : ℕ}
    (hI : CFSG.GH74.GLS.IVK.IsL2 I (fun r => r = q)) (hq : 9 ≤ q) (hqodd : Odd q)
    (hAcomm : ∀ a b : A, a * b = b * a) (hAodd : Odd (Nat.card A))
    (hAq : Nat.Coprime (Nat.card A) q)
    (a₁ a₂ a₃ : A) (hgen : closure ({a₁, a₂, a₃} : Set A) = ⊤)
    (ρ : I →* MulAut A) : ∀ i : I, ρ i = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hI
  have hF' : Nat.card F = q := hF
  have _ := hAodd
  let e' : I ≃* CFSG.GorensteinWalter.PSL2 F := e.trans (CFSG.GH74.GLS.IVK.L2.equivPSL F)
  have key := psl2_acts_trivially (F := F) (A := A) (instA := commGroupOfComm hAcomm)
    (by omega) (by rwa [hF']) (by rwa [hF']) hgen (ρ.comp e'.symm.toMonoidHom)
  intro i
  have h := key (e' i)
  simpa using h

end CFSG.GH74.GLS.SP.Local
