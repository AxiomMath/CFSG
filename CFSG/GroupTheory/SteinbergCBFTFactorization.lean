module

public import CFSG.GroupTheory.SteinbergCBFTGeneration

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.HallHigman

section Factorization

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

open scoped Pointwise

@[expose] def IsFactorized (M N H : Subgroup G) : Prop :=
  (H : Set G) = ((H ⊓ M : Subgroup G) : Set G) * ((H ⊓ N : Subgroup G) : Set G)

omit [Finite G] hp in
theorem isFactorized_iff {M N H : Subgroup G} :
    IsFactorized M N H ↔ ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ n ∈ H ⊓ N, m * n = x := by
  constructor
  · intro h x hx
    have hx' : x ∈ ((H ⊓ M : Subgroup G) : Set G) * ((H ⊓ N : Subgroup G) : Set G) := h ▸ hx
    obtain ⟨m, hm, n, hn, rfl⟩ := hx'
    exact ⟨m, hm, n, hn, rfl⟩
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨m, hm, n, hn, rfl⟩ := h x hx
      exact Set.mul_mem_mul hm hn
    · rintro _ ⟨m, hm, n, hn, rfl⟩
      exact mul_mem (mem_inf.1 hm).1 (mem_inf.1 hn).1

omit [Finite G] hp in
theorem isFactorized_of_sup {M N R K₀ K L : Subgroup G} (hLK₀ : L ≤ normalizer (K₀ : Set G))
    (hK₀K : K₀ ≤ K) (hKR : K ≤ R) (hLR : L ≤ R) (hR : R = K₀ ⊔ L) (hK : IsFactorized M N K)
    (hL : IsFactorized M N L) : IsFactorized M N R := by
  rw [isFactorized_iff] at hK hL ⊢
  intro r hr
  have hr' : r ∈ ((K₀ ⊔ L : Subgroup G) : Set G) := hR ▸ hr
  rw [coe_mul_of_right_le_normalizer_left K₀ L hLK₀] at hr'
  obtain ⟨k, hk, l, hl, rfl⟩ := hr'
  obtain ⟨m, hm, n, hn, rfl⟩ := hL l hl
  obtain ⟨hmL, hmM⟩ := mem_inf.1 hm
  obtain ⟨hnL, hnN⟩ := mem_inf.1 hn
  have hkm : m⁻¹ * k * m ∈ K₀ := by
    have := (mem_normalizer_iff.1 (hLK₀ (inv_mem hmL)) k).1 hk
    simpa using this
  obtain ⟨m₁, hm₁, n₁, hn₁, he⟩ := hK _ (hK₀K hkm)
  obtain ⟨hm₁K, hm₁M⟩ := mem_inf.1 hm₁
  obtain ⟨hn₁K, hn₁N⟩ := mem_inf.1 hn₁
  refine ⟨m * m₁, mem_inf.2 ⟨mul_mem (hLR hmL) (hKR hm₁K), mul_mem hmM hm₁M⟩, n₁ * n,
    mem_inf.2 ⟨mul_mem (hKR hn₁K) (hLR hnL), mul_mem hn₁N hnN⟩, ?_⟩
  calc m * m₁ * (n₁ * n) = m * (m₁ * n₁) * n := by group
    _ = m * (m⁻¹ * k * m) * n := by rw [he]
    _ = k * (m * n) := by group

omit [Finite G] hp in
theorem le_normalizer_map_subtype {R : Subgroup G} (T : Subgroup R) [T.Normal] :
    R ≤ normalizer ((T.map R.subtype : Subgroup G) : Set G) := by
  intro y hy
  have hmem : (⟨y, hy⟩ : R) ∈ normalizer (T : Set R) := by
    rw [normalizer_eq_top]
    exact mem_top _
  exact le_normalizer_map R.subtype ⟨⟨y, hy⟩, hmem, rfl⟩

theorem isFactorized_of_primeFactors_subset (hG : IsPiSeparable {r : Nat.Primes | r.val = p} G)
    (P : Sylow p G) {M N : Subgroup G} (hS : ∀ H ∈ ftS p (P : Subgroup G), IsFactorized M N H)
    {q : ℕ} (n : ℕ) :
    ∀ R : Subgroup G, Nat.card R = n → (P : Subgroup G) ≤ R →
      (Nat.card R).primeFactors ⊆ {p, q} → IsFactorized M N R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hRn hPR hRpq
  by_cases hlen : pLength p R ≤ 2
  · exact hS R ⟨hPR, hlen, (Finset.card_le_card hRpq).trans Finset.card_le_two⟩
  have hRsep : IsPiSeparable {r : Nat.Primes | r.val = p} R := hG.subgroup R
  have hprimes : ∀ H : Subgroup G, H ≤ R → (Nat.card H).primeFactors ⊆ {p, q} := fun H hH =>
    (Nat.primeFactors_mono (card_dvd_of_le hH) Nat.card_pos.ne').trans hRpq
  set PR : Sylow p R := P.subtype hPR with hPRdef
  have hPRmap : (PR : Subgroup R).map R.subtype = P := by
    rw [hPRdef, Sylow.coe_subtype, subgroupOf_map_subtype, inf_eq_left.2 hPR]
  have hT₂n : (corePP' p R).Normal := coreAbove_normal _ _
  have hT₃n : (corePP'P p R).Normal := coreAbove_normal _ _
  have hT₂top : corePP' p R ≠ ⊤ := fun h =>
    hlen (pLength_le_of_hasPSeries (hasPSeries_of_corePP'_eq_top h))
  set L := normalizer (((PR : Subgroup R) ⊓ corePP'P p R : Subgroup R) : Set R) with hLdef
  have hLtop : L ≠ ⊤ := fun h => hT₂top (corePP'_eq_top_of_normal hRsep PR h)
  have hPL : (PR : Subgroup R) ≤ L :=
    le_normalizer_inf_of_le le_normalizer (fun x _ =>
      (normalizer_eq_top (H := corePP'P p R)).symm ▸ mem_top x)
  set K := (PR : Subgroup R) ⊔ corePP' p R with hKdef
  have hKfac : IsFactorized M N (K.map R.subtype) := by
    refine hS _ (mem_ftS_of (q := q) ?_ ((hasPSeries_sup_corePP' PR).of_mulEquiv
      (K.equivMapOfInjective _ R.subtype_injective)) (hprimes _ (map_subtype_le _)))
    rw [← hPRmap]
    exact map_mono le_sup_left
  have hLfac : IsFactorized M N (L.map R.subtype) := by
    refine ih _ ?_ _ rfl ?_ (hprimes _ (map_subtype_le _))
    · rw [card_map_of_injective R.subtype_injective, ← hRn, ← card_top (G := R)]
      exact card_lt_of_lt (lt_top_iff_ne_top.2 hLtop)
    · rw [← hPRmap]
      exact map_mono hPL
  refine isFactorized_of_sup (K₀ := (corePP' p R).map R.subtype) (K := K.map R.subtype)
    ((map_subtype_le _).trans (le_normalizer_map_subtype _)) (map_mono le_sup_right)
    (map_subtype_le _) (map_subtype_le _) ?_ hKfac hLfac
  rw [← Subgroup.map_sup, corePP'_sup_normalizer PR, ← MonoidHom.range_eq_map, range_subtype]

theorem exists_sylow_normalized {W A : Subgroup G} (hA : IsPGroup p A)
    (hAW : A ≤ normalizer (W : Set G)) (hW : ¬ p ∣ Nat.card W) (q : ℕ) [Fact q.Prime] :
    ∃ S : Sylow q W, A ≤ normalizer (((S : Subgroup W).map W.subtype : Subgroup G) : Set G) := by
  let _ : MulDistribMulAction A W := Subgroup.conjMulDistribMulActionOfLeNormalizer A W hAW
  have hcard : ¬ p ∣ Nat.card (Sylow q W) := fun h =>
    hW (h.trans ((default : Sylow q W).card_dvd_index.trans (index_dvd_card _)))
  obtain ⟨S, hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q W) hcard
  refine ⟨S, fun a ha => mem_normalizer_iff.2 fun x => ?_⟩
  have hfix : (⟨a, ha⟩ : A) • (S : Subgroup W) = S := by
    rw [← Sylow.pointwise_smul_def]
    exact congrArg Sylow.toSubgroup (hS ⟨a, ha⟩)
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (⟨a, ha⟩ : A) • s ∈ (S : Subgroup W) :=
      hfix ▸ Subgroup.smul_mem_pointwise_smul s _ _ hs
    exact ⟨_, hs', rfl⟩
  · rintro ⟨s', hs', hs'x⟩
    rw [← hfix] at hs'
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hs'
    refine ⟨s, hs, ?_⟩
    have h1 : a * (s : G) * a⁻¹ = a * x * a⁻¹ := hs'x
    simpa using h1

omit hp in
theorem lt_inf_normalizer_of_lt {q : ℕ} [Fact q.Prime] {Q S : Subgroup G} (hS : IsPGroup q S)
    (hQS : Q < S) : Q < S ⊓ normalizer (Q : Set G) := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : Q.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hQS.ne (le_antisymm hQS.le (subgroupOf_eq_top.1 h))
  obtain ⟨x, hxN, hxQ⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hQS.le] at hxN
  refine lt_of_le_of_ne (le_inf hQS.le le_normalizer) fun h => hxQ ?_
  have hx : (x : G) ∈ S ⊓ normalizer (Q : Set G) := mem_inf.2 ⟨x.2, hxN⟩
  rw [← h] at hx
  exact hx

theorem exists_sylow_ge_normalized {q : ℕ} [Fact q.Prime] {W A Q₁ : Subgroup G}
    (hA : IsPGroup p A) (hAW : A ≤ normalizer (W : Set G)) (hW : ¬ p ∣ Nat.card W)
    (hQ₁W : Q₁ ≤ W) (hQ₁ : IsPGroup q Q₁) (hAQ₁ : A ≤ normalizer (Q₁ : Set G)) :
    ∃ Q₂ : Subgroup G, Q₁ ≤ Q₂ ∧ Q₂ ≤ W ∧ IsPGroup q Q₂ ∧ A ≤ normalizer (Q₂ : Set G) ∧
      ¬ q ∣ Q₂.relIndex W := by
  let 𝒯 : Set (Subgroup G) := {Q | Q₁ ≤ Q ∧ Q ≤ W ∧ IsPGroup q Q ∧ A ≤ normalizer (Q : Set G)}
  obtain ⟨Q₂, -, hmax⟩ := 𝒯.toFinite.exists_le_maximal (show Q₁ ∈ 𝒯 from ⟨le_rfl, hQ₁W, hQ₁, hAQ₁⟩)
  obtain ⟨hQ₁₂, hQ₂W, hQ₂, hAQ₂⟩ := hmax.prop
  refine ⟨Q₂, hQ₁₂, hQ₂W, hQ₂, hAQ₂, ?_⟩
  set W' := W ⊓ normalizer (Q₂ : Set G) with hW'def
  have hAW' : A ≤ normalizer (W' : Set G) :=
    le_normalizer_inf_of_le hAW (hAQ₂.trans le_normalizer)
  have hW' : ¬ p ∣ Nat.card W' := fun h => hW (h.trans (card_dvd_of_le inf_le_left))
  obtain ⟨S', hS'⟩ := exists_sylow_normalized hA hAW' hW' q
  have hQ₂W' : Q₂ ≤ W' := le_inf hQ₂W le_normalizer
  have hQ₂S' : Q₂ ≤ (S' : Subgroup W').map W'.subtype := by
    have hn : (Q₂.subgroupOf W').Normal := normal_subgroupOf_of_le_normalizer inf_le_right
    have hQ₂p' : IsPGroup q (Q₂.subgroupOf W') := hQ₂.comap_subtype
    have hle : Q₂.subgroupOf W' ≤ S' := hQ₂p'.le_sylow_of_normal S'
    have h2 : (Q₂.subgroupOf W').map W'.subtype = Q₂ := by
      rw [subgroupOf_map_subtype, inf_eq_left.2 hQ₂W']
    calc Q₂ = (Q₂.subgroupOf W').map W'.subtype := h2.symm
      _ ≤ _ := map_mono hle
  have hS'T : (S' : Subgroup W').map W'.subtype ∈ 𝒯 :=
    ⟨hQ₁₂.trans hQ₂S', (map_subtype_le _).trans inf_le_left, S'.isPGroup'.map _, hS'⟩
  have heq : (S' : Subgroup W').map W'.subtype = Q₂ :=
    le_antisymm (hmax.le_of_ge hS'T hQ₂S') hQ₂S'
  have hsyl : ¬ q ∣ Q₂.relIndex W' := by
    have h3 : ((S' : Subgroup W').map W'.subtype).subgroupOf W' = S' :=
      comap_map_eq_self_of_injective W'.subtype_injective _
    rw [← heq, relIndex, h3]
    exact S'.not_dvd_index
  obtain ⟨S₀, hS₀⟩ := (hQ₂.comap_subtype (K := W)).exists_le_sylow
  have hQ₂S : Q₂ ≤ (S₀ : Subgroup W).map W.subtype := by
    have h2 : (Q₂.subgroupOf W).map W.subtype = Q₂ := by
      rw [subgroupOf_map_subtype, inf_eq_left.2 hQ₂W]
    calc Q₂ = (Q₂.subgroupOf W).map W.subtype := h2.symm
      _ ≤ _ := map_mono hS₀
  have hSp : IsPGroup q ↥((S₀ : Subgroup W).map W.subtype) := S₀.isPGroup'.map _
  have hSN : (S₀ : Subgroup W).map W.subtype ⊓ normalizer (Q₂ : Set G) ≤ Q₂ :=
    le_of_isPGroup_of_not_dvd_relIndex hQ₂ hQ₂W' hsyl (hSp.to_le inf_le_left)
      (inf_le_inf_right _ (map_subtype_le _)) inf_le_right
  have hQ₂eq : Q₂ = (S₀ : Subgroup W).map W.subtype := by
    by_contra hne
    exact (lt_irrefl Q₂) ((lt_inf_normalizer_of_lt hSp (lt_of_le_of_ne hQ₂S hne)).trans_le hSN)
  have h4 : ((S₀ : Subgroup W).map W.subtype).subgroupOf W = S₀ :=
    comap_map_eq_self_of_injective W.subtype_injective _
  rw [hQ₂eq, relIndex, h4]
  exact S₀.not_dvd_index

omit [Finite G] hp in
theorem card_setMul_mul_card_inf (A B : Subgroup G) :
    Nat.card ↥((A : Set G) * (B : Set G)) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set G)
  have himg : Nat.card ↥((A : Set G).image ((↑) : G → G ⧸ B)) = B.relIndex A := by
    have horb : MulAction.orbit ↥A ((1 : G) : G ⧸ B) = (A : Set G).image ((↑) : G → G ⧸ B) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : G), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer ↥A ((1 : G) : G ⧸ B) = B.subgroupOf A := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : G) : G ⧸ B)) = ((a : G) : G ⧸ B) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        simpa using B.inv_mem h
      · intro h
        simpa using B.inv_mem h
    have := MulAction.index_stabilizer ↥A ((1 : G) : G ⧸ B)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm B A] at h2
  rw [h1, himg]
  calc Nat.card ↥B * B.relIndex A * Nat.card ↥(A ⊓ B)
      = Nat.card ↥B * (B.relIndex A * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h2]; ring

omit [Finite G] hp in
theorem card_mul_card_inf_of_isFactorized {M N R : Subgroup G} (h : IsFactorized M N R) :
    Nat.card R * Nat.card ↥(R ⊓ M ⊓ N) = Nat.card ↥(R ⊓ M) * Nat.card ↥(R ⊓ N) := by
  have h1 := card_setMul_mul_card_inf (R ⊓ M) (R ⊓ N)
  rw [← inf_inf_distrib_left, ← inf_assoc] at h1
  have h2 : Nat.card ↥(((R ⊓ M : Subgroup G) : Set G) * ((R ⊓ N : Subgroup G) : Set G)) =
      Nat.card R := by
    rw [← h]
    rfl
  rw [h2] at h1
  exact h1

omit hp in
theorem card_eq_card_map_mul_card_inf {X' : Type*} [Group X'] (f : G →* X') (H : Subgroup G) :
    Nat.card H = Nat.card (H.map f) * Nat.card ↥(f.ker ⊓ H) := by
  rw [CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (inf_le_right : f.ker ⊓ H ≤ H),
    inf_relIndex_right, relIndex_ker, mul_comm]

omit hp in
theorem factorization_le_of_le {q : ℕ} {H K : Subgroup G} (h : H ≤ K) :
    (Nat.card H).factorization q ≤ (Nat.card K).factorization q :=
  (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 (card_dvd_of_le h) q

omit hp in
theorem factorization_eq_of_not_dvd_relIndex {q : ℕ} {H K : Subgroup G}
    (h : H ≤ K) (hn : ¬ q ∣ H.relIndex K) :
    (Nat.card K).factorization q = (Nat.card H).factorization q := by
  have hr : H.relIndex K ≠ 0 := index_ne_zero_of_finite
  rw [CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex h,
    Nat.factorization_mul Nat.card_pos.ne' hr, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn, add_zero]

omit hp in
theorem primeFactors_sup_subset {P Q : Subgroup G} (h : P ≤ normalizer (Q : Set G)) {r s : ℕ}
    (hP : IsPGroup r P) (hQ : IsPGroup s Q) (hr : r.Prime) (hs : s.Prime) :
    (Nat.card ↥(P ⊔ Q)).primeFactors ⊆ {r, s} := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact s.Prime := ⟨hs⟩
  have h1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer h
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  obtain ⟨b, hb⟩ := hQ.exists_card_eq
  intro t ht
  have htp := Nat.prime_of_mem_primeFactors ht
  have hdvd : t ∣ r ^ a * s ^ b := by
    rw [← ha, ← hb, ← h1]
    exact (Nat.dvd_of_mem_primeFactors ht).trans (dvd_mul_right _ _)
  rcases (Nat.Prime.dvd_mul htp).1 hdvd with h2 | h2
  · rw [Finset.mem_insert]
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq htp hr).1 (htp.dvd_of_dvd_pow h2))
  · rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq htp hs).1 (htp.dvd_of_dvd_pow h2))

theorem factorization_le_of_normal_of_not_dvd {q : ℕ} [hq : Fact q.Prime] (hpq : q ≠ p)
    (P : Sylow p G) {M N N₀ : Subgroup G} [hN₀n : N₀.Normal] (hN₀ : ¬ p ∣ Nat.card N₀)
    (hPM : (P : Subgroup G) ≤ M) (hPN : (P : Subgroup G) ≤ N)
    (hfac : ∀ R : Subgroup G, (P : Subgroup G) ≤ R → (Nat.card R).primeFactors ⊆ {p, q} →
      IsFactorized M N R) :
    (Nat.card N₀).factorization q + (Nat.card ↥(M ⊓ N ⊓ N₀)).factorization q ≤
      (Nat.card ↥(M ⊓ N₀)).factorization q + (Nat.card ↥(N ⊓ N₀)).factorization q := by
  have hPp : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hPD₀ : (P : Subgroup G) ≤ normalizer ((M ⊓ N ⊓ N₀ : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le (le_normalizer_inf_of_le (hPM.trans le_normalizer)
      (hPN.trans le_normalizer)) le_normalizer_of_normal
  have hD₀ : ¬ p ∣ Nat.card ↥(M ⊓ N ⊓ N₀) := fun h => hN₀ (h.trans (card_dvd_of_le inf_le_right))
  obtain ⟨S₁, hS₁⟩ := exists_sylow_normalized hPp hPD₀ hD₀ q
  have hQ₁D₀ : (S₁ : Subgroup ↥(M ⊓ N ⊓ N₀)).map (M ⊓ N ⊓ N₀).subtype ≤ M ⊓ N ⊓ N₀ :=
    map_subtype_le _
  have hvQ₁ : (Nat.card ↥(M ⊓ N ⊓ N₀)).factorization q =
      (Nat.card ↥((S₁ : Subgroup ↥(M ⊓ N ⊓ N₀)).map (M ⊓ N ⊓ N₀).subtype)).factorization q := by
    refine factorization_eq_of_not_dvd_relIndex hQ₁D₀ ?_
    have h3 : ((S₁ : Subgroup ↥(M ⊓ N ⊓ N₀)).map (M ⊓ N ⊓ N₀).subtype).subgroupOf
        (M ⊓ N ⊓ N₀) = S₁ := comap_map_eq_self_of_injective (M ⊓ N ⊓ N₀).subtype_injective _
    rw [relIndex, h3]
    exact S₁.not_dvd_index
  obtain ⟨Q₂, hQ₁₂, hQ₂N₀, hQ₂p, hPQ₂, hQ₂syl⟩ := exists_sylow_ge_normalized hPp
    le_normalizer_of_normal hN₀ (hQ₁D₀.trans inf_le_right) (S₁.isPGroup'.map _) hS₁
  have hRQ₂ : (P : Subgroup G) ⊔ Q₂ ≤ normalizer (Q₂ : Set G) := sup_le hPQ₂ le_normalizer
  have hqP : ¬ q ∣ Nat.card (P : Subgroup G) := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [hk]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 (hq.out.dvd_of_dvd_pow h))
  have hidx : Q₂.relIndex ((P : Subgroup G) ⊔ Q₂) ∣ Nat.card (P : Subgroup G) := by
    rw [CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hPQ₂]
    exact relIndex_dvd_card _ _
  have hqH : ∀ H : Subgroup G, H ≤ (P : Subgroup G) ⊔ Q₂ →
      (Nat.card H).factorization q = (Nat.card ↥(Q₂ ⊓ H)).factorization q := by
    intro H hH
    refine factorization_eq_of_not_dvd_relIndex inf_le_right fun hdvd => hqP ?_
    rw [inf_relIndex_right, ← CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer
      (hH.trans hRQ₂)] at hdvd
    refine hdvd.trans ((Dvd.intro _ (relIndex_mul_relIndex Q₂ (H ⊔ Q₂) _ le_sup_right
      (sup_le hH le_sup_right))).trans hidx)
  have hfacR := card_mul_card_inf_of_isFactorized (hfac _ le_sup_left
    (primeFactors_sup_subset hPQ₂ hPp hQ₂p hp.out hq.out))
  have hv : (Nat.card ↥((P : Subgroup G) ⊔ Q₂) *
      Nat.card ↥(((P : Subgroup G) ⊔ Q₂) ⊓ M ⊓ N)).factorization q =
      (Nat.card ↥(((P : Subgroup G) ⊔ Q₂) ⊓ M) *
        Nat.card ↥(((P : Subgroup G) ⊔ Q₂) ⊓ N)).factorization q := by
    rw [hfacR]
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Finsupp.add_apply] at hv
  have hvR : (Nat.card ↥((P : Subgroup G) ⊔ Q₂)).factorization q =
      (Nat.card N₀).factorization q := by
    rw [hqH _ le_rfl, inf_eq_left.2 le_sup_right]
    exact (factorization_eq_of_not_dvd_relIndex hQ₂N₀ hQ₂syl).symm
  have hvM : (Nat.card ↥(((P : Subgroup G) ⊔ Q₂) ⊓ M)).factorization q ≤
      (Nat.card ↥(M ⊓ N₀)).factorization q := by
    rw [hqH _ inf_le_left]
    exact factorization_le_of_le
      (le_inf (inf_le_right.trans inf_le_right) (inf_le_left.trans hQ₂N₀))
  have hvN : (Nat.card ↥(((P : Subgroup G) ⊔ Q₂) ⊓ N)).factorization q ≤
      (Nat.card ↥(N ⊓ N₀)).factorization q := by
    rw [hqH _ inf_le_left]
    exact factorization_le_of_le
      (le_inf (inf_le_right.trans inf_le_right) (inf_le_left.trans hQ₂N₀))
  have hvD : (Nat.card ↥((S₁ : Subgroup ↥(M ⊓ N ⊓ N₀)).map (M ⊓ N ⊓ N₀).subtype)).factorization q ≤
      (Nat.card ↥(((P : Subgroup G) ⊔ Q₂) ⊓ M ⊓ N)).factorization q := by
    refine factorization_le_of_le (le_inf (le_inf (hQ₁₂.trans le_sup_right) ?_) ?_)
    · exact hQ₁D₀.trans (inf_le_left.trans inf_le_left)
    · exact hQ₁D₀.trans (inf_le_left.trans inf_le_right)
  omega

omit hp in
theorem factorization_eq_zero_of_isPGroup {q : ℕ} (hq : q.Prime) (hpq : q ≠ p) {H : Subgroup G}
    (hH : IsPGroup p H) [Fact p.Prime] : (Nat.card H).factorization q = 0 := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  rw [hk]
  exact Nat.factorization_eq_zero_of_not_dvd fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq hq Fact.out).1 (hq.dvd_of_dvd_pow h))

end Factorization

end CFSG.GroupTheory.FT63ChII
