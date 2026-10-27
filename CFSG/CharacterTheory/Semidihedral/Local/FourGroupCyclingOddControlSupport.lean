module

public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotientsSupport

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

variable {G : Type*} [Group G]

theorem mem_normalizer_map_of_normal {N : Subgroup G} (L : Subgroup N) [L.Normal] {m : G}
    (hm : m ∈ N) : m ∈ Subgroup.normalizer ((L.map N.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := L) N.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h hm

theorem mul_comm_of_mul_mul_inv_mul_inv_eq_one {M : Type*} [Group M] {x a : M}
    (h : x * a * x⁻¹ * a⁻¹ = 1) : x * a = a * x :=
  calc x * a = (x * a * x⁻¹ * a⁻¹) * (a * x) := by group
    _ = a * x := by rw [h, one_mul]

theorem commutator_mem_of_mem_center {A : Subgroup G} (K : Subgroup A) [K.Normal] {t : G}
    (htA : t ∈ A)
    (ht : (QuotientGroup.mk (⟨t, htA⟩ : A) : A ⧸ K) ∈ Subgroup.center (A ⧸ K)) {a : G}
    (ha : a ∈ A) : t * a * t⁻¹ * a⁻¹ ∈ K.map A.subtype := by
  have h := Subgroup.mem_center_iff.mp ht (QuotientGroup.mk (⟨a, ha⟩ : A))
  have hmem : (⟨t, htA⟩ * ⟨a, ha⟩ * (⟨t, htA⟩ : A)⁻¹ * (⟨a, ha⟩ : A)⁻¹ : A) ∈ K := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← h]
    group
  exact ⟨_, hmem, rfl⟩

theorem conj_commutator_mem {A K : Subgroup G} {g t : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (ht : ∀ a ∈ A, t * a * t⁻¹ * a⁻¹ ∈ K) {a : G} (ha : a ∈ A) :
    g * t * g⁻¹ * a * (g * t * g⁻¹)⁻¹ * a⁻¹ ∈ K := by
  have ha' : g⁻¹ * a * g ∈ A := (Subgroup.mem_normalizer_iff''.mp hgA a).mp ha
  have h1 := (Subgroup.mem_normalizer_iff.mp hgK _).mp (ht _ ha')
  convert h1 using 1
  group

theorem mul_commutator_mem {A K : Subgroup G} {v w : G}
    (hv : v ∈ Subgroup.normalizer (K : Set G)) (hvK : ∀ a ∈ A, v * a * v⁻¹ * a⁻¹ ∈ K)
    (hwK : ∀ a ∈ A, w * a * w⁻¹ * a⁻¹ ∈ K) {a : G} (ha : a ∈ A) :
    v * w * a * (v * w)⁻¹ * a⁻¹ ∈ K := by
  have h1 := (Subgroup.mem_normalizer_iff.mp hv _).mp (hwK a ha)
  convert K.mul_mem h1 (hvK a ha) using 1
  group

theorem kleinFour_mem_cases (V : Subgroup G) [IsKleinFour V] {x y v : G} (hx : x ∈ V)
    (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) (hv : v ∈ V) :
    v = x * y ∨ v = x ∨ v = y ∨ v = 1 := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
  let _ : Fintype V := Fintype.ofFinite V
  have hmem := Finset.mem_univ (⟨v, hv⟩ : V)
  rw [← IsKleinFour.eq_finset_univ (x := (⟨x, hx⟩ : V)) (y := ⟨y, hy⟩)
    (fun h => hx1 (congrArg Subtype.val h)) (fun h => hy1 (congrArg Subtype.val h))
    (fun h => hxy (congrArg Subtype.val h))] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

section Core

variable [Finite G]

theorem conj_mem_map_pPrimeCore (p : ℕ) [Fact p.Prime] {A : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (A : Set G)) {x : G}
    (hx : x ∈ (pPrimeCore p A).map A.subtype) :
    h * x * h⁻¹ ∈ (pPrimeCore p A).map A.subtype := by
  have hmem : ∀ a : A, h * (a : G) * h⁻¹ ∈ A := fun a =>
    (Subgroup.mem_normalizer_iff.mp hh a).mp a.2
  let φ : A →* A :=
    { toFun := fun a => ⟨h * a * h⁻¹, hmem a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hinj : Function.Injective φ := fun a b hab => Subtype.ext (by
    have := congrArg Subtype.val hab
    simpa [φ] using this)
  let e : A ≃* A := MulEquiv.ofBijective φ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  obtain ⟨a, ha, rfl⟩ := hx
  have hea : e a ∈ pPrimeCore p A := by
    rw [← pPrimeCore_map_iso p e]
    exact ⟨a, ha, rfl⟩
  exact ⟨e a, hea, rfl⟩

theorem mem_normalizer_map_pPrimeCore (p : ℕ) [Fact p.Prime] {A : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (A : Set G)) :
    h ∈ Subgroup.normalizer (((pPrimeCore p A).map A.subtype : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨conj_mem_map_pPrimeCore p hh, fun hx => ?_⟩
  have := conj_mem_map_pPrimeCore p (Subgroup.inv_mem _ hh) hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem le_map_pPrimeCore_of_le_normalizer (p : ℕ) [Fact p.Prime] {H J : Subgroup G}
    (hJH : J ≤ H) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (hJ : Nat.Coprime p (Nat.card J)) : J ≤ (pPrimeCore p H).map H.subtype := by
  have hn : (J.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mpr hHJ
  have hc : Nat.Coprime p (Nat.card (J.subgroupOf H)) := by
    rwa [card_subgroupOf_eq, inf_eq_left.mpr hJH]
  have hle : J.subgroupOf H ≤ pPrimeCore p H := le_sSup ⟨hn, hc⟩
  have := Subgroup.map_mono (f := H.subtype) hle
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJH] at this

theorem pPrimeCore_quotient_self_eq_bot (E : Type*) [Group E] [Finite E] (p : ℕ)
    [Fact p.Prime] : pPrimeCore p (E ⧸ pPrimeCore p E) = ⊥ := by
  rw [← pPrimeCore_map_eq_of_coprime_ker p (QuotientGroup.mk' (pPrimeCore p E))
    (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pPrimeCore_coprime_card), QuotientGroup.map_mk'_self]

theorem sylow_eq_of_commutator_mem {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {A V : Subgroup G} (hVA : V ≤ A) [IsKleinFour V]
    (hV : ∀ v ∈ V, ∀ a ∈ A, v * a * v⁻¹ * a⁻¹ ∈ (pPrimeCore 2 A).map A.subtype)
    (T : Sylow 2 A) (hVT : V.subgroupOf A ≤ T) : (T : Subgroup A) = V.subgroupOf A := by
  have hTG2 : IsPGroup 2 ((T : Subgroup A).map A.subtype) := T.isPGroup'.map A.subtype
  obtain ⟨S', hS'⟩ := hTG2.exists_le_sylow
  have hVTG : V ≤ (T : Subgroup A).map A.subtype := fun v hv =>
    ⟨⟨v, hVA hv⟩, hVT (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  obtain ⟨-, -, hSC⟩ := kleinFour_sylow_facts hn S' (f.trans (Sylow.equiv S S')) V
    (hVTG.trans hS')
  have hcop : Nat.Coprime (Nat.card ((T : Subgroup A).map A.subtype))
      (Nat.card ((pPrimeCore 2 A).map A.subtype)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTG2
    rw [hk, Subgroup.card_map_of_injective A.subtype_injective]
    exact Nat.Coprime.pow_left k pPrimeCore_coprime_card
  have hdisj := Subgroup.disjoint_of_coprime_natCard hcop
  refine le_antisymm (fun x hx => ?_) hVT
  rw [Subgroup.mem_subgroupOf]
  refine hSC ⟨hS' ⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hvT : (⟨v, hVA hv⟩ : A) ∈ T := hVT (Subgroup.mem_subgroupOf.mpr hv)
  have hc : v * x * v⁻¹ * (x : G)⁻¹ ∈ (T : Subgroup A).map A.subtype :=
    ⟨⟨v, hVA hv⟩ * x * (⟨v, hVA hv⟩ : A)⁻¹ * x⁻¹,
      mul_mem (mul_mem (mul_mem hvT hx) (inv_mem hvT)) (inv_mem hx), rfl⟩
  exact mul_comm_of_mul_mul_inv_mul_inv_eq_one (Subgroup.disjoint_def.mp hdisj hc (hV v hv x x.2))

theorem map_pPrimeCore_sup_eq {A V : Subgroup G} (hVA : V ≤ A) (T : Sylow 2 A)
    (hT : (T : Subgroup A) = V.subgroupOf A)
    (hV : ∀ v ∈ V, ∀ a ∈ A, v * a * v⁻¹ * a⁻¹ ∈ (pPrimeCore 2 A).map A.subtype) :
    (pPrimeCore 2 A).map A.subtype ⊔ V = A := by
  have hq : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 A)) :=
    QuotientGroup.mk'_surjective _
  let P := T.mapSurjective hq
  have hPc : ∀ y ∈ (P : Subgroup (A ⧸ pPrimeCore 2 A)),
      y ∈ Subgroup.center (A ⧸ pPrimeCore 2 A) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨a, rfl⟩ := hq z
    have hxV : (x : G) ∈ V := by
      rw [hT] at hx
      exact hx
    have hc : x * a * x⁻¹ * a⁻¹ ∈ pPrimeCore 2 A :=
      (Subgroup.mem_map_iff_mem A.subtype_injective).mp (hV x hxV a a.2)
    have h1 : QuotientGroup.mk' (pPrimeCore 2 A) (x * a * x⁻¹ * a⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hc
    simp only [map_mul, map_inv] at h1
    exact (mul_comm_of_mul_mul_inv_mul_inv_eq_one h1).symm
  have hP : Subgroup.normalizer (P : Set (A ⧸ pPrimeCore 2 A)) ≤
      Subgroup.centralizer (P : Set (A ⧸ pPrimeCore 2 A)) := by
    rw [(Subgroup.centralizer_eq_top_iff_subset (s := (P : Set (A ⧸ pPrimeCore 2 A)))).mpr
      fun y hy => hPc y hy]
    exact le_top
  obtain ⟨K, hKn, hK2, -, -, -, -, hKP, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hP
  have hKbot : K = ⊥ := by
    have hle : K ≤ pPrimeCore 2 (A ⧸ pPrimeCore 2 A) :=
      le_sSup ⟨hKn, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hK2⟩
    rw [pPrimeCore_quotient_self_eq_bot] at hle
    exact le_bot_iff.mp hle
  rw [hKbot, bot_sup_eq] at hKP
  have hTtop : (T : Subgroup A) ⊔ pPrimeCore 2 A = ⊤ := by
    have h := Subgroup.comap_map_eq (QuotientGroup.mk' (pPrimeCore 2 A)) (T : Subgroup A)
    rw [show (T : Subgroup A).map (QuotientGroup.mk' (pPrimeCore 2 A)) = ⊤ from hKP,
      Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have h := congrArg (Subgroup.map A.subtype) hTtop
  rw [Subgroup.map_sup, hT, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVA,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rw [sup_comm]
  exact h

theorem sup_inf_normalizer_eq {H A V : Subgroup G} (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal) (hVA : V ≤ A)
    (hcard : Nat.card V = 2 ^ (Nat.card A).factorization 2) :
    A ⊔ (H ⊓ Subgroup.normalizer (V : Set G)) = H := by
  have hVH : V ≤ H := hVA.trans hAH
  have hVsub : V.subgroupOf H ≤ A.subgroupOf H := fun x hx => hVA hx
  have hc : Nat.card ((V.subgroupOf H).subgroupOf (A.subgroupOf H)) =
      2 ^ (Nat.card (A.subgroupOf H)).factorization 2 := by
    rw [card_subgroupOf_eq, inf_eq_left.mpr hVsub, card_subgroupOf_eq, card_subgroupOf_eq,
      inf_eq_left.mpr hVH, inf_eq_left.mpr hAH, hcard]
  have hF := Sylow.normalizer_sup_eq_top (Sylow.ofCard _ hc)
  rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVsub,
    normalizer_subgroupOf_eq hVH] at hF
  have h := congrArg (Subgroup.map H.subtype) hF
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hAH, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rw [sup_comm, inf_comm]
  exact h

end Core

end CFSG.Semidihedral.Local
