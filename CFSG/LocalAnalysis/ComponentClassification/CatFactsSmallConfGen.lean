module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups Subgroup
open CFSG.ComponentClassification.GSThmB

section Count

variable {G : Type*} [Group G]

theorem mul_comm_of_sq {E : Subgroup G} (h : ∀ x ∈ E, x * x = 1) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := by
  have hxy := h (x * y) (mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

theorem card_le_length {E : Subgroup G} {L : List G} (h : ∀ x ∈ E, x ∈ L) :
    Nat.card E ≤ L.length := by
  classical
  calc Nat.card E ≤ Nat.card ↥L.toFinset :=
        Nat.card_le_card_of_injective (fun x : E => ⟨x, List.mem_toFinset.2 (h x x.2)⟩)
          (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ L.length := List.toFinset_card_le L

theorem forall_bad_of_count {X E : Subgroup G} {LX : List G} (hLX : ∀ x ∈ X, x ∈ LX)
    (bad : G → Prop) {k : ℕ}
    (hcount : ∀ x ∈ LX, x * x = 1 → ¬ bad x →
      ∃ L : List G, (∀ y ∈ LX, y * y = 1 → y * x = x * y → y ∈ L) ∧ L.length < k)
    (hEX : E ≤ X) (h2 : ∀ x ∈ E, x * x = 1) (hk : k ≤ Nat.card E) : ∀ x ∈ E, bad x := by
  intro x hx
  by_contra hb
  obtain ⟨L, hL, hlen⟩ := hcount x (hLX x (hEX hx)) (h2 x hx) hb
  have := card_le_length (E := E) (L := L) fun y hy =>
    hL y (hLX y (hEX hy)) (h2 y hy) (mul_comm_of_sq h2 hy hx)
  omega

theorem count_of_filter {LX : List G} [DecidableEq G] {x : G} {k : ℕ}
    (h : (LX.filter fun y => decide (y * y = 1) && decide (y * x = x * y)).length < k) :
    ∃ L : List G, (∀ y ∈ LX, y * y = 1 → y * x = x * y → y ∈ L) ∧ L.length < k :=
  ⟨_, fun y hy hy2 hyx => List.mem_filter.2 ⟨hy, by simp [hy2, hyx]⟩, h⟩

end Count

theorem mem_center_map_subtype {H : Type*} [Group H] {X : Subgroup H} {x : H} :
    x ∈ (center X).map X.subtype ↔ x ∈ X ∧ ∀ y ∈ X, y * x = x * y := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, fun y hy => ?_⟩
    have := (mem_center_iff.1 hw) ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.2 fun y => Subtype.ext (hc y y.2), rfl⟩

section Sylow

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem sylow_of_card (H : Subgroup G) {k m : ℕ} (hm : Odd m)
    (hG : Nat.card G = 2 ^ k * m) (hH : Nat.card H = 2 ^ k) :
    ∃ T : Sylow 2 G, (T : Subgroup G) = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 H := IsPGroup.of_card hH
  have hidx : H.index = m := by
    have h := card_mul_index H
    rw [hH, hG] at h
    have hpos : 0 < 2 ^ k := by positivity
    exact Nat.eq_of_mul_eq_mul_left hpos h
  have h2 : ¬ 2 ∣ H.index := by
    rw [hidx]
    exact Odd.not_two_dvd_nat hm
  exact ⟨hP.toSylow h2, IsPGroup.toSylow_coe hP h2⟩

theorem card_sylow_of_card (T : Sylow 2 G) {k m : ℕ} (hm : Odd m) (hG : Nat.card G = 2 ^ k * m) :
    Nat.card T = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 T.isPGroup'
  have h := card_mul_index (T : Subgroup G)
  rw [hG, hj] at h
  rw [hj]
  have hmj : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hm)
  have hik : Nat.Coprime (2 ^ k) (T : Subgroup G).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 T.not_dvd_index)
  have h1 : 2 ^ j ∣ 2 ^ k := hmj.dvd_of_dvd_mul_right ⟨_, h.symm⟩
  have h2 : 2 ^ k ∣ 2 ^ j := hik.dvd_of_dvd_mul_right ⟨m, h⟩
  exact Nat.dvd_antisymm h1 h2

end Sylow

theorem mem_commutator_of_sylow {G : Type*} [Group G] {C T₀ T : Subgroup G} [Finite C]
    {k m : ℕ} (hm : Odd m) (hC : Nat.card C = 2 ^ k * m) (hT₀C : T₀ ≤ C) (hTC : T ≤ C)
    (hT₀ : Nat.card T₀ = 2 ^ k) (hT : Nat.card T = 2 ^ k) {x : G}
    (hxC : ∀ c ∈ C, c * x * c⁻¹ = x) (hx : x ∈ ⁅T₀, T₀⁆) : x ∈ ⁅T, T⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := sylow_of_card (T₀.subgroupOf C) hm hC
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hT₀C).toEquiv, hT₀])
  obtain ⟨S, hS⟩ := sylow_of_card (T.subgroupOf C) hm hC
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv, hT])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S₀ S
  have hmem : ∀ y : C, y ∈ (S : Subgroup C) ↔ c⁻¹ * y * c ∈ (S₀ : Subgroup C) := by
    intro y
    rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
  have hTeq : T = T₀.map (MulAut.conj (c : G)).toMonoidHom := by
    ext y
    constructor
    · intro hy
      have h1 := (hmem ⟨y, hTC hy⟩).1 (by rw [hS, mem_subgroupOf]; exact hy)
      rw [hS₀, mem_subgroupOf] at h1
      refine ⟨_, h1, ?_⟩
      simp [mul_assoc]
    · rintro ⟨t, ht, rfl⟩
      have hyC : (c : G) * t * (c : G)⁻¹ ∈ C := C.mul_mem (C.mul_mem c.2 (hT₀C ht)) (C.inv_mem c.2)
      have h1 := (hmem ⟨_, hyC⟩).2 (by
        rw [hS₀, mem_subgroupOf]
        simpa [mul_assoc] using ht)
      rw [hS, mem_subgroupOf] at h1
      simpa using h1
  rw [hTeq, ← map_commutator]
  refine ⟨x, hx, ?_⟩
  simpa using hxC c c.2


section Transport

variable {K : Type} [Group K] {G : Type*} [Group G] (M : AutModel K G)

theorem ι_apply (θ : MulAut K) : M.ι θ = (M.Φ θ : G) := rfl

theorem exists_ι_eq {y : G} (hy : y ∈ M.A) : ∃ θ : MulAut K, M.ι θ = y :=
  ⟨M.Φ.symm ⟨y, hy⟩, by rw [ι_apply, MulEquiv.apply_symm_apply]⟩

theorem range_ι : M.ι.range = M.A := by
  ext y
  constructor
  · rintro ⟨θ, rfl⟩
    exact M.ι_mem θ
  · intro hy
    exact exists_ι_eq M hy

theorem map_ι_le (X : Subgroup (MulAut K)) : X.map M.ι ≤ M.A := by
  rintro _ ⟨θ, -, rfl⟩
  exact M.ι_mem θ

theorem map_comap_ι {X : Subgroup G} (hX : X ≤ M.A) : (X.comap M.ι).map M.ι = X := by
  rw [map_comap_eq, range_ι, inf_eq_right.2 hX]

theorem card_map_ι (X : Subgroup (MulAut K)) : Nat.card (X.map M.ι) = Nat.card X :=
  card_map_of_injective M.ι_injective

theorem mem_map_ι {X : Subgroup (MulAut K)} {θ : MulAut K} : M.ι θ ∈ X.map M.ι ↔ θ ∈ X :=
  mem_map_iff_mem M.ι_injective

theorem map_ι_injective {X Y : Subgroup (MulAut K)} (h : X.map M.ι = Y.map M.ι) : X = Y :=
  map_injective M.ι_injective h

theorem map_centralizer_set' (S : Subgroup (MulAut K)) :
    (centralizer (S : Set (MulAut K))).map M.ι =
      M.A ⊓ centralizer ((S.map M.ι : Subgroup G) : Set G) := by
  ext y
  rw [mem_map, mem_inf, mem_centralizer_iff]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    rw [mem_centralizer_iff] at hθ
    refine ⟨M.ι_mem θ, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hθ s hs]
  · rintro ⟨hy, hc⟩
    obtain ⟨θ, rfl⟩ := exists_ι_eq M hy
    refine ⟨θ, ?_, rfl⟩
    rw [mem_centralizer_iff]
    intro s hs
    apply M.ι_injective
    rw [map_mul, map_mul]
    exact hc _ ⟨s, hs, rfl⟩

theorem map_normalizer (S : Subgroup (MulAut K)) :
    (normalizer (S : Set (MulAut K))).map M.ι =
      M.A ⊓ normalizer ((S.map M.ι : Subgroup G) : Set G) := by
  ext y
  rw [mem_map, mem_inf]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨M.ι_mem θ, ?_⟩
    rw [mem_normalizer_iff] at hθ ⊢
    intro g
    by_cases hg : g ∈ M.A
    · obtain ⟨η, rfl⟩ := exists_ι_eq M hg
      rw [mem_map_ι, ← map_inv, ← map_mul, ← map_mul, mem_map_ι]
      exact hθ η
    · have h1 : g ∉ S.map M.ι := fun h => hg (map_ι_le M S h)
      have h2 : M.ι θ * g * (M.ι θ)⁻¹ ∉ S.map M.ι := fun h => hg (by
        have h3 := M.A.mul_mem (M.A.mul_mem (M.A.inv_mem (M.ι_mem θ)) (map_ι_le M S h))
          (M.ι_mem θ)
        simpa [mul_assoc] using h3)
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  · rintro ⟨hy, hn⟩
    obtain ⟨θ, rfl⟩ := exists_ι_eq M hy
    refine ⟨θ, ?_, rfl⟩
    rw [mem_normalizer_iff] at hn ⊢
    intro η
    have h := hn (M.ι η)
    rw [mem_map_ι, ← map_inv, ← map_mul, ← map_mul, mem_map_ι] at h
    exact h

theorem map_center (X : Subgroup (MulAut K)) :
    ((center X).map X.subtype).map M.ι = (center (X.map M.ι)).map (X.map M.ι).subtype := by
  ext y
  rw [mem_center_map_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_center_map_subtype] at hx
    refine ⟨mem_map_of_mem _ hx.1, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hx.2 w hw]
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, mem_center_map_subtype.2 ⟨hx, fun w hw => ?_⟩, rfl⟩
    apply M.ι_injective
    rw [map_mul, map_mul]
    exact hc _ (mem_map_of_mem _ hw)

theorem image_conjOrbit (N : Subgroup (MulAut K)) (w : MulAut K) :
    M.ι '' Cat8.conjOrbit N w = Cat8.conjOrbit (N.map M.ι) (M.ι w) := by
  ext y
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨M.ι n, mem_map_of_mem _ hn, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n⁻¹ * w * n, ⟨n, hn, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩

theorem card_conjOrbit (N : Subgroup (MulAut K)) (w : MulAut K) :
    Nat.card (Cat8.conjOrbit N w) = Nat.card (Cat8.conjOrbit (N.map M.ι) (M.ι w)) := by
  rw [← image_conjOrbit, Nat.card_image_of_injective M.ι_injective]

variable (hPA : M.P ≤ M.A) (hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1)
include hPA hcent

theorem map_Inn : (Cat8.Inn K).map M.ι = M.P := by
  ext y
  constructor
  · rintro ⟨η, hη, rfl⟩
    exact (mem_range_conj_iff M hPA hcent η).1 hη
  · intro hy
    obtain ⟨θ, rfl⟩ := exists_ι_eq M (hPA hy)
    exact ⟨θ, (mem_range_conj_iff M hPA hcent θ).2 hy, rfl⟩

theorem map_L0 (θ : MulAut K) :
    (Cat8.L0 K θ).map M.ι = ⁅M.P ⊓ centralizer ({M.ι θ} : Set G),
      M.P ⊓ centralizer ({M.ι θ} : Set G)⁆ := by
  rw [Cat8.L0, map_commutator, map_innFix M hPA hcent]
  rfl

end Transport

section Conj

variable {K : Type} {G : Type*} [Group K] [Group G] (M : AutModel K G)

theorem exists_conj_mem_iff [Finite K] (θ : MulAut K) (Q₀ : Subgroup G)
    (hQ₀ : Q₀ ≤ M.A ⊓ centralizer ({(M.Φ θ : G)} : Set G))
    (hcard : Nat.card ↥(M.A ⊓ centralizer ({(M.Φ θ : G)} : Set G)) = 2 ^ 5 * 45)
    (hcardQ₀ : Nat.card Q₀ = 2 ^ 5) (Q : Subgroup (MulAut K))
    (hQC : Q ≤ centralizer ({θ} : Set (MulAut K)))
    (hQS : ∃ T : Sylow 2 ↥(centralizer ({θ} : Set (MulAut K))),
      (T : Subgroup _) = Q.subgroupOf (centralizer ({θ} : Set (MulAut K)))) :
    ∃ c ∈ M.A ⊓ centralizer ({(M.Φ θ : G)} : Set G),
      ∀ η : MulAut K, η ∈ Q ↔ c⁻¹ * M.ι η * c ∈ Q₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : G := (M.Φ θ : G) with hσdef
  set CA : Subgroup G := M.A ⊓ centralizer ({σ} : Set G) with hCA
  have : Finite (MulAut K) :=
    Finite.of_injective (fun φ : MulAut K => (φ : K → K)) DFunLike.coe_injective
  have : Finite M.A := Finite.of_equiv _ M.Φ.toEquiv
  have : Finite CA := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have : Finite Q₀ := Finite.of_injective (inclusion (hQ₀.trans inf_le_left))
    (inclusion_injective _)
  have hmapC := map_centralizer_singleton M θ
  let e : ↥(centralizer ({θ} : Set (MulAut K))) ≃* CA :=
    ((centralizer ({θ} : Set (MulAut K))).equivMapOfInjective M.ι M.ι_injective).trans
      (MulEquiv.subgroupCongr hmapC)
  have he : ∀ x, ((e x : CA) : G) = M.ι x := fun x => rfl
  obtain ⟨T, hT⟩ := hQS
  let T' : Sylow 2 CA := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ₀2 : IsPGroup 2 (Q₀.subgroupOf CA) := by
    refine IsPGroup.of_card (n := 5) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hQ₀).toEquiv, hcardQ₀]
  have hQ₀i : ¬ 2 ∣ (Q₀.subgroupOf CA).index := by
    have h := index_mul_card (Q₀.subgroupOf CA)
    rw [Nat.card_congr (subgroupOfEquivOfLe hQ₀).toEquiv, hcardQ₀, hcard] at h
    have : (Q₀.subgroupOf CA).index = 45 := by omega
    rw [this]
    decide
  let S₀ : Sylow 2 CA := hQ₀2.toSylow hQ₀i
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq CA S₀ T'
  refine ⟨c, c.2, fun η => ?_⟩
  have hT'mem : ∀ y : CA, y ∈ (T' : Subgroup CA) ↔ c⁻¹ * y * c ∈ Q₀.subgroupOf CA := by
    intro y
    rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, IsPGroup.toSylow_coe]
  constructor
  · intro hη
    have hηC : η ∈ centralizer ({θ} : Set (MulAut K)) := hQC hη
    have h1 : e ⟨η, hηC⟩ ∈ (T' : Subgroup CA) := by
      show e ⟨η, hηC⟩ ∈ T.map e.toMonoidHom
      refine ⟨⟨η, hηC⟩, ?_, rfl⟩
      rw [hT, SetLike.mem_coe, mem_subgroupOf]
      exact hη
    have h2 := (hT'mem _).1 h1
    rw [mem_subgroupOf] at h2
    simpa [he] using h2
  · intro hη
    have hηA : M.ι η ∈ CA := by
      have : (c : G)⁻¹ * M.ι η * c ∈ CA := hQ₀ hη
      have h3 := CA.mul_mem (CA.mul_mem c.2 this) (CA.inv_mem c.2)
      simpa [mul_assoc] using h3
    obtain ⟨η', hη'⟩ := e.surjective ⟨M.ι η, hηA⟩
    have hηη : (η' : MulAut K) = η := by
      apply M.ι_injective
      rw [← he, hη']
    have h1 : e η' ∈ (T' : Subgroup CA) := by
      rw [hT'mem, mem_subgroupOf, hη']
      simpa using hη
    obtain ⟨t, ht, hte⟩ := h1
    have htη : t = η' := e.injective hte
    rw [hT, SetLike.mem_coe, mem_subgroupOf, htη, hηη] at ht
    exact ht

end Conj

section Pullback

variable {K : Type} [Group K] {G : Type*} [Group G] (M : AutModel K G)

@[expose] noncomputable def comapEquiv {X : Subgroup G} (hX : X ≤ M.A) : X.comap M.ι ≃* X :=
  ((X.comap M.ι).equivMapOfInjective M.ι M.ι_injective).trans
    (MulEquiv.subgroupCongr (map_comap_ι M hX))

theorem comapEquiv_apply {X : Subgroup G} (hX : X ≤ M.A) (x : X.comap M.ι) :
    (comapEquiv M hX x : G) = M.ι x := rfl

theorem center_comap {X : Subgroup G} (hX : X ≤ M.A) {w : MulAut K}
    (h : center X = (zpowers (M.ι w)).subgroupOf X) :
    center (X.comap M.ι) = (zpowers w).subgroupOf (X.comap M.ι) := by
  set e := comapEquiv M hX
  ext x
  rw [mem_subgroupOf, mem_center_iff]
  have hx : e x ∈ center X ↔ (x : MulAut K) ∈ zpowers w := by
    rw [h, mem_subgroupOf, comapEquiv_apply, ← MonoidHom.map_zpowers, mem_map_ι]
  rw [← hx, mem_center_iff]
  constructor
  · intro hc y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    rw [← map_mul, ← map_mul, hc y]
  · intro hc y
    apply e.injective
    rw [map_mul, map_mul, hc (e y)]

end Pullback

end CFSG.ComponentClassification.CatFactsSmall
