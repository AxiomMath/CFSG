module

public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup

@[expose] def EvenCentComm (X : Type) [Group X] (z : X) : Prop :=
  ∀ g ∈ centralizer ({z} : Set X), ∀ h ∈ centralizer ({z} : Set X),
    (∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
      ∀ k ∈ K, (k : X) * g = g * k) →
    (∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
      ∀ k ∈ K, (k : X) * h = h * k) → g * h = h * g

@[expose] def EvenCentInv (X : Type) [Group X] (z : X) : Prop :=
  ∀ g ∈ centralizer ({z} : Set X),
    (∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
      ∀ k ∈ K, (k : X) * g = g * k) → g * g = 1 → g = 1 ∨ g = z

theorem commute_of_mem_center {S : Type*} [Group S] {M : Subgroup S} [Group.IsPerfect M]
    {g : S} (hg : ∀ m ∈ M, g * m * g⁻¹ * m⁻¹ ∈ center S) : ∀ m ∈ M, g * m = m * g := by
  let φ : M →* center S :=
    { toFun := fun m => ⟨g * m * g⁻¹ * m⁻¹, hg m m.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hb := mem_center_iff.mp (hg b b.2) (a : S)⁻¹
        change g * (a * b : S) * g⁻¹ * (a * b : S)⁻¹ =
          g * a * g⁻¹ * (a : S)⁻¹ * (g * b * g⁻¹ * (b : S)⁻¹)
        calc g * (a * b : S) * g⁻¹ * (a * b : S)⁻¹ =
            g * a * g⁻¹ * ((g * b * g⁻¹ * (b : S)⁻¹) * (a : S)⁻¹) := by group
          _ = g * a * g⁻¹ * ((a : S)⁻¹ * (g * b * g⁻¹ * (b : S)⁻¹)) := by rw [hb]
          _ = _ := by group) }
  intro m hm
  have h1 : (⟨m, hm⟩ : M) ∈ φ.ker := Abelianization.commutator_subset_ker φ (by simp)
  have h2 : g * m * g⁻¹ * m⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp h1)
  calc g * m = g * m * g⁻¹ * m⁻¹ * (m * g) := by group
    _ = m * g := by rw [h2, one_mul]

theorem conj_mem_map_centralizer {S X : Type*} [Group S] [Group X] {π : S →* X}
    (hker : ∀ s, π s = 1 → s ∈ center S) {a ĥ : S}
    (hh : π ĥ ∈ centralizer ({π a} : Set X)) {x : S} (hx : x ∈ centralizer ({a} : Set S)) :
    ĥ * x * ĥ⁻¹ ∈ centralizer ({a} : Set S) := by
  rw [mem_centralizer_singleton_iff] at hh hx ⊢
  have hc : ĥ * a * ĥ⁻¹ * a⁻¹ ∈ center S := hker _ (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hh, mul_inv_cancel_right,
      mul_inv_cancel])
  set c := ĥ * a * ĥ⁻¹ * a⁻¹ with hcdef
  have h1 : (ĥ * x * ĥ⁻¹) * (ĥ * a * ĥ⁻¹) = (ĥ * a * ĥ⁻¹) * (ĥ * x * ĥ⁻¹) := by
    calc (ĥ * x * ĥ⁻¹) * (ĥ * a * ĥ⁻¹) = ĥ * (x * a) * ĥ⁻¹ := by group
      _ = ĥ * (a * x) * ĥ⁻¹ := by rw [hx]
      _ = _ := by group
  have h2 : ĥ * a * ĥ⁻¹ = c * a := by rw [hcdef]; group
  rw [h2] at h1
  have h3 := mem_center_iff.mp hc (ĥ * x * ĥ⁻¹)
  apply mul_left_cancel (a := c)
  calc c * (ĥ * x * ĥ⁻¹ * a) = (ĥ * x * ĥ⁻¹) * (c * a) := by rw [← mul_assoc, ← h3, mul_assoc]
    _ = (c * a) * (ĥ * x * ĥ⁻¹) := h1
    _ = c * (a * (ĥ * x * ĥ⁻¹)) := by rw [mul_assoc]

theorem two_dvd_orderOf_of_pow_four {G : Type*} [Group G] {y : G} (hy : y ^ 4 = 1)
    (hy1 : y ≠ 1) : 2 ∣ orderOf y := by
  have h4 : orderOf y ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hy
  obtain ⟨k, hk, hyk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
  have hk0 : k ≠ 0 := fun h0 => hy1 (orderOf_eq_one_iff.mp (by rw [hyk, h0, pow_zero]))
  rw [hyk]
  exact dvd_pow_self 2 hk0

theorem lift_commute_of_cover {S X : Type} [Group S] [Group X] [Finite S] (π : S →* X)
    (hπ : Function.Surjective π) (hker : ∀ s, π s = 1 → s ∈ center S) (a : S)
    (𝓜 : Set (Subgroup S)) (hC : ∀ M ∈ 𝓜, M ≤ centralizer ({a} : Set S))
    (hN : ∀ M ∈ 𝓜, ∀ x ∈ centralizer ({a} : Set S), ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hQ : ∀ M ∈ 𝓜, IsQuasisimple M) (hE : ∀ M ∈ 𝓜, ∃ m ∈ M, π m ≠ 1 ∧ m ^ 4 = 1)
    (g : X) (hg : ∀ K : Subgroup (centralizer ({π a} : Set X)), IsComponent K →
      Even (Nat.card K) → ∀ k ∈ K, (k : X) * g = g * k) (ĝ : S) (hĝ : π ĝ = g) :
    ∀ M ∈ 𝓜, ∀ m ∈ M, ĝ * m = m * ĝ := by
  set H := centralizer ({π a} : Set X) with hH
  set F := (centralizer ({a} : Set S)).map π with hF
  have hFH : F ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx]
  intro M hM
  have hMH : M.map π ≤ H := (map_mono (hC M hM)).trans hFH
  obtain ⟨m₀, hm₀, hm₀1, hm₀4⟩ := hE M hM
  have eM := subgroupOfEquivOfLe hMH
  have hK1 : IsComponent ((M.map π).subgroupOf H) := by
    refine ⟨LocalCores.isQuasisimple_of_mulEquiv eM.symm
      (LieType.CurtisTits.isQuasisimple_of_surjective (hQ M hM) (π.subgroupMap_surjective M)
        ⟨⟨m₀, hm₀⟩, fun h1 => hm₀1 (congrArg Subtype.val h1)⟩), ?_⟩
    refine IsSubnormal.step _ (F.subgroupOf H) (fun y hy => ?_) (Normal.isSubnormal ⟨?_⟩)
      ⟨?_⟩
    · exact mem_subgroupOf.mpr (map_mono (hC M hM) (mem_subgroupOf.mp hy))
    · intro f hf h
      rw [mem_subgroupOf] at hf ⊢
      obtain ⟨x, hx, hxf⟩ := hf
      obtain ⟨ĥ, hĥ⟩ := hπ h
      refine ⟨ĥ * x * ĥ⁻¹, conj_mem_map_centralizer hker (hĥ ▸ h.2) hx, ?_⟩
      rw [map_mul, map_mul, map_inv, hxf, hĥ]
      rfl
    · intro y hy f
      rw [mem_subgroupOf, mem_subgroupOf] at hy ⊢
      obtain ⟨m', hm', hm'y⟩ := hy
      obtain ⟨x, hx, hxf⟩ := mem_subgroupOf.mp f.2
      refine ⟨x * m' * x⁻¹, hN M hM x hx m' hm', ?_⟩
      rw [map_mul, map_mul, map_inv, hxf, hm'y]
      rfl
  have hK2 : Even (Nat.card ((M.map π).subgroupOf H)) := by
    rw [Nat.card_congr eM.toEquiv, even_iff_two_dvd]
    let y : M.map π := ⟨π m₀, mem_map_of_mem π hm₀⟩
    have hy4 : y ^ 4 = 1 := Subtype.ext (by
      change π m₀ ^ 4 = 1
      rw [← map_pow, hm₀4, map_one])
    have hy1 : y ≠ 1 := fun h1 => hm₀1 (congrArg Subtype.val h1)
    exact (two_dvd_orderOf_of_pow_four hy4 hy1).trans (orderOf_dvd_natCard y)
  have : Group.IsPerfect M := (hQ M hM).1
  refine commute_of_mem_center fun m hm => hker _ ?_
  have h1 := hg _ hK1 hK2 ⟨π m, hMH (mem_map_of_mem π hm)⟩
    (mem_subgroupOf.mpr (mem_map_of_mem π hm))
  change π m * g = g * π m at h1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hĝ, ← h1, mul_inv_cancel_right,
    mul_inv_cancel]

theorem evenCentComm_of_cover {S X : Type} [Group S] [Group X] [Finite S] (π : S →* X)
    (hπ : Function.Surjective π) (hker : ∀ s, π s = 1 → s ∈ center S) (a : S)
    (𝓜 : Set (Subgroup S)) (hC : ∀ M ∈ 𝓜, M ≤ centralizer ({a} : Set S))
    (hN : ∀ M ∈ 𝓜, ∀ x ∈ centralizer ({a} : Set S), ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hQ : ∀ M ∈ 𝓜, IsQuasisimple M) (hE : ∀ M ∈ 𝓜, ∃ m ∈ M, π m ≠ 1 ∧ m ^ 4 = 1)
    (hcomm : ∀ g h : S, (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) →
      (∀ M ∈ 𝓜, ∀ m ∈ M, h * m = m * h) → g * h = h * g) :
    EvenCentComm X (π a) := by
  intro g _ h _ hg hh
  obtain ⟨ĝ, hĝ⟩ := hπ g
  obtain ⟨ĥ, hĥ⟩ := hπ h
  rw [← hĝ, ← hĥ, ← map_mul, ← map_mul,
    hcomm ĝ ĥ (lift_commute_of_cover π hπ hker a 𝓜 hC hN hQ hE g hg ĝ hĝ)
      (lift_commute_of_cover π hπ hker a 𝓜 hC hN hQ hE h hh ĥ hĥ)]

theorem evenCentInv_of_cover {S X : Type} [Group S] [Group X] [Finite S] (π : S →* X)
    (hπ : Function.Surjective π) (hker : ∀ s, π s = 1 → s ∈ center S)
    (hcen : ∀ s ∈ center S, π s = 1) (a : S)
    (𝓜 : Set (Subgroup S)) (hC : ∀ M ∈ 𝓜, M ≤ centralizer ({a} : Set S))
    (hN : ∀ M ∈ 𝓜, ∀ x ∈ centralizer ({a} : Set S), ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hQ : ∀ M ∈ 𝓜, IsQuasisimple M) (hE : ∀ M ∈ 𝓜, ∃ m ∈ M, π m ≠ 1 ∧ m ^ 4 = 1)
    (hinv : ∀ g : S, (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) → g * g ∈ center S →
      g ∈ center S ∨ g * a⁻¹ ∈ center S) :
    EvenCentInv X (π a) := by
  intro g _ hg hgg
  obtain ⟨ĝ, hĝ⟩ := hπ g
  rcases hinv ĝ (lift_commute_of_cover π hπ hker a 𝓜 hC hN hQ hE g hg ĝ hĝ)
    (hker _ (by rw [map_mul, hĝ, hgg])) with h | h
  · exact Or.inl (hĝ ▸ hcen ĝ h)
  · refine Or.inr ?_
    have h1 := hcen _ h
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [← hĝ, h1]

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
