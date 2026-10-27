module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8CaseOne
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Setup

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup

theorem frameVec_add_self (v : FrameVec) : v + v = 0 :=
  funext fun i => by
    change v i + v i = 0
    generalize v i = x
    revert x
    decide

theorem mul_self_of_frameVec {X : Type*} [Group X] (ι : Multiplicative FrameVec →* X)
    (v : Multiplicative FrameVec) : ι v * ι v = 1 := by
  rw [← map_mul, show v * v = 1 from frameVec_add_self (Multiplicative.toAdd v), map_one]

theorem mul_self_of_mem_frameRange {X : Type*} [Group X] {ι : Multiplicative FrameVec →* X}
    {a : X} (ha : a ∈ ι.range) : a * a = 1 := by
  obtain ⟨v, rfl⟩ := ha
  exact mul_self_of_frameVec ι v

theorem comm_of_mem_frameRange {X : Type*} [Group X] {ι : Multiplicative FrameVec →* X}
    {a b : X} (ha : a ∈ ι.range) (hb : b ∈ ι.range) : a * b = b * a :=
  comm_of_mul_self (mul_self_of_mem_frameRange ha) (mul_self_of_mem_frameRange hb)
    (mul_self_of_mem_frameRange (mul_mem ha hb))

theorem card_inf_centralizer_map {G W : Type*} [Group G] [Group W] {ψ : W →* G}
    (hψ : Function.Injective ψ) (A : Subgroup W) (a : W) :
    Nat.card (A.map ψ ⊓ centralizer ({ψ a} : Set G) : Subgroup G) =
      Nat.card (A ⊓ centralizer ({a} : Set W) : Subgroup W) := by
  have h : (A ⊓ centralizer ({a} : Set W)).map ψ = A.map ψ ⊓ centralizer ({ψ a} : Set G) := by
    ext g
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, ⟨hxA, hxa⟩, rfl⟩
      exact ⟨⟨x, hxA, rfl⟩, by rw [← map_mul, ← map_mul, hxa]⟩
    · rintro ⟨⟨x, hxA, rfl⟩, hxa⟩
      exact ⟨x, ⟨hxA, hψ (by rw [map_mul, map_mul, hxa])⟩, rfl⟩
  rw [← h, card_map_of_injective hψ]

namespace Child8Weyl

variable {W : Type} [Group W] [Finite W] (M : Child8Weyl W)

theorem ιE1_inj_iff {u v : FrameVec} :
    M.ιE1 (Multiplicative.ofAdd u) = M.ιE1 (Multiplicative.ofAdd v) ↔ u = v :=
  ⟨fun h => M.ιE1_injective h, fun h => h ▸ rfl⟩

theorem x₀_ne_one : M.x₀ ≠ 1 := by
  rw [M.x₀_eq, ← map_one M.ιE1, show (1 : Multiplicative FrameVec) = Multiplicative.ofAdd 0
    from rfl, Ne, M.ιE1_inj_iff]
  decide

theorem x₀_ne_z : M.x₀ ≠ M.z := by
  rw [M.x₀_eq, ← M.ιE1_frameZ, Ne, M.ιE1_inj_iff]
  decide

theorem x₀z_ne_x₀ : M.x₀ * M.z ≠ M.x₀ := fun h => M.z_ne_one (by simpa using h)

theorem z_mem_T : M.z ∈ M.T := M.ιE1_frameZ ▸ M.ιE1_mem_T _

theorem x₀_mem_E1 : M.x₀ ∈ M.ιE1.range := M.x₀_eq ▸ ⟨_, rfl⟩

theorem ιE1_mem_C (v : Multiplicative FrameVec) :
    M.ιE1 v ∈ M.T ⊓ centralizer ({M.x₀} : Set W) :=
  ⟨M.ιE1_mem_T v, mem_centralizer_singleton_iff.2
    (comm_of_mem_frameRange ⟨v, rfl⟩ M.x₀_mem_E1)⟩

theorem x₀_mem_C : M.x₀ ∈ M.T ⊓ centralizer ({M.x₀} : Set W) := by
  obtain ⟨v, hv⟩ := M.x₀_mem_E1
  exact hv ▸ M.ιE1_mem_C v

theorem z_mem_C : M.z ∈ M.T ⊓ centralizer ({M.x₀} : Set W) :=
  ⟨M.z_mem_T, mem_centralizer_singleton_iff.2 (M.z_comm M.x₀).symm⟩

theorem conj_mem_C {t : W} (ht : t ∈ M.T) {c : W} (hc : c ∈ M.T ⊓ centralizer ({M.x₀} : Set W)) :
    t * c * t⁻¹ ∈ M.T ⊓ centralizer ({M.x₀} : Set W) :=
  conj_mem_of_two_mul_card_eq inf_le_left (by rw [M.card_T, M.card_C]; norm_num) ht hc

theorem exists_t : ∃ t ∈ M.T, t * M.x₀ * t⁻¹ = M.x₀ * M.z := by
  have hlt : ¬ M.T ≤ M.T ⊓ centralizer ({M.x₀} : Set W) := fun h => by
    have h1 := card_le_of_le h
    rw [M.card_T, M.card_C] at h1
    norm_num at h1
  obtain ⟨t, ht, htC⟩ := Set.not_subset.1 hlt
  have hy := M.conj_mem_C ht M.x₀_mem_C
  have hyc : ∀ d ∈ M.T ⊓ centralizer ({M.x₀} : Set W),
      t * M.x₀ * t⁻¹ * d = d * (t * M.x₀ * t⁻¹) := by
    intro d hd
    have hd' := M.conj_mem_C (inv_mem ht) hd
    rw [inv_inv] at hd'
    have h1 := mem_centralizer_singleton_iff.1 hd'.2
    calc t * M.x₀ * t⁻¹ * d = t * (M.x₀ * (t⁻¹ * d * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * d * t) * M.x₀) * t⁻¹ := by rw [h1]
      _ = d * (t * M.x₀ * t⁻¹) := by group
  rcases M.center_C _ hy hyc with h | h | h | h
  · refine absurd ?_ M.x₀_ne_one
    calc M.x₀ = t⁻¹ * (t * M.x₀ * t⁻¹) * t := by group
      _ = 1 := by rw [h]; group
  · exact absurd ⟨ht, mem_centralizer_singleton_iff.2 (by
      calc t * M.x₀ = t * M.x₀ * t⁻¹ * t := by group
        _ = M.x₀ * t := by rw [h])⟩ htC
  · refine absurd ?_ M.x₀_ne_z
    calc M.x₀ = t⁻¹ * (t * M.x₀ * t⁻¹) * t := by group
      _ = M.z := by rw [h, mul_assoc, ← M.z_comm t]; group
  · exact ⟨t, ht, h⟩

section GSide

variable {G : Type} [Group G] {ψ : W →* G}

@[expose] def UG (ψ : W →* G) : Set G := {1, ψ M.x₀, ψ M.z, ψ M.x₀ * ψ M.z}

@[expose] def CG (ψ : W →* G) : Subgroup G := (M.T ⊓ centralizer ({M.x₀} : Set W)).map ψ

theorem CG_le_TG : M.CG ψ ≤ M.T.map ψ := map_mono inf_le_left

theorem card_CG (hψ : Function.Injective ψ) : Nat.card (M.CG ψ) = 2 ^ 13 := by
  rw [CG, card_map_of_injective hψ, M.card_C]

theorem card_TG (hψ : Function.Injective ψ) : Nat.card (M.T.map ψ) = 2 ^ 14 := by
  rw [card_map_of_injective hψ, M.card_T]

theorem zG_comm (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) (w : W) :
    ψ w * ψ M.z = ψ M.z * ψ w :=
  (hH _).1 ⟨w, rfl⟩

theorem zG_mul_self : ψ M.z * ψ M.z = 1 := by rw [← map_mul, M.z_mul_self, map_one]

theorem UG_sub_CG {u : G} (hu : u ∈ M.UG ψ) : u ∈ M.CG ψ := by
  rcases hu with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact mem_map_of_mem ψ M.x₀_mem_C
  · exact mem_map_of_mem ψ M.z_mem_C
  · exact mul_mem (mem_map_of_mem ψ M.x₀_mem_C) (mem_map_of_mem ψ M.z_mem_C)

theorem comm_UG_CG {u c : G} (hu : u ∈ M.UG ψ) (hc : c ∈ M.CG ψ) : u * c = c * u := by
  obtain ⟨c', hc', rfl⟩ := hc
  have hx : ψ M.x₀ * ψ c' = ψ c' * ψ M.x₀ := by
    rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 hc'.2).symm]
  have hz : ψ M.z * ψ c' = ψ c' * ψ M.z := by rw [← map_mul, ← map_mul, M.z_comm]
  rcases hu with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hx
  · exact hz
  · rw [mul_assoc, hz, ← mul_assoc, hx, mul_assoc]

theorem center_CG (hψ : Function.Injective ψ) {c : G} (hc : c ∈ M.CG ψ)
    (hcent : ∀ d ∈ M.CG ψ, c * d = d * c) : c ∈ M.UG ψ := by
  obtain ⟨c', hc', rfl⟩ := hc
  rcases M.center_C c' hc' (fun d hd => hψ (by simpa using hcent _ (mem_map_of_mem ψ hd)))
    with h | h | h | h <;> rw [h]
  · exact Or.inl (map_one ψ)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul ψ _ _)))

theorem mem_CG_of (hψ : Function.Injective ψ) {g : G} (hg : g ∈ M.T.map ψ)
    (hgx : g * ψ M.x₀ = ψ M.x₀ * g) : g ∈ M.CG ψ := by
  obtain ⟨g', hg', rfl⟩ := hg
  refine mem_map_of_mem ψ ⟨hg', mem_centralizer_singleton_iff.2 (hψ ?_)⟩
  rw [map_mul, map_mul, hgx]

theorem normal_four_G (hψ : Function.Injective ψ) {v : G} (hv : v ∈ M.T.map ψ)
    (hv2 : v * v = 1)
    (ht : ∀ t ∈ M.T.map ψ, t * v * t⁻¹ = v ∨ t * v * t⁻¹ = v * ψ M.z) : v ∈ M.UG ψ := by
  obtain ⟨v', hv', rfl⟩ := hv
  have h := M.normal_four v' hv' (hψ (by rw [map_mul, hv2, map_one])) fun t ht' => by
    rcases ht (ψ t) (mem_map_of_mem ψ ht') with h | h
    · left
      exact hψ (by simpa using h)
    · right
      exact hψ (by simpa using h)
  rcases h with h | h | h | h <;> rw [h]
  · exact Or.inl (map_one ψ)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul ψ _ _)))

theorem xG_ne_zG (hψ : Function.Injective ψ) : ψ M.x₀ ≠ ψ M.z := fun h => M.x₀_ne_z (hψ h)

theorem zG_ne_one (hψ : Function.Injective ψ) : ψ M.z ≠ 1 := fun h =>
  M.z_ne_one (hψ (h.trans (map_one ψ).symm))

theorem xG_ne_one (hψ : Function.Injective ψ) : ψ M.x₀ ≠ 1 := fun h =>
  M.x₀_ne_one (hψ (h.trans (map_one ψ).symm))

theorem conj_z_eq [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) {k : G}
    (hk : k * ψ M.x₀ * k⁻¹ = ψ M.z) (hkT : ∀ c ∈ M.CG ψ, k * c * k⁻¹ ∈ M.T.map ψ) :
    k * ψ M.z * k⁻¹ = ψ M.x₀ ∨ k * ψ M.z * k⁻¹ = ψ M.x₀ * ψ M.z := by
  set N := (M.CG ψ).map (MulAut.conj k).toMonoidHom with hN
  have memN : ∀ c ∈ M.CG ψ, k * c * k⁻¹ ∈ N := fun c hc => ⟨c, hc, rfl⟩
  have NCG : ∀ n ∈ N, k⁻¹ * n * k ∈ M.CG ψ := by
    rintro _ ⟨c, hc, rfl⟩
    simpa [mul_assoc] using hc
  have hNT : N ≤ M.T.map ψ := by
    rintro _ ⟨c, hc, rfl⟩
    exact hkT c hc
  have hNnorm : ∀ t ∈ M.T.map ψ, ∀ n ∈ N, t * n * t⁻¹ ∈ N := fun t ht n hn =>
    conj_mem_of_two_mul_card_eq hNT (by
      rw [M.card_TG hψ, hN, card_map_of_injective (MulAut.conj k).injective, M.card_CG hψ]
      norm_num) ht hn
  have hzC : ψ M.z ∈ M.CG ψ := M.UG_sub_CG (Or.inr (Or.inr (Or.inl rfl)))
  set v := k * ψ M.z * k⁻¹ with hv
  have hvN : v ∈ N := memN _ hzC
  have hvT : v ∈ M.T.map ψ := hNT hvN
  have hclaim : ∀ t ∈ M.T.map ψ, k⁻¹ * (t * v * t⁻¹) * k ∈ M.UG ψ := by
    intro t ht
    refine M.center_CG hψ (NCG _ (hNnorm t ht v hvN)) fun d hd => ?_
    have hn' := hNnorm t⁻¹ (inv_mem ht) _ (memN d hd)
    have hd' := NCG _ hn'
    have hc := M.comm_UG_CG (Or.inr (Or.inr (Or.inl rfl))) hd'
    calc k⁻¹ * (t * v * t⁻¹) * k * d =
          k⁻¹ * t * k * (ψ M.z * (k⁻¹ * (t⁻¹ * (k * d * k⁻¹) * t⁻¹⁻¹) * k)) * k⁻¹ * t⁻¹ * k := by
            rw [hv]; group
      _ = k⁻¹ * t * k * ((k⁻¹ * (t⁻¹ * (k * d * k⁻¹) * t⁻¹⁻¹) * k) * ψ M.z) * k⁻¹ * t⁻¹ * k := by
            rw [hc]
      _ = d * (k⁻¹ * (t * v * t⁻¹) * k) := by rw [hv]; group
  have hv2 : v * v = 1 := by
    calc v * v = k * (ψ M.z * ψ M.z) * k⁻¹ := by rw [hv]; group
      _ = 1 := by rw [M.zG_mul_self]; group
  have hvU : v ∈ M.UG ψ := by
    refine M.normal_four_G hψ hvT hv2 fun t ht => ?_
    rcases hclaim t ht with h | h | h | h
    · exfalso
      apply M.zG_ne_one hψ
      have h1 : t * v * t⁻¹ = 1 := by
        calc t * v * t⁻¹ = k * (k⁻¹ * (t * v * t⁻¹) * k) * k⁻¹ := by group
          _ = 1 := by rw [h]; group
      calc ψ M.z = k⁻¹ * (t⁻¹ * (t * v * t⁻¹) * t) * k := by rw [hv]; group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply M.xG_ne_zG hψ
      have h1 : t * v * t⁻¹ = ψ M.z := by
        calc t * v * t⁻¹ = k * (k⁻¹ * (t * v * t⁻¹) * k) * k⁻¹ := by group
          _ = ψ M.z := by rw [h, hk]
      obtain ⟨t', -, rfl⟩ := ht
      have h2 : v = ψ M.z := by
        calc v = (ψ t')⁻¹ * (ψ t' * v * (ψ t')⁻¹) * ψ t' := by group
          _ = (ψ t')⁻¹ * (ψ M.z * ψ t') := by rw [h1]; group
          _ = ψ M.z := by rw [← M.zG_comm hH t']; group
      calc ψ M.x₀ = k⁻¹ * (k * ψ M.x₀ * k⁻¹) * k := by group
        _ = k⁻¹ * v * k := by rw [hk, h2]
        _ = ψ M.z := by rw [hv]; group
    · left
      calc t * v * t⁻¹ = k * (k⁻¹ * (t * v * t⁻¹) * k) * k⁻¹ := by group
        _ = v := by rw [h, hv]
    · right
      obtain ⟨v', -, hv'⟩ := hvT
      calc t * v * t⁻¹ = k * (k⁻¹ * (t * v * t⁻¹) * k) * k⁻¹ := by group
        _ = k * ψ M.x₀ * k⁻¹ * (k * ψ M.z * k⁻¹) := by rw [h]; group
        _ = ψ M.z * v := by rw [hk, hv]
        _ = v * ψ M.z := by rw [← hv', M.zG_comm hH v']
  rcases hvU with h | h | h | h
  · exfalso
    apply M.zG_ne_one hψ
    calc ψ M.z = k⁻¹ * v * k := by rw [hv]; group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exfalso
    apply M.xG_ne_zG hψ
    calc ψ M.x₀ = k⁻¹ * (k * ψ M.x₀ * k⁻¹) * k := by group
      _ = k⁻¹ * v * k := by rw [hk, h]
      _ = ψ M.z := by rw [hv]; group
  · exact Or.inr h

theorem xG_comm_zG (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) :
    ψ M.x₀ * ψ M.z = ψ M.z * ψ M.x₀ :=
  M.zG_comm hH M.x₀

theorem conj_mem_UG (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) {k : G}
    (hk : k * ψ M.x₀ * k⁻¹ = ψ M.z)
    (h3 : k * ψ M.z * k⁻¹ = ψ M.x₀ ∨ k * ψ M.z * k⁻¹ = ψ M.x₀ * ψ M.z) {u : G}
    (hu : u ∈ M.UG ψ) : k * u * k⁻¹ ∈ M.UG ψ := by
  have hxz : k * (ψ M.x₀ * ψ M.z) * k⁻¹ = ψ M.z * (k * ψ M.z * k⁻¹) := by
    rw [← hk]; group
  have hzz := M.zG_mul_self (ψ := ψ)
  rcases hu with rfl | rfl | rfl | rfl
  · exact Or.inl (by group)
  · exact Or.inr (Or.inr (Or.inl hk))
  · rcases h3 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · rw [hxz]
    rcases h3 with h | h <;> rw [h]
    · exact Or.inr (Or.inr (Or.inr (M.xG_comm_zG hH).symm))
    · refine Or.inr (Or.inl ?_)
      rw [← mul_assoc, ← M.xG_comm_zG hH, mul_assoc, hzz, mul_one]

theorem conj_mem_CG (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) {k : G}
    (hk : k * ψ M.x₀ * k⁻¹ = ψ M.z) (hkT : ∀ c ∈ M.CG ψ, k * c * k⁻¹ ∈ M.T.map ψ)
    (h3 : k * ψ M.z * k⁻¹ = ψ M.x₀ ∨ k * ψ M.z * k⁻¹ = ψ M.x₀ * ψ M.z) {c : G}
    (hc : c ∈ M.CG ψ) : k * c * k⁻¹ ∈ M.CG ψ := by
  obtain ⟨u, hu, hux⟩ : ∃ u ∈ M.UG ψ, k * u * k⁻¹ = ψ M.x₀ := by
    rcases h3 with h | h
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩
    · refine ⟨ψ M.x₀ * ψ M.z, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      calc k * (ψ M.x₀ * ψ M.z) * k⁻¹ = k * ψ M.x₀ * k⁻¹ * (k * ψ M.z * k⁻¹) := by group
        _ = ψ M.x₀ := by
          rw [hk, h, ← mul_assoc, ← M.xG_comm_zG hH, mul_assoc, M.zG_mul_self, mul_one]
  refine M.mem_CG_of hψ (hkT c hc) ?_
  rw [← hux]
  have h1 := M.comm_UG_CG hu hc
  calc k * c * k⁻¹ * (k * u * k⁻¹) = k * (u * c) * k⁻¹ := by rw [h1]; group
    _ = k * u * k⁻¹ * (k * c * k⁻¹) := by group

theorem not_two_dvd_index_T : ¬ 2 ∣ M.T.index := by
  have h := card_mul_index M.T
  rw [M.card_T, M.card_W] at h
  have h' : M.T.index = 42525 := by omega
  rw [h']
  decide

theorem exists_k [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) (hconj : IsConj (ψ M.z) (ψ M.x₀)) :
    ∃ k : G, k * ψ M.x₀ * k⁻¹ = ψ M.z ∧ ∀ c ∈ M.CG ψ, k * c * k⁻¹ ∈ M.T.map ψ := by
  obtain ⟨k₀, hk₀⟩ := isConj_iff.1 hconj.symm
  set K := (M.CG ψ).map (MulAut.conj k₀).toMonoidHom with hK
  have hKr : K ≤ ψ.range := by
    rintro _ ⟨c, hc, rfl⟩
    rw [hH]
    have h1 := M.comm_UG_CG (Or.inr (Or.inl rfl)) hc
    change k₀ * c * k₀⁻¹ * ψ M.z = ψ M.z * (k₀ * c * k₀⁻¹)
    rw [← hk₀]
    calc k₀ * c * k₀⁻¹ * (k₀ * ψ M.x₀ * k₀⁻¹) = k₀ * (ψ M.x₀ * c) * k₀⁻¹ := by rw [h1]; group
      _ = k₀ * ψ M.x₀ * k₀⁻¹ * (k₀ * c * k₀⁻¹) := by group
  have hQ : IsPGroup 2 (K.comap ψ) := IsPGroup.of_card (n := 13) (by
    rw [card_comap_of_le_range hψ hKr, hK, card_map_of_injective (MulAut.conj k₀).injective,
      M.card_CG hψ])
  obtain ⟨w, hw⟩ := exists_conj_le_sylow
    ((IsPGroup.of_card (n := 14) M.card_T).toSylow M.not_two_dvd_index_T) hQ
  refine ⟨ψ w * k₀, ?_, fun c hc => ?_⟩
  · calc ψ w * k₀ * ψ M.x₀ * (ψ w * k₀)⁻¹ = ψ w * (k₀ * ψ M.x₀ * k₀⁻¹) * (ψ w)⁻¹ := by group
      _ = ψ M.z := by rw [hk₀, M.zG_comm hH w]; group
  · obtain ⟨q, hq⟩ := hKr (show k₀ * c * k₀⁻¹ ∈ K from ⟨c, hc, rfl⟩)
    have hqQ : q ∈ K.comap ψ := by
      rw [mem_comap, hq]
      exact ⟨c, hc, rfl⟩
    have h1 := hw q hqQ
    refine ⟨w * q * w⁻¹, h1, ?_⟩
    rw [map_mul, map_mul, map_inv, hq]
    group

theorem exists_three_cycle [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) (hconj : IsConj (ψ M.z) (ψ M.x₀)) :
    ∃ n : G, (∀ c ∈ M.CG ψ, n * c * n⁻¹ ∈ M.CG ψ) ∧ (∀ u ∈ M.UG ψ, n * u * n⁻¹ ∈ M.UG ψ) ∧
      ∃ y₁ y₂ : G, n * ψ M.x₀ * n⁻¹ = y₁ ∧ n * y₁ * n⁻¹ = y₂ ∧ n * y₂ * n⁻¹ = ψ M.x₀ ∧
        y₁ ≠ ψ M.x₀ ∧ y₂ ≠ ψ M.x₀ := by
  obtain ⟨k, hk, hkT⟩ := M.exists_k hψ hH hconj
  have h3 := M.conj_z_eq hψ hH hk hkT
  have kC := fun c (hc : c ∈ M.CG ψ) => M.conj_mem_CG hψ hH hk hkT h3 hc
  have kU := fun u (hu : u ∈ M.UG ψ) => M.conj_mem_UG hH hk h3 hu
  have hzz := M.zG_mul_self (ψ := ψ)
  have hxz := M.xG_comm_zG hH
  have hxzx : ψ M.x₀ * ψ M.z ≠ ψ M.x₀ := fun h => M.x₀z_ne_x₀ (hψ (by rw [map_mul, h]))
  rcases h3 with h3 | h3
  · obtain ⟨t, ht, htx⟩ := M.exists_t
    have htx' : ψ t * ψ M.x₀ * (ψ t)⁻¹ = ψ M.x₀ * ψ M.z := by
      rw [← map_inv, ← map_mul, ← map_mul, htx, map_mul]
    have htz : ψ t * ψ M.z * (ψ t)⁻¹ = ψ M.z := by rw [M.zG_comm hH t]; group
    have tC : ∀ c ∈ M.CG ψ, ψ t * c * (ψ t)⁻¹ ∈ M.CG ψ := by
      rintro _ ⟨c, hc, rfl⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      exact mem_map_of_mem ψ (M.conj_mem_C ht hc)
    have tU : ∀ u ∈ M.UG ψ, ψ t * u * (ψ t)⁻¹ ∈ M.UG ψ := by
      rintro u (rfl | rfl | rfl | rfl)
      · exact Or.inl (by group)
      · exact Or.inr (Or.inr (Or.inr htx'))
      · exact Or.inr (Or.inr (Or.inl htz))
      · refine Or.inr (Or.inl ?_)
        calc ψ t * (ψ M.x₀ * ψ M.z) * (ψ t)⁻¹ =
              ψ t * ψ M.x₀ * (ψ t)⁻¹ * (ψ t * ψ M.z * (ψ t)⁻¹) := by group
          _ = ψ M.x₀ := by rw [htx', htz, mul_assoc, hzz, mul_one]
    refine ⟨k * ψ t, fun c hc => ?_, fun u hu => ?_, ψ M.x₀ * ψ M.z, ψ M.z, ?_, ?_, ?_, hxzx,
      (M.xG_ne_zG hψ).symm⟩
    · have e : k * ψ t * c * (k * ψ t)⁻¹ = k * (ψ t * c * (ψ t)⁻¹) * k⁻¹ := by group
      rw [e]
      exact kC _ (tC c hc)
    · have e : k * ψ t * u * (k * ψ t)⁻¹ = k * (ψ t * u * (ψ t)⁻¹) * k⁻¹ := by group
      rw [e]
      exact kU _ (tU u hu)
    · calc k * ψ t * ψ M.x₀ * (k * ψ t)⁻¹ = k * (ψ t * ψ M.x₀ * (ψ t)⁻¹) * k⁻¹ := by group
        _ = k * ψ M.x₀ * k⁻¹ * (k * ψ M.z * k⁻¹) := by rw [htx']; group
        _ = ψ M.x₀ * ψ M.z := by rw [hk, h3, hxz]
    · calc k * ψ t * (ψ M.x₀ * ψ M.z) * (k * ψ t)⁻¹ =
            k * (ψ t * ψ M.x₀ * (ψ t)⁻¹ * (ψ t * ψ M.z * (ψ t)⁻¹)) * k⁻¹ := by group
        _ = k * ψ M.x₀ * k⁻¹ := by
          rw [htx', htz, mul_assoc (ψ M.x₀) (ψ M.z) (ψ M.z), hzz, mul_one]
        _ = ψ M.z := hk
    · calc k * ψ t * ψ M.z * (k * ψ t)⁻¹ = k * (ψ t * ψ M.z * (ψ t)⁻¹) * k⁻¹ := by group
        _ = ψ M.x₀ := by rw [htz, h3]
  · refine ⟨k, fun c hc => kC c hc, fun u hu => kU u hu, ψ M.z, ψ M.x₀ * ψ M.z, hk, h3, ?_,
      (M.xG_ne_zG hψ).symm, hxzx⟩
    calc k * (ψ M.x₀ * ψ M.z) * k⁻¹ = k * ψ M.x₀ * k⁻¹ * (k * ψ M.z * k⁻¹) := by group
      _ = ψ M.x₀ := by rw [hk, h3, ← mul_assoc, ← hxz, mul_assoc, hzz, mul_one]

theorem card_frameVec : Nat.card FrameVec = 2 ^ 8 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_E1G (hψ : Function.Injective ψ) : Nat.card (ψ.comp M.ιE1).range = 2 ^ 8 := by
  rw [card_range_of_injective (ψ := ψ.comp M.ιE1) (hψ.comp M.ιE1_injective)]
  exact card_frameVec

theorem mem_E1G_iff (hψ : Function.Injective ψ) {w : W} :
    ψ w ∈ (ψ.comp M.ιE1).range ↔ w ∈ M.ιE1.range := by
  rw [MonoidHom.range_comp]
  exact ⟨fun h => mem_of_map_mem hψ h, fun h => mem_map_of_mem ψ h⟩

theorem elem_TG8 (hψ : Function.Injective ψ) {B : Subgroup G} (hB : B ≤ M.T.map ψ)
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : Nat.card B = 2 ^ 8) : B = (ψ.comp M.ιE1).range := by
  have hBr : B ≤ ψ.range := hB.trans (map_le_range ψ M.T)
  rw [← map_comap_eq_self hBr, M.elem_T _ (comap_le_of_le_map hψ hB)
    (fun b hb => hψ (by rw [map_mul, map_one]; exact hB2 _ hb))
    (by rw [card_comap_of_le_range hψ hBr, hBc]), MonoidHom.range_comp]

theorem conj_x₀_eq [Finite G] (hψ : Function.Injective ψ) {d : G}
    (hdC : ∀ c ∈ M.CG ψ, d * c * d⁻¹ ∈ M.CG ψ) (hdU : ∀ u ∈ M.UG ψ, d * u * d⁻¹ ∈ M.UG ψ)
    {m : ℕ} (hm : Odd m) (hdm : d ^ m = 1) : d * ψ M.x₀ * d⁻¹ = ψ M.x₀ := by
  have hE1C : (ψ.comp M.ιE1).range ≤ M.CG ψ := by
    rintro _ ⟨v, rfl⟩
    exact mem_map_of_mem ψ (M.ιE1_mem_C v)
  have hdE : d ∈ normalizer ((ψ.comp M.ιE1).range : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro e he
    have hB := M.elem_TG8 hψ (B := ((ψ.comp M.ιE1).range).map (MulAut.conj d).toMonoidHom)
      (by rintro _ ⟨e', he', rfl⟩; exact M.CG_le_TG (hdC _ (hE1C he')))
      (by
        rintro _ ⟨e', he', rfl⟩
        change d * e' * d⁻¹ * (d * e' * d⁻¹) = 1
        calc d * e' * d⁻¹ * (d * e' * d⁻¹) = d * (e' * e') * d⁻¹ := by group
          _ = 1 := by rw [mul_self_of_mem_frameRange he']; group)
      (by rw [card_map_of_injective (MulAut.conj d).injective, M.card_E1G hψ])
    rw [← hB]
    exact ⟨e, he, rfl⟩
  have hzcG : ∀ s ∈ M.T ⊓ centralizer ({M.x₀} : Set W),
      (∀ d' ∈ M.T ⊓ centralizer ({M.x₀} : Set W), s * d' * s⁻¹ * d'⁻¹ ∈ M.ιE1.range) →
      ∀ c ∈ M.CG ψ, ψ s * c * (ψ s)⁻¹ * c⁻¹ ∈ (ψ.comp M.ιE1).range := by
    rintro s - hs _ ⟨c, hc, rfl⟩
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, M.mem_E1G_iff hψ]
    exact hs c hc
  refine conj_eq_of_odd_of_zc (C := M.CG ψ) (E := (ψ.comp M.ιE1).range) (s₁ := ψ M.s₁)
    (s₂ := ψ M.s₂) (U := M.UG ψ) (fun a ha b hb => comm_of_mem_frameRange ha hb)
    (mem_map_of_mem ψ M.s₁_mem) (mem_map_of_mem ψ M.s₂_mem) (hzcG _ M.s₁_mem M.zc_s₁)
    (hzcG _ M.s₂_mem M.zc_s₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Or.inr (Or.inl rfl)) (M.xG_ne_one hψ)
    (mem_normalizer_of_conj_mem hdC) hdE hdU hm hdm
  · rintro _ ⟨c, hc, rfl⟩ hcent
    have h := M.zc c hc fun d' hd' => by
      rw [← M.mem_E1G_iff hψ, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hcent _ (mem_map_of_mem ψ hd')
    rcases h with h | h | h | h
    · exact Or.inl ((M.mem_E1G_iff hψ).2 h)
    · exact Or.inr (Or.inl (by rw [← map_inv, ← map_mul, M.mem_E1G_iff hψ]; exact h))
    · exact Or.inr (Or.inr (Or.inl (by rw [← map_inv, ← map_mul, M.mem_E1G_iff hψ]; exact h)))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [← map_mul, ← map_inv, ← map_mul, M.mem_E1G_iff hψ]; exact h)))
  · rw [M.mem_E1G_iff hψ]
    exact M.s₁_not_mem
  · rw [M.mem_E1G_iff hψ]
    exact M.s₂_not_mem
  · rw [← map_inv, ← map_mul, M.mem_E1G_iff hψ]
    exact M.inv_mul_not_mem
  · rw [← map_mul, MonoidHom.range_comp, card_inf_centralizer_map hψ,
      card_inf_centralizer_map hψ]
    exact M.card_ne₁
  · rw [← map_mul, MonoidHom.range_comp, card_inf_centralizer_map hψ,
      card_inf_centralizer_map hψ]
    exact M.card_ne₂
  · obtain ⟨e, he, hex⟩ := M.comm_eq
    exact ⟨ψ e, (M.mem_E1G_iff hψ).2 he, by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hex]⟩
  · rintro _ ⟨v, rfl⟩ hU
    have hcomm : (ψ.comp M.ιE1) v * ψ M.s₁ * ((ψ.comp M.ιE1) v)⁻¹ * (ψ M.s₁)⁻¹ =
        ψ (M.ιE1 v * M.s₁ * (M.ιE1 v)⁻¹ * M.s₁⁻¹) := by
      rw [MonoidHom.comp_apply, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hcomm] at hU ⊢
    obtain ⟨hne₁, hne₂⟩ := M.comm_ne _ ⟨v, rfl⟩
    rcases hU with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (hψ h) hne₁
    · exact absurd (hψ (h.trans (map_mul ψ _ _).symm)) hne₂

theorem not_isConj [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ M.z = ψ M.z * g) : ¬ IsConj (ψ M.z) (ψ M.x₀) := by
  intro hconj
  obtain ⟨n, hnC, hnU, y₁, y₂, h1, h2, h3, hy₁, hy₂⟩ := M.exists_three_cycle hψ hH hconj
  obtain ⟨a, m, hm, hdm⟩ := exists_pow_two_pow_odd n
  have hpow : ∀ {S : Set G}, (∀ u ∈ S, n * u * n⁻¹ ∈ S) →
      ∀ j : ℕ, ∀ u ∈ S, n ^ j * u * (n ^ j)⁻¹ ∈ S := by
    intro S hS j
    induction j with
    | zero => intro u hu; simpa using hu
    | succ j ih => intro u hu; rw [conj_pow_succ]; exact hS _ (ih u hu)
  exact conj_pow_two_pow_ne h1 h2 h3 hy₁ hy₂ a
    (M.conj_x₀_eq hψ (hpow (S := M.CG ψ) hnC _) (hpow hnU _) hm hdm)

end GSide

end Child8Weyl

end CFSG.EvenSmallLie.OmegaEight.Child8
