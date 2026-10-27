module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundAut

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.Assembly.LowTwoRank


section Conj

variable {G : Type} [Group G]

@[expose] def conjAut (K : Subgroup G) (t : G) (ht : t ∈ normalizer (K : Set G)) : MulAut ↥K where
  toFun k := ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.1 ht k).1 k.2⟩
  invFun k := ⟨t⁻¹ * k * t, (Subgroup.mem_normalizer_iff.1 ht (t⁻¹ * k * t)).2
    (by simp [mul_assoc])⟩
  left_inv k := by ext; simp [mul_assoc]
  right_inv k := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjAut_apply {K : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G)) (k : ↥K) :
    ((conjAut K t ht k : ↥K) : G) = t * k * t⁻¹ := rfl

theorem mem_fixedSubgroup_conjAut {K : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G)) (k : ↥K) :
    k ∈ fixedSubgroup ↥K (conjAut K t ht) ↔ (k : G) ∈ centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  show conjAut K t ht k = k ↔ _
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [conjAut_apply] at h1
    calc (k : G) * t = (t * k * t⁻¹) * t := by rw [h1]
      _ = t * k := by group
  · intro h
    apply Subtype.ext
    rw [conjAut_apply]
    calc t * (k : G) * t⁻¹ = ((k : G) * t) * t⁻¹ := by rw [h]
      _ = k := by group

theorem map_fixedSubgroup_conjAut {K : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G)) :
    (fixedSubgroup ↥K (conjAut K t ht)).map K.subtype = K ⊓ centralizer ({t} : Set G) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, (mem_fixedSubgroup_conjAut ht k).1 hk⟩
  · rintro ⟨hxK, hxc⟩
    exact ⟨⟨x, hxK⟩, (mem_fixedSubgroup_conjAut ht ⟨x, hxK⟩).2 hxc, rfl⟩

theorem conjAut_mul_self {K : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G)) (ht2 : t * t = 1) :
    conjAut K t ht * conjAut K t ht = 1 := by
  ext k
  show t * (t * (k : G) * t⁻¹) * t⁻¹ = k
  calc t * (t * (k : G) * t⁻¹) * t⁻¹ = (t * t) * (k : G) * (t * t)⁻¹ := by group
    _ = k := by rw [ht2]; group

theorem conjAut_mem_range_iff {K : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G)) :
    conjAut K t ht ∈ (MulAut.conj : ↥K →* MulAut ↥K).range ↔
      ∃ a ∈ K, ∀ k ∈ K, t * k * t⁻¹ = a * k * a⁻¹ := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, a.2, fun k hk => ?_⟩
    have := congrArg Subtype.val (DFunLike.congr_fun ha ⟨k, hk⟩)
    simpa [conjAut_apply, MulAut.conj_apply] using this.symm
  · rintro ⟨a, ha, h⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    ext k
    simp [conjAut_apply, MulAut.conj_apply, h k k.2]

theorem pPrimeCoreOf_eq_bot_of_fixed {K : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G))
    (h : pPrimeCore 2 ↥(fixedSubgroup ↥K (conjAut K t ht)) = ⊥) :
    pPrimeCoreOf 2 (K ⊓ centralizer ({t} : Set G)) = ⊥ := by
  have hX := map_fixedSubgroup_conjAut ht
  let D := fixedSubgroup ↥K (conjAut K t ht)
  let eD : ↥D ≃* ↥(K ⊓ centralizer ({t} : Set G)) :=
    (D.equivMapOfInjective K.subtype K.subtype_injective).trans (MulEquiv.subgroupCongr hX)
  have hmap := pPrimeCore_map_iso 2 eD
  rw [h, Subgroup.map_bot] at hmap
  unfold pPrimeCoreOf
  rw [← hmap, Subgroup.map_bot]

theorem card_pPrimeCoreOf_dvd_of_fixed {K : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G))
    {m : ℕ} (h : Nat.card ↥(fixedSubgroup ↥K (conjAut K t ht)) = m) :
    Nat.card ↥(pPrimeCoreOf 2 (K ⊓ centralizer ({t} : Set G))) ∣ m := by
  have hX := map_fixedSubgroup_conjAut ht
  have hcard : Nat.card ↥(K ⊓ centralizer ({t} : Set G)) = m := by
    rw [← h, ← hX]
    exact Subgroup.card_map_of_injective K.subtype_injective
  rw [← hcard]
  exact Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)

theorem mem_sup_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩
    · exact ⟨1, H.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := hx
    obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := hy
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
      _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hc h₂ hh₂ k₁ hk₁]
      _ = h₁ * h₂ * (k₁ * k₂) := by group
  | inv x _ hx =>
    obtain ⟨h, hh, k, hk, rfl⟩ := hx
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    calc (h * k)⁻¹ = k⁻¹ * h⁻¹ := by group
      _ = h⁻¹ * k⁻¹ := by
        have := hc h hh k hk
        calc k⁻¹ * h⁻¹ = (h * k)⁻¹ := by group
          _ = (k * h)⁻¹ := by rw [this]
          _ = h⁻¹ * k⁻¹ := by group

end Conj

section SL2

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F]

theorem pPrimeCoreOf_eq_bot_of_central {K : Subgroup G} (e : ↥K ≃* SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) {t : G} (hcen : ∀ k ∈ K, k * t = t * k) :
    pPrimeCoreOf 2 (K ⊓ centralizer ({t} : Set G)) = ⊥ := by
  have hle : K ≤ centralizer ({t} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcen k hk)
  rw [inf_eq_left.2 hle]
  unfold pPrimeCoreOf
  rw [pPrimeCore_eq_bot_of_equiv e hodd h3, Subgroup.map_bot]

theorem bound_outer {K : Subgroup G} (e : ↥K ≃* SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) {t : G} (ht : t ∈ normalizer (K : Set G))
    (ht2 : t * t = 1) (hout : ¬ ∃ a ∈ K, ∀ k ∈ K, t * k * t⁻¹ = a * k * a⁻¹) :
    Nat.card ↥(pPrimeCoreOf 2 (K ⊓ centralizer ({t} : Set G))) ∣
      (if Nat.card F % 4 = 1 then Nat.card F + 1 else Nat.card F - 1) := by
  have hφ2 := conjAut_mul_self ht ht2
  have hout' : conjAut K t ht ∉ (MulAut.conj : ↥K →* MulAut ↥K).range :=
    fun h => hout ((conjAut_mem_range_iff ht).1 h)
  rcases fixed_outer e hodd h3 _ hφ2 hout' with h | h
  · rw [pPrimeCoreOf_eq_bot_of_fixed ht h]
    simp
  · exact card_pPrimeCoreOf_dvd_of_fixed ht h

theorem bound_fused {K₁ K₂ : Subgroup G} (e : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) {t : G} (htK : t ∈ K₁ ⊔ K₂) (ht2 : t * t = 1) :
    Nat.card ↥(pPrimeCoreOf 2 (K₁ ⊓ centralizer ({t} : Set G))) ∣
      (if Nat.card F % 4 = 1 then Nat.card F - 1 else Nat.card F + 1) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm htK
  have hab : a * b = b * a := hcomm a ha b hb
  have haa : a * a * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hab]
      _ = a * b * (a * b) := by group
      _ = 1 := ht2
  have hab2 : a * a ∈ K₂ := by
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left haa
    rw [this]
    exact K₂.inv_mem (K₂.mul_mem hb hb)
  have ha2c : (⟨a, ha⟩ : ↥K₁) * ⟨a, ha⟩ ∈ center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact hcomm k k.2 (a * a) hab2
  by_cases hac : (⟨a, ha⟩ : ↥K₁) ∈ center ↥K₁
  · have hcen : ∀ k ∈ K₁, k * (a * b) = (a * b) * k := by
      intro k hk
      have h1 : (k : G) * a = a * k := by
        have := Subgroup.mem_center_iff.1 hac ⟨k, hk⟩
        exact congrArg Subtype.val this
      have h2 : k * b = b * k := hcomm k hk b hb
      calc k * (a * b) = (k * a) * b := by group
        _ = (a * k) * b := by rw [h1]
        _ = a * (k * b) := by group
        _ = a * (b * k) := by rw [h2]
        _ = (a * b) * k := by group
    rw [pPrimeCoreOf_eq_bot_of_central e hodd h3 hcen]
    simp
  · have hmap : (centralizer ({(⟨a, ha⟩ : ↥K₁)} : Set ↥K₁)).map K₁.subtype =
        K₁ ⊓ centralizer ({a * b} : Set G) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨k.2, ?_⟩
        have hk' : k ∈ centralizer ({(⟨a, ha⟩ : ↥K₁)} : Set ↥K₁) := hk
        rw [Subgroup.mem_centralizer_singleton_iff] at hk'
        show (k : G) ∈ centralizer ({a * b} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : (k : G) * a = a * k := congrArg Subtype.val hk'
        have h2 : (k : G) * b = b * k := hcomm k k.2 b hb
        calc (k : G) * (a * b) = (k * a) * b := by group
          _ = (a * k) * b := by rw [h1]
          _ = a * (k * b) := by group
          _ = a * (b * k) := by rw [h2]
          _ = (a * b) * k := by group
      · rintro ⟨hxK, hxc⟩
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        have hxc' : x ∈ centralizer ({a * b} : Set G) := hxc
        rw [Subgroup.mem_centralizer_singleton_iff] at hxc'
        show (⟨x, hxK⟩ : ↥K₁) ∈ centralizer ({(⟨a, ha⟩ : ↥K₁)} : Set ↥K₁)
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        have h2 : x * b = b * x := hcomm x hxK b hb
        show x * a = a * x
        have h3 : x * (a * b) = (a * b) * x := hxc'
        have : (x * a) * b = (a * x) * b := by
          calc (x * a) * b = x * (a * b) := by group
            _ = (a * b) * x := h3
            _ = a * (b * x) := by group
            _ = a * (x * b) := by rw [h2]
            _ = (a * x) * b := by group
        exact mul_right_cancel this
    have hcard : Nat.card ↥(K₁ ⊓ centralizer ({a * b} : Set G)) =
        if Nat.card F % 4 = 1 then Nat.card F - 1 else Nat.card F + 1 := by
      rw [← hmap, Subgroup.card_map_of_injective K₁.subtype_injective]
      exact card_centralizer_of_sq_mem_center e hodd ha2c hac
    rw [← hcard]
    exact Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)

end SL2

end CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound
