module

public import CFSG.GH74.GLS.C3.Layer1.Back114Defs
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G]

theorem Q_inf_conj_of [Finite G] {a : G} {Q T S : Subgroup G} (hS : IsPGroup 2 ↥S) (hTS : T ≤ S)
    (haS : a ∈ S) (haN : a ∈ normalizer (T : Set G)) (haT : a ∉ T) (ha2 : a * a ∈ T)
    (hQT : Q ≤ T) (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hcent : ∀ u ∈ Q, u ≠ 1 → (∀ t ∈ T, u * t = t * u) → ∀ s ∈ S, s * u = u * s → s ∈ T) :
    Q ⊓ conjugate Q a = ⊥ := by
  by_contra hne
  have hT2 : IsPGroup 2 ↥T := hS.to_le hTS
  have haNT : ∀ t ∈ T, a * t * a⁻¹ ∈ T := fun t ht => (Subgroup.mem_normalizer_iff.1 haN t).1 ht
  have haNT' : ∀ t ∈ T, a⁻¹ * t * a ∈ T := by
    intro t ht
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem haN) t).1 ht
    simpa using this
  have hHS : T ⊔ zpowers a ≤ S := sup_le hTS (zpowers_le.2 haS)
  have hH : IsPGroup 2 ↥(T ⊔ zpowers a) := hS.to_le hHS
  have hQan : ∀ t ∈ T, ∀ y ∈ conjugate Q a, t * y * t⁻¹ ∈ conjugate Q a := by
    intro t ht y hy
    rw [mem_conjugate_iff'] at hy ⊢
    have h1 := hQn (a * t * a⁻¹) (haNT t ht) _ hy
    have e : a * t * a⁻¹ * (a * y * a⁻¹) * (a * t * a⁻¹)⁻¹ = a * (t * y * t⁻¹) * a⁻¹ := by group
    rwa [e] at h1
  have hWn : ∀ t ∈ T, ∀ w ∈ Q ⊓ conjugate Q a, t * w * t⁻¹ ∈ Q ⊓ conjugate Q a :=
    fun t ht w hw => ⟨hQn t ht w hw.1, hQan t ht w hw.2⟩
  have hTnorm : T ≤ normalizer ((Q ⊓ conjugate Q a : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_of_two_sided (hWn t ht)
      (fun w hw => by simpa using hWn t⁻¹ (T.inv_mem ht) w hw)
  have haW : a ∈ normalizer ((Q ⊓ conjugate Q a : Subgroup G) : Set G) := by
    refine mem_normalizer_of_two_sided (fun w hw => Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      (fun w hw => Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact mem_conjugate_iff'.1 hw.2
    · rw [mem_conjugate_iff']
      have := hQn (a * a) ha2 w hw.1
      have e : a * (a * w * a⁻¹) * a⁻¹ = a * a * w * (a * a)⁻¹ := by group
      rw [e]
      exact this
    ·
      have hy := mem_conjugate_iff'.1 hw.2
      have h1 := hQn (a * a)⁻¹ (T.inv_mem ha2) _ hy
      have e : (a * a)⁻¹ * (a * w * a⁻¹) * (a * a)⁻¹⁻¹ = a⁻¹ * w * a := by group
      rwa [e] at h1
    · rw [mem_conjugate_iff']
      have e : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
      rw [e]
      exact hw.1
  have hHn : T ⊔ zpowers a ≤ normalizer ((Q ⊓ conjugate Q a : Subgroup G) : Set G) :=
    sup_le hTnorm (zpowers_le.2 haW)
  obtain ⟨w, hwW, hw1, hwc⟩ := exists_central_of_normal hH
    (fun x hx w hw => (Subgroup.mem_normalizer_iff.1 (hHn hx) w).1 hw)
    (inf_le_left.trans (hQT.trans le_sup_left)) hne
  exact haT (hcent w hwW.1 hw1 (fun t ht => (hwc t (Subgroup.mem_sup_left ht)).symm) a haS
    (hwc a (Subgroup.mem_sup_right (mem_zpowers a))))

theorem aconfigW_cent6 [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a) :
    ∀ u ∈ Q, u ≠ 1 → (∀ t ∈ T, u * t = t * u) → ∀ s ∈ S, s * u = u * s → s ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥S := h.sylowS.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := h.T_le_C
  have hxQ : x ∈ Q := h.x_mem_Q
  intro u hu hu1 huT s hsS hsu
  have hsyl : IsSylowOf 2 T (centralizer ({u} : Set G)) := by
    by_cases hQT : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q
    · exact h.cond6 hQT u hu hu1
    · push Not at hQT
      obtain ⟨q₀, hq₀, t₀, ht₀, hq₀t₀⟩ := hQT
      have hux : u = x := by
        by_contra hne
        classical
        have hxc : ∀ t ∈ T, x * t = t * x := fun t ht =>
          (mem_centralizer_singleton_iff.1 (hTC ht)).symm
        have hx1 : x ≠ 1 := h.x_ne_one
        set Z : Subgroup G := Q ⊓ centralizer (T : Set G) with hZdef
        have hxZ : x ∈ Z := ⟨hxQ, fun t ht => (hxc t ht).symm⟩
        have huZ : u ∈ Z := ⟨hu, fun t ht => (huT t ht).symm⟩
        have hq₀Z : q₀ ∉ Z := fun hz => hq₀t₀ (hz.2 t₀ ht₀).symm
        have hZQ : Z ≤ Q := inf_le_left
        have hdvd : Nat.card ↥Z ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hZQ
        rw [h.card_Q] at hdvd
        have hne4 : Nat.card ↥Z ≠ 4 := by
          intro h4
          have := Subgroup.eq_of_le_of_card_ge hZQ (by rw [h4, h.card_Q])
          exact hq₀Z (this ▸ hq₀)
        have h3 : 3 ≤ Nat.card ↥Z := by
          have hsub : (({1, x, u} : Finset G) : Set G) ⊆ (Z : Set G) := by
            intro y hy
            simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
              Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl | rfl
            · exact one_mem _
            · exact hxZ
            · exact huZ
          have hcard3 : ({1, x, u} : Finset G).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_singleton]
            · simp only [Finset.mem_singleton]
              exact fun h0 => hne h0.symm
            · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨fun h0 => hx1 h0.symm, fun h0 => hu1 h0.symm⟩
          calc 3 = ({1, x, u} : Finset G).card := hcard3.symm
            _ = (({1, x, u} : Finset G) : Set G).ncard := (Set.ncard_coe_finset _).symm
            _ ≤ (Z : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
            _ = Nat.card ↥Z := (Nat.card_coe_set_eq _).symm
        have hc4 : Nat.card ↥Z ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        have hc3 : Nat.card ↥Z = 3 := by omega
        rw [hc3] at hdvd
        norm_num at hdvd
      rw [hux]
      exact h.sylowT
  have hsC : s ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 hsu
  have hle : T ⊔ zpowers s ≤ centralizer ({u} : Set G) := sup_le hsyl.le (zpowers_le.2 hsC)
  have hleS : T ⊔ zpowers s ≤ S := sup_le h.T_lt_S.le (zpowers_le.2 hsS)
  have heq : T ⊔ zpowers s = T := hsyl.eq_of_le le_sup_left hle (hS2.to_le hleS)
  exact heq ▸ Subgroup.mem_sup_right (mem_zpowers s)

theorem aconfigW_Q_inf_conj [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a) : Q ⊓ conjugate Q a = ⊥ := by
  have hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    have hCnorm : centralizer ({x} : Set G) ≤ normalizer (K : Set G) := fun c hc =>
      mem_normalizer_of_two_sided (fun w hw => h.normalInC c hc w hw) (fun w hw => by
        simpa using h.normalInC c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc) w hw)
    have hNxK : t ∈ NxK x K := ⟨h.T_le_C ht, hCnorm (h.T_le_C ht)⟩
    have hQ := h.hQ
    rw [hQ] at hq ⊢
    refine ⟨T.mul_mem (T.mul_mem ht hq.1) (T.inv_mem ht), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (NxK_le_normalizer_CxK x K hNxK) q).1 hq.2
  exact Q_inf_conj_of h.sylowS.isPGroup h.T_lt_S.le h.a_mem.1 h.a_mem.2.1 h.a_mem.2.2.1
    (by rw [← sq]; exact h.a_mem.2.2.2) h.Q_le_T hQn (aconfigW_cent6 h)

end CFSG.GH74.GLS.C3.Layer1.Bk
