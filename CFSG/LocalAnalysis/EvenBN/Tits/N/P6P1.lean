module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Act

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem mem_map_conj_iff {P : Subgroup G} {k v : G} :
    v ∈ P.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * v * k ∈ P := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : k⁻¹ * (MulAut.conj k).toMonoidHom x * k = x := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hx
  · intro h
    refine ⟨k⁻¹ * v * k, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem isElemAbelian_map_conj {p : ℕ} {P : Subgroup G} (hP : IsElemAbelian p P) (k : G) :
    IsElemAbelian p (P.map (MulAut.conj k).toMonoidHom) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have ha := mem_map_conj_iff.1 a.2
    have hb := mem_map_conj_iff.1 b.2
    have h := mul_comm_of_isElemAbelian hP ha hb
    show (a : G) * b = b * a
    calc (a : G) * b = k * ((k⁻¹ * a * k) * (k⁻¹ * b * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * b * k) * (k⁻¹ * a * k)) * k⁻¹ := by rw [h]
      _ = b * a := by group
  · have hx' := mem_map_conj_iff.1 hx
    have h := hP.2 _ hx'
    calc x ^ p = (k * (k⁻¹ * x * k) * k⁻¹) ^ p := by group
      _ = k * (k⁻¹ * x * k) ^ p * k⁻¹ := conj_pow
      _ = 1 := by rw [h]; group

theorem conj_mem_normalizer_map {P N' : Subgroup G} {k n : G} (hn : n ∈ N')
    (hPn : ∀ n ∈ N', ∀ x ∈ P, n * x * n⁻¹ ∈ P) :
    k * n * k⁻¹ ∈ normalizer ((P.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro v
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have e : k⁻¹ * (k * n * k⁻¹ * v * (k * n * k⁻¹)⁻¹) * k = n * (k⁻¹ * v * k) * n⁻¹ := by group
  rw [e]
  constructor
  · intro hx
    exact hPn n hn _ hx
  · intro hx
    have h := hPn n⁻¹ (N'.inv_mem hn) _ hx
    have e2 : n⁻¹ * (n * (k⁻¹ * v * k) * n⁻¹) * n⁻¹⁻¹ = k⁻¹ * v * k := by group
    rwa [e2] at h

theorem inf_centralizer_normalizer_eq_bot {V P₁ Nn : Subgroup G} {t k s : G}
    (hVk : V = P₁.map (MulAut.conj k).toMonoidHom)
    (hPn : ∀ n ∈ Nn, ∀ x ∈ P₁, n * x * n⁻¹ ∈ P₁)
    (hC1 : P₁ ⊓ centralizer ((Nn ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥)
    (hks : k * t * k⁻¹ = s) :
    V ⊓ centralizer ((normalizer (V : Set G) ⊓ centralizer ({s} : Set G) : Subgroup G) : Set G) =
      ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.1 hv
  have hx : k⁻¹ * v * k ∈ P₁ := mem_map_conj_iff.1 (hVk ▸ hvV)
  have hxC : k⁻¹ * v * k ∈
      centralizer ((Nn ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨hnN, hnt⟩ := Subgroup.mem_inf.1 hn
    have hnt' : n * t = t * n := mem_centralizer_singleton_iff.1 hnt
    have hn'V : k * n * k⁻¹ ∈ normalizer (V : Set G) := by
      rw [hVk]
      exact conj_mem_normalizer_map hnN hPn
    have hn's : k * n * k⁻¹ ∈ centralizer ({s} : Set G) := by
      rw [mem_centralizer_singleton_iff, ← hks]
      calc k * n * k⁻¹ * (k * t * k⁻¹) = k * (n * t) * k⁻¹ := by group
        _ = k * (t * n) * k⁻¹ := by rw [hnt']
        _ = k * t * k⁻¹ * (k * n * k⁻¹) := by group
    have h := Subgroup.mem_centralizer_iff.1 hvC (k * n * k⁻¹) (Subgroup.mem_inf.2 ⟨hn'V, hn's⟩)
    calc n * (k⁻¹ * v * k) = k⁻¹ * ((k * n * k⁻¹) * v) * k := by group
      _ = k⁻¹ * (v * (k * n * k⁻¹)) * k := by rw [h]
      _ = k⁻¹ * v * k * n := by group
  have h1 : k⁻¹ * v * k ∈ P₁ ⊓ centralizer
      ((Nn ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := Subgroup.mem_inf.2 ⟨hx, hxC⟩
  rw [hC1, Subgroup.mem_bot] at h1
  have : v = 1 := by
    calc v = k * (k⁻¹ * v * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [this]
  exact one_mem _

theorem card_inf_centralizer_eq [Finite G] {V B : Subgroup G} {k s : G} (hV : IsElemAbelian 2 V)
    (hV10 : Nat.card V = 2 ^ 10) (hs2 : s * s = 1)
    (hD : zpowers s ⊔ (V ⊓ centralizer ({s} : Set G)) = B.map (MulAut.conj k).toMonoidHom)
    (hBcard : Nat.card B = 2 ^ 6) : Nat.card ↥(V ⊓ centralizer ({s} : Set G)) = 2 ^ 5 := by
  have hDcard : Nat.card ↥(zpowers s ⊔ (V ⊓ centralizer ({s} : Set G))) = 2 ^ 6 := by
    rw [hD, Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hBcard
  have hsV : s ∉ V := by
    intro hsV
    have hle : V ≤ centralizer ({s} : Set G) := fun v hv =>
      mem_centralizer_singleton_iff.2 (mul_comm_of_isElemAbelian hV hv hsV)
    have hinf : V ⊓ centralizer ({s} : Set G) = V := inf_eq_left.2 hle
    have hsup : zpowers s ⊔ V = V := sup_eq_right.2 (zpowers_le.2 hsV)
    rw [hinf, hsup, hV10] at hDcard
    omega
  have hn : ∀ p ∈ V ⊓ centralizer ({s} : Set G), s * p * s⁻¹ ∈ V ⊓ centralizer ({s} : Set G) := by
    intro p hp
    have hps : p * s = s * p := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hp).2
    have : s * p * s⁻¹ = p := by rw [← hps]; group
    rwa [this]
  have hsP : s ∉ V ⊓ centralizer ({s} : Set G) := fun h => hsV (Subgroup.mem_inf.1 h).1
  have hc := card_sup_zpowers hs2 hn hsP
  rw [sup_comm] at hDcard
  rw [hDcard] at hc
  omega

theorem z_facts [Finite G] {V Z : Subgroup G} {s : G} (hZV : Z ≤ V) (hZ4 : Nat.card Z = 4)
    (hZH : ∀ h ∈ normalizer (V : Set G), ∀ z ∈ Z, h * z * h⁻¹ ∈ Z)
    (hC : V ⊓ centralizer
      ((normalizer (V : Set G) ⊓ centralizer ({s} : Set G) : Subgroup G) : Set G) = ⊥)
    (hsH : s ∈ normalizer (V : Set G)) (hs2 : s * s = 1) :
    (∀ z ∈ Z, s * z = z * s) ∧ ∃ y ∈ normalizer (V : Set G), y * s = s * y ∧
      IsPGroup 3 (zpowers y) ∧ ∃ z ∈ Z, y * z ≠ z * y := by
  have hRZ : ∀ r ∈ normalizer (V : Set G) ⊓ centralizer ({s} : Set G), ∀ z ∈ Z,
      r * z * r⁻¹ ∈ Z := fun r hr z hz => hZH r (Subgroup.mem_inf.1 hr).1 z hz
  have hfix : ∀ z ∈ Z, (∀ r ∈ normalizer (V : Set G) ⊓ centralizer ({s} : Set G),
      r * z = z * r) → z = 1 := by
    intro z hz h
    have : z ∈ V ⊓ centralizer
        ((normalizer (V : Set G) ⊓ centralizer ({s} : Set G) : Subgroup G) : Set G) :=
      Subgroup.mem_inf.2 ⟨hZV hz, Subgroup.mem_centralizer_iff.2 fun r hr => h r hr⟩
    rw [hC, Subgroup.mem_bot] at this
    exact this
  have hsR : s ∈ normalizer (V : Set G) ⊓ centralizer ({s} : Set G) :=
    Subgroup.mem_inf.2 ⟨hsH, mem_centralizer_singleton_iff.2 rfl⟩
  have hsc : ∀ r ∈ normalizer (V : Set G) ⊓ centralizer ({s} : Set G), r * s = s * r :=
    fun r hr => mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hr).2
  refine ⟨comm_of_central_involution hZ4 hRZ hfix hsR hsc hs2, ?_⟩
  obtain ⟨y, hyR, hy3, hz⟩ := exists_isPGroup_three_not_comm hZ4 hRZ hfix
  obtain ⟨hyH, hys⟩ := Subgroup.mem_inf.1 hyR
  exact ⟨y, hyH, mem_centralizer_singleton_iff.1 hys, hy3, hz⟩

theorem p1_case_core [Finite G] {V P₁ Nn B Z : Subgroup G} {t k s : G}
    (hVk : V = P₁.map (MulAut.conj k).toMonoidHom) (hP1 : IsElemAbelian 2 P₁)
    (hP1card : Nat.card P₁ = 2 ^ 10) (hPn : ∀ n ∈ Nn, ∀ x ∈ P₁, n * x * n⁻¹ ∈ P₁)
    (hC1 : P₁ ⊓ centralizer ((Nn ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥)
    (ht2 : t * t = 1) (hks : k * t * k⁻¹ = s)
    (hD : zpowers s ⊔ (V ⊓ centralizer ({s} : Set G)) = B.map (MulAut.conj k).toMonoidHom)
    (hBcard : Nat.card B = 2 ^ 6) (hsH : s ∈ normalizer (V : Set G)) (hZV : Z ≤ V)
    (hZ4 : Nat.card Z = 4) (hZH : ∀ h ∈ normalizer (V : Set G), ∀ z ∈ Z, h * z * h⁻¹ ∈ Z) :
    IsElemAbelian 2 V ∧ Nat.card V = 2 ^ 10 ∧ s * s = 1 ∧
      Nat.card ↥(V ⊓ centralizer ({s} : Set G)) = 2 ^ 5 ∧ (∀ z ∈ Z, s * z = z * s) ∧
      ∃ y ∈ normalizer (V : Set G), y * s = s * y ∧ IsPGroup 3 (zpowers y) ∧
        ∃ z ∈ Z, y * z ≠ z * y := by
  have hV : IsElemAbelian 2 V := hVk ▸ isElemAbelian_map_conj hP1 k
  have hV10 : Nat.card V = 2 ^ 10 := by
    rw [hVk, Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hP1card
  have hs2 : s * s = 1 := by
    rw [← hks]
    calc k * t * k⁻¹ * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hC := inf_centralizer_normalizer_eq_bot hVk hPn hC1 hks
  obtain ⟨hZs, hy⟩ := z_facts hZV hZ4 hZH hC hsH hs2
  exact ⟨hV, hV10, hs2, card_inf_centralizer_eq hV hV10 hs2 hD hBcard, hZs, hy⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
