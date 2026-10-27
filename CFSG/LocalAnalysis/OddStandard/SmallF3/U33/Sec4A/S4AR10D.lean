module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR10B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11E
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup CFSG.Open

section Abstract

variable {G : Type} [Group G]

theorem exists_sub_card_sixteen [Finite G] {E : Subgroup G} (hE : IsPGroup 2 E)
    (h16 : 16 ≤ Nat.card E) : ∃ K : Subgroup G, K ≤ E ∧ Nat.card K = 16 := by
  obtain ⟨n, hn⟩ := hE.exists_card_eq
  have hn4 : 4 ≤ n := by
    by_contra h
    have h3 : n ≤ 3 := by omega
    have h8 : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) h3
    omega
  have hdvd : 2 ^ 4 ∣ Nat.card E := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 hn4
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 hdvd
  refine ⟨K.map E.subtype, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
    norm_num

variable {R Z X Y : Subgroup G}

theorem SL34Data.X_elem (h : SL34Data R Z X Y) : IsElemAbelian 2 X :=
  ⟨⟨⟨fun a b => Subtype.ext (h.X_comm a a.2 b b.2)⟩⟩, fun x hx => by
    rw [pow_two]
    exact h.X_sq x hx⟩

theorem SL34Data.Y_elem (h : SL34Data R Z X Y) : IsElemAbelian 2 Y :=
  h.symm.X_elem

theorem r10_contra_aux [Finite G] (sl : SL34Data R Z X Y) {τ : G} (hτ2 : τ * τ = 1)
    (hτR : τ ∉ R) (hτZ : ∀ z ∈ Z, z * τ = τ * z) {x : G} (hx : x ∈ X) (hxZ : x ∉ Z)
    (hxτ : x * τ = τ * x)
    (hno : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E = 16 →
      E ≤ centralizer ({τ} : Set G) → False) : False := by
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁ : Subgroup G, E₁ = X ⊓ centralizer ({τ} : Set G) := ⟨_, rfl⟩
  have hE₁el : IsElemAbelian 2 E₁ := by
    rw [hE₁def]
    exact sl.X_elem.mono inf_le_left
  have hZE₁ : Z ≤ E₁ := by
    rw [hE₁def]
    exact fun z hz => Subgroup.mem_inf.mpr ⟨sl.Z_le_X hz,
      Subgroup.mem_centralizer_singleton_iff.mpr (hτZ z hz)⟩
  have hxE₁ : x ∈ E₁ := by
    rw [hE₁def]
    exact Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxτ⟩
  have h8 : 8 ≤ Nat.card E₁ := by
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hZE₁
    rw [sl.card_Z] at hc
    have hne : Nat.card E₁ ≠ 4 := by
      intro h4
      have hZeq : Z = E₁ := Subgroup.eq_of_le_of_card_ge hZE₁ (by rw [h4, sl.card_Z])
      exact hxZ (hZeq ▸ hxE₁)
    have hpos : 0 < Nat.card E₁ := Nat.card_pos
    omega
  have hτ1 : τ ≠ 1 := fun h1 => hτR (h1 ▸ R.one_mem)
  have hτsq : τ ^ 2 = 1 := by
    rw [pow_two]
    exact hτ2
  have hord : orderOf τ = 2 := orderOf_eq_prime hτsq hτ1
  have hE₂el : IsElemAbelian 2 (zpowers τ) := isElemAbelian_zpowers hτsq
  have hE₂card : Nat.card (zpowers τ) = 2 := by
    rw [Nat.card_zpowers]
    exact hord
  have hinf : E₁ ⊓ zpowers τ = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    rcases pt_eq_one_or_of_mem_zpowers hord hu2 with rfl | rfl
    · exact Subgroup.one_mem _
    · exfalso
      rw [hE₁def] at hu1
      exact hτR (sl.X_le (Subgroup.mem_inf.mp hu1).1)
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ zpowers τ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [hE₁def] at ha
    have hc : Commute a τ := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2
    exact (hc.zpow_right n).eq
  have hEel : IsElemAbelian 2 (E₁ ⊔ zpowers τ) := hE₁el.sup_of_commute hE₂el hcomm
  have hEcard : 16 ≤ Nat.card ↥(E₁ ⊔ zpowers τ) := by
    have h1 := m11_card_mul_le_sup hinf
    rw [hE₂card] at h1
    omega
  obtain ⟨K, hKE, hK16⟩ := exists_sub_card_sixteen hEel.isPGroup hEcard
  have hEc : E₁ ⊔ zpowers τ ≤ centralizer ({τ} : Set G) := by
    refine sup_le ?_ ?_
    · rw [hE₁def]
      exact inf_le_right
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  exact hno K (hEel.mono hKE) hK16 (hKE.trans hEc)

theorem r10_no_tau [Finite G] {t ρ : G} (H : R10Hyp R Z X Y t ρ) (hZt : ∀ z ∈ Z, z * t = t * z)
    {τ k : G} (hτ2 : τ * τ = 1) (hτR : τ ∉ R) (hk : k ∈ R) (hτk : τ = t * k) (hkZ : k ∉ Z)
    (hno : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E = 16 →
      E ≤ centralizer ({τ} : Set G) → False) : False := by
  have hZτ : ∀ z ∈ Z, z * τ = τ * z := by
    intro z hz
    rw [hτk]
    calc z * (t * k) = (z * t) * k := (mul_assoc _ _ _).symm
      _ = (t * z) * k := by rw [hZt z hz]
      _ = t * (z * k) := mul_assoc _ _ _
      _ = t * (k * z) := by rw [H.sl.Z_central z hz k hk]
      _ = (t * k) * z := (mul_assoc _ _ _).symm
  obtain ⟨x', hx', y', hy', hk'⟩ := H.sl.dec_XY k hk
  by_cases hy'Z : y' ∈ Z
  · have hkX : k ∈ X := by
      rw [hk']
      exact X.mul_mem hx' (H.sl.Z_le_X hy'Z)
    obtain ⟨x, hxY, hxZ, hx⟩ := r10_K H.symm hkX hkZ (Subgroup.one_mem Y)
    refine r10_contra_aux H.sl.symm hτ2 hτR hZτ hxY hxZ ?_ hno
    rw [hτk]
    simpa only [one_mul] using hx
  · obtain ⟨x, hxX, hxZ, hx⟩ := r10_K H hy' hy'Z hx'
    refine r10_contra_aux H.sl hτ2 hτR hZτ hxX hxZ ?_ hno
    rw [hτk, hk']
    exact hx

end Abstract

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
