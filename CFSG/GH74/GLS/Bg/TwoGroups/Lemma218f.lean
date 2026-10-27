module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218e
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218d

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L218

open Subgroup

theorem mem_smul_sylow_iff {G : Type} [Group G] {p : ℕ} (P : Sylow p G) (g x : G) :
    x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

section Main

variable {E : Type} [CommGroup E] [Finite E] {X : Subgroup (MulAut E)} {S : Sylow 2 ↥X}

theorem Ctx.cent_u_two (c : Ctx E X S) {x : ↥X} (hx : x ∈ (S : Subgroup ↥X)) (hx1 : x ≠ 1)
    (φ : ↥(Subgroup.centralizer ({x} : Set ↥X)) ≃* Z2xS3) {u : ↥X} (hu : orderOf u = 3) :
    ∀ T : Subgroup ↥X, T ≤ Subgroup.centralizer ({u} : Set ↥X) → IsPGroup 2 T →
      Nat.card T ≤ 2 := by
  intro T hT hT2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := hT2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X S Q
  have hQcard : Nat.card Q = 4 := by
    rw [(Sylow.card_eq_multiplicity Q).trans (Sylow.card_eq_multiplicity S).symm]
    exact c.hS4
  have hdvd : Nat.card T ∣ 4 := hQcard ▸ Subgroup.card_dvd_of_le hTQ
  by_contra hlt
  have h4 : Nat.card T = 4 := by
    have hm : Nat.card T ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h4' : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [h4'] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have hTQeq : T = Q := Subgroup.eq_of_le_of_card_ge hTQ (by rw [h4, hQcard])
  have hQc : (Q : Subgroup ↥X) ≤ Subgroup.centralizer ({u} : Set ↥X) := hTQeq ▸ hT
  have hmemQ : ∀ s ∈ (S : Subgroup ↥X), g * s * g⁻¹ ∈ (Q : Subgroup ↥X) := by
    intro s hs
    rw [← hg, mem_smul_sylow_iff, show g⁻¹ * (g * s * g⁻¹) * g = s by group]
    exact hs
  have hw : ∀ s ∈ (S : Subgroup ↥X), (g⁻¹ * u * g) * s = s * (g⁻¹ * u * g) := by
    intro s hs
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hQc (hmemQ s hs))
    calc (g⁻¹ * u * g) * s = g⁻¹ * (u * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * u) * g := by rw [h1]
      _ = s * (g⁻¹ * u * g) := by group
  have hsq := c.centS_sq hx hx1 φ hw
  have huu : u * u = 1 := by
    calc u * u = g * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  have := orderOf_dvd_of_pow_eq_one (show u ^ 2 = 1 by rw [pow_two]; exact huu)
  rw [hu] at this
  omega

omit [Finite E] in
theorem v_fixes_e0 {e₀ : E} (he₀ : e₀ ≠ 1)
    (hS : e₀ ∈ fixS (S : Subgroup ↥X))
    (hE0 : ∀ e ∈ fixS (S : Subgroup ↥X), e = 1 ∨ e = e₀) {v : ↥X}
    (hvn : ∀ s, s ∈ (S : Subgroup ↥X) ↔ v * s * v⁻¹ ∈ (S : Subgroup ↥X)) :
    (v : MulAut E) e₀ = e₀ := by
  have hmem : (v : MulAut E) e₀ ∈ fixS (S : Subgroup ↥X) := by
    intro s hs
    have hs' : v⁻¹ * s * v ∈ (S : Subgroup ↥X) := by
      rw [hvn, show v * (v⁻¹ * s * v) * v⁻¹ = s by group]
      exact hs
    have h1 := hS _ hs'
    have h2 : s * v = v * (v⁻¹ * s * v) := by group
    have h3 : ((s * v : ↥X) : MulAut E) e₀ = ((v * (v⁻¹ * s * v) : ↥X) : MulAut E) e₀ := by
      rw [h2]
    simp only [Subgroup.coe_mul, MulAut.mul_apply] at h3 h1
    rw [h1] at h3
    exact h3
  rcases hE0 _ hmem with h | h
  · exfalso
    apply he₀
    have : (v : MulAut E) e₀ = (v : MulAut E) 1 := by rw [map_one]; exact h
    exact (v : MulAut E).injective this
  · exact h

theorem Ctx.card_Y (c : Ctx E X S)
    (hfree : ∀ s : ↥X, s ≠ 1 → s * s = 1 → Nat.card (fixE (s : MulAut E)) = 4)
    {e₀ : E} (he₀ : e₀ ≠ 1) (hS : e₀ ∈ fixS (S : Subgroup ↥X)) {v : ↥X} (hv3 : orderOf v = 3)
    (hv : (v : MulAut E) e₀ = e₀) : Nat.card (MulAction.stabilizer ↥X e₀) = 12 := by
  let Y : Subgroup ↥X := MulAction.stabilizer ↥X e₀
  have hmemY : ∀ g : ↥X, g ∈ Y ↔ (g : MulAut E) e₀ = e₀ := fun g => MulAction.mem_stabilizer_iff
  have hY1344 : Nat.card Y ∣ 1344 := by
    have hle : Y.map X.subtype ≤ MulAction.stabilizer (MulAut E) e₀ := by
      rintro _ ⟨g, hg, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      exact (hmemY g).mp hg
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective X.subtype_injective,
      card_stab c.h2 c.hE e₀ he₀] at h1
    exact h1
  have hSY : (S : Subgroup ↥X) ≤ Y := by
    intro s hs
    rw [hmemY]
    exact hS s hs
  have h4 : 4 ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hSY
    rwa [c.hS4] at this
  have hvY : v ∈ Y := (hmemY v).mpr hv
  have h3 : 3 ∣ Nat.card Y := by
    have := orderOf_dvd_natCard (⟨v, hvY⟩ : Y)
    rwa [Subgroup.orderOf_mk, hv3] at this
  have h8 : ¬ 8 ∣ Nat.card Y := by
    intro h
    have h1 : Nat.card Y ∣ Nat.card ↥X := Subgroup.card_subgroup_dvd_card Y
    have h2 := Subgroup.card_mul_index (S : Subgroup ↥X)
    have h3' := S.not_dvd_index
    rw [c.hS4] at h2
    have h5 : 8 ∣ Nat.card ↥X := dvd_trans h h1
    omega
  obtain ⟨m, hm⟩ : 12 ∣ Nat.card Y := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  have hm112 : m ∣ 112 := by
    rw [hm] at hY1344
    have : 12 * m ∣ 12 * 112 := by simpa using hY1344
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rw [hm] at h8
  have hmem : m ∈ Nat.divisors 112 := Nat.mem_divisors.mpr ⟨hm112, by norm_num⟩
  have h112 : Nat.divisors 112 = {1, 2, 4, 7, 8, 14, 16, 28, 56, 112} := by decide
  rw [h112] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h
  · rw [hm, h]
  all_goals first
    | omega
    | (exfalso
       have h84 : Nat.card Y = 84 := by rw [hm, h]
       exact no_Y84 c.h2 hfree Y h84)

end Main

theorem nine_dvd {E : Type} [CommGroup E] [Finite E] {X : Subgroup (MulAut E)} {u v : ↥X}
    (hu : orderOf u = 3) (hv : orderOf v = 3) {e₀ : E} (he₀ : e₀ ≠ 1)
    (hv0 : (v : MulAut E) e₀ = e₀) (hu1 : ∀ e : E, (u : MulAut E) e = e → e = 1) :
    9 ∣ Nat.card ↥X := by
  by_contra h9
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ w : ↥X, orderOf w = 3 →
      ∃ P : Sylow 3 ↥X, (P : Subgroup ↥X) = Subgroup.zpowers w := by
    intro w hw
    have hpg : IsPGroup 3 (Subgroup.zpowers w) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw]; norm_num)
    have hnd : ¬ 3 ∣ (Subgroup.zpowers w).index := by
      intro hd
      have h1 := Subgroup.card_mul_index (Subgroup.zpowers w)
      rw [Nat.card_zpowers, hw] at h1
      apply h9
      obtain ⟨k, hk⟩ := hd
      rw [hk] at h1
      exact ⟨k, by omega⟩
    exact ⟨hpg.toSylow hnd, rfl⟩
  obtain ⟨Pu, hPu⟩ := hsyl u hu
  obtain ⟨Pv, hPv⟩ := hsyl v hv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X Pu Pv
  have hmem : g * u * g⁻¹ ∈ (Pv : Subgroup ↥X) := by
    rw [← hg, mem_smul_sylow_iff, show g⁻¹ * (g * u * g⁻¹) * g = u by group, hPu]
    exact Subgroup.mem_zpowers u
  rw [hPv] at hmem
  have hstab : Subgroup.zpowers v ≤ MulAction.stabilizer ↥X e₀ :=
    Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hv0)
  have hfix := hstab hmem
  rw [MulAction.mem_stabilizer_iff] at hfix
  have hfix' : (g : MulAut E) ((u : MulAut E) ((g : MulAut E)⁻¹ e₀)) = e₀ := hfix
  have h1 : (u : MulAut E) ((g : MulAut E)⁻¹ e₀) = (g : MulAut E)⁻¹ e₀ := by
    have := congrArg (fun z => (g : MulAut E)⁻¹ z) hfix'
    simpa using this
  have h2 := hu1 _ h1
  apply he₀
  have : (g : MulAut E)⁻¹ e₀ = (g : MulAut E)⁻¹ 1 := by rw [h2, map_one]
  exact ((g : MulAut E)⁻¹).injective this

end L218

end CFSG.GH74.GLS.Bg.TwoGroups
