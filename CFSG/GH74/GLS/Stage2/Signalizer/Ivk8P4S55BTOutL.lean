module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteCore
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace OutL

theorem exists_oddPart {G : Type} [Group G] [Finite G] (Z : Subgroup G)
    (hZ : ∀ z ∈ Z, ∃ k : ℕ, z ^ 2 ^ k = 1) (hab : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ Z)
    (hsq : ∀ g : G, ∀ z ∈ Z, g ^ 2 * z = z * g ^ 2) :
    ∃ N : Subgroup G, N.Normal ∧ (∀ g ∈ N, ∃ m : ℕ, Odd m ∧ g ^ m = 1) ∧
      ∀ g : G, ∃ n : ℕ, g ^ 2 ^ n ∈ N := by
  have hcent : ∀ g : G, ∀ m : ℕ, Odd m → g ^ m = 1 → ∀ z ∈ Z, Commute g z := by
    rintro g m ⟨j, rfl⟩ hg z hz
    have hgj : g = (g ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, hg, one_mul]
    rw [hgj]
    exact Commute.pow_left (hsq g z hz) _
  have hcomm : ∀ g h : G, ∀ m : ℕ, Odd m → g ^ m = 1 → Commute g h := by
    intro g h m hm hg
    set c := g * h * g⁻¹ * h⁻¹ with hc
    have hcZ : c ∈ Z := hab g h
    have hgc : Commute g c := hcent g m hm hg c hcZ
    have hk : ∀ k : ℕ, g ^ k * h = c ^ k * h * g ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hgh : g * h = c * h * g := by rw [hc]; group
        calc g ^ (k + 1) * h = g * (g ^ k * h) := by rw [pow_succ', mul_assoc]
          _ = g * (c ^ k * h * g ^ k) := by rw [ih]
          _ = c ^ k * (g * h) * g ^ k := by
            rw [← mul_assoc, ← mul_assoc, (hgc.pow_right k).eq, mul_assoc (c ^ k) g h]
          _ = c ^ (k + 1) * h * g ^ (k + 1) := by
            rw [hgh, pow_succ, pow_succ']
            group
    have hcm : c ^ m = 1 := by
      have := hk m
      rw [hg, one_mul, mul_one] at this
      exact (mul_eq_right.mp this.symm)
    obtain ⟨k, hck⟩ := hZ c hcZ
    have hc1 : c = 1 := by
      have h1 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
      have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
      have hcop : Nat.Coprime m (2 ^ k) :=
        Nat.Coprime.pow_right k hm.coprime_two_right
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    have h3 : g * h * g⁻¹ * h⁻¹ = 1 := hc1
    show g * h = h * g
    calc g * h = (g * h * g⁻¹ * h⁻¹) * h * g := by group
      _ = h * g := by rw [h3, one_mul]
  let N : Subgroup G :=
    { carrier := {g | ∃ m : ℕ, Odd m ∧ g ^ m = 1}
      one_mem' := ⟨1, odd_one, one_pow 1⟩
      mul_mem' := by
        rintro g h ⟨m, hm, hg⟩ ⟨m', hm', hh⟩
        refine ⟨m * m', hm.mul hm', ?_⟩
        rw [(hcomm g h m hm hg).mul_pow, pow_mul, hg, one_pow, one_mul, mul_comm, pow_mul, hh,
          one_pow]
      inv_mem' := by
        rintro g ⟨m, hm, hg⟩
        exact ⟨m, hm, by rw [inv_pow, hg, inv_one]⟩ }
  refine ⟨N, ⟨fun g ⟨m, hm, hg⟩ x => ⟨m, hm, by rw [conj_pow, hg, mul_one, mul_inv_cancel]⟩⟩,
    fun g hg => hg, fun g => ?_⟩
  obtain ⟨k, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := G)).ne'
  refine ⟨k, m, hm, ?_⟩
  rw [← pow_mul, ← hcard, pow_card_eq_one']

theorem outTwoNilp_of_diag {Y : Type} [Group Y] [Finite Y] (D : Subgroup (MulAut Y))
    (hD2 : ∀ δ ∈ D, ∃ k : ℕ, δ ^ 2 ^ k ∈ (MulAut.conj : Y →* MulAut Y).range)
    (hab : ∀ α β : MulAut Y, α * β * α⁻¹ * β⁻¹ ∈ D)
    (hsq : ∀ α : MulAut Y, ∀ δ ∈ D,
      α ^ 2 * δ * (α ^ 2)⁻¹ * δ⁻¹ ∈ (MulAut.conj : Y →* MulAut Y).range) :
    OutTwoNilp Y := by
  have : (MulAut.conj : Y →* MulAut Y).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal Y
  have : Finite (MulAut Y) := Finite.of_injective (fun α : MulAut Y => (α : Y → Y))
    DFunLike.coe_injective
  let π := QuotientGroup.mk' (MulAut.conj : Y →* MulAut Y).range
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hone : ∀ x, π x = 1 ↔ x ∈ (MulAut.conj : Y →* MulAut Y).range :=
    fun x => QuotientGroup.eq_one_iff x
  obtain ⟨N, hN, hodd, h2⟩ := exists_oddPart (D.map π)
    (by
      rintro _ ⟨δ, hδ, rfl⟩
      obtain ⟨k, hk⟩ := hD2 δ hδ
      exact ⟨k, by rw [← map_pow, hone]; exact hk⟩)
    (by
      intro g h
      obtain ⟨α, rfl⟩ := hπ g
      obtain ⟨β, rfl⟩ := hπ h
      exact ⟨_, hab α β, by simp only [map_mul, map_inv]⟩)
    (by
      intro g z hz
      obtain ⟨α, rfl⟩ := hπ g
      obtain ⟨δ, hδ, rfl⟩ := hz
      have h1 : π (α ^ 2 * δ * (α ^ 2)⁻¹ * δ⁻¹) = 1 := (hone _).mpr (hsq α δ hδ)
      simp only [map_mul, map_inv, map_pow] at h1
      calc π α ^ 2 * π δ = (π α ^ 2 * π δ * (π α ^ 2)⁻¹ * (π δ)⁻¹) * π δ * π α ^ 2 := by group
        _ = π δ * π α ^ 2 := by rw [h1, one_mul])
  refine ⟨N.comap π, hN.comap π, fun x hx => ?_, fun w hw => ?_, fun y => ?_⟩
  · show π x ∈ N
    rw [(hone x).mpr hx]
    exact N.one_mem
  · obtain ⟨m, hm, hwm⟩ := hodd (π w) hw
    exact ⟨m, hm, (hone _).mp (by rw [map_pow]; exact hwm)⟩
  · obtain ⟨n, hn⟩ := h2 (π y)
    exact ⟨n, show π (y ^ 2 ^ n) ∈ N by rwa [map_pow]⟩

theorem outTwoNilp_of_outAbelian {Y : Type} [Group Y] [Finite Y]
    (h : ∀ α β : MulAut Y, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : Y →* MulAut Y).range) :
    OutTwoNilp Y := by
  have hN : (MulAut.conj : Y →* MulAut Y).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal Y
  refine outTwoNilp_of_diag _ (fun δ hδ => ⟨0, by rwa [pow_zero, pow_one]⟩) h
    fun α δ hδ => ?_
  exact mul_mem (hN.conj_mem _ hδ _) (inv_mem hδ)

theorem outTwoNilp_of_equiv {Y P : Type} [Group Y] [Group P] (e : Y ≃* P)
    (h : OutTwoNilp P) : OutTwoNilp Y := by
  obtain ⟨O, hO, hIO, hodd, h2⟩ := h
  have hconj : ∀ w : MulAut Y, MulAut.congr e w ∈ (MulAut.conj : P →* MulAut P).range →
      w ∈ (MulAut.conj : Y →* MulAut Y).range := by
    rintro w ⟨p, hp⟩
    refine ⟨e.symm p, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hp
  refine ⟨O.comap (MulAut.congr e).toMonoidHom, hO.comap _, ?_, fun w hw => ?_, fun y => ?_⟩
  · rintro _ ⟨y, rfl⟩
    show MulAut.congr e (MulAut.conj y) ∈ O
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
    exact hIO ⟨e y, rfl⟩
  · obtain ⟨m, hm, hwm⟩ := hodd _ hw
    exact ⟨m, hm, hconj _ (by rw [map_pow]; exact hwm)⟩
  · obtain ⟨n, hn⟩ := h2 (MulAut.congr e y)
    exact ⟨n, show MulAut.congr e (y ^ 2 ^ n) ∈ O by rwa [map_pow]⟩

end OutL

theorem outCell_fl2 : OutCell FL2 := by
  intro Y _ _ _ hY
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  refine OutL.outTwoNilp_of_outAbelian fun α β => ?_
  obtain ⟨s, hs⟩ :=
    CFSG.ComponentClassification.AutL2Facts.footeOutAbelian Y p f hp hp2 hf hLie α β
  exact ⟨s, hs.symm⟩

theorem outCell_fsp4 : OutCell FSp4 := fun _ _ _ _ hY =>
  OutL.outTwoNilp_of_outAbelian (outAbelian_of_FSp4 hY)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
