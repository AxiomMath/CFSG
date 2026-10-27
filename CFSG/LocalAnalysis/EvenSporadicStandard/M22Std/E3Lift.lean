module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.X1Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.RankTwoE

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std CFSG.QuasithinUnique.Unc25G2.M2x

variable {G : Type} [Group G] [Finite G]

theorem le_of_isPGroup_of_odd_relIndex {U₀ L₁ T : Subgroup G} (hLT : L₁ ≤ T) (hTU : T ≤ U₀)
    (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ L₁.relIndex U₀) : T ≤ L₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT.index (L₁.subgroupOf T)
  have hmul := Subgroup.relIndex_mul_relIndex L₁ T U₀ hLT hTU
  have hdvd : L₁.relIndex T ∣ L₁.relIndex U₀ := ⟨T.relIndex U₀, hmul.symm⟩
  have h1 : L₁.relIndex T = 1 := by
    have h2 : L₁.relIndex T = 2 ^ n := hn
    rcases n with _ | n
    · simpa using h2
    · exact absurd (dvd_trans (by rw [h2]; exact dvd_pow_self 2 (Nat.succ_ne_zero n)) hdvd) hodd
  exact Subgroup.relIndex_eq_one.1 h1

theorem exists_mem_centralizer_of_conj_mem_lift {X U₀ L₁ : Subgroup G} (hU₀X : U₀ ≤ X)
    (hnorm : ∀ x ∈ X, ∀ u ∈ U₀, x * u * x⁻¹ ∈ U₀) (hL₁U : L₁ ≤ U₀) (hL₁p : IsPGroup 2 L₁)
    (hL₁i : ¬ 2 ∣ L₁.relIndex U₀) (hL₁n : ∀ x ∈ X, ∀ l ∈ L₁, x * l * x⁻¹ ∈ L₁)
    (hL₁sq : ∀ l ∈ L₁, l * l = 1) {y : G} (hyX : y ∈ X) (hy2 : y * y = 1)
    (hH : ∀ m ∈ L₁, y * m * y⁻¹ = m → ∃ l ∈ L₁, m = l * (y * l * y⁻¹)) {x : G}
    (hxy : x * y * x⁻¹ * y⁻¹ ∈ U₀) :
    ∃ u ∈ U₀, (u⁻¹ * x) * y * (u⁻¹ * x)⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hynorm : ∀ u, u ∈ U₀ ↔ y * u * y⁻¹ ∈ U₀ := by
    intro u
    refine ⟨hnorm y hyX u, fun h => ?_⟩
    have := hnorm y⁻¹ (Subgroup.inv_mem _ hyX) _ h
    rwa [show y⁻¹ * (y * u * y⁻¹) * y⁻¹⁻¹ = u by group] at this
  set C : Subgroup G := U₀ ⊔ zpowers y with hC
  have hyC : y ∈ C := Subgroup.mem_sup_right (mem_zpowers y)
  have hU₀C : U₀ ≤ C := le_sup_left
  set v : G := x * y * x⁻¹ * y⁻¹ with hv
  set y' : G := x * y * x⁻¹ with hy'
  have hy'v : y' = v * y := by rw [hv, hy']; group
  have hy'C : y' ∈ C := by
    rw [hy'v]
    exact Subgroup.mul_mem _ (hU₀C hxy) hyC
  have hy'2 : y' * y' = 1 := by
    calc y' * y' = x * (y * y) * x⁻¹ := by rw [hy']; group
      _ = 1 := by rw [hy2]; group
  have hyp : IsPGroup 2 (zpowers y) := by
    intro g
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy2
    rw [Nat.cast_ofNat, this, one_zpow]
  have hy'p : IsPGroup 2 (zpowers y') := by
    intro g
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : y' ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy'2
    rw [Nat.cast_ofNat, this, one_zpow]
  have hzn : zpowers y ≤ normalizer (L₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => hL₁n y hyX l hl, fun h => by
      have := hL₁n y⁻¹ (Subgroup.inv_mem _ hyX) _ h
      rwa [show y⁻¹ * (y * l * y⁻¹) * y⁻¹⁻¹ = l by group] at this⟩
  have hS1p : IsPGroup 2 (L₁ ⊔ zpowers y : Subgroup G) := hL₁p.to_sup_of_normal_left' hyp hzn
  obtain ⟨Sy, hSy⟩ := (isPGroup_subgroupOf C hS1p).exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup (P := (Sy : Subgroup ↥C)) Sy.isPGroup'
    (Sylow.not_dvd_index Sy) (A := (zpowers y').subgroupOf C) (isPGroup_subgroupOf C hy'p)
  obtain ⟨g0, hg0C, rfl⟩ : ∃ g0 : G, ∃ h : g0 ∈ C, g = ⟨g0, h⟩ := ⟨g.1, g.2, rfl⟩
  have hL₁Sy : ∀ (l : G) (hl : l ∈ L₁), (⟨l, hU₀C (hL₁U hl)⟩ : ↥C) ∈ (Sy : Subgroup ↥C) :=
    fun l hl => hSy (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hl))
  have hySy : (⟨y, hyC⟩ : ↥C) ∈ (Sy : Subgroup ↥C) :=
    hSy (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (mem_zpowers y)))
  have hSyU : ∀ s : ↥C, s ∈ (Sy : Subgroup ↥C) → (s : G) ∈ U₀ → (s : G) ∈ L₁ := by
    intro s hs hsU
    set T : Subgroup G := (Sy : Subgroup ↥C).map C.subtype ⊓ U₀ with hT
    have hTp : IsPGroup 2 T := by
      intro t
      obtain ⟨⟨s', hs', hst⟩, -⟩ := Subgroup.mem_inf.1 t.2
      obtain ⟨n, hn⟩ := Sy.isPGroup' ⟨s', hs'⟩
      refine ⟨n, Subtype.ext ?_⟩
      have h1 : (s' : G) ^ 2 ^ n = 1 := by
        simpa using congrArg (fun a : ↥(Sy : Subgroup ↥C) => (((a : ↥C)) : G)) hn
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hst]
      exact h1
    have hL₁T : L₁ ≤ T := fun l hl => Subgroup.mem_inf.2 ⟨⟨_, hL₁Sy l hl, rfl⟩, hL₁U hl⟩
    have hTU : T ≤ U₀ := inf_le_right
    exact le_of_isPGroup_of_odd_relIndex hL₁T hTU hTp hL₁i
      (Subgroup.mem_inf.2 ⟨⟨s, hs, rfl⟩, hsU⟩)
  set y'' : G := g0 * y' * g0⁻¹ with hy''
  have hy''Sy : (⟨y'', C.mul_mem (C.mul_mem hg0C hy'C) (C.inv_mem hg0C)⟩ : ↥C) ∈
      (Sy : Subgroup ↥C) :=
    hg ⟨y', hy'C⟩ (Subgroup.mem_subgroupOf.2 (mem_zpowers y'))
  have hcoset : ∀ c ∈ C, c * y' * c⁻¹ * y⁻¹ ∈ U₀ := by
    intro c hc
    rcases mem_sup_zpowers_cases hy2 hynorm hc with hcU | ⟨u, hu, rfl⟩
    · have e : c * y' * c⁻¹ * y⁻¹ = (c * v * c⁻¹) * (c * (y * c⁻¹ * y⁻¹)) := by
        rw [hy'v]; group
      rw [e]
      exact Subgroup.mul_mem _ (hnorm c (hU₀X hcU) v hxy) (Subgroup.mul_mem _ hcU
        (hnorm y hyX c⁻¹ (Subgroup.inv_mem _ hcU)))
    · have e : u * y * y' * (u * y)⁻¹ * y⁻¹ = u * (y * v * y⁻¹) * (y * u⁻¹ * y⁻¹) := by
        rw [hy'v]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu (hnorm y hyX v hxy))
        (hnorm y hyX u⁻¹ (Subgroup.inv_mem _ hu))
  have hwU : y'' * y⁻¹ ∈ U₀ := hcoset g0 hg0C
  have hwSy : (⟨y'' * y⁻¹, C.mul_mem (C.mul_mem (C.mul_mem hg0C hy'C) (C.inv_mem hg0C))
      (C.inv_mem hyC)⟩ : ↥C) ∈ (Sy : Subgroup ↥C) :=
    Subgroup.mul_mem _ hy''Sy (Subgroup.inv_mem _ hySy)
  have hwL : y'' * y⁻¹ ∈ L₁ := hSyU _ hwSy hwU
  set w : G := y'' * y⁻¹ with hwdef
  have hy''w : y'' = w * y := by rw [hwdef]; group
  have hy''2 : y'' * y'' = 1 := by
    calc y'' * y'' = g0 * (y' * y') * g0⁻¹ := by rw [hy'']; group
      _ = 1 := by rw [hy'2]; group
  have hwy : y * w * y⁻¹ = w := by
    have h1 : w * (y * w * y⁻¹) = 1 := by
      calc w * (y * w * y⁻¹) = (w * y) * (w * y) * (y⁻¹ * y⁻¹) := by group
        _ = 1 := by rw [← hy''w, hy''2, hyi, hy2, mul_one]
    have h2 : y * w * y⁻¹ = w⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (hL₁sq w hwL)
  obtain ⟨l, hl, hwl⟩ := hH w hwL hwy
  have hly : y'' = l * y * l := by
    rw [hy''w, hwl]
    group
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right (hL₁sq l hl)
  have hc : g0⁻¹ * l ∈ C := C.mul_mem (C.inv_mem hg0C) (hU₀C (hL₁U hl))
  have hy'c : x * y * x⁻¹ = (g0⁻¹ * l) * y * (g0⁻¹ * l)⁻¹ := by
    have e1 : y' = g0⁻¹ * y'' * g0 := by rw [hy'']; group
    have e2 : (g0⁻¹ * l) * y * (g0⁻¹ * l)⁻¹ = g0⁻¹ * (l * y * l⁻¹) * g0 := by group
    rw [← hy', e1, hly, e2, hli]
  rcases mem_sup_zpowers_cases hy2 hynorm hc with hcU | ⟨u, hu, hcu⟩
  · refine ⟨g0⁻¹ * l, hcU, ?_⟩
    calc (g0⁻¹ * l)⁻¹ * x * y * ((g0⁻¹ * l)⁻¹ * x)⁻¹
        = (g0⁻¹ * l)⁻¹ * (x * y * x⁻¹) * (g0⁻¹ * l) := by group
      _ = y := by rw [hy'c]; group
  · refine ⟨u, hu, ?_⟩
    have e3 : (g0⁻¹ * l) * y * (g0⁻¹ * l)⁻¹ = u * y * u⁻¹ := by
      rw [hcu]; group
    calc u⁻¹ * x * y * (u⁻¹ * x)⁻¹ = u⁻¹ * (x * y * x⁻¹) * u := by group
      _ = y := by rw [hy'c, e3]; group

end CFSG.EvenSporadicStandard.M22Std
