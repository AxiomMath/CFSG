module

public import CFSG.LargeExtraspecial.AS35YRFrameX
public import CFSG.LargeExtraspecial.AS35YRFrameE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace AS35YR

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
  {U : Submodule (ZMod 2) V}

theorem zmod2_cases_YU (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact .inl rfl
  · exact .inr rfl

theorem exists_polar_zero_one_YU {x y : V} (hx : ∃ u ∈ U, polar q x u = 1)
    (hy : ∃ u ∈ U, polar q y u = 1) (hxy : ∃ u ∈ U, polar q (x + y) u = 1) :
    ∃ u ∈ U, polar q x u = 0 ∧ polar q y u = 1 := by
  obtain ⟨u₁, hu₁, h₁⟩ := hx
  obtain ⟨u₂, hu₂, h₂⟩ := hy
  obtain ⟨u₃, hu₃, h₃⟩ := hxy
  rw [polar_add_left] at h₃
  rcases zmod2_cases_YU (polar q x u₂) with e | e
  · exact ⟨u₂, hu₂, e, h₂⟩
  rcases zmod2_cases_YU (polar q y u₁) with e' | e'
  · refine ⟨u₁ + u₂, U.add_mem hu₁ hu₂, ?_, ?_⟩
    · rw [polar_add_right, h₁, e]
      rfl
    · rw [polar_add_right, e', h₂, zero_add]
  rcases zmod2_cases_YU (polar q x u₃) with e'' | e''
  · refine ⟨u₃, hu₃, e'', ?_⟩
    rwa [e'', zero_add] at h₃
  · have hy3 : polar q y u₃ = 0 := by
      rcases zmod2_cases_YU (polar q y u₃) with h | h
      · exact h
      · rw [e'', h] at h₃
        exact absurd h₃ (by decide)
    refine ⟨u₃ + u₁, U.add_mem hu₃ hu₁, ?_, ?_⟩
    · rw [polar_add_right, e'', h₁]
      rfl
    · rw [polar_add_right, hy3, e', zero_add]

theorem exists_singular_YU {r : V} (hr : q r = 1) (hrU' : r ∈ U)
    (hrU : ∀ u ∈ U, polar q u r = 0) {x : V} (hx : x ∈ U) :
    ∃ x' ∈ U, q x' = 0 ∧ ∀ u ∈ U, polar q u x' = polar q u x := by
  rcases zmod2_cases_YU (q x) with h | h
  · exact ⟨x, hx, h, fun _ _ => rfl⟩
  · refine ⟨x + r, U.add_mem hx hrU', ?_, fun u hu => ?_⟩
    · rw [QuadraticMap.map_add q, h, hr, hrU x hx]
      rfl
    · rw [polar_add_right, hrU u hu, add_zero]

theorem exists_polar_eq_one_of_rad_YU {r : V} (hr : q r = 1)
    (hrad : ∀ x ∈ U, (∀ u ∈ U, polar q x u = 0) → x = 0 ∨ x = r) {x : V} (hx : x ∈ U)
    (hx0 : x ≠ 0) (hqx : q x = 0) : ∃ u ∈ U, polar q x u = 1 := by
  by_contra hcon
  push Not at hcon
  rcases hrad x hx fun u hu => (zmod2_cases_YU _).resolve_right (hcon u hu) with h | h
  · exact hx0 h
  · rw [h, hr] at hqx
    exact one_ne_zero hqx

theorem exists_frame_in_YU {r : V} (hr : q r = 1) (hrU' : r ∈ U)
    (hrU : ∀ u ∈ U, polar q u r = 0)
    (hrad : ∀ x ∈ U, (∀ u ∈ U, polar q x u = 0) → x = 0 ∨ x = r) {a b : V} (haU : a ∈ U)
    (hbU : b ∈ U) (qa : q a = 0) (qb : q b = 0) (hab : polar q a b = 0) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hne : a ≠ b) :
    ∃ c ∈ U, ∃ c' ∈ U, q c = 0 ∧ q c' = 0 ∧ polar q a c = 0 ∧ polar q b c = 1 ∧
      polar q a c' = 1 ∧ polar q b c' = 0 ∧ polar q c c' = 0 := by
  have hab0 : a + b ≠ 0 := by
    intro h
    apply hne
    have := congrArg (· + b) h
    simpa [add_assoc, add_self_YR] using this
  have qab : q (a + b) = 0 := by
    rw [QuadraticMap.map_add q, qa, qb, hab]
    rfl
  have ea := exists_polar_eq_one_of_rad_YU hr hrad haU ha0 qa
  have eb := exists_polar_eq_one_of_rad_YU hr hrad hbU hb0 qb
  have eab := exists_polar_eq_one_of_rad_YU hr hrad (U.add_mem haU hbU) hab0 qab
  obtain ⟨c₁, hc₁U, hc₁a, hc₁b⟩ := exists_polar_zero_one_YU ea eb eab
  obtain ⟨d₁, hd₁U, hd₁b, hd₁a⟩ := exists_polar_zero_one_YU eb ea (by rwa [add_comm])
  obtain ⟨c₂, hc₂U, hc₂q, hc₂f⟩ := exists_singular_YU hr hrU' hrU hc₁U
  obtain ⟨d₂, hd₂U, hd₂q, hd₂f⟩ := exists_singular_YU hr hrU' hrU hd₁U
  have hc₂a : polar q a c₂ = 0 := by rw [hc₂f a haU, hc₁a]
  have hc₂b : polar q b c₂ = 1 := by rw [hc₂f b hbU, hc₁b]
  have hd₂a : polar q a d₂ = 1 := by rw [hd₂f a haU, hd₁a]
  have hd₂b : polar q b d₂ = 0 := by rw [hd₂f b hbU, hd₁b]
  obtain ⟨c, hcU, hcq, hca, hcb, hcd⟩ : ∃ c ∈ U, q c = 0 ∧ polar q a c = 0 ∧
      polar q b c = 1 ∧ polar q c d₂ = 0 := by
    rcases zmod2_cases_YU (polar q c₂ d₂) with h | h
    · exact ⟨c₂, hc₂U, hc₂q, hc₂a, hc₂b, h⟩
    · refine ⟨c₂ + a, U.add_mem hc₂U haU, ?_, ?_, ?_, ?_⟩
      · rw [QuadraticMap.map_add q, hc₂q, qa, polar_comm, hc₂a]
        rfl
      · rw [polar_add_right, hc₂a, polar_self_YR, add_zero]
      · rw [polar_add_right, hc₂b, polar_comm, hab, add_zero]
      · rw [polar_add_left, h, hd₂a]
        rfl
  exact ⟨c, hcU, d₂, hd₂U, hcq, hd₂q, hca, hcb, hd₂a, hd₂b, hcd⟩

theorem Frame.comm_t_of_fix_YU [FiniteDimensional (ZMod 2) V] (F : Frame q)
    (hq : q.polarBilin.Nondegenerate) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q) (ga : g F.a = F.a) (gb : g F.b = F.b) :
    g * F.t = F.t * g := by
  have h := F.conj_t_eq hq hg fun z hz => by
    rw [Frame.apply_eq_of_mem_ell ga gb hz]
    exact hz
  calc g * F.t = g * F.t * g⁻¹ * g := by group
    _ = F.t * g := by rw [h]

end AS35YR

end CFSG.LargeExtraspecial
