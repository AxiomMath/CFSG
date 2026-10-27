module

public import CFSG.CGT.T75F.E710Quot

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

@[expose] def Mhat (M : Subgroup X) : Subgroup (X ⧸ Subgroup.center X) :=
  M.map (QuotientGroup.mk' (Subgroup.center X))

theorem exists_fixed_of_involutive {α : Type*} [Finite α] (f : α → α) (hf : ∀ a, f (f a) = a)
    (hodd : Odd (Nat.card α)) : ∃ a, f a = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : Equiv.Perm α := ⟨f, f, hf, hf⟩
  have hσ : σ * σ = 1 := by
    ext a
    exact hf a
  have hP : IsPGroup 2 (Subgroup.zpowers σ) := isPGroup_two_zpowers_of_mul_self hσ
  have hnd : ¬ 2 ∣ Nat.card α := by
    obtain ⟨c, hc⟩ := hodd
    omega
  obtain ⟨a, ha⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card α hnd
  have h1 : σ a = a := by simpa using MulAction.mem_fixedPoints.1 ha ⟨σ, Subgroup.mem_zpowers σ⟩
  exact ⟨a, h1⟩

namespace Endgame710

variable (h : Endgame710 D M L q)
include h

theorem mk_commute_iff {d e : X} (hd : d ∈ D) (he : e ∈ D) :
    (QuotientGroup.mk d : X ⧸ Subgroup.center X) * QuotientGroup.mk e =
      QuotientGroup.mk e * QuotientGroup.mk d ↔ d * e = e * d := by
  constructor
  · intro hc
    have hd2 := h.sq_eq_one d hd
    have he2 := h.sq_eq_one e he
    have hζ : (d * e) ^ 2 ∈ Subgroup.center X := by
      have h1 : (QuotientGroup.mk ((d * e) ^ 2) : X ⧸ Subgroup.center X) = 1 := by
        have hd2' : (QuotientGroup.mk d : X ⧸ Subgroup.center X) * QuotientGroup.mk d = 1 := by
          rw [← QuotientGroup.mk_mul, hd2]; rfl
        have he2' : (QuotientGroup.mk e : X ⧸ Subgroup.center X) * QuotientGroup.mk e = 1 := by
          rw [← QuotientGroup.mk_mul, he2]; rfl
        rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, pow_two]
        calc (QuotientGroup.mk d : X ⧸ Subgroup.center X) * QuotientGroup.mk e *
              (QuotientGroup.mk d * QuotientGroup.mk e)
            = QuotientGroup.mk d * (QuotientGroup.mk e * QuotientGroup.mk d) *
                QuotientGroup.mk e := by group
          _ = QuotientGroup.mk d * (QuotientGroup.mk d * QuotientGroup.mk e) *
                QuotientGroup.mk e := by rw [hc]
          _ = (QuotientGroup.mk d * QuotientGroup.mk d) *
                (QuotientGroup.mk e * QuotientGroup.mk e) := by group
          _ = 1 := by rw [hd2', he2', one_mul]
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hcen : ∀ g : X, g * (d * e) ^ 2 = (d * e) ^ 2 * g := Subgroup.mem_center_iff.1 hζ
    have hinv : (d * e) ^ 2 = ((d * e) ^ 2)⁻¹ := by
      have h1 := dihedral_conj_pow hd2 he2 2
      rw [hcen d, mul_assoc, hd2, mul_one] at h1
      exact h1
    have h4 : (d * e) ^ 4 = 1 := by
      have : (d * e) ^ 2 * (d * e) ^ 2 = 1 := by
        calc (d * e) ^ 2 * (d * e) ^ 2 = (d * e) ^ 2 * ((d * e) ^ 2)⁻¹ := by
              rw [← hinv]
          _ = 1 := mul_inv_cancel _
      rw [← this]; group
    have hdvd : orderOf (d * e) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
    obtain ⟨i, hi2, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hsq : (d * e) ^ 2 = 1 := by
      rcases Nat.lt_or_ge i 2 with hlt | hge
      · have : orderOf (d * e) ∣ 2 := by
          rw [hi]
          interval_cases i <;> simp
        exact orderOf_dvd_iff_pow_eq_one.1 this
      · exfalso
        have hi2' : i = 2 := le_antisymm hi2 hge
        subst hi2'
        have ho4 : orderOf (d * e) = 4 := by simpa using hi
        have hεD := h.four d hd e he ho4
        exact h.not_mem_center hεD hζ
    have h3 : d * e = (d * e)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_two]; exact hsq)
    rw [h3, dihedral_inv hd2 he2]
  · intro hc
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]

theorem mk_mem_Mhat_iff {d : X} (hd : d ∈ D) :
    (QuotientGroup.mk d : X ⧸ Subgroup.center X) ∈ Mhat M ↔ d ∈ M := by
  constructor
  · rintro ⟨m, hm, hmd⟩
    have hz : m⁻¹ * d ∈ Subgroup.center X := by
      rw [← QuotientGroup.eq]
      exact hmd
    exact h.mem_M_of_mul_center hd hm hz (by group)
  · intro hdM
    exact ⟨d, hdM, rfl⟩

theorem H3hat {β d : X ⧸ Subgroup.center X}
    (hβ : β ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D) (hβM : β ∈ Mhat M)
    (hd : d ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D) (hc : d * β = β * d) :
    d ∈ Mhat M := by
  obtain ⟨b, hbD, rfl⟩ := hβ
  obtain ⟨e, heD, rfl⟩ := hd
  have hbM : b ∈ M := (h.mk_mem_Mhat_iff hbD).1 hβM
  have hcom : e * b = b * e := (h.mk_commute_iff heD hbD).1 hc
  exact (h.mk_mem_Mhat_iff heD).2 (h.H3 b hbD hbM e heD hcom)

theorem mem_center_quot_of_commute {v : X ⧸ Subgroup.center X}
    (hv : ∀ x ∈ (QuotientGroup.mk' (Subgroup.center X)) '' D, x * v = v * x) :
    v ∈ Subgroup.center (X ⧸ Subgroup.center X) := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure ((QuotientGroup.mk' (Subgroup.center X)) '' D) := by
    rw [h.Dhat_closure]; exact Subgroup.mem_top g
  have hle : Subgroup.closure ((QuotientGroup.mk' (Subgroup.center X)) '' D) ≤
      Subgroup.centralizer ({v} : Set (X ⧸ Subgroup.center X)) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hv x hx
  have := hle hg
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem commute_D_of_fixed {z β₀ : X}
    (hz : (QuotientGroup.mk z : X ⧸ Subgroup.center X) ∈ Subgroup.center (X ⧸ Subgroup.center X))
    (hβ₀ : β₀ ∈ D) (hfix : z * β₀ * z⁻¹ = β₀) : z ∈ Subgroup.center X := by
  refine h.mem_center_of_commute_D fun d hd => ?_
  obtain ⟨g, c, hc, hdeq⟩ := h.single_class hβ₀ hd
  have hcen : ∀ x : X, x * c = c * x := Subgroup.mem_center_iff.1 hc
  have hu : g⁻¹ * z * g * z⁻¹ ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff]
    have hgz := Subgroup.mem_center_iff.1 hz (QuotientGroup.mk g)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    set g' : X ⧸ Subgroup.center X := QuotientGroup.mk g with hg'
    set z' : X ⧸ Subgroup.center X := QuotientGroup.mk z with hz'
    calc g'⁻¹ * z' * g' * z'⁻¹ = g'⁻¹ * (z' * g') * z'⁻¹ := by group
      _ = g'⁻¹ * (g' * z') * z'⁻¹ := by rw [← hgz]
      _ = 1 := by group
  set u := g⁻¹ * z * g * z⁻¹ with hudef
  have hucen : ∀ x : X, x * u = u * x := Subgroup.mem_center_iff.1 hu
  have hzg : z * g = g * u * z := by
    calc z * g = g * (g⁻¹ * z * g * z⁻¹) * z := by group
      _ = g * u * z := by rw [hudef]
  have hzdz : z * d * z⁻¹ = d := by
    calc z * d * z⁻¹ = z * (g * β₀ * g⁻¹ * c) * z⁻¹ := by rw [← hdeq]
      _ = (z * g) * β₀ * (z * g)⁻¹ * (z * c * z⁻¹) := by group
      _ = (g * u * z) * β₀ * (g * u * z)⁻¹ * (z * c * z⁻¹) := by rw [hzg]
      _ = g * (u * (z * β₀ * z⁻¹) * u⁻¹) * g⁻¹ * c := by
          have h1 : z * c * z⁻¹ = c := by rw [hcen z]; group
          rw [h1]; group
      _ = g * (u * β₀ * u⁻¹) * g⁻¹ * c := by rw [hfix]
      _ = g * β₀ * g⁻¹ * c := by
          have : u * β₀ * u⁻¹ = β₀ := by rw [← hucen β₀]; group
          rw [this]
      _ = d := hdeq.symm
  have h2 : d * z = z * d := by
    have := mul_inv_eq_iff_eq_mul.1 hzdz
    exact this.symm
  exact h2

end Endgame710

end CFSG.CGT.T75F
