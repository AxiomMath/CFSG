module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

@[expose] def zjNorm (ρ g : H) : H := g * (ρ * g * ρ⁻¹) * (ρ⁻¹ * g * ρ)

@[expose] def IsZJMc (ρ : H) (Q Mh Mc : Subgroup H) : Prop :=
  ∀ g : H, g ∈ Mc ↔ g ∈ Mh ∧ zjNorm ρ g ∈ Q

private theorem mul_self_mul_self_eq_one_of_pow_three {G : Type*} [Group G] {r : G}
    (h : r ^ 3 = 1) : r * (r * r) = 1 := by
  rw [show r * (r * r) = r ^ 3 by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two, pow_one]
    group]
  exact h

private theorem mul_self_eq_inv_of_pow_three {G : Type*} [Group G] {r : G} (h : r ^ 3 = 1) :
    r * r = r⁻¹ :=
  (inv_eq_of_mul_eq_one_right (mul_self_mul_self_eq_one_of_pow_three h)).symm

private theorem inv_mul_inv_eq_self_of_pow_three {G : Type*} [Group G] {r : G}
    (h : r ^ 3 = 1) : r⁻¹ * r⁻¹ = r := by
  have h3 := mul_self_mul_self_eq_one_of_pow_three h
  rw [inv_eq_of_mul_eq_one_right h3]
  calc r * r * (r * r) = r * (r * (r * r)) := by group
    _ = r * 1 := by rw [h3]
    _ = r := by rw [mul_one]

private theorem mul_six_eq {G : Type*} [Group G] {p₁ p₂ p₃ q₁ q₂ q₃ : G}
    (h₂ : p₂ * q₁ = q₁ * p₂) (h₃ : p₃ * q₁ = q₁ * p₃) (h₆ : p₃ * q₂ = q₂ * p₃) :
    p₁ * q₁ * p₂ * q₂ * p₃ * q₃ = p₁ * p₂ * p₃ * q₁ * q₂ * q₃ := by
  calc p₁ * q₁ * p₂ * q₂ * p₃ * q₃
      = p₁ * (q₁ * p₂) * q₂ * p₃ * q₃ := by group
    _ = p₁ * (p₂ * q₁) * q₂ * p₃ * q₃ := by rw [← h₂]
    _ = p₁ * p₂ * q₁ * (q₂ * p₃) * q₃ := by group
    _ = p₁ * p₂ * q₁ * (p₃ * q₂) * q₃ := by rw [← h₆]
    _ = p₁ * p₂ * (q₁ * p₃) * q₂ * q₃ := by group
    _ = p₁ * p₂ * (p₃ * q₁) * q₂ * q₃ := by rw [← h₃]
    _ = p₁ * p₂ * p₃ * q₁ * q₂ * q₃ := by group

private theorem mul_three_eq {G : Type*} [Group G] {p q r : G} (h : q * r = r * q) :
    p * q * r = p * r * q := by
  calc p * q * r = p * (q * r) := by group
    _ = p * (r * q) := by rw [h]
    _ = p * r * q := by group

private theorem zjNorm_conj_of_comm {g x : H} (hcomm : g * ρ = ρ * g) :
    zjNorm ρ (g * x * g⁻¹) = g * zjNorm ρ x * g⁻¹ := by
  have hgiρ : g⁻¹ * ρ = ρ * g⁻¹ := by
    have h := congrArg (fun z => g⁻¹ * z * g⁻¹) hcomm
    rw [show g⁻¹ * (g * ρ) * g⁻¹ = ρ * g⁻¹ by group,
      show g⁻¹ * (ρ * g) * g⁻¹ = g⁻¹ * ρ by group] at h
    exact h.symm
  have hgiρi : g⁻¹ * ρ⁻¹ = ρ⁻¹ * g⁻¹ := by
    have h := congrArg Inv.inv hcomm
    simpa [mul_inv_rev] using h.symm
  have hρig : ρ⁻¹ * g = g * ρ⁻¹ := by
    have h := congrArg Inv.inv hgiρ
    simpa [mul_inv_rev] using h
  have h1 : ρ * (g * x * g⁻¹) * ρ⁻¹ = g * (ρ * x * ρ⁻¹) * g⁻¹ := by
    calc ρ * (g * x * g⁻¹) * ρ⁻¹
        = (ρ * g) * x * (g⁻¹ * ρ⁻¹) := by group
      _ = (g * ρ) * x * (ρ⁻¹ * g⁻¹) := by rw [hcomm, hgiρi]
      _ = g * (ρ * x * ρ⁻¹) * g⁻¹ := by group
  have h2 : ρ⁻¹ * (g * x * g⁻¹) * ρ = g * (ρ⁻¹ * x * ρ) * g⁻¹ := by
    calc ρ⁻¹ * (g * x * g⁻¹) * ρ
        = (ρ⁻¹ * g) * x * (g⁻¹ * ρ) := by group
      _ = (g * ρ⁻¹) * x * (ρ * g⁻¹) := by rw [hρig, hgiρ]
      _ = g * (ρ⁻¹ * x * ρ) * g⁻¹ := by group
  simp only [zjNorm]
  rw [h1, h2]
  group

private theorem zjNorm_conj_of_l {l : H} (hl : l * ρ * l⁻¹ = ρ⁻¹) (hli : l⁻¹ = l) (x : H) :
    zjNorm ρ (l * x * l⁻¹) = l * zjNorm ρ⁻¹ x * l⁻¹ := by
  have hρl : ρ * l = l * ρ⁻¹ := by
    have h : l⁻¹ * (l * ρ * l⁻¹) = l⁻¹ * ρ⁻¹ := congrArg (fun z => l⁻¹ * z) hl
    have h2 : ρ * l⁻¹ = l⁻¹ * ρ⁻¹ := by rw [← h]; group
    rw [hli] at h2
    exact h2
  have hρil : ρ⁻¹ * l = l * ρ := by
    have h : (l * ρ * l⁻¹) * l = ρ⁻¹ * l := congrArg (fun z => z * l) hl
    have h2 : l * ρ = ρ⁻¹ * l := by rw [← h]; group
    exact h2.symm
  have hlρ : l⁻¹ * ρ⁻¹ = ρ * l⁻¹ := by
    have h := congrArg Inv.inv hρl
    simpa [mul_inv_rev] using h
  have hliρ : l⁻¹ * ρ = ρ⁻¹ * l := by
    have h := congrArg Inv.inv hρil
    simpa [mul_inv_rev, hli] using h
  have h1 : ρ * (l * x * l⁻¹) * ρ⁻¹ = l * (ρ⁻¹ * x * ρ) * l⁻¹ := by
    calc ρ * (l * x * l⁻¹) * ρ⁻¹
        = (ρ * l) * x * (l⁻¹ * ρ⁻¹) := by group
      _ = (l * ρ⁻¹) * x * (ρ * l⁻¹) := by rw [hρl, hlρ]
      _ = l * (ρ⁻¹ * x * ρ) * l⁻¹ := by group
  have h2 : ρ⁻¹ * (l * x * l⁻¹) * ρ = l * (ρ * x * ρ⁻¹) * l⁻¹ := by
    calc ρ⁻¹ * (l * x * l⁻¹) * ρ
        = (ρ⁻¹ * l) * x * (l⁻¹ * ρ) := by group
      _ = (l * ρ) * x * (ρ⁻¹ * l) := by
            calc (ρ⁻¹ * l) * x * (l⁻¹ * ρ)
                = (l * ρ) * x * (l⁻¹ * ρ) := by rw [hρil]
              _ = (l * ρ) * x * (ρ⁻¹ * l) := by rw [hliρ]
      _ = l * (ρ * x * ρ⁻¹) * l⁻¹ := by rw [hli]; group
  simp only [zjNorm]
  rw [h1, h2]
  group

theorem zjNorm_comm_rho (hρ : ρ ^ 3 = 1) (m : H) :
    zjNorm ρ (m * (ρ * m⁻¹ * ρ⁻¹)) = 1 := by
  have hρ2 : ρ⁻¹ * ρ⁻¹ = ρ := inv_mul_inv_eq_self_of_pow_three hρ
  have h1 : ρ * (m * (ρ * m⁻¹ * ρ⁻¹)) * ρ⁻¹ =
      (ρ * m * ρ⁻¹) * (ρ⁻¹ * m⁻¹ * ρ) := by
    calc ρ * (m * (ρ * m⁻¹ * ρ⁻¹)) * ρ⁻¹
        = (ρ * m) * (ρ * m⁻¹) * (ρ⁻¹ * ρ⁻¹) := by group
      _ = (ρ * m) * (ρ * m⁻¹) * ρ := by rw [hρ2]
      _ = (ρ * m) * ρ * (m⁻¹ * ρ) := by group
      _ = (ρ * m) * (ρ⁻¹ * ρ⁻¹) * (m⁻¹ * ρ) := by rw [hρ2]
      _ = (ρ * m * ρ⁻¹) * (ρ⁻¹ * m⁻¹ * ρ) := by group
  have h2 : ρ⁻¹ * (m * (ρ * m⁻¹ * ρ⁻¹)) * ρ = (ρ⁻¹ * m * ρ) * m⁻¹ := by
    group
  simp only [zjNorm]
  rw [h1, h2]
  group

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

theorem Q_le_Mh : Q ≤ Mh := fun q hq => E_le_Mh h hMh (h.Q_le_E hq)

theorem tau_mem_Mh : τ ∈ Mh := E_le_Mh h hMh h.tau_mem_E

theorem zjNorm_mul_mem {a b : H} (ha : a ∈ Mh) (hb : b ∈ Mh) :
    zjNorm ρ (a * b) * (zjNorm ρ a * zjNorm ρ b)⁻¹ ∈ Q := by
  haveI hQn : Q.Normal := ⟨fun x hx g => h.normal_Q g x hx⟩
  let φ : H →* H ⧸ Q := QuotientGroup.mk' Q
  have hφ1 : ∀ x : H, φ x = 1 ↔ x ∈ Q := by
    intro x
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' (N := Q)]
  have ha' : ρ * a * ρ⁻¹ ∈ Mh := Mh_normal h hMh (g := ρ) ha
  have ha'' : ρ⁻¹ * a * ρ ∈ Mh := by
    have hh := Mh_normal h hMh (g := ρ⁻¹) ha
    simpa using hh
  have hb' : ρ * b * ρ⁻¹ ∈ Mh := Mh_normal h hMh (g := ρ) hb
  have hb'' : ρ⁻¹ * b * ρ ∈ Mh := by
    have hh := Mh_normal h hMh (g := ρ⁻¹) hb
    simpa using hh
  have hcomm : ∀ x y : H, x ∈ Mh → y ∈ Mh → φ x * φ y = φ y * φ x := by
    intro x y hx hy
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (hφ1 _).mpr (by simpa [commutatorElement_def] using Mh_comm_mem_Q h hMh hx hy)
  have hL : φ (zjNorm ρ (a * b)) =
      φ a * φ b * (φ (ρ * a * ρ⁻¹) * φ (ρ * b * ρ⁻¹)) *
        (φ (ρ⁻¹ * a * ρ) * φ (ρ⁻¹ * b * ρ)) := by
    simp only [zjNorm, map_mul, map_inv, inv_inv] <;> group
  have hR : φ (zjNorm ρ a * zjNorm ρ b) =
      (φ a * φ (ρ * a * ρ⁻¹) * φ (ρ⁻¹ * a * ρ)) *
        (φ b * φ (ρ * b * ρ⁻¹) * φ (ρ⁻¹ * b * ρ)) := by
    simp only [zjNorm, map_mul, map_inv, inv_inv] <;> group
  have hEq : φ (zjNorm ρ (a * b)) = φ (zjNorm ρ a * zjNorm ρ b) := by
    rw [hL, hR]
    rw [show φ a * φ b * (φ (ρ * a * ρ⁻¹) * φ (ρ * b * ρ⁻¹)) *
            (φ (ρ⁻¹ * a * ρ) * φ (ρ⁻¹ * b * ρ))
          = φ a * φ b * φ (ρ * a * ρ⁻¹) * φ (ρ * b * ρ⁻¹) *
            φ (ρ⁻¹ * a * ρ) * φ (ρ⁻¹ * b * ρ) by group,
        show (φ a * φ (ρ * a * ρ⁻¹) * φ (ρ⁻¹ * a * ρ)) *
              (φ b * φ (ρ * b * ρ⁻¹) * φ (ρ⁻¹ * b * ρ))
          = φ a * φ (ρ * a * ρ⁻¹) * φ (ρ⁻¹ * a * ρ) *
            φ b * φ (ρ * b * ρ⁻¹) * φ (ρ⁻¹ * b * ρ) by group,
        mul_six_eq (hcomm (ρ * a * ρ⁻¹) b ha' hb)
          (hcomm (ρ⁻¹ * a * ρ) b ha'' hb)
          (hcomm (ρ⁻¹ * a * ρ) (ρ * b * ρ⁻¹) ha'' hb')]
  exact (hφ1 _).mp (by rw [map_mul, map_inv, hEq, mul_inv_cancel])

theorem zjNorm_inv_rho_mem {g : H} (hg : g ∈ Mh) :
    zjNorm ρ⁻¹ g * (zjNorm ρ g)⁻¹ ∈ Q := by
  haveI hQn : Q.Normal := ⟨fun x hx g => h.normal_Q g x hx⟩
  let φ : H →* H ⧸ Q := QuotientGroup.mk' Q
  have hφ1 : ∀ x : H, φ x = 1 ↔ x ∈ Q := by
    intro x
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' (N := Q)]
  have hg1 : ρ * g * ρ⁻¹ ∈ Mh := Mh_normal h hMh (g := ρ) hg
  have hg2 : ρ⁻¹ * g * ρ ∈ Mh := by
    have hh := Mh_normal h hMh (g := ρ⁻¹) hg
    simpa using hh
  have hcomm : ∀ x y : H, x ∈ Mh → y ∈ Mh → φ x * φ y = φ y * φ x := by
    intro x y hx hy
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (hφ1 _).mpr (by simpa [commutatorElement_def] using Mh_comm_mem_Q h hMh hx hy)
  have hL : φ (zjNorm ρ⁻¹ g) =
      φ g * ((φ ρ)⁻¹ * φ g * φ ρ) * (φ ρ * φ g * (φ ρ)⁻¹) := by
    simp only [zjNorm, map_mul, map_inv, inv_inv] <;> group
  have hR : φ (zjNorm ρ g) =
      φ g * (φ ρ * φ g * (φ ρ)⁻¹) * ((φ ρ)⁻¹ * φ g * φ ρ) := by
    simp only [zjNorm, map_mul, map_inv, inv_inv] <;> group
  have hqr : ((φ ρ)⁻¹ * φ g * φ ρ) * (φ ρ * φ g * (φ ρ)⁻¹) =
      (φ ρ * φ g * (φ ρ)⁻¹) * ((φ ρ)⁻¹ * φ g * φ ρ) := by
    have h1 : (φ ρ)⁻¹ * φ g * φ ρ = φ (ρ⁻¹ * g * ρ) := by
      simp only [map_mul, map_inv, inv_inv]
    have h2 : φ ρ * φ g * (φ ρ)⁻¹ = φ (ρ * g * ρ⁻¹) := by
      simp only [map_mul, map_inv, inv_inv]
    rw [h1, h2]
    exact hcomm (ρ⁻¹ * g * ρ) (ρ * g * ρ⁻¹) hg2 hg1
  have hEq : φ (zjNorm ρ⁻¹ g) = φ (zjNorm ρ g) := by
    rw [hL, hR]
    exact mul_three_eq hqr
  exact (hφ1 _).mp (by rw [map_mul, map_inv, hEq, mul_inv_cancel])

theorem exists_Mc : ∃ Mc : Subgroup H, IsZJMc ρ Q Mh Mc := by
  refine ⟨⟨⟨⟨{g : H | g ∈ Mh ∧ zjNorm ρ g ∈ Q}, ?_⟩, ?_⟩, ?_⟩, fun g => Iff.rfl⟩
  · rintro a b ⟨haM, haQ⟩ ⟨hbM, hbQ⟩
    refine ⟨Mh.mul_mem haM hbM, ?_⟩
    have h := zjNorm_mul_mem h hMh haM hbM
    have hq : zjNorm ρ a * zjNorm ρ b ∈ Q := Q.mul_mem haQ hbQ
    have heq : zjNorm ρ (a * b) =
        (zjNorm ρ (a * b) * (zjNorm ρ a * zjNorm ρ b)⁻¹) *
          (zjNorm ρ a * zjNorm ρ b) := by group
    rw [heq]
    exact Q.mul_mem h hq
  · exact ⟨Mh.one_mem, by simp [zjNorm]⟩
  · rintro a ⟨haM, haQ⟩
    refine ⟨Mh.inv_mem haM, ?_⟩
    have h := zjNorm_mul_mem h hMh haM (Mh.inv_mem haM)
    rw [show a * a⁻¹ = 1 by group, show zjNorm ρ (1 : H) = 1 by simp [zjNorm], one_mul] at h
    have h2 : zjNorm ρ a * zjNorm ρ a⁻¹ ∈ Q := by simpa using Q.inv_mem h
    have heq : zjNorm ρ a⁻¹ = (zjNorm ρ a)⁻¹ * (zjNorm ρ a * zjNorm ρ a⁻¹) := by group
    rw [heq]
    exact Q.mul_mem (Q.inv_mem haQ) h2

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem Mc_le_Mh : Mc ≤ Mh := fun g hg => ((hMc g).mp hg).1

theorem Q_le_Mc : Q ≤ Mc := by
  intro q hq
  rw [hMc q]
  refine ⟨Q_le_Mh h hMh hq, ?_⟩
  have h1 : ρ * q * ρ⁻¹ ∈ Q := h.rho_norm_Q q hq
  have h2 : ρ⁻¹ * q * ρ ∈ Q := by
    have hh := h.normal_Q ρ⁻¹ q hq
    simpa using hh
  have heq : zjNorm ρ q = q * (ρ * q * ρ⁻¹) * (ρ⁻¹ * q * ρ) := rfl
  rw [heq]
  exact Q.mul_mem (Q.mul_mem hq h1) h2

theorem tau_not_mem_Mc : τ ∉ Mc := by
  intro hτ
  have hτQ : zjNorm ρ τ ∈ Q := ((hMc τ).mp hτ).2
  have h1 : ρ * τ * ρ⁻¹ = τ := by
    calc ρ * τ * ρ⁻¹ = (ρ * τ) * ρ⁻¹ := by group
      _ = (τ * ρ) * ρ⁻¹ := by rw [h.tau_rho.symm]
      _ = τ := by group
  have h2 : ρ⁻¹ * τ * ρ = τ := by
    calc ρ⁻¹ * τ * ρ = ρ⁻¹ * (τ * ρ) := by group
      _ = ρ⁻¹ * (ρ * τ) := by rw [h.tau_rho]
      _ = τ := by group
  have hnorm : zjNorm ρ τ = τ := by
    simp only [zjNorm, h1, h2, h.tau_sq, one_mul]
  rw [hnorm] at hτQ
  exact h.tau_not_mem_Q hτQ

theorem Mc_conj_Mh {m c : H} (hm : m ∈ Mh) (hc : c ∈ Mc) : m * c * m⁻¹ ∈ Mc := by
  have hcM : c ∈ Mh := Mc_le_Mh h hMh hMc hc
  have hcomm : m * c * m⁻¹ * c⁻¹ ∈ Q := by
    simpa using Mh_comm_mem_Q h hMh hm hcM
  have heq : m * c * m⁻¹ = (m * c * m⁻¹ * c⁻¹) * c := by group
  rw [heq]
  exact Mc.mul_mem (Q_le_Mc h hMh hMc hcomm) hc

theorem Mc_conj_rho {x : H} (hx : x ∈ Mc) : ρ * x * ρ⁻¹ ∈ Mc := by
  have hxM : x ∈ Mh := Mc_le_Mh h hMh hMc hx
  have hxQ : zjNorm ρ x ∈ Q := ((hMc x).mp hx).2
  rw [hMc (ρ * x * ρ⁻¹)]
  refine ⟨Mh_normal h hMh (g := ρ) hxM, ?_⟩
  rw [zjNorm_conj_of_comm (g := ρ) (x := x) rfl]
  exact h.normal_Q ρ (zjNorm ρ x) hxQ

theorem Mc_conj_t {x : H} (hx : x ∈ Mc) : t * x * t⁻¹ ∈ Mc := by
  have hxM : x ∈ Mh := Mc_le_Mh h hMh hMc hx
  have hxQ : zjNorm ρ x ∈ Q := ((hMc x).mp hx).2
  rw [hMc (t * x * t⁻¹)]
  refine ⟨Mh_normal h hMh (g := t) hxM, ?_⟩
  rw [zjNorm_conj_of_comm (g := t) (x := x) h.t_rho]
  exact h.normal_Q t (zjNorm ρ x) hxQ

theorem Mc_conj_tau {x : H} (hx : x ∈ Mc) : τ * x * τ⁻¹ ∈ Mc := by
  have hxM : x ∈ Mh := Mc_le_Mh h hMh hMc hx
  have hxQ : zjNorm ρ x ∈ Q := ((hMc x).mp hx).2
  rw [hMc (τ * x * τ⁻¹)]
  refine ⟨Mh_normal h hMh (g := τ) hxM, ?_⟩
  rw [zjNorm_conj_of_comm (g := τ) (x := x) h.tau_rho]
  exact h.normal_Q τ (zjNorm ρ x) hxQ

theorem Mc_conj_l {x : H} (hx : x ∈ Mc) : l * x * l⁻¹ ∈ Mc := by
  have hxM : x ∈ Mh := Mc_le_Mh h hMh hMc hx
  have hxQ : zjNorm ρ x ∈ Q := ((hMc x).mp hx).2
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right h.l_sq
  rw [hMc (l * x * l⁻¹)]
  refine ⟨Mh_normal h hMh (g := l) hxM, ?_⟩
  rw [zjNorm_conj_of_l h.l_rho hli x]
  have hxQ' : zjNorm ρ⁻¹ x ∈ Q := by
    have hh := zjNorm_inv_rho_mem h hMh hxM
    have heq : zjNorm ρ⁻¹ x = (zjNorm ρ⁻¹ x * (zjNorm ρ x)⁻¹) * zjNorm ρ x := by group
    rw [heq]
    exact Q.mul_mem hh hxQ
  exact h.normal_Q l (zjNorm ρ⁻¹ x) hxQ'

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
