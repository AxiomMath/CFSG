module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

section Lift

variable {G B : Type*} [Group G] [CommGroup B]

theorem lift_mem_centralizer (ι : B →* G) (φx φy : B →* B) (gx gy s : G) (h u a : B)
    (hs : s = ι h * gx) (hx : ∀ t, gx * ι t * gx⁻¹ = ι (φx t))
    (hy : ∀ t, gy * ι t * gy⁻¹ = ι (φy t)) (hu : gy * gx * gy⁻¹ = ι u * gx)
    (ha : a * (φx a)⁻¹ = h * (φy h)⁻¹ * u⁻¹) :
    ι a * gy ∈ Subgroup.centralizer ({s} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  subst hs
  have hxs : ∀ t, (ι h * gx) * ι t * (ι h * gx)⁻¹ = ι (φx t) := by
    intro t
    have : (ι h * gx) * ι t * (ι h * gx)⁻¹ = ι h * (gx * ι t * gx⁻¹) * (ι h)⁻¹ := by group
    rw [this, hx, ← map_mul, ← map_inv, ← map_mul, mul_comm h, mul_assoc, mul_inv_cancel,
      mul_one]
  have e1 : gy * (ι h * gx) * gy⁻¹ = ι (φy h * u * h⁻¹) * (ι h * gx) := by
    have : gy * (ι h * gx) * gy⁻¹ = (gy * ι h * gy⁻¹) * (gy * gx * gy⁻¹) := by group
    rw [this, hy, hu]
    simp only [map_mul, map_inv]
    group
  have e2 : ι a * gy * (ι h * gx) * (ι a * gy)⁻¹ = ι h * gx := by
    have : ι a * gy * (ι h * gx) * (ι a * gy)⁻¹ = ι a * (gy * (ι h * gx) * gy⁻¹) * (ι a)⁻¹ := by
      group
    rw [this, e1]
    have h3 : ι a * (ι (φy h * u * h⁻¹) * (ι h * gx)) * (ι a)⁻¹ =
        ι (a * (φy h * u * h⁻¹)) * ((ι h * gx) * (ι a)⁻¹ * (ι h * gx)⁻¹) * (ι h * gx) := by
      simp only [map_mul, map_inv]; group
    have h4 : (ι h * gx) * (ι a)⁻¹ * (ι h * gx)⁻¹ = ι (φx a)⁻¹ := by
      rw [← map_inv, hxs, map_inv]
    rw [h3, h4, ← map_mul]
    have h5 : a * (φy h * u * h⁻¹) * (φx a)⁻¹ = 1 := by
      have : a * (φx a)⁻¹ = h * (φy h)⁻¹ * u⁻¹ := ha
      calc a * (φy h * u * h⁻¹) * (φx a)⁻¹ = (a * (φx a)⁻¹) * (φy h * u * h⁻¹) := by
            rw [mul_right_comm]
        _ = 1 := by rw [this]; simp [mul_comm, mul_left_comm, mul_assoc]
    rw [h5, map_one, one_mul]
  exact mul_inv_eq_iff_eq_mul.1 e2

theorem cube_of_conj (ι : B →* G) (φ : B →* B) (g : G) (h : B)
    (hx : ∀ t, g * ι t * g⁻¹ = ι (φ t)) (h3 : g ^ 3 = 1) :
    (ι h * g) ^ 3 = ι (h * φ h * φ (φ h)) := by
  have e : (ι h * g) ^ 3 = ι h * (g * ι h * g⁻¹) * (g * (g * ι h * g⁻¹) * g⁻¹) * g ^ 3 := by
    rw [pow_succ, pow_succ, pow_one]; group
  rw [e, hx, hx, h3, mul_one]
  simp only [map_mul]

end Lift

section Count

variable {G W : Type*} [Group G] [Group W]

theorem card_eq_card_inf_ker_mul_card_map (ψ : G →* W) (C : Subgroup G) :
    Nat.card C = Nat.card ↥(C ⊓ ψ.ker) * Nat.card ↥(C.map ψ) := by
  set f : C →* W := ψ.comp C.subtype with hf
  have h1 : Nat.card C = Nat.card (C ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (C ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : f.range = C.map ψ := by
    ext w
    simp only [MonoidHom.mem_range, Subgroup.mem_map, hf, MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, hc⟩, rfl⟩
  have h4 : Nat.card f.ker = Nat.card ↥(C ⊓ ψ.ker) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨c.1.1, c.1.2, MonoidHom.mem_ker.1 c.2⟩
        invFun := fun d => ⟨⟨d.1, d.2.1⟩, MonoidHom.mem_ker.2 d.2.2⟩
        left_inv := fun c => rfl
        right_inv := fun d => rfl }
  rw [h1, h2, h3, h4, mul_comm]

theorem eightyOne_dvd_of_ker_range (ψ : G →* W) (C : Subgroup G)
    (hV : 9 ∣ Nat.card ↥(C ⊓ ψ.ker)) (hI : 9 ∣ Nat.card ↥(C.map ψ)) : 81 ∣ Nat.card C := by
  rw [card_eq_card_inf_ker_mul_card_map ψ C]
  exact (show (81 : ℕ) = 9 * 9 by norm_num) ▸ mul_dvd_mul hV hI

end Count

section Nine

variable {B : Type*} [Group B]

theorem nine_dvd_card_of_two (H : Subgroup B) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {t₁ t₂ : B}
    (h₁ : t₁ ∈ H) (h₂ : t₂ ∈ H)
    (o₁ : orderOf t₁ = 3) (o₂ : t₂ ^ 3 = 1) (hn : t₂ ∉ Subgroup.zpowers t₁) :
    9 ∣ Nat.card H := by
  set S : Subgroup H := (Subgroup.zpowers t₁).subgroupOf H with hS
  have hSc : Nat.card S = 3 := by
    have hle : Subgroup.zpowers t₁ ≤ H := (Subgroup.zpowers_le).2 h₁
    rw [hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, o₁]
  have : S.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subtype.ext (hH _ g.2 _ n.2)
    rwa [this]⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup S
  have hq : 3 ∣ Nat.card (H ⧸ S) := by
    have hne : (QuotientGroup.mk (⟨t₂, h₂⟩ : H) : H ⧸ S) ≠ 1 := by
      intro hc
      rw [← QuotientGroup.mk_one, QuotientGroup.eq, mul_one, inv_mem_iff] at hc
      exact hn (by simpa [hS, Subgroup.mem_subgroupOf] using hc)
    have hpow : (QuotientGroup.mk (⟨t₂, h₂⟩ : H) : H ⧸ S) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨t₂, h₂⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using o₂)
      rw [this, QuotientGroup.mk_one]
    have hord : orderOf (QuotientGroup.mk (⟨t₂, h₂⟩ : H) : H ⧸ S) = 3 :=
      orderOf_eq_prime hpow hne
    rw [← hord]
    exact orderOf_dvd_natCard _
  obtain ⟨k, hk⟩ := hq
  rw [h, hk, hSc]
  exact ⟨k, by ring⟩

theorem nine_dvd_closure_pair (x y : B) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (hy : y ∉ Subgroup.zpowers x) :
    9 ∣ Nat.card (Subgroup.closure ({x, y} : Set B)) := by
  have hcomm : ∀ a ∈ Subgroup.closure ({x, y} : Set B), ∀ b ∈ Subgroup.closure ({x, y} : Set B),
      a * b = b * a := by
    have hc : ∀ a ∈ ({x, y} : Set B), ∀ b ∈ ({x, y} : Set B), a * b = b * a := by
      rintro a (rfl | rfl) b (rfl | rfl) <;> first | rfl | exact hxy | exact hxy.symm
    have hc' : ∀ a ∈ ({x, y} : Set B), a ∈ Subgroup.centralizer ({x, y} : Set B) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hc b hb a ha)
    intro a ha b hb
    have h1 : Subgroup.closure ({x, y} : Set B) ≤ Subgroup.centralizer ({x, y} : Set B) :=
      (Subgroup.closure_le _).2 hc'
    have h2 := h1 ha
    rw [← Subgroup.centralizer_closure] at h2
    exact (Subgroup.mem_centralizer_iff.1 h2 b hb).symm
  exact nine_dvd_card_of_two _ hcomm (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) (orderOf_eq_prime hx3 hx1) hy3 hy

end Nine

section Conj

theorem card_centralizer_conj {G : Type*} [Group G] (g s : G) :
    Nat.card (Subgroup.centralizer ({g * s * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  have e : ∀ a : G, a ∈ Subgroup.centralizer ({s} : Set G) ↔
      (MulAut.conj g) a ∈ Subgroup.centralizer ({(MulAut.conj g) s} : Set G) := by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← map_mul, ← map_mul, (MulAut.conj g).injective.eq_iff]
  have := Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv e)
  simpa [MulAut.conj_apply] using this.symm

end Conj

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
