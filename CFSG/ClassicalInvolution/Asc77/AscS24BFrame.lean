module

public import CFSG.ClassicalInvolution.Asc77.AscT7XLat

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem rep_mul_self {W : Subgroup G} (c : Thompson.Ctx p f Ω W) (ρ : Thompson.Rep Ω W) {z₀ : G}
    (hz : IsUniqueInvolution ρ.K z₀) : ρ.r * ρ.r = z₀ := by
  obtain ⟨hRW, -, hcyc, -, hcard⟩ :=
    Thompson.inf_W_of_mem_D c.hp c.hq c.hΩ c.hW ρ.hR ρ.hK ρ.hRK
  have hzKW := Thompson.uniqueInvolution_mem_W c.hp c.hq c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hz
  have hzR : z₀ ∈ ρ.R := by
    have h : z₀ ∈ ρ.R ⊓ W := by rw [hRW]; exact hzKW
    exact h.1
  exact AscL62.sq_eq_of_not_mem (c.hΩ.isQuatSub_of_mem_RSet c.hp ρ.hR.1)
    (AscL62.isUniqueInvolution_of_le hz ρ.hRK.1 hzR) inf_le_left hcyc hcard ρ.hr
    (fun h => ρ.hrW h.2)

structure Ctx8 (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Type where
  hs : Hyp23Setting p f Ω K K' z
  hd : Hyp24Data Ω K K' W S R R' z u
  h8 : Nat.card ↥R = 8
  D : T7X.Frame24 p f Ω W
  hK : D.F.ρ.K = K
  hK' : D.F.ρ'.K = K'
  hR : D.F.ρ.R = R
  hR' : D.F.ρ'.R = R'
  hz : D.F.z = z

theorem Ctx8.nonempty [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8) :
    Nonempty (Ctx8 p f Ω K K' W S R R' z u) := by
  obtain ⟨D, hK, hK', hR, hR', hz⟩ := T7X.exists_frame24 hs hd
  exact ⟨⟨hs, hd, h8, D, hK, hK', hR, hR', hz⟩⟩

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

theorem m_eq_one : C.D.m = 1 := by
  have h1 := Thompson.D_card C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW C.D.F.ρ.hR
  have h2 : Nat.card ↥(C.D.F.ρ.R ⊓ W) = 4 * C.D.m := by
    rw [← C.D.h₁, Nat.card_zpowers, C.D.o₁]
  have h3 : Nat.card ↥C.D.F.ρ.R = 8 := by rw [C.hR]; exact C.h8
  omega

theorem orderOf_x₁ : orderOf C.D.x₁ = 4 := by rw [C.D.o₁, C.m_eq_one]

theorem orderOf_x₂ : orderOf C.D.x₂ = 4 := by rw [C.D.o₂, C.m_eq_one]

theorem orderOf_x₃ : orderOf C.D.x₃ = 4 := by rw [C.D.o₃, C.m_eq_one]

theorem x₁_sq : C.D.x₁ ^ 2 = z := by
  have h := C.D.z₁
  rw [C.m_eq_one, C.hz] at h
  simpa using h

theorem x₂_sq : C.D.x₂ ^ 2 = z := by
  have h := C.D.z₂
  rw [C.m_eq_one, C.hz] at h
  simpa using h

theorem x₃_sq : C.D.x₃ ^ 2 = C.D.F.j := by
  have h := C.D.z₃
  rw [C.m_eq_one] at h
  simpa using h

theorem eps_eq_one : C.D.x₁ * C.D.x₂⁻¹ * C.D.x₃ ^ 2 = 1 := by
  have h := C.D.eps_pow_eq_one C.hd.hZ
  rw [C.m_eq_one, pow_one] at h
  exact h

theorem x₂_eq : C.D.x₂ = C.D.x₁ * C.D.x₃ ^ 2 := by
  have h := C.eps_eq_one
  have hc : Commute C.D.x₂⁻¹ (C.D.x₃ ^ 2) := (C.D.comm23.pow_right 2).inv_left
  calc C.D.x₂ = C.D.x₂ * (C.D.x₁ * C.D.x₂⁻¹ * C.D.x₃ ^ 2) := by rw [h, mul_one]
    _ = C.D.x₂ * C.D.x₁ * (C.D.x₂⁻¹ * C.D.x₃ ^ 2) := by group
    _ = C.D.x₂ * C.D.x₁ * (C.D.x₃ ^ 2 * C.D.x₂⁻¹) := by rw [hc.eq]
    _ = C.D.x₂ * C.D.x₁ * C.D.x₃ ^ 2 * C.D.x₂⁻¹ := by group
    _ = C.D.x₁ * C.D.x₃ ^ 2 := by
      rw [show C.D.x₂ * C.D.x₁ = C.D.x₁ * C.D.x₂ from C.D.comm12.eq.symm]
      have hc2 : Commute C.D.x₂ (C.D.x₃ ^ 2) := C.D.comm23.pow_right 2
      calc C.D.x₁ * C.D.x₂ * C.D.x₃ ^ 2 * C.D.x₂⁻¹
          = C.D.x₁ * (C.D.x₂ * C.D.x₃ ^ 2) * C.D.x₂⁻¹ := by group
        _ = C.D.x₁ * (C.D.x₃ ^ 2 * C.D.x₂) * C.D.x₂⁻¹ := by rw [hc2.eq]
        _ = C.D.x₁ * C.D.x₃ ^ 2 := by group

theorem j_eq : C.D.F.j = C.D.x₁⁻¹ * C.D.x₂ := by
  rw [← C.x₃_sq, C.x₂_eq]
  group

theorem x₁_mem_R : C.D.x₁ ∈ R :=
  (congrArg (fun X => C.D.x₁ ∈ X) C.hR).mp
    (C.D.h₁ ▸ Subgroup.mem_zpowers C.D.x₁ : C.D.x₁ ∈ C.D.F.ρ.R ⊓ W).1

theorem x₂_mem_R' : C.D.x₂ ∈ R' :=
  (congrArg (fun X => C.D.x₂ ∈ X) C.hR').mp
    (C.D.h₂ ▸ Subgroup.mem_zpowers C.D.x₂ : C.D.x₂ ∈ C.D.F.ρ'.R ⊓ W).1

theorem x₃_mem_R₃ : C.D.x₃ ∈ C.D.F.ρ₃.R :=
  (C.D.h₃ ▸ Subgroup.mem_zpowers C.D.x₃ : C.D.x₃ ∈ C.D.F.ρ₃.R ⊓ W).1

theorem x₁_mem_K : C.D.x₁ ∈ K := C.hd.hR.2.1 C.x₁_mem_R

theorem x₂_mem_K' : C.D.x₂ ∈ K' := C.hd.hR'.2.1 C.x₂_mem_R'

theorem x₃_mem_J : C.D.x₃ ∈ C.D.F.ρ₃.K := C.D.F.ρ₃.hRK.1 C.x₃_mem_R₃

theorem j_mem_sup : C.D.F.j ∈ K ⊔ K' := by
  rw [C.j_eq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left C.x₁_mem_K))
    (Subgroup.mem_sup_right C.x₂_mem_K')

include C in
theorem hzK : IsUniqueInvolution K z := C.hs.hz

include C in
theorem hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hs.hz C.hs.hK'

theorem hjJ : IsUniqueInvolution C.D.F.ρ₃.K C.D.F.j := C.D.F.hj

theorem z_ne_j : z ≠ C.D.F.j := by
  intro h
  have hJ : C.D.F.ρ₃.K ∈ twinSet Ω K := ⟨C.D.F.ρ₃.hK, z, C.hzK,
    (congrArg (IsUniqueInvolution C.D.F.ρ₃.K) h).mpr C.hjJ⟩
  rw [C.hs.twinSet_eq] at hJ
  rcases hJ with hJ | hJ
  · exact C.D.F.hne₁ (C.hK.trans hJ.symm)
  · exact C.D.F.hne₂ (C.hK'.trans hJ.symm)

theorem zpowers_inf_eq_bot : Subgroup.zpowers C.D.x₁ ⊓ Subgroup.zpowers C.D.x₃ = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  by_contra hy1
  have h4 : y ^ 4 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy.1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      ← C.orderOf_x₁, pow_orderOf_eq_one, one_zpow]
  have key : ∀ a ∈ Subgroup.zpowers C.D.x₁ ⊓ Subgroup.zpowers C.D.x₃, a ≠ 1 → a * a = 1 →
      False := by
    intro a ha ha1 haa
    have haK : a ∈ K := (Subgroup.zpowers_le.mpr C.x₁_mem_K) ha.1
    have haJ : a ∈ C.D.F.ρ₃.K := (Subgroup.zpowers_le.mpr C.x₃_mem_J) ha.2
    have h1 : a = z := (C.hzK.unique a haK haa).resolve_left ha1
    have h2 : a = C.D.F.j := (C.hjJ.unique a haJ haa).resolve_left ha1
    exact C.z_ne_j (h1.symm.trans h2)
  by_cases hyy : y * y = 1
  · exact key y hy hy1 hyy
  · refine key (y * y) (Subgroup.mul_mem _ hy hy) hyy ?_
    calc y * y * (y * y) = y ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4

theorem r_mul_self : C.D.F.ρ.r * C.D.F.ρ.r = z :=
  (rep_mul_self C.D.c C.D.F.ρ C.D.F.hz).trans C.hz

theorem t_mul_self : C.D.F.ρ'.r * C.D.F.ρ'.r = z :=
  (rep_mul_self C.D.c C.D.F.ρ' C.D.F.hz').trans C.hz

theorem r_mem_R : C.D.F.ρ.r ∈ R := (congrArg (fun X => C.D.F.ρ.r ∈ X) C.hR).mp C.D.F.ρ.hr

theorem t_mem_R' : C.D.F.ρ'.r ∈ R' := (congrArg (fun X => C.D.F.ρ'.r ∈ X) C.hR').mp C.D.F.ρ'.hr

theorem r_mem_K : C.D.F.ρ.r ∈ K := C.hd.hR.2.1 C.r_mem_R

theorem t_mem_K' : C.D.F.ρ'.r ∈ K' := C.hd.hR'.2.1 C.t_mem_R'

include C in
theorem R_ne_R' : R ≠ R' := by
  intro h
  have hst := C.hs.stand
  have h2 := hst.hyp.card_le_two_of_le_inf hst.mem C.hs.hK'.1 C.hs.hne.symm
    (C.D.F.ρ.hRK.2.1.to_le (le_of_eq C.hR.symm)) C.hd.hR.2.1 (h ▸ C.hd.hR'.2.1)
  rw [C.h8] at h2
  omega

include C in
theorem commutes_R_R' : Commutes R R' :=
  l6_7_proved p f C.hs.stand.odd C.hs.stand.five G Ω C.hs.stand.hyp S R C.hd.hR.1 R' C.hd.hR'.1
    C.hd.hR.2.2 C.hd.hR'.2.2 C.R_ne_R'

theorem commute_r_t : Commute C.D.F.ρ.r C.D.F.ρ'.r :=
  C.commutes_R_R' _ C.r_mem_R _ C.t_mem_R'

theorem exists_nf {w : G} (hw : w ∈ W) : ∃ a b : ℤ, w = C.D.x₁ ^ a * C.D.x₃ ^ b := by
  obtain ⟨i, j, k, rfl⟩ :=
    A3Mod.exists_normal_form C.D.comm12 C.D.comm13 C.D.comm23 (C.D.hgen hw)
  refine ⟨i + j, 2 * j + k, ?_⟩
  have hc : Commute C.D.x₁ (C.D.x₃ ^ 2) := C.D.comm13.pow_right 2
  rw [C.x₂_eq, hc.mul_zpow, ← zpow_natCast, ← zpow_mul, zpow_add, zpow_add]
  have h1 := (C.D.comm13.zpow_zpow ((2 : ℕ) * j) i).eq
  push_cast at h1 ⊢
  calc C.D.x₁ ^ i * (C.D.x₁ ^ j * C.D.x₃ ^ (2 * j)) * C.D.x₃ ^ k
      = C.D.x₁ ^ i * C.D.x₁ ^ j * (C.D.x₃ ^ (2 * j) * C.D.x₃ ^ k) := by group
    _ = C.D.x₁ ^ i * C.D.x₁ ^ j * (C.D.x₃ ^ (2 * j) * C.D.x₃ ^ k) := rfl

theorem mul_nf (a b c d : ℤ) :
    C.D.x₁ ^ a * C.D.x₃ ^ b * (C.D.x₁ ^ c * C.D.x₃ ^ d) = C.D.x₁ ^ (a + c) * C.D.x₃ ^ (b + d) := by
  have h := (C.D.comm13.zpow_zpow c b).eq
  calc C.D.x₁ ^ a * C.D.x₃ ^ b * (C.D.x₁ ^ c * C.D.x₃ ^ d)
      = C.D.x₁ ^ a * (C.D.x₃ ^ b * C.D.x₁ ^ c) * C.D.x₃ ^ d := by group
    _ = C.D.x₁ ^ a * (C.D.x₁ ^ c * C.D.x₃ ^ b) * C.D.x₃ ^ d := by rw [← h]
    _ = C.D.x₁ ^ (a + c) * C.D.x₃ ^ (b + d) := by rw [zpow_add, zpow_add]; group

theorem conj_r_nf (a b : ℤ) :
    C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ.r⁻¹ = C.D.x₁ ^ (b - a) * C.D.x₃ ^ b := by
  have h := A3Mod.conj_nf_r C.D.comm12 C.D.comm13 C.D.r₁ C.D.r₂ C.D.r₃ a 0 b
  simpa using h

theorem conj_t_nf (a b : ℤ) :
    C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ'.r⁻¹ =
      C.D.x₁ ^ (a + b) * C.D.x₃ ^ (3 * b) := by
  have h := A3Mod.conj_nf_t C.D.comm23 C.D.t₁ C.D.t₂ C.D.t₃ a 0 b
  simp only [zpow_zero, mul_one, sub_zero] at h
  rw [h, C.x₂_eq, (C.D.comm13.pow_right 2).mul_zpow, ← zpow_natCast C.D.x₃ 2, ← zpow_mul]
  have e := C.mul_nf a 0 b (↑(2 : ℕ) * b)
  simp only [zpow_zero, mul_one] at e
  calc C.D.x₁ ^ a * (C.D.x₁ ^ b * C.D.x₃ ^ ((↑(2 : ℕ) : ℤ) * b)) * C.D.x₃ ^ b
      = C.D.x₁ ^ a * C.D.x₁ ^ b * (C.D.x₃ ^ ((↑(2 : ℕ) : ℤ) * b) * C.D.x₃ ^ b) := by group
    _ = C.D.x₁ ^ (a + b) * C.D.x₃ ^ (3 * b) := by
      rw [← zpow_add, ← zpow_add]; congr 2; push_cast; ring

theorem eq_one_of_nf (a b : ℤ) (h : C.D.x₁ ^ a * C.D.x₃ ^ b = 1) :
    C.D.x₁ ^ a = 1 ∧ C.D.x₃ ^ b = 1 := by
  have h1 : C.D.x₁ ^ a = (C.D.x₃ ^ b)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hmem : C.D.x₁ ^ a ∈ Subgroup.zpowers C.D.x₁ ⊓ Subgroup.zpowers C.D.x₃ := by
    refine ⟨Subgroup.zpow_mem_zpowers _ _, ?_⟩
    rw [h1, ← zpow_neg]
    exact Subgroup.zpow_mem_zpowers _ _
  rw [C.zpowers_inf_eq_bot, Subgroup.mem_bot] at hmem
  refine ⟨hmem, ?_⟩
  rw [hmem] at h1
  exact inv_eq_one.mp h1.symm

theorem four_dvd_of_x₁ {a : ℤ} (h : C.D.x₁ ^ a = 1) : (4 : ℤ) ∣ a := by
  have := orderOf_dvd_iff_zpow_eq_one.mpr h
  rw [C.orderOf_x₁] at this
  exact_mod_cast this

theorem four_dvd_of_x₃ {a : ℤ} (h : C.D.x₃ ^ a = 1) : (4 : ℤ) ∣ a := by
  have := orderOf_dvd_iff_zpow_eq_one.mpr h
  rw [C.orderOf_x₃] at this
  exact_mod_cast this

theorem mem_sup_of_even {a b : ℤ} (hb : Even b) : C.D.x₁ ^ a * C.D.x₃ ^ b ∈ K ⊔ K' := by
  obtain ⟨c, rfl⟩ := hb
  have hx3 : C.D.x₃ ^ (c + c) = C.D.F.j ^ c := by
    rw [← C.x₃_sq, ← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  rw [hx3]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_sup_left C.x₁_mem_K) _)
    (Subgroup.zpow_mem _ C.j_mem_sup _)

include C in
theorem mem_sup_of_mul_self {w : G} (hw : w ∈ W) (h2 : w * w = 1) : w ∈ K ⊔ K' := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  rw [C.mul_nf] at h2
  have hb := C.four_dvd_of_x₃ (C.eq_one_of_nf _ _ h2).2
  refine C.mem_sup_of_even ?_
  obtain ⟨k, hk⟩ := hb
  exact ⟨k, by omega⟩

theorem r_mul_mem_sup {w : G} (hw : w ∈ W) (h2 : C.D.F.ρ.r * w * (C.D.F.ρ.r * w) = 1) :
    C.D.F.ρ.r * w ∈ K ⊔ K' := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  have hrr : C.D.F.ρ.r * C.D.F.ρ.r = C.D.x₁ ^ (2 : ℤ) * C.D.x₃ ^ (0 : ℤ) := by
    rw [zpow_zero, mul_one]
    exact C.r_mul_self.trans (by exact_mod_cast C.x₁_sq.symm)
  have e : C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * (C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b)) =
      C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ.r⁻¹ * (C.D.F.ρ.r * C.D.F.ρ.r) *
        (C.D.x₁ ^ a * C.D.x₃ ^ b) := by group
  rw [e, C.conj_r_nf, hrr, C.mul_nf, C.mul_nf] at h2
  have hb := C.four_dvd_of_x₃ (C.eq_one_of_nf _ _ h2).2
  have hev : Even b := by obtain ⟨k, hk⟩ := hb; exact ⟨k, by omega⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left C.r_mem_K) (C.mem_sup_of_even hev)

theorem rt_mul_mem_sup {w : G} (hw : w ∈ W)
    (h2 : C.D.F.ρ.r * C.D.F.ρ'.r * w * (C.D.F.ρ.r * C.D.F.ρ'.r * w) = 1) :
    C.D.F.ρ.r * C.D.F.ρ'.r * w ∈ K ⊔ K' := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  have hrt : C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r) = 1 := by
    calc C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r)
        = C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.F.ρ.r) * C.D.F.ρ'.r := by group
      _ = C.D.F.ρ.r * (C.D.F.ρ.r * C.D.F.ρ'.r) * C.D.F.ρ'.r := by rw [C.commute_r_t.eq]
      _ = (C.D.F.ρ.r * C.D.F.ρ.r) * (C.D.F.ρ'.r * C.D.F.ρ'.r) := by group
      _ = 1 := by
        rw [C.r_mul_self, C.t_mul_self]
        exact (C.hzK.sq)
  have e : C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) *
        (C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b)) =
      C.D.F.ρ.r * (C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ'.r⁻¹) * C.D.F.ρ.r⁻¹ *
        (C.D.F.ρ.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r)) * (C.D.x₁ ^ a * C.D.x₃ ^ b) := by
    group
  rw [e, hrt, mul_one, C.conj_t_nf, C.conj_r_nf, C.mul_nf] at h2
  have hb := C.four_dvd_of_x₁ (C.eq_one_of_nf _ _ h2).1
  have hev : Even b := by obtain ⟨k, hk⟩ := hb; exact ⟨k, by omega⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left C.r_mem_K)
    (Subgroup.mem_sup_right C.t_mem_K')) (C.mem_sup_of_even hev)

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
