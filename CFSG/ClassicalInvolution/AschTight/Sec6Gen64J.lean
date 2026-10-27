module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64H

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

omit [Finite G] in
theorem pairNormalizers_comm (K J : Subgroup G) (z j : G) :
    pairNormalizers J K j z = pairNormalizers K J z j := by
  unfold pairNormalizers
  rw [Set.pair_comm, sup_comm]

namespace Cfg64

variable (c : Cfg64 Ω K J z j u v R T)
include c

theorem mem_Z_sq {x : G} (hx : x ∈ Subgroup.closure ({z, j} : Set G)) :
    x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ∧ x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨Subgroup.mem_sup_left c.z_mem_U, c.hz.sq⟩
    · exact ⟨Subgroup.mem_sup_right c.j_mem_V, c.hj.sq⟩
  | one => exact ⟨Subgroup.one_mem _, mul_one 1⟩
  | mul a b _ _ ha hb =>
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_⟩
    have hab : a * b = b * a := c.UV_comm a ha.1 b hb.1
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha.2, hb.2, one_mul]
  | inv a _ ha =>
    refine ⟨Subgroup.inv_mem _ ha.1, ?_⟩
    rw [← mul_inv_rev, ha.2, inv_one]

theorem mem_Z_iff {x : G} : x ∈ Subgroup.closure ({z, j} : Set G) ↔
    x = 1 ∨ x = z ∨ x = j ∨ x = z * j := by
  constructor
  · intro hx
    obtain ⟨h1, h2⟩ := c.mem_Z_sq hx
    exact c.sq_eq_one_of_mem_UV h1 h2
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem normalizer_UV_le :
    Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G),
      ∀ h ∈ Subgroup.closure ({z, j} : Set G), g * h * g⁻¹ ∈ Subgroup.closure ({z, j} : Set G) := by
    intro g hg h hh
    obtain ⟨h1, h2⟩ := c.mem_Z_sq hh
    have hmem : g * h * g⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
      (Subgroup.mem_normalizer_iff.mp hg h).mp h1
    have hsq : (g * h * g⁻¹) * (g * h * g⁻¹) = 1 := by
      calc (g * h * g⁻¹) * (g * h * g⁻¹) = g * (h * h) * g⁻¹ := by group
        _ = 1 := by rw [h2]; group
    exact c.mem_Z_iff.mpr (c.sq_eq_one_of_mem_UV hmem hsq)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer _).inv_mem hg) _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

omit [Finite G] in
theorem le_normalizer_Z_of_centralizes {g : G} (hgz : g ∈ Subgroup.centralizer ({z} : Set G))
    (hgj : g ∈ Subgroup.centralizer ({j} : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
  have h1 : g ∈ Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) :
      Set G) := by
    rw [Subgroup.centralizer_closure]
    intro w hw
    rcases hw with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hgz).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hgj).symm
  exact Subgroup.centralizer_le_normalizer _ h1

theorem R_quat : IsQuatSub R ∧ IsUniqueInvolution R z :=
  ⟨isQuatSub_of_mem_RSet c.hΩ (mem_RSet_of_isSylow2In c.hK c.hR),
    AscL62.isUniqueInvolution_of_le c.hz c.hR.1 (mem_of_isSylow2In c.hz c.hR)⟩

theorem exists_r : ∃ r ∈ R, r ∉ Subgroup.zpowers u := by
  by_contra h
  push Not at h
  have h1 := Subgroup.card_le_of_le (show R ≤ Subgroup.zpowers u from h)
  have h2 := c.natCard_R
  have h3 := c.four_le_U
  omega

theorem sq_of_not_mem {r : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) : r * r = z :=
  AscL62.sq_eq_of_not_mem c.R_quat.1 c.R_quat.2 c.huR inferInstance c.natCard_R hr hru

theorem conj_U_of_not_mem {r : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) {w : G}
    (hw : w ∈ Subgroup.zpowers u) : r * w * r⁻¹ = w⁻¹ :=
  AscL62.conj_eq_inv_of_not_mem c.R_quat.1 c.R_quat.2 c.huR inferInstance c.natCard_R hr hru hw

theorem R_le_normalizer_Z :
    R ≤ Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :=
  c.hRN.trans c.normalizer_UV_le

theorem R_le_Y : R ≤ pairNormalizers K J z j :=
  le_sup_of_le_left (le_inf c.hR.1 c.R_le_normalizer_Z)

theorem T_le_Y : T ≤ pairNormalizers K J z j := pairNormalizers_comm K J z j ▸ c.symm.R_le_Y

omit [Finite G] in
theorem CKj_le_Y : K ⊓ Subgroup.centralizer ({j} : Set G) ≤ pairNormalizers K J z j :=
  fun _ hx => Subgroup.mem_sup_left ⟨hx.1, c.le_normalizer_Z_of_centralizes
    (c.CKj_le_centralizer_z hx) hx.2⟩

theorem X_le_Y : (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) ≤
    pairNormalizers K J z j := by
  rw [c.X_eq]
  refine sup_le ?_ c.CKj_le_Y
  have := c.symm.CKj_le_Y
  rwa [pairNormalizers_comm K J z j] at this

theorem NKZ_le : K ⊓ Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G)
    ≤ ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G))) ⊔ R := by
  intro y hy
  have hjZ : j ∈ Subgroup.closure ({z, j} : Set G) := Subgroup.subset_closure (by simp)
  have hyj : y * j * y⁻¹ ∈ Subgroup.closure ({z, j} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hy.2 j).mp hjZ
  have hyz : y * z * y⁻¹ = z := by rw [c.z_comm hy.1]; group
  have hX : K ⊓ Subgroup.centralizer ({j} : Set G) ≤
      (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) :=
    c.X_eq ▸ le_sup_right
  rcases c.mem_Z_iff.mp hyj with h | h | h | h
  · exfalso
    apply c.hj.ne_one
    have := congrArg (fun w => y⁻¹ * w * y) h
    simpa [mul_assoc] using this
  · exfalso
    apply c.z_ne_j
    have h1 : y * j * y⁻¹ = y * z * y⁻¹ := by rw [h, hyz]
    have := congrArg (fun w => y⁻¹ * w * y) h1
    simpa [mul_assoc] using this.symm
  · refine Subgroup.mem_sup_left (hX ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩)
    calc y * j = (y * j * y⁻¹) * y := by group
      _ = j * y := by rw [h]
  · obtain ⟨r, hr, hru⟩ := c.exists_r
    have hr' : r⁻¹ ∉ Subgroup.zpowers u := fun h' => hru (by simpa using Subgroup.inv_mem _ h')
    have hrj := c.conj_j_of_not_mem (R.inv_mem hr) hr'
    have hyr : y * r⁻¹ ∈ K ⊓ Subgroup.centralizer ({j} : Set G) := by
      refine ⟨K.mul_mem hy.1 (K.inv_mem (c.hR.1 hr)), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have e : (y * r⁻¹) * j * (y * r⁻¹)⁻¹ = j := by
        calc (y * r⁻¹) * j * (y * r⁻¹)⁻¹ = y * (r⁻¹ * j * r⁻¹⁻¹) * y⁻¹ := by group
          _ = y * (z * j) * y⁻¹ := by rw [hrj]
          _ = (y * z * y⁻¹) * (y * j * y⁻¹) := by group
          _ = z * (z * j) := by rw [hyz, h]
          _ = j := by rw [← mul_assoc, c.hz.sq, one_mul]
      calc y * r⁻¹ * j = (y * r⁻¹) * j * (y * r⁻¹)⁻¹ * (y * r⁻¹) := by group
        _ = j * (y * r⁻¹) := by rw [e]
    have := Subgroup.mul_mem _ (Subgroup.mem_sup_left (hX hyr)) (Subgroup.mem_sup_right hr)
    simpa using this

theorem Y_le : pairNormalizers K J z j ≤
    ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G))) ⊔ R ⊔ T := by
  refine sup_le (c.NKZ_le.trans le_sup_left) ?_
  intro y hy
  have hZ : Subgroup.closure ({j, z} : Set G) = Subgroup.closure ({z, j} : Set G) := by
    rw [Set.pair_comm]
  have hy' : y ∈ J ⊓ Subgroup.normalizer
      ((Subgroup.closure ({j, z} : Set G) : Subgroup G) : Set G) := by
    rw [hZ]
    exact hy
  have h := c.symm.NKZ_le hy'
  have hX : (K ⊓ Subgroup.normalizer (J : Set G)) ⊔ (J ⊓ Subgroup.normalizer (K : Set G)) =
      (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) :=
    sup_comm _ _
  rw [hX] at h
  have hle : ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G))) ⊔ T ≤
      ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G))) ⊔ R ⊔ T :=
    sup_le (le_sup_of_le_left le_sup_left) le_sup_right
  exact hle h

theorem Y_le_normalizer_X {N₀K N₀J : Subgroup G}
    (hK0 : OddCompl (K ⊓ Subgroup.centralizer ({j} : Set G)) (Subgroup.zpowers u) N₀K)
    (hJ0 : OddCompl (J ⊓ Subgroup.centralizer ({z} : Set G)) (Subgroup.zpowers v) N₀J) :
    pairNormalizers K J z j ≤ Subgroup.normalizer
      (((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) :
        Subgroup G) : Set G) := by
  refine c.Y_le.trans (sup_le (sup_le Subgroup.le_normalizer ?_) ?_)
  · intro r hr
    by_cases hru : r ∈ Subgroup.zpowers u
    · have hrX : r ∈ (J ⊓ Subgroup.normalizer (K : Set G)) ⊔
          (K ⊓ Subgroup.normalizer (J : Set G)) :=
        c.X_eq ▸ Subgroup.mem_sup_right ⟨c.hUK hru, c.U_le_centralizer hru⟩
      exact Subgroup.le_normalizer hrX
    · exact mem_normalizer_iff_conjSub_eq.mpr (c.conjSub_X hK0 hJ0 hr hru)
  · intro t ht
    by_cases htv : t ∈ Subgroup.zpowers v
    · have htX : t ∈ (J ⊓ Subgroup.normalizer (K : Set G)) ⊔
          (K ⊓ Subgroup.normalizer (J : Set G)) :=
        c.X_eq ▸ Subgroup.mem_sup_left ⟨c.hVJ htv, c.symm.U_le_centralizer htv⟩
      exact Subgroup.le_normalizer htX
    · have h := c.symm.conjSub_X hJ0 hK0 ht htv
      rw [sup_comm] at h
      exact mem_normalizer_iff_conjSub_eq.mpr h

end Cfg64

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
