module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.FusionInterface
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YInterface

public section

namespace CFSG.EvenSporadicStandard.J4Std.EgawaApply

open Subgroup

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G} {Y : Subgroup G}

abbrev Mn (Y : Subgroup G) : Subgroup G := normalizer (Y : Set G)

abbrev Sec (Y : Subgroup G) : Type := ↥(Mn Y) ⧸ Y.subgroupOf (Mn Y)

noncomputable def pi (Y : Subgroup G) : ↥(Mn Y) →* Sec Y := QuotientGroup.mk' _

theorem pi_eq_one_iff {m : ↥(Mn Y)} : pi Y m = 1 ↔ (m : G) ∈ Y :=
  (QuotientGroup.eq_one_iff m).trans mem_subgroupOf

theorem pi_eq_iff {a b : ↥(Mn Y)} : pi Y a = pi Y b ↔ ((a⁻¹ * b : ↥(Mn Y)) : G) ∈ Y :=
  QuotientGroup.eq.trans mem_subgroupOf

theorem pi_surjective (Y : Subgroup G) : Function.Surjective (pi Y) :=
  QuotientGroup.mk'_surjective _

theorem U_le_L (hD : LocalData L U T0) : U ≤ L := hD.U_le_T0.trans hD.T0_le_L

theorem Hloc_le_M (hS : Setting L z) (hD : LocalData L U T0) (hF : FusionData L U z Y) :
    Hloc L U ≤ Mn Y :=
  (Hloc_le_N hS (U_le_L hD)).trans hF.N_le_M

theorem z_mem_M (hF : FusionData L U z Y) : z ∈ Mn Y := hF.N_le_M (V_le_N z_mem_V)

theorem Csub_le_M (hF : FusionData L U z Y) : Csub U z ≤ Mn Y := fun _ hc =>
  hF.N_le_M (mem_Csub.1 hc).1

theorem mem_Y_iff_of_mem_Hloc (hD : LocalData L U T0) (hY : YStruct L U z Y) {h : G}
    (hh : h ∈ Hloc L U) : h ∈ Y ↔ h ∈ U := by
  refine ⟨fun hy => ?_, fun hu => hY.U_le hu⟩
  exact hD.selfCentralizing h (Hloc_le_L hh) (mem_Csub.1 (hY.le_W hy)).2

@[expose] noncomputable def psi (hH : Hloc L U ≤ Mn Y) : Hloc L U →* Sec Y :=
  (pi Y).comp (inclusion hH)

theorem psi_apply (hH : Hloc L U ≤ Mn Y) (h : Hloc L U) :
    psi hH h = pi Y ⟨h, hH h.2⟩ := rfl

theorem ker_psi (hD : LocalData L U T0) (hY : YStruct L U z Y) (hH : Hloc L U ≤ Mn Y) :
    (psi hH).ker = U.subgroupOf (Hloc L U) := by
  ext h
  rw [MonoidHom.mem_ker, psi_apply, pi_eq_one_iff, mem_subgroupOf]
  exact mem_Y_iff_of_mem_Hloc hD hY h.2

theorem isSporadic_range_psi (hD : LocalData L U T0) (hY : YStruct L U z Y)
    (hH : Hloc L U ≤ Mn Y) (hq : QuotData L U) :
    CFSG.Blueprint.NativeSporadic.IsSporadic (psi hH).range .M24 := by
  obtain ⟨f, hf, hker⟩ := hq
  exact ⟨(QuotientGroup.quotientKerEquivRange (psi hH)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((ker_psi hD hY hH).trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf))⟩

theorem psi_comm_pi (hS : Setting L z) (hH : Hloc L U ≤ Mn Y) (hzM : z ∈ Mn Y)
    (h : Hloc L U) : psi hH h * pi Y ⟨z, hzM⟩ = pi Y ⟨z, hzM⟩ * psi hH h := by
  rw [psi_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (hS.z_comm h (Hloc_le_L h.2)).symm

theorem pi_z_mul_self (hS : Setting L z) (hzM : z ∈ Mn Y) :
    pi Y ⟨z, hzM⟩ * pi Y ⟨z, hzM⟩ = 1 := by
  rw [← map_mul]
  have : (⟨z, hzM⟩ * ⟨z, hzM⟩ : ↥(Mn Y)) = 1 := Subtype.ext hS.z_mul_self
  rw [this, map_one]

theorem pi_z_ne_one (hY : YStruct L U z Y) (hzM : z ∈ Mn Y) : pi Y ⟨z, hzM⟩ ≠ 1 :=
  fun h => hY.z_not_mem (pi_eq_one_iff.1 h)

theorem cover_of_comm (hS : Setting L z) (hD : LocalData L U T0) (hY : YStruct L U z Y)
    (hF : FusionData L U z Y) (hzM : z ∈ Mn Y) (x : Sec Y)
    (hx : x * pi Y ⟨z, hzM⟩ = pi Y ⟨z, hzM⟩ * x) :
    ∃ k ∈ (psi (Hloc_le_M hS hD hF)).range, x = k ∨ x = k * pi Y ⟨z, hzM⟩ := by
  obtain ⟨m, rfl⟩ := pi_surjective Y x
  rw [← map_mul, ← map_mul, pi_eq_iff] at hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hx
  have hmN : (m : G) ∈ Nsub U z := by
    have h1 := hF.cent_le_N ((m : G)⁻¹) (inv_mem m.2) _ hx (by group)
    simpa using inv_mem h1
  obtain ⟨w, hw, h, hh, hmwh⟩ := hF.N_eq m hmN
  have hwM : w ∈ Mn Y := Csub_le_M hF hw
  have hhM : h ∈ Mn Y := Hloc_le_M hS hD hF hh
  have hm : m = ⟨w, hwM⟩ * ⟨h, hhM⟩ := Subtype.ext hmwh
  have hψ : psi (Hloc_le_M hS hD hF) ⟨h, hh⟩ = pi Y ⟨h, hhM⟩ := rfl
  rcases hY.cover w hw with hwY | hwY
  · refine ⟨psi (Hloc_le_M hS hD hF) ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, Or.inl ?_⟩
    rw [hm, map_mul, pi_eq_one_iff.2 hwY, one_mul]
    exact hψ.symm
  · refine ⟨psi (Hloc_le_M hS hD hF) ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, Or.inr ?_⟩
    have h1 : pi Y ⟨z, hzM⟩ * pi Y ⟨w, hwM⟩ = 1 := by
      rw [← map_mul]
      exact pi_eq_one_iff.2 hwY
    have h2 : pi Y ⟨w, hwM⟩ = pi Y ⟨z, hzM⟩ :=
      (inv_eq_of_mul_eq_one_right h1).symm.trans
        (inv_eq_of_mul_eq_one_right (pi_z_mul_self hS hzM))
    rw [hm, map_mul, h2, ← hψ]
    exact (psi_comm_pi hS (Hloc_le_M hS hD hF) hzM ⟨h, hh⟩).symm

theorem exists_conj_ne (hS : Setting L z) (hD : LocalData L U T0) (hY : YStruct L U z Y)
    (hF : FusionData L U z Y) (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u)
    (hzM : z ∈ Mn Y) {s : G} (hs : s ∈ Hloc L U) (hsU : s ∉ U)
    (hinv : ∃ l ∈ L, l * s * l⁻¹ ∈ U) :
    ∃ x : Sec Y, x * pi Y ⟨z, hzM⟩ * x⁻¹ ≠ pi Y ⟨z, hzM⟩ ∧
      (x * pi Y ⟨z, hzM⟩ * x⁻¹) * pi Y ⟨z, hzM⟩ =
        pi Y ⟨z, hzM⟩ * (x * pi Y ⟨z, hzM⟩ * x⁻¹) := by
  obtain ⟨l, hlL, hlu⟩ := hinv
  obtain ⟨n, -, hnz⟩ := htrans _ hlu
  have hzl : z * l⁻¹ = l⁻¹ * z := hS.z_comm _ (inv_mem hlL)
  have hg : (l⁻¹ * n) * z * (l⁻¹ * n)⁻¹ = z * s := by
    calc (l⁻¹ * n) * z * (l⁻¹ * n)⁻¹ = l⁻¹ * (n * z * n⁻¹) * l := by group
      _ = l⁻¹ * (z * (l * s * l⁻¹)) * l := by rw [hnz]
      _ = (l⁻¹ * z) * (l * s * l⁻¹) * l := by group
      _ = (z * l⁻¹) * (l * s * l⁻¹) * l := by rw [hzl]
      _ = z * s := by group
  have hsM : s ∈ Mn Y := Hloc_le_M hS hD hF hs
  have hzsM : z * s ∈ Mn Y := mul_mem hzM hsM
  obtain ⟨m, hmM, hmz⟩ := hF.fuse (z * s) hzsM ⟨l⁻¹ * n, hg⟩
  have hx : pi Y ⟨m, hmM⟩ * pi Y ⟨z, hzM⟩ * (pi Y ⟨m, hmM⟩)⁻¹ =
      pi Y ⟨z, hzM⟩ * pi Y ⟨s, hsM⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hmz
  refine ⟨pi Y ⟨m, hmM⟩, ?_, ?_⟩
  · rw [hx]
    intro h1
    apply hsU
    have h2 : pi Y ⟨s, hsM⟩ = 1 := by
      have := congrArg (fun a => (pi Y ⟨z, hzM⟩)⁻¹ * a) h1
      simpa using this
    exact (mem_Y_iff_of_mem_Hloc hD hY hs).1 (pi_eq_one_iff.1 h2)
  · rw [hx]
    have hc : pi Y ⟨s, hsM⟩ * pi Y ⟨z, hzM⟩ = pi Y ⟨z, hzM⟩ * pi Y ⟨s, hsM⟩ :=
      psi_comm_pi hS (Hloc_le_M hS hD hF) hzM ⟨s, hs⟩
    calc pi Y ⟨z, hzM⟩ * pi Y ⟨s, hsM⟩ * pi Y ⟨z, hzM⟩
        = pi Y ⟨z, hzM⟩ * (pi Y ⟨s, hsM⟩ * pi Y ⟨z, hzM⟩) := by rw [mul_assoc]
      _ = pi Y ⟨z, hzM⟩ * (pi Y ⟨z, hzM⟩ * pi Y ⟨s, hsM⟩) := by rw [hc]

end CFSG.EvenSporadicStandard.J4Std.EgawaApply
