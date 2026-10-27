module

public import CFSG.GF2Type.Aschbacher1976Full.HSDefs
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnside
public import CFSG.GF2Type.Aschbacher1976Full.WidthTI

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.BL

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup
open CFSG.GF2Type.Aschbacher1976Common (conjugatesIn card_conjugate_eq commute_of_mem_iSup_conjugate)

variable {G : Type} [Group G] [Finite G]

theorem conjugate_one {H : Subgroup G} : conjugate H 1 = H := by
  ext x
  simp [Width.mem_conjugate_iff]

theorem conjugate_mono {A B : Subgroup G} (h : A ≤ B) (g : G) : conjugate A g ≤ conjugate B g :=
  Subgroup.map_mono h

theorem conjugate_le_of_mem {A T : Subgroup G} (h : A ≤ T) {t : G} (ht : t ∈ T) :
    conjugate A t ≤ T := by
  intro x hx
  have h1 : t * x * t⁻¹ ∈ T := h (Width.mem_conjugate_iff.mp hx)
  have h2 := T.mul_mem (T.mul_mem (T.inv_mem ht) h1) ht
  have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
  rwa [e] at h2

theorem mem_normalizer_of_conjugate_eq {A : Subgroup G} {g : G} (h : conjugate A g = A) :
    g ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← Width.mem_conjugate_iff, h]

theorem conjugate_eq_of_mem_normalizer {A : Subgroup G} {g : G}
    (h : g ∈ normalizer (A : Set G)) : conjugate A g = A := by
  ext x
  rw [Width.mem_conjugate_iff]
  exact ((Subgroup.mem_normalizer_iff.mp h) x).symm

theorem exists_inv_conj {z u : G} (h : IsConj z u) : ∃ g : G, u = g⁻¹ * z * g := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact ⟨c⁻¹, by rw [← hc]; simp⟩

theorem isConj_conj_iff {z x : G} (n : G) : IsConj z (n * x * n⁻¹) ↔ IsConj z x :=
  ⟨fun h => h.trans (isConj_iff.mpr ⟨n⁻¹, by group⟩),
    fun h => h.trans (isConj_iff.mpr ⟨n, rfl⟩)⟩

theorem mul_self_of_isConj {z v : G} (hz : orderOf z = 2) (h : IsConj z v) : v * v = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  have hzz : z * z = 1 := by rw [← sq]; exact Width.z_sq hz
  calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [hzz]; group

theorem ne_one_of_isConj {z v : G} (hz : orderOf z = 2) (h : IsConj z v) : v ≠ 1 := by
  rintro rfl
  rw [isConj_one_right.mp h.symm, orderOf_one] at hz
  omega

abbrev WZ (Z T : Subgroup G) : Subgroup G := ⨆ B ∈ conjugatesIn Z T, B

abbrev VS (T : Subgroup G) (z : G) : Set G := {v : G | IsConj z v ∧ ZF v ≤ T}

theorem le_WZ {Z T B : Subgroup G} (hB : B ∈ conjugatesIn Z T) : B ≤ WZ Z T :=
  le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ conjugatesIn Z T) => B) B hB

theorem WZ_le {Z T : Subgroup G} : WZ Z T ≤ T :=
  iSup₂_le fun _ ⟨_, _, hBT⟩ => hBT

structure Ctx (z : G) (w : ℕ) (Z A : Subgroup G) (T : Sylow 2 G) : Prop where
  hD : Width.Z4Data z w Z A
  hz : orderOf z = 2
  hF2 : IsPGroup 2 (Fz z)
  hTH : (T : Subgroup G) ≤ Hz z

namespace Ctx

variable {z : G} {w : ℕ} {Z A : Subgroup G} {T : Sylow 2 G} (c : Ctx z w Z A T)
include c

theorem Z_le_F : Z ≤ Fz z := c.hD.sup_eq ▸ le_sup_left

theorem F_le_T : Fz z ≤ (T : Subgroup G) := by
  have hnorm : (T : Subgroup G) ≤ normalizer (Fz z : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · exact fun hf => Width.Fz_conj_mem (c.hTH ht) hf
    · intro hf
      have h := Width.Fz_conj_mem ((Hz z).inv_mem (c.hTH ht)) hf
      have e : t⁻¹ * (t * f * t⁻¹) * t⁻¹⁻¹ = f := by group
      rwa [e] at h
  have hsup : IsPGroup 2 ↥((T : Subgroup G) ⊔ Fz z) :=
    T.isPGroup'.to_sup_of_normal_right' c.hF2 hnorm
  exact le_sup_right.trans (T.is_maximal' hsup le_sup_left).le

theorem Z_le_T : Z ≤ (T : Subgroup G) := c.Z_le_F.trans c.F_le_T

theorem ZF_self : ZF z = Z :=
  Subgroup.ext fun _ => Width.mem_centerAt_iff c.hD c.hz c.hF2

theorem WT_eq : WT (T : Subgroup G) z = WZ Z (T : Subgroup G) := by
  unfold WT
  rw [c.ZF_self]

theorem ZF_conj_eq (g : G) : ZF (g⁻¹ * z * g) = conjugate Z g := by
  show centerAt (g⁻¹ * z * g) = conjugate Z g
  rw [centerAt_conj z g]
  exact congrArg (fun K => conjugate K g) c.ZF_self

theorem TI : ∀ g : G, conjugate Z g = Z ∨ Z ⊓ conjugate Z g = ⊥ := by
  intro g
  rcases Width.conj_pair_eq_or_disjoint c.hD c.hz c.hF2 1 g with h | h
  · left
    rw [conjugate_one] at h
    exact h.symm
  · right
    rw [conjugate_one] at h
    exact h

theorem Z_mem_conjugatesIn : Z ∈ conjugatesIn Z (T : Subgroup G) :=
  ⟨1, conjugate_one.symm, c.Z_le_T⟩

theorem z_mem_WZ : z ∈ WZ Z (T : Subgroup G) := le_WZ c.Z_mem_conjugatesIn c.hD.mem_z

theorem WZ_comm : ∀ x ∈ WZ Z (T : Subgroup G), ∀ y ∈ WZ Z (T : Subgroup G), x * y = y * x :=
  commute_of_mem_iSup_conjugate c.hD.cyc (c.hF2.to_le c.Z_le_F) c.hD.card_Z.symm.le c.TI
    T.isPGroup'

theorem conjugate_WZ_le {g : G} (hg : conjugate (WZ Z (T : Subgroup G)) g ≤ T) :
    conjugate (WZ Z (T : Subgroup G)) g ≤ WZ Z (T : Subgroup G) := by
  unfold conjugate
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun B hB => ?_
  obtain ⟨g', rfl, hg'T⟩ := hB
  intro x hx
  rw [Subgroup.mem_comap]
  have hle : conjugate Z (g' * g) ≤ T := by
    intro y hy
    refine hg ?_
    rw [Width.mem_conjugate_iff]
    refine le_WZ ⟨g', rfl, hg'T⟩ ?_
    rw [Width.mem_conjugate_iff]
    rw [show g' * (g * y * g⁻¹) * g'⁻¹ = g' * g * y * (g' * g)⁻¹ by group]
    exact Width.mem_conjugate_iff.mp hy
  refine le_WZ ⟨g' * g, rfl, hle⟩ ?_
  rw [Width.mem_conjugate_iff]
  show g' * g * (g⁻¹ * x * g⁻¹⁻¹) * (g' * g)⁻¹ ∈ Z
  rw [show g' * g * (g⁻¹ * x * g⁻¹⁻¹) * (g' * g)⁻¹ = g' * x * g'⁻¹ by group]
  exact Width.mem_conjugate_iff.mp hx

theorem conjugate_WZ_eq {g : G} (hg : conjugate (WZ Z (T : Subgroup G)) g ≤ T) :
    conjugate (WZ Z (T : Subgroup G)) g = WZ Z (T : Subgroup G) :=
  Subgroup.eq_of_le_of_card_ge (c.conjugate_WZ_le hg) (card_conjugate_eq _ _).symm.le

theorem T_le_normalizer : (T : Subgroup G) ≤ normalizer (WZ Z (T : Subgroup G) : Set G) :=
  fun _ ht => mem_normalizer_of_conjugate_eq (c.conjugate_WZ_eq (conjugate_le_of_mem WZ_le ht))

theorem exists_normalizer_conj {v : G} (hv : v ∈ WZ Z (T : Subgroup G)) (hc : IsConj z v) :
    ∃ n ∈ normalizer (WZ Z (T : Subgroup G) : Set G), n * z * n⁻¹ = v := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  obtain ⟨n, hn, hnv⟩ := burnside_fusion T (WZ Z (T : Subgroup G)) WZ_le c.WZ_comm
    (fun _ hg' => c.conjugate_WZ_eq hg') c.z_mem_WZ (g := g) (by rw [hg]; exact hv)
  exact ⟨n, hn, hnv.trans hg⟩

theorem mem_VS_iff {v : G} :
    v ∈ VS (T : Subgroup G) z ↔ IsConj z v ∧ v ∈ WZ Z (T : Subgroup G) := by
  constructor
  · rintro ⟨hc, hle⟩
    refine ⟨hc, ?_⟩
    obtain ⟨g, rfl⟩ := exists_inv_conj hc
    rw [c.ZF_conj_eq] at hle
    refine le_WZ ⟨g, rfl, hle⟩ ?_
    rw [Width.mem_conjugate_iff, show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    exact c.hD.mem_z
  · rintro ⟨hc, hW⟩
    refine ⟨hc, ?_⟩
    obtain ⟨n, hn, hnv⟩ := c.exists_normalizer_conj hW hc
    have e : v = (n⁻¹)⁻¹ * z * n⁻¹ := by rw [← hnv, inv_inv]
    rw [e, c.ZF_conj_eq]
    calc conjugate Z n⁻¹ ≤ conjugate (WZ Z (T : Subgroup G)) n⁻¹ :=
          conjugate_mono (le_WZ c.Z_mem_conjugatesIn) _
      _ = WZ Z (T : Subgroup G) := conjugate_eq_of_mem_normalizer ((normalizer _).inv_mem hn)
      _ ≤ T := WZ_le

theorem ZF_le_WZ {v : G} (hv : v ∈ VS (T : Subgroup G) z) : ZF v ≤ WZ Z (T : Subgroup G) := by
  obtain ⟨g, rfl⟩ := exists_inv_conj hv.1
  have hle := hv.2
  rw [c.ZF_conj_eq] at hle ⊢
  exact le_WZ ⟨g, rfl, hle⟩

theorem mem_WZ_of_mem_VS {v : G} (hv : v ∈ VS (T : Subgroup G) z) : v ∈ WZ Z (T : Subgroup G) :=
  ((mem_VS_iff c).mp hv).2

theorem VS_subset_F (hti : HSTI z) {v : G} (hv : v ∈ VS (T : Subgroup G) z) : v ∈ Fz z := by
  by_cases hvz : v = z
  · rw [hvz]
    exact c.Z_le_F c.hD.mem_z
  · exact (hti.2 v ⟨hv.1, hvz, hv.2.trans c.hTH⟩).1

end Ctx

end CFSG.GF2Type.Aschbacher1976Full.HS.BL
