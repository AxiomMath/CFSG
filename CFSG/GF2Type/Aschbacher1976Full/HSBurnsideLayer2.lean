module

public import CFSG.GF2Type.Aschbacher1976Full.HSBurnsideLayer
public import CFSG.GF2Type.Aschbacher1976Full.HSVDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.BL

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {z : G} {w : ℕ} {Z A : Subgroup G} {T : Sylow 2 G} (c : Ctx z w Z A T)
include c

theorem isConj_mul_z (hti : HSTI z) {u : G} (hu : IsConj z u) (hne : u ≠ z)
    (hcomm : u * z = z * u) : IsConj z (u * z) := by
  have hD := c.hD
  have hz := c.hz
  have hu2 : u * u = 1 := mul_self_of_isConj hz hu
  have hu1 : u ≠ 1 := ne_one_of_isConj hz hu
  obtain ⟨k, hkZ, -, hgen, hk2⟩ := Width.exists_gen_Z hD hz
  have hzk : z * k = k * z := Width.comm_Z hD hD.mem_z hkZ
  by_cases hk : u * k = k * u
  ·
    have hcentZ : u ∈ centralizer (Z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨i, rfl⟩ := hgen x hx
      exact (Commute.zpow_right (show Commute u k from hk) i).eq.symm
    obtain ⟨g, hg⟩ := exists_inv_conj hu
    have hH := Width.conjugate_le_H_of_comm hD hz (hg ▸ hcentZ)
    have hDinv : u ∈ Dinv z := by
      refine ⟨hu, hne, ?_⟩
      rw [hg, c.ZF_conj_eq]
      intro y hy
      have h1 := hH _ (Width.mem_conjugate_iff.mp hy)
      rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
    have huF : u ∈ Fz z := (hti.2 u hDinv).1
    by_cases hall : ∀ b ∈ Fz z, u * b = b * u
    · exfalso
      have hA : ∀ b ∈ A, u * b = b * u := fun b hb =>
        hall b (hD.sup_eq ▸ Subgroup.mem_sup_right hb)
      exact hne (Width.involution_eq hD hz (Width.mem_Z_of_comm hD hz huF hA)
        (by rw [sq]; exact hu2) hu1)
    · push_neg at hall
      obtain ⟨f, hfF, hf⟩ := hall
      rcases Width.comm_F hD hz hfF huF with h | h
      · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h).symm hf
      · have hfu : f * u * f⁻¹ = z * u := by
          rw [commutatorElement_def] at h
          calc f * u * f⁻¹ = (f * u * f⁻¹ * u⁻¹) * u := by group
            _ = z * u := by rw [h]
        rw [hcomm]
        exact hu.trans (isConj_iff.mpr ⟨f, hfu⟩)
  ·
    have huH : u ∈ Hz z := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    obtain ⟨y, hydef⟩ : ∃ y : G, y = u * k * u⁻¹ := ⟨_, rfl⟩
    have hy : y ∈ Z := by
      rw [hydef]
      exact Width.Z_conj_mem hD hz huH hkZ
    have hkk : k * k = z := by rw [← sq]; exact hk2
    have hyy : y * y = z := by
      calc y * y = u * (k * k) * u⁻¹ := by rw [hydef]; group
        _ = u * z * u⁻¹ := by rw [hkk]
        _ = z := by rw [hcomm]; group
    have hckz : k⁻¹ * y = y * k⁻¹ := Width.comm_Z hD (Z.inv_mem hkZ) hy
    have ht : y * k⁻¹ ∈ Z := Z.mul_mem hy (Z.inv_mem hkZ)
    have ht2 : (y * k⁻¹) ^ 2 = 1 := by
      calc (y * k⁻¹) ^ 2 = (y * k⁻¹) * (y * k⁻¹) := sq _
        _ = y * (k⁻¹ * y) * k⁻¹ := by group
        _ = y * (y * k⁻¹) * k⁻¹ := by rw [hckz]
        _ = (y * y) * (k⁻¹ * k⁻¹) := by group
        _ = z * z⁻¹ := by rw [hyy, ← mul_inv_rev, hkk]
        _ = 1 := mul_inv_cancel z
    by_cases ht1 : y * k⁻¹ = 1
    · exfalso
      apply hk
      have hyk : y = k := mul_inv_eq_one.mp ht1
      rw [hydef] at hyk
      calc u * k = (u * k * u⁻¹) * u := by group
        _ = k * u := by rw [hyk]
    · have htz : y * k⁻¹ = z := Width.involution_eq hD hz ht ht2 ht1
      have hy' : y = z * k := by rw [← htz]; group
      have hkzk : k⁻¹ * z * k = z := by
        calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
          _ = k⁻¹ * (k * z) := by rw [hzk]
          _ = z := by group
      have hconj : k⁻¹ * u * k⁻¹⁻¹ = u * z := by
        calc k⁻¹ * u * k⁻¹⁻¹ = k⁻¹ * ((u * k * u⁻¹) * u) := by group
          _ = k⁻¹ * (z * k * u) := by rw [← hydef, hy']
          _ = (k⁻¹ * z * k) * u := by group
          _ = z * u := by rw [hkzk]
          _ = u * z := hcomm.symm
      exact hu.trans (isConj_iff.mpr ⟨k⁻¹, hconj⟩)

theorem mul_mem_VS (hti : HSTI z) {v v' : G} (hv : v ∈ VS (T : Subgroup G) z)
    (hv' : v' ∈ VS (T : Subgroup G) z) (hne : v ≠ v') : v * v' ∈ VS (T : Subgroup G) z := by
  obtain ⟨hvc, hvW⟩ := (c.mem_VS_iff).mp hv
  obtain ⟨hvc', hvW'⟩ := (c.mem_VS_iff).mp hv'
  obtain ⟨n, hn, hnv⟩ := c.exists_normalizer_conj hvW hvc
  have hn' : n⁻¹ ∈ normalizer (WZ Z (T : Subgroup G) : Set G) := (normalizer _).inv_mem hn
  have huW : n⁻¹ * v' * n ∈ WZ Z (T : Subgroup G) := by
    have h := (Subgroup.mem_normalizer_iff.mp hn' v').mp hvW'
    rwa [inv_inv] at h
  have huc : IsConj z (n⁻¹ * v' * n) := by
    have h := (isConj_conj_iff (z := z) (x := v') n⁻¹).mpr hvc'
    rwa [inv_inv] at h
  have hune : n⁻¹ * v' * n ≠ z := by
    intro h
    apply hne
    rw [← hnv]
    calc n * z * n⁻¹ = n * (n⁻¹ * v' * n) * n⁻¹ := by rw [h]
      _ = v' := by group
  have hcomm : (n⁻¹ * v' * n) * z = z * (n⁻¹ * v' * n) := c.WZ_comm _ huW _ c.z_mem_WZ
  have hcj : IsConj z (z * (n⁻¹ * v' * n)) := by
    rw [← hcomm]
    exact c.isConj_mul_z hti huc hune hcomm
  have hprod : v * v' = n * (z * (n⁻¹ * v' * n)) * n⁻¹ := by
    rw [← hnv]
    group
  refine (c.mem_VS_iff).mpr ⟨?_, (WZ Z (T : Subgroup G)).mul_mem hvW hvW'⟩
  rw [hprod]
  exact (isConj_conj_iff n).mpr hcj

theorem mul_cases (hti : HSTI z) {x y : G} (hx : x = 1 ∨ x ∈ VS (T : Subgroup G) z)
    (hy : y = 1 ∨ y ∈ VS (T : Subgroup G) z) : x * y = 1 ∨ x * y ∈ VS (T : Subgroup G) z := by
  rcases hx with rfl | hx
  · rw [one_mul]
    exact hy
  rcases hy with rfl | hy
  · rw [mul_one]
    exact Or.inr hx
  by_cases hxy : x = y
  · left
    rw [hxy]
    exact mul_self_of_isConj c.hz hy.1
  · exact Or.inr (c.mul_mem_VS hti hx hy hxy)

theorem mem_ET_iff (hti : HSTI z) {x : G} :
    x ∈ ET (T : Subgroup G) z ↔ x = 1 ∨ x ∈ VS (T : Subgroup G) z := by
  constructor
  · intro hx
    refine Subgroup.closure_induction
      (p := fun x _ => x = 1 ∨ x ∈ VS (T : Subgroup G) z) ?_ ?_ ?_ ?_ hx
    · exact fun x hx => Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      exact c.mul_cases hti hx hy
    · intro x _ hx
      rcases hx with rfl | hx
      · exact Or.inl inv_one
      · refine Or.inr ?_
        have e : x⁻¹ = x := inv_eq_of_mul_eq_one_right (mul_self_of_isConj c.hz hx.1)
        rw [e]
        exact hx
  · rintro (rfl | hx)
    · exact one_mem _
    · exact Subgroup.subset_closure hx

theorem mem_WZ_of_mem_ET (hti : HSTI z) {x : G} (hx : x ∈ ET (T : Subgroup G) z) :
    x ∈ WZ Z (T : Subgroup G) := by
  rcases (c.mem_ET_iff hti).mp hx with rfl | hx
  · exact one_mem _
  · exact c.mem_WZ_of_mem_VS hx

theorem hsV (hti : HSTI z) (hcard : Nat.card (ET (T : Subgroup G) z) = 8)
    (hcardW : Nat.card (WT (T : Subgroup G) z) = 64) :
    HSV z (T : Subgroup G) (ET (T : Subgroup G) z) where
  isElem := by
    refine And.intro ⟨⟨fun a b => Subtype.ext ?_⟩⟩ ?_
    · exact c.WZ_comm a.1 (c.mem_WZ_of_mem_ET hti a.2) b.1 (c.mem_WZ_of_mem_ET hti b.2)
    · intro x hx
      rcases (c.mem_ET_iff hti).mp hx with rfl | hx
      · exact one_pow 2
      · rw [sq]
        exact mul_self_of_isConj c.hz hx.1
  card_eq := hcard
  le_F := fun x hx => by
    rcases (c.mem_ET_iff hti).mp hx with rfl | hx
    · exact (Fz z).one_mem
    · exact c.VS_subset_F hti hx
  z_mem := Subgroup.subset_closure
    ⟨IsConj.refl z, by rw [c.ZF_self]; exact c.Z_le_T⟩
  sylow := ⟨T.isPGroup', fun S hS hTS => T.is_maximal' hS hTS⟩
  le_H := c.hTH
  F_le_T := c.F_le_T
  normal_in_T := by
    intro t ht v hv
    rcases (c.mem_ET_iff hti).mp hv with rfl | hv
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · obtain ⟨hvc, hvW⟩ := (c.mem_VS_iff).mp hv
      refine (c.mem_ET_iff hti).mpr (Or.inr ((c.mem_VS_iff).mpr ⟨(isConj_conj_iff t).mpr hvc, ?_⟩))
      exact (Subgroup.mem_normalizer_iff.mp (c.T_le_normalizer ht) v).mp hvW
  isConj := fun v hv hv1 => (((c.mem_ET_iff hti).mp hv).resolve_left hv1).1
  ZF_le := fun v hv hv1 => (((c.mem_ET_iff hti).mp hv).resolve_left hv1).2
  ZF_comm := by
    intro v hv hv1 v' hv' hv1' a ha b hb
    have h1 := ((c.mem_ET_iff hti).mp hv).resolve_left hv1
    have h2 := ((c.mem_ET_iff hti).mp hv').resolve_left hv1'
    exact c.WZ_comm a (c.ZF_le_WZ h1 ha) b (c.ZF_le_WZ h2 hb)
  trans := by
    intro v hv hv1
    have hvVS := ((c.mem_ET_iff hti).mp hv).resolve_left hv1
    obtain ⟨hvc, hvW⟩ := (c.mem_VS_iff).mp hvVS
    obtain ⟨n, hn, hnv⟩ := c.exists_normalizer_conj hvW hvc
    refine ⟨n, ?_, hnv⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [c.mem_ET_iff hti, c.mem_ET_iff hti, c.mem_VS_iff, c.mem_VS_iff]
    have hW : x ∈ WZ Z (T : Subgroup G) ↔ n * x * n⁻¹ ∈ WZ Z (T : Subgroup G) :=
      Subgroup.mem_normalizer_iff.mp hn x
    have h1 : x = 1 ↔ n * x * n⁻¹ = 1 := by
      constructor
      · rintro rfl
        rw [mul_one, mul_inv_cancel]
      · intro h
        calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
          _ = 1 := by rw [h]; group
    rw [h1, hW, isConj_conj_iff n]
  W_comm := fun a ha b hb => by
    rw [c.WT_eq] at ha hb
    exact c.WZ_comm a ha b hb
  card_W := hcardW
  W_le_T := by
    rw [c.WT_eq]
    exact WZ_le
  ZF_le_W := by
    intro v hv hv1
    rw [c.WT_eq]
    exact c.ZF_le_WZ (((c.mem_ET_iff hti).mp hv).resolve_left hv1)

end Ctx

end CFSG.GF2Type.Aschbacher1976Full.HS.BL

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

theorem hsV_of_wide {G : Type} [Group G] [Finite G] {z : G} (hset : HSSetting G z) (hti : HSTI z)
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ Hz z)
    (hcard : Nat.card (ET (T : Subgroup G) z) = 8) (hcardW : Nat.card (WT (T : Subgroup G) z) = 64) :
    HSV z (T : Subgroup G) (ET (T : Subgroup G) z) := by
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  exact (BL.Ctx.mk hD hz hsymp.1 hTH).hsV hti hcard hcardW

end CFSG.GF2Type.Aschbacher1976Full.HS
