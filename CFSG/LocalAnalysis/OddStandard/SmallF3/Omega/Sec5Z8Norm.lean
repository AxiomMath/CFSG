module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Pk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PUniqDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec5z8_twoCoreIn_map (φ : G ≃* G) (H H' : Subgroup G)
    (h : H.map φ.toMonoidHom = H') :
    twoCoreIn H' = (twoCoreIn H).map φ.toMonoidHom := by
  have key := CFSG.pCore_map_iso 2 ((MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr h))
  unfold twoCoreIn CFSG.inSubgroup
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {K₁ K₂ : Subgroup G}

theorem sec5z8_conj_pocket (hy : Sec5B59Hyp) (h : Sec5Ctx G t L S z) {g : G}
    (hgt : g ∈ centralizer ({t} : Set G)) (hgz : g * z = z * g) {K : Subgroup G}
    (hK : Sl23PocketIn L z K) : Sl23PocketIn L z (CFSG.conjugate K g) := by
  have hL : CFSG.conjugate L g = L :=
    conjugate_eq_self_of_lemma36 hy.h36 h.toSec5Setting.toSec3SettingLB g hgt
  have hz : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group
  have hc := hK.conjugate g
  rwa [hL, hz] at hc

theorem sec5z8_conj_Q_le (hy : Sec5B59Hyp) (hU : Asc82FactPocketsUniq6) (h : Sec5Ctx G t L S z)
    (hk : Sec510Pk G t L S z K₁ K₂) {g : G} (hgt : g ∈ centralizer ({t} : Set G))
    (hgz : g * z = z * g) {x : G} (hx : x ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂) :
    g⁻¹ * x * g ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
  obtain ⟨hF, -⟩ := hU G L z h.toSec5Setting.isOm6Z2 h.pocket K₁ K₂ hk.pocket₁ hk.pocket₂ hk.ne
    hk.q.iso₁ hk.q.iso₂ hk.q.comm hk.q.card hk.q.center
  have hmap : ∀ K : Subgroup G, Sl23PocketIn L z K →
      (twoCoreIn K).map (MulAut.conj g⁻¹).toMonoidHom ≤ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
    intro K hK
    have hKg : Sl23PocketIn L z (CFSG.conjugate K g) := sec5z8_conj_pocket hy h hgt hgz hK
    have e : twoCoreIn (CFSG.conjugate K g) =
        (twoCoreIn K).map (MulAut.conj g⁻¹).toMonoidHom :=
      sec5z8_twoCoreIn_map (MulAut.conj g⁻¹) K _ rfl
    rw [← e]
    rcases hF _ hKg with h1 | h1
    · rw [h1]
      exact le_sup_left
    · rw [h1]
      exact le_sup_right
  have hsup : (twoCoreIn K₁ ⊔ twoCoreIn K₂).map (MulAut.conj g⁻¹).toMonoidHom ≤
      twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
    rw [Subgroup.map_sup]
    exact sup_le (hmap K₁ hk.pocket₁) (hmap K₂ hk.pocket₂)
  exact hsup (Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩)

theorem sec5z8_conj_mem_R (hy : Sec5B59Hyp) (hU : Asc82FactPocketsUniq6) (h : Sec5Ctx G t L S z)
    (hk : Sec510Pk G t L S z K₁ K₂) {g : G} (hgt : g ∈ centralizer ({t} : Set G))
    (hgz : g * z = z * g) {x : G} (hx : x ∈ sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))
    (hxg : g * x * g⁻¹ ∈ S) : g * x * g⁻¹ ∈ sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) := by
  refine ⟨hxg, ?_⟩
  show g * x * g⁻¹ ∈ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : g⁻¹ * q * g ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂ :=
    sec5z8_conj_Q_le hy hU h hk hgt hgz hq
  have e := Subgroup.mem_centralizer_iff.mp hx.2 (g⁻¹ * q * g) hq'
  calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [e]
    _ = (g * x * g⁻¹) * q := by group

end CFSG.OddStandard.SmallF3.Omega
