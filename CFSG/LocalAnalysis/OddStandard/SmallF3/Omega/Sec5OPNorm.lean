module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Pk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PUniqDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {K₁ K₂ : Subgroup G}

private theorem sec5op_twoCoreIn_map (φ : G ≃* G) (H H' : Subgroup G)
    (h : H.map φ.toMonoidHom = H') :
    twoCoreIn H' = (twoCoreIn H).map φ.toMonoidHom := by
  have key := CFSG.pCore_map_iso 2 ((MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr h))
  unfold twoCoreIn CFSG.inSubgroup
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem sec5op_conj_pocket (hy : Sec5B59Hyp) (h : Sec5Ctx G t L S z) {y : G}
    (hyt : y ∈ centralizer ({t} : Set G)) (hyz : y ∈ centralizer ({z} : Set G))
    {K : Subgroup G} (hK : Sl23PocketIn L z K) : Sl23PocketIn L z (CFSG.conjugate K y) := by
  have hL : CFSG.conjugate L y = L :=
    conjugate_eq_self_of_lemma36 hy.h36 h.toSec5Setting.toSec3SettingLB y hyt
  have hz : y⁻¹ * z * y = z := by
    calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
      _ = y⁻¹ * (y * z) := by rw [(Subgroup.mem_centralizer_singleton_iff.mp hyz).symm]
      _ = z := by group
  have hc := hK.conjugate y
  rwa [hL, hz] at hc

theorem sec5op_conj_Q_le (hy : Sec5B59Hyp) (hU : Asc82FactPocketsUniq6) (h : Sec5Ctx G t L S z)
    (hk : Sec510Pk G t L S z K₁ K₂) {y : G} (hyt : y ∈ centralizer ({t} : Set G))
    (hyz : y ∈ centralizer ({z} : Set G)) {x : G} (hx : x ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂) :
    y⁻¹ * x * y ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
  obtain ⟨hF, -⟩ := hU G L z h.toSec5Setting.isOm6Z2 h.pocket K₁ K₂ hk.pocket₁ hk.pocket₂ hk.ne
    hk.q.iso₁ hk.q.iso₂ hk.q.comm hk.q.card hk.q.center
  have hmap : ∀ K : Subgroup G, Sl23PocketIn L z K →
      (twoCoreIn K).map (MulAut.conj y⁻¹).toMonoidHom ≤ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
    intro K hK
    have hKy : Sl23PocketIn L z (CFSG.conjugate K y) := sec5op_conj_pocket hy h hyt hyz hK
    have e : twoCoreIn (CFSG.conjugate K y) =
        (twoCoreIn K).map (MulAut.conj y⁻¹).toMonoidHom :=
      sec5op_twoCoreIn_map (MulAut.conj y⁻¹) K _ rfl
    rw [← e]
    rcases hF _ hKy with h1 | h1
    · rw [h1]
      exact le_sup_left
    · rw [h1]
      exact le_sup_right
  have hsup : (twoCoreIn K₁ ⊔ twoCoreIn K₂).map (MulAut.conj y⁻¹).toMonoidHom ≤
      twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
    rw [Subgroup.map_sup]
    exact sup_le (hmap K₁ hk.pocket₁) (hmap K₂ hk.pocket₂)
  exact hsup (Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩)

end CFSG.OddStandard.SmallF3.Omega
