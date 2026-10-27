module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PUniqDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Pk

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec5z_twoCoreIn_map (φ : G ≃* G) (H H' : Subgroup G)
    (h : H.map φ.toMonoidHom = H') :
    twoCoreIn H' = (twoCoreIn H).map φ.toMonoidHom := by
  have key := CFSG.pCore_map_iso 2 ((MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr h))
  unfold twoCoreIn CFSG.inSubgroup
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {K₁ K₂ : Subgroup G}

theorem sec5z_conj_pocket (hy : Sec5B59Hyp) (h : Sec5Ctx G t L S z) {s : G} (hs : s ∈ S)
    {K : Subgroup G} (hK : Sl23PocketIn L z K) : Sl23PocketIn L z (CFSG.conjugate K s) := by
  have hL : CFSG.conjugate L s = L :=
    conjugate_eq_self_of_lemma36 hy.h36 h.toSec5Setting.toSec3SettingLB s (h.sylow.1 hs)
  have hz : s⁻¹ * z * s = z := by
    calc s⁻¹ * z * s = s⁻¹ * (z * s) := by group
      _ = s⁻¹ * (s * z) := by rw [h.central s hs]
      _ = z := by group
  have hc := hK.conjugate s
  rwa [hL, hz] at hc

theorem sec5z_conj_Q_le (hy : Sec5B59Hyp) (hU : Asc82FactPocketsUniq6) (h : Sec5Ctx G t L S z)
    (hk : Sec510Pk G t L S z K₁ K₂) {s : G} (hs : s ∈ S) {x : G}
    (hx : x ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂) : s⁻¹ * x * s ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
  obtain ⟨hF, -⟩ := hU G L z h.toSec5Setting.isOm6Z2 h.pocket K₁ K₂ hk.pocket₁ hk.pocket₂ hk.ne
    hk.q.iso₁ hk.q.iso₂ hk.q.comm hk.q.card hk.q.center
  have hmap : ∀ K : Subgroup G, Sl23PocketIn L z K →
      (twoCoreIn K).map (MulAut.conj s⁻¹).toMonoidHom ≤ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
    intro K hK
    have hKs : Sl23PocketIn L z (CFSG.conjugate K s) := sec5z_conj_pocket hy h hs hK
    have e : twoCoreIn (CFSG.conjugate K s) =
        (twoCoreIn K).map (MulAut.conj s⁻¹).toMonoidHom :=
      sec5z_twoCoreIn_map (MulAut.conj s⁻¹) K _ rfl
    rw [← e]
    rcases hF _ hKs with h1 | h1
    · rw [h1]
      exact le_sup_left
    · rw [h1]
      exact le_sup_right
  have hsup : (twoCoreIn K₁ ⊔ twoCoreIn K₂).map (MulAut.conj s⁻¹).toMonoidHom ≤
      twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
    rw [Subgroup.map_sup]
    exact sup_le (hmap K₁ hk.pocket₁) (hmap K₂ hk.pocket₂)
  exact hsup (Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩)

theorem sec5z_S_le_normalizer_Q (hy : Sec5B59Hyp) (hU : Asc82FactPocketsUniq6)
    (h : Sec5Ctx G t L S z) (hk : Sec510Pk G t L S z K₁ K₂) :
    S ≤ normalizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hc := sec5z_conj_Q_le hy hU h hk (inv_mem hs) hx
    have e : s⁻¹⁻¹ * x * s⁻¹ = s * x * s⁻¹ := by rw [inv_inv]
    rwa [e] at hc
  · intro hx
    have hc := sec5z_conj_Q_le hy hU h hk hs hx
    have e : s⁻¹ * (s * x * s⁻¹) * s = x := by group
    rwa [e] at hc

end CFSG.OddStandard.SmallF3.Omega
