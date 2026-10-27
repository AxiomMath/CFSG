module

public import CFSG.CharacterTheory.Semidihedral.DihedralNormalIndex
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Semidihedral.CharacteristicSL2Layer

universe u v w

variable {H : Type u} {G : Type v} [Group H] [Group G]

theorem characteristic_comap_equiv (e : H ≃* G) (L : Subgroup G)
    (hL : L.Characteristic) : (L.comap e.toMonoidHom).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro alpha x hx
  let beta : G ≃* G := (e.symm.trans alpha).trans e
  have hfixed := Subgroup.characteristic_iff_le_comap.mp hL beta hx
  change beta (e x) ∈ L at hfixed
  change e (alpha x) ∈ L
  simpa only [beta, MulEquiv.trans_apply, e.symm_apply_apply] using hfixed

theorem characteristic_preimage (pi : H →* G) (hpi : Function.Surjective pi)
    (hk : pi.ker.Characteristic) (L : Subgroup G) (hL : L.Characteristic) :
    (L.comap pi).Characteristic := by
  let e : H ⧸ pi.ker ≃* G := QuotientGroup.quotientKerEquivOfSurjective pi hpi
  let K : Subgroup (H ⧸ pi.ker) := L.comap e.toMonoidHom
  let : pi.ker.Characteristic := hk
  have hK : K.Characteristic := characteristic_comap_equiv e L hL
  have hpre := Subgroup.Characteristic.comap_quotient_mk hK
  have heq : K.comap (QuotientGroup.mk' pi.ker) = L.comap pi := by
    ext x
    change e (QuotientGroup.mk' pi.ker x) ∈ L ↔ pi x ∈ L
    rfl
  exact heq ▸ hpre

theorem centralizer_preimage_eq_kernel (pi : H →* G)
    (hpi : Function.Surjective pi) (hk : pi.ker ≤ Subgroup.center H)
    (L : Subgroup G) (hcentral : Subgroup.centralizer (L : Set G) = ⊥) :
    Subgroup.centralizer (L.comap pi : Set H) = pi.ker := by
  apply le_antisymm
  · intro x hx
    have hquot : pi x ∈ Subgroup.centralizer (L : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      obtain ⟨a, ha⟩ := hpi y
      have hpre : a ∈ L.comap pi := by
        change pi a ∈ L
        rwa [ha]
      have hcomm := congrArg pi (Subgroup.mem_centralizer_iff.mp hx a hpre)
      simpa only [map_mul, ha] using hcomm
    rw [hcentral] at hquot
    exact hquot
  · intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y _
    exact Subgroup.mem_center_iff.mp (hk hx) y

theorem center_eq_kernel (pi : H →* G) (hpi : Function.Surjective pi)
    (hk : pi.ker ≤ Subgroup.center H) (L : Subgroup G)
    (hcentral : Subgroup.centralizer (L : Set G) = ⊥) :
    Subgroup.center H = pi.ker := by
  apply le_antisymm _ hk
  intro x hx
  rw [← centralizer_preimage_eq_kernel pi hpi hk L hcentral]
  apply Subgroup.mem_centralizer_iff.mpr
  intro y _
  exact Subgroup.mem_center_iff.mp hx y

theorem characteristic_layer_preimage (z : H) (hz : z ∈ Subgroup.center H)
    (pi : H →* G) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (L : Subgroup G) (hL : L.Characteristic)
    (hcentral : Subgroup.centralizer (L : Set G) = ⊥) :
    (L.comap pi).Characteristic ∧
      Subgroup.center H = Subgroup.zpowers z ∧
      Subgroup.centralizer (L.comap pi : Set H) = Subgroup.zpowers z := by
  have hk : pi.ker ≤ Subgroup.center H := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr hz
  have hcenter := center_eq_kernel pi hpi hk L hcentral
  have hchar : pi.ker.Characteristic := by
    rw [← hcenter]
    infer_instance
  exact ⟨characteristic_preimage pi hpi hchar L hL,
    hcenter.trans hker, (centralizer_preimage_eq_kernel pi hpi hk L hcentral).trans hker⟩

theorem map_preimage (pi : H →* G) (hpi : Function.Surjective pi)
    (L : Subgroup G) : (L.comap pi).map pi = L := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx
  · intro y hy
    obtain ⟨x, hx⟩ := hpi y
    refine ⟨x, ?_, hx⟩
    change pi x ∈ L
    rwa [hx]

theorem preimage_index (pi : H →* G) (hpi : Function.Surjective pi)
    (L : Subgroup G) : (L.comap pi).index = L.index :=
  Subgroup.index_comap_of_surjective L hpi

theorem preimage_relIndex (pi : H →* G) (hpi : Function.Surjective pi)
    (L J : Subgroup G) : (L.comap pi).relIndex (J.comap pi) = L.relIndex J := by
  rw [Subgroup.relIndex_comap, map_preimage pi hpi J]

theorem central_cover_dihedral_index [Finite G]
    (pi : H →* G) (hpi : Function.Surjective pi)
    (k : ℕ) (hk : 2 ≤ k)
    (S : Sylow 2 G) (eS : S ≃* DihedralGroup (2 ^ (k - 1)))
    (L : Subgroup G) (hLnormal : L.Normal)
    (J : Subgroup G) (hJindex : J.index = 2) (hLJ : L ≤ J)
    (U : Sylow 2 L) (hUnc : ¬ IsCyclic U) :
    3 ≤ k ∧ Odd ((L.comap pi).relIndex (J.comap pi)) ∧
      (L.comap pi).index.factorization 2 = 1 ∧
      2 ^ (L.comap pi).index.factorization 2 = 2 := by
  obtain ⟨hk3, _, _, hodd, _, hfactor, hpow⟩ :=
    DihedralNormalIndex.noncyclic_normal_dihedral_fills_index_two
      k hk S eS L hLnormal J hJindex hLJ U hUnc
  rw [preimage_relIndex pi hpi L J, preimage_index pi hpi L]
  exact ⟨hk3, hodd, hfactor, hpow⟩

end CFSG.Semidihedral.CharacteristicSL2Layer
