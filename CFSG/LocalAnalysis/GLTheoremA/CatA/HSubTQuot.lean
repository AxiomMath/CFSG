module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTGroup
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open
open scoped commutatorElement

theorem map_center_eq_of_surj {G G' : Type} [Group G] [Group G'] (hq : IsQuasisimple G)
    (ψ : G →* G') (hψ : Function.Surjective ψ) (hk : ∀ x, ψ x = 1 → x ∈ Subgroup.center G) :
    Subgroup.center G' = (Subgroup.center G).map ψ := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := hψ y
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    refine mem_center_of_commutator_mem_center hq (fun g => hk _ ?_)
    rw [map_commutatorElement]
    have := (Subgroup.mem_center_iff.mp hy) (ψ g)
    rw [commutatorElement_def, ← this]
    group
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨g, rfl⟩ := hψ g'
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) g]

theorem quotCenter_mulEquiv_of_surj {G G' : Type} [Group G] [Group G'] (hq : IsQuasisimple G)
    (ψ : G →* G') (hψ : Function.Surjective ψ) (hk : ∀ x, ψ x = 1 → x ∈ Subgroup.center G) :
    Nonempty ((G ⧸ Subgroup.center G) ≃* (G' ⧸ Subgroup.center G')) := by
  have hC := map_center_eq_of_surj hq ψ hψ hk
  have hle : Subgroup.center G ≤ (Subgroup.center G').comap ψ := by
    intro z hz
    rw [Subgroup.mem_comap, hC]
    exact Subgroup.mem_map_of_mem ψ hz
  let φ : (G ⧸ Subgroup.center G) →* (G' ⧸ Subgroup.center G') :=
    QuotientGroup.map (Subgroup.center G) (Subgroup.center G') ψ hle
  have hφ : ∀ x : G, φ (QuotientGroup.mk x) = QuotientGroup.mk (ψ x) := fun x => rfl
  refine ⟨MulEquiv.ofBijective φ ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rw [hφ, QuotientGroup.eq_one_iff, hC] at ha
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp ha
    rw [QuotientGroup.eq_one_iff]
    have hzx' : z⁻¹ * x ∈ Subgroup.center G := by
      refine hk _ ?_
      rw [map_mul, map_inv, hzx, inv_mul_cancel]
    have h2 := (Subgroup.center G).mul_mem hz hzx'
    rwa [mul_inv_cancel_left] at h2
  · intro b
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨x, rfl⟩ := hψ b'
    exact ⟨QuotientGroup.mk x, hφ x⟩

theorem isQuasisimple_of_surj {G G' : Type} [Group G] [Group G'] (hq : IsQuasisimple G)
    (ψ : G →* G') (hψ : Function.Surjective ψ) (hk : ∀ x, ψ x = 1 → x ∈ Subgroup.center G) :
    IsQuasisimple G' := by
  haveI : Group.IsPerfect G := ⟨hq.1⟩
  haveI : Group.IsPerfect G' := Group.IsPerfect.ofSurjective (f := ψ) hψ
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  obtain ⟨e⟩ := quotCenter_mulEquiv_of_surj hq ψ hψ hk
  haveI := hq.2
  exact e.symm.isSimpleGroup

theorem isComponentOf_map_mulEquiv {G G' : Type} [Group G] [Group G'] {K X : Subgroup G}
    (hK : IsComponentOf K X) (e : G ≃* G') :
    IsComponentOf (K.map (e : G →* G')) (X.map (e : G →* G')) := by
  refine ⟨Subgroup.map_mono hK.1, CFSG.Open.IsSubnormal.map (e : G →* G') hK.2.1, ?_⟩
  have hiso : ↥K ≃* ↥(K.map (e : G →* G')) :=
    Subgroup.equivMapOfInjective K (e : G →* G') e.injective
  exact (IsQuasisimple.congr hiso).mp hK.2.2

theorem isComponentOf_image_centralizer {G G' : Type} [Group G] [Group G']
    (ψ : G →* G') (hψ : Function.Surjective ψ) (hk : ∀ x, ψ x = 1 → x ∈ Subgroup.center G)
    {j : G} {K : Subgroup G} (hK : IsComponentOf K (Subgroup.centralizer ({j} : Set G))) :
    IsComponentOf (K.map ψ) (Subgroup.centralizer ({ψ j} : Set G')) := by
  set L : Subgroup G := Subgroup.centralizer ({j} : Set G) with hLdef
  set X : Subgroup G := (Subgroup.centralizer ({ψ j} : Set G')).comap ψ with hXdef
  have hmemL : ∀ c : G, c ∈ L ↔ c * j = j * c := fun c => by
    rw [hLdef, Subgroup.mem_centralizer_singleton_iff]
  have hmemX : ∀ x : G, x ∈ X ↔ ψ x * ψ j = ψ j * ψ x := fun x => by
    rw [hXdef, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  have hLX : L ≤ X := by
    intro c hc
    rw [hmemX, ← map_mul, ← map_mul, (hmemL c).mp hc]
  have hnorm : (L.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLX]
    intro c x hc hx
    have hx' : ψ x * ψ j = ψ j * ψ x := (hmemX x).mp hx
    set u : G := x * j * x⁻¹ * j⁻¹ with hudef
    have hu : u ∈ Subgroup.center G := by
      refine hk u ?_
      rw [hudef, map_mul, map_mul, map_mul, map_inv, map_inv, hx']
      group
    have hconj : x * j * x⁻¹ = u * j := by rw [hudef]; group
    have hcj : c * j = j * c := (hmemL c).mp hc
    have hzu : ∀ g : G, g * u = u * g := fun g => Subgroup.mem_center_iff.mp hu g
    rw [hmemL]
    have hyuj : (x * c * x⁻¹) * (u * j) = (u * j) * (x * c * x⁻¹) := by
      rw [← hconj]
      calc x * c * x⁻¹ * (x * j * x⁻¹) = x * (c * j) * x⁻¹ := by group
        _ = x * (j * c) * x⁻¹ := by rw [hcj]
        _ = (x * j * x⁻¹) * (x * c * x⁻¹) := by group
    apply mul_left_cancel (a := u)
    calc u * ((x * c * x⁻¹) * j) = (u * (x * c * x⁻¹)) * j := by group
      _ = ((x * c * x⁻¹) * u) * j := by rw [hzu (x * c * x⁻¹)]
      _ = (x * c * x⁻¹) * (u * j) := by group
      _ = (u * j) * (x * c * x⁻¹) := hyuj
      _ = u * (j * (x * c * x⁻¹)) := by group
  have hsub : IsSubnormal K X :=
    CFSG.Open.IsSubnormal.trans hK.2.1 (CFSG.Open.IsSubnormal.step hLX hnorm
      (CFSG.Open.IsSubnormal.refl X))
  have hXmap : X.map ψ = Subgroup.centralizer ({ψ j} : Set G') :=
    Subgroup.map_comap_eq_self_of_surjective hψ _
  refine ⟨?_, ?_, ?_⟩
  · rw [← hXmap]
    exact Subgroup.map_mono (hK.1.trans hLX)
  · rw [← hXmap]
    exact CFSG.Open.IsSubnormal.map ψ hsub
  · let ψK : ↥K →* ↥(K.map ψ) :=
      (ψ.comp K.subtype).codRestrict (K.map ψ) (fun x => Subgroup.mem_map_of_mem ψ x.2)
    have hψK : Function.Surjective ψK := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hkK : ∀ x : ↥K, ψK x = 1 → x ∈ Subgroup.center ↥K := by
      intro x hx
      have hx1 : ψ (x : G) = 1 := by
        have := congrArg Subtype.val hx
        simpa [ψK] using this
      have hxc := hk _ hx1
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have := (Subgroup.mem_center_iff.mp hxc) (g : G)
      simpa using this
    exact isQuasisimple_of_surj hK.2.2 ψK hψK hkK

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
