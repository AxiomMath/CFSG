module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParPk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Pair
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

@[expose] noncomputable def sec5cdPhi (φ : ↥L →* omegaGroup hQ) : ↥L →* OGroup Q :=
  (omegaGroup hQ).subtype.comp φ

theorem sec5cdPhi_apply (φ : ↥L →* omegaGroup hQ) (l : ↥L) :
    sec5cdPhi φ l = ((φ l : omegaGroup hQ) : OGroup Q) :=
  rfl

theorem sec5cdPhi_injective {φ : ↥L →* omegaGroup hQ} (hinj : Function.Injective φ) :
    Function.Injective (sec5cdPhi φ) :=
  fun _ _ h => hinj (Subtype.ext h)

theorem sec5cdPhi_range {φ : ↥L →* omegaGroup hQ} (hsurj : Function.Surjective φ) :
    (sec5cdPhi φ).range = omegaGroup hQ := by
  ext g
  constructor
  · rintro ⟨l, rfl⟩
    exact (φ l).2
  · intro hg
    obtain ⟨l, hl⟩ := hsurj ⟨g, hg⟩
    exact ⟨l, congrArg Subtype.val hl⟩

@[expose] noncomputable def sec5cdPull (φ : ↥L →* omegaGroup hQ)
    (B : Subgroup (OGroup Q)) : Subgroup G :=
  (B.comap (sec5cdPhi φ)).map L.subtype

theorem mem_sec5cdPull_iff {φ : ↥L →* omegaGroup hQ} {B : Subgroup (OGroup Q)} {x : G} :
    x ∈ sec5cdPull φ B ↔ ∃ l : ↥L, (l : G) = x ∧ sec5cdPhi φ l ∈ B := by
  unfold sec5cdPull
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, rfl, Subgroup.mem_comap.mp hl⟩
  · rintro ⟨l, rfl, hl⟩
    exact ⟨l, Subgroup.mem_comap.mpr hl, rfl⟩

theorem sec5cdPull_sup {φ : ↥L →* omegaGroup hQ} (hsurj : Function.Surjective φ)
    {B B' : Subgroup (OGroup Q)} (hB : B ≤ omegaGroup hQ) (hB' : B' ≤ omegaGroup hQ) :
    sec5cdPull φ (B ⊔ B') = sec5cdPull φ B ⊔ sec5cdPull φ B' := by
  have hr := sec5cdPhi_range hsurj
  unfold sec5cdPull
  rw [← Subgroup.map_sup, Subgroup.comap_sup_eq_of_le_range _ (hr ▸ hB) (hr ▸ hB')]

theorem sec5cd_twoRes_le {X : Subgroup G} (hX : X ≤ L) : twoRes X ≤ L :=
  (Subgroup.closure_le L).mpr fun _ hg => hX hg.1

theorem sec5cd_mem_twoRes_iff {φ : ↥L →* omegaGroup hQ} (hinj : Function.Injective φ)
    (hsurj : Function.Surjective φ) {z : G} (hz : z ∈ L) (l : ↥L) :
    (l : G) ∈ twoRes (L ⊓ centralizer ({z} : Set G)) ↔
      sec5cdPhi φ l ∈ twoRes (omegaGroup hQ ⊓
        centralizer ({sec5cdPhi φ ⟨z, hz⟩} : Set (OGroup Q))) := by
  have hΦ := sec5cdPhi_injective hinj
  let zL : ↥L := ⟨z, hz⟩
  let S : Set ↥L := {l | l * zL = zL * l ∧ Odd (orderOf l)}
  have hG : twoRes (L ⊓ centralizer ({z} : Set G)) = (Subgroup.closure S).map L.subtype := by
    rw [MonoidHom.map_closure]
    refine congrArg Subgroup.closure (Set.ext fun g => ?_)
    constructor
    · rintro ⟨hg, hodd⟩
      obtain ⟨hgL, hgc⟩ := Subgroup.mem_inf.mp hg
      refine ⟨⟨g, hgL⟩, ⟨Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgc), ?_⟩, rfl⟩
      rw [← Subgroup.orderOf_coe (⟨g, hgL⟩ : ↥L)] at *
      exact hodd
    · rintro ⟨l, ⟨hl1, hl2⟩, rfl⟩
      refine ⟨Subgroup.mem_inf.mpr ⟨l.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val hl1)⟩, ?_⟩
      show Odd (orderOf (l : G))
      rw [Subgroup.orderOf_coe l]
      exact hl2
  have hΩ : twoRes (omegaGroup hQ ⊓ centralizer ({sec5cdPhi φ zL} : Set (OGroup Q))) =
      (Subgroup.closure S).map (sec5cdPhi φ) := by
    rw [MonoidHom.map_closure]
    refine congrArg Subgroup.closure (Set.ext fun g => ?_)
    constructor
    · rintro ⟨hg, hodd⟩
      obtain ⟨hgΩ, hgc⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨l, hl⟩ := hsurj ⟨g, hgΩ⟩
      have hlg : sec5cdPhi φ l = g := congrArg Subtype.val hl
      refine ⟨l, ⟨?_, ?_⟩, hlg⟩
      · apply hΦ
        rw [map_mul, map_mul, hlg]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hgc)
      · rw [← hlg, orderOf_injective _ hΦ] at hodd
        exact hodd
    · rintro ⟨l, ⟨hl1, hl2⟩, rfl⟩
      refine ⟨Subgroup.mem_inf.mpr ⟨(φ l).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
      · rw [← map_mul, ← map_mul, hl1]
      · rw [orderOf_injective _ hΦ]
        exact hl2
  rw [hG, hΩ]
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).trans
    (Subgroup.mem_map_iff_mem hΦ).symm

theorem sec5cd_mem_twoRes_iff_sup {φ : ↥L →* omegaGroup hQ} (hinj : Function.Injective φ)
    (hsurj : Function.Surjective φ) {z : G} (hz : z ∈ L)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hz⟩)) (l : ↥L) :
    (l : G) ∈ twoRes (L ⊓ centralizer ({z} : Set G)) ↔ sec5cdPhi φ l ∈ D.L ⊔ D.R := by
  rw [sec5cd_mem_twoRes_iff hinj hsurj hz l, D.twoRes_eq]

theorem sec5cdPull_sup_eq_twoRes {φ : ↥L →* omegaGroup hQ} (hinj : Function.Injective φ)
    (hsurj : Function.Surjective φ) {z : G} (hz : z ∈ L)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hz⟩)) :
    sec5cdPull φ (D.L ⊔ D.R) = twoRes (L ⊓ centralizer ({z} : Set G)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨l, rfl, hl⟩ := mem_sec5cdPull_iff.mp hx
    exact (sec5cd_mem_twoRes_iff_sup hinj hsurj hz D l).mpr hl
  · intro hx
    have hxL : x ∈ L := sec5cd_twoRes_le inf_le_left hx
    exact mem_sec5cdPull_iff.mpr ⟨⟨x, hxL⟩, rfl,
      (sec5cd_mem_twoRes_iff_sup hinj hsurj hz D ⟨x, hxL⟩).mp hx⟩

namespace Om6Par

variable {t : OGroup Q} (D : Om6Par Q t)

@[expose] noncomputable def q8Img : Subgroup (OGroup Q) :=
  (q8SL.prod q8SL).map (D.theta.comp detPhi)

theorem mem_q8Img_iff {g : OGroup Q} :
    g ∈ D.q8Img ↔ ∃ a b : SL2F3, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ D.theta (detPhi (a, b)) = g := by
  unfold q8Img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨a, b, hab.1, hab.2, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

theorem theta_left_mem_q8Img {a : SL2F3} (ha : a ^ 4 = 1) :
    D.theta (leftMulHom a) ∈ D.q8Img :=
  (mem_q8Img_iff D).mpr ⟨a, 1, ha, one_pow 4, by rw [detPhi_apply]; simp⟩

theorem theta_right_mem_q8Img {b : SL2F3} (hb : b ^ 4 = 1) :
    D.theta (rightMulHom b) ∈ D.q8Img :=
  (mem_q8Img_iff D).mpr ⟨1, b, one_pow 4, hb, by rw [detPhi_apply]; simp⟩

theorem q8Img_pow_four {g : OGroup Q} (hg : g ∈ D.q8Img) : g ^ 4 = 1 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_q8Img_iff D).mp hg
  have h4 : ((a, b) : SL2F3 × SL2F3) ^ 4 = 1 := Prod.ext (by simpa using ha) (by simpa using hb)
  rw [← map_pow, ← map_pow, h4, map_one, map_one]

theorem q8Img_le_sup : D.q8Img ≤ D.L ⊔ D.R := by
  intro g hg
  obtain ⟨a, b, -, -, rfl⟩ := (mem_q8Img_iff D).mp hg
  rw [detPhi_apply, map_mul]
  exact Subgroup.mul_mem_sup (Subgroup.mem_map.mpr ⟨leftMulHom a, ⟨a, rfl⟩, rfl⟩)
    (Subgroup.mem_map.mpr ⟨rightMulHom b, ⟨b, rfl⟩, rfl⟩)

theorem q8Img_le_omega : D.q8Img ≤ omegaGroup D.nd :=
  D.q8Img_le_sup.trans (D.le_omega_cent.trans inf_le_left)

theorem conj_q8Img {g q : OGroup Q} (hg : g ∈ D.L ⊔ D.R) (hq : q ∈ D.q8Img) :
    g * q * g⁻¹ ∈ D.q8Img := by
  rw [← D.map_omega] at hg
  obtain ⟨ω, hω, rfl⟩ := Subgroup.mem_map.mp hg
  rw [← range_detPhi] at hω
  obtain ⟨⟨A, B⟩, rfl⟩ := hω
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_q8Img_iff D).mp hq
  refine (mem_q8Img_iff D).mpr ⟨A * a * A⁻¹, B * b * B⁻¹,
    (mem_q8SL_iff _).mp (q8SL_normal.conj_mem a ((mem_q8SL_iff a).mpr ha) A),
    (mem_q8SL_iff _).mp (q8SL_normal.conj_mem b ((mem_q8SL_iff b).mpr hb) B), ?_⟩
  have h : ((A, B) * (a, b) * (A, B)⁻¹ : SL2F3 × SL2F3) = (A * a * A⁻¹, B * b * B⁻¹) := rfl
  rw [← h]
  simp only [map_mul, map_inv]

end Om6Par

theorem sec5cd_pull_q8_le_twoCoreIn {φ : ↥L →* omegaGroup hQ} (hinj : Function.Injective φ)
    (hsurj : Function.Surjective φ) {z : G} (hz : z ∈ L)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hz⟩)) :
    sec5cdPull φ D.q8Img ≤ twoCoreIn (twoRes (L ⊓ centralizer ({z} : Set G))) := by
  have hΦ := sec5cdPhi_injective hinj
  have hmem := sec5cd_mem_twoRes_iff_sup hinj hsurj hz D
  have hLH : twoRes (L ⊓ centralizer ({z} : Set G)) ≤ L := sec5cd_twoRes_le inf_le_left
  have hPH : sec5cdPull φ D.q8Img ≤ twoRes (L ⊓ centralizer ({z} : Set G)) := by
    intro x hx
    obtain ⟨l, rfl, hl⟩ := mem_sec5cdPull_iff.mp hx
    exact (hmem l).mpr (D.q8Img_le_sup hl)
  refine le_twoCoreIn_of_normal hPH ?_ ?_
  · intro g
    refine ⟨2, ?_⟩
    obtain ⟨l, hl, hql⟩ := mem_sec5cdPull_iff.mp g.2
    have h4 : l ^ 4 = 1 := hΦ (by rw [map_pow, D.q8Img_pow_four hql, map_one])
    have h4' : l ^ 2 ^ 2 = 1 := h4
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hl, ← Subgroup.coe_pow, h4', Subgroup.coe_one]
  · rw [Subgroup.normal_subgroupOf_iff hPH]
    intro h k hh hk
    obtain ⟨lh, rfl, hlh⟩ := mem_sec5cdPull_iff.mp hh
    have hkL : k ∈ L := hLH hk
    have hk' := (hmem ⟨k, hkL⟩).mp hk
    refine mem_sec5cdPull_iff.mpr ⟨⟨k, hkL⟩ * lh * ⟨k, hkL⟩⁻¹, rfl, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact D.conj_q8Img hk' hlh

end CFSG.OddStandard.SmallF3.Omega
