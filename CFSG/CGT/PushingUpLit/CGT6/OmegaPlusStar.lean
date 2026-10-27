module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusRoot
public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusEnd

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.ComponentClassification CFSG.RankThree.PartOne CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {V : Type} [CommGroup V]

theorem PlusSide.eq_one_of_central {G Y D B : Subgroup (MulAut V)} {n : ℕ}
    (hP : PlusSide G Y D B n) {z : MulAut V} (hz : z ∈ B) (hzc : ∀ b ∈ B, z * b = b * z) :
    z = 1 := by
  obtain ⟨θ⟩ := hP.bsl
  have hc : θ ⟨z, hz⟩ ∈ Subgroup.center (SLq n) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨g, rfl⟩ := θ.surjective s
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (hzc g g.2).symm)
  rw [center_sl2_eq_bot (Fq n), Subgroup.mem_bot] at hc
  have := θ.injective (hc.trans (map_one θ).symm)
  exact congrArg Subtype.val this

theorem PlusSide.qs [Finite V] {G Y D B : Subgroup (MulAut V)} {n : ℕ} (hP : PlusSide G Y D B n) :
    Nine7.QS (D.subgroupOf G) := by
  obtain ⟨θ⟩ := hP.dsl
  exact Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe (hP.dy.trans hP.yg))
    (Components.quasisimple_of_equiv θ (isQuasisimple_sl2_gf hP.hn))

theorem PlusSide.sub_cent [Finite V] {G T Y D B : Subgroup (MulAut V)} {n : ℕ}
    (cfg : Emb4Cfg G T Y)
    (hP : PlusSide G Y D B n) {c : MulAut V}
    (hc : c ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (hc1 : c ≠ 1) (hc2 : c ^ 2 = 1) :
    (D.subgroupOf (G ⊓ Subgroup.centralizer ({c} : Set (MulAut V)))).IsSubnormal := by
  have hYK : Y ≤ G ⊓ Subgroup.centralizer ({c} : Set (MulAut V)) := fun y hy =>
    ⟨hP.yg hy,
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc.2 y hy)⟩
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans hP.dy hYK hP.dnormal.isSubnormal
    (cfg.cent c hc hc1 hc2)

theorem apply_mem_commV {Y : Subgroup (MulAut V)} {y : MulAut V} (hy : y ∈ Y) {u : V}
    (hu : u ∈ commV Y) : y u ∈ commV Y :=
  CFSG.Quasithin.commV_apply_mem_of_mem hy hu

theorem PlusSide.mem_kStab_mixed {G Y D B : Subgroup (MulAut V)} {n : ℕ}
    (hP : PlusSide G Y D B n) {β c : MulAut V} (hβ : β ∈ B)
    (hc : c ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (hc2 : c ^ 2 = 1) :
    β ∈ kStab G (β * c) := by
  have hβY : β ∈ Y := hP.by_ hβ
  have hbc : β * c = c * β := Subgroup.mem_centralizer_iff.mp hc.2 β hβY
  refine mem_kStab.mpr ⟨⟨hP.yg hβY, ?_⟩, ?_⟩
  · rw [mul_assoc, ← hbc, ← mul_assoc]
  · intro v hv
    rw [mem_fixV_zpowers_iff] at hv
    have hvs : v ∈ fixV Y ⊔ commV Y := by rw [hP.vsup]; exact Subgroup.mem_top v
    obtain ⟨w, hw, u, hu, rfl⟩ := Subgroup.mem_sup.mp hvs
    have hcu : c u = u := hP.ctriv c hc ⟨1, by simpa using hc2⟩ u hu
    have hcw : c w ∈ fixV Y := by
      intro y hy
      have h1 := congrArg (fun x : MulAut V => x w) (Subgroup.mem_centralizer_iff.mp hc.2 y hy)
      simp only [MulAut.mul_apply] at h1
      rw [h1, hw y hy]
    have hβu : β u ∈ commV Y := apply_mem_commV hβY hu
    have hβw : β w = w := hw β hβY
    have hβcw : β (c w) = c w := hcw β hβY
    have hav : c w * β u = w * u := by
      have h1 : (β * c) (w * u) = c w * β u := by
        simp only [MulAut.mul_apply, map_mul, hcu, hβcw]
      rw [← h1]
      exact hv
    have hcwe : c w = w := by
      have h2 : c w * w⁻¹ ∈ fixV Y ⊓ commV Y := by
        refine ⟨Subgroup.mul_mem _ hcw (Subgroup.inv_mem _ hw), ?_⟩
        have h3 : c w * w⁻¹ = u * (β u)⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, hav, mul_comm]
        rw [h3]
        exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hβu)
      rw [hP.vinf, Subgroup.mem_bot, mul_inv_eq_one] at h2
      exact h2
    have hβue : β u = u := by
      rw [hcwe] at hav
      exact mul_left_cancel hav
    rw [map_mul, hβw, hβue]

theorem subnormal_cent_iff {G D : Subgroup (MulAut V)} (a : ↥G) :
    (D.subgroupOf (G ⊓ Subgroup.centralizer ({(a : MulAut V)} : Set (MulAut V)))).IsSubnormal ↔
      ((D.subgroupOf G).subgroupOf (Subgroup.centralizer ({a} : Set ↥G))).IsSubnormal := by
  have hC : (G ⊓ Subgroup.centralizer ({(a : MulAut V)} : Set (MulAut V))).subgroupOf G =
      Subgroup.centralizer ({a} : Set ↥G) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Nine7.mem_centralizer_single]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
  have h := CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff (B := D)
    (L := G ⊓ Subgroup.centralizer ({(a : MulAut V)} : Set (MulAut V))) (K := G) inf_le_left
  rw [hC] at h
  exact h.symm

variable [Finite V]

theorem star_D (hV : ∀ v : V, v ^ 2 = 1) {G T Y D B : Subgroup (MulAut V)} {n : ℕ}
    (hSch : LBalance.SchreierSections ↥G) (cfg : Emb4Cfg G T Y) (hP : PlusSide G Y D B n) :
    ∀ a ∈ G ⊓ Subgroup.centralizer (D : Set (MulAut V)), a ≠ 1 → a ^ 2 = 1 →
      (D.subgroupOf (G ⊓ Subgroup.centralizer ({a} : Set (MulAut V)))).IsSubnormal := by
  intro a ha ha1 ha2
  obtain ⟨β, hβB, c, hcC, rfl⟩ := hP.cdec a ha
  have hβY : β ∈ Y := hP.by_ hβB
  have hbc : β * c = c * β := Subgroup.mem_centralizer_iff.mp hcC.2 β hβY
  have hsq : β ^ 2 * c ^ 2 = 1 := by
    rw [← (Commute.mul_pow (show Commute β c from hbc)), ha2]
  have hβ2 : β ^ 2 = 1 := by
    refine hP.eq_one_of_central (B.pow_mem hβB 2) fun b hb => ?_
    have hcb : c * b = b * c := (Subgroup.mem_centralizer_iff.mp hcC.2 b (hP.by_ hb)).symm
    have hcb2 : Commute (c ^ 2) b := (show Commute c b from hcb).pow_left 2
    have hβ2c : β ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [hβ2c]
    exact (hcb2.inv_left : Commute (c ^ 2)⁻¹ b)
  have hc2 : c ^ 2 = 1 := by rw [hβ2, one_mul] at hsq; exact hsq
  have hDG : D ≤ G := hP.dy.trans hP.yg
  by_cases hβ1 : β = 1
  · subst hβ1
    have hc1 : c ≠ 1 := by simpa using ha1
    have h := hP.sub_cent cfg hcC hc1 hc2
    rw [one_mul]
    exact h
  by_cases hc1 : c = 1
  · subst hc1
    have h := star_root hV cfg hP hβB hβ2 hβ1
    rw [mul_one]
    exact h
  have hβG : β ∈ G := hP.yg hβY
  have hcG : c ∈ G := hcC.1
  let b' : ↥G := ⟨β, hβG⟩
  let c' : ↥G := ⟨c, hcG⟩
  have hb'2 : b' ^ 2 = 1 := Subtype.ext hβ2
  have hc'2 : c' ^ 2 = 1 := Subtype.ext hc2
  have hbc' : b' * c' = c' * b' := Subtype.ext hbc
  have hDb : D.subgroupOf G ≤ Subgroup.centralizer ({b'} : Set ↥G) := fun x hx =>
    Nine7.mem_centralizer_single.mpr (Subtype.ext
      ((hP.comm x.1 hx β hβB).symm))
  have hDc : D.subgroupOf G ≤ Subgroup.centralizer ({c'} : Set ↥G) := fun x hx =>
    Nine7.mem_centralizer_single.mpr (Subtype.ext
      ((Subgroup.mem_centralizer_iff.mp hcC.2 x.1 (hP.dy hx)).symm))
  have hsb := (subnormal_cent_iff (D := D) b').mp (star_root hV cfg hP hβB hβ2 hβ1)
  have hsc := (subnormal_cent_iff (D := D) c').mp (hP.sub_cent cfg hcC hc1 hc2)
  have hKmem : ∀ x : ↥G, x ∈ (kStab G (β * c)).subgroupOf G ↔
      (x : MulAut V) ∈ kStab G (β * c) := fun x => Subgroup.mem_subgroupOf
  have hK2 : IsPGroup 2 ↥((kStab G (β * c)).subgroupOf G) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by
      simpa using (kStab_abelian hV ha2).2 (x.1 : MulAut V) ((hKmem x.1).mp x.2)))⟩
  have hKa : (kStab G (β * c)).subgroupOf G ≤ Subgroup.centralizer ({b' * c'} : Set ↥G) :=
    fun x hx => Nine7.mem_centralizer_single.mpr (Subtype.ext
      (((mem_kStab.mp ((hKmem x).mp hx)).1.2).symm))
  have hKn : (((kStab G (β * c)).subgroupOf G).subgroupOf
      (Subgroup.centralizer ({b' * c'} : Set ↥G))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : ((x : ↥G) : MulAut V) ∈ kStab G (β * c) := (hKmem _).mp hx
    have hgc : (b' * c') * (g : ↥G) = (g : ↥G) * (b' * c') :=
      Nine7.mem_centralizer_single.mp g.2
    have hgc' : (g : ↥G).1 * (β * c) = (β * c) * (g : ↥G).1 :=
      (congrArg Subtype.val hgc).symm
    exact (hKmem _).mpr (kStab_conj_mem (g : ↥G).2 hgc' hx')
  have hbK : b' ∈ (kStab G (β * c)).subgroupOf G :=
    (hKmem b').mpr (hP.mem_kStab_mixed hβB hcC hc2)
  have hres := star_mixed hSch hP.qs hb'2 hc'2 hbc' hDb hDc hsb hsc _ hK2 hKa hKn hbK
  exact (subnormal_cent_iff (D := D) (b' * c')).mpr hres

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
