module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutEngine6

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

theorem coe_mem_liftSub_iff (l : L) : (l : G) ∈ liftSub F ↔ (l : L ⧸ center L) ∈ F := by
  constructor
  · intro h
    obtain ⟨l', hl', hl'F⟩ := mem_liftSub.1 h
    rwa [show l' = l from Subtype.ext hl'] at hl'F
  · intro h
    exact mem_liftSub.2 ⟨l, rfl, h⟩

namespace OutData

variable (D : OutData L z t T₁ F tb)

include D in
theorem theta_mem_normalizer_iff
    (hinj : Function.Injective (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)))
    (c : centralizer ({z} : Set G)) :
    thetaH D.cfg.cent_le c ∈ normalizer ((innerImage (L ⧸ center L) F :
      Subgroup (MulAut (L ⧸ center L))) : Set (MulAut (L ⧸ center L))) ↔
      (c : G) ∈ normalizer (liftSub F : Set G) := by
  rw [mem_normalizer_innerImage_iff hinj, Subgroup.mem_normalizer_iff]
  have hmem : ∀ l : L, thetaH D.cfg.cent_le c (l : L ⧸ center L) ∈ F ↔
      (c : G) * (l : G) * (c : G)⁻¹ ∈ liftSub F := by
    intro l
    rw [D.theta_apply_mk c.2 l]
    exact (coe_mem_liftSub_iff ⟨(c : G) * l * (c : G)⁻¹, D.conj_mem_L c.2 l.2⟩).symm
  constructor
  · intro h g
    constructor
    · intro hg
      obtain ⟨l, rfl, hl⟩ := mem_liftSub.1 hg
      exact (hmem l).1 ((h _).1 hl)
    · intro hg
      have hgL : g ∈ L := by
        have := D.conj_mem_L (Subgroup.inv_mem _ c.2) (liftSub_le F hg)
        simpa [mul_assoc] using this
      lift g to L using hgL
      exact (coe_mem_liftSub_iff g).2 ((h _).2 ((hmem g).2 hg))
  · intro h y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact (coe_mem_liftSub_iff l).symm.trans ((h l).trans (hmem l).symm)

include D in
theorem theta_inj_of_mem {A : Subgroup G} (hzA : z ∉ A) {c c' : centralizer ({z} : Set G)}
    (hc : (c : G) ∈ A) (hc' : (c' : G) ∈ A)
    (h : thetaH D.cfg.cent_le c = thetaH D.cfg.cent_le c') : c = c' := by
  have h1 : thetaH D.cfg.cent_le (c * c'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := (D.ker _).1 h1
  rcases mem_zpowers_involution D.cfg.z_sq h2 with h3 | h3
  · exact mul_inv_eq_one.1 (Subtype.ext h3)
  · exact absurd (by
      have : (↑(c * c'⁻¹) : G) = (c : G) * (c' : G)⁻¹ := rfl
      rw [← h3, this]
      exact A.mul_mem hc (A.inv_mem hc')) hzA

include D in
theorem exists_mem_theta_eq (hθ : Function.Surjective (thetaH D.cfg.cent_le)) {A : Subgroup G}
    (hAH : A ≤ centralizer ({z} : Set G)) (hAz : A ⊔ zpowers z = centralizer ({z} : Set G))
    (β : MulAut (L ⧸ center L)) :
    ∃ c : centralizer ({z} : Set G), (c : G) ∈ A ∧ thetaH D.cfg.cent_le c = β := by
  obtain ⟨h, rfl⟩ := hθ β
  have hh : (h : G) ∈ A ⊔ zpowers z := by rw [hAz]; exact h.2
  have hzc : zpowers z ≤ centralizer (A : Set G) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hAH ha))
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hzc hh
  have hbH : b ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2
    (by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (Commute.refl z) k).symm.eq)
  refine ⟨⟨a, hAH ha⟩, ha, ?_⟩
  have h1 : h = ⟨a, hAH ha⟩ * ⟨b, hbH⟩ := Subtype.ext hab
  rw [h1, map_mul, (D.ker ⟨b, hbH⟩).2 hb, mul_one]

include D in
theorem theta_mem_innerImage_iff {A : Subgroup G} (hLA : L ≤ A) (hzA : z ∉ A)
    (c : centralizer ({z} : Set G)) (hc : (c : G) ∈ A) :
    thetaH D.cfg.cent_le c ∈ innerImage (L ⧸ center L) F ↔ (c : G) ∈ liftSub F := by
  constructor
  · rintro ⟨f, hf, hfc⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective f
    have hlH : (l : G) ∈ centralizer ({z} : Set G) := D.l_mem_H l.2
    have h1 : thetaH D.cfg.cent_le ⟨(l : G), hlH⟩ = MulAut.conj (l : L ⧸ center L) :=
      thetaH_conj D.cfg.cent_le D.cfg.z_cent l
    have h2 : c = ⟨(l : G), hlH⟩ :=
      D.theta_inj_of_mem hzA hc (hLA l.2) (by rw [h1]; exact hfc.symm)
    rw [h2]
    exact (coe_mem_liftSub_iff l).2 hf
  · intro hcF
    obtain ⟨l, hl, hlF⟩ := mem_liftSub.1 hcF
    refine ⟨(l : L ⧸ center L), hlF, ?_⟩
    have : c = ⟨(l : G), D.l_mem_H l.2⟩ := Subtype.ext hl.symm
    rw [this]
    exact (thetaH_conj D.cfg.cent_le D.cfg.z_cent l).symm

@[expose] noncomputable def thetaD
    (hinj : Function.Injective (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)))
    {A : Subgroup G} (hAH : A ≤ centralizer ({z} : Set G)) :
    ↥(normalizer (liftSub F : Set G) ⊓ A) →*
      ↥(normalizer ((innerImage (L ⧸ center L) F : Subgroup (MulAut (L ⧸ center L))) :
        Set (MulAut (L ⧸ center L)))) :=
  ((thetaH D.cfg.cent_le).comp (Subgroup.inclusion (inf_le_right.trans hAH))).codRestrict _
    (fun x => (D.theta_mem_normalizer_iff hinj (Subgroup.inclusion (inf_le_right.trans hAH) x)).2
      (mem_inf.1 x.2).1)

include D in
theorem thetaD_bijective (hcZ : center (L ⧸ center L) = ⊥)
    (hθ : Function.Surjective (thetaH D.cfg.cent_le)) {A : Subgroup G}
    (hAH : A ≤ centralizer ({z} : Set G)) (hzA : z ∉ A)
    (hAz : A ⊔ zpowers z = centralizer ({z} : Set G)) :
    Function.Bijective (D.thetaD (HypOne.conj_injective_of_center_eq_bot hcZ) hAH) := by
  have hinj : Function.Injective (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)) :=
    HypOne.conj_injective_of_center_eq_bot hcZ
  refine ⟨fun a b hab => ?_, fun n => ?_⟩
  · have h1 : thetaH D.cfg.cent_le ⟨(a : G), hAH (mem_inf.1 a.2).2⟩ =
        thetaH D.cfg.cent_le ⟨(b : G), hAH (mem_inf.1 b.2).2⟩ := congrArg Subtype.val hab
    have h2 := D.theta_inj_of_mem hzA (mem_inf.1 a.2).2 (mem_inf.1 b.2).2 h1
    have h3 : (a : G) = (b : G) := Subtype.mk.inj h2
    exact Subtype.ext h3
  · obtain ⟨c, hcA, hc⟩ := D.exists_mem_theta_eq hθ hAH hAz (n : MulAut (L ⧸ center L))
    have hcN : (c : G) ∈ normalizer (liftSub F : Set G) :=
      (D.theta_mem_normalizer_iff hinj c).1 (hc ▸ n.2)
    exact ⟨⟨(c : G), mem_inf.2 ⟨hcN, hcA⟩⟩, Subtype.ext hc⟩

include D in
theorem normQuot_A (hcZ : center (L ⧸ center L) = ⊥)
    (hθ : Function.Surjective (thetaH D.cfg.cent_le)) {A : Subgroup G} (hLA : L ≤ A)
    (hAH : A ≤ centralizer ({z} : Set G)) (hzA : z ∉ A)
    (hAz : A ⊔ zpowers z = centralizer ({z} : Set G)) (hq : AutS6Quot (L ⧸ center L) F) :
    NormQuot (Equiv.Perm (Fin 6)) (normalizer (liftSub F : Set G) ⊓ A) (liftSub F) := by
  have hinj : Function.Injective (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)) :=
    HypOne.conj_injective_of_center_eq_bot hcZ
  obtain ⟨ψ₀, hψ₀, hker₀⟩ := hq
  let ι : ↥(normalizer (liftSub F : Set G) ⊓ A) →* ↥(centralizer ({z} : Set G)) :=
    Subgroup.inclusion (inf_le_right.trans hAH)
  have hιmem : ∀ x, (ι x : G) = (x : G) := fun x => rfl
  let g : ↥(normalizer (liftSub F : Set G) ⊓ A) →*
      ↥(normalizer ((innerImage (L ⧸ center L) F : Subgroup (MulAut (L ⧸ center L))) :
        Set (MulAut (L ⧸ center L)))) :=
    ((thetaH D.cfg.cent_le).comp ι).codRestrict _ (fun x =>
      (D.theta_mem_normalizer_iff hinj (ι x)).2 (by rw [hιmem]; exact (mem_inf.1 x.2).1))
  refine ⟨ψ₀.comp g, ?_, ?_⟩
  · intro s
    obtain ⟨n, rfl⟩ := hψ₀ s
    obtain ⟨c, hcA, hc⟩ := D.exists_mem_theta_eq hθ hAH hAz (n : MulAut (L ⧸ center L))
    have hcN : (c : G) ∈ normalizer (liftSub F : Set G) :=
      (D.theta_mem_normalizer_iff hinj c).1 (hc ▸ n.2)
    refine ⟨⟨(c : G), mem_inf.2 ⟨hcN, hcA⟩⟩, ?_⟩
    show ψ₀ (g ⟨(c : G), mem_inf.2 ⟨hcN, hcA⟩⟩) = ψ₀ n
    congr 1
    exact Subtype.ext hc
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ψ₀ (g x) = 1 ↔ g x ∈ ψ₀.ker := Iff.rfl
    show ψ₀ (g x) = 1 ↔ _
    rw [h1, hker₀, Subgroup.mem_subgroupOf]
    exact D.theta_mem_innerImage_iff hLA hzA (ι x) (by rw [hιmem]; exact (mem_inf.1 x.2).2)

end OutData

end CFSG.EvenSporadicStandard.M22Std
