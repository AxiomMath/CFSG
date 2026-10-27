module

public import CFSG.GH74.GLS.NT44.ActualCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Root
import CFSG.GH74.GLS.NT44.ActualCover
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6KProd

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.PSL3Four.F4

theorem exists_root_complement
    (g : CFSG.ComponentClassification.PSL3Four.S) :
    let R : Subgroup CFSG.ComponentClassification.PSL3Four.S :=
      CFSG.ComponentClassification.GrSLit.GrS5.rootX01.map
        (MulAut.conj g).toMonoidHom
    ∃ Y : Subgroup CFSG.GH74.GLS.NT44.FullTwoCover,
      Y.map CFSG.GH74.GLS.NT44.fullTwoCoverToS = R ∧
      Y ⊓ Subgroup.center CFSG.GH74.GLS.NT44.FullTwoCover = ⊥ ∧
      Y ⊔ Subgroup.center CFSG.GH74.GLS.NT44.FullTwoCover =
        R.comap CFSG.GH74.GLS.NT44.fullTwoCoverToS ∧
      CFSG.Open.IsElemAbelian 2 Y ∧
      Nat.card Y = 4 ∧
      ∃ e : (↥Y × ↥(Subgroup.center CFSG.GH74.GLS.NT44.FullTwoCover)) ≃*
          ↥(R.comap CFSG.GH74.GLS.NT44.fullTwoCoverToS),
        ∀ (y : Y) (z : Subgroup.center CFSG.GH74.GLS.NT44.FullTwoCover),
          ((e (y, z) : ↥(R.comap CFSG.GH74.GLS.NT44.fullTwoCoverToS)) :
              CFSG.GH74.GLS.NT44.FullTwoCover) =
            (y : CFSG.GH74.GLS.NT44.FullTwoCover) *
              (z : CFSG.GH74.GLS.NT44.FullTwoCover) := by
  obtain ⟨-, -, -, -, -, hπsurj, -, hπker, hkercard, -, hfin, -, -⟩ :=
    modelStructure
  have : Finite FullTwoCover := hfin
  let R : Subgroup S := rootX01.map (MulAut.conj g).toMonoidHom
  let c : S ≃* S := MulAut.conj g
  let pi_g : FullTwoCover →* S := c.symm.toMonoidHom.comp fullTwoCoverToS
  change ∃ Y : Subgroup FullTwoCover,
      Y.map fullTwoCoverToS = R ∧
      Y ⊓ Subgroup.center FullTwoCover = ⊥ ∧
      Y ⊔ Subgroup.center FullTwoCover = R.comap fullTwoCoverToS ∧
      CFSG.Open.IsElemAbelian 2 Y ∧
      Nat.card Y = 4 ∧
      ∃ e : (↥Y × ↥(Subgroup.center FullTwoCover)) ≃*
          ↥(R.comap fullTwoCoverToS),
        ∀ (y : Y) (z : Subgroup.center FullTwoCover),
          ((e (y, z) : ↥(R.comap fullTwoCoverToS)) : FullTwoCover) =
            (y : FullTwoCover) * (z : FullTwoCover)
  have hker_g : pi_g.ker = fullTwoCoverToS.ker :=
    MonoidHom.ker_comp_of_injective fullTwoCoverToS c.symm.toMonoidHom c.symm.injective
  have hπgsurj : Function.Surjective pi_g := by
    intro s
    obtain ⟨x, hx⟩ := hπsurj (c s)
    refine ⟨x, ?_⟩
    change c.symm (fullTwoCoverToS x) = s
    simpa only [hx] using c.symm_apply_apply s
  have hK_g : pi_g.ker ≤ Subgroup.center FullTwoCover := by
    rw [hker_g, hπker]
  have h3_pi : ∀ z ∈ fullTwoCoverToS.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    have hdvd16 : orderOf z ∣ 16 := by
      have h := Subgroup.orderOf_dvd_natCard fullTwoCoverToS.ker hz
      rwa [hkercard] at h
    have hdvd3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hcop : Nat.Coprime 16 3 := by decide
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd16 hdvd3)
  have h3_g : ∀ z ∈ pi_g.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    exact h3_pi z (by rwa [hker_g] at hz) hz3
  have hroot_inj : Function.Injective (fun d : F4 => rhoS (x01S d)) := by
    intro a b hab
    change rhoS (x01S a) = rhoS (x01S b) at hab
    have hsq : ∀ d : F4, rhoS (x01S d) * rhoS (x01S d) = 1 := fun d => by
      simp only [rhoS_x01_mul, CharTwo.add_self_eq_zero, rhoS_x01_zero]
    have h0 : rhoS (x01S (a + b)) = 1 := by
      rw [← rhoS_x01_mul, hab]
      exact hsq b
    have hz : a + b = 0 := by
      by_contra hne
      exact rhoS_x01_ne_one hne h0
    exact CharTwo.add_eq_zero.mp hz
  let f : F4 → rootX01 := fun d =>
    ⟨rhoS (x01S d), mem_rootX01.mpr ⟨d, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact hroot_inj (congrArg Subtype.val hab)
  have hf_surj : Function.Surjective f := by
    intro v
    obtain ⟨d, hd⟩ := mem_rootX01.mp v.2
    exact ⟨d, Subtype.ext hd⟩
  have hcard_root : Nat.card rootX01 = 4 := by
    have h := Nat.card_eq_of_bijective f ⟨hf_inj, hf_surj⟩
    rw [CFSG.ComponentClassification.PSL3Four.natCard_F4] at h
    exact h.symm
  obtain ⟨Y, hYK_g, hYV_g, hYab⟩ :=
    CFSG.ComponentClassification.GrSLit.GrS5.exists_split
      (E := FullTwoCover) (P := S) (π := pi_g) hπgsurj hK_g h3_g
      (V := rootX01) rootX01_commutators (h := rhoS hS)
      (fun v hv => by
        obtain ⟨d, rfl⟩ := mem_rootX01.mp hv
        rw [rootX01_conj_h]
        exact mem_rootX01.mpr ⟨ω * ω * d, rfl⟩)
      rootX01_norm
  have hYV : Y.map fullTwoCoverToS = R := by
    have hmap : Y.map pi_g = (Y.map fullTwoCoverToS).map c.symm.toMonoidHom := by
      change Y.map (c.symm.toMonoidHom.comp fullTwoCoverToS) =
        (Y.map fullTwoCoverToS).map c.symm.toMonoidHom
      simp only [Subgroup.map_map]
    have h1 : (Y.map fullTwoCoverToS).map c.symm.toMonoidHom = rootX01 := by
      rw [← hmap]
      exact hYV_g
    have hcc : c.toMonoidHom.comp c.symm.toMonoidHom = MonoidHom.id S := by
      apply MonoidHom.ext
      intro x
      exact c.apply_symm_apply x
    have h2 := congrArg (Subgroup.map c.toMonoidHom) h1
    rw [Subgroup.map_map, hcc, Subgroup.map_id] at h2
    change Y.map fullTwoCoverToS = rootX01.map (MulAut.conj g).toMonoidHom
    exact h2
  have hYcenter : Y ⊓ Subgroup.center FullTwoCover = ⊥ := by
    simpa only [hker_g, hπker] using hYK_g
  have hYsup : Y ⊔ Subgroup.center FullTwoCover = R.comap fullTwoCoverToS := by
    have h := Subgroup.comap_map_eq (f := fullTwoCoverToS) (H := Y)
    rw [hYV, hπker] at h
    exact h.symm
  have hYsq : ∀ x ∈ Y, x ^ 2 = 1 := by
    intro x hx
    have hxroot : pi_g x ∈ rootX01 := by
      have hmem : pi_g x ∈ Y.map pi_g := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [hYV_g] at hmem
    obtain ⟨d, hd⟩ := mem_rootX01.mp hxroot
    have hroot_sq : rhoS (x01S d) * rhoS (x01S d) = 1 := by
      simp only [rhoS_x01_mul, CharTwo.add_self_eq_zero, rhoS_x01_zero]
    have hmap2 : pi_g (x ^ 2) = 1 := by
      rw [map_pow, ← hd, pow_two]
      exact hroot_sq
    have hmem2 : x ^ 2 ∈ Y ⊓ pi_g.ker :=
      Subgroup.mem_inf.mpr ⟨Y.pow_mem hx 2, MonoidHom.mem_ker.mpr hmap2⟩
    rw [hYK_g] at hmem2
    exact Subgroup.mem_bot.mp hmem2
  have hYea : CFSG.Open.IsElemAbelian 2 Y :=
    ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hYab a a.2 b b.2)), hYsq⟩
  let phi : Y → rootX01 := fun y =>
    ⟨pi_g (y : FullTwoCover), by
      have hmem : pi_g (y : FullTwoCover) ∈ Y.map pi_g :=
        Subgroup.mem_map.mpr ⟨y, y.2, rfl⟩
      rwa [hYV_g] at hmem⟩
  have hphi_inj : Function.Injective phi := by
    intro y1 y2 h
    have hpi : pi_g (y1 : FullTwoCover) = pi_g (y2 : FullTwoCover) :=
      congrArg Subtype.val h
    have hmem : (y1 : FullTwoCover) * (y2 : FullTwoCover)⁻¹ ∈ Y ⊓ pi_g.ker := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Y.mul_mem y1.2 (Y.inv_mem y2.2)
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hpi]
        exact mul_inv_cancel _
    rw [hYK_g] at hmem
    exact Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem))
  have hphi_surj : Function.Surjective phi := by
    intro v
    have hv : (v : S) ∈ Y.map pi_g := by
      rw [hYV_g]
      exact v.2
    obtain ⟨y, hy, hpy⟩ := Subgroup.mem_map.mp hv
    exact ⟨⟨y, hy⟩, Subtype.ext hpy⟩
  have hcardY : Nat.card Y = 4 := by
    have h := Nat.card_eq_of_bijective phi ⟨hphi_inj, hphi_surj⟩
    rw [hcard_root] at h
    exact h
  have hcomm_center : ∀ a ∈ Y, ∀ b ∈ Subgroup.center FullTwoCover, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_center_iff.mp hb a
  let e : (↥Y × ↥(Subgroup.center FullTwoCover)) ≃*
      ↥(R.comap fullTwoCoverToS) :=
    (CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.KProd.prodEquivSup Y
        (Subgroup.center FullTwoCover) hcomm_center hYcenter).trans
      (MulEquiv.subgroupCongr hYsup)
  refine ⟨Y, hYV, hYcenter, hYsup, hYea, hcardY, e, ?_⟩
  intro y z
  dsimp only [e]
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
  exact CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.KProd.prodEquivSup_apply
    Y (Subgroup.center FullTwoCover) hcomm_center hYcenter (y, z)

end CFSG.GH74.GLS.NT44
