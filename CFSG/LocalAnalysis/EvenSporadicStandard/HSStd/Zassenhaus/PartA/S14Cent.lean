module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14Fusion
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

namespace S14Cfg

variable {G : Type} [Group G] [Finite G] {t : G} (c : S14Cfg G t)

include c

@[expose] noncomputable def cE : Multiplicative (ZMod 3) ≃* ↥(zpowers c.xt) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact mulEquivOfPrimeCardEq (p := 3) (by simp [Nat.card_eq_fintype_card])
    (by rw [Nat.card_zpowers]; exact c.orderOf_xt)

@[expose] noncomputable def eBt : Equiv.Perm (Fin 5) ≃* ↥c.Btsub :=
  c.eB.symm.trans (MulEquiv.subgroupMap (MulAut.conj t) c.Bsub)

@[expose] noncomputable def Phi0 : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5) →* G :=
  MonoidHom.noncommCoprod ((zpowers c.xt).subtype.comp c.cE.toMonoidHom)
    (c.Btsub.subtype.comp c.eBt.toMonoidHom)
    (fun ζ σ => (c.cm_xt_Bt.comm (c.cE ζ).2 (c.eBt σ).2 :
      ((c.cE ζ : ↥(zpowers c.xt)) : G) * (c.eBt σ : G) = (c.eBt σ : G) * (c.cE ζ : G)))

theorem Phi0_apply (ζ : Multiplicative (ZMod 3)) (σ : Equiv.Perm (Fin 5)) :
    c.Phi0 (ζ, σ) = ((c.cE ζ : ↥(zpowers c.xt)) : G) * ((c.eBt σ : ↥c.Btsub) : G) := by
  simp [Phi0]

theorem Phi0_mem_J (p : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) : c.Phi0 p ∈ c.Jc := by
  obtain ⟨ζ, σ⟩ := p
  rw [Phi0_apply]
  exact mul_mem (zpowers_le.2 c.xt_mem_J (c.cE ζ).2) (c.Bt_le_J (c.eBt σ).2)

theorem exists_Phi0 {g : G} (hg : g ∈ zpowers c.xt ⊔ c.Btsub) :
    ∃ p, c.Phi0 p = g := by
  obtain ⟨w, hw, b, hb, rfl⟩ := (mem_sup_iff_of_cm c.cm_xt_Bt).1 hg
  refine ⟨(c.cE.symm ⟨w, hw⟩, c.eBt.symm ⟨b, hb⟩), ?_⟩
  rw [Phi0_apply]
  simp

theorem Phi0_mem_sup (p : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) :
    c.Phi0 p ∈ zpowers c.xt ⊔ c.Btsub := by
  obtain ⟨ζ, σ⟩ := p
  rw [Phi0_apply]
  exact mul_mem (mem_sup_left (c.cE ζ).2) (mem_sup_right (c.eBt σ).2)

theorem Phi0_mem_Zc {p : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)} (h : c.Phi0 p ∈ c.Zc) :
    p = 1 := by
  obtain ⟨ζ, σ⟩ := p
  rw [Phi0_apply] at h
  have hw : ((c.cE ζ : ↥(zpowers c.xt)) : G) ∈ zpowers c.xt := (c.cE ζ).2
  have hAB : ((c.eBt σ : ↥c.Btsub) : G) ∈ c.Asub ⊔ c.Bsub := by
    have e : ((c.eBt σ : ↥c.Btsub) : G) =
        (((c.cE ζ : ↥(zpowers c.xt)) : G))⁻¹ *
          (((c.cE ζ : ↥(zpowers c.xt)) : G) * (c.eBt σ : G)) := by group
    rw [e]
    exact mul_mem (inv_mem (mem_sup_left (mem_sup_right hw))) (c.Zc_le_AB h)
  have hσ : σ = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro g
    have h1 := c.cm_AB_Bt.comm hAB (c.eBt g).2
    apply c.eBt.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact h1
  rw [hσ, map_one] at h
  simp only [OneMemClass.coe_one, mul_one] at h
  have hw1 : ((c.cE ζ : ↥(zpowers c.xt)) : G) = 1 :=
    c.eq_one_of_mem_Zc_Xt h (zpowers_le.2 c.xt_mem_Xt hw)
  have hζ : ζ = 1 := c.cE.map_eq_one_iff.1 (Subtype.ext hw1)
  rw [hσ, hζ]
  rfl

theorem range_Phi0 : c.Phi0.range = zpowers c.xt ⊔ c.Btsub := by
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    exact c.Phi0_mem_sup p
  · intro hg
    obtain ⟨p, hp⟩ := c.exists_Phi0 hg
    exact ⟨p, hp⟩

theorem Rc_eq : c.Rc = c.Zc ⊔ c.Phi0.range := by
  rw [c.range_Phi0, ← sup_assoc]
  exact c.centralizer_xt_inf_J

end S14Cfg

instance instNormalZcSubgroupOf {G : Type} [Group G] [Finite G] {t : G} (c : S14Cfg G t) :
    (c.Zc.subgroupOf c.Jc).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h : (n : G) * g = g * n := mem_centralizer_iff.1 g.2 n hn
    have e : (g * n * g⁻¹ : ↥c.Jc) = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_inv_eq_iff_eq_mul]
      exact h.symm
    rw [e]
    exact hn⟩

namespace S14Cfg

variable {G : Type} [Group G] [Finite G] {t : G} (c : S14Cfg G t)

abbrev Yq : Type := ↥c.Jc ⧸ c.Zc.subgroupOf c.Jc

@[expose] def mkY : ↥c.Jc →* c.Yq := QuotientGroup.mk' (c.Zc.subgroupOf c.Jc)

theorem mkY_surjective : Function.Surjective c.mkY := QuotientGroup.mk'_surjective _

theorem mkY_eq_one_iff (g : ↥c.Jc) : c.mkY g = 1 ↔ (g : G) ∈ c.Zc := by
  rw [mkY, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

@[expose] def xbar : c.Yq := c.mkY ⟨c.xt, c.xt_mem_J⟩

@[expose] noncomputable def Phi1 : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5) →* c.Yq :=
  c.mkY.comp (c.Phi0.codRestrict c.Jc c.Phi0_mem_J)

theorem Phi1_apply (p : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) :
    c.Phi1 p = c.mkY ⟨c.Phi0 p, c.Phi0_mem_J p⟩ := rfl

theorem Phi1_injective : Function.Injective c.Phi1 :=
  (injective_iff_map_eq_one _).2 fun p h =>
    c.Phi0_mem_Zc ((c.mkY_eq_one_iff ⟨c.Phi0 p, c.Phi0_mem_J p⟩).1 h)

theorem centralizer_xbar_eq (hA : AutFacts ↥c.L₁) :
    centralizer ({c.xbar} : Set c.Yq) = c.Phi1.range := by
  ext y
  obtain ⟨g, rfl⟩ := c.mkY_surjective y
  constructor
  · intro hy
    rw [mem_centralizer_singleton_iff] at hy
    let xt' : ↥c.Jc := ⟨c.xt, c.xt_mem_J⟩
    have h1 : c.mkY (g * xt' * g⁻¹ * xt'⁻¹) = 1 := by
      have hy' : c.mkY g * c.mkY xt' = c.mkY xt' * c.mkY g := hy
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc c.mkY g * c.mkY xt' * (c.mkY g)⁻¹ * (c.mkY xt')⁻¹
          = (c.mkY xt' * c.mkY g) * (c.mkY g)⁻¹ * (c.mkY xt')⁻¹ := by rw [hy']
        _ = 1 := by group
    have h2 : (g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹ ∈ c.Zc := (c.mkY_eq_one_iff _).1 h1
    have hcom : c.xt * ((g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹) =
        ((g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹) * c.xt :=
      (c.cm_Z_xt.comm h2 (mem_zpowers _)).symm
    have h3 : (g : G) * c.xt * (g : G)⁻¹ = c.xt := by
      apply c.conj_xt_eq_of_mem hA
      refine ⟨_, h2, ?_⟩
      calc (g : G) * c.xt * (g : G)⁻¹ = ((g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹) * c.xt := by group
        _ = c.xt * ((g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹) := hcom.symm
    have hR : (g : G) ∈ c.Rc :=
      ⟨g.2, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h3)⟩
    rw [c.Rc_eq] at hR
    obtain ⟨z0, hz0, e, ⟨p, rfl⟩, hge⟩ := (mem_sup_iff_of_cm
      (c.cm_Z_xt.sup_right c.cm_Z_Bt |>.mono le_rfl (c.range_Phi0 ▸ le_rfl))).1 hR
    refine ⟨p, ?_⟩
    rw [Phi1_apply]
    have : g = ⟨z0, c.Zc_le_Jc hz0⟩ * ⟨c.Phi0 p, c.Phi0_mem_J p⟩ := Subtype.ext hge
    rw [this, map_mul, (c.mkY_eq_one_iff ⟨z0, c.Zc_le_Jc hz0⟩).2 hz0, one_mul]
  · rintro ⟨p, hp⟩
    rw [mem_centralizer_singleton_iff, ← hp, Phi1_apply, xbar, ← map_mul, ← map_mul]
    congr 1
    have hR : c.Phi0 p ∈ c.Rc := by
      rw [c.Rc_eq]
      exact mem_sup_right ⟨p, rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hR.2)

theorem centralizer_xbar_equiv (hA : AutFacts ↥c.L₁) :
    Nonempty (↥(centralizer ({c.xbar} : Set c.Yq)) ≃*
      Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) :=
  ⟨(MulEquiv.subgroupCongr (c.centralizer_xbar_eq hA)).trans
    (MonoidHom.ofInjective c.Phi1_injective).symm⟩

end S14Cfg

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
