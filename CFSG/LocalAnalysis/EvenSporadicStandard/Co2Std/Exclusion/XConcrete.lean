module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.NWQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XHyp

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] noncomputable def XW (W : Subgroup G) : Subgroup (MulAut ↥W) :=
  W.normalizerMonoidHom.range

@[expose] noncomputable def toXW (W : Subgroup G) : ↥(normalizer (W : Set G)) →* ↥(XW W) :=
  W.normalizerMonoidHom.rangeRestrict

theorem toXW_surjective (W : Subgroup G) : Function.Surjective (toXW W) :=
  MonoidHom.rangeRestrict_surjective _

theorem coe_toXW_apply (W : Subgroup G) (n : ↥(normalizer (W : Set G))) (w : ↥W) :
    ((((toXW W n : ↥(XW W)) : MulAut ↥W) w : ↥W) : G) = (n : G) * w * (n : G)⁻¹ :=
  rfl

variable [Finite G] {L A T : Subgroup G} {z t : G} {W W₁ W₂ : Subgroup G}

private theorem WHyp.le_W₁ (h : WHyp G L A T z t W W₁ W₂) : W₁ ≤ W :=
  h.sup_eq ▸ le_sup_left

private theorem WHyp.le_W₂ (h : WHyp G L A T z t W W₁ W₂) : W₂ ≤ W :=
  h.sup_eq ▸ le_sup_right

private noncomputable def deltaV₁ (h : WHyp G L A T z t W W₁ W₂) :
    ↥(W₁.subgroupOf W) →* ↥A :=
  (E3Facts.deltaRestrict h.e2 h.e3).comp (Subgroup.subtype (W₁.subgroupOf W))

private theorem coe_deltaV₁ (h : WHyp G L A T z t W W₁ W₂) (v : ↥(W₁.subgroupOf W)) :
    ((deltaV₁ h v : ↥A) : G) = delta z ((v : ↥W) : G) := rfl

private theorem deltaV₁_injective (h : WHyp G L A T z t W W₁ W₂) :
    Function.Injective (deltaV₁ h) := by
  intro v w hvw
  have hdelta : deltaV₁ h (v * w⁻¹) = 1 := by
    rw [map_mul, hvw, map_inv, mul_inv_cancel]
  have hdelta' :
      E3Facts.deltaRestrict h.e2 h.e3 ((v * w⁻¹ : ↥(W₁.subgroupOf W)) : ↥W) = 1 := by
    apply Subtype.ext
    simpa [coe_deltaV₁] using congrArg (fun a : ↥A => (a : G)) hdelta
  have hA : (((v * w⁻¹ : ↥(W₁.subgroupOf W)) : ↥W) : G) ∈ A :=
    (E3Facts.deltaRestrict_eq_one_iff h.hyp h.e2 h.e3 _).1 hdelta'
  have hW₁ : (((v * w⁻¹ : ↥(W₁.subgroupOf W)) : ↥W) : G) ∈ W₁ := by
    have hv : ((v : ↥W) : G) ∈ W₁ := Subgroup.mem_subgroupOf.1 v.2
    have hw : ((w : ↥W) : G) ∈ W₁ := Subgroup.mem_subgroupOf.1 w.2
    simpa using W₁.mul_mem hv (W₁.inv_mem hw)
  have hbot : ((v * w⁻¹ : ↥(W₁.subgroupOf W)) : ↥W) = 1 := by
    apply Subtype.ext
    have hmem : (((v * w⁻¹ : ↥(W₁.subgroupOf W)) : ↥W) : G) ∈ (⊥ : Subgroup G) := by
      rw [← h.w.inf_A]
      exact ⟨hW₁, hA⟩
    simpa using hmem
  have h1 : v * w⁻¹ = 1 := Subtype.ext (by simpa using hbot)
  calc v = v * w⁻¹ * w := by group
    _ = 1 * w := by rw [h1]
    _ = w := by group

private theorem card_V₁ (h : WHyp G L A T z t W W₁ W₂) :
    Nat.card ↥(W₁.subgroupOf W) = 2 ^ 10 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (WHyp.le_W₁ h)).toEquiv, h.w.card₁]

private theorem deltaV₁_bijective (h : WHyp G L A T z t W W₁ W₂) :
    Function.Bijective (deltaV₁ h) := by
  refine (Nat.bijective_iff_injective_and_card (deltaV₁ h)).2
    ⟨deltaV₁_injective h, ?_⟩
  rw [card_V₁ h, h.hyp.jc.module.card]

private noncomputable def eA (h : WHyp G L A T z t W W₁ W₂) :
    ↥A ≃* ↥(W₁.subgroupOf W) :=
  (MulEquiv.ofBijective (deltaV₁ h) (deltaV₁_bijective h)).symm

private theorem deltaV₁_eA (h : WHyp G L A T z t W W₁ W₂) (a : ↥A) :
    deltaV₁ h (eA h a) = a :=
  (MulEquiv.ofBijective (deltaV₁ h) (deltaV₁_bijective h)).apply_symm_apply a

private theorem coe_eA (h : WHyp G L A T z t W W₁ W₂) (a : ↥A) :
    delta z (((eA h a : ↥(W₁.subgroupOf W)) : ↥W) : G) = (a : G) := by
  have h := congrArg (fun x : ↥A => (x : G)) (deltaV₁_eA h a)
  simpa [coe_deltaV₁] using h

private theorem eA_conj (h : WHyp G L A T z t W W₁ W₂) {x : G}
    (hx : x ∈ L ⊓ normalizer (A : Set G)) (a : ↥A) :
    eA h ⟨x * (a : G) * x⁻¹, (mem_normalizer_iff.1 hx.2 a).1 a.2⟩ =
      ⟨⟨x * (((eA h a : ↥(W₁.subgroupOf W)) : ↥W) : G) * x⁻¹,
          (mem_normalizer_iff.1 (h.le_normalizer hx) ((eA h a : ↥(W₁.subgroupOf W)) : ↥W)).1
            ((eA h a : ↥(W₁.subgroupOf W)) : ↥W).2⟩,
        by
          rw [Subgroup.mem_subgroupOf]
          exact h.w.normalizes x hx _ (Subgroup.mem_subgroupOf.1 (eA h a).2)⟩ := by
  rw [← (deltaV₁_injective h).eq_iff, deltaV₁_eA]
  apply Subtype.ext
  rw [coe_deltaV₁, h.hyp.delta_conj hx.1, coe_eA h a]

private noncomputable def XQ (h : WHyp G L A T z t W W₁ W₂) : Subgroup ↥(XW W) :=
  ((L ⊓ normalizer (A : Set G)).subgroupOf (normalizer (W : Set G))).map (toXW W)

private noncomputable def XQ₁ (h : WHyp G L A T z t W W₁ W₂) :
    Subgroup (MulAut ↥(W₁.subgroupOf W)) :=
  (autImage L A).map (MulAut.congr (eA h)).toMonoidHom

private noncomputable def Xt₁ (h : WHyp G L A T z t W W₁ W₂) : ↥(W₁.subgroupOf W) :=
  eA h ⟨t, h.hyp.jc.t_mem⟩

private theorem module_XQ₁ (h : WHyp G L A T z t W W₁ W₂) :
    ModuleFacts (XQ₁ h) (Xt₁ h) :=
  h.hyp.jc.module.map_mulEquiv (eA h)

private theorem exists_of_mem_XQ (h : WHyp G L A T z t W W₁ W₂) {q : ↥(XW W)}
    (hq : q ∈ XQ h) :
    ∃ n : ↥(normalizer (W : Set G)), (n : G) ∈ L ⊓ normalizer (A : Set G) ∧ toXW W n = q := by
  rw [XQ, Subgroup.mem_map] at hq
  obtain ⟨n, hn, rfl⟩ := hq
  exact ⟨n, hn, rfl⟩

private theorem XQ_apply_mem (h : WHyp G L A T z t W W₁ W₂) {q : ↥(XW W)} (hq : q ∈ XQ h)
    {v : ↥W} (hv : v ∈ W₁.subgroupOf W) :
    ((q : MulAut ↥W) v : ↥W) ∈ W₁.subgroupOf W := by
  obtain ⟨n, hn, hqn⟩ := exists_of_mem_XQ h hq
  rw [Subgroup.mem_subgroupOf]
  rw [← hqn]
  rw [coe_toXW_apply]
  exact h.w.normalizes (n : G) hn _ (Subgroup.mem_subgroupOf.1 hv)

private theorem map_XQ_eq (h : WHyp G L A T z t W W₁ W₂) {q : ↥(XW W)} (hq : q ∈ XQ h) :
    (W₁.subgroupOf W).map (q : MulAut ↥W).toMonoidHom = W₁.subgroupOf W := by
  refine le_antisymm ?_ ?_
  · intro w hw
    rw [Subgroup.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact XQ_apply_mem h hq hv
  · intro v hv
    rw [Subgroup.mem_map]
    refine ⟨((q : MulAut ↥W))⁻¹ v, XQ_apply_mem h ((XQ h).inv_mem hq) hv, ?_⟩
    calc (q : MulAut ↥W) ((q : MulAut ↥W)⁻¹ v) = ((q : MulAut ↥W) * (q : MulAut ↥W)⁻¹) v := rfl
      _ = v := by rw [mul_inv_cancel]; rfl

private noncomputable def restrictAut (h : WHyp G L A T z t W W₁ W₂) (q : ↥(XQ h)) :
    MulAut ↥(W₁.subgroupOf W) :=
  (MulEquiv.subgroupMap (q : MulAut ↥W) (W₁.subgroupOf W)).trans
    (MulEquiv.subgroupCongr (map_XQ_eq h q.2))

private theorem coe_restrictAut (h : WHyp G L A T z t W W₁ W₂) (q : ↥(XQ h))
    (v : ↥(W₁.subgroupOf W)) :
    (((restrictAut h q) v : ↥(W₁.subgroupOf W)) : ↥W) = (q : MulAut ↥W) v :=
  rfl

private noncomputable def restrictHom (h : WHyp G L A T z t W W₁ W₂) :
    ↥(XQ h) →* MulAut ↥(W₁.subgroupOf W) where
  toFun := restrictAut h
  map_one' := by
    ext v
    simp [coe_restrictAut]
  map_mul' q q' := by
    ext v
    rw [coe_restrictAut]
    change ((q * q' : ↥(XQ h)) : MulAut ↥W) v =
      ((↑(((restrictAut h q) ((restrictAut h q') v) : ↥(W₁.subgroupOf W)) : ↥W)) : G)
    rw [Subgroup.coe_mul, coe_restrictAut, coe_restrictAut]
    rfl

private theorem restrictHom_toXW (h : WHyp G L A T z t W W₁ W₂)
    {n : ↥(normalizer (W : Set G))} (hn : (n : G) ∈ L ⊓ normalizer (A : Set G)) :
    restrictHom h ⟨toXW W n, by
      change (toXW W n) ∈ ((L ⊓ normalizer (A : Set G)).subgroupOf
        (normalizer (W : Set G))).map (toXW W)
      exact Subgroup.mem_map_of_mem (toXW W) (by
        rw [Subgroup.mem_subgroupOf]
        exact hn)⟩ =
      MulAut.congr (eA h) (toAutImage (L := L) (A := A) ⟨(n : G), hn⟩) := by
  ext v
  rw [show (restrictHom h ⟨toXW W n, _⟩ : MulAut ↥(W₁.subgroupOf W)) =
      restrictAut h ⟨toXW W n, _⟩ from rfl]
  rw [coe_restrictAut]
  let a : ↥A := (eA h).symm v
  have harg : conjN L A ⟨(n : G), hn⟩ a =
      ⟨(n : G) * (a : G) * (n : G)⁻¹, (mem_normalizer_iff.1 hn.2 a).1 a.2⟩ :=
    Subtype.ext (conjN_apply ⟨(n : G), hn⟩ a)
  have hcongr : (MulAut.congr (eA h) (toAutImage (L := L) (A := A) ⟨(n : G), hn⟩)) v =
      eA h (conjN L A ⟨(n : G), hn⟩ a) := rfl
  rw [hcongr, harg]
  rw [coe_toXW_apply]
  have h3 := congrArg (fun x : ↥(W₁.subgroupOf W) => ((x : ↥W) : G)) (eA_conj h hn a)
  rw [h3]
  simp [a]

private theorem restrictHom_eq_one (h : WHyp G L A T z t W W₁ W₂) {q : ↥(XQ h)}
    (hq : restrictHom h q = 1) : q = 1 := by
  obtain ⟨n, hn, hqn⟩ := exists_of_mem_XQ h q.2
  have hfix : ∀ a : ↥A,
      eA h ⟨(n : G) * (a : G) * (n : G)⁻¹,
        (mem_normalizer_iff.1 hn.2 a).1 a.2⟩ = eA h a := by
    intro a
    have h1 : restrictAut h q (eA h a) = eA h a := by
      have hval := congrArg (fun f : MulAut ↥(W₁.subgroupOf W) => f (eA h a)) hq
      change restrictAut h q (eA h a) = (1 : MulAut ↥(W₁.subgroupOf W)) (eA h a) at hval
      simpa using hval
    have h2 : ((q : MulAut ↥W) (eA h a : ↥W) : ↥W) = (eA h a : ↥W) := by
      have := congrArg (fun x : ↥(W₁.subgroupOf W) => (x : ↥W)) h1
      simpa [coe_restrictAut] using this
    rw [← hqn] at h2
    have h4 : (n : G) * (((eA h a : ↥(W₁.subgroupOf W)) : ↥W) : G) * (n : G)⁻¹ =
        (((eA h a : ↥(W₁.subgroupOf W)) : ↥W) : G) := by
      rw [← coe_toXW_apply W n ((eA h a : ↥(W₁.subgroupOf W)) : ↥W)]
      exact congrArg Subtype.val h2
    rw [eA_conj h hn a]
    apply Subtype.ext
    apply Subtype.ext
    simpa using h4
  have hcent : (n : G) ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have h5 : (⟨(n : G) * a * (n : G)⁻¹, (mem_normalizer_iff.1 hn.2 a).1 ha⟩ : ↥A) =
        ⟨a, ha⟩ := (eA h).injective (hfix ⟨a, ha⟩)
    have h6 : (n : G) * a * (n : G)⁻¹ = a := congrArg Subtype.val h5
    calc a * (n : G) = ((n : G) * a * (n : G)⁻¹) * (n : G) := by rw [h6]
      _ = (n : G) * a := by group
  have hnA : (n : G) ∈ A := by
    have h1 : (n : G) ∈ L ⊓ centralizer (A : Set G) := ⟨hn.1, hcent⟩
    rwa [h.hyp.jc.centralizer_eq] at h1
  apply Subtype.ext
  ext w
  rw [← hqn]
  rw [coe_toXW_apply]
  haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
  have hcomm : (n : G) * (w : G) = (w : G) * (n : G) :=
    congrArg Subtype.val (mul_comm' (⟨(n : G), h.e3.A_le hnA⟩ : ↥W) w)
  rw [hcomm]
  simp

private theorem restrictHom_injective (h : WHyp G L A T z t W W₁ W₂) :
    Function.Injective (restrictHom h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  rw [MonoidHom.mem_ker] at hq
  rw [Subgroup.mem_bot]
  exact restrictHom_eq_one h hq

private theorem restrictHom_range (h : WHyp G L A T z t W W₁ W₂) :
    (restrictHom h).range = XQ₁ h := by
  have hmem : ∀ n : ↥(normalizer (W : Set G)),
      (hn : (n : G) ∈ L ⊓ normalizer (A : Set G)) → toXW W n ∈ XQ h := by
    intro n hn
    change (toXW W n) ∈ ((L ⊓ normalizer (A : Set G)).subgroupOf
      (normalizer (W : Set G))).map (toXW W)
    exact Subgroup.mem_map_of_mem (toXW W) (by
      rw [Subgroup.mem_subgroupOf]
      exact hn)
  refine le_antisymm ?_ ?_
  · rintro _ ⟨q, rfl⟩
    obtain ⟨n, hn, hqn⟩ := exists_of_mem_XQ h q.2
    let q' : ↥(XQ h) := ⟨toXW W n, hmem n hn⟩
    have hq'q : q' = q := Subtype.ext hqn
    rw [← hq'q]
    rw [restrictHom_toXW h (n := n) hn]
    rw [XQ₁]
    refine Subgroup.mem_map_of_mem (MulAut.congr (eA h)).toMonoidHom ?_
    exact (toAutImage ⟨(n : G), hn⟩).2
  · rintro _ hg
    rw [XQ₁, Subgroup.mem_map] at hg
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    obtain ⟨x, hx⟩ := toAutImage_surjective (L := L) (A := A) ⟨g₀, hg₀⟩
    have hx' : (toAutImage x : MulAut A) = g₀ := congrArg Subtype.val hx
    rw [← hx']
    refine ⟨⟨toXW W ⟨(x : G), h.le_normalizer x.2⟩, hmem _ x.2⟩, ?_⟩
    exact restrictHom_toXW h (n := ⟨(x : G), h.le_normalizer x.2⟩) x.2

private noncomputable def resEquiv (h : WHyp G L A T z t W W₁ W₂) :
    ↥(XQ h) ≃* ↥(XQ₁ h) :=
  (MulEquiv.ofBijective (restrictHom h).rangeRestrict
    ⟨fun a b hab => restrictHom_injective h (congrArg Subtype.val hab),
      MonoidHom.rangeRestrict_surjective _⟩).trans
    (MulEquiv.subgroupCongr (restrictHom_range h))

private theorem resEquiv_apply (h : WHyp G L A T z t W W₁ W₂) (q : ↥(XQ h))
    (v : ↥(W₁.subgroupOf W)) :
    (((resEquiv h q : MulAut ↥(W₁.subgroupOf W)) v : ↥(W₁.subgroupOf W)) : ↥W) =
      (q : MulAut ↥W) v := by
  rw [resEquiv]
  rfl

private theorem zX_mul_self (h : WHyp G L A T z t W W₁ W₂) :
    toXW W ⟨z, h.z_mem_normalizer⟩ * toXW W ⟨z, h.z_mem_normalizer⟩ = 1 := by
  rw [← map_mul]
  have hzz : (⟨z, h.z_mem_normalizer⟩ : ↥(normalizer (W : Set G))) *
      ⟨z, h.z_mem_normalizer⟩ = 1 := by
    apply Subtype.ext
    simpa using h.hyp.z_sq
  rw [hzz, map_one]

private theorem toXW_eq_zpow_of_mem_R₀ (h : WHyp G L A T z t W W₁ W₂) {r : G}
    (hr : r ∈ R₀ A z) :
    ∃ j : ℤ, toXW W ⟨r, h.e3.M_le hr.1⟩ =
      (toXW W ⟨z, h.z_mem_normalizer⟩) ^ j := by
  have hcoe : (↑(W ⊔ zpowers z) : Set G) = (W : Set G) * (zpowers z : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left W (zpowers z)
      (zpowers_le.2 h.z_mem_normalizer)
  have hr' : r ∈ (W : Set G) * (zpowers z : Set G) := by
    rw [← hcoe, ← h.R₀_eq]
    exact hr
  rw [Set.mem_mul] at hr'
  obtain ⟨v, hvW, w, hwz, hvw⟩ := hr'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hwz
  have hvN : v ∈ normalizer (W : Set G) := h.e3.M_le (h.e3.le_R₀ hvW).1
  refine ⟨j, ?_⟩
  have hdecomp : (⟨r, h.e3.M_le hr.1⟩ : ↥(normalizer (W : Set G))) =
      ⟨v, hvN⟩ * ⟨z, h.z_mem_normalizer⟩ ^ j := by
    apply Subtype.ext
    simpa using hvw.symm
  rw [hdecomp, map_mul, map_zpow]
  have hv1 : toXW W ⟨v, hvN⟩ = 1 := by
    apply Subtype.ext
    ext x
    rw [coe_toXW_apply]
    haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
    have hcomm : v * (x : G) = (x : G) * v :=
      congrArg Subtype.val (mul_comm' (⟨v, hvW⟩ : ↥W) x)
    rw [hcomm]
    group
    simp
  rw [hv1, one_mul]

private theorem toXW_mem_sup_of_mem_M (h : WHyp G L A T z t W W₁ W₂) {m : G}
    (hmM : m ∈ M A z) :
    toXW W ⟨m, h.e3.M_le hmM⟩ ∈
      zpowers (toXW W ⟨z, h.z_mem_normalizer⟩) ⊔ XQ h := by
  obtain ⟨r, hrR, y, hyLN, hmry⟩ := h.hyp.exists_mul_of_mem_M h.e2 hmM
  have hrN : r ∈ normalizer (W : Set G) := h.e3.M_le hrR.1
  have hyN : y ∈ normalizer (W : Set G) := h.le_normalizer hyLN
  have hdec : (⟨m, h.e3.M_le hmM⟩ : ↥(normalizer (W : Set G))) = ⟨r, hrN⟩ * ⟨y, hyN⟩ := by
    apply Subtype.ext
    simpa using hmry
  have hpow : toXW W ⟨r, hrN⟩ ∈ zpowers (toXW W ⟨z, h.z_mem_normalizer⟩) := by
    obtain ⟨j, hj⟩ := toXW_eq_zpow_of_mem_R₀ h hrR
    exact Subgroup.mem_zpowers_iff.2 ⟨j, hj.symm⟩
  have hq : toXW W ⟨y, hyN⟩ ∈ XQ h := by
    change toXW W ⟨y, hyN⟩ ∈
      ((L ⊓ normalizer (A : Set G)).subgroupOf (normalizer (W : Set G))).map (toXW W)
    exact Subgroup.mem_map_of_mem (toXW W) (by
      rw [Subgroup.mem_subgroupOf]
      exact hyLN)
  rw [hdec, map_mul]
  exact mul_mem_sup hpow hq

private theorem XQ_le_centralizer (h : WHyp G L A T z t W W₁ W₂) :
    XQ h ≤ centralizer ({toXW W ⟨z, h.z_mem_normalizer⟩} : Set ↥(XW W)) := by
  intro q hq
  obtain ⟨n, hn, hqn⟩ := exists_of_mem_XQ h hq
  rw [mem_centralizer_singleton_iff]
  have hcomm : n * ⟨z, h.z_mem_normalizer⟩ = ⟨z, h.z_mem_normalizer⟩ * n := by
    apply Subtype.ext
    exact h.hyp.commute_of_mem hn.1
  rw [← hqn, ← map_mul, ← map_mul, hcomm]

private theorem centralizer_zX (h : WHyp G L A T z t W W₁ W₂) :
    centralizer ({toXW W ⟨z, h.z_mem_normalizer⟩} : Set ↥(XW W)) =
      zpowers (toXW W ⟨z, h.z_mem_normalizer⟩) ⊔ XQ h := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_centralizer_singleton_iff] at hx
    obtain ⟨n, hn, rfl⟩ := toXW_surjective W x
    have hc : ∀ w ∈ W, (n : G) * (z * w * z⁻¹) * (n : G)⁻¹ =
        z * ((n : G) * w * (n : G)⁻¹) * z⁻¹ := by
      intro w hw
      have hx' : ((toXW W n * toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) =
          ((toXW W ⟨z, h.z_mem_normalizer⟩ * toXW W n : ↥(XW W)) : MulAut ↥W) :=
        congrArg Subtype.val hx
      have h1 : ((toXW W n : MulAut ↥W) * (toXW W ⟨z, h.z_mem_normalizer⟩ : MulAut ↥W))
            ⟨w, hw⟩ =
          ((toXW W ⟨z, h.z_mem_normalizer⟩ : MulAut ↥W) * (toXW W n : MulAut ↥W)) ⟨w, hw⟩ := by
        simpa using congrArg (fun f : MulAut ↥W => f ⟨w, hw⟩) hx'
      have h2 := congrArg Subtype.val h1
      simp only [MulAut.mul_apply, coe_toXW_apply] at h2
      simpa using h2
    obtain ⟨m, hmM, hmact⟩ := h.exists_mem_M_of_commute (n := (n : G)) n.2 hc
    have hnm : toXW W n = toXW W ⟨m, h.e3.M_le hmM⟩ := by
      apply Subtype.ext
      ext w
      rw [coe_toXW_apply, coe_toXW_apply]
      exact hmact w w.2
    rw [hnm]
    exact toXW_mem_sup_of_mem_M h hmM
  · rw [sup_le_iff]
    refine ⟨?_, XQ_le_centralizer h⟩
    rw [zpowers_le, mem_centralizer_singleton_iff]

private theorem fixed_zX (h : WHyp G L A T z t W W₁ W₂)
    (H : ∀ x : ↥(XW W), ∀ v : ↥W,
      ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) v = v →
      ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)
        (((x : ↥(XW W)) : MulAut ↥W) v) = ((x : ↥(XW W)) : MulAut ↥W) v) :
    zpowers (toXW W ⟨z, h.z_mem_normalizer⟩) ⊔ XQ h = ⊤ := by
  have hA : ∀ m ∈ normalizer (W : Set G), ∀ a ∈ A, m * a * m⁻¹ ∈ A := by
    intro m hm a ha
    have haW : a ∈ W := h.e3.A_le ha
    have hzfix : ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) ⟨a, haW⟩ =
        ⟨a, haW⟩ := by
      apply Subtype.ext
      rw [coe_toXW_apply]
      have hcomm : z * a = a * z := (h.hyp.commute_of_mem (h.hyp.jc.le ha)).symm
      show z * a * z⁻¹ = a
      rw [hcomm]
      group
    have h1 := H (toXW W ⟨m, hm⟩) ⟨a, haW⟩ hzfix
    have h2 := congrArg Subtype.val h1
    simp only [MulAut.mul_apply, coe_toXW_apply] at h2
    have huW : m * a * m⁻¹ ∈ W := (mem_normalizer_iff.1 hm a).1 haW
    rw [h.mem_A_iff huW]
    calc z * (m * a * m⁻¹) = (z * (m * a * m⁻¹) * z⁻¹) * z := by group
      _ = (m * a * m⁻¹) * z := by rw [h2]
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn, rfl⟩ := toXW_surjective W x
  obtain ⟨m, hmM, hmact⟩ := h.exists_mem_M_of_normalizes hA n.2
  have hnm : toXW W n = toXW W ⟨m, h.e3.M_le hmM⟩ := by
    apply Subtype.ext
    ext w
    rw [coe_toXW_apply, coe_toXW_apply]
    exact hmact w w.2
  rw [hnm]
  exact toXW_mem_sup_of_mem_M h hmM

private theorem zX_apply_mem_W₂ (h : WHyp G L A T z t W W₁ W₂) {v : ↥W}
    (hv : v ∈ W₁.subgroupOf W) :
    ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) v ∈ W₂.subgroupOf W := by
  rw [Subgroup.mem_subgroupOf]
  rw [coe_toXW_apply]
  exact h.w.swap (v : G) (Subgroup.mem_subgroupOf.1 hv)

private theorem zX_apply_mem_W₁_of_mem_W₂ (h : WHyp G L A T z t W W₁ W₂) {v : ↥W}
    (hv : v ∈ W₂.subgroupOf W) :
    ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) v ∈ W₁.subgroupOf W := by
  have hle : (W₁.subgroupOf W).map
        (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)).toMonoidHom ≤
      W₂.subgroupOf W := by
    intro u hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    exact zX_apply_mem_W₂ h hw
  have hcardW₂ : Nat.card ↥(W₂.subgroupOf W) = 2 ^ 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (WHyp.le_W₂ h)).toEquiv, h.w.card₂]
  have hcard : Nat.card ↥((W₁.subgroupOf W).map
        (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)).toMonoidHom) =
      Nat.card ↥(W₂.subgroupOf W) := by
    rw [Subgroup.card_map_of_injective (K := W₁.subgroupOf W)
      (f := MulEquiv.toMonoidHom
        (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)))
      (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)).injective, card_V₁ h, hcardW₂]
  have heq : (W₁.subgroupOf W).map
        (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)).toMonoidHom =
      W₂.subgroupOf W :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  rw [Subgroup.mem_subgroupOf] at hv ⊢
  have hvin : (v : ↥W) ∈ (W₁.subgroupOf W).map
      (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)).toMonoidHom := by
    rw [heq]
    exact hv
  rw [Subgroup.mem_map] at hvin
  obtain ⟨u, hu, hvu⟩ := hvin
  have hz2 : (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)
      (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) u) : ↥W) = u := by
    apply Subtype.ext
    rw [coe_toXW_apply, coe_toXW_apply]
    show z * (z * (u : G) * z⁻¹) * z⁻¹ = (u : G)
    rw [h.hyp.z_inv]
    calc z * (z * (u : G) * z) * z = (z * z) * (u : G) * (z * z) := by group
      _ = (u : G) := by rw [h.hyp.z_sq]; group
  have hzv : (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) v : ↥W) = u := by
    rw [← hvu]
    exact hz2
  rw [hzv]
  exact Subgroup.mem_subgroupOf.1 hu

private theorem swap_zX (h : WHyp G L A T z t W W₁ W₂) :
    ∀ v : ↥W, v ∈ W₁.subgroupOf W ↔
      ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) v ∈ W₂.subgroupOf W := by
  intro v
  constructor
  · exact zX_apply_mem_W₂ h
  · intro hv
    have hmem : ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)
        (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) v) ∈ W₁.subgroupOf W :=
      zX_apply_mem_W₁_of_mem_W₂ h hv
    have hvv : ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W)
        (((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) v) = v := by
      apply Subtype.ext
      rw [coe_toXW_apply, coe_toXW_apply]
      show z * (z * (v : G) * z⁻¹) * z⁻¹ = (v : G)
      rw [h.hyp.z_inv]
      calc z * (z * (v : G) * z) * z = (z * z) * (v : G) * (z * z) := by group
        _ = (v : G) := by rw [h.hyp.z_sq]; group
    rw [← hvv]
    exact hmem

private theorem inf_V₁_V₂ (h : WHyp G L A T z t W W₁ W₂) :
    (W₁.subgroupOf W) ⊓ (W₂.subgroupOf W) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have h1 : ((v : ↥W) : G) ∈ W₁ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hv).1
  have h2 : ((v : ↥W) : G) ∈ W₂ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hv).2
  have h3 : ((v : ↥W) : G) ∈ W₁ ⊓ W₂ := ⟨h1, h2⟩
  rw [h.w.inf_eq_bot] at h3
  simpa using h3

private theorem sup_V₁_V₂ (h : WHyp G L A T z t W W₁ W₂) :
    (W₁.subgroupOf W) ⊔ (W₂.subgroupOf W) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup (WHyp.le_W₁ h) (WHyp.le_W₂ h), h.sup_eq,
    Subgroup.subgroupOf_self]

theorem WHyp.exists_xHyp (h : WHyp G L A T z t W W₁ W₂) :
    ∃ (Q : Subgroup ↥(XW W)) (Q₁ : Subgroup (MulAut ↥(W₁.subgroupOf W)))
      (t₁ : ↥(W₁.subgroupOf W)),
      XHyp (XW W).subtype Q (W₁.subgroupOf W) (W₂.subgroupOf W)
        (toXW W ⟨z, h.z_mem_normalizer⟩) Q₁ t₁ := by
  refine ⟨XQ h, XQ₁ h, Xt₁ h, ?_⟩
  exact
    { injective := fun _ _ hxy => Subtype.ext hxy
      elemAb := h.elemAb
      inf_eq_bot := inf_V₁_V₂ h
      sup_eq_top := sup_V₁_V₂ h
      mul_self := zX_mul_self h
      swap := swap_zX h
      centralizer_eq := centralizer_zX h
      res := ⟨resEquiv h, fun q v => resEquiv_apply h q v⟩
      module := module_XQ₁ h
      fixed := fixed_zX h }

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
