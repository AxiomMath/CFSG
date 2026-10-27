module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Clifford
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPCoreCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPSubgroupGLAction

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Signalizer.L53
open scoped commutatorElement IsMulCommutative

section Chief

variable {G : Type} [Group G]

theorem isChiefPair_subgroupOf {H X Y : Subgroup G} (hc : IsChiefFactorIn H X Y) :
    IsChiefPair (X.subgroupOf H) (Y.subgroupOf H) := by
  obtain ⟨hXH, hYX, hXn, hYn, hmin⟩ := hc
  have hYH : Y ≤ H := hYX.le.trans hXH
  have hXhn : (X.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    exact (mem_normalizer_iff.mp (hXn g g.2) (x : G)).mp hx
  have hYhn : (Y.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    exact (mem_normalizer_iff.mp (hYn g g.2) (x : G)).mp hx
  refine ⟨hXhn, hYhn, ?_, ?_⟩
  · refine lt_of_le_of_ne (fun x hx => hYX.le hx) ?_
    intro heq
    obtain ⟨x, hxX, hxY⟩ := IsConcreteLE.exists_of_lt hYX
    have : (⟨x, hXH hxX⟩ : ↥H) ∈ X.subgroupOf H := hxX
    rw [← heq] at this
    exact hxY this
  · intro Z hZn hYZ hZX
    have hZ'mem : ∀ w : G, w ∈ Z.map H.subtype ↔ ∃ hw : w ∈ H, (⟨w, hw⟩ : ↥H) ∈ Z := by
      intro w
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, hz⟩
      · rintro ⟨hw, hz⟩
        exact ⟨⟨w, hw⟩, hz, rfl⟩
    have hYZ' : Y ≤ Z.map H.subtype := fun y hy => (hZ'mem y).mpr ⟨hYH hy, hYZ hy⟩
    have hZ'X : Z.map H.subtype ≤ X := fun w hw => by
      obtain ⟨hwH, hwZ⟩ := (hZ'mem w).mp hw
      exact hZX hwZ
    have hZ'N : ∀ h ∈ H, h ∈ normalizer (Z.map H.subtype : Set G) := by
      intro h hh
      rw [mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        obtain ⟨hwH, hwZ⟩ := (hZ'mem w).mp hw
        refine (hZ'mem _).mpr ⟨H.mul_mem (H.mul_mem hh hwH) (H.inv_mem hh), ?_⟩
        exact hZn.conj_mem ⟨w, hwH⟩ hwZ ⟨h, hh⟩
      · intro hw
        obtain ⟨hwH, hwZ⟩ := (hZ'mem _).mp hw
        have hwH' : w ∈ H := by
          have := H.mul_mem (H.mul_mem (H.inv_mem hh) hwH) hh
          simpa [mul_assoc] using this
        refine (hZ'mem w).mpr ⟨hwH', ?_⟩
        have := hZn.conj_mem _ hwZ (⟨h, hh⟩ : ↥H)⁻¹
        convert this using 1
        apply Subtype.ext
        simp [mul_assoc]
    rcases hmin _ hYZ' hZ'X hZ'N with h | h
    · left
      ext w
      constructor
      · intro hwZ
        have : (w : G) ∈ Z.map H.subtype := (hZ'mem _).mpr ⟨w.2, hwZ⟩
        rw [h] at this
        exact this
      · intro hwY
        have : (w : G) ∈ Z.map H.subtype := by rw [h]; exact hwY
        exact ((hZ'mem _).mp this).2
    · right
      ext w
      constructor
      · intro hwZ
        have : (w : G) ∈ Z.map H.subtype := (hZ'mem _).mpr ⟨w.2, hwZ⟩
        rw [h] at this
        exact this
      · intro hwX
        have : (w : G) ∈ Z.map H.subtype := by rw [h]; exact hwX
        exact ((hZ'mem _).mp this).2

end Chief

section Module

variable {G : Type} [Group G] [Finite G]

theorem chief_module (p : ℕ) [Fact p.Prime] {H X Y : Subgroup G} (hc : IsChiefFactorIn H X Y)
    (hXp : IsPGroup p ↥X) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V)
      (_ : Module (ZMod p) V) (_ : Module.Finite (ZMod p) V)
      (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (π : ↥H →* Γ), Function.Surjective π ∧
      Function.Injective ρ ∧ (∀ N : Subgroup Γ, N.Normal → IsPGroup p ↥N → N = ⊥) ∧
      (∀ h : ↥H, π h = 1 ↔ ∀ x ∈ X, ⁅x, (h : G)⁆ ∈ Y) ∧
      ∀ g : ↥H, (∀ x ∈ X, ⁅⁅x, (g : G)⁆, (g : G)⁆ ∈ Y) →
        (((ρ (π g) : (V →ₗ[ZMod p] V)ˣ) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 := by
  classical
  have hXH : X ≤ H := hc.1
  obtain ⟨hXn, hYn, hYX, hmin⟩ := isChiefPair_subgroupOf hc
  set Xh := X.subgroupOf H with hXh
  set Yh := Y.subgroupOf H with hYh
  have hXhp : IsPGroup p ↥Xh := by
    intro x
    obtain ⟨k, hk⟩ := hXp ⟨(x : G), x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  let π0 : ↥H →* ↥H ⧸ Yh := QuotientGroup.mk' Yh
  have hπ0 : Function.Surjective π0 := QuotientGroup.mk'_surjective Yh
  have hker0 : ∀ x, π0 x = 1 ↔ x ∈ Yh := fun x => QuotientGroup.eq_one_iff x
  set N : Subgroup (↥H ⧸ Yh) := Xh.map π0 with hN
  have hNn : N.Normal := Subgroup.Normal.map hXn π0 hπ0
  have hNmin : IsMinimalNormal N := by
    refine ⟨fun K hKn hKH => ?_⟩
    have hKn' : (K.comap π0).Normal := Subgroup.Normal.comap hKn π0
    have hYK : Yh ≤ K.comap π0 := fun y hy => by
      rw [Subgroup.mem_comap, (hker0 y).mpr hy]
      exact K.one_mem
    have hKX : K.comap π0 ≤ Xh := by
      intro x hx
      have hπx : π0 x ∈ N := hKH hx
      obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp hπx
      have : x'⁻¹ * x ∈ Yh := by
        rw [← hker0, map_mul, map_inv, hxx', inv_mul_cancel]
      have h2 : x = x' * (x'⁻¹ * x) := by group
      rw [h2]
      exact Xh.mul_mem hx' (hYX.le this)
    rcases hmin _ hKn' hYK hKX with h | h
    · left
      rw [eq_bot_iff]
      intro q hq'
      obtain ⟨x, rfl⟩ := hπ0 q
      have : x ∈ K.comap π0 := hq'
      rw [h] at this
      exact (Subgroup.mem_bot).mpr ((hker0 x).mpr this)
    · right
      refine le_antisymm hKH ?_
      intro q hq'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq'
      have : x ∈ K.comap π0 := by rw [h]; exact hx
      exact this
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hYX.not_ge
    intro x hx
    have : π0 x ∈ N := Subgroup.mem_map_of_mem π0 hx
    rw [hbot, Subgroup.mem_bot, hker0] at this
    exact this
  have hNp : IsPGroup p ↥N := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    obtain ⟨k, hk⟩ := hXhp ⟨x, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    show (y : ↥H ⧸ Yh) ^ (p ^ k) = 1
    rw [← hxy, ← map_pow, hk', map_one]
  let _ : IsElementaryAbelian p N :=
    CFSG.Glauberman.minimalNormal_pSubgroup_isElementaryAbelian N hNne hNp
  let _ : IsMulCommutative N := (inferInstance : IsElementaryAbelian p N).toIsMulCommutative
  let _ : Module (ZMod p) (Additive N) := IsElementaryAbelian.isVectorSpace p
  obtain ⟨ρ, hρinj, -, hρeval⟩ :=
    CFSG.Glauberman.exists_minimalNormal_pSubgroup_GL_faithful_irreducible_action
      (p := p) N hNne hNp
  have hopbot := CFSG.Glauberman.pCore_quotient_centralizer_eq_bot_of_minimalNormal_pSubgroup
    (p := p) N hNne hNp
  let π : ↥H →* (↥H ⧸ Yh) ⧸ centralizer (N : Set (↥H ⧸ Yh)) :=
    (QuotientGroup.mk' (centralizer (N : Set (↥H ⧸ Yh)))).comp π0
  have hπsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp hπ0
  refine ⟨(↥H ⧸ Yh) ⧸ centralizer (N : Set (↥H ⧸ Yh)), inferInstance, inferInstance,
    Additive N, inferInstance, inferInstance, inferInstance, ρ, π, hπsurj, hρinj, ?_, ?_, ?_⟩
  · intro M hMn hMp
    have hle : M ≤ pCore p ((↥H ⧸ Yh) ⧸ centralizer (N : Set (↥H ⧸ Yh))) :=
      le_sSup ⟨hMn, hMp⟩
    rw [hopbot] at hle
    exact le_bot_iff.mp hle
  ·
    intro h
    change (QuotientGroup.mk' (centralizer (N : Set (↥H ⧸ Yh))) (π0 h) = 1) ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hcomm x hx
      have hxH : x ∈ H := hXH hx
      have hn : π0 ⟨x, hxH⟩ ∈ N := Subgroup.mem_map_of_mem π0 (show (⟨x, hxH⟩ : ↥H) ∈ Xh from hx)
      have h1 := hcomm _ hn
      have h3 : π0 (⟨x, hxH⟩ * h) = π0 (h * ⟨x, hxH⟩) := by
        rw [map_mul, map_mul]
        exact h1
      have h4 := (QuotientGroup.eq_iff_div_mem).mp h3
      have h5 : ((⟨x, hxH⟩ * h / (h * ⟨x, hxH⟩) : ↥H) : G) = ⁅x, (h : G)⁆ := by
        show x * (h : G) / ((h : G) * x) = ⁅x, (h : G)⁆
        rw [div_eq_mul_inv, mul_inv_rev, commutatorElement_def]
        simp only [mul_assoc]
      have h6 : ((⟨x, hxH⟩ * h / (h * ⟨x, hxH⟩) : ↥H) : G) ∈ Y := h4
      rw [h5] at h6
      exact h6
    · intro hx n hn
      obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hn
      have hxX' : (x : G) ∈ X := hxX
      have h1 := hx (x : G) hxX'
      have h5 : ((x * h / (h * x) : ↥H) : G) = ⁅(x : G), (h : G)⁆ := by
        show (x : G) * (h : G) / ((h : G) * (x : G)) = ⁅(x : G), (h : G)⁆
        rw [div_eq_mul_inv, mul_inv_rev, commutatorElement_def]
        simp only [mul_assoc]
      have h6 : x * h / (h * x) ∈ Yh := by
        show ((x * h / (h * x) : ↥H) : G) ∈ Y
        rw [h5]
        exact h1
      rw [← map_mul, ← map_mul]
      exact (QuotientGroup.eq_iff_div_mem).mpr h6
  ·
    intro g hq
    let ρ' : (↥H ⧸ Yh) →* Module.End (ZMod p) (Additive N) :=
      (Units.coeHom (Module.End (ZMod p) (Additive N))).comp
        (ρ.comp (QuotientGroup.mk' (centralizer (N : Set (↥H ⧸ Yh)))))
    have hev : ∀ (q : ↥H ⧸ Yh) (n : N),
        ρ' q (Additive.ofMul n) = Additive.ofMul (MulAut.conjNormal (H := N) q n) := by
      intro q n
      apply Additive.toMul.injective
      exact hρeval q (Additive.ofMul n)
    let cm : (↥H ⧸ Yh) → N → N := fun q n =>
      ⟨⁅q, (n : ↥H ⧸ Yh)⁆, by
        have e : ⁅q, (n : ↥H ⧸ Yh)⁆ = (q * (n : ↥H ⧸ Yh) * q⁻¹) * (n : ↥H ⧸ Yh)⁻¹ := by
          simp only [commutatorElement_def]
        rw [e]
        exact N.mul_mem (Normal.conj_mem inferInstance _ n.2 q) (N.inv_mem n.2)⟩
    have hcm : ∀ (q : ↥H ⧸ Yh) (n : N),
        (ρ' q - 1) (Additive.ofMul n) = Additive.ofMul (cm q n) := by
      intro q n
      rw [LinearMap.sub_apply, hev, Module.End.one_apply, ← ofMul_div]
      congr 1
      apply Subtype.ext
      have h1 : ((MulAut.conjNormal (H := N) q n : N) : ↥H ⧸ Yh) = q * (n : ↥H ⧸ Yh) * q⁻¹ :=
        MulAut.conjNormal_apply q n
      show ((MulAut.conjNormal (H := N) q n / n : N) : ↥H ⧸ Yh) = ⁅q, (n : ↥H ⧸ Yh)⁆
      rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, h1, commutatorElement_def]
    have hquad : ∀ q : ↥H ⧸ Yh, (∀ v ∈ N, ⁅q, ⁅q, v⁆⁆ = 1) → (ρ' q - 1) * (ρ' q - 1) = 0 := by
      intro q hq'
      ext v
      obtain ⟨n, rfl⟩ := Additive.ofMul.surjective v
      simp only [Module.End.mul_apply, LinearMap.zero_apply]
      rw [hcm, hcm]
      have : cm q (cm q n) = 1 := by
        apply Subtype.ext
        exact hq' (n : ↥H ⧸ Yh) n.2
      rw [this]
      rfl
    have hq' : ∀ v ∈ N, ⁅π0 g, ⁅π0 g, v⁆⁆ = 1 := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
      rw [← map_commutatorElement, ← map_commutatorElement, hker0]
      have h1 : (⁅x, g⁆ : ↥H) ∈ phiSub Yh hYn g := by
        show ((⁅⁅x, g⁆, g⁆ : ↥H) : G) ∈ Y
        exact hq (x : G) hx
      have h2 : (⁅x, g⁆ : ↥H)⁻¹ ∈ phiSub Yh hYn g := (phiSub Yh hYn g).inv_mem h1
      have h3 : ⁅(⁅x, g⁆ : ↥H)⁻¹, g⁆ ∈ Yh := h2
      have e : ⁅g, ⁅g, x⁆⁆ = ⁅⁅x, g⁆⁻¹, g⁆⁻¹ := by
        rw [commutatorElement_inv x g, commutatorElement_inv]
      rw [e]
      exact Yh.inv_mem h3
    rw [sq]
    exact hquad (π0 g) hq'

end Module

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
