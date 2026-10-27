module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxBasic
import CFSG.GF2Type.Aschbacher1976Full.HSEmbedFacts
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourSymplecticFusion
import CFSG.GF2Type.Aschbacher1976Full.WidthForm

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.CruxQuad

open CFSG CFSG.Blueprint Subgroup PartC
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {z : G}

theorem eq_or_eq_mul_z {Z A : Subgroup G} (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) {d e : G} (heF : e ∈ Fz z) (hd2 : d ^ 2 = 1) (he2 : e ^ 2 = 1)
    (hc : e⁻¹ * d ∈ ZF z) : e = d ∨ e = d * z := by
  have hcZ : e⁻¹ * d ∈ Z := (ZF_z hD hz hF2) ▸ hc
  have hcomm : Commute (e⁻¹ * d) e := Width.Z_comm_F hD hcZ heF
  have hd : d = e * (e⁻¹ * d) := by group
  have hc2 : (e⁻¹ * d) ^ 2 = 1 := by
    have h1 : d ^ 2 = e ^ 2 * (e⁻¹ * d) ^ 2 := by
      conv_lhs => rw [hd]
      exact hcomm.symm.mul_pow 2
    rw [hd2, he2, one_mul] at h1
    exact h1.symm
  by_cases hc1 : e⁻¹ * d = 1
  · left
    have : d = e := by rw [hd, hc1, mul_one]
    exact this.symm
  · right
    have hcz : e⁻¹ * d = z := Width.involution_eq hD hz hcZ hc2 hc1
    have hzz : z * z = 1 := by rw [← pow_two]; exact Width.z_sq hz
    have hde : d = e * z := by rw [← hcz]; group
    rw [hde, mul_assoc, hzz, mul_one]

theorem quad_of_package
    (hFinW : CruxFinWStmt) (hset : HSSetting G z) (hti : HSTI z) (hnf : NineFree (Dtil z))
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : LinearMap.BilinForm (ZMod 2) V) (halt : b.IsAlt) (hnd : b.Nondegenerate)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (vec : G → V) (σ : ↥(Hz z) →* (V ≃ₗ[ZMod 2] V))
    (hker : ∀ m : ↥(Hz z), σ m = 1 ↔ (m : G) ∈ Fz z)
    (hmul : ∀ x ∈ Fz z, ∀ y ∈ Fz z, vec (x * y) = vec x + vec y)
    (hbit : ∀ x ∈ Fz z, ∀ y ∈ Fz z, b (vec x) (vec y) = Width.cbit z x y)
    (heq : ∀ x ∈ Fz z, ∀ y ∈ Fz z, vec x = vec y ↔ x⁻¹ * y ∈ ZF z)
    (hact : ∀ (m : ↥(Hz z)), ∀ x ∈ Fz z, σ m (vec x) = vec ((m : G) * x * (m : G)⁻¹))
    (hiso : ∀ (m : ↥(Hz z)) (x y : V), b (σ m x) (σ m y) = b x y) :
    ∃ θ : G → ZMod 2, QuadFun z θ := by
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  obtain ⟨N, hNn, hN9, hfree⟩ := hnf
  let ι : Qbar z →* (V ≃ₗ[ZMod 2] V) :=
    QuotientGroup.lift _ σ (fun m hm => (hker m).mpr (Subgroup.mem_subgroupOf.mp hm))
  have hι : ∀ m : ↥(Hz z), ι (qmk z m) = σ m := fun m => rfl
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨m, rfl⟩ := qmk_surjective z q
    rw [hι] at hq
    exact (qmk_eq_one_iff z m).mpr ((hker m).mp hq)
  have hN'card : Nat.card (N.map ι) = 9 := by
    rw [Subgroup.card_map_of_injective hιinj]
    exact hN9
  have hN'iso : ∀ g ∈ N.map ι, ∀ x y : V, b (g x) (g y) = b x y := by
    rintro g ⟨n, -, rfl⟩ x y
    obtain ⟨m, rfl⟩ := qmk_surjective z n
    rw [hι]
    exact hiso m x y
  obtain ⟨q, -, hqadd, hqinv, hqfree⟩ := hFinW b halt hnd hdim (N.map ι) hN'card hN'iso
  have hvec1 : vec 1 = 0 := by
    have h := hmul 1 (Fz z).one_mem 1 (Fz z).one_mem
    rw [mul_one] at h
    simpa using h
  have hZF : ZF z ≤ Fz z := by
    rw [ZF_z hD hz hF2, ← hD.sup_eq]
    exact le_sup_left
  refine ⟨fun x => q (vec x), ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    show q (vec (x * y)) = q (vec x) + q (vec y) + Width.cbit z x y
    rw [hmul x hx y hy, hqadd, hbit x hx y hy]
  · intro x hx c hc
    show q (vec (x * c)) = q (vec x)
    congr 1
    refine (heq (x * c) ((Fz z).mul_mem hx (hZF hc)) x hx).mpr ?_
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact (ZF z).inv_mem hc
  · intro h hh x hx
    show q (vec (h * x * h⁻¹)) = q (vec x)
    rw [← hact ⟨h, hh⟩ x hx]
    refine hqinv (σ ⟨h, hh⟩) (hiso _) ?_ (vec x)
    rintro _ ⟨n₀, hn₀, rfl⟩
    refine ⟨qmk z ⟨h, hh⟩ * n₀ * (qmk z ⟨h, hh⟩)⁻¹, hNn.conj_mem n₀ hn₀ _, ?_⟩
    rw [map_mul, map_mul, map_inv, hι]
  · intro d hd
    have hdF : d ∈ Fz z := (hti.2 d hd).1
    obtain ⟨-, -, -, hd2, hd1⟩ := ZF_props hD hz hF2 hd.1
    show q (vec d) = 0
    refine hqfree (vec d) ?_ ?_
    · intro h0
      rw [← hvec1] at h0
      have h1 := (heq d hdF 1 (Fz z).one_mem).mp h0
      rw [mul_one] at h1
      have hdZ : d ∈ Z := by
        have := (ZF z).inv_mem h1
        rw [inv_inv, ZF_z hD hz hF2] at this
        exact this
      exact hd.2.1 (Width.involution_eq hD hz hdZ hd2 hd1)
    · rintro _ ⟨n₀, hn₀, rfl⟩ hn1 hnd
      have hn₀1 : n₀ ≠ 1 := fun h => hn1 (by rw [h, map_one])
      obtain ⟨m, rfl⟩ := qmk_surjective z n₀
      rw [hι] at hnd
      have h1 : vec ((m : G) * d * (m : G)⁻¹) = vec d := (hact m d hdF).symm.trans hnd
      have heF : (m : G) * d * (m : G)⁻¹ ∈ Fz z := Width.Fz_conj_mem m.2 hdF
      have he2 : ((m : G) * d * (m : G)⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hd2]
        group
      have hc := (heq _ heF d hdF).mp h1
      have hy : yBar z ((m : G) * d * (m : G)⁻¹) = yBar z d := by
        rcases eq_or_eq_mul_z hD hz hF2 heF hd2 he2 hc with h | h
        · rw [h]
        · rw [h, (yBar_mul_z hD hz hF2 hti hd).2]
      rw [yBar_conj hD hz hF2 hti hd m] at hy
      exact hfree _ hn₀ hn₀1 (yBar z d) ⟨d, hd, rfl⟩ hy

abbrev PC (z : G) : Subgroup ↥(Hz z) := pCore 2 ↥(Hz z)

abbrev VF (z : G) : Type := Additive (↥(PC z) ⧸ Subgroup.center ↥(PC z))

abbrev toG (p : ↥(PC z)) : G := ((p : ↥(Hz z)) : G)

abbrev cls (p : ↥(PC z)) : VF z := Additive.ofMul (QuotientGroup.mk p)

theorem toG_injective : Function.Injective (toG (z := z)) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem toG_mem (hF2 : IsPGroup 2 ↥(Fz z)) (p : ↥(PC z)) : toG p ∈ Fz z := by
  rw [Embed.Fz_eq_inSubgroup_pCore hF2]
  exact ⟨p.1, p.2, rfl⟩

theorem exists_toG (hF2 : IsPGroup 2 ↥(Fz z)) {x : G} (hx : x ∈ Fz z) :
    ∃ p : ↥(PC z), toG p = x := by
  rw [Embed.Fz_eq_inSubgroup_pCore hF2] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨⟨p, hp⟩, rfl⟩

open Classical in
noncomputable def vecF (z x : G) : VF z :=
  if h : ∃ p : ↥(PC z), toG p = x then cls h.choose else 0

theorem vecF_toG (p : ↥(PC z)) : vecF z (toG p) = cls p := by
  have h : ∃ q : ↥(PC z), toG q = toG p := ⟨p, rfl⟩
  rw [vecF, dif_pos h, toG_injective h.choose_spec]

theorem vecF_mul (hF2 : IsPGroup 2 ↥(Fz z)) {x y : G} (hx : x ∈ Fz z) (hy : y ∈ Fz z) :
    vecF z (x * y) = vecF z x + vecF z y := by
  obtain ⟨p, rfl⟩ := exists_toG hF2 hx
  obtain ⟨q, rfl⟩ := exists_toG hF2 hy
  have h : toG p * toG q = toG (p * q) := rfl
  rw [h, vecF_toG, vecF_toG, vecF_toG, cls, cls, cls, QuotientGroup.mk_mul, ofMul_mul]

theorem mem_center_iff {Z A : Subgroup G} (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) (p : ↥(PC z)) :
    p ∈ Subgroup.center ↥(PC z) ↔ toG p ∈ ZF z := by
  rw [ZF_z hD hz hF2]
  constructor
  · intro hp
    refine Width.mem_Z_of_comm hD hz (toG_mem hF2 p) fun a ha => ?_
    have haF : a ∈ Fz z := hD.sup_eq ▸ Subgroup.mem_sup_right ha
    obtain ⟨q, rfl⟩ := exists_toG hF2 haF
    exact (congrArg toG (Subgroup.mem_center_iff.mp hp q)).symm
  · intro hZ
    rw [Subgroup.mem_center_iff]
    intro q
    exact toG_injective (Width.Z_comm_F hD hZ (toG_mem hF2 q)).symm

theorem vecF_eq_iff {Z A : Subgroup G} (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) {x y : G} (hx : x ∈ Fz z) (hy : y ∈ Fz z) :
    vecF z x = vecF z y ↔ x⁻¹ * y ∈ ZF z := by
  obtain ⟨p, rfl⟩ := exists_toG hF2 hx
  obtain ⟨q, rfl⟩ := exists_toG hF2 hy
  have h : (toG p)⁻¹ * toG q = toG (p⁻¹ * q) := rfl
  rw [vecF_toG, vecF_toG, h, ← mem_center_iff hD hz hF2, cls, cls,
    ← QuotientGroup.eq (s := Subgroup.center ↥(PC z)), Additive.ofMul.injective.eq_iff]

section Action

variable [Fact (Nat.Prime 2)] [IsElementaryAbelian 2 (↥(PC z) ⧸ Subgroup.center ↥(PC z))]

theorem vecF_bit (hz : orderOf z = 2) (b : LinearMap.BilinForm (ZMod 2) (VF z))
    (hrule : ∀ x y : ↥(PC z), toG ⁅x, y⁆ = z ^ (b (cls x) (cls y)).val) (p q : ↥(PC z)) :
    b (cls p) (cls q) = Width.cbit z (toG p) (toG q) := by
  have hr := hrule p q
  have hcomm : toG ⁅p, q⁆ = ⁅toG p, toG q⁆ := rfl
  rw [hcomm] at hr
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  rcases Width.zmod2_cases (b (cls p) (cls q)) with h | h
  · rw [h] at hr ⊢
    simp only [ZMod.val_zero, pow_zero] at hr
    simp [Width.cbit, hr]
  · rw [h] at hr ⊢
    have h1 : (1 : ZMod 2).val = 1 := rfl
    rw [h1, pow_one] at hr
    simp [Width.cbit, hr, hz1]

theorem vecF_act (ρ : ↥(Hz z) →* LinearMap.GeneralLinearGroup (ZMod 2) (VF z))
    (hρ : ∀ (h : ↥(Hz z)) (x y : ↥(PC z)), (y : ↥(Hz z)) = h * x * h⁻¹ →
      ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2) (VF z)) : Module.End (ZMod 2) (VF z))
        (cls x) = cls y)
    (hF2 : IsPGroup 2 ↥(Fz z)) (m : ↥(Hz z)) {x : G} (hx : x ∈ Fz z) :
    ((ρ m : LinearMap.GeneralLinearGroup (ZMod 2) (VF z)) : Module.End (ZMod 2) (VF z))
        (vecF z x) = vecF z ((m : G) * x * (m : G)⁻¹) := by
  obtain ⟨p, rfl⟩ := exists_toG hF2 hx
  let q : ↥(PC z) := ⟨m * p * m⁻¹, (pCore_normal : (PC z).Normal).conj_mem p.1 p.2 m⟩
  have h1 := hρ m p q rfl
  have h2 : (m : G) * toG p * (m : G)⁻¹ = toG q := rfl
  rw [h2, vecF_toG, vecF_toG]
  exact h1

end Action

end CFSG.GF2Type.Aschbacher1976Full.HS.CruxQuad

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC CruxQuad
open scoped commutatorElement IsMulCommutative

theorem cruxQuad_holds : CruxQuadStmt := by
  intro hFinW G _ _ z hset hti hnf
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset'
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hvel, -, b, hrule, -, halt, hnd, ρ, hρ, hker, hiso, -, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.SteinbergCH.core_symplectic_transport (B := ⊥) bot_le
      (Embed.isCharacteristicP_Hz hF2) (by simp) (Embed.Fz_eq_inSubgroup_pCore hF2)
      (Embed.isCyclic_center_Fz hD hz hF2) (Width.isEA_quot (Embed.cdata_Fz hD hz))
      (Embed.z_mem_map_center_Fz hD hz hF2) hz (Embed.commutator_Fz hD hz)
  haveI := hvel
  haveI : FiniteDimensional (ZMod 2) (VF z) := Module.Finite.of_finite
  refine quad_of_package hFinW hset hti hnf b halt hnd (Embed.finrank_quot_pCore hD hz hF2)
    (vecF z) ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).toMonoidHom.comp ρ)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro m
    have h1 : ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).toMonoidHom.comp ρ) m =
        1 ↔ ρ m = 1 := by simp
    rw [h1, ← MonoidHom.mem_ker, hker]
    constructor
    · intro hm
      exact toG_mem hF2 ⟨m, hm⟩
    · intro hm
      obtain ⟨p, hp⟩ := exists_toG hF2 hm
      have h2 : p.1 = m := Subtype.ext hp
      rw [← h2]
      exact p.2
  · intro x hx y hy
    exact vecF_mul hF2 hx hy
  · intro x hx y hy
    obtain ⟨p, rfl⟩ := exists_toG hF2 hx
    obtain ⟨q, rfl⟩ := exists_toG hF2 hy
    rw [vecF_toG, vecF_toG]
    exact vecF_bit hz b hrule p q
  · intro x hx y hy
    exact vecF_eq_iff hD hz hF2 hx hy
  · intro m x hx
    exact vecF_act ρ hρ hF2 m hx
  · intro m x y
    exact hiso m x y

end CFSG.GF2Type.Aschbacher1976Full.HS
