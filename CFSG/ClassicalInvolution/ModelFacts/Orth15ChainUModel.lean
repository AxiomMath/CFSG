module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainU
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame
import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutAmbient
import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTransfer

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped MatrixGroups

namespace ChainU

theorem eq_of_central_ratio {S : Type} [Group S] (B : Subgroup S) [Group.IsPerfect B]
    (α : S →* S) (hcen : ∀ r ∈ B, α r * r⁻¹ ∈ Subgroup.center S) : ∀ r ∈ B, α r = r := by
  let κ : B →* S := MonoidHom.mk' (fun r => α r * (r : S)⁻¹) fun r r' => by
    have h := Subgroup.mem_center_iff.mp (hcen r' r'.2) (r : S)⁻¹
    have e : α (↑(r * r')) * (↑(r * r') : S)⁻¹ = α r * ((α r' * (r' : S)⁻¹) * (r : S)⁻¹) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [e, ← h]
    group
  have hcomm : ∀ a b : κ.range, a * b = b * a := by
    rintro ⟨_, r, rfl⟩ ⟨_, r', rfl⟩
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcen r' r'.2) (κ r)
  have : IsMulCommutative κ.range := ⟨⟨hcomm⟩⟩
  have hperf : Group.IsPerfect κ.range := Group.IsPerfect.range κ
  have hs : Subsingleton κ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  intro r hr
  have h1 : (⟨κ ⟨r, hr⟩, ⟨r, hr⟩, rfl⟩ : κ.range) = 1 := Subsingleton.elim _ _
  have h2 : α r * r⁻¹ = 1 := congrArg Subtype.val h1
  rwa [mul_inv_eq_one] at h2

section SU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem psu3_std (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {H : Type}
    [Group H] (θ : Su K p f 3 →* H) (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {w : H}
    (hw : w ∈ Subgroup.normalizer (θ.range : Set H)) (hw2 : w * w = 1)
    (hwR : ∀ r ∈ rootSU2 K p f (show 2 ≤ 3 by norm_num), w * θ r = θ r * w) :
    (∀ y ∈ θ.range, w * y = y * w) ∨
      (∀ y ∈ θ.range, (w * θ (rootInvSU K p f (show 2 ≤ 3 by norm_num))) * y =
        y * (w * θ (rootInvSU K p f (show 2 ≤ 3 by norm_num)))) := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  let σ : H ≃* H := MulAut.conj w
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    show w * (w * y * w⁻¹) * w⁻¹ = y
    rw [hwinv]
    calc w * (w * y * w) * w = (w * w) * y * (w * w) := by group
      _ = y := by rw [hw2]; group
  have hstab : ∀ x, σ (θ x) ∈ θ.range := fun x =>
    (Subgroup.mem_normalizer_iff.mp hw (θ x)).mp ⟨x, rfl⟩
  obtain ⟨α, g, φ, h1, h2, h3, h4, h5⟩ :=
    unitaryAutClassification_ambient hK hp hq (le_refl 3) θ hker σ hσ hstab
  have hαα : ∀ x, α (α x) = x := fun x => DFunLike.congr_fun h5 x
  have hfix : ∀ r ∈ rootSU2 K p f (show 2 ≤ 3 by norm_num), α r = r := by
    have hcl := isClassicalSL2_rootSU2 hK hp (show 2 ≤ 3 by norm_num)
    have h4F : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) := by
      rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
      omega
    have : Group.IsPerfect (rootSU2 K p f (show 2 ≤ 3 by norm_num)) := hcl.isPerfect h4F
    refine eq_of_central_ratio (rootSU2 K p f (show 2 ≤ 3 by norm_num)) α fun r hr => hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1 r]
    show w * θ r * w⁻¹ * (θ r)⁻¹ = 1
    rw [hwR r hr, mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
  rcases ChainU.su3_fixing hK hp α g φ (fun x => h2 x) h3 h4 hαα hfix with hα1 | hα2
  · left
    intro y hy
    obtain ⟨s, rfl⟩ := hy
    have h' : θ s = w * θ s * w⁻¹ := by
      have := h1 s
      rw [hα1 s] at this
      exact this
    calc w * θ s = (w * θ s * w⁻¹) * w := by group
      _ = θ s * w := by rw [← h']
  · right
    intro y hy
    obtain ⟨s, rfl⟩ := hy
    set X := rootInvSU K p f (show 2 ≤ 3 by norm_num) with hX
    have e1 : w * θ (α s) * w⁻¹ = θ s := by
      have := h1 (α s)
      rw [hαα s] at this
      exact this.symm
    have e2 : w * θ (α s) = θ s * w := by
      calc w * θ (α s) = (w * θ (α s) * w⁻¹) * w := by group
        _ = θ s * w := by rw [e1]
    have e3 : (X * s * X⁻¹) * X = X * s := by group
    calc (w * θ X) * θ s = w * θ (X * s) := by rw [map_mul]; group
      _ = w * θ ((X * s * X⁻¹) * X) := by rw [e3]
      _ = (w * θ (α s)) * θ X := by rw [← hα2 s, map_mul]; group
      _ = θ s * (w * θ X) := by rw [e2]; group

theorem psu3_involution_fund (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {H : Type} [Group H] (θ : Su K p f 3 →* H)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {R : Subgroup (Su K p f 3)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 3 by norm_num))
    {x : Su K p f 3} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) {v : H}
    (hv : v ∈ Subgroup.normalizer (θ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * θ r = θ r * v) :
    (∀ y ∈ θ.range, v * y = y * v) ∨ (∀ y ∈ θ.range, (v * θ x) * y = y * (v * θ x)) := by
  obtain ⟨g, hg⟩ := (mem_longRootSetU_iff (show 2 ≤ 3 by norm_num)).mp hR
  have hθg : θ g ∈ θ.range := ⟨g, rfl⟩
  set w : H := (θ g)⁻¹ * v * θ g with hwdef
  have hw : w ∈ Subgroup.normalizer (θ.range : Set H) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Subgroup.le_normalizer hθg)) hv) (Subgroup.le_normalizer hθg)
  have hw2 : w * w = 1 := by
    calc w * w = (θ g)⁻¹ * (v * v) * θ g := by rw [hwdef]; group
      _ = 1 := by rw [hv2]; group
  have hmemR : ∀ r ∈ rootSU2 K p f (show 2 ≤ 3 by norm_num), g * r * g⁻¹ ∈ R := by
    intro r hr
    rw [hg]
    exact ⟨r, hr, rfl⟩
  have hwR : ∀ r ∈ rootSU2 K p f (show 2 ≤ 3 by norm_num), w * θ r = θ r * w := by
    intro r hr
    have h := hvR _ (hmemR r hr)
    rw [map_mul, map_mul, map_inv] at h
    calc w * θ r = (θ g)⁻¹ * (v * (θ g * θ r * (θ g)⁻¹)) * θ g := by rw [hwdef]; group
      _ = (θ g)⁻¹ * ((θ g * θ r * (θ g)⁻¹) * v) * θ g := by rw [h]
      _ = θ r * w := by rw [hwdef]; group
  obtain ⟨r₀, hr₀, hr₀x⟩ : ∃ r₀ ∈ rootSU2 K p f (show 2 ≤ 3 by norm_num), g * r₀ * g⁻¹ = x := by
    rw [hg] at hxR
    obtain ⟨r₀, hr₀, hr⟩ := hxR
    exact ⟨r₀, hr₀, hr⟩
  have hr₀c : ∀ r ∈ rootSU2 K p f (show 2 ≤ 3 by norm_num), r₀ * r = r * r₀ := by
    intro r hr
    have h := hxc _ (hmemR r hr)
    rw [← hr₀x] at h
    have h' : g * (r₀ * r) * g⁻¹ = g * (r * r₀) * g⁻¹ := by
      calc g * (r₀ * r) * g⁻¹ = g * r₀ * g⁻¹ * (g * r * g⁻¹) := by group
        _ = g * r * g⁻¹ * (g * r₀ * g⁻¹) := h
        _ = g * (r * r₀) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  have hr₀1 : r₀ ≠ 1 := by
    intro h
    apply hx1
    rw [← hr₀x, h]
    group
  have h2F : (2 : CFSG.LieType.Steinberg.fixedSubfield K p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ (odd_natCard_fixedSubfield hK hp)
  have hr₀X : r₀ = rootInvSU K p f (show 2 ≤ 3 by norm_num) :=
    (eq_one_or_eq_of_isClassicalSL2_center h2F
      (isClassicalSL2_rootSU2 hK hp (show 2 ≤ 3 by norm_num)) hr₀ hr₀c).resolve_left hr₀1
  have hxe : x = g * rootInvSU K p f (show 2 ≤ 3 by norm_num) * g⁻¹ := by rw [← hr₀X, hr₀x]
  have hcentral : ∀ w' : H, (∀ y ∈ θ.range, w' * y = y * w') →
      ∀ y ∈ θ.range, (θ g * w' * (θ g)⁻¹) * y = y * (θ g * w' * (θ g)⁻¹) := by
    intro w' hw' y hy
    have hy' : (θ g)⁻¹ * y * θ g ∈ θ.range :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hθg) hy) hθg
    have := hw' _ hy'
    calc θ g * w' * (θ g)⁻¹ * y = θ g * (w' * ((θ g)⁻¹ * y * θ g)) * (θ g)⁻¹ := by group
      _ = θ g * (((θ g)⁻¹ * y * θ g) * w') * (θ g)⁻¹ := by rw [this]
      _ = y * (θ g * w' * (θ g)⁻¹) := by group
  rcases psu3_std hK hp hq θ hker hw hw2 hwR with h | h
  · left
    have := hcentral w h
    have e : θ g * w * (θ g)⁻¹ = v := by rw [hwdef]; group
    rwa [e] at this
  · right
    have := hcentral (w * θ (rootInvSU K p f (show 2 ≤ 3 by norm_num))) h
    have e : θ g * (w * θ (rootInvSU K p f (show 2 ≤ 3 by norm_num))) * (θ g)⁻¹ = v * θ x := by
      rw [hxe, map_mul, map_mul, map_inv, hwdef]
      group
    rwa [e] at this

end SU

end ChainU

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank in
theorem psu3_model_involution_fund {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ}
    (hq : 5 ≤ p ^ e) (hadm : StatedLieAdmissible .PSU 3 p e) {H : Type} [Group H]
    (ψ : (modelUniv .PSU 3 p e Fact.out).K →* H)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .PSU 3 p e Fact.out).K)
    {R : Subgroup (modelUniv .PSU 3 p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 3 p e Fact.out).D)
    {x : (modelUniv .PSU 3 p e Fact.out).K} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x)
    (hx1 : x ≠ 1) {v : H} (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * ψ r = ψ r * v) :
    (∀ y ∈ ψ.range, v * y = y * v) ∨ (∀ y ∈ ψ.range, (v * ψ x) * y = y * (v * ψ x)) := by
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ : ∃ φ : (modelUniv .PSU 3 p e Fact.out).K ≃* Su (GaloisField p (2 * e)) p e 3,
      ∀ R : Subgroup (modelUniv .PSU 3 p e Fact.out).K,
        R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 3 p e Fact.out).D ↔
          R.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * e)) (p := p) (f := e)
            (show 2 ≤ 3 by norm_num) :=
    CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  obtain ⟨θ, hθdef⟩ : ∃ θ : Su (GaloisField p (2 * e)) p e 3 →* H,
      θ = ψ.comp φ.symm.toMonoidHom := ⟨_, rfl⟩
  have hθφ : ∀ r, θ (φ r) = ψ r := fun r => by
    rw [hθdef]
    show ψ (φ.symm (φ r)) = ψ r
    rw [MulEquiv.symm_apply_apply]
  have hθker : θ.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e 3) := by
    intro y hy
    have h1 : φ.symm y ∈ Subgroup.center (modelUniv .PSU 3 p e Fact.out).K := by
      apply hker
      rw [MonoidHom.mem_ker]
      have := MonoidHom.mem_ker.mp hy
      rw [hθdef] at this
      exact this
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro z
    apply φ.symm.injective
    rw [map_mul, map_mul]
    exact h1 (φ.symm z)
  have hθrange : θ.range = ψ.range := by
    rw [hθdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr φ.symm.surjective,
      ← MonoidHom.range_eq_map]
  have hxc' : ∀ r' ∈ R.map φ.toMonoidHom, φ x * r' = r' * φ x := by
    rintro _ ⟨r, hr, rfl⟩
    show φ x * φ r = φ r * φ x
    rw [← map_mul, ← map_mul, hxc r hr]
  have := ChainU.psu3_involution_fund hK hp2 hq θ hθker ((hφ R).mp hR)
    (x := φ x) ⟨x, hxR, rfl⟩ hxc' (fun h => hx1 (φ.injective (by rw [h, map_one])))
    (v := v) (by rw [hθrange]; exact hv) hv2 (by
      rintro _ ⟨r, hr, rfl⟩
      show v * θ (φ r) = θ (φ r) * v
      rw [hθφ]
      exact hvR r hr)
  rw [hθrange, hθφ] at this
  exact this

end CFSG.ClassicalInvolution.ModelFacts.Orth15
