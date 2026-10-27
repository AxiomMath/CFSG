module

public import CFSG.ClassicalInvolution.Asc77.AscT3VBase
import CFSG.ClassicalInvolution.Asc77.AscT3VHexYEng
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate8A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement Pointwise

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


private theorem Std20.late_toG (d : Std20 p f K K' J S R R' W V z t) :
    Std20G K K' J S R R' W V z t :=
  { toStd20F :=
      { d with
        hyp := d.late_hΩ
        late_ne_inv := d.late_ne_inv
        late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.branch.odd d.hyp d.viol.star d.viol.hzJ
        late_card2 := fun hU hK hR =>
          Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hU hK hR }
    late_hWc := d.late_hWc
    late_t_mem_W := d.late_t_mem_W
    late_z_mem_W := d.late_z_mem_W
    late_hW := d.late_hW
    late_JW := d.late_JW
    late_exists_swap := d.late_exists_swap
    late_swap_data := fun hu huK => d.late_swap_data hu huK }

theorem Std20.v_hexY (d : Std20 p f K K' J S R R' W V z t) :
    ∃ X : Subgroup G, X = (J ⊓ Subgroup.normalizer (K : Set G)) ⊔
        (K ⊓ Subgroup.normalizer (J : Set G)) ∧
      X ≤ pairNormalizers K J z t ∧
      pairNormalizers K J z t ≤ Subgroup.normalizer (X : Set G) ∧
      X = oddCoreOf X ⊔ W ∧
      pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) ≤ X ∧
      (∃ r ∈ K ⊓ (S : Subgroup G), ∃ r' ∈ K' ⊓ (S : Subgroup G),
        r ∈ pairNormalizers K J z t ∧ r' ∈ pairNormalizers K J z t ∧ r * t * r⁻¹ = z * t ∧
        (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧
        pairNormalizers K J z t ⊓ Subgroup.centralizer
            ((Subgroup.closure {z, t} : Subgroup G) : Set G) = X ⊔ Subgroup.zpowers (r * r')) ∧
      ∃ φ : ↥(pairNormalizers K J z t) →* DihedralGroup 6, Function.Surjective φ ∧
        φ.ker = X.subgroupOf (pairNormalizers K J z t) := by
  exact d.late_toG.v_hexY

omit [Finite G] [Fact p.Prime] in
theorem pairNormalizers_le_normalizer (K J : Subgroup G) (z t : G) :
    pairNormalizers K J z t ≤
      Subgroup.normalizer ((Subgroup.closure {z, t} : Subgroup G) : Set G) :=
  sup_le inf_le_right inf_le_right

omit [Fact p.Prime] in
theorem odd_orderOf_of_mem_oddCoreOf (X : Subgroup G) {q : G} (hq : q ∈ oddCoreOf X) :
    Odd (orderOf q) := by
  have h1 : orderOf (⟨q, hq⟩ : ↥(oddCoreOf X)) ∣ Nat.card ↥(oddCoreOf X) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact (oddCoreOf_odd_natCard X).of_dvd_nat h1

theorem Y_odd_aux {Y X W : Subgroup G} {z t r r' g x : G} (φ : ↥Y →* DihedralGroup 6)
    (hφk : φ.ker = X.subgroupOf Y) (hXY : X ≤ Y) (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (hXeq : X = oddCoreOf X ⊔ W) (hf : Y ⊓ Subgroup.centralizer (W : Set G) ≤ X)
    (hrY : r ∈ Y) (hr'Y : r' ∈ Y) (hinv : ∀ w ∈ W, (r * r') * w * (r * r')⁻¹ = w⁻¹)
    (hcent : Y ⊓ Subgroup.centralizer ((Subgroup.closure {z, t} : Subgroup G) : Set G) =
      X ⊔ Subgroup.zpowers (r * r'))
    (hYZ : Y ≤ Subgroup.normalizer ((Subgroup.closure {z, t} : Subgroup G) : Set G))
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k = 1)
    (hinvol : ∀ w ∈ W, w * w = 1 → w = 1 ∨ w = z ∨ w = t ∨ w = z * t)
    (hzW : z ∈ W) (htW : t ∈ W)
    (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hgz : g * z * g⁻¹ = z)
    (hgt : g * t * g⁻¹ = t) (hxY : x ∈ Y)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hx : Odd (orderOf x)) :
    x⁻¹ * (g * x * g⁻¹) ∈ Y ⊓ Subgroup.centralizer (W : Set G) := by
  have hxZ : x ∈ Subgroup.normalizer (((Subgroup.closure {z, t} : Subgroup G)) : Set G) := hYZ hxY
  have hgx : g * x * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hgY x).mp hxY
  have hyY : x⁻¹ * (g * x * g⁻¹) ∈ Y := Y.mul_mem (Y.inv_mem hxY) hgx
  have hgZ : ∀ c ∈ (Subgroup.closure {z, t} : Subgroup G), g * c * g⁻¹ = c := by
    intro c hc
    have hle : (Subgroup.closure {z, t} : Subgroup G) ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      intro a ha
      rcases ha with rfl | ha
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have : g * a = a * g := by
          calc g * a = (g * a * g⁻¹) * g := by group
            _ = a * g := by rw [hgz]
        exact this.symm
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have : g * a = a * g := by
          calc g * a = (g * a * g⁻¹) * g := by group
            _ = a * g := by rw [hgt]
        exact this.symm
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
    calc g * c * g⁻¹ = c * g * g⁻¹ := by rw [this]
      _ = c := by group
  have hyZ : ∀ c ∈ (Subgroup.closure {z, t} : Subgroup G),
      (x⁻¹ * (g * x * g⁻¹)) * c = c * (x⁻¹ * (g * x * g⁻¹)) := by
    intro c hc
    have hxc : x * c * x⁻¹ ∈ (Subgroup.closure {z, t} : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hxZ c).mp hc
    have h1 : g * (x * c * x⁻¹) * g⁻¹ = x * c * x⁻¹ := hgZ _ hxc
    have h2 : g⁻¹ * c * g = c := by
      have := hgZ c hc
      calc g⁻¹ * c * g = g⁻¹ * (g * c * g⁻¹) * g := by rw [this]
        _ = c := by group
    calc (x⁻¹ * (g * x * g⁻¹)) * c
        = x⁻¹ * (g * (x * (g⁻¹ * c * g) * x⁻¹) * g⁻¹) * (g * x * g⁻¹) := by group
      _ = x⁻¹ * (g * (x * c * x⁻¹) * g⁻¹) * (g * x * g⁻¹) := by rw [h2]
      _ = x⁻¹ * (x * c * x⁻¹) * (g * x * g⁻¹) := by rw [h1]
      _ = c * (x⁻¹ * (g * x * g⁻¹)) := by group
  have hyC : x⁻¹ * (g * x * g⁻¹) ∈
      Subgroup.centralizer (((Subgroup.closure {z, t} : Subgroup G)) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hyZ c hc).symm
  have hyXr : x⁻¹ * (g * x * g⁻¹) ∈ X ⊔ Subgroup.zpowers (r * r') := by
    rw [← hcent]
    exact ⟨hyY, hyC⟩
  have hρ'Y : r * r' ∈ Y := Y.mul_mem hrY hr'Y
  have hρ'N : Subgroup.zpowers (r * r') ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.zpowers_le.mpr hρ'Y).trans hYX
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left X (Subgroup.zpowers (r * r')) hρ'N
  obtain ⟨x₁, hx₁, ρk, hρk, hyeq⟩ : x⁻¹ * (g * x * g⁻¹) ∈
      (X : Set G) * (Subgroup.zpowers (r * r') : Set G) := by
    rw [← hset]
    exact hyXr
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hρk
  have hker : ∀ a : ↥Y, (a : G) ∈ X → φ a = 1 := fun a ha => by
    have : a ∈ φ.ker := by
      rw [hφk]
      exact Subgroup.mem_subgroupOf.mpr ha
    exact MonoidHom.mem_ker.mp this
  set ρh : ↥Y := ⟨r * r', hρ'Y⟩ with hρh
  have hρ2 : φ ρh * φ ρh = 1 := by
    rw [← map_mul]
    refine hker _ ?_
    refine hf ⟨Y.mul_mem hρ'Y hρ'Y, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro w hw
    have e1 : (r * r') * w = w⁻¹ * (r * r') := by
      calc (r * r') * w = ((r * r') * w * (r * r')⁻¹) * (r * r') := by group
        _ = w⁻¹ * (r * r') := by rw [hinv w hw]
    have e2 : (r * r') * w⁻¹ = w * (r * r') := by
      calc (r * r') * w⁻¹ = ((r * r') * w⁻¹ * (r * r')⁻¹) * (r * r') := by group
        _ = w * (r * r') := by rw [hinv w⁻¹ (W.inv_mem hw), inv_inv]
    calc w * ((r * r') * (r * r')) = (w * (r * r')) * (r * r') := by group
      _ = ((r * r') * w⁻¹) * (r * r') := by rw [e2]
      _ = (r * r') * (w⁻¹ * (r * r')) := by group
      _ = (r * r') * ((r * r') * w) := by rw [e1]
      _ = ((r * r') * (r * r')) * w := by group
  set xh : ↥Y := ⟨x, hxY⟩ with hxh
  set gh : ↥Y := ⟨g * x * g⁻¹, hgx⟩ with hgh
  set yh : ↥Y := ⟨x⁻¹ * (g * x * g⁻¹), hyY⟩ with hyh
  have hyx : yh = xh⁻¹ * gh := rfl
  have hyφ : φ yh = φ ρh ^ m := by
    have : yh = (⟨x₁, hXY hx₁⟩ : ↥Y) * ρh ^ m := by
      apply Subtype.ext
      exact hyeq.symm
    rw [this, map_mul, map_zpow, hker _ hx₁, one_mul]
  have hyφ2 : (φ xh)⁻¹ * φ gh * ((φ xh)⁻¹ * φ gh) = 1 := by
    have h1 : (φ xh)⁻¹ * φ gh = φ yh := by rw [hyx, map_mul, map_inv]
    rw [h1, hyφ, ← zpow_add, ← two_mul, zpow_mul, zpow_two, hρ2, one_zpow]
  have hox : Odd (orderOf (φ xh)) := by
    have h1 : orderOf (φ xh) ∣ orderOf xh := orderOf_map_dvd φ xh
    have h2 : orderOf xh = orderOf x := Subgroup.orderOf_mk x hxY
    rw [h2] at h1
    exact hx.of_dvd_nat h1
  have hog : Odd (orderOf (φ gh)) := by
    have h1 : orderOf (φ gh) ∣ orderOf gh := orderOf_map_dvd φ gh
    have h2 : orderOf gh = orderOf (g * x * g⁻¹) := Subgroup.orderOf_mk _ hgx
    have h3 : orderOf (g * x * g⁻¹) = orderOf x := by
      have := MulEquiv.orderOf_eq (MulAut.conj g) x
      simpa [MulAut.conj_apply] using this
    rw [h2, h3] at h1
    exact hx.of_dvd_nat h1
  have heq : φ xh = φ gh := T3V.dihedral6_eq_of_odd hox hog hyφ2
  have hyker : yh ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hyx, map_mul, map_inv, heq, inv_mul_cancel]
  have hyX : x⁻¹ * (g * x * g⁻¹) ∈ X := by
    rw [hφk] at hyker
    exact Subgroup.mem_subgroupOf.mp hyker
  have hWX : W ≤ X := hXeq ▸ le_sup_right
  have hXN : X ≤ Subgroup.normalizer (oddCoreOf X : Set G) := fun a ha =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer ha)
  have hset2 := Subgroup.coe_mul_of_right_le_normalizer_left (oddCoreOf X) W (hWX.trans hXN)
  obtain ⟨q, hq, w, hw, hqw⟩ : x⁻¹ * (g * x * g⁻¹) ∈ (oddCoreOf X : Set G) * (W : Set G) := by
    rw [← hset2, ← hXeq]
    exact hyX
  have hyN : x⁻¹ * (g * x * g⁻¹) ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxW) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgW hxW)
      (Subgroup.inv_mem _ hgW))
  have hqeq : q = (x⁻¹ * (g * x * g⁻¹)) * w⁻¹ := by rw [← hqw]; group
  have hqN : q ∈ Subgroup.normalizer (W : Set G) := by
    rw [hqeq]
    exact Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ (Subgroup.le_normalizer hw))
  have hqodd : Odd (orderOf q) := odd_orderOf_of_mem_oddCoreOf X hq
  have hqfix : ∀ a ∈ W, a * a = 1 → q * a * q⁻¹ = a := by
    intro a ha ha2
    have hZa : a ∈ (Subgroup.closure {z, t} : Subgroup G) := by
      rcases hinvol a ha ha2 with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    have hya : (x⁻¹ * (g * x * g⁻¹)) * a = a * (x⁻¹ * (g * x * g⁻¹)) := hyZ a hZa
    have hwa : w⁻¹ * a = a * w⁻¹ := hWc _ (W.inv_mem hw) a ha
    rw [hqeq]
    calc (x⁻¹ * (g * x * g⁻¹)) * w⁻¹ * a * ((x⁻¹ * (g * x * g⁻¹)) * w⁻¹)⁻¹
        = (x⁻¹ * (g * x * g⁻¹)) * (w⁻¹ * a) * w * (x⁻¹ * (g * x * g⁻¹))⁻¹ := by group
      _ = (x⁻¹ * (g * x * g⁻¹)) * (a * w⁻¹) * w * (x⁻¹ * (g * x * g⁻¹))⁻¹ := by rw [hwa]
      _ = ((x⁻¹ * (g * x * g⁻¹)) * a) * (x⁻¹ * (g * x * g⁻¹))⁻¹ := by group
      _ = a := by rw [hya]; group
  have hqW := T3V.centralizes_of_odd_of_invol hWc hW2 hqN hqodd hqfix
  refine ⟨hyY, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
  have h1 : q * a * q⁻¹ = a := hqW a ha
  have h2 : w * a = a * w := hWc w hw a ha
  have : x⁻¹ * (g * x * g⁻¹) = q * w := hqw.symm
  rw [this]
  calc a * (q * w) = (a * q) * w := by group
    _ = (q * a) * w := by
      have : q * a = a * q := by
        calc q * a = (q * a * q⁻¹) * q := by group
          _ = a * q := by rw [h1]
      rw [this]
    _ = q * (a * w) := by group
    _ = q * (w * a) := by rw [← hWc a ha w hw]
    _ = (q * w) * a := by group

theorem Std20.v_Y_odd (d : Std20 p f K K' J S R R' W V z t) {g x : G}
    (hgY : g ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hgz : g * z * g⁻¹ = z)
    (hgt : g * t * g⁻¹ = t) (hxY : x ∈ pairNormalizers K J z t)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hx : Odd (orderOf x)) :
    x⁻¹ * (g * x * g⁻¹) ∈ pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) := by
  obtain ⟨X, -, hXY, hYX, hXeq, hf, ⟨r, hr, r', hr', hrY, hr'Y, hrt, hinv, hcent⟩, φ, hφs,
    hφk⟩ := d.v_hexY
  refine Y_odd_aux φ hφk hXY hYX hXeq hf hrY hr'Y hinv hcent
    (pairNormalizers_le_normalizer K J z t) d.late_hWc ?_
    (fun w hw w2 => d.late_inv_W w hw w2) d.late_z_mem_W d.late_t_mem_W hgY hgW hgz hgt hxY hxW hx
  intro w hw
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨w, d.hWS hw⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
