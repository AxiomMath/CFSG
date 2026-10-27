module

public import CFSG.GH74.Generic.S3.L3Sylow
public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.GH74.Generic.S3.L3Out
public import CFSG.GH74.Generic.S3.Lem26Z
public import CFSG.GH74.Generic.BarSubnormal

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Fusion

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank Subgroup

structure BarShape (X : Type) [Group X] [Finite X] (xh : X) (Kb : Subgroup X) : Prop where
  xh_sq : xh * xh = 1
  xh_ne : xh ≠ 1
  xh_cent : ∀ g : X, g * xh = xh * g
  normal : Kb.Normal
  quasi : IsQuasisimple ↥Kb
  centerless : center ↥Kb = ⊥
  model : ∃ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) ∧ p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
    LieModel ↥Kb t 3 p f
  only : ∀ u ∈ centralizer (Kb : Set X), orderOf u = 2 → u = xh

variable {X : Type} [Group X] [Finite X] {xh : X} {Kb : Subgroup X}

theorem BarShape.odd_center (h : BarShape X xh Kb) : Odd (Nat.card ↥(center ↥Kb)) := by
  rw [h.centerless, Subgroup.card_bot]
  exact odd_one

theorem BarShape.model_quot (h : BarShape X xh Kb) :
    ∃ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) ∧ p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
      LieModel (↥Kb ⧸ center ↥Kb) t 3 p f := by
  obtain ⟨t, p, f, ht, hp, hp2, h5, hm⟩ := h.model
  exact ⟨t, p, f, ht, hp, hp2, h5, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq h.centerless.symm)) hm⟩

theorem BarShape.xh_notin (h : BarShape X xh Kb) : xh ∉ Kb := fun hx =>
  not_central_involution_of_odd h.odd_center hx h.xh_sq h.xh_ne (fun i _ => h.xh_cent i)

theorem BarShape.exists_conj_invol (h : BarShape X xh Kb) {a b : X} (ha : a ∈ Kb) (hb : b ∈ Kb)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) :
    ∃ g ∈ Kb, g * a * g⁻¹ = b := by
  obtain ⟨t, p, f, ht, hp, hp2, h5, hmod⟩ := h.model_quot
  exact b_L3_class X t p f ht hp hp2 h5 Kb h.quasi h.odd_center hmod a ha b hb ha2 ha1 hb2 hb1

theorem BarShape.exists_sylow (h : BarShape X xh Kb) {y : X} (hy : y ∈ Kb) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) :
    ∃ Q : Sylow 2 X, y ∈ (Q : Subgroup X) ∧ (∀ a ∈ (Q : Subgroup X), a * y = y * a) ∧
      (∀ z ∈ (Q : Subgroup X), (∀ a ∈ (Q : Subgroup X), a * z = z * a) → z * z = 1 →
        z = 1 ∨ z = xh ∨ z = y ∨ z = y * xh) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, p, f, ht, hp, hp2, h5, hmod⟩ := h.model_quot
  obtain ⟨e, heK, he2, he1⟩ := exists_involution_mem_of_quasisimple h.quasi
  obtain ⟨R₁, hR₁, heR₁⟩ := exists_isSylowOf_ge (K := Kb) (P := Subgroup.zpowers e)
    (Subgroup.zpowers_le.mpr heK) (isPGroup_zpowers_of_involution he2)
  have heR₁' : e ∈ R₁ := heR₁ (Subgroup.mem_zpowers e)
  have hR₁ne : R₁ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at heR₁'
    exact he1 heR₁'
  obtain ⟨v, hvR₁, hv2, hv1, hvc⟩ := exists_central_involution hR₁.isPGroup hR₁ne
  have hvK : v ∈ Kb := hR₁.le hvR₁
  obtain ⟨g, hgK, hg⟩ := b_L3_class X t p f ht hp hp2 h5 Kb h.quasi h.odd_center hmod v hvK y hy hv2 hv1
    hy2 hy1
  set R : Subgroup X := R₁.map (MulAut.conj g).toMonoidHom with hRdef
  have hRK : R ≤ Kb := by
    rintro _ ⟨r, hr, rfl⟩
    exact Kb.mul_mem (Kb.mul_mem hgK (hR₁.le hr)) (Kb.inv_mem hgK)
  have hR : IsSylowOf 2 R Kb := by
    refine isSylowOf_of_card hRK ?_
    rw [hRdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hR₁.card_eq]
  have hyR : y ∈ R := ⟨v, hvR₁, by simpa [MulAut.conj_apply] using hg⟩
  have hyRc : ∀ r ∈ R, r * y = y * r := by
    rintro _ ⟨r₀, hr₀, rfl⟩
    have := hvc r₀ hr₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg]
    calc g * r₀ * g⁻¹ * (g * v * g⁻¹) = g * (r₀ * v) * g⁻¹ := by group
      _ = g * (v * r₀) * g⁻¹ := by rw [this]
      _ = g * v * g⁻¹ * (g * r₀ * g⁻¹) := by group
  obtain ⟨Q, hRQ⟩ := hR.isPGroup.exists_le_sylow
  set T : Subgroup X := (Q : Subgroup X) with hTdef
  have hTp : IsPGroup 2 ↥T := Q.isPGroup'
  have hRT : R ≤ T := hRQ
  have hTR : T ⊓ Kb = R := hR.eq_of_le (le_inf hRT hRK) inf_le_right hTp.to_inf_left
  obtain ⟨hcyc, -, -, hksplit⟩ := b_L3_sylow X t p f ht hp hp2 h5 Kb h.quasi h.odd_center hmod R hR
  have hyT : y ∈ T := hRT hyR
  have hyZ : y ∈ R ⊓ centralizer (R : Set X) :=
    ⟨hyR, mem_centralizer_iff.mpr fun r hr => hyRc r hr⟩
  have hyTc : ∀ a ∈ T, a * y = y * a := by
    intro a ha
    have hy' : a * y * a⁻¹ ∈ R := by
      rw [← hTR]
      exact ⟨T.mul_mem (T.mul_mem ha hyT) (T.inv_mem ha), h.normal.conj_mem y hy a⟩
    have hy'c : ∀ r ∈ R, r * (a * y * a⁻¹) = (a * y * a⁻¹) * r := by
      intro r hr
      have hr' : a⁻¹ * r * a ∈ R := by
        rw [← hTR]
        refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ha) (hRT hr)) ha, ?_⟩
        have := h.normal.conj_mem r (hRK hr) a⁻¹
        simpa using this
      have := hyRc _ hr'
      calc r * (a * y * a⁻¹) = a * ((a⁻¹ * r * a) * y) * a⁻¹ := by group
        _ = a * (y * (a⁻¹ * r * a)) * a⁻¹ := by rw [this]
        _ = (a * y * a⁻¹) * r := by group
    have hy'2 : (a * y * a⁻¹) * (a * y * a⁻¹) = 1 := by
      calc (a * y * a⁻¹) * (a * y * a⁻¹) = a * (y * y) * a⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    have hy'1 : a * y * a⁻¹ ≠ 1 := by
      intro h1
      apply hy1
      have : y = a⁻¹ * (a * y * a⁻¹) * a := by group
      rw [this, h1]
      group
    have hZ1 : a * y * a⁻¹ ∈ R ⊓ centralizer (R : Set X) :=
      ⟨hy', mem_centralizer_iff.mpr fun r hr => hy'c r hr⟩
    have heq := eq_of_involutions_of_cyclic hcyc hZ1 hyZ hy'1 hy1 hy'2 hy2
    calc a * y = (a * y * a⁻¹) * a := by group
      _ = y * a := by rw [heq]
  refine ⟨Q, hyT, hyTc, ?_⟩
  intro z hzT hzc hz2
  have hAN : Subgroup.zpowers z ≤ normalizer (Kb : Set X) := by
    rw [normalizer_eq_top_iff.mpr h.normal]
    exact le_top
  have hAcent : ∀ a ∈ Subgroup.zpowers z, ∀ r ∈ R, a * r = r * a := by
    intro a ha r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcomm : Commute z r := (hzc r (hRT hr)).symm
    exact (hcomm.zpow_left k).eq
  obtain ⟨z', hz'R, hcC⟩ := hksplit (Subgroup.zpowers z) hAN
    (isPGroup_zpowers_of_involution hz2) hAcent z (Subgroup.mem_zpowers z)
  have hz'K : z' ∈ Kb := hRK hz'R.1
  set c : X := z * z'⁻¹ with hc
  have hzc' : z = c * z' := by rw [hc]; group
  have hcz' : z' * c = c * z' := mem_centralizer_iff.mp hcC z' hz'K
  have h1 : c * c * (z' * z') = 1 := by
    have hcomm : Commute z' c := hcz'
    have := hcomm.mul_mul_mul_comm c z'
    rw [← this, ← hzc']
    exact hz2
  have hzz' : z' * z' = 1 := by
    have hu : z' * z' = (c * c)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hmem : (⟨z' * z', Kb.mul_mem hz'K hz'K⟩ : ↥Kb) ∈ center ↥Kb := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hcc : (c * c) ∈ centralizer (Kb : Set X) := (centralizer (Kb : Set X)).mul_mem hcC hcC
      have : ((c * c)⁻¹) ∈ centralizer (Kb : Set X) := (centralizer (Kb : Set X)).inv_mem hcc
      rw [← hu] at this
      exact mem_centralizer_iff.mp this g g.2
    have hRz : z' * z' ∈ R := R.mul_mem hz'R.1 hz'R.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR.isPGroup) ⟨z' * z', hRz⟩
    have hk' : orderOf (⟨z' * z', Kb.mul_mem hz'K hz'K⟩ : ↥Kb) = 2 ^ k := by
      rw [← hk, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe (⟨z' * z', hRz⟩ : ↥R)]
    have := eq_one_of_odd_center_of_two_power h.odd_center hmem hk'
    exact congrArg Subtype.val this
  have hcc : c * c = 1 := by rwa [hzz', mul_one] at h1
  have hcx : c = 1 ∨ c = xh := by
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · exact Or.inr (h.only c hcC (orderOf_eq_prime (by rw [sq]; exact hcc) hc1))
  have hz'y : z' = 1 ∨ z' = y := by
    by_cases hz'1 : z' = 1
    · exact Or.inl hz'1
    · exact Or.inr (eq_of_involutions_of_cyclic hcyc hz'R hyZ hz'1 hy1 hzz' hy2)
  rw [hzc']
  rcases hcx with h1 | h1 <;> rcases hz'y with h2 | h2
  · left; rw [h1, h2, mul_one]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2, h.xh_cent y]

theorem BarShape.perfect_le (h : BarShape X xh Kb) {J : Subgroup X} (hJ : Group.IsPerfect ↥J) :
    ∀ j ∈ J, ∃ m ∈ Kb, j * m⁻¹ ∈ centralizer (Kb : Set X) := by
  obtain ⟨t, p, f, ht, hp, hp2, h5, hmod⟩ := h.model_quot
  have : Group.IsPerfect ↥Kb := h.quasi.1
  exact exists_mul_centralizer_of_perfect Kb (perfectInInn_of_lieModel ht h5 hmod)
    (by rw [normalizer_eq_top_iff.mpr h.normal]; exact le_top) hJ

end S3Fusion

end CFSG.GH74.Generic.BProg.B3
