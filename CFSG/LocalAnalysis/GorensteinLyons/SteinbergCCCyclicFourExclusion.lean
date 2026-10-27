module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticCentralProduct
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLOrderFourCompression

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Module
open scoped commutatorElement IsMulCommutative
open LinearMap (BilinForm)

namespace CyclicFourExclusion

theorem pow_four_conj_eq {Q : Type*} [Group Q] (cj : Q →* Q) {x d₁ d₂ d₃ z : Q}
    (hz : z ∈ center Q) (hzz : z * z = 1) (hc1 : cj x = x * d₁) (hc2 : cj d₁ = d₁ * d₂)
    (hc3 : cj d₂ = d₂ * d₃) (hc4 : cj d₃ = d₃) (h12 : d₂ * d₁ = d₁ * d₂ * z)
    (h23 : d₂ * d₃ = d₃ * d₂) (hs1 : d₁ * d₁ ∈ center Q) (hs1f : cj (d₁ * d₁) = d₁ * d₁)
    (hs1o : d₁ * d₁ * (d₁ * d₁) = 1) (hs2f : cj (d₂ * d₂) = d₂ * d₂) :
    cj (cj (cj (cj x))) = x * z := by
  have hzc := mem_center_iff.mp hz
  have hs1c := mem_center_iff.mp hs1
  have hd2sq : d₂ * d₂ = z := by
    have h1 : cj (d₁ * d₁) = d₁ * d₁ * (d₂ * d₂ * z) := by
      rw [map_mul, hc2]
      calc d₁ * d₂ * (d₁ * d₂) = d₁ * (d₂ * d₁) * d₂ := by group
        _ = d₁ * (d₁ * d₂ * z) * d₂ := by rw [h12]
        _ = d₁ * d₁ * (d₂ * (z * d₂)) := by group
        _ = d₁ * d₁ * (d₂ * (d₂ * z)) := by rw [← hzc d₂]
        _ = d₁ * d₁ * (d₂ * d₂ * z) := by group
    rw [hs1f] at h1
    have h2 : d₂ * d₂ * z = 1 := mul_left_cancel (h1.symm.trans (mul_one _).symm)
    calc d₂ * d₂ = d₂ * d₂ * z * z := by rw [mul_assoc (d₂ * d₂), hzz, mul_one]
      _ = z := by rw [h2, one_mul]
  have hd3sq : d₃ * d₃ = 1 := by
    have h1 : cj (d₂ * d₂) = d₂ * d₂ * (d₃ * d₃) := by
      rw [map_mul, hc3]
      calc d₂ * d₃ * (d₂ * d₃) = d₂ * (d₃ * d₂) * d₃ := by group
        _ = d₂ * (d₂ * d₃) * d₃ := by rw [← h23]
        _ = d₂ * d₂ * (d₃ * d₃) := by group
    rw [hs2f] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
  have e2 : cj (cj x) = x * (d₁ * d₁) * d₂ := by
    rw [hc1, map_mul, hc1, hc2]
    group
  have e3 : cj (cj (cj x)) = x * d₁ * (d₁ * d₁) * (d₂ * d₃) := by
    rw [e2, map_mul, map_mul, hc1, hs1f, hc3]
  have e4 : cj (cj (cj (cj x))) = x * d₁ * (d₁ * d₂) * (d₁ * d₁) * (d₂ * d₃) * d₃ := by
    rw [e3, map_mul, map_mul, map_mul, hc1, hc2, hs1f, map_mul, hc3, hc4]
    group
  rw [e4]
  calc x * d₁ * (d₁ * d₂) * (d₁ * d₁) * (d₂ * d₃) * d₃
      = x * (d₁ * d₁) * (d₂ * (d₁ * d₁)) * d₂ * (d₃ * d₃) := by group
    _ = x * (d₁ * d₁) * ((d₁ * d₁) * d₂) * d₂ * (d₃ * d₃) := by rw [hs1c d₂]
    _ = x * (d₁ * d₁ * (d₁ * d₁)) * (d₂ * d₂) * (d₃ * d₃) := by group
    _ = x * z := by simp only [hs1o, hd2sq, hd3sq, mul_one]

end CyclicFourExclusion

open CyclicFourExclusion in
theorem cyclic_four_normalizer_excludes_order_four_central_quotient_action
    {G : Type*} [Group G] [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hZ : IsCyclic (center Q)) {z : Q} (hz : orderOf z = 2)
    (hΦ : frattini Q = zpowers z) (hQ' : commutator Q = zpowers z)
    [IsElementaryAbelian 2 (Q ⧸ center Q)]
    {t : G} (htN : t ∈ normalizer (Q : Set G)) (ht4 : orderOf t = 4)
    (htZ : ∀ c : Q, c ∈ center Q → t * (c : G) * t⁻¹ = c)
    (haQ : t ^ 2 ∉ Q) (hN : normalizer (zpowers t : Set G) = centralizer {t ^ 2})
    (T : Module.End (ZMod 2) (Additive (Q ⧸ center Q)))
    (hT : ∀ y y' : Q, (y' : G) = t * y * t⁻¹ →
      T (Additive.ofMul (y : Q ⧸ center Q)) = Additive.ofMul (y' : Q ⧸ center Q)) :
    Q ⊓ centralizer {t ^ 2} = Q ⊓ centralizer {t} ∧
    (∀ v, T v = v ↔ ∃ y : Q, (y : G) * t = t * y ∧ v = Additive.ofMul (y : Q ⧸ center Q)) ∧
    T * T = 1 ∧ finrank (ZMod 2) (LinearMap.range (T - 1)) ≤ 1 ∧ orderOf T ≠ 4 := by
  classical
  have hQf : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have ht2 : t ^ 2 = t * t := pow_two t
  rw [ht2] at haQ hN ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hpair : ∀ x : Q, x ∈ zpowers z → x = 1 ∨ x = z := fun x hx =>
    eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz hx
  have hzZ : z ∈ center Q := by
    rw [mem_center_iff]
    intro g
    have hmem : g * z * g⁻¹ ∈ zpowers z := by
      rw [← hΦ]
      exact (inferInstance : (frattini Q).Normal).conj_mem _ (hΦ ▸ mem_zpowers z) g
    rcases hpair _ hmem with h | h
    · exfalso
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h]
  have hzle : zpowers z ≤ center Q := zpowers_le.mpr hzZ
  have hsqz : ∀ a : Q, a * a ∈ zpowers z := fun a => by
    rw [← pow_two, ← hΦ]
    exact CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) a
  have hC : CommPairHyp Q z :=
    { mem_center := hzZ
      orderOf_eq := hz
      comm_pair := fun a b => hpair _
        (hQ' ▸ Subgroup.commutator_mem_commutator (mem_top a) (mem_top b))
      sq_mem_center := fun a => hzle (by rw [pow_two]; exact hsqz a) }
  set π : Q → Additive (Q ⧸ center Q) := fun y => Additive.ofMul (y : Q ⧸ center Q) with hπdef
  have hπmul : ∀ x y : Q, π (x * y) = π x + π y := fun x y => by
    simp only [hπdef, QuotientGroup.mk_mul, ofMul_mul]
  have hπzero : ∀ y : Q, π y = 0 ↔ y ∈ center Q := fun y => by
    simp only [hπdef]
    rw [← ofMul_one, Additive.ofMul.apply_eq_iff_eq, QuotientGroup.eq_one_iff]
  have hπinv : ∀ y : Q, π y⁻¹ = -π y := fun y => by
    simp only [hπdef, QuotientGroup.mk_inv, ofMul_inv]
  have hπsurj : ∀ v, ∃ y : Q, π y = v := fun v => by
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    refine ⟨y, ?_⟩
    simp only [hπdef]
    rw [hy]
    rfl
  have htmem : ∀ y : Q, t * (y : G) * t⁻¹ ∈ Q := fun y =>
    (mem_normalizer_iff.mp htN y).mp y.2
  let cj : Q →* Q :=
    { toFun := fun y => ⟨t * (y : G) * t⁻¹, htmem y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcj : ∀ y : Q, (cj y : G) = t * y * t⁻¹ := fun y => rfl
  have hTcj : ∀ y : Q, T (π y) = π (cj y) := fun y => hT y (cj y) rfl
  have hcjZ : ∀ c : Q, c ∈ center Q → cj c = c := fun c hc => Subtype.ext (htZ c hc)
  have h4 : t ^ 4 = 1 := by
    rw [← ht4]
    exact pow_orderOf_eq_one t
  have ht4' : t * t * (t * t) = 1 := by
    rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hcj4 : ∀ y : Q, cj (cj (cj (cj y))) = y := by
    intro y
    apply Subtype.ext
    simp only [hcj]
    calc t * (t * (t * (t * (y : G) * t⁻¹) * t⁻¹) * t⁻¹) * t⁻¹ =
        (t * t * (t * t)) * y * (t * t * (t * t))⁻¹ := by group
      _ = y := by rw [ht4']; group
  have hcj2 : ∀ y : Q, (cj (cj y) : G) = t * t * y * (t * t)⁻¹ := fun y => by
    simp only [hcj]
    group
  set b := hC.commForm with hbdef
  have hbapp : ∀ x y : Q, b (π x) (π y) = zlog z ⁅x, y⁆ := fun x y => by
    rw [hbdef, CommPairHyp.commForm_apply]
    exact hC.commVal_mk x y
  have hbiso : ∀ u v, b (T u) (T v) = b u v := by
    intro u v
    obtain ⟨x, rfl⟩ := hπsurj u
    obtain ⟨y, rfl⟩ := hπsurj v
    rw [hTcj, hTcj, hbapp, hbapp, ← map_commutatorElement]
    rcases hC.comm_pair x y with h | h
    · rw [h, map_one]
    · rw [h, hcjZ z hzZ]
  have hCa : ∀ q : Q, (q : G) * (t * t) = t * t * q → (q : G) * t = t * q := by
    intro q hq
    have hqN : (q : G) ∈ normalizer (zpowers t : Set G) := by
      rw [hN, mem_centralizer_singleton_iff]
      exact hq
    have h1 : (q : G) * t * (q : G)⁻¹ ∈ zpowers t :=
      (mem_normalizer_iff.mp hqN t).mp (mem_zpowers t)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    have hord : orderOf ((q : G) * t * (q : G)⁻¹) = 4 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht4]
    have hkmod := zpow_mod_orderOf t k
    rw [ht4] at hkmod
    push_cast at hkmod
    rw [hk] at hkmod
    have hk0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
    have hk3 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
    interval_cases hkk : k % 4
    · exfalso
      rw [zpow_zero] at hkmod
      rw [← hkmod, orderOf_one] at hord
      norm_num at hord
    · rw [zpow_one] at hkmod
      calc (q : G) * t = (q : G) * t * (q : G)⁻¹ * q := by group
        _ = t * q := by rw [← hkmod]
    · exfalso
      have h2 : (t * t) * (t * t) = 1 := ht4'
      have h3 : t ^ (2 : ℤ) = t * t := by
        rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
      rw [h3] at hkmod
      rw [← hkmod] at hord
      have := orderOf_dvd_of_pow_eq_one (show (t * t) ^ 2 = 1 by rw [pow_two]; exact h2)
      rw [hord] at this
      norm_num at this
    · exfalso
      have h3 : t ^ (3 : ℤ) = t⁻¹ := by
        have h4 : t ^ (3 : ℤ) * t = 1 := by
          rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
          calc t ^ 3 * t = t * t * (t * t) := by
                simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = 1 := ht4'
        exact eq_inv_of_mul_eq_one_left h4
      rw [h3] at hkmod
      apply haQ
      have h5 : t⁻¹ * (q : G) * t ∈ Q := by
        have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) q).mp q.2
        simpa using this
      have h6 : t⁻¹ * ((q : G) * t * (q : G)⁻¹) ∈ Q := by
        have := Q.mul_mem h5 (Q.inv_mem q.2)
        simpa only [mul_assoc] using this
      rw [← hkmod] at h6
      have h7 : t⁻¹ * t⁻¹ = (t * t)⁻¹ := by rw [mul_inv_rev]
      rw [h7] at h6
      exact (Q.inv_mem_iff).mp h6
  have hcent : Q ⊓ centralizer {t * t} = Q ⊓ centralizer {t} := by
    ext g
    simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hg, hga⟩
      exact ⟨hg, hCa ⟨g, hg⟩ hga⟩
    · rintro ⟨hg, hgt⟩
      refine ⟨hg, ?_⟩
      rw [← mul_assoc, hgt, mul_assoc, hgt, mul_assoc]
  have hcj2fix : ∀ y : Q, cj (cj y) = y → (y : G) * t = t * y := by
    intro y hy
    apply hCa y
    have h3 := congrArg Subtype.val hy
    rw [hcj2] at h3
    calc (y : G) * (t * t) = t * t * y * (t * t)⁻¹ * (t * t) := by rw [h3]
      _ = t * t * y := by group
  have hfixcj : ∀ y : Q, (y : G) * t = t * y → cj y = y := fun y hy => by
    apply Subtype.ext
    rw [hcj, ← hy, mul_inv_cancel_right]
  have hfixT : ∀ y : Q, T (π y) = π y → (y : G) * t = t * y := by
    intro y hy
    rw [hTcj] at hy
    have hc : y⁻¹ * cj y ∈ center Q := by
      rw [← hπzero, hπmul, hy, hπinv, neg_add_cancel]
    set c := y⁻¹ * cj y with hcdef
    have hcy : cj y = y * c := by rw [hcdef, mul_inv_cancel_left]
    have hcc : c * c = 1 := by
      have h1 : cj (y * y) = y * y := hcjZ _ (hzle (hsqz y))
      rw [map_mul, hcy] at h1
      have h2 : y * c * (y * c) = y * y * (c * c) := by
        calc y * c * (y * c) = y * (c * y) * c := by group
          _ = y * (y * c) * c := by rw [← mem_center_iff.mp hc y]
          _ = y * y * (c * c) := by group
      rw [h2] at h1
      exact mul_left_cancel (h1.trans (mul_one _).symm)
    apply hcj2fix y
    rw [hcy, map_mul, hcy, hcjZ c hc, mul_assoc, hcc, mul_one]
  have hfixed : ∀ v, T v = v ↔ ∃ y : Q, (y : G) * t = t * y ∧ v = π y := by
    intro v
    constructor
    · intro hv
      obtain ⟨y, rfl⟩ := hπsurj v
      exact ⟨y, hfixT y hv, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hTcj, hfixcj y hy]
  have hT4 : T ^ 4 = 1 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, rfl⟩ := hπsurj v
    rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_one,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hTcj, hTcj, hTcj, hTcj,
      hcj4, Module.End.one_apply]
  have hT3l : T * T ^ 3 = 1 := by rw [← pow_succ', hT4]
  have hT3r : T ^ 3 * T = 1 := by rw [← pow_succ, hT4]
  let Te : Additive (Q ⧸ center Q) ≃ₗ[ZMod 2] Additive (Q ⧸ center Q) :=
    LinearEquiv.ofLinearMap T (T ^ 3) hT3l hT3r
  have hTe : ∀ v, Te v = T v := fun v => rfl
  let ιe := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2)
    (M := Additive (Q ⧸ center Q))
  have hιe : Function.Injective ιe := fun f g h => LinearEquiv.ext fun v =>
    LinearMap.congr_fun h v
  have hιeTe : ιe Te = T := rfl
  have hordTe : orderOf Te = orderOf T := by
    rw [← hιeTe, orderOf_injective ιe hιe]
  have hfixSub : ∀ v, v ∈ fixSub Te ↔ T v = v := fun v => mem_fixSub
  have hfix2 : ∀ v, v ∈ fixSub (Te ^ 2) ↔ T (T v) = v := fun v => by
    rw [mem_fixSub, pow_two, LinearEquiv.mul_apply, hTe, hTe]
  have : Module.Finite (ZMod 2) (Additive (Q ⧸ center Q)) := Module.Finite.of_finite
  have hk : ∀ y : Q, T (T (π y)) = π y → cj (cj y) = y ∨ cj (cj y) = y * z := by
    intro y hy
    rw [hTcj, hTcj] at hy
    have hc : y⁻¹ * cj (cj y) ∈ center Q := by
      rw [← hπzero, hπmul, hy, hπinv, neg_add_cancel]
    set k := y⁻¹ * cj (cj y) with hkdef
    have hky : cj (cj y) = y * k := by rw [hkdef, mul_inv_cancel_left]
    have h1 := hcj4 y
    rw [hky, map_mul, map_mul, hky, hcjZ k hc, hcjZ k hc, mul_assoc] at h1
    have h2 : k * k = 1 := mul_left_cancel (h1.trans (mul_one _).symm)
    rcases hpair _ (mem_zpowers_of_sq_eq_one hZ hzZ hz hc (by rw [pow_two]; exact h2))
      with h | h
    · left
      rw [hky, h, mul_one]
    · right
      rw [hky, h]
  have hdim : finrank (ZMod 2) (fixSub (Te ^ 2)) ≤ finrank (ZMod 2) (fixSub Te) + 1 := by
    by_cases hsub : fixSub (Te ^ 2) ≤ fixSub Te
    · have := Submodule.finrank_mono hsub
      omega
    · obtain ⟨v₀, hv₀2, hv₀1⟩ := IsConcreteLE.not_le_iff_exists.mp hsub
      have hv₀ne : v₀ ≠ 0 := fun h => hv₀1 (h ▸ Submodule.zero_mem _)
      have hnfix : ∀ y : Q, π y ∈ fixSub (Te ^ 2) → π y ∉ fixSub Te → cj (cj y) = y * z := by
        intro y hy2 hy1
        rcases hk y ((hfix2 _).mp hy2) with h | h
        · exfalso
          apply hy1
          rw [hfixSub, hTcj, hfixcj y (hcj2fix y h)]
        · exact h
      have hle : fixSub (Te ^ 2) ≤ fixSub Te ⊔ (ZMod 2) ∙ v₀ := by
        intro v hv
        by_cases hv1 : v ∈ fixSub Te
        · exact Submodule.mem_sup_left hv1
        · obtain ⟨y, rfl⟩ := hπsurj v
          obtain ⟨y₀, rfl⟩ := hπsurj v₀
          have e1 := hnfix y hv hv1
          have e2 := hnfix y₀ hv₀2 hv₀1
          have hyy : cj (cj (y * y₀)) = y * y₀ := by
            rw [map_mul, map_mul, e1, e2]
            calc y * z * (y₀ * z) = y * (z * y₀) * z := by group
              _ = y * (y₀ * z) * z := by rw [← mem_center_iff.mp hzZ y₀]
              _ = y * y₀ * (z * z) := by group
              _ = y * y₀ := by rw [hC.z_mul_z, mul_one]
          have hfixyy : π (y * y₀) ∈ fixSub Te := by
            rw [hfixSub, hTcj, hfixcj _ (hcj2fix _ hyy)]
          rw [hπmul] at hfixyy
          have : π y = (π y + π y₀) + π y₀ := by
            rw [add_assoc, ← two_smul (ZMod 2) (π y₀), show (2 : ZMod 2) = 0 from rfl,
              zero_smul, add_zero]
          rw [this]
          exact Submodule.add_mem_sup hfixyy (Submodule.mem_span_singleton_self _)
      calc finrank (ZMod 2) (fixSub (Te ^ 2))
          ≤ finrank (ZMod 2) (fixSub Te ⊔ (ZMod 2) ∙ v₀ : Submodule (ZMod 2) _) :=
            Submodule.finrank_mono hle
        _ ≤ finrank (ZMod 2) (fixSub Te) + finrank (ZMod 2) ((ZMod 2) ∙ v₀) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ = finrank (ZMod 2) (fixSub Te) + 1 := by rw [finrank_span_singleton hv₀ne]
  have hnot4 : orderOf T ≠ 4 := by
    intro hT4o
    have hTe4 : orderOf Te = 4 := hordTe.trans hT4o
    have hb : b.IsAlt := hC.commForm_isAlt
    have hnd : b.Nondegenerate := hC.commForm_nondegenerate
    have hTeiso : Te ∈ TauCeti.BilinForm.isometryGroup b :=
      TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun u v => hbiso u v
    have hHle : zpowers Te ≤ TauCeti.BilinForm.isometryGroup b := zpowers_le.mpr hTeiso
    have hUfix : ∀ h ∈ zpowers Te, ∀ u ∈ fixSub Te, h u = u := by
      intro h hh u hu
      have hst : zpowers Te ≤ MulAction.stabilizer
          (Additive (Q ⧸ center Q) ≃ₗ[ZMod 2] Additive (Q ⧸ center Q)) u :=
        zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (mem_fixSub.mp hu))
      exact MulAction.mem_stabilizer_iff.mp (hst hh)
    have hUc : fixSub Te ≤ fixSub (Te ^ 2) := fun u hu => by
      rw [mem_fixSub] at hu ⊢
      rw [pow_two, LinearEquiv.mul_apply, hu, hu]
    obtain ⟨-, -, L, -, -, hndL, -, ⟨e, hli, hspan, hc0, hc1, hc2, hc3⟩, -⟩ :=
      symplectic_order_four_almost_fixed_square_compression hb hnd hHle (mem_zpowers Te) hTe4
        hUfix hUc hdim
    have hTe0 : T (e 0) = e 0 := hc0
    have hfix0 : ∀ v, b (e 0) (T v) = b (e 0) v := fun v => by
      rw [← hbiso (e 0) v, hTe0]
    have hb01 : b (e 0) (e 1) = 0 := by
      have h := hfix0 (e 2)
      rw [← hTe, hc2, map_add] at h
      exact (add_eq_left).mp h
    have hb02 : b (e 0) (e 2) = 0 := by
      have h := hfix0 (e 3)
      rw [← hTe, hc3, map_add] at h
      exact (add_eq_left).mp h
    have hb00 : b (e 0) (e 0) = 0 := hb (e 0)
    have hz2cases : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    have hb03 : b (e 0) (e 3) = 1 := by
      by_contra h0
      have h03 : b (e 0) (e 3) = 0 := by
        by_contra h1
        exact h0 (hz2cases _ h1)
      have he0 : e 0 ∈ L := hspan ▸ Submodule.subset_span ⟨0, rfl⟩
      have hzero : (⟨e 0, he0⟩ : L) = 0 := by
        refine hndL.1 _ fun n => ?_
        have hn : (n : Additive (Q ⧸ center Q)) ∈ Submodule.span (ZMod 2) (Set.range e) :=
          hspan ▸ n.2
        have key : ∀ m ∈ Submodule.span (ZMod 2) (Set.range e), b (e 0) m = 0 := by
          intro m hm
          induction hm using Submodule.span_induction with
          | mem u hu =>
            obtain ⟨i, rfl⟩ := hu
            fin_cases i
            · exact hb00
            · exact hb01
            · exact hb02
            · exact h03
          | zero => exact map_zero _
          | add u w _ _ hu hw => rw [map_add, hu, hw, add_zero]
          | smul c u _ hu => rw [map_smul, hu, smul_zero]
        exact key _ hn
      exact hli.ne_zero 0 (congrArg Subtype.val hzero)
    have hb12 : b (e 1) (e 2) = 1 := by
      have h := hbiso (e 1) (e 3)
      rw [← hTe, ← hTe, hc1, hc3] at h
      simp only [map_add, LinearMap.add_apply] at h
      rw [hb03, hb02] at h
      revert h
      generalize b (e 1) (e 3) = p
      generalize b (e 1) (e 2) = r
      generalize b (e 0) (e 3) = s
      revert p r
      decide
    have hb10 : b (e 1) (e 0) = 0 := by
      rw [hbdef, hC.commForm_comm, ← hbdef]
      exact hb01
    have hb21 : b (e 2) (e 1) = 1 := by
      rw [hbdef, hC.commForm_comm, ← hbdef]
      exact hb12
    obtain ⟨x, hx⟩ := hπsurj (e 3)
    let d₁ : Q := x⁻¹ * cj x
    let d₂ : Q := d₁⁻¹ * cj d₁
    let d₃ : Q := d₂⁻¹ * cj d₂
    have hπN : ∀ y : Q, π (y⁻¹ * cj y) = T (π y) - π y := fun y => by
      rw [hπmul, hTcj, hπinv]
      abel
    have hsub2 : ∀ v w : Additive (Q ⧸ center Q), v + w - v = w := fun v w => by abel
    have hd1 : π d₁ = e 2 := by
      rw [hπN, hx, ← hTe, hc3, hsub2]
    have hd2 : π d₂ = e 1 := by
      rw [hπN, hd1, ← hTe, hc2, hsub2]
    have hd3 : π d₃ = e 0 := by
      rw [hπN, hd2, ← hTe, hc1, hsub2]
    have hc1' : cj x = x * d₁ := by rw [mul_inv_cancel_left]
    have hc2' : cj d₁ = d₁ * d₂ := by rw [mul_inv_cancel_left]
    have hc3' : cj d₂ = d₂ * d₃ := by rw [mul_inv_cancel_left]
    have hc4' : cj d₃ = d₃ := hfixcj d₃ (hfixT d₃ (by rw [hd3]; exact hTe0))
    have h12 : d₂ * d₁ = d₁ * d₂ * z := by
      have h1 : ⁅d₁, d₂⁆ = z := by
        rw [hC.commutatorElement_eq_zpow]
        have h2 : commVal z (d₁ : Q ⧸ center Q) (d₂ : Q ⧸ center Q) = 1 := by
          have := hbapp d₁ d₂
          rw [hd1, hd2, hb21] at this
          rw [hC.commVal_mk]
          exact this.symm
        rw [h2]
        exact pow_one z
      rw [commutatorElement_def] at h1
      calc d₂ * d₁ = (d₁ * d₂ * d₁⁻¹ * d₂⁻¹)⁻¹ * (d₁ * d₂) := by group
        _ = z⁻¹ * (d₁ * d₂) := by rw [h1]
        _ = z * (d₁ * d₂) := by rw [inv_eq_of_mul_eq_one_right hC.z_mul_z]
        _ = d₁ * d₂ * z := (mem_center_iff.mp hzZ _).symm
    have h23 : d₂ * d₃ = d₃ * d₂ := by
      rw [← hC.commVal_eq_zero_iff, hC.commVal_mk]
      have := hbapp d₂ d₃
      rw [hd2, hd3, hb10] at this
      exact this.symm
    have hs1 : d₁ * d₁ ∈ center Q := hzle (hsqz d₁)
    have hs1o : d₁ * d₁ * (d₁ * d₁) = 1 := by
      rcases hpair _ (hsqz d₁) with h | h
      · rw [h, mul_one]
      · rw [h, hC.z_mul_z]
    have hfinal := pow_four_conj_eq cj hzZ hC.z_mul_z hc1' hc2' hc3' hc4' h12 h23 hs1
      (hcjZ _ hs1) hs1o (hcjZ _ (hzle (hsqz d₂)))
    rw [hcj4 x] at hfinal
    have hz' : z = 1 := mul_left_cancel (hfinal.symm.trans (mul_one x).symm)
    exact hz1 hz'
  have hT2 : T * T = 1 := by
    have hdvd : orderOf T ∣ 4 := orderOf_dvd_of_pow_eq_one hT4
    have h2 : orderOf T ∣ 2 := by
      have h1 : orderOf T ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : orderOf T
      · exact absurd hdvd (by norm_num)
      · exact one_dvd 2
      · exact dvd_refl 2
      · exact absurd hdvd (by norm_num)
      · exact absurd rfl hnot4
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  have hrank : finrank (ZMod 2) (LinearMap.range (T - 1)) ≤ 1 := by
    have hF : fixSub (Te ^ 2) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [hfix2, ← Module.End.mul_apply, hT2, Module.End.one_apply]
    rw [hF, finrank_top] at hdim
    have hker : LinearMap.ker (T - 1) = fixSub Te := by
      ext v
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hfixSub]
    have h := LinearMap.finrank_range_add_finrank_ker (T - 1)
    rw [hker] at h
    omega
  exact ⟨hcent, hfixed, hT2, hrank, hnot4⟩

end CFSG.LocalAnalysis.GorensteinLyons
