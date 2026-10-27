module

public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4Norm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)
open scoped MatrixGroups


section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G} {a : ℕ}
  {t : StatedLieTag} {n : ℕ}

theorem Pkg3.exists_member_of_involution (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) (F : G2D4Facts3 (CompData.model t n)) {M₀ : Subgroup G}
    (hM₀ : Fb Ω w M₀) {x₀ : G} (hx₀ : IsClassicalMember3 M₀ x₀) {u : (P.D.kind P.i₁).G}
    (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ (N : Subgroup G) (x : G) (hY : x ∈ locLayer Ω w), Fb Ω w N ∧ IsClassicalMember3 N x ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) ⟨x, hY⟩ =
        P.D.hom P.i₁ u := by
  have hF := P.facts F
  obtain ⟨R, r, hx₀Y, hRf, -, hRu, hr⟩ := P.partner_data hΩ hex F hM₀ hx₀
  obtain ⟨R', hR'f, hR'u⟩ := hF.exists_fund u hu2 hu1
  obtain ⟨g, hg⟩ := hF.inv_conj R hRf R' hR'f r hRu.mem u hR'u.mem hRu.sq hu2 hRu.ne_one hu1
    (fun y hy => hRu.commute_of_mem hy) (fun y hy => hR'u.commute_of_mem hy)
  obtain ⟨ĝ, hĝ⟩ := QuotientGroup.mk'_surjective
    (classicalInvolutionOddCore ↥(locLayer Ω w)) (P.D.hom P.i₁ g)
  have hĝw : (ĝ : G) * w * (ĝ : G)⁻¹ = w := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {w} ĝ.2)
    exact mul_inv_eq_iff_eq_mul.mpr this
  have hN : Fb Ω w (conjSub (ĝ : G) M₀) := by
    have := (fb_conj_iff hΩ.conjInvariant (ĝ : G)).mpr hM₀
    rwa [hĝw] at this
  have hx : IsClassicalMember3 (conjSub (ĝ : G) M₀) ((ĝ : G) * x₀ * (ĝ : G)⁻¹) := hx₀.conj _
  have hY : (ĝ : G) * x₀ * (ĝ : G)⁻¹ ∈ locLayer Ω w := le_centralizingLayer hN.1 hx.mem
  refine ⟨conjSub (ĝ : G) M₀, (ĝ : G) * x₀ * (ĝ : G)⁻¹, hY, hN, hx, ?_⟩
  have e1 : (⟨(ĝ : G) * x₀ * (ĝ : G)⁻¹, hY⟩ : ↥(locLayer Ω w)) = ĝ * ⟨x₀, hx₀Y⟩ * ĝ⁻¹ :=
    Subtype.ext rfl
  rw [e1, map_mul, map_mul, map_inv, hĝ, ← hr, ← map_inv, ← map_mul, ← map_mul, hg]

end Members

section Final

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {a : ℕ} {t : StatedLieTag}
  {n : ℕ}

theorem typeB [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (S : ExCtx3 G K z a t n)
    (F : G2D4Facts3 (CompData.model t n)) {u : G} {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K)
    (hu : IsClassicalMember3 N₀ u) {M M₁ : Subgroup G} (hM : Fb (conjClass3 K) u M)
    (hM₁ : Fb (conjClass3 K) u M₁) {p q : G} (hp : IsClassicalMember3 M p)
    (hq : IsClassicalMember3 M₁ q) (hpq : p ≠ q) (hcomm : p * q = q * p) :
    ∀ x ∈ layerX (conjClass3 K) p, (q * u) * x = x * (q * u) := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨Pu⟩ := S.exists_pkg hN₀ hu
  obtain ⟨Pp⟩ := S.exists_pkg hM.1.1 hp
  have hN₀cn : Cn (conjClass3 K) u N₀ := Pu.cn_of_isClassicalMember hΩ hex F hN₀ hu
  have hN₀fb : Fb (conjClass3 K) p N₀ := fb_of_cn_of_fb S F hN₀ hu hM hp hN₀cn
  have hq2 : q * q = 1 := mul_self_eq_one_of_isClassicalMember3 hq
  have hcN₀ : Commutes N₀ M₁ := by
    rcases hN₀cn.2 M₁ hM₁.1 with h | h
    · subst h
      exact absurd hN₀cn hM₁.2
    · exact h
  have hqA : ∀ x ∈ N₀, q * x = x * q := fun x hx => (hcN₀ x hx q hq.mem).symm
  rcases Pp.lemmaA hΩ hex F hN₀fb hu hq2 hcomm.symm hqA with h | h
  · exact (typeA_false hnab S F hN₀ hu hM hM₁ hp hq hpq hcomm h).elim
  · exact h

theorem not_central_layerX (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n))
    {u : G} {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) (hu : IsClassicalMember3 N₀ u)
    {M : Subgroup G} (hM : Fb (conjClass3 K) u M) {p : G} (hp : IsClassicalMember3 M p)
    (hcent : ∀ x ∈ layerX (conjClass3 K) p, u * x = x * u) : False := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨Pu⟩ := S.exists_pkg hN₀ hu
  obtain ⟨Pp⟩ := S.exists_pkg hM.1.1 hp
  have hN₀cn : Cn (conjClass3 K) u N₀ := Pu.cn_of_isClassicalMember hΩ hex F hN₀ hu
  have hN₀fb : Fb (conjClass3 K) p N₀ := fb_of_cn_of_fb S F hN₀ hu hM hp hN₀cn
  have hF := Pp.facts F
  have hinj := Pp.inj F
  obtain ⟨R, r, huY, hRf, -, hRu, hr⟩ := Pp.partner_data hΩ hex F hN₀fb hu
  have hrc : ∀ g : (Pp.D.kind Pp.i₁).G, r * g = g * r := by
    intro g
    obtain ⟨y, hyL, hy⟩ := Pp.range_le_map_layerX hΩ hex F (⟨g, rfl⟩ : Pp.D.hom Pp.i₁ g ∈
      (Pp.D.hom Pp.i₁).range)
    have hyc : (⟨u, huY⟩ : ↥(locLayer (conjClass3 K) p)) * y = y * ⟨u, huY⟩ :=
      Subtype.ext (hcent y hyL)
    have := congrArg (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(locLayer (conjClass3 K) p))) hyc
    rw [map_mul, map_mul] at this
    apply hinj
    rw [map_mul, map_mul, hr, ← hy]
    exact this
  have hr1 : r = 1 := by
    have : r ∈ Subgroup.center (Pp.D.kind Pp.i₁).G :=
      Subgroup.mem_center_iff.mpr fun g => (hrc g).symm
    rw [hF.center_bot] at this
    exact this
  exact hRu.ne_one hr1

theorem false_of_g2d4_exotic [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n)) : False := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : IsClassicalMember3 K z := S.setup.cls
  by_cases htd : t = .trialityD4 ∧ 2 ≤ a
  · exact false_of_td4_two S F htd.1 htd.2 hKΩ hKz
  obtain ⟨Pz⟩ := S.exists_pkg hKΩ hKz
  have hinj := Pz.inj F
  obtain ⟨M₀, hM₀c⟩ := exists_mem_compMembers3 (D := Pz.D) Pz.i₁
  have hM₀ : Fb (conjClass3 K) z M₀ := (Pz.fb_iff hΩ hex F).mpr hM₀c
  obtain ⟨x₀, hx₀⟩ := hΩ.classical M₀ hM₀c.1.1
  obtain ⟨R, r, hx₀Y, hRf, -, hRu, hr⟩ := Pz.partner_data hΩ hex F hM₀ hx₀
  obtain ⟨w, w', hw2, hw'2, hw1, hw'1, hww', hrw, hrw', hwcomm, hwr, hw'r, hww'r⟩ :=
    (Pz.facts F).rank3 R hRf r hRu.mem (fun y hy => hRu.commute_of_mem hy) hRu.sq hRu.ne_one
  have hww2 : (w * w') * (w * w') = 1 := by
    calc w * w' * (w * w') = w * (w' * w) * w' := by group
      _ = w * (w * w') * w' := by rw [hwcomm]
      _ = (w * w) * (w' * w') := by group
      _ = 1 := by rw [hw2, hw'2, one_mul]
  have hww1 : w * w' ≠ 1 := by
    intro h
    apply hww'
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hw'2]
  obtain ⟨N₁, x₁, hY₁, hN₁, hx₁, hi₁⟩ := Pz.exists_member_of_involution hΩ hex F hM₀ hx₀ hw2 hw1
  obtain ⟨N₂, x₂, hY₂, hN₂, hx₂, hi₂⟩ := Pz.exists_member_of_involution hΩ hex F hM₀ hx₀ hw'2 hw'1
  obtain ⟨N₃, x₃, hY₃, hN₃, hx₃, hi₃⟩ :=
    Pz.exists_member_of_involution hΩ hex F hM₀ hx₀ hww2 hww1
  have hs₀ := mul_self_eq_one_of_isClassicalMember3 hx₀
  have hs₁ := mul_self_eq_one_of_isClassicalMember3 hx₁
  have hs₂ := mul_self_eq_one_of_isClassicalMember3 hx₂
  have hs₃ := mul_self_eq_one_of_isClassicalMember3 hx₃
  have hz2 : z * z = 1 := mul_self_eq_one_of_isClassicalMember3 hKz
  have key : ∀ (y y' : G) (hy : y ∈ locLayer (conjClass3 K) z)
      (hy' : y' ∈ locLayer (conjClass3 K) z) (e e' : (Pz.D.kind Pz.i₁).G), y * y = 1 → y' * y' = 1 →
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z)) ⟨y, hy⟩ =
        Pz.D.hom Pz.i₁ e →
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z)) ⟨y', hy'⟩ =
        Pz.D.hom Pz.i₁ e' → e * e' = e' * e → y * y' = y' * y := by
    intro y y' hy hy' e e' hy2 hy'2 h1 h2 hee
    refine commute_of_mk_commute3 Pz.p1 hy hy' hy2 hy'2 ?_
    rw [h1, h2, ← map_mul, ← map_mul, hee]
  have hr' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z))
      ⟨x₀, hx₀Y⟩ = Pz.D.hom Pz.i₁ r := hr.symm
  have hrww : r * (w * w') = (w * w') * r := by
    calc r * (w * w') = (r * w) * w' := by group
      _ = (w * r) * w' := by rw [hrw]
      _ = w * (r * w') := by group
      _ = w * (w' * r) := by rw [hrw']
      _ = (w * w') * r := by group
  have hwww : w * (w * w') = (w * w') * w := by
    calc w * (w * w') = w * (w' * w) := by rw [hwcomm]
      _ = (w * w') * w := by group
  have hw'ww : w' * (w * w') = (w * w') * w' := by
    calc w' * (w * w') = (w' * w) * w' := by group
      _ = (w * w') * w' := by rw [← hwcomm]
  have c01 : x₀ * x₁ = x₁ * x₀ := key x₀ x₁ hx₀Y hY₁ r w hs₀ hs₁ hr' hi₁ hrw
  have c02 : x₀ * x₂ = x₂ * x₀ := key x₀ x₂ hx₀Y hY₂ r w' hs₀ hs₂ hr' hi₂ hrw'
  have c03 : x₀ * x₃ = x₃ * x₀ := key x₀ x₃ hx₀Y hY₃ r (w * w') hs₀ hs₃ hr' hi₃ hrww
  have c12 : x₁ * x₂ = x₂ * x₁ := key x₁ x₂ hY₁ hY₂ w w' hs₁ hs₂ hi₁ hi₂ hwcomm
  have c13 : x₁ * x₃ = x₃ * x₁ := key x₁ x₃ hY₁ hY₃ w (w * w') hs₁ hs₃ hi₁ hi₃ hwww
  have c23 : x₂ * x₃ = x₃ * x₂ := key x₂ x₃ hY₂ hY₃ w' (w * w') hs₂ hs₃ hi₂ hi₃ hw'ww
  have hne : ∀ (y : G) (hy : y ∈ locLayer (conjClass3 K) z) (e : (Pz.D.kind Pz.i₁).G),
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z)) ⟨y, hy⟩ =
        Pz.D.hom Pz.i₁ e → e ≠ r → x₀ ≠ y := by
    intro y hy e he her h
    apply her
    apply hinj
    rw [← he, ← hr']
    exact congrArg _ (Subtype.ext h.symm)
  have n01 : x₀ ≠ x₁ := hne x₁ hY₁ w hi₁ hwr
  have n02 : x₀ ≠ x₂ := hne x₂ hY₂ w' hi₂ hw'r
  have n03 : x₀ ≠ x₃ := hne x₃ hY₃ (w * w') hi₃ hww'r
  have hYprod : x₁ * x₂ * x₃ ∈ locLayer (conjClass3 K) z :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hY₁ hY₂) hY₃
  have hprod : x₁ * x₂ * x₃ = 1 := by
    have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z))
        ⟨x₁ * x₂ * x₃, hYprod⟩ = 1 := by
      have e : (⟨x₁ * x₂ * x₃, hYprod⟩ : ↥(locLayer (conjClass3 K) z)) =
          ⟨x₁, hY₁⟩ * ⟨x₂, hY₂⟩ * ⟨x₃, hY₃⟩ := rfl
      rw [e, map_mul, map_mul, hi₁, hi₂, hi₃, ← map_mul, ← map_mul, hww2, map_one]
    have hO : (⟨x₁ * x₂ * x₃, hYprod⟩ : ↥(locLayer (conjClass3 K) z)) ∈
        classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z) :=
      (QuotientGroup.eq_one_iff _).mp hmk
    have hsq : (x₁ * x₂ * x₃) * (x₁ * x₂ * x₃) = 1 := by
      have h13 : Commute x₁ x₃ := c13
      have h23 : Commute x₂ x₃ := c23
      have h12 : Commute x₁ x₂ := c12
      rw [← pow_two, Commute.mul_pow (h13.mul_left h23), h12.mul_pow, pow_two, pow_two, pow_two,
        hs₁, hs₂, hs₃]
      simp
    have := eq_one_of_mem_oddCore_of_sq3 hO (Subtype.ext hsq)
    exact congrArg Subtype.val this
  have hB₁ := typeB hnab S F hKΩ hKz hM₀ hN₁ hx₀ hx₁ n01 c01
  have hB₂ := typeB hnab S F hKΩ hKz hM₀ hN₂ hx₀ hx₂ n02 c02
  have hB₃ := typeB hnab S F hKΩ hKz hM₀ hN₃ hx₀ hx₃ n03 c03
  have hz₁ : z * x₁ = x₁ * z := (Subgroup.mem_centralizer_singleton_iff.mp
    (hN₁.1.2 hx₁.mem)).symm
  have hz₂ : z * x₂ = x₂ * z := (Subgroup.mem_centralizer_singleton_iff.mp
    (hN₂.1.2 hx₂.mem)).symm
  have hz₃ : z * x₃ = x₃ * z := (Subgroup.mem_centralizer_singleton_iff.mp
    (hN₃.1.2 hx₃.mem)).symm
  have hz : (x₁ * z) * (x₂ * z) * (x₃ * z) = z := by
    calc (x₁ * z) * (x₂ * z) * (x₃ * z) = x₁ * (z * x₂) * z * x₃ * z := by group
      _ = x₁ * (x₂ * z) * z * x₃ * z := by rw [hz₂]
      _ = x₁ * x₂ * (z * z) * x₃ * z := by group
      _ = x₁ * x₂ * x₃ * z := by rw [hz2]; group
      _ = z := by rw [hprod]; group
  refine not_central_layerX S F hKΩ hKz hM₀ hx₀ ?_
  intro x hx
  have h1 := hB₁ x hx
  have h2 := hB₂ x hx
  have h3 := hB₃ x hx
  calc z * x = ((x₁ * z) * (x₂ * z) * (x₃ * z)) * x := by rw [hz]
    _ = (x₁ * z) * (x₂ * z) * ((x₃ * z) * x) := by group
    _ = (x₁ * z) * (x₂ * z) * (x * (x₃ * z)) := by rw [h3]
    _ = (x₁ * z) * ((x₂ * z) * x) * (x₃ * z) := by group
    _ = (x₁ * z) * (x * (x₂ * z)) * (x₃ * z) := by rw [h2]
    _ = ((x₁ * z) * x) * (x₂ * z) * (x₃ * z) := by group
    _ = (x * (x₁ * z)) * (x₂ * z) * (x₃ * z) := by rw [h1]
    _ = x * ((x₁ * z) * (x₂ * z) * (x₃ * z)) := by group
    _ = x * z := by rw [hz]

end Final

end CFSG.ClassicalInvolution.Q3.Q3W.EX
