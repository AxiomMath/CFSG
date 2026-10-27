module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Four
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

omit [Finite G] in
theorem phig_zpow {g : G} (hg : g ∈ Cx x) (j : ℤ) :
    phig x Kb (g ^ j) = (phig x Kb g) ^ j := by
  rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
  · simp only [zpow_natCast]
    exact phig_pow x Kb hg n
  · simp only [zpow_neg, zpow_natCast]
    rw [phig_inv x Kb (pow_mem hg n), phig_pow x Kb hg n]

omit [Finite G] [Kb.Normal] in
theorem decomp_NT {a : MulAut ↥Kb} (ha : a ∈ (N.T : Subgroup (MulAut ↥Kb))) :
    ∃ d ∈ N.Pt, ∃ f ∈ N.R, d * f = a := by
  have hD : (IVK.innDiagSub e).Normal := IVK.innDiagSub_normal e
  have hFD := IVK.innDiagSub_inf_fieldAutSub e
  have ha' : a ∈ IVK.innDiagSub e ⊔ IVK.fieldAutSub e := by
    rw [IVK.innDiagSub_sup_fieldAutSub e]; exact Subgroup.mem_top a
  obtain ⟨d, hd, f, hf, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 ha'
  have hp : IsPGroup 2 ↥(N.T : Subgroup (MulAut ↥Kb)) := N.T.isPGroup'
  obtain ⟨k, hk⟩ := hp ⟨d * f, ha⟩
  have hk1 : (d * f) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hmk : (QuotientGroup.mk' (IVK.innDiagSub e)) d = 1 := (QuotientGroup.eq_one_iff d).2 hd
  have hf1 : f ^ (2 ^ k) = 1 := by
    have h1 : (QuotientGroup.mk' (IVK.innDiagSub e)) ((d * f) ^ (2 ^ k)) = 1 := by
      rw [hk1, map_one]
    rw [map_pow, map_mul, hmk, one_mul] at h1
    have h2 : (QuotientGroup.mk' (IVK.innDiagSub e)) (f ^ (2 ^ k)) = 1 := by
      rw [map_pow]; exact h1
    have h3 : f ^ (2 ^ k) ∈ IVK.innDiagSub e ⊓ IVK.fieldAutSub e :=
      ⟨(QuotientGroup.eq_one_iff _).1 h2, pow_mem hf _⟩
    rw [hFD] at h3
    exact h3
  have hf2 : IsPGroup 2 ↥(Subgroup.zpowers f) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hf1)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hfT : f ∈ (N.T : Subgroup (MulAut ↥Kb)) := by
    have hs := hf2.inf_normalizer_sylow N.T
    have hmem : f ∈ Subgroup.zpowers f ⊓ Subgroup.normalizer (N.T : Set (MulAut ↥Kb)) :=
      ⟨Subgroup.mem_zpowers f, N.T_inv hf⟩
    rw [hs] at hmem
    exact hmem.2
  have hdT : d ∈ (N.T : Subgroup (MulAut ↥Kb)) := by
    have := mul_mem ha (inv_mem hfT)
    simpa using this
  exact ⟨d, ⟨hdT, hd⟩, f, ⟨hfT, hf⟩, rfl⟩

omit [Kb.Normal] in
theorem NP_normal_in_NPt (hF : IVK.L2Field F) {c a : MulAut ↥Kb} (hc : c ∈ N.Pt) (ha : a ∈ N.P) :
    c * a * c⁻¹ ∈ N.P := by
  have hidx := NPt_index_two (e := e) (N := N) hF
  have : (N.P.subgroupOf N.Pt).Normal := Subgroup.normal_of_index_eq_two hidx
  have h1 := (inferInstance : (N.P.subgroupOf N.Pt).Normal).conj_mem
    ⟨a, NP_le_NPt ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨c, hc⟩
  exact Subgroup.mem_subgroupOf.1 h1

omit [Finite G] [Kb.Normal] in
theorem NR_inv_cent {f : MulAut ↥Kb} (hf : f ∈ N.R) (hf2 : f * f = 1) :
    ∀ a ∈ N.P, a * f = f * a := by
  by_cases hf1 : f = 1
  · intro a _
    subst hf1
    simp
  · have hord : orderOf f = 2 := orderOf_eq_prime (by rw [pow_two]; exact hf2) hf1
    exact N.R_cent f ⟨hf.1, hf.2⟩ hord

omit [Kb.Normal] in
theorem comm_mem_NP (hF : IVK.L2Field F) (h12a : IVK.IVK_1_2a_struct) (h12d : IVK.IVK_1_2d)
    {f c : MulAut ↥Kb} (hf : f ∈ N.R) (hc : c ∈ N.Pt) : f * c * f⁻¹ * c⁻¹ ∈ N.P := by
  have hd := (h12d F hF ↥Kb e N).1
  have hcD : c ∈ IVK.innAut ↥Kb ⊔ Subgroup.zpowers N.t := by rw [hd]; exact hc.2
  have h1 : ⁅f, c⁆ ∈ IVK.innAut ↥Kb := (h12a F hF ↥Kb e N).2.2.2 f hf.2 c hcD
  have hfT : f ∈ (N.T : Subgroup (MulAut ↥Kb)) := hf.1
  have hcT : c ∈ (N.T : Subgroup (MulAut ↥Kb)) := hc.1
  have hmem : f * c * f⁻¹ * c⁻¹ ∈ (N.T : Subgroup (MulAut ↥Kb)) :=
    mul_mem (mul_mem (mul_mem hfT hcT) (inv_mem hfT)) (inv_mem hcT)
  exact ⟨hmem, by simpa [commutatorElement_def] using h1⟩

omit [Kb.Normal] in
theorem comm_mem_center (hF : IVK.L2Field F) (h12a : IVK.IVK_1_2a_struct) (h12d : IVK.IVK_1_2d)
    {f c : MulAut ↥Kb} (hf : f ∈ N.R) (hf2 : f * f = 1) (hc : c ∈ N.Pt) :
    f * c * f⁻¹ * c⁻¹ ∈ N.P ∧ ∀ a ∈ N.P, (f * c * f⁻¹ * c⁻¹) * a = a * (f * c * f⁻¹ * c⁻¹) := by
  refine ⟨comm_mem_NP hF h12a h12d hf hc, fun a ha => ?_⟩
  have hfc : ∀ a ∈ N.P, a * f = f * a := NR_inv_cent hf hf2
  have hfa : Commute f a := (hfc a ha).symm
  set A' : MulAut ↥Kb := c⁻¹ * a * c with hA'
  have hA'P : A' ∈ N.P := by
    have := NP_normal_in_NPt hF (N.Pt.inv_mem hc) ha
    simpa [hA'] using this
  have hfA' : f * A' = A' * f := (hfc A' hA'P).symm
  have hf'a : Commute (c * f * c⁻¹) a := by
    show c * f * c⁻¹ * a = a * (c * f * c⁻¹)
    have e1 : c * f * c⁻¹ * a = c * (f * A') * c⁻¹ := by simp only [hA']; group
    have e2 : a * (c * f * c⁻¹) = c * (A' * f) * c⁻¹ := by simp only [hA']; group
    rw [e1, e2, hfA']
  have hu : f * c * f⁻¹ * c⁻¹ = f * (c * f * c⁻¹)⁻¹ := by group
  rw [hu]
  exact (hfa.mul_left hf'a.inv_left).eq

theorem map_conj_congr {M : Type*} [Group M] {V : Subgroup M} {g g' : M}
    (h : ∀ v ∈ V, g * v * g⁻¹ = g' * v * g'⁻¹) :
    V.map (MulAut.conj g).toMonoidHom = V.map (MulAut.conj g').toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (h v hv).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, h v hv⟩

omit [Kb.Normal] in
theorem four_conj_field (hF : IVK.L2Field F) (h12a : IVK.IVK_1_2a_struct) (h12d : IVK.IVK_1_2d)
    (h13fa : IVK.IVK_1_3f_a) {r : MulAut ↥Kb} (hr : r ∈ N.R) {V : Subgroup (MulAut ↥Kb)}
    (hVP : V ≤ N.P) (hV : IVK.IsFourSubgroup V) :
    ∃ a ∈ N.P, ∀ v ∈ V, r * v * r⁻¹ = a * v * a⁻¹ := by
  obtain ⟨U₀, hU₀P, hU₀4, hU₀c⟩ := N.four_cent
  obtain ⟨c, hc, hcU⟩ := h13fa F hF ↥Kb e N U₀ V hU₀P hVP hU₀4 hV
  refine ⟨r * c * r⁻¹ * c⁻¹, comm_mem_NP hF h12a h12d hr hc, ?_⟩
  intro v hv
  rw [← hcU] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  have hru : r * u = u * r := hU₀c r hr.2 u hu
  have h1 : r⁻¹ * u * r = u := by
    calc r⁻¹ * u * r = r⁻¹ * (u * r) := by rw [mul_assoc]
      _ = r⁻¹ * (r * u) := by rw [hru]
      _ = u := by group
  simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
  calc r * (c * u * c⁻¹) * r⁻¹ = r * c * (r⁻¹ * u * r) * c⁻¹ * r⁻¹ := by rw [h1]; group
    _ = _ := by group

omit [Kb.Normal] in
theorem mul_inv_mem_NP (hF : IVK.L2Field F) {u v : MulAut ↥Kb} (hu : u ∈ N.Pt) (hv : v ∈ N.Pt)
    (hu' : u ∉ N.P) (hv' : v ∉ N.P) : u * v⁻¹ ∈ N.P := by
  have hidx := NPt_index_two (e := e) (N := N) hF
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨u, hu⟩ : ↥N.Pt))
    (b := (⟨v⁻¹, N.Pt.inv_mem hv⟩ : ↥N.Pt))).2 (by
      constructor
      · intro h1; exact absurd (Subgroup.mem_subgroupOf.1 h1) hu'
      · intro h2; exact absurd (inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 h2)) hv')
  exact Subgroup.mem_subgroupOf.1 this

omit [Kb.Normal] in
theorem fuse_twisted (hF : IVK.L2Field F) (h12a : IVK.IVK_1_2a_struct) (h12d : IVK.IVK_1_2d)
    (h13fa : IVK.IVK_1_3f_a) {d₀ r : MulAut ↥Kb} (hd₀ : d₀ ∈ N.Pt) (hd₀P : d₀ ∉ N.P)
    (hr : r ∈ N.R) {V V' : Subgroup (MulAut ↥Kb)} (hV : V ≤ N.P) (hV' : V' ≤ N.P)
    (h4 : IVK.IsFourSubgroup V) (h4' : IVK.IsFourSubgroup V') :
    (∃ a ∈ N.P, V.map (MulAut.conj a).toMonoidHom = V') ∨
      ∃ a ∈ N.P, V.map (MulAut.conj (a * (d₀ * r))).toMonoidHom = V' := by
  obtain ⟨c₁, hc₁, hc₁V⟩ := h13fa F hF ↥Kb e N V V' hV hV' h4 h4'
  by_cases hc₁P : c₁ ∈ N.P
  · exact Or.inl ⟨c₁, hc₁P, hc₁V⟩
  right
  obtain ⟨a₁, ha₁, hra⟩ := four_conj_field hF h12a h12d h13fa hr hV h4
  have hda₁ : d₀ * a₁ ∈ N.Pt := mul_mem hd₀ (NP_le_NPt ha₁)
  have hda₁P : d₀ * a₁ ∉ N.P := by
    intro h1
    apply hd₀P
    have := mul_mem h1 (inv_mem ha₁)
    simpa using this
  have ha₂ : c₁ * (d₀ * a₁)⁻¹ ∈ N.P := mul_inv_mem_NP hF hc₁ hda₁ hc₁P hda₁P
  refine ⟨c₁ * (d₀ * a₁)⁻¹, ha₂, ?_⟩
  rw [← hc₁V]
  apply map_conj_congr
  intro v hv
  have e1 : c₁ * (d₀ * a₁)⁻¹ * (d₀ * r) * v * (c₁ * (d₀ * a₁)⁻¹ * (d₀ * r))⁻¹ =
      (c₁ * (d₀ * a₁)⁻¹ * d₀) * (r * v * r⁻¹) * (c₁ * (d₀ * a₁)⁻¹ * d₀)⁻¹ := by group
  rw [e1, hra v hv]
  group

theorem eq_one_or_phi_z (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) {z : G}
    (hz : HZ T (Pg x Kb T) z) (h8 : 8 ≤ Nat.card (Pg x Kb T)) {c : MulAut ↥Kb} (hc : c ∈ N.P)
    (hcc : ∀ a ∈ N.P, c * a = a * c) : c = 1 ∨ c = phig x Kb z := by
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  right
  obtain ⟨m, hm, ⟨e₀⟩⟩ := NP_dihedral (e := e) (N := N) h.hF h12c
  have hNZ : NeZero (2 ^ m) := ⟨by positivity⟩
  have hk : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hcard : Nat.card ↥N.P = Nat.card (Pg x Kb T) := (Nat.card_congr (PgEquiv h).toEquiv).symm
  have hm2 : 2 ^ m ≠ 2 := by
    intro h2
    have h3 : Nat.card ↥N.P = 2 * 2 ^ m := by
      rw [Nat.card_congr e₀.toEquiv, DihedralGroup.nat_card]
    omega
  have key : ∀ (w : MulAut ↥Kb) (hw : w ∈ N.P), (∀ a ∈ N.P, w * a = a * w) → w ≠ 1 →
      e₀ ⟨w, hw⟩ = Dihedral.z₀ (2 ^ m) := by
    intro w hw hwc hw1
    have hsq : (⟨w, hw⟩ : ↥N.P) * ⟨w, hw⟩ = 1 :=
      Dihedral.central_sq_of_equiv e₀ hk (z := ⟨w, hw⟩) (fun y => Subtype.ext (hwc y y.2))
    have hw2 : e₀ ⟨w, hw⟩ * e₀ ⟨w, hw⟩ = 1 := by rw [← map_mul, hsq, map_one]
    refine Dihedral.eq_z₀_of_central hk hm2 hw2 ?_ ?_
    · intro h1
      apply hw1
      have := e₀.injective (h1.trans e₀.map_one.symm)
      exact congrArg Subtype.val this
    · intro y
      obtain ⟨a, rfl⟩ := e₀.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hwc a a.2)
  have hzP : phig x Kb z ∈ N.P := (h.hPN _).2 ⟨z, hz.z_mem_P, rfl⟩
  have hzC : z ∈ Cx x := ((mem_Kg x Kb).1 hz.z_mem_P.2).1
  have hzc : ∀ a ∈ N.P, phig x Kb z * a = a * phig x Kb z := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := (h.hPN a).1 ha
    have hpC : p ∈ Cx x := h.T_le_C hp.1
    rw [← phig_mul x Kb hzC hpC, ← phig_mul x Kb hpC hzC, hz.z_central p hp.1]
  have hz1 : phig x Kb z ≠ 1 := by
    intro h1
    apply hz.z_ne_one
    exact h.phig_inj_P hz.z_mem_P (Pg x Kb T).one_mem (by rw [h1, phig_one])
  have h1 := key c hc hcc hc1
  have h2 := key (phig x Kb z) hzP hzc hz1
  have := e₀.injective (h1.trans h2.symm)
  exact congrArg Subtype.val this

end CFSG.GH74.GLS.Stage1.Thm6.Glue
