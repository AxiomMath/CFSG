module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFOdd

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound


section B

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem Bsub_le_Cen_nf {g : G} (hAz : ∀ a ∈ OddCore z, zc z g * a = a * zc z g) : Bsub z g ≤ Cen z := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_Bsub.1 hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hAz a ha
  simp only [zc] at h1
  calc g * a * g⁻¹ * z = g * (a * (g⁻¹ * z * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * z * g) * a) * g⁻¹ := by rw [← h1]
    _ = z * (g * a * g⁻¹) := by group

omit [Finite G] in
theorem Bsub_comm_t {g : G} : ∀ b ∈ Bsub z g, b * (g * z * g⁻¹) = (g * z * g⁻¹) * b := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_Bsub.1 hb
  have haC : a ∈ Cen z := (Subgroup.map_subtype_le _ ha : a ∈ Cen z)
  have h1 : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.1 haC
  calc g * a * g⁻¹ * (g * z * g⁻¹) = g * (a * z) * g⁻¹ := by group
    _ = g * (z * a) * g⁻¹ := by rw [h1]
    _ = g * z * g⁻¹ * (g * a * g⁻¹) := by group

theorem nf_F_inf_B (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) {g : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (htS : g * z * g⁻¹ ∈ S) (htz : g * z * g⁻¹ ≠ z) :
    ∀ x ∈ F20 z, x ∈ Bsub z g → x = 1 := by
  have htS' : zc z g⁻¹ ∈ S := by
    have : zc z g⁻¹ = g * z * g⁻¹ := by simp [zc]
    rw [this]; exact htS
  have hnot : zc z g⁻¹ ∉ zpowers z := by
    intro hmem
    have e : zc z g⁻¹ = g * z * g⁻¹ := by simp [zc]
    rw [e] at hmem
    rcases eq_one_or_eq_of_mem_zpowers hz2 hmem with h1 | h1
    · have h2 : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [h1] at h2
      apply hz1
      rw [h2]; group
    · exact htz h1
  have hbot := h11 G z k S M hF hMC hT g⁻¹ htS' hnot
  intro x hxF hxB
  obtain ⟨a, ha, rfl⟩ := mem_Bsub.1 hxB
  have hxA : g * a * g⁻¹ ∈ Ag z g⁻¹ := by
    show g * a * g⁻¹ ∈ conjugate (OddCore z) g⁻¹
    rw [L20.mem_conjugate_iff]
    simpa [mul_assoc] using ha
  have : g * a * g⁻¹ ∈ F20 z ⊓ Ag z g⁻¹ := ⟨hxF, hxA⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.mp this

theorem nf_F_comm_B (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) {g : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (htS : g * z * g⁻¹ ∈ S) (htz : g * z * g⁻¹ ≠ z)
    (hAt : ∀ a ∈ OddCore z, a * (g * z * g⁻¹) = (g * z * g⁻¹) * a)
    (hBC : Bsub z g ≤ Cen z) : ∀ f ∈ F20 z, ∀ b ∈ Bsub z g, f * b = b * f := by
  intro f hf b hb
  have hfA : f ∈ OddCore z := F20_le_OddCore z hf
  have h1 : f * b * f⁻¹ ∈ Bsub z g := conj_mem_Bsub (hAt f hfA) b hb
  have hc : f * b * f⁻¹ * b⁻¹ ∈ Bsub z g := (Bsub z g).mul_mem h1 ((Bsub z g).inv_mem hb)
  have hcF : f * b * f⁻¹ * b⁻¹ ∈ F20 z := by
    have := (F20 z).mul_mem hf (F20_conj_mem z (hBC hb) ((F20 z).inv_mem hf))
    simpa [mul_assoc] using this
  have := nf_F_inf_B h11 hF hMC hT hz2 hz1 htS htz _ hcF hc
  calc f * b = (f * b * f⁻¹ * b⁻¹) * b * f := by group
    _ = b * f := by rw [this]; group

theorem nf_A_inf_B (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) {g : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (htS : g * z * g⁻¹ ∈ S) (htz : g * z * g⁻¹ ≠ z)
    (hAt : ∀ a ∈ OddCore z, a * (g * z * g⁻¹) = (g * z * g⁻¹) * a)
    (hBC : Bsub z g ≤ Cen z) : ∀ x ∈ OddCore z, x ∈ Bsub z g → x = 1 := by
  intro x hxA hxB
  have hxF : x ∈ F20 z := oddCore_centralizer_le_F z hxA
    (fun f hf => nf_F_comm_B h11 hF hMC hT hz2 hz1 htS htz hAt hBC f hf x hxB)
  exact nf_F_inf_B h11 hF hMC hT hz2 hz1 htS htz x hxF hxB

end B

section W

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

theorem exists_invol_lift (z : G) {x : ↥(Cen z)} (hx : toBar z x * toBar z x = 1) :
    ∃ w : ↥(Cen z), w * w = 1 ∧ toBar z w = toBar z x ∧ ∀ c : ↥(Cen z), c * x = x * c → c * w = w * c := by
  have hker : x * x ∈ (toBar z).ker := by
    rw [MonoidHom.mem_ker, map_mul]; exact hx
  have hodd : Odd (orderOf (x * x)) :=
    (odd_card_ker_toBar z).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hker)
  set o := orderOf (x * x) with ho
  refine ⟨x ^ o, ?_, ?_, ?_⟩
  · calc x ^ o * x ^ o = (x * x) ^ o := by rw [← pow_add, ← two_mul, pow_mul, sq]
      _ = 1 := pow_orderOf_eq_one _
  · obtain ⟨m, hm⟩ := hodd
    rw [map_pow, hm, pow_succ, pow_mul, show toBar z x ^ 2 = 1 by rw [sq]; exact hx, one_pow, one_mul]
  · intro c hc
    exact ((Commute.pow_right (show Commute c x from hc) o)).eq


open CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2 in
theorem NFCtx.exists_w (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G} (hg : GoodInvolution z S L₁ L₂ q u) :
    ∃ (w : G) (hwC : w ∈ Cen z), w * w = 1 ∧ w ∈ Em (Cen z) ∧ w * u = u * w ∧
      toBar z ⟨w, hwC⟩ ∉ L₁ ⊓ L₂ := by
  have huC : u ∈ Cen z := h.SC hg.1
  obtain ⟨hO₁, hO₂⟩ := h.outer_of_good hg
  have p₁ := pair₁_of_stage1 h.pair
  have p₂ := pair₂_of_stage1 h.pair
  have hz₀ := h.zbar_mem
  have hz₀' : toBar z ⟨z, mem_Cen_self z⟩ ∈ L₂ ⊓ L₁ := by rw [inf_comm]; exact hz₀
  have hz01 : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
    intro h1
    have := eq_one_of_toBar_eq_one z (x := ⟨z, mem_Cen_self z⟩) (Subtype.ext h.z2) h1
    exact h.z1 (congrArg Subtype.val this)
  have hzz : toBar z ⟨z, mem_Cen_self z⟩ * toBar z ⟨z, mem_Cen_self z⟩ = 1 := p₁.sq_of_mem_inf hz₀
  obtain ⟨a₁, ha₁, ha₁z, ha₁inv⟩ := exists_inv_a hO₁ p₁ hz₀ hz01
  obtain ⟨a₂, ha₂, ha₂z, ha₂inv⟩ := exists_inv_a hO₂ p₂ hz₀' hz01
  set ū := toBar z ⟨u, huC⟩ with hū
  have hcomm : a₁ * a₂ = a₂ * a₁ := p₁.comm a₁ ha₁ a₂ ha₂
  have hw2 : (a₁ * a₂) * (a₁ * a₂) = 1 := by
    calc (a₁ * a₂) * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
      _ = a₁ * (a₁ * a₂) * a₂ := by rw [← hcomm]
      _ = (a₁ * a₁) * (a₂ * a₂) := by group
      _ = 1 := by rw [ha₁z, ha₂z]; exact hzz
  have hwu : ū * (a₁ * a₂) = (a₁ * a₂) * ū := by
    have e1 : ū * a₁ = a₁⁻¹ * ū := by
      have := ha₁inv
      calc ū * a₁ = (ū * a₁ * ū⁻¹) * ū := by group
        _ = a₁⁻¹ * ū := by rw [this]
    have e2 : ū * a₂ = a₂⁻¹ * ū := by
      have := ha₂inv
      calc ū * a₂ = (ū * a₂ * ū⁻¹) * ū := by group
        _ = a₂⁻¹ * ū := by rw [this]
    have hinv : (a₁ * a₂)⁻¹ = a₁ * a₂ := inv_eq_of_mul_eq_one_right hw2
    have hcomm' : a₁⁻¹ * a₂⁻¹ = a₂⁻¹ * a₁⁻¹ := by
      have := congrArg (fun x => x⁻¹) hcomm
      simp only [mul_inv_rev] at this
      exact this.symm
    calc ū * (a₁ * a₂) = (ū * a₁) * a₂ := by group
      _ = a₁⁻¹ * (ū * a₂) := by rw [e1]; group
      _ = a₁⁻¹ * (a₂⁻¹ * ū) := by rw [e2]
      _ = (a₁⁻¹ * a₂⁻¹) * ū := by group
      _ = (a₁ * a₂)⁻¹ * ū := by rw [hcomm', mul_inv_rev]
      _ = a₁ * a₂ * ū := by rw [hinv]
  have hu2 : (⟨u, huC⟩ : ↥(Cen z)) * ⟨u, huC⟩ = 1 := Subtype.ext (sq_of_good hg)
  obtain ⟨x, hxbar, hxc⟩ := exists_lift_centralizer z hu2 (m := a₁ * a₂) hwu.symm
  obtain ⟨w, hw2', hwbar, hwc⟩ := exists_invol_lift z (x := x) (by rw [hxbar]; exact hw2)
  have hwbar' : toBar z w = a₁ * a₂ := hwbar.trans hxbar
  have hwx : (⟨u, huC⟩ : ↥(Cen z)) * w = w * ⟨u, huC⟩ := hwc _ hxc.symm
  have hmem : a₁ * a₂ ∈ L₁ ⊔ L₂ := Subgroup.mul_mem_sup ha₁ ha₂
  have hnot : a₁ * a₂ ∉ L₁ ⊓ L₂ := by
    intro hI
    have h2 : a₂ ∈ L₁ := by
      have : a₂ = a₁⁻¹ * (a₁ * a₂) := by group
      rw [this]
      exact L₁.mul_mem (L₁.inv_mem ha₁) hI.1
    have h3 : a₂ * a₂ = 1 := p₁.sq_of_mem_inf ⟨h2, ha₂⟩
    rw [ha₂z] at h3
    exact hz01 h3
  have hw2G : (w : G) * (w : G) = 1 := congrArg Subtype.val hw2'
  refine ⟨(w : G), w.2, hw2G, ?_, ?_, ?_⟩
  · apply h.comp.mem_layer (w : G) w.2 hw2G
    have : toBar z ⟨(w : G), w.2⟩ = a₁ * a₂ := hwbar'
    rw [this]; exact hmem
  · exact (congrArg Subtype.val hwx).symm
  · have : toBar z ⟨(w : G), w.2⟩ = a₁ * a₂ := hwbar'
    rw [this]; exact hnot


end W

section Bbar

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

theorem NFCtx.Bbar_data (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {t g : G} (htg : g * z * g⁻¹ = t)
    (htC : t ∈ Cen z) (ht2 : t * t = 1) :
    (∀ y ∈ barOf z (Bsub z g), Odd (orderOf y)) ∧
    (∀ y ∈ barOf z (Bsub z g), y ∈ normalizer (L₁ : Set (CentralizerBar z))) ∧
    (∀ y ∈ barOf z (Bsub z g), y ∈ normalizer (L₂ : Set (CentralizerBar z))) ∧
    (∀ y ∈ barOf z (Bsub z g), y * toBar z ⟨t, htC⟩ = toBar z ⟨t, htC⟩ * y) ∧
    (∀ c : CentralizerBar z, c * toBar z ⟨t, htC⟩ = toBar z ⟨t, htC⟩ * c →
      ∀ y ∈ barOf z (Bsub z g), c * y * c⁻¹ ∈ barOf z (Bsub z g)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨b, hb, hbB, rfl⟩ := bar_mem_barOf_iff.1 hy
    have h1 := orderOf_map_dvd (toBar z) (⟨b, hb⟩ : ↥(Cen z))
    have h2 : orderOf (⟨b, hb⟩ : ↥(Cen z)) = orderOf b := Subgroup.orderOf_mk _ _
    rw [h2] at h1
    exact Odd.of_dvd_nat (Bsub_odd b hbB) h1
  · intro y hy
    obtain ⟨b, hb, hbB, rfl⟩ := bar_mem_barOf_iff.1 hy
    have hN := mem_normalizer_K₁_of_odd h.comp hb (Bsub_odd b hbB)
    have := bar_mem_normalizer_image hb hN
    rwa [h.comp.bar₁] at this
  · intro y hy
    obtain ⟨b, hb, hbB, rfl⟩ := bar_mem_barOf_iff.1 hy
    have hN := mem_normalizer_K₂_of_odd h.comp hb (Bsub_odd b hbB)
    have := bar_mem_normalizer_image hb hN
    rwa [h.comp.bar₂] at this
  · intro y hy
    obtain ⟨b, hb, hbB, rfl⟩ := bar_mem_barOf_iff.1 hy
    have hbt : b * t = t * b := by rw [← htg]; exact Bsub_comm_t b hbB
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hbt
  · intro c hc y hy
    obtain ⟨b, hb, hbB, rfl⟩ := bar_mem_barOf_iff.1 hy
    have ht2' : (⟨t, htC⟩ : ↥(Cen z)) * ⟨t, htC⟩ = 1 := Subtype.ext ht2
    obtain ⟨x, hxc, hxt⟩ := CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2.exists_lift_centralizer z ht2' (m := c) hc
    have hxt' : (x : G) * (g * z * g⁻¹) = (g * z * g⁻¹) * (x : G) := by rw [htg]; exact congrArg Subtype.val hxt
    have h1 := conj_mem_Bsub hxt' b hbB
    refine bar_mem_barOf_iff.2 ⟨(x : G) * b * (x : G)⁻¹, (Cen z).mul_mem ((Cen z).mul_mem x.2 hb) ((Cen z).inv_mem x.2), h1, ?_⟩
    rw [← hxc]
    have : (⟨(x : G) * b * (x : G)⁻¹, (Cen z).mul_mem ((Cen z).mul_mem x.2 hb) ((Cen z).inv_mem x.2)⟩ : ↥(Cen z)) =
        x * ⟨b, hb⟩ * x⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]


theorem NFCtx.not_swap_mem_sup (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {x : G} (hx : TwoClassData G z S L₁ L₂ q x)
    {e : G} (heC : e ∈ Cen z) (he2 : e * e = 1) (hexc : IsConj x e) (hns : ¬ Swaps z e L₁ L₂) :
    toBar z ⟨e, heC⟩ ∈ L₁ ⊔ L₂ := by
  by_contra hnot
  have heo : orderOf e = 2 := orderOf_eq_two_of_conj hx.x_inv hexc
  obtain ⟨kk, hkk, hmem⟩ := exists_conj_mem_S h.ctx.sylow heC heo
  set e' := kk⁻¹ * e * kk with he'
  have he'2 : e' * e' = 1 := by
    calc e' * e' = kk⁻¹ * (e * e) * kk := by simp only [he']; group
      _ = 1 := by rw [he2]; group
  have he'1 : e' ≠ 1 := by
    intro e1
    have : e = kk * e' * kk⁻¹ := by simp only [he']; group
    rw [e1] at this
    have h1 : e = 1 := by rw [this]; group
    rw [h1, orderOf_one] at heo
    omega
  have hns' : ¬ Swaps z e' L₁ L₂ := fun hsw' => hns (by
    have := swaps_conj h.pair hkk hsw'
    have e1 : kk * e' * kk⁻¹ = e := by simp only [he']; group
    rwa [e1] at this)
  have hLC' : e' ∉ LC z := by
    intro hLC'
    apply hnot
    have hb' : toBar z ⟨e', h.SC hmem⟩ ∈ LBar z :=
      ⟨⟨e', h.SC hmem⟩, Subgroup.mem_subgroupOf.mpr hLC', rfl⟩
    have h1 := (LBar_normal z).conj_mem _ hb' (toBar z ⟨kk, hkk⟩)
    have e1 : toBar z ⟨kk, hkk⟩ * toBar z ⟨e', h.SC hmem⟩ * (toBar z ⟨kk, hkk⟩)⁻¹ = toBar z ⟨e, heC⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [he']
      show kk * (kk⁻¹ * e * kk) * kk⁻¹ = e
      group
    rw [e1] at h1
    rwa [h.pair.prod.1]
  have hn := (h.swaps_or_nrm hmem).resolve_left hns'
  have hgood := h.good_of_nrm hmem he'2 he'1 hn.1 hn.2 hLC'
  have hc := h.fuse e' hgood
  have hce : IsConj e' e := isConj_iff.2 ⟨kk, by simp only [he']; group⟩
  exact hx.x_nonCentral (isCentralInvolution_of_conj' h.ctx.central (hc.trans (hce.trans hexc.symm)))


omit [Finite G] in
theorem exists_equiv_barOf {B : Subgroup G} (hBC : B ≤ Cen z) (hinj : ∀ b ∈ B, b ∈ OddCore z → b = 1) :
    Nonempty (↥B ≃* ↥(barOf z B)) := by
  let φ : ↥B →* CentralizerBar z := (toBar z).comp (Subgroup.inclusion hBC)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h1 : (Subgroup.inclusion hBC b) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 hb
    have h2 : (b : G) ∈ OddCore z := ⟨_, h1, rfl⟩
    exact Subtype.ext (hinj b b.2 h2)
  have hr : φ.range = barOf z B := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact bar_mem_barOf_iff.2 ⟨b, hBC b.2, b.2, rfl⟩
    · intro hy
      obtain ⟨b, hb, hbB, rfl⟩ := bar_mem_barOf_iff.1 hy
      exact ⟨⟨b, hbB⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr)⟩


open CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2 in
theorem nf_embed (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hT : TypeCl z k S) (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {t : G} (hg : GoodInvolution z S L₁ L₂ q t) :
    IsCyclic ↥(OddCore z) ∧ Nat.card ↥(OddCore z) ∣
      Nat.card ↥(pPrimeCoreOf 2 (L₁ ⊓ centralizer ({toBar z ⟨t, h.SC hg.1⟩} : Set (CentralizerBar z)))) := by
  have hz2 := h.z2
  have hz1 := h.z1
  obtain ⟨hne, hnsw, hLC, hconj, hn₁, hn₂⟩ := h.good_props hg
  have htS := hg.1
  have htC := h.SC htS
  have ht2 := sq_of_good hg
  obtain ⟨x, hx⟩ := h.two
  obtain ⟨g', hzc', hg'S⟩ := h.exists_g htC hconj
  set g := g'⁻¹ with hgdef
  have hgt : g * z * g⁻¹ = t := by
    have := hzc'
    simp only [zc] at this
    simpa [hgdef] using this
  have hz''eq : zc z g = g' * z * g'⁻¹ := by simp [zc, hgdef]
  have hz''S : zc z g ∈ S := hz''eq ▸ hg'S
  have hz''C : zc z g ∈ Cen z := h.SC hz''S
  have hz''conj : IsConj z (zc z g) := by rw [hz''eq]; exact isConj_conj_self z g'
  have hz''2 := mul_self_eq_one_of_conj' hz2 hz''conj
  have hz''ne : zc z g ≠ z := by
    intro e
    apply hne
    have hcomm : z * g = g * z := by
      calc z * g = g * (g⁻¹ * z * g) := by group
        _ = g * z := by rw [show g⁻¹ * z * g = z from e]
    rw [← hgt]
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hcomm]
      _ = z := by group
  have hz''1 : zc z g ≠ 1 := by
    intro e
    apply hz1
    have : z = g * zc z g * g⁻¹ := by simp only [zc]; group
    rw [this, e]; group
  have hz''LC : zc z g ∉ LC z := by
    intro hLC'
    have hbar : toBar z ⟨zc z g, hz''C⟩ ∈ L₁ ⊔ L₂ := by
      rw [h.pair.prod.1]; exact ⟨⟨zc z g, hz''C⟩, Subgroup.mem_subgroupOf.mpr hLC', rfl⟩
    have hem := h.comp.mem_layer _ hz''C hz''2 hbar
    exact hz''ne (layer_conj_eq_of_two h.ctx.central hx _ hem hz''conj)
  have hz''nsw : ¬ Swaps z (zc z g) L₁ L₂ := by
    intro hsw
    have := h.partner_swaps hz''S hz''conj hsw (g := g) rfl (by rw [hgt]; exact htS)
    rw [hgt] at this
    exact hnsw this
  have hnrm'' := (h.swaps_or_nrm hz''S).resolve_left hz''nsw
  have hz''good := h.good_of_nrm hz''S hz''2 hz''1 hnrm''.1 hnrm''.2 hz''LC
  have hAt : ∀ a ∈ OddCore z, a * (g * z * g⁻¹) = (g * z * g⁻¹) * a := by
    intro a ha
    rw [hgt]
    exact (h.good_centralizes_A h11 hF hMC hT hg a ha).symm
  have hAz : ∀ a ∈ OddCore z, zc z g * a = a * zc z g := fun a ha =>
    h.good_centralizes_A h11 hF hMC hT hz''good a ha
  have hBC : Bsub z g ≤ Cen z := Bsub_le_Cen_nf hAz
  have hgtS : g * z * g⁻¹ ∈ S := by rw [hgt]; exact htS
  have hgtz : g * z * g⁻¹ ≠ z := by rw [hgt]; exact hne
  have hAB := nf_A_inf_B h11 hF hMC hT hz2 hz1 hgtS hgtz hAt hBC
  obtain ⟨hBodd, hBn₁, hBn₂, hBcomm, hBnc⟩ := h.Bbar_data hgt htC ht2
  obtain ⟨hO₁, hO₂⟩ := h.outer_of_good hg
  have p₁ := pair₁_of_stage1 h.pair
  have p₂ := pair₂_of_stage1 h.pair
  have hC := centralizer_sup_le h.pair
  have hz₀ := h.zbar_mem
  have hz01 : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
    intro h1
    have := eq_one_of_toBar_eq_one z (x := ⟨z, mem_Cen_self z⟩) (Subtype.ext hz2) h1
    exact hz1 (congrArg Subtype.val this)
  have hz₀c : ∀ y : CentralizerBar z, y * toBar z ⟨z, mem_Cen_self z⟩ = toBar z ⟨z, mem_Cen_self z⟩ * y :=
    Subgroup.mem_center_iff.mp (toBar_z_mem_center z)
  obtain ⟨w, hwC, hw2, hwE, hwz, hwnot⟩ := h.exists_w hz''good
  set e := g * w * g⁻¹ with he
  have heC : e ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : w * zc z g = zc z g * w := hwz
    simp only [zc] at h1
    calc e * z = g * (w * (g⁻¹ * z * g)) * g⁻¹ := by simp only [he]; group
      _ = g * ((g⁻¹ * z * g) * w) * g⁻¹ := by rw [h1]
      _ = z * e := by simp only [he]; group
  have he2 : e * e = 1 := by
    calc e * e = g * (w * w) * g⁻¹ := by simp only [he]; group
      _ = 1 := by rw [hw2]; group
  have hec : ∀ b ∈ Bsub z g, e * b = b * e := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_Bsub.1 hb
    have h1 : a * w = w * a := h.comp.oddcomm a ha w hwE
    calc e * (g * a * g⁻¹) = g * (w * a) * g⁻¹ := by simp only [he]; group
      _ = g * (a * w) * g⁻¹ := by rw [h1]
      _ = (g * a * g⁻¹) * e := by simp only [he]; group
  have hw1 : w ≠ 1 := fun e1 => hwnot (by
    rw [show (⟨w, hwC⟩ : ↥(Cen z)) = 1 from Subtype.ext e1, map_one]; exact (L₁ ⊓ L₂).one_mem)
  have hwz' : w ≠ z := fun e1 => hwnot (by subst e1; exact hz₀)
  have hword : orderOf w = 2 := orderOf_eq_prime (by rw [← sq] at hw2; exact hw2) hw1
  have hxw : IsConj x w := (hx.invol_L w (em_le_LC z hwE) hword hwz').1
  have hxe : IsConj x e := hxw.trans (isConj_iff.2 ⟨g, rfl⟩)
  have hBinj : ∀ b ∈ Bsub z g, b ∈ OddCore z → b = 1 := fun b hb ha => hAB b ha hb
  have hec' : ∀ y ∈ barOf z (Bsub z g), toBar z ⟨e, heC⟩ * y = y * toBar z ⟨e, heC⟩ := by
    intro y hy
    obtain ⟨b, hb, hbB, rfl⟩ := bar_mem_barOf_iff.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hec b hbB)
  by_cases hsw : Swaps z e L₁ L₂
  ·
    obtain ⟨heC', hcj₁, hcj₂⟩ := hsw
    have he₁ : ∀ a ∈ L₁, toBar z ⟨e, heC⟩ * a * (toBar z ⟨e, heC⟩)⁻¹ ∈ L₂ := fun a ha => by
      have : a ∈ conjugate L₂ (toBar z ⟨e, heC⟩) := by rw [hcj₂]; exact ha
      exact bar_mem_conjugate_iff.1 this
    have he₂ : ∀ a ∈ L₂, toBar z ⟨e, heC⟩ * a * (toBar z ⟨e, heC⟩)⁻¹ ∈ L₁ := fun a ha => by
      have : a ∈ conjugate L₁ (toBar z ⟨e, heC⟩) := by rw [hcj₁]; exact ha
      exact bar_mem_conjugate_iff.1 this
    obtain ⟨φ, hφ⟩ := yo_embed p₁ p₂ hC hO₁ hBodd hBn₁ hBcomm hBnc he₁ he₂ hec'
    obtain ⟨hcyc, -⟩ := hO₁.cyclic_card
    have hXcyc : IsCyclic ↥(pPrimeCoreOf 2 (L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z)))) :=
      (Subgroup.equivMapOfInjective (pPrimeCore 2 ↥(L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z))))
        (L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z))).subtype
        (L₁ ⊓ centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z))).subtype_injective).isCyclic.1 inferInstance
    have hBcyc : IsCyclic ↥(barOf z (Bsub z g)) := isCyclic_of_injective φ hφ
    obtain ⟨eqBB⟩ := exists_equiv_barOf hBC hBinj
    have eqA : ↥(OddCore z) ≃* ↥(Bsub z g) :=
      Subgroup.equivMapOfInjective (OddCore z) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    refine ⟨(eqA.trans eqBB).isCyclic.2 hBcyc, ?_⟩
    have hdvd := Subgroup.card_dvd_of_injective φ hφ
    rwa [← Nat.card_congr (eqA.trans eqBB).toEquiv] at hdvd
  ·
    exfalso
    have hemem : toBar z ⟨e, heC⟩ ∈ L₁ ⊔ L₂ := h.not_swap_mem_sup hx heC he2 hxe hsw
    have hweq : w = g⁻¹ * e * g := by simp only [he]; group
    have heinf : toBar z ⟨e, heC⟩ ∉ L₁ ⊓ L₂ := by
      intro hI
      have hcase : (⟨e, heC⟩ : ↥(Cen z)) = 1 ∨ (⟨e, heC⟩ : ↥(Cen z)) = ⟨z, mem_Cen_self z⟩ := by
        rcases p₁.inf_cases hz₀ hz01 hI with h1 | h1
        · exact Or.inl (eq_one_of_toBar_eq_one z (Subtype.ext he2) h1)
        · exact eq_one_or_eq_z_of_toBar z hz2 (Subtype.ext he2) (Or.inr h1)
      rcases hcase with h2 | h2
      · apply hw1
        have e1 : e = 1 := congrArg Subtype.val h2
        rw [hweq, e1]; group
      · have e1 : e = z := congrArg Subtype.val h2
        rw [e1] at hxe
        exact hx.x_nonCentral (isCentralInvolution_of_conj' h.ctx.central hxe.symm)
    have hB1 := yo_noL p₁ p₂ hC hz₀ hz01 hz₀c hO₁ hO₂ hBodd hBn₁ hBn₂ hBcomm hBnc
      (e := toBar z ⟨e, heC⟩) (by rw [← map_mul]; exact (by
        have : (⟨e, heC⟩ : ↥(Cen z)) * ⟨e, heC⟩ = 1 := Subtype.ext he2
        rw [this, map_one])) hemem heinf hec'
    have hAne : OddCore z ≠ ⊥ := by
      have := hF.odd_ne
      rw [hMC] at this
      exact this
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
    have hbB : g * (a : G) * g⁻¹ ∈ Bsub z g := mem_Bsub.2 ⟨a, a.2, rfl⟩
    have hbC := hBC hbB
    have hbar : toBar z ⟨g * (a : G) * g⁻¹, hbC⟩ = 1 :=
      hB1 _ (bar_mem_barOf_iff.2 ⟨_, hbC, hbB, rfl⟩)
    have hbA : g * (a : G) * g⁻¹ ∈ OddCore z := by
      have h2 : (⟨g * (a : G) * g⁻¹, hbC⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
        (QuotientGroup.eq_one_iff _).1 hbar
      exact ⟨_, h2, rfl⟩
    have h3 := hAB _ hbA hbB
    apply ha1
    apply Subtype.ext
    have : (a : G) = g⁻¹ * (g * (a : G) * g⁻¹) * g := by group
    rw [this, h3]
    simp

end Bbar


end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
