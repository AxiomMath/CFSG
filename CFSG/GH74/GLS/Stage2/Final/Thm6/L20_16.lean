module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_16Cnt
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_16I
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_16J

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.ABGLocalTools CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Final

variable {G : Type} [Group G]

theorem comm_of_sq_one {X : Subgroup G} (hX : ∀ x ∈ X, x * x = 1) : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  intro a ha b hb
  have hab := hX (a * b) (X.mul_mem ha hb)
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hX a ha)
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hX b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h1, h2]

theorem Q4_sq {z y : G} (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) :
    ∀ x ∈ Q4 z y hz2 hy2 hzy, x * x = 1 := by
  rintro x (rfl | rfl | rfl | rfl)
  · simp
  · exact hz2
  · exact hy2
  · exact yzyz_eq hz2 hy2 hzy

theorem Q4_le {z y : G} (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) {K : Subgroup G}
    (hz : z ∈ K) (hy : y ∈ K) : Q4 z y hz2 hy2 hzy ≤ K := by
  rintro x (rfl | rfl | rfl | rfl)
  · exact K.one_mem
  · exact hz
  · exact hy
  · exact K.mul_mem hy hz

theorem central_involution_of_conj16 {z x : G} (hz : IsCentralInvolution z) (h : IsConj z x) :
    IsCentralInvolution x := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group

variable [Finite G]

theorem final16 {z u : G} {S R I J : Subgroup G}
    (hrank : pRank 2 G ≤ 4) (hSsyl : IsSylowOf 2 S ⊤)
    (hSR : ∀ a ∈ S, ∀ b ∈ S, a ∉ R → b ∉ R → a⁻¹ * b ∈ R)
    (hzR : ∀ w ∈ R, w * w = 1 → IsConj z w → w = z)
    (hcen : ∀ t : G, t * t = 1 → t ≠ 1 →
      (∃ T : Sylow 2 G, t ∈ (T : Subgroup G) ∧ ∀ s ∈ (T : Subgroup G), s * t = t * s) → IsConj z t)
    (hu : ¬ IsConj z u)
    (hIJ : ∀ a ∈ I, ∀ b ∈ J, a * b = b * a)
    (hI4 : ∃ x₁ ∈ I, ∃ x₂ ∈ I, x₁ * x₁ = 1 ∧ x₂ * x₂ = 1 ∧ x₁ * x₂ = x₂ * x₁ ∧ x₁ ≠ 1 ∧ x₂ ≠ 1 ∧ x₁ ≠ x₂)
    (hIc : ∀ a ∈ I, ∀ b ∈ I, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → ∃ c ∈ I, c * a * c⁻¹ = b)
    (hIz : ∀ x ∈ I, x * x = 1 → x ≠ 1 → ¬ IsConj z x)
    (hIcen : ∀ w ∈ I, (∀ v ∈ I, v * w = w * v) → w * w = 1 → w = 1)
    (huJ : u ∈ J) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hJ4 : ∃ v ∈ J, v * v = 1 ∧ v ≠ 1 ∧ v ≠ u ∧ u * v = v * u)
    (hJc : ∀ a ∈ J, ∀ b ∈ J, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → ∃ c ∈ J, c * a * c⁻¹ = b) : False := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hx₁2, hx₂2, hx₁₂, hx₁1, hx₂1, hx₁₂ne⟩ := hI4
  obtain ⟨v, hvJ, hv2, hv1, hvu, huv⟩ := hJ4
  have hXI : Q4 x₁ x₂ hx₁2 hx₂2 hx₁₂ ≤ I := Q4_le hx₁2 hx₂2 hx₁₂ hx₁ hx₂
  have hYJ : Q4 u v hu2 hv2 huv ≤ J := Q4_le hu2 hv2 huv huJ hvJ
  set X := Q4 x₁ x₂ hx₁2 hx₂2 hx₁₂ with hX
  set Y := Q4 u v hu2 hv2 huv with hY
  have hX2 : ∀ x ∈ X, x * x = 1 := Q4_sq hx₁2 hx₂2 hx₁₂
  have hY2 : ∀ y ∈ Y, y * y = 1 := Q4_sq hu2 hv2 huv
  have hXc := comm_of_sq_one hX2
  have hYc := comm_of_sq_one hY2
  have hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := fun x hx y hy => hIJ x (hXI hx) y (hYJ hy)
  have hbot : ∀ g ∈ X, g ∈ Y → g = 1 := fun g hgX hgY =>
    hIcen g (hXI hgX) (fun w hw => hIJ w hw g (hYJ hgY)) (hX2 g hgX)
  have hXcard : Nat.card X = 4 := card_Q4 hx₁2 hx₂2 hx₁₂ hx₁1 hx₂1 hx₁₂ne
  have hYcard : Nat.card Y = 4 := card_Q4 hu2 hv2 huv hu1 hv1 (Ne.symm hvu)
  obtain ⟨t, htD, ht2, ht1, T, htT, htc⟩ := central_involution_mem_D hrank hX2 hY2 hXc hYc hXY hbot hXcard hYcard
  have htz : IsConj z t := hcen t ht2 ht1 ⟨T, htT, htc⟩
  obtain ⟨xa, hxa, ya, hya, rfl⟩ := CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute hXY htD
  have hxa1 : xa ≠ 1 := by
    intro h1
    subst h1
    rw [one_mul] at htz ht1 ht2
    obtain ⟨c, hcJ, hc⟩ := hJc ya (hYJ hya) u huJ ht2 hu2 ht1 hu1
    exact hu (htz.trans (isConj_iff.mpr ⟨c, hc⟩))
  have hya1 : ya ≠ 1 := by
    intro h1
    subst h1
    rw [mul_one] at htz ht1 ht2
    exact hIz xa (hXI hxa) ht2 ht1 htz
  have hmix : ∀ x ∈ X, ∀ y ∈ Y, x ≠ 1 → y ≠ 1 → IsConj z (x * y) := by
    intro x hx y hy hx1 hy1
    obtain ⟨c₁, hc₁, hc₁e⟩ := hIc xa (hXI hxa) x (hXI hx) (hX2 xa hxa) (hX2 x hx) hxa1 hx1
    obtain ⟨c₂, hc₂, hc₂e⟩ := hJc ya (hYJ hya) y (hYJ hy) (hY2 ya hya) (hY2 y hy) hya1 hy1
    refine htz.trans (isConj_iff.mpr ⟨c₁ * c₂, ?_⟩)
    have e1 : c₂ * xa = xa * c₂ := (hIJ xa (hXI hxa) c₂ hc₂).symm
    have e2 : c₁ * y = y * c₁ := hIJ c₁ hc₁ y (hYJ hy)
    calc c₁ * c₂ * (xa * ya) * (c₁ * c₂)⁻¹ = c₁ * (c₂ * xa) * ya * c₂⁻¹ * c₁⁻¹ := by group
      _ = c₁ * (xa * c₂) * ya * c₂⁻¹ * c₁⁻¹ := by rw [e1]
      _ = (c₁ * xa) * (c₂ * ya * c₂⁻¹) * c₁⁻¹ := by group
      _ = (c₁ * xa) * y * c₁⁻¹ := by rw [hc₂e]
      _ = (c₁ * xa * c₁⁻¹) * (c₁ * y * c₁⁻¹) := by group
      _ = x * y := by rw [hc₁e, e2]; group
  obtain ⟨hD2, hDc⟩ := elementary_sup hX2 hY2 hXc hYc hXY
  have hDp : IsPGroup 2 ↥(X ⊔ Y) := fun d => ⟨1, by
    apply Subtype.ext
    show (d : G) ^ (2 ^ 1) = 1
    rw [pow_one, sq]
    exact hD2 d d.2⟩
  obtain ⟨c, hcS⟩ := exists_conj_le_sylow hSsyl hDp
  exact count16 hSR hzR hX2 hY2 hXY hbot (fun x hx => hcS x (Subgroup.mem_sup_left hx))
    (fun y hy => hcS y (Subgroup.mem_sup_right hy))
    ⟨x₁, Or.inr (Or.inl rfl), x₂, Or.inr (Or.inr (Or.inl rfl)), hx₁1, hx₂1, hx₁₂ne⟩
    ⟨u, Or.inr (Or.inl rfl), v, Or.inr (Or.inr (Or.inl rfl)), hu1, hv1, fun h => hvu h.symm⟩ hmix

end Final

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6.L20

theorem lemma20_16_thm (h12 : Lemma20_12) : Lemma20_16 := by
  intro G _ _ z k S M h hMC hpsp g hS h14 h15
  subst hMC
  have hctx : Stage2Ctx G z k S := h.ctx.ctx17.ctx
  have hSC : S ≤ Cen z := hctx.S_le_Cen
  have hz2 : z * z = 1 := by
    have := hctx.orderOf_z
    calc z * z = z ^ 2 := (sq z).symm
      _ = 1 := by rw [← this]; exact pow_orderOf_eq_one z
  have hz1' : z ≠ 1 := by
    intro h1
    have := hctx.orderOf_z
    rw [h1, orderOf_one] at this
    omega
  have h4a : pLayerOf 2 (Cen z) = Em (Cen z) := h.ctx.thm4.1
  obtain ⟨q, L₁, L₂, hpair, hswap⟩ := hS.swap
  obtain ⟨q', hk, L₁', L₂', hpsp4⟩ := hpsp
  have hT : TypeCl z k S := Or.inr ⟨q', hk, L₁', L₂', hpsp4⟩
  obtain ⟨-, h12b, h12c⟩ := h12 G z k S (Cen z) h rfl hT
  obtain ⟨K₁, K₂, hK⟩ := exists_compData hpair h4a
  have hyS : zc z g ∈ S := hS.y_mem
  have hyC : zc z g ∈ Cen z := hSC hyS
  have hy2 : zc z g * zc z g = 1 := by
    calc zc z g * zc z g = g⁻¹ * (z * z) * g := by simp only [zc]; group
      _ = 1 := by rw [hz2]; group
  have hyconj : IsConj z (zc z g) := isConj_iff.mpr ⟨g⁻¹, by simp [zc]⟩
  have hy1 : zc z g ≠ 1 := by
    intro h1
    apply hz1'
    have : z = g * zc z g * g⁻¹ := by simp only [zc]; group
    rw [this, h1]; group
  obtain ⟨hyC', hsw⟩ := swaps_cj hswap
  have hyne : zc z g ≠ z := by
    intro hyz
    have hcen : toBar z ⟨zc z g, hyC'⟩ ∈ center (CentralizerBar z) := by
      have := toBar_z_mem_center z
      have e : (⟨zc z g, hyC'⟩ : ↥(Cen z)) = ⟨z, mem_Cen_self z⟩ := Subtype.ext hyz
      rwa [e]
    have hfix : cj (toBar z ⟨zc z g, hyC'⟩) L₁ = L₁ :=
      cj_eq_iff.mpr (Subgroup.center_le_normalizer (L₁ : Set (CentralizerBar z)) hcen)
    exact hpair.ne (hfix.symm.trans hsw)
  have hzy : z * zc z g = zc z g * z := (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
  have hIy : Iy z g = Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G)) := by
    unfold Iy L20; rw [hK.layer]
  have hHy : Hy z g = centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G)) : Set G) := by
    unfold Hy; rw [hIy]
  have hIL : Iy z g ≤ Em (Cen z) := by
    refine (Subgroup.map_subtype_le _).trans ?_
    exact inf_le_left
  have hzH : z ∈ Hy z g := by
    rw [Hy]
    refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.map_subtype_le _ (hIL hi) : i ∈ Cen z))
  have hyH : zc z g ∈ Hy z g := by
    rw [Hy]
    refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
    have hiy : i ∈ L20 z ⊓ centralizer ({zc z g} : Set G) := Subgroup.map_subtype_le _ hi
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hiy).2
  have hab : Abs15 (Hy z g) z (zc z g) :=
    { hzH := hzH
      hyH := hyH
      hz2 := hz2
      hy2 := hy2
      hzy := hzy
      hne := hyne.symm
      hz1 := hz1'
      hy1 := hy1
      hu := hS.u_not
      hA := fun X hXH hXz hXp hyX => hA_of hpair hK hz2 hz1' hyC' hy2 hsw X (hHy ▸ hXH) hXz hXp hyX
      hF := fun e he => (h14 e he).2.2
      hO := fun N hNH hNn hNp huN =>
        hO_of hK hyC' (fun f hf => h12c _ hyS hyconj ⟨q, L₁, L₂, hpair, hswap⟩ f hf) h.odd_ne N
          (fun hh hhH n hn => hNn hh (hHy ▸ hhH) n hn) hNp huN }
  have hu2 : (zc z g * z) * (zc z g * z) = 1 := yzyz_eq hz2 hy2 hzy
  have hu1 : zc z g * z ≠ 1 := by
    intro h1
    apply hyne
    have : zc z g = z⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right hz2
  have huJ : zc z g * z ∈ Em (Hy z g) := h15.2
  obtain ⟨hJc, v, hvJ, hv2, hv1, hvu, huv⟩ := hab.jside huJ
  obtain ⟨hI4, hIc, hIcen⟩ := I_facts hpair hK hz2 hz1' hyC' hy2 hsw
  have hIEm : Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G)) ≤ Em (Cen z) := by
    rw [hK.layer]
    exact (Em_le _).trans inf_le_left
  have hIz : ∀ x ∈ Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G)), x * x = 1 → x ≠ 1 → ¬ IsConj z x := by
    intro x hx hx2 hx1 hconj
    have hxz : x = z := h12b x (hIEm hx) hconj
    apply hz1'
    rw [hxz] at hx
    refine hIcen z hx (fun w hw => ?_) hz2
    have hwC : w ∈ Cen z := Subgroup.map_subtype_le _ (hIEm hw)
    exact (Subgroup.mem_centralizer_singleton_iff.mp hwC)
  have hsup : LBar z = L₁ ⊔ L₂ := hpair.prod.1.symm
  have hbarLC : ∀ (w : G) (hw : w ∈ Cen z), w ∈ LC z → toBar z ⟨w, hw⟩ ∈ L₁ ⊔ L₂ := by
    intro w hw hLC
    rw [← hsup]
    exact ⟨⟨w, hw⟩, hLC, rfl⟩
  have hzR : ∀ w ∈ RC S z, w * w = 1 → IsConj z w → w = z := by
    intro w hw hw2 hwz
    have hwC : w ∈ Cen z := hSC hw.1
    exact h12b w (hK.mem_layer w hwC hw2 (hbarLC w hwC hw.2)) hwz
  obtain ⟨x₀, hx₀⟩ := hpsp4.two
  have hcen : ∀ t : G, t * t = 1 → t ≠ 1 →
      (∃ T : Sylow 2 G, t ∈ (T : Subgroup G) ∧ ∀ s ∈ (T : Subgroup G), s * t = t * s) → IsConj z t := by
    intro t ht2 ht1 hT'
    have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
    obtain ⟨T, htT, htc⟩ := hT'
    rcases hx₀.classes t hord with hzt | hxt
    · exact hzt
    · exact absurd (central_involution_of_conj16 (z := t) ⟨hord, T, htT, htc⟩ hxt.symm) hx₀.x_nonCentral
  exfalso
  refine final16 (R := RC S z) (I := Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G))) (J := Em (Hy z g))
    hctx.std.rank.2 hctx.sylow_top
    (fun a ha b hb haR hbR => inv_mul_mem_of_relIndex_two hpsp4.index ha hb haR hbR) hzR hcen hS.u_not
    (fun a ha b hb => ?_) hI4 hIc hIz hIcen huJ hu2 hu1 ⟨v, hvJ, hv2, hv1, hvu, huv⟩ hJc
  have hbH : b ∈ Hy z g := Em_le _ hb
  rw [hHy] at hbH
  exact Subgroup.mem_centralizer_iff.mp hbH a ha

end CFSG.GH74.GLS.Stage2.Final.Thm6
