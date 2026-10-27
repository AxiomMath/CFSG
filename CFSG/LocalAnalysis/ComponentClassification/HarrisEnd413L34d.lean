module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413L34c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma43
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndGroups

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

namespace HarrisEnd

@[expose] def omegaCenter {G : Type*} [Group G] (R : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ R ∧ (∀ r ∈ R, r * g = g * r) ∧ g ^ 2 = 1}
  one_mem' := ⟨one_mem R, fun r _ => by rw [mul_one, one_mul], one_pow 2⟩
  mul_mem' := by
    rintro a b ⟨haR, ha, ha2⟩ ⟨hbR, hb, hb2⟩
    refine ⟨mul_mem haR hbR, fun r hr => ?_, ?_⟩
    · rw [← mul_assoc, ha r hr, mul_assoc, hb r hr, ← mul_assoc]
    · rw [(show Commute a b from (ha b hbR).symm).mul_pow, ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haR, ha, ha2⟩
    refine ⟨inv_mem haR, fun r hr => ?_, by rw [inv_pow, ha2, inv_one]⟩
    have h := ha r hr
    calc r * a⁻¹ = a⁻¹ * (a * r) * a⁻¹ := by group
      _ = a⁻¹ * (r * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * r := by group

theorem le_omegaCenter_sup {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b = b * a) :
    zpowers a ⊔ zpowers b ≤ omegaCenter (zpowers a ⊔ zpowers b) := by
  have h1 : zpowers a ⊔ zpowers b ≤ centralizer ({a} : Set G) ⊓ centralizer {b} :=
    sup_le (zpowers_le.mpr (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
      mem_centralizer_singleton_iff.mpr hab⟩))
      (zpowers_le.mpr (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hab.symm,
        mem_centralizer_singleton_iff.mpr rfl⟩))
  have hcen : ∀ c ∈ ({a, b} : Set G), ∀ r ∈ zpowers a ⊔ zpowers b, r * c = c * r := by
    rintro c (rfl | rfl) r hr
    · exact (mem_centralizer_singleton_iff.mp (mem_inf.mp (h1 hr)).1)
    · exact (mem_centralizer_singleton_iff.mp (mem_inf.mp (h1 hr)).2)
  exact sup_le (zpowers_le.mpr ⟨mem_sup_left (mem_zpowers a), hcen a (by simp), ha⟩)
    (zpowers_le.mpr ⟨mem_sup_right (mem_zpowers b), hcen b (by simp), hb⟩)

end HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace Setting46e

theorem card_closure_xt_z_beta (hs : Setting46e t L p f S w z V i j) {x : X} (hxD : x ∈ S ⊓ L)
    (hx2 : x ^ 2 = 1) :
    Nat.card ↥(zpowers (x * t) ⊔ zpowers z ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      8 := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set h := hs.standing with hh
  have htL := h.config.not_mem
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (h.config.le_centralizer hxD.2)
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hxt2 : (x * t) ^ 2 = 1 := by
    rw [(show Commute x t from hxt).mul_pow, hx2, ht2, one_mul]
  have hxt1 : x * t ≠ 1 := fun h1 => htL (by
    rw [show t = x⁻¹ from eq_inv_of_mul_eq_one_right h1]
    exact inv_mem hxD.2)
  have hoxt : orderOf (x * t) = 2 := orderOf_eq_prime hxt2 hxt1
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hoβ : orderOf β = 2 := orderOf_eq_prime hβ2 hs.beta.ne_one
  have hzL := hs.setup.z_mem.2
  have hzx : Commute x z := hs.setup.z_comm_D hxD
  have hzt : Commute z t := mem_centralizer_singleton_iff.mp (h.config.le_centralizer hzL)
  have hzxt : Commute z (x * t) := hzx.symm.mul_right hzt
  have hd1 : Disjoint (zpowers (x * t)) (zpowers z) := by
    rw [disjoint_iff, eq_bot_iff]
    intro g hg
    rcases eq_one_or_eq_of_mem_zpowers hoxt (mem_inf.mp hg).1 with rfl | rfl
    · exact one_mem _
    · exfalso
      rcases eq_one_or_eq_of_mem_zpowers hs.setup.z_order (mem_inf.mp hg).2 with h1 | h1
      · exact hxt1 h1
      · apply htL
        rw [show t = x⁻¹ * (x * t) by group, h1]
        exact mul_mem (inv_mem hxD.2) hzL
  have hn1 : zpowers z ≤ normalizer ((zpowers (x * t) : Subgroup X) : Set X) := by
    rw [zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (hzxt.zpow_right k).eq.symm
  have hc1 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hn1 hd1
  rw [Nat.card_zpowers, Nat.card_zpowers, hoxt, hs.setup.z_order] at hc1
  have hle : zpowers (x * t) ⊔ zpowers z ≤ zpowers t ⊔ L :=
    sup_le (zpowers_le.mpr (mul_mem (mem_sup_right hxD.2) (mem_sup_left (mem_zpowers t))))
      (zpowers_le.mpr (mem_sup_right hzL))
  have hd2 : Disjoint (zpowers (x * t) ⊔ zpowers z) (zpowers β) := by
    rw [disjoint_iff, eq_bot_iff]
    intro g hg
    rcases eq_one_or_eq_of_mem_zpowers hoβ (mem_inf.mp hg).2 with rfl | rfl
    · exact one_mem _
    · exfalso
      exact hs.setup.rho_beta_not_mem_inn i j
        (h.rho_mem_innAut (hle (mem_inf.mp hg).1) (hs.setup.beta_mem_H i j))
  have hxM := hs.setup.D_le_centralizer_beta i j hxD
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hβxt : Commute β (x * t) :=
    (Commute.symm (mem_centralizer_singleton_iff.mp hxM)).mul_right
      (Commute.symm (mem_centralizer_singleton_iff.mp htM))
  have hβz : Commute β z := Commute.symm (mem_centralizer_singleton_iff.mp
    (K_le_centralizer_beta i j hs.lemma45.z_mem.2))
  have hn2 : zpowers β ≤ normalizer ((zpowers (x * t) ⊔ zpowers z : Subgroup X) : Set X) := by
    rw [zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro y hy
    have hyc : y ∈ centralizer ({β} : Set X) := by
      refine (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)) hy
      · exact mem_centralizer_singleton_iff.mpr hβxt.eq.symm
      · exact mem_centralizer_singleton_iff.mpr hβz.eq.symm
    exact mem_centralizer_singleton_iff.mp hyc
  have hc2 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hn2 hd2
  rw [hc2, hc1, Nat.card_zpowers, hoβ]

theorem l34_false (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hs : Setting46e t L p f S w z V i j)
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))]
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2)
    (hout : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxD, hx2, hx1, hxρ⟩ := hs.l34_exists_x h412 hY hout
  obtain ⟨R, hRle, hRp, hβR, hxtR, hzR, hzc, h64, a, haR, b, hbR, ha2, hb2, hab⟩ :=
    hs.l34_sylow_R hFC hKC hI hKF h412 hY hout hxD hx2 hx1 hxρ
  obtain ⟨c, hc⟩ := hs.l34_conj_tx hKF h412 hY hout hxD hx2 hx1
  have hw2 := hs.l34_orderOf_w h412 hY hout
  obtain ⟨-, -, -, -, ⟨eD⟩⟩ := hs.l34_structure h412 hY hout
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 :=
    hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer hxD.2)
  have hxt2 : (x * t) ^ 2 = 1 := by
    rw [(show Commute x t from hxt).mul_pow, hx2, ht2, one_mul]
  have hRt : ∀ r ∈ R, c⁻¹ * r * c ∈ centralizer ({t} : Set X) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    have h1 : r * (x * t) = (x * t) * r :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp (hRle hr)).1
    calc c⁻¹ * r * c * t = c⁻¹ * (r * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * (r * (x * t)) * c := by rw [hc]
      _ = c⁻¹ * ((x * t) * r) * c := by rw [h1]
      _ = c⁻¹ * ((c * t * c⁻¹) * r) * c := by rw [hc]
      _ = t * (c⁻¹ * r * c) := by group
  have hPH : R.map (MulAut.conj c⁻¹).toMonoidHom ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨r, hr, rfl⟩
    have := hRt r hr
    simpa [MulAut.conj_apply] using this
  obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_ge (hRp.map _) hPH
  obtain ⟨h₁, hh₁H, hh₁S⟩ := hs.sylow.exists_mem_conj hS'
  have hdS : ∀ r ∈ R, (c * h₁)⁻¹ * r * (c * h₁) ∈ S := by
    intro r hr
    have h1 : c⁻¹ * r * c ∈ S' := hPS' ⟨r, hr, by simp⟩
    have h2 := (hh₁S _).mp h1
    rwa [show h₁⁻¹ * (c⁻¹ * r * c) * h₁ = (c * h₁)⁻¹ * r * (c * h₁) by group] at h2
  set d := c * h₁ with hd
  set R'' := R.map (MulAut.conj d⁻¹).toMonoidHom with hR''
  have hconj : ∀ g : X, (MulAut.conj d⁻¹).toMonoidHom g = d⁻¹ * g * d := fun g => by
    simp
  have hR''S : R'' ≤ S := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hconj]
    exact hdS r hr
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have hu : w ^ (orderOf w / 2) = w := by rw [hw2]; norm_num
  have hR''T : R'' ≤ T := by
    by_cases hST : S = T
    · exact hST ▸ hR''S
    obtain ⟨-, -, -, -, hcardS, -, hCu, -⟩ :=
      hs.standing.lemma41_of_lift hs.sylow hs.setup.lift hs.setup.gen3
    rw [← hT] at hcardS hCu
    have hT64 : Nat.card T = 64 := by
      rw [hT, hs.card_T_eq, Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, hw2]
      norm_num
    have hR''card : 64 ≤ Nat.card R'' := by
      rw [hR'', Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective]
      exact h64
    set J := R''.subgroupOf S with hJ
    have hJcard : Nat.card J = Nat.card R'' :=
      Nat.card_congr (subgroupOfEquivOfLe hR''S).toEquiv
    have hidx : J.index ≤ 2 := by
      have h := J.card_mul_index
      rw [hJcard] at h
      by_contra hlt
      have : 64 * 3 ≤ Nat.card R'' * J.index := Nat.mul_le_mul hR''card (by omega)
      omega
    have hRn : ∀ s ∈ S, ∀ r ∈ R'', s * r * s⁻¹ ∈ R'' := by
      intro s hs' r hr
      have hpos : J.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases (show J.index = 1 ∨ J.index = 2 by omega) with h1 | h2
      · have hJt := Subgroup.index_eq_one.mp h1
        have hsr : (⟨s * r * s⁻¹, mul_mem (mul_mem hs' (hR''S hr)) (inv_mem hs')⟩ : ↥S) ∈ J := by
          rw [hJt]
          exact mem_top _
        exact hsr
      · have hn := Subgroup.normal_of_index_eq_two h2
        exact hn.conj_mem ⟨r, hR''S hr⟩ hr ⟨s, hs'⟩
    set F := omegaCenter R'' with hF
    have hFS : F ≤ S := fun g hg => hR''S hg.1
    have hFn : ∀ g ∈ S ⊓ L, ∀ y ∈ F, g * y * g⁻¹ ∈ F := by
      intro g hg y hy
      obtain ⟨hyR, hyc, hy2⟩ := hy
      refine ⟨hRn g hg.1 y hyR, fun r hr => ?_, ?_⟩
      · have h1 := hyc (g⁻¹ * r * g) (by
          have := hRn g⁻¹ (inv_mem hg.1) r hr
          rwa [inv_inv] at this)
        calc r * (g * y * g⁻¹) = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by group
          _ = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
          _ = g * y * g⁻¹ * r := by group
      · rw [sq, show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group, ← sq, hy2,
          mul_one, mul_inv_cancel]
    have hFX := hs.setup.le_X_of_normal_S hFS hFn (fun y hy => hy.2.2)
    have hBR : zpowers (x * t) ⊔ zpowers z ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
        omegaCenter R := by
      refine sup_le (sup_le (zpowers_le.mpr ⟨hxtR, fun r hr => ?_, hxt2⟩)
        (zpowers_le.mpr ⟨hzR, hzc, hz2⟩)) (zpowers_le.mpr ⟨hβR, fun r hr => ?_, hβ2⟩)
      · exact mem_centralizer_singleton_iff.mp (mem_inf.mp (hRle hr)).1
      · exact mem_centralizer_singleton_iff.mp (mem_inf.mp (hRle hr)).2
    set B := (zpowers (x * t) ⊔ zpowers z ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j)).map
      (MulAut.conj d⁻¹).toMonoidHom with hB
    have hBF : B ≤ F := by
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨hgR, hgc, hg2⟩ := hBR hg
      refine ⟨⟨g, hgR, rfl⟩, ?_, by rw [← map_pow, hg2, map_one]⟩
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_mul, ← map_mul, hgc r hr]
    have hBcard : Nat.card B = 8 := by
      rw [hB, Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective,
        hs.card_closure_xt_z_beta hxD hx2]
    have hBX : B = closure {t, w ^ (orderOf w / 2), z} :=
      Subgroup.eq_of_le_of_card_ge (hBF.trans hFX) (by rw [hs.setup.card_X, hBcard])
    have huF : w ^ (orderOf w / 2) ∈ F := hBF (by rw [hBX]; exact subset_closure (by simp))
    intro r hr
    rw [← hCu]
    exact mem_inf.mpr ⟨hR''S hr, mem_centralizer_singleton_iff.mpr (huF.2.1 r hr)⟩
  have hT' : T = (S ⊓ L) ⊔ (zpowers t ⊔ zpowers w) := by
    rw [hT, sup_comm (zpowers t), sup_assoc]
  have hw2' : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  have htw : t * w = w * t :=
    (mem_centralizer_singleton_iff.mp (hs.sylow.le hs.setup.w_mem)).symm
  have hAo := le_omegaCenter_sup ht2 hw2' htw
  have hAD : zpowers t ⊔ zpowers w ≤ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
    refine sup_le (zpowers_le.mpr (mem_centralizer_iff.mpr fun d hd => ?_))
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun d hd => ?_))
    · exact mem_centralizer_singleton_iff.mp (hs.standing.config.le_centralizer hd.2)
    · have := hs.setup.lift.comm_D d hd
      rwa [hu] at this
  have hmem : ∀ g ∈ R, d⁻¹ * g * d ∈ (S ⊓ L) ⊔ (zpowers t ⊔ zpowers w) := by
    intro g hg
    rw [← hT']
    exact hR''T ⟨g, hg, hconj g⟩
  have hsq : ∀ g : X, g ^ 2 ≠ 1 → (d⁻¹ * g * d) ^ 2 ≠ 1 := by
    intro g hg h
    apply hg
    rw [sq, show d⁻¹ * g * d * (d⁻¹ * g * d) = d⁻¹ * (g * g) * d by group, ← sq] at h
    calc g ^ 2 = d * (d⁻¹ * g ^ 2 * d) * d⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hcomm := commute_of_sq_ne_one eD (fun g hg => (hAo hg).2.2)
    (fun g hg y hy => (mem_centralizer_iff.mp (hAD hg) y hy).symm)
    (fun g hg y hy => (hAo hy).2.1 g hg) (hmem a haR) (hmem b hbR) (hsq a ha2)
    (hsq b hb2)
  apply hab
  calc a * b = d * ((d⁻¹ * a * d) * (d⁻¹ * b * d)) * d⁻¹ := by group
    _ = d * ((d⁻¹ * b * d) * (d⁻¹ * a * d)) * d⁻¹ := by rw [hcomm]
    _ = b * a := by group

end Setting46e

theorem harris413_L34 (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput) : Harris413L34Case := by
  intro X _ _ _ _ _ _ t L p f S w z V i j hhyp hY
  obtain ⟨hs, h412, -, hsimple, hout⟩ := hhyp
  exact hs.l34_false hFC hKC hI hKF h412 hY hout

end CFSG.ComponentClassification.HarrisLit
