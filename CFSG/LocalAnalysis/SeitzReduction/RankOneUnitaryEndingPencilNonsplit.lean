module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingCommPencil
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilArith
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilCoords

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pencilNS_map_conj_map_conj {G : Type*} [Group G] (X : Subgroup G) (a b : G) :
    (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      X.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem pencilNS_map_conj_one {G : Type*} [Group G] (X : Subgroup G) :
    X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext x
  simp

private theorem pencilNS_mem_normalizer_of_map_eq {G : Type*} [Group G] {X : Subgroup G} {g : G}
    (h : X.map (MulAut.conj g).toMonoidHom = X) : g ∈ normalizer (X : Set G) := by
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← h]
    exact ⟨x, hx, by simp⟩
  · rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := mul_left_cancel (mul_right_cancel hyx)
    rwa [← this]

private theorem pencilNS_card_sup_mul_card_inf_of_normal {G : Type*} [Group G] (A N : Subgroup G)
    [N.Normal] :
    Nat.card (A ⊔ N : Subgroup G) * Nat.card (A ⊓ N : Subgroup G) = Nat.card A * Nat.card N := by
  have h1 := Subgroup.relIndex_mul_card (H := N) (K := A ⊔ N)
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : N ≤ A ⊔ N)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

private theorem pencilNS_card_sup_mul_card_inf {G : Type*} [Group G] {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := pencilNS_card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ Y : Subgroup G, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

private theorem pencilNS_conj_commutator {G : Type*} [Group G] (g x y : G) :
    g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

section Certificates

namespace U3EndingData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}
  {s : G}

theorem not_mem_normalizer_of_nonsplit (hD : U3EndingData G L f t T R₂ U₁ s) {v : G}
    (hvT : v ∈ T) (hv2 : v ^ 2 = 1) (hvS : v ∉ szT₁ L T ⊔ zpowers t) (hsv : s * t * s⁻¹ = t * v)
    {X : Subgroup G} (hRX : R₂ ≤ X) (hXU : X ≤ U₁) (hX2 : ∀ x ∈ X, x ^ 2 = 1)
    (hXcard : (2 ^ f) ^ 4 ≤ Nat.card X) (hXt : ∀ x ∈ X, t * x * t⁻¹ ∈ X → x ∈ R₂)
    (huniq : ∀ Y : Subgroup G, R₂ ≤ Y → Y ≤ U₁ → (∀ y ∈ Y, y ^ 2 = 1) →
      (2 ^ f) ^ 4 ≤ Nat.card Y → Y = X ∨ Y = X.map (MulAut.conj t).toMonoidHom) :
    v ∉ normalizer (X : Set G) := by
  intro hvX
  classical
  have h := hD.start
  have hS2 := hD.card_sylow
  have hR := hD.r2
  have hU := hD.u1
  have hf : 2 ≤ f := h.two_le
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  have htR : t ∈ normalizer (R₂ : Set G) := by
    refine mem_normalizer_iff.mpr fun r => ⟨fun hr => hR.tN r hr, fun hr => ?_⟩
    have h1 := hR.tN _ hr
    have e : t * (t * r * t⁻¹) * t⁻¹ = (t * t) * r * (t * t)⁻¹ := by group
    rwa [e, htt, one_mul, inv_one, mul_one] at h1
  have hRU : R₂ ≤ U₁ := le_sup_right.trans hU.le
  have hUR : ∀ x ∈ U₁, ∀ r ∈ R₂, x * r = r * x := fun x hx r hr =>
    (mem_centralizer_iff.mp (hU.le_centralizer hx) r hr).symm
  have hRinv : ∀ r ∈ R₂, r⁻¹ = r := fun r hr =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU.sq_R₂ r hr)
  have hsU := hD.s_mem_normalizer_U₁
  have hsR := hD.s_mem_normalizer_R₂
  have hv : v = t * (s * t * s⁻¹) := by
    calc v = t⁻¹ * (t * v) := by group
      _ = t * (s * t * s⁻¹) := by rw [← hsv, htinv]
  have hvU : v ∈ normalizer (U₁ : Set G) := by
    rw [hv]
    exact mul_mem htU (mul_mem (mul_mem hsU htU) (inv_mem hsU))
  have hvR : v ∈ normalizer (R₂ : Set G) := by
    rw [hv]
    exact mul_mem htR (mul_mem (mul_mem hsR htR) (inv_mem hsR))
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  have hconj : ∀ g ∈ normalizer (X : Set G), ∀ x ∈ X, g * x * g⁻¹ ∈ X := fun g hg x hx =>
    (mem_normalizer_iff.mp hg x).mp hx
  have hXinv : ∀ x ∈ X, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hX2 x hx)
  have hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ := (hXinv _ (mul_mem hx hy)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hXinv y hy, hXinv x hx]
  have hUX : ∀ g ∈ U₁, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact mul_mem (hRX (hU.comm_mem g hg x (hXU hx))) hx
  have hUN : U₁ ≤ normalizer (X : Set G) := by
    intro g hg
    refine mem_normalizer_iff.mpr fun x => ⟨fun hx => hUX g hg x hx, fun hx => ?_⟩
    have := hUX g⁻¹ (inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  have key : ∀ g ∈ normalizer (U₁ : Set G), g ∈ normalizer (R₂ : Set G) →
      X.map (MulAut.conj g).toMonoidHom = X ∨
        X.map (MulAut.conj g).toMonoidHom = X.map (MulAut.conj t).toMonoidHom := by
    intro g hgU hgR
    refine huniq _ (fun r hr => ?_) ?_ ?_ ?_
    · refine ⟨g⁻¹ * r * g, hRX ?_, by simp [mul_assoc]⟩
      have := (mem_normalizer_iff.mp (inv_mem hgR) r).mp hr
      rwa [inv_inv] at this
    · rintro _ ⟨x, hx, rfl⟩
      simpa [mul_assoc] using (mem_normalizer_iff.mp hgU x).mp (hXU hx)
    · rintro _ ⟨x, hx, rfl⟩
      have h1 := hX2 x hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [sq] at h1 ⊢
      calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hXcard
  obtain ⟨E, _, _, _, σ, u, w, d, μ, a, χ₁, χ₂, hP⟩ := hD.exists_pencilCoords
  have hSc := hP.semilinear
  have hKE : Fintype.card E = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hSc.card]
  have hσ := hSc.sigma
  have hdt := hP.d_comm
  have hdX : d ∈ normalizer (X : Set G) := by
    rcases key d hP.d_mem_normalizer_U₁ hP.d_mem_normalizer_R₂ with h1 | h1
    · exact pencilNS_mem_normalizer_of_map_eq h1
    · have h2 : X.map (MulAut.conj (d * d)).toMonoidHom = X := by
        rw [← pencilNS_map_conj_map_conj, h1, pencilNS_map_conj_map_conj, hdt,
          ← pencilNS_map_conj_map_conj, h1, pencilNS_map_conj_map_conj, htt,
          pencilNS_map_conj_one]
      have hd2 := pencilNS_mem_normalizer_of_map_eq h2
      obtain ⟨m, hm⟩ := hP.odd_orderOf_d
      have e : d = (d * d) ^ (m + 1) := by
        rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf d + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [e]
      exact pow_mem hd2 _
  have haX : ∀ x ∈ X, a x = 0 → x ∈ R₂ := by
    intro x hx hax
    have h1 := (hP.a_eq_zero_iff x (hXU hx)).mp hax
    have hx' : t * x * t⁻¹ ∈ X := by
      have := mul_mem (inv_mem hx) (hRX h1)
      rwa [inv_mul_cancel_left] at this
    exact hXt x hx hx'
  have hasurj : ∀ z : E, ∃ x ∈ X, a x = z := by
    let Aim : AddSubgroup E :=
      { carrier := {z | ∃ x ∈ X, a x = z}
        zero_mem' := ⟨1, one_mem _, hP.a_one⟩
        add_mem' := by
          rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
          exact ⟨x * x', mul_mem hx hx', hP.a_mul x (hXU hx) x' (hXU hx')⟩
        neg_mem' := by
          rintro _ ⟨x, hx, rfl⟩
          exact ⟨x⁻¹, inv_mem hx, hP.a_inv (hXU hx)⟩ }
    have hAim : ∀ z ∈ Aim, μ * z ∈ Aim := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨d * x * d⁻¹, hconj d hdX x hx, hP.a_conj_d (hXU hx)⟩
    rcases SemilinearField.eq_bot_or_eq_top_of_orderOf hf hSc.card hP.orderOf_mu Aim hAim with
      hbot | htop
    · exfalso
      have hXR : X ≤ R₂ := fun x hx => haX x hx (by
        have hm : a x ∈ Aim := ⟨x, hx, rfl⟩
        rw [hbot] at hm
        exact (AddSubgroup.mem_bot).mp hm)
      have h1 := Subgroup.card_le_of_le hXR
      rw [hR.card] at h1
      have h2 : (2 ^ f) ^ 2 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    · intro z
      have hm : z ∈ Aim := htop ▸ AddSubgroup.mem_top z
      exact hm
  choose sec hsecX hseca using hasurj
  have htX : ∀ y ∈ X, t * y * t⁻¹ ∈ U₁ := fun y hy => (mem_normalizer_iff.mp htU _).mp (hXU hy)
  have hcR : ∀ x ∈ X, ∀ y ∈ X, ⁅x, t * y * t⁻¹⁆ ∈ R₂ := fun x hx y hy => by
    rw [commutatorElement_def]
    exact hU.comm_mem x (hXU hx) _ (htX y hy)
  have hcomR : ∀ x ∈ U₁, ∀ y ∈ U₁, ⁅x, y⁆ ∈ R₂ := fun x hx y hy => by
    rw [commutatorElement_def]
    exact hU.comm_mem x hx y hy
  have hcmul : ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ X,
      ⁅x * x', t * y * t⁻¹⁆ = ⁅x, t * y * t⁻¹⁆ * ⁅x', t * y * t⁻¹⁆ := by
    intro x hx x' hx' y hy
    exact SplitComm.mul_left_eq (hUR x (hXU hx) _ (hcR x' hx' y hy)).symm
      (hR.comm _ (hcR x' hx' y hy) _ (hcR x hx y hy))
  have hcmul' : ∀ x ∈ X, ∀ y ∈ X, ∀ y' ∈ X,
      ⁅x, t * (y * y') * t⁻¹⁆ = ⁅x, t * y * t⁻¹⁆ * ⁅x, t * y' * t⁻¹⁆ := by
    intro x hx y hy y' hy'
    rw [show t * (y * y') * t⁻¹ = (t * y * t⁻¹) * (t * y' * t⁻¹) by group]
    exact SplitComm.mul_right_eq (hUR _ (htX y hy) _ (hcR x hx y' hy')).symm
  have hcongr : ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ X, ∀ y' ∈ X, a x = a x' → a y = a y' →
      ⁅x, t * y * t⁻¹⁆ = ⁅x', t * y' * t⁻¹⁆ := by
    intro x hx x' hx' y hy y' hy' hxx hyy
    have hr : x'⁻¹ * x ∈ R₂ := haX _ (mul_mem (inv_mem hx') hx) (by
      rw [hP.a_mul _ (inv_mem (hXU hx')) _ (hXU hx), hP.a_inv (hXU hx'), hxx, neg_add_cancel])
    have hr' : y'⁻¹ * y ∈ R₂ := haX _ (mul_mem (inv_mem hy') hy) (by
      rw [hP.a_mul _ (inv_mem (hXU hy')) _ (hXU hy), hP.a_inv (hXU hy'), hyy, neg_add_cancel])
    have ex : x = x' * (x'⁻¹ * x) := by group
    have ey : t * y * t⁻¹ = (t * y' * t⁻¹) * (t * (y'⁻¹ * y) * t⁻¹) := by group
    have hrt : t * (y'⁻¹ * y) * t⁻¹ ∈ R₂ := hR.tN _ hr'
    rw [ex, ey, SplitComm.mul_right_of_commute
      (hUR _ (mul_mem (htX y' hy') (hRU hrt)) _ hr).symm,
      SplitComm.mul_right_of_commute' (hUR _ (hXU hx') _ hrt).symm]
  have hconjc : ∀ g : G, g * t = t * g → ∀ x y : G,
      g * ⁅x, t * y * t⁻¹⁆ * g⁻¹ = ⁅g * x * g⁻¹, t * (g * y * g⁻¹) * t⁻¹⁆ := by
    intro g hg x y
    rw [pencilNS_conj_commutator]
    congr 1
    calc g * (t * y * t⁻¹) * g⁻¹ = (g * t) * y * (g * t)⁻¹ := by group
      _ = (t * g) * y * (t * g)⁻¹ := by rw [hg]
      _ = t * (g * y * g⁻¹) * t⁻¹ := by group
  have hform : ∀ χ : G → E, (∀ r ∈ R₂, ∀ r' ∈ R₂, χ (r * r') = χ r + χ r') →
      (∀ r ∈ R₂, χ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ r) →
      ∃ γ γ' : E, ∀ x ∈ X, ∀ y ∈ X,
        χ ⁅x, t * y * t⁻¹⁆ = γ * (a x * a y ^ 2 ^ f) + γ' * (a x ^ 2 ^ f * a y) := by
    intro χ hχ hχd
    obtain ⟨γ, γ', hγ⟩ := exists_eq_of_biadditive_equivariant' hf hKE
      (fun α β => χ ⁅sec α, t * sec β * t⁻¹⁆)
      (fun α α' β => by
        rw [hcongr _ (hsecX _) _ (mul_mem (hsecX α) (hsecX α')) _ (hsecX β) _ (hsecX β)
          (by rw [hseca, hP.a_mul _ (hXU (hsecX α)) _ (hXU (hsecX α')), hseca, hseca]) rfl,
          hcmul _ (hsecX α) _ (hsecX α') _ (hsecX β)]
        exact hχ _ (hcR _ (hsecX α) _ (hsecX β)) _ (hcR _ (hsecX α') _ (hsecX β)))
      (fun α β β' => by
        rw [hcongr _ (hsecX α) _ (hsecX α) _ (hsecX _) _ (mul_mem (hsecX β) (hsecX β')) rfl
          (by rw [hseca, hP.a_mul _ (hXU (hsecX β)) _ (hXU (hsecX β')), hseca, hseca]),
          hcmul' _ (hsecX α) _ (hsecX β) _ (hsecX β')]
        exact hχ _ (hcR _ (hsecX α) _ (hsecX β)) _ (hcR _ (hsecX α) _ (hsecX β')))
      hP.mu_ne_zero hP.orderOf_mu
      (fun α β => by
        have hdα := hconj d hdX _ (hsecX α)
        have hdβ := hconj d hdX _ (hsecX β)
        rw [hcongr _ (hsecX _) _ hdα _ (hsecX _) _ hdβ
          (by rw [hseca, hP.a_conj_d (hXU (hsecX α)), hseca])
          (by rw [hseca, hP.a_conj_d (hXU (hsecX β)), hseca]),
          ← hconjc d hdt, hχd _ (hcR _ (hsecX α) _ (hsecX β))])
    refine ⟨γ, γ', fun x hx y hy => ?_⟩
    rw [hcongr x hx _ (hsecX (a x)) y hy _ (hsecX (a y)) (hseca _).symm (hseca _).symm]
    exact hγ (a x) (a y)
  obtain ⟨γ₁, γ₁', hγ₁⟩ := hform χ₁ hP.chi₁_mul hP.chi₁_conj
  obtain ⟨γ₂, γ₂', hγ₂⟩ := hform χ₂ hP.chi₂_mul hP.chi₂_conj
  obtain ⟨m, hm, hva⟩ := hP.exists_conj_outer h hS2 hvT hvS (by rw [hv2]; exact one_mem _) hvR
  have hm' : m * m ^ 2 ^ f = 1 := by rw [← hσ]; exact hm
  have htvc : ∀ x ∈ X, ∀ y ∈ X,
      (t * v) * ⁅x, t * y * t⁻¹⁆ * (t * v)⁻¹ = ⁅x, t * y * t⁻¹⁆ := by
    intro x hx y hy
    have hx' := hconj v hvX x hx
    have hy' := hconj v hvX y hy
    have e : (t * v) * ⁅x, t * y * t⁻¹⁆ * (t * v)⁻¹ =
        ⁅v * y * v⁻¹, t * (v * x * v⁻¹) * t⁻¹⁆ := by
      have e1 : (t * v) * ⁅x, t * y * t⁻¹⁆ * (t * v)⁻¹ =
          t * (v * ⁅x, t * y * t⁻¹⁆ * v⁻¹) * t⁻¹ := by group
      rw [e1, hconjc v hvt, pencilNS_conj_commutator, ← hRinv _ (hcR _ hy' _ hx'),
        commutatorElement_inv]
      congr 1
      calc t * (t * (v * y * v⁻¹) * t⁻¹) * t⁻¹ = (t * t) * (v * y * v⁻¹) * (t * t)⁻¹ := by group
        _ = v * y * v⁻¹ := by rw [htt]; group
    have hmem : (t * v) * ⁅x, t * y * t⁻¹⁆ * (t * v)⁻¹ ∈ R₂ := by
      rw [e]
      exact hcR _ hy' _ hx'
    refine hP.eq_of_chi_eq hU.sq_R₂ hmem (hcR x hx y hy) ?_ ?_
    · rw [e, hγ₁ _ hy' _ hx', hγ₁ x hx y hy, hva y (hXU hy), hva x (hXU hx), hσ, hσ]
      exact apply_swap_semilinear_eq hKE γ₁ γ₁' m hm' (a x) (a y)
    · rw [e, hγ₂ _ hy' _ hx', hγ₂ x hx y hy, hva y (hXU hy), hva x (hXU hx), hσ, hσ]
      exact apply_swap_semilinear_eq hKE γ₂ γ₂' m hm' (a x) (a y)
  set Xt := X.map (MulAut.conj t).toMonoidHom with hXt_def
  have hmemXt : ∀ z, z ∈ Xt ↔ ∃ y ∈ X, t * y * t⁻¹ = z := fun z => by
    simp only [hXt_def, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hXtU : Xt ≤ U₁ := fun z hz => by
    obtain ⟨y, hy, rfl⟩ := (hmemXt z).mp hz
    exact htX y hy
  have hinf : X ⊓ Xt ≤ R₂ := by
    intro z hz
    obtain ⟨hzX, hzXt⟩ := mem_inf.mp hz
    obtain ⟨y, hy, rfl⟩ := (hmemXt z).mp hzXt
    exact hR.tN _ (hXt y hy hzX)
  have hsup : X ⊔ Xt = U₁ := by
    have hprod := pencilNS_card_sup_mul_card_inf (hXtU.trans hUN)
    have hcXt : Nat.card Xt = Nat.card X :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    have hI : Nat.card (X ⊓ Xt : Subgroup G) ≤ (2 ^ f) ^ 2 := by
      rw [← hR.card]
      exact Subgroup.card_le_of_le hinf
    refine Subgroup.eq_of_le_of_card_ge (sup_le hXU hXtU) ?_
    rw [hU.card]
    have h1 : (2 ^ f) ^ 6 * (2 ^ f) ^ 2 ≤ Nat.card (X ⊔ Xt : Subgroup G) * (2 ^ f) ^ 2 := by
      calc (2 ^ f) ^ 6 * (2 ^ f) ^ 2 = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by ring
        _ ≤ Nat.card X * Nat.card Xt := by rw [hcXt]; exact Nat.mul_le_mul hXcard hXcard
        _ = Nat.card (X ⊔ Xt : Subgroup G) * Nat.card (X ⊓ Xt : Subgroup G) := hprod.symm
        _ ≤ Nat.card (X ⊔ Xt : Subgroup G) * (2 ^ f) ^ 2 := Nat.mul_le_mul_left _ hI
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  have hcomm : ∀ g₁ ∈ U₁, ∀ g₂ ∈ U₁, ⁅g₁, g₂⁆ ∈ centralizer ({t * v} : Set G) := by
    have hdec : ∀ g ∈ U₁, ∃ x ∈ X, ∃ y ∈ X, x * (t * y * t⁻¹) = g := by
      intro g hg
      rw [← hsup] at hg
      obtain ⟨x, hx, z, hz, rfl⟩ :=
        exists_mul_eq_of_mem_sup_of_le_normalizer (hXtU.trans hUN) hg
      obtain ⟨y, hy, rfl⟩ := (hmemXt z).mp hz
      exact ⟨x, hx, y, hy, rfl⟩
    have hfix : ∀ x ∈ X, ∀ y ∈ X, ⁅x, t * y * t⁻¹⁆ ∈ centralizer ({t * v} : Set G) := by
      intro x hx y hy
      refine mem_centralizer_singleton_iff.mpr ?_
      have h1 := htvc x hx y hy
      calc ⁅x, t * y * t⁻¹⁆ * (t * v) =
          (t * v) * ⁅x, t * y * t⁻¹⁆ * (t * v)⁻¹ * (t * v) := by rw [h1]
        _ = (t * v) * ⁅x, t * y * t⁻¹⁆ := by group
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hdec g₁ hg₁
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hdec g₂ hg₂
    have hY₁ := htX y₁ hy₁
    have hY₂ := htX y₂ hy₂
    have hx₁U := hXU hx₁
    have hx₂U := hXU hx₂
    have hYY : ⁅t * y₁ * t⁻¹, t * y₂ * t⁻¹⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      calc t * y₁ * t⁻¹ * (t * y₂ * t⁻¹) = t * (y₁ * y₂) * t⁻¹ := by group
        _ = t * (y₂ * y₁) * t⁻¹ := by rw [hXab y₁ hy₁ y₂ hy₂]
        _ = t * y₂ * t⁻¹ * (t * y₁ * t⁻¹) := by group
    have hxx : ⁅x₁, x₂⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hXab x₁ hx₁ x₂ hx₂)
    have e : ⁅x₁ * (t * y₁ * t⁻¹), x₂ * (t * y₂ * t⁻¹)⁆ =
        ⁅x₁, t * y₂ * t⁻¹⁆ * ⁅x₂, t * y₁ * t⁻¹⁆⁻¹ := by
      have g2U : x₂ * (t * y₂ * t⁻¹) ∈ U₁ := mul_mem hx₂U hY₂
      rw [SplitComm.mul_left_eq (hUR _ hx₁U _ (hcomR _ hY₁ _ g2U)).symm
          (hR.comm _ (hcomR _ hY₁ _ g2U) _ (hcomR _ hx₁U _ g2U)),
        SplitComm.mul_right_eq (hUR _ hx₂U _ (hcomR _ hx₁U _ hY₂)).symm,
        SplitComm.mul_right_eq (hUR _ hx₂U _ (hcomR _ hY₁ _ hY₂)).symm,
        hxx, hYY, one_mul, mul_one, commutatorElement_inv]
    rw [e]
    exact mul_mem (hfix x₁ hx₁ y₂ hy₂) (inv_mem (hfix x₂ hx₂ y₁ hy₁))
  have hle : R₂ ≤ centralizer ({t * v} : Set G) := by
    rw [← hU.commutator_eq, Subgroup.commutator_le]
    exact hcomm
  apply hU.conj_not_mem_centralizer h hS2 hR s
  rw [hsv]
  exact mem_centralizer_iff.mpr fun r hr => mem_centralizer_singleton_iff.mp (hle hr)

end U3EndingData

theorem u3EndingNonsplitInput : U3EndingNonsplitInput := by
  intro G _ _ L f t T R₂ U₁ s v hD hvT hv2 hvS hsv X hRX hXU hX2 hXcard hXt huniq
  exact hD.not_mem_normalizer_of_nonsplit hvT hv2 hvS hsv hRX hXU hX2 hXcard hXt huniq

theorem u3EndingInput_of_pencil (hp : U3EndingPencilInput) (hsyl : U3EndingSylowInput) :
    U3EndingInput :=
  u3EndingInput_of_pencil_of_nonsplit hp u3EndingNonsplitInput hsyl

end Certificates

end CFSG.SeitzReduction.RankOne
