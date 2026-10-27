module

public import CFSG.GH74.Generic.S3.LyDiagE
public import CFSG.GH74.Generic.S3.LyVertCore
public import CFSG.GH74.Generic.S3.LyVertFusion

public section

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS (InG2 InC2 InT2 InB2 InCalK2 HasSL2Model)
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S3

theorem exists_conj_of_involutions_of_odd {Y : Type*} [Group Y] {N : Subgroup Y}
    (hN : Odd (Nat.card N)) {u v : Y} (hu : u * u = 1) (hv : v * v = 1) (huv : u * v ∈ N) :
    ∃ r : Y, r * v * r⁻¹ = u := by
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  set w : Y := u * v with hw
  have hdvd : orderOf w ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N huv
    simpa using this
  have hodd : Odd (orderOf w) := hN.of_dvd_nat hdvd
  obtain ⟨m, hm⟩ := hodd
  refine ⟨w ^ (m + 1), ?_⟩
  have hvw : v * w * v⁻¹ = w⁻¹ := by
    rw [hv', hw]
    calc v * (u * v) * v = v * u * (v * v) := by group
      _ = v * u := by rw [hv, mul_one]
      _ = (u * v)⁻¹ := by rw [mul_inv_rev, hu', hv']
  have hconj : v * w ^ (m + 1) * v⁻¹ = (w⁻¹) ^ (m + 1) := by
    rw [← hvw, conj_pow]
  have h2 : v * (w ^ (m + 1))⁻¹ * v⁻¹ = w ^ (m + 1) := by
    have : v * (w ^ (m + 1))⁻¹ * v⁻¹ = (v * w ^ (m + 1) * v⁻¹)⁻¹ := by group
    rw [this, hconj, inv_pow, inv_inv]
  calc w ^ (m + 1) * v * (w ^ (m + 1))⁻¹
      = w ^ (m + 1) * (v * (w ^ (m + 1))⁻¹ * v⁻¹) * v := by group
    _ = w ^ (m + 1) * w ^ (m + 1) * v := by rw [h2]
    _ = w ^ (2 * m + 2) * v := by rw [← pow_add]; ring_nf
    _ = w * v := by
        rw [show 2 * m + 2 = orderOf w + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
    _ = u := by rw [hw, mul_assoc, hv, mul_one]


@[expose] def LyVertB2SL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → OnlyInvX x K →
    ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G) (hnd : NbrData G t p f x y Iw Iv),
      imgBar x Iw = K →
      ∀ (L : Subgroup (barQ ↥(centralizer ({y} : Set G)))), CFSG.IsComponent L →
        conjSub (barMk _ ⟨x, hnd.x_mem_centralizer_y⟩)⁻¹ L = L → S45.barSub y Iv ≤ L →
          InB2 ↥L → HasSL2Model ↥L Odd

theorem lyVertTrivial_of_sl2 (hSL2 : LyVertB2SL2) : LyVertTrivial := by
  intro G _ _ x K hset hmax hnt honly t p f y Iw Iv hnd himg L hL hv hle hB2
  have hxY := hnd.x_mem_centralizer_y
  set Y : Type := ↥(centralizer ({y} : Set G)) with hYdef
  set s : barQ Y := barMk _ ⟨x, hxY⟩ with hs
  have hso := orderOf_mk_centralizer hxY hnd.x_inv
  have hsH : orderOf s = 2 := orderOf_barMk hso
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hsH, pow_two] at this
  have hgen : Gen4 (barQ Y) := (gen4Cen_barQ hset.gen4 hnd.y_inv).gen4
  have hΔq : CFSG.IsQuasisimple ↥(S45.barSub y Iv) := hnd.barSub_isQuasisimple
  have hΔs : ((S45.barSub y Iv).subgroupOf (centralizer ({s} : Set (barQ Y)))).IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
      (isPCompIn_two_iff.mp hnd.isPCompIn_barSub).2.1 Subgroup.IsSubnormal.top
  have hΔC : S45.barSub y Iv ≤ centralizer ({s} : Set (barQ Y)) := hnd.isPCompIn_barSub.1
  by_cases hcentr : ∀ l ∈ L, l * s = s * l
  ·
    have hLC : L ≤ centralizer ({s} : Set (barQ Y)) := fun l hl =>
      mem_centralizer_singleton_iff.2 (hcentr l hl)
    have hsubL : ((S45.barSub y Iv).subgroupOf L).IsSubnormal :=
      CFSG.GH74.GLS.TwoThin.isSubnormal_inf_subgroupOf hΔs hLC
    rcases quasisimple_subnormal_subgroups hL.1 hsubL with htop | hcen
    · rw [Subgroup.subgroupOf_eq_top] at htop
      exact le_antisymm hle htop
    · exfalso
      obtain ⟨a, b, hab⟩ := S45.exists_noncomm_of_isQuasisimple hΔq
      apply hab
      have ha : (⟨a.1, hle a.2⟩ : ↥L) ∈ center ↥L := hcen (show _ ∈ (S45.barSub y Iv).subgroupOf L from a.2)
      have := Subgroup.mem_center_iff.1 ha ⟨b.1, hle b.2⟩
      exact Subtype.ext (congrArg Subtype.val this).symm
  · exfalso
    push Not at hcentr
    obtain ⟨l0, hl0L, hl0⟩ := hcentr
    obtain ⟨F₁, _, _, hodd₁, ⟨eS⟩⟩ :=
      hSL2 G x K hset hmax hnt honly t p f y Iw Iv hnd himg L hL hv hle hB2
    let e : ↥L ≃* SL(2, F₁) := eS.trans (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F₁)
    have h3 : 3 < Nat.card F₁ := by
      by_contra hle3
      push Not at hle3
      have hq1 : 1 < Nat.card F₁ := Finite.one_lt_card
      have hq3 : Nat.card F₁ = 3 := by
        obtain ⟨k, hk⟩ := hodd₁
        omega
      have hcardL : Nat.card ↥L = 24 := by
        rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hq3]
        norm_num
      have hcardΔ : Nat.card ↥(S45.barSub y Iv) ≤ 24 := hcardL ▸ Subgroup.card_le_of_le hle
      obtain ⟨F, _, _, hFc, ⟨eF⟩⟩ := hnd.Iv_iso
      obtain ⟨φ, -⟩ := hnd.barSub_equiv
      have hΔcard : Nat.card ↥(S45.barSub y Iv) = Nat.card F * (Nat.card F ^ 2 - 1) := by
        rw [← CFSG.GorensteinWalter.sl2_card_formula F, Nat.card_congr (eF.trans φ).toEquiv]
      have h5 : 5 ≤ Nat.card F := hFc ▸ hnd.prime.2.2
      have h6 : 5 * (5 ^ 2 - 1) ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
        Nat.mul_le_mul h5 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h5 2) 1)
      omega
    have hsN : s ∈ normalizer (L : Set (barQ Y)) := by
      have h1 : s⁻¹ ∈ normalizer (L : Set (barQ Y)) := (mem_normalizer_iff_conjSub s⁻¹).mpr hv
      have := (normalizer (L : Set (barQ Y))).inv_mem h1
      rwa [inv_inv] at this
    have hout : autOf e hsN ∉ (glConjHom (F := F₁)).range := by
      intro hrange
      obtain ⟨a, b, hab⟩ := S45.exists_noncomm_of_isQuasisimple hΔq
      have hfix : ∀ c : ↥(S45.barSub y Iv),
          autOf e hsN (e ⟨c.1, hle c.2⟩) = e ⟨c.1, hle c.2⟩ := by
        intro c
        apply e.symm.injective
        apply Subtype.ext
        rw [autOf_coe e hsN, MulEquiv.symm_apply_apply]
        have hc : (c : barQ Y) * s = s * c := mem_centralizer_singleton_iff.1 (hΔC c.2)
        show s * (c : barQ Y) * s⁻¹ = (c : barQ Y)
        rw [← hc]
        group
      have hne : e ⟨a.1, hle a.2⟩ * e ⟨b.1, hle b.2⟩ ≠ e ⟨b.1, hle b.2⟩ * e ⟨a.1, hle a.2⟩ := by
        intro h
        apply hab
        have h1 : (⟨a.1, hle a.2⟩ : ↥L) * ⟨b.1, hle b.2⟩ = ⟨b.1, hle b.2⟩ * ⟨a.1, hle a.2⟩ := by
          apply e.injective
          rw [map_mul, map_mul]
          exact h
        have h2 := congrArg (fun z : ↥L => (z : barQ Y)) h1
        exact Subtype.ext h2
      have hβ1 := eq_one_of_mem_range_of_fix_nonabelian hrange
        ⟨e ⟨a.1, hle a.2⟩, e ⟨b.1, hle b.2⟩, hfix a, hfix b, hne⟩
      apply hl0
      have h1 := autOf_coe e hsN ⟨l0, hl0L⟩
      rw [hβ1, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
      have h2 : l0 = s * l0 * s⁻¹ := h1
      calc l0 * s = (s * l0 * s⁻¹) * s := by rw [← h2]
        _ = s * l0 := by group
    have hsq : autOf e hsN * autOf e hsN = 1 := autOf_sq e hsN hs2
    obtain ⟨σ, P, hσ1, hσσ, hβ⟩ := sl2_involution_normal_form hodd₁ h3 (autOf e hsN) hsq hout
    obtain ⟨ℓ, hℓ⟩ := exists_neg_of_normal_form hσ1 hσσ hβ
    have hyL : xbar y ∈ L := hle hnd.xbar_mem_barSub
    have hord : orderOf (xbar y) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact xbar_mul_self hnd.y_inv) hnd.xbar_ne_one
    have hyb : e ⟨xbar y, hyL⟩ = (-1 : SL(2, F₁)) := by
      have h1 : orderOf (e ⟨xbar y, hyL⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe ⟨xbar y, hyL⟩]
        exact hord
      exact (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hodd₁ _).mp h1
    set ℓ' : ↥L := e.symm ℓ with hℓ'
    have hconjH : s * (ℓ' : barQ Y) * s⁻¹ = xbar y * (ℓ' : barQ Y) := by
      have h1 := autOf_coe e hsN ℓ'
      have h2 : e ℓ' = ℓ := e.apply_symm_apply ℓ
      rw [h2, hℓ, map_mul, (e.symm_apply_eq).2 hyb.symm] at h1
      exact h1.symm
    obtain ⟨ℓ'', hℓ''⟩ := QuotientGroup.mk_surjective (ℓ' : barQ Y)
    let xY : Y := ⟨x, hxY⟩
    let yY : Y := ⟨y, NbrData.y_mem_centralizer_y y⟩
    have hxY2 : xY * xY = 1 := Subtype.ext hnd.x_sq
    have hyY2 : yY * yY = 1 := Subtype.ext hnd.y_sq
    have hv2 : (yY * xY) * (yY * xY) = 1 := by
      have hxy : xY * yY = yY * xY := Subtype.ext hnd.comm.symm
      calc (yY * xY) * (yY * xY) = yY * (xY * yY) * xY := by group
        _ = yY * (yY * xY) * xY := by rw [hxy]
        _ = (yY * yY) * (xY * xY) := by group
        _ = 1 := by rw [hyY2, hxY2, one_mul]
    have hu2 : (ℓ''⁻¹ * xY * ℓ'') * (ℓ''⁻¹ * xY * ℓ'') = 1 := by
      calc (ℓ''⁻¹ * xY * ℓ'') * (ℓ''⁻¹ * xY * ℓ'') = ℓ''⁻¹ * (xY * xY) * ℓ'' := by group
        _ = 1 := by rw [hxY2]; group
    have hmk : (QuotientGroup.mk (ℓ''⁻¹ * xY * ℓ'') : barQ Y) = QuotientGroup.mk (yY * xY) := by
      have hc : ∀ g : barQ Y, g * xbar y = xbar y * g := fun g =>
        Subgroup.mem_center_iff.1 (xbar_mem_center y) g
      have h1 : s * (ℓ' : barQ Y) = xbar y * (ℓ' : barQ Y) * s := by
        calc s * (ℓ' : barQ Y) = (s * (ℓ' : barQ Y) * s⁻¹) * s := by group
          _ = xbar y * (ℓ' : barQ Y) * s := by rw [hconjH]
      have h2 : (QuotientGroup.mk (ℓ''⁻¹ * xY * ℓ'') : barQ Y) = (ℓ' : barQ Y)⁻¹ * s * (ℓ' : barQ Y) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hℓ'']
        rfl
      calc (QuotientGroup.mk (ℓ''⁻¹ * xY * ℓ'') : barQ Y)
          = (ℓ' : barQ Y)⁻¹ * (s * (ℓ' : barQ Y)) := by rw [h2, mul_assoc]
        _ = (ℓ' : barQ Y)⁻¹ * (xbar y * (ℓ' : barQ Y) * s) := by rw [h1]
        _ = ((ℓ' : barQ Y)⁻¹ * xbar y) * (ℓ' : barQ Y) * s := by group
        _ = (xbar y * (ℓ' : barQ Y)⁻¹) * (ℓ' : barQ Y) * s := by rw [hc (ℓ' : barQ Y)⁻¹]
        _ = xbar y * s := by group
        _ = QuotientGroup.mk (yY * xY) := by rw [QuotientGroup.mk_mul]; rfl
    have hN : Odd (Nat.card (pPrimeCore 2 Y)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
    have huv : (ℓ''⁻¹ * xY * ℓ'') * (yY * xY) ∈ pPrimeCore 2 Y := by
      have h1 := (QuotientGroup.eq).1 hmk
      have hu' : (ℓ''⁻¹ * xY * ℓ'')⁻¹ = ℓ''⁻¹ * xY * ℓ'' := inv_eq_of_mul_eq_one_right hu2
      rwa [hu'] at h1
    obtain ⟨r, hr⟩ := exists_conj_of_involutions_of_odd hN hu2 hv2 huv
    have hxy : IsConj x (y * x) := by
      let ι : Y →* G := (centralizer ({y} : Set G)).subtype
      refine (isConj_iff.mpr ⟨ι (ℓ'' * r), ?_⟩ : IsConj (y * x) x).symm
      have h1 : ℓ'' * (r * (yY * xY) * r⁻¹) * ℓ''⁻¹ = xY := by
        have hr' : r * (yY * xY) * r⁻¹ = ℓ''⁻¹ * xY * ℓ'' := hr
        rw [hr']
        group
      calc ι (ℓ'' * r) * (y * x) * (ι (ℓ'' * r))⁻¹
          = ι ((ℓ'' * r) * (yY * xY) * (ℓ'' * r)⁻¹) := by
            simp only [map_mul]
            rfl
        _ = ι (ℓ'' * (r * (yY * xY) * r⁻¹) * ℓ''⁻¹) := by
            rw [mul_inv_rev]
            simp only [mul_assoc]
        _ = x := by rw [h1]; rfl
    have hnc : ¬ IsConj y x := hnd.not_isConj_y_x hset.gen4 honly himg hxy
    obtain ⟨hx, hxc⟩ := hnd.x_mem_commutator hset.simple hset.nonab honly himg hxy hnc
    have hcomm : s ∈ commutator (barQ Y) := by
      have h1 : s ∈ (commutator Y).map (barMk Y) := ⟨⟨x, hx⟩, hxc, rfl⟩
      have h2 : (commutator Y).map (barMk Y) ≤ commutator (barQ Y) := by
        rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      exact h2 h1
    exact vert_false hgen hL hodd₁ h3 e hs2 hsN hout hcomm

end CFSG.GH74.Generic.S3
