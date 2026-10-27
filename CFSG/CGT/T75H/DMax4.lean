module

public import CFSG.CGT.T75H.NormD
public import CFSG.CGT.T75I.DMax

public section

namespace CFSG.CGT.T75H

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75I

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem hSub_sup_eq_top_of_card_four (h1 : Sec4NoA) (h63 : Sec63)
    (hBen : AschbacherDisconnectedInput) (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T)))
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) :
    hSub T (normIn T₁ T) ⊔ T₁ = ⊤ := by
  classical
  have : Finite G := hc.finite
  have : IsSimpleGroup G := hc.hy.simple
  have hP := hc.hy.pair
  have hTab := hP.wc.1
  have hS3 : Sec3 T T₁ := hc.sec3
  have hT4 : Nat.card T = 4 := by simpa using hc.hT
  set H := hSub T (normIn T₁ T) with hH
  by_contra hne
  set U : Subgroup G := H ⊔ T₁ with hU
  have hTbot : T ≠ ⊥ := hS3.cfg.left_ne_bot
  have hTU : T ≤ U := left_le_hSub.trans le_sup_left
  have hHU : H ≤ U := le_sup_left
  obtain ⟨d₀, hd₀T, hd₀1⟩ : ∃ d₀ ∈ T, d₀ ≠ 1 := by
    obtain ⟨⟨d, hd⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hTbot
    exact ⟨d, hd, fun h => hne1 (Subtype.ext h)⟩
  have hd₀D : d₀ ∈ classD T := mem_classD_of_mem hd₀T hd₀1
  have hcls : ∃ d : G, classD T = {g | IsConj d g} := by
    refine ⟨d₀, ?_⟩
    ext g
    constructor
    · rintro ⟨c, t, ht, ht1, rfl⟩
      obtain ⟨h, -, hh⟩ := h57 d₀ hd₀T hd₀1 t ht ht1
      refine isConj_iff.2 ⟨c⁻¹ * h, ?_⟩
      rw [← hh]
      group
    · intro hg
      obtain ⟨c, hc'⟩ := isConj_iff.1 hg
      exact ⟨c⁻¹, d₀, hd₀T, hd₀1, by rw [← hc']; group⟩
  have hord : ∀ d ∈ classD T, orderOf d = 2 := fun d hd => by
    have hsq := mul_self_eq_one_of_mem_classD hTab hd
    exact orderOf_eq_prime (by rwa [← pow_two] at hsq) (ne_one_of_mem_classD hd)
  have hgen : Subgroup.closure (classD T) = ⊤ := by
    rw [closure_classD_eq_normalClosure]
    exact normalClosure_eq_top_of_simple hTbot
  have hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥ := fun N hN hs =>
    eq_bot_of_solvable_normal_simple hc.hy.nonab N hs
  have hclosed : ∀ x ∈ classD T, ∀ y ∈ classD T, x * y = y * x → x ≠ y → x * y ∈ classD T :=
    fun x hx y hy hxy hne => hc.classD_mul_of_comm h63 rfl x hx y hy hne hxy
  have hcomm : ∃ u ∈ classD T, ∃ v ∈ classD T, u ≠ v ∧ u * v = v * u := by
    have h2 : 2 < Nat.card T := by rw [hT4]; norm_num
    obtain ⟨u, hu, hu1, v, hv, hv1, huv⟩ := exists_ne_one_ne_of_two_lt_natCard h2
    exact ⟨u, mem_classD_of_mem hu hu1, v, mem_classD_of_mem hv hv1, huv,
      elemAbelian_mul_comm hTab hu hv⟩
  have hDU : ∃ y ∈ classD T, y ∉ U := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    exact hcon
  obtain ⟨y, hyD, hyU⟩ := hDU
  let E : G → Prop := fun z => ∃ u ∈ U, ∃ s ∈ T, s ≠ 1 ∧ z = u⁻¹ * s * u
  have hE_conj : ∀ z, E z → ∀ u ∈ U, E (u⁻¹ * z * u) := by
    rintro z ⟨u₀, hu₀, s, hs, hs1, rfl⟩ u hu
    exact ⟨u₀ * u, U.mul_mem hu₀ hu, s, hs, hs1, by group⟩
  have hE_mem : ∀ z, E z → z ∈ U := by
    rintro z ⟨u, hu, s, hs, -, rfl⟩
    exact U.mul_mem (U.mul_mem (U.inv_mem hu) (hTU hs)) hu
  have hET : ∀ s ∈ T, s ≠ 1 → E s := fun s hs hs1 => ⟨1, U.one_mem, s, hs, hs1, by group⟩
  have hℓL : ℓ ∈ normIn T₁ T := D.hℓ
  have hℓ1 : ℓ ≠ 1 := D.hℓ1
  obtain ⟨σ, hσX, -, hσT, -⟩ := hS3.exists_swap
  have hσU : σ ∈ U := (sup_le hTU le_sup_right : T ⊔ T₁ ≤ U) hσX
  have hℓT₁ : ℓ ∈ T₁ := normIn_le _ _ hℓL
  have hℓN : ℓ ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hℓL).2
  have hℓE : E ℓ := by
    have hmem : σ⁻¹ * ℓ * σ ∈ T := by
      have : ℓ ∈ conjSubgroup σ T := by rw [hσT]; exact hℓT₁
      exact mem_conjSubgroup.1 this
    refine ⟨σ⁻¹, U.inv_mem hσU, σ⁻¹ * ℓ * σ, hmem, ?_, by group⟩
    intro h
    apply hℓ1
    have : ℓ = σ * (σ⁻¹ * ℓ * σ) * σ⁻¹ := by group
    rw [this, h]
    group
  have hℓnormD : ℓ ∈ normD T :=
    mem_normD_of_mem_conjSubgroup (k := σ) (by rw [hσT]; exact hℓT₁) hℓ1 hℓN
  have hℓnT : ℓ ∉ T := by
    intro hT'
    have : ℓ ∈ T ⊓ T₁ := ⟨hT', hℓT₁⟩
    rw [hS3.cfg.inf, Subgroup.mem_bot] at this
    exact hℓ1 this
  have hnormD_E : ∀ w, w ∈ normD T → E w := by
    intro w hw
    by_cases hwT : w ∈ T
    · exact hET w hwT (ne_one_of_mem_classD hw.1)
    · have hwH : w ∈ H := hc.normD_le_hSub_of_not_a8 h1 h63 (by omega) hw
      have hww : w * w = 1 := mul_self_eq_one_of_mem_classD hTab hw.1
      obtain ⟨h, hhH, hwh⟩ := exists_hSub_conj_of_invol hc h48 h57 D hwH hww hwT
      have := hE_conj ℓ hℓE h⁻¹ (U.inv_mem (hHU hhH))
      rw [inv_inv] at this
      rw [hwh]
      exact this
  have hB : ∀ z, E z → ∀ w ∈ classD T, z * w = w * z → E w := by
    rintro z ⟨u, hu, s, hs, hs1, rfl⟩ w hw hzw
    set w' := u * w * u⁻¹ with hw'
    have hw'D : w' ∈ classD T := by
      have := classD_conj hw u⁻¹
      simpa [hw'] using this
    have hcomm' : w' * s = s * w' := by
      calc w' * s = u * (w * (u⁻¹ * s * u)) * u⁻¹ := by simp only [hw']; group
        _ = u * ((u⁻¹ * s * u) * w) * u⁻¹ := by rw [← hzw]
        _ = s * w' := by simp only [hw']; group
    have hw'N : w' ∈ Subgroup.normalizer (T : Set G) :=
      hP.wc.centralizer_le_normalizer hs hs1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm')
    have hEw' := hnormD_E w' ⟨hw'D, hw'N⟩
    have := hE_conj w' hEw' u hu
    have e : u⁻¹ * w' * u = w := by simp only [hw']; group
    rwa [e] at this
  have hreach : ∀ z, ReachD (classD T) d₀ z → E z := by
    intro z hz
    unfold ReachD at hz
    induction hz with
    | refl => exact hET d₀ hd₀T hd₀1
    | tail _ hstep ih => exact hB _ ih _ hstep.2.1 hstep.2.2
  have hnreach : ¬ ReachD (classD T) d₀ y := fun h => hyU (hE_mem y (hreach y h))
  have hBender := hBen G (classD T) hcls hord hgen hrad ⟨d₀, hd₀D, y, hyD, hnreach⟩ hclosed hcomm
  obtain ⟨x, hx⟩ := hP.conj
  have hxne : conjSubgroup x T ≠ T := by rw [← hx]; exact hP.ne
  have hbot := benderWCInput_of_repo G hBender T hP.wc hTbot x hxne
  exact hP.nontriv (by rw [hx]; exact hbot)
end CFSG.CGT.T75H
