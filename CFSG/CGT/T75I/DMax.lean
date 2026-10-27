module

public import CFSG.CGT.Timmesfeld75.BenderInputs5
public import CFSG.CGT.Timmesfeld75.Sec68Basic
public import CFSG.CGT.T75I.Conj
public import CFSG.CGT.T75I.BenderInput

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem eq_bot_of_solvable_normal_simple {G : Type} [Group G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) (N : Subgroup G) [N.Normal] (hs : Group.IsSolvable N) :
    N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    subst h
    have hGsol : Group.IsSolvable G :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).toMonoidHom)
        (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).surjective
    have : Nontrivial G := by
      obtain ⟨a, b, hab⟩ := hna
      exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial G
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h' | h'
    · obtain ⟨a, b, hab⟩ := hna
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact hlt.ne h'

theorem hSub_sup_eq_top (h1 : Sec4NoA) (h57 : Step57) (h62 : Sec62) (h63 : Sec63)
    (hBen : AschbacherDisconnectedInput) (hc : Sec6Ctx T T₁ 2 2)
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)))) :
    hSub T (normIn T₁ T) ⊔ T₁ = ⊤ := by
  classical
  have : Finite G := hc.finite
  have : IsSimpleGroup G := hc.hy.simple
  have hP := hc.hy.pair
  have hTab := hP.wc.1
  have hS3 : Sec3 T T₁ := hc.sec3
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
      obtain ⟨h, -, hh⟩ := h57 G T T₁ hc.hy d₀ hd₀T hd₀1 t ht ht1
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
    have h2 : 2 < Nat.card T := by rw [hc.hT]; norm_num
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
  obtain ⟨x₀, hx₀L, hx₀1⟩ : ∃ x₀ ∈ normIn T₁ T, x₀ ≠ 1 := by
    obtain ⟨⟨d, hd⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hS3.cfg.ne₁
    exact ⟨d, hd, fun h => hne1 (Subtype.ext h)⟩
  obtain ⟨σ, hσX, -, hσT, -⟩ := hS3.exists_swap
  have hσU : σ ∈ U := (sup_le hTU le_sup_right : T ⊔ T₁ ≤ U) hσX
  have hx₀T₁ : x₀ ∈ T₁ := normIn_le _ _ hx₀L
  have hx₀N : x₀ ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hx₀L).2
  have hx₀E : E x₀ := by
    have hmem : σ⁻¹ * x₀ * σ ∈ T := by
      have : x₀ ∈ conjSubgroup σ T := by rw [hσT]; exact hx₀T₁
      exact mem_conjSubgroup.1 this
    refine ⟨σ⁻¹, U.inv_mem hσU, σ⁻¹ * x₀ * σ, hmem, ?_, by group⟩
    intro h
    apply hx₀1
    have : x₀ = σ * (σ⁻¹ * x₀ * σ) * σ⁻¹ := by group
    rw [this, h]
    group
  have hx₀normD : x₀ ∈ normD T :=
    mem_normD_of_mem_conjSubgroup (k := σ) (by rw [hσT]; exact hx₀T₁) hx₀1 hx₀N
  have hx₀nT : x₀ ∉ T := by
    intro hT'
    have : x₀ ∈ T ⊓ T₁ := ⟨hT', hx₀T₁⟩
    rw [hS3.cfg.inf, Subgroup.mem_bot] at this
    exact hx₀1 this
  have hnormD_E : ∀ w, w ∈ normD T → E w := by
    intro w hw
    by_cases hwT : w ∈ T
    · exact hET w hwT (ne_one_of_mem_classD hw.1)
    · obtain ⟨h, hhH, hwh⟩ :=
        exists_hSub_conj_of_normD h1 h62 h63 hc hhat hx₀normD hx₀nT hw hwT
      have := hE_conj x₀ hx₀E h⁻¹ (U.inv_mem (hHU hhH))
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

end CFSG.CGT.T75I
