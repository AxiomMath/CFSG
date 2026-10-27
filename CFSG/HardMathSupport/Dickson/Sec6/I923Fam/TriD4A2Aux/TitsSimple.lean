module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.Adjust
public import Mathlib.GroupTheory.IsPerfect
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldNoAbel

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Pointwise commutatorElement

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

theorem rgd2_normal_dichotomy {G : Type*} [Group G] {n : ℕ} {H : Subgroup G} {r₁ r₂ : G}
    {U : Subgroup G} {root : ℤ → Subgroup G} (R : RGD2 n H r₁ r₂ U root)
    [(cartan (H ⊔ U) R.N).Normal] (hgen : (H ⊔ U) ⊔ R.N = ⊤) (A : Subgroup G) [A.Normal] :
    A ⊔ (H ⊔ U) = ⊤ ∨ A ≤ H ⊔ U := by
  have hT := R.isTitsSystem hgen
  have hst : R.w₁ ≠ R.w₂ := R.weyl_ne
  have h3 := R.three_le
  have hcomm : R.w₁ * R.w₂ ≠ R.w₂ * R.w₁ := by
    intro hc
    have hw1 : R.w₁ * R.w₁ = 1 := by
      have := R.orderOf_w 0
      have h' := pow_orderOf_eq_one R.w₁
      rwa [show orderOf R.w₁ = 2 from this, sq] at h'
    have hw2 : R.w₂ * R.w₂ = 1 := by
      have := R.orderOf_w 1
      have h' := pow_orderOf_eq_one R.w₂
      rwa [show orderOf R.w₂ = 2 from this, sq] at h'
    have h2 : (R.w₁ * R.w₂) ^ 2 = 1 := by
      calc (R.w₁ * R.w₂) ^ 2 = R.w₁ * (R.w₂ * R.w₁) * R.w₂ := by rw [sq]; group
        _ = R.w₁ * (R.w₁ * R.w₂) * R.w₂ := by rw [← hc]
        _ = (R.w₁ * R.w₁) * (R.w₂ * R.w₂) := by group
        _ = 1 := by rw [hw1, hw2, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [R.orderOf_w₁_mul_w₂] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  exact rank_two_normal_sup_eq_top_or_le hT hst hcomm A

theorem rgd2_eq_bot_or_top_of_perfect {G : Type*} [Group G] {n : ℕ} {H : Subgroup G} {r₁ r₂ : G}
    {U : Subgroup G} {root : ℤ → Subgroup G} (R : RGD2 n H r₁ r₂ U root)
    [(cartan (H ⊔ U) R.N).Normal] (hgen : (H ⊔ U) ⊔ R.N = ⊤) [Group.IsPerfect G]
    (hC : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h = 1) (A : Subgroup G) [A.Normal] :
    A = ⊥ ∨ A = ⊤ := by
  rcases rgd2_normal_dichotomy R hgen A with hAtop | hAB
  · right
    by_contra hne
    have hBsolv := R.isSolvable_B
    have hsurj : Function.Surjective ((QuotientGroup.mk' A).comp (H ⊔ U).subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hx : x ∈ A ⊔ (H ⊔ U) := by rw [hAtop]; trivial
      have hx' : x ∈ (A : Set G) * ((H ⊔ U : Subgroup G) : Set G) := by
        rw [← Subgroup.normal_mul]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      refine ⟨⟨b, hb⟩, ?_⟩
      show QuotientGroup.mk b = (QuotientGroup.mk (a * b) : G ⧸ A)
      rw [QuotientGroup.eq]
      have : b⁻¹ * (a * b) ∈ A := by
        have := (inferInstance : A.Normal).conj_mem a ha b⁻¹
        simpa [mul_assoc] using this
      exact this
    have hquot : Group.IsSolvable (G ⧸ A) := Group.isSolvable_of_surjective hsurj
    have hnt : Nontrivial (G ⧸ A) := by
      obtain ⟨g, hg⟩ : ∃ g, g ∉ A := by
        by_contra hall
        push Not at hall
        exact hne (eq_top_iff.2 fun g _ => hall g)
      exact ⟨⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).1 h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (G ⧸ A) hquot
  · left
    have hsat := R.isSaturated
    have hAH : A ≤ H := by
      intro a ha
      have : a ∈ (H ⊔ U) ⊓ R.N := by
        rw [IsSaturated] at hsat
        rw [hsat, Subgroup.mem_iInf]
        intro m
        refine ⟨(m : G) * a * (m : G)⁻¹, hAB ((inferInstance : A.Normal).conj_mem a ha m), ?_⟩
        simp [mul_assoc]
      rwa [R.B_inf_N] at this
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    refine hC a (hAH ha) fun u hu => ?_
    have h1 : a * u * a⁻¹ ∈ U := R.conj_mem_U (hAH ha) hu
    have h2 : u * a⁻¹ * u⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem a⁻¹ (A.inv_mem ha) u
    have h3 : a * (u * a⁻¹ * u⁻¹) ∈ A := A.mul_mem ha h2
    have h4 : a * (u * a⁻¹ * u⁻¹) = (a * u * a⁻¹) * u⁻¹ := by group
    have h5 : (a * u * a⁻¹) * u⁻¹ ∈ U := U.mul_mem h1 (U.inv_mem hu)
    have h6 : (a * u * a⁻¹) * u⁻¹ ∈ U ⊓ H := ⟨h5, hAH (h4 ▸ h3)⟩
    rw [R.U_inf_H, Subgroup.mem_bot] at h6
    have h7 : a * u * a⁻¹ = u := mul_inv_eq_one.1 h6
    calc a * u = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [h7]

variable {X : Type*} [Group X] {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem U_le_of_root_le (R : RGD2 n H r₁ r₂ U root) {S : Subgroup X}
    (hroot : ∀ i, IsRoot n i → root i ≤ S) : U ≤ S := by
  intro u hu
  have : u ∈ chainProd root (intList 1 n) := by rw [← R.carrier_eq]; exact hu
  exact chainProd_subset root S (intList 1 n) (fun k hk => hroot k (isRoot_pos
    (mem_intList_iff.1 hk).1 (mem_intList_iff.1 hk).2)) this

theorem perfect_le_adjust_gen (R : RGD2 n H r₁ r₂ U root) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (S : Subgroup X) [S.Normal] (hperf : ⁅S, S⁆ = S) {a b : X} (ha : a ∈ H) (hb : b ∈ H)
    (hr₁S : r₁ * a ∈ S) (hr₂S : r₂ * b ∈ S) (hU : U ≤ S) :
    S ≤ ((H ⊓ S) ⊔ U) ⊔
      Subgroup.closure (((H ⊓ S : Subgroup X) : Set X) ∪ {r₁ * a, r₂ * b}) := by
  set S₀ : Subgroup X := ((H ⊓ S) ⊔ U) ⊔
      Subgroup.closure (((H ⊓ S : Subgroup X) : Set X) ∪ {r₁ * a, r₂ * b}) with hS₀
  have hHS : H ⊓ S ≤ S₀ := le_sup_left.trans le_sup_left
  have hUS₀ : U ≤ S₀ := le_sup_right.trans le_sup_left
  have hr₁S₀ : r₁ * a ∈ S₀ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
  have hr₂S₀ : r₂ * b ∈ S₀ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr (Or.inr rfl)))
  have hnorm : ∀ h ∈ H, ∀ x ∈ S₀, h * x * h⁻¹ ∈ S₀ := by
    intro h hh
    have key : ∀ (r c : X), c ∈ H → r * c ∈ S → r * c ∈ S₀ → (∀ y ∈ H, r⁻¹ * y * r ∈ H) →
        h * (r * c) * h⁻¹ ∈ S₀ := by
      intro r c hc hrcS hrcS₀ hconj
      have hz : (r * c)⁻¹ * h * (r * c) * h⁻¹ ∈ H ⊓ S := by
        refine ⟨?_, ?_⟩
        · have e : (r * c)⁻¹ * h * (r * c) * h⁻¹ = c⁻¹ * (r⁻¹ * h * r) * c * h⁻¹ := by group
          rw [e]
          exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hc) (hconj h hh)) hc) (H.inv_mem hh)
        · have e : (r * c)⁻¹ * h * (r * c) * h⁻¹ = (r * c)⁻¹ * (h * (r * c) * h⁻¹) := by group
          rw [e]
          exact S.mul_mem (S.inv_mem hrcS) ((inferInstance : S.Normal).conj_mem _ hrcS h)
      have e : h * (r * c) * h⁻¹ = (r * c) * ((r * c)⁻¹ * h * (r * c) * h⁻¹) := by group
      rw [e]
      exact S₀.mul_mem hrcS₀ (hHS hz)
    have hle : S₀ ≤ S₀.comap (MulAut.conj h).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ((Subgroup.closure_le _).2 ?_)
      · intro x hx
        show h * x * h⁻¹ ∈ S₀
        rw [show h * x * h⁻¹ = x from by
          have := R.comm_H h hh x hx.1
          rw [this]; group]
        exact hHS hx
      · intro u hu
        exact hUS₀ (R.conj_mem_U hh hu)
      · rintro g (hg | hg)
        · show h * g * h⁻¹ ∈ S₀
          rw [show h * g * h⁻¹ = g from by
            have := R.comm_H h hh g hg.1
            rw [this]; group]
          exact hHS hg
        · rcases hg with rfl | rfl
          · exact key r₁ a ha hr₁S hr₁S₀ fun y hy => R.conj_H₁' hy
          · exact key r₂ b hb hr₂S hr₂S₀ fun y hy => R.conj_H₂' hy
    exact fun x hx => hle hx
  have htop : S₀ ⊔ H = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le (sup_le le_sup_right (hUS₀.trans le_sup_left)) ((Subgroup.closure_le _).2 ?_)
    rintro g (hg | hg)
    · exact Subgroup.mem_sup_right hg
    · rcases hg with rfl | rfl
      · have : g = (g * a) * a⁻¹ := by group
        rw [this]
        exact (S₀ ⊔ H).mul_mem (Subgroup.mem_sup_left hr₁S₀)
          ((S₀ ⊔ H).inv_mem (Subgroup.mem_sup_right ha))
      · have : g = (g * b) * b⁻¹ := by group
        rw [this]
        exact (S₀ ⊔ H).mul_mem (Subgroup.mem_sup_left hr₂S₀)
          ((S₀ ⊔ H).inv_mem (Subgroup.mem_sup_right hb))
  have hHnorm : H ≤ Subgroup.normalizer (S₀ : Set X) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm h hh x hx, fun hx => ?_⟩
    have := hnorm h⁻¹ (H.inv_mem hh) _ hx
    simpa [mul_assoc] using this
  have hcoe : ((S₀ ⊔ H : Subgroup X) : Set X) = (S₀ : Set X) * (H : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left S₀ H hHnorm
  have hdec : ∀ g : X, ∃ s ∈ S₀, ∃ h ∈ H, g = s * h := by
    intro g
    have hg : g ∈ ((S₀ ⊔ H : Subgroup X) : Set X) := by rw [htop]; trivial
    rw [hcoe] at hg
    obtain ⟨s, hs, h, hh, rfl⟩ := Set.mem_mul.1 hg
    exact ⟨s, hs, h, hh, rfl⟩
  haveI hS₀n : S₀.Normal := ⟨fun x hx g => by
    obtain ⟨s, hs, h, hh, rfl⟩ := hdec g
    have e : s * h * x * (s * h)⁻¹ = s * (h * x * h⁻¹) * s⁻¹ := by group
    rw [e]
    exact S₀.mul_mem (S₀.mul_mem hs (hnorm h hh x hx)) (S₀.inv_mem hs)⟩
  have hcomm : ∀ g₁ g₂ : X, ⁅g₁, g₂⁆ ∈ S₀ := by
    intro g₁ g₂
    obtain ⟨s₁, hs₁, h₁, hh₁, rfl⟩ := hdec g₁
    obtain ⟨s₂, hs₂, h₂, hh₂, rfl⟩ := hdec g₂
    have hπ : ∀ (s h : X), s ∈ S₀ →
        (QuotientGroup.mk' S₀) (s * h) = (QuotientGroup.mk' S₀) h := by
      intro s h hs
      have h0 : (QuotientGroup.mk' S₀) s = 1 := (QuotientGroup.eq_one_iff s).2 hs
      rw [map_mul, h0, one_mul]
    have h1 : ⁅h₁, h₂⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (R.comm_H h₁ hh₁ h₂ hh₂)
    have h2 : (QuotientGroup.mk' S₀) ⁅s₁ * h₁, s₂ * h₂⁆ = 1 := by
      rw [map_commutatorElement, hπ s₁ h₁ hs₁, hπ s₂ h₂ hs₂, ← map_commutatorElement, h1,
        map_one]
    exact (QuotientGroup.eq_one_iff _).1 h2
  intro x hx
  have : x ∈ ⁅S, S⁆ := by rw [hperf]; exact hx
  exact (Subgroup.commutator_le.2 fun g₁ _ g₂ _ => hcomm g₁ g₂) this

theorem rgd2_simple_normal (R : RGD2 n H r₁ r₂ U root) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hC : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h = 1)
    (S : Subgroup X) [S.Normal] (hperf : ⁅S, S⁆ = S)
    (hroot : ∀ i, IsRoot n i → root i ≤ S)
    (A : Subgroup X) (hAS : A ≤ S) (hAn : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A) :
    A = ⊥ ∨ A = S := by
  obtain ⟨a, ha, b, hb, hr₁S, hr₂S, R'⟩ := rgd2_adjust R S hroot
  have hU : U ≤ S := U_le_of_root_le R hroot
  have hgenS := perfect_le_adjust_gen R hgen S hperf ha hb hr₁S hr₂S hU
  have hH' : H ⊓ S ≤ S := inf_le_right
  have R'' := R'.restrict S hH' hr₁S hr₂S hU hroot
  have hgen'' := R'.restrict_gen S hH' hr₁S hr₂S hU hroot (fun x hx => hgenS hx)
  haveI := R''.cartan_normal
  haveI : Group.IsPerfect S := Subgroup.isPerfect_iff.2 hperf
  have hC'' : ∀ h ∈ (H ⊓ S).subgroupOf S, (∀ u ∈ U.subgroupOf S, h * u = u * h) → h = 1 := by
    intro h hh hcomm
    apply Subtype.ext
    exact hC h.1 hh.1 (fun u hu => by
      have := hcomm ⟨u, hU hu⟩ hu
      exact congrArg Subtype.val this)
  haveI hAn' : (A.subgroupOf S).Normal := ⟨fun x hx g => by
    have h1 : (x : X) ∈ A := hx
    exact hAn g.1 g.2 x h1⟩
  rcases rgd2_eq_bot_or_top_of_perfect R'' hgen'' hC'' (A.subgroupOf S) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hAS hx⟩ : S) ∈ A.subgroupOf S := hx
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  · right
    refine le_antisymm hAS fun x hx => ?_
    have h1 : (⟨x, hx⟩ : S) ∈ A.subgroupOf S := by rw [h]; trivial
    exact h1

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
