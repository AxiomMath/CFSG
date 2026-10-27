module

public import CFSG.CGT.T75G.Sec68Setup
public import CFSG.CGT.Timmesfeld75.Sec5NineLift
public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.CGT.T75G

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {m : ℕ}

namespace Cfg68

variable (c : Cfg68 T T₁ m)
include c

omit c in
theorem L_le_P : normIn T T₁ ≤ T ⊔ normIn T₁ T := (normIn_le T T₁).trans le_sup_left

theorem inf_eq_bot : T ⊓ T₁ = ⊥ := c.cfg.inf

theorem mem_P_of_commute {e f : G} (he : e ∈ normIn T T₁) (he1 : e ≠ 1) (hf : f ∈ classD T)
    (hfe : f * e = e * f) : f ∈ T ⊔ normIn T₁ T := by
  rw [← c.hcl e he he1]
  exact Subgroup.subset_closure ⟨hf, hfe⟩

theorem comm_of_mem_L {e w : G} (he : e ∈ normIn T T₁) (hw : w ∈ T ⊔ normIn T₁ T) :
    e * w = w * e :=
  (c.hZ e (L_le_P he)).2 he w hw

theorem commute_iff {d e f : G} (hd : d ∈ normIn T T₁) (hd1 : d ≠ 1) (he : e ∈ normIn T T₁)
    (he1 : e ≠ 1) (hf : f ∈ classD T) : Commute e f ↔ Commute d f := by
  constructor
  · intro h
    have hfP := c.mem_P_of_commute he he1 hf h.symm.eq
    exact (c.comm_of_mem_L hd hfP)
  · intro h
    have hfP := c.mem_P_of_commute hd hd1 hf h.symm.eq
    exact (c.comm_of_mem_L he hfP)

theorem rootSet_eq {d : G} (hd : d ∈ normIn T T₁) (hd1 : d ≠ 1) :
    rootSet (CorB.cls d) d = {e | e ∈ normIn T T₁ ∧ e ≠ 1} := by
  have hs := c.setup hd hd1
  have hdT : d ∈ T := normIn_le T T₁ hd
  have hDcl := c.classD_iff hdT hd1
  ext e
  constructor
  · rintro ⟨he, hrs⟩
    have he1 : e ≠ 1 := by
      intro h
      have := hs.orderOf_mem he
      rw [h, orderOf_one] at this
      omega
    have heD : e ∈ classD T := (hDcl e).2 he
    have hed : Commute e d := (hrs d (CorB.mem_cls_self d)).2 (Commute.refl d)
    have heP : e ∈ T ⊔ normIn T₁ T := c.mem_P_of_commute hd hd1 heD hed.eq
    have hcent : ∀ w ∈ T ⊔ normIn T₁ T, e * w = w * e := by
      intro w hw
      rw [← c.hcl d hd hd1] at hw
      have hsub : {x : G | x ∈ classD T ∧ x * d = d * x} ⊆
          (Subgroup.centralizer ({e} : Set G) : Set G) := by
        rintro x ⟨hxD, hxd⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ((hrs x ((hDcl x).1 hxD)).2 (show Commute d x from hxd.symm)).eq
      have := (Subgroup.closure_le (Subgroup.centralizer ({e} : Set G))).2 hsub hw
      rw [Subgroup.mem_centralizer_iff] at this
      exact this e (Set.mem_singleton e)
    exact ⟨(c.hZ e heP).1 hcent, he1⟩
  · rintro ⟨he, he1⟩
    have heD : e ∈ classD T := mem_classD_of_mem (normIn_le T T₁ he) he1
    exact ⟨(hDcl e).1 heD, fun f hf => c.commute_iff hd hd1 he he1 ((hDcl f).2 hf)⟩

theorem rootGroup_eq {d : G} (hd : d ∈ normIn T T₁) (hd1 : d ≠ 1) :
    rootGroup (CorB.cls d) d = normIn T T₁ := by
  unfold rootGroup
  rw [c.rootSet_eq hd hd1]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun e he => he.1
  · intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hx, hx1⟩

theorem exists_rootSet_ne {d : G} (hd : d ∈ normIn T T₁) (hd1 : d ≠ 1) :
    ∃ x ∈ CorB.cls d, ∃ e ∈ rootSet (CorB.cls d) x, e ≠ x := by
  have := c.hy.finite
  have hcard : 4 ≤ Nat.card (normIn T T₁) := by
    rw [c.card_L]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) c.hm
  have hex : ∃ e ∈ normIn T T₁, e ≠ 1 ∧ e ≠ d := by
    by_contra hcon
    push Not at hcon
    have hsub : ((normIn T T₁ : Subgroup G) : Set G) ⊆ {1, d} := by
      intro e he
      by_cases h1 : e = 1
      · exact Or.inl h1
      · exact Or.inr (hcon e he h1)
    have h2 : Set.ncard ((normIn T T₁ : Subgroup G) : Set G) ≤ Set.ncard ({1, d} : Set G) :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 : Set.ncard ({1, d} : Set G) ≤ 2 := by
      have := Set.ncard_insert_le (1 : G) ({d} : Set G)
      rw [Set.ncard_singleton] at this
      exact this
    have h4 : Nat.card (normIn T T₁) = Set.ncard ((normIn T T₁ : Subgroup G) : Set G) :=
      Nat.card_coe_set_eq _
    omega
  obtain ⟨e, he, he1, hed⟩ := hex
  refine ⟨d, CorB.mem_cls_self d, e, ?_, hed⟩
  rw [c.rootSet_eq hd hd1]
  exact ⟨he, he1⟩

theorem exists_orderOf_eq_four {d : G} (hd : d ∈ normIn T T₁) (hd1 : d ≠ 1) :
    ∃ a ∈ CorB.cls d, ∃ b ∈ CorB.cls d, orderOf (a * b) = 4 := by
  have := c.hy.finite
  have hcfg := c.cfg
  have hdT := normIn_le T T₁ hd
  have hDcl := c.classD_iff hdT hd1
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.ne₁
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyT₁ : y ∈ T₁ := (mem_normIn.1 hy).1
  have hyD : y ∈ classD T := by
    obtain ⟨x, hx⟩ := c.hy.pair.conj
    have hyx := hyT₁
    rw [hx, mem_conjSubgroup] at hyx
    refine ⟨x⁻¹, x⁻¹ * y * x, hyx, fun h => hy1' ?_, by group⟩
    have : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [this, h]
    group
  have hnc : ∃ t ∈ T, t * y ≠ y * t := by
    by_contra hcon
    push Not at hcon
    have hyP : y ∈ T ⊔ normIn T₁ T := Subgroup.mem_sup_right hy
    have hsub : T ⊔ normIn T₁ T ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (fun t ht => ?_) (fun l hl => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (hcon t ht).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact elemAbelian_mul_comm hcfg.wc₁.1 hyT₁ (mem_normIn.1 hl).1
    have hcentral : ∀ w ∈ T ⊔ normIn T₁ T, y * w = w * y := fun w hw =>
      Subgroup.mem_centralizer_iff.1 (hsub hw) y (Set.mem_singleton y)
    have hyL := (c.hZ y hyP).1 hcentral
    have : y ∈ T ⊓ T₁ := ⟨(mem_normIn.1 hyL).1, hyT₁⟩
    rw [c.inf_eq_bot] at this
    exact hy1' (Subgroup.mem_bot.1 this)
  obtain ⟨t, htT, htn⟩ := hnc
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact htn (by simp)
  have htD : t ∈ classD T := mem_classD_of_mem htT ht1
  refine ⟨t, (hDcl t).1 htD, y, (hDcl y).1 hyD, ?_⟩
  have htt : t * t = 1 := elemAbelian_mul_self c.isElemAbelian htT
  have hyy : y * y = 1 := elemAbelian_mul_self hcfg.wc₁.1 hyT₁
  have hcomm : ⁅t, y⁆ = (t * y) ^ 2 := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right htt, inv_eq_of_mul_eq_one_right hyy,
      sq]
    simp [mul_assoc]
  have hcL : ⁅t, y⁆ ∈ normIn T T₁ :=
    c.hab t (Subgroup.mem_sup_left htT) y (Subgroup.mem_sup_right hy)
  have hcT : ⁅t, y⁆ ∈ T := (mem_normIn.1 hcL).1
  have hc2 : ⁅t, y⁆ * ⁅t, y⁆ = 1 := elemAbelian_mul_self c.isElemAbelian hcT
  have hne2 : ¬ (t * y) ^ 2 ^ 1 = 1 := by
    intro h
    rw [pow_one, ← hcomm, commutatorElement_eq_one_iff_mul_comm] at h
    exact htn h
  have hfin4 : (t * y) ^ 2 ^ (1 + 1) = 1 := by
    have : (t * y) ^ 2 ^ (1 + 1) = ((t * y) ^ 2) ^ 2 := by
      rw [← pow_mul]
      norm_num
    rw [this, ← hcomm, sq]
    exact hc2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := orderOf_eq_prime_pow hne2 hfin4
  simpa using h4

theorem not_isCoatom : ¬ IsCoatom (Subgroup.normalizer ((normIn T T₁ : Subgroup G) : Set G)) := by
  intro hco
  have := c.hy.finite
  have hL1 : normIn T T₁ ≠ ⊥ := c.hy.pair.nontriv
  have hLT : normIn T T₁ ≤ T := normIn_le T T₁
  have h1 := normalizer_le_of_isTI c.isTI hLT hL1
  have hLne : normIn T T₁ ≠ T := by
    intro h
    have h2 : Nat.card (normIn T T₁) = Nat.card T := by rw [h]
    rw [c.card_L, c.hT, sq] at h2
    have h3 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) c.hm
    nlinarith
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun x hx => (mem_normIn.1 hx).2
  obtain ⟨h, hh, hhn⟩ := NaturalSL.exists_not_normalizes c.hnat
    (left_le_hSub : T ≤ hSub T (normIn T₁ T)) hLT hL1 hLne
  have hhN : h ∈ Subgroup.normalizer (T : Set G) := hSub_le_normalizer hL₁N hh
  have hlt : Subgroup.normalizer ((normIn T T₁ : Subgroup G) : Set G) <
      Subgroup.normalizer (T : Set G) :=
    lt_of_le_of_ne h1 (fun heq => hhn (heq ▸ hhN))
  have htop : Subgroup.normalizer (T : Set G) = ⊤ := hco.2 _ hlt
  have hTnorm : T.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have : IsSimpleGroup G := c.hy.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with hT0 | hT0
  · have := c.hy.card
    rw [hT0, Subgroup.card_bot] at this
    omega
  · obtain ⟨a, b, hab⟩ := c.hy.nonab
    exact hab (elemAbelian_mul_comm c.isElemAbelian (hT0 ▸ Subgroup.mem_top a)
      (hT0 ▸ Subgroup.mem_top b))

end Cfg68

end CFSG.CGT.T75G
