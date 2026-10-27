module

public import CFSG.CGT.Timmesfeld75.Sec3Def
public import CFSG.CGT.Timmesfeld75.Config214
public import CFSG.CGT.Timmesfeld75.Targets

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Trans

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

theorem Cfg.exists_comm_mem_cfgM (c : Cfg T T₁) {u s : G}
    (hu : u ∈ Subgroup.normalizer (T : Set G)) (huu : u * u = 1) (hs : s ∈ T)
    (hsM : s ∉ cfgM T T₁) : ∃ y ∈ T, y ∉ cfgM T T₁ ∧ ⁅u, y⁆ ∈ cfgM T T₁ := by
  have hv : u * s * u⁻¹ ∈ T := conj_mem_of_mem_normalizer hu hs
  by_cases hw : s * (u * s * u⁻¹) ∈ cfgM T T₁
  · refine ⟨s, hs, hsM, ?_⟩
    have e : ⁅u, s⁆ = s * (u * s * u⁻¹) := by
      rw [commutatorElement_def, elemAbelian_inv c.wc.1 hs]
      exact elemAbelian_mul_comm c.wc.1 hv hs
    rwa [e]
  · refine ⟨s * (u * s * u⁻¹), T.mul_mem hs hv, hw, ?_⟩
    have huv : u * (u * s * u⁻¹) * u⁻¹ = s := by
      have e : u * (u * s * u⁻¹) * u⁻¹ = (u * u) * s * (u * u)⁻¹ := by group
      rw [e, huu, inv_one, one_mul, mul_one]
    have e : u * (s * (u * s * u⁻¹)) * u⁻¹ = s * (u * s * u⁻¹) :=
      calc u * (s * (u * s * u⁻¹)) * u⁻¹
          = (u * s * u⁻¹) * (u * (u * s * u⁻¹) * u⁻¹) := by group
        _ = (u * s * u⁻¹) * s := by rw [huv]
        _ = s * (u * s * u⁻¹) := elemAbelian_mul_comm c.wc.1 hv hs
    rw [commutatorElement_def, e, mul_inv_cancel]
    exact (cfgM T T₁).one_mem

theorem Cfg.normIn_conjSubgroup_le_cfgM (c : Cfg T T₁) {x : G} (hx : x ∈ T ⊔ T₁)
    (hne : conjSubgroup x T ≠ T) : normIn (conjSubgroup x T) T ≤ cfgM T T₁ := by
  intro u hu
  by_contra huM
  obtain ⟨huC, huN⟩ := mem_normIn.1 hu
  have hs : x⁻¹ * u * x ∈ T := mem_conjSubgroup.1 huC
  have huu : u * u = 1 := elemAbelian_mul_self (isElemAbelian_conjSubgroup c.wc.1 x) huC
  have hsM : x⁻¹ * u * x ∉ cfgM T T₁ := fun h => huM (by
    have h' := c.conj_mem_cfgM hx h
    rwa [show x * (x⁻¹ * u * x) * x⁻¹ = u by group] at h')
  have hsL : x⁻¹ * u * x ∉ normIn T T₁ := fun h => hsM (Cfg.normIn_le_cfgM_left T T₁ h)
  obtain ⟨y, hyT, hyM, hy⟩ := c.exists_comm_mem_cfgM huN huu hs hsM
  have e : (x⁻¹)⁻¹ * (x⁻¹ * u * x) * x⁻¹ = u := by group
  have huT : u ∈ T := by
    have h' := c.strongly_closed_star hyT hyM ((T ⊔ T₁).inv_mem hx) hs hsL (by rwa [e])
    rwa [e] at h'
  have h1 : u ∈ T ⊓ conjSubgroup x T := ⟨huT, huC⟩
  rw [c.wc.inf_conj_eq_bot hne, Subgroup.mem_bot] at h1
  exact huM (h1 ▸ (cfgM T T₁).one_mem)

end Trans

section Involutions

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

theorem Cfg.exists_mem_conjSubgroup_of_isConj_mod [Finite G] (c : Cfg T T₁)
    (hconj : ∃ x : G, T₁ = conjSubgroup x T)
    (hQ : ∀ b ∈ T ⊔ T₁, b * b = 1 → b ∉ cfgM T T₁ → ∀ a ∈ T ⊔ T₁, a * a = 1 →
      a ∉ cfgM T T₁ → ∃ k ∈ T ⊔ T₁, (k * b * k⁻¹)⁻¹ * a ∈ cfgM T T₁)
    {a : G} (ha : a ∈ T ⊔ T₁) (haa : a * a = 1) (haM : a ∉ cfgM T T₁) :
    ∃ x ∈ T ⊔ T₁, a ∈ conjSubgroup x T := by
  obtain ⟨t, htT, htL⟩ := IsConcreteLE.exists_of_lt (c.normIn_lt hconj)
  have htM : t ∉ cfgM T T₁ := fun hM => htL (by rw [← c.inf_cfgM]; exact ⟨htT, hM⟩)
  have htt : t * t = 1 := elemAbelian_mul_self c.wc.1 htT
  obtain ⟨k, hk, hkm⟩ := hQ t (Subgroup.mem_sup_left htT) htt htM a ha haa haM
  obtain ⟨a', ha'def⟩ : ∃ a', a' = k * t * k⁻¹ := ⟨_, rfl⟩
  rw [← ha'def] at hkm
  have ht' : k⁻¹ * a' * k = t := by rw [ha'def]; group
  have ha'a' : a' * a' = 1 :=
    calc a' * a' = k * (t * t) * k⁻¹ := by rw [ha'def]; group
      _ = 1 := by rw [htt]; group
  have ha'mem : a' ∈ conjSubgroup k T := mem_conjSubgroup.2 (by rw [ht']; exact htT)
  have hmm : (a'⁻¹ * a) * (a'⁻¹ * a) = 1 := elemAbelian_mul_self c.isElemAbelian_cfgM hkm
  have hcomm : a' * (a'⁻¹ * a) = (a'⁻¹ * a) * a' := by
    rw [inv_eq_of_mul_eq_one_right ha'a'] at hmm ⊢
    calc a' * (a' * a) = a := by rw [← mul_assoc, ha'a', one_mul]
      _ = (a' * a * (a' * a)) * a := by rw [hmm, one_mul]
      _ = (a' * a) * a' * (a * a) := by simp only [mul_assoc]
      _ = (a' * a) * a' := by rw [haa, mul_one]
  have hm' : k⁻¹ * (a'⁻¹ * a) * k ∈ cfgM T T₁ := by
    have h := c.conj_mem_cfgM ((T ⊔ T₁).inv_mem hk) hkm
    rwa [inv_inv] at h
  have hct : t * (k⁻¹ * (a'⁻¹ * a) * k) = (k⁻¹ * (a'⁻¹ * a) * k) * t :=
    calc t * (k⁻¹ * (a'⁻¹ * a) * k) = (k⁻¹ * a' * k) * (k⁻¹ * (a'⁻¹ * a) * k) := by rw [ht']
      _ = k⁻¹ * (a' * (a'⁻¹ * a)) * k := by group
      _ = k⁻¹ * ((a'⁻¹ * a) * a') * k := by rw [hcomm]
      _ = (k⁻¹ * (a'⁻¹ * a) * k) * (k⁻¹ * a' * k) := by group
      _ = (k⁻¹ * (a'⁻¹ * a) * k) * t := by rw [ht']
  have hmC : k⁻¹ * (a'⁻¹ * a) * k ∈ cfgM T T₁ ⊓ Subgroup.centralizer ({t} : Set G) :=
    ⟨hm', Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh; subst hh; exact hct⟩
  rw [c.cfgM_inf_centralizer htT htM] at hmC
  refine ⟨k, hk, ?_⟩
  have h := Subgroup.mul_mem _ ha'mem (mem_conjSubgroup.2 (normIn_le _ _ hmC))
  rwa [mul_inv_cancel_left] at h

end Involutions

section Quotient

variable {Y : Type*} [Group Y]

theorem exists_conj_mul_mem_of_quotient_isConj {N : Subgroup Y} [N.Normal]
    (h : ∀ x y : Y ⧸ N, orderOf x = 2 → orderOf y = 2 → IsConj x y) {a b : Y}
    (haa : a * a = 1) (hbb : b * b = 1) (haN : a ∉ N) (hbN : b ∉ N) :
    ∃ k : Y, (k * b * k⁻¹)⁻¹ * a ∈ N := by
  have hord : ∀ z : Y, z * z = 1 → z ∉ N → orderOf (z : Y ⧸ N) = 2 := by
    intro z hzz hzN
    refine orderOf_eq_prime ?_ fun h1 => hzN ((QuotientGroup.eq_one_iff z).1 h1)
    rw [pow_two, ← QuotientGroup.mk_mul, hzz]
    rfl
  obtain ⟨k', hk'⟩ := isConj_iff.1 (h _ _ (hord b hbb hbN) (hord a haa haN))
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k'
  refine ⟨k, QuotientGroup.eq.1 ?_⟩
  rw [← hk', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

end Quotient

section Inputs

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mul_mem_cfgM_of_inputs (hL214 : Lemma214) (hInv : InvolutionClassInput)
    {T : Subgroup G} (hT : IsWC T) {g : G} (hne : conjSubgroup g T ≠ T)
    (hL : normIn T (conjSubgroup g T) ≠ ⊥) {b : G} (hb : b ∈ T ⊔ conjSubgroup g T)
    (hbb : b * b = 1) (hbM : b ∉ cfgM T (conjSubgroup g T)) {a : G}
    (ha : a ∈ T ⊔ conjSubgroup g T) (haa : a * a = 1) (haM : a ∉ cfgM T (conjSubgroup g T)) :
    ∃ k ∈ T ⊔ conjSubgroup g T, (k * b * k⁻¹)⁻¹ * a ∈ cfgM T (conjSubgroup g T) := by
  obtain ⟨-, hn, hcases⟩ := hL214 G T hT g hne hL
  obtain ⟨k, hk⟩ := exists_conj_mul_mem_of_quotient_isConj (hInv _ hcases)
    (a := (⟨a, ha⟩ : ↥(T ⊔ conjSubgroup g T))) (b := (⟨b, hb⟩ : ↥(T ⊔ conjSubgroup g T)))
    (Subtype.ext haa) (Subtype.ext hbb) (fun h => haM (Subgroup.mem_subgroupOf.1 h))
    (fun h => hbM (Subgroup.mem_subgroupOf.1 h))
  exact ⟨k, k.2, Subgroup.mem_subgroupOf.1 hk⟩

theorem Sec3.of_inputs (hL214 : Lemma214) (hInv : InvolutionClassInput) {T : Subgroup G}
    (hT : IsWC T) {g : G} (hne : conjSubgroup g T ≠ T)
    (hL : normIn T (conjSubgroup g T) ≠ ⊥) : Sec3 T (conjSubgroup g T) := by
  have c : Cfg T (conjSubgroup g T) := Cfg.of_conj hT hne hL
  obtain ⟨x, hxX, hx⟩ := exists_mem_conj_eq_of_le hT
    (le_sup_left : T ≤ T ⊔ conjSubgroup g T) le_sup_right
  refine ⟨c, ⟨x, hxX, hx⟩, fun a ha haa haM => ?_, fun y hy hne' =>
    c.normIn_conjSubgroup_le_cfgM hy hne'⟩
  exact c.exists_mem_conjSubgroup_of_isConj_mod ⟨g, rfl⟩
    (fun b hb hbb hbM a ha haa haM =>
      exists_conj_mul_mem_cfgM_of_inputs hL214 hInv hT hne hL hb hbb hbM ha haa haM) ha haa haM

end Inputs

end CFSG.CGT.Timmesfeld75
