module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB3
public import CFSG.CGT.Timmesfeld75.Sec3TenFpf
public import CFSG.CGT.Timmesfeld75.Sec3TenExcBasic
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB2

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open DihedralGroup

theorem natCard_subtype_ne_one_add_one {A : Type*} [Group A] [Finite A] :
    Nat.card {a : A // a ≠ 1} + 1 = Nat.card A := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl (fun a : A => a = 1))
  rw [Nat.card_sum] at h
  have h1 : Nat.card {a : A // a = 1} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩, ⟨⟨1, rfl⟩⟩⟩
  rw [h1] at h
  have h2 : Nat.card {a : A // a ≠ 1} = Nat.card {a : A // ¬ a = 1} := rfl
  omega

section Quotient

variable {G : Type} [Group G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

theorem Sec3.exists_mul_of_mem_normalizer_dihedral [Finite G] (hS : Sec3 T T₁) {n : ℕ}
    (hn : Odd n) (e : XQ ≃* DihedralGroup n) {x : G} (hxX : x ∈ T ⊔ T₁)
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) : ∃ t ∈ T, ∃ m ∈ cfgM T T₁, x = t * m := by
  set mk : ↥(T ⊔ T₁) →* XQ := QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) with hmk
  have hTab := hS.cfg.wc.1
  obtain ⟨t₀, ht₀T, ht₀M⟩ : ∃ t₀ ∈ T, t₀ ∉ cfgM T T₁ := by
    by_contra h
    push Not at h
    exact hS.not_le_cfgM h
  have ht₀X : t₀ ∈ T ⊔ T₁ := (le_sup_left : T ≤ T ⊔ T₁) ht₀T
  have hmkM : ∀ y : ↥(T ⊔ T₁), mk y = 1 ↔ (y : G) ∈ cfgM T T₁ := fun y =>
    ⟨fun h => Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h),
      fun h => (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h)⟩
  set s : XQ := mk ⟨t₀, ht₀X⟩ with hs
  have hs1 : s ≠ 1 := fun h => ht₀M ((hmkM _).1 h)
  have hss : s * s = 1 := by
    rw [hs, ← map_mul]
    have : (⟨t₀, ht₀X⟩ * ⟨t₀, ht₀X⟩ : ↥(T ⊔ T₁)) = 1 :=
      Subtype.ext (elemAbelian_mul_self hTab ht₀T)
    rw [this, map_one]
  have hcard : Nat.card ((T.subgroupOf (T ⊔ T₁)).map mk) = 2 := hS.card_map_dihedral hn e
  have hsT : s ∈ (T.subgroupOf (T ⊔ T₁)).map mk :=
    ⟨⟨t₀, ht₀X⟩, Subgroup.mem_subgroupOf.2 ht₀T, rfl⟩
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  have hzp : Subgroup.zpowers s = (T.subgroupOf (T ⊔ T₁)).map mk := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hsT) ?_
    rw [hcard, Nat.card_zpowers, hord]
  have hTQ : ∀ y ∈ (T.subgroupOf (T ⊔ T₁)).map mk, y = 1 ∨ y = s := by
    intro y hy
    rw [← hzp] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      have : s ^ k = s ^ (k % (orderOf s : ℤ)) := (zpow_mod_orderOf s k).symm
      rw [this, hord]
      simp [hk]
    · right
      have : s ^ k = s ^ (k % (orderOf s : ℤ)) := (zpow_mod_orderOf s k).symm
      rw [this, hord]
      simp [hk]
  obtain ⟨b, hb⟩ : ∃ b : XQ, b = mk ⟨x, hxX⟩ := ⟨_, rfl⟩
  have hbs : b * s * b⁻¹ = s := by
    have hxt : x * t₀ * x⁻¹ ∈ T := by
      have := (Subgroup.mem_normalizer_iff.1 hxN t₀).1 ht₀T
      exact this
    have hxtX : x * t₀ * x⁻¹ ∈ T ⊔ T₁ := (le_sup_left : T ≤ T ⊔ T₁) hxt
    have h1 : b * s * b⁻¹ = mk ⟨x * t₀ * x⁻¹, hxtX⟩ := by
      rw [hb, hs, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have h2 : b * s * b⁻¹ ∈ (T.subgroupOf (T ⊔ T₁)).map mk :=
      ⟨⟨x * t₀ * x⁻¹, hxtX⟩, Subgroup.mem_subgroupOf.2 hxt, h1.symm⟩
    rcases hTQ _ h2 with h3 | h3
    · exfalso
      apply hs1
      have : b⁻¹ * (b * s * b⁻¹) * b = s := by group
      rw [← this, h3]
      group
    · exact h3
  have hbs' : e b * e s = e s * e b := by
    have : b * s = s * b := by
      calc b * s = (b * s * b⁻¹) * b := by group
        _ = s * b := by rw [hbs]
    rw [← map_mul, ← map_mul, this]
  obtain ⟨j, hj⟩ := dih_exists_sr_of_sq hn (by rw [← map_mul, hss, map_one])
    (fun h => hs1 (e.injective (h.trans (map_one e).symm)))
  rw [hj] at hbs'
  rcases dih_eq_one_or_of_comm_sr hn j hbs' with h1 | h1
  ·
    have hb1 : b = 1 := e.injective (h1.trans (map_one e).symm)
    refine ⟨1, one_mem _, x, (hmkM ⟨x, hxX⟩).1 (hb ▸ hb1), by group⟩
  · have hbs2 : b = s := e.injective (h1.trans hj.symm)
    have hq : mk ⟨x, hxX⟩ = mk ⟨t₀, ht₀X⟩ := hb ▸ hbs2
    have hmem := QuotientGroup.eq.1 hq
    have hmem' : x⁻¹ * t₀ ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 hmem
    refine ⟨t₀, ht₀T, t₀⁻¹ * x, ?_, by group⟩
    have := (cfgM T T₁).inv_mem hmem'
    simpa using this

theorem Sec3.eq_five_and_exists_conj_of_card_four [Finite G] (hS : Sec3 T T₁) {n : ℕ}
    (hn : Odd n) (hn3 : 3 < n) (e : XQ ≃* DihedralGroup n)
    (hL4 : Nat.card (normIn T T₁) = 4) :
    n = 5 ∧ ∀ m ∈ cfgM T T₁, m ≠ 1 → ∃ x ∈ T ⊔ T₁, m ∈ conjSubgroup x T := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  choose lift hlift using fun k : ZMod n => QuotientGroup.mk_surjective (e.symm (r k))
  have hTab := hS.cfg.wc.1
  have hMab := hS.cfg.isElemAbelian_cfgM
  have hmemM : ∀ (k : ZMod n) (l : ↥(normIn T T₁)),
      (lift k : G) * (l : G) * (lift k : G)⁻¹ ∈ cfgM T T₁ := fun k l =>
    hS.cfg.conj_mem_cfgM (lift k).2 (Cfg.normIn_le_cfgM_left T T₁ l.2)
  have hne1 : ∀ (k : ZMod n) (l : ↥(normIn T T₁)), l ≠ 1 →
      (⟨(lift k : G) * (l : G) * (lift k : G)⁻¹, hmemM k l⟩ : ↥(cfgM T T₁)) ≠ 1 := by
    intro k l hl h
    apply hl
    have h' : (lift k : G) * (l : G) * (lift k : G)⁻¹ = 1 := congrArg Subtype.val h
    apply Subtype.ext
    calc (l : G) = (lift k : G)⁻¹ * ((lift k : G) * (l : G) * (lift k : G)⁻¹) * (lift k : G) := by
          group
      _ = 1 := by rw [h']; group
  let F : ZMod n × {l : ↥(normIn T T₁) // l ≠ 1} → {m : ↥(cfgM T T₁) // m ≠ 1} := fun p =>
    ⟨⟨(lift p.1 : G) * (p.2.1 : G) * (lift p.1 : G)⁻¹, hmemM p.1 p.2.1⟩, hne1 p.1 p.2.1 p.2.2⟩
  have hinj : Function.Injective F := by
    rintro ⟨k, l, hl1⟩ ⟨k', l', hl1'⟩ hF
    have hF' : (lift k : G) * (l : G) * (lift k : G)⁻¹ =
        (lift k' : G) * (l' : G) * (lift k' : G)⁻¹ :=
      congrArg (fun z : {m : ↥(cfgM T T₁) // m ≠ 1} => ((z.1 : ↥(cfgM T T₁)) : G)) hF
    have hyX : (lift k' : G)⁻¹ * (lift k : G) ∈ T ⊔ T₁ :=
      (T ⊔ T₁).mul_mem ((T ⊔ T₁).inv_mem (lift k').2) (lift k).2
    have hyl : ((lift k' : G)⁻¹ * (lift k : G)) * (l : G) * ((lift k' : G)⁻¹ * (lift k : G))⁻¹ =
        l' := by
      calc ((lift k' : G)⁻¹ * (lift k : G)) * (l : G) * ((lift k' : G)⁻¹ * (lift k : G))⁻¹
          = (lift k' : G)⁻¹ * ((lift k : G) * (l : G) * (lift k : G)⁻¹) * (lift k' : G) := by
            group
        _ = l' := by rw [hF']; group
    have hlT : (l : G) ∈ T := normIn_le T T₁ l.2
    have hl'T : (l' : G) ∈ T := normIn_le T T₁ l'.2
    have hyN : (lift k' : G)⁻¹ * (lift k : G) ∈ Subgroup.normalizer (T : Set G) := by
      have hconj : (l' : G) ∈ conjSubgroup ((lift k' : G)⁻¹ * (lift k : G)) T := by
        rw [mem_conjSubgroup]
        have e1 : ((lift k' : G)⁻¹ * (lift k : G))⁻¹ * (l' : G) *
            ((lift k' : G)⁻¹ * (lift k : G)) = l := by
          rw [← hyl]
          group
        rw [e1]
        exact hlT
      have hinf : T ⊓ conjSubgroup ((lift k' : G)⁻¹ * (lift k : G)) T ≠ ⊥ := by
        intro h0
        apply hl1'
        apply Subtype.ext
        have hm : (l' : G) ∈ T ⊓ conjSubgroup ((lift k' : G)⁻¹ * (lift k : G)) T := ⟨hl'T, hconj⟩
        rw [h0, Subgroup.mem_bot] at hm
        exact hm
      exact mem_normalizer_of_conjSubgroup_eq (hS.cfg.wc.conj_eq_of_inf_ne_bot hinf)
    obtain ⟨t, htT, m, hmM, hym⟩ :=
      hS.exists_mul_of_mem_normalizer_dihedral hn e hyX hyN
    have hml : m * (l : G) * m⁻¹ = l := by
      rw [elemAbelian_mul_comm hMab hmM (Cfg.normIn_le_cfgM_left T T₁ l.2)]
      group
    have htl : t * (l : G) * t⁻¹ = l := by
      rw [elemAbelian_mul_comm hTab htT hlT]
      group
    have hll' : (l' : G) = l := by
      rw [← hyl, hym]
      calc t * m * (l : G) * (t * m)⁻¹ = t * (m * (l : G) * m⁻¹) * t⁻¹ := by group
        _ = l := by rw [hml, htl]
    have hkk : k = k' := by
      by_contra hne
      have himg : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
          ⟨(lift k' : G)⁻¹ * (lift k : G), hyX⟩ = e.symm (r (k - k')) := by
        have : (⟨(lift k' : G)⁻¹ * (lift k : G), hyX⟩ : ↥(T ⊔ T₁)) = (lift k')⁻¹ * lift k := rfl
        rw [this, map_mul, map_inv]
        have e1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) (lift k) = e.symm (r k) :=
          hlift k
        have e2 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) (lift k') =
            e.symm (r k') := hlift k'
        rw [e1, e2, ← map_inv, ← map_mul, inv_r, r_mul_r]
        congr 2
        ring
      have hodd : Odd (orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
          ⟨(lift k' : G)⁻¹ * (lift k : G), hyX⟩)) := by
        rw [himg, MulEquiv.orderOf_eq]
        have h2 : (r (k - k') : DihedralGroup n) ^ n = 1 := by
          rw [r_pow]
          have : ((k - k') * (n : ZMod n)) = 0 := by simp
          rw [this]
          rfl
        exact hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)
      have hx1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
          ⟨(lift k' : G)⁻¹ * (lift k : G), hyX⟩ ≠ 1 := by
        rw [himg]
        intro h1
        have h2 := e.symm.injective (h1.trans (map_one e.symm).symm)
        have h3 : (k - k') = 0 := DihedralGroup.r.inj (h2.trans r_zero)
        exact hne (sub_eq_zero.1 h3)
      have hfix : ((lift k' : G)⁻¹ * (lift k : G)) * (l : G) *
          ((lift k' : G)⁻¹ * (lift k : G))⁻¹ = l := by rw [hyl, hll']
      exact hl1 (Subtype.ext (hS.centralizer_cfgM_eq_bot_of_odd_dihedral hn e hyX hodd hx1 l
        (Cfg.normIn_le_cfgM_left T T₁ l.2) hfix))
    subst hkk
    have : l = l' := Subtype.ext hll'.symm
    subst this
    rfl
  have hcardL : Nat.card {l : ↥(normIn T T₁) // l ≠ 1} = 3 := by
    have := natCard_subtype_ne_one_add_one (A := ↥(normIn T T₁))
    rw [hL4] at this
    omega
  have hcardM : Nat.card {m : ↥(cfgM T T₁) // m ≠ 1} = 15 := by
    have := natCard_subtype_ne_one_add_one (A := ↥(cfgM T T₁))
    rw [hS.card_cfgM_eq_sq, hL4] at this
    omega
  have hle := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_prod, Nat.card_zmod, hcardL, hcardM] at hle
  have hn5 : n = 5 := by
    obtain ⟨c, hc⟩ := hn
    omega
  subst hn5
  refine ⟨rfl, ?_⟩
  have hbij : Function.Bijective F :=
    Function.Injective.bijective_of_nat_card_le hinj (by
      rw [Nat.card_prod, Nat.card_zmod, hcardL, hcardM])
  intro m hm hm1
  have hm1' : (⟨m, hm⟩ : ↥(cfgM T T₁)) ≠ 1 := fun h => hm1 (congrArg Subtype.val h)
  obtain ⟨⟨k, l, hl1⟩, hFk⟩ := hbij.2 ⟨⟨m, hm⟩, hm1'⟩
  have hmeq : m = (lift k : G) * (l : G) * (lift k : G)⁻¹ :=
    (congrArg (fun z : {m : ↥(cfgM T T₁) // m ≠ 1} => ((z.1 : ↥(cfgM T T₁)) : G)) hFk).symm
  refine ⟨lift k, (lift k).2, ?_⟩
  rw [hmeq, mem_conjSubgroup]
  have e1 : (lift k : G)⁻¹ * ((lift k : G) * (l : G) * (lift k : G)⁻¹) * (lift k : G) = l := by
    group
  rw [e1]
  exact normIn_le T T₁ l.2

end Quotient

end CFSG.CGT.Timmesfeld75
