module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Tools
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

variable {A : Type} [Group A]

theorem comp_not_le_centralizer {J : Subgroup A} (hJ : IsComponent J) : ¬ J ≤ centralizer (J : Set A) := by
  intro h
  obtain ⟨_, hs, a, b, hab⟩ := hJ.1
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have := (Subgroup.mem_centralizer_iff.mp (h b'.2)) a' a'.2
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext this

theorem isComponent_map_of_normal {T : Subgroup A} [T.Normal] {K' : Subgroup ↥T} (hK : IsComponent K') :
    IsComponent (K'.map T.subtype) := by
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (K'.equivMapOfInjective T.subtype T.subtype_injective) hK.1
  · have hle : K'.map T.subtype ≤ T := by
      rintro _ ⟨k, -, rfl⟩; exact k.2
    refine Subgroup.IsSubnormal.trans hle ?_ (Subgroup.Normal.isSubnormal inferInstance)
    have : (K'.map T.subtype).subgroupOf T = K' := Subgroup.comap_map_eq_self_of_injective T.subtype_injective K'
    rw [this]; exact hK.2

theorem layer_eq_bot_of_normal {T J : Subgroup A} [T.Normal] (hJ : IsComponent J) (hJC : T ≤ centralizer (J : Set A))
    (hcomp : ∀ J' : Subgroup A, IsComponent J' → J' ≤ T → J' = J) : layer ↥T = ⊥ := by
  apply CFSG.LocalCores.layer_eq_bot_of_forall
  intro K' hK'
  have hq := isComponent_map_of_normal hK'
  have hle : K'.map T.subtype ≤ T := by
    rintro _ ⟨k, -, rfl⟩; exact k.2
  have := hcomp _ hq hle
  rw [this] at hle
  exact comp_not_le_centralizer hJ (hle.trans hJC)


section
variable [Finite A]

omit [Finite A] in
theorem pCore_map_normal (T : Subgroup A) [T.Normal] (q : ℕ) : ((pCore q ↥T).map T.subtype).Normal := by
  refine ⟨?_⟩
  rintro n ⟨y, hy, rfl⟩ g
  refine ⟨MulAut.conjNormal g y, ?_, ?_⟩
  · have hfix := (inferInstance : (pCore q ↥T).Characteristic).fixed (MulAut.conjNormal g)
    have : y ∈ (pCore q ↥T).comap (MulAut.conjNormal g).toMonoidHom := by rw [hfix]; exact hy
    exact this
  · simp

theorem ncl_cent_facts {p : ℕ} (hp : p.Prime) {X J : Subgroup A}
    (_hXp : IsPGroup p ↥X) (hop : pCore p A = ⊥) (hJ : IsComponent J) (hJn : J.Normal)
    (hcomp : ∀ J' : Subgroup A, IsComponent J' → J' ≤ ncl X → J' = J)
    (hF : ∀ q : ℕ, q.Prime → X ≤ centralizer ((pCore q A : Subgroup A) : Set A)) :
    (∀ t ∈ ncl X ⊓ centralizer (J : Set A), ∀ k ∈ ncl X, t * k = k * t) ∧
      (∀ t ∈ ncl X ⊓ centralizer (J : Set A), ∀ m : ℕ, t ^ (p ^ m) = 1 → t = 1) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set K : Subgroup A := ncl X with hK
  have hKn : K.Normal := Subgroup.normalClosure_normal
  have := hJn
  set C : Subgroup A := centralizer (J : Set A) with hC
  have hCn : C.Normal := normal_centralizer_of_normal J
  set T : Subgroup A := K ⊓ C with hT
  have hTn : T.Normal := inferInstance
  have hlay : layer ↥T = ⊥ :=
    layer_eq_bot_of_normal hJ inf_le_right (fun J' hJ' hle => hcomp J' hJ' (hle.trans inf_le_left))
  have hgf : generalizedFitting ↥T = fittingSubgroup ↥T := by
    rw [generalizedFitting, hlay, sup_bot_eq]
  have hq : ∀ q : ℕ, q.Prime → ∀ y : ↥T, y ∈ pCore q ↥T → ∀ k ∈ K, (y : A) * k = k * (y : A) := by
    intro q hq y hy k hk
    set D : Subgroup A := (pCore q ↥T).map T.subtype with hD
    have hDn : D.Normal := pCore_map_normal T q
    have hDle : D ≤ pCore q A := pCore_map_le T q
    have hXD : X ≤ centralizer (D : Set A) :=
      (hF q hq).trans (Subgroup.centralizer_le hDle)
    have hCD : (centralizer (D : Set A)).Normal := normal_centralizer_of_normal D
    have hKD : K ≤ centralizer (D : Set A) := Subgroup.normalClosure_le_normal hXD
    exact Subgroup.mem_centralizer_iff.mp (hKD hk) (y : A) ⟨y, hy, rfl⟩
  have hFcent : ∀ y : ↥T, y ∈ fittingSubgroup ↥T → ∀ k ∈ K, (y : A) * k = k * (y : A) := by
    intro y hy
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore] at hy
    refine Subgroup.iSup_induction (fun p : (Nat.card ↥T).primeFactors => pCore (p : ℕ) ↥T)
      (C := fun y : ↥T => ∀ k ∈ K, (y : A) * k = k * (y : A)) hy ?_ ?_ ?_
    · intro i y hy
      exact hq (i : ℕ) (Nat.prime_of_mem_primeFactors i.2) y hy
    · intro k _; simp
    · intro y₁ y₂ h₁ h₂ k hk
      calc ((y₁ * y₂ : ↥T) : A) * k = (y₁ : A) * ((y₂ : A) * k) := by simp [mul_assoc]
        _ = (y₁ : A) * (k * (y₂ : A)) := by rw [h₂ k hk]
        _ = ((y₁ : A) * k) * (y₂ : A) := by rw [mul_assoc]
        _ = (k * (y₁ : A)) * (y₂ : A) := by rw [h₁ k hk]
        _ = k * ((y₁ * y₂ : ↥T) : A) := by simp [mul_assoc]
  have hTz : ∀ t ∈ T, ∀ k ∈ K, t * k = k * t := by
    intro t ht k hk
    have hy : (⟨t, ht⟩ : ↥T) ∈ centralizer ((generalizedFitting ↥T : Subgroup ↥T) : Set ↥T) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      rw [hgf] at hf
      apply Subtype.ext
      exact hFcent f hf t ((show T ≤ K from inf_le_left) ht)
    have hyF := centralizer_generalizedFitting_le_fitting' ↥T hy
    exact hFcent _ hyF k hk
  have hTK : T ≤ K := inf_le_left
  have hTp : ∀ t ∈ T, ∀ m : ℕ, t ^ (p ^ m) = 1 → t = 1 := by
    intro t0 ht0 m0 hm0
    let S : Subgroup A :=
      { carrier := {t | t ∈ T ∧ ∃ m : ℕ, t ^ (p ^ m) = 1}
        one_mem' := ⟨T.one_mem, 0, by simp⟩
        mul_mem' := by
          rintro a b ⟨haT, m₁, h₁⟩ ⟨hbT, m₂, h₂⟩
          refine ⟨T.mul_mem haT hbT, m₁ + m₂, ?_⟩
          have hc : Commute a b := hTz a haT b (hTK hbT)
          rw [hc.mul_pow]
          have e1 : a ^ (p ^ (m₁ + m₂)) = 1 := by
            rw [pow_add, pow_mul, h₁, one_pow]
          have e2 : b ^ (p ^ (m₁ + m₂)) = 1 := by
            rw [add_comm, pow_add, pow_mul, h₂, one_pow]
          rw [e1, e2, one_mul]
        inv_mem' := by
          rintro a ⟨haT, m, h⟩
          exact ⟨T.inv_mem haT, m, by rw [inv_pow, h, inv_one]⟩ }
    have hSn : S.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨hnT, m, hm⟩ := hn
      exact ⟨hTn.conj_mem n hnT g, m, by rw [conj_pow, hm]; group⟩
    have hSp : IsPGroup p ↥S := by
      rintro ⟨s, hs⟩
      obtain ⟨m, hm⟩ := hs.2
      exact ⟨m, Subtype.ext hm⟩
    have hmem : S ∈ {M : Subgroup A | M.Normal ∧ IsPGroup p ↥M} := ⟨hSn, hSp⟩
    have hSle : S ≤ pCore p A := le_sSup hmem
    rw [hop] at hSle
    exact Subgroup.mem_bot.mp (hSle ⟨ht0, m0, hm0⟩)
  exact ⟨hTz, hTp⟩

theorem ncl_eq_of_single_comp {p : ℕ} (hp : p.Prime) {X J : Subgroup A}
    (hXp : IsPGroup p ↥X) (hop : pCore p A = ⊥) (hJ : IsComponent J) (hJn : J.Normal) (hJK : J ≤ ncl X)
    (hXJ : X ≤ J ⊔ centralizer (J : Set A))
    (hcomp : ∀ J' : Subgroup A, IsComponent J' → J' ≤ ncl X → J' = J)
    (hF : ∀ q : ℕ, q.Prime → X ≤ centralizer ((pCore q A : Subgroup A) : Set A)) :
    ncl X = J := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTz, hTp⟩ := ncl_cent_facts hp hXp hop hJ hJn hcomp hF
  set K : Subgroup A := ncl X with hK
  have hKn : K.Normal := Subgroup.normalClosure_normal
  have := hJn
  set C : Subgroup A := centralizer (J : Set A) with hC
  have hCn : C.Normal := normal_centralizer_of_normal J
  set T : Subgroup A := K ⊓ C with hT
  have hTn : T.Normal := inferInstance
  have hKle : K ≤ J ⊔ C := by
    refine Subgroup.normalClosure_le_normal ?_
    exact hXJ
  have hdec : ∀ k ∈ K, ∃ j ∈ J, ∃ t ∈ T, k = j * t := by
    intro k hk
    have hk' : k ∈ ((J ⊔ C : Subgroup A) : Set A) := hKle hk
    rw [Subgroup.normal_mul J C] at hk'
    obtain ⟨j, hj, c, hc, rfl⟩ := hk'
    refine ⟨j, hj, c, ⟨?_, hc⟩, rfl⟩
    have : c = j⁻¹ * (j * c) := by group
    rw [this]; exact K.mul_mem (K.inv_mem (hJK hj)) hk
  have hTK : T ≤ K := inf_le_left
  have hmk : ∀ k ∈ K, ∃ t ∈ T, QuotientGroup.mk' J k = QuotientGroup.mk' J t := by
    intro k hk
    obtain ⟨j, hj, t, ht, rfl⟩ := hdec k hk
    refine ⟨t, ht, ?_⟩
    have : QuotientGroup.mk' J j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
    rw [map_mul, this, one_mul]
  have hcommq : ∀ k₁ ∈ K, ∀ k₂ ∈ K,
      QuotientGroup.mk' J k₁ * QuotientGroup.mk' J k₂ = QuotientGroup.mk' J k₂ * QuotientGroup.mk' J k₁ := by
    intro k₁ h₁ k₂ h₂
    obtain ⟨t₁, ht₁, e₁⟩ := hmk k₁ h₁
    obtain ⟨t₂, ht₂, e₂⟩ := hmk k₂ h₂
    rw [e₁, e₂, ← map_mul, ← map_mul, hTz t₁ ht₁ t₂ (hTK ht₂)]
  have hqp : ∀ k ∈ K, ∃ m : ℕ, (QuotientGroup.mk' J k) ^ (p ^ m) = 1 := by
    intro k hk
    have hk2 : k ∈ Subgroup.closure (Group.conjugatesOfSet (X : Set A)) := hk
    refine Subgroup.closure_induction
      (p := fun k _ => ∃ m : ℕ, (QuotientGroup.mk' J k) ^ (p ^ m) = 1) ?_ ?_ ?_ ?_ hk2
    · intro g hg
      obtain ⟨b, hb, hbg⟩ := Group.mem_conjugatesOfSet_iff.mp hg
      obtain ⟨c, rfl⟩ := isConj_iff.mp hbg
      obtain ⟨m, hm⟩ := hXp ⟨b, hb⟩
      refine ⟨m, ?_⟩
      have hm' : b ^ (p ^ m) = 1 := by simpa using congrArg Subtype.val hm
      rw [← map_pow, conj_pow, hm']
      simp
    · exact ⟨0, by simp⟩
    · intro x y hx hy ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
      refine ⟨m₁ + m₂, ?_⟩
      have hc : Commute (QuotientGroup.mk' J x) (QuotientGroup.mk' J y) := hcommq x hx y hy
      rw [map_mul, hc.mul_pow]
      have e1 : (QuotientGroup.mk' J x) ^ (p ^ (m₁ + m₂)) = 1 := by
        rw [pow_add, pow_mul, h₁, one_pow]
      have e2 : (QuotientGroup.mk' J y) ^ (p ^ (m₁ + m₂)) = 1 := by
        rw [add_comm, pow_add, pow_mul, h₂, one_pow]
      rw [e1, e2, one_mul]
    · intro x hx ⟨m, h⟩
      exact ⟨m, by rw [map_inv, inv_pow, h, inv_one]⟩
  have hTJ : ∀ t ∈ T, t ∈ J := by
    intro t ht
    obtain ⟨m, hm⟩ := hqp t (hTK ht)
    have hmJ : t ^ (p ^ m) ∈ J := by
      rw [← map_pow] at hm
      exact (QuotientGroup.eq_one_iff _).mp hm
    have hcop : Nat.Coprime (p ^ m) (orderOf t) := by
      refine Nat.Coprime.pow_left m ?_
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
      intro hdvd
      obtain ⟨c, hc⟩ := hdvd
      have hpos : 0 < orderOf t := orderOf_pos t
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        omega
      have hord : orderOf (t ^ c) = p := by
        rw [orderOf_pow_of_dvd hc0 ⟨p, by rw [hc]; ring⟩, hc, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hc0)]
      have hone := hTp (t ^ c) (T.pow_mem ht _) 1 (by rw [pow_one, ← hord]; exact pow_orderOf_eq_one _)
      rw [hone, orderOf_one] at hord
      exact hp.one_lt.ne hord
    obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hr]
    exact J.pow_mem hmJ r
  have hKJ : K ≤ J := by
    intro k hk
    obtain ⟨j, hj, t, ht, rfl⟩ := hdec k hk
    exact J.mul_mem hj (hTJ t ht)
  exact le_antisymm hKJ hJK

end


end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
