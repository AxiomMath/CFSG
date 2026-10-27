module

public import CFSG.Fischer.Uniq.F23Uniq
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1009
public import CFSG.Fischer.Polar.Lines

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Rec23

theorem fi22_exists_localClass
    (p : Sporadic.Fi22.D) :
    ∃ q : Sporadic.Fi22.D, (q : Sporadic.Fi22.J) ≠ p ∧
      (q : Sporadic.Fi22.J) * p = p * (q : Sporadic.Fi22.J) := by
  obtain ⟨q, hq⟩ := Set.nonempty_of_ncard_ne_zero
    (s := LocalClass Sporadic.Fi22.D (p : Sporadic.Fi22.J))
    (by rw [ncard_localClass_D p.2]; norm_num)
  exact ⟨⟨q, hq.1⟩, hq.2.1, hq.2.2⟩

theorem fi22_exists_not_commute
    (p q : Sporadic.Fi22.D) :
    ∃ s : Sporadic.Fi22.D, (s : Sporadic.Fi22.J) * p ≠ p * s ∧
      (s : Sporadic.Fi22.J) * q ≠ q * s := by
  by_contra hcon
  have hcon' : ∀ s : Sporadic.Fi22.D, (s : Sporadic.Fi22.J) * p ≠ p * s →
      (s : Sporadic.Fi22.J) * q = q * s := fun s hs => by
    by_contra hq
    exact hcon ⟨s, hs, hq⟩
  have hsub : (Sporadic.Fi22.D : Set Sporadic.Fi22.J) ⊆
      ({(p : Sporadic.Fi22.J), (q : Sporadic.Fi22.J)} : Set Sporadic.Fi22.J) ∪
        LocalClass Sporadic.Fi22.D (p : Sporadic.Fi22.J) ∪
        LocalClass Sporadic.Fi22.D (q : Sporadic.Fi22.J) := by
    intro s hs
    by_cases h1 : s * p = p * s
    · by_cases h2 : s = p
      · exact Or.inl (Or.inl (Or.inl h2))
      · exact Or.inl (Or.inr ⟨hs, h2, h1⟩)
    · have h3 := hcon' ⟨s, hs⟩ h1
      by_cases h4 : s = q
      · exact Or.inl (Or.inl (Or.inr h4))
      · exact Or.inr ⟨hs, h4, h3⟩
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h1 := Set.ncard_union_le (({(p : Sporadic.Fi22.J), (q : Sporadic.Fi22.J)} :
    Set Sporadic.Fi22.J) ∪ LocalClass Sporadic.Fi22.D (p : Sporadic.Fi22.J))
    (LocalClass Sporadic.Fi22.D (q : Sporadic.Fi22.J))
  have h2 := Set.ncard_union_le ({(p : Sporadic.Fi22.J), (q : Sporadic.Fi22.J)} :
    Set Sporadic.Fi22.J) (LocalClass Sporadic.Fi22.D (p : Sporadic.Fi22.J))
  have h3 : ({(p : Sporadic.Fi22.J), (q : Sporadic.Fi22.J)} : Set Sporadic.Fi22.J).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  rw [ncard_D] at hcard
  rw [ncard_localClass_D p.2] at h2
  rw [ncard_localClass_D q.2] at h1
  omega

structure LocalHyp (G : Type) [Group G] (D : Set G) : Prop where
  inv : ∀ d ∈ D, orderOf d = 2
  prod : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)
  loc : ∀ d ∈ D, Nonempty (LocalPoints (pairModel Sporadic.Fi22.pair_D) D d)

structure IsStarClosed {G : Type} [Group G] (D K : Set G) : Prop where
  subset : K ⊆ D
  nonempty : K.Nonempty
  nbr : ∀ k ∈ K, ∀ c ∈ D, c * k = k * c → c ∈ K
  conj : ∀ k ∈ K, ∀ c ∈ K, k * c * k ∈ K

@[expose] def HasZ {G : Type} [Group G] (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ g : G, (∀ f ∈ insert d (LocalClass D d), g * f = f * g) → g = 1 ∨ g = d

variable {G : Type} [Group G] {D K : Set G}

theorem exists_mem_localClass_of_localPoints {d : G}
    (L : LocalPoints (pairModel Sporadic.Fi22.pair_D) D d) : ∃ f, f ∈ LocalClass D d :=
  ⟨L.χ.symm ⟨Sporadic.Fi22.a, Sporadic.Fi22.a_mem_D⟩, (L.χ.symm _).2⟩

namespace LocalHyp

theorem of_pair (hE : Pair G D)
    (hloc : ∀ f ∈ D, Nonempty (LocalPoints (pairModel Sporadic.Fi22.pair_D) D f)) :
    LocalHyp G D :=
  ⟨hE.2.2.1, hE.2.2.2.1, hloc⟩

variable (hH : LocalHyp G D)
include hH

theorem mul_self {d : G} (hd : d ∈ D) : d * d = 1 := by
  rw [← sq, ← hH.inv d hd, pow_orderOf_eq_one]

theorem inv_eq {d : G} (hd : d ∈ D) : d⁻¹ = d :=
  inv_eq_of_mul_eq_one_right (hH.mul_self hd)

theorem mul_mul_eq {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ≠ b * a) :
    a * b * a = b * a * b := by
  have h3 : orderOf (a * b) = 3 := by
    rcases hH.prod a ha b hb with h | h | h
    · rw [orderOf_eq_one_iff] at h
      have hfe : b = a := by rw [← hH.inv_eq ha]; exact eq_inv_of_mul_eq_one_right h
      exact absurd (by rw [hfe]) hab
    · exfalso
      apply hab
      have h2 : (a * b) * (a * b) = 1 := by rw [← sq, ← h, pow_orderOf_eq_one]
      rw [eq_inv_of_mul_eq_one_left h2, mul_inv_rev, hH.inv_eq ha, hH.inv_eq hb]
    · exact h
  have h3' : (a * b) ^ 3 = 1 := by rw [← h3, pow_orderOf_eq_one]
  have h : a * b * a * (b * a * b) = 1 := by
    rw [← h3']; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, mul_inv_rev, hH.inv_eq ha, hH.inv_eq hb,
    mul_assoc]

theorem exists_common_nbr
    {a b : G} (ha : a ∈ D) (hb : b ∈ LocalClass D a) :
    ∃ g, g ∈ LocalClass D a ∧ g ∈ LocalClass D b := by
  obtain ⟨L⟩ := hH.loc a ha
  obtain ⟨q, hqp, hqc⟩ := fi22_exists_localClass (L.χ ⟨b, hb⟩)
  refine ⟨(L.χ.symm q : G), (L.χ.symm q).2, (L.χ.symm q).2.1, ?_, ?_⟩
  · intro h
    apply hqp
    have : L.χ.symm q = ⟨b, hb⟩ := Subtype.ext h
    rw [← Equiv.apply_symm_apply L.χ q, this]
  · have := (L.comm (L.χ.symm q) ⟨b, hb⟩).2
    rw [Equiv.apply_symm_apply] at this
    exact this hqc

theorem exists_noncomm_nbr
    {g a b : G} (hg : g ∈ D) (ha : a ∈ LocalClass D g)
    (hb : b ∈ LocalClass D g) :
    ∃ σ, σ ∈ LocalClass D g ∧ σ * a ≠ a * σ ∧ σ * b ≠ b * σ := by
  obtain ⟨L⟩ := hH.loc g hg
  obtain ⟨s, hsa, hsb⟩ := fi22_exists_not_commute (L.χ ⟨a, ha⟩) (L.χ ⟨b, hb⟩)
  refine ⟨(L.χ.symm s : G), (L.χ.symm s).2, fun h => hsa ?_, fun h => hsb ?_⟩
  · have := (L.comm (L.χ.symm s) ⟨a, ha⟩).1 h
    rwa [Equiv.apply_symm_apply] at this
  · have := (L.comm (L.χ.symm s) ⟨b, hb⟩).1 h
    rwa [Equiv.apply_symm_apply] at this

end LocalHyp

namespace IsStarClosed

variable (hH : LocalHyp G D) (hK : IsStarClosed D K)
include hH hK

theorem conjIn_of_not_commute {a b : G} (ha : a ∈ K) (hb : b ∈ K) (hab : a * b ≠ b * a) :
    ∃ w ∈ Subgroup.closure K, w * a * w⁻¹ = b := by
  refine ⟨a * b, Subgroup.mul_mem _ (Subgroup.subset_closure ha) (Subgroup.subset_closure hb), ?_⟩
  have haD := hK.subset ha
  have hbD := hK.subset hb
  have hbr := hH.mul_mul_eq haD hbD hab
  have h1 : (a * b)⁻¹ = b * a := by
    rw [mul_inv_rev, hH.inv_eq haD, hH.inv_eq hbD]
  rw [h1]
  calc a * b * a * (b * a) = (a * b * a) * (b * a) := by group
    _ = (b * a * b) * (b * a) := by rw [hbr]
    _ = b * a * (b * b) * a := by group
    _ = b := by rw [hH.mul_self hbD, mul_one, mul_assoc, hH.mul_self haD, mul_one]

theorem conjIn
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    ∃ w ∈ Subgroup.closure K, w * a * w⁻¹ = b := by
  by_cases hab : a * b = b * a
  · by_cases hEq : a = b
    · exact ⟨1, one_mem _, by simp [hEq]⟩
    · have hbl : b ∈ LocalClass D a := ⟨hK.subset hb, fun h => hEq h.symm, hab.symm⟩
      obtain ⟨g, hga, hgb⟩ := hH.exists_common_nbr (hK.subset ha) hbl
      have hgK : g ∈ K := hK.nbr a ha g hga.1 hga.2.2
      have hal : a ∈ LocalClass D g := ⟨hK.subset ha, fun h => hga.2.1 h.symm, hga.2.2.symm⟩
      have hbl' : b ∈ LocalClass D g := ⟨hK.subset hb, fun h => hgb.2.1 h.symm, hgb.2.2.symm⟩
      obtain ⟨σ, hσ, hσa, hσb⟩ := hH.exists_noncomm_nbr (hK.subset hgK) hal hbl'
      have hσK : σ ∈ K := hK.nbr g hgK σ hσ.1 hσ.2.2
      obtain ⟨w₁, hw₁, e₁⟩ := conjIn_of_not_commute hH hK ha hσK fun h => hσa h.symm
      obtain ⟨w₂, hw₂, e₂⟩ := conjIn_of_not_commute hH hK hσK hb hσb
      refine ⟨w₂ * w₁, Subgroup.mul_mem _ hw₂ hw₁, ?_⟩
      rw [← e₂, ← e₁]
      group
  · exact conjIn_of_not_commute hH hK ha hb hab

theorem conj_mem_of_mem_closure {w : G} (hw : w ∈ Subgroup.closure K) {c : G} (hc : c ∈ K) :
    w * c * w⁻¹ ∈ K := by
  have key : ∀ w ∈ Subgroup.closure K,
      (∀ c ∈ K, w * c * w⁻¹ ∈ K) ∧ (∀ c ∈ K, w⁻¹ * c * w ∈ K) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      have hx' : x⁻¹ = x := hH.inv_eq (hK.subset hx)
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩ <;> rw [hx'] <;> exact hK.conj x hx c hc
    | one => simp
    | mul x y _ _ hx hy =>
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · have e : x * y * c * (x * y)⁻¹ = x * (y * c * y⁻¹) * x⁻¹ := by group
        rw [e]
        exact hx.1 _ (hy.1 c hc)
      · have e : (x * y)⁻¹ * c * (x * y) = y⁻¹ * (x⁻¹ * c * x) * y := by group
        rw [e]
        exact hy.2 _ (hx.2 c hc)
    | inv x _ hx =>
      simp only [inv_inv]
      exact ⟨hx.2, hx.1⟩
  exact (key w hw).1 c hc

theorem pair_closure
    [Finite G] :
    Pair (Subgroup.closure K) (Subtype.val ⁻¹' K : Set (Subgroup.closure K)) := by
  obtain ⟨k₀, hk₀⟩ := hK.nonempty
  refine ⟨inferInstance, ⟨⟨k₀, Subgroup.subset_closure hk₀⟩, ?_⟩, ?_, ?_,
    Subgroup.closure_closure_coe_preimage⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨w, hw, e⟩ := conjIn hH hK hk₀ hx
      exact isConj_iff.2 ⟨⟨w, hw⟩, Subtype.ext e⟩
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.1 hx
      have := conj_mem_of_mem_closure hH hK c.2 hk₀
      show (x : G) ∈ K
      rw [← hc]
      exact this
  · intro e he
    rw [← Subgroup.orderOf_coe]
    exact hH.inv _ (hK.subset he)
  · intro e he f hf
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact hH.prod _ (hK.subset he) _ (hK.subset hf)

end IsStarClosed

section Subgroup

variable {S : Subgroup G}

@[expose] def starEquiv (hK : IsStarClosed D K) (hKS : K ⊆ S) {k : S} (hk : (k : G) ∈ K) :
    LocalClass (Subtype.val ⁻¹' K : Set S) k ≃ LocalClass D (k : G) where
  toFun f := ⟨((f : S) : G), hK.subset f.2.1, fun h => f.2.2.1 (Subtype.ext h),
    congrArg Subtype.val f.2.2.2⟩
  invFun c := ⟨⟨(c : G), hKS (hK.nbr (k : G) hk c c.2.1 c.2.2.2)⟩,
    hK.nbr (k : G) hk c c.2.1 c.2.2.2, fun h => c.2.2.1 (congrArg Subtype.val h),
    Subtype.ext c.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def restrictPoints {P : Type} {M : LocalModel P} (hK : IsStarClosed D K)
    (hKS : K ⊆ S) {k : S} (hk : (k : G) ∈ K) (L : LocalPoints M D (k : G)) :
    LocalPoints M (Subtype.val ⁻¹' K : Set S) k where
  χ := (starEquiv hK hKS hk).trans L.χ
  comm f g := by
    have h := L.comm (starEquiv hK hKS hk f) (starEquiv hK hKS hk g)
    exact Iff.trans ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩ h
  tau f g h := L.tau (starEquiv hK hKS hk f) (starEquiv hK hKS hk g)
    (starEquiv hK hKS hk ⟨_, h⟩).2

theorem HasZ.subgroup (hZ : HasZ D) (hK : IsStarClosed D K) (hKS : K ⊆ S) :
    HasZ (Subtype.val ⁻¹' K : Set S) := by
  intro d hd g hg
  have hdK : (d : G) ∈ K := hd
  have key : ∀ f ∈ insert (d : G) (LocalClass D (d : G)), (g : G) * f = f * g := by
    rintro f (rfl | hf)
    · exact congrArg Subtype.val (hg d (Set.mem_insert _ _))
    · have hfK : f ∈ K := hK.nbr d hdK f hf.1 hf.2.2
      have := hg ⟨f, hKS hfK⟩ (Set.mem_insert_of_mem _
        ⟨hfK, fun h => hf.2.1 (congrArg Subtype.val h), Subtype.ext hf.2.2⟩)
      exact congrArg Subtype.val this
  rcases hZ _ (hK.subset hdK) g key with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

end Subgroup

theorem HasZ.eq_one_of_forall_commute (hZ : HasZ D) (hne : D.Nonempty)
    (hstar : ∀ d ∈ D, ∃ f, f ∈ LocalClass D d) {z : G} (hz : ∀ x ∈ D, z * x = x * z) : z = 1 := by
  have hz' : ∀ d ∈ D, ∀ x ∈ insert d (LocalClass D d), z * x = x * z := by
    rintro d hd x (rfl | hx)
    · exact hz _ hd
    · exact hz x hx.1
  obtain ⟨d, hd⟩ := hne
  obtain ⟨f, hf⟩ := hstar d hd
  rcases hZ d hd z (hz' d hd) with h | h
  · exact h
  · rcases hZ f hf.1 z (hz' f hf.1) with h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') hf.2.1.symm

theorem HasZ.center_eq_bot (hZ : HasZ D) (hne : D.Nonempty)
    (hstar : ∀ d ∈ D, ∃ f, f ∈ LocalClass D d) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact hZ.eq_one_of_forall_commute hne hstar fun x _ => (Subgroup.mem_center_iff.1 hz x).symm

end Rec23

end CFSG.Fischer
