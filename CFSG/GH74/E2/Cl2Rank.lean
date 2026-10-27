module

public import CFSG.GH74.E2.Cl2Defs
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

variable {Q : Type*} [Group Q]

private theorem coatom_normal [Finite Q] (hQ : IsPGroup 2 Q) {K : Subgroup Q}
    (hK : IsCoatom K) : K.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Q := hQ.isNilpotent
  exact (Group.normalizerCondition_of_isNilpotent (G := Q)).normal_of_coatom K hK

private theorem mul_self_mem_coatom [Finite Q] (hQ : IsPGroup 2 Q) {K : Subgroup Q}
    (hK : IsCoatom K) (g : Q) : g * g ∈ K := by
  have hKn : K.Normal := coatom_normal hQ hK
  by_cases hg : g ∈ K
  · exact K.mul_mem hg hg
  · have hle : K ≤ K ⊔ Subgroup.zpowers (g * g) := le_sup_left
    rcases hK.le_iff.mp hle with hL | hL
    · exfalso
      have hgL : g ∈ K ⊔ Subgroup.zpowers (g * g) := by rw [hL]; trivial
      obtain ⟨k, hk, z, hz, hkz⟩ := Subgroup.mem_sup_of_normal_left.mp hgL
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      obtain ⟨e, he⟩ := hQ g
      have h2 : (g * g) ^ m = g ^ (2 * m) := by
        rw [← sq, ← zpow_natCast, ← zpow_mul]; norm_num
      rw [h2] at hkz
      have hkg : k = g ^ (1 - 2 * m) := by
        have h3 : k = g * (g ^ (2 * m))⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq]; exact hkz
        rw [h3, ← zpow_neg, ← zpow_one_add]
        congr 1
      have hcop : IsCoprime (1 - 2 * m : ℤ) ((2 : ℤ) ^ e) :=
        IsCoprime.pow_right ⟨1, m, by ring⟩
      obtain ⟨u, v, huv⟩ := hcop
      have h3 : g ^ ((2 : ℤ) ^ e) = 1 := by
        have : ((2 : ℤ) ^ e) = ((2 ^ e : ℕ) : ℤ) := by push_cast; rfl
        rw [this, zpow_natCast]
        exact he
      have hg2 : g = k ^ u := by
        have h4 : g = g ^ (u * (1 - 2 * m) + v * (2 ^ e : ℤ)) := by rw [huv]; simp
        have h5 : g ^ (v * (2 ^ e : ℤ)) = 1 := by
          rw [mul_comm, zpow_mul, h3, one_zpow]
        rw [h4, zpow_add, h5, mul_one, hkg, ← zpow_mul, mul_comm (1 - 2 * m) u]
      exact hg (by rw [hg2]; exact K.zpow_mem hk u)
    · have h1 : g * g ∈ K ⊔ Subgroup.zpowers (g * g) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rw [hL] at h1
      exact h1

theorem mul_self_mem_frattini [Finite Q] (hQ : IsPGroup 2 Q) (g : Q) :
    g * g ∈ frattini Q := by
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro K hK
  exact mul_self_mem_coatom hQ hK g

private theorem comm_mem_coatom [Finite Q] (hQ : IsPGroup 2 Q) {K : Subgroup Q}
    (hK : IsCoatom K) (x y : Q) : ⁅x, y⁆ ∈ K := by
  have hKn : K.Normal := coatom_normal hQ hK
  by_cases hx : x ∈ K
  · have h1 : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [h1]
    exact K.mul_mem hx (hKn.conj_mem _ (K.inv_mem hx) y)
  · have hle : K ≤ K ⊔ Subgroup.zpowers x := le_sup_left
    rcases hK.le_iff.mp hle with hL | hL
    · have hyL : y ∈ K ⊔ Subgroup.zpowers x := by rw [hL]; trivial
      obtain ⟨k, hk, z, hz, hkz⟩ := Subgroup.mem_sup_of_normal_left.mp hyL
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hz' : x ^ j * x⁻¹ = x⁻¹ * x ^ j :=
        (((Commute.refl x).zpow_right j).inv_left).eq.symm
      have h2 : ⁅x, y⁆ = (x * k * x⁻¹) * k⁻¹ := by
        rw [← hkz]
        calc ⁅x, k * x ^ j⁆ = x * k * (x ^ j * x⁻¹) * (x ^ j)⁻¹ * k⁻¹ := by
              simp [commutatorElement_def, mul_assoc]
          _ = x * k * (x⁻¹ * x ^ j) * (x ^ j)⁻¹ * k⁻¹ := by rw [hz']
          _ = (x * k * x⁻¹) * k⁻¹ := by simp [mul_assoc]
      rw [h2]
      exact K.mul_mem (hKn.conj_mem _ hk x) (K.inv_mem hk)
    · exact absurd (hL ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))) hx

theorem dsub_le_frattini [Finite Q] (hQ : IsPGroup 2 Q) :
    ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ frattini Q := by
  unfold frattini Order.radical
  simp only [le_iInf_iff]
  intro K hK
  rw [Subgroup.commutator_le]
  intro x _ y _
  exact comm_mem_coatom hQ hK x y

private theorem zpowers_exponent_two {h : Q} (h2 : h * h = 1) {z : Q}
    (hz : z ∈ Subgroup.zpowers h) : z = 1 ∨ z = h := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hsq : h ^ 2 = 1 := by rw [sq]; exact h2
  have hmod : h ^ j = h ^ (j % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv j 2, zpow_add, zpow_mul]
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hsq, one_zpow, mul_one]
  rw [hmod]
  rcases Int.emod_two_eq_zero_or_one j with h0 | h1
  · left; rw [h0]; simp
  · right; rw [h1]; simp

theorem frattini_eq_bot_of_exponent_two [Finite Q] (hc : ∀ g h : Q, g * h = h * g)
    (h2 : ∀ g : Q, g * g = 1) : frattini Q = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  by_contra hg1
  have hg1' : g ≠ 1 := fun h => hg1 (by rw [h]; exact Subgroup.one_mem _)
  let S : Set (Subgroup Q) := {K | g ∉ K}
  have hS : S.Nonempty := ⟨⊥, fun h => hg1' (by simpa using h)⟩
  obtain ⟨K, hKS, hKmax⟩ := (wellFounded_gt (α := Subgroup Q)).has_min S hS
  have hgK : g ∉ K := hKS
  have hKn : K.Normal := ⟨fun n hn x => by rwa [hc x n, mul_assoc, mul_inv_cancel, mul_one]⟩
  have htop : K ⊔ Subgroup.zpowers g = ⊤ := by
    rw [eq_top_iff]
    intro h _
    by_cases hh : h ∈ K
    · exact Subgroup.mem_sup_left hh
    · have hlt : K < K ⊔ Subgroup.zpowers h := by
        refine lt_of_le_of_ne le_sup_left fun heq => hh ?_
        rw [heq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers h)
      have hgin : g ∈ K ⊔ Subgroup.zpowers h := by
        by_contra hnot
        exact hKmax _ hnot hlt
      obtain ⟨k, hk, z, hz, hkz⟩ := Subgroup.mem_sup_of_normal_left.mp hgin
      rcases zpowers_exponent_two (h2 h) hz with hz1 | hzh
      · rw [hz1, mul_one] at hkz
        exact absurd (hkz ▸ hk) hgK
      · rw [hzh] at hkz
        have hh' : h = k⁻¹ * g := by rw [← hkz]; group
        rw [hh']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.inv_mem hk))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hle : K ⊔ Subgroup.zpowers g ≤ K ⊔ frattini Q :=
    sup_le_sup_left ((Subgroup.zpowers_le).mpr hg) K
  have : K ⊔ frattini Q = ⊤ := by rw [eq_top_iff, ← htop]; exact hle
  exact hgK (by rw [frattini_nongenerating this]; trivial)

private theorem card_closure_le_of_sq_one {G : Type*} [Group G] [Finite G]
    (h2 : ∀ x : G, x * x = 1) (t : Finset G) :
    Nat.card (Subgroup.closure (t : Set G)) ≤ 2 ^ t.card := by
  classical
  have hi : ∀ z : G, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (h2 z)
  have hc : ∀ x y : G, x * y = y * x := by
    intro x y
    calc x * y = (x * y)⁻¹ := (hi (x * y)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hi x, hi y]
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    have hcl : Subgroup.closure ((insert a t : Finset G) : Set G) =
        Subgroup.closure (t : Set G) ⊔ Subgroup.zpowers a := by
      rw [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, sup_comm,
        Subgroup.zpowers_eq_closure]
    rw [hcl, Finset.card_insert_of_notMem hat, pow_succ]
    set K := Subgroup.closure (t : Set G) with hK
    have hKn : K.Normal := ⟨fun n hn x => by rwa [hc x n, mul_assoc, mul_inv_cancel, mul_one]⟩
    let f : K × Bool → (K ⊔ Subgroup.zpowers a : Subgroup G) := fun p =>
      ⟨p.1 * (if p.2 then a else 1), Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
        (by split_ifs
            · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
            · exact Subgroup.one_mem _)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk, z, hz, hkz⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      rcases zpowers_exponent_two (h2 a) hz with rfl | rfl
      · exact ⟨(⟨k, hk⟩, false), Subtype.ext (by simpa [f] using hkz)⟩
      · exact ⟨(⟨k, hk⟩, true), Subtype.ext (by simpa [f] using hkz)⟩
    calc Nat.card (K ⊔ Subgroup.zpowers a : Subgroup G)
        ≤ Nat.card (K × Bool) := Nat.card_le_card_of_surjective f hf
      _ = Nat.card K * 2 := by
          rw [Nat.card_prod]; simp
      _ ≤ 2 ^ t.card * 2 := Nat.mul_le_mul_right 2 ih

theorem relIndex_le_two_pow_card [Finite Q] (s : Finset Q) {R : Subgroup Q}
    (hnorm : ∀ h ∈ Subgroup.closure (s : Set Q), ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hsq : ∀ h ∈ Subgroup.closure (s : Set Q), h * h ∈ R) :
    R.relIndex (Subgroup.closure (s : Set Q)) ≤ 2 ^ s.card := by
  classical
  set H := Subgroup.closure (s : Set Q) with hH
  let N : Subgroup H := R.subgroupOf H
  have hNn : N.Normal := ⟨fun n hn h => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm h.1 h.2 n.1 hn⟩
  have h2 : ∀ x : H ⧸ N, x * x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hsq g.1 g.2
  let f : s → H ⧸ N := fun t => QuotientGroup.mk ⟨t, Subgroup.subset_closure t.2⟩
  let t' : Finset (H ⧸ N) := s.attach.image f
  have hgen : Subgroup.closure (t' : Set (H ⧸ N)) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    induction g using QuotientGroup.induction_on with
    | H h =>
      obtain ⟨x, hx⟩ := h
      refine Subgroup.closure_induction
        (p := fun x hx => (QuotientGroup.mk ⟨x, hx⟩ : H ⧸ N) ∈ Subgroup.closure (t' : Set (H ⧸ N)))
        ?_ ?_ ?_ ?_ hx
      · intro y hy
        apply Subgroup.subset_closure
        simp only [t', Finset.coe_image, Finset.mem_coe, Set.mem_image, Finset.mem_attach, true_and]
        exact ⟨⟨y, hy⟩, rfl⟩
      · exact (QuotientGroup.mk_one (N := N) ▸ Subgroup.one_mem _)
      · intro y z hy hz ihy ihz
        have : (QuotientGroup.mk (⟨y * z, Subgroup.mul_mem _ hy hz⟩ : H) : H ⧸ N) =
            QuotientGroup.mk ⟨y, hy⟩ * QuotientGroup.mk ⟨z, hz⟩ := rfl
        rw [this]
        exact Subgroup.mul_mem _ ihy ihz
      · intro y hy ihy
        have : (QuotientGroup.mk (⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : H) : H ⧸ N) =
            (QuotientGroup.mk ⟨y, hy⟩)⁻¹ := rfl
        rw [this]
        exact Subgroup.inv_mem _ ihy
  have hcard := card_closure_le_of_sq_one h2 t'
  rw [hgen, Subgroup.card_top] at hcard
  have hrel : R.relIndex H = Nat.card (H ⧸ N) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
  rw [hrel]
  calc Nat.card (H ⧸ N) ≤ 2 ^ t'.card := hcard
    _ ≤ 2 ^ s.card := Nat.pow_le_pow_right (by norm_num)
        (Finset.card_image_le.trans (by simp))

theorem FourGen.subgroup (hQ : FourGen Q) (H : Subgroup Q) : FourGen H := by
  classical
  intro K
  obtain ⟨s, hs, hsK⟩ := hQ (K.map H.subtype)
  have hsub : (s : Set Q) ⊆ H.subtype '' (K : Set H) := by
    intro x hx
    have hx' : x ∈ K.map H.subtype := hsK ▸ Subgroup.subset_closure hx
    simpa using hx'
  obtain ⟨t, -, hts⟩ := Finset.subset_set_image_iff.mp hsub
  refine ⟨t, ?_, ?_⟩
  · rw [← Finset.card_image_of_injective t H.subtype_injective, hts]
    exact hs
  · apply Subgroup.map_injective H.subtype_injective
    rw [MonoidHom.map_closure, ← Finset.coe_image, hts, hsK]

theorem FourGen.quotient (hQ : FourGen Q) (N : Subgroup Q) [N.Normal] : FourGen (Q ⧸ N) := by
  classical
  intro K
  obtain ⟨s, hs, hsK⟩ := hQ (K.comap (QuotientGroup.mk' N))
  refine ⟨s.image (QuotientGroup.mk' N), Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsK]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K

theorem FourGen.relIndex_le [Finite Q] (hQ : FourGen Q) {H R : Subgroup Q}
    (hnorm : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hsq : ∀ h ∈ H, h * h ∈ R) :
    R.relIndex H ≤ 16 := by
  obtain ⟨s, hs, rfl⟩ := hQ H
  exact (relIndex_le_two_pow_card s hnorm hsq).trans
    (le_trans (Nat.pow_le_pow_right (by norm_num) hs) (by norm_num))

theorem relIndex_sup_of_commute [Finite Q] {U V RU RV : Subgroup Q}
    (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hRU : RU ≤ U) (hRV : RV ≤ V)
    (hnU : ∀ u ∈ U, ∀ r ∈ RU, u * r * u⁻¹ ∈ RU) (hnV : ∀ v ∈ V, ∀ r ∈ RV, v * r * v⁻¹ ∈ RV)
    (hint : U ⊓ V ≤ RU ⊓ RV) :
    (RU ⊔ RV).relIndex (U ⊔ V) = RU.relIndex U * RV.relIndex V := by
  classical
  let RU' : Subgroup U := RU.subgroupOf U
  let RV' : Subgroup V := RV.subgroupOf V
  have hRUn : RU'.Normal := ⟨fun n hn u => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnU u.1 u.2 n.1 hn⟩
  have hRVn : RV'.Normal := ⟨fun n hn v => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnV v.1 v.2 n.1 hn⟩
  have hcommute : ∀ (u : U) (v : V), Commute (U.subtype u) (V.subtype v) :=
    fun u v => hcomm u.1 u.2 v.1 v.2
  let ψ : U × V →* Q := MonoidHom.noncommCoprod U.subtype V.subtype hcommute
  have hψapp : ∀ y : U × V, ψ y = y.1.1 * y.2.1 := fun y => rfl
  have hrange : ψ.range = U ⊔ V := by
    have := MonoidHom.noncommCoprod_range U.subtype V.subtype hcommute
    rw [Subgroup.range_subtype, Subgroup.range_subtype] at this
    exact this
  let ψ' : U × V →* ↥(U ⊔ V) := ψ.codRestrict (U ⊔ V) (fun x => by
    rw [← hrange]; exact ⟨x, rfl⟩)
  have hψ'surj : Function.Surjective ψ' := by
    intro x
    have hx : (x : Q) ∈ ψ.range := by rw [hrange]; exact x.2
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  let Φ : U × V →* (U ⧸ RU') × (V ⧸ RV') :=
    (QuotientGroup.mk' RU').prodMap (QuotientGroup.mk' RV')
  have hker : ψ'.ker ≤ Φ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have h1 : y.1.1 * y.2.1 = 1 := by
      have := congrArg Subtype.val hy
      rw [← hψapp]
      exact this
    have h2 : y.1.1 ∈ RU ⊓ RV := by
      apply hint
      refine ⟨y.1.2, ?_⟩
      have : y.1.1 = (y.2.1)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact V.inv_mem y.2.2
    have h3 : y.2.1 ∈ RU ⊓ RV := by
      have : y.2.1 = (y.1.1)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact (RU ⊓ RV).inv_mem h2
    refine Prod.ext ?_ ?_
    · exact (QuotientGroup.eq_one_iff y.1).2 (by rw [Subgroup.mem_subgroupOf]; exact h2.1)
    · exact (QuotientGroup.eq_one_iff y.2).2 (by rw [Subgroup.mem_subgroupOf]; exact h3.2)
  let θ : ↥(U ⊔ V) →* (U ⧸ RU') × (V ⧸ RV') :=
    (ψ'.liftOfRightInverse (Function.surjInv hψ'surj) (Function.rightInverse_surjInv hψ'surj))
      ⟨Φ, hker⟩
  have hθ : ∀ y, θ (ψ' y) = Φ y := fun y =>
    ψ'.liftOfRightInverse_comp_apply (Function.surjInv hψ'surj)
      (Function.rightInverse_surjInv hψ'surj) ⟨Φ, hker⟩ y
  have hθsurj : Function.Surjective θ := by
    rintro ⟨a, b⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective RU' a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective RV' b
    exact ⟨ψ' (u, v), by rw [hθ]; rfl⟩
  have hθker : θ.ker = (RU ⊔ RV).subgroupOf (U ⊔ V) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hψ'surj x
      rw [hθ] at hx
      have h1 : (QuotientGroup.mk' RU') y.1 = 1 := congrArg Prod.fst hx
      have h2 : (QuotientGroup.mk' RV') y.2 = 1 := congrArg Prod.snd hx
      have h1' : y.1.1 ∈ RU :=
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y.1).mp h1)
      have h2' : y.2.1 ∈ RV :=
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y.2).mp h2)
      exact Subgroup.mul_mem_sup h1' h2'
    · intro hx
      have hcommute' : ∀ (r : RU) (r' : RV), Commute (RU.subtype r) (RV.subtype r') :=
        fun r r' => hcomm r.1 (hRU r.2) r'.1 (hRV r'.2)
      have hr := MonoidHom.noncommCoprod_range RU.subtype RV.subtype hcommute'
      rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
      have hx' : (x : Q) ∈ (MonoidHom.noncommCoprod RU.subtype RV.subtype hcommute').range := by
        rw [hr]; exact hx
      obtain ⟨p, hp⟩ := hx'
      have hxy : x = ψ' (⟨p.1.1, hRU p.1.2⟩, ⟨p.2.1, hRV p.2.2⟩) := by
        apply Subtype.ext
        exact hp.symm
      rw [hxy, hθ]
      refine Prod.ext ?_ ?_
      · exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.mpr p.1.2)
      · exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.mpr p.2.2)
  have hidx : ((RU ⊔ RV).subgroupOf (U ⊔ V)).index = Nat.card ((U ⧸ RU') × (V ⧸ RV')) := by
    rw [← hθker, Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj).toEquiv
  rw [Subgroup.relIndex, hidx, Nat.card_prod, Subgroup.relIndex, Subgroup.relIndex,
    Subgroup.index_eq_card, Subgroup.index_eq_card]

theorem mem_sup_iff_of_commute {U V : Subgroup Q} (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    {x : Q} : x ∈ U ⊔ V ↔ ∃ u ∈ U, ∃ v ∈ V, u * v = x := by
  constructor
  · intro hx
    have hcommute : ∀ (u : U) (v : V), Commute (U.subtype u) (V.subtype v) :=
      fun u v => hcomm u.1 u.2 v.1 v.2
    have hr := MonoidHom.noncommCoprod_range U.subtype V.subtype hcommute
    rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
    have hx' : x ∈ (MonoidHom.noncommCoprod U.subtype V.subtype hcommute).range := by
      rw [hr]; exact hx
    obtain ⟨p, hp⟩ := hx'
    exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, hp⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact Subgroup.mul_mem_sup hu hv

theorem FourGen.relIndex_mul_le [Finite Q] (hQ : FourGen Q) {U V RU RV : Subgroup Q}
    (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hRU : RU ≤ U) (hRV : RV ≤ V)
    (hnU : ∀ u ∈ U, ∀ r ∈ RU, u * r * u⁻¹ ∈ RU) (hnV : ∀ v ∈ V, ∀ r ∈ RV, v * r * v⁻¹ ∈ RV)
    (hsqU : ∀ u ∈ U, u * u ∈ RU) (hsqV : ∀ v ∈ V, v * v ∈ RV)
    (hint : U ⊓ V ≤ RU ⊓ RV) :
    RU.relIndex U * RV.relIndex V ≤ 16 := by
  rw [← relIndex_sup_of_commute hcomm hRU hRV hnU hnV hint]
  have hcommR : ∀ r ∈ RU, ∀ r' ∈ RV, r * r' = r' * r := fun r hr r' hr' =>
    hcomm r (hRU hr) r' (hRV hr')
  apply hQ.relIndex_le
  · intro h hh r hr
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hh
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := (mem_sup_iff_of_commute hcommR).mp hr
    have hcu : ∀ w ∈ V, u * w = w * u := fun w hw => hcomm u hu w hw
    have e1 : u * v * (r₁ * r₂) * (u * v)⁻¹ = (u * r₁ * u⁻¹) * (v * r₂ * v⁻¹) := by
      have c1 : v * r₁ = r₁ * v := (hcomm r₁ (hRU hr₁) v hv).symm
      have c2 : u * r₂ = r₂ * u := hcomm u hu r₂ (hRV hr₂)
      have c3 : v * u = u * v := (hcomm u hu v hv).symm
      calc u * v * (r₁ * r₂) * (u * v)⁻¹
          = u * (v * r₁) * r₂ * (v⁻¹ * u⁻¹) := by group
        _ = u * (r₁ * v) * r₂ * (v⁻¹ * u⁻¹) := by rw [c1]
        _ = (u * r₁) * (v * r₂) * (v⁻¹ * u⁻¹) := by group
        _ = (u * r₁) * (v * r₂ * v⁻¹) * u⁻¹ := by group
        _ = (u * r₁ * u⁻¹) * (v * r₂ * v⁻¹) := by
            have c4 : u⁻¹ * (v * r₂ * v⁻¹) = (v * r₂ * v⁻¹) * u⁻¹ := by
              have : (v * r₂ * v⁻¹) * u = u * (v * r₂ * v⁻¹) := by
                have h5 : ∀ w ∈ V, w * u = u * w := fun w hw => (hcu w hw).symm
                exact h5 _ (V.mul_mem (V.mul_mem hv (hRV hr₂)) (V.inv_mem hv))
              calc u⁻¹ * (v * r₂ * v⁻¹) = u⁻¹ * ((v * r₂ * v⁻¹) * u) * u⁻¹ := by group
                _ = u⁻¹ * (u * (v * r₂ * v⁻¹)) * u⁻¹ := by rw [this]
                _ = (v * r₂ * v⁻¹) * u⁻¹ := by group
            calc (u * r₁) * (v * r₂ * v⁻¹) * u⁻¹ = u * r₁ * ((v * r₂ * v⁻¹) * u⁻¹) := by group
              _ = u * r₁ * (u⁻¹ * (v * r₂ * v⁻¹)) := by rw [c4]
              _ = (u * r₁ * u⁻¹) * (v * r₂ * v⁻¹) := by group
    rw [e1]
    exact Subgroup.mul_mem_sup (hnU u hu r₁ hr₁) (hnV v hv r₂ hr₂)
  · intro h hh
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hh
    have c3 : v * u = u * v := (hcomm u hu v hv).symm
    have e2 : u * v * (u * v) = (u * u) * (v * v) := by
      calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [c3]
        _ = (u * u) * (v * v) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup (hsqU u hu) (hsqV v hv)

end CFSG.GH74.E2
