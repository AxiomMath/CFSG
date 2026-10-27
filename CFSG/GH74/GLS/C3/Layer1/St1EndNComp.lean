module

public import CFSG.GH74.GLS.C3.Layer1.St1Iv251

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN

open Subgroup

namespace CompAux

section Elementary

variable {X : Type} [Group X]

theorem ne_one_of_orderOf_two {g : X} (hg : orderOf g = 2) : g ≠ 1 := by
  rintro rfl
  simp at hg

theorem mem_map_conj_iff {K : Subgroup X} (g y : X) :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    simpa [MulAut.conj_apply, e] using hk
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    group

theorem mul_comm_of_commutator_eq_bot {A B : Subgroup X} (h : ⁅A, B⁆ = ⊥) {a b : X}
    (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm

theorem mul_comm_of_isComponent_of_ne [Finite X] {A B : Subgroup X} (hA : CFSG.IsComponent A)
    (hB : CFSG.IsComponent B) (hne : A ≠ B) {a b : X} (ha : a ∈ A) (hb : b ∈ B) :
    a * b = b * a :=
  mul_comm_of_commutator_eq_bot
    ((LocalCores.distinct_components_commute hA hB).resolve_left hne) ha hb

theorem false_of_central_involution_conj {K : Subgroup X}
    (hZ : ∀ z ∈ Subgroup.center ↥K, orderOf (z : X) ≠ 2) (s v : X)
    (hv : v ∈ K.map (MulAut.conj s).toMonoidHom) (hv2 : orderOf v = 2)
    (hc : ∀ y ∈ K.map (MulAut.conj s).toMonoidHom, v * y = y * v) : False := by
  have hw : s⁻¹ * v * s ∈ K := (mem_map_conj_iff s v).mp hv
  refine hZ ⟨s⁻¹ * v * s, hw⟩ ?_ ?_
  · rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hk : s * (k : X) * s⁻¹ ∈ K.map (MulAut.conj s).toMonoidHom := ⟨k, k.2, rfl⟩
    have h := hc _ hk
    show (k : X) * (s⁻¹ * v * s) = (s⁻¹ * v * s) * (k : X)
    calc (k : X) * (s⁻¹ * v * s) = s⁻¹ * ((s * k * s⁻¹) * v) * s := by group
      _ = s⁻¹ * (v * (s * k * s⁻¹)) * s := by rw [h]
      _ = (s⁻¹ * v * s) * k := by group
  · show orderOf (s⁻¹ * v * s) = 2
    have := (MulAut.conj s⁻¹).orderOf_eq v
    simpa [MulAut.conj_apply, hv2] using this

theorem exists_involution_ne_of_commuting {K K' K'' : Subgroup X} {x v₀ : X}
    (hx2 : orderOf x = 2) (hv₀K' : v₀ ∈ K') (hv₀2 : orderOf v₀ = 2)
    (hK'' : ∀ y ∈ K', x * y * x⁻¹ ∈ K'')
    (hcomm : ∀ a ∈ K', ∀ b ∈ K'', a * b = b * a)
    (hKx : ∀ k ∈ K, x * k = k * x) (hKv : ∀ k ∈ K, v₀ * k = k * v₀)
    (hnc : ¬ ∀ y ∈ K', v₀ * y = y * v₀) :
    ∃ u : X, orderOf u = 2 ∧ (∀ k ∈ K, u * k = k * u) ∧ u * x = x * u ∧ u ≠ x := by
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : X, v₁ = x * v₀ * x⁻¹ := ⟨_, rfl⟩
  have hv₁K'' : v₁ ∈ K'' := hv₁ ▸ hK'' v₀ hv₀K'
  have hc01 : v₀ * v₁ = v₁ * v₀ := hcomm v₀ hv₀K' v₁ hv₁K''
  have hxx : x * x = 1 := by
    have : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
    rwa [pow_two] at this
  have hxix : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hxx, inv_one]
  have hv₀sq : v₀ * v₀ = 1 := by
    have : v₀ ^ 2 = 1 := by rw [← hv₀2]; exact pow_orderOf_eq_one v₀
    rwa [pow_two] at this
  have hv₁sq : v₁ * v₁ = 1 := by
    calc v₁ * v₁ = x * (v₀ * v₀) * x⁻¹ := by rw [hv₁]; group
      _ = 1 := by rw [hv₀sq]; group
  have hv₁v₀ : x * v₁ * x⁻¹ = v₀ := by
    calc x * v₁ * x⁻¹ = (x * x) * v₀ * (x⁻¹ * x⁻¹) := by rw [hv₁]; group
      _ = v₀ := by rw [hxx, hxix]; group
  have hne : v₀ ≠ v₁ := fun h =>
    hnc fun y hy => (hcomm y hy v₀ (by rw [h]; exact hv₁K'')).symm
  have hu1 : v₀ * v₁ ≠ 1 := by
    intro h
    apply hne
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hv₀sq]
  have hu2 : orderOf (v₀ * v₁) = 2 := by
    refine orderOf_eq_prime ?_ hu1
    rw [pow_two]
    calc (v₀ * v₁) * (v₀ * v₁) = v₀ * (v₁ * v₀) * v₁ := by group
      _ = v₀ * (v₀ * v₁) * v₁ := by rw [← hc01]
      _ = (v₀ * v₀) * (v₁ * v₁) := by group
      _ = 1 := by rw [hv₀sq, hv₁sq, mul_one]
  have hux : v₀ * v₁ ≠ x := by
    intro h
    apply hne
    have hxv₀ : x * v₀ = v₀ * x := by
      calc x * v₀ = (v₀ * v₁) * v₀ := by rw [h]
        _ = v₀ * (v₁ * v₀) := by rw [mul_assoc]
        _ = v₀ * (v₀ * v₁) := by rw [hc01]
        _ = v₀ * x := by rw [h]
    rw [hv₁]
    calc v₀ = (v₀ * x) * x⁻¹ := by group
      _ = (x * v₀) * x⁻¹ := by rw [hxv₀]
  have huK : ∀ k ∈ K, (v₀ * v₁) * k = k * (v₀ * v₁) := by
    intro k hk
    have hxk : Commute x k := hKx k hk
    have hvk : Commute v₀ k := hKv k hk
    have hv₁k : Commute v₁ k := by
      rw [hv₁]
      exact (hxk.mul_left hvk).mul_left hxk.inv_left
    exact hvk.mul_left hv₁k
  have hxu : (v₀ * v₁) * x = x * (v₀ * v₁) := by
    have h1 : x * (v₀ * v₁) * x⁻¹ = v₀ * v₁ := by
      calc x * (v₀ * v₁) * x⁻¹ = (x * v₀ * x⁻¹) * (x * v₁ * x⁻¹) := by group
        _ = v₁ * v₀ := by rw [← hv₁, hv₁v₀]
        _ = v₀ * v₁ := hc01.symm
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  exact ⟨v₀ * v₁, hu2, huK, hxu, hux⟩

end Elementary

section TwoGroups

variable {X : Type} [Group X] [Finite X]

theorem commutes_of_mem_normalizer {P K : Subgroup X} {x : X} (hP : IsPGroup 2 ↥P) (hxP : x ∈ P)
    (hx2 : orderOf x = 2) (hKx : ∀ k ∈ K, x * k = k * x)
    (hh : ∀ u : X, orderOf u = 2 → (∀ k ∈ K, u * k = k * u) → u * x = x * u → u = x)
    {s : X} (hsP : s ∈ P) (hsK : s ∈ normalizer (K : Set X)) : x * s = s * x := by
  have hxcK : x ∈ centralizer (K : Set X) := mem_centralizer_iff.mpr fun k hk => (hKx k hk).symm
  have hxN : x ∈ P ⊓ normalizer (K : Set X) :=
    ⟨hxP, Subgroup.centralizer_le_normalizer (K : Set X) hxcK⟩
  have hxR : x ∈ (P ⊓ normalizer (K : Set X)) ⊓ centralizer (K : Set X) := ⟨hxN, hxcK⟩
  have hR0 : (P ⊓ normalizer (K : Set X)) ⊓ centralizer (K : Set X) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hxR
    exact ne_one_of_orderOf_two hx2 hxR
  have hNR : P ⊓ normalizer (K : Set X) ≤
      normalizer (((P ⊓ normalizer (K : Set X)) ⊓ centralizer (K : Set X) : Subgroup X) : Set X) :=
    fun n hn => TwoThin.mem_normalizer_inf (Subgroup.le_normalizer hn)
      (Iv251.mem_normalizer_centralizer hn.2)
  obtain ⟨z, hzR, hz2, hzc⟩ :=
    Iv251.exists_central_involution (hP.to_inf_left) inf_le_left hNR hR0
  have hzx : z = x :=
    hh z hz2 (fun k hk => (mem_centralizer_iff.mp hzR.2 k hk).symm) (hzc x hxN)
  have := hzc s ⟨hsP, hsK⟩
  rwa [hzx] at this

theorem false_of_normalizes {K' : Subgroup X} {x : X} (hx2 : orderOf x = 2)
    (hxK' : x ∈ normalizer (K' : Set X)) (hrk : 2 ≤ CFSG.pRank 2 ↥K')
    (hh : ∀ u ∈ K', orderOf u = 2 → u * x = x * u → u = x) : False := by
  have hV : IsPGroup 2 ↥(zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2]; norm_num)
  obtain ⟨R, hRS, -, hVR⟩ := Iv251.exists_invariant_sylow (C := K') (Q := ⊥) (V := zpowers x)
    bot_le (IsPGroup.of_card (n := 0) (by simp)) hV (zpowers_le.mpr hxK')
    (fun p _ => by rw [Subgroup.normalizer_eq_top]; trivial)
  have hrkR : 2 ≤ CFSG.pRank 2 ↥R := by
    rw [GLS.pRank_eq_of_isSylowOf hRS]
    exact hrk
  obtain ⟨a, haR, b, hbR, ha2, hb2, hab, -⟩ := U1a.exists_commuting_involutions hrkR
  have hT : IsPGroup 2 ↥(R ⊔ zpowers x) := hRS.isPGroup.to_sup_of_normal_left' hV hVR
  have hR0 : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at haR
    exact ne_one_of_orderOf_two ha2 haR
  obtain ⟨z, hzR, hz2, hzc⟩ := Iv251.exists_central_involution hT le_sup_left
    (sup_le Subgroup.le_normalizer hVR) hR0
  have hzx : z = x :=
    hh z (hRS.le hzR) hz2 (hzc x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  have hxc : ∀ r ∈ R, x * r = r * x := fun r hr => by
    have := hzc r (Subgroup.mem_sup_left hr)
    rwa [hzx] at this
  have hax : a = x := hh a (hRS.le haR) ha2 (hxc a haR).symm
  have hbx : b = x := hh b (hRS.le hbR) hb2 (hxc b hbR).symm
  exact hab (hax.trans hbx.symm)

end TwoGroups

end CompAux

theorem central_of_subnormal_component
    {X : Type} [Group X] [Finite X] {P K : Subgroup X} {x : X}
    (hP : IsPGroup 2 ↥P) (hxP : x ∈ P) (hx2 : orderOf x = 2)
    (hKq : CFSG.IsQuasisimple ↥K) (hKs : K.IsSubnormal) (hKx : ∀ k ∈ K, x * k = k * x)
    (hrk : 2 ≤ CFSG.pRank 2 ↥K) (hZ : ∀ z ∈ Subgroup.center ↥K, orderOf (z : X) ≠ 2)
    (hh : ∀ u : X, orderOf u = 2 → (∀ k ∈ K, u * k = k * u) → u * x = x * u → u = x) :
    ∀ s ∈ P, x * s = s * x := by
  intro s hsP
  by_contra hxs
  have hsK : s ∉ normalizer (K : Set X) := fun hs =>
    hxs (CompAux.commutes_of_mem_normalizer hP hxP hx2 hKx hh hsP hs)
  have hK : CFSG.IsComponent K := ⟨hKq, hKs⟩
  set K' : Subgroup X := K.map (MulAut.conj s).toMonoidHom with hK'def
  have hK'c : CFSG.IsComponent K' := LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hK
  have hKne : K ≠ K' := fun h => hsK (mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a :=
    fun a ha b hb => CompAux.mul_comm_of_isComponent_of_ne hK hK'c hKne ha hb
  by_cases hxK' : x ∈ normalizer (K' : Set X)
  · refine CompAux.false_of_normalizes hx2 hxK' ?_ fun u hu hu2 hux =>
      hh u hu2 (fun k hk => (hcomm k hk u hu).symm) hux
    exact le_of_le_of_eq hrk
      (Stage1.Thm2.Recip.pRank_eq_of_mulEquiv' (MulEquiv.subgroupMap (MulAut.conj s) K))
  · set K'' : Subgroup X := K'.map (MulAut.conj x).toMonoidHom with hK''def
    have hK''c : CFSG.IsComponent K'' := LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK'c
    have hK'ne : K' ≠ K'' := fun h => hxK' (mem_normalizer_iff_map_conj_eq.mpr h.symm)
    have hcomm' : ∀ a ∈ K', ∀ b ∈ K'', a * b = b * a :=
      fun a ha b hb => CompAux.mul_comm_of_isComponent_of_ne hK'c hK''c hK'ne ha hb
    have hK''mem : ∀ y ∈ K', x * y * x⁻¹ ∈ K'' := fun y hy => ⟨y, hy, rfl⟩
    obtain ⟨a₀, ha₀K, -, -, ha₀2, -⟩ := U1a.exists_commuting_involutions hrk
    have hv₀K' : s * a₀ * s⁻¹ ∈ K' := ⟨a₀, ha₀K, rfl⟩
    have hv₀2 : orderOf (s * a₀ * s⁻¹) = 2 := by
      have := (MulAut.conj s).orderOf_eq a₀
      rwa [ha₀2] at this
    obtain ⟨u, hu2, huK, hux, hune⟩ := CompAux.exists_involution_ne_of_commuting hx2 hv₀K' hv₀2
      hK''mem hcomm' hKx (fun k hk => (hcomm k hk _ hv₀K').symm)
      (fun hc => CompAux.false_of_central_involution_conj hZ s _ hv₀K' hv₀2 hc)
    exact hune (hh u hu2 huK hux)

end CFSG.GH74.GLS.C3.Layer1.EndN
