module

public import CFSG.ClassicalInvolution.Uniform.U3M11
public import CFSG.ClassicalInvolution.Uniform.UFacade

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Blueprint CFSG.ClassicalInvolution.Q3 Equiv
open scoped Pointwise

section SD16

private theorem m11Sd_central : ∀ p : Fin 8 × Fin 2,
    (m11SdMap p * m11SdX = m11SdX * m11SdMap p ∧ m11SdMap p * m11SdY = m11SdY * m11SdMap p) →
    p = (0, 0) ∨ p = (4, 0) := by
  decide +kernel

private theorem m11SdMap_zero : m11SdMap ((0 : Fin 8), (0 : Fin 2)) = 1 := by
  decide +kernel

private theorem m11SdMap_four : m11SdMap ((4 : Fin 8), (0 : Fin 2)) = m11SdX ^ 4 := by
  decide +kernel

theorem m11SdS_center_le_two : Nat.card (Subgroup.center ↥m11SdS) ≤ 2 := by
  have hxS : (⟨m11SdX, m11SdX_mem⟩ : ↥NativeSporadic.M11) ∈ m11SdS :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hyS : (⟨m11SdY, m11SdY_mem⟩ : ↥NativeSporadic.M11) ∈ m11SdS :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have key : ∀ s : ↥m11SdS, s ∈ Subgroup.center ↥m11SdS →
      (s : ↥NativeSporadic.M11).1 = 1 ∨ (s : ↥NativeSporadic.M11).1 = m11SdX ^ 4 := by
    intro s hs
    obtain ⟨p, hp⟩ := exists_m11SdMap_eq_of_mem s.2
    have hcx := Subgroup.mem_center_iff.mp hs ⟨⟨m11SdX, m11SdX_mem⟩, hxS⟩
    have hcy := Subgroup.mem_center_iff.mp hs ⟨⟨m11SdY, m11SdY_mem⟩, hyS⟩
    have h1 : m11SdMap p * m11SdX = m11SdX * m11SdMap p := by
      rw [hp]
      exact (congrArg (fun a : ↥m11SdS => (a : ↥NativeSporadic.M11).1) hcx).symm
    have h2 : m11SdMap p * m11SdY = m11SdY * m11SdMap p := by
      rw [hp]
      exact (congrArg (fun a : ↥m11SdS => (a : ↥NativeSporadic.M11).1) hcy).symm
    rcases m11Sd_central p ⟨h1, h2⟩ with rfl | rfl
    · exact Or.inl (hp.symm.trans m11SdMap_zero)
    · exact Or.inr (hp.symm.trans m11SdMap_four)
  set A : Set (Perm (Fin 11)) := {1, m11SdX ^ 4} with hA
  let f : ↥(Subgroup.center ↥m11SdS) → ↥A := fun s =>
    ⟨(s.1 : ↥NativeSporadic.M11).1, by
      rcases key s.1 s.2 with h | h
      · exact Or.inl h
      · exact Or.inr h⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h : ((a.1 : ↥m11SdS) : ↥NativeSporadic.M11).1 =
        ((b.1 : ↥m11SdS) : ↥NativeSporadic.M11).1 := congrArg (Subtype.val : ↥A → Perm (Fin 11)) hab
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have hfin : Finite ↥A := Set.toFinite A
  calc Nat.card (Subgroup.center ↥m11SdS) ≤ Nat.card ↥A := Nat.card_le_card_of_injective f hf
    _ = A.ncard := Nat.card_coe_set_eq A
    _ ≤ 2 := by
      calc A.ncard ≤ ({m11SdX ^ 4} : Set (Perm (Fin 11))).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]

end SD16

section Sylow

theorem m11_sylow_card (P : Sylow 2 ↥NativeSporadic.M11) :
    Nat.card (P : Subgroup ↥NativeSporadic.M11) = 16 := by
  rw [Sylow.card_eq_multiplicity P, card_m11_kernel]
  have h : (Nat.factorization 7920) 2 = 4 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    have h1 : (7920 : ℕ) = 2 ^ 4 * 495 := by norm_num
    rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    have h0 : padicValNat 2 495 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    omega
  rw [h]
  norm_num

theorem m11_sylow_center_le_two (P : Sylow 2 ↥NativeSporadic.M11) :
    Nat.card (Subgroup.center ↥(P : Subgroup ↥NativeSporadic.M11)) ≤ 2 := by
  have hS : IsPGroup 2 m11SdS := IsPGroup.of_card (n := 4) (by rw [card_m11SdS]; norm_num)
  have hidx : ¬ 2 ∣ m11SdS.index := by
    have h := Subgroup.card_mul_index m11SdS
    rw [card_m11SdS, card_m11_kernel] at h
    have : m11SdS.index = 495 := by omega
    rw [this]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M11 (hS.toSylow hidx) P
  have hPeq : (P : Subgroup ↥NativeSporadic.M11) = MulAut.conj g • m11SdS := by
    have h := congrArg (fun Q : Sylow 2 ↥NativeSporadic.M11 => (Q : Subgroup ↥NativeSporadic.M11))
      hg
    rw [Sylow.coe_subgroup_smul] at h
    exact h.symm
  let e : ↥m11SdS ≃* ↥(P : Subgroup ↥NativeSporadic.M11) :=
    (Subgroup.equivSMul (MulAut.conj g) m11SdS).trans (MulEquiv.subgroupCongr hPeq.symm)
  calc Nat.card (Subgroup.center ↥(P : Subgroup ↥NativeSporadic.M11))
      = Nat.card (Subgroup.center ↥m11SdS) := (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
    _ ≤ 2 := m11SdS_center_le_two

end Sylow

section Outside

variable {X : Type*} [Group X] [Finite X]

theorem false_of_central_involution_outside
    (hP : ∀ P : Sylow 2 X, Nat.card (P : Subgroup X) = 16)
    (hZ : ∀ P : Sylow 2 X, Nat.card (Subgroup.center ↥(P : Subgroup X)) ≤ 2)
    {R : Subgroup X} (hR2 : IsPGroup 2 R) (hR8 : Nat.card R = 8) {z : X} (hz2 : orderOf z = 2)
    (hzR : z ∉ R) (hc : ∀ r ∈ R, z * r = r * z) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (R : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer (R : Set X) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hc r hr).symm
  have hT2 : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers z) := hR2.to_sup_of_normal_left' hzp hzN
  obtain ⟨P, hTP⟩ := hT2.exists_le_sylow
  have hRP : R ≤ (P : Subgroup X) := le_sup_left.trans hTP
  have hzP : z ∈ (P : Subgroup X) := hTP (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hidx : (R.subgroupOf (P : Subgroup X)).index = 2 := by
    have h := Subgroup.relIndex_mul_card R (P : Subgroup X)
    rw [inf_eq_left.mpr hRP, hR8, hP P] at h
    show R.relIndex (P : Subgroup X) = 2
    omega
  have hdecomp : ∀ g ∈ (P : Subgroup X), g ∈ R ∨ ∃ r ∈ R, g = r * z := by
    intro g hg
    by_cases hgR : g ∈ R
    · exact Or.inl hgR
    · right
      have hg' : (⟨g, hg⟩ : ↥(P : Subgroup X)) ∉ R.subgroupOf (P : Subgroup X) := hgR
      have hz' : (⟨z, hzP⟩ : ↥(P : Subgroup X)) ∉ R.subgroupOf (P : Subgroup X) := hzR
      have hmul : (⟨g, hg⟩ : ↥(P : Subgroup X)) * ⟨z, hzP⟩ ∈ R.subgroupOf (P : Subgroup X) :=
        (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hg' hz')
      refine ⟨g * z, hmul, ?_⟩
      calc g = g * (z * z) := by rw [hzz, mul_one]
        _ = g * z * z := by rw [mul_assoc]
  have hRnt : Nontrivial ↥R := by
    rw [← Finite.one_lt_card_iff_nontrivial, hR8]
    norm_num
  have := hR2.center_nontrivial
  obtain ⟨u₀, hu₀⟩ := exists_ne (1 : ↥(Subgroup.center ↥R))
  set u : X := ((u₀ : ↥R) : X) with hu
  have huR : u ∈ R := (u₀ : ↥R).2
  have hu1 : u ≠ 1 := by
    intro h
    apply hu₀
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have huc : ∀ r ∈ R, u * r = r * u := by
    intro r hr
    have := Subgroup.mem_center_iff.mp u₀.2 ⟨r, hr⟩
    exact congrArg Subtype.val this.symm
  have hzu : z * u = u * z := hc u huR
  have hzcen : ∀ g ∈ (P : Subgroup X), g * z = z * g := by
    intro g hg
    rcases hdecomp g hg with h | ⟨r, hr, rfl⟩
    · exact (hc g h).symm
    · have h1 : z * (r * z) = r := by
        rw [← mul_assoc, hc r hr, mul_assoc, hzz, mul_one]
      calc r * z * z = r := by rw [mul_assoc, hzz, mul_one]
        _ = z * (r * z) := h1.symm
  have hucen : ∀ g ∈ (P : Subgroup X), g * u = u * g := by
    intro g hg
    rcases hdecomp g hg with h | ⟨r, hr, rfl⟩
    · exact (huc g h).symm
    · calc r * z * u = r * (z * u) := mul_assoc _ _ _
        _ = r * (u * z) := by rw [hzu]
        _ = (r * u) * z := (mul_assoc _ _ _).symm
        _ = (u * r) * z := by rw [huc r hr]
        _ = u * (r * z) := mul_assoc _ _ _
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hzu1 : z * u ≠ 1 := by
    intro h
    apply hzR
    have : z = u⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact R.inv_mem huR
  have hzne : z ≠ u := fun h => hzR (h ▸ huR)
  have hmemz : (⟨z, hzP⟩ : ↥(P : Subgroup X)) ∈ Subgroup.center ↥(P : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzcen g.1 g.2)
  have hmemu : (⟨u, hRP huR⟩ : ↥(P : Subgroup X)) ∈ Subgroup.center ↥(P : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hucen g.1 g.2)
  let f : Fin 4 → ↥(Subgroup.center ↥(P : Subgroup X)) :=
    ![1, ⟨_, hmemz⟩, ⟨_, hmemu⟩, ⟨_, Subgroup.mul_mem _ hmemz hmemu⟩]
  have hf : Function.Injective f := by
    intro i j h
    have h' : ((f i : ↥(Subgroup.center ↥(P : Subgroup X))) : ↥(P : Subgroup X)).1 =
        ((f j : ↥(Subgroup.center ↥(P : Subgroup X))) : ↥(P : Subgroup X)).1 := by rw [h]
    fin_cases i <;> fin_cases j <;> simp [f] at h' ⊢
    all_goals first
      | exact absurd h'.symm hz1 | exact absurd h' hz1 | exact absurd h'.symm hu1
      | exact absurd h' hu1 | exact absurd h' hzne | exact absurd h'.symm hzne
      | exact absurd h' hzu1 | exact absurd h'.symm hzu1
  have h4 : 4 ≤ Nat.card (Subgroup.center ↥(P : Subgroup X)) := by
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have := hZ P
  omega

end Outside

section Edge

open CFSG.ClassicalInvolution Generic

theorem m11_eq_of_two_group_le_normalizer {K J R : Subgroup ↥NativeSporadic.M11}
    {zK zJ : ↥NativeSporadic.M11} (hK : Q3.IsClassicalMember3 K zK)
    (hJ : Q3.IsClassicalMember3 J zJ) (hR2 : IsPGroup 2 R) (hR8 : Nat.card R = 8) (hRJ : R ≤ J)
    (hRN : R ≤ Subgroup.normalizer (K : Set ↥NativeSporadic.M11)) : J = K := by
  have hKU := (IsClassicalMemberU.ofQ3 hK).isUniqueInvolution_sl2
  have hJU := (IsClassicalMemberU.ofQ3 hJ).isUniqueInvolution_sl2
  have hc : ∀ r ∈ R, zK * r = r * zK := by
    intro r hr
    have h := hKU.conj_eq (conjSub_eq_of_mem_normalizer (hRN hr))
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  by_cases hzR : zK ∈ R
  · have hzJ : zK = zJ := by
      rcases hJU.unique zK (hRJ hzR) hKU.sq with h | h
      · exact absurd h hKU.ne_one
      · exact h
    rw [← hzJ] at hJ
    exact m11_classical_eq hJ hK
  · exact (false_of_central_involution_outside m11_sylow_card m11_sylow_center_le_two hR2 hR8
      hK.orderOf_eq_two hzR hc).elim

theorem eq_of_two_group_le_normalizer_of_mulEquiv_m11 {G : Type} [Group G]
    (e : ↥NativeSporadic.M11 ≃* G) {K J R : Subgroup G} {zK zJ : G}
    (hK : Q3.IsClassicalMember3 K zK) (hJ : Q3.IsClassicalMember3 J zJ) (hR2 : IsPGroup 2 R)
    (hR8 : Nat.card R = 8) (hRJ : R ≤ J) (hRN : R ≤ Subgroup.normalizer (K : Set G)) : J = K := by
  have hK' := hK.map_mulEquiv e.symm
  have hJ' := hJ.map_mulEquiv e.symm
  have hR2' : IsPGroup 2 (R.map e.symm.toMonoidHom) := hR2.map _
  have hR8' : Nat.card (R.map e.symm.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hR8]
  have hRN' : R.map e.symm.toMonoidHom ≤ Subgroup.normalizer
      ((K.map e.symm.toMonoidHom : Subgroup ↥NativeSporadic.M11) : Set ↥NativeSporadic.M11) := by
    rw [← Subgroup.map_equiv_normalizer_eq K e.symm]
    exact Subgroup.map_mono hRN
  have h := m11_eq_of_two_group_le_normalizer hK' hJ' hR2' hR8' (Subgroup.map_mono hRJ) hRN'
  exact Subgroup.map_injective e.symm.injective h

end Edge

end CFSG.ClassicalInvolution.Uniform
