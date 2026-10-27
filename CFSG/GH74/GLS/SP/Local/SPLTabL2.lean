module

public import CFSG.GH74.GLS.SP.Local.SPLPumpTabDefs
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2 CFSG.GorensteinWalter

theorem exists_equiv_pgl2_fixedSubgroup {F : Type} [Field F] [Finite F] {K : Type} [Group K]
    [Finite K] (hF : L2Field F) (e : K ≃* L2 F) (N : L2Notation e) {y : MulAut K}
    (hy2 : y ^ 2 = 1) (hyD : y ∉ innDiagSub e) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ ^ 2 = Nat.card F ∧
      Nonempty (↥(fixedSubgroup K y) ≃* PGL2 F₀) := by
  have hyInn : y ∉ innAut K := fun h => hyD (innAut_le_innDiagSub e h)
  obtain ⟨g, hg, hyg⟩ := fieldAutHom_fieldProj_mul e y
  have hσ1 : fieldProj e y ≠ 1 := fun h => hyD ((mem_innDiagSub_iff e y).2 h)
  have hσ2 : fieldProj e y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hσo : orderOf (fieldProj e y) = 2 := orderOf_eq_prime hσ2 hσ1
  have hf1 : fieldAutHom e (fieldProj e y) ≠ 1 := fun h =>
    hσ1 (fieldAutHom_injective e (h.trans (map_one _).symm))
  have hf2 : fieldAutHom e (fieldProj e y) ^ 2 = 1 := by rw [← map_pow, hσ2, map_one]
  have hfo : orderOf (fieldAutHom e (fieldProj e y)) = 2 := orderOf_eq_prime hf2 hf1
  have hfF : fieldAutHom e (fieldProj e y) ∈ fieldAutSub e := ⟨_, rfl⟩
  have hfT : fieldAutHom e (fieldProj e y) ∈ (N.T : Subgroup (MulAut K)) := by
    have hP : IsPGroup 2 ↥(zpowers (fieldAutHom e (fieldProj e y))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hfo]; norm_num)
    have h1 := hP.inf_normalizer_sylow N.T
    have h2 : fieldAutHom e (fieldProj e y) ∈
        zpowers (fieldAutHom e (fieldProj e y)) ⊓ normalizer (N.T : Set (MulAut K)) :=
      ⟨mem_zpowers _, N.T_inv hfF⟩
    rw [h1] at h2
    exact h2.2
  have hyo : orderOf (g * fieldAutHom e (fieldProj e y)) = 2 := by
    rw [← hyg]
    exact orderOf_eq_prime hy2 (fun h => hyInn (by rw [h]; exact one_mem _))
  obtain ⟨a, -, hay⟩ := ivk_1_2h_c F hF K e N _ ⟨hfT, hfF⟩ hfo g hg hyo
  rw [← hyg] at hay
  obtain ⟨F₀, i₁, i₂, hF₀, ⟨φ⟩⟩ :=
    (ivk_1_4a F hF K e (fieldProj e y)).2.2 (by rw [hσo]; exact even_two)
  rw [hσo] at hF₀
  exact ⟨F₀, i₁, i₂, hF₀, ⟨(fixedSubgroupEquivOfConj hay).trans φ⟩⟩

theorem fixedSubgroup_cases {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]
    (hF : L2Field F) (e₀ : K ≃* L2 F) {σ : MulAut K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    (∃ d : ℕ, IsDihedralOrder ↥(fixedSubgroup K σ) d) ∨
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ ^ 2 = Nat.card F ∧
        Nonempty (↥(fixedSubgroup K σ) ≃* PGL2 F₀) := by
  obtain ⟨e, N, -⟩ :=
    ivk_1_2a_exists F hF K e₀ (inferInstance : Nonempty (Sylow 2 (MulAut K))).some
  have hinj := conj_injective_of_L2 e
  have hσo : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    by_cases h : t % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  by_cases hyInn : σ ∈ innAut K
  ·
    left
    obtain ⟨u, rfl⟩ := hyInn
    have hu2 : u ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hσ2, map_one]
    have hu1 : u ≠ 1 := fun h => hσ1 (by rw [h, map_one])
    have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
      ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
    refine ⟨d, ?_⟩
    rw [Lemma118.fixedSubgroup_conj]
    exact (ivk_1_3a F hF K e ε hε1 hε d hd u hu).2.1
  · by_cases hyD : σ ∈ innDiagSub e
    ·
      left
      obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
        ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
      exact ⟨d, (ivk_1_3b F hF K e ε hε1 hε d hd σ hyD hyInn hσo).2.1⟩
    ·
      right
      exact exists_equiv_pgl2_fixedSubgroup hF e N hσ2 hyD

private theorem exists_two_element_not_mem {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hJ : J.index = 2) : ∃ c : G, c ∉ J ∧ ∃ k : ℕ, c ^ (2 ^ k) = 1 := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ J := by
    by_contra h
    push Not at h
    have : J = ⊤ := eq_top_iff.2 fun x _ => h x
    rw [this, index_top] at hJ
    omega
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g ^ m, ?_, a, ?_⟩
  · intro hgm
    apply hg
    obtain ⟨j, rfl⟩ := hm
    have h1 : (g ^ 2) ^ j ∈ J := J.pow_mem (sq_mem_of_index_two hJ g) j
    have h2 : g = g ^ (2 * j + 1) * ((g ^ 2) ^ j)⁻¹ := by group
    rw [h2]
    exact J.mul_mem hgm (J.inv_mem h1)
  · rw [← pow_mul, mul_comm, ← hnm]
    exact pow_orderOf_eq_one g

private theorem exists_mul_of_mem_sup_centralizer {K : Type} [Group K] (I : Subgroup K) {c : K}
    (hc : c ∈ I ⊔ centralizer (I : Set K)) :
    ∃ i ∈ I, ∃ d ∈ centralizer (I : Set K), c = i * d := by
  let S : Subgroup K :=
    { carrier := {x | ∃ i ∈ I, ∃ d ∈ centralizer (I : Set K), x = i * d}
      mul_mem' := by
        rintro _ _ ⟨i₁, hi₁, d₁, hd₁, rfl⟩ ⟨i₂, hi₂, d₂, hd₂, rfl⟩
        refine ⟨i₁ * i₂, I.mul_mem hi₁ hi₂, d₁ * d₂, Subgroup.mul_mem _ hd₁ hd₂, ?_⟩
        have h := (Subgroup.mem_centralizer_iff.1 hd₁) i₂ hi₂
        calc i₁ * d₁ * (i₂ * d₂) = i₁ * (d₁ * i₂) * d₂ := by group
          _ = i₁ * (i₂ * d₁) * d₂ := by rw [h]
          _ = i₁ * i₂ * (d₁ * d₂) := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨i, hi, d, hd, rfl⟩
        refine ⟨i⁻¹, I.inv_mem hi, d⁻¹, Subgroup.inv_mem _ hd, ?_⟩
        have h := (Subgroup.mem_centralizer_iff.1 hd) i hi
        calc (i * d)⁻¹ = (d * i)⁻¹ := by rw [h]
          _ = i⁻¹ * d⁻¹ := by group }
  have hle : I ⊔ centralizer (I : Set K) ≤ S :=
    sup_le (fun x hx => ⟨x, hx, 1, one_mem _, (mul_one x).symm⟩)
      (fun x hx => ⟨1, one_mem _, x, hx, (one_mul x).symm⟩)
  exact hle hc

private theorem not_isSolvable_of_equiv_psl2 {X : Type} [Group X] {F₁ : Type} [Field F₁] [Finite F₁]
    (h : 3 < Nat.card F₁) (e : X ≃* PSL2 F₁) : ¬ Group.IsSolvable X := by
  have hp : Group.IsPerfect (PSL2 F₁) := psl2_isPerfect_of_card_gt_three F₁ h
  have hX : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Nontrivial X := e.symm.injective.nontrivial
  exact Group.IsPerfect.not_isSolvable X

theorem hasOuterTwoElement_of_equiv_pgl2 {K : Type} [Group K] [Finite K] {C I : Subgroup K}
    (hIC : I ≤ C) {F₀ F₁ : Type} [Field F₀] [Finite F₀] [Field F₁] [Finite F₁]
    (hF₀ : IsOddPrimePower (Nat.card F₀)) (hF₁ : 3 < Nat.card F₁) (ψ : ↥C ≃* PGL2 F₀)
    (eI : ↥I ≃* PSL2 F₁) (hsub : (I.subgroupOf C).IsSubnormal) : HasOuterTwoElement C I := by
  set I' : Subgroup ↥C := I.subgroupOf C with hI'
  set J : Subgroup (PGL2 F₀) := I'.map ψ.toMonoidHom with hJ
  let eJ : PSL2 F₁ ≃* ↥J :=
    eI.symm.trans ((Subgroup.subgroupOfEquivOfLe hIC).symm.trans
      (Subgroup.equivMapOfInjective I' ψ.toMonoidHom ψ.injective))
  have hperf : Group.IsPerfect (PSL2 F₁) := psl2_isPerfect_of_card_gt_three F₁ hF₁
  have hJperf : Group.IsPerfect ↥J :=
    Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hJne : J ≠ ⊥ := by
    have : Nontrivial ↥J := eJ.injective.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot J).1 this
  have hJsn : J.IsSubnormal := hsub.map ψ.surjective
  obtain ⟨hgt, hJc⟩ := pgl2_perfect_subnormal_eq_commutator F₀ hF₀ J hJne hJperf hJsn
  have hJrange : J = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range :=
    hJc.trans (pgl2_commutator_eq_psl2_range_of_card_gt_three F₀ hF₀ hgt)
  have hJidx : J.index = 2 := by
    rw [hJrange]
    exact pgl2_psl2Range_index_eq_two F₀ hF₀
  have hJN : J.Normal := Subgroup.normal_of_index_eq_two hJidx
  have hcentJ : centralizer (J : Set (PGL2 F₀)) = ⊥ := by
    rw [hJrange]
    exact pgl2_psl2Range_centralizer_eq_bot F₀ hF₀
  have hI'N : I'.Normal := by
    have h : I' = J.comap ψ.toMonoidHom :=
      (Subgroup.comap_map_eq_self_of_injective ψ.injective I').symm
    rw [h]
    exact Subgroup.Normal.comap hJN _
  have : Finite (PGL2 F₀) := Finite.of_equiv ↥C ψ.toEquiv
  obtain ⟨c₀, hc₀J, k, hc₀k⟩ := exists_two_element_not_mem hJidx
  have hc'I : ψ.symm c₀ ∉ I' := by
    intro h
    apply hc₀J
    have h1 : ψ (ψ.symm c₀) ∈ J := Subgroup.mem_map_of_mem ψ.toMonoidHom h
    rwa [ψ.apply_symm_apply] at h1
  refine ⟨(ψ.symm c₀ : ↥C), (ψ.symm c₀).2, ⟨k, ?_⟩, ?_, ?_⟩
  · have h : ψ.symm c₀ ^ (2 ^ k) = 1 := by
      rw [← map_pow, hc₀k, map_one]
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  · intro x hx
    have h := hI'N.conj_mem ⟨x, hIC hx⟩ (Subgroup.mem_subgroupOf.2 hx) (ψ.symm c₀)
    exact Subgroup.mem_subgroupOf.1 h
  · intro hmem
    obtain ⟨i, hi, d, hd, hcid⟩ := exists_mul_of_mem_sup_centralizer I hmem
    have hdC : d ∈ C := by
      have h : d = i⁻¹ * ((ψ.symm c₀ : ↥C) : K) := by rw [hcid]; group
      rw [h]
      exact C.mul_mem (C.inv_mem (hIC hi)) (ψ.symm c₀).2
    have hd1 : (⟨d, hdC⟩ : ↥C) = 1 := by
      have h : ψ ⟨d, hdC⟩ ∈ centralizer (J : Set (PGL2 F₀)) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨z, hz, rfl⟩
        have hzI : (z : K) ∈ I := Subgroup.mem_subgroupOf.1 hz
        have hcomm : (z : K) * d = d * (z : K) := Subgroup.mem_centralizer_iff.1 hd _ hzI
        show ψ z * ψ ⟨d, hdC⟩ = ψ ⟨d, hdC⟩ * ψ z
        rw [← map_mul, ← map_mul]
        exact congrArg ψ (Subtype.ext hcomm)
      rw [hcentJ, Subgroup.mem_bot] at h
      exact ψ.injective (by rw [h, map_one])
    have hd1' : d = 1 := congrArg Subtype.val hd1
    apply hc'I
    rw [hI', Subgroup.mem_subgroupOf, hcid, hd1', mul_one]
    exact hi

theorem tabL2Card :
    ∀ (F : Type) [Field F] [Finite F], IVK.L2Field F → ∀ (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* IVK.L2 F) → ∀ σ : MulAut K, σ ^ 2 = 1 → σ ≠ 1 →
        4 ≤ Nat.card ↥(fixedSubgroup K σ) := by
  intro F _ _ hF K _ _ ⟨e⟩ σ hσ2 hσ1
  rcases fixedSubgroup_cases hF e hσ2 hσ1 with ⟨d, k, -, hk, ⟨ψ⟩⟩ | ⟨F₀, _, _, -, ⟨ψ⟩⟩
  · have : NeZero k := ⟨by omega⟩
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    omega
  · rw [Nat.card_congr ψ.toEquiv, pgl2_card_formula F₀]
    have h2 : 2 ≤ Nat.card F₀ := Finite.one_lt_card
    have h4 : 4 ≤ Nat.card F₀ ^ 2 := by nlinarith
    calc 4 ≤ 2 * 3 := by norm_num
      _ ≤ Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := Nat.mul_le_mul h2 (by omega)

theorem tabL2Outer :
    ∀ (F : Type) [Field F] [Finite F], IVK.L2Field F → ∀ (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* IVK.L2 F) → ∀ σ : MulAut K, σ ^ 2 = 1 → σ ≠ 1 →
        ∀ q : ℕ, Odd q → 5 ≤ q → ∀ I : Subgroup K, (∀ x ∈ I, σ x = x) →
          IVK.IsL2 ↥I (fun r => r = q) → (I.subgroupOf (fixedSubgroup K σ)).IsSubnormal →
            HasOuterTwoElement (fixedSubgroup K σ) I := by
  intro F _ _ hF K _ _ ⟨e⟩ σ hσ2 hσ1 q hq hq5 I hIfix hIL2 hsub
  obtain ⟨F₁, _, _, hF₁q, ⟨eI⟩⟩ := hIL2
  have hF₁ : 3 < Nat.card F₁ := by omega
  have hIC : I ≤ fixedSubgroup K σ := fun x hx => hIfix x hx
  rcases fixedSubgroup_cases hF e hσ2 hσ1 with ⟨d, hd⟩ | ⟨F₀, _, _, hq₀, ⟨ψ⟩⟩
  ·
    exfalso
    have hsolv : Group.IsSolvable ↥(fixedSubgroup K σ) :=
      CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_isDihedralOrder hd
    have hIsolv : Group.IsSolvable ↥I :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIC)
        (Subgroup.inclusion_injective hIC)
    exact not_isSolvable_of_equiv_psl2 hF₁ (eI.trans (L2.equivPSL F₁)) hIsolv
  · have hodd : Odd (Nat.card F₀) := by
      have h1 : Odd (Nat.card F₀ ^ 2) := by rw [hq₀]; exact hF.1
      exact (Nat.odd_mul.mp (by simpa [pow_two] using h1)).1
    exact hasOuterTwoElement_of_equiv_pgl2 hIC (isOddPrimePower_of_odd_card hodd) hF₁ ψ
      (eI.trans (L2.equivPSL F₁)) hsub

end CFSG.GH74.GLS.SP.Local
