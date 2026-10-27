module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L32LocBase
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.L2.Lemma12hc
public import CFSG.GH74.GLS.IVK.L2.Lemma13
public import CFSG.GH74.GLS.IVK.L2.Fixed14a

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.C3.Layer1.Thm1L32.Loc
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

theorem perfect_subnormal_pgl2 {Q : Type} [Group Q] [Finite Q] {F₀ : Type} [Field F₀] [Finite F₀]
    (hodd : Odd (Nat.card F₀)) (ψ : Q ≃* PGL2 F₀) (R : Subgroup Q) (hR : ⁅R, R⁆ = R)
    (hR1 : R ≠ ⊥) (hsn : R.IsSubnormal) : L2Field F₀ ∧ Nonempty (↥R ≃* L2 F₀) := by
  have : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.2 hR
  have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).2 hR1
  have hq3 : 3 < Nat.card F₀ := by
    by_contra hle
    push Not at hle
    have hge : 1 < Nat.card F₀ := Finite.one_lt_card
    have h3 : Nat.card F₀ = 3 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    have hQcard : Nat.card Q = 2 ^ 3 * 3 ^ 1 := by
      rw [Nat.card_congr ψ.toEquiv, pgl2_card_formula, h3]
      norm_num
    have hsolv : Group.IsSolvable Q := isSolvable_of_card_two_pow_mul_three_pow hQcard
    have : Group.IsSolvable ↥R :=
      Group.isSolvable_of_isSolvable_injective (f := R.subtype) R.subtype_injective
    exact Group.IsPerfect.not_isSolvable ↥R inferInstance
  refine ⟨⟨hodd, hq3⟩, ?_⟩
  have hK : IsOddPrimePower (Nat.card F₀) := isOddPrimePower_of_odd_card hodd
  obtain ⟨eD⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three F₀ hK hq3 ψ
  have : IsSimpleGroup (PSL2 F₀) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hsimple : IsSimpleGroup ↥(commutator Q) := eD.isSimpleGroup
  have hRD : R ≤ commutator Q :=
    calc R = ⁅R, R⁆ := hR.symm
      _ ≤ ⁅(⊤ : Subgroup Q), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator Q := rfl
  have hsn' : (R.subgroupOf (commutator Q)).IsSubnormal := hsn.subgroupOf
  have hne' : R.subgroupOf (commutator Q) ≠ ⊥ := by
    intro h
    apply hR1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hRD hx⟩ : ↥(commutator Q)) ∈ R.subgroupOf (commutator Q) := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  have htop : R.subgroupOf (commutator Q) = ⊤ :=
    (Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple hsn').resolve_left hne'
  have hDR : commutator Q ≤ R := Subgroup.subgroupOf_eq_top.1 htop
  have hReq : R = commutator Q := le_antisymm hRD hDR
  exact ⟨(MulEquiv.subgroupCongr hReq).trans (eD.trans (L2.equivPSL F₀).symm)⟩


theorem isSolvable_dihedralGroup (z : ℕ) [NeZero z] : Group.IsSolvable (DihedralGroup z) := by
  classical
  let R : Subgroup (DihedralGroup z) := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)
  have hRnormal : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simp [DihedralGroup.r_mul_r]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  have : IsCyclic R := Subgroup.isCyclic_zpowers _
  let : CommGroup R := IsCyclic.commGroup
  have hRcard : Nat.card R = z := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hQcard : Nat.card (DihedralGroup z ⧸ R) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [DihedralGroup.nat_card, hRcard] at h
    have hz : 0 < z := Nat.pos_of_ne_zero (NeZero.ne z)
    exact (Nat.eq_of_mul_eq_mul_right hz h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (DihedralGroup z ⧸ R) := isCyclic_of_prime_card hQcard
  let : CommGroup (DihedralGroup z ⧸ R) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

section Fixed

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_eps (hF : L2Field F) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
  have h4 : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    obtain ⟨m, hm⟩ := hF.1
    omega
  rcases h4 with h | h
  · exact ⟨1, Or.inl rfl, by rw [Int.ModEq]; omega⟩
  · exact ⟨-1, Or.inr rfl, by rw [Int.ModEq]; omega⟩

theorem solv_centralizer_involution (hF : L2Field F) (e : K ≃* L2 F) (k₀ : K)
    (hk₀ : orderOf k₀ = 2) : Group.IsSolvable ↥(centralizer ({k₀} : Set K)) := by
  obtain ⟨ε, hε, hcong⟩ := exists_eps hF
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
    ⟨(Nat.card F - ε).toNat,
      Int.toNat_of_nonneg (by have := hF.2; rcases hε with rfl | rfl <;> omega)⟩
  obtain ⟨-, hdih, -⟩ := ivk_1_3a F hF K e ε hε hcong d hd k₀ hk₀
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hdih
  have : NeZero k := ⟨by omega⟩
  have := isSolvable_dihedralGroup k
  exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

theorem solv_fixed_outer_diag (hF : L2Field F) (e : K ≃* L2 F) (v : MulAut K)
    (hv : v ∈ innDiagSub e) (hvI : v ∉ innAut K) (hv2 : orderOf v = 2) :
    Group.IsSolvable ↥(fixedSubgroup K v) := by
  obtain ⟨ε, hε, hcong⟩ := exists_eps hF
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
    ⟨(Nat.card F + ε).toNat,
      Int.toNat_of_nonneg (by have := hF.2; rcases hε with rfl | rfl <;> omega)⟩
  obtain ⟨-, hdih, -⟩ := ivk_1_3b F hF K e ε hε hcong d hd v hv hvI hv2
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hdih
  have : NeZero k := ⟨by omega⟩
  have := isSolvable_dihedralGroup k
  exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

omit [Finite F] [Finite K] in
theorem fixedSubgroup_conj_eq (u : K) :
    fixedSubgroup K (MulAut.conj u) = centralizer ({u} : Set K) := by
  ext k
  rw [mem_centralizer_singleton_iff]
  show u * k * u⁻¹ = k ↔ k * u = u * k
  constructor
  · intro h
    calc k * u = (u * k * u⁻¹) * u := by rw [h]
      _ = u * k := by group
  · intro h
    calc u * k * u⁻¹ = (k * u) * u⁻¹ := by rw [h]
      _ = k := by group

omit [Finite F] [Finite K] in
theorem map_fixedSubgroup_eq' {y f a : MulAut K} (h : a * y * a⁻¹ = f) :
    (fixedSubgroup K y).map (a : K ≃* K).toMonoidHom = fixedSubgroup K f := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : y k = k := hk
    show f (a k) = a k
    rw [← h]
    simp [hk']
  · intro hx
    have hx' : f x = x := hx
    refine ⟨a⁻¹ x, ?_, by simp⟩
    show y (a⁻¹ x) = a⁻¹ x
    have h1 : a * y = f * a := by rw [← h]; group
    have h2 : y = a⁻¹ * f * a := by
      calc y = a⁻¹ * (a * y) := by group
        _ = a⁻¹ * (f * a) := by rw [h1]
        _ = a⁻¹ * f * a := by group
    rw [h2]
    show a⁻¹ (f (a (a⁻¹ x))) = a⁻¹ x
    simp [hx']

noncomputable def fixedSubgroupEquivOfConj' {y f a : MulAut K} (h : a * y * a⁻¹ = f) :
    ↥(fixedSubgroup K y) ≃* ↥(fixedSubgroup K f) :=
  ((a : K ≃* K).subgroupMap (fixedSubgroup K y)).trans
    (MulEquiv.subgroupCongr (map_fixedSubgroup_eq' h))

theorem fixed_L2 (hF : L2Field F) (e : K ≃* L2 F) (σ : MulAut K) (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) :
    Group.IsSolvable ↥(fixedSubgroup K σ) ∨
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ ^ 2 = Nat.card F ∧
        Nonempty (↥(fixedSubgroup K σ) ≃* PGL2 F₀) := by
  obtain ⟨e', N, -⟩ :=
    ivk_1_2a_exists F hF K e (inferInstance : Nonempty (Sylow 2 (MulAut K))).some
  have hinj := conj_injective_of_L2 e'
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  by_cases hD : σ ∈ innDiagSub e'
  · left
    by_cases hI : σ ∈ innAut K
    · obtain ⟨u, rfl⟩ := hI
      have hu2 : u ^ 2 = 1 := by
        apply hinj
        rw [map_pow, map_one, sq]
        exact hσ2
      have hu1 : u ≠ 1 := fun h => hσ1 (by rw [h, map_one])
      have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
      rw [fixedSubgroup_conj_eq]
      exact solv_centralizer_involution hF e' u hu
    · exact solv_fixed_outer_diag hF e' σ hD hI hσo
  · right
    have hyInn : σ ∉ innAut K := fun h => hD (innAut_le_innDiagSub e' h)
    obtain ⟨g, hg, hyg⟩ := fieldAutHom_fieldProj_mul e' σ
    have hτ1 : fieldProj e' σ ≠ 1 := fun h => hD ((mem_innDiagSub_iff e' σ).2 h)
    have hτ2 : fieldProj e' σ ^ 2 = 1 := by rw [← map_pow, sq, hσ2, map_one]
    have hτo : orderOf (fieldProj e' σ) = 2 := orderOf_eq_prime hτ2 hτ1
    have hf1 : fieldAutHom e' (fieldProj e' σ) ≠ 1 := fun h =>
      hτ1 (fieldAutHom_injective e' (h.trans (map_one _).symm))
    have hf2 : fieldAutHom e' (fieldProj e' σ) ^ 2 = 1 := by rw [← map_pow, hτ2, map_one]
    have hfo : orderOf (fieldAutHom e' (fieldProj e' σ)) = 2 := orderOf_eq_prime hf2 hf1
    have hfF : fieldAutHom e' (fieldProj e' σ) ∈ fieldAutSub e' := ⟨_, rfl⟩
    have hfT : fieldAutHom e' (fieldProj e' σ) ∈ (N.T : Subgroup (MulAut K)) := by
      have hP : IsPGroup 2 ↥(zpowers (fieldAutHom e' (fieldProj e' σ))) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hfo]; norm_num)
      have h1 := hP.inf_normalizer_sylow N.T
      have h2 : fieldAutHom e' (fieldProj e' σ) ∈
          zpowers (fieldAutHom e' (fieldProj e' σ)) ⊓ normalizer (N.T : Set (MulAut K)) :=
        ⟨mem_zpowers _, N.T_inv hfF⟩
      rw [h1] at h2
      exact h2.2
    have hyo : orderOf (g * fieldAutHom e' (fieldProj e' σ)) = 2 := by
      rw [← hyg]
      exact hσo
    obtain ⟨a, -, hay⟩ := ivk_1_2h_c F hF K e' N _ ⟨hfT, hfF⟩ hfo g hg hyo
    rw [← hyg] at hay
    obtain ⟨F₀, hF₀, hFin₀, hcard₀, ⟨φ⟩⟩ :=
      (ivk_1_4a F hF K e' (fieldProj e' σ)).2.2 (by rw [hτo]; exact even_two)
    rw [hτo] at hcard₀
    exact ⟨F₀, hF₀, hFin₀, hcard₀, ⟨(fixedSubgroupEquivOfConj' hay).trans φ⟩⟩

end Fixed

theorem l2_fixed_classification {Z : Type} [Group Z] [Finite Z] {F : Type} [Field F] [Finite F]
    (hF : L2Field F) (L : Subgroup Z) (e : ↥L ≃* L2 F) (s : Z) (hs2 : s * s = 1)
    (hsL : ∀ l ∈ L, s * l * s⁻¹ ∈ L) (hmove : ∃ l ∈ L, s * l * s⁻¹ ≠ l)
    (P : Subgroup Z) (hPL : P ≤ L) (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥)
    (hPs : ∀ x ∈ P, s * x * s⁻¹ = x)
    (hsub : (P.subgroupOf (centralizer ({s} : Set Z))).IsSubnormal) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), L2Field F₀ ∧ Nat.card F₀ ^ 2 = Nat.card F ∧
      Nonempty (↥P ≃* L2 F₀) := by
  obtain ⟨σ, P', -, hσ2, hσ1, ⟨eP⟩, hP'1, hP', hfix, hsubP'⟩ :=
    local_data L s hs2 hsL hmove P hPL hP hP1 hPs hsub
  have hP'le : P' ≤ fixedSubgroup ↥L σ := fun x hx => hfix x hx
  have hR : ⁅P'.subgroupOf (fixedSubgroup ↥L σ), P'.subgroupOf (fixedSubgroup ↥L σ)⁆ =
      P'.subgroupOf (fixedSubgroup ↥L σ) := by
    apply Subgroup.map_injective (fixedSubgroup ↥L σ).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hP'le, hP']
  have hR1 : P'.subgroupOf (fixedSubgroup ↥L σ) ≠ ⊥ := by
    intro h
    apply hP'1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hP'le hx⟩ : ↥(fixedSubgroup ↥L σ)) ∈ P'.subgroupOf (fixedSubgroup ↥L σ) := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  have hsubR : (P'.subgroupOf (fixedSubgroup ↥L σ)).IsSubnormal := hsubP'
  rcases fixed_L2 hF e σ hσ2 hσ1 with hsolv | ⟨F₀, hF₀, hFin₀, hcard, ⟨ψ⟩⟩
  · exfalso
    have : Group.IsPerfect ↥(P'.subgroupOf (fixedSubgroup ↥L σ)) := Subgroup.isPerfect_iff.2 hR
    have : Nontrivial ↥(P'.subgroupOf (fixedSubgroup ↥L σ)) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 hR1
    have : Group.IsSolvable ↥(P'.subgroupOf (fixedSubgroup ↥L σ)) :=
      Group.isSolvable_of_isSolvable_injective (f := (P'.subgroupOf (fixedSubgroup ↥L σ)).subtype)
        (P'.subgroupOf (fixedSubgroup ↥L σ)).subtype_injective
    exact Group.IsPerfect.not_isSolvable ↥(P'.subgroupOf (fixedSubgroup ↥L σ)) inferInstance
  · have hodd₀ : Odd (Nat.card F₀) := by
      by_contra hne
      rw [Nat.not_odd_iff_even] at hne
      have : Even (Nat.card F) := by
        rw [← hcard]
        exact Nat.even_pow.2 ⟨hne, by norm_num⟩
      exact (Nat.not_even_iff_odd.2 hF.1) this
    obtain ⟨hL2, ⟨eR⟩⟩ := perfect_subnormal_pgl2 hodd₀ ψ _ hR hR1 hsubR
    exact ⟨F₀, hF₀, hFin₀, hL2, hcard,
      ⟨eP.trans ((Subgroup.subgroupOfEquivOfLe hP'le).symm.trans eR)⟩⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
