module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCBasic
public import CFSG.Milestones.ASVolI.I2Covers
public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L52
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
  CFSG.ComponentClassification.GrSLit in
theorem l34_fixed_simple
    {S' : Type} [Group S'] [Finite S'] [IsSimpleGroup S']
    (hτ : Blueprint.LieModel S' .PSL 3 2 2) {σ : MulAut S'}
    {P : Subgroup S'} (h : ProperFixedComponent σ P) :
    IsSimpleGroup ↥P ∧ ((Nat.card ↥P = 168 ∧ Blueprint.LieModel ↥P .PSL 2 7 1) ∨
      (Nat.card ↥P = 60 ∧ Blueprint.LieModel ↥P .PSL 2 5 1)) := by
  obtain ⟨hσ, hPF, hP, hPne⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstated : Assembly.LowTwoRank.StatedClassicalModel S' .PSL 3 2 2 := by
    rcases hτ with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  obtain ⟨θ⟩ := nonempty_equiv_of_stated S' hstated
  obtain ⟨e, he, -⟩ := full_automorphism_action
  set σ' := MulAut.congr θ σ with hσ'def
  set r := e.symm σ' with hrdef
  have her : e r = σ' := e.apply_symm_apply σ'
  have hrs : ∀ s : S, ((σ' s : S) : Equiv.Perm (Fin 42)) =
      (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ := by
    intro s
    have h := he r s
    rw [her] at h
    exact h
  have hσ'2 : σ' * σ' = 1 := by
    refine MulEquiv.ext fun t => ?_
    show σ' (σ' t) = t
    rw [hσ'def, Sporadic.HeldB.congr_apply', Sporadic.HeldB.congr_apply',
      MulEquiv.symm_apply_apply, hσ, MulEquiv.apply_symm_apply]
  have hr2 : r * r = 1 := e.injective (by rw [map_mul, her, hσ'2, map_one])
  set F := FixedCommutingProduct.fixedSubgroup σ with hFdef
  set F' := FixedCommutingProduct.fixedSubgroup σ' with hF'def
  have φ₁ : F ≃* F' := Sporadic.HeldB.fixedSubgroupCongr θ σ
  have hF'map : F'.map S.subtype = centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, s.2⟩
      have h1 := congrArg Subtype.val (show σ' s = s from hs)
      rw [hrs] at h1
      change (s : Equiv.Perm (Fin 42)) * r = r * s
      calc (s : Equiv.Perm (Fin 42)) * r =
          (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ * r := by rw [h1]
        _ = r * s := by group
    · intro hx
      obtain ⟨hxr, hxS⟩ := mem_inf.mp hx
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      change σ' ⟨x, hxS⟩ = ⟨x, hxS⟩
      apply Subtype.ext
      rw [hrs]
      have h1 : x * r = r * x := mem_centralizer_singleton_iff.mp hxr
      change (r : Equiv.Perm (Fin 42)) * x * (r : Equiv.Perm (Fin 42))⁻¹ = x
      rw [← h1]
      group
  have φ₂ : F' ≃* ↥(centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S) :=
    (F'.equivMapOfInjective S.subtype S.subtype_injective).trans (MulEquiv.subgroupCongr hF'map)
  have hPF₁ : IsPComponent 2 (P.subgroupOf F) := hP
  have hsimple : ∀ (C : Subgroup (Equiv.Perm (Fin 42))) [IsSimpleGroup ↥C], (F ≃* ↥C) →
      Nonempty (↥P ≃* ↥C) := by
    intro C _ ψ
    have : IsSimpleGroup ↥F := ψ.isSimpleGroup
    have htop := eq_top_of_isPComponent_of_isSimpleGroup hPF₁
    have hPeq : P = F := le_antisymm hPF (Subgroup.subgroupOf_eq_top.mp htop)
    exact ⟨(MulEquiv.subgroupCongr hPeq).trans ψ⟩
  by_cases hr1 : r = 1
  ·
    exfalso
    have hσ'1 : σ' = 1 := by rw [← her, hr1, map_one]
    have hσ1 : σ = 1 := (MulAut.congr θ).injective (by rw [← hσ'def, hσ'1, map_one])
    have hFtop : F = ⊤ := by
      rw [hFdef, hσ1, eq_top_iff]
      intro x _
      rfl
    have : IsSimpleGroup F :=
      ((MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv).isSimpleGroup
    have h := eq_top_of_isPComponent_of_isSimpleGroup hPF₁
    apply hPne
    rw [eq_top_iff]
    intro x _
    have hx : (⟨x, hFtop ▸ mem_top x⟩ : F) ∈ P.subgroupOf F := h ▸ mem_top _
    exact hx
  · have hro : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
    have key : ∀ (C : Subgroup (Equiv.Perm (Fin 42))) (ri : Equiv.Perm (Fin 42)),
        C = centralizer {ri} ⊓ S → (∃ c ∈ R, (r : Equiv.Perm (Fin 42)) = c * ri * c⁻¹) →
        Nonempty (F ≃* C) := by
      rintro C ri rfl ⟨c, hc, hrc⟩
      exact ⟨φ₁.trans (φ₂.trans ((MulEquiv.subgroupCongr (by rw [hrc])).trans
        (centralizerInfConjEquiv (R_le_normalizer hc) ri)))⟩
    rcases (orderOf_eq_two_iff r).mp hro with h | h | h | h
    · obtain ⟨ψ⟩ := key C₁ r₁ rfl (eq_conj_of_isConj h)
      have : Group.IsSolvable ↥C₁ := isSolvable_C₁
      exact absurd hPF₁ (not_isPComponent_of_equiv_solvable ψ _)
    · obtain ⟨ψ⟩ := key C₂ r₂ rfl (eq_conj_of_isConj h)
      have : IsSimpleGroup ↥C₂ := isSimpleGroup_C₂
      obtain ⟨ε⟩ := hsimple C₂ ψ
      exact ⟨ε.isSimpleGroup, Or.inl ⟨(Nat.card_congr ε.toEquiv).trans card_C₂,
        LieType.CurtisTits.lieModel_of_mulEquiv ε.symm lieModel_C₂⟩⟩
    · obtain ⟨ψ⟩ := key C₃ r₃ rfl (eq_conj_of_isConj h)
      have : IsSimpleGroup ↥C₃ := isSimpleGroup_C₃
      obtain ⟨ε⟩ := hsimple C₃ ψ
      exact ⟨ε.isSimpleGroup, Or.inr ⟨(Nat.card_congr ε.toEquiv).trans card_C₃,
        LieType.CurtisTits.lieModel_of_mulEquiv ε.symm lieModel_C₃⟩⟩
    · obtain ⟨ψ⟩ := key C₄ r₄ rfl (eq_conj_of_isConj h)
      have : Group.IsSolvable ↥C₄ := isSolvable_C₄
      exact absurd hPF₁ (not_isPComponent_of_equiv_solvable ψ _)

theorem exists_mul_ne_of_simple_of_not_prime {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { ‹Group X› with mul_comm := hc }
  exact hX IsSimpleGroup.prime_card

theorem false_of_l34_fixed_cover
    {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (hm : Blueprint.LieModel (K ⧸ center K) .PSL 3 2 2) (hE : IsElementaryAbelian 2 ↥(center K))
    {T : Subgroup K} (hTperf : Group.IsPerfect ↥T) (hTZ : center (↥T ⧸ pPrimeCore 2 ↥T) ≠ ⊥)
    {σ : MulAut (K ⧸ center K)}
    (h : ProperFixedComponent σ (T.map (QuotientGroup.mk' (center K)))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (K ⧸ center K) := hK.2.1
  set π := QuotientGroup.mk' (center K) with hπ
  set P := T.map π with hPdef
  obtain ⟨hPs, hPcard⟩ := l34_fixed_simple hm h
  have hz2 : ∀ z ∈ center K, z ^ 2 = 1 := fun z hz => elemPow_eq_one_of_isElementaryAbelian z hz
  have hP2 : 2 ∣ Nat.card P := by
    rcases hPcard with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> norm_num
  have hPnab : ∃ a b : P, a * b ≠ b * a :=
    exists_mul_ne_of_simple_of_not_prime (by rcases hPcard with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;>
      norm_num)
  let ρ : T →* P := (π.comp T.subtype).codRestrict P fun t => mem_map_of_mem π t.2
  have hρs : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨⟨t, ht⟩, rfl⟩
  have hρker : ∀ t : T, t ∈ ρ.ker ↔ (t : K) ∈ center K := fun t => by
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
    · intro h1
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
  have hodd1 : ∀ t : T, (t : K) ∈ center K → Odd (orderOf t) → t = 1 := by
    intro t htZ hodd
    have h2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      rw [Subgroup.coe_pow, hz2 _ htZ, Subgroup.coe_one]))
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  have hOT : pPrimeCore 2 T = ⊥ := by
    have hN : ((pPrimeCore 2 T).map ρ).Normal := Subgroup.Normal.map inferInstance ρ hρs
    have hNbot : (pPrimeCore 2 T).map ρ = ⊥ := by
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hPs _ hN with h1 | h1
      · exact h1
      · exfalso
        have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 T).map ρ)) :=
          Nat.Coprime.coprime_dvd_right (card_map_dvd _ _) pPrimeCore_coprime_card
        rw [h1, card_top] at hcop
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop hP2
    rw [eq_bot_iff]
    intro x hx
    have hx1 : ρ x = 1 := by
      have : ρ x ∈ (pPrimeCore 2 T).map ρ := mem_map_of_mem ρ hx
      rwa [hNbot, mem_bot] at this
    have hodd : Odd (orderOf x) := by
      have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : pPrimeCore 2 T)
      rw [Subgroup.orderOf_mk] at h1
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card (h2.trans h1))
    rw [mem_bot]
    exact hodd1 x ((hρker x).mp hx1) hodd
  have eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* ↥T :=
    (QuotientGroup.quotientMulEquivOfEq hOT).trans QuotientGroup.quotientBot
  have hZT : center ↥T ≠ ⊥ := center_ne_bot_of_mulEquiv eT hTZ
  have hZker : center ↥T = ρ.ker := by
    ext t
    rw [hρker t]
    constructor
    · intro ht
      have hc : ρ t ∈ center P := by
        rw [mem_center_iff]
        intro y
        obtain ⟨u, rfl⟩ := hρs y
        rw [← map_mul, ← map_mul, mem_center_iff.mp ht u]
      rw [center_eq_bot_of_simple hPnab, mem_bot] at hc
      exact (hρker t).mp hc
    · intro ht
      rw [mem_center_iff]
      intro u
      exact Subtype.ext (mem_center_iff.mp ht u)
  have eTP : ↥T ⧸ center ↥T ≃* ↥P :=
    (QuotientGroup.quotientMulEquivOfEq hZker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)
  have hTq : IsQuasisimple ↥T := by
    obtain ⟨a, b, hab⟩ := hPnab
    refine ⟨hTperf, eTP.isSimpleGroup, eTP.symm a, eTP.symm b, fun hc => hab ?_⟩
    have := congrArg eTP hc
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  obtain ⟨q, hq, hq2, hLq⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      Blueprint.LieModel (↥T ⧸ center ↥T) .PSL 2 q 1 := by
    rcases hPcard with ⟨-, hL⟩ | ⟨-, hL⟩
    · exact ⟨7, by norm_num, by norm_num, Blueprint.LieModel.of_mulEquiv eTP.symm hL⟩
    · exact ⟨5, by norm_num, by norm_num, Blueprint.LieModel.of_mulEquiv eTP.symm hL⟩
  rcases GH74.Generic.BProg.B2.l2_cover_cases hTq hq hq2 hLq with
    ⟨z, hz1, hzc, hzodd⟩ | ⟨hZ0, -⟩ | ⟨-, F, _, _, hF, ⟨φ⟩⟩
  · have hzZ : z ∈ center ↥T := mem_center_iff.mpr hzc
    rw [hZker, hρker] at hzZ
    exact hz1 (hodd1 z hzZ hzodd)
  · exact hZT hZ0
  have : CharP F q := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hq
    le_rfl hF
  have h2F : (2 : F) ≠ 0 := by
    intro h20
    have h2 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h20
    have hdvd := (CharP.cast_eq_zero_iff F q 2).mp h2
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd
    exact hq2 this
  have hinv : ∀ t : ↥T, t ^ 2 = 1 → t ≠ 1 → t ∈ center ↥T := by
    intro t ht2 ht1
    rw [mem_center_iff]
    intro g
    have hc2 : (g * t * g⁻¹) ^ 2 = 1 := by
      rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
      group
    have hc1 : g * t * g⁻¹ ≠ 1 := fun h1 => ht1 (by
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using this)
    have huniq := GH74.GLS.IVK.Proofs2.ivk93l5_sl2_involution_unique h2F
      (g := φ (g * t * g⁻¹)) (h := φ t) (by rw [← map_pow, hc2, map_one])
      (fun h1 => hc1 (φ.injective (h1.trans (map_one φ).symm)))
      (by rw [← map_pow, ht2, map_one]) (fun h1 => ht1 (φ.injective (h1.trans (map_one φ).symm)))
    have hgt : g * t * g⁻¹ = t := φ.injective huniq
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [hgt]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hP2
  have hx2 : (x : K ⧸ center K) ^ 2 = 1 := by
    have h1 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hx1 : (x : K ⧸ center K) ≠ 1 := fun h1 => by
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hlift := ASVolI.burnsideI22P3_clause_b1 hK (hm.statedClassicalModel (by decide))
    (IsElementaryAbelian.isPGroup 2 ↥(center K))
  obtain ⟨k, hk2, hkx⟩ := hlift _ hx2 hx1
  obtain ⟨t₀, ht₀T, ht₀⟩ := mem_map.mp x.2
  have hz : k⁻¹ * t₀ ∈ center K := by
    have h1 : (k : K ⧸ center K) = (t₀ : K ⧸ center K) := hkx.trans ht₀.symm
    exact QuotientGroup.eq.mp h1
  have ht₀2 : t₀ ^ 2 = 1 := by
    have hcomm := mem_center_iff.mp hz k
    have hzz := hz2 _ hz
    calc t₀ ^ 2 = (k * (k⁻¹ * t₀)) * (k * (k⁻¹ * t₀)) := by rw [sq, mul_inv_cancel_left]
      _ = k ^ 2 * (k⁻¹ * t₀) ^ 2 := by
        rw [sq, sq, mul_assoc, ← mul_assoc (k⁻¹ * t₀) k, ← hcomm]
        group
      _ = 1 := by rw [hk2, hzz, one_mul]
  set t : ↥T := ⟨t₀, ht₀T⟩ with htdef
  have ht2 : t ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ht₀2, Subgroup.coe_one])
  have ht1 : t ≠ 1 := fun h1 => hx1 (by
    rw [← ht₀]
    have : t₀ = 1 := congrArg Subtype.val h1
    rw [this, map_one])
  have htc := hinv t ht2 ht1
  rw [hZker, hρker] at htc
  apply hx1
  rw [← ht₀]
  exact (QuotientGroup.eq_one_iff _).mpr htc

end CFSG.ComponentClassification.GS82PumpInputs
