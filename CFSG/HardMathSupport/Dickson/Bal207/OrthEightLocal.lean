module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthEightFixed
public import CFSG.HardMathSupport.Dickson.Bal207.CoreFreeInner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Group
public import CFSG.RankThree.PartOne.S11d.OrthSplitFixed
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthEight

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

section Generic

theorem noNormalPPrime_of_commuting_quasisimple {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {C : Subgroup G} {ι : Type*} (L : ι → Subgroup G) (hsup : (⨆ i, L i) = C)
    (hq : ∀ i, CFSG.IsQuasisimple ↥(L i)) (hpL : ∀ i, p ∣ Nat.card (L i))
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ L i, ∀ v ∈ L j, u * v = v * u)
    (hZ : ∀ z ∈ C, (∀ t ∈ C, z * t = t * z) → z = 1) : NoNormalPPrime p C := by
  classical
  have hLC : ∀ i, L i ≤ C := fun i => hsup ▸ le_iSup L i
  have hcent : ∀ r : G, (∀ i, ∀ j ∈ L i, r * j = j * r) → ∀ t ∈ C, r * t = t * r := by
    intro r hr t ht
    have hle : C ≤ Subgroup.centralizer ({r} : Set G) := by
      rw [← hsup]
      exact iSup_le fun i j hj => Subgroup.mem_centralizer_singleton_iff.mpr (hr i j hj).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ht)).symm
  have hnorm : ∀ i, C ≤ Subgroup.normalizer (L i : Set G) := by
    intro i
    rw [← hsup]
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · subst hij
      exact Subgroup.le_normalizer
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        rw [hcomm j i hij g hg n hn, mul_inv_cancel_right]
        exact hn
      · intro hn
        have h1 := hcomm j i hij g hg _ hn
        have h2 : n = g * n * g⁻¹ := by
          calc n = g⁻¹ * ((g * n * g⁻¹) * g) := by group
            _ = g⁻¹ * (g * (g * n * g⁻¹)) := by rw [h1]
            _ = g * n * g⁻¹ := by group
        rw [h2]
        exact hn
  refine noNormalPPrime_of_components L hLC
    (fun i f hf n hn => (Subgroup.mem_normalizer_iff.mp (hnorm i hf) n).mp hn) (fun i => ?_)
    (fun r hr hrc _ => hZ r hr (hcent r hrc))
  refine noNormalPPrime_of_isQuasisimple hp (hq i) (hpL i) fun z hz hzc _ =>
    hZ z (hLC i hz) (hcent z fun k j hj => ?_)
  by_cases hki : k = i
  · subst hki
    exact hzc j hj
  · exact hcomm i k (Ne.symm hki) z hz j hj

end Generic

section Factors

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem cyc3_mem_primaryFactors (hK : Nat.card K = 8)
    (hm : 1 ≤ primaryMultiplicity x.toLinearMap (cyc3 K)) :
    cyc3 K ∈ primaryFactors x.toLinearMap := by
  refine mem_primaryFactors_of_primaryComponent_ne_bot (irreducible_cyc3 hK) (monic_cyc3 K)
    fun h => ?_
  have h1 := finrank_cyc3 (x := x) hK
  rw [h, finrank_bot] at h1
  omega

theorem noNormalPPrime_specialBlock_cyc3 (hK : Nat.card K = 8) (hx : OddOrderIsometry Q 3 x)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap (cyc3 K)) :
    NoNormalPPrime 3 (specialBlock Q x (cyc3 K)) := by
  have hh := cyc3_mem_primaryFactors (x := x) hK (by omega)
  refine noNormalPPrime_of_isQuasisimple Nat.prime_three
    (orth3_quasisimple_specialBlock hx Nat.prime_three (by norm_num) (by omega) hh
      (cyc3_ne_X_sub_one K) hm)
    (orth3_dvd_card_orthSpecialBlock hx Nat.prime_three (by norm_num) hh (cyc3_ne_X_sub_one K) hm)
    fun z hz hzc hzo => ?_
  obtain ⟨hzO, hzx⟩ := Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer _ hz)
  exact eq_one_of_mem_supportedBlock_cyc3 hK hx (specialBlock_le_supportedBlock _ hz)
    (fixes_cyc3 hK hx hzO (Subgroup.mem_centralizer_singleton_iff.mp hzx) hzo
      (pow_orderOf_eq_one z) fun _ f hf => hzc f hf)

theorem noNormalPPrime_supportedFixedDerived (hK : Nat.card K = 8) (hx : OddOrderIsometry Q 3 x)
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ finrank K (fixedSpace x)) :
    NoNormalPPrime 3 (supportedFixedDerived Q x) := by
  classical
  have := charP_two hK
  have hK4 : 4 ≤ Nat.card K := by omega
  have h3 : 3 ≤ finrank K (fixedSpace x) := by omega
  have hZ : ∀ z ∈ supportedFixedDerived Q x,
      (∀ t ∈ supportedFixedDerived Q x, z * t = t * z) → z = 1 :=
    fun z hz hzc => eq_one_of_commute_supportedFixedDerived hK hx hQ h3 hz hzc
  by_cases hns : finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x),
      finrank K S = 2 ∧ ∀ u ∈ S, (Q.comp (fixedSpace x).subtype) u = 0
  ·
    obtain ⟨hW4, hsplit⟩ := hns
    obtain ⟨M⟩ := exists_splitFourModel hx hW4 hsplit hK4
    set ψ := M.psi hx with hψ
    have hψi : Function.Injective ψ := M.psi_injective hx
    have hSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le le_rfl hK4
    have hSL3 : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
      dvd_card_SL_of_dvd_pow_sub_one (e := 2) Nat.prime_three (by rw [hK]; norm_num)
        (by norm_num) le_rfl (by rw [hK]; norm_num)
    have hle : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K →*
        Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K,
        (ψ.comp g).range ≤ ψ.range := fun g y hy => by
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
      exact MonoidHom.mem_range.mpr ⟨g a, rfl⟩
    have hc : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) K, ψ (a, 1) * ψ (1, b) =
        ψ (1, b) * ψ (a, 1) := fun a b => by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (by simp)
    let F : Bool → Subgroup (V ≃ₗ[K] V) := fun b =>
      cond b (ψ.comp (MonoidHom.inl _ _)).range (ψ.comp (MonoidHom.inr _ _)).range
    have hFi : ∀ b, ∃ f : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V),
        Function.Injective f ∧ F b = f.range := by
      intro b
      cases b
      · exact ⟨ψ.comp (MonoidHom.inr _ _), fun a b h => (Prod.mk.inj (hψi h)).2, rfl⟩
      · exact ⟨ψ.comp (MonoidHom.inl _ _), fun a b h => (Prod.mk.inj (hψi h)).1, rfl⟩
    refine noNormalPPrime_of_commuting_quasisimple Nat.prime_three F ?_ (fun b => ?_)
      (fun b => ?_) ?_ hZ
    · rw [iSup_bool_eq, ← M.range_psi hx]
      refine le_antisymm (sup_le (hle _) (hle _)) fun y hy => ?_
      obtain ⟨⟨a, b⟩, rfl⟩ := MonoidHom.mem_range.mp hy
      have hab : ((a, b) : Matrix.SpecialLinearGroup (Fin 2) K ×
          Matrix.SpecialLinearGroup (Fin 2) K) = (a, 1) * (1, b) := Prod.ext (by simp) (by simp)
      rw [hab, map_mul]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (show ψ (a, 1) ∈ F true from MonoidHom.mem_range.mpr ⟨a, rfl⟩))
        (Subgroup.mem_sup_right (show ψ (1, b) ∈ F false from MonoidHom.mem_range.mpr ⟨b, rfl⟩))
    · obtain ⟨f, hf, hFb⟩ := hFi b
      rw [hFb]
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hf) hSL
    · obtain ⟨f, hf, hFb⟩ := hFi b
      rw [hFb, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
      exact hSL3
    · intro i j hij u hu v hv
      cases i <;> cases j
      · exact absurd rfl hij
      · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp
          (show u ∈ (ψ.comp (MonoidHom.inr _ _)).range from hu)
        obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp
          (show v ∈ (ψ.comp (MonoidHom.inl _ _)).range from hv)
        exact (hc b a).symm
      · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp
          (show u ∈ (ψ.comp (MonoidHom.inl _ _)).range from hu)
        obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp
          (show v ∈ (ψ.comp (MonoidHom.inr _ _)).range from hv)
        exact hc a b
      · exact absurd rfl hij
  ·
    have hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype) := by
      rintro (⟨-, h⟩ | ⟨-, h | h⟩) <;> omega
    have hqO := orthogonal_regular_space_derived_quasisimple (Q.comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate h3 hnexc hns
    have e1 : ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype))) ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
      (Subgroup.equivMapOfInjective _
        (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype
        (TauCeti.QuadraticMap.orthogonalGroup _).subtype_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))
    have hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans (supportedFixedDerivedEquiv hx).symm) hqO
    obtain ⟨U, hU3, hU1, -⟩ :=
      exists_supportedBlock_pow_three hx (three_dvd_natCard_orthogonalGroup_fixed hK hx h4)
    have hUs : (U : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x :=
      orth3_mem_supportedFixedDerived hx Nat.prime_three (by norm_num) hK4 h3 U.2
        (congrArg Subtype.val hU3)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hUo : orderOf (U : V ≃ₗ[K] V) = 3 :=
      orderOf_eq_prime (congrArg Subtype.val hU3) fun h => hU1 (Subtype.ext h)
    have h3S : 3 ∣ Nat.card ↥(supportedFixedDerived Q x) := by
      rw [← hUo]
      exact Subgroup.orderOf_dvd_natCard _ hUs
    exact noNormalPPrime_of_isQuasisimple Nat.prime_three hq h3S fun z hz hzc _ => hZ z hz hzc

end Factors

section Centralizer

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem noNormalPPrime_isometryCentralizer_inf_orthDerived (hK : Nat.card K = 8)
    (hx : OddOrderIsometry Q 3 x) (hQ : (polarBilin Q).Nondegenerate)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) :
    NoNormalPPrime 3 (isometryCentralizer Q x ⊓ orthDerived Q) := by
  classical
  have := charP_two hK
  set L := isometryCentralizer Q x ⊓ orthDerived Q with hLdef
  have hnb : ∀ f ∈ L, ∀ n ∈ (⊥ : Subgroup (V ≃ₗ[K] V)),
      f * n * f⁻¹ ∈ (⊥ : Subgroup (V ≃ₗ[K] V)) := by
    intro f _ n hn
    rw [Subgroup.mem_bot] at hn ⊢
    rw [hn, mul_one, mul_inv_cancel]
  have hNb : NoNormalPPrime 3 (⊥ : Subgroup (V ≃ₗ[K] V)) := fun N hN _ _ => le_bot_iff.mp hN
  obtain ⟨Jh, hJhL, hJhn, hJh, hJhe⟩ : ∃ J : Subgroup (V ≃ₗ[K] V), J ≤ L ∧
      (∀ f ∈ L, ∀ n ∈ J, f * n * f⁻¹ ∈ J) ∧ NoNormalPPrime 3 J ∧
      (2 ≤ primaryMultiplicity x.toLinearMap (cyc3 K) → J = specialBlock Q x (cyc3 K)) := by
    by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap (cyc3 K)
    · refine ⟨specialBlock Q x (cyc3 K), le_inf (specialBlock_le_isometryCentralizer _)
        (orth3_specialBlock_le_orthDerived hx Nat.prime_three (by norm_num) (by omega)
          (cyc3_mem_primaryFactors hK (by omega)) (cyc3_ne_X_sub_one K) hm),
        fun f hf n hn => conj_mem_specialBlock (Subgroup.mem_inf.mp hf).1 hn,
        noNormalPPrime_specialBlock_cyc3 hK hx hm, fun _ => rfl⟩
    · exact ⟨⊥, bot_le, hnb, hNb, fun h => absurd h hm⟩
  obtain ⟨JW, hJWL, hJWn, hJW, hJWe⟩ : ∃ J : Subgroup (V ≃ₗ[K] V), J ≤ L ∧
      (∀ f ∈ L, ∀ n ∈ J, f * n * f⁻¹ ∈ J) ∧ NoNormalPPrime 3 J ∧
      (4 ≤ finrank K (fixedSpace x) → J = supportedFixedDerived Q x) := by
    by_cases h4 : 4 ≤ finrank K (fixedSpace x)
    · exact ⟨supportedFixedDerived Q x, le_inf supportedFixedDerived_le_isometryCentralizer
        hx.supportedFixedDerived_le_orthDerived,
        fun f hf n hn => hx.conj_mem_supportedFixedDerived (Subgroup.mem_inf.mp hf).1 hn,
        noNormalPPrime_supportedFixedDerived hK hx hQ h4, fun _ => rfl⟩
    · exact ⟨⊥, bot_le, hnb, hNb, fun h => absurd h h4⟩
  refine noNormalPPrime_of_components (fun b : Bool => cond b Jh JW) (fun b => ?_) (fun b => ?_)
    (fun b => ?_) ?_
  · cases b
    · exact hJWL
    · exact hJhL
  · cases b
    · exact hJWn
    · exact hJhn
  · cases b
    · exact hJW
    · exact hJh
  intro r hr hrc hro
  obtain ⟨hrM, hrΩ⟩ := Subgroup.mem_inf.mp hr
  obtain ⟨hrO, hrx⟩ := Subgroup.mem_inf.mp hrM
  refine eq_one_of_fixes hK hx ?_ (fixes_cyc3 hK hx hrO
    (Subgroup.mem_centralizer_singleton_iff.mp hrx) hro (pow_orderOf_eq_one r)
    fun hm f hf => hrc true f (by rw [hJhe hm]; exact hf))
  obtain ⟨a, ha⟩ := hx.even_finrank_fixed
  rcases (show a = 0 ∨ a = 1 ∨ 2 ≤ a by omega) with h0 | h1 | h2
  · intro w hw
    have hbot : fixedSpace x = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    rw [hbot, Submodule.mem_bot] at hw
    rw [hw, map_zero]
  · exact fixes_fixedSpace_two_of_mem_orthDerived hK hx hQ hpar (by omega) hrM hrΩ hro
      (pow_orderOf_eq_one r)
  · exact fixes_fixedSpace_of_commute_derived hK hx hQ (by omega) hrM
      fun f hf => hrc false f (by rw [hJWe (by omega)]; exact hf)

theorem eq_one_of_commute_isometryCentralizer_inf (hK : Nat.card K = 8)
    (hx : OddOrderIsometry Q 3 x) (hxΩ : x ∈ orthDerived Q) (hQ : (polarBilin Q).Nondegenerate)
    (h3V : 3 ≤ finrank K V) (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) {G : V ≃ₗ[K] V}
    (hG : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {k : ℕ} (hk : Nat.Coprime 3 k)
    (hGk : G ^ k = 1)
    (hcomm : ∀ f ∈ isometryCentralizer Q x ⊓ orthDerived Q, G * f = f * G) : G = 1 := by
  classical
  have := charP_two hK
  have hK4 : 4 ≤ Nat.card K := by omega
  have hxM : x ∈ isometryCentralizer Q x :=
    Subgroup.mem_inf.mpr ⟨hx.mem, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hGx : G * x = x * G := hcomm x (Subgroup.mem_inf.mpr ⟨hxM, hxΩ⟩)
  have hGM : G ∈ isometryCentralizer Q x :=
    Subgroup.mem_inf.mpr ⟨hG, Subgroup.mem_centralizer_singleton_iff.mpr hGx⟩
  refine eq_one_of_fixes hK hx ?_ (fixes_cyc3 hK hx hG hGx hk hGk fun hm f hf => hcomm f
    (le_inf (specialBlock_le_isometryCentralizer _) (orth3_specialBlock_le_orthDerived hx
      Nat.prime_three (by norm_num) hK4 (cyc3_mem_primaryFactors hK (by omega))
      (cyc3_ne_X_sub_one K) hm) hf))
  obtain ⟨a, ha⟩ := hx.even_finrank_fixed
  rcases (show a = 0 ∨ a = 1 ∨ 2 ≤ a by omega) with h0 | h1 | h2
  · intro w hw
    have hbot : fixedSpace x = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    rw [hbot, Submodule.mem_bot] at hw
    rw [hw, map_zero]
  · refine fixes_fixedSpace_two_of_commute hK hx hpar (by omega) hGM hk hGk fun U hU hU3 =>
      hcomm U (Subgroup.mem_inf.mpr ⟨supportedBlock_le_isometryCentralizer _ hU, ?_⟩)
    exact orth3_mem_orthDerived_of_pow_prime Q hQ h3V hK4 Nat.prime_three (by norm_num)
      (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer _ hU)).1 hU3
  · exact fixes_fixedSpace_of_commute_derived hK hx hQ (by omega) hGM fun f hf => hcomm f
      (Subgroup.mem_inf.mpr ⟨supportedFixedDerived_le_isometryCentralizer hf,
        hx.supportedFixedDerived_le_orthDerived hf⟩)

end Centralizer

section Projective

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] in
theorem three_le_finrank_of_singular
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) : 3 ≤ finrank K V := by
  obtain ⟨U, hU, -⟩ := hT
  have := Submodule.finrank_le U
  omega

theorem exists_lift_of_orderOf_eq_three (hK : Nat.card K = 8)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {a : ProjOrthDerived Q}
    (ha : orderOf a = 3) :
    ∃ x : orthDerived Q, OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) ∧
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        centralizerImage Q (x : V ≃ₗ[K] V) := by
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, -⟩ := hlift 3 Nat.prime_three (by norm_num) a ha
  exact ⟨x, oddOrderIsometry_of_orthDerived Nat.prime_three
      (by rw [ringChar_eq_two hK]; norm_num) hQ x hxp,
    (orth3_conj_injective_and_centralizer hQ hT Nat.prime_three (by norm_num) a ha x hxa
      hxp).2⟩

theorem noNormalPPrime_centralizer_projOrthDerived (hK : Nat.card K = 8)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) {a : ProjOrthDerived Q}
    (ha : orderOf a = 3) :
    NoNormalPPrime 3 (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) := by
  have := charP_two hK
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K)
    (by have := three_le_finrank_of_singular hT; omega)
  obtain ⟨x, hx, hcent⟩ := exists_lift_of_orderOf_eq_three hK hQ hT ha
  have hinj : Function.Injective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := piOrth_injective hQ
  rw [hcent, centralizerImage, W2.noNormalPPrime_map_iff _ hinj,
    ← W2.noNormalPPrime_map_iff _ (orthDerived Q).subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  exact noNormalPPrime_isometryCentralizer_inf_orthDerived hK hx hQ hpar

theorem eq_one_of_conj_fixes_centralizer_projOrthDerived (hK : Nat.card K = 8)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) {a : ProjOrthDerived Q}
    (ha : orderOf a = 3) {G : V ≃ₗ[K] V} (hG : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {k : ℕ} (hk : Nat.Coprime 3 k) (hGk : G ^ k = 1)
    (hfix : ∀ y : orthDerived Q, (QuotientGroup.mk y : ProjOrthDerived Q) ∈
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) →
      ∃ hy : G * (y : V ≃ₗ[K] V) * G⁻¹ ∈ orthDerived Q,
        (QuotientGroup.mk ⟨G * y * G⁻¹, hy⟩ : ProjOrthDerived Q) = QuotientGroup.mk y) :
    G = 1 := by
  have := charP_two hK
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K)
    (by have := three_le_finrank_of_singular hT; omega)
  obtain ⟨x, hx, hcent⟩ := exists_lift_of_orderOf_eq_three hK hQ hT ha
  have hinj : Function.Injective (piOrth Q) := piOrth_injective hQ
  refine eq_one_of_commute_isometryCentralizer_inf hK hx x.2 hQ (three_le_finrank_of_singular hT)
    hpar hG hk hGk fun f hf => ?_
  obtain ⟨hfM, hfΩ⟩ := Subgroup.mem_inf.mp hf
  have ht : (QuotientGroup.mk (⟨f, hfΩ⟩ : orthDerived Q) : ProjOrthDerived Q) ∈
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) := by
    rw [hcent]
    exact ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hfM, rfl⟩
  obtain ⟨hy, hGf⟩ := hfix ⟨f, hfΩ⟩ ht
  have h1 := @hinj ⟨G * f * G⁻¹, hy⟩ ⟨f, hfΩ⟩ hGf
  have h2 : G * f * G⁻¹ = f := congrArg Subtype.val h1
  calc G * f = G * f * G⁻¹ * G := by group
    _ = f * G := by rw [h2]

theorem eq_one_of_fixes_centralizer_projOrthDerived (hK : Nat.card K = 8)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) {a : ProjOrthDerived Q}
    (ha : orderOf a = 3) {G : V ≃ₗ[K] V} (hG : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {α : MulAut (ProjOrthDerived Q)}
    (hα : ∀ y : orthDerived Q, ∃ hy : G * (y : V ≃ₗ[K] V) * G⁻¹ ∈ orthDerived Q,
      α (QuotientGroup.mk y) = QuotientGroup.mk ⟨G * y * G⁻¹, hy⟩)
    (hco : Nat.Coprime 3 (orderOf α))
    (hfix : ∀ t ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)), α t = t) : α = 1 := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hpow : ∀ (n : ℕ) (y : orthDerived Q),
      ∃ hy : G ^ n * (y : V ≃ₗ[K] V) * (G ^ n)⁻¹ ∈ orthDerived Q,
        (α ^ n) (QuotientGroup.mk y) = QuotientGroup.mk ⟨G ^ n * y * (G ^ n)⁻¹, hy⟩ := by
    intro n
    induction n with
    | zero =>
      intro y
      refine ⟨by rw [pow_zero, one_mul, inv_one, mul_one]; exact y.2, ?_⟩
      rw [pow_zero, MulAut.one_apply]
      exact congrArg _ (Subtype.ext (by simp))
    | succ n ih =>
      intro y
      obtain ⟨hy, h⟩ := ih y
      obtain ⟨hy', h'⟩ := hα ⟨G ^ n * y * (G ^ n)⁻¹, hy⟩
      have e : G ^ (n + 1) * (y : V ≃ₗ[K] V) * (G ^ (n + 1))⁻¹ =
          G * (G ^ n * y * (G ^ n)⁻¹) * G⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        simp only [mul_assoc]
      refine ⟨by rw [e]; exact hy', ?_⟩
      rw [pow_succ', MulAut.mul_apply, h, h']
      exact congrArg _ (Subtype.ext e.symm)
  have hfixn : ∀ (n : ℕ), ∀ t ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
      (α ^ n) t = t := by
    intro n
    induction n with
    | zero => intro t _; rw [pow_zero, MulAut.one_apply]
    | succ n ih =>
      intro t ht
      rw [pow_succ', MulAut.mul_apply, ih t ht, hfix t ht]
  obtain ⟨e, m', hm', hGo⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos G).ne' 3
    (by norm_num)
  have hG1 : G ^ (3 ^ e) = 1 := by
    refine eq_one_of_conj_fixes_centralizer_projOrthDerived hK hQ hT hpar ha (pow_mem hG _)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm') ?_ fun y hy => ?_
    · rw [← pow_mul, ← hGo, pow_orderOf_eq_one]
    · obtain ⟨hy', h⟩ := hpow (3 ^ e) y
      exact ⟨hy', h.symm.trans (hfixn _ _ hy)⟩
  have hα1 : α ^ (3 ^ e) = 1 := by
    refine MulEquiv.ext fun t => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨hy, h⟩ := hpow (3 ^ e) y
    rw [h, MulAut.one_apply]
    exact congrArg _ (Subtype.ext (by simp [hG1]))
  have hdvd : orderOf α ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hα1
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left e hco).symm hdvd)

end Projective

end CFSG.HardMathSupport.Dickson.Bal207.OrthEight

end
