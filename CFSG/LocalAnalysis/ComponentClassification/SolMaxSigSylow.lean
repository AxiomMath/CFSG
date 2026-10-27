module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78HPump
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwapB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigExact
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36P

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem card_le_two_pow_of_le [Finite X] {Y P : Subgroup X} (hPY : P ≤ Y) (hP : IsPGroup 2 P) :
    Nat.card P ≤ 2 ^ (Nat.card Y).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf Y) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  calc Nat.card P = Nat.card (P.subgroupOf Y) :=
        (Nat.card_congr (subgroupOfEquivOfLe hPY).toEquiv).symm
    _ ≤ Nat.card Q := Subgroup.card_le_of_le hQ
    _ = 2 ^ (Nat.card Y).factorization 2 := Q.card_eq_multiplicity

theorem exists_mem_orderOf_eq_two_of_ne_bot [Finite X] {R : Subgroup X} (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) : ∃ r ∈ R, orderOf r = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card R := by
    rcases hR2.card_eq_or_dvd with h | h
    · exact absurd ((Subgroup.card_eq_one).mp h) hR1
    · exact h
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 2 hdvd
  exact ⟨r, r.2, by rw [Subgroup.orderOf_coe]; exact hr⟩

theorem exists_conj_le_of_card [Finite X] {Y F R : Subgroup X} (hFY : F ≤ Y)
    (hF : Nat.card F = 2 ^ (Nat.card Y).factorization 2) (hRY : R ≤ Y) (hR : IsPGroup 2 R) :
    ∃ g ∈ Y, ∀ y ∈ R, g⁻¹ * y * g ∈ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Nat.card (F.subgroupOf Y) = 2 ^ (Nat.card Y).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFY).toEquiv, hF]
  have hR' : IsPGroup 2 (R.subgroupOf Y) := hR.comap_subtype
  obtain ⟨P, hP⟩ := hR'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Y) (Sylow.ofCard (F.subgroupOf Y) hF') P
  refine ⟨g, g.2, fun y hy => ?_⟩
  have hyP : (⟨y, hRY hy⟩ : ↥Y) ∈ (P : Subgroup ↥Y) := hP hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyP
  have h1 : g⁻¹ * (⟨y, hRY hy⟩ : ↥Y) * g ∈ F.subgroupOf Y := by
    simpa [Sylow.coe_ofCard] using hyP
  rw [mem_subgroupOf] at h1
  simpa using h1

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem card_two_eq_of_sup (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) :
    ∃ S₀ : Subgroup X, S₀ ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ∧
      S₀ ≤ centralizer ({t} : Set X) ∧ IsPGroup 2 S₀ ∧
      Nat.card S₀ =
        2 ^ (Nat.card (normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  obtain ⟨S₀, hS₀N, hS₀2, hS₀card, htS₀, hS₀C⟩ := S.pair.2.2.2.2.2
  have hS₀H : S₀ ≤ H := hS₀N.trans (S.normalizer_le_normalizer_completion h33 h35)
  refine ⟨S₀, hS₀H, hS₀C, hS₀2, ?_⟩
  have hS₀2' : IsPGroup 2 (S₀.subgroupOf H) := hS₀2.comap_subtype
  obtain ⟨Q, hQ⟩ := hS₀2'.exists_le_sylow
  set S₁ : Subgroup X := (Q : Subgroup ↥H).map H.subtype with hS₁def
  have hS₁H : S₁ ≤ H := map_subtype_le _
  have hS₀S₁ : S₀ ≤ S₁ := fun x hx => ⟨⟨x, hS₀H hx⟩, hQ hx, rfl⟩
  have hS₁card : Nat.card S₁ = 2 ^ (Nat.card H).factorization 2 := by
    rw [hS₁def, card_map_of_injective H.subtype_injective, Q.card_eq_multiplicity]
  have hS₁2 : IsPGroup 2 S₁ := Q.isPGroup'.map _
  have htM : t ∈ normalizer (M : Set X) := hHN (hS₀H htS₀)
  have htK : t ∈ UnbalancedLayer.coreActionKernel M :=
    Sol78H.mem_coreActionKernel_of_sup_le_centralizer htM S.pair.1.2.1 hsup
  obtain ⟨z, hzS₁, hzK, hz2, hzc⟩ : ∃ z ∈ S₁, z ∈ UnbalancedLayer.coreActionKernel M ∧
      orderOf z = 2 ∧ ∀ y ∈ S₁, y * z = z * y := by
    set K' : Subgroup ↥S₁ := (UnbalancedLayer.coreActionKernel M).subgroupOf S₁ with hK'def
    have hK'n : K'.Normal := by
      refine ⟨fun k hk g => ?_⟩
      rw [hK'def, mem_subgroupOf] at hk ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact UnbalancedLayer.conj_mem_coreActionKernel (hHN (hS₁H g.2)) hk
    have hK'1 : K' ≠ ⊥ := by
      intro h
      have h1 : (⟨t, hS₀S₁ htS₀⟩ : ↥S₁) ∈ K' := by rw [hK'def, mem_subgroupOf]; exact htK
      rw [h, mem_bot] at h1
      have h2 := S.pair.1.1
      rw [show t = 1 from congrArg Subtype.val h1, orderOf_one] at h2
      omega
    have hnil : Group.IsNilpotent ↥S₁ := hS₁2.isNilpotent
    have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hK'1
    have hZ2 : IsPGroup 2 ↥(K' ⊓ center ↥S₁ : Subgroup ↥S₁) := hS₁2.to_subgroup _
    obtain ⟨w, hw, hw2⟩ := exists_mem_orderOf_eq_two_of_ne_bot hZ2 hZ
    obtain ⟨hwK, hwZ⟩ := mem_inf.mp hw
    refine ⟨w, w.2, ?_, by rw [Subgroup.orderOf_coe]; exact hw2, fun y hy => ?_⟩
    · rw [hK'def, mem_subgroupOf] at hwK
      exact hwK
    · have h1 := (mem_center_iff.mp hwZ) ⟨y, hy⟩
      exact congrArg Subtype.val h1
  have hzt : z ∈ centralizer ({t} : Set X) :=
    mem_centralizer_singleton_iff.mpr (hzc t (hS₀S₁ htS₀)).symm
  have hzKJ : z ∈ UnbalancedLayer.coreActionKernel J :=
    S.mem_coreActionKernel_of_le hT13 hML hSch (le_sup_left.trans hsup.le) hzt hzK
  have hCz : centralizer ({z} : Set X) ≤ H :=
    S.centralizer_le_of_kernel h33 h35 hT13 hML hSch hz2 hzt hzKJ
  have hz2' : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hzH : z ∈ H := hS₁H hzS₁
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hMpc).2.2
  have hMsub : (M.subgroupOf H).IsSubnormal := hMpc.choose_spec.2.1
  set Jz := GSLit.fixedLayer M (zpowers z) with hJzdef
  have hCzz : centralizer ((zpowers z : Subgroup X) : Set X) = centralizer ({z} : Set X) :=
    UnbalancedLayer.centralizer_zpowers_eq z
  have hJzpc : IsPComponent 2 (Jz.subgroupOf (centralizer ({z} : Set X))) := by
    have h1 := GSLit.fixedLayer_isPComponent hMH hMsub (zpowers_le.mpr hzH)
      (zpowers_le.mpr hzK) hz2' hMq
    rwa [hCzz, inf_eq_right.mpr hCz] at h1
  have hJzC : Jz ≤ centralizer ({z} : Set X) := by
    rw [← hCzz]
    exact (GSLit.fixedLayer_le_inf M (zpowers z)).trans inf_le_right
  have hJzM : Jz ≤ M := (GSLit.fixedLayer_le_inf M (zpowers z)).trans inf_le_left
  obtain ⟨hJzsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq (zpowers_le.mpr hzK) hz2'
  obtain ⟨θz, -⟩ := exists_coreQuot_of_sup hJzM hJzsup θ
  have hmax := S.pair.2.2.2.2.1 z Jz ⟨hz2, hJzC, hJzpc, ⟨θz⟩⟩
  have hS₁N : S₁ ≤ normalizer (Jz : Set X) := fun y hy =>
    GSLit.mem_normalizer_fixedLayer (hHN (hS₁H hy))
      (mem_normalizer_zpowers_of_commute (hzc y hy).symm)
  have h1 : Nat.card S₁ ≤ 2 ^ (Nat.card (normalizer (Jz : Set X))).factorization 2 :=
    card_le_two_pow_of_le hS₁N hS₁2
  have h2 : 2 ^ (Nat.card (normalizer (Jz : Set X))).factorization 2 ≤
      2 ^ (Nat.card (normalizer (J : Set X))).factorization 2 :=
    Nat.pow_le_pow_right (by norm_num) hmax
  have h3 : Nat.card S₀ ≤ Nat.card S₁ := Subgroup.card_le_of_le hS₀S₁
  rw [hS₁card] at h1 h3
  rw [hS₀card] at h3 ⊢
  omega

theorem centralizer_le_of_le_coreActionKernel (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {R : Subgroup X}
    (hRH : R ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hRK : R ≤ UnbalancedLayer.coreActionKernel M) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  obtain ⟨S₀, hS₀H, hS₀C, -, hS₀card⟩ :=
    S.card_two_eq_of_sup h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup
  obtain ⟨g, hgH, hg⟩ := exists_conj_le_of_card hS₀H hS₀card hRH hR2
  obtain ⟨r, hrR, hr2⟩ := exists_mem_orderOf_eq_two_of_ne_bot hR2 hR1
  set r' := g⁻¹ * r * g with hr'def
  have hr'S₀ : r' ∈ S₀ := hg r hrR
  have hr't : r' ∈ centralizer ({t} : Set X) := hS₀C hr'S₀
  have hr'K : r' ∈ UnbalancedLayer.coreActionKernel M := by
    have h1 := UnbalancedLayer.conj_mem_coreActionKernel (hHN (inv_mem hgH)) (hRK hrR)
    rwa [inv_inv] at h1
  have hr'2 : orderOf r' = 2 := by
    rw [hr'def, show g⁻¹ * r * g = MulAut.conj g⁻¹ r by simp,
      MulEquiv.orderOf_eq]
    exact hr2
  have hCr' : centralizer ({r'} : Set X) ≤ H :=
    S.centralizer_le_of_kernel h33 h35 hT13 hML hSch hr'2 hr't
      (S.mem_coreActionKernel_of_le hT13 hML hSch (le_sup_left.trans hsup.le) hr't hr'K)
  intro c hc
  have hcr : c * r = r * c := (mem_centralizer_iff.mp hc r hrR).symm
  have h1 : g⁻¹ * c * g ∈ centralizer ({r'} : Set X) := by
    rw [mem_centralizer_singleton_iff, hr'def]
    calc g⁻¹ * c * g * (g⁻¹ * r * g) = g⁻¹ * (c * r) * g := by group
      _ = g⁻¹ * (r * c) * g := by rw [hcr]
      _ = g⁻¹ * r * g * (g⁻¹ * c * g) := by group
  have h2 := mul_mem (mul_mem hgH (hCr' h1)) (inv_mem hgH)
  rwa [show g * (g⁻¹ * c * g) * g⁻¹ = c by group] at h2

theorem isSolomonMember_of_ne {M K : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hKH : K ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hKpc : IsPComponent 2 (K.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M) (hne : K ≠ M) : FooteLit.IsSolomonMember K := by
  have hMK : M ≤ UnbalancedLayer.coreActionKernel K :=
    GSThmB.B5a.le_coreActionKernel_of_ne hKH hMH hKpc hMpc hne
  have hE1 : E ≠ ⊥ := by
    intro h
    have h4 := (card_sq_of_klein S.klein).1
    rw [h, Subgroup.card_bot] at h4
    omega
  have hNE : normalizer (E : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    normalizer_le_normalizer_signalizerCompletion_self E
  exact Sol78H.isSolomonMember_of_centralizer_le ⟨hKH, hKpc⟩ hE1 S.isPGroup
    ((S.le.trans hJM).trans hMK) (le_normalizer.trans hNE)
    ((Subgroup.centralizer_le_normalizer (E : Set X)).trans hNE)

theorem eq_of_isPComponent_alt_of_sup (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M K : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hKH : K ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hKpc : IsPComponent 2 (K.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (htM : t ∈ normalizer (M : Set X)) (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    (eM : Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin n)))
    (eK : Nonempty (K ⧸ pPrimeCore 2 K ≃* alternatingGroup (Fin n))) : K = M := by
  by_contra hne
  have hCt := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have hmM := S.isSolomonMember_of_trivial_pump hMH hMpc hCt htM hsup
  have hmK := S.isSolomonMember_of_ne hMH hMpc hKH hKpc (le_sup_left.trans hsup.le) hne
  exact hne (S.eq_of_isPComponent_alt_of_member hT13 hML hSch hKH hMH hKpc hMpc hmK hmM eK eM)

end Sig36

end CFSG.ComponentClassification.SolMax
