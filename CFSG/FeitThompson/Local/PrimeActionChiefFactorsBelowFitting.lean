module

public import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
public import CFSG.FeitThompson.Local.RankTwoSectionChiefFactorCentralization
public import CFSG.FeitThompson.Local.FittingMonoNormal
public import CFSG.FeitThompson.Local.NormalModularSubgroupIrreducibleTrivial
public import CFSG.FeitThompson.Local.PrimeCentralizerSpecialFixedLine
public import CFSG.FeitThompson.Local.NormalNilpotentCentralizesChiefFactors
public import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
public import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
public import CFSG.FeitThompson.Local.FittingModuleFaithfulAction
public import CFSG.FeitThompson.OddOrder.SemidirectReassociation
public import CFSG.FeitThompson.Representations.ZeroFixedSpacePrimeComplementCentralizes
public import CFSG.FeitThompson.Representations.PrimeComplementNoFixedVectorCentralizes

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type u} [Group G]

def fittingOfNormal [Finite G] (K : Subgroup G) : Subgroup G :=
  (fittingRaw ↥K).map K.subtype

theorem fittingOfNormal_le [Finite G] (K : Subgroup G) : fittingOfNormal K ≤ K :=
  map_subtype_le _

theorem fittingOfNormal_eq_inf [Finite G] {K : Subgroup G} (hK : K.Normal) :
    fittingOfNormal K = fittingRaw G ⊓ K := by
  rw [fittingOfNormal, fittingRaw_eq_subgroupOf_fittingRaw hK, subgroupOf_map_subtype]

theorem normal_fittingOfNormal [Finite G] {K : Subgroup G} (hK : K.Normal) :
    (fittingOfNormal K).Normal := by
  rw [fittingOfNormal_eq_inf hK]
  have := hK
  have := fittingRaw_normal G
  exact Subgroup.normal_inf_normal _ _

theorem isNilpotent_fittingOfNormal [Finite G] {K : Subgroup G} (hK : K.Normal) :
    Group.IsNilpotent ↥(fittingOfNormal K) := by
  refine isNilpotent_of_le_fittingRaw ?_
  rw [fittingOfNormal_eq_inf hK]
  exact inf_le_left

theorem subgroupOf_fittingOfNormal [Finite G] (K : Subgroup G) :
    (fittingOfNormal K).subgroupOf K = fittingRaw ↥K :=
  Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem natCard_map_mk'_eq_relIndex {F K : Subgroup G} [F.Normal] :
    Nat.card (K.map (mk' F)) = F.relIndex K := by
  have hker : ((mk' F).comp K.subtype).ker = F.subgroupOf K := by
    ext x
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : ((mk' F).comp K.subtype).range = K.map (mk' F) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h := Nat.card_congr (QuotientGroup.quotientKerEquivRange ((mk' F).comp K.subtype)).toEquiv
  rw [hker, hrange] at h
  rw [← h, ← Subgroup.index_eq_card]
  rfl

theorem relIndex_fittingOfNormal [Finite G] (K : Subgroup G) :
    (fittingOfNormal K).relIndex K = Nat.card (↥K ⧸ fittingRaw ↥K) := by
  rw [show (fittingOfNormal K).relIndex K = ((fittingOfNormal K).subgroupOf K).index from rfl,
    subgroupOf_fittingOfNormal, Subgroup.index_eq_card]

theorem commutator_le_of_eq_sup {N K P R F : Subgroup G} [N.Normal] (hK : K = P ⊔ F)
    (hFN : F ≤ N) (hPR : ⁅P, R⁆ ≤ N) : ⁅K, R⁆ ≤ N := by
  have hFbot : F.map (mk' N) = ⊥ := (Subgroup.map_eq_bot_iff _).2 (by rwa [ker_mk'])
  have h : (⁅K, R⁆ : Subgroup G).map (mk' N) = ⊥ := by
    rw [Subgroup.map_commutator, hK, Subgroup.map_sup, hFbot, sup_bot_eq,
      ← Subgroup.map_commutator]
    exact (Subgroup.map_eq_bot_iff _).2 (by rwa [ker_mk'])
  have h2 := (Subgroup.map_eq_bot_iff _).1 h
  rwa [ker_mk'] at h2

theorem sup_eq_of_isHallSubgroup_of_relIndex_eq_pow [Finite G] {K P F : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hPK : P ≤ K) (hPHall : IsHallSubgroup {p} (P.subgroupOf K)) (hFK : F ≤ K)
    {a : ℕ} (hF : F.relIndex K = p ^ a) : P ⊔ F = K := by
  set P' := P.subgroupOf K with hP'
  set F' := F.subgroupOf K with hF'
  have hidx : (P' ⊔ F').index = 1 := by
    have h1 : (P' ⊔ F').index ∣ P'.index := Subgroup.index_dvd_of_le le_sup_left
    have h2 : (P' ⊔ F').index ∣ F'.index := Subgroup.index_dvd_of_le le_sup_right
    have hF'idx : F'.index = p ^ a := hF
    have hnp : ¬ p ∣ P'.index := fun hdvd =>
      isPiNumber_iff.1 hPHall.index p
        (Nat.mem_primeFactors.2 ⟨hp, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl
    rcases (Nat.dvd_prime_pow hp).1 (hF'idx ▸ h2) with ⟨k, hk, hkeq⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hkeq, hk0, pow_zero]
    · exact absurd ((hkeq ▸ dvd_pow_self p hk0.ne').trans h1) hnp
  have htop : P' ⊔ F' = ⊤ := Subgroup.index_eq_one.1 hidx
  have h := congrArg (Subgroup.map K.subtype) htop
  rwa [Subgroup.map_sup, hP', hF', subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_eq_left.2 hPK, inf_eq_left.2 hFK, ← MonoidHom.range_eq_map, subtype_range] at h

theorem representationOfMulAut_comp {M N A W : Type*} [Monoid M] [Monoid N] [Group A]
    [AddCommGroup W] (q : ℕ) [Module (ZMod q) W] (σ : M →* MulAut A)
    (e : A ≃* Multiplicative W) (f : N →* M) :
    representationOfMulAut q (σ.comp f) e = (representationOfMulAut q σ e).comp f := by
  ext n w
  simp only [MonoidHom.coe_comp, Function.comp_apply, representationOfMulAut_apply]

theorem invariants_representationOfMulAut_eq_bot {M A W : Type*} [Monoid M] [Group A]
    [AddCommGroup W] (q : ℕ) [Module (ZMod q) W] (σ : M →* MulAut A)
    (e : A ≃* Multiplicative W) {B : Type*} [Group B] (f : B →* M)
    (h : ∀ a : A, (∀ b : B, σ (f b) a = a) → a = 1) :
    Representation.invariants ((representationOfMulAut q σ e).comp f) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
  rw [Representation.mem_invariants] at hw
  have ha : e.symm (Multiplicative.ofAdd w) = 1 := by
    refine h _ fun b => ?_
    have hb := hw b
    simp only [MonoidHom.coe_comp, Function.comp_apply, representationOfMulAut_apply] at hb
    exact e.injective (by simpa using congrArg Multiplicative.ofAdd hb)
  have h2 := congrArg (fun x => Multiplicative.toAdd (e x)) ha
  simpa using h2

theorem natCard_quotientFactor_eq_pow [Finite G] {U V : Subgroup G} [V.Normal] {q d : ℕ}
    (hq : q.Prime) (e : ↥(quotientFactor U V) ≃* Multiplicative (Fin d → ZMod q)) :
    Nat.card ↥(quotientFactor U V) = q ^ d := by
  rw [Nat.card_congr e.toEquiv]
  let _ := Fact.mk hq
  change Nat.card (Fin d → ZMod q) = q ^ d
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem dvd_natCard_of_natCard_quotientFactor [Finite G] {U V : Subgroup G} [V.Normal] {q d : ℕ}
    (hq : q.Prime) (hd : 1 ≤ d)
    (e : ↥(quotientFactor U V) ≃* Multiplicative (Fin d → ZMod q)) : q ∣ Nat.card ↥U := by
  have hdvd : Nat.card ↥(quotientFactor U V) ∣ Nat.card ↥U := by
    rw [← map_mk'_eq_quotientFactor U V]
    exact Subgroup.card_map_dvd U _
  exact dvd_trans ((natCard_quotientFactor_eq_pow hq e) ▸ dvd_pow_self q (by omega)) hdvd

theorem quotientFactor_eq_one_of_forall_conj_eq [Finite G] {U V R : Subgroup G} [U.Normal]
    [V.Normal] [Group.IsSolvable ↥U] [Group.IsSolvable ↥R]
    (hcop : (Nat.card ↥R).Coprime (Nat.card ↥U))
    (hbot : U ⊓ centralizer (R : Set G) = ⊥) {a : ↥(quotientFactor U V)}
    (ha : ∀ r ∈ R, quotientFactorConj U V r a = a) : a = 1 := by
  have ha2 : (a : G ⧸ V) ∈ U.map (mk' V) := by
    rw [map_mk'_eq_quotientFactor]; exact a.2
  have hmem : (a : G ⧸ V) ∈ U.map (mk' V) ⊓
      centralizer ((R.map (mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) := by
    refine mem_inf_centralizer_map_mk'_iff.2 ⟨ha2, fun r hr => ?_⟩
    have h := congrArg (fun x : ↥(quotientFactor U V) => (x : G ⧸ V)) (ha r hr)
    simpa using h
  rw [inf_centralizer_map_mk'_eq_map hcop (le_normalizer_of_normal (H := U)), hbot,
    Subgroup.map_bot, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem le_ker_quotientFactorConj_of_isIrreducible_same_char [Finite G]
    {K F U V : Subgroup G} [K.Normal] [F.Normal] [U.Normal] [V.Normal]
    {p a : ℕ} (hp : p.Prime) (hKFcard : F.relIndex K = p ^ a) (hFU : ⁅F, U⁆ ≤ V)
    {d : ℕ} (e : ↥(quotientFactor U V) ≃* Multiplicative (Fin d → ZMod p))
    (hirr : letI := Fact.mk hp
      (representationOfMulAut p (quotientFactorConjAut U V hFU) e).IsIrreducible) :
    K ≤ (quotientFactorConj U V).ker := by
  let _ := Fact.mk hp
  have hKcard : Nat.card ↥(K.map (mk' F)) = p ^ a := by
    rw [natCard_map_mk'_eq_relIndex, hKFcard]
  have hker := le_ker_of_isIrreducible (U := K.map (mk' F)) hKcard hirr
  intro k hk
  rw [MonoidHom.mem_ker]
  have h2 := hker (show (k : G ⧸ F) ∈ K.map (mk' F) from ⟨k, hk, rfl⟩)
  rw [MonoidHom.mem_ker] at h2
  rw [← quotientFactorConjAut_mk U V hFU k, ← representationOfMulAut_eq_one_iff p _ e]
  exact h2

theorem commutator_le_ker_quotientFactorConj [Finite G] [Group.IsSolvable G]
    {U V P R : Subgroup G} [U.Normal] [V.Normal] (hodd : Odd (Nat.card G))
    (hRP : R ≤ normalizer (P : Set G)) (hdisj : P ⊓ R = ⊥)
    (hRprime : (Nat.card ↥R).Prime) (hcopPR : (Nat.card ↥P).Coprime (Nat.card ↥R))
    {q d : ℕ} (hq : q.Prime) (hqPR : ¬ q ∣ Nat.card ↥(P ⊔ R))
    (e : ↥(quotientFactor U V) ≃* Multiplicative (Fin d → ZMod q))
    (hCV : letI := Fact.mk hq
      Representation.invariants
        ((representationOfMulAut q (quotientFactorConj U V) e).comp
          ((P ⊔ R : Subgroup G).subtype.comp (R.subgroupOf (P ⊔ R)).subtype)) = ⊥) :
    ⁅P, R⁆ ≤ (quotientFactorConj U V).ker := by
  let _ := Fact.mk hq
  set X : Subgroup G := P ⊔ R with hX
  have hPnormal : (P.subgroupOf X).Normal := by
    rw [hX, Subgroup.normal_subgroupOf_iff le_sup_left]
    intro x k hx hk
    exact (mem_normalizer_iff.1 ((sup_le le_normalizer hRP) hk) x).1 hx
  have hcompl : (P.subgroupOf X).IsComplement' (R.subgroupOf X) :=
    isComplement'_subgroupOf_sup hRP (disjoint_iff.2 hdisj)
  have hcop' : (Nat.card ↥(P.subgroupOf X)).Coprime (Nat.card ↥(R.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ X)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : R ≤ X)).toEquiv]
    exact hcopPR
  have hRp' : (Nat.card ↥(R.subgroupOf X)).Prime := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : R ≤ X)).toEquiv]
    exact hRprime
  have hoddX : Odd (Nat.card ↥X) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card X)
  have hCV' : Representation.invariants
      (((representationOfMulAut q (quotientFactorConj U V) e).comp X.subtype).comp
        (R.subgroupOf X).subtype) = ⊥ := hCV
  intro y hy
  rw [MonoidHom.mem_ker]
  have hyX : y ∈ X :=
    ((Subgroup.commutator_mono (le_sup_left : P ≤ X) (le_sup_right : R ≤ X)).trans
      (Subgroup.commutator_le_self X)) hy
  have hx : (⟨y, hyX⟩ : ↥X) ∈ (⁅P.subgroupOf X, R.subgroupOf X⁆ : Subgroup ↥X) := by
    rw [commutator_subgroupOf le_sup_left le_sup_right, Subgroup.mem_subgroupOf]
    exact hy
  have h1 := eq_one_of_mem_commutator_of_invariants_eq_bot_zmod hoddX hcompl hcop' hRp' hqPR
    _ hCV' hx
  simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype] at h1
  rw [← representationOfMulAut_eq_one_iff q (quotientFactorConj U V) e y]
  exact h1

theorem commutator_commutator_le_of_isChiefFactor_le_fitting [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal] (hKR : K.IsComplement' R)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R)) (hRprime : (Nat.card ↥R).Prime)
    {p a : ℕ} (hp : p.Prime) (hKF : (fittingOfNormal K).relIndex K = p ^ a)
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥)
    {U V : Subgroup G} (hUF : U ≤ fittingOfNormal K) (hchief : IsChiefFactor U V) :
    ⁅⁅K, R⁆, U⁆ ≤ V := by
  have hUn := hchief.normal_num
  have hVn := hchief.normal_den
  set F : Subgroup G := fittingOfNormal K with hFdef
  have hFn : F.Normal := normal_fittingOfNormal ‹K.Normal›
  have hFK : F ≤ K := fittingOfNormal_le K
  have hFU : ⁅F, U⁆ ≤ V :=
    commutator_le_of_isChiefFactor hFn (isNilpotent_fittingOfNormal ‹K.Normal›) hchief
  have hUcent : U ⊓ centralizer (R : Set G) = ⊥ :=
    le_bot_iff.1 (hcent ▸ inf_le_inf_right _ hUF)
  have hcopRU : (Nat.card ↥R).Coprime (Nat.card ↥U) :=
    hcop.symm.coprime_dvd_right (Subgroup.card_dvd_of_le (hUF.trans hFK))
  obtain ⟨q, d, hq, hd, e, hirr⟩ :=
    exists_prime_mulEquiv_isIrreducible_quotient_of_isChiefFactor U V hchief hFU
  let _ := Fact.mk hq
  have hCV : ∀ {B : Type u} [Group B] (f : B →* G), (∀ r ∈ R, ∃ b : B, f b = r) →
      Representation.invariants
        ((representationOfMulAut q (quotientFactorConj U V) e).comp f) = ⊥ := by
    intro B _ f hf
    refine invariants_representationOfMulAut_eq_bot q _ e f fun z hz => ?_
    refine quotientFactor_eq_one_of_forall_conj_eq hcopRU hUcent fun r hr => ?_
    obtain ⟨b, hb⟩ := hf r hr
    rw [← hb]
    exact hz b
  by_cases hqp : q = p
  ·
    subst hqp
    refine (Subgroup.commutator_mono (Subgroup.commutator_le_left K R) le_rfl).trans ?_
    exact commutator_le_of_le_ker_quotientFactorConj U V
      (le_ker_quotientFactorConj_of_isIrreducible_same_char hq hKF hFU e hirr)
  ·
    obtain ⟨P, hPK, hPHall, hRP⟩ :=
      exists_isHallSubgroup_singleton_le_normalizer hKR.sup_eq_top hcop p
    have hKPF : P ⊔ F = K := sup_eq_of_isHallSubgroup_of_relIndex_eq_pow hp hPK hPHall hFK hKF
    have hdisj : P ⊓ R = ⊥ := disjoint_iff.1 (hKR.disjoint.mono_left hPK)
    have hcopPR : (Nat.card ↥P).Coprime (Nat.card ↥R) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hPK)
    have hqK : q ∣ Nat.card ↥K :=
      (dvd_natCard_of_natCard_quotientFactor hq hd e).trans
        (Subgroup.card_dvd_of_le (hUF.trans hFK))
    have hPcard : Nat.card ↥P = Nat.card ↥(P.subgroupOf K) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv).symm
    have hqPR : ¬ q ∣ Nat.card ↥(P ⊔ R) := by
      have hqP : ¬ q ∣ Nat.card ↥P := fun hdvd => hqp (by
        have h := isPiNumber_iff.1 hPHall.natCard q
          (Nat.mem_primeFactors.2 ⟨hq, hPcard ▸ hdvd, Nat.card_pos.ne'⟩)
        simpa using h)
      have hqR : ¬ q ∣ Nat.card ↥R := fun hdvd =>
        hq.one_lt.ne' (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hqK hdvd))
      rw [natCard_sup_eq_mul_of_le_normalizer hRP hdisj]
      exact fun hdvd => ((Nat.Prime.dvd_mul hq).1 hdvd).elim hqP hqR
    have hPRker : ⁅P, R⁆ ≤ (quotientFactorConj U V).ker :=
      commutator_le_ker_quotientFactorConj hodd hRP hdisj hRprime hcopPR hq hqPR e
        (hCV ((P ⊔ R : Subgroup G).subtype.comp (R.subgroupOf (P ⊔ R)).subtype)
          fun r hr => ⟨⟨⟨r, (le_sup_right : R ≤ P ⊔ R) hr⟩,
            by simpa [Subgroup.mem_subgroupOf] using hr⟩, rfl⟩)
    have hFker : F ≤ (quotientFactorConj U V).ker := le_ker_quotientFactorConj U V hFU
    exact commutator_le_of_le_ker_quotientFactorConj U V
      (commutator_le_of_eq_sup (N := (quotientFactorConj U V).ker) hKPF.symm hFker hPRker)

theorem commutator_commutator_le_of_isChiefFactor_le_fitting_of_natCard_quotient [Finite G]
    [Group.IsSolvable G] (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R) (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R))
    (hRprime : (Nat.card ↥R).Prime) {p a : ℕ} (hp : p.Prime)
    (hKF : Nat.card (↥K ⧸ fittingRaw ↥K) = p ^ a)
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥)
    {U V : Subgroup G} (hUF : U ≤ fittingOfNormal K) (hchief : IsChiefFactor U V) :
    ⁅⁅K, R⁆, U⁆ ≤ V :=
  commutator_commutator_le_of_isChiefFactor_le_fitting hodd hKR hcop hRprime hp
    ((relIndex_fittingOfNormal K).trans hKF) hcent hUF hchief

theorem inv_mul_inv_mul_mul_mem_of_isChiefFactor_le_fitting [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal] (hKR : K.IsComplement' R)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R)) (hRprime : (Nat.card ↥R).Prime)
    {p a : ℕ} (hp : p.Prime) (hKF : (fittingOfNormal K).relIndex K = p ^ a)
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥)
    {U V : Subgroup G} (hUF : U ≤ fittingOfNormal K) (hchief : IsChiefFactor U V)
    {x u : G} (hx : x ∈ (⁅K, R⁆ : Subgroup G)) (hu : u ∈ U) : x⁻¹ * u⁻¹ * x * u ∈ V := by
  have hmem := Subgroup.commutator_mem_commutator
    ((⁅K, R⁆ : Subgroup G).inv_mem hx) (U.inv_mem hu)
  rw [commutatorElement_def, inv_inv, inv_inv] at hmem
  exact commutator_commutator_le_of_isChiefFactor_le_fitting hodd hKR hcop hRprime hp hKF hcent
    hUF hchief hmem

end CFSG.FeitThompson
