module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldExport
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldExport
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial

section Transport

theorem isLpType_of_mulEquiv {p Q : ℕ} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLpType p Q Y) : IsLpType p Q X := by
  obtain ⟨F, hF, hFin, hc, ⟨f⟩⟩ := h
  exact ⟨F, hF, hFin, hc, ⟨e.trans f⟩⟩

noncomputable def centerQuotCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem fixSubgroup_congr_eq_map {S T : Type*} [Group S] [Group T] (e : S ≃* T) (α : MulAut S) :
    fixSubgroup (MulAut.congr e α) = (fixSubgroup α).map (e : S →* T) := by
  ext x
  rw [mem_fixSubgroup]
  refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
  rw [mem_fixSubgroup]
  show e (α (e.symm x)) = x ↔ α (e.symm x) = e.symm x
  exact e.eq_symm_apply.symm

theorem isComponentOf_map_congr {S T : Type*} [Group S] [Group T] (e : S ≃* T) {α : MulAut S}
    {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup α)) :
    IsComponentOf (K.map (e : S →* T)) (fixSubgroup (MulAut.congr e α)) := by
  rw [fixSubgroup_congr_eq_map]
  exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK

theorem isLpType_center_map {p Q : ℕ} {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    {K : Subgroup S} (h : IsLpType p Q (↥K ⧸ Subgroup.center ↥K)) :
    IsLpType p Q (↥(K.map (e : S →* T)) ⧸ Subgroup.center ↥(K.map (e : S →* T))) :=
  isLpType_of_mulEquiv (centerQuotCongr (K.equivMapOfInjective (e : S →* T) e.injective)).symm h

theorem congr_self_eq {P : Type*} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

end Transport

section Orders

open CFSG.OrderReductions.LinearOrders

theorem card_of_isLpType_three_three {T : Type*} [Group T] (h : IsLpType 3 3 T) :
    Nat.card T = 5616 := by
  obtain ⟨F, hF, hFin, hc, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).toEquiv,
    card_projectiveSpecialLinear F 3 (by norm_num), hc]
  decide

theorem exists_card_eq_three_pow {E : Type*} [Field E] [Finite E] (hE : ringChar E = 3) :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card E = 3 ^ f := by
  haveI : Fintype E := Fintype.ofFinite E
  haveI : CharP E 3 := ringChar.of_eq hE
  obtain ⟨n, -, hn⟩ := FiniteField.card E 3
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem sl_l33 {E : Type*} [Field E] [Finite E] (hE : ringChar E = 3) {m : ℕ} (hm : 2 ≤ m)
    {K : Type*} [Group K] (f : Matrix.SpecialLinearGroup (Fin m) E →* K)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center _)
    (hL : IsLpType 3 3 (K ⧸ Subgroup.center K)) : m = 3 ∧ Nat.card E = 3 := by
  obtain ⟨a, ha, hEa⟩ := exists_card_eq_three_pow hE
  have hKZ := card_of_isLpType_three_three hL
  have hSL := card_specialLinear E m (by omega)
  have hZ := card_specialLinear_center E m (by omega)
  haveI : Finite K := Finite.of_surjective f hf
  have hSL2 : m = 2 → Nat.card (Matrix.SpecialLinearGroup (Fin m) E) =
      Nat.card E * (Nat.card E ^ 2 - 1) := by
    rintro rfl
    rw [hSL]
    simp
  have hperf : 3 ≤ m ∨ 4 ≤ Nat.card E := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hm3, hE4⟩ := hcon
    obtain rfl : m = 2 := by omega
    have hE3 : Nat.card E = 3 := by
      have : 3 ≤ 3 ^ a := Nat.le_self_pow (by omega) 3
      omega
    have h1 : Nat.card K ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) E) :=
      Nat.card_le_card_of_surjective f hf
    have h2 : Nat.card (K ⧸ Subgroup.center K) ≤ Nat.card K :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    rw [hSL2 rfl, hE3] at h1
    rw [hKZ] at h2
    norm_num at h1
    omega
  have hq := CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hm hperf
  have hcomm : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ := hq.1.commutator_eq_top
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv hcomm f hf
      hker
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin m) E) =
      5616 * Nat.gcd m (Nat.card E - 1) := by
    rw [(Subgroup.center
        (Matrix.SpecialLinearGroup (Fin m) E)).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr e.toEquiv, hKZ, hZ]
  have hdvd : 3 ^ (a * (m * (m - 1) / 2)) ∣ 5616 * Nat.gcd m (Nat.card E - 1) := by
    rw [← hcard, hSL, hEa, ← pow_mul]
    exact Dvd.intro _ rfl
  have hcop : Nat.Coprime (3 ^ (a * (m * (m - 1) / 2))) (Nat.gcd m (Nat.card E - 1)) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    have h3' : 3 ∣ Nat.card E - 1 := h3.trans (Nat.gcd_dvd_right _ _)
    have h3E : 3 ∣ Nat.card E := by rw [hEa]; exact dvd_pow_self 3 (by omega)
    have hE1 : 1 ≤ Nat.card E := Nat.card_pos
    omega
  have h5616 : 3 ^ (a * (m * (m - 1) / 2)) ∣ 5616 := hcop.dvd_of_dvd_mul_right hdvd
  have hle : a * (m * (m - 1) / 2) ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h81 : 3 ^ 4 ∣ 5616 := (pow_dvd_pow 3 hlt).trans h5616
    omega
  have hm3 : m ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hlt (by omega)
    have h6 : 6 ≤ m * (m - 1) / 2 := by omega
    have : 1 * 6 ≤ a * (m * (m - 1) / 2) := Nat.mul_le_mul ha h6
    omega
  rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
  · exfalso
    have ha3 : a ≤ 3 := by
      norm_num at hle
      exact hle
    have hgcd : Nat.gcd 2 (Nat.card E - 1) = 2 := by
      rw [hEa]
      apply Nat.gcd_eq_left
      have hodd : Odd (3 ^ a) := Odd.pow (by decide)
      obtain ⟨t, ht⟩ := hodd
      exact ⟨t, by omega⟩
    rw [hSL2 rfl, hgcd, hEa] at hcard
    interval_cases a <;> norm_num at hcard
  · refine ⟨rfl, ?_⟩
    norm_num at hle
    have : a = 1 := by omega
    rw [hEa, this, pow_one]

end Orders

section Cases

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem exists_card_eq_pow_ringChar {K : Type} [Field K] [Finite K] :
    ∃ f : ℕ, 1 ≤ f ∧ (ringChar K).Prime ∧ Nat.card K = ringChar K ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨f, hℓ, hK⟩ := FiniteField.card K (ringChar K)
  exact ⟨f, f.pos, hℓ, by rw [Nat.card_eq_fintype_card, hK]⟩

theorem linear_cases_of_three_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (β : MulAut (LinearFlag.projectiveSL n K)) (hβ : β ^ p = 1) :
    (∃ (A : GL (Fin n) K) (c : Kˣ), A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
      β = LinearFlag.conjAut n K A) ∨
    (∃ (h : MulAut (LinearFlag.projectiveSL n K)) (σ : K ≃+* K), orderOf σ = p ∧
      β = h * LinearFlag.fieldAut n K σ * h⁻¹) := by
  obtain ⟨f, hf, hℓ, hK⟩ := exists_card_eq_pow_ringChar (K := K)
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
    hℓ hf hn hK
  by_cases hlin : β ∈ LinearFlag.linearAutGroup n K
  · left
    have hrange : LinearFlag.linearAutGroup n K = (LinearFlag.conjAut n K).range := by
      rw [LinearFlag.linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rw [hrange] at hlin
    obtain ⟨A, rfl⟩ := hlin
    have hAp : A ^ p ∈ (LinearFlag.conjAut n K).ker := by rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact ⟨A, c, hc.symm, rfl⟩
  · right
    obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn
      (hp.odd_of_ne_two hp2) hβ
    have hmem : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ∈
        LinearFlag.semilinearAutGroup n K :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup
        (LinearFlag.conjAut_mem_linearAutGroup A))
        (LinearFlag.fieldAut_mem_semilinearAutGroup σ)
    have hne : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ≠ 1 := fun h =>
      hlin (h ▸ one_mem _)
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ) = p :=
      orderOf_eq_prime hβ hne
    obtain ⟨-, τ, hτ, ⟨h, -, hβτ⟩, -⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.linear_prime_descent_char hℓ hf hn hK hp
        hmem hlin hord
    exact ⟨h, τ, hτ, hβτ⟩

theorem linear_cases_two {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (β : MulAut (LinearFlag.projectiveSL 2 K)) (hβ : β ^ p = 1) :
    (∃ (A : GL (Fin 2) K) (c : Kˣ), A ^ p = Matrix.GeneralLinearGroup.scalar (Fin 2) c ∧
      β = LinearFlag.conjAut 2 K A) ∨
    (∃ (h : MulAut (LinearFlag.projectiveSL 2 K)) (σ : K ≃+* K), orderOf σ = p ∧
      β = h * LinearFlag.fieldAut 2 K σ * h⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨β₀, hββ₀⟩ : ∃ β₀ : MulAut (PSL2 K), MulAut.congr (psl2Equiv K) β₀ = β :=
    ⟨(MulAut.congr (psl2Equiv K)).symm β, (MulAut.congr (psl2Equiv K)).apply_symm_apply β⟩
  have hβ₀p : β₀ ^ p = 1 :=
    (MulAut.congr (psl2Equiv K)).injective (by rw [map_pow, hββ₀, hβ, map_one])
  by_cases hD : β₀ ∈ (pglAction K).range
  · left
    obtain ⟨g, hg⟩ := hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβA : β = LinearFlag.conjAut 2 K A := by
      rw [← hββ₀, ← hg]
      exact congr_pglAction_mk A
    have hAp : A ^ p ∈ Subgroup.center (GL (Fin 2) K) := by
      have h1 : pglAction K (Matrix.ProjGenLinGroup.mk (A ^ p)) = pglAction K 1 := by
        rw [map_pow, map_pow, hg, hβ₀p, map_one]
      exact Matrix.ProjGenLinGroup.mk_eq_one.1
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K h1)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact ⟨A, c, hc.symm, hβA⟩
  · right
    have hne : β₀ ≠ 1 := fun h => hD ⟨1, by rw [map_one, h]⟩
    have hord : orderOf β₀ = p := orderOf_eq_prime hβ₀p hne
    obtain ⟨σ, hσ, g, hgσ⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent hp β₀ hord hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hcongr : MulAut.congr (psl2Equiv K)
        (pglAction K (Matrix.ProjGenLinGroup.mk A)) = LinearFlag.conjAut 2 K A :=
      congr_pglAction_mk A
    refine ⟨LinearFlag.conjAut 2 K A, σ, hσ, ?_⟩
    rw [← hββ₀, hgσ, map_mul, map_mul, map_inv, hcongr, congr_psl2FieldAut]

end Cases

section Components

open Polynomial CFSG.RankThree.PartOne.KCPrimary
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem exists_surjective_ker_le_center_map_proj {n : ℕ} {k : Type} [Field k] {G : Type*}
    [Group G] {S : Subgroup (Matrix.SpecialLinearGroup (Fin n) k)} (e : G ≃* S) :
    ∃ f : G →* ↥(S.map (LinearFlag.proj n k)), Function.Surjective f ∧
      f.ker ≤ Subgroup.center G := by
  refine ⟨((LinearFlag.proj n k).subgroupMap S).comp e.toMonoidHom,
    (MonoidHom.subgroupMap_surjective _ S).comp e.surjective, fun g hg => ?_⟩
  have h1 : LinearFlag.proj n k (e g : Matrix.SpecialLinearGroup (Fin n) k) = 1 :=
    congrArg Subtype.val hg
  have h2 : (e g : Matrix.SpecialLinearGroup (Fin n) k) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) :=
    LinearFlag.scalars_le_center n k (LinearFlag.proj_eq_one_iff.1 h1)
  rw [Subgroup.mem_center_iff]
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (e y))

theorem linear_inner_l33_false {n : ℕ} {k : Type} [Field k] [Finite k] (hk : ringChar k = 3)
    (hk9 : 9 ≤ Nat.card k) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ 13 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.conjAut n k A)))
    (hL : IsLpType 3 3 (↥K ⧸ Subgroup.center ↥K)) : False := by
  have hpk : ((13 : ℕ) : k) ≠ 0 := by
    rw [Ne, ringChar.spec, hk]
    decide
  obtain ⟨h, rfl⟩ := linear_inner_components hpk hA K hK
  have hsq := squarefree_minpoly_glA hpk hA
  haveI : Fact (Irreducible h.1.1) := ⟨irreducible_of_mem_primaryFactors h.1.2⟩
  haveI : Finite (AdjoinRoot h.1.1) := Module.finite_of_finite k
  obtain ⟨e⟩ := nonempty_mulEquiv_specialFactor hsq h.1.2
  obtain ⟨f, hf, hker⟩ := exists_surjective_ker_le_center_map_proj e
  have hm : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1 := by
    rcases h.2 with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  have hE : ringChar (AdjoinRoot h.1.1) = 3 := by
    rw [← Algebra.ringChar_eq k (AdjoinRoot h.1.1), hk]
  obtain ⟨-, hE3⟩ := sl_l33 hE hm f hf hker hL
  have hle : Nat.card k ≤ Nat.card (AdjoinRoot h.1.1) :=
    Nat.card_le_card_of_injective (algebraMap k (AdjoinRoot h.1.1))
      (algebraMap k (AdjoinRoot h.1.1)).injective
  omega

theorem linear_field_l33 {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k]
    (hk : ringChar k = 3) (σ : k ≃+* k) (hσ : orderOf σ = 13)
    (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.fieldAut n k σ)))
    (hL : IsLpType 3 3 (↥K ⧸ Subgroup.center ↥K)) : n = 3 ∧ Nat.card k = 3 ^ 13 := by
  obtain ⟨-, f, hf, hker⟩ := linearFieldAut_components hn σ K hK
  have hE : ringChar (CFSG.GH74.GLS.IVK.fixedField σ) = 3 := by
    rw [Algebra.ringChar_eq (CFSG.GH74.GLS.IVK.fixedField σ) k, hk]
  obtain ⟨hn3, hE3⟩ := sl_l33 hE hn f hf hker hL
  refine ⟨hn3, ?_⟩
  rw [← CFSG.GH74.GLS.IVK.fixedField_card_pow σ, hE3, hσ]

end Components

section Linear

noncomputable def projSLEquivStated (n : ℕ) (k : Type) [Field k] :
    LinearFlag.projectiveSL n k ≃* StatedProj (StatedSL n k) :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n k)

theorem linear_l33 {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq3 : q.p = 3) (hne : q.card ≠ 3)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group))
    {α : MulAut S} (hα : α ^ 13 = 1) {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup α))
    (hL : IsLpType 3 3 (↥K ⧸ Subgroup.center ↥K)) : IsLpType 3 (3 ^ 13) S := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨e⟩ := he
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hchar : ringChar (GaloisField q.p q.exponent) = 3 := by
    rw [ringChar.eq (GaloisField q.p q.exponent) q.p, hq3]
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hk9 : 9 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcard, TauCeti.PrimePower.card_def, hq3]
    have h1 : q.exponent ≠ 1 := by
      intro h1
      apply hne
      rw [TauCeti.PrimePower.card_def, hq3, h1, pow_one]
    have h2 : 2 ≤ q.exponent := by have := q.exponent_pos; omega
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
  have hβ' : MulAut.congr e' α ^ 13 = 1 := by rw [← map_pow, hα, map_one]
  have hK' := isComponentOf_map_congr e' hK
  have hL' := isLpType_center_map e' hL
  have hcases := (Nat.lt_or_ge r 2).elim
    (fun hr2 => by
      obtain rfl : r = 1 := by omega
      exact linear_cases_two (by norm_num) (MulAut.congr e' α) hβ')
    (fun hr2 => linear_cases_of_three_le (by norm_num) (by norm_num) (by omega)
      (MulAut.congr e' α) hβ')
  rcases hcases with ⟨A, c, hA, hβA⟩ | ⟨h, σ, hσ, hβh⟩
  · rw [hβA] at hK'
    exact (linear_inner_l33_false hchar hk9 hA _ hK' hL').elim
  · have hβφ : MulAut.congr (h⁻¹ : MulAut _) (MulAut.congr e' α) =
        LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ := by
      rw [congr_self_eq, hβh]
      group
    have hK'' := isComponentOf_map_congr (h⁻¹ : MulAut _) hK'
    rw [hβφ] at hK''
    have hL'' := isLpType_center_map (h⁻¹ : MulAut _) hL'
    obtain ⟨hn3, hk⟩ := linear_field_l33 (by omega) hchar σ hσ _ hK'' hL''
    obtain rfl : r = 2 := by omega
    exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hk,
      ⟨e'.trans (projSLEquivStated 3 _)⟩⟩

end Linear

section UnitaryFamily

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

section SUOrder

theorem ker_comp_mulEquiv_le_center {X Y T : Type*} [Group X] [Group Y] [Group T] (e : X ≃* Y)
    (g : Y →* T) (h : g.ker ≤ Subgroup.center Y) :
    (g.comp e.toMonoidHom).ker ≤ Subgroup.center X := by
  intro x hx
  have h1 : e x ∈ Subgroup.center Y := h hx
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact h1 (e y)

theorem su_l33_false {E : Type} [Field E] {ℓ e m : ℕ} (hE : UnitaryFieldData ℓ e E)
    (hℓ3 : ℓ = 3) (hm : 3 ≤ m) {T : Type*} [Group T]
    (g : ↥(StatedSU m (ℓ ^ e) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center _) (hL : IsLpType 3 3 (T ⧸ Subgroup.center T)) : False := by
  haveI := hE.finite
  haveI : Fact ℓ.Prime := ⟨hE.prime⟩
  have he : 1 ≤ e := hE.one_le
  have hF : Nat.card E = (ℓ ^ e) ^ 2 := by rw [hE.card, ← pow_mul, mul_comm]
  have hnq : (m, ℓ ^ e) ≠ (3, 2) := by
    intro h32
    have h2 := congrArg Prod.snd h32
    simp only at h2
    rw [hℓ3] at h2
    have : 3 ≤ 3 ^ e := Nat.le_self_pow (by omega) 3
    omega
  obtain ⟨hqs, hcen⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF hm hnq
  have hcomm : commutator ↥(StatedSU m (ℓ ^ e) E) = ⊤ := hqs.1.commutator_eq_top
  obtain ⟨eq⟩ := nonempty_centralQuotient_mulEquiv hcomm g hg hker
  have hKZ := card_of_isLpType_three_three hL
  have hZ : Nat.card ↥(Subgroup.center ↥(StatedSU m (ℓ ^ e) E)) = Nat.gcd m (ℓ ^ e + 1) := by
    have h1 := CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars hE (n := m) (by omega)
    rw [CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq hE (by omega)] at h1
    rw [hcen]
    exact h1
  have hcard : Nat.card ↥(StatedSU m (ℓ ^ e) E) = 5616 * Nat.gcd m (ℓ ^ e + 1) := by
    rw [(Subgroup.center ↥(StatedSU m (ℓ ^ e) E)).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr eq.toEquiv, hKZ, hZ]
  have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hE (n := m) (by omega)
  subst hℓ3
  have hdvdZ : ((3 ^ (e * (m * (m - 1) / 2)) : ℕ) : ℤ) ∣
      (Nat.card ↥(StatedSU m (3 ^ e) E) : ℤ) := by
    rw [hint, pow_mul]
    push_cast
    exact Dvd.intro _ rfl
  have hdvd : 3 ^ (e * (m * (m - 1) / 2)) ∣ 5616 * Nat.gcd m (3 ^ e + 1) := by
    rw [← hcard]
    exact Int.natCast_dvd_natCast.mp hdvdZ
  have hcop : Nat.Coprime (3 ^ (e * (m * (m - 1) / 2))) (Nat.gcd m (3 ^ e + 1)) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    have h3' : 3 ∣ 3 ^ e + 1 := h3.trans (Nat.gcd_dvd_right _ _)
    have h3e : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
    omega
  have h5616 : 3 ^ (e * (m * (m - 1) / 2)) ∣ 5616 := hcop.dvd_of_dvd_mul_right hdvd
  have hle : e * (m * (m - 1) / 2) ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h81 : 3 ^ 4 ∣ 5616 := (pow_dvd_pow 3 hlt).trans h5616
    omega
  have h6 : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  have hN3 : 3 ≤ m * (m - 1) / 2 := by omega
  have he1 : e = 1 := by
    have : e * 3 ≤ e * (m * (m - 1) / 2) := Nat.mul_le_mul_left e hN3
    omega
  have hm3 : m = 3 := by
    by_contra hne
    have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have : 6 ≤ m * (m - 1) / 2 := by omega
    rw [he1] at hle
    omega
  subst he1 hm3
  have h6048 : (Nat.card ↥(StatedSU 3 (3 ^ 1) E) : ℤ) = 6048 := by
    rw [hint]
    decide
  rw [hcard] at h6048
  norm_num at h6048

end SUOrder

section Helpers

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Open

section Abstract

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

private theorem finite_gl_of_unitaryFieldData (hK : UnitaryFieldData ℓ f K) :
    Finite (LinearMap.GeneralLinearGroup K V) := by
  have := hK.finite
  have : Finite V := Module.finite_of_finite K
  have : Finite (Module.End K V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[K] V))
  exact Finite.of_injective _ Units.val_injective

private theorem specialBlockFacts_of_mult_le_one (hq : 2 ≤ ℓ ^ f)
    (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (hm : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1) : SpecialBlockFacts B x a := by
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact specialBlockFacts_of_selfDual hq a hself (selfDualPrimaryBlock H a hself)
      (fun h2 => absurd hm (by omega))
  · exact specialBlockFacts_of_paired hq a (pairedPrimaryBlock H a (Ne.symm hself))

private theorem isSolvable_orbitFactor_of_not_good (hq : 2 ≤ ℓ ^ f)
    (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (ha : ¬ IsGoodBlock hK x a) : Group.IsSolvable ↥(orbitFactor B x (a : K[X])) := by
  have := finite_gl_of_unitaryFieldData (V := V) hK
  by_cases hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])
  · have hself : dualPoly hK.bar (a : K[X]) = a := by
      by_contra hne
      exact ha ⟨hm, fun h => absurd h hne⟩
    have hbad : (primaryMultiplicity (x : Module.End K V) (a : K[X]),
        ℓ ^ (f * (a : K[X]).natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
      by_contra hnot
      exact ha ⟨hm, fun _ => hnot⟩
    obtain ⟨h1, h2, h3⟩ := card_orbitFactor_exceptional H a hself
    apply isSolvable_of_card_primeFactors_le_two
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hbad
    rcases hbad with ⟨hm', hQ⟩ | ⟨hm', hQ⟩ | ⟨hm', hQ⟩
    · rw [h1 hm' hQ, show (18 : ℕ) = 2 * 3 ^ 2 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three,
        Nat.Prime.primeFactors Nat.prime_two]
      decide
    · rw [h2 hm' hQ, show (96 : ℕ) = 2 ^ 5 * 3 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.Prime.primeFactors Nat.prime_three]
      decide
    · rw [h3 hm' hQ, show (648 : ℕ) = 2 ^ 3 * 3 ^ 4 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      decide
  · have hm1 : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1 := by omega
    have hS := (specialBlockFacts_of_mult_le_one hq H a hm1).abelian hm1
    exact Group.isSolvable_of_comm fun g g' => Subtype.ext (hS g g.2 g' g'.2).eq

private theorem isSolvable_range_blockRestrict_of_not_good (hq : 2 ≤ ℓ ^ f)
    (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (ha : ¬ IsGoodBlock hK x a) {G : Type*} [Group G] (φ : G →* gl_centralizer x)
    (hφ : ∀ g, (φ g : LinearMap.GeneralLinearGroup K V) ∈ unitaryCentralizer B x) :
    Group.IsSolvable ↥((blockRestrict x (a : K[X])).comp φ).range := by
  have hsolv := isSolvable_orbitFactor_of_not_good hq H a ha
  let κ : ↥(orbitFactor B x (a : K[X])) →* blockGL (x : Module.End K V) (a : K[X]) :=
    (blockRestrict x (a : K[X])).comp (Subgroup.inclusion orbitFactor_le_gl_centralizer)
  have hκ : Group.IsSolvable ↥κ.range :=
    Group.isSolvable_of_surjective (f := κ.rangeRestrict) κ.rangeRestrict_surjective
  have hle : ((blockRestrict x (a : K[X])).comp φ).range ≤ κ.range := by
    rintro _ ⟨g, rfl⟩
    have hO : ∀ b ∈ primaryFactors (x : Module.End K V),
        b ∈ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) →
          dualPoly hK.bar b ∈ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) := by
      intro b hb hbO
      rcases hbO with rfl | hbO
      · exact Or.inr rfl
      · rw [Set.mem_singleton_iff] at hbO
        subst hbO
        exact Or.inl (dualPoly_dualPoly_of_mem H a.2)
    obtain ⟨gO, hgO, hgOeq⟩ := exists_component H hO (hφ g)
    refine ⟨⟨gO, hgO⟩, ?_⟩
    refine blockGL_ext fun v hv => ?_
    change ((gO : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      ((φ g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v
    exact hgOeq (a : K[X]) a.2 (Or.inl rfl) v hv
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

private theorem mem_iSup_specialBlock_of_blocks (H : UnitaryPrimaryData hK.bar B x)
    {y : LinearMap.GeneralLinearGroup K V} (hy : y ∈ unitaryCentralizer B x)
    (hdet : ∀ b : primaryFactors (x : Module.End K V),
      KCUnitary.blockDetHom x (b : K[X]) ⟨y, hy.2⟩ = 1)
    (hbad : ∀ b : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x b →
      blockRestrict x (b : K[X]) ⟨y, hy.2⟩ = 1) :
    y ∈ ⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
      specialBlock B x (a.1 : K[X]) := by
  classical
  have hsq := H.squarefree
  set M := ⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
    specialBlock B x (a.1 : K[X]) with hM
  suffices key : ∀ F : Finset K[X], ∀ (y : LinearMap.GeneralLinearGroup K V)
      (hy : y ∈ unitaryCentralizer B x),
      (∀ b : primaryFactors (x : Module.End K V),
        KCUnitary.blockDetHom x (b : K[X]) ⟨y, hy.2⟩ = 1) →
      (∀ b : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x b →
        blockRestrict x (b : K[X]) ⟨y, hy.2⟩ = 1) →
      (∀ b ∈ primaryFactors (x : Module.End K V), b ∉ F →
        ∀ v ∈ primaryComponent (x : Module.End K V) b, (y : Module.End K V) v = v) → y ∈ M by
    exact key (primaryFactors (x : Module.End K V)) y hy hdet hbad fun b hb hbn => absurd hb hbn
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro y hy _ _ h
    have : y = 1 := eq_one_of_forall_apply_eq hsq fun b hb v hv => h b hb (by simp) v hv
    rw [this]
    exact M.one_mem
  | insert b F hbF ih =>
    intro y hy hdet hbad h
    by_cases hbΦ : b ∈ primaryFactors (x : Module.End K V)
    · set O : Set K[X] := {b, dualPoly hK.bar b} with hOdef
      have hbO : b ∈ O := Or.inl rfl
      have hO : ∀ c ∈ primaryFactors (x : Module.End K V), c ∈ O → dualPoly hK.bar c ∈ O := by
        intro c hc hcO
        rcases hcO with rfl | hcO
        · exact Or.inr rfl
        · rw [Set.mem_singleton_iff] at hcO
          subst hcO
          exact Or.inl (dualPoly_dualPoly_of_mem H hbΦ)
      obtain ⟨gO, hgO, hgOeq⟩ := exists_component H hO hy
      have hgOc : gO ∈ gl_centralizer x := hgO.1.2
      have hres : ∀ c : primaryFactors (x : Module.End K V), (c : K[X]) ∈ O →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = blockRestrict x (c : K[X]) ⟨y, hy.2⟩ :=
        fun c hc => blockGL_ext fun v hv => hgOeq c c.2 hc v hv
      have hres1 : ∀ c : primaryFactors (x : Module.End K V), (c : K[X]) ∉ O →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = 1 :=
        fun c hc => blockGL_ext fun v hv => hgO.2 c c.2 hc v hv
      have hdetO : ∀ c : primaryFactors (x : Module.End K V),
          KCUnitary.blockDetHom x (c : K[X]) ⟨gO, hgOc⟩ = 1 := by
        intro c
        by_cases hc : (c : K[X]) ∈ O
        · have : KCUnitary.blockDetHom x (c : K[X]) ⟨gO, hgOc⟩ =
              KCUnitary.blockDetHom x (c : K[X]) ⟨y, hy.2⟩ := by
            simp only [KCUnitary.blockDetHom, MonoidHom.comp_apply]
            rw [hres c hc]
          rw [this]
          exact hdet c
        · simp only [KCUnitary.blockDetHom, MonoidHom.comp_apply]
          rw [hres1 c hc, map_one]
      have hbadO : ∀ c : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x c →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = 1 := by
        intro c hcb
        by_cases hc : (c : K[X]) ∈ O
        · rw [hres c hc]
          exact hbad c hcb
        · exact hres1 c hc
      have hgOM : gO ∈ M := by
        by_cases hgood : IsGoodBlock hK x ⟨b, hbΦ⟩
        · refine Subgroup.mem_iSup_of_mem
            (⟨⟨b, hbΦ⟩, hgood⟩ : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a})
            (mem_specialBlock.mpr ⟨hgO, hgOc, hdetO ⟨b, hbΦ⟩⟩)
        · have h1 : gO = 1 := by
            refine eq_one_of_paired H hbΦ hgO fun v hv => ?_
            have := congrArg (fun γ : blockGL (x : Module.End K V) b => blockApply γ v hv)
              (hbadO ⟨b, hbΦ⟩ hgood)
            exact this
          rw [h1]
          exact M.one_mem
      have hy' : gO⁻¹ * y ∈ unitaryCentralizer B x := mul_mem (inv_mem hgO.1) hy
      have hdet' : ∀ c : primaryFactors (x : Module.End K V),
          KCUnitary.blockDetHom x (c : K[X]) ⟨gO⁻¹ * y, hy'.2⟩ = 1 := by
        intro c
        have : (⟨gO⁻¹ * y, hy'.2⟩ : gl_centralizer x) = ⟨gO, hgOc⟩⁻¹ * ⟨y, hy.2⟩ := rfl
        rw [this, map_mul, map_inv, hdetO c, hdet c, inv_one, mul_one]
      have hbad' : ∀ c : primaryFactors (x : Module.End K V), ¬ IsGoodBlock hK x c →
          blockRestrict x (c : K[X]) ⟨gO⁻¹ * y, hy'.2⟩ = 1 := by
        intro c hcb
        have : (⟨gO⁻¹ * y, hy'.2⟩ : gl_centralizer x) = ⟨gO, hgOc⟩⁻¹ * ⟨y, hy.2⟩ := rfl
        rw [this, map_mul, map_inv, hbadO c hcb, hbad c hcb, inv_one, mul_one]
      have hinv : ∀ u, ((gO⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          ((gO : Module.End K V) u) = u := fun u => by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
        rfl
      have h' : ∀ c ∈ primaryFactors (x : Module.End K V), c ∉ F →
          ∀ v ∈ primaryComponent (x : Module.End K V) c,
          ((gO⁻¹ * y : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
        intro c hc hcF v hv
        by_cases hcO : c ∈ O
        · rw [Units.val_mul, Module.End.mul_apply, ← hgOeq c hc hcO v hv, hinv]
        · have hgo : (gO : Module.End K V) v = v := hgO.2 c hc hcO v hv
          have hcb : c ∉ insert b F := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨fun h => hcO (h ▸ hbO), hcF⟩
          rw [Units.val_mul, Module.End.mul_apply, h c hc hcb v hv, ← hgo, hinv, hgo]
      have hrest := ih _ hy' hdet' hbad' h'
      have hg_eq : y = gO * (gO⁻¹ * y) := by simp
      rw [hg_eq]
      exact M.mul_mem hgOM hrest
    · refine ih y hy hdet hbad fun c hc hcF v hv => h c hc ?_ v hv
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hbΦ (h ▸ hc), hcF⟩

end Abstract

section Concrete

variable {ℓ f : ℕ} {K : Type} [Field K]

private theorem isSolvable_pi_of_finite_index {ι : Type*} [Finite ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, Group.IsSolvable (G i)] : Group.IsSolvable (∀ i, G i) := by
  cases nonempty_fintype ι
  have hle : ∀ m : ℕ, derivedSeries (∀ i, G i) m ≤
      Subgroup.pi Set.univ (fun i => derivedSeries (G i) m) := by
    intro m
    induction m with
    | zero =>
      simp only [derivedSeries_zero]
      rw [Subgroup.pi_top]
    | succ m ih =>
      rw [derivedSeries_succ]
      calc ⁅derivedSeries (∀ i, G i) m, derivedSeries (∀ i, G i) m⁆
          ≤ ⁅Subgroup.pi Set.univ (fun i => derivedSeries (G i) m),
              Subgroup.pi Set.univ (fun i => derivedSeries (G i) m)⁆ :=
            Subgroup.commutator_mono ih ih
        _ ≤ Subgroup.pi Set.univ (fun i => ⁅derivedSeries (G i) m, derivedSeries (G i) m⁆) :=
            Subgroup.commutator_pi_pi_le _ _
        _ = Subgroup.pi Set.univ (fun i => derivedSeries (G i) (m + 1)) := by
            simp_rw [derivedSeries_succ]
  choose d hd using fun i => (inferInstance : Group.IsSolvable (G i)).solvable
  refine ⟨⟨Finset.univ.sup d, ?_⟩⟩
  rw [eq_bot_iff]
  refine (hle _).trans ?_
  rw [le_bot_iff, Subgroup.pi_eq_bot_iff]
  intro i
  rw [eq_bot_iff, ← hd i]
  exact derivedSeries_antitone (G i) (Finset.le_sup (f := d) (Finset.mem_univ i))

private theorem squarefree_minpoly_toLin_of_pow_scalar {n p : ℕ} (hpK : (p : K) ≠ 0)
    {a : GL (Fin n) K} {c : Kˣ} (hap : a ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K ((Matrix.GeneralLinearGroup.toLin a :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))) := by
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - C (c : K))
    (Polynomial.separable_X_pow_sub_C (c : K) hpK c.ne_zero).squarefree ?_
  have h1 : ((Matrix.GeneralLinearGroup.toLin a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) := rfl
  rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val,
    hap]
  ext v i
  by_cases hi : i = v <;> simp [hi]

private theorem primaryData_toLin' {n : ℕ} (h : UnitaryFieldData ℓ f K) {P : GL (Fin n) K}
    (hP : P ∈ primeFormUnitary h (idGram K n)) {c : Kˣ} {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hap : P ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    UnitaryPrimaryData h.bar (idForm h n) (Matrix.GeneralLinearGroup.toLin P) := by
  have : CharP K ℓ := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm
  have hsq := squarefree_minpoly_toLin_of_pow_scalar hpK hap
  have hX : ((Matrix.GeneralLinearGroup.toLin P : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (P : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  refine ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n,
    (toLin_mem_sesqUnitaryGroup_iff P).mpr hP, ?_⟩
  rw [hX]
  exact hsq

variable (h : UnitaryFieldData ℓ f K) (n : ℕ)

private noncomputable def toLinSU :
    ↥(gramSU h (idGram K n)) →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)
    ).toMonoidHom.comp (gramSU h (idGram K n)).subtype

variable {h n}

private theorem toLinSU_injective : Function.Injective (toLinSU h n) := fun _ _ e =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective e)

private theorem toLinSU_mem_sesqSpecialUnitaryGroup (g : ↥(gramSU h (idGram K n))) :
    toLinSU h n g ∈ sesqSpecialUnitaryGroup (idForm h n) :=
  (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (g : GL (Fin n) K)).mpr g.2

private theorem mem_range_toLinSU {g' : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hg' : g' ∈ sesqSpecialUnitaryGroup (idForm h n)) : g' ∈ (toLinSU h n).range := by
  have hmem : Matrix.GeneralLinearGroup.toLin.symm g' ∈ gramSU h (idGram K n) := by
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n), MulEquiv.apply_symm_apply]
    exact hg'
  exact ⟨⟨Matrix.GeneralLinearGroup.toLin.symm g', hmem⟩, by
    show Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm g') = g'
    exact MulEquiv.apply_symm_apply _ _⟩

private theorem mem_fixSubgroup_primeFormConjSU_iff (A : primeFormUnitary h (idGram K n))
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hx : x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    (g : ↥(gramSU h (idGram K n))) :
    g ∈ fixSubgroup (primeFormConjSU h (idGram K n) A) ↔ toLinSU h n g ∈ gl_centralizer x := by
  subst hx
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  have e : toLinSU h n g * Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) * toLinSU h n g ↔
      (g : GL (Fin n) K) * (A : GL (Fin n) K) = (A : GL (Fin n) K) * (g : GL (Fin n) K) := by
    change Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) *
      Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) *
          Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) ↔ _
    rw [← map_mul, ← map_mul]
    exact Matrix.GeneralLinearGroup.toLin.injective.eq_iff
  rw [e]
  constructor
  · intro hα
    have h1 : (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ = g := congrArg Subtype.val hα
    calc (g : GL (Fin n) K) * (A : GL (Fin n) K)
        = ((A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹) * (A : GL (Fin n) K) := by rw [h1]
      _ = (A : GL (Fin n) K) * g := by group
  · intro hc
    apply Subtype.ext
    change (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ = g
    rw [mul_inv_eq_iff_eq_mul]
    exact hc.symm

private theorem toLinSU_mem_unitaryCentralizer (A : primeFormUnitary h (idGram K n))
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hx : x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    {g : ↥(gramSU h (idGram K n))} (hg : g ∈ fixSubgroup (primeFormConjSU h (idGram K n) A)) :
    toLinSU h n g ∈ unitaryCentralizer (idForm h n) x :=
  Subgroup.mem_inf.mpr ⟨sesqSpecialUnitaryGroup_le _ (toLinSU_mem_sesqSpecialUnitaryGroup g),
    (mem_fixSubgroup_primeFormConjSU_iff A hx g).mp hg⟩

private theorem exists_good_block_of_component (hq : 2 ≤ ℓ ^ f)
    (A : primeFormUnitary h (idGram K n)) {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hx : x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    (H : UnitaryPrimaryData h.bar (idForm h n) x)
    (T : Subgroup (primeFormP h (idGram K n)))
    (hT : IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K n) A))) :
    ∃ a : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a},
      T = ((specialBlock (idForm h n) x (a.1 : K[X])).comap (toLinSU h n)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) := by
  classical
  haveI := h.finite
  let α : MulAut ↥(gramSU h (idGram K n)) := primeFormConjSU h (idGram K n) A
  let φ : ↥(fixSubgroup α) →* gl_centralizer x :=
    ((toLinSU h n).comp (fixSubgroup α).subtype).codRestrict (gl_centralizer x) fun g =>
      (mem_fixSubgroup_primeFormConjSU_iff A hx g.1).mp g.2
  have hφU : ∀ g, (φ g : LinearMap.GeneralLinearGroup K (Fin n → K)) ∈
      unitaryCentralizer (idForm h n) x := fun g => toLinSU_mem_unitaryCentralizer A hx g.2
  let ρ : (b : {b : primaryFactors (x : Module.End K (Fin n → K)) // ¬ IsGoodBlock h x b}) →
      ↥(fixSubgroup α) →* blockGL (x : Module.End K (Fin n → K)) (b.1 : K[X]) :=
    fun b => (blockRestrict x (b.1 : K[X])).comp φ
  haveI : ∀ b, Group.IsSolvable ↥(ρ b).range := fun b =>
    isSolvable_range_blockRestrict_of_not_good hq H b.1 b.2 φ hφU
  haveI : Group.IsSolvable ((b : {b : primaryFactors (x : Module.End K (Fin n → K)) //
      ¬ IsGoodBlock h x b}) → ↥(ρ b).range) := isSolvable_pi_of_finite_index
  haveI : Group.IsSolvable ((b : primaryFactors (x : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) := inferInstance
  let ψ : ↥(fixSubgroup α) →* ((b : primaryFactors (x : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) × ((b : {b : primaryFactors (x : Module.End K (Fin n → K)) //
      ¬ IsGoodBlock h x b}) → ↥(ρ b).range) :=
    MonoidHom.prod (MonoidHom.pi fun b => (KCUnitary.blockDetHom x (b : K[X])).comp φ)
      (MonoidHom.pi fun b => (ρ b).rangeRestrict)
  have hSBle : ∀ a : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a},
      specialBlock (idForm h n) x (a.1 : K[X]) ≤ (toLinSU h n).range := fun a g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hg)
  let F : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a} →
      Subgroup ↥(gramSU h (idGram K n)) :=
    fun a => (specialBlock (idForm h n) x (a.1 : K[X])).comap (toLinSU h n)
  have hFmap : ∀ a, (F a).map (toLinSU h n) = specialBlock (idForm h n) x (a.1 : K[X]) :=
    fun a => Subgroup.map_comap_eq_self (hSBle a)
  haveI : Finite ↥(gramSU h (idGram K n)) := inferInstance
  haveI : Finite (primeFormP h (idGram K n)) := inferInstance
  refine components_of_centralQuotient
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))
    (QuotientGroup.mk'_surjective _) ?_ α (primeFormConjHom h (idGram K n) A) ?_ F ?_ ?_ ?_ ψ ?_
    T hT
  · rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  · intro g
    exact (primeFormConjHom_mk h (idGram K n) A g).symm
  · intro a g hg
    exact (mem_fixSubgroup_primeFormConjSU_iff A hx g).mpr
      (specialBlock_le_unitaryCentralizer (Subgroup.mem_comap.mp hg)).2
  · intro a c' hc g hg
    have hcU := toLinSU_mem_unitaryCentralizer A hx hc
    have := conj_mem_specialBlock hcU (Subgroup.mem_comap.mp hg)
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact this
  · intro a
    have e : ↥(F a) ≃* ↥(specialBlock (idForm h n) x (a.1 : K[X])) :=
      (Subgroup.equivMapOfInjective (F a) (toLinSU h n) toLinSU_injective).trans
        (MulEquiv.subgroupCongr (hFmap a))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      ((specialBlockFacts_of_good H hq a.1 a.2).quasisimple a.2.1)
  · intro g hg
    have hy := hφU g
    have hdet : ∀ b : primaryFactors (x : Module.End K (Fin n → K)),
        KCUnitary.blockDetHom x (b : K[X]) ⟨toLinSU h n g, hy.2⟩ = 1 := fun b =>
      congrFun (congrArg Prod.fst hg) b
    have hbad : ∀ b : primaryFactors (x : Module.End K (Fin n → K)), ¬ IsGoodBlock h x b →
        blockRestrict x (b : K[X]) ⟨toLinSU h n g, hy.2⟩ = 1 := fun b hb =>
      congrArg Subtype.val (congrFun (congrArg Prod.snd hg) ⟨b, hb⟩)
    have hmem := mem_iSup_specialBlock_of_blocks H hy hdet hbad
    have hmapsup : (⨆ a, F a).map (toLinSU h n) =
        ⨆ a : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a},
          specialBlock (idForm h n) x (a.1 : K[X]) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hFmap
    have hk : toLinSU h n g ∈ (⨆ a, F a).map (toLinSU h n) := by
      rw [hmapsup]
      exact hmem
    obtain ⟨s, hs, hs'⟩ := hk
    have : s = g := toLinSU_injective hs'
    rw [← this]
    exact hs

end Concrete

section Block

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

private theorem specialBlock_eq_kerImage' {a : K[X]} {Ω : Type*} [Group Ω]
    (φ : orbitFactor B x a ≃* Ω) (ι : Ω →* blockGL (x : Module.End K V) a)
    (D : Ω →* (AdjoinRoot a)ˣ) (hD : ∀ w, D w = blockGLDet (x : Module.End K V) a (ι w))
    (hcompat : ∀ s : orbitFactor B x a,
      ι (φ s) = blockRestrict x a ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩) :
    specialBlock B x a = kerImage (orbitFactor B x a) φ D := by
  ext g
  rw [mem_specialBlock, mem_kerImage]
  constructor
  · rintro ⟨hs, hg, h⟩
    refine ⟨hs, ?_⟩
    rw [hD, hcompat ⟨g, hs⟩]
    exact h
  · rintro ⟨hs, h⟩
    refine ⟨hs, orbitFactor_le_gl_centralizer hs, ?_⟩
    rw [hD, hcompat ⟨g, hs⟩] at h
    exact h

private theorem nonempty_specialBlock_mulEquiv_SL {a : primaryFactors (x : Module.End K V)}
    (hP : PairedPrimaryBlock hK B x a) :
    Nonempty (↥(specialBlock B x (a : K[X])) ≃*
      Matrix.SpecialLinearGroup (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
        (AdjoinRoot (a : K[X]))) := by
  obtain ⟨φ, hφ, -⟩ := exists_pairedFactor hP
  have hspec := specialBlock_eq_kerImage' φ (MonoidHom.id _)
    (blockGLDet (x : Module.End K V) (a : K[X])) (fun _ => rfl)
    (fun s => blockGL_ext fun v hv => hφ s v hv)
  obtain ⟨e1⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ
    (blockGLDet (x : Module.End K V) (a : K[X]))
  obtain ⟨e2⟩ := nonempty_specialLinearGroup_mulEquiv_ker_det (E := AdjoinRoot (a : K[X]))
    (W := primaryComponent (x : Module.End K V) (a : K[X]))
  exact ⟨((MulEquiv.subgroupCongr hspec).trans e1).trans e2.symm⟩

private theorem nonempty_specialBlock_mulEquiv_sesqSU {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a) :
    ∃ (hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X])))
      (Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
        primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
          AdjoinRoot (a : K[X])),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
        Nonempty (↥(specialBlock B x (a : K[X])) ≃* ↥(sesqSpecialUnitaryGroup Hf)) := by
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ := exists_selfDualFactor hself hS
  refine ⟨hE, Hf, hHf, hHfl, ?_⟩
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (a : K[X]))ˣ :=
    (blockGLDet (x : Module.End K V) (a : K[X])).comp (sesqUnitaryGroup Hf).subtype
  have hspec := specialBlock_eq_kerImage' φ (sesqUnitaryGroup Hf).subtype D (fun _ => rfl)
    (fun s => blockGL_ext fun v hv => hφ s v hv)
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h
      simpa [D, blockGLDet] using this
    · rintro ⟨-, h⟩
      apply Units.ext
      simpa [D, blockGLDet] using h
  obtain ⟨e1⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ D
  exact ⟨((MulEquiv.subgroupCongr hspec).trans e1).trans
    ((MulEquiv.subgroupCongr hker).trans
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)))⟩

end Block

section Factor

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Open

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem false_of_good_block_l33 (hℓ3 : ℓ = 3)
    (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    {T : Type} [Group T] (g : ↥(specialBlock B x (a : K[X])) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center _) (hL : IsLpType 3 3 (T ⧸ Subgroup.center T)) : False := by
  haveI := hK.finite
  haveI : CharP K ℓ := hK.charP
  have hd : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hfd : 1 ≤ f * (a : K[X]).natDegree := Nat.mul_pos hK.one_le hd
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot (a : K[X])) := Fintype.ofFinite _
  have hcharE : ringChar (AdjoinRoot (a : K[X])) = ℓ :=
    (Algebra.ringChar_eq K (AdjoinRoot (a : K[X]))).symm.trans (ringChar.eq K ℓ)
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
      nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
    · have hV : Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := by
        have : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
        exact this
      obtain ⟨e2⟩ :=
        CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
      haveI : Finite hE.fixedField := inferInstance
      letI : Fintype hE.fixedField := Fintype.ofFinite _
      have hcardF : Fintype.card hE.fixedField = ℓ ^ (f * (a : K[X]).natDegree) := by
        rw [← Nat.card_eq_fintype_card]
        exact hE.card_fixedField
      haveI : Fact ℓ.Prime := ⟨hK.prime⟩
      haveI : CharP hE.fixedField ℓ := charP_of_card_eq_prime_pow hcardF
      have hcharF : ringChar hE.fixedField = 3 := by rw [ringChar.eq _ ℓ, hℓ3]
      have hφ := ker_comp_mulEquiv_le_center (e.trans e2).symm g hker
      obtain ⟨h3, -⟩ := sl_l33 hcharF le_rfl (g.comp (e.trans e2).symm.toMonoidHom)
        (hg.comp (e.trans e2).symm.surjective) hφ hL
      omega
    · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨e3⟩ :=
        CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
          (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))))
            (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
          (fun i j => by rw [hb i j, Matrix.one_apply])
      let e4 := (e.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
      have hφ := ker_comp_mulEquiv_le_center e4.symm g hker
      exact su_l33_false (m := primaryMultiplicity (x : Module.End K V) (a : K[X])) hE hℓ3 hm
        (g.comp e4.symm.toMonoidHom) (hg.comp e4.symm.surjective) hφ hL
  · obtain ⟨e⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock H a (Ne.symm hself))
    have hcard : Nat.card (AdjoinRoot (a : K[X])) = ℓ ^ (2 * (f * (a : K[X]).natDegree)) :=
      natCard_adjoinRoot hK
    have hφ := ker_comp_mulEquiv_le_center e.symm g hker
    obtain ⟨-, hE3⟩ := sl_l33 (hcharE.trans hℓ3) hm2 (g.comp e.symm.toMonoidHom)
      (hg.comp e.symm.surjective) hφ hL
    rw [hcard, hℓ3] at hE3
    have h9 : 3 ^ 2 ≤ 3 ^ (2 * (f * (a : K[X]).natDegree)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end Factor

section Assembly

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Open

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem unitary_inner_l33_false (hℓ3 : ℓ = 3) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (T : Subgroup (primeFormP h (idGram K n)))
    (hT : IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K n) A)))
    (hL : IsLpType 3 3 (↥T ⧸ Subgroup.center ↥T)) : False := by
  classical
  haveI := h.finite
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  have H := primaryData_toLin' h A.2 hp hpℓ hA
  obtain ⟨a, ha⟩ := exists_good_block_of_component hq A rfl H T hT
  have hSle : specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X]) ≤ (toLinSU h n).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hg)
  let F : Subgroup ↥(gramSU h (idGram K n)) :=
    (specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X])).comap (toLinSU h n)
  have hFmap : F.map (toLinSU h n) = specialBlock (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a.1 : K[X]) :=
    Subgroup.map_comap_eq_self hSle
  let ε : ↥(specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
      (a.1 : K[X])) ≃* ↥F :=
    ((Subgroup.equivMapOfInjective F (toLinSU h n) toLinSU_injective).trans
      (MulEquiv.subgroupCongr hFmap)).symm
  let π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
  haveI : Finite ↥F := inferInstance
  subst ha
  refine false_of_good_block_l33 hℓ3 H a.1 a.2 ((π.subgroupMap F).comp ε.toMonoidHom)
    ((MonoidHom.subgroupMap_surjective π F).comp ε.surjective) (fun u hu => ?_) hL
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hu
  have h1 : π (ε u : ↥(gramSU h (idGram K n))) = 1 := congrArg Subtype.val hu
  have h2 : ((ε u : ↥F) : ↥(gramSU h (idGram K n))) ∈
      normOneScalars h (gramSU h (idGram K n)) n := (QuotientGroup.eq_one_iff _).1 h1
  have h3 := normOneScalars_le_center h _ n h2
  rw [Subgroup.mem_center_iff]
  intro w
  apply ε.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.1 h3 _

end Assembly

end Helpers

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem unitary_l33_false {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq3 : q.p = 3)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group))
    {α : MulAut S} (hα : α ^ 13 = 1) {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup α))
    (hL : IsLpType 3 3 (↥K ⧸ Subgroup.center ↥K)) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp13 : (13 : ℕ).Prime := by norm_num
  obtain ⟨e⟩ := he
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, F, _, _, hF, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := F))
  let e' : S ≃* primeFormP h (idGram F (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hC : IsPrimeFormGram (1 : GL (Fin (r + 1)) F) := isPrimeFormGram_idGram
  have hβ' : MulAut.congr e' α ^ 13 = 1 := by rw [← map_pow, hα, map_one]
  have hK1 := isComponentOf_map_congr e' hK
  have hL1 := isLpType_center_map e' hL
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' α) = 1
  ·
    have hβD : MulAut.congr e' α ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, hA⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A ^ 13, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hA, hβ', map_one, one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    have hAp : (A : GL (Fin (r + 1)) F) ^ 13 =
        Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
      rwa [SubgroupClass.coe_pow] at hc
    rw [← hA] at hK1
    exact unitary_inner_l33_false hq3 hp13 (by rw [hq3]; norm_num) A hAp _ hK1 hL1
  ·
    have hne : MulAut.congr e' α ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have : Fact (13 : ℕ).Prime := ⟨hp13⟩
    have hord : orderOf (MulAut.congr e' α) = 13 := orderOf_eq_prime hβ' hne
    have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' α)) = 13 :=
      orderOf_eq_prime (by rw [← map_pow, hβ', map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' hp13
        (by norm_num) (MulAut.congr e' α) hord _ rfl hσp
    have hK2 := isComponentOf_map_congr
      ((primeFormConjHom h (idGram F (r + 1)) M)⁻¹ : MulAut _) hK1
    rw [congr_self_eq, inv_inv, hM] at hK2
    have hL2 := isLpType_center_map ((primeFormConjHom h (idGram F (r + 1)) M)⁻¹ : MulAut _) hL1
    obtain ⟨-, g, hg, hgk⟩ :=
      unitary_fieldAut_components h hn3 hC hp13 (by norm_num) hσp _ hK2
    exact su_l33_false (CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h hp13 (by norm_num)
      hσp) hq3 hn3 g hg hgk hL2

end Unitary

end UnitaryFamily

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33
