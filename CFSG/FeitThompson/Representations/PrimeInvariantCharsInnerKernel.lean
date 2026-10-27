module

public import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
public import CFSG.FeitThompson.Representations.BrauerPermutationLemma
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
public import
  CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
public import Mathlib.GroupTheory.Complement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {K : Type*} [Group K] {N E U : Subgroup K} {b : MulAut K} {q : ℕ}

def conjClassesCongr {L : Type*} [Group L] (e : K ≃* L) : ConjClasses K ≃ ConjClasses L where
  toFun := ConjClasses.map (e : K →* L)
  invFun := ConjClasses.map (e.symm : L →* K)
  left_inv D := by
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective D
    change ConjClasses.mk _ = _
    simp
  right_inv D := by
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective D
    change ConjClasses.mk _ = _
    simp

@[simp]
theorem conjClassesCongr_mk {L : Type*} [Group L] (e : K ≃* L) (x : K) :
    conjClassesCongr e (ConjClasses.mk x) = ConjClasses.mk (e x) := (rfl)

theorem natCard_conjClasses_eq_one_of_forall_eq_one (h : ∀ x : K, x = 1) :
    Nat.card (ConjClasses K) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun D₁ D₂ => ?_⟩, ⟨1⟩⟩
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective D₁
  obtain ⟨y, rfl⟩ := ConjClasses.mk_surjective D₂
  rw [h x, h y]

theorem map_mulAut_eq_of_mapsTo (hq : 0 < q) (hbq : b ^ q = 1) {S : Subgroup K}
    (h : ∀ x ∈ S, b x ∈ S) : S.map (b : K →* K) = S := by
  have hpow : ∀ n : ℕ, ∀ x ∈ S, (b ^ n) x ∈ S := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ, MulAut.mul_apply]; exact ih _ (h x hx)
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact h x hx
  · intro x hx
    refine ⟨(b ^ (q - 1)) x, hpow _ x hx, ?_⟩
    change b ((b ^ (q - 1)) x) = x
    rw [← MulAut.mul_apply, ← pow_succ', Nat.sub_add_cancel hq, hbq, MulAut.one_apply]

theorem mapsTo_centralizer_inf (hE : E.map (b : K →* K) = E) (hU : ∀ u ∈ U, b u ∈ U) :
    ∀ x ∈ Subgroup.centralizer (E : Set K) ⊓ U,
      b x ∈ Subgroup.centralizer (E : Set K) ⊓ U := by
  intro x hx
  refine ⟨Subgroup.mem_centralizer_iff.2 ?_, hU x hx.2⟩
  intro e he
  have hmem : e ∈ E.map (b : K →* K) := by rw [hE]; exact he
  obtain ⟨e', he', rfl⟩ := hmem
  change b e' * b x = b x * b e'
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hx.1 e' he']

theorem normal_centralizer_inf_of_isComplement (E U : Subgroup K) [E.Normal]
    (h : Subgroup.IsComplement' E U) :
    (Subgroup.centralizer (E : Set K) ⊓ U).Normal := by
  constructor
  intro n hn g
  have hg : g ∈ (E : Set K) * (U : Set K) := by rw [h.mul_eq]; trivial
  obtain ⟨e, he, u, hu, rfl⟩ := hg
  have hm : u * n * u⁻¹ ∈ Subgroup.centralizer (E : Set K) ⊓ U := by
    refine ⟨(Subgroup.normal_centralizer (H := E)).conj_mem n hn.1 u, ?_⟩
    exact U.mul_mem (U.mul_mem hu hn.2) (U.inv_mem hu)
  have hcomm : e * (u * n * u⁻¹) = (u * n * u⁻¹) * e :=
    (Subgroup.mem_centralizer_iff.1 hm.1) e he
  have heq : e * u * n * (e * u)⁻¹ = e * (u * n * u⁻¹) * e⁻¹ := by group
  rw [heq, hcomm]
  simpa using hm

def quotientAutOfMapEq (N : Subgroup K) [N.Normal] {b : MulAut K}
    (h : N.map (b : K →* K) = N) : MulAut (K ⧸ N) :=
  QuotientGroup.congr N N b h

@[simp]
theorem quotientAutOfMapEq_mk (N : Subgroup K) [N.Normal] {b : MulAut K}
    (h : N.map (b : K →* K) = N) (x : K) :
    quotientAutOfMapEq N h (QuotientGroup.mk x) = QuotientGroup.mk (b x) :=
  QuotientGroup.congr_mk N N b h x

theorem quotientAutOfMapEq_pow_mk (N : Subgroup K) [N.Normal] {b : MulAut K}
    (h : N.map (b : K →* K) = N) (n : ℕ) (x : K) :
    (quotientAutOfMapEq N h ^ n) (QuotientGroup.mk x) = QuotientGroup.mk ((b ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, quotientAutOfMapEq_mk, ih, pow_succ, MulAut.mul_apply]

theorem quotientAutOfMapEq_pow_eq_one (N : Subgroup K) [N.Normal] {b : MulAut K}
    (h : N.map (b : K →* K) = N) {q : ℕ} (hbq : b ^ q = 1) :
    quotientAutOfMapEq N h ^ q = 1 := by
  ext t
  induction t using QuotientGroup.induction_on with
  | _ x => rw [quotientAutOfMapEq_pow_mk, hbq, MulAut.one_apply, MulAut.one_apply]

theorem eq_one_of_quotientAutOfMapEq_eq_self [E.Normal]
    (hEU : Subgroup.IsComplement' E U) (hE : E.map (b : K →* K) = E)
    (hU : ∀ u ∈ U, b u ∈ U) (hfree : ∀ u ∈ U, b u = u → u = 1)
    {t : K ⧸ E} (ht : quotientAutOfMapEq E hE t = t) : t = 1 := by
  induction t using QuotientGroup.induction_on with
  | _ g =>
    obtain ⟨e, he, u, hu, rfl⟩ : g ∈ (E : Set K) * (U : Set K) := by rw [hEU.mul_eq]; trivial
    have hconj : u⁻¹ * (e * u) ∈ E := by
      have h2 := (Subgroup.Normal.conj_mem (inferInstance : E.Normal)) e he u⁻¹
      simpa [mul_assoc] using h2
    have hmk : (QuotientGroup.mk (e * u) : K ⧸ E) = QuotientGroup.mk u :=
      (QuotientGroup.eq.2 hconj).symm
    rw [hmk] at ht ⊢
    rw [quotientAutOfMapEq_mk] at ht
    have hmem : u⁻¹ * b u ∈ E := by
      have h1 : (b u)⁻¹ * u ∈ E := QuotientGroup.eq.1 ht
      simpa using E.inv_mem h1
    have hmemU : u⁻¹ * b u ∈ U := U.mul_mem (U.inv_mem hu) (hU u hu)
    have h1 : u⁻¹ * b u = 1 := Subgroup.disjoint_def.1 hEU.disjoint hmem hmemU
    rw [hfree u hu (inv_mul_eq_one.1 h1).symm]
    simp

theorem exists_autFixed_mk_eq [Finite K] [N.Normal] (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K)
    (hbq : b ^ q = 1) (h : N.map (b : K →* K) = N) {t : K ⧸ N}
    (ht : quotientAutOfMapEq N h t = t) :
    ∃ x : K, b x = x ∧ (QuotientGroup.mk x : K ⧸ N) = t := by
  induction t using QuotientGroup.induction_on with
  | _ x =>
    rw [quotientAutOfMapEq_mk] at ht
    have hn₀ : x⁻¹ * b x ∈ N := by
      have h1 : (b x)⁻¹ * x ∈ N := QuotientGroup.eq.1 ht
      simpa using N.inv_mem h1
    have hstab : ∀ y ∈ (x • (N : Set K)), b y ∈ (x • (N : Set K)) := by
      intro y hy
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe] at hy ⊢
      have hrw : x⁻¹ * b y = (x⁻¹ * b x) * (b (x⁻¹ * y)) := by rw [map_mul, map_inv]; group
      rw [hrw]
      exact N.mul_mem hn₀ (h ▸ Subgroup.mem_map_of_mem _ hy)
    have hcard : ¬ q ∣ Nat.card ↥(x • (N : Set K)) := by
      rw [Set.natCard_smul_set]
      refine fun hd => hqK (hd.trans ?_)
      simpa using N.card_subgroup_dvd_card
    obtain ⟨y, hy, hyb⟩ := exists_fixed_mem_of_not_dvd_natCard hq hbq hstab hcard
    refine ⟨y, hyb, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe] at hy
    exact (QuotientGroup.eq.2 hy).symm

def autFixedQuotientHom [N.Normal] (h : N.map (b : K →* K) = N) :
    autFixedSubgroup b →* autFixedSubgroup (quotientAutOfMapEq N h) :=
  MonoidHom.codRestrict ((QuotientGroup.mk' N).comp (autFixedSubgroup b).subtype) _ (by
    intro x
    rw [mem_autFixedSubgroup]
    change quotientAutOfMapEq N h (QuotientGroup.mk (x : K)) = QuotientGroup.mk (x : K)
    rw [quotientAutOfMapEq_mk, mem_autFixedSubgroup.1 x.2])

@[simp]
theorem coe_autFixedQuotientHom_apply [N.Normal] (h : N.map (b : K →* K) = N)
    (x : autFixedSubgroup b) :
    ((autFixedQuotientHom h x : autFixedSubgroup (quotientAutOfMapEq N h)) : K ⧸ N)
      = QuotientGroup.mk (x : K) := (rfl)

theorem autFixedQuotientHom_injective [N.Normal] (h : N.map (b : K →* K) = N)
    (hNfix : ∀ n ∈ N, b n = n → n = 1) : Function.Injective (autFixedQuotientHom h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  refine Subtype.ext (hNfix _ ?_ (mem_autFixedSubgroup.1 x.2))
  have h1 : (QuotientGroup.mk (x : K) : K ⧸ N) = 1 := congrArg Subtype.val hx
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem autFixedQuotientHom_surjective [Finite K] [N.Normal] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) (h : N.map (b : K →* K) = N) :
    Function.Surjective (autFixedQuotientHom h) := by
  intro t
  obtain ⟨x, hxb, hxt⟩ := exists_autFixed_mk_eq hq hqK hbq h (mem_autFixedSubgroup.1 t.2)
  exact ⟨⟨x, mem_autFixedSubgroup.2 hxb⟩, Subtype.ext hxt⟩

noncomputable def autFixedQuotientEquiv [Finite K] [N.Normal] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) (h : N.map (b : K →* K) = N)
    (hNfix : ∀ n ∈ N, b n = n → n = 1) :
    autFixedSubgroup b ≃* autFixedSubgroup (quotientAutOfMapEq N h) :=
  MulEquiv.ofBijective (autFixedQuotientHom h)
    ⟨autFixedQuotientHom_injective h hNfix, autFixedQuotientHom_surjective hq hqK hbq h⟩

theorem natCard_fixed_Irr_eq_natCard_conjClasses_autFixed [Finite K] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) :
    Nat.card {χ : Irr K // irrAut b χ = χ} = Nat.card (ConjClasses (autFixedSubgroup b)) := by
  rw [card_fixed_irrAut_eq_card_fixed_conjClassesAut b]
  refine Nat.card_congr ((Equiv.subtypeEquivRight ?_).trans
    (bStableConjClassesEquivConjClassesAutFixed hq hqK hbq))
  intro D
  rw [conjClassesAut_eq_self_iff, mem_bStableConjClasses]
  rfl

theorem natCard_fixed_Irr_quotient_eq [Finite K] [N.Normal] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) (h : N.map (b : K →* K) = N)
    (hNfix : ∀ n ∈ N, b n = n → n = 1) :
    Nat.card {ψ : Irr (K ⧸ N) // irrAut (quotientAutOfMapEq N h) ψ = ψ}
      = Nat.card {χ : Irr K // irrAut b χ = χ} := by
  have hqQ : ¬ q ∣ Nat.card (K ⧸ N) := fun hd => hqK (hd.trans N.card_quotient_dvd_card)
  rw [natCard_fixed_Irr_eq_natCard_conjClasses_autFixed hq hqQ
      (quotientAutOfMapEq_pow_eq_one N h hbq),
    natCard_fixed_Irr_eq_natCard_conjClasses_autFixed hq hqK hbq]
  exact Nat.card_congr (conjClassesCongr (autFixedQuotientEquiv hq hqK hbq h hNfix)).symm

def inflationFixed [N.Normal] (h : N.map (b : K →* K) = N)
    (ψ : {ψ : Irr (K ⧸ N) // irrAut (quotientAutOfMapEq N h) ψ = ψ}) :
    {χ : Irr K // irrAut b χ = χ} :=
  ⟨⟨(ψ.1 : K ⧸ N → ℂ) ∘ (QuotientGroup.mk : K → K ⧸ N),
      irrTrivialOn_subset_Irr (mem_irrTrivialOn_comp_mk ψ.1.2)⟩, by
    rw [irrAut_eq_self_iff]
    intro x
    have hψ := (irrAut_eq_self_iff _ _).1 ψ.2 (QuotientGroup.mk x)
    change (ψ.1 : K ⧸ N → ℂ) (QuotientGroup.mk (b x)) = (ψ.1 : K ⧸ N → ℂ) (QuotientGroup.mk x)
    rw [← quotientAutOfMapEq_mk N h x, hψ]⟩

@[simp]
theorem coe_inflationFixed [N.Normal] (h : N.map (b : K →* K) = N)
    (ψ : {ψ : Irr (K ⧸ N) // irrAut (quotientAutOfMapEq N h) ψ = ψ}) :
    ((inflationFixed h ψ).1 : K → ℂ)
      = (ψ.1 : K ⧸ N → ℂ) ∘ (QuotientGroup.mk : K → K ⧸ N) := (rfl)

theorem inflationFixed_injective [N.Normal] (h : N.map (b : K →* K) = N) :
    Function.Injective (inflationFixed h) := fun _ _ hψ =>
  Subtype.ext (Subtype.ext (comp_mk_injective (congrArg (fun t => (t.1 : K → ℂ)) hψ)))

theorem inflationFixed_surjective [Finite K] [N.Normal] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) (h : N.map (b : K →* K) = N)
    (hNfix : ∀ n ∈ N, b n = n → n = 1) : Function.Surjective (inflationFixed h) :=
  ((inflationFixed_injective h).bijective_of_nat_card_le
    (le_of_eq (natCard_fixed_Irr_quotient_eq hq hqK hbq h hNfix).symm)).2

theorem subset_charValueKernel_of_fixed [Finite K] [N.Normal] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) (h : N.map (b : K →* K) = N)
    (hNfix : ∀ n ∈ N, b n = n → n = 1) {θ : K → ℂ} (hθ : θ ∈ Irr K)
    (hθb : ∀ x : K, θ (b x) = θ x) : (N : Set K) ⊆ charValueKernel θ := by
  obtain ⟨ψ, hψ⟩ := inflationFixed_surjective hq hqK hbq h hNfix
    ⟨⟨θ, hθ⟩, (irrAut_eq_self_iff b ⟨θ, hθ⟩).2 hθb⟩
  have hθeq : θ = (ψ.1 : K ⧸ N → ℂ) ∘ (QuotientGroup.mk : K → K ⧸ N) :=
    (congrArg (fun t => ((t : {χ : Irr K // irrAut b χ = χ}).1 : K → ℂ)) hψ).symm
  intro n hn
  rw [hθeq]
  exact mem_charValueKernel.2 ((mem_irrTrivialOn.1 (mem_irrTrivialOn_comp_mk ψ.1.2)).2 n hn)

theorem eq_one_of_fixed_of_forall_fixed_eq_one [Finite K] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) (hfree : ∀ x : K, b x = x → x = 1)
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hθb : ∀ x : K, θ (b x) = θ x) : θ = 1 := by
  have hcard : Nat.card {χ : Irr K // irrAut b χ = χ} = 1 := by
    rw [natCard_fixed_Irr_eq_natCard_conjClasses_autFixed hq hqK hbq]
    exact natCard_conjClasses_eq_one_of_forall_eq_one fun x =>
      Subtype.ext (hfree _ (mem_autFixedSubgroup.1 x.2))
  have hsub : Subsingleton {χ : Irr K // irrAut b χ = χ} := (Nat.card_eq_one_iff_unique.1 hcard).1
  have h1 : irrAut b (⟨1, one_mem_Irr⟩ : Irr K) = ⟨1, one_mem_Irr⟩ :=
    (irrAut_eq_self_iff b _).2 fun _ => rfl
  exact congrArg (fun t => ((t : {χ : Irr K // irrAut b χ = χ}).1 : K → ℂ))
    (hsub.allEq ⟨⟨θ, hθ⟩, (irrAut_eq_self_iff b ⟨θ, hθ⟩).2 hθb⟩ ⟨⟨1, one_mem_Irr⟩, h1⟩)

variable [Finite K] [E.Normal]

theorem subset_charValueKernel_centralizer_inf_of_fixed (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) (hEU : Subgroup.IsComplement' E U)
    (hE : ∀ x ∈ E, b x ∈ E) (hU : ∀ u ∈ U, b u ∈ U) (hCU : ∀ u ∈ U, b u = u → u = 1)
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hθb : ∀ x : K, θ (b x) = θ x) :
    ((Subgroup.centralizer (E : Set K) ⊓ U : Subgroup K) : Set K) ⊆ charValueKernel θ := by
  have hEmap : E.map (b : K →* K) = E := map_mulAut_eq_of_mapsTo hq.pos hbq hE
  have _ : (Subgroup.centralizer (E : Set K) ⊓ U).Normal :=
    normal_centralizer_inf_of_isComplement E U hEU
  refine subset_charValueKernel_of_fixed hq hqK hbq
    (map_mulAut_eq_of_mapsTo hq.pos hbq (mapsTo_centralizer_inf hEmap hU)) ?_ hθ hθb
  intro n hn hbn
  exact hCU n hn.2 hbn

theorem not_subset_charValueKernel_of_fixed_of_ne_one (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) (hEU : Subgroup.IsComplement' E U)
    (hE : ∀ x ∈ E, b x ∈ E) (hU : ∀ u ∈ U, b u ∈ U) (hCU : ∀ u ∈ U, b u = u → u = 1)
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hθb : ∀ x : K, θ (b x) = θ x) (hθ1 : θ ≠ 1) :
    ¬ ((E : Set K) ⊆ charValueKernel θ) := by
  intro hsub
  have hEmap : E.map (b : K →* K) = E := map_mulAut_eq_of_mapsTo hq.pos hbq hE
  obtain ⟨ψ, hψ, hψθ⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn (N := E)
    (mem_irrTrivialOn.2 ⟨hθ, fun n hn => mem_charValueKernel.1 (hsub hn)⟩)
  have hqQ : ¬ q ∣ Nat.card (K ⧸ E) := fun hd => hqK (hd.trans E.card_quotient_dvd_card)
  have hψb : ∀ t : K ⧸ E, ψ (quotientAutOfMapEq E hEmap t) = ψ t := by
    intro t
    induction t using QuotientGroup.induction_on with
    | _ x =>
      rw [quotientAutOfMapEq_mk]
      have h1 : ψ (QuotientGroup.mk (b x)) = θ (b x) := congrFun hψθ (b x)
      have h2 : ψ (QuotientGroup.mk x) = θ x := congrFun hψθ x
      rw [h1, h2, hθb]
  have hψ1 : ψ = 1 := eq_one_of_fixed_of_forall_fixed_eq_one hq hqQ
    (quotientAutOfMapEq_pow_eq_one E hEmap hbq)
    (fun t ht => eq_one_of_quotientAutOfMapEq_eq_self hEU hEmap hU hCU ht) hψ hψb
  refine hθ1 ?_
  rw [← hψθ, hψ1]
  rfl

end CFSG.FeitThompson
