module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7Two

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Lemmas

variable {L : Type} [Field L] [IsAlgClosed L]

theorem rootChar_pow_eq_inv_of_seven {τ : Tag} (q : ℕ) (hq : 7 ∣ q + 1)
    {a : Fin τ.rank → L ˣ} (ha : ∀ i, a i ^ 7 = 1) (v : Fin τ.rank → ℤ) :
    rootChar a v ^ q = (rootChar a v)⁻¹ := by
  obtain ⟨m, hm⟩ := hq
  have h7 : rootChar a v ^ 7 = 1 := rootChar_pow_eq_one a ha v
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, show q + 1 = 7 * m from hm, pow_mul, h7, one_pow]

theorem rootChar_neg_eq_inv {τ : Tag} (a : Fin τ.rank → L ˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

theorem smul_inv_neg_of {τ : Tag} {w0 : WeylGroup τ} (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u)
    (u : Fin τ.rank → ℤ) : w0⁻¹ • u = -u := by
  have h := hw0 (w0⁻¹ • u)
  rw [smul_inv_smul] at h
  exact neg_eq_iff_eq_neg.mp h.symm

theorem exists_two_gen_of_card_sq {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (E : Subgroup G) (hE : Nat.card E = p ^ 2) (hexp : ∀ x ∈ E, x ^ p = 1) :
    ∃ x1 ∈ E, ∃ x2 ∈ E, E = Subgroup.closure {x1, x2} := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; exact pow_ne_zero 2 hp.ne_zero)
  have hnt : ∃ x ∈ E, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : E = ⊥ := by
      ext x
      exact ⟨fun hx => hcon x hx, fun hx => (Subgroup.mem_bot.mp hx) ▸ E.one_mem⟩
    rw [hsub, Subgroup.card_bot] at hE
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨x1, hx1E, hx1⟩ := hnt
  have hord : orderOf x1 = p := orderOf_eq_prime (hexp x1 hx1E) hx1
  haveI : Finite (Subgroup.zpowers x1) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; exact hp.ne_zero)
  have hZ : Nat.card (Subgroup.zpowers x1) = p := by rw [Nat.card_zpowers, hord]
  obtain ⟨x2, hx2E, hx2⟩ : ∃ x2 ∈ E, x2 ∉ Subgroup.zpowers x1 := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers x1 := fun x hx => hcon x hx
    have hc := Subgroup.card_le_of_le hle
    rw [hE, hZ] at hc
    have : p < p ^ 2 := by
      have h1 : 1 < p := hp.one_lt
      nlinarith
    omega
  set H := Subgroup.closure ({x1, x2} : Set G) with hH
  have hHE : H ≤ E := (Subgroup.closure_le E).2 (by
    intro x hx
    rcases hx with rfl | rfl
    · exact hx1E
    · exact hx2E)
  haveI : Finite H := Finite.of_injective (Set.inclusion (SetLike.coe_subset_coe.2 hHE))
    (Set.inclusion_injective _)
  have hZH : Subgroup.zpowers x1 ≤ H :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  have hx2H : x2 ∈ H := Subgroup.subset_closure (by simp)
  have hdvd : Nat.card H ∣ p ^ 2 := by
    rw [← hE]
    exact Subgroup.card_dvd_of_le hHE
  obtain ⟨i, hi, hiH⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hHcard : Nat.card H = p ^ 2 := by
    interval_cases i
    ·
      exfalso
      have hH1 : Nat.card H = 1 := by simpa using hiH
      have hx1H : x1 ∈ H := Subgroup.subset_closure (by simp)
      have hb : H = ⊥ := Subgroup.eq_bot_of_card_eq H hH1
      exact hx1 (Subgroup.mem_bot.mp (hb ▸ hx1H))
    ·
      exfalso
      have hHp : Nat.card H = p := by simpa using hiH
      have heq : Subgroup.zpowers x1 = H :=
        Subgroup.eq_of_le_of_card_ge hZH (by rw [hZ, hHp])
      exact hx2 (heq ▸ hx2H)
    · simpa using hiH
  refine ⟨x1, hx1E, x2, hx2E, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hHE (by rw [hHcard, hE])).symm

theorem rootChar_of_twisted_fixed (ℓ e : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {w : WeylGroup Tag.E7}
    {a : Fin Tag.E7.rank → L ˣ} (ha : ∀ i, a i ^ 7 = 1) (hq : 7 ∣ ℓ ^ e + 1)
    (hfix : canonicalRep (coxeterSystem Tag.E7) L w *
        entrywiseFrobGL Tag.E7 L ℓ e (rootDiagUnit Tag.E7 a) *
        (canonicalRep (coxeterSystem Tag.E7) L w)⁻¹ = rootDiagUnit Tag.E7 a)
    (v : Fin Tag.E7.rank → ℤ) :
    rootChar a (w • v) = (rootChar a v)⁻¹ := by
  rw [entrywiseFrobGL_rootDiagUnit_eq_pow] at hfix
  have hv := (rootDiagUnit_eq_conj_canonicalRep_iff (τ := Tag.E7) (K := L) a (a ^ ℓ ^ e) w).1
    hfix.symm v
  rw [rootChar_pow', rootChar_pow_eq_inv_of_seven (ℓ ^ e) hq ha v] at hv
  exact hv

theorem twisted_w0_fix (ℓ e : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {w0 : WeylGroup Tag.E7}
    (hw0 : ∀ u : Fin Tag.E7.rank → ℤ, w0 • u = -u) (hq : 7 ∣ ℓ ^ e + 1)
    {b : Fin Tag.E7.rank → L ˣ} (hb : ∀ i, b i ^ 7 = 1) :
    canonicalRep (coxeterSystem Tag.E7) L w0 * entrywiseFrobGL Tag.E7 L ℓ e (rootDiagUnit Tag.E7 b) *
      (canonicalRep (coxeterSystem Tag.E7) L w0)⁻¹ = rootDiagUnit Tag.E7 b := by
  rw [entrywiseFrobGL_rootDiagUnit_eq_pow]
  refine (rootDiagUnit_eq_conj_canonicalRep_iff (τ := Tag.E7) (K := L) b (b ^ ℓ ^ e) w0).2 ?_ |>.symm
  intro v
  rw [hw0 v, rootChar_neg_eq_inv, rootChar_pow', rootChar_pow_eq_inv_of_seven (ℓ ^ e) hq hb v]

theorem image_neg_familyKernel (a : Fin 2 → Fin Tag.E7.rank → L ˣ) {w0 : WeylGroup Tag.E7}
    (hw0 : ∀ u : Fin Tag.E7.rank → ℤ, w0 • u = -u) :
    (fun α => w0 • α) '' familyKernel (τ := Tag.E7) a = familyKernel (τ := Tag.E7) a := by
  have hneg : ∀ β ∈ familyKernel (τ := Tag.E7) a, -β ∈ familyKernel (τ := Tag.E7) a :=
    fun β hβ => ⟨IsRoot.neg hβ.1, fun i => by rw [rootChar_neg_eq_inv, hβ.2 i, inv_one]⟩
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    dsimp only
    rw [hw0 α]
    exact hneg α hα
  · intro hβ
    refine ⟨-β, hneg β hβ, ?_⟩
    dsimp only
    rw [hw0 (-β), neg_neg]

theorem canonicalRep_mem_familyGroup_of_closure (a : Fin 2 → Fin Tag.E7.rank → L ˣ)
    {y : WeylGroup Tag.E7}
    (hy : y ∈ Subgroup.closure ((fun α => rootReflection α) '' familyKernel (τ := Tag.E7) a)) :
    canonicalRep (coxeterSystem Tag.E7) L y ∈ familyGroup (τ := Tag.E7) (K := L) a := by
  let R : Subgroup (WeylGroup Tag.E7) :=
    { carrier := {x | canonicalRep (coxeterSystem Tag.E7) L x ∈ familyGroup (τ := Tag.E7) (K := L) a}
      mul_mem' := fun {x x'} hx hx' => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.E7) (R := L) x x'
        have hmul : canonicalRep (coxeterSystem Tag.E7) L (x * x') =
            k⁻¹ * (canonicalRep (coxeterSystem Tag.E7) L x * canonicalRep (coxeterSystem Tag.E7) L x') := by
          rw [hkk]
          group
        show canonicalRep (coxeterSystem Tag.E7) L (x * x') ∈ familyGroup (τ := Tag.E7) (K := L) a
        rw [hmul]
        exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) (mul_mem hx hx')
      one_mem' := by
        show canonicalRep (coxeterSystem Tag.E7) L 1 ∈ familyGroup (τ := Tag.E7) (K := L) a
        rw [canonicalRep_one]
        exact one_mem _
      inv_mem' := fun {x} hx => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.E7) (R := L) x x⁻¹
        rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkk
        have hinv : canonicalRep (coxeterSystem Tag.E7) L x⁻¹ =
            (canonicalRep (coxeterSystem Tag.E7) L x)⁻¹ * k := by
          rw [← hkk]
          group
        show canonicalRep (coxeterSystem Tag.E7) L x⁻¹ ∈ familyGroup (τ := Tag.E7) (K := L) a
        rw [hinv]
        exact mul_mem (inv_mem hx) (Subgroup.mem_sup_left hk) }
  have hgen : ∀ r ∈ (fun α => rootReflection α) '' familyKernel (τ := Tag.E7) a, r ∈ R := by
    rintro r ⟨α, hα, rfl⟩
    show canonicalRep (coxeterSystem Tag.E7) L (rootReflection α) ∈ familyGroup (τ := Tag.E7) (K := L) a
    have hn := canonicalRep_rootReflection_mem (τ := Tag.E7) (K := L) hα.1
    have hneg : -α ∈ familyKernel (τ := Tag.E7) a :=
      ⟨IsRoot.neg hα.1, fun i => by rw [rootChar_neg_eq_inv, hα.2 i, inv_one]⟩
    have hsub : rootSubgroup Tag.E7 L α ⊔ rootSubgroup Tag.E7 L (-α) ≤
        familyGroup (τ := Tag.E7) (K := L) a :=
      sup_le ((rootSubgroup_le_rootSpan (τ := Tag.E7) (K := L) hα).trans le_sup_right)
        ((rootSubgroup_le_rootSpan (τ := Tag.E7) (K := L) hneg).trans le_sup_right)
    exact (sup_le le_sup_left hsub) hn
  exact (Subgroup.closure_le R).2 (fun r hr => hgen r hr) hy

theorem exists_datum_change (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (e : ℕ) (he : 1 ≤ e)
    (a : Fin 2 → Fin Tag.E7.rank → L ˣ) (w w0 : WeylGroup Tag.E7)
    (g : ModGL Tag.E7 L)
    (hfix : entrywiseFrobGL Tag.E7 L ℓ e g = g * canonicalRep (coxeterSystem Tag.E7) L w)
    (hw0 : (fun α => w0 • α) '' familyKernel (τ := Tag.E7) a = familyKernel (τ := Tag.E7) a)
    (hy : canonicalRep (coxeterSystem Tag.E7) L (w0⁻¹ * w) ∈ familyGroup (τ := Tag.E7) (K := L) a) :
    ∃ z ∈ familyGroup (τ := Tag.E7) (K := L) a,
      entrywiseFrobGL Tag.E7 L ℓ e (g * z) = g * z * canonicalRep (coxeterSystem Tag.E7) L w0 := by
  have hQ := canonicalRep_mem_normalizer_of_image (τ := Tag.E7) (K := L) hw0
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.E7) (R := L) w0 (w0⁻¹ * w)
  rw [mul_inv_cancel_left] at hkk
  have hmM : canonicalRep (coxeterSystem Tag.E7) L w *
      (canonicalRep (coxeterSystem Tag.E7) L w0)⁻¹ ∈ familyGroup (τ := Tag.E7) (K := L) a := by
    have h1 : canonicalRep (coxeterSystem Tag.E7) L w =
        k⁻¹ * (canonicalRep (coxeterSystem Tag.E7) L w0 *
          canonicalRep (coxeterSystem Tag.E7) L (w0⁻¹ * w)) := by
      rw [hkk]
      group
    rw [h1]
    have hc := (Subgroup.mem_normalizer_iff.1 hQ _).1 hy
    have h2 : k⁻¹ * (canonicalRep (coxeterSystem Tag.E7) L w0 *
          canonicalRep (coxeterSystem Tag.E7) L (w0⁻¹ * w)) *
        (canonicalRep (coxeterSystem Tag.E7) L w0)⁻¹ =
        k⁻¹ * (canonicalRep (coxeterSystem Tag.E7) L w0 *
          canonicalRep (coxeterSystem Tag.E7) L (w0⁻¹ * w) *
          (canonicalRep (coxeterSystem Tag.E7) L w0)⁻¹) := by
      group
    rw [h2]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) hc
  have hn : (g⁻¹ * entrywiseFrobGL Tag.E7 L ℓ e g) =
      (canonicalRep (coxeterSystem Tag.E7) L w * (canonicalRep (coxeterSystem Tag.E7) L w0)⁻¹) *
        canonicalRep (coxeterSystem Tag.E7) L w0 := by
    rw [hfix]
    group
  obtain ⟨z, hz, hzeq⟩ := exists_mem_lang_conj (entrywiseFrobGL Tag.E7 L ℓ e)
    (M := familyGroup (τ := Tag.E7) (K := L) a) hmM hn (lang_familyGroup ℓ a e he _ hQ)
  refine ⟨z, hz, ?_⟩
  rw [inv_mul_eq_iff_eq_mul] at hzeq
  exact hzeq

@[expose] def E7SevenPlaneWeyl : Prop :=
  ∀ (L : Type) [Field L] (a : Fin 2 → Fin Tag.E7.rank → Lˣ),
    (∀ (s : Fin 2) (i : Fin Tag.E7.rank), a s i ^ 7 = 1) →
    ∀ y : WeylGroup Tag.E7,
      (∀ (s : Fin 2) (v : Fin Tag.E7.rank → ℤ), rootChar (a s) (y • v) = rootChar (a s) v) →
        y ∈ Subgroup.closure ((fun α => rootReflection α) '' familyKernel (τ := Tag.E7) a)

@[expose] def E7SevenFrameDatum : Prop :=
  ∃ w0 : WeylGroup Tag.E7, (∀ u : Fin Tag.E7.rank → ℤ, w0 • u = -u) ∧
    ∀ (K : Type) [Field K] [Finite K], 7 ∣ Nat.card K + 1 →
      ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
        ∃ g ∈ adjointGroup Tag.E7 (AlgebraicClosure K),
          Units.map (entrywiseHom Fr) g = g * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0 ∧
          ∀ y : adjointGroup Tag.E7 K, y ^ 7 = 1 →
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E7 K) ∈
              (twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0)
                (Units.map (entrywiseHom Fr))).map (MulAut.conj g).toMonoidHom →
            y ∈ e7FrameGroup K

theorem exp_seven_of_rootDiagUnit (a : Fin Tag.E7.rank → L ˣ) (h : rootDiagUnit Tag.E7 a ^ 7 = 1) :
    ∀ i, a i ^ 7 = 1 := by
  have h1 : rootDiagUnit Tag.E7 (a ^ 7) = rootDiagUnit Tag.E7 1 := by
    rw [rootDiagUnit_one, ← h]
    exact (rootDiagUnitHom Tag.E7 L).map_pow a 7
  have h2 := CFSG.LieType.Chevalley.rootDiagUnit_injective (K := L) (τ := Tag.E7) h1
  exact fun i => by simpa using congrFun h2 i

theorem rootChar_y_fix (ℓ e : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {w w0 : WeylGroup Tag.E7}
    (hw0 : ∀ u : Fin Tag.E7.rank → ℤ, w0 • u = -u)
    {a : Fin Tag.E7.rank → L ˣ} (ha : ∀ i, a i ^ 7 = 1) (hq : 7 ∣ ℓ ^ e + 1)
    (hfix : canonicalRep (coxeterSystem Tag.E7) L w *
        entrywiseFrobGL Tag.E7 L ℓ e (rootDiagUnit Tag.E7 a) *
        (canonicalRep (coxeterSystem Tag.E7) L w)⁻¹ = rootDiagUnit Tag.E7 a)
    (v : Fin Tag.E7.rank → ℤ) :
    rootChar a ((w0⁻¹ * w) • v) = rootChar a v := by
  rw [mul_smul, smul_inv_neg_of hw0, rootChar_neg_eq_inv,
    rootChar_of_twisted_fixed ℓ e ha hq hfix, inv_inv]

theorem comm_of_conj_eq {G : Type*} [Group G] {x z : G} (h : x * z * x⁻¹ = z) : z * x = x * z := by
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

end Lemmas

end CFSG.LieType.SeitzGeneration.ExcHigh
