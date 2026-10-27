module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec8Bender
import CFSG.Goldschmidt.Steps.Sec8Comp
import CFSG.Walter.Bender1970.S38.JR
import CFSG.Walter.Bender1970.S4.Rank
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem inv_of_inf_eq_bot {K : Subgroup G} {a : G} (ha2 : a * a = 1)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hK : K ⊓ Subgroup.centralizer ({a} : Set G) = ⊥)
    {y : G} (hy : y ∈ K) : a * y * a⁻¹ = y⁻¹ := by
  set φ := (K.normalizerMonoidHom ⟨a, haK⟩).toMonoidHom with hφ
  have hφy : ∀ z : K, ((φ z : K) : G) = a * z * a⁻¹ := fun _ => rfl
  have hfpf : MonoidHom.FixedPointFree φ := fun z hz => by
    have h1 : a * (z : G) * a⁻¹ = z := by rw [← hφy, hz]
    have h2 : (z : G) ∈ K ⊓ Subgroup.centralizer ({a} : Set G) := ⟨z.2, by
      show (z : G) ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (z : G) * a = a * z * a⁻¹ * a := by rw [h1]
        _ = a * z := by group⟩
    rw [hK, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hinv : Function.Involutive φ := fun z => Subtype.ext (by
    rw [hφy, hφy]
    calc a * (a * z * a⁻¹) * a⁻¹ = (a * a) * z * (a * a)⁻¹ := by group
      _ = z := by rw [ha2]; group)
  have := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinv) ⟨y, hy⟩
  exact congrArg Subtype.val this

omit [Finite G] in
theorem mem_centralizer_of_forall_conj {K : Subgroup G} {c : G}
    (h : ∀ y ∈ K, c * y * c⁻¹ = y) : c ∈ Subgroup.centralizer (K : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun y hy => by
    calc y * c = (c * y * c⁻¹) * c := by rw [h y hy]
      _ = c * y := by group

omit [Finite G] in
theorem commutator_mem_centralizer_of_le {K : Subgroup G} {x a : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (ha : K ≤ Subgroup.centralizer ({a} : Set G)) :
    x * a * x⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  refine mem_centralizer_of_forall_conj fun y hy => ?_
  have hy' : x⁻¹ * y * x ∈ K := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
  have e1 : a⁻¹ * y * a = y := by
    rw [mul_assoc, Subgroup.mem_centralizer_singleton_iff.mp (ha hy)]; group
  have e2 : a * (x⁻¹ * y * x) * a⁻¹ = x⁻¹ * y * x := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (ha hy')]; group
  calc (x * a * x⁻¹ * a⁻¹) * y * (x * a * x⁻¹ * a⁻¹)⁻¹
      = x * a * x⁻¹ * (a⁻¹ * y * a) * x * a⁻¹ * x⁻¹ := by group
    _ = x * (a * (x⁻¹ * y * x) * a⁻¹) * x⁻¹ := by rw [e1]; group
    _ = y := by rw [e2]; group

omit [Finite G] in
theorem commutator_mem_centralizer_of_inv {K : Subgroup G} {x a : G} (ha2 : a * a = 1)
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (ha : ∀ y ∈ K, a * y * a⁻¹ = y⁻¹) :
    x * a * x⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  refine mem_centralizer_of_forall_conj fun y hy => ?_
  have hy' : x⁻¹ * y * x ∈ K := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
  have e1 : a⁻¹ * y * a = y⁻¹ := by
    have := ha y hy
    rw [hai] at this ⊢
    exact this
  have e2 : a * (x⁻¹ * y * x)⁻¹ * a⁻¹ = x⁻¹ * y * x := by
    rw [show a * (x⁻¹ * y * x)⁻¹ * a⁻¹ = (a * (x⁻¹ * y * x) * a⁻¹)⁻¹ by group, ha _ hy', inv_inv]
  calc (x * a * x⁻¹ * a⁻¹) * y * (x * a * x⁻¹ * a⁻¹)⁻¹
      = x * a * x⁻¹ * (a⁻¹ * y * a) * x * a⁻¹ * x⁻¹ := by group
    _ = x * (a * (x⁻¹ * y * x)⁻¹ * a⁻¹) * x⁻¹ := by rw [e1]; group
    _ = y := by rw [e2]; group

theorem not_isPGroup_fstar (h64 : S_G64) (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) {q : ℕ}
    (hq : q.Prime) : ¬ IsPGroup q (generalizedFittingSubgroupOf H) := by
  intro hFq
  obtain ⟨ha2, -⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  have haF : a ∈ generalizedFittingSubgroupOf H :=
    le_sup_left (a := CFSG.fittingSubgroupOf H)
      (qCoreOf_le_fittingSubgroupOf H 2 Nat.prime_two ha2)
  have hq2 : q = 2 := by
    obtain ⟨k, hk⟩ := hFq ⟨a, haF⟩
    have h1 : orderOf a ∣ q ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [orderOf_eq_prime (hset.elem.2 a ha) ha1] at h1
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp
      (Nat.prime_two.dvd_of_dvd_pow h1)).symm
  subst hq2
  apply commutator_ne_bot hset h4 ha ha1 hH
  have hFn := generalizedFittingSubgroupOf_isNormalIn H
  have hdisj : ∀ z ∈ generalizedFittingSubgroupOf H, z ∈ oddCoreOf H → z = 1 := fun z hz hzO => by
    obtain ⟨k, hk⟩ := hFq ⟨z, hz⟩
    exact eq_one_of_pow_two_of_odd (odd_card_oddCoreOf H) hzO (k := k)
      (by simpa using congrArg Subtype.val hk)
  have hO1 : oddCoreOf H = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr ?_
    have hyH : y ∈ H := oddCoreOf_le H hy
    have hyC : y ∈ Subgroup.centralizer (generalizedFittingSubgroupOf H : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
      have hfH : f ∈ H := hFn.1 hf
      have h1 : y * f * y⁻¹ * f⁻¹ ∈ oddCoreOf H := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreOf H hfH) y⁻¹).mp
          (Subgroup.inv_mem _ hy)
        simpa [mul_assoc] using Subgroup.mul_mem _ hy this
      have h2 : y * f * y⁻¹ * f⁻¹ ∈ generalizedFittingSubgroupOf H :=
        Subgroup.mul_mem _ (hFn.2 y hyH f hf) (Subgroup.inv_mem _ hf)
      have h3 := hdisj _ h2 h1
      calc f * y = (y * f * y⁻¹ * f⁻¹)⁻¹ * (y * f) := by group
        _ = y * f := by rw [h3, inv_one, one_mul]
    exact hdisj y (Walter.inf_centralizer_generalizedFitting_le H ⟨hyH, hyC⟩) hy
  rw [hO1, Subgroup.commutator_bot_right]

theorem pResidualOf_ne_bot (h64 : S_G64) (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) {q : ℕ}
    (hq : q.Prime) : pResidualOf (generalizedFittingSubgroupOf H) q ≠ ⊥ := fun hres =>
  not_isPGroup_fstar h64 hset h4 ha ha1 hH hq (isPGroup_of_pResidualOf_eq_bot _ q hq hres)

omit [Finite G] in
theorem mem_primesOfOrder_fitting [Finite G] {H P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hP : P ≤ qCoreOf H p) (hP1 : P ≠ ⊥) : p ∈ primesOfOrder (CFSG.fittingSubgroupOf H) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := ((qCoreOf_isPGroup H p).to_le hP).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hP1 (Subgroup.card_eq_one.mp (by simpa using hk))
  have hdvd : p ∣ Nat.card (CFSG.fittingSubgroupOf H) := by
    refine (dvd_pow_self p hk0).trans ?_
    rw [← hk]
    exact Subgroup.card_dvd_of_le (hP.trans (qCoreOf_le_fittingSubgroupOf H p hp))
  exact Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩

theorem centralizer_le_normalizer_inf {H : Subgroup G} (hCH : Subgroup.centralizer (A : Set G) ≤ H)
    (p : ℕ) : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer
      ((qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := fun _ hc =>
  mem_normalizer_inf (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) (hCH hc))
    (Subgroup.le_normalizer hc)

theorem le_centralizer_of_isPGroup (h64 : S_G64) (h31 : S_G31) (h82 : S_G82)
    (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {H : Subgroup G} (hH : H ∈ Walter.benderM a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP1 : qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥) {M : Subgroup G}
    (hM : IsCoatom M) (hPM : Subgroup.normalizer
      ((qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) ≤ M)
    {P₁ : Subgroup G} (hP₁M : P₁ ≤ M) (hP₁p : IsPGroup p P₁)
    (haP₁ : a ∈ Subgroup.normalizer (P₁ : Set G)) :
    P₁ ≤ Subgroup.centralizer ({a} : Set G) := by
  have := hset.isSimpleGroup
  obtain ⟨-, hHa⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  by_cases hMH : M = H
  · rw [← hHa, ← hMH]
    exact hP₁M
  have hHco := Walter.isCoatom_of_mem_benderM hH
  have haF := h82 G S A hset h4 a ha ha1 H hH p hp hP1 M hM hPM hMH
  have hCH : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)).trans
      (Walter.centralizer_le_of_mem_benderM hH)
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => comm hset.elem hy hx
  have hAM : A ≤ M := (hAC.trans (centralizer_le_normalizer_inf hCH p)).trans hPM
  have haM : a ∈ M := hAM ha
  have hS := sstar_of_le hset hM.1 hAM
  have hPle : qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) ≤ qCoreOf H p := inf_le_left
  have haE : componentLayerOf M ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sSup_le fun L hL => ?_
    by_contra hLa
    have haL : a ∉ Subgroup.centralizer (L : Set G) := fun h => hLa fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h l hl)
    have hLQ := isComponentOf_normalClosureIn hL (le_normalClosureIn hAM ha) haL
    have hAL := le_of_isComponentOf h31 hS hset.elem h4 hLQ
    exact haF (le_sup_right (a := CFSG.fittingSubgroupOf M) (le_sSup hL (hAL ha)))
  have hcore : ∀ q : ℕ, q.Prime → qCoreOf M q ≤ Subgroup.centralizer ({a} : Set G) ∨
      ∀ y ∈ qCoreOf M q, a * y * a⁻¹ = y⁻¹ := by
    intro q hq
    by_cases hqF : q ∈ primesOfOrder (CFSG.fittingSubgroupOf H)
    · exact Or.inl (hHa ▸ qCoreOf_le_of_mem this hHco hp hPle hPM hq hqF
        (pResidualOf_ne_bot h64 hset h4 ha ha1 hH hq))
    · refine Or.inr fun y hy => inv_of_inf_eq_bot (mul_self_eq_one hset.elem ha)
        (le_normalizer_of_isNormalIn (qCoreOf_normal_in M q) haM) ?_ hy
      rw [← hHa]
      exact qCoreOf_inf_eq_bot this hHco hp hPle hPM hq hqF
  have ha2 : a * a = 1 := mul_self_eq_one hset.elem ha
  have hpF := mem_primesOfOrder_fitting hp hPle hP1
  intro x hx
  set c := x * a * x⁻¹ * a⁻¹ with hc
  have hxM : x ∈ M := hP₁M hx
  have hxN : ∀ K : Subgroup G, IsNormalIn K M → x ∈ Subgroup.normalizer (K : Set G) :=
    fun K hK => le_normalizer_of_isNormalIn hK hxM
  have hcK : ∀ K : Subgroup G, IsNormalIn K M → (K ≤ Subgroup.centralizer ({a} : Set G) ∨
      ∀ y ∈ K, a * y * a⁻¹ = y⁻¹) → K ≤ Subgroup.centralizer ({c} : Set G) := by
    intro K hK hKa y hy
    have hcy : c ∈ Subgroup.centralizer (K : Set G) := by
      rcases hKa with h | h
      · exact commutator_mem_centralizer_of_le (hxN K hK) h
      · exact commutator_mem_centralizer_of_inv ha2 (hxN K hK) h
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcy y hy)
  have hFle : generalizedFittingSubgroupOf M ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sup_le ?_ (hcK _ (componentLayerOf_isNormalIn M) (Or.inl haE))
    rw [fittingSubgroupOf_eq_iSup_qCoreOf]
    exact iSup_le fun q => hcK _ (qCoreOf_normal_in M _)
      (hcore _ (Nat.prime_of_mem_primeFactors q.1.2))
  have hcC : c ∈ Subgroup.centralizer (generalizedFittingSubgroupOf M : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hFle hy))
  have hcP : c ∈ P₁ := by
    have := (Subgroup.mem_normalizer_iff.mp haP₁ x⁻¹).mp (P₁.inv_mem hx)
    simpa [hc, mul_assoc] using P₁.mul_mem hx this
  have hcM : c ∈ M := hP₁M hcP
  have hcF : c ∈ generalizedFittingSubgroupOf M :=
    Walter.inf_centralizer_generalizedFitting_le M ⟨hcM, hcC⟩
  have hcFit : c ∈ CFSG.fittingSubgroupOf M :=
    Walter.generalizedFittingSubgroupOf_inf_centralizer_le M
      ⟨hcF, Subgroup.centralizer_le (le_sup_right : componentLayerOf M ≤ _) hcC⟩
  have hcp : IsPGroup p (Subgroup.zpowers c) := hP₁p.to_le (Subgroup.zpowers_le.mpr hcP)
  have hcO : c ∈ qCoreOf M p :=
    Walter.le_qCoreOf_of_le_fittingSubgroupOf hp (Subgroup.zpowers_le.mpr hcFit) hcp
      (Subgroup.mem_zpowers c)
  have hOpM : qCoreOf M p ≤ Subgroup.centralizer ({a} : Set G) :=
    hHa ▸ qCoreOf_le_of_mem this hHco hp hPle hPM hp hpF
      (pResidualOf_ne_bot h64 hset h4 ha ha1 hH hp)
  have hca : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp (hOpM hcO)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hinv : a * c * a⁻¹ = c⁻¹ := by
    rw [hc, hai]
    calc a * (x * a * x⁻¹ * a) * a = a * x * a * x⁻¹ * (a * a) := by group
      _ = (x * a * x⁻¹ * a)⁻¹ := by
        rw [ha2, mul_one]; simp only [mul_inv_rev, inv_inv, hai, mul_assoc]
  have hcc : c * c = 1 := by
    have h1 : a * c * a⁻¹ = c := by rw [← hca, mul_inv_cancel_right]
    rw [hinv] at h1
    calc c * c = c⁻¹⁻¹ * c := by rw [inv_inv]
      _ = 1 := by rw [h1, inv_mul_cancel]
  obtain ⟨k, hk⟩ := hP₁p ⟨c, hcP⟩
  have hk' : c ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hc1 : c = 1 := (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left k
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))).mp ⟨hk', by rw [sq]; exact hcc⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * a = c * (a * x) := by rw [hc]; group
    _ = a * x := by rw [hc1, one_mul]

end CFSG.Goldschmidt.Sec8
