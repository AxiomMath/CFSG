module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusQuotient
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.GroupTheory.ABGDGroups.LinearASeven
public import CFSG.GroupTheory.ABGDGroups.LinearQuotient
public import CFSG.GroupTheory.ABGDGroups.LinearOddCyclic
public import CFSG.Dihedral.PerfectDihedralFourgroupAction
public import CFSG.GroupTheory.OddInversion
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizers
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.CharacterTheory.Wreathed.Coordinates
public import CFSG.CharacterTheory.Wreathed.Involutions
public import CFSG.CharacterTheory.Wreathed.MaximalOrder
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.CharacterTheory.Semidihedral.KleinFourOddKernel
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders
public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate7
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven

public noncomputable section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion Omnibus
open scoped Pointwise commutatorElement

namespace OmnibusDConjugacyQD

section Abstract

variable {K : Type} [Group K]

private def dSig (T C : Subgroup K) (r : ℕ) : Set (Subgroup K) :=
  {Y | IsPGroup r Y ∧ T ≤ Subgroup.normalizer (Y : Set K) ∧ (Y : Set K) * C = C * Y}

private theorem dSig_conjSub {T C : Subgroup K} {r : ℕ} {n : K}
    (hnT : n ∈ Subgroup.normalizer (T : Set K)) (hnC : n ∈ Subgroup.normalizer (C : Set K))
    {Y : Subgroup K} (hY : Y ∈ dSig T C r) : conjSub n Y ∈ dSig T C r :=
  ⟨isPGroup_conjSub hY.1, le_normalizer_conjSub hY.2.1 hnT, conjSub_mul_comm hnC hY.2.2⟩

private theorem dSig_conjSub_maximals {T C : Subgroup K} {r : ℕ} {n : K}
    (hnT : n ∈ Subgroup.normalizer (T : Set K)) (hnC : n ∈ Subgroup.normalizer (C : Set K))
    {Y : Subgroup K} (hY : Y ∈ maximals (dSig T C r)) : conjSub n Y ∈ maximals (dSig T C r) := by
  refine ⟨dSig_conjSub hnT hnC hY.1, fun Z hZ hle => ?_⟩
  have hZ' := dSig_conjSub (Subgroup.inv_mem _ hnT) (Subgroup.inv_mem _ hnC) hZ
  have hYZ : Y ≤ conjSub n⁻¹ Z := by
    rw [← conjSub_le_conjSub_iff (g := n), conjSub_conjSub_inv]
    exact hle
  have := hY.2 _ hZ' hYZ
  rw [← this, conjSub_conjSub_inv]

private theorem mem_normalizer_centralizer {T : Subgroup K} {n : K}
    (hn : n ∈ Subgroup.normalizer (T : Set K)) :
    n ∈ Subgroup.normalizer ((Subgroup.centralizer (T : Set K) : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc t ht
    have ht' : n⁻¹ * t * n ∈ T := (Subgroup.mem_normalizer_iff''.mp hn t).mp ht
    have h := hc _ ht'
    calc t * (n * c * n⁻¹) = n * ((n⁻¹ * t * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * t * n)) * n⁻¹ := by rw [h]
      _ = n * c * n⁻¹ * t := by group
  · intro hc t ht
    have ht' : n * t * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn t).mp ht
    have h := hc _ ht'
    calc t * c = n⁻¹ * ((n * t * n⁻¹) * (n * c * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * c * n⁻¹) * (n * t * n⁻¹)) * n := by rw [h]
      _ = c * t := by group

private theorem exists_conjSub_eq_of_unique {T : Subgroup K} {r : ℕ} {X X' : Subgroup K}
    {t t' : K} (hX' : X' ∈ maximals (dSig T (Subgroup.centralizer (T : Set K)) r))
    (ht'X' : X' ≤ Subgroup.centralizer ({t'} : Set K))
    (huniq : ∀ Y ∈ maximals (dSig T (Subgroup.centralizer (T : Set K)) r),
      Y ≤ Subgroup.centralizer ({t} : Set K) → Y = X)
    (h : X = X' ∨ ∃ n ∈ Subgroup.normalizer (T : Set K), n * t' * n⁻¹ = t) :
    ∃ n ∈ Subgroup.normalizer (T : Set K), conjSub n X' = X := by
  rcases h with h | ⟨n, hn, hnt⟩
  · exact ⟨1, Subgroup.one_mem _, by rw [conjSub_one, h]⟩
  refine ⟨n, hn, huniq _ (dSig_conjSub_maximals hn (mem_normalizer_centralizer hn) hX') ?_⟩
  calc conjSub n X' ≤ conjSub n (Subgroup.centralizer ({t'} : Set K)) := conjSub_mono ht'X'
    _ = Subgroup.centralizer ({t} : Set K) := by rw [conjSub_centralizer, hnt]

end Abstract

section FourGroup

variable {K : Type} [Group K]

private theorem kleinFour_cases {V : Subgroup K} [IsKleinFour V] {a b c : K} (ha : a ∈ V)
    (hb : b ∈ V) (hc : c ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hca, hcb, hcab⟩ := hcon
  apply hcab
  have h := IsKleinFour.eq_mul_of_ne_all (x := (⟨a, ha⟩ : V)) (y := ⟨b, hb⟩) (z := ⟨c, hc⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (fun h => hab (congrArg Subtype.val h)) (fun h => hc1 (congrArg Subtype.val h))
    (fun h => hca (congrArg Subtype.val h)) (fun h => hcb (congrArg Subtype.val h))
  exact congrArg Subtype.val h

private theorem kleinFour_mul_self' {V : Subgroup K} [IsKleinFour V] {a : K} (ha : a ∈ V) :
    a * a = 1 :=
  congrArg Subtype.val (IsKleinFour.mul_self (⟨a, ha⟩ : V))

private theorem kleinFour_comm {V : Subgroup K} [IsKleinFour V] {a b : K} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a :=
  congrArg Subtype.val ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem mem_centralizer_of_mem_centralizer_pair {V : Subgroup K} [IsKleinFour V]
    {a b g : K} (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hga : g ∈ Subgroup.centralizer ({a} : Set K))
    (hgb : g ∈ Subgroup.centralizer ({b} : Set K)) :
    g ∈ Subgroup.centralizer (V : Set K) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hga hgb
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  rcases kleinFour_cases ha hb hc ha1 hb1 hab with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hga.symm
  · exact hgb.symm
  · rw [mul_assoc, ← hgb, ← mul_assoc, ← hga, mul_assoc]

private theorem exists_conj_of_fixedPointFree {V : Subgroup K} [IsKleinFour V] {g : K}
    (hg : g ∈ Subgroup.normalizer (V : Set K)) (hfpf : ∀ v ∈ V, v ≠ 1 → g * v * g⁻¹ ≠ v)
    {v w : K} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (V : Set K), n * v * n⁻¹ = w := by
  have hconj : ∀ u ∈ V, g * u * g⁻¹ ∈ V := fun u hu => (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have hne1 : ∀ u : K, u ≠ 1 → g * u * g⁻¹ ≠ 1 := fun u hu h =>
    hu (calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  set v₁ := g * v * g⁻¹ with hv₁
  set v₂ := g * v₁ * g⁻¹ with hv₂
  have hv₁V : v₁ ∈ V := hconj v hv
  have hv₂V : v₂ ∈ V := hconj v₁ hv₁V
  have hv₁1 : v₁ ≠ 1 := hne1 v hv1
  have hv₂1 : v₂ ≠ 1 := hne1 v₁ hv₁1
  have hv₁v : v₁ ≠ v := hfpf v hv hv1
  have hv₂v₁ : v₂ ≠ v₁ := hfpf v₁ hv₁V hv₁1
  have hv₂v : v₂ ≠ v := by
    intro h
    have hvv₁ : v * v₁ ≠ 1 := by
      intro h1
      apply hv₁v
      have h2 := kleinFour_mul_self' hv
      calc v₁ = v * (v * v₁) := by rw [← mul_assoc, h2, one_mul]
        _ = v := by rw [h1, mul_one]
    apply hfpf (v * v₁) (V.mul_mem hv hv₁V) hvv₁
    calc g * (v * v₁) * g⁻¹ = (g * v * g⁻¹) * (g * v₁ * g⁻¹) := by group
      _ = v₁ * v := by rw [← hv₁, ← hv₂, h]
      _ = v * v₁ := kleinFour_comm hv₁V hv
  by_cases h1 : w = v
  · exact ⟨1, Subgroup.one_mem _, by rw [h1]; group⟩
  by_cases h2 : w = v₁
  · exact ⟨g, hg, h2.symm⟩
  have h3 : w = v₂ := by
    rcases kleinFour_cases hv hv₁V hw hv1 hv₁1 hv₁v.symm with h | h | h | h
    · exact absurd h hw1
    · exact absurd h h1
    · exact absurd h h2
    rcases kleinFour_cases hv hv₁V hv₂V hv1 hv₁1 hv₁v.symm with h' | h' | h' | h'
    · exact absurd h' hv₂1
    · exact absurd h' hv₂v
    · exact absurd h' hv₂v₁
    · rw [h, h']
  refine ⟨g * g, Subgroup.mul_mem _ hg hg, ?_⟩
  rw [h3, hv₂, hv₁]
  group

private theorem exists_conj_of_surjective {V : Subgroup K} [IsKleinFour V]
    (hs : Function.Surjective V.normalizerMonoidHom) {v w : K} (hv : v ∈ V) (hw : w ∈ V)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) : ∃ n ∈ Subgroup.normalizer (V : Set K), n * v * n⁻¹ = w := by
  classical
  set a : V := ⟨v, hv⟩ with hadef
  set b : V := ⟨w, hw⟩ with hbdef
  have ha : a ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have hb : b ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  let φ : MulAut V :=
    IsKleinFour.mulEquiv (Equiv.swap a b) (Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm)
  obtain ⟨n, hn⟩ := hs φ
  refine ⟨n, n.2, ?_⟩
  have h := congrArg (fun ψ : MulAut V => ((ψ a : V) : K)) hn
  simp only [normalizerMonoidHom_apply_coe] at h
  rw [h]
  change ((Equiv.swap a b a : V) : K) = w
  rw [Equiv.swap_apply_left]

private theorem exists_conj_of_perfect_dihedral [Finite K] [Group.IsPerfect K] (S : Sylow 2 K)
    {m : ℕ} (hm : 2 ≤ m) (e : S ≃* DihedralGroup (2 ^ m)) {V : Subgroup K}
    (hVS : V ≤ (S : Subgroup K)) (hV : IsKleinFour V) {v w : K} (hv : v ∈ V) (hw : w ∈ V)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) : ∃ n ∈ Subgroup.normalizer (V : Set K), n * v * n⁻¹ = w :=
  have : IsKleinFour V := hV
  exists_conj_of_surjective
    (CFSG.GorensteinWalter.perfect_dihedral_fourgroup_normalizer_surjective S hm e V hVS hV)
    hv hw hv1 hw1

private theorem exists_fixedPointFree_of_sylow [Finite K] (P : Sylow 2 K)
    [IsKleinFour (P : Subgroup K)]
    (hC : Subgroup.centralizer ((P : Subgroup K) : Set K) ≤ P)
    (hnc : ∀ N : Subgroup K, N.Normal → Odd (Nat.card N) → N = ⊥) (hcard : 4 < Nat.card K) :
    ∃ g ∈ Subgroup.normalizer ((P : Subgroup K) : Set K),
      ∀ v ∈ (P : Subgroup K), v ≠ 1 → g * v * g⁻¹ ≠ v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  have hPC : (P : Subgroup K) ≤ Subgroup.centralizer ((P : Subgroup K) : Set K) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact kleinFour_comm hb ha
  have hNC : Subgroup.normalizer ((P : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((P : Subgroup K) : Set K) := by
    intro g hg
    obtain ⟨v, hvP, hv1, hgv⟩ := hne g hg
    set a := (P : Subgroup K).normalizerMonoidHom ⟨g, hg⟩ with hadef
    have hafix : a ⟨v, hvP⟩ = ⟨v, hvP⟩ := Subtype.ext hgv
    have ha2 : a ^ 2 = 1 := CFSG.GorensteinWalter.mulAut_sq_eq_one_of_fixed_ne_one a
      (fun h => hv1 (congrArg Subtype.val h)) hafix
    have hg2 : g ^ 2 ∈ Subgroup.centralizer ((P : Subgroup K) : Set K) := by
      have hker : (⟨g, hg⟩ : Subgroup.normalizer ((P : Subgroup K) : Set K)) ^ 2 ∈
          (P : Subgroup K).normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker, map_pow]
        exact ha2
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
      simpa using hker
    have hg2P : g ^ 2 ∈ (P : Subgroup K) := hC hg2
    have h4 : g ^ 2 ^ 2 = 1 := by
      rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, kleinFour_mul_self' hg2P]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h4)
    have hzp : IsPGroup 2 (Subgroup.zpowers g) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
    have hW : IsPGroup 2 ((P : Subgroup K) ⊔ Subgroup.zpowers g : Subgroup K) :=
      IsPGroup.to_sup_of_normal_left' P.isPGroup' hzp (Subgroup.zpowers_le.mpr hg)
    have hWP := P.is_maximal' hW le_sup_left
    have hgP : g ∈ (P : Subgroup K) := by
      rw [← hWP]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
    exact hPC hgP
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hodd : ¬ 2 ∣ Nat.card (MonoidHom.transferSylow P hNC).ker :=
    MonoidHom.not_dvd_card_ker_transferSylow P hNC
  have hN : (MonoidHom.transferSylow P hNC).ker = ⊥ :=
    hnc _ inferInstance (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
  have hc := hcomp.card_mul_card
  rw [hN, Subgroup.card_bot, one_mul, IsKleinFour.card_four] at hc
  omega

end FourGroup

section PGroup

variable {K : Type} [Group K]

private theorem odd_orderOf_of_isPGroup {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {Y : Subgroup K}
    (hY : IsPGroup r Y) {y : K} (hy : y ∈ Y) : Odd (orderOf y) := by
  obtain ⟨k, hk⟩ := hY ⟨y, hy⟩
  have hk' : y ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact Odd.of_dvd_nat (hr.odd_of_ne_two hr2).pow (orderOf_dvd_of_pow_eq_one hk')

private theorem eq_bot_or_eq_of_le_card_three [Finite K] {Y U : Subgroup K} (hYU : Y ≤ U)
    (hU : Nat.card U = 3) : Y = ⊥ ∨ Y = U := by
  have hdvd : Nat.card Y ∣ 3 := hU ▸ Subgroup.card_dvd_of_le hYU
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact Or.inl (Subgroup.card_eq_one.mp h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hYU (by rw [h, hU]))

end PGroup

section ASeven

local notation "A₇" => alternatingGroup (Fin 7)

open CFSG.GorensteinWalter (a7t a7u a7a a7v a7s a7S)

private def dq7g₁ : A₇ := ⟨Equiv.swap (2 : Fin 7) 4 * Equiv.swap 3 5, by simp [Equiv.Perm.sign_mul]⟩

private def dq7g₂ : A₇ := ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap 1 5, by simp [Equiv.Perm.sign_mul]⟩

private def dq7c : Fin 3 → A₇ := ![a7a, dq7g₁ * a7a * dq7g₁⁻¹, dq7g₂ * a7a * dq7g₂⁻¹]

private theorem dq7_pow_three_eq_one_of_odd {M : Type*} [Monoid M] {x : M}
    (hx : Odd (orderOf x)) (h12 : x ^ 12 = 1) : x ^ 3 = 1 := by
  have hdvd : orderOf x ∣ 3 * 4 := orderOf_dvd_of_pow_eq_one h12
  have hcop : Nat.Coprime (orderOf x) 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_right.mpr hx).pow_right 2
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)

private theorem dq7_involution_cases {v : A₇} (hv : v ∈ a7S) (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1) :
    v = a7t ∨ v = a7u ∨ v = a7t * a7u ∨ v = dq7g₁ * a7t * dq7g₁⁻¹ ∨
      v = dq7g₂ * a7t * dq7g₂⁻¹ := by
  change v = 1 ∨ v = a7v ∨ v = a7v ^ 2 ∨ v = a7v ^ 3 ∨ v = a7s ∨ v = a7s * a7v ∨
    v = a7s * a7v ^ 2 ∨ v = a7s * a7v ^ 3 at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hv1
  · exact absurd hv2 (by decide +kernel)
  · left; decide +kernel
  · exact absurd hv2 (by decide +kernel)
  · right; right; right; left; decide +kernel
  · right; left; decide +kernel
  · right; right; right; right; decide +kernel
  · right; right; left; decide +kernel

private theorem dq7_eq_of_commute_conj_a7t {g x : A₇} (hx : Odd (orderOf x))
    (hc : x * (g * a7t * g⁻¹) = g * a7t * g⁻¹ * x) :
    x = 1 ∨ x = g * a7a * g⁻¹ ∨ x = (g * a7a * g⁻¹) ^ 2 := by
  set y := g⁻¹ * x * g with hy
  have hxy : x = g * y * g⁻¹ := by rw [hy]; group
  have hyc : y * a7t = a7t * y := by
    rw [hy]
    calc g⁻¹ * x * g * a7t = g⁻¹ * (x * (g * a7t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a7t * g⁻¹ * x) * g := by rw [hc]
      _ = a7t * (g⁻¹ * x * g) := by group
  have hyo : orderOf y = orderOf x := by
    rw [hy, show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq]
  obtain ⟨h12, h3⟩ := (CFSG.ABGDGroups.aSeven_centralizer_involution_a7V_certificate y).1 hyc
  rcases h3 (dq7_pow_three_eq_one_of_odd (hyo ▸ hx) h12) with h | h | h
  · left
    rw [hxy, h]
    group
  · right; left
    rw [hxy, h]
  · right; right
    rw [hxy, h, conj_pow]

private theorem dq7_exists_index_of_involution {v : A₇} (hv : v ∈ a7S) (hv1 : v ≠ 1)
    (hv2 : v ^ 2 = 1) :
    ∃ i : Fin 3, ∀ x : A₇, x * v = v * x → Odd (orderOf x) →
      x = 1 ∨ x = dq7c i ∨ x = dq7c i ^ 2 := by
  have hcert := CFSG.ABGDGroups.aSeven_centralizer_involution_a7V_certificate
  rcases dq7_involution_cases hv hv1 hv2 with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, fun x hc hx => ((hcert x).1 hc).2
      (dq7_pow_three_eq_one_of_odd hx ((hcert x).1 hc).1)⟩
  · exact ⟨0, fun x hc hx => ((hcert x).2.1 hc).2
      (dq7_pow_three_eq_one_of_odd hx ((hcert x).2.1 hc).1)⟩
  · exact ⟨0, fun x hc hx => ((hcert x).2.2 hc).2
      (dq7_pow_three_eq_one_of_odd hx ((hcert x).2.2 hc).1)⟩
  · exact ⟨1, fun x hc hx => dq7_eq_of_commute_conj_a7t hx hc⟩
  · exact ⟨2, fun x hc hx => dq7_eq_of_commute_conj_a7t hx hc⟩

private theorem dq7c_certificate : ∀ i : Fin 3, dq7c i ^ 3 = 1 ∧ dq7c i ≠ 1 := by
  decide +kernel

variable {K : Type} [Group K] [Finite K]

private theorem aSeven_exists_card_three (e : K ≃* A₇) {t : K} (ht : orderOf t = 2) :
    ∃ U : Subgroup K, Nat.card U = 3 ∧
      ∀ x : K, x * t = t * x → Odd (orderOf x) → x ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨φ, hφ⟩ := CFSG.ABGDGroups.exists_mulEquiv_aSeven_map_sylow_eq e S
  have hφt : φ t ∈ a7S := by
    rw [← hφ]
    exact ⟨t, hS (Subgroup.mem_zpowers t), rfl⟩
  have hφt1 : φ t ≠ 1 := by
    intro h
    have h1 : t = 1 := φ.injective (h.trans (map_one φ).symm)
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hφt2 : φ t ^ 2 = 1 := by
    rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨i, hi⟩ := dq7_exists_index_of_involution hφt hφt1 hφt2
  obtain ⟨hc3, hc1⟩ := dq7c_certificate i
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨Subgroup.zpowers (φ.symm (dq7c i)), ?_, fun x hxt hx => ?_⟩
  · rw [Nat.card_zpowers, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hc3 hc1
  · have hc : φ x * φ t = φ t * φ x := by rw [← map_mul, ← map_mul, hxt]
    have hxo : Odd (orderOf (φ x)) := by rwa [MulEquiv.orderOf_eq]
    have hxeq : x = φ.symm (φ x) := (φ.symm_apply_apply x).symm
    rcases hi (φ x) hc hxo with h | h | h
    · rw [hxeq, h, map_one]
      exact Subgroup.one_mem _
    · rw [hxeq, h]
      exact Subgroup.mem_zpowers _
    · rw [hxeq, h, map_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2

private theorem aSeven_eq_of_maximals (e : K ≃* A₇) {T C : Subgroup K} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {t : K} (ht : orderOf t = 2) {Y Y' : Subgroup K}
    (hY : Y ∈ maximals (dSig T C r)) (hY' : Y' ∈ maximals (dSig T C r))
    (hYt : Y ≤ Subgroup.centralizer ({t} : Set K))
    (hY't : Y' ≤ Subgroup.centralizer ({t} : Set K)) : Y' = Y := by
  obtain ⟨U, hU, hUodd⟩ := aSeven_exists_card_three e ht
  have hle : ∀ {Z : Subgroup K}, IsPGroup r Z → Z ≤ Subgroup.centralizer ({t} : Set K) →
      Z ≤ U := fun hZ hZt z hz =>
    hUodd z (Subgroup.mem_centralizer_singleton_iff.mp (hZt hz))
      (odd_orderOf_of_isPGroup hr hr2 hZ hz)
  rcases eq_bot_or_eq_of_le_card_three (hle hY.1.1 hYt) hU with h | h
  · exact hY.2 Y' hY'.1 (h ▸ bot_le)
  rcases eq_bot_or_eq_of_le_card_three (hle hY'.1.1 hY't) hU with h' | h'
  · exact (hY'.2 Y hY.1 (h' ▸ bot_le)).symm
  · rw [h, h']

private theorem aSeven_exists_conj (e : K ≃* A₇) {T : Subgroup K} (hT : IsKleinFour T)
    {t t' : K} (ht : t ∈ T) (ht' : t' ∈ T) (ht1 : t ≠ 1) (ht'1 : t' ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (T : Set K), n * t' * n⁻¹ = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect A₇ :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  have : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT.card_four]; norm_num)
  obtain ⟨S, hTS⟩ := hT2.exists_le_sylow
  have hD : CFSG.GorensteinWalter.HasDihedralSylowTwo K :=
    CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven
  obtain ⟨m, -, ⟨eS⟩⟩ := hD S
  have hcardS : Nat.card (S : Subgroup K) = 8 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv,
      CFSG.ABGDGroups.card_alternatingGroup_fin_seven,
      CFSG.GorensteinWalter.factorization_two_2520]
    norm_num
  have hm : 2 ≤ m := by
    have h := Nat.card_congr eS.toEquiv
    rw [hcardS, DihedralGroup.nat_card] at h
    by_contra hm
    interval_cases m <;> simp_all
  exact exists_conj_of_perfect_dihedral S hm eS hTS hT ht' ht ht'1 ht1

end ASeven

section RPart

variable {K : Type} [Group K]

private theorem exists_rPart (r : ℕ) (Z : Subgroup K)
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, (∃ i : ℕ, a ^ r ^ i = 1) → (∃ j : ℕ, b ^ r ^ j = 1) →
      a * b = b * a) :
    ∃ R : Subgroup K, ∀ x : K, x ∈ R ↔ x ∈ Z ∧ ∃ k : ℕ, x ^ r ^ k = 1 := by
  refine ⟨{ carrier := {x | x ∈ Z ∧ ∃ k : ℕ, x ^ r ^ k = 1}
            mul_mem' := ?_
            one_mem' := ⟨Z.one_mem, 0, by simp⟩
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro a b ⟨ha, i, hi⟩ ⟨hb, j, hj⟩
    refine ⟨Z.mul_mem ha hb, i + j, ?_⟩
    have h1 : a ^ r ^ (i + j) = 1 := by rw [pow_add, pow_mul, hi, one_pow]
    have h2 : b ^ r ^ (i + j) = 1 := by rw [add_comm, pow_add, pow_mul, hj, one_pow]
    have hc : Commute a b := hcomm a ha b hb ⟨i, hi⟩ ⟨j, hj⟩
    rw [hc.mul_pow, h1, h2, one_mul]
  · rintro x ⟨hx, k, hk⟩
    exact ⟨Z.inv_mem hx, k, by rw [inv_pow, hk, inv_one]⟩

private theorem isPGroup_of_rPart {r : ℕ} {Z R : Subgroup K}
    (hR : ∀ x : K, x ∈ R ↔ x ∈ Z ∧ ∃ k : ℕ, x ^ r ^ k = 1) : IsPGroup r R := fun x => by
  obtain ⟨-, k, hk⟩ := (hR x).mp x.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

private theorem rPart_le {r : ℕ} {Z R : Subgroup K}
    (hR : ∀ x : K, x ∈ R ↔ x ∈ Z ∧ ∃ k : ℕ, x ^ r ^ k = 1) : R ≤ Z := fun x hx =>
  ((hR x).mp hx).1

private theorem mem_normalizer_rPart {r : ℕ} {Z R : Subgroup K}
    (hR : ∀ x : K, x ∈ R ↔ x ∈ Z ∧ ∃ k : ℕ, x ^ r ^ k = 1) {g : K}
    (hg : g ∈ Subgroup.normalizer (Z : Set K)) : g ∈ Subgroup.normalizer (R : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hR, hR, ← Subgroup.mem_normalizer_iff.mp hg h]
  refine and_congr_right fun _ => exists_congr fun k => ?_
  rw [conj_pow]
  constructor
  · intro hk
    rw [hk]
    group
  · intro hk
    have := congrArg (fun x => g⁻¹ * x * g) hk
    simpa [mul_assoc] using this

private theorem dvd_card_of_rPart_ne_bot [Finite K] {r : ℕ} (hr : r.Prime) {Z R : Subgroup K}
    (hR : ∀ x : K, x ∈ R ↔ x ∈ Z ∧ ∃ k : ℕ, x ^ r ^ k = 1) (hne : R ≠ ⊥) :
    r ∣ Nat.card Z := by
  obtain ⟨⟨z, hzR⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨hzZ, k, hk⟩ := (hR z).mp hzR
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hz1' hj
  calc r ∣ r ^ j := dvd_pow_self r hj0
    _ = orderOf z := hj.symm
    _ ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hzZ

private theorem dihedral_comm_of_odd {m : ℕ} {Z : Subgroup K} (e : Z ≃* DihedralGroup m)
    {a b : K} (ha : a ∈ Z) (hb : b ∈ Z) (hao : Odd (orderOf a)) (hbo : Odd (orderOf b)) :
    a * b = b * a := by
  have key : ∀ x : Z, Odd (orderOf x) → ∃ i, e x = DihedralGroup.r i := by
    intro x hx
    match hex : e x with
    | DihedralGroup.r i => exact ⟨i, rfl⟩
    | DihedralGroup.sr i =>
      exfalso
      have h2 : orderOf (e x) = 2 := by rw [hex]; exact DihedralGroup.orderOf_sr i
      rw [MulEquiv.orderOf_eq] at h2
      rw [h2] at hx
      exact (Nat.not_odd_iff_even.mpr even_two) hx
  obtain ⟨i, hi⟩ := key ⟨a, ha⟩ (by rwa [Subgroup.orderOf_mk])
  obtain ⟨j, hj⟩ := key ⟨b, hb⟩ (by rwa [Subgroup.orderOf_mk])
  have h : (⟨a, ha⟩ : Z) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    apply e.injective
    rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  exact congrArg Subtype.val h

end RPart

section Arith

open CFSG.GorensteinWalter (IsOddPrimePower)

private theorem exists_epsilon {q : ℕ} (hq : IsOddPrimePower q) :
    ∃ ε : ℤ, (q : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
  obtain ⟨p, f, -, hpodd, -, rfl⟩ := hq
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp hpodd.pow
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h | h
  · exact ⟨1, by unfold Int.ModEq; omega, Or.inl rfl⟩
  · exact ⟨-1, by unfold Int.ModEq; omega, Or.inr rfl⟩

private theorem three_le_of_isOddPrimePower {q : ℕ} (hq : IsOddPrimePower q) : 3 ≤ q := by
  obtain ⟨p, f, hp, hpodd, hf, rfl⟩ := hq
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨c, rfl⟩ := hpodd
    omega
  exact hp3.trans (Nat.le_self_pow (by omega) p)

end Arith

section Linear

open CFSG.ABGDGroups
open CFSG.GorensteinWalter (PGammaL2 PSL2 pGammaL2PSLRange IsOddPrimePower)

variable {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F] {ι : K →* PGammaL2 F}
  {L E : Subgroup K} {S : Sylow 2 K}

private theorem linear_centralizer_comm (hd : IsLinearDecomposition ι L E S) {T : Subgroup K}
    (hT : IsKleinFour T) (hTS : T ≤ S) {a b : K} (ha : a ∈ Subgroup.centralizer (T : Set K))
    (hb : b ∈ Subgroup.centralizer (T : Set K)) : a * b = b * a := by
  have : IsKleinFour T := hT
  rw [(hd.centralizer_kleinFour hT hTS).1] at ha hb
  have hTE : E ≤ Subgroup.centralizer (T : Set K) :=
    hd.le_centralizer.trans (Subgroup.centralizer_le hTS)
  have hTT : T ≤ Subgroup.centralizer (T : Set K) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => kleinFour_comm hy hx
  have hEE : E ≤ Subgroup.centralizer (E : Set K) := by
    have := hd.isCyclic
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have h' : g ^ j * g ^ i = g ^ i * g ^ j := zpow_mul_comm g j i
    rw [hi, hj] at h'
    exact congrArg Subtype.val h'
  have hall : T ⊔ E ≤ Subgroup.centralizer ((T ⊔ E : Subgroup K) : Set K) := by
    apply sup_le
    · exact Subgroup.le_centralizer_iff.mpr (sup_le hTT hTE)
    · exact Subgroup.le_centralizer_iff.mpr
        (sup_le (Subgroup.le_centralizer_iff.mpr hTE) hEE)
  exact ((Subgroup.mem_centralizer_iff.mp (hall hb)) a ha)

omit [Finite K] in
private theorem linear_sq_mem (hd : IsLinearDecomposition ι L E S) {l : K} (hl : l ∈ L) :
    l ^ 2 ∈ linearCore ι := by
  change ι (l ^ 2) ∈ pGammaL2PSLRange F
  rw [map_pow]
  exact sq_mem_pGammaL2PSLRange hd.isOddPrimePower_card
    (hd.isStandardLayer.right_sq ⟨l, hl, rfl⟩)

omit [Finite K] in
private theorem linear_commutator_mem (hd : IsLinearDecomposition ι L E S) (a b : K) :
    (a * b)⁻¹ * (b * a) ∈ linearCore ι := by
  have h : ⁅b⁻¹, a⁻¹⁆ ∈ commutator K :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h' := hd.commutator_le_linearCore h
  rw [commutatorElement_def] at h'
  rw [show (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ by group]
  exact h'

omit [Finite K] in
private theorem linear_exists_mul (hd : IsLinearDecomposition ι L E S) {r : ℕ} (hr : Odd r)
    {y : K} {k : ℕ} (hy : y ^ r ^ k = 1) :
    ∃ l ∈ linearCore ι, ∃ e ∈ E, e ^ r ^ k = 1 ∧ y = l * e := by
  have := hd.normal
  have := hd.linearCore_normal
  have hy' : y ∈ ((L ⊔ E : Subgroup K) : Set K) := by
    rw [hd.sup_eq_top]
    trivial
  rw [Subgroup.normal_mul] at hy'
  obtain ⟨l, hl, e, he, rfl⟩ := hy'
  set π₀ := QuotientGroup.mk' (linearCore ι) with hπ₀
  have hcomm : Commute (π₀ l) (π₀ e) := by
    change π₀ l * π₀ e = π₀ e * π₀ l
    rw [← map_mul, ← map_mul, hπ₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    exact linear_commutator_mem hd l e
  have hN : Odd (r ^ k) := hr.pow
  have hl2 : π₀ l ^ 2 = 1 := by
    rw [← map_pow, hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact linear_sq_mem hd hl
  have hlN : π₀ l ^ r ^ k = π₀ l := by
    obtain ⟨c, hc⟩ := hN
    rw [hc, pow_succ, pow_mul, hl2, one_pow, one_mul]
  have h1 : π₀ l * π₀ e ^ r ^ k = 1 := by
    rw [← hlN, ← hcomm.mul_pow, ← map_mul, ← map_pow, hy, map_one]
  have h2 : π₀ (e ^ (2 * r ^ k)) = 1 := by
    have h3 : π₀ e ^ r ^ k = (π₀ l)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [map_pow, pow_mul', h3, inv_pow, hl2, inv_one]
  have hbot : linearCore ι ⊓ E = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right E hd.linearCore_le).trans hd.inf_eq_bot.le)
  have h3 : e ^ (2 * r ^ k) = 1 := by
    have hmem : e ^ (2 * r ^ k) ∈ linearCore ι ⊓ E :=
      ⟨(QuotientGroup.eq_one_iff _).mp h2, E.pow_mem he _⟩
    rw [hbot] at hmem
    exact hmem
  have heo : Odd (orderOf e) := hd.odd_card.of_dvd_nat (Subgroup.orderOf_dvd_natCard E he)
  have h4 : e ^ r ^ k = 1 := by
    have hdvd : orderOf e ∣ 2 * r ^ k := orderOf_dvd_of_pow_eq_one h3
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((Nat.coprime_two_right.mpr heo).dvd_of_dvd_mul_left hdvd)
  refine ⟨l, ?_, e, he, h4, rfl⟩
  have h5 : π₀ l = 1 := by rwa [← map_pow, h4, map_one, mul_one] at h1
  exact (QuotientGroup.eq_one_iff l).mp h5

omit [Finite K] in
private theorem linear_mem_normalizer_inf (hd : IsLinearDecomposition ι L E S) {t g : K}
    (hg : g ∈ Subgroup.centralizer ({t} : Set K)) :
    g ∈ Subgroup.normalizer ((linearCore ι ⊓ Subgroup.centralizer ({t} : Set K) :
      Subgroup K) : Set K) := by
  have := hd.linearCore_normal
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_inf]
  refine and_congr ?_ ?_
  · constructor
    · intro hh
      exact (inferInstance : (linearCore ι).Normal).conj_mem h hh g
    · intro hh
      have := (inferInstance : (linearCore ι).Normal).conj_mem _ hh g⁻¹
      simpa [mul_assoc] using this
  · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) h)

private theorem linear_le_sup (hd : IsLinearDecomposition ι L E S) {T : Subgroup K}
    [IsKleinFour T] (hTS : T ≤ S) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {P : Subgroup K}
    (hP : ∀ x : K, x ∈ P ↔ x ∈ Subgroup.centralizer (T : Set K) ∧ ∃ k : ℕ, x ^ r ^ k = 1)
    {t : K} (ht : t ∈ T) (ht1 : t ≠ 1) {R : Subgroup K}
    (hR : ∀ x : K, x ∈ R ↔
      x ∈ linearCore ι ⊓ Subgroup.centralizer ({t} : Set K) ∧ ∃ k : ℕ, x ^ r ^ k = 1)
    {Y : Subgroup K} (hY : Y ∈ dSig T (Subgroup.centralizer (T : Set K)) r)
    (hYt : Y ≤ Subgroup.centralizer ({t} : Set K)) : Y ≤ R ⊔ P := by
  have := hd.linearCore_normal
  have hT : IsKleinFour T := inferInstance
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨u, huT, hu1, hut⟩ : ∃ u ∈ T, u ≠ 1 ∧ u ≠ t := by
    have hlt : Subgroup.zpowers t < T := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr ht) fun h => ?_
      have hc := hT.card_four
      rw [← h, Nat.card_zpowers] at hc
      have h2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by
        rw [pow_two]
        exact kleinFour_mul_self' ht)
      rw [hc] at h2
      norm_num at h2
    obtain ⟨u, huT, hu⟩ := IsConcreteLE.exists_of_lt hlt
    exact ⟨u, huT, fun h => hu (h ▸ Subgroup.one_mem _), fun h => hu (h ▸ Subgroup.mem_zpowers t)⟩
  have hu2 : orderOf u = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact kleinFour_mul_self' huT) hu1
  have hYodd : Odd (Nat.card Y) := odd_card_of_isPGroup hr hr2 hY.1
  have huN : u ∈ Subgroup.normalizer (Y : Set K) := hY.2.1 huT
  have hEC : E ≤ Subgroup.centralizer (T : Set K) := by
    rw [(hd.centralizer_kleinFour hT hTS).1]
    exact le_sup_right
  have hCt : Subgroup.centralizer (T : Set K) ≤ Subgroup.centralizer ({t} : Set K) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht)
  have hut' : u ∈ Subgroup.centralizer ({t} : Set K) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (kleinFour_comm huT ht)
  intro y hy
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, rfl⟩ :=
    (CFSG.OddInversion.fixed_mul_inverted_bijOn hYodd hu2 huN).surjOn hy
  obtain ⟨hcY, hcu⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨hjY, hju⟩ := hj
  have hcP : c ∈ P := by
    refine (hP c).mpr ⟨mem_centralizer_of_mem_centralizer_pair ht huT ht1 hu1 hut.symm
      (hYt hcY) hcu, ?_⟩
    obtain ⟨k, hk⟩ := hY.1 ⟨c, hcY⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨k, hk⟩ := hY.1 ⟨j, hjY⟩
  have hk' : j ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨l, hl, e, he, -, hje⟩ := linear_exists_mul hd hrodd hk'
  have heC : e ∈ Subgroup.centralizer (T : Set K) := hEC he
  have heu : u * e = e * u := Subgroup.mem_centralizer_iff.mp heC u huT
  have hlt : l ∈ Subgroup.centralizer ({t} : Set K) := by
    have : l = j * e⁻¹ := by rw [hje]; group
    rw [this]
    exact Subgroup.mul_mem _ (hYt hjY) (Subgroup.inv_mem _ (hCt heC))
  have hj2 : j ^ 2 = l * (u * l⁻¹ * u⁻¹) := by
    have h1 : u * j * u⁻¹ = j⁻¹ := hju
    calc j ^ 2 = j * (u * j * u⁻¹)⁻¹ := by rw [h1, inv_inv, pow_two]
      _ = l * e * (u * (l * e) * u⁻¹)⁻¹ := by rw [hje]
      _ = l * e * (u * l * u⁻¹ * (u * e * u⁻¹))⁻¹ := by group
      _ = l * e * (u * l * u⁻¹ * e)⁻¹ := by rw [heu, mul_inv_cancel_right]
      _ = l * (u * l⁻¹ * u⁻¹) := by group
  have hj2Z : j ^ 2 ∈ linearCore ι ⊓ Subgroup.centralizer ({t} : Set K) := by
    rw [hj2]
    refine ⟨Subgroup.mul_mem _ hl ((inferInstance : (linearCore ι).Normal).conj_mem _
      (Subgroup.inv_mem _ hl) u), Subgroup.mul_mem _ hlt (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hut' (Subgroup.inv_mem _ hlt)) (Subgroup.inv_mem _ hut'))⟩
  have hj2R : j ^ 2 ∈ R := (hR _).mpr ⟨hj2Z, k, by rw [← pow_mul, mul_comm, pow_mul, hk', one_pow]⟩
  have hjR : j ∈ R := mem_of_sq_mem (odd_orderOf_of_isPGroup hr hr2 hY.1 hjY) hj2R
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcP) (Subgroup.mem_sup_left hjR)

omit [Finite K] in
private theorem linear_sup_mem (hd : IsLinearDecomposition ι L E S) {T : Subgroup K}
    [IsKleinFour T] {r : ℕ} {P : Subgroup K}
    (hP : ∀ x : K, x ∈ P ↔ x ∈ Subgroup.centralizer (T : Set K) ∧ ∃ k : ℕ, x ^ r ^ k = 1)
    {t : K} (ht : t ∈ T) {R : Subgroup K}
    (hR : ∀ x : K, x ∈ R ↔
      x ∈ linearCore ι ⊓ Subgroup.centralizer ({t} : Set K) ∧ ∃ k : ℕ, x ^ r ^ k = 1) :
    R ⊔ P ∈ dSig T (Subgroup.centralizer (T : Set K)) r ∧
      R ⊔ P ≤ Subgroup.centralizer ({t} : Set K) := by
  have hT : IsKleinFour T := inferInstance
  have hCt : Subgroup.centralizer (T : Set K) ≤ Subgroup.centralizer ({t} : Set K) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht)
  have hTC : T ≤ Subgroup.centralizer (T : Set K) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => kleinFour_comm hy hx
  have hNR : Subgroup.centralizer ({t} : Set K) ≤ Subgroup.normalizer (R : Set K) :=
    fun g hg => mem_normalizer_rPart hR (linear_mem_normalizer_inf hd hg)
  have hNP : Subgroup.centralizer (T : Set K) ≤ Subgroup.normalizer (P : Set K) :=
    fun g hg => mem_normalizer_rPart hP (Subgroup.le_normalizer hg)
  have hCN : Subgroup.centralizer (T : Set K) ≤ Subgroup.normalizer ((R ⊔ P : Subgroup K) :
      Set K) := fun g hg => mem_normalizer_sup (hNR (hCt hg)) (hNP hg)
  refine ⟨⟨IsPGroup.to_sup_of_normal_left' (isPGroup_of_rPart hR) (isPGroup_of_rPart hP)
    ((rPart_le hP).trans (hCt.trans hNR)), hTC.trans hCN,
    (mul_comm_of_le_normalizer hCN).symm⟩, sup_le ((rPart_le hR).trans inf_le_right)
    ((rPart_le hP).trans hCt)⟩

private theorem linear_card_inf_centralizer (hd : IsLinearDecomposition ι L E S) {ε : ℤ}
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1) {u : K}
    (hu : orderOf u = 2) :
    (u ∈ linearCore ι → (Nat.card (linearCore ι ⊓ Subgroup.centralizer ({u} : Set K) :
      Subgroup K) : ℤ) = Nat.card F - ε) ∧
    (u ∉ linearCore ι → (Nat.card (linearCore ι ⊓ Subgroup.centralizer ({u} : Set K) :
      Subgroup K) : ℤ) = Nat.card F + ε) := by
  refine ⟨fun huL => ?_, fun huL => ?_⟩
  · obtain ⟨m, hm, ⟨e⟩⟩ := hd.centralizer_dihedral_of_mem_linearCore hε hε1 hu huL
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, ← hm]
    push_cast
    ring
  · obtain ⟨m, hm, ⟨e⟩⟩ := hd.centralizer_dihedral_of_not_mem_linearCore hε hε1 hu huL
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, ← hm]
    push_cast
    ring

private theorem linear_not_dvd_both (hd : IsLinearDecomposition ι L E S) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {u u' : K} (hu : orderOf u = 2) (hu' : orderOf u' = 2)
    (huL : u ∈ linearCore ι) (hu'L : u' ∉ linearCore ι)
    (h : r ∣ Nat.card (linearCore ι ⊓ Subgroup.centralizer ({u} : Set K) : Subgroup K))
    (h' : r ∣ Nat.card (linearCore ι ⊓ Subgroup.centralizer ({u'} : Set K) : Subgroup K)) :
    False := by
  obtain ⟨ε, hε, hε1⟩ := exists_epsilon hd.isOddPrimePower_card
  have h1 := (linear_card_inf_centralizer hd hε hε1 hu).1 huL
  have h2 := (linear_card_inf_centralizer hd hε hε1 hu').2 hu'L
  have hd1 : (r : ℤ) ∣ (Nat.card F : ℤ) - ε := by
    rw [← h1]
    exact Int.natCast_dvd_natCast.mpr h
  have hd2 : (r : ℤ) ∣ (Nat.card F : ℤ) + ε := by
    rw [← h2]
    exact Int.natCast_dvd_natCast.mpr h'
  have hd3 : (r : ℤ) ∣ 2 := by
    have h3 := dvd_sub hd2 hd1
    rcases hε1 with rfl | rfl
    · rwa [show (Nat.card F : ℤ) + 1 - (Nat.card F - 1) = 2 by ring] at h3
    · rw [show (Nat.card F : ℤ) + -1 - (Nat.card F - -1) = -2 by ring] at h3
      exact dvd_neg.mp h3
  have hd4 : r ∣ 2 := by exact_mod_cast hd3
  have := Nat.le_of_dvd (by norm_num) hd4
  have := hr.two_le
  omega

private theorem linear_exists_conj_of_le (hd : IsLinearDecomposition ι L E S) {T : Subgroup K}
    [IsKleinFour T] (hTS : T ≤ S) (hTL : T ≤ linearCore ι) {t t' : K} (ht : t ∈ T)
    (ht' : t' ∈ T) (ht1 : t ≠ 1) (ht'1 : t' ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (T : Set K), n * t' * n⁻¹ = t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsKleinFour T := inferInstance
  have hF := hd.isOddPrimePower_card
  obtain ⟨eM⟩ := hd.nonempty_linearCore_mulEquiv
  have hV : IsKleinFour (T.subgroupOf (linearCore ι)) := isKleinFour_subgroupOf hTL hT
  have hnorm : (Subgroup.normalizer (T : Set K)).comap (linearCore ι).subtype =
      Subgroup.normalizer ((T.subgroupOf (linearCore ι) : Subgroup (linearCore ι)) :
        Set (linearCore ι)) :=
    Subgroup.comap_normalizer_eq_of_le_range (by simpa using hTL)
  suffices h : ∃ n₀ ∈ Subgroup.normalizer ((T.subgroupOf (linearCore ι) :
      Subgroup (linearCore ι)) : Set (linearCore ι)),
      n₀ * ⟨t', hTL ht'⟩ * n₀⁻¹ = ⟨t, hTL ht⟩ by
    obtain ⟨n₀, hn₀, hn₀t⟩ := h
    rw [← hnorm] at hn₀
    exact ⟨n₀, hn₀, congrArg Subtype.val hn₀t⟩
  have htV : (⟨t, hTL ht⟩ : linearCore ι) ∈ T.subgroupOf (linearCore ι) := ht
  have ht'V : (⟨t', hTL ht'⟩ : linearCore ι) ∈ T.subgroupOf (linearCore ι) := ht'
  have ht1' : (⟨t, hTL ht⟩ : linearCore ι) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ht'1' : (⟨t', hTL ht'⟩ : linearCore ι) ≠ 1 := fun h => ht'1 (congrArg Subtype.val h)
  have hV2 : IsPGroup 2 (T.subgroupOf (linearCore ι)) :=
    IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  obtain ⟨P₀, hVP₀⟩ := hV2.exists_le_sylow
  have hDM : CFSG.GorensteinWalter.HasDihedralSylowTwo (linearCore ι) :=
    CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eM
      (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hF)
  obtain ⟨m, hm1, ⟨eP⟩⟩ := hDM P₀
  have hcardP₀ : Nat.card (P₀ : Subgroup (linearCore ι)) = 2 * 2 ^ m := by
    rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have hcardM : Nat.card (linearCore ι) = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eM.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F hF]
  have hq3 := three_le_of_isOddPrimePower hF
  by_cases hm : 2 ≤ m
  · have h3 : 3 < Nat.card F := by
      by_contra h3
      have hq : Nat.card F = 3 := by omega
      have hM12 : Nat.card (linearCore ι) = 12 := by rw [hcardM, hq]; norm_num
      have hdvd : Nat.card (P₀ : Subgroup (linearCore ι)) ∣ 12 :=
        hM12 ▸ Subgroup.card_subgroup_dvd_card _
      rw [hcardP₀] at hdvd
      have h8 : 8 ∣ 2 * 2 ^ m := by
        obtain ⟨c, rfl⟩ : ∃ c, m = c + 2 := ⟨m - 2, by omega⟩
        exact ⟨2 ^ c, by ring⟩
      have := h8.trans hdvd
      norm_num at this
    have : Group.IsPerfect (PSL2 F) :=
      CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three F h3
    have : Group.IsPerfect (linearCore ι) :=
      Group.IsPerfect.ofSurjective (f := eM.symm.toMonoidHom) eM.symm.surjective
    exact exists_conj_of_perfect_dihedral P₀ hm eP hVP₀ hV ht'V htV ht'1' ht1'
  · have hm1' : m = 1 := by omega
    have hVeq : T.subgroupOf (linearCore ι) = P₀ := Subgroup.eq_of_le_of_card_ge hVP₀ (by
      rw [hcardP₀, hV.card_four, hm1']
      norm_num)
    have : IsKleinFour (P₀ : Subgroup (linearCore ι)) := hVeq ▸ hV
    have hC : Subgroup.centralizer ((P₀ : Subgroup (linearCore ι)) : Set (linearCore ι)) ≤
        P₀ := by
      rw [← hVeq]
      intro g hg
      have hgC : (g : K) ∈ Subgroup.centralizer (T : Set K) := by
        rw [Subgroup.mem_centralizer_iff]
        intro τ hτ
        have := Subgroup.mem_centralizer_iff.mp hg ⟨τ, hTL hτ⟩ hτ
        exact congrArg Subtype.val this
      have hgK : (g : K) ∈ L ⊓ Subgroup.centralizer (T : Set K) :=
        Subgroup.mem_inf.mpr ⟨hd.linearCore_le g.2, hgC⟩
      rw [(hd.centralizer_kleinFour hT hTS).2] at hgK
      exact hgK
    have hnc : ∀ N : Subgroup (linearCore ι), N.Normal → Odd (Nat.card N) → N = ⊥ := by
      intro N hN hNodd
      have : (N.map eM.toMonoidHom).Normal := hN.map _ eM.surjective
      have hbot := eq_bot_of_normal_of_odd_card_psl2 hF (N.map eM.toMonoidHom)
        (by rwa [Subgroup.card_map_of_injective eM.injective])
      exact (Subgroup.map_eq_bot_iff_of_injective _ eM.injective).mp hbot
    have hcard4 : 4 < Nat.card (linearCore ι) := by
      rw [hcardM]
      have h1 : 8 ≤ Nat.card F ^ 2 - 1 := by
        have : 9 ≤ Nat.card F ^ 2 := by nlinarith
        omega
      have h2 : 3 * 8 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul hq3 h1
      generalize Nat.card F * (Nat.card F ^ 2 - 1) = x at h2 ⊢
      omega
    obtain ⟨g, hgN, hfpf⟩ := exists_fixedPointFree_of_sylow P₀ hC hnc hcard4
    rw [hVeq]
    exact exists_conj_of_fixedPointFree hgN hfpf (hVeq ▸ ht'V) (hVeq ▸ htV) ht'1' ht1'

private theorem linear_exists_conj_of_not_mem (hd : IsLinearDecomposition ι L E S)
    {T : Subgroup K} [IsKleinFour T] (hTS : T ≤ S) {t t' : K} (ht : t ∈ T) (ht' : t' ∈ T)
    (ht1 : t ≠ 1) (ht'1 : t' ≠ 1) (htt' : t ≠ t') (htL : t ∉ linearCore ι)
    (ht'L : t' ∉ linearCore ι) :
    ∃ n ∈ Subgroup.normalizer (T : Set K), n * t' * n⁻¹ = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsKleinFour T := inferInstance
  have := hd.linearCore_normal
  have hTL : T ≤ L := hTS.trans (hd.sylow_le S)
  have hw : t * t' ∈ linearCore ι := by
    rcases hd.relIndex_linearCore with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h (hTL ht)) htL
    · have h' := Subgroup.mul_mem_iff_of_index_two h (a := ⟨t, hTL ht⟩) (b := ⟨t', hTL ht'⟩)
      have : (⟨t, hTL ht⟩ : L) * ⟨t', hTL ht'⟩ ∈ (linearCore ι).subgroupOf L :=
        h'.mpr (iff_of_false htL ht'L)
      exact this
  have hw1 : t * t' ≠ 1 := by
    intro h
    apply htt'
    calc t = t * t' * t' := by rw [mul_assoc, kleinFour_mul_self' ht', mul_one]
      _ = t' := by rw [h, one_mul]
  have hST : T ≠ (S : Subgroup K) := by
    intro hST
    obtain ⟨eM⟩ := hd.nonempty_linearCore_mulEquiv
    have hDM : CFSG.GorensteinWalter.HasDihedralSylowTwo (linearCore ι) :=
      CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eM
        (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hd.isOddPrimePower_card)
    obtain ⟨Q⟩ : Nonempty (Sylow 2 (linearCore ι)) := inferInstance
    obtain ⟨m, hm, ⟨eQ⟩⟩ := hDM Q
    obtain ⟨e'⟩ := nonempty_sylow_equiv_inf S (linearCore ι) Q
    have hc : Nat.card (linearCore ι ⊓ (S : Subgroup K) : Subgroup K) = 2 * 2 ^ m := by
      rw [← Nat.card_congr e'.toEquiv, Nat.card_congr eQ.toEquiv, DihedralGroup.nat_card]
    have h4 : Nat.card T ≤ Nat.card (linearCore ι ⊓ T : Subgroup K) := by
      rw [hST, hc, ← hST, hT.card_four]
      have : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2 |>.trans' le_rfl
      omega
    have hle := Subgroup.eq_of_le_of_card_ge (inf_le_right : linearCore ι ⊓ T ≤ T) h4
    have htLT : t ∈ linearCore ι ⊓ T := by
      rw [hle]
      exact ht
    exact htL (Subgroup.mem_inf.mp htLT).1
  obtain ⟨v, hvS, hvN, hvT⟩ := exists_mem_normalizer_not_mem S.isPGroup' hTS hST
  have hvC : v ∉ Subgroup.centralizer (T : Set K) := by
    intro hvC
    have : v ∈ L ⊓ Subgroup.centralizer (T : Set K) := ⟨hd.sylow_le S hvS, hvC⟩
    rw [(hd.centralizer_kleinFour hT hTS).2] at this
    exact hvT this
  have hconj : ∀ u ∈ T, v * u * v⁻¹ ∈ T := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hvN u).mp hu
  have hne1 : ∀ u : K, u ≠ 1 → v * u * v⁻¹ ≠ 1 := fun u hu h =>
    hu (calc u = v⁻¹ * (v * u * v⁻¹) * v := by group
      _ = 1 := by rw [h]; group)
  have hvw : v * (t * t') * v⁻¹ = t * t' := by
    have hmem : v * (t * t') * v⁻¹ ∈ linearCore ι :=
      (inferInstance : (linearCore ι).Normal).conj_mem _ hw v
    rcases kleinFour_cases ht ht' (hconj _ (T.mul_mem ht ht')) ht1 ht'1 htt' with
      h | h | h | h
    · exact absurd h (hne1 _ hw1)
    · exact absurd (h ▸ hmem) htL
    · exact absurd (h ▸ hmem) ht'L
    · exact h
  rcases kleinFour_cases ht ht' (hconj t' ht') ht1 ht'1 htt' with h | h | h | h
  · exact absurd h (hne1 _ ht'1)
  · exact ⟨v, hvN, h⟩
  · exfalso
    apply hvC
    refine mem_centralizer_of_mem_centralizer_pair ht' (T.mul_mem ht ht') ht'1 hw1 ?_ ?_ ?_
    · intro h'
      apply ht1
      calc t = t * t' * t' := by rw [mul_assoc, kleinFour_mul_self' ht', mul_one]
        _ = 1 := by rw [← h', kleinFour_mul_self' ht']
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc v * t' = v * t' * v⁻¹ * v := by group
        _ = t' * v := by rw [h]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc v * (t * t') = v * (t * t') * v⁻¹ * v := by group
        _ = t * t' * v := by rw [hvw]
  · exfalso
    have : t' = t * t' := by
      have h2 : v * t' * v⁻¹ = v * (t * t') * v⁻¹ := by rw [h, hvw]
      calc t' = v⁻¹ * (v * t' * v⁻¹) * v := by group
        _ = v⁻¹ * (v * (t * t') * v⁻¹) * v := by rw [h2]
        _ = t * t' := by group
    apply ht1
    calc t = t * t' * t' := by rw [mul_assoc, kleinFour_mul_self' ht', mul_one]
      _ = t' * t' := by rw [← this]
      _ = 1 := kleinFour_mul_self' ht'

private theorem linear_exists_conjSub (hd : IsLinearDecomposition ι L E S) {T : Subgroup K}
    (hT : IsKleinFour T) (hTS : T ≤ S) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X X' : Subgroup K} {t t' : K} (ht : t ∈ T) (ht' : t' ∈ T) (ht1 : t ≠ 1) (ht'1 : t' ≠ 1)
    (hX : X ∈ maximals (dSig T (Subgroup.centralizer (T : Set K)) r))
    (hX' : X' ∈ maximals (dSig T (Subgroup.centralizer (T : Set K)) r))
    (hXt : X ≤ Subgroup.centralizer ({t} : Set K))
    (hX't : X' ≤ Subgroup.centralizer ({t'} : Set K)) :
    ∃ n ∈ Subgroup.normalizer (T : Set K), conjSub n X' = X := by
  have : IsKleinFour T := hT
  obtain ⟨ε, hε, hε1⟩ := exists_epsilon hd.isOddPrimePower_card
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨P, hP⟩ := exists_rPart r (Subgroup.centralizer (T : Set K))
    (fun a ha b hb _ _ => linear_centralizer_comm hd hT hTS ha hb)
  have hRex : ∀ u : K, orderOf u = 2 → ∃ R : Subgroup K, ∀ x : K, x ∈ R ↔
      x ∈ linearCore ι ⊓ Subgroup.centralizer ({u} : Set K) ∧ ∃ k : ℕ, x ^ r ^ k = 1 := by
    intro u hu
    have hZ : ∃ m : ℕ, Nonempty ((linearCore ι ⊓ Subgroup.centralizer ({u} : Set K) :
        Subgroup K) ≃* DihedralGroup m) := by
      by_cases huL : u ∈ linearCore ι
      · obtain ⟨m, -, he⟩ := hd.centralizer_dihedral_of_mem_linearCore hε hε1 hu huL
        exact ⟨m, he⟩
      · obtain ⟨m, -, he⟩ := hd.centralizer_dihedral_of_not_mem_linearCore hε hε1 hu huL
        exact ⟨m, he⟩
    obtain ⟨m, ⟨eZ⟩⟩ := hZ
    exact exists_rPart r _ fun a ha b hb ⟨i, hi⟩ ⟨j, hj⟩ =>
      dihedral_comm_of_odd eZ ha hb (Odd.of_dvd_nat hrodd.pow (orderOf_dvd_of_pow_eq_one hi))
        (Odd.of_dvd_nat hrodd.pow (orderOf_dvd_of_pow_eq_one hj))
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact kleinFour_mul_self' ht) ht1
  have ht'2 : orderOf t' = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact kleinFour_mul_self' ht') ht'1
  obtain ⟨R, hR⟩ := hRex t ht2
  obtain ⟨R', hR'⟩ := hRex t' ht'2
  have hW := linear_sup_mem hd hP ht hR
  have hW' := linear_sup_mem hd hP ht' hR'
  have hXeq : R ⊔ P = X := hX.2 _ hW.1 (linear_le_sup hd hTS hr hr2 hP ht ht1 hR hX.1 hXt)
  have hX'eq : R' ⊔ P = X' :=
    hX'.2 _ hW'.1 (linear_le_sup hd hTS hr hr2 hP ht' ht'1 hR' hX'.1 hX't)
  have huniq : ∀ Y ∈ maximals (dSig T (Subgroup.centralizer (T : Set K)) r),
      Y ≤ Subgroup.centralizer ({t} : Set K) → Y = X := by
    intro Y hY hYt
    rw [← hXeq]
    exact (hY.2 _ hW.1 (linear_le_sup hd hTS hr hr2 hP ht ht1 hR hY.1 hYt)).symm
  refine exists_conjSub_eq_of_unique hX' hX't huniq ?_
  by_cases htt : t = t'
  · left
    have hRR : R = R' := Subgroup.ext fun x => by rw [hR, hR', htt]
    rw [← hXeq, ← hX'eq, hRR]
  by_cases hR0 : R = ⊥
  · left
    have hle : X ≤ X' := by
      rw [← hXeq, ← hX'eq, hR0, bot_sup_eq]
      exact le_sup_right
    exact (hX.2 X' hX'.1 hle).symm
  by_cases hR'0 : R' = ⊥
  · left
    have hle : X' ≤ X := by
      rw [← hXeq, ← hX'eq, hR'0, bot_sup_eq]
      exact le_sup_right
    exact hX'.2 X hX.1 hle
  right
  have hdvd := dvd_card_of_rPart_ne_bot hr hR hR0
  have hdvd' := dvd_card_of_rPart_ne_bot hr hR' hR'0
  by_cases htL : t ∈ linearCore ι <;> by_cases ht'L : t' ∈ linearCore ι
  · have hTL : T ≤ linearCore ι := fun τ hτ => by
      rcases kleinFour_cases ht ht' hτ ht1 ht'1 htt with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact htL
      · exact ht'L
      · exact Subgroup.mul_mem _ htL ht'L
    exact linear_exists_conj_of_le hd hTS hTL ht ht' ht1 ht'1
  · exact (linear_not_dvd_both hd hr hr2 ht2 ht'2 htL ht'L hdvd hdvd').elim
  · exact (linear_not_dvd_both hd hr hr2 ht'2 ht2 ht'L htL hdvd' hdvd).elim
  · exact linear_exists_conj_of_not_mem hd hTS ht ht' ht1 ht'1 htt htL ht'L

end Linear

section Core

variable {K : Type} [Group K] [Finite K]

private theorem dGroup_exists_conjSub (hK : IsDGroup K) (hO : CFSG.oddCore K = ⊥)
    (hW : ¬ ∃ n, HasWreathedSylow K n) {T : Subgroup K} (hT : IsKleinFour T) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {X X' : Subgroup K} {t t' : K} (ht : t ∈ T) (ht' : t' ∈ T)
    (ht1 : t ≠ 1) (ht'1 : t' ≠ 1)
    (hX : X ∈ maximals (dSig T (Subgroup.centralizer (T : Set K)) r))
    (hX' : X' ∈ maximals (dSig T (Subgroup.centralizer (T : Set K)) r))
    (hXt : X ≤ Subgroup.centralizer ({t} : Set K))
    (hX't : X' ≤ Subgroup.centralizer ({t'} : Set K)) :
    ∃ n ∈ Subgroup.normalizer (T : Set K), conjSub n X' = X := by
  have : IsKleinFour T := hT
  rcases CFSG.ABGDGroups.aSeven_or_linearDecomposition hK hO hW with he | hlin
  · obtain ⟨e⟩ := he
    have ht2 : orderOf t = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact kleinFour_mul_self' ht) ht1
    exact exists_conjSub_eq_of_unique hX' hX't
      (fun Y hY hYt => aSeven_eq_of_maximals e hr hr2 ht2 hX hY hXt hYt)
      (Or.inr (aSeven_exists_conj e hT ht ht' ht1 ht'1))
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT.card_four]; norm_num)
    obtain ⟨S, hTS⟩ := hT2.exists_le_sylow
    obtain ⟨F, _, _, ι, L, E, hd⟩ := hlin S
    exact linear_exists_conjSub hd hT hTS hr hr2 ht ht' ht1 ht'1 hX hX' hXt hX't

end Core

section Lift

variable {G : Type} [Group G] [Finite G]

private def qbar (H X : Subgroup G) : Subgroup (H ⧸ CFSG.oddCore H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.oddCore H))

private def qlift (H : Subgroup G) (Y : Subgroup (H ⧸ CFSG.oddCore H)) : Subgroup G :=
  (Y.comap (QuotientGroup.mk' (CFSG.oddCore H))).map H.subtype

omit [Finite G] in
private theorem mem_qbar {H X : Subgroup G} {x : H} (hx : (x : G) ∈ X) :
    QuotientGroup.mk' (CFSG.oddCore H) x ∈ qbar H X :=
  ⟨x, hx, rfl⟩

omit [Finite G] in
private theorem mem_qbar_iff {H X : Subgroup G} {y : H ⧸ CFSG.oddCore H} :
    y ∈ qbar H X ↔ ∃ x : H, (x : G) ∈ X ∧ QuotientGroup.mk' (CFSG.oddCore H) x = y := by
  unfold qbar
  rw [Subgroup.mem_map]
  rfl

omit [Finite G] in
private theorem mem_qlift {H : Subgroup G} {Y : Subgroup (H ⧸ CFSG.oddCore H)} {g : G} :
    g ∈ qlift H Y ↔ ∃ hg : g ∈ H, QuotientGroup.mk' (CFSG.oddCore H) ⟨g, hg⟩ ∈ Y := by
  unfold qlift
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hgY⟩
    exact ⟨⟨g, hg⟩, hgY, rfl⟩

omit [Finite G] in
private theorem qlift_le (H : Subgroup G) (Y : Subgroup (H ⧸ CFSG.oddCore H)) :
    qlift H Y ≤ H := fun _ hg => (mem_qlift.mp hg).1

omit [Finite G] in
private theorem oddCoreIn_le_qlift (H : Subgroup G) (Y : Subgroup (H ⧸ CFSG.oddCore H)) :
    oddCoreIn H ≤ qlift H Y := by
  rintro _ ⟨o, ho, rfl⟩
  refine mem_qlift.mpr ⟨o.2, ?_⟩
  have h1 : QuotientGroup.mk' (CFSG.oddCore H) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  show QuotientGroup.mk' (CFSG.oddCore H) o ∈ Y
  rw [h1]
  exact Y.one_mem

omit [Finite G] in
private theorem qlift_qbar {H X : Subgroup G} (hOX : oddCoreIn H ≤ X) (hXH : X ≤ H) :
    qlift H (qbar H X) = X := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgH, hgq⟩ := mem_qlift.mp hg
    obtain ⟨x, hxX, hxe⟩ := mem_qbar_iff.mp hgq
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxe
    have ho : ((x⁻¹ * ⟨g, hgH⟩ : H) : G) ∈ X := hOX ⟨_, hxe, rfl⟩
    have : g = (x : G) * ((x⁻¹ * ⟨g, hgH⟩ : H) : G) := by simp
    rw [this]
    exact X.mul_mem hxX ho
  · intro g hg
    exact mem_qlift.mpr ⟨hXH hg, mem_qbar hg⟩

omit [Finite G] in
private theorem qlift_qbar_eq_sup {H X : Subgroup G} (hXH : X ≤ H) :
    qlift H (qbar H X) = X ⊔ oddCoreIn H := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgH, hgq⟩ := mem_qlift.mp hg
    obtain ⟨x, hxX, hxe⟩ := mem_qbar_iff.mp hgq
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxe
    have ho : ((x⁻¹ * ⟨g, hgH⟩ : H) : G) ∈ oddCoreIn H := ⟨_, hxe, rfl⟩
    have : g = (x : G) * ((x⁻¹ * ⟨g, hgH⟩ : H) : G) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hxX ho
  · exact sup_le (fun g hg => mem_qlift.mpr ⟨hXH hg, mem_qbar hg⟩) (oddCoreIn_le_qlift H _)

omit [Finite G] in
private theorem qbar_qlift (H : Subgroup G) (Y : Subgroup (H ⧸ CFSG.oddCore H)) :
    qbar H (qlift H Y) = Y := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_qbar_iff.mp hy
    obtain ⟨_, hxY⟩ := mem_qlift.mp hx
    exact hxY
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore H) y
    exact mem_qbar (mem_qlift.mpr ⟨x.2, hy⟩)

omit [Finite G] in
private theorem qlift_mono {H : Subgroup G} {Y Y' : Subgroup (H ⧸ CFSG.oddCore H)}
    (h : Y ≤ Y') : qlift H Y ≤ qlift H Y' := fun _ hg => by
  obtain ⟨hgH, hgY⟩ := mem_qlift.mp hg
  exact mem_qlift.mpr ⟨hgH, h hgY⟩

private theorem mul_comm_of_subset' {Q : Type*} [Group Q] {A B : Subgroup Q}
    (h : (A : Set Q) * B ⊆ B * A) : (A : Set Q) * B = B * A := by
  refine Set.Subset.antisymm h fun x hx => ?_
  obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨b', hb', a', ha', he⟩ :=
    Set.mem_mul.mp (h (Set.mem_mul.mpr ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, rfl⟩))
  refine Set.mem_mul.mpr ⟨a'⁻¹, A.inv_mem ha', b'⁻¹, B.inv_mem hb', ?_⟩
  rw [← mul_inv_rev, he, mul_inv_rev, inv_inv, inv_inv]

omit [Finite G] in
private theorem qbar_mul_comm {H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H)
    (h : (A : Set G) * B = B * A) :
    ((qbar H A : Subgroup _) : Set (H ⧸ CFSG.oddCore H)) * (qbar H B : Set (H ⧸ CFSG.oddCore H)) =
      (qbar H B : Set (H ⧸ CFSG.oddCore H)) * (qbar H A : Set (H ⧸ CFSG.oddCore H)) := by
  refine mul_comm_of_subset' ?_
  intro z hz
  obtain ⟨_, ha, _, hb, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨a, haA, rfl⟩ := mem_qbar_iff.mp ha
  obtain ⟨b, hbB, rfl⟩ := mem_qbar_iff.mp hb
  have hab : (a : G) * b ∈ (B : Set G) * A := h ▸ Set.mem_mul.mpr ⟨(a : G), haA, (b : G), hbB, rfl⟩
  obtain ⟨b', hb', a', ha', he⟩ := Set.mem_mul.mp hab
  refine Set.mem_mul.mpr ⟨_, mem_qbar (x := ⟨b', hB hb'⟩) hb', _, mem_qbar (x := ⟨a', hA ha'⟩) ha',
    ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext he

omit [Finite G] in
private theorem qlift_mul_comm {H C : Subgroup G} (hCH : C ≤ H)
    {Y : Subgroup (H ⧸ CFSG.oddCore H)}
    (h : (Y : Set (H ⧸ CFSG.oddCore H)) * (qbar H C : Set (H ⧸ CFSG.oddCore H)) =
      (qbar H C : Set (H ⧸ CFSG.oddCore H)) * (Y : Set (H ⧸ CFSG.oddCore H))) :
    ((qlift H Y : Subgroup G) : Set G) * C = C * qlift H Y := by
  refine mul_comm_of_subset' ?_
  intro z hz
  obtain ⟨y, hy, c, hc, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨hyH, hyY⟩ := mem_qlift.mp hy
  have hmem : QuotientGroup.mk' (CFSG.oddCore H) ⟨y, hyH⟩ *
      QuotientGroup.mk' (CFSG.oddCore H) ⟨c, hCH hc⟩ ∈
        (qbar H C : Set (H ⧸ CFSG.oddCore H)) * (Y : Set (H ⧸ CFSG.oddCore H)) :=
    h ▸ Set.mem_mul.mpr ⟨_, hyY, _, mem_qbar (x := ⟨c, hCH hc⟩) hc, rfl⟩
  obtain ⟨_, hc₁, yb, hyb, he⟩ := Set.mem_mul.mp hmem
  obtain ⟨c₁, hc₁C, rfl⟩ := mem_qbar_iff.mp hc₁
  refine Set.mem_mul.mpr ⟨(c₁ : G), hc₁C, (c₁ : G)⁻¹ * (y * c), ?_, by group⟩
  refine mem_qlift.mpr ⟨H.mul_mem (H.inv_mem c₁.2) (H.mul_mem hyH (hCH hc)), ?_⟩
  have h1 : (⟨(c₁ : G)⁻¹ * (y * c), H.mul_mem (H.inv_mem c₁.2) (H.mul_mem hyH (hCH hc))⟩ : H) =
      c₁⁻¹ * (⟨y, hyH⟩ * ⟨c, hCH hc⟩) := Subtype.ext rfl
  rw [h1, map_mul, map_mul, map_inv, ← he, inv_mul_cancel_left]
  exact hyb

variable {σ : Setting G} {r : ℕ}

omit [Finite G] in
private theorem qbar_mem_dSig {H X : Subgroup G} (hCH : σ.C ≤ H)
    (hX : X ∈ liftedSignalizers σ H r) : qbar H X ∈ dSig (qbar H σ.T) (qbar H σ.C) r := by
  obtain ⟨hOX, hXH, hXr, hTX, hXC⟩ := hX
  refine ⟨fun y => ?_, ?_, qbar_mul_comm hXH hCH hXC⟩
  · obtain ⟨x, hxX, hxe⟩ := mem_qbar_iff.mp y.2
    obtain ⟨k, hk⟩ := hXr _ hxX
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← hxe, ← map_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    obtain ⟨o, ho, hoe⟩ := hk
    have : o = x ^ r ^ k := Subtype.ext (by simpa using hoe)
    rw [← this]
    exact ho
  · unfold qbar
    exact (Subgroup.map_mono (subgroupOf_le_normalizer hTX)).trans (Subgroup.le_normalizer_map _)

omit [Finite G] in
private theorem qlift_mem {H : Subgroup G} (hTH : σ.T ≤ H) (hCH : σ.C ≤ H)
    {Y : Subgroup (H ⧸ CFSG.oddCore H)} (hY : Y ∈ dSig (qbar H σ.T) (qbar H σ.C) r) :
    qlift H Y ∈ liftedSignalizers σ H r := by
  obtain ⟨hYr, hTY, hYC⟩ := hY
  refine ⟨oddCoreIn_le_qlift H Y, qlift_le H Y, fun g hg => ?_, ?_, qlift_mul_comm hCH hYC⟩
  · obtain ⟨hgH, hgY⟩ := mem_qlift.mp hg
    obtain ⟨k, hk⟩ := hYr ⟨_, hgY⟩
    refine ⟨k, ⟨⟨g, hgH⟩ ^ r ^ k, ?_, by simp⟩⟩
    have hk' : QuotientGroup.mk' (CFSG.oddCore H) (⟨g, hgH⟩ ^ r ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    exact (QuotientGroup.eq_one_iff _).mp hk'
  · intro τ hτ
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hτN : QuotientGroup.mk' (CFSG.oddCore H) ⟨τ, hTH hτ⟩ ∈
        Subgroup.normalizer (Y : Set (H ⧸ CFSG.oddCore H)) := hTY (mem_qbar hτ)
    constructor
    · intro hg
      obtain ⟨hgH, hgY⟩ := mem_qlift.mp hg
      have hmem : τ * g * τ⁻¹ ∈ H := H.mul_mem (H.mul_mem (hTH hτ) hgH) (H.inv_mem (hTH hτ))
      refine mem_qlift.mpr ⟨hmem, ?_⟩
      have h1 : (⟨τ * g * τ⁻¹, hmem⟩ : H) = ⟨τ, hTH hτ⟩ * ⟨g, hgH⟩ * ⟨τ, hTH hτ⟩⁻¹ :=
        Subtype.ext rfl
      rw [h1, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hτN _).mp hgY
    · intro hg
      obtain ⟨hmem, hgY⟩ := mem_qlift.mp hg
      have hgH : g ∈ H := by
        have := H.mul_mem (H.mul_mem (H.inv_mem (hTH hτ)) hmem) (hTH hτ)
        simpa [mul_assoc] using this
      refine mem_qlift.mpr ⟨hgH, ?_⟩
      have h1 : (⟨τ * g * τ⁻¹, hmem⟩ : H) = ⟨τ, hTH hτ⟩ * ⟨g, hgH⟩ * ⟨τ, hTH hτ⟩⁻¹ :=
        Subtype.ext rfl
      rw [h1, map_mul, map_mul, map_inv] at hgY
      exact (Subgroup.mem_normalizer_iff.mp hτN _).mpr hgY

omit [Finite G] in
private theorem qbar_mem_maximals {H X : Subgroup G} (hTH : σ.T ≤ H) (hCH : σ.C ≤ H)
    (hX : X ∈ maximals (liftedSignalizers σ H r)) :
    qbar H X ∈ maximals (dSig (qbar H σ.T) (qbar H σ.C) r) := by
  refine ⟨qbar_mem_dSig hCH hX.1, fun Y hY hle => ?_⟩
  have hXY : X ≤ qlift H Y := by
    rw [← qlift_qbar hX.1.1 hX.1.2.1]
    exact qlift_mono hle
  have h := hX.2 _ (qlift_mem hTH hCH hY) hXY
  rw [← qbar_qlift H Y, h]

private theorem qbar_C_eq (hσ : σ.IsValid) {H : Subgroup G} (hCH : σ.C ≤ H) :
    qbar H σ.C =
      Subgroup.centralizer ((qbar H σ.T : Subgroup _) : Set (H ⧸ CFSG.oddCore H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : σ.T ≤ H := (σ.T_le_C hσ).trans hCH
  have hN : ¬ 2 ∣ Nat.card (CFSG.oddCore H) := fun h2 =>
    (Nat.not_even_iff_odd.mpr (odd_card_oddCore H)) (even_iff_two_dvd.mpr h2)
  have hA : IsPGroup 2 (σ.T.subgroupOf H) := (T_isPGroup hσ).comap_subtype
  have hcop := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 2 (CFSG.oddCore H) hN
    (σ.T.subgroupOf H) hA
  have hC : Subgroup.centralizer ((σ.T.subgroupOf H : Subgroup H) : Set H) =
      σ.C.subgroupOf H := by
    ext h
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
    change _ ↔ (h : G) ∈ Subgroup.centralizer (σ.T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hh τ hτ
      exact congrArg Subtype.val (hh ⟨τ, hTH hτ⟩ hτ)
    · intro hh τ hτ
      exact Subtype.ext (hh τ hτ)
  unfold qbar
  rw [← hC, hcop]

private theorem isKleinFour_qbar_T (hσ : σ.IsValid) {H : Subgroup G} (hTH : σ.T ≤ H) :
    IsKleinFour (qbar H σ.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold qbar
  refine CFSG.ABGDGroups.isKleinFour_map_of_inf_ker_eq_bot _
    (isKleinFour_subgroupOf hTH (T_isKleinFour hσ)) ?_
  rw [QuotientGroup.ker_mk']
  exact inf_eq_bot_of_two_odd (T_isPGroup hσ).comap_subtype (odd_card_oddCore H)

private theorem qmk_ne_one (hσ : σ.IsValid) {H : Subgroup G} (hTH : σ.T ≤ H) {t : G}
    (ht : t ∈ σ.T) (ht1 : t ≠ 1) : QuotientGroup.mk' (CFSG.oddCore H) ⟨t, hTH ht⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hO : (⟨t, hTH ht⟩ : H) ∈ CFSG.oddCore H := (QuotientGroup.eq_one_iff _).mp h
  have hbot : σ.T.subgroupOf H ⊓ CFSG.oddCore H = ⊥ :=
    inf_eq_bot_of_two_odd ((T_isPGroup hσ).comap_subtype (K := H)) (odd_card_oddCore H)
  have hmem : (⟨t, hTH ht⟩ : H) ∈ σ.T.subgroupOf H ⊓ CFSG.oddCore H := ⟨ht, hO⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact ht1 (congrArg Subtype.val hmem)

omit [Finite G] in
private theorem qbar_le_centralizer {H X : Subgroup G} {t : G} (htH : t ∈ H)
    (h : ∀ y ∈ X, y * t * y⁻¹ * t⁻¹ ∈ oddCoreIn H) :
    qbar H X ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.oddCore H) ⟨t, htH⟩} : Set (H ⧸ CFSG.oddCore H)) := by
  intro z hz
  obtain ⟨x, hxX, rfl⟩ := mem_qbar_iff.mp hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨o, ho, hoe⟩ := h _ hxX
  have h1 : o = x * ⟨t, htH⟩ * x⁻¹ * ⟨t, htH⟩⁻¹ := Subtype.ext (by simpa using hoe)
  have h2 : QuotientGroup.mk' (CFSG.oddCore H) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  set a := QuotientGroup.mk' (CFSG.oddCore H) x
  set b := QuotientGroup.mk' (CFSG.oddCore H) ⟨t, htH⟩
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h2, one_mul]

private theorem odd_card_of_mem_lifted (hr : r.Prime) (hr2 : r ≠ 2) {H X : Subgroup G}
    (hX : X ∈ liftedSignalizers σ H r) : Odd (Nat.card X) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hOX, hXH, hXr, -, -⟩ := hX
  set O : Subgroup G := oddCoreIn H with hOdef
  have hnormal : (O.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr
      (hXH.trans (le_normalizer_oddCoreIn H))
  have hq : IsPGroup r (X ⧸ O.subgroupOf X) := by
    intro g
    induction g using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨k, hk⟩ := hXr x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hq
  have h1 := Subgroup.relIndex_mul_card O X
  rw [inf_eq_left.mpr hOX, Subgroup.relIndex, Subgroup.index_eq_card, hn] at h1
  rw [← h1]
  exact ((hr.odd_of_ne_two hr2).pow).mul (odd_card_oddCoreIn H)

private theorem exists_conjSub_of_qbar (hσ : σ.IsValid) {H X X' : Subgroup G}
    (hCH : σ.C ≤ H) (hX : X ∈ liftedSignalizers σ H r) (hX' : X' ∈ liftedSignalizers σ H r)
    {n : H ⧸ CFSG.oddCore H}
    (hn : n ∈ Subgroup.normalizer ((qbar H σ.T : Subgroup _) : Set (H ⧸ CFSG.oddCore H)))
    (hnX : conjSub n (qbar H X') = qbar H X) :
    ∃ m ∈ H ⊓ Subgroup.normalizer (σ.T : Set G), conjSub m X' = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : σ.T ≤ H := (σ.T_le_C hσ).trans hCH
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore H) n
  have hconjq : ∀ g : G, ∀ hg : g ∈ H, ∀ hg' : (n₀ : G)⁻¹ * g * n₀ ∈ H,
      (QuotientGroup.mk' (CFSG.oddCore H) n₀)⁻¹ * QuotientGroup.mk' (CFSG.oddCore H) ⟨g, hg⟩ *
        QuotientGroup.mk' (CFSG.oddCore H) n₀ =
      QuotientGroup.mk' (CFSG.oddCore H) ⟨(n₀ : G)⁻¹ * g * n₀, hg'⟩ := by
    intro g hg hg'
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hconj : conjSub (n₀ : G) X' = X := by
    ext g
    rw [mem_conjSub]
    constructor
    · intro hg
      have hgH : g ∈ H := by
        have := H.mul_mem (H.mul_mem n₀.2 (hX'.2.1 hg)) (H.inv_mem n₀.2)
        simpa [mul_assoc] using this
      rw [← qlift_qbar hX.1 hX.2.1, mem_qlift]
      refine ⟨hgH, ?_⟩
      rw [← hnX, mem_conjSub, hconjq g hgH (hX'.2.1 hg)]
      exact mem_qbar hg
    · intro hg
      have hgH : g ∈ H := hX.2.1 hg
      have hmem : (n₀ : G)⁻¹ * g * n₀ ∈ H := H.mul_mem (H.mul_mem (H.inv_mem n₀.2) hgH) n₀.2
      rw [← qlift_qbar hX.1 hX.2.1, mem_qlift] at hg
      obtain ⟨_, hgq⟩ := hg
      rw [← hnX, mem_conjSub, hconjq g hgH hmem] at hgq
      have h' : (n₀ : G)⁻¹ * g * n₀ ∈ qlift H (qbar H X') := mem_qlift.mpr ⟨hmem, hgq⟩
      rwa [qlift_qbar hX'.1 hX'.2.1] at h'
  set TO : Subgroup G := σ.T ⊔ oddCoreIn H with hTOdef
  have hTOH : TO ≤ H := sup_le hTH (oddCoreIn_le H)
  have hnT : conjSub (n₀ : G) σ.T ≤ TO := by
    intro g hg
    rw [mem_conjSub] at hg
    have hgH : g ∈ H := by
      have := H.mul_mem (H.mul_mem n₀.2 (hTH hg)) (H.inv_mem n₀.2)
      simpa [mul_assoc] using this
    rw [hTOdef, ← qlift_qbar_eq_sup hTH, mem_qlift]
    refine ⟨hgH, ?_⟩
    have h2 : (QuotientGroup.mk' (CFSG.oddCore H) n₀)⁻¹ *
        QuotientGroup.mk' (CFSG.oddCore H) ⟨g, hgH⟩ * QuotientGroup.mk' (CFSG.oddCore H) n₀ ∈
          qbar H σ.T := by
      rw [hconjq g hgH (hTH hg)]
      exact mem_qbar hg
    exact (Subgroup.mem_normalizer_iff''.mp hn
      (QuotientGroup.mk' (CFSG.oddCore H) ⟨g, hgH⟩)).mpr h2
  have hTO : (σ.T : Set G) * oddCoreIn H = oddCoreIn H * σ.T :=
    mul_comm_of_le_normalizer (hTH.trans (le_normalizer_oddCoreIn H))
  have hidx : σ.T.relIndex TO = σ.T.relIndex (oddCoreIn H) := by
    rw [hTOdef, sup_comm]
    exact relIndex_sup_of_mul_comm hTO.symm
  have hodd : ¬ 2 ∣ σ.T.relIndex TO := by
    rw [hidx]
    intro h2
    have := h2.trans (Subgroup.relIndex_dvd_card _ _)
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn H)) (even_iff_two_dvd.mpr this)
  have hsylT : IsSylowOf 2 σ.T TO := isSylowOf_iff.mpr ⟨le_sup_left, T_isPGroup hσ, hodd⟩
  have hsylnT : IsSylowOf 2 (conjSub (n₀ : G) σ.T) TO := by
    refine isSylowOf_iff.mpr ⟨hnT, isPGroup_conjSub (T_isPGroup hσ), ?_⟩
    have h1 := Subgroup.relIndex_mul_card (conjSub (n₀ : G) σ.T) TO
    have h2 := Subgroup.relIndex_mul_card σ.T TO
    rw [inf_eq_left.mpr hnT, card_conjSub] at h1
    rw [inf_eq_left.mpr le_sup_left] at h2
    have h3 : (conjSub (n₀ : G) σ.T).relIndex TO = σ.T.relIndex TO :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
    rw [h3]
    exact hodd
  obtain ⟨k, hkTO, hk⟩ := exists_conjSub_eq_of_isSylowOf hsylnT hsylT
  refine ⟨k * n₀, ⟨H.mul_mem (hTOH hkTO) n₀.2, ?_⟩, ?_⟩
  · apply mem_normalizer_of_conjSub_eq
    rw [conjSub_mul, hk]
  · have hkX : k ∈ Subgroup.normalizer (X : Set G) :=
      (sup_le hX.2.2.2.1 (hX.1.trans Subgroup.le_normalizer) : TO ≤ _) hkTO
    rw [conjSub_mul, hconj, conjSub_eq_self hkX]

end Lift

section Wreath

open CFSG.Open CFSG.Semidihedral
open CFSG.Wreathed (Wreath)

private theorem dq_wreath_half_involution (k : ℕ) :
    orderOf (Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0) = 2 ∧
      Wreathed.element (2 ^ (k + 1)) 0 0 1 *
          Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 *
          (Wreathed.element (2 ^ (k + 1)) 0 0 1)⁻¹ ≠
        Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 := by
  refine ⟨(Wreathed.element_base_involution_iff k _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
  rw [Wreathed.conjugate_base_by_swap]
  intro h
  rw [Wreathed.element_eq_iff] at h
  exact Wreathed.half_residue_ne_zero k h.1.symm

private theorem dq_wreath_not_embed {n k : ℕ} (hn : 4 ≤ n) (hk : 1 ≤ k)
    (ι : Wreath (2 ^ (k + 1)) →* SemidihedralGroup n) (hι : Function.Injective ι) : False := by
  have := presentation_finite n (by omega)
  obtain ⟨hx2, hxw⟩ := dq_wreath_half_involution k
  set x := Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 with hx
  set y := Wreathed.element (2 ^ (k + 1)) 1 0 0 with hy
  set w := Wreathed.element (2 ^ (k + 1)) 0 0 1 with hw
  have hxy : x * y = y * x := by
    rw [hx, hy, Wreathed.element_base_mul, Wreathed.element_base_mul, Wreathed.element_eq_iff]
    exact ⟨add_comm _ _, rfl, rfl⟩
  have hy2 : y ^ 2 ≠ 1 := by
    rw [hy, Wreathed.element_base_pow]
    intro h2
    rw [Wreathed.element_base_eq_one_iff] at h2
    have h2' : ((2 : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by simpa [nsmul_eq_mul] using h2.1
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have hle := Nat.le_of_dvd (by norm_num) h2'
    have h4 : 2 ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hX2 : orderOf (ι x) = 2 := by rw [orderOf_injective ι hι, hx2]
  have hXz : ι x ∉ Subgroup.zpowers (z n) := by
    intro h
    rcases (KleinFourOddKernel.mem_zpowers_involution _ _ (orderOf_z n (by omega))).mp h with
      h1 | h1
    · rw [h1, orderOf_one] at hX2
      omega
    · apply hxw
      apply hι
      rw [map_mul, map_mul, map_inv, h1,
        Subgroup.mem_center_iff.mp (z_mem_center n hn) (ι w), mul_inv_cancel_right]
  obtain ⟨h1, -, -⟩ := Local.semidihedral_four_subgroup_centralizers n hn
    (MulEquiv.refl (SemidihedralGroup n))
  have hz : (MulEquiv.refl (SemidihedralGroup n)) (r n) ^ (2 ^ (n - 1) / 2) = z n := by
    rw [MulEquiv.refl_apply, two_pow_div_two hn]
    rfl
  rw [hz] at h1
  obtain ⟨hC, hK⟩ := h1 (ι x) hX2 hXz
  have hYC : ι y ∈ Subgroup.centralizer ({ι x} : Set (SemidihedralGroup n)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxy]
  rw [hC] at hYC
  have hYsq := congrArg Subtype.val (IsKleinFour.mul_self (⟨ι y, hYC⟩ :
    Subgroup.closure ({z n, ι x} : Set (SemidihedralGroup n))))
  apply hy2
  apply hι
  rw [map_pow, map_one, pow_two]
  exact hYsq

private theorem dq_not_hasWreathedSylow {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : HasSemidihedralSylow G n) (K : Subgroup G) (m : ℕ) : ¬ HasWreathedSylow K m := by
  rintro ⟨hm, hW⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨e⟩ := hW P
  have hP' : IsPGroup 2 ((P : Subgroup K).map K.subtype) := P.isPGroup'.map K.subtype
  obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
  obtain ⟨f'⟩ := hG.2 S'
  let ι : Wreath (2 ^ m) →* SemidihedralGroup n :=
    f'.symm.toMonoidHom.comp ((Subgroup.inclusion hS').comp
      (((P : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom.comp
        e.symm.toMonoidHom))
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 := congrArg Subtype.val (f'.symm.injective hab)
    apply e.symm.injective
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  exact dq_wreath_not_embed hG.1 (by omega) ι hι

end Wreath

end OmnibusDConjugacyQD

open OmnibusDConjugacyQD

variable {G : Type} [Group G] [Finite G] {σ : Setting G}

theorem abg_V_8_7_D_input_of (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h57 : ABG_II_5_7_Input σ) : ABG_V_8_7_D_Input σ r := by
  intro hh H hCH _ hD X hX X' hX'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : σ.T ≤ H := (σ.T_le_C hσ).trans hCH
  have hT := T_isKleinFour hσ
  obtain ⟨t, ht, ht1, htX⟩ := h57 hh H hD σ.T hTH hT X hX.1.2.1
    (odd_card_of_mem_lifted hr hr2 hX.1) hX.1.2.2.2.1
  obtain ⟨t', ht', ht'1, ht'X⟩ := h57 hh H hD σ.T hTH hT X' hX'.1.2.1
    (odd_card_of_mem_lifted hr hr2 hX'.1) hX'.1.2.2.2.1
  have hK : IsDGroup (H ⧸ CFSG.oddCore H) := CFSG.ABGDGroups.isDGroup_quotient_oddCore hD
  have hO := CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot H
  obtain ⟨m, hSD⟩ : ∃ m, HasSemidihedralSylow G m := by
    rcases hσ.sylow with ⟨-, h⟩ | h
    · exact h
    · exact absurd h.1 (by rw [hh]; norm_num)
  have hW : ¬ ∃ n, HasWreathedSylow (H ⧸ CFSG.oddCore H) n := by
    rintro ⟨n, hn⟩
    rw [CFSG.ABGDGroups.hasWreathedSylow_quotient_oddCore_iff] at hn
    exact dq_not_hasWreathedSylow hSD H n hn
  have hXb := qbar_mem_maximals hTH hCH hX
  have hX'b := qbar_mem_maximals hTH hCH hX'
  rw [qbar_C_eq hσ hCH] at hXb hX'b
  obtain ⟨n, hn, hnX⟩ := dGroup_exists_conjSub hK hO hW (isKleinFour_qbar_T hσ hTH) hr hr2
    (mem_qbar (x := ⟨t, hTH ht⟩) ht) (mem_qbar (x := ⟨t', hTH ht'⟩) ht')
    (qmk_ne_one hσ hTH ht ht1) (qmk_ne_one hσ hTH ht' ht'1) hXb hX'b
    (qbar_le_centralizer (hTH ht) htX) (qbar_le_centralizer (hTH ht') ht'X)
  exact exists_conjSub_of_qbar hσ hCH hX.1 hX'.1 hn hnX

end CFSG.ABGTheoremB.TotallyInverted
