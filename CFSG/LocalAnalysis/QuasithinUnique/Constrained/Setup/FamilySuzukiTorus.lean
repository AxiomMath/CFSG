module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiFamilyOrderIdentity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiFamilyNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiInvolutions
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersSuzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.LieType.Ree.SuzukiFrobeniusExponents
public import Certificates.Certificate43
public import Certificates.Certificate113
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Subgroup CFSG.Blueprint

theorem inverts_of_centralizer_trivial {G : Type*} [Group G] (X : Subgroup G)
    (hcomm : ∀ a b : X, a * b = b * a) {t : G} (ht2 : t * t = 1)
    (hnorm : ∀ y ∈ X, t * y * t⁻¹ ∈ X) (hfix : ∀ y ∈ X, t * y = y * t → y = 1) :
    ∀ x ∈ X, t * x * t⁻¹ = x⁻¹ := by
  intro x hx
  set y := t * x * t⁻¹ with hy
  have hyX : y ∈ X := hnorm x hx
  have hb : x * y ∈ X := mul_mem hx hyX
  have hcomm' : x * y = y * x := congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hyX⟩)
  have hty : t * y * t⁻¹ = x := by
    calc t * y * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by rw [hy]; group
      _ = x := by rw [ht2]; group
  have hbt : t * (x * y) = (x * y) * t := by
    calc t * (x * y) = (t * x * t⁻¹) * (t * y * t⁻¹) * t := by group
      _ = y * x * t := by rw [hty, ← hy]
      _ = x * y * t := by rw [hcomm']
  have h1 := hfix _ hb hbt
  calc t * x * t⁻¹ = x⁻¹ * (x * y) := by rw [hy]; group
    _ = x⁻¹ := by rw [h1]; group

theorem exists_inverter_of_index_four {G : Type*} [Group G] [Finite G] (X : Subgroup G)
    (hcyc : IsCyclic X) (hodd : Odd (Nat.card X)) (hidx : X.relIndex (normalizer (X : Set G)) = 4)
    (hinv : ∀ t : G, orderOf t = 2 → IsPGroup 2 (centralizer ({t} : Set G))) :
    ∃ t : G, orderOf t = 2 ∧ ∀ x ∈ X, t * x * t⁻¹ = x⁻¹ := by
  set N := normalizer (X : Set G) with hN
  have hXN : X ≤ N := Subgroup.le_normalizer
  have hcard : Nat.card N = Nat.card X * 4 := by
    have h1 := Subgroup.card_mul_index (X.subgroupOf N)
    rw [Subgroup.relIndex] at hidx
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv] at h1
    exact h1.symm
  have h2 : 2 ∣ Nat.card N := ⟨Nat.card X * 2, by rw [hcard]; ring⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
  set t : G := (t' : G) with ht
  have htord : orderOf t = 2 := by rw [ht, Subgroup.orderOf_coe, ht']
  have ht2 : t * t = 1 := by rw [← pow_two, ← htord]; exact pow_orderOf_eq_one t
  have htN : t ∈ N := t'.2
  have hnorm : ∀ y ∈ X, t * y * t⁻¹ ∈ X := fun y hy =>
    ((Subgroup.mem_normalizer_iff.1 htN y).1 hy)
  have hcomm : ∀ a b : X, a * b = b * a := by
    let _ : CommGroup X := IsCyclic.commGroup
    exact fun a b => mul_comm a b
  have hfix : ∀ y ∈ X, t * y = y * t → y = 1 := by
    intro y hy hty
    have hyc : y ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hty.symm
    have h2g := hinv t htord
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h2g) ⟨y, hyc⟩
    have hk' : orderOf y = 2 ^ k := by rw [← hk]; exact (Subgroup.orderOf_mk _ _).symm
    have hdvd : orderOf y ∣ Nat.card X := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : X)
      rwa [Subgroup.orderOf_mk] at this
    have hyodd : Odd (orderOf y) := hodd.of_dvd_nat hdvd
    have hk0 : k = 0 := by
      by_contra hne
      rw [hk'] at hyodd
      exact (Nat.not_even_iff_odd.2 hyodd) (even_two.pow_of_ne_zero hne)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
    exact hk'
  exact ⟨t, htord, inverts_of_centralizer_trivial X hcomm ht2 hnorm hfix⟩

theorem suzuki_torus_order_cases {q e s r : ℕ} (hq : q = 2 * e ^ 2) (hprod : s * r = q ^ 2 + 1)
    (hsum : s + r = 2 * (q + 1)) : s = q + 1 + 2 * e ∨ r = q + 1 + 2 * e := by
  have h1 : (s : ℤ) * r = (q : ℤ) ^ 2 + 1 := by exact_mod_cast hprod
  have h2 : (s : ℤ) + r = 2 * ((q : ℤ) + 1) := by exact_mod_cast hsum
  have hq' : (q : ℤ) = 2 * (e : ℤ) ^ 2 := by exact_mod_cast hq
  have hr : (r : ℤ) = 2 * ((q : ℤ) + 1) - s := by linarith
  rw [hr] at h1
  have h3 : ((s : ℤ) - (q + 1)) ^ 2 = (2 * (e : ℤ)) ^ 2 := by nlinarith [h1, hq']
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h
  · left
    have : (s : ℤ) = q + 1 + 2 * e := by linarith
    exact_mod_cast this
  · right
    have : (r : ℤ) = q + 1 + 2 * e := by linarith
    exact_mod_cast this

open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator CFSG.BenderSuzuki.MatrixGroups in
theorem suzukiMatrixGroup_torus_inverter {m : ℕ} (hm : 0 < m) :
    ∃ x t : SuzukiMatrixGroup m, orderOf x = 2 ^ (2 * m + 1) + 2 * 2 ^ m + 1 ∧ orderOf t = 2 ∧
      t * x * t⁻¹ = x⁻¹ := by
  have hcard := suzuki_derangement_family_card_eq_two m hm
  obtain ⟨c, d, hcd, -⟩ := (Nat.card_eq_two_iff).1 hcard
  have hsp := suzuki_derangement_two_family_order_sum_product m hm c d hcd
  have hq : 2 ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 := by
    rw [← pow_mul, pow_succ]; ring_nf
  have key : ∀ c' : suzukiDerangementCentralizerClasses m,
      Nat.card (suzukiDerangementCentralizerRepresentative m c').val =
        2 ^ (2 * m + 1) + 1 + 2 * 2 ^ m →
      ∃ x t : SuzukiMatrixGroup m, orderOf x = 2 ^ (2 * m + 1) + 2 * 2 ^ m + 1 ∧ orderOf t = 2 ∧
        t * x * t⁻¹ = x⁻¹ := by
    intro c' hc'
    set X := (suzukiDerangementCentralizerRepresentative m c').val with hX
    obtain ⟨hcyc, hodd⟩ := suzuki_derangement_family_cyclic_odd m hm
      (suzukiDerangementCentralizerRepresentative m c')
    have hidx := suzuki_derangement_family_normalizer_index_eq_four m hm c'
    obtain ⟨t, ht2, hinvX⟩ := exists_inverter_of_index_four X hcyc hodd hidx
      (fun t ht => suzuki_involution_centralizer_isPGroup m hm t ht)
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    refine ⟨(g : SuzukiMatrixGroup m), t, ?_, ht2, hinvX _ g.2⟩
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hc']
    ring
  rcases suzuki_torus_order_cases hq hsp.1 hsp.2 with h | h
  · exact key c (by rw [h])
  · exact key d (by rw [h])

section Zero

open CFSG.LieType.Ree

@[expose] def wMatrixZ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

@[expose] def sMatrixZ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 1, 0, 1]

theorem wMatrixZ_mul_self : wMatrixZ * wMatrixZ = 1 := by decide

theorem sMatrixZ_mul_self : sMatrixZ * sMatrixZ = 1 := by decide

theorem wsMatrixZ_pow_five : (wMatrixZ * sMatrixZ) ^ 5 = 1 := by decide

theorem wsMatrixZ_ne_one : wMatrixZ * sMatrixZ ≠ 1 := by decide

theorem sMatrixZ_ne_one : sMatrixZ ≠ 1 := by decide

theorem suzukiGroup_zero_torus_inverter
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 0 + 1)) :
    ∃ x t : suzukiGroup 0 K, orderOf x = 5 ∧ orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹ := by
  have hchar : CharP K 2 := (suzuki_frobenius_exponents 0 K hK).1
  let f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hfinj : Function.Injective f := f.injective
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin 4) (Fin 4) (ZMod 2) →+* _) :=
    fun A B h => Matrix.map_injective hfinj (by simpa [RingHom.mapMatrix_apply] using h)
  let ι : suzukiGroup 0 K →* Matrix (Fin 4) (Fin 4) K :=
    (Units.coeHom (Matrix (Fin 4) (Fin 4) K)).comp (Subgroup.subtype _)
  have hι : Function.Injective ι := fun a b h => Subtype.ext (Units.ext h)
  have hW : suzukiW K = f.mapMatrix wMatrixZ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [suzukiW, wMatrixZ, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hS : suzukiS 0 (0 : K) 1 = f.mapMatrix sMatrixZ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [suzukiS, suzukiN, sMatrixZ, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hιW : ι (suzukiWElt 0 K) = f.mapMatrix wMatrixZ := hW
  have hιS : ι (suzukiSElt 0 K 0 1) = f.mapMatrix sMatrixZ := hS
  set w := suzukiWElt 0 K with hw
  set s := suzukiSElt 0 K 0 1 with hs
  have hww : w * w = 1 := hι (by
    rw [map_mul, hιW, ← map_mul, wMatrixZ_mul_self, map_one, map_one])
  have hss : s * s = 1 := hι (by
    rw [map_mul, hιS, ← map_mul, sMatrixZ_mul_self, map_one, map_one])
  have hx5 : (w * s) ^ 5 = 1 := hι (by
    have h : ι ((w * s) ^ 5) = (f.mapMatrix wMatrixZ * f.mapMatrix sMatrixZ) ^ 5 := by
      rw [map_pow, map_mul, hιW, hιS]
    rw [h, ← map_mul f.mapMatrix, ← map_pow f.mapMatrix, wsMatrixZ_pow_five,
      map_one f.mapMatrix, map_one ι])
  have hx1 : w * s ≠ 1 := by
    intro h
    have h1 := congrArg ι h
    rw [map_mul, hιW, hιS, ← map_mul f.mapMatrix, map_one ι] at h1
    exact wsMatrixZ_ne_one (hinj (h1.trans (map_one f.mapMatrix).symm))
  have hs1 : s ≠ 1 := by
    intro h
    have h1 := congrArg ι h
    rw [hιS, map_one ι] at h1
    exact sMatrixZ_ne_one (hinj (h1.trans (map_one f.mapMatrix).symm))
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  refine ⟨w * s, s, orderOf_eq_prime hx5 hx1, orderOf_eq_prime (by rw [pow_two]; exact hss) hs1, ?_⟩
  rw [mul_inv_rev, hsi, hwi]
  calc s * (w * s) * s = s * w * (s * s) := by simp only [mul_assoc]
    _ = s * w := by rw [hss, mul_one]

end Zero

theorem suzukiGroup_torus_inverter
    (a : ℕ) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x t : suzukiGroup a K, orderOf x = 2 ^ (2 * a + 1) + 2 * 2 ^ a + 1 ∧ orderOf t = 2 ∧
      t * x * t⁻¹ = x⁻¹ := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨x, t, hx, ht, hxt⟩ := suzukiGroup_zero_torus_inverter hK
    exact ⟨x, t, by rw [hx]; norm_num, ht, hxt⟩
  · obtain ⟨x, t, hx, ht, hxt⟩ := suzukiMatrixGroup_torus_inverter ha
    let e := CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup (a := a) hK
    refine ⟨e.symm x, e.symm t, ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq, hx]
    · rw [MulEquiv.orderOf_eq, ht]
    · have h1 := congrArg e.symm hxt
      simpa [map_mul, map_inv] using h1

theorem suzuki_nonsplit_torus_and_inverter
    (a : ℕ) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∃ (C : Subgroup (suzukiGroup a K)) (t : suzukiGroup a K), IsCyclic C ∧
      Nat.card C = 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 ∧ orderOf t = 2 ∧
      ∀ c ∈ C, t * c * t⁻¹ = c⁻¹) ∧
    (∃ x t : suzukiGroup a K, orderOf x = 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 ∧ orderOf t = 2 ∧
      t * x * t⁻¹ = x⁻¹) ∧
    Odd (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) ∧
    2 ^ (2 * a + 1) < 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 ∧
    (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  obtain ⟨x, t, hx, ht, hxt⟩ := suzukiGroup_torus_inverter a hK
  have hm : 2 * 2 ^ a = 2 ^ (a + 1) := by rw [pow_succ]; ring
  rw [hm] at hx
  refine ⟨⟨Subgroup.zpowers x, t, ?_, ?_, ht, ?_⟩, ⟨x, t, hx, ht, hxt⟩, ?_, ?_, ?_⟩
  · infer_instance
  · rw [Nat.card_zpowers, hx]
  · intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have : t * x ^ k * t⁻¹ = (t * x * t⁻¹) ^ k := conj_zpow.symm
    rw [this, hxt, inv_zpow]
  · have h2 : Even (2 ^ (2 * a + 1)) := even_two.pow_of_ne_zero (by omega)
    have h3 : Even (2 ^ (a + 1)) := even_two.pow_of_ne_zero (by omega)
    exact (h2.add h3).add_one
  · have : 0 < 2 ^ (a + 1) := Nat.two_pow_pos _
    omega
  · have hq : 2 ^ (2 * a + 1) = 2 * (2 ^ a) ^ 2 := by
      rw [← pow_mul, pow_succ]; ring_nf
    refine ⟨2 ^ (2 * a + 1) + 1 - 2 ^ (a + 1), ?_⟩
    have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) + 1 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.le_add_right _ _)
    zify [hle]
    have hq' : ((2 : ℤ) ^ (2 * a + 1)) = 2 * ((2 : ℤ) ^ a) ^ 2 := by exact_mod_cast hq
    have h2 : ((2 : ℤ) ^ (a + 1)) = 2 * 2 ^ a := by rw [pow_succ]; ring
    rw [h2]
    linear_combination (-2) * hq'

end CFSG.QuasithinUnique.Setup.Family
