module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Chain
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import Certificates.Certificate26014
public import Certificates.Certificate26015

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

noncomputable def sylSub : Subgroup (Equiv.Perm (Fin 820)) :=
  closure (tp 820 '' {x | x ∈ sylTabs})

theorem sylSub_enum :
    (∀ k < 128, Rep 820 sylEnum.1[k]! (tablePerm 820 sylEnum.1[k]!) ∧
      tablePerm 820 sylEnum.1[k]! ∈ sylSub) ∧
    (∀ x ∈ sylSub, ∃ k < 128, Rep 820 sylEnum.1[k]! x) ∧ Nat.card sylSub = 128 := by
  obtain ⟨hperm, -, henum⟩ := Certificates.certificate26014
  simp only [sylPermCheck, Array.all_eq_true', Bool.and_eq_true] at hperm
  simp only [sylEnumCheck, Bool.and_eq_true, beq_iff_eq] at henum
  obtain ⟨⟨⟨htree, hclosed⟩, hdist⟩, hsize⟩ := henum
  obtain ⟨h1, h2, h3⟩ := enum_spec (n := 820) (by norm_num) (A := sylTabs)
    (fun x hx => (hperm x hx).1) (fun x hx => (hperm x hx).2) (cap := sylCap) htree hclosed hdist
  have hs : (mulClosureH 820 sylTabs sylCap).1.size = 128 := hsize
  rw [hs] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem sylSub_le_P :
    sylSub ≤ P := by
  obtain ⟨hperm, hinP, -⟩ := Certificates.certificate26014
  simp only [sylPermCheck, Array.all_eq_true', Bool.and_eq_true] at hperm
  simp only [sylInPCheck, Array.all_eq_true'] at hinP
  rw [sylSub, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact (inP_iff (co2Rep_natArr_iff.2 (rep_tp (hperm x hx).1))).1 (hinP x hx)

theorem card_le_sixteen_of_le_sylSub
    (D : Subgroup (Equiv.Perm (Fin 820))) (hDS : D ≤ sylSub)
    (hab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (h2 : ∀ a ∈ D, a * a = 1) : Nat.card D ≤ 16 := by
  obtain ⟨hrep, hcov, hcard⟩ := sylSub_enum
  obtain ⟨hZ, hI⟩ := of_decide_eq_true Certificates.certificate26015
  set e : ℕ → Equiv.Perm (Fin 820) := fun k => tablePerm 820 sylEnum.1[k]!
  have hD : ∀ a ∈ D, ∃ k < 128, a = e k := fun a ha => by
    obtain ⟨k, hk, hr⟩ := hcov a (hDS ha)
    exact ⟨k, hk, (tablePerm_eq hr).symm⟩
  have hcomm : ∀ k < 128, ∀ j < 128, commTT 820 sylEnum.1[k]! sylEnum.1[j]! = true ↔
      e k * e j = e j * e k := fun k hk j hj => commTT_iff (hrep k hk).1 (hrep j hj).1
  have hinvol : ∀ k < 128, e k ≠ 1 → e k * e k = 1 → involOK 820 sylEnum.1[k]! = true :=
    fun k hk h1 hk2 => by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact involOK_of_orderOf (by norm_num) (hrep k hk).1 (orderOf_eq_prime (by rwa [sq]) h1)
  have hncard : Nat.card D = (D : Set (Equiv.Perm (Fin 820))).ncard := Nat.card_coe_set_eq _
  have hle31 : Nat.card D ≤ 31 := by
    by_cases hc : ∀ a ∈ D, ∀ s ∈ sylSub, a * s = s * a
    ·
      set Zs := (Finset.range 128).filter fun i =>
        ∀ j < 128, commTT 820 sylEnum.1[i]! sylEnum.1[j]! = true
      have hsub : (D : Set (Equiv.Perm (Fin 820))) ⊆ e '' (Zs : Set ℕ) := by
        intro a ha
        obtain ⟨k, hk, rfl⟩ := hD a ha
        exact ⟨k, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 hk,
          fun j hj => (hcomm k hk j hj).2 (hc _ ha _ (hrep j hj).2)⟩), rfl⟩
      calc Nat.card D = (D : Set (Equiv.Perm (Fin 820))).ncard := hncard
        _ ≤ (e '' (Zs : Set ℕ)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (Zs : Set ℕ).ncard := Set.ncard_image_le (Set.toFinite _)
        _ = Zs.card := Set.ncard_coe_finset Zs
        _ ≤ 16 := hZ
        _ ≤ 31 := by norm_num
    ·
      push Not at hc
      obtain ⟨a, ha, s, hs, hne⟩ := hc
      obtain ⟨k₀, hk₀, rfl⟩ := hD a ha
      have ha1 : e k₀ ≠ 1 := fun h => hne (by rw [h, one_mul, mul_one])
      have hinv₀ := hinvol k₀ hk₀ ha1 (h2 _ ha)
      obtain ⟨j₀, hj₀, hsj⟩ := hcov s hs
      have hsj' : s = e j₀ := (tablePerm_eq hsj).symm
      have hfalse : commTT 820 sylEnum.1[k₀]! sylEnum.1[j₀]! = false := by
        rw [Bool.eq_false_iff]
        intro h
        exact hne (by rw [hsj']; exact (hcomm k₀ hk₀ j₀ hj₀).1 h)
      have h30 := hI k₀ hk₀ hinv₀ ⟨j₀, hj₀, hfalse⟩
      set Fs := (Finset.range 128).filter fun j => involOK 820 sylEnum.1[j]! = true ∧
        commTT 820 sylEnum.1[k₀]! sylEnum.1[j]! = true
      have hsub : (D : Set (Equiv.Perm (Fin 820))) \ {1} ⊆ e '' (Fs : Set ℕ) := by
        rintro b ⟨hb, hb1⟩
        obtain ⟨j, hj, rfl⟩ := hD b hb
        have hb1' : e j ≠ 1 := fun h => hb1 (by rw [h]; rfl)
        exact ⟨j, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj,
          hinvol j hj hb1' (h2 _ hb), (hcomm k₀ hk₀ j hj).2 (hab _ ha _ hb)⟩), rfl⟩
      have hdiff : ((D : Set (Equiv.Perm (Fin 820))) \ {1}).ncard ≤ 30 :=
        calc ((D : Set (Equiv.Perm (Fin 820))) \ {1}).ncard
            ≤ (e '' (Fs : Set ℕ)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ (Fs : Set ℕ).ncard := Set.ncard_image_le (Set.toFinite _)
          _ = Fs.card := Set.ncard_coe_finset Fs
          _ ≤ 30 := h30
      have := Set.ncard_sdiff_singleton_add_one (s := (D : Set (Equiv.Perm (Fin 820)))) (a := 1)
        D.one_mem (Set.toFinite _)
      omega
  have hdvd : Nat.card D ∣ 2 ^ 7 := by
    have := Subgroup.card_dvd_of_le hDS
    rw [hcard] at this
    norm_num
    exact this
  obtain ⟨i, -, hiD⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi4 : i ≤ 4 := by
    by_contra h
    have h32 : 2 ^ 5 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc Nat.card D = 2 ^ i := hiD
    _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi4
    _ = 16 := by norm_num

theorem exists_conj_le_of_card {M : Type*} [Group M] [Finite M] {R S D : Subgroup M}
    (hSR : S ≤ R) (hS : Nat.card S = 2 ^ (Nat.card R).factorization 2) (hDR : D ≤ R)
    (hD : IsPGroup 2 D) : ∃ x ∈ R, ∀ t ∈ D, x⁻¹ * t * x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 R := Sylow.ofCard (S.subgroupOf R) (by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv)
  have hD' : IsPGroup 2 (D.subgroupOf R) := hD.of_equiv (subgroupOfEquivOfLe hDR).symm
  obtain ⟨T, hT⟩ := hD'.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq R S' T
  refine ⟨x, x.2, fun t ht => ?_⟩
  have htT : (⟨t, hDR ht⟩ : R) ∈ (T : Subgroup R) := hT (mem_subgroupOf.2 ht)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htT
  obtain ⟨s, hs, hst⟩ := htT
  have hsS : (s : M) ∈ S := by
    have : s ∈ S.subgroupOf R := by
      rwa [show ((S' : Subgroup R)) = S.subgroupOf R from Sylow.coe_ofCard _ _] at hs
    exact mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨t, hDR ht⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

private theorem factorization_3265920 : (3265920 : ℕ).factorization 2 = 7 := by
  rw [show (3265920 : ℕ) = 2 ^ 7 * 25515 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem card_P_eq : Nat.card P = 3265920 := by
  rw [← Nat.card_congr psiEquiv.toEquiv]
  exact CFSG.LieType.Multipliers.U43.card_X₀

theorem card_elemAb_le_sixteen
    (D : Subgroup (Equiv.Perm (Fin 820))) (hDP : D ≤ P)
    (hab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (h2 : ∀ a ∈ D, a * a = 1) : Nat.card D ≤ 16 := by
  have hS : Nat.card sylSub = 2 ^ (Nat.card P).factorization 2 := by
    rw [sylSub_enum.2.2, card_P_eq, factorization_3265920]
    norm_num
  have hDp : IsPGroup 2 D := fun g => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (h2 g g.2)⟩
  obtain ⟨x, -, hx⟩ := exists_conj_le_of_card sylSub_le_P hS hDP hDp
  set f : Equiv.Perm (Fin 820) →* Equiv.Perm (Fin 820) := (MulAut.conj x⁻¹).toMonoidHom
  have hD'S : D.map f ≤ sylSub := by
    rintro _ ⟨t, ht, rfl⟩
    show x⁻¹ * t * x⁻¹⁻¹ ∈ sylSub
    rw [inv_inv]
    exact hx t ht
  have hcard : Nat.card (D.map f) = Nat.card D :=
    Subgroup.card_map_of_injective (f := f) (MulAut.conj x⁻¹).injective
  have hab' : ∀ a ∈ D.map f, ∀ b ∈ D.map f, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hab a ha b hb]
  have h2' : ∀ a ∈ D.map f, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, h2 a ha, map_one]
  rw [← hcard]
  exact card_le_sixteen_of_le_sylSub _ hD'S hab' h2'

end CFSG.EvenSporadicStandard.M24Std.CU43
