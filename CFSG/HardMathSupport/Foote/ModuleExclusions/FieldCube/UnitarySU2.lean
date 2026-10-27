module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.UnitaryDickson
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.SU2Generation
public import CFSG.GH74.Generic.BProg.B3.LocBalL3Uni
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryComponent

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.BenderSuzuki.MatrixGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.SU2Gen

theorem closure_threePrime_eq_top {G : Type*} [Group G] [Finite G] (hperf : Group.IsPerfect G)
    (hsimple : IsSimpleGroup (G ⧸ Subgroup.center G)) :
    Subgroup.closure {g : G | (orderOf g).Coprime 3} = ⊤ := by
  classical
  set S : Set G := {g | (orderOf g).Coprime 3} with hS
  have hSconj : ∀ g x : G, x ∈ S → g * x * g⁻¹ ∈ S := by
    intro g x hx
    show (orderOf (g * x * g⁻¹)).Coprime 3
    have : orderOf (g * x * g⁻¹) = orderOf x :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    rw [this]; exact hx
  set N : Subgroup G := Subgroup.closure S with hN
  have hNn : N.Normal := by
    refine ⟨fun x hx g => ?_⟩
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact Subgroup.subset_closure (hSconj g y hy)
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]; exact N.mul_mem ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]; exact N.inv_mem ha
  have hZ : (Subgroup.center G).Normal := inferInstance
  by_cases hNZ : N ≤ Subgroup.center G
  · exfalso
    have hpg : IsPGroup 3 (G ⧸ Subgroup.center G) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have hord0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
      obtain ⟨e, m, hm, hgm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord0 3 (by norm_num)
      refine ⟨e, ?_⟩
      have hcop : Nat.Coprime (orderOf (g ^ 3 ^ e)) 3 := by
        have hdvd : orderOf (g ^ 3 ^ e) ∣ m := by
          refine orderOf_dvd_of_pow_eq_one ?_
          rw [← pow_mul, ← hgm]; exact pow_orderOf_eq_one g
        refine Nat.Coprime.coprime_dvd_left hdvd ?_
        exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm).symm
      have hc : g ^ 3 ^ e ∈ Subgroup.center G := hNZ (Subgroup.subset_closure hcop)
      show ((g : G ⧸ Subgroup.center G)) ^ 3 ^ e = 1
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hc
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hnil : Group.IsNilpotent (G ⧸ Subgroup.center G) := hpg.isNilpotent
    have hsol : Group.IsSolvable (G ⧸ Subgroup.center G) := inferInstance
    have hperfQ : Group.IsPerfect (G ⧸ Subgroup.center G) := by
      refine ⟨?_⟩
      have h1 : ⁅(⊤ : Subgroup G), ⊤⁆ = ⊤ := hperf.commutator_eq_top
      rw [eq_top_iff]
      intro q _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by rw [h1]; trivial
      have := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center G)) hg
      have h2 := Subgroup.map_commutator (⊤ : Subgroup G) (⊤ : Subgroup G) (QuotientGroup.mk' (Subgroup.center G))
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
      rw [h2] at this
      exact this
    have : Nontrivial (G ⧸ Subgroup.center G) := hsimple.toNontrivial
    exact Group.IsPerfect.not_isSolvable _ hsol
  ·
    have hmap : (N.map (QuotientGroup.mk' (Subgroup.center G))).Normal :=
      Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective _)
    have hQtop : N.map (QuotientGroup.mk' (Subgroup.center G)) = ⊤ := by
      have := hsimple
      have := hmap
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (N.map (QuotientGroup.mk' (Subgroup.center G))) with h0 | h1
      · exfalso
        apply hNZ
        intro x hx
        have : QuotientGroup.mk' (Subgroup.center G) x ∈
            N.map (QuotientGroup.mk' (Subgroup.center G)) := Subgroup.mem_map_of_mem _ hx
        rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
        exact this
      · exact h1
    have hcenter : ∀ g : G, ∃ n ∈ N, ∃ z ∈ Subgroup.center G, g = n * z := by
      intro g
      have : (g : G ⧸ Subgroup.center G) ∈ N.map (QuotientGroup.mk' (Subgroup.center G)) := by
        rw [hQtop]; trivial
      obtain ⟨n, hn, hng⟩ := this
      refine ⟨n, hn, n⁻¹ * g, ?_, by group⟩
      rw [← QuotientGroup.eq_one_iff]
      have : (n : G ⧸ Subgroup.center G) = g := hng
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, this, inv_mul_cancel]
    have h1 : ⁅(⊤ : Subgroup G), ⊤⁆ = ⊤ := hperf.commutator_eq_top
    rw [eq_top_iff, ← h1, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hcenter a
    obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hcenter b
    rw [commutatorElement_def,
      CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.SU2Gen.comm_mul_central _ _ _ _
        hz₁ hz₂]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)




section Arith

theorem threePrime_index_le (q₀ a m N : ℕ) (h3 : 3 ∣ q₀ + 1) (hq₀ : 5 ≤ q₀)
    (hqm : q₀ ^ 3 + 1 = 3 ^ a * m) (hNdvd : N ∣ q₀ ^ 3 + 1) (hmN : m ∣ N) (hqN : q₀ + 1 ∣ N) :
    q₀ ^ 3 + 1 ≤ 3 * N := by
  obtain ⟨k, hk⟩ := h3
  obtain ⟨j, rfl⟩ : ∃ j, q₀ = 3 * j + 2 := ⟨k - 1, by omega⟩
  have hs : (3 * j + 2) ^ 3 + 1 = (3 * j + 2 + 1) * (3 * (3 * j ^ 2 + 3 * j + 1)) := by ring
  obtain ⟨I, hI⟩ := hNdvd
  obtain ⟨d, hd⟩ := hmN
  obtain ⟨c, hc⟩ := hqN
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hqm; omega
    · exact h0
  have h1 : 3 ^ a = d * I := by
    have : 3 ^ a * m = (d * I) * m := by rw [← hqm, hI, hd]; ring
    exact Nat.eq_of_mul_eq_mul_right hm0 this
  have h2 : 3 * (3 * j ^ 2 + 3 * j + 1) = c * I := by
    have : (3 * j + 2 + 1) * (3 * (3 * j ^ 2 + 3 * j + 1)) = (3 * j + 2 + 1) * (c * I) := by
      rw [← hs, hI, hc]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hIdvd : I ∣ 3 ^ a := ⟨d, by rw [h1]; ring⟩
  obtain ⟨b, hb, hIb⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hIdvd
  have hb1 : b ≤ 1 := by
    by_contra hb2
    have h9I : 9 ∣ I := by
      rw [hIb]
      exact (pow_dvd_pow 3 (by omega : 2 ≤ b) : 3 ^ 2 ∣ 3 ^ b)
    have h9 : 9 ∣ 3 * (3 * j ^ 2 + 3 * j + 1) := by
      rw [h2]; exact Dvd.dvd.mul_left h9I c
    obtain ⟨t, ht⟩ : ∃ t, t = j ^ 2 := ⟨_, rfl⟩
    rw [← ht] at h9
    omega
  have hI3 : I ≤ 3 := by
    rw [hIb]; interval_cases b <;> norm_num
  calc (3 * j + 2) ^ 3 + 1 = N * I := hI
    _ ≤ N * 3 := Nat.mul_le_mul_left N hI3
    _ = 3 * N := mul_comm _ _

theorem not_le_six_mul_of_dvd_sixty (q₀ : ℕ) (hq₀ : 5 ≤ q₀) (h3 : 3 ∣ q₀ + 1) (n : ℕ)
    (hn : n ∣ 60) (hnq : n ∣ q₀ ^ 3 + 1) : ¬ q₀ ^ 3 + 1 ≤ 6 * n := by
  intro hle
  have hn60 : n ≤ 60 := Nat.le_of_dvd (by norm_num) hn
  have hq7 : q₀ ≤ 7 := by
    by_contra hc
    have hc := not_le.mp hc
    have : 8 ^ 3 ≤ q₀ ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases q₀
  · have := Nat.dvd_gcd hn hnq
    norm_num at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · omega
  · omega

end Arith

section Main

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem closure_threePrime_unitarySU_two
    (h : UnitaryFieldData ℓ f K) (f₀ : ℕ) (hf : f = 3 * f₀) (K₀ : Subfield K)
    (hK₀ : Nat.card K₀ = (ℓ ^ f₀) ^ 2) (hq₀ : ℓ ^ f₀ ≠ 2) (h3 : 3 ∣ ℓ ^ f₀ + 1) :
    Subgroup.closure
      ({A : unitarySU ℓ f K 2 | (∀ i j : Fin 2, i ≠ j →
          ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = 0) ∧ (orderOf A).Coprime 3} ∪
        {A : unitarySU ℓ f K 2 | (∀ i j : Fin 2,
          ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ K₀) ∧
            (orderOf A).Coprime 3}) = ⊤ := by
  classical
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have hq₀5 : 5 ≤ ℓ ^ f₀ := by
    have : 2 ≤ ℓ ^ f₀ := by
      have := (Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt : 1 < ℓ ^ f₀)
      omega
    omega
  have hqq : ℓ ^ f = (ℓ ^ f₀) ^ 3 := by rw [hf, mul_comm, pow_mul]
  have hq : 120 ≤ ℓ ^ f := by
    rw [hqq]
    have : 5 ^ 3 ≤ (ℓ ^ f₀) ^ 3 := Nat.pow_le_pow_left hq₀5 3
    omega
  have hf₀ : 1 ≤ f₀ := by
    have := h.one_le
    omega
  have h₀ : UnitaryFieldData ℓ f₀ K₀ :=
    ⟨h.prime, hf₀, by rw [hK₀, ← pow_mul, mul_comm]⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := CFSG.RankThree.PartTwo.Census.nonempty_sl2_mulEquiv_unitarySU_two h
  obtain ⟨π, hπ, hkfin, hker, hcen⟩ := exists_proj_of_sl2 e
  set S₃ : Set (unitarySU ℓ f K 2) := {A : unitarySU ℓ f K 2 | (∀ i j : Fin 2, i ≠ j →
          ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = 0) ∧ (orderOf A).Coprime 3}
    with hS₃
  set R₃ : Set (unitarySU ℓ f K 2) := {A : unitarySU ℓ f K 2 | (∀ i j : Fin 2,
          ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ K₀) ∧ (orderOf A).Coprime 3}
    with hR₃
  set H := Subgroup.closure (S₃ ∪ R₃) with hH
  set ι := subfieldSU h f₀ hf K₀ hK₀ h₀ with hι
  have hι_inj : Function.Injective ι := subfieldSU_injective h f₀ hf K₀ hK₀ h₀
  have : CharP K ℓ := h.charP
  have : CharP K₀ ℓ := h₀.charP
  have := h₀.finite
  have hq4 : 4 ≤ ℓ ^ f₀ := by omega
  have hqs₀ := CFSG.GH74.Generic.BProg.B3.LocBalL3Uni.quasisimple_unitarySU_two h₀ hq4
  have hq4' : 4 ≤ ℓ ^ f := by omega
  have hqs := CFSG.GH74.Generic.BProg.B3.LocBalL3Uni.quasisimple_unitarySU_two h hq4'
  have hSH : ι.range ≤ H := by
    have hgen := closure_threePrime_eq_top hqs₀.1 hqs₀.2.1
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.subset_closure (Or.inr ⟨fun i j => (((y : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) i j).2, ?_⟩)
    rw [orderOf_injective ι hι_inj y]
    exact hy
  set T : Subgroup (unitarySU ℓ f K 2) := (diagHom h).range with hT
  have hTcyc : IsCyclic T := by
    have : IsCyclic (Units.map h.normHom).ker := inferInstance
    exact isCyclic_of_surjective (diagHom h).rangeRestrict (diagHom h).rangeRestrict_surjective
  have hTcard : Nat.card T = ℓ ^ f + 1 := by
    rw [← (h.card_ker_normUnits_and_surjective).1]
    exact (Nat.card_congr (Equiv.ofInjective _ (diagHom_injective h))).symm
  have hTdiag : ∀ A ∈ T, ∀ i j : Fin 2, i ≠ j →
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = 0 := by
    rintro _ ⟨u, rfl⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [diagHom, diag2]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := T)
  obtain ⟨a, m, hm, hqm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := ℓ ^ f + 1) (by omega) 3
    (by norm_num)
  have hdvd : 3 ^ a ∣ orderOf g := ⟨m, by rw [hg, hTcard, hqm]⟩
  have hordx : orderOf (g ^ 3 ^ a) = m := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hg, hTcard, hqm]
    exact Nat.mul_div_cancel_left m (by positivity)
  set x : unitarySU ℓ f K 2 := ((g ^ 3 ^ a : T) : unitarySU ℓ f K 2) with hx
  have hxT : x ∈ T := (g ^ 3 ^ a : T).2
  have hxord : orderOf x = m := by
    rw [hx, orderOf_submonoid, hordx]
  have hxH : x ∈ H := by
    refine Subgroup.subset_closure (Or.inl ⟨hTdiag x hxT, ?_⟩)
    rw [hxord]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm).symm
  set T₀ : Subgroup (unitarySU ℓ f K 2) := (diagHom h₀).range.map ι with hT₀
  have hT₀ι : T₀ ≤ ι.range := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hT₀T : T₀ ≤ T := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    have hu : h.norm ((Units.map K₀.subtype.toMonoidHom (u : K₀ˣ) : Kˣ) : K) = 1 := by
      have h1 : h₀.norm ((u : K₀ˣ) : K₀) = 1 := (UnitaryFieldData.mem_ker_normUnits h₀).1 u.2
      have h2 : h.norm ((((u : K₀ˣ) : K₀)) : K) = ((h₀.norm ((u : K₀ˣ) : K₀) : K₀) : K) := by
        rw [UnitaryFieldData.norm, bar_subfield h f₀ hf K₀ hK₀ h₀, UnitaryFieldData.norm]
        rfl
      show h.norm ((((u : K₀ˣ) : K₀)) : K) = 1
      rw [h2, h1]
      rfl
    refine ⟨⟨Units.map K₀.subtype.toMonoidHom (u : K₀ˣ),
      (UnitaryFieldData.mem_ker_normUnits h).2 hu⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagHom, diag2, ι, subfieldSU, Matrix.GeneralLinearGroup.map]
  have hT₀card : Nat.card T₀ = ℓ ^ f₀ + 1 := by
    rw [hT₀, Subgroup.card_map_of_injective hι_inj,
      ← (h₀.card_ker_normUnits_and_surjective).1]
    exact (Nat.card_congr (Equiv.ofInjective _ (diagHom_injective h₀))).symm
  set C : Subgroup (unitarySU ℓ f K 2) := Subgroup.zpowers x ⊔ T₀ with hC
  have hCT : C ≤ T := sup_le (Subgroup.zpowers_le.2 hxT) hT₀T
  have hCH : C ≤ H := sup_le (Subgroup.zpowers_le.2 hxH) (hT₀ι.trans hSH)
  have hCcyc : IsCyclic C := Subgroup.isCyclic_of_le hCT
  have hNq : Nat.card C ∣ ℓ ^ f + 1 := hTcard ▸ Subgroup.card_dvd_of_le hCT
  have hmN : m ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers x ≤ C)
    rwa [Nat.card_zpowers, hxord] at this
  have hqN : ℓ ^ f₀ + 1 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le (le_sup_right : T₀ ≤ C)
    rwa [hT₀card] at this
  have hNq3 : ℓ ^ f + 1 ≤ 3 * Nat.card C := by
    rw [hqq] at hNq hqm ⊢
    exact threePrime_index_le (ℓ ^ f₀) a m (Nat.card C) h3 hq₀5 hqm hNq hmN hqN
  have hns : ¬ Group.IsSolvable (H.map π) := by
    intro hsol
    have hS' : Group.IsSolvable (ι.range.map π) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
        (Subgroup.map_mono hSH))
    have hSperf : ⁅ι.range, ι.range⁆ = ι.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
      congr 1
      exact hqs₀.1.commutator_eq_top
    have hSne : ι.range ≠ ⊥ := by
      have hnt := hqs₀.2.1.toNontrivial
      obtain ⟨x, hx⟩ := exists_ne (1 : unitarySU ℓ f₀ K₀ 2 ⧸ Subgroup.center (unitarySU ℓ f₀ K₀ 2))
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have hy : y ≠ 1 := fun hy => hx (by rw [hy]; rfl)
      refine fun hbot => ?_
      have : ι y ∈ ι.range := ⟨y, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hy (hι_inj (this.trans (map_one ι).symm))
    have hne : ι.range.map π ≠ ⊥ := by
      intro hbot
      apply hSne
      have hker' : ι.range ≤ π.ker := fun z hz => MonoidHom.mem_ker.mpr (by
        have : π z ∈ ι.range.map π := ⟨z, hz, rfl⟩
        rw [hbot] at this
        exact this)
      have hcent : ι.range ≤ Subgroup.center _ := hker'.trans hcen
      rw [← hSperf, eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp (hcent ha) b).symm
    have hperf : Group.IsPerfect (ι.range.map π) :=
      Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hSperf])
    have : Nontrivial (ι.range.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable _ hS'
  have hmap : H.map π = ⊤ :=
    map_eq_top_of_cyclic_six hF π hkfin hker hq H hns C hCH hCcyc rfl hNq hNq3
      (fun n hn hnq => by
        rw [hqq] at hnq ⊢
        exact not_le_six_mul_of_dvd_sixty (ℓ ^ f₀) hq₀5 h3 n hn hnq)
  have hGperf : ⁅(⊤ : Subgroup (unitarySU ℓ f K 2)), ⊤⁆ = ⊤ := hqs.1.commutator_eq_top
  rw [eq_top_iff, ← hGperf, Subgroup.commutator_le]
  have hlift : ∀ a : unitarySU ℓ f K 2, ∃ h1 ∈ H, ∃ z ∈ Subgroup.center (unitarySU ℓ f K 2),
      a = h1 * z := by
    intro a
    have : π a ∈ H.map π := by rw [hmap]; trivial
    obtain ⟨h1, hh1, e1⟩ := this
    refine ⟨h1, hh1, h1⁻¹ * a, hcen ?_, by simp⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, e1, inv_mul_cancel]
  intro a _ b _
  obtain ⟨h1, hh1, z1, hz1, rfl⟩ := hlift a
  obtain ⟨h2, hh2, z2, hz2, rfl⟩ := hlift b
  rw [commutatorElement_def, comm_mul_central _ _ _ _ hz1 hz2]
  exact H.mul_mem (H.mul_mem (H.mul_mem hh1 hh2) (H.inv_mem hh1)) (H.inv_mem hh2)

end Main

end CFSG.HardMathSupport.Foote.ModuleExclusions
