module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.LinearPilot (linearSwapDiag linearSwapDiag_apply
  ker_linearSwapDiag_le_center)
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_spGlobal_of_swap (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK4 : 4 ≤ Nat.card K) (e : L ≃* StatedSp n K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {A : Subgroup G} (hq : CFSG.Open.IsQuasisimple A)
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hcard : Nat.card L ≤ Nat.card (A ⧸ center A)) : A ≤ spGlobal e := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have : Group.IsPerfect A := ⟨hq.1⟩
  set δ := linearSwapDiag hA with hδdef
  have hperf : ⁅δ.range, δ.range⁆ = δ.range := by
    rw [MonoidHom.range_eq_map]
    exact LinearPilot.commutator_map_eq_of_commutator_eq δ (by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top)
  have hle : δ.range ≤ L :=
    std_perfect_le hset hOut htC ht hperf (LinearPilot.range_linearSwapDiag_le_centralizer htt hA)
  have hrange : δ.range = L := Subgroup.eq_of_le_of_card_ge hle
    (hcard.trans (LinearPilot.card_quotient_center_le_card_range_linearSwapDiag hA))
  have hmemL : ∀ x : A, δ x ∈ L := fun x => hle ⟨x, rfl⟩
  set π : A →* StatedSp n K := e.toMonoidHom.comp (δ.codRestrict L hmemL) with hπ
  have hπapp : ∀ x : A, π x = e ⟨δ x, hmemL x⟩ := fun x => rfl
  have hπs : Function.Surjective π := by
    intro z
    have hz : ((e.symm z : L) : G) ∈ δ.range := hrange ▸ (e.symm z).2
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    rw [hπapp]
    have h1 : (⟨δ x, hmemL x⟩ : L) = e.symm z := Subtype.ext hx
    rw [h1, MulEquiv.apply_symm_apply]
  have hπker : π.ker ≤ center A := by
    intro x hx
    apply ker_linearSwapDiag_le_center hA
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [hπapp] at hx
    have h1 : (⟨δ x, hmemL x⟩ : L) = 1 := by
      apply e.injective
      rw [hx, map_one]
    exact congrArg Subtype.val h1
  set B : Fin n → Subgroup A := fun j => (simpleRootSL2 K j).comap π with hB
  set C : Fin n → Subgroup A := fun j => perfectCore (B j) with hC
  have hCB : ∀ j, C j ≤ B j := fun j => CFSG.Quasithin.perfectCore_le _
  have hCpiece : ∀ j, (C j).map A.subtype ≤ pieceCore e ({j} : Finset (Fin n)) := by
    intro j
    have hperfC : ⁅(C j).map A.subtype, (C j).map A.subtype⁆ = (C j).map A.subtype := by
      rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    refine F4Pilot.le_centralizerPerfectCore hperfC ?_
    set T : Subgroup A := (leviTorusSp K ({j} : Finset (Fin n))).comap π with hT
    have hCT : (C j).map A.subtype ≤ centralizer ((T.map A.subtype : Subgroup G) : Set G) := by
      refine LinearPilot.le_centralizer_of_commutator_le_center (M := A) (map_subtype_le _)
        hperfC ?_
      rw [Subgroup.commutator_le]
      rintro _ ⟨c, hc, rfl⟩ _ ⟨x, hx, rfl⟩
      have hcB : π c ∈ simpleRootSL2 K j := hCB j hc
      have hxT : π x ∈ leviTorusSp K ({j} : Finset (Fin n)) := hx
      have hcomm : π ⁅c, x⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (mem_centralizer_iff.1 (simpleRootSL2_le_centralizer_leviTorusSp
          (Finset.mem_singleton_self j) hcB) _ hxT).symm
      exact ⟨⁅c, x⁆, hπker hcomm, rfl⟩
    intro w hw
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨c, hc, rfl⟩ := hw
    obtain ⟨z, hz, hzy⟩ := (mem_modelToG e).1 hy
    have hyL : y ∈ L := hzy ▸ (e.symm z).2
    obtain ⟨x, hx⟩ : y ∈ δ.range := hrange ▸ hyL
    have hxT : x ∈ T := by
      change π x ∈ leviTorusSp K ({j} : Finset (Fin n))
      have h1 : (⟨δ x, hmemL x⟩ : L) = e.symm z := Subtype.ext (hx.trans hzy.symm)
      rw [hπapp, h1, MulEquiv.apply_symm_apply]
      exact hz
    have h1 : (x : G) * c = c * x := mem_centralizer_iff.1 (hCT ⟨c, hc, rfl⟩) _ ⟨x, hxT, rfl⟩
    have h2 : (c : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * c :=
      mem_centralizer_iff.1 (hA ⟨x, x.2, rfl⟩) c c.2
    rw [← hx, hδdef, linearSwapDiag_apply]
    change (x : G) * (t * x * t⁻¹) * c = c * (x * (t * x * t⁻¹))
    calc (x : G) * (t * x * t⁻¹) * c = x * ((t * x * t⁻¹) * c) := by group
      _ = x * (c * (t * x * t⁻¹)) := by rw [h2]
      _ = (x * c) * (t * x * t⁻¹) := by group
      _ = (c * x) * (t * x * t⁻¹) := by rw [h1]
      _ = c * (x * (t * x * t⁻¹)) := by group
  have hgen : (⨆ j, C j) = ⊤ := by
    refine LinearPilot.eq_top_of_sup_center_eq_top_of_perfect ?_
    have hi : ∀ j, (C j).map π = simpleRootSL2 K j := by
      intro j
      rw [hC, CFSG.Quasithin.map_perfectCore, hB, Subgroup.map_comap_eq_self_of_surjective hπs,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (commutator_simpleRootSL2_eq_of_four_le hK4 j)]
    have hmap : (⨆ j, C j).map π = ⊤ := by
      rw [Subgroup.map_iSup]
      simp_rw [hi]
      exact iSup_simpleRootSL2_eq_top hn
    refine eq_top_iff.2 ?_
    calc (⊤ : Subgroup A) = (⨆ j, C j) ⊔ π.ker := by
          rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
      _ ≤ (⨆ j, C j) ⊔ center A := sup_le_sup_left hπker _
  intro g hg
  have hmem : (⟨g, hg⟩ : A) ∈ ⨆ j, C j := hgen ▸ mem_top _
  have h2 : g ∈ (⨆ j, C j).map A.subtype := ⟨⟨g, hg⟩, hmem, rfl⟩
  rw [Subgroup.map_iSup] at h2
  exact (iSup_mono hCpiece) h2

end Swap

section Factor

variable {G : Type} [Group G] [Finite G]

theorem exists_factorAut_of_odd {L : Subgroup G} (hZL : center L = ⊥) {C : Type*} [Group C]
    [Finite C] (e : L ≃* C) {A : Subgroup G} {φ : A →* L} (hφ : Function.Surjective φ)
    (hφZ : φ.ker ≤ center A) (hodd : Odd (Nat.card (center A))) {t : G} (htt : t * t = 1)
    (htA : t ∈ normalizer (A : Set G)) :
    ∃ θ : MulAut C, θ * θ = 1 ∧
      Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) = Nat.card (fixedSubgroup θ) *
        Nat.card ((A ⊓ centralizer ({t} : Set G)) ⊓ (center A).map A.subtype : Subgroup G) ∧
      Nat.card (perfectCore (A ⊓ centralizer ({t} : Set G))) =
        Nat.card (perfectCore (fixedSubgroup θ)) *
          Nat.card (perfectCore (A ⊓ centralizer ({t} : Set G)) ⊓ (center A).map A.subtype :
            Subgroup G) := by
  set τ := A.normalizerMonoidHom ⟨t, htA⟩ with hτ
  have hτ2 : τ * τ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one A htA (by rw [sq]; exact htt)
  have hker := LinearPilot.ker_eq_center_of_surjective hZL hφ hφZ
  set ψ : A ⧸ center A ≃* C :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).trans e with hψ
  set θ := MulAut.congr ψ (F4Pilot.centerQuotientAut τ) with hθ
  have hfix : (fixedSubgroup τ).map A.subtype = A ⊓ centralizer ({t} : Set G) :=
    F4Pilot.map_fixedSubgroup_normalizerMonoidHom A htA
  have hcore : (perfectCore (fixedSubgroup τ)).map A.subtype =
      perfectCore (A ⊓ centralizer ({t} : Set G)) := by
    rw [CFSG.Quasithin.map_perfectCore, hfix]
  refine ⟨θ, ?_, ?_, ?_⟩
  · rw [hθ, ← map_mul, ← LinearPilot.centerQuotientAut_mul, hτ2, LinearPilot.centerQuotientAut_one,
      map_one]
  · rw [← hfix, card_map_of_injective A.subtype_injective, hθ, LinearPilot.card_fixedSubgroup_congr,
      LinearPilot.card_fixedSubgroup_eq_of_odd hτ2 hodd, ← map_inf _ _ _ A.subtype_injective,
      card_map_of_injective A.subtype_injective]
  · rw [← hcore, card_map_of_injective A.subtype_injective, hθ,
      LinearPilot.card_perfectCore_fixedSubgroup_congr,
      LinearPilot.card_perfectCore_fixedSubgroup_eq, ← map_inf _ _ _ A.subtype_injective,
      card_map_of_injective A.subtype_injective]

end Factor

section Pair

variable {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem mul_self_eq_one_of_conj_mul_self {s : StatedSp n K}
    (h : MulAut.conj s * MulAut.conj s = 1) : s * s = 1 := by
  have h1 : MulAut.conj (s * s) = 1 := by rw [map_mul]; exact h
  have h2 : s * s ∈ center (StatedSp n K) := by
    rw [mem_center_iff]
    intro y
    have h3 := DFunLike.congr_fun h1 y
    rw [MulAut.conj_apply, MulAut.one_apply] at h3
    calc y * (s * s) = (s * s) * y * (s * s)⁻¹ * (s * s) := by rw [h3]
      _ = (s * s) * y := by group
  rwa [center_statedSp_eq_bot, mem_bot] at h2

omit [Finite K] [CharP K 2] in
theorem involution_dichotomy_sp [Finite K] [CharP K 2] (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ f)
    {θ : MulAut (StatedSp n K)} (hθ : θ * θ = 1) :
    f * (n * (n + 1) / 2) ≤ (Nat.card (fixedSubgroup θ)).factorization 2 ∨
      ∃ k : Subfield K, Nat.card k ^ 2 = Nat.card K ∧
        Nat.card (fixedSubgroup θ) = Nat.card (StatedSp n k) ∧
        perfectCore (fixedSubgroup θ) = fixedSubgroup θ := by
  by_cases hi : θ ∈ (MulAut.conj : StatedSp n K →* MulAut (StatedSp n K)).range
  · left
    obtain ⟨s, rfl⟩ := hi
    have hss := mul_self_eq_one_of_conj_mul_self hθ
    have hdvd := pow_dvd_card_centralizer_statedSp (F := K) hss
    rw [← fixedSubgroup_conj_eq_centralizer, hK, ← pow_mul] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  · right
    obtain ⟨k, hk, hcard, hperf⟩ := exists_subfield_of_not_inner hn hθ hi
    exact ⟨k, hk, hcard, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf⟩

omit [Finite K] [CharP K 2] in
theorem exists_card_subfield_of_sq [Finite K] [CharP K 2] (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ f)
    (k : Subfield K) (hk : Nat.card k ^ 2 = Nat.card K) :
    ∃ f' : ℕ, 2 * f' = f ∧ 1 ≤ f' ∧ Nat.card k = 2 ^ f' ∧
      (Nat.card (StatedSp n k)).factorization 2 = f' * n ^ 2 := by
  have : CharP k 2 := (k.subtype).charP k.subtype_injective 2
  obtain ⟨f', hf', hkc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k)
  have h2 : 2 ^ (f' * 2) = 2 ^ f := by rw [pow_mul, ← hkc, hk, hK]
  have h3 : f' * 2 = f := Nat.pow_right_injective le_rfl h2
  exact ⟨f', by omega, hf', hkc, factorization_card_statedSp hn hkc hf'⟩

omit [Finite K] [CharP K 2] in
theorem false_of_involution_pair_sp [Finite K] [CharP K 2] (hn : 4 ≤ n)
    (hK : Nat.card K = 2 ^ f) {θ₁ θ₂ : MulAut (StatedSp n K)} (h₁ : θ₁ * θ₁ = 1)
    (h₂ : θ₂ * θ₂ = 1)
    (hC1 : (Nat.card (fixedSubgroup θ₁)).factorization 2 +
      (Nat.card (fixedSubgroup θ₂)).factorization 2 ≤ f * n ^ 2 + 1 + f.factorization 2)
    (hC3 : Nat.card (perfectCore (fixedSubgroup θ₁)) * Nat.card (perfectCore (fixedSubgroup θ₂)) ∣
      Nat.card (StatedSp n K)) : False := by
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hnn : n * (n + 1) / 2 * 2 = n * (n + 1) :=
    Nat.div_mul_cancel (Nat.even_mul_succ_self n).two_dvd
  have hmixed : ∀ f' : ℕ, 2 * f' = f → 1 ≤ f' →
      f * (n * (n + 1) / 2) + f' * n ^ 2 ≤ f * n ^ 2 + 1 + f.factorization 2 → False := by
    intro f' hf'2 hf'1 h
    have hvf' : f.factorization 2 = 1 + f'.factorization 2 := by
      rw [← hf'2, Nat.factorization_mul two_ne_zero (by omega), Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two]
    have hvf'' : f'.factorization 2 < f' := Nat.factorization_lt 2 (by omega)
    have h5 : f * (n * (n + 1) / 2) = f' * n ^ 2 + f' * n := by
      rw [← hf'2]
      calc 2 * f' * (n * (n + 1) / 2) = f' * (n * (n + 1) / 2 * 2) := by ring
        _ = f' * n ^ 2 + f' * n := by rw [hnn]; ring
    have h6 : f * n ^ 2 = 2 * (f' * n ^ 2) := by rw [← hf'2]; ring
    have h4 : 4 * f' ≤ f' * n := by nlinarith
    omega
  rcases involution_dichotomy_sp (by omega) hK h₁ with hi₁ | ⟨k₁, hk₁, hc₁, hp₁⟩ <;>
    rcases involution_dichotomy_sp (by omega) hK h₂ with hi₂ | ⟨k₂, hk₂, hc₂, hp₂⟩
  ·
    have h4 : 2 * f ≤ f * n := by nlinarith
    have h5 : f * (n * (n + 1) / 2) * 2 = f * n ^ 2 + f * n := by
      calc f * (n * (n + 1) / 2) * 2 = f * (n * (n + 1) / 2 * 2) := by ring
        _ = f * n ^ 2 + f * n := by rw [hnn]; ring
    omega
  ·
    obtain ⟨f', hf'2, hf'1, -, hv⟩ := exists_card_subfield_of_sq (n := n) (by omega) hK k₂ hk₂
    rw [hc₂, hv] at hC1
    exact hmixed f' hf'2 hf'1 (by omega)
  ·
    obtain ⟨f', hf'2, hf'1, -, hv⟩ := exists_card_subfield_of_sq (n := n) (by omega) hK k₁ hk₁
    rw [hc₁, hv] at hC1
    exact hmixed f' hf'2 hf'1 (by omega)
  ·
    obtain ⟨f₁, -, -, hk₁c, -⟩ := exists_card_subfield_of_sq (n := n) (by omega) hK k₁ hk₁
    have hk₁₂ : Nat.card k₁ = Nat.card k₂ :=
      Nat.pow_left_injective two_ne_zero (hk₁.trans hk₂.symm)
    have hSp : Nat.card (StatedSp n k₂) = Nat.card (StatedSp n k₁) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hk₁₂]
    rw [hp₁, hp₂, hc₁, hc₂, hSp, ← sq] at hC3
    exact not_sq_card_statedSp_dvd (by omega) hk₁c hk₁.symm hC3

end Pair

section NonSwap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem odd_card_center_of_swapFactors {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) : Odd (Nat.card (center G₁)) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLG₀ : L ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨x, hx, rfl⟩)
  have htN : t ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    F4Pilot.mem_normalizer_sup_of_map_conj_eq htt rfl
  have htZ : t ∉ centralizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    intro htZ
    obtain ⟨hpA, hbA, -⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
    have hfix : ∀ x ∈ G₁, t * x * t⁻¹ = x := by
      intro x hx
      have h1 : x * t = t * x := mem_centralizer_iff.1 htZ x (mem_sup_left hx)
      rw [← h1]
      group
    have hG₂ : G₁.map (MulAut.conj t).toMonoidHom = G₁ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change t * y * t⁻¹ ∈ G₁
        rw [hfix y hy]
        exact hy
      · intro hx
        exact ⟨x, hx, hfix x hx⟩
    have h2 : G₁ ≤ centralizer (G₁ : Set G) := by
      have h3 := h₁₂
      rw [hG₂] at h3
      exact h3
    apply hbA
    rw [← hpA, commutator_eq_bot_iff_le_centralizer.2 h2]
  have hodd := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLG₀ ht htN htZ
  have hle : (center G₁).map G₁.subtype ≤
      centralizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hsup : G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer ({(z : G)} : Set G) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val ((mem_center_iff.1 hz) ⟨y, hy⟩)
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 (h₁₂ hy) z z.2).symm
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.1 (hsup hy)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [card_map_of_injective G₁.subtype_injective] at hdvd
  exact Odd.of_dvd_nat hodd hdvd

theorem false_of_mem_normalizer_factors (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {A : Subgroup G}
    {φ : A →* L} (hφs : Function.Surjective φ) (hφZ : φ.ker ≤ center A)
    (hoddA : Odd (Nat.card (center A))) (g : G)
    (hAB : A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G))
    (htA : t ∈ normalizer (A : Set G))
    (htB : t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) : False := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
  have hZL : center L = ⊥ := hset.center_eq_bot
  set B := A.map (MulAut.conj g).toMonoidHom with hB
  obtain ⟨φB, hφBs, hφBZ⟩ := LinearPilot.exists_surjective_map_conj hφs hφZ g
  have hoddB : Odd (Nat.card (center B)) := by
    let E : A ≃* B := A.equivMapOfInjective _ (MulAut.conj g).injective
    rw [← map_center_eq E, card_map_of_injective E.injective]
    exact hoddA
  obtain ⟨θA, hθA2, hcA, hpA⟩ := exists_factorAut_of_odd hZL e hφs hφZ hoddA htt htA
  obtain ⟨θB, hθB2, hcB, hpB⟩ := exists_factorAut_of_odd hZL e hφBs hφBZ hoddB htt htB
  have hBA : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.1 (hAB hy) x hx
  have hIZ : A ⊓ B ≤ (center A).map A.subtype := by
    rintro x ⟨hxA, hxB⟩
    refine ⟨⟨x, hxA⟩, mem_center_iff.2 fun y => Subtype.ext (hBA y y.2 x hxB), rfl⟩
  set CA := A ⊓ centralizer ({t} : Set G) with hCA
  set CB := B ⊓ centralizer ({t} : Set G) with hCB
  have hcomm : ∀ x ∈ CA, ∀ y ∈ CB, x * y = y * x := fun x hx y hy => hBA x hx.1 y hy.1
  have hIZC : CA ⊓ CB ≤ (center A).map A.subtype := fun x hx => hIZ ⟨hx.1.1, hx.2.1⟩
  have hC1 : Nat.card (fixedSubgroup θA) * Nat.card (fixedSubgroup θB) ∣
      Nat.card (CA ⊔ CB : Subgroup G) :=
    LinearPilot.mul_dvd_card_sup_of_commute hcomm hIZC hcA ⟨_, hcB⟩
  have hDt : CA ⊔ CB ≤ centralizer ({t} : Set G) := sup_le inf_le_right inf_le_right
  have hv := factorization_card_le_of_le_centralizer_sp hset.standardSetting.standard (by omega)
    hKc e ht hKt hDt
  have hv1 : (Nat.card (fixedSubgroup θA)).factorization 2 +
      (Nat.card (fixedSubgroup θB)).factorization 2 ≤ f * n ^ 2 + 1 + f.factorization 2 := by
    have h1 := (Nat.factorization_le_iff_dvd (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
      Nat.card_pos.ne').2 hC1 2
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply] at h1
    omega
  set PA := perfectCore CA with hPA
  set PB := perfectCore CB with hPB
  have hPAL : PA ≤ L := std_perfect_le hset.standardSetting hOut htC ht
    (CFSG.Quasithin.perfectCore_perfect _) ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
  have hPBL : PB ≤ L := std_perfect_le hset.standardSetting hOut htC ht
    (CFSG.Quasithin.perfectCore_perfect _) ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
  have hPcomm : ∀ x ∈ PA, ∀ y ∈ PB, x * y = y * x := fun x hx y hy =>
    hcomm x (CFSG.Quasithin.perfectCore_le _ hx) y (CFSG.Quasithin.perfectCore_le _ hy)
  have hPIZ : PA ⊓ PB ≤ (center A).map A.subtype := fun x hx =>
    hIZC ⟨CFSG.Quasithin.perfectCore_le _ hx.1, CFSG.Quasithin.perfectCore_le _ hx.2⟩
  have hC3 : Nat.card (perfectCore (fixedSubgroup θA)) *
      Nat.card (perfectCore (fixedSubgroup θB)) ∣ Nat.card (PA ⊔ PB : Subgroup G) :=
    LinearPilot.mul_dvd_card_sup_of_commute hPcomm hPIZ hpA ⟨_, hpB⟩
  have hPL : Nat.card (PA ⊔ PB : Subgroup G) ∣ Nat.card (StatedSp n K) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_le (sup_le hPAL hPBL)
  exact false_of_involution_pair_sp hn hKc hθA2 hθB2 hv1 (hC3.trans hPL)

end NonSwap

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem unique_of_spSwapRow (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hsup : G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = ⨆ k : Fin n, neighbourCore e k)
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer ((⨆ k : Fin n, neighbourCore e k : Subgroup G) : Set G) →
      g ∈ normalizer ((⨆ k : Fin n, neighbourCore e k : Subgroup G) : Set G) := by
  rw [← hsup]
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
  have hcard₁ := LinearPilot.card_quotient_center_eq_of_swapFactors hset.center_eq_bot h₁₂ hδ
    hsurj
  have hodd₁ := odd_card_center_of_swapFactors ht hKt hq h₁₂ hsurj
  refine F4Pilot.unique_of_forall_conjugate_eq fun h htM => ?_
  have hM : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h =
      CFSG.conjugate G₁ h ⊔ CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h :=
    Subgroup.map_sup _ _ _
  rw [hM] at htM
  have hqA := LinearPilot.isQuasisimple_conjugate hq h
  have hqB := LinearPilot.isQuasisimple_conjugate (LinearPilot.isQuasisimple_map_conj hq t) h
  have hAB := LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ h
  have hBA := le_centralizer_iff.1 hAB
  obtain ⟨hpA, hbA, hnA⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqA
  obtain ⟨hpB, hbB, hnB⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqB
  rcases F4Pilot.map_conj_eq_or_eq_of_perfect hAB hpA hbA hnA hnB htM with hAA | hswap
  ·
    exfalso
    rcases F4Pilot.map_conj_eq_or_eq_of_perfect hBA hpB hbB hnB hnA
        (by rw [sup_comm]; exact htM) with hBB | hBA'
    ·
      have hBconj := LinearPilot.map_conj_conjugate_eq (A := G₁) h t
      have hoddA : Odd (Nat.card (center (CFSG.conjugate G₁ h))) := by
        let E : G₁ ≃* CFSG.conjugate G₁ h := LinearPilot.conjugateEquiv G₁ h
        rw [← map_center_eq E, card_map_of_injective E.injective]
        exact hodd₁
      obtain ⟨φA, hφAs, hφAZ⟩ :=
        LinearPilot.exists_surjective_conjugate_of_linearSwapDiag h₁₂ hδ hsurj h
      refine false_of_mem_normalizer_factors hset hn hKc e ht hKt hφAs hφAZ hoddA (h⁻¹ * t * h)
        ?_ (F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hAA) ?_
      · rw [hBconj]
        exact hAB
      · rw [hBconj]
        exact F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hBB
    ·
      have hAB' : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h = CFSG.conjugate G₁ h :=
        F4Pilot.map_conj_toMonoidHom_inj.1 (hBA'.trans hAA.symm)
      rw [hAB'] at hAB
      exact hbA (by rw [← hpA, commutator_eq_bot_iff_le_centralizer.2 hAB])
  ·
    have hA : (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom ≤
        centralizer (CFSG.conjugate G₁ h : Set G) := by
      rw [hswap]
      exact hAB
    have hcardA : Nat.card L ≤
        Nat.card (CFSG.conjugate G₁ h ⧸ center (CFSG.conjugate G₁ h)) := by
      rw [← Nat.card_congr (LinearPilot.conjugateQuotientCenterEquiv G₁ h).toEquiv, hcard₁]
    have hAle : CFSG.conjugate G₁ h ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
      rw [hsup]
      exact (le_spGlobal_of_swap hset.standardSetting hOut (by omega) hK4 e htC ht hqA hA
        hcardA).trans (spGlobal_le_iSup_neighbourCore (by omega) e)
    have htG₀ : t ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) :
        Set G) := F4Pilot.mem_normalizer_sup_of_map_conj_eq htt rfl
    have hBle : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h ≤
        G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
      rw [← hswap]
      calc (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom
          ≤ (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom :=
            map_mono hAle
        _ = G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom :=
            F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 htG₀
    have hle : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h ≤
        G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
      rw [hM]
      exact sup_le hAle hBle
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge

theorem spSwapRowUniqueInput_holds : SpSwapRowUniqueInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt _ G₁ hq h₁₂ hsup hδ hsurj
  exact unique_of_spSwapRow hset hn hKc hf e ht hKt hq h₁₂ hsup hδ hsurj

end Unique

end CFSG.SeitzReduction.SymplecticPilot
