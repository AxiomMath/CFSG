module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapDiagData
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracSw
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma34Solv

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Moved

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem perfect_le_layer_of_le_EPlus {W : Type} [Group W] [Finite W] (hO : pPrimeCore 2 W = ⊥)
    {Yh : Subgroup W} (hperf : ⁅Yh, Yh⁆ = Yh) (hE : Yh ≤ EPlus W) : Yh ≤ layer W := by
  classical
  have h3 : pCore 3 W = ⊥ := pCore_three_eq_bot hO
  haveI h1 : Group.IsSolvable ↥(NOne W) := isSolvable_NOne h3
  haveI h2 : Group.IsSolvable ↥(NTwo W) := isSolvable_NTwo h3
  haveI hN1 : (NOne W).Normal := NOne_normal
  haveI hN2 : (NTwo W).Normal := NTwo_normal
  have hS : Group.IsSolvable ↥(NOne W ⊔ NTwo W) :=
    CFSG.SignalizerFunctor.Helpers.solvable_sup_of_normalizing (NOne W) (NTwo W)
      (fun x _ => by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        exact ⟨fun hy => hN1.conj_mem y hy x, fun hy => by
          have := hN1.conj_mem _ hy x⁻¹
          simpa [mul_assoc] using this⟩) h1 h2
  haveI hlC : (layer W).Characteristic := layer_characteristic
  haveI hlN : (layer W).Normal := inferInstance
  let φ : W →* W ⧸ layer W := QuotientGroup.mk' (layer W)
  let ψ : ↥(NOne W ⊔ NTwo W) →* W ⧸ layer W := φ.comp (NOne W ⊔ NTwo W).subtype
  have hRsolv : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  have hRle : Yh.map φ ≤ ψ.range := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ layer W ⊔ (NOne W ⊔ NTwo W) := by
      have := hE hy
      rwa [EPlus, sup_assoc] at this
    obtain ⟨l, hl, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy'
    refine ⟨⟨n, hn⟩, ?_⟩
    show φ n = φ (l * n)
    have hφl : φ l = 1 := (QuotientGroup.eq_one_iff l).2 hl
    rw [map_mul, hφl, one_mul]
  have hRperf : ⁅Yh.map φ, Yh.map φ⁆ = Yh.map φ := by
    rw [← Subgroup.map_commutator, hperf]
  have hRbot : Yh.map φ = ⊥ := by
    by_contra hne
    haveI : Group.IsSolvable ↥(Yh.map φ) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hRle)
    haveI : Nontrivial ↥(Yh.map φ) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥(Yh.map φ)
    have hperf' : commutator ↥(Yh.map φ) = ⊤ :=
      Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hRperf)
    exact absurd hperf' hlt.ne
  intro y hy
  have : φ y ∈ Yh.map φ := Subgroup.mem_map_of_mem φ hy
  rw [hRbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff y).1 this

theorem normalizes_of_perfect_le_LPlusIn {H Y B : Subgroup X} (hY : ⁅Y, Y⁆ = Y)
    (hYL : Y ≤ LPlusIn H) (hB : IsPCompIn 2 H B) : Y ≤ normalizer (B : Set X) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYH : Y ≤ H := hYL.trans (LPlusIn_le H)
  have hY₀map : (Y.subgroupOf H).map H.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYH
  have hY₀perf : ⁅Y.subgroupOf H, Y.subgroupOf H⁆ = Y.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hY₀map, hY]
  have hYhperf : ⁅(Y.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)),
      (Y.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H))⁆ =
      (Y.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) := by
    rw [← Subgroup.map_commutator, hY₀perf]
  have hYhE : (Y.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) ≤
      EPlus (↥H ⧸ pPrimeCore 2 ↥H) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hwy⟩ := hYL (show (y : X) ∈ Y from hy)
    have hwy' : w = y := Subtype.ext hwy
    rw [hwy'] at hw
    exact hw
  have hYhlayer := perfect_le_layer_of_le_EPlus (pPrimeCore_quotient_eq_bot (G := ↥H)
    Nat.prime_two) hYhperf hYhE
  obtain ⟨K, hK, -, hKeq, -⟩ := hB.2
  have hKN : layer (↥H ⧸ pPrimeCore 2 ↥H) ≤ normalizer (K : Set (↥H ⧸ pPrimeCore 2 ↥H)) :=
    layer_le_normalizer hK
  intro y hy
  have hyH : y ∈ H := hYH hy
  have hyhY : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨y, hyH⟩ ∈
      (Y.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :=
    Subgroup.mem_map_of_mem _ (show (⟨y, hyH⟩ : ↥H) ∈ Y.subgroupOf H from hy)
  have hyN := hKN (hYhlayer hyhY)
  refine mem_normalizer_of_map_normalizes_pCompIn hB hyH ?_
  rw [hKeq]
  exact hyN

theorem eq_one_of_forall_comm_alt {n : ℕ} (hn : 4 ≤ n) (τ : Perm (Fin n))
    (hτ : ∀ g ∈ alternatingGroup (Fin n), τ * g = g * τ) : τ = 1 := by
  classical
  by_contra hτ1
  obtain ⟨a, ha⟩ : ∃ a, τ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hτ1 (Equiv.ext hcon)
  obtain ⟨b, hb⟩ : ∃ b, b = τ a := ⟨_, rfl⟩
  have hba : b ≠ a := by rw [hb]; exact ha
  have hcard : 1 < ((Finset.univ : Finset (Fin n)) \ {a, b}).card := by
    have h1 := Finset.le_card_sdiff ({a, b} : Finset (Fin n)) (Finset.univ : Finset (Fin n))
    have h2 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
    not_or] at hc hd
  have hac : a ≠ c := fun e => hc.1 e.symm
  have had : a ≠ d := fun e => hd.1 e.symm
  have hbc : b ≠ c := fun e => hc.2 e.symm
  have hbd : b ≠ d := fun e => hd.2 e.symm
  obtain ⟨γ, hγ⟩ : ∃ γ : Perm (Fin n), γ = Equiv.swap a c * Equiv.swap a d := ⟨_, rfl⟩
  have hγA : γ ∈ alternatingGroup (Fin n) := by
    rw [hγ, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hac,
      Equiv.Perm.sign_swap had]
    decide
  have h2 : γ a = d := by
    rw [hγ, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hcd)]
  have h3 : γ b = b := by
    rw [hγ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hba hbd,
      Equiv.swap_apply_of_ne_of_ne hba hbc]
  have h1 : τ (γ a) = γ (τ a) := by
    have := congrArg (fun f : Perm (Fin n) => f a) (hτ γ hγA)
    simpa only [Equiv.Perm.mul_apply] using this
  rw [h2, ← hb, h3] at h1
  exact had (τ.injective (h1.trans hb)).symm

theorem alternatingGroup_le_of_card {n : ℕ} (hn : 5 ≤ n) (H : Subgroup (Perm (Fin n)))
    (hH : (Nat.card (Perm (Fin n))) ≤ 2 * Nat.card H) : alternatingGroup (Fin n) ≤ H := by
  classical
  have hA := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hind : H.index = 1 ∨ H.index = 2 := by
    have h1 := Subgroup.card_mul_index H
    have hpos : 0 < H.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have hHpos : 0 < Nat.card H := Nat.card_pos
    have : H.index ≤ 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    omega
  rcases hind with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    rw [h1]
    exact le_top
  · haveI : H.Normal := Subgroup.normal_of_index_eq_two h2
    have hrel : (H.subgroupOf (alternatingGroup (Fin n))).index ∣ 2 := by
      have := Subgroup.relIndex_dvd_index_of_normal (H := H) (K := alternatingGroup (Fin n))
      rwa [h2] at this
    have hK : (H.subgroupOf (alternatingGroup (Fin n))).index = 1 := by
      have hle : (H.subgroupOf (alternatingGroup (Fin n))).index = 1 ∨
          (H.subgroupOf (alternatingGroup (Fin n))).index = 2 :=
        (Nat.dvd_prime Nat.prime_two).1 hrel
      rcases hle with h | h
      · exact h
      · haveI : (H.subgroupOf (alternatingGroup (Fin n))).Normal :=
          Subgroup.normal_of_index_eq_two h
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (H.subgroupOf (alternatingGroup (Fin n))) with hb | ht
        · rw [hb, Subgroup.index_bot] at h
          have h5 := two_mul_nat_card_alternatingGroup (α := Fin n)
          have hfac : 120 ≤ Nat.card (Perm (Fin n)) := by
            rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
            calc 120 = Nat.factorial 5 := by decide
              _ ≤ Nat.factorial n := Nat.factorial_le hn
          omega
        · rw [ht, Subgroup.index_top] at h
          omega
    rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hK
    exact hK

theorem perm_eq_one_of_commute {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 5 ≤ n)
    (h2 : primeResidual 2 G = ⊤)
    (e : Nonempty (G ⧸ pPrimeCore 2 G ≃* alternatingGroup (Fin n)))
    (θ : G →* Perm (Fin n)) (hθ : ∃ g, θ g ≠ 1) (τ : Perm (Fin n))
    (hτ : ∀ g, τ * θ g = θ g * τ) : τ = 1 := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := e
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  haveI hAs : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  haveI : IsSimpleGroup (G ⧸ pPrimeCore 2 G) := MulEquiv.isSimpleGroup e
  have hker : θ.ker ≤ pPrimeCore 2 G := by
    by_contra hk
    haveI hN : (θ.ker.map (QuotientGroup.mk' (pPrimeCore 2 G))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (θ.ker.map (QuotientGroup.mk' (pPrimeCore 2 G))) with hb | ht
    · apply hk
      intro k hkk
      have h1 : QuotientGroup.mk' (pPrimeCore 2 G) k ∈ (⊥ : Subgroup (G ⧸ pPrimeCore 2 G)) :=
        hb ▸ Subgroup.mem_map_of_mem _ hkk
      exact (QuotientGroup.eq_one_iff k).1 (Subgroup.mem_bot.1 h1)
    · have hcover : ∀ g : G, ∃ k ∈ θ.ker, ∃ o ∈ pPrimeCore 2 G, g = k * o := by
        intro g
        have hg : QuotientGroup.mk' (pPrimeCore 2 G) g ∈
            θ.ker.map (QuotientGroup.mk' (pPrimeCore 2 G)) := ht ▸ Subgroup.mem_top _
        obtain ⟨k, hk', hkg⟩ := Subgroup.mem_map.1 hg
        refine ⟨k, hk', k⁻¹ * g, ?_, by group⟩
        rw [← QuotientGroup.ker_mk' (pPrimeCore 2 G), MonoidHom.mem_ker, map_mul, map_inv, hkg]
        group
      have hodd : Nat.Coprime 2 (Nat.card (pPrimeCore 2 G)) := pPrimeCore_coprime_card
      have htriv : ∀ x : G, (∃ j : ℕ, orderOf x = 2 ^ j) → θ x = 1 := by
        rintro x ⟨j, hj⟩
        obtain ⟨k, hkk, o, ho, hxko⟩ := hcover x
        have hθx : θ x = θ o := by
          rw [hxko, map_mul, MonoidHom.mem_ker.1 hkk, one_mul]
        have h3 : orderOf (θ x) ∣ 2 ^ j := hj ▸ orderOf_map_dvd θ x
        have h4 : orderOf (θ x) ∣ Nat.card (pPrimeCore 2 G) := by
          rw [hθx]
          have h5 := orderOf_dvd_natCard (⟨o, ho⟩ : pPrimeCore 2 G)
          rw [← Subgroup.orderOf_coe] at h5
          exact (orderOf_map_dvd θ o).trans h5
        have h6 : Nat.Coprime (orderOf (θ x)) (Nat.card (pPrimeCore 2 G)) :=
          Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_left j hodd)
        exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h6 h4)
      obtain ⟨g, hg⟩ := hθ
      apply hg
      have hgt : g ∈ (⊤ : Subgroup G) := Subgroup.mem_top g
      rw [← h2, primeResidual_eq_closure] at hgt
      exact (Subgroup.closure_le θ.ker).2 (fun x hx => MonoidHom.mem_ker.2 (htriv x hx)) hgt
  have hcard : Nat.card (Perm (Fin n)) ≤ 2 * Nat.card θ.range := by
    have hsurj : Function.Surjective
        (QuotientGroup.map θ.ker (pPrimeCore 2 G) (MonoidHom.id G) (by simpa using hker)) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨QuotientGroup.mk g, rfl⟩
    have h1 : Nat.card (G ⧸ pPrimeCore 2 G) ≤ Nat.card (G ⧸ θ.ker) :=
      Nat.card_le_card_of_surjective _ hsurj
    have h2' : Nat.card (G ⧸ θ.ker) = Nat.card θ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
    have h3 : Nat.card (G ⧸ pPrimeCore 2 G) = Nat.card (alternatingGroup (Fin n)) :=
      Nat.card_congr e.toEquiv
    have h4 := two_mul_nat_card_alternatingGroup (α := Fin n)
    omega
  have hA : alternatingGroup (Fin n) ≤ θ.range := alternatingGroup_le_of_card hn _ hcard
  refine eq_one_of_forall_comm_alt (by omega) τ fun g hg => ?_
  obtain ⟨x, rfl⟩ := hA hg
  exact hτ x

theorem exists_moved_of_diag (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s) (hzs : z * s = s * z)
    {M Δ : Subgroup X} (hD : SwapDiag X n z s M Δ)
    (hnt : ∃ B, Sec5Comp X n (centralizer ({s} : Set X)) B ∧ ∃ d ∈ Δ, ∃ b ∈ B,
      ⁅b, d⁆ ∉ oddCoreOf (centralizer ({s} : Set X))) :
    ∃ B, Sec5Comp X n (centralizer ({s} : Set X)) B ∧
      B.map (MulAut.conj z).toMonoidHom ≠ B := by
  classical
  obtain ⟨B, hB, d₀, hd₀, b₀, hb₀, hnot⟩ := hnt
  refine ⟨B, hB, fun hzB => ?_⟩
  have hn : 8 ≤ n := h.maxdeg.1
  have hz1 : z ≠ 1 := by
    intro e
    have := h.orderOf_z
    rw [e, orderOf_one] at this
    omega
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z] at this
  have hzN : z ∈ normalizer (B : Set X) := mem_normalizer_of_map_conj_eq hzB
  have hΔL : Δ ≤ LPlusIn (centralizer ({s} : Set X)) :=
    le_LPlusIn_of_isPCompIn_inf hz2 hzs hD.isPComp
  have hΔN : Δ ≤ normalizer (B : Set X) :=
    normalizes_of_perfect_le_LPlusIn hD.perfect hΔL hB.isPCompIn
  set Mm : AhatModel X n B := AhatModel.ofCover hB.2 with hMm
  let Θ : ↥Δ →* Perm (Fin n) := (Mm.permHom hn).comp (Subgroup.inclusion hΔN)
  have hΘ : ∀ d : ↥Δ, Θ d = Mm.perm (d : X) (hΔN d.2) := fun d => rfl
  have hΘne : ∃ d : ↥Δ, Θ d ≠ 1 := by
    refine ⟨⟨d₀, hd₀⟩, fun h1 => ?_⟩
    rw [hΘ] at h1
    have hc : CentModOdd B d₀ := (Mm.perm_eq_one_iff hn (hΔN hd₀)).1 h1
    exact hnot (oddCoreOf_le_of_isPCompIn hB.isPCompIn (hc b₀ hb₀))
  have hτ : ∀ d : ↥Δ, Mm.perm z hzN * Θ d = Θ d * Mm.perm z hzN := by
    intro d
    have hdz : (d : X) * z = z * (d : X) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hD.le_cen d.2).1
    rw [hΘ]
    calc Mm.perm z hzN * Mm.perm (d : X) (hΔN d.2)
        = Mm.perm (z * (d : X)) (Subgroup.mul_mem _ hzN (hΔN d.2)) :=
          (Mm.perm_mul hn hzN (hΔN d.2)).symm
      _ = Mm.perm ((d : X) * z) (Subgroup.mul_mem _ (hΔN d.2) hzN) := by
          congr 1
          exact hdz.symm
      _ = Mm.perm (d : X) (hΔN d.2) * Mm.perm z hzN := Mm.perm_mul hn (hΔN d.2) hzN
  have hτ1 : Mm.perm z hzN = 1 :=
    perm_eq_one_of_commute (by omega) hD.twoGen hD.quot Θ hΘne _ hτ
  have hcent : CentModOdd B z := (Mm.perm_eq_one_iff hn hzN).1 hτ1
  have hsc : z ∈ centralizerSection B (pPrimeCoreOf 2 B) := mem_QOf_iff.2 ⟨hzN, hcent⟩
  exact K0_ne_bot_of_centralizerSection hz2 hB hsc (sec5_K0_inf_eq_bot h hs h.z_mem hz1 hzs)

end Moved

end CFSG.OddStandard.Solomon75
