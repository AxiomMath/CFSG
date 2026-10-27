module

public import CFSG.GH74.GLS.C3.Layer1.P34RealL2B
public import CFSG.GH74.GLS.C3.Layer1.P34RealAut
public import CFSG.GH74.GLS.C3.Layer1.P34RealL2A
public import CFSG.GH74.GLS.IVK.L2.KI2Aux
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

section L2

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_sigma_of_outer (hF : L2Field F) {e' : K ≃* L2 F} (N : L2Notation e')
    {y : MulAut K} (hyT : y ∈ (N.T : Subgroup (MulAut K))) (hy2 : y * y = 1)
    (hyD : y ∉ innDiagSub e') :
    ∃ σ ∈ N.R, orderOf σ = 2 ∧ ∃ p ∈ N.P, y = p * σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy1 : y ≠ 1 := fun h => hyD (h ▸ (innDiagSub e').one_mem)
  have hyord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  set τ : F ≃+* F := fieldProj e' y with hτ
  have hτ1 : τ ≠ 1 := fun h => hyD ((mem_innDiagSub_iff e' y).2 h)
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul, hy2, map_one]
  set σ₀ : MulAut K := fieldAutHom e' τ with hσ₀
  have hσ₀F : σ₀ ∈ fieldAutSub e' := ⟨τ, rfl⟩
  have hσ₀proj : fieldProj e' σ₀ = τ := fieldProj_fieldAutHom e' τ
  have hσ₀1 : σ₀ ≠ 1 := fun h => hτ1 (by rw [← hσ₀proj, h, map_one])
  have hσ₀sq : σ₀ * σ₀ = 1 := by
    rw [hσ₀, ← map_mul, hτ2, map_one]
  have hσ₀ord : orderOf σ₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ₀sq) hσ₀1
  have hσ₀T : σ₀ ∈ (N.T : Subgroup (MulAut K)) := by
    have hH : IsPGroup 2 ↥(zpowers σ₀) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hσ₀ord, pow_one]
    have hN : zpowers σ₀ ≤ normalizer ((N.T : Subgroup (MulAut K)) : Set (MulAut K)) :=
      (zpowers_le).2 (N.T_inv hσ₀F)
    exact le_sylow_of_le_normalizer N.T hH hN (mem_zpowers σ₀)
  have hσ₀R : σ₀ ∈ N.R := ⟨hσ₀T, hσ₀F⟩
  have hinnle : innAut K ≤ innDiagSub e' := innAut_le_innDiagSub e'
  rcases ivk_1_2i_c F hF K e' N σ₀ hσ₀R hσ₀ord y hyT hyord with h | ⟨h, -⟩ | ⟨p, hpP, hyp⟩
  · exact absurd (hinnle h.2) hyD
  · exact absurd h.2 hyD
  · exact ⟨σ₀, hσ₀R, hσ₀ord, p, hpP, hyp⟩

theorem exists_two_ne_one_of_four {M : Type} [Group M] {V : Subgroup M} (hV : Nat.card V = 4) :
    ∃ a ∈ V, ∃ b ∈ V, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have h1 : 1 < Nat.card V := by omega
  obtain ⟨a, haV, ha1⟩ : ∃ a ∈ V, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).2 hcon
    rw [this, Subgroup.card_bot] at hV
    omega
  obtain ⟨b, hbV, hb1, hba⟩ : ∃ b ∈ V, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (V : Set M) ⊆ {1, a} := by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · simp [hcon x hx hx1]
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 : ({1, a} : Set M).ncard ≤ 2 := by
      calc ({1, a} : Set M).ncard ≤ ({a} : Set M).ncard + 1 := Set.ncard_insert_le 1 {a}
        _ = 2 := by rw [Set.ncard_singleton]
    have h4 : Nat.card V = (V : Set M).ncard := (Nat.card_coe_set_eq (V : Set M)).symm ▸ rfl
    omega
  exact ⟨a, haV, b, hbV, ha1, hb1, hba.symm⟩

theorem exists_shear_elements (hF : L2Field F) {e' : K ≃* L2 F} (N : L2Notation e')
    {B : Subgroup (MulAut K)} (hPeq : N.P = B ⊓ innAut K)
    (hSyl : IsSylowOf 2 (B ⊓ innAut K) (innAut K)) {σ : MulAut K} (hσR : σ ∈ N.R)
    (hσ2 : orderOf σ = 2) {n : ℕ} (hn3 : 3 ≤ n) (hn : IsDihedralTwoGroup ↥N.P n) :
    (∃ x ∈ N.P, x * x = 1 ∧ x ∉ ((oResidual 2 ↥(fixedSubgroup K σ)).map
      (fixedSubgroup K σ).subtype).map (MulAut.conj : K →* MulAut K)) ∧
    (∃ V : Subgroup (MulAut K), V ≤ N.P ∧ V ≤ ((oResidual 2 ↥(fixedSubgroup K σ)).map
      (fixedSubgroup K σ).subtype).map (MulAut.conj : K →* MulAut K) ∧ Nat.card V = 4 ∧
      ∀ v ∈ V, v * v = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F₀, _, _, hodd₀, h3₀, -, ⟨φ⟩⟩ := pgl2_data hF e' hσR.2 hσ2
  have hconjinj := conj_injective_of_L2 e'
  set Y : Subgroup K := fixedSubgroup K σ with hY
  set Pk : Subgroup K := N.P.comap (MulAut.conj : K →* MulAut K) with hPk
  have hNPle : N.P ≤ (MulAut.conj : K →* MulAut K).range := by
    rw [hPeq]
    exact inf_le_right
  have hmapP : Pk.map (MulAut.conj : K →* MulAut K) = N.P := Subgroup.map_comap_eq_self hNPle
  have hPσ : ∀ q ∈ N.P, σ * q = q * σ := fun q hq => (N.R_cent σ hσR hσ2 q hq).symm
  have hPkY : Pk ≤ Y := by
    intro k hk
    have hc : MulAut.conj k ∈ N.P := hk
    have h1 := Proofs2.Lemma12hb.mul_conj_mul_inv σ k
    have h2 : σ * MulAut.conj k * σ⁻¹ = MulAut.conj k := by
      rw [hPσ _ hc]
      group
    rw [h2] at h1
    exact (hconjinj h1).symm
  have hPkcard : Nat.card Pk = Nat.card N.P := by
    calc Nat.card Pk = Nat.card (Pk.map (MulAut.conj : K →* MulAut K)) :=
        (Subgroup.card_map_of_injective hconjinj).symm
      _ = Nat.card N.P := by rw [hmapP]
  have hInncard : Nat.card ↥(innAut K) = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hconjinj).toEquiv).symm
  have hSylPk : IsSylowOf 2 Pk Y := by
    refine isSylowOf_of_card hPkY ?_
    rw [hPkcard, hPeq, hSyl.card_eq, hInncard, hY,
      fix_two_part_L2 hF e' hσR.2 hσ2]
  have eqPk : ↥Pk ≃* ↥N.P :=
    (Subgroup.equivMapOfInjective Pk (MulAut.conj : K →* MulAut K) hconjinj).trans
      (MulEquiv.subgroupCongr hmapP)
  have hdih : P34.IsDihedralGE8 Pk := isDihedralGE8_of_equiv eqPk hn3 hn.2
  have hgen := (P34.dihedralShapeFacts K Pk hdih).2.2.1
  obtain ⟨⟨x, hxS, hxsq, hxI⟩, ⟨V, hVS, hVI, hVc, hVsq⟩⟩ :=
    shear_abs hodd₀ h3₀ φ hPkY hSylPk hgen
  refine ⟨⟨MulAut.conj x, hxS, by rw [← map_mul, hxsq, map_one], ?_⟩,
    ⟨V.map (MulAut.conj : K →* MulAut K), ?_, Subgroup.map_mono hVI, ?_, ?_⟩⟩
  · rintro ⟨k, hk, hkx⟩
    exact hxI (by rw [← hconjinj hkx]; exact hk)
  · rintro _ ⟨v, hv, rfl⟩
    exact hVS hv
  · rw [Subgroup.card_map_of_injective hconjinj, hVc]
  · rintro _ ⟨v, hv, rfl⟩
    show MulAut.conj v * MulAut.conj v = 1
    rw [← map_mul, hVsq v hv, map_one]

theorem autP34_of_L2
    (hF : L2Field F) (e : K ≃* L2 F) {B : Subgroup (MulAut K)}
    (hB2 : IsPGroup 2 ↥B) (hSyl : IsSylowOf 2 (B ⊓ innAut K) (innAut K)) {α : MulAut K}
    (hαB : α ∈ B) (hα2 : orderOf α = 2) (hαe : α ∈ fieldAutSub e)
    (hαc : ∀ q ∈ B ⊓ innAut K, α * q = q * α) : ∃ z : MulAut K, AutP34 B α z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2hb : IVK_1_2h_b := Proofs2.ivk_1_2h_b
  obtain ⟨T', hBT'⟩ := hB2.exists_le_sylow
  obtain ⟨e', N, hNT⟩ := ivk_1_2a_exists F hF K e T'
  have hBN : B ≤ (N.T : Subgroup (MulAut K)) := by rw [hNT]; exact hBT'
  have hPeq : N.P = B ⊓ innAut K :=
    hSyl.eq_of_le (inf_le_inf_right _ hBN) inf_le_right N.T.isPGroup'.to_inf_left
  have hαα : α * α = 1 := by
    have := pow_orderOf_eq_one α
    rwa [hα2, sq] at this
  have hα1 : α ≠ 1 := fun h => by rw [h, orderOf_one] at hα2; omega
  have hαD : α ∉ innDiagSub e' := by
    rw [innDiagSub_eq e e']
    exact fun h => hα1 (eq_one_of_mem_fieldAutSub_of_mem_innDiagSub e hαe h)
  have hαinn : α ∉ innAut K := fun h => hαD (innAut_le_innDiagSub e' h)
  obtain ⟨σ, hσR, hσ2, p₀, hp₀P, hασ⟩ := exists_sigma_of_outer hF N (hBN hαB) hαα hαD
  obtain ⟨n, hn⟩ := ivk_1_2c F hF K e' N
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hn.2
  have hcard : Nat.card ↥N.P = 2 ^ n := by
    have h1 : Nat.card ↥N.P = Nat.card (DihedralGroup k) := Nat.card_congr φ.toEquiv
    have hk0 : NeZero k := ⟨by omega⟩
    rw [h1, Nat.card_eq_fintype_card, DihedralGroup.card]
    omega
  have hn3 : 3 ≤ n := three_le_of_involution_mem_R hF N hσR hσ2 n hcard
  obtain ⟨z, hzP, hz1, hzz, hzc⟩ := P_exists_central_involution hF N n hcard hn3
  have hzu : ∀ w ∈ N.P, (∀ q ∈ N.P, w * q = q * w) → w = 1 ∨ w = z := by
    intro w hw hwc
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (P_central_unique hF N n hcard hn3 hw hzP hw1 hz1 hwc (fun q hq => hzc q hq))
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hzB : z ∈ B ⊓ innAut K := by rw [← hPeq]; exact hzP
  have hPinn : N.P ≤ innAut K := hPeq ▸ inf_le_right
  have hσα : (∀ q ∈ B ⊓ innAut K, α * q = q * α) := hαc
  obtain ⟨hcls, hfus⟩ := fus_L2 h2hb hF N B hPeq hσR hσ2 hzP hz2 (fun q hq => hzc q hq) hzu
  have hαcls : α = σ ∨ α = σ * z := hcls α hαB hα2 hαinn hαc
  have hσα' : σ = α ∨ σ = α * z := by
    rcases hαcls with h | h
    · exact Or.inl h.symm
    · right
      rw [h, mul_assoc, hzz, mul_one]
  have hσB : σ ∈ B := by
    rcases hσα' with h | h
    · rw [h]; exact hαB
    · rw [h]; exact B.mul_mem hαB (hzB.1)
  have hmul : ∀ u u' : MulAut K, u ∈ N.Pt → u ∉ N.P → u' ∈ N.Pt → u' ∉ N.P → u' * u⁻¹ ∈ N.P := by
    intro u u' hu hu1 hu' hu1'
    have hidx := P_index_two hF N
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨u', hu'⟩ : ↥N.Pt))
      (b := (⟨u, hu⟩ : ↥N.Pt)⁻¹)).2 (by
        rw [inv_mem_iff]
        exact iff_of_false hu1' hu1)
    exact h1
  have hPt : ∀ u ∈ B, u * u = 1 → u ∉ (B ⊓ innAut K) ⊔ zpowers α → u ∈ N.Pt ∧ u ∉ N.P := by
    intro u huB hu2 hunot
    have hu1 : u ≠ 1 := fun h => hunot (h ▸ Subgroup.one_mem _)
    have huo : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
    have huT : u ∈ (N.T : Subgroup (MulAut K)) := hBN huB
    rcases ivk_1_2i_c F hF K e' N σ hσR hσ2 u huT huo with h | ⟨h, h'⟩ | ⟨p, hpP, hup⟩
    · exact absurd (Subgroup.mem_sup_left (hPeq ▸ h)) hunot
    · exact ⟨h, h'⟩
    · exfalso
      apply hunot
      rw [hup]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (hPeq ▸ hpP)) ?_
      rcases hσα' with h | h
      · rw [h]; exact Subgroup.mem_sup_right (mem_zpowers α)
      · rw [h]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers α))
          (Subgroup.mem_sup_left hzB)
  have hEq : ∀ u ∈ N.Pt, u ∉ N.P → N.P ⊔ zpowers u = N.Pt := by
    intro u hu hu1
    apply le_antisymm
    · exact sup_le (P_le_Pt N) ((zpowers_le).2 hu)
    · intro x hx
      by_cases hxP : x ∈ N.P
      · exact Subgroup.mem_sup_left hxP
      · have h1 := hmul u x hu hu1 hx hxP
        have h2 := Subgroup.mul_mem_sup h1 (Subgroup.mem_zpowers u)
        simpa using h2
  obtain ⟨E, hEcyc, hEF, ⟨m, hmodd, hEcard⟩, hcent, -, -⟩ := ivk_1_4j F hF K e' N
  have hPσ : ∀ q ∈ N.P, σ * q = q * σ := fun q hq => (N.R_cent σ hσR hσ2 q hq).symm
  have hEcentral : ∀ ε ∈ E, ∀ q ∈ N.P, q * ε = ε * q := by
    intro ε hε q hq
    have : ε ∈ centralizer (N.P : Set (MulAut K)) := by
      rw [hcent]
      exact Subgroup.mem_sup_right hε
    exact mem_centralizer_iff.1 this q hq
  have hZE : ∀ ζ ∈ (center ↥N.P).map N.P.subtype, ∀ ε ∈ E, ζ * ε = ε * ζ := by
    intro ζ hζ ε hε
    obtain ⟨ζ', _, rfl⟩ := hζ
    exact hEcentral ε hε ζ' ζ'.2
  have hdecomp : ∀ w ∈ centralizer (N.P : Set (MulAut K)), ∃ ζ ∈ N.P, (ζ = 1 ∨ ζ = z) ∧
      ∃ ε ∈ E, ζ * ε = ε * ζ ∧ w = ζ * ε := by
    intro w hw
    rw [hcent] at hw
    obtain ⟨ζ, hζ, ε, hε, rfl⟩ := Back.exists_mul_of_mem_sup_of_commute hZE hw
    have hcomm := hZE ζ hζ ε hε
    obtain ⟨ζ', hζ', rfl⟩ := hζ
    refine ⟨ζ', ζ'.2, hzu ζ' ζ'.2 (fun q hq => ?_), ε, hε, hcomm, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hζ' ⟨q, hq⟩).symm
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ2
    omega
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ2, sq] at this
  have hσE : σ ∈ E := by
    have hσc : σ ∈ centralizer (N.P : Set (MulAut K)) :=
      mem_centralizer_iff.2 fun q hq => (hPσ q hq).symm
    obtain ⟨ζ, hζP, hζ, ε, hε, -, hσeq⟩ := hdecomp σ hσc
    rcases hζ with h | h
    · rw [hσeq, h, one_mul]
      exact hε
    · exfalso
      have hzF : z ∈ fieldAutSub e' := by
        have h1 : z = σ * ε⁻¹ := by rw [← h, hσeq]; group
        rw [h1]
        exact (fieldAutSub e').mul_mem hσR.2 ((fieldAutSub e').inv_mem (hEF hε))
      have hzD : z ∈ innDiagSub e' := innAut_le_innDiagSub e' (hPinn hzP)
      have hz1' := eq_one_of_mem_fieldAutSub_of_mem_innDiagSub e' hzF hzD
      exact hz1 hz1'
  have hcentB : ∀ w ∈ B, (∀ q ∈ B ⊓ innAut K, w * q = q * w) → w ∈ zpowers α ⊔ zpowers z := by
    intro w hwB hwc
    have hwN : w ∈ centralizer (N.P : Set (MulAut K)) :=
      mem_centralizer_iff.2 fun q hq => (hwc q (hPeq ▸ hq)).symm
    obtain ⟨ζ, hζP, hζ, ε, hε, hζε, hw⟩ := hdecomp w hwN
    have hζB : ζ ∈ B := (hPeq ▸ hζP : ζ ∈ B ⊓ innAut K).1
    have hεB : ε ∈ B := by
      have : ε = ζ⁻¹ * w := by rw [hw]; group
      rw [this]
      exact B.mul_mem (B.inv_mem hζB) hwB
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hB2) ⟨ε, hεB⟩
    have hεo : orderOf ε = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
    have hdvd : orderOf ε ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E hε
    have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hmodd)
    have hεdvd2 : orderOf ε ∣ 2 := by
      rw [hεo] at hdvd ⊢
      rcases hEcard with h | h
      · rw [h] at hdvd
        have : 2 ^ j = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
        rw [this]
        exact one_dvd _
      · rw [h] at hdvd
        exact hcop.dvd_of_dvd_mul_right hdvd
    have hεε : ε * ε = 1 := by
      have := orderOf_dvd_iff_pow_eq_one.1 hεdvd2
      rwa [sq] at this
    have hε1σ : ε = 1 ∨ ε = σ := by
      by_cases hε1 : ε = 1
      · exact Or.inl hε1
      · right
        have := hEcyc
        have h := DihedralAux.cyclic_unique_involution (G := ↥E) (a := ⟨ε, hε⟩) (b := ⟨σ, hσE⟩)
          (fun h => hε1 (congrArg Subtype.val h)) (fun h => hσ1 (congrArg Subtype.val h))
          (Subtype.ext hεε) (Subtype.ext hσσ)
        exact congrArg Subtype.val h
    have hσmem : σ ∈ zpowers α ⊔ zpowers z := by
      rcases hσα' with h | h
      · rw [h]; exact Subgroup.mem_sup_left (mem_zpowers α)
      · rw [h]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers α))
          (Subgroup.mem_sup_right (mem_zpowers z))
    rw [hw]
    refine Subgroup.mul_mem _ ?_ ?_
    · rcases hζ with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_sup_right (mem_zpowers z)
    · rcases hε1σ with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact hσmem
  have hxσo : ∀ x ∈ N.P, x * x = 1 → orderOf (x * σ) = 2 := by
    intro x hx hxx
    have hxσ : x * σ = σ * x := N.R_cent σ hσR hσ2 x hx
    have h1 : (x * σ) * (x * σ) = 1 := by
      calc x * σ * (x * σ) = x * (σ * x) * σ := by group
        _ = x * (x * σ) * σ := by rw [← hxσ]
        _ = (x * x) * (σ * σ) := by group
        _ = 1 := by rw [hxx, hσσ, one_mul]
    have h2 : x * σ ≠ 1 := by
      intro h
      have hσx : σ = x⁻¹ := eq_inv_of_mul_eq_one_right h
      have hσD : σ ∈ innDiagSub e' := by
        rw [hσx]
        exact (innDiagSub e').inv_mem (innAut_le_innDiagSub e' (hPinn hx))
      exact hσ1 (eq_one_of_mem_fieldAutSub_of_mem_innDiagSub e' hσR.2 hσD)
    exact orderOf_eq_prime (by rw [sq]; exact h1) h2
  have hshear : ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut K →
      (∀ q ∈ B ⊓ innAut K, σ' * q = q * σ') →
      ∃ p ∈ B ⊓ innAut K, orderOf p = 2 ∧ ∃ g ∈ innAut K, g * σ' * g⁻¹ = σ' * p := by
    intro σ' hσ'B hσ'2 hσ'inn hσ'c
    obtain ⟨hE1, hE2⟩ := exists_shear_elements hF N hPeq hSyl hσR hσ2 hn3 hn
    obtain ⟨hb1, hb2⟩ := h2hb F hF K e' N σ hσR hσ2 z hzP hz2 (fun x hx => (hzc x hx).symm)
    rcases hcls σ' hσ'B hσ'2 hσ'inn hσ'c with h | h
    ·
      rw [h]
      obtain ⟨x, hxP, hxsq, hxnot⟩ := hE1
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hxnot ⟨1, (Subgroup.one_mem _), by simp⟩
      have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hxsq) hx1
      obtain ⟨g, hg, hgx⟩ := hb2 x hxP hxnot (hxσo x hxP hxsq)
      refine ⟨x, hPeq ▸ hxP, hxo, g⁻¹, (innAut K).inv_mem hg, ?_⟩
      have hxσ : x * σ = σ * x := N.R_cent σ hσR hσ2 x hxP
      calc g⁻¹ * σ * g⁻¹⁻¹ = g⁻¹ * σ * g := by group
        _ = g⁻¹ * (g * (x * σ) * g⁻¹) * g := by rw [hgx]
        _ = x * σ := by group
        _ = σ * x := hxσ
    ·
      rw [h]
      obtain ⟨V, hVP, hVI, hVc, hVsq⟩ := hE2
      obtain ⟨a, haV, b, hbV, ha1, hb1', hab⟩ := exists_two_ne_one_of_four hVc
      obtain ⟨x, hxV, hx1, hxz⟩ : ∃ x ∈ V, x ≠ 1 ∧ x ≠ z := by
        by_cases haz : a = z
        · refine ⟨b, hbV, hb1', fun hbz => hab (haz.trans hbz.symm)⟩
        · exact ⟨a, haV, ha1, haz⟩
      have hxP : x ∈ N.P := hVP hxV
      have hxsq := hVsq x hxV
      have hxI := hVI hxV
      obtain ⟨g, hg, hgx⟩ := hb1 x hxP hxI hx1 (hxσo x hxP hxsq)
      have hzx : z * x = x * z := hzc x hxP
      have hzxsq : (z * x) * (z * x) = 1 := by
        calc z * x * (z * x) = z * (x * z) * x := by group
          _ = z * (z * x) * x := by rw [← hzx]
          _ = (z * z) * (x * x) := by group
          _ = 1 := by rw [hzz, hxsq, one_mul]
      have hzx1 : z * x ≠ 1 := by
        intro h1
        exact hxz (by
          have : x = z⁻¹ := eq_inv_of_mul_eq_one_right h1
          rw [this, inv_eq_of_mul_eq_one_right hzz])
      have hzxo : orderOf (z * x) = 2 := orderOf_eq_prime (by rw [sq]; exact hzxsq) hzx1
      refine ⟨z * x, Subgroup.mul_mem _ (hPeq ▸ hzP) (hPeq ▸ hxP), hzxo, g⁻¹,
        (innAut K).inv_mem hg, ?_⟩
      have hxσ : x * σ = σ * x := N.R_cent σ hσR hσ2 x hxP
      calc g⁻¹ * (σ * z) * g⁻¹⁻¹ = g⁻¹ * (σ * z) * g := by group
        _ = g⁻¹ * (g * (x * σ) * g⁻¹) * g := by rw [hgx]
        _ = x * σ := by group
        _ = σ * x := hxσ
        _ = σ * z * (z * x) := by
          calc σ * x = σ * (z * z) * x := by rw [hzz, mul_one]
            _ = σ * z * (z * x) := by group
  refine ⟨z, ?_⟩
  refine
    { dihedral := ⟨n, hn3, by rw [← hPeq]; exact hn⟩
      z_mem := hzB
      z_order := hz2
      z_cent := fun q hq => hzc q (by rw [hPeq]; exact hq)
      z_unique := fun w hw hwc => hzu w (hPeq ▸ hw) (fun q hq => hwc q (by rw [← hPeq]; exact hq))
      abelian := fun a ha b hb => ⟨B.mul_mem (B.mul_mem (B.mul_mem ha hb) (B.inv_mem ha))
        (B.inv_mem hb), comm_mem_innAut e hF a b⟩
      invol_coset := fun u huB hu2 hunot u' hu'B hu'2 hu'not => by
        obtain ⟨hu, hu1⟩ := hPt u huB hu2 hunot
        obtain ⟨hu', hu1'⟩ := hPt u' hu'B hu'2 hu'not
        rw [← hPeq]
        exact hmul u u' hu hu1 hu' hu1'
      invol_dih := fun u huB hu2 hunot => by
        obtain ⟨hu, hu1⟩ := hPt u huB hu2 hunot
        have hE := hEq u hu hu1
        obtain ⟨n', -, k', hk'eq, hk'2, ⟨ψ⟩⟩ := (ivk_1_2d F hF K e' N).2.2.2
        have hcPt : Nat.card ↥N.Pt = 2 * 2 ^ n := by rw [card_Pt_eq hF N, hcard]
        have hk'0 : NeZero k' := ⟨by omega⟩
        have hk'n : k' = 2 ^ n := by
          have h1 : Nat.card ↥N.Pt = Nat.card (DihedralGroup k') := Nat.card_congr ψ.toEquiv
          rw [hcPt, DihedralGroup.nat_card] at h1
          omega
        refine ⟨n, by omega, ⟨?_⟩⟩
        have hsub : (B ⊓ innAut K) ⊔ zpowers u = N.Pt := by rw [← hPeq]; exact hE
        exact (MulEquiv.subgroupCongr hsub).trans (hk'n ▸ ψ)
      cent_B := ?_
      conj_z := fun p hp hp2 => by
        obtain ⟨g, hg, hgz⟩ := (ivk_1_2g F hF K e' N).1 z hzP p (hPeq ▸ hp) hz2 hp2
        exact ⟨g, hg, hgz⟩
      fus_alpha := fun v hv hv2 => ?_
      shear := hshear }
  · exact hcentB
  ·
    have hvP : v ∈ N.P := hPeq ▸ hv
    have hvv : v * v = 1 := by
      have := pow_orderOf_eq_one v
      rwa [hv2, sq] at this
    have hαv : α * v = v * α := hαc v hv
    have huB : α * v ∈ B := B.mul_mem hαB hv.1
    have huu : (α * v) * (α * v) = 1 := by
      calc α * v * (α * v) = α * (v * α) * v := by group
        _ = α * (α * v) * v := by rw [← hαv]
        _ = (α * α) * (v * v) := by group
        _ = 1 := by rw [hαα, hvv, one_mul]
    have hu1 : α * v ≠ 1 := by
      intro h
      apply hαinn
      have : α = v⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact (innAut K).inv_mem hv.2
    have huo : orderOf (α * v) = 2 := orderOf_eq_prime (by rw [sq]; exact huu) hu1
    have hu_sup : α * v ∈ (B ⊓ innAut K) ⊔ zpowers α :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers α)) (Subgroup.mem_sup_left hv)
    obtain ⟨g, hg, hgu⟩ := hfus α hαB hα2 hαinn hαc (α * v) hu_sup huo
    rcases hgu with h | h | h
    · exfalso
      apply hαinn
      have hu_eq : α * v = g⁻¹ * z * g := by rw [← h]; group
      have hui : α * v ∈ innAut K := by
        rw [hu_eq]
        have := (innAut_normal (K := K)).conj_mem z hzB.2 g⁻¹
        simpa using this
      have : α = (α * v) * v⁻¹ := by group
      rw [this]
      exact (innAut K).mul_mem hui ((innAut K).inv_mem hv.2)
    · exact ⟨g, hg, Or.inl h⟩
    · exact ⟨g, hg, Or.inr h⟩

end L2

end CFSG.GH74.GLS.C3.Layer1.P34Real
