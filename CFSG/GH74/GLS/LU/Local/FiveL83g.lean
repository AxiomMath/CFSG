module

public import CFSG.GH74.GLS.LU.Local.FiveL83d
public import CFSG.GH74.GLS.LU.Local.FiveCbarE
public import CFSG.GH74.GLS.LU.Local.FiveCbarF
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma92b

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section LemmaA

theorem pPrimeCoreOf_top_eq_bot {H : Type} [Group H] [Finite H] (h : pPrimeCore 2 H = ⊥) :
    pPrimeCoreOf 2 (⊤ : Subgroup H) = ⊥ := by
  have h1 := pPrimeCore_map_iso 2 (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)
  rw [h] at h1
  have h2 : pPrimeCore 2 ↥(⊤ : Subgroup H) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).1 h1
  unfold pPrimeCoreOf
  rw [h2, Subgroup.map_bot]

theorem eq_one_of_sq_of_odd_pow {H : Type} [Group H] {s : H} (hs : s * s = 1) {m : ℕ} (hm : Odd m)
    (h : s ^ m = 1) : s = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have : s ^ (2 * k + 1) = s := by rw [pow_succ, pow_mul, pow_two, hs, one_pow, one_mul]
  rw [← this]; exact h

theorem eq_one_of_pow_five_of_not_dvd {H : Type} [Group H] [Finite H] (h : ¬ 5 ∣ Nat.card H) {y : H}
    (hy : y ^ 5 = 1) : y = 1 := by
  have h1 : orderOf y ∣ 5 := orderOf_dvd_of_pow_eq_one hy
  rcases (Nat.dvd_prime Nat.prime_five).1 h1 with h2 | h2
  · exact orderOf_eq_one_iff.1 h2
  · exfalso; apply h; rw [← h2]; exact orderOf_dvd_natCard y

variable {G : Type} [Group G] [Finite G]

theorem c0Quot_abstract
    (C T : Subgroup G) (u : G) (hu2 : u * u = 1) (hnorm : ∀ c ∈ C, u * c * u⁻¹ ∈ C) (hunC : u ∉ C)
    (hTC : T ≤ C) (hT4 : Nat.card ↥T = 4) (hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hT2 : ∀ a ∈ T, a * a = 1) (hC2 : (Nat.card ↥C).factorization 2 = 2)
    (huT : ∀ a ∈ T, u * a = a * u)
    (hcent : ∀ y : G, y * y = 1 → y ≠ 1 → y ∈ C ⊔ zpowers u →
      Nat.card ↥(centralizer ({y} : Set G)) ∣ 28800) : C0Quot C T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup ↥C := pPrimeCore 2 ↥C with hW
  let π : ↥C →* ↥C ⧸ W := QuotientGroup.mk' W
  have hWodd : Odd (Nat.card ↥W) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥C))
  have hcardC : Nat.card ↥C = Nat.card (↥C ⧸ W) * Nat.card ↥W :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup W
  have hW2 : (Nat.card ↥W).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h =>
      (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h))
  have hfacC : ∀ q : ℕ, (Nat.card ↥C).factorization q =
      (Nat.card (↥C ⧸ W)).factorization q + (Nat.card ↥W).factorization q := by
    intro q
    rw [hcardC, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp
  have hH2 : (Nat.card (↥C ⧸ W)).factorization 2 = 2 := by
    have := hfacC 2
    omega
  set T' : Subgroup ↥C := T.subgroupOf C with hT'
  have hT'card : Nat.card ↥T' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv, hT4]
  have hπinj : ∀ s : ↥C, s ∈ T' → π s = 1 → s = 1 := by
    intro s hs hπ
    have hsW : s ∈ W := (QuotientGroup.eq_one_iff s).1 hπ
    have hs2 : s * s = 1 := Subtype.ext (hT2 s.1 hs)
    have hsW5 : s ^ Nat.card ↥W = 1 := pow_card_eq_one_of_mem (K := W) hsW
    exact eq_one_of_sq_of_odd_pow hs2 hWodd hsW5
  set S : Subgroup (↥C ⧸ W) := T'.map π with hS
  have hScard : Nat.card ↥S = 4 := by
    let e : ↥T' ≃ ↥S := Equiv.ofBijective (fun x => ⟨π x, ⟨x, x.2, rfl⟩⟩) ⟨?_, ?_⟩
    · rw [← Nat.card_congr e, hT'card]
    · intro x y hxy
      have h1 : π (x : ↥C) = π (y : ↥C) := congrArg Subtype.val hxy
      have h2 : π ((x : ↥C)⁻¹ * (y : ↥C)) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 := hπinj _ (T'.mul_mem (T'.inv_mem x.2) y.2) h2
      exact Subtype.ext (inv_mul_eq_one.mp h3)
    · rintro ⟨_, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hTcomm a.1 ha b.1 hb)
  let SS : Sylow 2 (↥C ⧸ W) := Sylow.ofCard S (by rw [hScard, hH2]; norm_num)
  have hSS : (SS : Subgroup (↥C ⧸ W)) = S := rfl
  have hO : pPrimeCore 2 (↥C ⧸ W) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥C) 2
  have hmain : (∀ x : ↥C, x ^ 5 = 1 → ∀ s : ↥C, s ∈ T' → s ≠ 1 → s * x = x * s → π x = 1) ∧
      (Nat.card (↥C ⧸ W)).factorization 5 ≤ 1 := by
    have h92 := CFSG.GH74.GLS.IVK.Proofs2.ivk_9_2b_four (↥C ⧸ W) (pPrimeCoreOf_top_eq_bot hO) SS
      (by rw [show (Nat.card ↥SS) = Nat.card ↥S from rfl, hScard]) (by rw [hSS]; exact hScomm)
    rcases h92 with hSTop | ⟨⟨e4⟩⟩ | ⟨L, hLn, hSL, F, _, _, hFodd, hF3, ⟨eL'⟩⟩
    ·
      have hcard : Nat.card (↥C ⧸ W) = 4 := by
        have h1 : Nat.card ↥(⊤ : Subgroup (↥C ⧸ W)) = 4 := by
          rw [← hSTop, hSS, hScard]
        rwa [Subgroup.card_top] at h1
      have h5 : ¬ 5 ∣ Nat.card (↥C ⧸ W) := by rw [hcard]; norm_num
      refine ⟨fun x hx _ _ _ _ => eq_one_of_pow_five_of_not_dvd h5 (by rw [← map_pow, hx, map_one]), ?_⟩
      rw [Nat.factorization_eq_zero_of_not_dvd h5]; norm_num
    ·
      have hcard : Nat.card (↥C ⧸ W) = 12 := by
        rw [Nat.card_congr e4.toEquiv, Nat.card_eq_fintype_card]
        decide
      have h5 : ¬ 5 ∣ Nat.card (↥C ⧸ W) := by rw [hcard]; norm_num
      refine ⟨fun x hx _ _ _ _ => eq_one_of_pow_five_of_not_dvd h5 (by rw [← map_pow, hx, map_one]), ?_⟩
      rw [Nat.factorization_eq_zero_of_not_dvd h5]; norm_num
    ·
      have eL : ↥L ≃* CFSG.GH74.GLS.IVK.L2 F := eL'.trans (CFSG.GH74.GLS.IVK.L2.equivPSL F).symm
      have hFL : CFSG.GH74.GLS.IVK.L2Field F := ⟨hFodd, hF3⟩
      have hSL' : (SS : Subgroup (↥C ⧸ W)) ≤ L := hSL
      have hL2 : (Nat.card ↥L).factorization 2 = 2 := by
        have h1 : 4 ∣ Nat.card ↥L := by
          have h0 := Subgroup.card_dvd_of_le hSL'
          have hSS4 : Nat.card ↥(SS : Subgroup (↥C ⧸ W)) = 4 := hScard
          rwa [hSS4] at h0
        have h2 : Nat.card ↥L ∣ Nat.card (↥C ⧸ W) := Subgroup.card_subgroup_dvd_card L
        have h3 : (Nat.card ↥L).factorization 2 ≤ (Nat.card (↥C ⧸ W)).factorization 2 :=
          (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 h2 2
        have h4 : (4 : ℕ).factorization 2 ≤ (Nat.card ↥L).factorization 2 :=
          (Nat.factorization_le_iff_dvd (by norm_num) Nat.card_pos.ne').2 h1 2
        have h44 : (4 : ℕ).factorization 2 = 2 := by
          have : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [this, Nat.Prime.factorization_pow Nat.prime_two]; simp
        omega
      let cu : ↥C ≃* ↥C :=
        { toFun := fun c => ⟨u * c * u⁻¹, hnorm c c.2⟩
          invFun := fun c => ⟨u * c * u⁻¹, hnorm c c.2⟩
          left_inv := fun c => by
            apply Subtype.ext
            show u * (u * (c : G) * u⁻¹) * u⁻¹ = c
            calc u * (u * (c : G) * u⁻¹) * u⁻¹ = (u * u) * c * (u⁻¹ * u⁻¹) := by group
              _ = c := by
                have : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
                rw [hu2, this]; group
          right_inv := fun c => by
            apply Subtype.ext
            show u * (u * (c : G) * u⁻¹) * u⁻¹ = c
            calc u * (u * (c : G) * u⁻¹) * u⁻¹ = (u * u) * c * (u⁻¹ * u⁻¹) := by group
              _ = c := by
                have : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
                rw [hu2, this]; group
          map_mul' := fun a b => by
            apply Subtype.ext
            show u * ((a : G) * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹)
            group }
      have hWcu : W.map cu.toMonoidHom = W := pPrimeCore_map_iso 2 cu
      let ψ : MulAut (↥C ⧸ W) := QuotientGroup.congr W W cu hWcu
      have hψ : ∀ c : ↥C, ψ (π c) = π (cu c) := fun c => QuotientGroup.congr_mk _ _ _ _ _
      have hψψ : ∀ x : ↥C ⧸ W, ψ (ψ x) = x := by
        intro x
        obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
        have hcc : cu (cu c) = c := by
          apply Subtype.ext
          show u * (u * (c : G) * u⁻¹) * u⁻¹ = c
          calc u * (u * (c : G) * u⁻¹) * u⁻¹ = (u * u) * c * (u⁻¹ * u⁻¹) := by group
            _ = c := by
              have : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
              rw [hu2, this]; group
        show ψ (ψ (π c)) = π c
        rw [hψ c, hψ (cu c), hcc]
      have hcuT : ∀ s : ↥C, s ∈ T' → cu s = s := by
        intro s hs
        apply Subtype.ext
        show u * (s : G) * u⁻¹ = s
        calc u * (s : G) * u⁻¹ = ((s : G) * u) * u⁻¹ := by rw [huT s.1 hs]
          _ = s := by group
      have hψS : ∀ s ∈ (SS : Subgroup (↥C ⧸ W)), ψ s = s := by
        intro s hs
        obtain ⟨c, hc, rfl⟩ := (show s ∈ S from hs)
        rw [hψ, hcuT c hc]
      obtain ⟨s₀, hs₀S, hs₀⟩ := klein_fixing_involution_inner (SS : Subgroup (↥C ⧸ W))
        (show Nat.card ↥SS = 4 from hScard) (by rw [hSS]; exact hScomm) L hSL' hFL eL hL2 ψ hψψ hψS
      obtain ⟨τ, hτT', hτ⟩ := (show s₀ ∈ S from hs₀S)
      have hτG : (τ : G) ∈ T := hτT'
      have hτ2 : (τ : G) * τ = 1 := hT2 _ hτG
      have hτu : (τ : G) * u = u * τ := (huT _ hτG).symm
      have hτi : (τ : G)⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
      have hs₀2 : s₀ * s₀ = 1 := by
        rw [← hτ, ← map_mul]
        have : τ * τ = 1 := Subtype.ext hτ2
        rw [this, map_one]
      obtain ⟨y, hy⟩ : ∃ y : G, y = (τ : G) * u := ⟨_, rfl⟩
      have hy2 : y * y = 1 := by
        calc y * y = (τ : G) * (u * τ) * u := by rw [hy]; group
          _ = (τ : G) * (τ * u) * u := by rw [hτu]
          _ = ((τ : G) * τ) * (u * u) := by group
          _ = 1 := by rw [hτ2, hu2, one_mul]
      have hyi : y⁻¹ = u * (τ : G) := by
        apply inv_eq_of_mul_eq_one_right
        calc y * (u * (τ : G)) = (τ : G) * (u * u) * τ := by rw [hy]; group
          _ = 1 := by rw [hu2, mul_one, hτ2]
      have hy1 : y ≠ 1 := by
        intro h
        rw [hy] at h
        apply hunC
        have : u = (τ : G)⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this]; exact C.inv_mem τ.2
      have hyCu : y ∈ C ⊔ zpowers u := by
        rw [hy]
        exact mul_mem (Subgroup.mem_sup_left τ.2) (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
      have hcentY := hcent y hy2 hy1 hyCu
      have hconj : ∀ c : ↥C, y * (c : G) * y⁻¹ = (τ : G) * (u * c * u⁻¹) * (τ : G)⁻¹ := by
        intro c
        rw [hyi, hy, hτi]
        have : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
        rw [this]; group
      have hyC : ∀ c : ↥C, y * (c : G) * y⁻¹ ∈ C := fun c => by
        rw [hconj c]
        exact C.mul_mem (C.mul_mem τ.2 (hnorm c c.2)) (C.inv_mem τ.2)
      have hπy : ∀ c : ↥C, π c ∈ L → π ⟨y * (c : G) * y⁻¹, hyC c⟩ = π c := by
        intro c hcL
        have h1 : (⟨y * (c : G) * y⁻¹, hyC c⟩ : ↥C) = τ * cu c * τ⁻¹ := by
          apply Subtype.ext
          show y * (c : G) * y⁻¹ = (τ : G) * (u * c * u⁻¹) * (τ : G)⁻¹
          exact hconj c
        rw [h1, map_mul, map_mul, map_inv, hτ, ← hψ, hs₀ _ hcL]
        have e2 : s₀ * (s₀ * π c * s₀⁻¹) * s₀⁻¹ = (s₀ * s₀) * π c * (s₀ * s₀)⁻¹ := by group
        rw [e2, hs₀2]; group
      set J : Subgroup G := (L.comap π).map C.subtype with hJ
      have hJC : J ≤ C := Subgroup.map_subtype_le _
      set A : Subgroup G := J ⊓ centralizer ({y} : Set G) with hA
      have hAC : A ≤ C := inf_le_left.trans hJC
      set X : Subgroup G := pPrimeCoreOf 2 C with hX
      have hXodd : Odd (Nat.card ↥X) := odd_card_pPrimeCoreOf C
      have hCcj : cjL u C = C := cjL_eq_of_mem_normalizer
        (CFSG.Walter.J1.mem_normalizer_of_conj_mem hnorm)
      have hXcj : cjL u X = X := by
        have := pPrimeCoreOf_cjL u C
        rw [hCcj] at this
        exact this.symm
      have hux : ∀ x ∈ X, u * x * u⁻¹ ∈ X := fun x hx => by
        have := mem_cjL_self (g := u) hx
        rwa [hXcj] at this
      have hτX : ∀ x ∈ X, (τ : G) * x * (τ : G)⁻¹ ∈ X := fun x hx =>
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf τ.2) x).mp hx
      have hzX : ∀ x ∈ X, y * x * y⁻¹ ∈ X := by
        intro x hx
        have h1 := hτX _ (hux x hx)
        have e : y * x * y⁻¹ = (τ : G) * (u * x * u⁻¹) * (τ : G)⁻¹ := by
          rw [hyi, hy, hτi]
          have : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
          rw [this]; group
        rw [e]; exact h1
      have hcosets : ∀ c : ↥C, π c ∈ L → ∃ c' : ↥C, (c' : G) ∈ A ∧ π c' = π c := by
        intro c hcL
        have hr : (y * (c : G) * y⁻¹)⁻¹ * c ∈ X := by
          have h1 : π ((⟨y * (c : G) * y⁻¹, hyC c⟩ : ↥C)⁻¹ * c) = 1 := by
            rw [map_mul, map_inv, hπy c hcL, inv_mul_cancel]
          have h2 : ((⟨y * (c : G) * y⁻¹, hyC c⟩ : ↥C)⁻¹ * c) ∈ W := (QuotientGroup.eq_one_iff _).1 h1
          exact Subgroup.mem_map.mpr ⟨_, h2, rfl⟩
        obtain ⟨x, hxX, hfix⟩ := exists_fixed_in_coset hy2 hzX hXodd hr
        have hxC : x ∈ C := pPrimeCoreOf_le' C hxX
        obtain ⟨w, hwW, hwx⟩ := Subgroup.mem_map.mp hxX
        have hwx' : w = ⟨x, hxC⟩ := Subtype.ext hwx
        have hπw : π w = 1 := (QuotientGroup.eq_one_iff w).2 hwW
        refine ⟨⟨(c : G) * x, C.mul_mem c.2 hxC⟩, ⟨⟨⟨(c : G) * x, C.mul_mem c.2 hxC⟩, ?_, rfl⟩, ?_⟩, ?_⟩
        · show π _ ∈ L
          have : π (⟨(c : G) * x, C.mul_mem c.2 hxC⟩ : ↥C) = π c := by
            have e : (⟨(c : G) * x, C.mul_mem c.2 hxC⟩ : ↥C) = c * ⟨x, hxC⟩ := rfl
            rw [e, map_mul, ← hwx', hπw, mul_one]
          rw [this]; exact hcL
        · apply Subgroup.mem_centralizer_singleton_iff.mpr
          calc (c : G) * x * y = (y * ((c : G) * x) * y⁻¹) * y := by rw [hfix]
            _ = y * ((c : G) * x) := by group
        · have e : (⟨(c : G) * x, C.mul_mem c.2 hxC⟩ : ↥C) = c * ⟨x, hxC⟩ := rfl
          rw [e, map_mul, ← hwx', hπw, mul_one]
      let f : ↥A →* ↥C ⧸ W := π.comp (Subgroup.inclusion hAC)
      have hfL : f.range = L := by
        apply le_antisymm
        · rintro _ ⟨a, rfl⟩
          obtain ⟨c, hc, hca⟩ := a.2.1
          have : Subgroup.inclusion hAC a = c := Subtype.ext hca.symm
          show π (Subgroup.inclusion hAC a) ∈ L
          rw [this]; exact hc
        · intro ℓ hℓ
          obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective ℓ
          obtain ⟨c', hc'A, hc'⟩ := hcosets c hℓ
          exact ⟨⟨c', hc'A⟩, hc'⟩
      have hLA : Nat.card ↥L ∣ Nat.card ↥A := by
        have := Subgroup.card_range_dvd f
        rwa [hfL] at this
      have hdiv : Nat.card ↥L ∣ 28800 :=
        hLA.trans ((Subgroup.card_dvd_of_le inf_le_right).trans hcentY)
      obtain ⟨e5⟩ := cbar_alternating_five hO hH2 (SS : Subgroup (↥C ⧸ W))
        (show Nat.card ↥SS = 4 from hScard) L hSL' hFL eL hdiv
      have hcard : Nat.card (↥C ⧸ W) = 60 := by
        rw [Nat.card_congr e5.toEquiv, Nat.card_eq_fintype_card]
        decide
      refine ⟨?_, ?_⟩
      · intro x hx5 s hsT hs1 hcomm
        have hs1' : π s ≠ 1 := fun h => hs1 (hπinj s hsT h)
        have hs2 : e5 (π s) * e5 (π s) = 1 := by
          rw [← map_mul, ← map_mul]
          have : s * s = 1 := Subtype.ext (hT2 s.1 hsT)
          rw [this, map_one, map_one]
        have hs1'' : e5 (π s) ≠ 1 := fun h => hs1' (e5.injective (by rw [h, map_one]))
        by_contra hx1
        have ha1 : e5 (π x) ≠ 1 := fun h => hx1 (e5.injective (by rw [h, map_one]))
        have ha5 : e5 (π x) ^ 5 = 1 := by rw [← map_pow, ← map_pow, hx5, map_one, map_one]
        have haa : e5 (π x) * e5 (π x) ≠ 1 := by
          intro h
          apply ha1
          calc e5 (π x) = e5 (π x) ^ 5 * ((e5 (π x) * e5 (π x))⁻¹) ^ 2 := by group
            _ = 1 := by rw [ha5, h]; simp
        have hc : e5 (π s) * e5 (π x) = e5 (π x) * e5 (π s) := by
          rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcomm]
        exact hs1'' (CFSG.GorensteinWalter.no_involution_centralizes_noninvolution_alternatingGroup_five
          _ _ ha1 haa hs2 hc)
      · rw [hcard]
        have : (60 : ℕ).factorization 5 = 1 := by
          have h60 : (60 : ℕ) = 5 ^ 1 * 12 := by norm_num
          rw [h60, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
            Nat.Prime.factorization_pow Nat.prime_five,
            Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 12)]
          simp
        rw [this]
  obtain ⟨hcore, hval⟩ := hmain
  have hmem : ∀ x : ↥C, π x = 1 → (x : G) ∈ pPrimeCoreOf 2 C := fun x hx =>
    Subgroup.mem_map.mpr ⟨x, (QuotientGroup.eq_one_iff x).1 hx, rfl⟩
  refine ⟨?_, ?_⟩
  · intro x hx hx5 s hsT hs1 hcomm
    refine hmem ⟨x, hx⟩ (hcore ⟨x, hx⟩ (Subtype.ext hx5) ⟨s, hTC hsT⟩ hsT ?_ (Subtype.ext hcomm))
    exact fun h => hs1 (congrArg Subtype.val h)
  · have hcardX : Nat.card ↥(pPrimeCoreOf 2 C) = Nat.card ↥W := by
      rw [pPrimeCoreOf, Subgroup.card_map_of_injective C.subtype_injective]
    rw [hcardX, hfacC 5]
    omega

end LemmaA

end CFSG.GH74.GLS.LU.Local.Five
