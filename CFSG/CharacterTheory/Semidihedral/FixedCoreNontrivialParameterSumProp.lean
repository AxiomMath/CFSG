module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumTwo
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialOddComplement

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem odd_card_of_forall_odd {R : Subgroup G} (hR : ∀ x ∈ R, Odd (orderOf x)) :
    Odd (Nat.card R) := by
  by_contra h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h2))
  have := hR x x.2
  rw [Subgroup.orderOf_coe, hx] at this
  exact absurd this (by decide)

theorem exists_conj_mem_of_not_dvd_relIndex {R W : Subgroup G} (hWR : W ≤ R) {r : ℕ}
    [hr : Fact r.Prime] (hrR : ¬ r ∣ W.relIndex R) {x : G} (hxR : x ∈ R) (hx : orderOf x = r) :
    ∃ j ∈ R, j⁻¹ * x * j ∈ W := by
  classical
  let PW : Sylow r W := default
  let P : Subgroup G := (PW : Subgroup W).map W.subtype
  have hPW : P ≤ W := Subgroup.map_subtype_le _
  have hPR : P ≤ R := hPW.trans hWR
  have hPcard : Nat.card (P.subgroupOf R) = Nat.card PW := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hPp : IsPGroup r (P.subgroupOf R) := by
    obtain ⟨k, hk⟩ := PW.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (hPcard.trans hk)
  have hPidx : ¬ r ∣ (P.subgroupOf R).index := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf R)
    have h2 := Subgroup.card_mul_index (PW : Subgroup W)
    have h3 := Subgroup.card_mul_index (W.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWR).toEquiv] at h3
    rw [hPcard, ← h3, ← h2, mul_assoc] at h1
    have h4 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [h4]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hr.out).mp hdvd with h5 | h5
    · exact PW.not_dvd_index h5
    · exact hrR h5
  let T : Sylow r R := hPp.toSylow hPidx
  have hxp : IsPGroup r (Subgroup.zpowers (⟨x, hxR⟩ : R)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx, pow_one])
  obtain ⟨T', hT'⟩ := hxp.exists_le_sylow
  obtain ⟨j, hj⟩ := MulAction.exists_smul_eq R T T'
  have hmem : (⟨x, hxR⟩ : R) ∈ ((j • T : Sylow r R) : Subgroup R) := by
    rw [hj]
    exact hT' (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, hyT, hyx⟩ := hmem
  have hyP : (y : G) ∈ P := by
    have : y ∈ (T : Subgroup R) := hyT
    rw [IsPGroup.toSylow_coe] at this
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨j, j.2, ?_⟩
  have hyx' : (j : G) * y * (j : G)⁻¹ = x := by
    have := congrArg Subtype.val hyx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [← hyx']
  have : (j : G)⁻¹ * ((j : G) * y * (j : G)⁻¹) * j = y := by group
  rw [this]
  exact hPW hyP

end Generic

namespace CaseIData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {q : ℕ}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
  (h : CaseIData G t s₀ d d₁ J q F' φ)
include h

theorem false_of_mem_K_of_orderOf_eq_four {k : G} (hk : k ∈ torusK G t s₀) (hk4 : orderOf k = 4) :
    False := by
  classical
  have hL := h.localData
  obtain ⟨P, hP⟩ := h.sylow_K
  have hkp : IsPGroup 2 (Subgroup.zpowers (⟨k, hk⟩ : torusK G t s₀)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk4]; norm_num)
  obtain ⟨T', hT'⟩ := hkp.exists_le_sylow
  obtain ⟨j, hj⟩ := MulAction.exists_smul_eq (torusK G t s₀) P T'
  have hmem : (⟨k, hk⟩ : torusK G t s₀) ∈ ((j • P : Sylow 2 (torusK G t s₀)) :
      Subgroup (torusK G t s₀)) := by
    rw [hj]
    exact hT' (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, hyP, hyk⟩ := hmem
  have hyV : (y : G) ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ := by
    rw [← hP]
    exact ⟨y, hyP, rfl⟩
  have hy2 : (y : G) * y = 1 := by
    rcases hL.mem_V_cases hyV with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact one_mul 1
    · exact hL.t_sq
    · exact hL.s_sq
    · calc t * s₀ * (t * s₀) = t * (s₀ * t) * s₀ := by group
        _ = t * (t * s₀) * s₀ := by rw [hL.ts]
        _ = (t * t) * (s₀ * s₀) := by group
        _ = 1 := by rw [hL.t_sq, hL.s_sq, one_mul]
  have hk' : (j : G) * y * (j : G)⁻¹ = k := by
    have := congrArg Subtype.val hyk
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hk2 : k ^ 2 = 1 := by
    rw [← hk', pow_two]
    calc (j : G) * y * (j : G)⁻¹ * ((j : G) * y * (j : G)⁻¹) = (j : G) * ((y : G) * y) *
        (j : G)⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have := orderOf_dvd_of_pow_eq_one hk2
  rw [hk4] at this
  exact absurd this (by decide)

theorem inv_of_involution_mem_C {i : G} (hiC : i ∈ C t) (hi2 : orderOf i = 2) (hit : i ≠ t)
    {b : G} (hb : b ∈ (N t).map (C t).subtype) : i * b * i⁻¹ = b⁻¹ := by
  have hL := h.localData
  obtain ⟨c, hcC, hc⟩ := h.conj_s₀ i hiC hi2 hit
  have hi : i = c⁻¹ * s₀ * c := by rw [← hc]; group
  have hcb : c * b * c⁻¹ ∈ (N t).map (C t).subtype := hL.B_conj c hcC b hb
  have h1 := hL.s_inv _ hcb
  rw [hi]
  calc c⁻¹ * s₀ * c * b * (c⁻¹ * s₀ * c)⁻¹ = c⁻¹ * (s₀ * (c * b * c⁻¹) * s₀⁻¹) * c := by group
    _ = c⁻¹ * (c * b * c⁻¹)⁻¹ * c := by rw [h1]
    _ = b⁻¹ := by group

theorem normalizer_le_centralizer_v {g : G} (hg : g * t * g⁻¹ = s₀ * d) {b₀ : G}
    (hb₀ : b₀ ∈ (N t).map (C t).subtype) (hb₀1 : b₀ ≠ 1) {Q : Subgroup G}
    (hQv : Q ≤ Subgroup.centralizer {s₀ * d}) (hQ : g * b₀ * g⁻¹ ∈ Q) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.centralizer {s₀ * d} := by
  have hL := h.localData
  have hv2 := h.v_orderOf
  apply normalizer_le_centralizer_of_unique_involution _ _ hv2
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQv hx)
  · intro i hi hi2
    have hiu : i * (g * b₀ * g⁻¹) = g * b₀ * g⁻¹ * i :=
      (Subgroup.mem_centralizer_iff.mp hi _ hQ).symm
    have hib : g⁻¹ * i * g * b₀ = b₀ * (g⁻¹ * i * g) := by
      calc g⁻¹ * i * g * b₀ = g⁻¹ * (i * (g * b₀ * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * b₀ * g⁻¹ * i) * g := by rw [hiu]
        _ = b₀ * (g⁻¹ * i * g) := by group
    have hiC : g⁻¹ * i * g ∈ C t := h.confine b₀ hb₀ hb₀1
      (Subgroup.mem_centralizer_singleton_iff.mpr hib)
    have hi2' : orderOf (g⁻¹ * i * g) = 2 := by
      have : g⁻¹ * i * g = MulAut.conj g⁻¹ i := by simp
      rw [this, MulEquiv.orderOf_eq, hi2]
    by_cases hit : g⁻¹ * i * g = t
    · rw [← hg, ← hit]
      group
    · exfalso
      have hinv := h.inv_of_involution_mem_C hiC hi2' hit hb₀
      have h1 : b₀⁻¹ = b₀ := by
        rw [← hinv, hib]
        group
      have hodd : Odd (orderOf b₀) := hL.B_odd b₀ hb₀
      apply hb₀1
      apply eq_one_of_mul_self_eq_one_of_odd hodd
      calc b₀ * b₀ = b₀ * b₀⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel b₀

theorem card_torusU_eq_card_torusW_of_hall
    (hHall : Nat.card (torusU G t s₀ d) ≠ Nat.card (torusW G t s₀) → ∀ R : Subgroup G,
      R ≤ Subgroup.centralizer (torusU G t s₀ d : Set G) → Odd (Nat.card R) →
      torusW G t s₀ ≤ R →
      Nat.Coprime (Nat.card (torusW G t s₀)) ((torusW G t s₀).relIndex (R ⊓ torusH G t s₀))) :
    Nat.card (torusU G t s₀ d) = Nat.card (torusW G t s₀) := by
  classical
  by_contra hne
  have hL := h.localData
  obtain ⟨R, hR⟩ := h.exists_oddPart_centralizer_torusU hne
  have hRU : R ≤ Subgroup.centralizer (torusU G t s₀ d : Set G) := fun x hx => ((hR x).mp hx).1
  have hRodd : Odd (Nat.card R) := odd_card_of_forall_odd (fun x hx => ((hR x).mp hx).2)
  have hWU : torusW G t s₀ ≤ Subgroup.centralizer (torusU G t s₀ d : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Subgroup.mem_centralizer_iff.mp (h.U_le_K hu)) w hw).symm
  have hWR : torusW G t s₀ ≤ R := fun w hw => (hR w).mpr ⟨hWU hw, odd_orderOf_of_mem_W hw⟩
  obtain ⟨hcopR, M, hMR, hRM, hdisj, -, hcard⟩ :=
    odd_subgroup_torus_hall_normal_complement h.clauses R hRodd hWR (hHall hne R hRU hRodd hWR)
  have hvC : s₀ * d ∈ Subgroup.centralizer (torusU G t s₀ d : Set G) :=
    v_mem_centralizer_torusU
  have hvR : s₀ * d ∈ Subgroup.normalizer (R : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨hxC, hxodd⟩ := (hR x).mp hx
    apply (hR _).mpr
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hvC hxC) (Subgroup.inv_mem _ hvC), ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hxodd
  have hcardMR : Nat.card M * M.relIndex R = Nat.card R := by
    have h1 := Subgroup.card_mul_index (M.subgroupOf R)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMR).toEquiv] at h1
  have hidxM : M.relIndex R = Nat.card (torusW G t s₀) := by
    have hM0 : 0 < Nat.card M := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hM0
    rw [hcardMR, hcard]
  have hcardWR : Nat.card (torusW G t s₀) * (torusW G t s₀).relIndex R = Nat.card R := by
    have h1 := Subgroup.card_mul_index ((torusW G t s₀).subgroupOf R)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWR).toEquiv] at h1
  have hcardM : Nat.card M = (torusW G t s₀).relIndex R := by
    have hW0 : 0 < Nat.card (torusW G t s₀) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hW0
    rw [hcardWR, ← hcard, mul_comm]
  have hcopM : Nat.Coprime (Nat.card M) (M.relIndex R) := by
    rw [hidxM, hcardM]
    exact hcopR.symm
  have hvM := conj_mem_of_coprime_relIndex hMR hRM hcopM hvR
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.conj_t (s₀ * d) h.v_orderOf)
  have hg : c⁻¹ * t * c⁻¹⁻¹ = s₀ * d := by rw [← hc]; group
  have hUJ := h.torusU_le_map_conj hg
  have hBR : ∀ b ∈ (N t).map (C t).subtype, c⁻¹ * b * c⁻¹⁻¹ ∈ R := by
    intro b hb
    apply (hR _).mpr
    constructor
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨j, hj, hju⟩ := hUJ hu
      have hju' : c⁻¹ * j * c⁻¹⁻¹ = u := by simpa [MulAut.conj_apply] using hju
      rw [← hju']
      have hjb := hL.JB_comm j hj b hb
      calc c⁻¹ * j * c⁻¹⁻¹ * (c⁻¹ * b * c⁻¹⁻¹) = c⁻¹ * (j * b) * c⁻¹⁻¹ := by group
        _ = c⁻¹ * (b * j) * c⁻¹⁻¹ := by rw [hjb]
        _ = c⁻¹ * b * c⁻¹⁻¹ * (c⁻¹ * j * c⁻¹⁻¹) := by group
    · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hL.B_odd b hb
  have hcopBW : Nat.Coprime (Nat.card ((N t).map (C t).subtype)) (Nat.card (torusW G t s₀)) := by
    by_contra hcop
    obtain ⟨r, hr, hrB, hrW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := (N t).map (C t).subtype) r hrB
    have hrR : ¬ r ∣ (torusW G t s₀).relIndex R := by
      intro hrR
      have := Nat.eq_one_of_dvd_coprimes hcopR hrW hrR
      exact hr.one_lt.ne' this
    have hbord : orderOf (c⁻¹ * (b : G) * c⁻¹⁻¹) = r := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hb]
    obtain ⟨m, -, hmW⟩ := exists_conj_mem_of_not_dvd_relIndex hWR hrR (hBR b b.2) hbord
    have hw1 : m⁻¹ * (c⁻¹ * (b : G) * c⁻¹⁻¹) * m ≠ 1 := by
      intro h1
      have h2 : (b : G) = 1 := by
        have : (b : G) = c * m * (m⁻¹ * (c⁻¹ * (b : G) * c⁻¹⁻¹) * m) * m⁻¹ * c⁻¹ := by group
        rw [this, h1]
        group
      have h3 : orderOf (b : G) = 1 := by rw [h2, orderOf_one]
      rw [Subgroup.orderOf_coe, hb] at h3
      exact hr.one_lt.ne' h3
    have hCK := h.centralizer_eq _ hmW hw1
    have hd₁4 : orderOf d₁ = 4 := by
      have h1 : d₁ ^ 2 = t := by rw [pow_two]; exact hL.d_sq
      have h2 : d₁ ^ 2 ^ (1 + 1) = 1 := by
        rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h1, pow_two, hL.t_sq]
      have h3 : ¬ d₁ ^ 2 ^ 1 = 1 := by rw [pow_one, h1]; exact hL.t_ne_one
      exact orderOf_eq_prime_pow h3 h2
    have hk : m⁻¹ * (c⁻¹ * d₁ * c⁻¹⁻¹) * m ∈ torusK G t s₀ := by
      rw [← hCK, Subgroup.mem_centralizer_singleton_iff]
      have hdb := hL.JB_comm d₁ hL.d_mem b b.2
      calc m⁻¹ * (c⁻¹ * d₁ * c⁻¹⁻¹) * m * (m⁻¹ * (c⁻¹ * (b : G) * c⁻¹⁻¹) * m) =
          m⁻¹ * (c⁻¹ * (d₁ * b) * c⁻¹⁻¹) * m := by group
        _ = m⁻¹ * (c⁻¹ * (b * d₁) * c⁻¹⁻¹) * m := by rw [hdb]
        _ = m⁻¹ * (c⁻¹ * (b : G) * c⁻¹⁻¹) * m * (m⁻¹ * (c⁻¹ * d₁ * c⁻¹⁻¹) * m) := by group
    apply h.false_of_mem_K_of_orderOf_eq_four hk
    rw [show m⁻¹ * (c⁻¹ * d₁ * c⁻¹⁻¹) * m = MulAut.conj m⁻¹ (MulAut.conj c⁻¹ d₁) by simp,
      MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hd₁4]
  have hB1 : Nat.card ((N t).map (C t).subtype) ≠ 1 := by
    have := h.three_le_card_B; omega
  obtain ⟨r, hr, hrB⟩ := Nat.exists_prime_and_dvd hB1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' (G := (N t).map (C t).subtype) r hrB
  have hb₀1 : (b₀ : G) ≠ 1 := by
    intro h1
    have h3 : orderOf (b₀ : G) = 1 := by rw [h1, orderOf_one]
    rw [Subgroup.orderOf_coe, hb₀] at h3
    exact hr.one_lt.ne' h3
  have hrW : ¬ r ∣ Nat.card (torusW G t s₀) := by
    intro hrW
    exact hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcopBW hrB hrW)
  have hu₀R := hBR b₀ b₀.2
  have hu₀v : c⁻¹ * (b₀ : G) * c⁻¹⁻¹ ∈ Subgroup.centralizer {s₀ * d} := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have hbt : (b₀ : G) * t = t * b₀ := Subgroup.mem_centralizer_singleton_iff.mp (hL.B_le b₀.2)
    calc c⁻¹ * (b₀ : G) * c⁻¹⁻¹ * (c⁻¹ * t * c⁻¹⁻¹) = c⁻¹ * ((b₀ : G) * t) * c⁻¹⁻¹ := by group
      _ = c⁻¹ * (t * b₀) * c⁻¹⁻¹ := by rw [hbt]
      _ = c⁻¹ * t * c⁻¹⁻¹ * (c⁻¹ * (b₀ : G) * c⁻¹⁻¹) := by group
  have hu₀p : IsPGroup r (Subgroup.zpowers (⟨c⁻¹ * (b₀ : G) * c⁻¹⁻¹, hu₀R⟩ : R)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
        Subgroup.orderOf_coe, hb₀, pow_one])
  obtain ⟨P, hP⟩ := hu₀p.exists_le_sylow
  have hu₀P : c⁻¹ * (b₀ : G) * c⁻¹⁻¹ ∈ (P : Subgroup R).map R.subtype :=
    ⟨_, hP (Subgroup.mem_zpowers _), rfl⟩
  have hPGp : IsPGroup r ((P : Subgroup R).map R.subtype) := P.isPGroup'.map _
  have hPM : (P : Subgroup R).map R.subtype ≤ M := by
    refine le_of_coprime_relIndex hMR hRM (Subgroup.map_subtype_le _) ?_
    rw [hidxM]
    obtain ⟨k, hk⟩ := hPGp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrW)
  have hPv : (P : Subgroup R).map R.subtype ≤ Subgroup.centralizer {s₀ * d} := by
    by_contra hPv
    have hne' : (P : Subgroup R).map R.subtype ⊓ Subgroup.centralizer {s₀ * d} ≠
        (P : Subgroup R).map R.subtype := fun heq => hPv (heq ▸ inf_le_right)
    obtain ⟨y, hyP, hyN, hyQ⟩ := exists_mem_normalizer_not_mem_of_isPGroup hPGp inf_le_left hne'
    have hNQ := h.normalizer_le_centralizer_v hg b₀.2 hb₀1 inf_le_right ⟨hu₀P, hu₀v⟩
    exact hyQ ⟨hyP, hNQ hyN⟩
  have hNP := h.normalizer_le_centralizer_v hg b₀.2 hb₀1 hPv hu₀P
  apply h.W_ne_bot
  refine eq_bot_of_inv_of_mul_mem hvM hdisj
    (h.inv_of_not_mem_K _ h.v_mem_H h.v_not_mem_K) (fun w hw => odd_orderOf_of_mem_W hw) ?_
  intro w hw
  obtain ⟨n, m', hn, hm', hw'⟩ :=
    exists_mul_of_sylow_le hMR hRM P (fun x hx => hPM ⟨x, hx, rfl⟩) (hWR hw)
  exact ⟨n, m', Subgroup.mem_centralizer_singleton_iff.mp (hNP hn), hm', hw'⟩

end CaseIData

end CFSG.Semidihedral.FixedCoreNontrivial
