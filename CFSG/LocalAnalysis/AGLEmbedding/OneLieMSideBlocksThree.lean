module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefs
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.ComponentCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneLieArith
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideBlocksThreeAux2
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barM_blockCentralizer_le (M L : Subgroup G) :
    barM M (blockCentralizer M L) ≤ Subgroup.centralizer (barM M L : Set _) := by
  rintro _ ⟨⟨c, hcM⟩, hc, rfl⟩
  exact (mem_blockCentralizer_iff ⟨c, hcM⟩).mp (Subgroup.mem_subgroupOf.mp hc)

variable {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G} {M H R Np Z : Subgroup G}

theorem D1OneLieMData.exists_of_inf_blockCentralizer (h : D1OneLieMData p n e P M H R Np Z)
    (hp3 : p = 3) (hn : 3 ≤ n) {L : Subgroup G} {t : G} (htK : t ∈ H ⊓ M) {j : ℕ}
    (htjL : t ^ j ∈ Subgroup.normalizer (L : Set G))
    {φ : Multiplicative (GaloisField p n) ≃* Z} {l₀ : (GaloisField p n)ˣ}
    (htj : ∀ a, t ^ j * (φ a : G) * (t ^ j)⁻¹ =
      φ (Multiplicative.ofAdd ((((l₀ : GaloisField p n) ^ e) ^ j) * Multiplicative.toAdd a)))
    (hW0 : Z ⊓ blockCentralizer M L ≠ ⊥) (hZC : ¬ Z ≤ blockCentralizer M L)
    (hord : orderOf l₀ = p ^ n - 1) (he : e = 1 ∨ e = 2) (hj0 : 0 < j)
    (hjμ : j ≤ (if e = 2 then n else 2 * n) + 1) :
    ∃ d : ℕ, 1 ≤ d ∧ 3 ^ d ≤ (Z ⊓ blockCentralizer M L).relIndex Z ∧
      Open.pRank 3 (H ⊓ M) < 5 * d / 2 + 1 := by
  subst hp3
  have hn0 : n ≠ 0 := by omega
  set W := Z ⊓ blockCentralizer M L with hW
  obtain ⟨W', hW'mem, hW'card⟩ := exists_addSubgroup_of_le φ (inf_le_left : W ≤ Z)
  set γ := ((l₀ : GaloisField 3 n) ^ e) ^ j with hγ
  have hγ0 : γ ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Units.ne_zero l₀))
  have hjM : t ^ j ∈ M := ((H ⊓ M).pow_mem htK j).2
  have htjZ : t ^ j ∈ Subgroup.normalizer (Z : Set G) := mem_normalizer_of_torus_conj φ hγ0 htj
  have htjW : W.map (MulAut.conj (t ^ j)).toMonoidHom ≤ W := by
    refine map_conj_inf_preimage_centralizer_le hjM htjZ ?_
    have hLj : L.map (MulAut.conj (t ^ j)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htjL
    have h1 := barM_map_conj hjM L
    rw [hLj] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1.symm
  have hW'γ : ∀ w ∈ W', γ * w ∈ W' := by
    intro w hw
    rw [hW'mem] at hw ⊢
    have h1 : (MulAut.conj (t ^ j)).toMonoidHom (φ (Multiplicative.ofAdd w) : G) ∈ W :=
      htjW (Subgroup.mem_map_of_mem _ hw)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    rwa [htj, toAdd_ofAdd] at h1
  have hW'bot : W' ≠ ⊥ := by
    intro hb
    apply hW0
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx.1⟩
    have hxa : (φ a : G) = x := congrArg Subtype.val ha
    have haW : Multiplicative.toAdd a ∈ W' := by rw [hW'mem, ofAdd_toAdd, hxa]; exact hx
    rw [hb, AddSubgroup.mem_bot] at haW
    have ha1 : a = 1 := Multiplicative.toAdd.injective (haW.trans toAdd_one.symm)
    rw [← hxa, ha1, map_one, Subgroup.coe_one]
  have hW'top : W' ≠ ⊤ := by
    intro htop
    apply hZC
    intro x hx
    obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hxa : (φ a : G) = x := congrArg Subtype.val ha
    have haW : Multiplicative.toAdd a ∈ W' := htop ▸ AddSubgroup.mem_top _
    rw [hW'mem, ofAdd_toAdd, hxa] at haW
    exact haW.2
  obtain ⟨f, hfn, hf0, hfl, hγf, hfcard⟩ :=
    exists_subfield_of_mul_mem hn0 hγ0 W' hW'γ hW'bot hW'top
  have hineq : 3 ^ n - 1 ≤ e * j * (3 ^ f - 1) := by
    have h1 : l₀ ^ (e * j * (3 ^ f - 1)) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, pow_mul]
      exact hγf
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    have h3 : 3 ≤ 3 ^ f := Nat.le_self_pow hf0.ne' 3
    exact Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos (by omega) hj0) (by omega)) h2
  obtain ⟨he2, hn4, hf2, -⟩ := stmtOneLieArithBi n e f j hn he hfn hfl hf0 hineq hjμ
  refine ⟨2, by norm_num, ?_, h.pRank_le.trans_lt (by simp [he2, hn4])⟩
  rw [hW'card] at hfcard
  have h1 := Subgroup.relIndex_mul_card W Z
  rw [inf_of_le_left (inf_le_left : W ≤ Z), h.card_eq] at h1
  rw [← h1, hf2] at hfcard
  exact Nat.le_of_mul_le_mul_right hfcard Nat.card_pos

theorem D1OneLieMData.barM_le_centralizer_of_three_le (h : D1OneLieMData p n e P M H R Np Z)
    (hLB : StmtLemmaBRelCyc) (hB3 : StmtBlockThree) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hp3 : p = 3)
    (hcyc : IsCyclic (CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M))) (hn : 3 ≤ n) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M Z ≤ Subgroup.centralizer (barM M L : Set _) := by
  classical
  subst hp3
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hn0 : n ≠ 0 := by omega
  have hKeq := h.ph3.inf_eq_inf_normalizer_twoCore
  have hZK : Z ≤ H ⊓ M := h.le_R.trans h.ph3.le_inf
  have hB3' : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockHasThree M (pCoreOf 2 H) L' := fun L' hL' => hB3 h.ph3 hL'
  have he : e = 1 ∨ e = 2 := by rcases h.e_cases with he | ⟨he, -⟩ <;> omega
  obtain ⟨r, hr, hrdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := 3) (n := n) le_rfl hn
  have hrp1 : ¬ r ∣ 3 - 1 := by simpa using hprim 1 one_pos (by omega)
  have hr2 : r ≠ 2 := by rintro rfl; exact hrp1 (by norm_num)
  have hr3 : r ≠ 3 := by
    rintro rfl
    have h4 : 3 ∣ 3 ^ n := dvd_pow_self 3 hn0
    have h5 : 3 ^ n = (3 ^ n - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))).symm
    rw [h5] at h4
    exact absurd (Nat.le_of_dvd one_pos ((Nat.dvd_add_right hrdvd).mp h4)) (by norm_num)
  have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
  obtain ⟨φ, htor⟩ := h.torus
  obtain ⟨l₀, hl₀⟩ := IsCyclic.exists_generator (α := (GaloisField 3 n)ˣ)
  have hord : orderOf l₀ = 3 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hl₀, Nat.card_units, GaloisField.card 3 n hn0]
  obtain ⟨t, htK, ht⟩ := htor l₀
  have hl0 : (l₀ : GaloisField 3 n) ^ e ≠ 0 := pow_ne_zero _ (Units.ne_zero l₀)
  have htZ : t ∈ Subgroup.normalizer (Z : Set G) := mem_normalizer_of_torus_conj φ hl0 ht
  have hex : ∃ i : ℕ, 0 < i ∧ t ^ i ∈ Subgroup.normalizer (L : Set G) :=
    ⟨orderOf t, orderOf_pos t, by rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _⟩
  obtain ⟨j, ⟨hj0, htjL⟩, hjmin⟩ : ∃ j : ℕ, (0 < j ∧ t ^ j ∈ Subgroup.normalizer (L : Set G)) ∧
      ∀ a : ℕ, 0 < a → a < j → t ^ a ∉ Subgroup.normalizer (L : Set G) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun a ha haj hta => Nat.find_min hex haj ⟨ha, hta⟩⟩
  have hjK : j ≤ Open.pRank 3 (H ⊓ M) :=
    h.ph3.le_pRank_three_of_injective_conj hB3' hL (fun i : Fin j => t ^ (i : ℕ))
      (fun i => (H ⊓ M).pow_mem htK _) (injective_map_conj_pow hjmin)
  have hjμ : j ≤ (if e = 2 then n else 2 * n) + 1 := hjK.trans h.pRank_le
  have htj := conj_pow_of_torus_conj φ ht j
  set u : (GaloisField 3 n)ˣ := l₀ ^ (e * j) with hu
  by_cases hA : r ∣ orderOf u
  ·
    set β : (GaloisField 3 n)ˣ := u ^ (orderOf u / r) with hβ
    have hβr : orderOf β = r := orderOf_pow_orderOf_div (orderOf_pos u).ne' hA
    have hβval : (β : GaloisField 3 n) = (((l₀ : GaloisField 3 n) ^ e) ^ j) ^ (orderOf u / r) := by
      simp only [hβ, hu, Units.val_pow_eq_pow_val, pow_mul]
    set t' := (t ^ j) ^ (orderOf u / r) with ht'
    have ht'a : ∀ a, t' * (φ a : G) * t'⁻¹ =
        φ (Multiplicative.ofAdd ((β : GaloisField 3 n) * Multiplicative.toAdd a)) := by
      intro a
      rw [ht', conj_pow_of_torus_conj φ htj (orderOf u / r) a, hβval]
    have hβ1 : (β : GaloisField 3 n) ≠ 1 := by
      intro h1
      rw [show β = 1 from Units.ext h1, orderOf_one] at hβr
      exact hr.one_lt.ne hβr
    have hβpow : (β : GaloisField 3 n) ^ r = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hβr, pow_orderOf_eq_one, Units.val_one]
    have ht'K : t' ∈ H ⊓ M := (H ⊓ M).pow_mem ((H ⊓ M).pow_mem htK j) _
    have ht'L : t' ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ htjL _
    have ht'Z : t' ∈ Subgroup.normalizer (Z : Set G) :=
      mem_normalizer_of_torus_conj φ (Units.ne_zero β) ht'a
    have ht'r : ∀ x ∈ Z, t' ^ r * x * (t' ^ r)⁻¹ = x := by
      intro x hx
      obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
      have hxa : (φ a : G) = x := congrArg Subtype.val ha
      rw [← hxa, conj_pow_of_torus_conj φ ht'a r, hβpow, one_mul, ofAdd_toAdd]
    have ht'nt : ∃ x ∈ Z, t' * x * t'⁻¹ ≠ x := by
      refine ⟨φ (Multiplicative.ofAdd 1), (φ _).2, fun h1 => ?_⟩
      rw [ht'a, toAdd_ofAdd, mul_one] at h1
      exact hβ1 (Multiplicative.ofAdd.injective (φ.injective (Subtype.ext h1)))
    obtain ⟨hnot1, -⟩ := h.ph3.nineThree_not_one h85 hD2 hL
    have hnS := h.ph3.not_isSylowTwoOf_inf h85 hD2 hL
    exact stmtLemmaBCyc_of_relCyc hLB G M (pCoreOf 2 H) L Z 3 r t' h.ph3.isKGroup.1
      h.ph3.asc81bHyp hL hnot1 hnS hp (by norm_num) h.cyc (hKeq ▸ hZK)
      (h.le_normalizer_block hB3 rfl hL) h.isElemAbelian
      (by rw [h.card_eq]; exact Nat.pow_le_pow_right (by norm_num) hn) (hKeq ▸ ht'K) ht'L ht'Z
      hr hr2 hr3 hr3 hrp1 ht'r ht'nt
      (fun Y hYZ hY => eq_bot_or_eq_of_torus_conj hn0 hr hprim φ hβpow hβ1 ht'a hYZ hY)
  ·
    have hrj : r ∣ j := by
      have h1 : l₀ ^ (e * j * orderOf u) = 1 := by
        rw [pow_mul]
        exact pow_orderOf_eq_one _
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at h2
      rcases (Nat.Prime.dvd_mul hr).mp (hrdvd.trans h2) with h4 | h4
      · rcases (Nat.Prime.dvd_mul hr).mp h4 with h5 | h5
        · exfalso
          have := Nat.le_of_dvd (by omega) h5
          omega
        · exact h5
      · exact absurd h4 hA
    have hmove5 : ∀ a : ℕ, 0 < a → a < 5 → t ^ a ∉ Subgroup.normalizer (L : Set G) :=
      fun a ha ha5 => hjmin a ha (by have := Nat.le_of_dvd hj0 hrj; omega)
    by_cases hZC : Z ≤ blockCentralizer M L
    · exact (barM_mono hZC).trans (barM_blockCentralizer_le M L)
    exfalso
    set W := Z ⊓ blockCentralizer M L with hW
    obtain ⟨d, hd1, hdidx, hdμ⟩ : ∃ d : ℕ, 1 ≤ d ∧ 3 ^ d ≤ W.relIndex Z ∧
        Open.pRank 3 (H ⊓ M) < 5 * d / 2 + 1 := by
      by_cases hW0 : W = ⊥
      · refine ⟨n, by omega, ?_, h.pRank_le.trans_lt (by split_ifs <;> omega)⟩
        rw [hW0, Subgroup.relIndex_bot_left, h.card_eq]
      ·
        exact h.exists_of_inf_blockCentralizer rfl hn htK htjL htj hW0 hZC hord he hj0 hjμ
    exact absurd (h.le_pRank_of_five h84 h86 hD2 hB3 rfl hcyc hL htK htZ hmove5 hd1 hdidx)
      (not_le.mpr hdμ)

theorem D1OneLieMData.barM_le_centralizer_of_eq_two (h : D1OneLieMData p n e P M H R Np Z)
    (hLB : StmtLemmaBRelCyc) (hB3 : StmtBlockThree) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hp3 : p = 3)
    (hYZ : pCorePreimage p M ⊓ Z = ⊥) (hcyc : IsCyclic (CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hn2 : n = 2) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M Z ≤ Subgroup.centralizer (barM M L : Set _) := by
  subst hp3 hn2
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hKeq := h.ph3.inf_eq_inf_normalizer_twoCore
  have hB3' : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockHasThree M (pCoreOf 2 H) L' := fun L' hL' => hB3 h.ph3 hL'
  have he : e = 1 := by rcases h.e_cases with he | ⟨-, he⟩ <;> omega
  have hrank : Open.pRank 3 (H ⊓ M) ≤ 5 := by
    have h1 := h.pRank_le
    split_ifs at h1 <;> omega
  obtain ⟨U, hZU, hUR, hUU, hZc, hUp, hUcard, hppd⟩ := h.pair rfl
  have hprim5 : ∀ k : ℕ, 0 < k → k < 4 → ¬ 5 ∣ 3 ^ k - 1 := by
    intro k hk hk4
    interval_cases k <;> norm_num
  obtain ⟨t, htK, htU, htr, htZ, htrU, htnt, hirr⟩ :=
    hppd 5 (by norm_num) (by norm_num) hprim5
  have hUK : U ≤ H ⊓ M := hUR.trans h.ph3.le_inf
  have hUpg : IsPGroup 3 U := h.ph3.isPGroup_R.to_le hUR
  have hrel : Z.relIndex U = 81 := by
    have h1 := Subgroup.relIndex_mul_card Z U
    rw [inf_of_le_left hZU, h.card_eq, hUcard] at h1
    have h6 : (3 : ℕ) ^ 6 = 81 * 3 ^ 2 := by norm_num
    rw [h6] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have htZc : ∀ z ∈ Z, Commute t z := fun z hz => mul_inv_eq_iff_eq_mul.mp (htZ z hz)
  have htZn : t ∈ Subgroup.normalizer (Z : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun z hz => (htZc z hz).symm)
  by_cases htL : t ∈ Subgroup.normalizer (L : Set G)
  ·
    have htNUL : t ∈ Subgroup.normalizer
        ((U ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨htU, Subgroup.le_normalizer htL⟩
    have hUL : U ≤ Subgroup.normalizer (L : Set G) := by
      rcases eq_or_le_of_mem_normalizer hUU hZc htZn hirr inf_le_left htNUL with heq | hle
      · exact heq ▸ inf_le_right
      · exfalso
        have hidx := h.ph3.relIndex_le_pRank_three hB3' hUK hL
        have hne : (U ⊓ Subgroup.normalizer (L : Set G)).relIndex U ≠ 0 := by
          rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
        have h1 := Subgroup.relIndex_le_of_le_left hle hne
        rw [hrel] at h1
        omega
    obtain ⟨hnot1, -⟩ := h.ph3.nineThree_not_one h85 hD2 hL
    have hnS := h.ph3.not_isSylowTwoOf_inf h85 hD2 hL
    have hUbar := hLB G M (pCoreOf 2 H) L U Z 3 5 t h.ph3.isKGroup.1 h.ph3.asc81bHyp hL hnot1
      hnS hp (by norm_num) h.cyc (hKeq ▸ hUK) hUL hUpg hUU hZc
      (fun u hu => by rw [hUp u hu]; exact Z.one_mem) (by rw [hrel]; norm_num)
      (hKeq ▸ htK) htL htU (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun u hu => by rw [htrU u hu, mul_inv_cancel]; exact Z.one_mem) htnt hirr
    exact (Subgroup.map_mono (Subgroup.subgroupOf_mono M hZU)).trans hUbar
  ·
    exfalso
    have hmove := pow_not_mem_normalizer (by norm_num : (5 : ℕ).Prime) htr htL
    have hZE : Z ≤ blockClosure M (H ⊓ M) L :=
      (h.le_blockClosure_or_le_normalizer hB3 rfl hL).resolve_right fun hK => htL (hK htK)
    set W := Z ⊓ blockCentralizer M L with hW
    have hWC : ∀ k ∈ H ⊓ M, barM M W ≤
        Subgroup.centralizer (barM M (L.map (MulAut.conj k).toMonoidHom) : Set _) := by
      intro k hk
      obtain ⟨i, -, hki⟩ := h.exists_eq_map_conj_pow hB3 hL htK hrank hmove hk
      rw [hki]
      refine (barM_mono fun w hw => ?_).trans (barM_blockCentralizer_le M _)
      have hti : t ^ i * w * (t ^ i)⁻¹ = w := by
        rw [((htZc w hw.1).pow_left i).eq, mul_inv_cancel_right]
      rw [← hti]
      exact conj_mem_blockCentralizer_map ((H ⊓ M).pow_mem htK i).2 hw.2
    have hWp : IsPGroup 3 W := (h.ph3.isPGroup_R.to_le h.le_R).to_le inf_le_left
    have hWO := barM_le_pCore_of_le_blockClosure inf_le_right hL.toIsTwoPrimeComponent
      (inf_le_left.trans hZE) hWp hWC
    have hWY : W ≤ pCorePreimage 3 M := by
      intro w hw
      have hwM : w ∈ M := blockCentralizer_le M L hw.2
      exact ⟨⟨w, hwM⟩, hWO (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw)), rfl⟩
    have hWb : W = ⊥ := by
      have h1 : W ≤ pCorePreimage 3 M ⊓ Z := le_inf hWY inf_le_left
      rw [hYZ] at h1
      exact le_bot_iff.mp h1
    have hidx : 3 ^ 2 ≤ W.relIndex Z := by
      rw [hWb, Subgroup.relIndex_bot_left, h.card_eq]
    have h1 := h.le_pRank_of_five h84 h86 hD2 hB3 rfl hcyc hL htK htZn hmove (by norm_num) hidx
    omega

theorem stmtOneLieBlocksThree : StmtOneLieBlocksThree := by
  intro G _ _ p _ n e P M H R Np Z hLB hB3 h84 h85 h86 hD2 h hp3 hYZ L hL
  have hcyc : IsCyclic (CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hp3 ▸ h.isCyclic_pCore h84 hD2 hYZ
  rcases Nat.lt_or_ge n 3 with hn | hn
  · exact h.barM_le_centralizer_of_eq_two hLB hB3 h84 h85 h86 hD2 hp3 hYZ hcyc
      (by have := h.two_le; omega) hL
  · exact h.barM_le_centralizer_of_three_le hLB hB3 h84 h85 h86 hD2 hp3 hcyc hn hL

end CFSG.AGLEmbedding
