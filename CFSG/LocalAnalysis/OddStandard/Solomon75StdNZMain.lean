module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdNZ
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStarSylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPairBound

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS AhatData

section Elements

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {n : ℕ} {z : G}

theorem StdSetup.sq_eq_one_of_mem_zpowers (S : StdSetup G L n z) {w : G}
    (hw : w ∈ Subgroup.zpowers z) : w * w = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hz2 : z ^ (2 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one z
    rw [S.hz] at h
    exact_mod_cast h
  rw [← zpow_add, ← two_mul, zpow_mul, hz2, one_zpow]

theorem StdSetup.pow_four_eq_one (S : StdSetup G L n z) {l κ : G} (hl : l ∈ L)
    (hκ : κ ∈ centralizer (L : Set G)) (h : (l * κ) * (l * κ) = 1) : κ ^ 4 = 1 := by
  have hc : l * κ = κ * l := Subgroup.mem_centralizer_iff.1 hκ l hl
  have h1 : κ * κ = (l * l)⁻¹ := by
    have : (l * l) * (κ * κ) = 1 := by
      calc (l * l) * (κ * κ) = l * (l * κ) * κ := by group
        _ = l * (κ * l) * κ := by rw [hc]
        _ = (l * κ) * (l * κ) := by group
        _ = 1 := h
    exact (eq_inv_of_mul_eq_one_right this)
  have hmemL : κ * κ ∈ L := by
    rw [h1]
    exact L.inv_mem (L.mul_mem hl hl)
  have hmemK : κ * κ ∈ centralizer (L : Set G) := (centralizer (L : Set G)).mul_mem hκ hκ
  have hmem : κ * κ ∈ Subgroup.zpowers z := by
    rw [← S.centralizer_inf_eq]
    exact ⟨hmemK, hmemL⟩
  have := S.sq_eq_one_of_mem_zpowers hmem
  calc κ ^ 4 = (κ * κ) * (κ * κ) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = 1 := this

end Elements

section Pair

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}
  (P : StdPair G L L' n z a)

include P in
theorem StdPair.exists_decomp : ∃ l ∈ L, ∃ κ ∈ centralizer (L : Set G), a = l * κ := by
  have hn := P.setup.hn
  let M := P.setup.model
  let M' := P.setup'.model
  have hσ2 := P.perm_a_sq M
  have hsign : sign (M.perm a P.a_mem_norm) = 1 :=
    sign_eq_one_of_even_transCount hσ2 (P.symm.even_transCount' M' M)
  obtain ⟨l, hl, hlσ⟩ := P.setup.exists_mem_perm_eq M hsign
  have hκN : l⁻¹ * a ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem (Subgroup.le_normalizer hl))
      P.a_mem_norm
  refine ⟨l, hl, l⁻¹ * a, ?_, by group⟩
  rw [← P.setup.perm_eq_one_iff M hκN]
  have e : (⟨l⁻¹ * a, hκN⟩ : ↥(normalizer (L : Set G))) =
      (⟨l, Subgroup.le_normalizer hl⟩ : ↥(normalizer (L : Set G)))⁻¹ * ⟨a, P.a_mem_norm⟩ := rfl
  have h1 := congrArg (M.permHom hn) e
  rw [map_mul, map_inv] at h1
  have h2 : M.permHom hn ⟨l, Subgroup.le_normalizer hl⟩ = M.perm a P.a_mem_norm := hlσ
  have h3 : M.permHom hn ⟨a, P.a_mem_norm⟩ = M.perm a P.a_mem_norm := rfl
  rw [h2, h3, inv_mul_cancel] at h1
  exact h1

theorem exists_sylow_mem_of_pow_four_eq_one {H : Type*} [Group H] [Finite H] {x : H}
    (hx : x ^ 4 = 1) : ∃ T : Sylow 2 H, x ∈ (T : Subgroup H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    have hdvd : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  exact ⟨T, hT (Subgroup.mem_zpowers x)⟩

include P in
theorem StdPair.mem_of_card_sylow
    (hK : ∀ T : Sylow 2 ↥(centralizer (L : Set G)),
      Nat.card (T : Subgroup ↥(centralizer (L : Set G))) = 2) : a ∈ L := by
  obtain ⟨l, hl, κ, hκ, hlκ⟩ := P.exists_decomp
  have ha2 : (l * κ) * (l * κ) = 1 := by rw [← hlκ]; exact P.a_mul_self
  have hκ4 := P.setup.pow_four_eq_one hl hκ ha2
  set κ' : ↥(centralizer (L : Set G)) := ⟨κ, hκ⟩ with hκ'
  have hκ'4 : κ' ^ 4 = 1 := Subtype.ext hκ4
  obtain ⟨T, hκT⟩ := exists_sylow_mem_of_pow_four_eq_one hκ'4
  have hord : orderOf κ' ∣ 2 := by
    have h1 : orderOf (⟨κ', hκT⟩ : ↥(T : Subgroup ↥(centralizer (L : Set G)))) ∣ Nat.card T :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hK T] at h1
    exact h1
  have hκ2 : κ * κ = 1 := by
    have := orderOf_dvd_iff_pow_eq_one.1 hord
    have h2 : κ' * κ' = 1 := by rw [← pow_two]; exact this
    exact congrArg Subtype.val h2
  by_cases hκ1 : κ = 1
  · rw [hlκ, hκ1, mul_one]
    exact hl
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hκord : orderOf κ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hκ2) hκ1
    have hκz : κ = z := P.setup.inv_unique κ hκ hκord
    rw [hlκ, hκz]
    exact L.mul_mem hl P.setup.z_mem

theorem StdPair.four_dvd_transCount (M : AhatModel G n L) (ha : a ∈ L) :
    4 ∣ transCount (M.perm a P.a_mem_norm) := by
  have hn := P.setup.hn
  have hσ2 := P.perm_a_sq M
  have hperm : M.perm a P.a_mem_norm = M.C.ρ (M.toK ⟨a, ha⟩) := M.perm_of_mem hn ha
  have hx2 : M.toK ⟨a, ha⟩ * M.toK ⟨a, ha⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a, ha⟩ : ↥L) * ⟨a, ha⟩ = 1 := Subtype.ext P.a_mul_self
    rw [this, map_one]
  have hρ2 : M.C.ρ (M.toK ⟨a, ha⟩) * M.C.ρ (M.toK ⟨a, ha⟩) = 1 := by
    rw [← hperm]
    exact hσ2
  have h8 := (M.C.sq_eq_one_iff_dvd hn hρ2).1 hx2
  rw [← hperm, card_support_eq_two_mul_transCount hσ2] at h8
  omega

end Pair

section C6

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {n : ℕ} {z : G}

theorem StdSetup.exists_order_four_commute (S : StdSetup G L n z)
    (T' : Sylow 2 ↥(centralizer (L : Set G))) (h4 : 4 ∣ Nat.card T') {κ : G}
    (hκ : κ ∈ centralizer (L : Set G))
    (hκT' : (⟨κ, hκ⟩ : ↥(centralizer (L : Set G))) ∈ (T' : Subgroup ↥(centralizer (L : Set G)))) :
    ∃ u ∈ centralizer (L : Set G), orderOf u = 4 ∧ u * κ = κ * u := by
  have : IsCyclic ↥(T' : Subgroup ↥(centralizer (L : Set G))) := S.isCyclic_sylow T'
  obtain ⟨gen, hgen⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := ↥(T' : Subgroup ↥(centralizer (L : Set G))))
  obtain ⟨c, hc⟩ := h4
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := ↥(T' : Subgroup ↥(centralizer (L : Set G))))
    omega
  let u : ↥(T' : Subgroup ↥(centralizer (L : Set G))) := gen ^ c
  have hu4 : orderOf u = 4 := by
    rw [orderOf_pow_of_dvd hc0 (by rw [hgen, hc]; exact Dvd.intro_left 4 rfl), hgen, hc]
    exact Nat.mul_div_cancel 4 (Nat.pos_of_ne_zero hc0)
  refine ⟨((u : ↥(centralizer (L : Set G))) : G), ?_, ?_, ?_⟩
  · exact (u : ↥(centralizer (L : Set G))).2
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu4]
  · have := (IsCyclic.isMulCommutative
      (α := ↥(T' : Subgroup ↥(centralizer (L : Set G))))).is_comm.comm u ⟨_, hκT'⟩
    exact congrArg (fun w : ↥(T' : Subgroup ↥(centralizer (L : Set G))) =>
      ((w : ↥(centralizer (L : Set G))) : G)) this

theorem StdSetup.card_sylow_eq_two (S : StdSetup G L n z)
    (T : Sylow 2 ↥(centralizer (L : Set G))) :
    Nat.card (T : Subgroup ↥(centralizer (L : Set G))) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hz' : (⟨z, S.z_cent⟩ : ↥(centralizer (L : Set G))) ∈ (T : Subgroup _) := by
    have hzord : orderOf (⟨z, S.z_cent⟩ : ↥(centralizer (L : Set G))) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact S.hz
    have hzcen : (⟨z, S.z_cent⟩ : ↥(centralizer (L : Set G))) ∈
        center ↥(centralizer (L : Set G)) := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h.2 z S.z_mem).symm
    exact CFSG.ComponentClassification.StandardRecognition.mem_sylow_of_mem_center_of_orderOf_eq_two
      hzcen hzord T
  have h4 : 4 ∣ Nat.card (T : Subgroup ↥(centralizer (L : Set G))) := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    have h2 : 2 ∣ Nat.card (T : Subgroup ↥(centralizer (L : Set G))) := by
      have h1 := orderOf_dvd_natCard (⟨_, hz'⟩ : ↥(T : Subgroup ↥(centralizer (L : Set G))))
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, S.hz] at h1
    rw [hk] at h2 hne ⊢
    rcases k with _ | _ | k
    · simp at h2
    · simp at hne
    · exact (pow_dvd_pow 2 (by omega : 2 ≤ k + 2))
  obtain ⟨g, hg1, hg2⟩ := S.exists_partner
  have P := StdPair.of_setup S g hg1 hg2
  let M' := (S.conj g).model
  obtain ⟨l, hl, κ, hκ, hlκ⟩ := P.exists_decomp
  have ha2 : (l * κ) * (l * κ) = 1 := by rw [← hlκ]; exact P.a_mul_self
  have hκ4 := S.pow_four_eq_one hl hκ ha2
  have hκ'4 : (⟨κ, hκ⟩ : ↥(centralizer (L : Set G))) ^ 4 = 1 := Subtype.ext hκ4
  obtain ⟨T', hκT'⟩ := exists_sylow_mem_of_pow_four_eq_one hκ'4
  have hcard : Nat.card (T' : Subgroup ↥(centralizer (L : Set G))) =
      Nat.card (T : Subgroup ↥(centralizer (L : Set G))) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  obtain ⟨u, huK, huord, hκu⟩ := S.exists_order_four_commute T' (hcard ▸ h4) hκ hκT'
  have hlu : u * l = l * u := (Subgroup.mem_centralizer_iff.1 huK l hl).symm
  have hua : u ∈ centralizer ({g⁻¹ * z * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hlκ]
    calc u * (l * κ) = (u * l) * κ := by group
      _ = l * (u * κ) := by rw [hlu]; group
      _ = l * (κ * u) := by rw [hκu]
      _ = (l * κ) * u := by group
  have h2 := P.symm.transCount_eq_two_of_orderOf_four M' huK hua huord
  rcases (P.arith S.model M').2.1 with h | h <;> omega

end C6

section C7

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {n : ℕ} {z : G}

theorem StdSetup.n_le_eleven (S : StdSetup G L n z) : n ≤ 11 := by
  by_contra h
  push Not at h
  obtain ⟨g, hg1, hg2⟩ := S.exists_partner
  have P := StdPair.of_setup S g hg1 hg2
  let M := S.model
  let M' := (S.conj g).model
  obtain ⟨-, -, -, h12⟩ := P.arith M M'
  rcases h12 (by omega) with h6 | h6
  · have h4 := P.four_dvd_transCount M (P.mem_of_card_sylow S.card_sylow_eq_two)
    omega
  · have h4 := P.symm.four_dvd_transCount M' (P.symm.mem_of_card_sylow (S.conj g).card_sylow_eq_two)
    omega

end C7

theorem solomon2AnStdCoreFull : Solomon2AnStdCoreFull := by
  intro G _ _ _ L n z S
  refine ⟨S.n_le_eleven, S.card_sylow_eq_two, ?_⟩
  intro M a ha haC hne hconj
  obtain ⟨g, rfl⟩ := hconj
  have hc : (g⁻¹ * z * g) * z = z * (g⁻¹ * z * g) := Subgroup.mem_centralizer_singleton_iff.1 haC
  have P := StdPair.of_setup S g hne hc
  let M' := (S.conj g).model
  have haL := P.mem_of_card_sylow S.card_sylow_eq_two
  refine ⟨haL, ?_⟩
  have h4 := P.four_dvd_transCount M haL
  rcases (P.arith M M').1 with h | h <;> omega

theorem solomon2AnStdCore : Solomon2AnStdCore := by
  intro G _ _ _ L n z S
  obtain ⟨h1, h2, h3⟩ := solomon2AnStdCoreFull G L n z S
  refine ⟨h1, h2, fun M a ha haC hne hconj => ?_⟩
  obtain ⟨haL, -⟩ := h3 M a ha haC hne hconj
  rw [show M.perm a ha = M.perm a (Subgroup.le_normalizer haL) from rfl, M.perm_of_mem S.hn haL]
  exact M.C.sign_ρ _

end CFSG.OddStandard.Solomon75
