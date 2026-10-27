module

public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.GH74.GLS.C3.Layer1.BackAuxSA
public import CFSG.GH74.GLS.C3.Layer1.BackAuxCI
public import CFSG.GH74.GLS.C3.Layer1.BackStmt
public import CFSG.GH74.GLS.C3.Layer1.Split

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.U1a
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K L M T Q : Subgroup G}

theorem CxK_centralizes (hh : Hyp9A x K L M T Q) (hKL : K = L)
    (hO : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥) :
    ∀ n ∈ CxK x K, ∀ k ∈ K, n * k = k * n := by
  subst hKL
  have hCM := hh.centralizer_le
  have hKC : K ≤ centralizer ({x} : Set G) := hh.K_le_centralizer
  have hnormK : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K :=
    fun c hc k hk => hh.L_normal.2 c (hCM hc) k hk
  have hW : pPrimeCoreOf 2 K = ⊥ := pPrimeCoreOf_eq_bot hKC hnormK hO
  intro n hn k hk
  have hc := hn.2.2.2 k hk
  rw [hW, Subgroup.mem_bot] at hc
  rw [commutatorElement_def] at hc
  calc n * k = (k * n * k⁻¹ * n⁻¹) * (n * k) := by rw [hc, one_mul]
    _ = k * n := by group

theorem CxK_eq_Q (hh : Hyp9A x K L M T Q) (hKL : K = L)
    (hO : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥)
    (hQ4 : Nat.card ↥Q = 4) : CxK x K = Q := by
  have hNcomm := CxK_centralizes hh hKL hO
  subst hKL
  have hCM := hh.centralizer_le
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  have hKC : K ≤ C := hh.K_le_centralizer
  have hnormK : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk => hh.L_normal.2 c (hCM hc) k hk
  have hNC : CxK x K ≤ C := inf_le_left
  have hnormN : ∀ c ∈ C, ∀ n ∈ CxK x K, c * n * c⁻¹ ∈ CxK x K := by
    intro c hc n hn
    refine ⟨?_, mem_centralizerSection_of_centralizes (fun k hk => ?_) ?_⟩
    · have hn' : n ∈ C := hNC hn
      have h1 : n * x = x * n := mem_centralizer_singleton_iff.1 hn'
      have h2 : c * x = x * c := mem_centralizer_singleton_iff.1 hc
      exact mem_centralizer_singleton_iff.2 (by
        calc c * n * c⁻¹ * x = c * n * (c⁻¹ * x) := by group
          _ = c * n * (x * c⁻¹) := by
              have : c⁻¹ * x = x * c⁻¹ := by
                calc c⁻¹ * x = c⁻¹ * x * (c * c⁻¹) := by group
                  _ = c⁻¹ * (x * c) * c⁻¹ := by group
                  _ = c⁻¹ * (c * x) * c⁻¹ := by rw [h2]
                  _ = x * c⁻¹ := by group
              rw [this]
          _ = c * (n * x) * c⁻¹ := by group
          _ = c * (x * n) * c⁻¹ := by rw [h1]
          _ = x * (c * n * c⁻¹) := by
              calc c * (x * n) * c⁻¹ = (c * x) * n * c⁻¹ := by group
                _ = (x * c) * n * c⁻¹ := by rw [h2]
                _ = x * (c * n * c⁻¹) := by group)
    · have hck : c⁻¹ * k * c ∈ K := by
        have := hnormK c⁻¹ (C.inv_mem hc) k hk
        simpa using this
      have := hNcomm n hn _ hck
      calc c * n * c⁻¹ * k = c * (n * (c⁻¹ * k * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * k * c) * n) * c⁻¹ := by rw [this]
        _ = k * (c * n * c⁻¹) := by group
    · intro y hy
      obtain ⟨y', -, rfl⟩ := hy
      exact y'.2
  have hQsubN : Q ≤ CxK x K := by rw [hh.hQ]; exact inf_le_right
  have hQN : IsSylowOf 2 Q (CxK x K) := by
    have h1 : IsSylowOf 2 Q (CMK M K) := hh.sylowQ
    have hNle : CxK x K ≤ CMK M K := fun n hn => ⟨hCM (hNC hn), hn.2⟩
    exact h1.of_le hQsubN hNle
  have hxN : x ∈ CxK x K := hh.x_mem_CxK
  let x' : ↥(CxK x K) := ⟨x, hxN⟩
  have hx' : orderOf x' = 2 := by rw [Subgroup.orderOf_mk]; exact hh.orderOf_x
  have hxc : ∀ n : ↥(CxK x K), n * x' = x' * n := fun n =>
    Subtype.ext (mem_centralizer_singleton_iff.1 (hNC n.2))
  have hP : IsPGroup 2 (Q.subgroupOf (CxK x K)) := hQN.isPGroup.comap_subtype
  have hPidx : ¬ 2 ∣ (Q.subgroupOf (CxK x K)).index := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (isSylowOf_iff.1 hQN).2.2
  have hPcard : Nat.card ↥(Q.subgroupOf (CxK x K)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQsubN).toEquiv]; exact hQ4
  have hx'P : x' ∈ Q.subgroupOf (CxK x K) := hh.x_mem_Q
  have hW : pPrimeCoreOf 2 (CxK x K) = ⊥ := pPrimeCoreOf_eq_bot hNC hnormN hO
  have hW' : pPrimeCore 2 ↥(CxK x K) = ⊥ := by
    have := hW
    unfold pPrimeCoreOf at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ (CxK x K).subtype_injective).1 this
  have hOgp : ∀ W : Subgroup ↥(CxK x K), W.Normal → Odd (Nat.card ↥W) → W = ⊥ := by
    intro W hWn hWodd
    have hle : W ≤ pPrimeCore 2 ↥(CxK x K) :=
      le_sSup ⟨hWn, Nat.coprime_two_left.2 hWodd⟩
    rw [hW'] at hle
    exact le_bot_iff.1 hle
  have htop := eq_top_of_central_involution_sylow_four hx' hxc hP hPidx hPcard hx'P hOgp
  refine le_antisymm (fun n hn => ?_) hQsubN
  have : (⟨n, hn⟩ : ↥(CxK x K)) ∈ Q.subgroupOf (CxK x K) := by rw [htop]; exact trivial
  exact this

theorem quotientType_of (hh : Hyp9A x K L M T Q) (hKL : K = L)
    (hO : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥) (hQ4 : Nat.card ↥Q = 4)
    (hQab : CFSG.IsElementaryAbelian 2 ↥Q) {n : ℕ} (hn : 5 ≤ n)
    (e0 : kBar K ≃* alternatingGroup (Fin n))
    (hψ : ∃ ψ₀ : ↥M →* Equiv.Perm (Fin n), ψ₀.ker = (CMK M K).subgroupOf M)
    (hfive : n = 5 → ∃ y ∈ T, orderOf y = 2 ∧ T = (T ⊓ K) ⊔ Q ⊔ zpowers y ∧
      ∃ q ∈ Q, y * q ≠ q * y) :
    ∃ ψ : ↥(centralizer ({x} : Set G)) →* Equiv.Perm (Fin n),
      ψ.ker = Q.subgroupOf (centralizer ({x} : Set G)) ∧
      (ψ.range = ⊤ ∨ (n ≠ 5 ∧ ψ.range = alternatingGroup (Fin n))) := by
  have hNcomm := CxK_centralizes hh hKL hO
  have hNQ : CxK x K = Q := CxK_eq_Q hh hKL hO hQ4
  subst hKL
  obtain ⟨ψ₀, hker⟩ := hψ
  have hCM := hh.centralizer_le
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  have hKC : K ≤ C := hh.K_le_centralizer
  have hKM : K ≤ M := hKC.trans hCM
  have hnormK : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk => hh.L_normal.2 c (hCM hc) k hk
  have hW : pPrimeCoreOf 2 K = ⊥ := pPrimeCoreOf_eq_bot hKC hnormK hO
  have hW' : pPrimeCore 2 ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 hW
  let ψ : ↥C →* Equiv.Perm (Fin n) := ψ₀.comp (Subgroup.inclusion hCM)
  have hker_iff : ∀ c : ↥C, ψ c = 1 ↔ (c : G) ∈ Q := by
    intro c
    have h1 : ψ c = 1 ↔ (Subgroup.inclusion hCM c) ∈ ψ₀.ker := by rw [MonoidHom.mem_ker]; rfl
    rw [h1, hker, Subgroup.mem_subgroupOf]
    show (c : G) ∈ CMK M K ↔ (c : G) ∈ Q
    rw [← hNQ]
    constructor
    · intro hc; exact ⟨c.2, hc.2⟩
    · intro hc; exact ⟨hCM c.2, hc.2⟩
  refine ⟨ψ, ?_, ?_⟩
  · ext c; rw [MonoidHom.mem_ker, hker_iff, Subgroup.mem_subgroupOf]
  · have e0' : ↥K ≃* alternatingGroup (Fin n) :=
      (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hW'.symm)).trans e0
    have hcard4 : 4 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    have hZ : ∀ k : ↥K, (∀ k' : ↥K, k' * k = k * k') → k = 1 := by
      intro k hk
      have hc : e0' k ∈ Subgroup.center (alternatingGroup (Fin n)) := by
        rw [Subgroup.mem_center_iff]
        intro a
        have := congrArg e0' (hk (e0'.symm a))
        simpa using this
      rw [alternatingGroup.center_eq_bot hcard4] at hc
      exact e0'.injective (by simpa using Subgroup.mem_bot.1 hc)
    let ψK : ↥K →* Equiv.Perm (Fin n) := ψ₀.comp (Subgroup.inclusion hKM)
    have hψK_inj : Function.Injective ψK := by
      rw [injective_iff_map_eq_one]
      intro k hk
      have hk' : (Subgroup.inclusion hKM k) ∈ ψ₀.ker := hk
      rw [hker, Subgroup.mem_subgroupOf] at hk'
      have hkC : (k : G) ∈ CMK M K := hk'
      apply hZ k
      intro k'
      have := hkC.2.2.2 k' k'.2
      rw [hW, Subgroup.mem_bot, commutatorElement_def] at this
      apply Subtype.ext
      show (k' : G) * k = k * k'
      calc (k' : G) * k = ((k' : G) * (k : G) * (k' : G)⁻¹ * (k : G)⁻¹) * ((k : G) * (k' : G)) := by
            group
        _ = 1 * ((k : G) * (k' : G)) := by rw [this]
        _ = (k : G) * (k' : G) := one_mul _
    have hcardR : Nat.card ↥ψK.range = Nat.card ↥(alternatingGroup (Fin n)) := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hψK_inj).toEquiv]
      exact Nat.card_congr e0'.toEquiv
    have : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    have hAidx : (alternatingGroup (Fin n)).index = 2 := alternatingGroup.index_eq_two
    have hRidx : ψK.range.index = 2 := by
      have h1 := Subgroup.card_mul_index ψK.range
      have h2 := Subgroup.card_mul_index (alternatingGroup (Fin n))
      rw [hcardR] at h1
      rw [hAidx] at h2
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
    have hRA : ψK.range = alternatingGroup (Fin n) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hRidx
    have hKrange : ψK.range ≤ ψ.range := by
      rintro _ ⟨k, rfl⟩
      exact ⟨⟨k, hKC k.2⟩, rfl⟩
    have hAle : alternatingGroup (Fin n) ≤ ψ.range := hRA ▸ hKrange
    have hdvd : ψ.range.index ∣ 2 := hAidx ▸ Subgroup.index_dvd_of_le hAle
    have hcases : ψ.range = ⊤ ∨ ψ.range = alternatingGroup (Fin n) := by
      have h2 : ψ.range.index = 1 ∨ ψ.range.index = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h <;> simp [h]
      rcases h2 with h | h
      · left; exact Subgroup.index_eq_one.1 h
      · right; exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two h
    by_cases hn5 : n = 5
    · left
      rcases hcases with hc | hc
      · exact hc
      · exfalso
        obtain ⟨y, hyT, -, -, q0, hq0, hyq0⟩ := hfive hn5
        have hyC : y ∈ C := hh.sylowT.le hyT
        have hyr : ψ ⟨y, hyC⟩ ∈ ψ.range := ⟨_, rfl⟩
        rw [hc, ← hRA] at hyr
        obtain ⟨k, hk⟩ := hyr
        have hq' : (y * (k : G)⁻¹) ∈ Q := by
          have h1 : ψ (⟨y, hyC⟩ * (⟨k, hKC k.2⟩ : ↥C)⁻¹) = 1 := by
            rw [map_mul, map_inv]
            have : ψ ⟨k, hKC k.2⟩ = ψK k := rfl
            rw [this, hk]; simp
          have := (hker_iff _).1 h1
          simpa using this
        have hy_eq : y = (y * (k : G)⁻¹) * k := by group
        have hqk : q0 * k = k * q0 := by
          have := hNcomm q0 (hNQ ▸ hq0) k k.2
          exact this
        have hcommQ : (y * (k : G)⁻¹) * q0 = q0 * (y * (k : G)⁻¹) := by
          have : IsMulCommutative ↥Q := hQab.toIsMulCommutative
          have hc := mul_comm' (⟨y * (k : G)⁻¹, hq'⟩ : ↥Q) ⟨q0, hq0⟩
          exact congrArg Subtype.val hc
        apply hyq0
        calc y * q0 = ((y * (k : G)⁻¹) * k) * q0 := by rw [← hy_eq]
          _ = (y * (k : G)⁻¹) * (k * q0) := by group
          _ = (y * (k : G)⁻¹) * (q0 * k) := by rw [hqk]
          _ = ((y * (k : G)⁻¹) * q0) * k := by group
          _ = (q0 * (y * (k : G)⁻¹)) * k := by rw [hcommQ]
          _ = q0 * ((y * (k : G)⁻¹) * k) := by group
          _ = q0 * y := by rw [← hy_eq]
    · rcases hcases with hc | hc
      · left; exact hc
      · right; exact ⟨hn5, hc⟩


theorem aconfig_of_concl {x : G} {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q)
    (p91 : Prop91Concl K M T Q) (l113 : Lemma113Concl x K L M T Q)
    (hO : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥) :
    ∃ n ∈ ({5, 6, 7} : Finset ℕ), AConfig G n := by
  obtain ⟨⟨hQab, hQ4⟩, -, -, -⟩ := p91
  obtain ⟨hnot, hKL, hterm, n, hn, ⟨e0⟩, hψ, hfive⟩ := l113
  refine ⟨n, hn, ?_⟩
  have hn5 : 5 ≤ n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  obtain ⟨ψ, hψker, hψrange⟩ := quotientType_of hh hKL hO hQ4 hQab hn5 e0 hψ hfive
  subst hKL
  obtain ⟨S, hSsyl, hTS, a, haS, haN, haT, ha2⟩ :=
    exists_sylow_gt_and_a hh.sylowT.isPGroup hnot
  have hCM := hh.centralizer_le
  have hQsubN : Q ≤ CxK x K := by rw [hh.hQ]; exact inf_le_right
  have hNle : CxK x K ≤ CMK M K := fun n hn => ⟨hCM hn.1, hn.2⟩
  have : CFSG.IsElementaryAbelian 2 ↥Q := hQab
  refine ⟨x, K, T, Q, S, a, ?_⟩
  exact
    { twoTerminal := hh.twoTerminal
      terminal := hterm
      kbar := ⟨e0⟩
      normalInC := fun c hc k hk => hh.L_normal.2 c (hCM hc) k hk
      sylowT := hh.sylowT
      hQ := hh.hQ
      sylowQ := hh.sylowQ.of_le hQsubN hNle
      card_Q := hQ4
      elemQ := hQab
      sylowS := hSsyl
      T_lt_S := hTS
      a_mem := ⟨haS, haN, haT, ha2⟩
      cond6 := fun hcen u hu hu1 => by
        have hu' : u ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Q) u hu
        exact hh.cent5 u hu (fun t ht => hcen u hu t ht) (orderOf_eq_prime hu' hu1)
      noOddCore := hO
      quotientType := ⟨ψ, hψker, hψrange⟩
      fiveCase := hfive }

end CFSG.GH74.GLS.C3.Layer1.Back

namespace CFSG.GH74.GLS

theorem s_back_of (h91 : S_prop91) (h113 : S_lemma113) (h114 : S_lemma114) : S_back := by
  intro G _ _ hG x K L M T Q h
  have p91 := h91 G hG x K L M T Q h
  have l113 := h113 G hG x K L M T Q h p91
  have l114 := h114 G hG x K L M T Q h p91 l113
  exact C3.Layer1.Back.aconfig_of_concl h.a p91 l113 l114

end CFSG.GH74.GLS
