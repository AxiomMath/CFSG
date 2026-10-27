module

public import CFSG.GH74.GLS.C3.Layer1.BkTh2A7
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.GH74.GLS.C3.Layer1.BkL114

public section

namespace CFSG.GH74.GLS

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS.Th2
open scoped commutatorElement

section Cfg

variable {G : Type} [Group G] [Finite G]

theorem Th2Std.exists_aconfigW (hc5 : B_thm2_cent5) (hG : C3Hyp G) {x y : G} {K T S : Subgroup G}
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hTS : T < S)
    (hQel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K)) (hterm : IsTerminalPair 2 x K) :
    ∃ a : G, IsAConfigW 7 x K T (T ⊓ CxK x K) S a := by
  obtain ⟨e7⟩ := h7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN := hs.K_normal_A7 hG ⟨e7⟩
  obtain ⟨a, haS, haN, haT, ha2⟩ := C3.Layer1.Bk.exists_a_of_lt hs.sylowS.isPGroup hTS
  obtain ⟨ψ, hker, -⟩ := C3.Layer1.Bk.lemma113d_alt hs.K_le_C hKN (n := 7) (by norm_num)
    (by norm_num) e7
  refine ⟨a, ?_⟩
  exact
    { twoTerminal := hs.v2ss.isV2Triple.2.1
      terminal := hterm
      kbar := ⟨e7⟩
      normalInC := hKN
      sylowT := hs.setup.sylowT
      hQ := rfl
      sylowQ := hs.sylow_Q
      card_Q := hQ4
      elemQ := hQel
      sylowS := hs.sylowS
      T_lt_S := hTS
      a_mem := ⟨haS, haN, haT, by rw [sq]; exact ha2⟩
      cond6 := fun hcen u hu hu1 => by
        have hu' : u ^ 2 = 1 :=
          CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := T ⊓ CxK x K) u hu
        exact hc5 G hG x y K T S hs u hu (fun t ht => hcen u hu t ht)
          (orderOf_eq_prime hu' hu1)
      quotientType := ⟨ψ, hker⟩
      fiveCase := fun h => absurd h (by norm_num) }

end Cfg

namespace IsAConfigW

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem noOddCore_of_leaves (hfus : C3.Layer1.Bk.B_L114_fusion57)
    (hfin : C3.Layer1.Bk.B_L114_final57) (hG : C3Hyp G) (h : IsAConfigW 7 x K T Q S a) :
    pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥ := by
  obtain ⟨-, hS, hA7⟩ := hfus G hG 7 (by simp) x K T Q S a h
  exact hfin G hG 7 (by simp) x K T Q S a h hS (h.a_mem_normalizer_W (hA7 rfl))

theorem CxK_eq_Q (h : IsAConfigW n x K T Q S a)
    (hO : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥) : CxK x K = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : pPrimeCoreOf 2 (centralizer ({x} : Set G)) = ⊥ := by
    unfold pPrimeCoreOf; rw [hO, Subgroup.map_bot]
  have hp : IsPGroup 2 ↥(CxK x K) := by
    rw [IsPGroup.iff_orderOf]
    intro g
    obtain ⟨k, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf (g : G))
      (orderOf_pos _).ne'
    refine ⟨k, ?_⟩
    have hgk : (g : G) ^ (2 ^ k) ∈ CxK x K := Subgroup.pow_mem _ g.2 _
    have hord : orderOf ((g : G) ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (by positivity) ⟨m, hgm⟩, hgm,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hodd : Odd (orderOf ((g : G) ^ (2 ^ k))) := by rw [hord]; exact hm
    have h1 : (g : G) ^ (2 ^ k) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
      h.odd_mem_W hgk hodd
    rw [hW, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hord
    rw [← Subgroup.orderOf_coe, hgm, ← hord, mul_one]
  exact h.sylowQ.eq_of_le h.Q_le_CxK le_rfl hp

theorem toAConfig7 (h : IsAConfigW 7 x K T Q S a)
    (hO : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥) : IsAConfig 7 x K T Q S a := by
  have hCxK := h.CxK_eq_Q hO
  obtain ⟨e⟩ := h.kbar
  obtain ⟨ψ, hker, hψK⟩ := C3.Layer1.Bk.lemma113d_alt h.K_le_C h.normalInC (n := 7)
    (by norm_num) (by norm_num) e
  have hker' : ψ.ker = Q.subgroupOf (centralizer ({x} : Set G)) := by
    rw [hker]
    show (CxK x K).subgroupOf _ = _
    rw [hCxK]
  have hAle : alternatingGroup (Fin 7) ≤ ψ.range := by
    intro g hg
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨g, hg⟩)
    refine ⟨⟨k.1, h.K_le_C k.2⟩, ?_⟩
    rw [hψK k.1 k.2]
    have : e (QuotientGroup.mk k) = ⟨g, hg⟩ := by rw [hk]; simp
    exact congrArg Subtype.val this
  have : Nontrivial (Fin 7) := ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, by simp⟩
  have hAidx : (alternatingGroup (Fin 7)).index = 2 := alternatingGroup.index_eq_two
  have hdvd : ψ.range.index ∣ 2 := hAidx ▸ Subgroup.index_dvd_of_le hAle
  have hcases : ψ.range = ⊤ ∨ ψ.range = alternatingGroup (Fin 7) := by
    have h2 : ψ.range.index = 1 ∨ ψ.range.index = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h <;> simp [h]
    rcases h2 with h | h
    · left; exact Subgroup.index_eq_one.1 h
    · right; exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two h
  exact
    { twoTerminal := h.twoTerminal
      terminal := h.terminal
      kbar := h.kbar
      normalInC := h.normalInC
      sylowT := h.sylowT
      hQ := h.hQ
      sylowQ := h.sylowQ
      card_Q := h.card_Q
      elemQ := h.elemQ
      sylowS := h.sylowS
      T_lt_S := h.T_lt_S
      a_mem := h.a_mem
      cond6 := h.cond6
      noOddCore := hO
      quotientType := ⟨ψ, hker', by
        rcases hcases with hc | hc
        · exact Or.inl hc
        · exact Or.inr ⟨by norm_num, hc⟩⟩
      fiveCase := h.fiveCase }

end IsAConfigW

section Cfg2

variable {G : Type} [Group G] [Finite G]

theorem Th2Std.exists_aconfig (hc5 : B_thm2_cent5) (hfus : C3.Layer1.Bk.B_L114_fusion57)
    (hfin : C3.Layer1.Bk.B_L114_final57) (hG : C3Hyp G) {x y : G} {K T S : Subgroup G}
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hTS : T < S)
    (hQel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K)) (hterm : IsTerminalPair 2 x K) :
    ∃ a : G, IsAConfig 7 x K T (T ⊓ CxK x K) S a := by
  obtain ⟨a, h⟩ := hs.exists_aconfigW hc5 hG h7 hQ4 hTS hQel hterm
  exact ⟨a, h.toAConfig7 (h.noOddCore_of_leaves hfus hfin hG)⟩

end Cfg2

end CFSG.GH74.GLS
