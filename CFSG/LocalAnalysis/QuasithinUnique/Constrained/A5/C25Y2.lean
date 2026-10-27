module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25One
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A4
public import Certificates.Data.A5
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem mem_centralizer_phi_of_fix4 {t : G} (c : S2.Ctx T M H S L t) {P₂ : A5Pi (cj t L)}
    (hE : P₂.im (baum S) = Estd) (hI : P₂.im (s2I S L) = Estd) {z : G} (hz : z ∈ cj t L)
    (hz4 : P₂.pf z 4 = 4) : z ∈ Subgroup.centralizer (s2Phi S L : Set G) := by
  have h := c.data
  refine Subgroup.mem_centralizer_iff.2 fun f hf => ?_
  obtain ⟨u, hu, d, hd, hfud, huC⟩ := c.phi_comp hI hf
  have hzN : z ∈ Subgroup.normalizer (cj t L : Set G) := Subgroup.le_normalizer hz
  have hzu : z * u = u * z := by
    refine (P₂.comm_iff hzN hu).2 ?_
    rcases c.bf_cases hE hu huC with hb | hb
    · rw [hb]
      exact vact_zero _
    · rw [hb]
      exact vact_zv hz4
  have hzd : z * d = d * z := Subgroup.mem_centralizer_iff.1 hd.2 z (h.L₂_le_L₀ hz)
  have hzf : z * f = f * z := by
    rw [hfud]
    calc z * (u * d) = (z * u) * d := by group
      _ = (u * z) * d := by rw [hzu]
      _ = u * (z * d) := by group
      _ = u * (d * z) := by rw [hzd]
      _ = (u * d) * z := by group
  exact hzf.symm

theorem exists_order_three_cent (hC54 : LemmaC54_3_s2) (h567 : Lemma245_C56_7)
    (cfg : A5Cfg2 G T M H S L) :
    ∃ y : G, y ∈ Subgroup.centralizer (s2Phi S L : Set G) ∧ orderOf y = 3 ∧
      ∀ l ∈ L, y * l = l * y := by
  obtain ⟨t, h⟩ := exists_data cfg
  have c := ctx_of hC54 h567 h
  obtain ⟨P₂, hE, hI⟩ := c.exists_P₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let c3 : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
  have hc3 : orderOf c3 = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      show (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ^ 3 = 1
      decide
    · intro h1
      have := congrArg Subtype.val h1
      revert this
      decide
  have hc34 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 5)) 4 = 4 := by
    decide
  have hker : ∀ z : ↥(cj t L), P₂.α z = 1 → ∃ k : ℕ, z ^ 2 ^ k = 1 := by
    intro z hz
    have hmem : z ∈ CFSG.pCore 2 ↥(cj t L) := P₂.hαk ▸ (MonoidHom.mem_ker.2 hz)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(cj t L))) ⟨z, hmem⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨z₀, hz₀⟩ := P₂.hα c3
  obtain ⟨y, hy3, hαy⟩ := exists_order_three_lift P₂.α hker hc3 hz₀
  have hy4 : P₂.pf (y : G) 4 = 4 := by
    rw [P₂.pf_eq (Subgroup.le_normalizer y.2), P₂.hπα (y : G) y.2]
    have : P₂.α ⟨(y : G), y.2⟩ = c3 := hαy
    rw [this]
    exact hc34
  refine ⟨(y : G), mem_centralizer_phi_of_fix4 c hE hI y.2 hy4,
    (Subgroup.orderOf_coe y).trans hy3, fun l hl => ?_⟩
  exact (h.comm_elem l hl (y : G) y.2).symm

end CFSG.QuasithinUnique.A5.C25
