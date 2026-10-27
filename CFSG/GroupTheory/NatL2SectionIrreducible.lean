module

public import CFSG.Quasithin.Background.C1GNDefs
import CFSG.Quasithin.Background.G2SL2
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort

public section

namespace CFSG.Quasithin

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem charP_two_of_card_pow_nl2 {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (h : Fintype.card F = 2 ^ n) : CharP F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow h

private theorem eq_top_of_isPGroup_quotient_nl2 {X : Subgroup G} (hX : twoResidual X = X)
    {N : Subgroup X} [hN : N.Normal] (h2 : IsPGroup 2 (X ⧸ N)) : N = ⊤ := by
  set M : Subgroup G := N.map X.subtype with hM
  have hXM : X ≤ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx m hm
    obtain ⟨n, hn, rfl⟩ := hm
    let x' : X := ⟨x, hx⟩
    have hn' : x' * n * x'⁻¹ ∈ N := hN.conj_mem n hn x'
    simpa [M, x'] using Subgroup.mem_map_of_mem X.subtype hn'
  have h2mem : ∀ y ∈ X, ∃ k : ℕ, y ^ 2 ^ k ∈ M := by
    intro y hy
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp h2 (QuotientGroup.mk' N ⟨y, hy⟩)
    refine ⟨k, ?_⟩
    have hk' : ((⟨y, hy⟩ : X) ^ 2 ^ k : X) ∈ N := by
      have hk'' : QuotientGroup.mk' N ((⟨y, hy⟩ : X) ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact hk
      exact (QuotientGroup.eq_one_iff _).mp (by simpa using hk'')
    simpa [M] using Subgroup.mem_map_of_mem X.subtype hk'
  have hXM' : X ≤ M := by
    rw [← hX]
    exact twoResidual_le_of_isTwoQuotient (Subgroup.map_subtype_le N) hXM h2mem
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn, hnx⟩ := hXM' x.2
  have : n = x := Subtype.ext hnx
  simpa [this] using hn

private theorem commutatorElement_mul_left_of_mem_centralizer_nl2 {c u x : G}
    (hcx : c * x = x * c) : ⁅u * c, x⁆ = ⁅u, x⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hc : ⁅c, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcx
  rw [hc, mul_one]
  group

theorem IsNatL2Section.le_or_forall_exists_mul {K C W₁ W₀ U : Subgroup G} {n : ℕ}
    (h : IsNatL2Section K C W₁ W₀ n) (hUW₁ : U ≤ W₁) (hKU : K ≤ normalizer (U : Set G)) :
    U ≤ W₀ ∨ ∀ w ∈ W₁, ∃ u ∈ U, ∃ c ∈ W₀, u * c = w := by
  obtain ⟨F, _, _, hcard, α, _, hαrange, β, _, hβker, hβeq⟩ := h
  let M : Subgroup (Multiplicative (Fin 2 → F)) := (U.subgroupOf W₁).map β
  have hMinv : ∀ A ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) F),
      ∀ x ∈ M, SL2Model.natAct A x ∈ M := by
    intro A hA x hx
    obtain ⟨k, hk⟩ : ∃ k : K, α k = A := by
      have : A ∈ α.range := by rw [hαrange]; exact hA
      simpa using this
    subst A
    obtain ⟨u, hu, rfl⟩ := hx
    have hconj : (k : G) * (u : G) * (k : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hKU k.2) (u : G)).mp hu
    let v : W₁ := ⟨(k : G) * (u : G) * (k : G)⁻¹, hUW₁ hconj⟩
    have hβv : β v = SL2Model.natAct (α k) (β u) := by
      have hv := hβeq k u v rfl
      rw [SL2Model.natAct_apply, SL2Model.smul_eq_mulVec', ← hv]
      exact ofAdd_toAdd (β v)
    exact ⟨v, hconj, hβv⟩
  rcases @SL2Model.natAct_irreducible_comm F (inferInstance) (Finite.of_fintype F)
    (charP_two_of_card_pow_nl2 hcard) M hMinv with hM | hM
  · left
    intro u hu
    have huW : u ∈ W₁ := hUW₁ hu
    have hmem : β ⟨u, huW⟩ ∈ M := Subgroup.mem_map_of_mem β hu
    rw [hM] at hmem
    have h1 : β ⟨u, huW⟩ = 1 := Subgroup.mem_bot.mp hmem
    have hker : (⟨u, huW⟩ : W₁) ∈ W₀.subgroupOf W₁ := by
      rw [← hβker]
      exact MonoidHom.mem_ker.mpr h1
    exact hker
  · right
    intro w hw
    let w' : W₁ := ⟨w, hw⟩
    have hmem : β w' ∈ M := hM ▸ Subgroup.mem_top _
    obtain ⟨u, hu, hβu⟩ := hmem
    have hker : u⁻¹ * w' ∈ W₀.subgroupOf W₁ := by
      rw [← hβker]
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβu]
      exact inv_mul_cancel _
    exact ⟨(u : G), hu, ((u : G)⁻¹ * w), hker, by group⟩

theorem commutator_le_of_isNatL2Section [Finite G] {V W X C : Subgroup G} {n : ℕ}
    (hV : IsPGroup 2 V) (hX : twoResidual X = X) (hXV : X ≤ normalizer (V : Set G))
    (hWV : W ≤ V) (hXW : X ≤ normalizer (W : Set G))
    (hnat : IsNatL2Section X C ⁅V, X⁆ (⁅V, X⁆ ⊓ centralizer (X : Set G)) n)
    (hW : ¬ X ≤ centralizer (W : Set G)) : ⁅V, X⁆ ≤ W := by
  have hJ : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤ :=
    fun N _ hN => eq_top_of_isPGroup_quotient_nl2 hX hN
  have hUW : ⁅W, X⁆ ≤ W := (Subgroup.le_normalizer_iff_commutator_le_left).mp hXW
  have hXU : X ≤ Subgroup.normalizer ((⁅W, X⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right W X
  have hUD : ⁅W, X⁆ ≤ ⁅V, X⁆ := Subgroup.commutator_mono hWV le_rfl
  rcases hnat.le_or_forall_exists_mul hUD hXU with hU | hcover
  · exfalso
    apply hW
    have hsims : ⁅⁅W, X⁆, X⁆ = ⁅W, X⁆ :=
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
        hJ (hV.to_le hWV) hXW
    have hbot : ⁅⁅W, X⁆, X⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hU.trans inf_le_right
    rw [hsims] at hbot
    have : ⁅X, W⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
  · have hsims : ⁅⁅V, X⁆, X⁆ = ⁅V, X⁆ :=
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual hJ hV hXV
    rw [← hsims, Subgroup.commutator_le]
    intro d hd x hx
    obtain ⟨u, hu, c, hc, rfl⟩ := hcover d hd
    have hcx : c * x = x * c := (Subgroup.mem_centralizer_iff.mp hc.2 x hx).symm
    rw [commutatorElement_mul_left_of_mem_centralizer_nl2 hcx]
    exact hUW (Subgroup.commutator_mem_commutator (hUW hu) hx)

end CFSG.Quasithin
