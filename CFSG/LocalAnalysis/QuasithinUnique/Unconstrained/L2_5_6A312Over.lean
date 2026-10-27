module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinBender

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A312Sub

open scoped Pointwise
open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.QuasithinUnique.Vol2Native.A312L

@[expose] def Over (X : Type) [Group X] [Finite X] (P : Subgroup X → Prop) : Prop :=
  ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ → P B

section Transport

variable {X : Type} [Group X] [Finite X]

theorem Over.of_sylow {P : Subgroup X → Prop}
    (hinv : ∀ (e : X ≃* X) (B : Subgroup X), P (B.map e.toMonoidHom) → P B)
    (T₀ : Subgroup X) (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ∀ B ∈ lFamily T₀, B ≠ ⊤ → P B) : Over X P := by
  intro T hT B hB hBtop
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hT₀ hT
  let e : X ≃* X := (MulAut.conj g).symm
  have hT' : T.map e.toMonoidHom = T₀ := by
    rw [← hg]
    exact map_map_symm (MulAut.conj g) T₀
  have hB' : B.map e.toMonoidHom ∈ lFamily T₀ := by
    have h1 := cComp_map_mulEquiv e (show B ∈ cComp (B ⊔ T) from hB)
    rw [Subgroup.map_sup, hT'] at h1
    exact h1
  have hne : B.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hBtop
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  exact hinv e B (h _ hB' hne)

theorem Over.of_mulEquiv {Y : Type} [Group Y] [Finite Y] (e : X ≃* Y) {P : Subgroup X → Prop}
    {Q : Subgroup Y → Prop} (hPQ : ∀ B : Subgroup X, Q (B.map e.toMonoidHom) → P B)
    (h : Over Y Q) : Over X P := by
  intro T hT B hB hBtop
  have hT' : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ :=
    A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hT
  have hB' : B.map e.toMonoidHom ∈ lFamily (T.map e.toMonoidHom) := by
    have h1 := cComp_map_mulEquiv e (show B ∈ cComp (B ⊔ T) from hB)
    rw [Subgroup.map_sup] at h1
    exact h1
  have hne : B.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hBtop
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  exact hPQ B (h _ hT' _ hB' hne)

theorem Over.of_false {P : Subgroup X → Prop} (h : Over X (fun _ => False)) : Over X P :=
  fun T hT B hB hne => (h T hT B hB hne).elim

theorem over_of_solvable_overgroups (hq : CFSG.IsQuasisimple X) (T₀ : Subgroup X)
    (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ∀ M : Subgroup X, T₀ ≤ M → M ≠ ⊤ → Group.IsSolvable ↥M) :
    Over X (fun _ => False) := by
  refine Over.of_sylow (fun _ _ h => h) T₀ hT₀ fun B hB hBtop => ?_
  have hB' : B ∈ cComp (B ⊔ T₀) := hB
  have hne : B ⊔ T₀ ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hsolv : Group.IsSolvable ↥(B ⊔ T₀) := h _ le_sup_right hne
  exact not_isSolvable_of_mem_cComp hB'
    (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T₀))
      (Subgroup.inclusion_injective _))

end Transport

section Bender

open CFSG.QuasithinUnique.Unc25G2.BenderBorel MulAction

theorem bender_overgroups {X : Type} [Group X] [Finite X] [hs : IsSimpleGroup X]
    (hB : fusionIsBenderGroup X) (Q : Sylow 2 X) {M : Subgroup X}
    (hQM : (Q : Subgroup X) ≤ M) (hM : M ≠ ⊤) : Group.IsSolvable ↥M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, hq4, hBor⟩ := exists_borel_of_bender hB
  obtain ⟨hSE, ⟨D, hDcyc, hDodd, hQD, hsup⟩, hZpow, hZcard, hQcard⟩ := hBor Q
  have hsolvN := isSolvable_normalizer_of_sup_cyclic Q.isPGroup' hDcyc hsup
  have hreg := regular_of_borel (isSimpleBenderGroup_of_fusion hB) Q hsolvN
  set N := Subgroup.normalizer ((Q : Subgroup X) : Set X) with hN
  have hQN : (Q : Subgroup X) ≤ N := Subgroup.le_normalizer
  have hQne : (Q : Subgroup X) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (Subgroup.center (Q : Subgroup X)) = 1 := by
      have : Subsingleton (↥(Q : Subgroup X)) := by
        rw [hbot]
        infer_instance
      have : Subsingleton (Subgroup.center (Q : Subgroup X)) :=
        (Subgroup.center (Q : Subgroup X)).subtype_injective.subsingleton
      exact Nat.card_unique
    omega
  have hMN : M ≤ N := by
    by_contra hnot
    obtain ⟨m₀, hm₀M, hm₀N⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    have hconj : ∀ g : X, ∀ x ∈ (Q : Subgroup X), g * x * g⁻¹ ∈ M := by
      intro g x hx
      have hex : ∃ m ∈ M, m⁻¹ * g ∈ N := by
        by_cases hg : g ∈ N
        · exact ⟨1, M.one_mem, by simpa using hg⟩
        · have hα : (QuotientGroup.mk m₀ : X ⧸ N) ≠ QuotientGroup.mk 1 := by
            intro h
            apply hm₀N
            have := QuotientGroup.eq.mp h
            simpa using N.inv_mem this
          have hβ : (QuotientGroup.mk g : X ⧸ N) ≠ QuotientGroup.mk 1 := by
            intro h
            apply hg
            have := QuotientGroup.eq.mp h
            simpa using N.inv_mem this
          obtain ⟨⟨r, hr⟩, hrβ, -⟩ := hreg hα hβ
          refine ⟨r * m₀, M.mul_mem (hQM hr) hm₀M, ?_⟩
          have h1 : (QuotientGroup.mk (r * m₀) : X ⧸ N) = QuotientGroup.mk g := by
            have : (⟨r, hr⟩ : ↥(Q : Subgroup X)) • (QuotientGroup.mk m₀ : X ⧸ N) =
                QuotientGroup.mk g := hrβ
            simpa [MulAction.Quotient.smul_mk] using this
          exact QuotientGroup.eq.mp h1
      obtain ⟨m, hmM, hmN⟩ := hex
      have hgn : g = m * (m⁻¹ * g) := by group
      set n := m⁻¹ * g with hn
      have hnx : n * x * n⁻¹ ∈ (Q : Subgroup X) := by
        have := (Subgroup.mem_normalizer_iff.mp hmN) x
        exact this.mp hx |> fun h => by simpa using h
      have hmem : m * (n * x * n⁻¹) * m⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem hmM (hQM hnx)) (M.inv_mem hmM)
      have heq : g * x * g⁻¹ = m * (n * x * n⁻¹) * m⁻¹ := by rw [hgn]; group
      rw [heq]
      exact hmem
    have hcl : Subgroup.normalClosure ((Q : Subgroup X) : Set X) ≤ M := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro y hy
      obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      obtain ⟨g, rfl⟩ := isConj_iff.mp hay
      exact hconj g a ha
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure ((Q : Subgroup X) : Set X)) with h | h
    · apply hQne
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ Subgroup.normalClosure ((Q : Subgroup X) : Set X) := Subgroup.subset_normalClosure hx
      rw [h] at this
      exact this
    · apply hM
      rw [eq_top_iff]
      rw [h] at hcl
      exact hcl
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hMN)
    (Subgroup.inclusion_injective hMN)

theorem over_bender {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hB : fusionIsBenderGroup X) : Over X (fun _ => False) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup X := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  exact over_of_solvable_overgroups hq (Q : Subgroup X) (isSylowTwoOf_top_of_sylow Q)
    fun M hQM hM => bender_overgroups hB Q hQM hM

end Bender

end A312Sub

end CFSG.QuasithinUnique.Unc25G2
