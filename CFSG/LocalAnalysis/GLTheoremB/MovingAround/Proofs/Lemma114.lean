module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Lemma114Basic

variable {G : Type} [Group G] [Finite G]

theorem l114_core_le {p : ℕ} {M E : Subgroup G} (hE : inD p M E) {e : G} (he : e ∈ E)
    (he1 : e ≠ 1) : GLAPPrimeCoreOf p (Subgroup.centralizer ({e} : Set G)) ≤ M :=
  le_sup_left.trans (hE.2.clause_a e he he1)

theorem l114_normalizer_le_glbCore {p : ℕ} {P Q : Subgroup G} (hQ : Q ≤ P)
    (hk : 2 ≤ CFSG.Open.pRank p Q) : Subgroup.normalizer (Q : Set G) ≤ GLBCore p 2 P :=
  le_sSup ⟨Q, hQ, hk, rfl⟩

theorem l114_glbCore_mono {p : ℕ} {P Q : Subgroup G} (h : P ≤ Q) :
    GLBCore p 2 P ≤ GLBCore p 2 Q := by
  unfold GLBCore
  refine sSup_le ?_
  rintro _ ⟨R, hR, hk, rfl⟩
  exact le_sSup ⟨R, hR.trans h, hk, rfl⟩

theorem l114_card_hyperplane {p : ℕ} [hp : Fact p.Prime] {A₁ : Subgroup G} {s : ℕ}
    (hcard : Nat.card A₁ = p ^ s) (hs : 1 ≤ s) {B : Subgroup ↥A₁} (hB : B.index = p) :
    Nat.card B = p ^ (s - 1) := by
  have h := B.card_mul_index
  rw [hB, hcard] at h
  have hs' : s = (s - 1) + 1 := by omega
  rw [hs', pow_succ] at h
  exact Nat.eq_of_mul_eq_mul_right hp.out.pos h

end Lemma114Basic

section Lemma114Gen

variable {G : Type} [Group G] [Finite G]

theorem l114_core_le_glbCore {p : ℕ} [hp : Fact p.Prime] {e a : G} {A₁ : Subgroup G} {s : ℕ}
    (hA₁ : IsElemAbelian p A₁) (hA₁C : A₁ ≤ Subgroup.centralizer ({e, a} : Set G))
    (hcard : Nat.card A₁ = p ^ s) (hs : 3 ≤ s) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({e, a} : Set G)) ≤ GLBCore p 2 A₁ := by
  classical
  set C2 : Subgroup G := Subgroup.centralizer ({e, a} : Set G) with hC2
  set X : Subgroup G := GLAPPrimeCoreOf p C2 with hX
  have hAN : A₁ ≤ Subgroup.normalizer (X : Set G) := hA₁C.trans (le_normalizer_glaPPrimeCoreOf p C2)
  have hcop : ¬ p ∣ Nat.card ↥X := not_dvd_card_glaPPrimeCoreOf hp.out C2
  have hnt : Nontrivial ↥A₁ := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.out.one_lt
  letI : MulDistribMulAction ↥A₁ ↥X := Subgroup.conjMulDistribMulActionOfLeNormalizer A₁ X hAN
  haveI : CFSG.IsElementaryAbelian p ↥A₁ := CFSG.Open.IsElemAbelian.isElementaryAbelian hA₁
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := ↥A₁) (H := ↥X) hcop
  have key : ∀ B : Subgroup ↥A₁, B.index = p → ∀ y ∈ CFSG.fixedPointSubgroup B ↥X,
      (y : G) ∈ GLBCore p 2 A₁ := by
    intro B hB y hy
    set B' : Subgroup G := B.map A₁.subtype with hB'
    have hB'le : B' ≤ A₁ := Subgroup.map_subtype_le B
    have hcomm : ∀ b ∈ B', (y : G) * b = b * (y : G) := by
      intro b hb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      have hfix := (FixedPoints.mem_subgroup _ _ _).mp hy ⟨b', hb'⟩
      have hval : (b' : G) * (y : G) * (b' : G)⁻¹ = (y : G) := congrArg (fun z : ↥X => (z : G)) hfix
      have h2 : (b' : G) * (y : G) = (y : G) * (b' : G) := by
        calc (b' : G) * (y : G) = ((b' : G) * (y : G) * (b' : G)⁻¹) * (b' : G) := by group
          _ = (y : G) * (b' : G) := by rw [hval]
      exact h2.symm
    have hconjInv : ∀ k ∈ B', (y : G)⁻¹ * k * (y : G) = k := by
      intro k hk
      have hk' := hcomm k hk
      calc (y : G)⁻¹ * k * (y : G) = (y : G)⁻¹ * (k * (y : G)) := by group
        _ = (y : G)⁻¹ * ((y : G) * k) := by rw [hk']
        _ = k := by group
    have hconj : ∀ k ∈ B', (y : G) * k * (y : G)⁻¹ = k := by
      intro k hk
      have hk' := hcomm k hk
      calc (y : G) * k * (y : G)⁻¹ = ((y : G) * k) * (y : G)⁻¹ := rfl
        _ = (k * (y : G)) * (y : G)⁻¹ := by rw [hk']
        _ = k := by group
    have hyN : (y : G) ∈ Subgroup.normalizer (B' : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [hconj h hh]
        exact hh
      · intro hh
        have h1 := hconjInv _ hh
        have h2 : (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G) = h := by group
        rw [h1] at h2
        rw [← h2]
        exact hh
    have hB'ea : IsElemAbelian p B' := isElemAbelian_mono hA₁ hB'le
    have hcardB' : Nat.card B' = p ^ (s - 1) := by
      rw [hB', Subgroup.card_map_of_injective A₁.subtype_injective]
      exact l114_card_hyperplane hcard (by omega) hB
    have hrank : 2 ≤ CFSG.Open.pRank p B' := by
      have h := CFSG.SectionRank.le_pRank hp.out.one_lt (le_refl B') hB'ea hcardB'
      rw [pRank_eq_pRank_top_subtype hp.out.one_lt] at h ⊢
      omega
    exact l114_normalizer_le_glbCore hB'le hrank hyN
  have htop : (⊤ : Subgroup ↥X) ≤ (GLBCore p 2 A₁).comap X.subtype := by
    rw [← hgen]
    refine iSup₂_le fun B hB => ?_
    intro y hy
    exact key B hB y hy
  intro x hx
  exact htop (Subgroup.mem_top (⟨x, hx⟩ : ↥X))

theorem l114_rank_eq_two {p : ℕ} [hp : Fact p.Prime] {M E A : Subgroup G} {e a : G}
    (hE : inD p M E) (hA : inDp p M A) (hEA : 2 ≤ CFSG.Open.pRank p (E ⊓ A))
    (ha : a ∈ A) (he : e ∈ E ⊓ A)
    (hncore : ¬ GLAPPrimeCoreOf p (Subgroup.centralizer ({e, a} : Set G)) ≤ M) :
    CFSG.Open.pRank p (E ⊓ A) = 2 := by
  by_contra hne
  have h3 : 3 ≤ CFSG.Open.pRank p (E ⊓ A) := by omega
  obtain ⟨E'', hE''le, hE''ea, hE''card⟩ :=
    CFSG.SectionRank.exists_pRank hp.out.one_lt (E ⊓ A)
  apply hncore
  have hEel : IsElemAbelian p E := hE.1.1.2.1
  have hAel : IsElemAbelian p A := hA.1.1.2.1
  have hC : E'' ≤ Subgroup.centralizer ({e, a} : Set G) := by
    intro x hx
    have hxE : x ∈ E := (hE''le hx).1
    have hxA : x ∈ A := (hE''le hx).2
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact elemAbelian_comm hEel he.1 hxE
    · exact elemAbelian_comm hAel ha hxA
  have hfin := l114_core_le_glbCore hE''ea hC hE''card h3
  exact hfin.trans ((l114_glbCore_mono (hE''le.trans inf_le_left)).trans hE.2.clause_d)

end Lemma114Gen


section Lemma114Statement

variable {G : Type} [Group G] [Finite G]

theorem lemma114_i_ii {m p : ℕ} {B M E A : Subgroup G} {e a : G} (h : Fails112 G m p B M E A e a) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({e} : Set G)) ≤ M ∧
      CFSG.Open.pRank p (E ⊓ A) = 2 := by
  have hp : Fact p.Prime := ⟨h.standing.prime⟩
  have hE : inD p M E := h.pair.1.1
  have hA : inDp p M A := h.pair.1.2.1
  have hEA : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := h.pair.1.2.2
  have he : e ∈ E := (Subgroup.mem_inf.1 h.he.1).1
  exact ⟨l114_core_le hE he h.he.2, l114_rank_eq_two hE hA hEA h.ha.1 h.he.1 h.not_i⟩

end Lemma114Statement

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
