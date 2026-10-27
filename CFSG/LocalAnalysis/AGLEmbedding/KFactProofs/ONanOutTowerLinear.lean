module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOutTower
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinAut

public section

namespace CFSG.AGLEmbedding

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem commutator_mem_of_isCyclic_quotient {G : Type*} [Group G] [Finite G] {D I : Subgroup G}
    [D.Normal] [I.Normal] (hcyc : IsCyclic (D ⧸ I.subgroupOf D)) {p : ℕ} (hp : p.Prime)
    (htot : ¬ p ∣ Nat.totient (Nat.card (D ⧸ I.subgroupOf D))) {α : G} {k : ℕ}
    (hα : α ^ (p ^ k) = 1) {δ : G} (hδ : δ ∈ D) : α * δ * α⁻¹ * δ⁻¹ ∈ I := by
  set N := I.subgroupOf D with hN
  let c : G →* MulAut D := MulAut.conjNormal
  have hcN : ∀ g : G, N.map (c g).toMonoidHom = N := by
    intro g
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change (c g x : G) ∈ I
      rw [MulAut.conjNormal_apply]
      exact ‹I.Normal›.conj_mem _ hx g
    · intro x hx
      refine ⟨(c g)⁻¹ x, ?_, by simp⟩
      change (((c g)⁻¹ x : D) : G) ∈ I
      rw [MulAut.conjNormal_inv_apply]
      have := ‹I.Normal›.conj_mem _ hx g⁻¹
      rwa [inv_inv] at this
  let φ : MulAut (D ⧸ N) := QuotientGroup.congr N N (c α) (hcN α)
  have hφ : ∀ (j : ℕ) (x : D), (φ ^ j) (x : D ⧸ N) = ((c α ^ j) x : D ⧸ N) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply]
      exact QuotientGroup.congr_mk' N N (c α) (hcN α) _
  have hpow : φ ^ (p ^ k) = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [hφ, ← map_pow, hα, map_one]
      rfl
  have h2 : orderOf φ ∣ Nat.totient (Nat.card (D ⧸ N)) := by
    rw [← IsCyclic.card_mulAut]
    exact orderOf_dvd_natCard φ
  have h3 : orderOf φ = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hpow)
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply htot
      rw [hj] at h2
      exact (dvd_pow_self p (Nat.succ_ne_zero j)).trans h2
  rw [orderOf_eq_one_iff] at h3
  have h4 : φ ((⟨δ, hδ⟩ : D) : D ⧸ N) = ((⟨δ, hδ⟩ : D) : D ⧸ N) := by rw [h3]; rfl
  have h5 := hφ 1 ⟨δ, hδ⟩
  rw [pow_one, pow_one, h4] at h5
  have h6 := (QuotientGroup.eq).1 h5
  have h7 : δ⁻¹ * (α * δ * α⁻¹) ∈ I := by
    have := Subgroup.mem_subgroupOf.1 h6
    have e1 : ((c α ⟨δ, hδ⟩ : D) : G) = α * δ * α⁻¹ := MulAut.conjNormal_apply α ⟨δ, hδ⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, e1] at this
    exact this
  have h8 := ‹I.Normal›.conj_mem _ h7 δ
  have h9 : δ * (δ⁻¹ * (α * δ * α⁻¹)) * δ⁻¹ = α * δ * α⁻¹ * δ⁻¹ := by group
  rwa [h9] at h8

section Linear

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem commutator_mem_linearAutGroup (hn : 3 ≤ n) {ℓ f : ℕ} (_hℓ : ℓ.Prime) (_hf : 1 ≤ f)
    (_hF : Nat.card F = ℓ ^ f) (α β : MulAut (projectiveSL n F)) :
    α * β * α⁻¹ * β⁻¹ ∈ linearAutGroup n F :=
  OuterDerived.commutator_mem_linearAutGroup hn α β

theorem outTowerAt_projectiveSL (hn : 3 ≤ n) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (htot : ¬ p ∣ Nat.totient (Nat.gcd n (Nat.card F - 1))) :
    OutTowerAt (projectiveSL n F) p := by
  have : (linearAutGroup n F).Normal :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.linearAutGroup_normal hn
  have : ((MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  refine ⟨linearAutGroup n F, fun γ α _ => commutator_mem_linearAutGroup hn hℓ hf hF γ α,
    fun α ⟨k, hk⟩ δ hδ => ?_⟩
  have hcyc := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.isCyclic_linearD_quotient (K := F) hn
  have hdvd := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.relIndex_inner_linearAutGroup_dvd
    (k := F) (n := n) (by omega)
  have htot' : ¬ p ∣ Nat.totient (Nat.card (linearAutGroup n F ⧸
      (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range.subgroupOf
        (linearAutGroup n F))) := by
    intro h
    apply htot
    refine h.trans (Nat.totient_dvd_of_dvd ?_)
    have : Nat.card (linearAutGroup n F ⧸
        (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range.subgroupOf
          (linearAutGroup n F)) =
        (inner (projectiveSL n F)).relIndex (linearAutGroup n F) := rfl
    rw [this]
    exact hdvd
  exact commutator_mem_of_isCyclic_quotient hcyc hp htot' hk hδ

theorem outTowerAt_catA {m : ℕ} (hm : 2 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime)
    (htot : ¬ p ∣ Nat.totient (Nat.gcd (m + 1) (q.card - 1))) :
    OutTowerAt (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group p := by
  let e : (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group ≃*
      projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent := by
    rw [GaloisField.card _ _ q.exponent_pos.ne']
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine OutTowerAt.of_mulEquiv e (outTowerAt_projectiveSL (by omega) q.prime_p q.exponent_pos
    hcardF hp ?_)
  rwa [hcardF, ← TauCeti.PrimePower.card_def]

end Linear

end CFSG.AGLEmbedding
