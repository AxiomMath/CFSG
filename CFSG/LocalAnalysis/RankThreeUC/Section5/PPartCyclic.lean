module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralizerSemiregular
public import CFSG.GroupTheory.CyclicSubgroup.CentralCommutator

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace PPartCyclic

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_coset {p : ℕ} (hp : p.Prime) {P X D : Subgroup G}
    (hP : IsPGroup p P) (hXP : X ≤ P) (hXc : ∀ x ∈ X, ∀ y ∈ P, x * y = y * x)
    (hXne : X ≠ P) (hD : IsPGroup p D) (hDN : D ≤ Subgroup.normalizer (P : Set G))
    (hDX : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d) :
    ∃ y ∈ P, y ∉ X ∧ ∀ d ∈ D, d * y * d⁻¹ * y⁻¹ ∈ X := by
  haveI : Fact p.Prime := ⟨hp⟩
  set X' : Subgroup P := X.subgroupOf P with hX'
  haveI : X'.Normal := ⟨fun n hn g => by
    have h1 : (n : G) ∈ X := hn
    show ((g * n * g⁻¹ : P) : G) ∈ X
    have : (g : G) * n * (g : G)⁻¹ = n := by
      rw [← hXc n h1 g g.2]; simp
    show ((g : G) * n * (g : G)⁻¹ ∈ X)
    rw [this]; exact h1⟩
  let φ : D → P →* P := fun d =>
    { toFun := fun y => ⟨d * y * (d : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hDN d.2) y).1 y.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [mul_assoc] }
  have hφ : ∀ d : D, ∀ y : P, ((φ d y : P) : G) = d * y * (d : G)⁻¹ := fun d y => rfl
  have hφX : ∀ d : D, X' ≤ X'.comap (φ d) := by
    intro d n hn
    have h1 : (n : G) ∈ X := hn
    show ((φ d n : P) : G) ∈ X
    rw [hφ]
    have : (d : G) * n * (d : G)⁻¹ = n := by
      rw [hDX d d.2 n h1]; simp
    rw [this]; exact h1
  let ψ : D → (P ⧸ X') →* (P ⧸ X') := fun d => QuotientGroup.map X' X' (φ d) (hφX d)
  have hψ : ∀ d : D, ∀ y : P, ψ d (y : P ⧸ X') = ((φ d y : P) : P ⧸ X') :=
    fun d y => rfl
  letI : MulAction D (P ⧸ X') :=
    { smul := fun d q => ψ d q
      one_smul := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H y =>
          show ψ 1 (y : P ⧸ X') = y
          rw [hψ]
          congr 1; ext; simp [hφ]
      mul_smul := by
        intro a b q
        induction q using QuotientGroup.induction_on with
        | H y =>
          show ψ (a * b) (y : P ⧸ X') = ψ a (ψ b (y : P ⧸ X'))
          rw [hψ, hψ, hψ]
          congr 1; ext; simp [hφ, mul_assoc] }
  have hsm : ∀ (d : D) (y : P), d • (y : P ⧸ X') = ((φ d y : P) : P ⧸ X') := fun d y => rfl
  have hmod := hD.card_modEq_card_fixedPoints (P ⧸ X')
  have hQdvd : Nat.card (P ⧸ X') ∣ Nat.card P := by
    rw [← Subgroup.index_eq_card]; exact Subgroup.index_dvd_card X'
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hPcard : Nat.card P = p ^ n := hn
  obtain ⟨j, hj, hjQ⟩ := (Nat.dvd_prime_pow hp).1 (hPcard ▸ hQdvd)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, ← Subgroup.index_eq_card, Subgroup.index_eq_one,
      hX', Subgroup.subgroupOf_eq_top] at hjQ
    exact hXne (le_antisymm hXP hjQ)
  have hpd : p ∣ Nat.card (P ⧸ X') := by
    rw [hjQ]; exact dvd_pow_self p hj0
  have hfixdvd : p ∣ Nat.card (MulAction.fixedPoints D (P ⧸ X')) := by
    have h0 : Nat.card (P ⧸ X') ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 hpd
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans h0)
  have hone : (1 : P ⧸ X') ∈ MulAction.fixedPoints D (P ⧸ X') := by
    intro d
    show ψ d 1 = 1
    exact map_one _
  have hpos : 0 < Nat.card (MulAction.fixedPoints D (P ⧸ X')) :=
    Nat.card_pos_iff.2 ⟨⟨⟨1, hone⟩⟩, inferInstance⟩
  have hgt : 1 < Nat.card (MulAction.fixedPoints D (P ⧸ X')) :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hfixdvd)
  haveI : Nontrivial (MulAction.fixedPoints D (P ⧸ X')) := Finite.one_lt_card_iff_nontrivial.1 hgt
  obtain ⟨⟨q, hq⟩, hq1⟩ := exists_ne (⟨1, hone⟩ : MulAction.fixedPoints D (P ⧸ X'))
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  induction q using QuotientGroup.induction_on with
  | H y =>
    refine ⟨y, y.2, ?_, ?_⟩
    · intro hy
      apply hq1'
      rw [QuotientGroup.eq_one_iff]
      exact hy
    · intro d hd
      have h1 := hq ⟨d, hd⟩
      rw [hsm] at h1
      have h2 := QuotientGroup.eq.1 h1
      have h3 : (((φ ⟨d, hd⟩ y)⁻¹ * y : P) : G) ∈ X := h2
      have h4 : (((φ ⟨d, hd⟩ y)⁻¹ * y : P) : G) = d * (y : G)⁻¹ * (d : G)⁻¹ * y := by
        simp [hφ, mul_assoc]
      rw [h4] at h3
      have h5 := inv_mem h3
      have h6 := hXc _ h5 y y.2
      have : d * y * d⁻¹ * (y : G)⁻¹ = (y : G) * (d * (y : G)⁻¹ * (d : G)⁻¹ * y)⁻¹ * (y : G)⁻¹ := by
        group
      rw [this, ← h6]
      simpa using h5

private theorem open_pCore_eq (p : ℕ) (X : Type) [Group X] :
    CFSG.Open.pCore p X = CFSG.pCore p X := rfl

private theorem pCoreOf_isPGroup (p : ℕ) (H : Subgroup G) :
    IsPGroup p (CFSG.Open.pCoreOf p H : Subgroup G) := by
  unfold CFSG.Open.pCoreOf
  rw [open_pCore_eq]
  exact (CFSG.pCore_isPGroup (p := p) (G := H)).map H.subtype

private theorem pCoreOf_le (p : ℕ) (H : Subgroup G) : CFSG.Open.pCoreOf p H ≤ H := by
  intro x hx
  unfold CFSG.Open.pCoreOf at hx
  obtain ⟨a, _, ha⟩ := Subgroup.mem_map.mp hx
  rw [← ha]
  exact a.2

end PPartCyclic
variable {G : Type} [Group G] [Finite G]

theorem actor_primeCore_isCyclic {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    IsCyclic ↥(CFSG.Open.pCoreOf p B) := by
  have hp : p.Prime := h.oddPrimeClassTwoAction.setting.prime
  have h9 := commutator_actorTwoCore_sup_actor_center_eq_bot h
  have hcent := centralizer_nonidentity_actor_eq_center h
  have hZle : centerP P ≤ P := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hZcard : Nat.card (centerP P) = p := by
    have h1 := h.extraspecial.2.2.2
    unfold centerP
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact h1
  have hXc : ∀ x ∈ centerP P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    have := (Subgroup.mem_center_iff.1 hz) ⟨y, hy⟩
    have h2 := congrArg Subtype.val this
    simpa using h2.symm
  have hXne : centerP P ≠ P := by
    intro hXP
    have hPcard : Nat.card P = p := by rw [← hXP]; exact hZcard
    have hrank := h.faithfulBinaryIrreducibleAction.rank_gt
    have : CFSG.Open.pRank p P ≤ 1 := by
      apply csSup_le'
      rintro k ⟨E, hEP, _, hEk⟩
      have h1 : Nat.card E ≤ Nat.card P := Subgroup.card_le_of_le hEP
      rw [hEk, hPcard] at h1
      by_contra hk
      push Not at hk
      have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
      have : p * p ≤ p := by nlinarith
      nlinarith [hp.one_lt]
    omega
  have hX : twoCoreCommutator T B ⊔ B ≤ Subgroup.centralizer (centerP P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h9
  have hDB : CFSG.Open.pCoreOf p B ≤ B := PPartCyclic.pCoreOf_le p B
  obtain ⟨y, hyP, hyX, hy⟩ := PPartCyclic.exists_fixed_coset hp h.oddPrimeClassTwoAction.setting.pGroup hZle hXc hXne
    (PPartCyclic.pCoreOf_isPGroup p B) (hDB.trans h.oddPrimeClassTwoAction.setting.normB)
    (fun d hd x hx => by
      have hd' : d ∈ (twoCoreCommutator T B ⊔ B : Subgroup G) := (le_sup_right : B ≤ twoCoreCommutator T B ⊔ B) (hDB hd)
      exact (hX hd' x hx).symm)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (centerP P) := isCyclic_of_prime_card hZcard
  refine CFSG.GroupTheory.CyclicSubgroup.isCyclic_of_faithful_central_commutator
    (CFSG.Open.pCoreOf p B) (centerP P) y ?_ hy ?_
  · intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hd' : d ∈ (twoCoreCommutator T B ⊔ B : Subgroup G) := (le_sup_right : B ≤ twoCoreCommutator T B ⊔ B) (hDB hd)
    exact hX hd' x hx
  · intro d hd hdy
    by_contra hd1
    apply hyX
    rw [← hcent d (hDB hd) hd1]
    refine ⟨hyP, ?_⟩
    show y ∈ Subgroup.centralizer ({d} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hdy

end Section5
end CFSG.LocalAnalysis.RankThreeUC
