module

public import CFSG.GH74.GLS.Balance.Bender.Ambient

public section

namespace CFSG.GH74.GLS.Balance.BenderExt

theorem isSylowIn_iff_isSylowOf {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T N : Subgroup G} : IsSylowIn p T N ↔ CFSG.ABGLocalTools.IsSylowOf p T N := by
  constructor
  · exact exists_sylow_of_isSylowIn p
  · rintro ⟨S, rfl⟩
    exact isSylowIn_of_sylow p S

theorem le_of_isSylowIn_of_le_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N P S : Subgroup G} (hP : IsSylowIn p P N) (hSN : S ≤ N) (hS : IsPGroup p ↥S)
    (hSC : S ≤ Subgroup.centralizer (P : Set G)) : S ≤ P := by
  obtain ⟨hPN, hP2, hPs⟩ := hP
  have hsup : IsPGroup p ↥(S ⊔ P) :=
    IsPGroup.to_sup_of_normal_right' hS hP2 (hSC.trans (Subgroup.centralizer_le_normalizer _))
  have hcard : Nat.card ↥(S ⊔ P) ≤ Nat.card ↥P := hPs _ (sup_le hSN hPN) hsup
  have heq : P = S ⊔ P := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  exact le_sup_left.trans heq.symm.le

theorem isSylowIn_inf_of_le_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N P X₀ : Subgroup G} (hP : IsSylowIn p P N) (hX₀ : X₀ ≤ Subgroup.centralizer (P : Set G)) :
    IsSylowIn p (P ⊓ X₀) (N ⊓ X₀) := by
  refine ⟨inf_le_inf_right X₀ hP.1, hP.2.1.to_inf_left, fun S hSN hS => ?_⟩
  have hSP : S ≤ P := le_of_isSylowIn_of_le_centralizer hP (hSN.trans inf_le_left) hS
    (hSN.trans (inf_le_right.trans hX₀))
  exact Subgroup.card_le_of_le (le_inf hSP (hSN.trans inf_le_right))

private theorem relIndex_sup_of_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hLE).toEquiv.symm

private theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {H N : Subgroup G} (hLE : H ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(N ⊓ H) = Nat.card ↥N * Nat.card ↥H := by
  have h1 := Subgroup.relIndex_mul_card N (H ⊔ N)
  have h2 := Subgroup.relIndex_mul_card N H
  rw [inf_eq_left.mpr le_sup_right, relIndex_sup_of_le_normalizer hLE] at h1
  rw [← h1, ← h2]
  ring

private theorem le_normalizer_inf_of_le_normalizer {G : Type*} [Group G] {N M₀ : Subgroup G}
    (hM₀ : M₀ ≤ Subgroup.normalizer (N : Set G)) :
    M₀ ≤ Subgroup.normalizer ((N ⊓ M₀ : Subgroup G) : Set G) :=
  (le_inf hM₀ Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem add_factorization_eq_of_mul_eq {p a b c d : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (h : a * b = c * d) :
    a.factorization p + b.factorization p = c.factorization p + d.factorization p := by
  have := congrArg (fun n => n.factorization p) h
  simpa [Nat.factorization_mul, ha, hb, hc, hd] using this

theorem isSylowIn_sup_of_le_normalizer {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N M₀ M P R : Subgroup G} (hM : M = N ⊔ M₀) (hM₀ : M₀ ≤ Subgroup.normalizer (N : Set G))
    (hP : IsSylowIn p P N) (hR : IsSylowIn p R M₀)
    (hRP : R ≤ Subgroup.centralizer (P : Set G)) : IsSylowIn p (P ⊔ R) M := by
  subst hM
  have hPN : P ≤ N := hP.1
  have hRM₀ : R ≤ M₀ := hR.1
  have hPs : CFSG.ABGLocalTools.IsSylowOf p P N := isSylowIn_iff_isSylowOf.mp hP
  have hRs : CFSG.ABGLocalTools.IsSylowOf p R M₀ := isSylowIn_iff_isSylowOf.mp hR
  have h1 : N ⊓ R ≤ P :=
    le_of_isSylowIn_of_le_centralizer hP inf_le_left hR.2.1.to_inf_right (inf_le_right.trans hRP)
  have hNR : N ⊓ R = P ⊓ R := le_antisymm (le_inf h1 inf_le_right) (inf_le_inf_right R hPN)
  have h2 : CFSG.ABGLocalTools.IsSylowOf p (R ⊓ (N ⊓ M₀)) (N ⊓ M₀) :=
    hRs.inf_of_le_normalizer inf_le_right (le_normalizer_inf_of_le_normalizer hM₀)
  have hR2 : R ⊓ (N ⊓ M₀) = P ⊓ R := by
    rw [← hNR]
    exact le_antisymm (le_inf (inf_le_right.trans inf_le_left) inf_le_left)
      (le_inf inf_le_right (le_inf inf_le_left (inf_le_right.trans hRM₀)))
  have hcP : Nat.card ↥P = p ^ (Nat.card ↥N).factorization p := hPs.card_eq
  have hcR : Nat.card ↥R = p ^ (Nat.card ↥M₀).factorization p := hRs.card_eq
  have hcPR : Nat.card ↥(P ⊓ R) = p ^ (Nat.card ↥(N ⊓ M₀)).factorization p := by
    rw [← hR2]
    exact h2.card_eq
  have hA : Nat.card ↥(R ⊔ P) * Nat.card ↥(P ⊓ R) = Nat.card ↥P * Nat.card ↥R :=
    card_sup_mul_card_inf_of_le_normalizer (hRP.trans (Subgroup.centralizer_le_normalizer _))
  have hB : Nat.card ↥(N ⊔ M₀) * Nat.card ↥(N ⊓ M₀) = Nat.card ↥N * Nat.card ↥M₀ := by
    rw [sup_comm]
    exact card_sup_mul_card_inf_of_le_normalizer hM₀
  have hB' : (Nat.card ↥(N ⊔ M₀)).factorization p + (Nat.card ↥(N ⊓ M₀)).factorization p =
      (Nat.card ↥N).factorization p + (Nat.card ↥M₀).factorization p :=
    add_factorization_eq_of_mul_eq Nat.card_pos.ne' Nat.card_pos.ne' Nat.card_pos.ne'
      Nat.card_pos.ne' hB
  have hpc : 0 < p ^ (Nat.card ↥(N ⊓ M₀)).factorization p := pow_pos (Fact.out : p.Prime).pos _
  have hAcard : Nat.card ↥(R ⊔ P) = p ^ (Nat.card ↥(N ⊔ M₀)).factorization p := by
    apply Nat.eq_of_mul_eq_mul_right hpc
    calc Nat.card ↥(R ⊔ P) * p ^ (Nat.card ↥(N ⊓ M₀)).factorization p
        = Nat.card ↥(R ⊔ P) * Nat.card ↥(P ⊓ R) := by rw [hcPR]
      _ = Nat.card ↥P * Nat.card ↥R := hA
      _ = p ^ (Nat.card ↥N).factorization p * p ^ (Nat.card ↥M₀).factorization p := by
        rw [hcP, hcR]
      _ = p ^ ((Nat.card ↥N).factorization p + (Nat.card ↥M₀).factorization p) :=
        (pow_add _ _ _).symm
      _ = p ^ ((Nat.card ↥(N ⊔ M₀)).factorization p + (Nat.card ↥(N ⊓ M₀)).factorization p) := by
        rw [hB']
      _ = p ^ (Nat.card ↥(N ⊔ M₀)).factorization p * p ^ (Nat.card ↥(N ⊓ M₀)).factorization p :=
        pow_add _ _ _
  rw [sup_comm] at hAcard
  exact isSylowIn_iff_isSylowOf.mpr (CFSG.ABGLocalTools.isSylowOf_of_card
    (sup_le (hPN.trans le_sup_left) (hRM₀.trans le_sup_right)) hAcard)

end CFSG.GH74.GLS.Balance.BenderExt
