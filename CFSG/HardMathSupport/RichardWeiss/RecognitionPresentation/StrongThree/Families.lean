module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open CFSG.RankThree.PartOne.Census3 TauCeti

@[expose] def Gls3PlusCase (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ K : Subgroup X, K.Normal → IsSimpleGroup ↥K → (∃ a b : ↥K, a * b ≠ b * a) →
      Nonempty (↥K ≃* i.Group) → Subgroup.centralizer (K : Set X) = ⊥ →
      ∀ P : Sylow 3 X, 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X) →
        gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤ → Gls3ConclusionPlus X K (P : Subgroup X)

theorem isCatalogGroup_transport {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hB : CFSG.Open.IsCatalogGroup B) : CFSG.Open.IsCatalogGroup A := by
  obtain ⟨i, ⟨f⟩⟩ := hB
  exact ⟨i, ⟨e.trans f⟩⟩

theorem gls3PlusCase_cyclic (p : ℕ) (hp : p.Prime) : Gls3PlusCase (.cyclic p hp) := by
  unfold Gls3PlusCase
  intro X _ _ _ K _ _ hnc hiso _ _ _ _
  exfalso
  obtain ⟨a, b, hab⟩ := hnc
  obtain ⟨e⟩ := hiso
  have key : ∀ x y : Multiplicative (ZMod p), x * y = y * x := fun x y => mul_comm x y
  have h : e (a * b) = e (b * a) := by
    rw [map_mul, map_mul]
    exact key (e a) (e b)
  exact hab (e.injective h)

theorem gls3StronglyThreeEmbeddedPlus_of_families
    (hA : ∀ n (h5 : 5 ≤ n), Gls3PlusCase (.alternating n h5))
    (hL : ∀ idx, Gls3PlusCase (.lie idx)) (hS : ∀ s, Gls3PlusCase (.sporadic s)) :
    Gls3StronglyThreeEmbeddedPlus := by
  unfold Gls3StronglyThreeEmbeddedPlus
  intro X _ _ hX K hKn hKs hKnc hKc P hP hΓ
  have hbot : (⊥ : Subgroup X).subgroupOf K = ⊥ := Subgroup.bot_subgroupOf K
  have : ((⊥ : Subgroup X).subgroupOf K).Normal := by
    rw [hbot]
    infer_instance
  have eqQ : K ⧸ (⊥ : Subgroup X).subgroupOf K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hsimpleQ : IsSimpleGroup (K ⧸ (⊥ : Subgroup X).subgroupOf K) := eqQ.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hKnc
  have hpairQ : ∃ a' b' : K ⧸ (⊥ : Subgroup X).subgroupOf K, a' * b' ≠ b' * a' :=
    ⟨eqQ.symm a, eqQ.symm b, fun h => hab (by
      have := congrArg eqQ h
      simpa using this)⟩
  have hcatQ : CFSG.Open.IsCatalogGroup (K ⧸ (⊥ : Subgroup X).subgroupOf K) :=
    hX K ⊥ bot_le hsimpleQ hpairQ
  have hcat : CFSG.Open.IsCatalogGroup K := isCatalogGroup_transport eqQ.symm hcatQ
  obtain ⟨i, hiso⟩ := hcat
  cases i with
  | cyclic p hp =>
    exact gls3PlusCase_cyclic p hp X hX K hKn hKs ⟨a, b, hab⟩ hiso hKc P hP hΓ
  | alternating n h5 =>
    exact hA n h5 X hX K hKn hKs ⟨a, b, hab⟩ hiso hKc P hP hΓ
  | lie idx =>
    exact hL idx X hX K hKn hKs ⟨a, b, hab⟩ hiso hKc P hP hΓ
  | sporadic s =>
    exact hS s X hX K hKn hKs ⟨a, b, hab⟩ hiso hKc P hP hΓ

theorem gls3PlusCase_alternating_five (h5 : 5 ≤ 5) : Gls3PlusCase (.alternating 5 h5) := by
  unfold Gls3PlusCase
  intro X _ _ _ K hKn hKs hnc hiso hKc P hP _
  exfalso
  obtain ⟨e⟩ := hiso
  have e' : ↥K ≃* ↥(alternatingGroup (Fin 5)) := e
  have hinj : Function.Injective (Subgroup.normalizerMonoidHom K) := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hmem : n ∈ (Subgroup.normalizerMonoidHom K).ker := hn
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, hKc, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcard : Nat.card (MulAut ↥K) = 120 := by
    have e1 : MulAut ↥K ≃* MulAut ↥(alternatingGroup (Fin 5)) := MulAut.congr e'
    have e2 : Equiv.Perm (Fin 5) ≃* MulAut ↥(alternatingGroup (Fin 5)) :=
      MulEquiv.ofBijective MulAut.conjNormal
        (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
          (by norm_num) (by norm_num))
    rw [Nat.card_congr (e1.trans e2.symm).toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    rfl
  have hdvd : Nat.card (Subgroup.normalizer (K : Set X)) ∣ 120 := by
    have h := Subgroup.card_dvd_of_injective (Subgroup.normalizerMonoidHom K) hinj
    rwa [hcard] at h
  have hnorm : Nat.card (Subgroup.normalizer (K : Set X)) = Nat.card X := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn, Subgroup.card_top]
  have hXdvd : Nat.card X ∣ 120 := by
    rw [← hnorm]
    exact hdvd
  have hE : ∀ k : ℕ, (∃ E : Subgroup X, E ≤ (P : Subgroup X) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k) → k ≤ 1 := by
    rintro k ⟨E, -, -, hEk⟩
    have h1 : 3 ^ k ∣ 120 := by
      have h := Subgroup.card_subgroup_dvd_card E
      rw [hEk] at h
      exact h.trans hXdvd
    by_contra hk
    have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (show 2 ≤ k by omega)
    exact absurd (h9.trans h1) (by norm_num)
  have hpR : CFSG.Open.pRank 3 (P : Subgroup X) ≤ 1 := by
    unfold CFSG.Open.pRank
    apply csSup_le'
    intro k hk
    exact hE k hk
  omega

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
