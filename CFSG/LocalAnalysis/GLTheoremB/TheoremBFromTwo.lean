module

public import CFSG.LocalAnalysis.GLTheoremB.Statements
public import CFSG.LocalAnalysis.GLTheoremB.Connected
public import CFSG.LocalAnalysis.GLTheoremB.Equivariant
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCore

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def NormalPlaneLemma : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (G : Type) [Group G] [Finite G] (R : Subgroup G),
    IsPGroup p R → 2 ≤ pRank p R →
      ∃ U : Subgroup G, U ≤ R ∧ IsPPlane p U ∧ R ≤ Subgroup.normalizer (U : Set G)

theorem glaWeakCore_eq_weakTwoGeneratedPCore [Finite G] (p : ℕ) (P : Subgroup G) :
    GLAWeakCore p P = CFSG.LargeEvenClassification.Helpers.weakTwoGeneratedPCore p P := by
  refine le_antisymm (sSup_le ?_) (iSup_le fun Q => le_sSup ⟨Q.1, Q.2.1, Q.2.2.1, Q.2.2.2, rfl⟩)
  rintro _ ⟨Q, hQP, h2, h3, rfl⟩
  exact CFSG.LargeEvenClassification.Helpers.eligible_normalizer_le_weak_core P Q ⟨hQP, h2, h3⟩

theorem glaWeakCore_map_conj [Finite G] {p : ℕ} (hp : 1 < p) (g : G) (P : Subgroup G) :
    GLAWeakCore p (P.map (MulAut.conj g).toMonoidHom) =
      (GLAWeakCore p P).map (MulAut.conj g).toMonoidHom := by
  rw [glaWeakCore_eq_weakTwoGeneratedPCore, glaWeakCore_eq_weakTwoGeneratedPCore]
  exact (CFSG.LargeEvenClassification.Helpers.weak_core_map_mulEquiv hp (MulAut.conj g) P).symm

theorem isTwoLocal_map_conj {M : Subgroup G} (hM : IsTwoLocal M) (g : G) :
    IsTwoLocal (M.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨R, hR, hR2, rfl⟩ := hM
  refine ⟨R.map (MulAut.conj g).toMonoidHom, ?_, hR2.map _, ?_⟩
  · intro h
    exact hR ((Subgroup.map_eq_bot_iff_of_injective R (MulAut.conj g).injective).1 h)
  · exact Subgroup.map_equiv_normalizer_eq R (MulAut.conj g)

theorem exists_maximal_isPGroup [Finite G] {p : ℕ} {M B : Subgroup G} (hB : IsPGroup p B)
    (hBM : B ≤ M) :
    ∃ P : Subgroup G, P ≤ M ∧ IsPGroup p P ∧ B ≤ P ∧
      ∀ S : Subgroup G, S ≤ M → IsPGroup p S → P ≤ S → S = P := by
  have hfin : {S : Subgroup G | S ≤ M ∧ IsPGroup p S ∧ B ≤ S}.Finite := Set.toFinite _
  obtain ⟨P, hP, hmax⟩ := hfin.exists_maximal ⟨B, hBM, hB, le_rfl⟩
  exact ⟨P, hP.1, hP.2.1, hP.2.2, fun S hSM hSp hPS =>
    le_antisymm (hmax ⟨hSM, hSp, hP.2.2.trans hPS⟩ hPS) hPS⟩

theorem eq_of_isPGroup_of_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {P M : Subgroup G}
    (hPM : P ≤ M) (hmax : ∀ S : Subgroup G, S ≤ M → IsPGroup p S → P ≤ S → S = P)
    (hN : Subgroup.normalizer (P : Set G) ≤ M) {S : Subgroup G} (hS : IsPGroup p S)
    (hPS : P ≤ S) : S = P := by
  by_contra hne
  have hlt : P.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hne (le_antisymm (Subgroup.subgroupOf_eq_top.1 h) hPS)
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  obtain ⟨s, hs, hsn⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hsN : (s : G) ∈ Subgroup.normalizer (P : Set G) := by
    have := Subgroup.subgroupOf_normalizer_eq hPS
    rw [← Subgroup.mem_subgroupOf, this]
    exact hs
  have hsM : (s : G) ∈ M := hN hsN
  have hS' : P ⊔ Subgroup.zpowers (s : G) ≤ S :=
    sup_le hPS ((Subgroup.zpowers_le).2 s.2)
  have := hmax _ (sup_le hPM ((Subgroup.zpowers_le).2 hsM)) (hS.to_le hS') le_sup_left
  apply hsn
  rw [Subgroup.mem_subgroupOf]
  have h2 : (s : G) ∈ P ⊔ Subgroup.zpowers (s : G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rwa [this] at h2

theorem normalizer_le_of_eligible {p : ℕ} [Fact p.Prime] [Finite G] {P M B Q : Subgroup G}
    {θ : Subgroup G → Subgroup G}
    (hNP : ∀ R : Subgroup G, IsPGroup p R → 2 ≤ pRank p R →
      ∃ U : Subgroup G, U ≤ R ∧ IsPPlane p U ∧ R ≤ Subgroup.normalizer (U : Set G))
    (hPp : IsPGroup p P) (hPM : P ≤ M) (hB : IsElemAbelian p B) (hBP : B ≤ P)
    (hB3 : p ^ 3 ≤ Nat.card B) (hQP : Q ≤ P) (hQ2 : 2 ≤ pRank p Q)
    (hQ3 : 3 ≤ pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))))
    (hθ : ∀ D : Subgroup G, IsPPlane p D → IsPGroup 2 (θ D) ∧
      (∀ g : G, θ (GLBConj g D) = GLBConj g (θ D)) ∧
      (D ≤ M → IsTwoConnectedIn p M D B → pCoreOf 2 M ≤ θ D ∧ θ D ≤ M ∧
        ∀ T : Subgroup G, pCoreOf 2 M ≤ T → T ≤ θ D → Subgroup.normalizer (T : Set G) ≤ M)) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hQp : IsPGroup p Q := hPp.to_le hQP
  obtain ⟨D, hDQ, hD, hDN⟩ := hNP Q hQp hQ2
  have hXP : Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G)) ≤ P := sup_le hQP inf_le_left
  have hXp : IsPGroup p ↥(Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))) := hPp.to_le hXP
  have hP2 : 2 ≤ pRank p P := by
    obtain ⟨j, hj⟩ := exists_card_eq_pow (hPp.to_le hBP)
    have hj3 : 3 ≤ j := by
      rw [hj] at hB3
      exact (Nat.pow_le_pow_iff_right hp1).1 hB3
    have := CFSG.SectionRank.le_pRank hp1 hBP hB hj
    omega
  obtain ⟨U, hUP, hU, hUN⟩ := hNP P hPp hP2
  have hconn : ∀ D' : Subgroup G, D' ≤ Q → IsPPlane p D' →
      Q ≤ Subgroup.normalizer (D' : Set G) → IsTwoConnectedIn p M D' B := by
    intro D' hD'Q hD' hD'N
    have hXN : Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G)) ≤ Subgroup.normalizer (D' : Set G) := by
      refine sup_le hD'N fun c hc => ?_
      have hcD : c ∈ Subgroup.centralizer (D' : Set G) :=
        Subgroup.centralizer_le (by exact_mod_cast hD'Q) hc.2
      exact Subgroup.centralizer_le_normalizer _ hcD
    obtain ⟨F, hFX, hFel, hFcard⟩ := CFSG.SectionRank.exists_pRank (p := p) hp1
      (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G)))
    have hF3 : p ^ 3 ≤ Nat.card F := by
      rw [hFcard]; exact Nat.pow_le_pow_right hp.pos hQ3
    obtain ⟨E, hEX, hEel, hD'E, hE3⟩ := exists_elemAbelian_above_plane hXp hD'
      (hD'Q.trans le_sup_left) hXN hFel hFX hF3
    have hEP : E ≤ P := hEX.trans hXP
    have hEnc : IsNoncyclicElemAbelianIn p P E :=
      ⟨hEP, hEel, not_isCyclic_of_isElemAbelian hEel
        (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hE3)⟩
    have hD'nc : IsNoncyclicElemAbelianIn p P D' :=
      ⟨(hD'Q.trans hQP), hD'.1, not_isCyclic_of_isElemAbelian hD'.1 (hD'.2 ▸ le_rfl)⟩
    have hEB : IsTwoConnectedIn p P E B :=
      isTwoConnectedIn_of_rank_three' hPp hU hUP hUN hEel hEP hE3 hB hBP hB3
    exact ((isTwoConnectedIn_of_le hD'nc hEnc hD'E).trans' hEB).mono' hPM
  have hDM : D ≤ M := hDQ.trans (hQP.trans hPM)
  have hO : ∀ y ∈ Subgroup.normalizer (Q : Set G), pCoreOf 2 M ≤ θ (GLBConj y D) := by
    intro y hy
    have hD' := isPPlane_gLBConj y hD
    have hD'Q : GLBConj y D ≤ Q :=
      (gLBConj_mono y hDQ).trans (gLBConj_eq_of_mem_normalizer hy).le
    have hD'N := le_normalizer_gLBConj hy hDN
    exact ((hθ _ hD').2.2 (hD'Q.trans (hQP.trans hPM)) (hconn _ hD'Q hD' hD'N)).1
  have hnorm : ∀ T : Subgroup G, pCoreOf 2 M ≤ T → T ≤ θ D →
      Subgroup.normalizer (T : Set G) ≤ M := fun T h1 h2 =>
    ((hθ D hD).2.2 hDM (hconn D hDQ hD hDN)).2.2 T h1 h2
  exact normalizer_le_of_equivariant hD (fun D' hD' g => (hθ D' hD').2.1 g) hO hnorm

theorem glaWeakCoreLocal_of_theta {p : ℕ} [Fact p.Prime] [Finite G] {B M : Subgroup G} {m : ℕ}
    (hm : 4 ≤ m)
    (hNP : ∀ R : Subgroup G, IsPGroup p R → 2 ≤ pRank p R →
      ∃ U : Subgroup G, U ≤ R ∧ IsPPlane p U ∧ R ≤ Subgroup.normalizer (U : Set G))
    (hB : IsElemAbelian p B) (hBcard : Nat.card B = p ^ m) (hBM : B ≤ M) (hM : IsTwoLocal M)
    {θ : Subgroup G → Subgroup G}
    (hθ : ∀ D : Subgroup G, IsPPlane p D → IsPGroup 2 (θ D) ∧
      (∀ g : G, θ (GLBConj g D) = GLBConj g (θ D)) ∧
      (D ≤ M → IsTwoConnectedIn p M D B → pCoreOf 2 M ≤ θ D ∧ θ D ≤ M ∧
        ∀ T : Subgroup G, pCoreOf 2 M ≤ T → T ≤ θ D → Subgroup.normalizer (T : Set G) ≤ M)) :
    GLAWeakCoreLocal G p := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hBp : IsPGroup p B := IsPGroup.of_card hBcard
  have hB3 : p ^ 3 ≤ Nat.card B := by
    rw [hBcard]; exact Nat.pow_le_pow_right hp.pos (by omega)
  obtain ⟨P, hPM, hPp, hBP, hmax⟩ := exists_maximal_isPGroup hBp hBM
  have hrankP : m ≤ pRank p P := CFSG.SectionRank.le_pRank hp1 hBP hB hBcard
  have hkey : ∀ Q : Subgroup G, Q ≤ P → 2 ≤ pRank p Q →
      3 ≤ pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))) →
        Subgroup.normalizer (Q : Set G) ≤ M := fun Q hQP h2 h3 =>
    normalizer_le_of_eligible hNP hPp hPM hB hBP hB3 hQP h2 h3 hθ
  have hNP' : Subgroup.normalizer (P : Set G) ≤ M := by
    refine hkey P le_rfl (by omega) ?_
    rw [sup_eq_left.2 inf_le_left]
    omega
  have hSyl : ∀ S : Subgroup G, IsPGroup p S → P ≤ S → S = P := fun S hS hPS =>
    eq_of_isPGroup_of_normalizer_le hPM hmax hNP' hS hPS
  have hwc : GLAWeakCore p P ≤ M := by
    refine sSup_le ?_
    rintro _ ⟨Q, hQP, h2, h3, rfl⟩
    exact hkey Q hQP h2 h3
  refine ⟨le_trans (by omega) (CFSG.SectionRank.le_pRank hp1 le_top hB hBcard), fun P' => ?_⟩
  let S0 : Sylow p G :=
    { toSubgroup := P, isPGroup' := hPp, is_maximal' := fun {Q} hQ hPQ => hSyl Q hQ hPQ }
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S0 P'
  have hP' : (P' : Subgroup G) = P.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  refine ⟨M.map (MulAut.conj g).toMonoidHom, isTwoLocal_map_conj hM g, ?_⟩
  rw [hP', glaWeakCore_map_conj hp1 g P]
  exact Subgroup.map_mono hwc

theorem theoremB_of_theoremOne_theoremTwo (h1 : TheoremOne) (h2 : TheoremTwo)
    (hNP : NormalPlaneLemma) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → ∀ m : ℕ, 4 ≤ m →
        (∀ q ∈ GLABeta (m + 1) G, GLAWeakCoreLocal G q) →
          ∀ p ∈ GLABeta m G, GLAWeakCoreLocal G p ∨ GLADeltaZero G p := by
  intro G _ _ _ hnonab hK hchar he m hm ha p hp
  by_cases hΔ : GLADeltaZero G p
  · exact Or.inr hΔ
  by_cases hgt : m < GLATwoLocalRank p G
  · exact Or.inl (ha p ⟨hp.1, hp.2.1, hp.2.2.1, hgt⟩)
  have hrank : GLATwoLocalRank p G = m := le_antisymm (not_lt.1 hgt) hp.2.2.2
  obtain ⟨B, hBmax, M, hM, hΛ, hΓ⟩ := h1 G hnonab hK hchar he m hm ha p hp hrank hΔ
  rcases h2 G hnonab hK hchar he m hm ha p hp hrank hΔ B M hBmax hM hΛ hΓ with h | ⟨θ, hθ⟩
  · exact h
  · have : Fact p.Prime := ⟨hp.1⟩
    have hp1 : 1 < p := hp.1.one_lt
    have hB : IsElemAbelian p B := hBmax.1.1
    have hBcard : Nat.card B = p ^ m := hrank ▸ hBmax.1.2.1
    have h3 : 3 ≤ pRank p B := le_trans (by omega) (CFSG.SectionRank.le_pRank hp1 le_rfl hB hBcard)
    have hBM : B ≤ M :=
      Subgroup.le_normalizer.trans ((le_sSup ⟨B, le_rfl, h3, rfl⟩ : _ ≤ GLBCore p 3 B).trans hΓ)
    exact Or.inl (glaWeakCoreLocal_of_theta hm (fun R hR hR2 => hNP p hp.1 hp.2.1 G R hR hR2) hB
      hBcard hBM hM.1 hθ)

theorem theoremB_holds (h1 : TheoremOne) (h2 : TheoremTwo) (hNP : NormalPlaneLemma) : TheoremB :=
  theoremB_of_theoremOne_theoremTwo h1 h2 hNP

end CFSG.LocalAnalysis.GLTheoremB
