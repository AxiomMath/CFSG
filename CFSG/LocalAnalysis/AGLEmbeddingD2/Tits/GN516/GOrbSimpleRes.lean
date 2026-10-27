module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleConcl
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbReduceBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdge

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem gOrbConclS_of_residualGraph {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hL : IsSimpleGroup ↥L) (hG : ResidualGraph ↥L) (hRN : R ≤ Subgroup.normalizer (L : Set Y))
    (hR2 : IsPGroup 2 R) (hSyl : IsSylowTwoOf (R ⊓ L) L) (hMin : IsMinOverBorel L (R ⊓ L) P)
    (hnP : ¬ R ≤ Subgroup.normalizer (P : Set Y)) : GOrbConclS R P := by
  have hι : Function.Injective L.subtype := Subgroup.subtype_injective L
  have hLtop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup ↥L, T = (R ⊓ L).subgroupOf L := ⟨_, rfl⟩
  obtain ⟨Pl, hPldef⟩ : ∃ Pl : Subgroup ↥L, Pl = P.subgroupOf L := ⟨_, rfl⟩
  have hTmap : T.map L.subtype = R ⊓ L := by
    rw [hTdef, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hPmap : Pl.map L.subtype = P := by
    rw [hPldef, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hMin.1
  have hTsyl : IsSylowTwoOf T ⊤ := by
    refine (GOrbReduce.isSylowTwoOf_map_iff hι).1 ?_
    rw [hTmap, hLtop]
    exact hSyl
  have hPmin : IsMinOverBorel (⊤ : Subgroup ↥L) T Pl := by
    refine (GOrbReduce.isMinOverBorel_map_iff hι).1 ?_
    rw [hTmap, hLtop, hPmap]
    exact hMin
  have hNlt : Subgroup.normalizer (T : Set ↥L) < Pl := by
    have h := hPmin.2.1
    rwa [top_inf_eq] at h
  have hPL_ne : P ≠ L := fun e => hnP (by rw [e]; exact hRN)
  have hPl_ne_top : Pl ≠ ⊤ := by
    intro e
    apply hPL_ne
    rw [← hPmap, e, hLtop]
  rcases hG T hTsyl with ⟨P₁, P₂, h⟩ | hcoat
  ·
    have hPlN : Pl = P₁ ∨ Pl = P₂ := by
      rcases h.hover Pl hNlt.le with e | e | e | e
      · exact absurd e hNlt.ne'
      · exact Or.inl e
      · exact Or.inr e
      · exact absurd e hPl_ne_top
    have hsup : P₁ ⊔ P₂ = ⊤ := by
      have hN1 := h.lt₁
      have hN2 := h.lt₂
      rcases h.hover (P₁ ⊔ P₂) (hN1.le.trans le_sup_left) with e | e | e | e
      · exact absurd (le_sup_left.trans e.le) (not_le_of_gt hN1)
      · have hP21 : P₂ ≤ P₁ := le_sup_right.trans e.le
        rcases h.atom₁ P₂ hN2.le hP21 with e2 | e2
        · exact absurd e2 hN2.ne'
        · exact absurd e2.symm h.ne
      · have hP12 : P₁ ≤ P₂ := le_sup_left.trans e.le
        rcases h.atom₂ P₁ hN1.le hP12 with e2 | e2
        · exact absurd e2 hN1.ne'
        · exact absurd e2 h.ne
      · exact e
    obtain ⟨r, hr, hrP⟩ : ∃ r ∈ R, r ∉ Subgroup.normalizer (P : Set Y) := by
      by_contra hcon
      exact hnP fun r hr => by_contra fun hn => hcon ⟨r, hr, hn⟩
    have hrL : r ∈ Subgroup.normalizer (L : Set Y) := hRN hr
    have hrS : r ∈ Subgroup.normalizer ((R ⊓ L : Subgroup Y) : Set Y) :=
      CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.mem_normalizer_inf hRN hr
    have hAL : B6.conjSub r P ≤ L := by
      calc B6.conjSub r P ≤ B6.conjSub r L := (B6.conjSub r).monotone hMin.1
        _ = L := B6.conjSub_eq_self hrL
    have hAmin : IsMinOverBorel L (R ⊓ L) (B6.conjSub r P) :=
      CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.isMinOverBorel_conjSub hrL hrS hMin
    obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup ↥L, Q = (B6.conjSub r P).subgroupOf L := ⟨_, rfl⟩
    have hQmap : Q.map L.subtype = B6.conjSub r P := by
      rw [hQdef, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 hAL
    have hQmin : IsMinOverBorel (⊤ : Subgroup ↥L) T Q := by
      refine (GOrbReduce.isMinOverBorel_map_iff hι).1 ?_
      rw [hTmap, hLtop, hQmap]
      exact hAmin
    have hNQ : Subgroup.normalizer (T : Set ↥L) < Q := by
      have h' := hQmin.2.1
      rwa [top_inf_eq] at h'
    have hQ_ne_top : Q ≠ ⊤ := by
      intro e
      apply hPL_ne
      have h1 : B6.conjSub r P = L := by rw [← hQmap, e, hLtop]
      have h2 : B6.conjSub r P = B6.conjSub r L := by rw [h1, B6.conjSub_eq_self hrL]
      exact (B6.conjSub r).injective h2
    have hQnode : Q = P₁ ∨ Q = P₂ := by
      rcases h.hover Q hNQ.le with e | e | e | e
      · exact absurd e hNQ.ne'
      · exact Or.inl e
      · exact Or.inr e
      · exact absurd e hQ_ne_top
    have hPlQ : Pl ≠ Q := by
      intro e
      apply hrP
      have hEq : B6.conjSub r P = P := by rw [← hQmap, ← e, hPmap]
      have h2 : B6.conjSub r⁻¹ P = P := by
        calc B6.conjSub r⁻¹ P = B6.conjSub r⁻¹ (B6.conjSub r P) := by rw [hEq]
          _ = B6.conjSub (r⁻¹ * r) P := (B6.conjSub_mul _ _ _).symm
          _ = P := by rw [inv_mul_cancel, B6.conjSub_one]
      exact B6.mem_normalizer_of_conjSub_le hEq.le h2.le
    have hAconj : B6.conjSub r P ≤ conjClosure P R := by
      intro x hx
      rw [B6.mem_conjSub] at hx
      have h1 := mem_conjClosure hr hx
      have e : r * (r⁻¹ * x * r) * r⁻¹ = x := by group
      rwa [e] at h1
    have hjoin : Pl ⊔ Q = ⊤ := by
      rcases hPlN with e1 | e1 <;> rcases hQnode with e2 | e2
      · exact absurd (e1.trans e2.symm) hPlQ
      · rw [e1, e2]; exact hsup
      · rw [e1, e2, sup_comm]; exact hsup
      · exact absurd (e1.trans e2.symm) hPlQ
    have hCL : conjClosure P R = L := by
      apply le_antisymm
      · apply conjClosure_le
        intro k hk z hz
        exact (Subgroup.mem_normalizer_iff.1 (hRN hk) z).1 (hMin.1 hz)
      · have h1 : (Pl ⊔ Q).map L.subtype = L := by rw [hjoin, hLtop]
        rw [Subgroup.map_sup, hPmap, hQmap] at h1
        exact h1.symm.le.trans (sup_le (le_conjClosure P R) hAconj)
    have hnonab : ∃ Q' : Subgroup ↥L, IsPGroup 2 Q' ∧ ∃ a ∈ Q', ∃ b ∈ Q', a * b ≠ b * a := by
      refine ⟨T, h.sylow.2.1, ?_⟩
      by_contra hcon
      push_neg at hcon
      have hTP₁ : T ≤ P₁ := Subgroup.le_normalizer.trans h.lt₁.le
      have hsyl1 : IsSylowTwoOf T P₁ := by
        refine ⟨hTP₁, h.sylow.2.1, ?_⟩
        have h1 : T.relIndex P₁ * P₁.index = T.index := Subgroup.relIndex_mul_index hTP₁
        have h2 : ¬ 2 ∣ T.index := by
          rw [← Subgroup.relIndex_top_right]
          exact h.sylow.2.2
        have hdvd : T.relIndex P₁ ∣ T.index := ⟨P₁.index, h1.symm⟩
        exact fun hd => h2 (hd.trans hdvd)
      have hcore : pCoreOf 2 P₁ ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hsyl1
      have hcent : T ≤ Subgroup.centralizer (pCoreOf 2 P₁ : Set ↥L) := by
        intro x hx
        exact Subgroup.mem_centralizer_iff.2 fun y hy => hcon y (hcore hy) x hx
      have hTcore : T ≤ pCoreOf 2 P₁ := by
        intro x hx
        exact h.ct₁ (Subgroup.mem_inf.2 ⟨hTP₁ hx, hcent hx⟩)
      have hP1N : P₁ ≤ Subgroup.normalizer (T : Set ↥L) := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        rw [le_antisymm hTcore hcore]
        exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P₁
      exact not_le_of_gt h.lt₁ hP1N
    unfold GOrbConclS
    right
    right
    rw [hCL]
    exact CFSG.AGLEmbeddingD2.Tits.GN516.Edge.quasisimpleModTwoNonab_of_simple hL hnonab
  ·
    exfalso
    have hPl : Pl = ⊤ := hcoat.2 Pl hNlt
    apply hnP
    have hPL : P = L := by rw [← hPmap, hPl, hLtop]
    rw [hPL]
    exact hRN

end CFSG.AGLEmbeddingD2.Tits.GN516
