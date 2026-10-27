module

public import CFSG.GH74.GLS.C3.Layer1.St1RigStep

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpRigid

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.C3.Layer1.PumpCalc
open scoped commutatorElement

section Ord

variable {G : Type} [Group G] [Finite G]

@[expose] def IsGilmanMax (x : G) (K : Subgroup G) : Prop :=
  ∀ (x' : G) (K' : Subgroup G), LongPumpUp 2 x K x' K' →
    pRank 2 ↥(CxK x' K') < pRank 2 ↥(CxK x K) ∨
      (pRank 2 ↥(CxK x' K') = pRank 2 ↥(CxK x K) ∧ sylVal x' K' ≤ sylVal x K)

omit [Finite G] in
theorem LongPumpUp.refl' {x : G} {K : Subgroup G} (h : IsILo 2 x K) : LongPumpUp 2 x K x K :=
  ⟨h, Relation.ReflTransGen.refl⟩

omit [Finite G] in
theorem LongPumpUp.single' {x y : G} {K L : Subgroup G} (h : PumpUpLT 2 x K y L) :
    LongPumpUp 2 x K y L :=
  ⟨h.1, Relation.ReflTransGen.single h⟩

omit [Finite G] in
theorem LongPumpUp.trans' {x y z : G} {K L M : Subgroup G} (h₁ : LongPumpUp 2 x K y L)
    (h₂ : LongPumpUp 2 y L z M) : LongPumpUp 2 x K z M :=
  ⟨h₁.1, h₁.2.trans h₂.2⟩

omit [Finite G] in
theorem LongPumpUp.isILo_right {x y : G} {K L : Subgroup G} (h : LongPumpUp 2 x K y L) :
    IsILo 2 y L := by
  obtain ⟨h1, h2⟩ := h
  cases h2 with
  | refl => exact h1
  | tail _ hstep => exact hstep.2.1

theorem hat_le_of_chain {p q : G × Subgroup G}
    (h : Relation.ReflTransGen (fun a b : G × Subgroup G => PumpUpLT 2 a.1 a.2 b.1 b.2) p q) :
    hatCard p.2 ≤ hatCard q.2 := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (hat_le_of_pumpUpLT hstep)

theorem hat_equiv_of_chain {p q : G × Subgroup G}
    (h : Relation.ReflTransGen (fun a b : G × Subgroup G => PumpUpLT 2 a.1 a.2 b.1 b.2) p q) :
    hatCard q.2 ≤ hatCard p.2 → Nonempty (kBar q.2 ≃* kBar p.2) := by
  induction h with
  | refl => exact fun _ => ⟨MulEquiv.refl _⟩
  | @tail b c hb hstep ih =>
    intro hle
    have hpb : hatCard p.2 ≤ hatCard b.2 := hat_le_of_chain hb
    have hbc : hatCard b.2 ≤ hatCard c.2 := hat_le_of_pumpUpLT hstep
    obtain ⟨e1⟩ := ih (hbc.trans hle)
    obtain ⟨e2⟩ := hat_equiv_of_pumpUpLT hstep (hle.trans hpb)
    exact ⟨e2.trans e1⟩

theorem exists_rigid {x : G} {K : Subgroup G} (h : IsILo 2 x K) :
    ∃ (x' : G) (K' : Subgroup G), LongPumpUp 2 x K x' K' ∧ IsPRigid 2 x' K' := by
  classical
  let S := {p : G × Subgroup G // LongPumpUp 2 x K p.1 p.2}
  have : Nonempty S := ⟨⟨(x, K), LongPumpUp.refl' h⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_max (fun p : S => hatCard p.1.2)
  refine ⟨p.1.1, p.1.2, p.2, p.2.isILo_right, fun x'' K'' hlong => ?_⟩
  have hle : hatCard K'' ≤ hatCard p.1.2 := hp ⟨(x'', K''), LongPumpUp.trans' p.2 hlong⟩
  exact hat_equiv_of_chain hlong.2 hle

theorem exists_rigid_gilman {x : G} {K : Subgroup G} (hrig : IsPRigid 2 x K) :
    ∃ (x' : G) (K' : Subgroup G), LongPumpUp 2 x K x' K' ∧ IsPRigid 2 x' K' ∧
      IsGilmanMax x' K' := by
  classical
  let S := {p : G × Subgroup G // LongPumpUp 2 x K p.1 p.2}
  have : Nonempty S := ⟨⟨(x, K), LongPumpUp.refl' hrig.1⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_max
    (fun p : S => toLex (pRank 2 ↥(CxK p.1.1 p.1.2), sylVal p.1.1 p.1.2))
  refine ⟨p.1.1, p.1.2, p.2, ⟨p.2.isILo_right, fun x'' K'' hlong => ?_⟩, fun x'' K'' hlong => ?_⟩
  · obtain ⟨e1⟩ := hrig.2 p.1.1 p.1.2 p.2
    obtain ⟨e2⟩ := hrig.2 x'' K'' (LongPumpUp.trans' p.2 hlong)
    exact ⟨e2.trans e1.symm⟩
  · have h1 := hp ⟨(x'', K''), LongPumpUp.trans' p.2 hlong⟩
    rw [Prod.Lex.le_iff] at h1
    exact h1

theorem mem_CxK_of_centralizes {t q : G} {K' : Subgroup G}
    (hK' : IsPCompIn 2 (centralizer ({t} : Set G)) K') (hq : q ∈ centralizer ({t} : Set G))
    (h : ∀ w ∈ bar t K', sbar q hq * w * (sbar q hq)⁻¹ = w) : q ∈ CxK t K' := by
  refine Subgroup.mem_inf.mpr ⟨hq, mem_centralizerSection_of_map_eq hK'.1
    (isPCompIn_two_iff.mp hK').2 hq (fun m hm => ?_)⟩
  have := h (barMk _ m) ⟨m, hm, rfl⟩
  simpa [sbar, map_mul, map_inv] using this

theorem centralizes_of_mem_CxK {t q : G} {K' : Subgroup G}
    (hK' : IsPCompIn 2 (centralizer ({t} : Set G)) K') (hq : q ∈ centralizer ({t} : Set G))
    (hqC : q ∈ CxK t K') : ∀ w ∈ bar t K', sbar q hq * w * (sbar q hq)⁻¹ = w := by
  rintro _ ⟨m, hm, rfl⟩
  have := map_eq_of_mem_cSec hK' hq (Subgroup.mem_inf.mp hqC).2 m hm
  simpa [sbar, map_mul, map_inv] using this

theorem pRank_of_isSylowOf {Q C : Subgroup G} (h : IsSylowOf 2 Q C) :
    pRank 2 ↥Q = pRank 2 ↥C := by
  obtain ⟨T, rfl⟩ := h
  rw [pRank_two_subgroup_eq_open, pRank_two_subgroup_eq_open]
  exact CFSG.ProperTwoGeneratedCore.sylow_image_two_rank_eq C T

theorem isTwoTerminal_of_noDiag_of_immediate {x : G} {K : Subgroup G}
    (hILo : IsILo 2 x K)
    (hrig_imm : ∀ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' →
      Nonempty (kBar K' ≃* kBar K))
    (hgm_imm : ∀ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' →
      pRank 2 ↥(CxK t K') < pRank 2 ↥(CxK x K) ∨
        (pRank 2 ↥(CxK t K') = pRank 2 ↥(CxK x K) ∧ sylVal t K' ≤ sylVal x K))
    (hnd_imm : ∀ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' →
      x ∈ normalizer (K' : Set G)) :
    IsTwoTerminal x K := by
  refine ⟨hILo, fun x' K' hlt => ⟨hnd_imm x' K' hlt, ?_⟩, ?_⟩
  · exact hrig_imm x' K' hlt
  · intro Q hQ x' K' hlt hx'Q hx'c
    have hxY : x ∈ centralizer ({x'} : Set G) := mem_centralizer_symm hlt.2.2.1
    obtain ⟨e⟩ := hrig_imm x' K' hlt
    have hle : hatCard K' ≤ hatCard K := (Nat.card_congr e.toEquiv).le
    obtain ⟨Λ, hΛ, hK'c, -, -, hcent, hcases⟩ := rigid_step hlt hxY hle
    have hvert : bar x' Λ = bar x' K' :=
      (hcases.resolve_right (fun h => h.1 (hnd_imm x' K' hlt))).2
    have hQle : Q ≤ CxK x' K' := by
      intro q hq
      have hqY : q ∈ centralizer ({x'} : Set G) :=
        mem_centralizer_singleton_iff.mpr (hx'c q hq).symm
      have hqC : q ∈ CxK x K := hQ.le hq
      refine mem_CxK_of_centralizes hK'c hqY (fun w hw => ?_)
      rw [← hvert] at hw
      exact hcent q hqY hqC w hw
    have hQcard : Nat.card ↥Q = 2 ^ sylVal x K := hQ.card_eq
    have hrkQ : pRank 2 ↥Q = pRank 2 ↥(CxK x K) := pRank_of_isSylowOf hQ
    have hQrk : pRank 2 ↥Q ≤ pRank 2 ↥(CxK x' K') := by
      rw [pRank_two_subgroup_eq_open, pRank_two_subgroup_eq_open]
      exact CFSG.SectionRank.pRank_mono Nat.one_lt_two hQle
    rcases hgm_imm x' K' hlt with hlt' | ⟨-, hsyl⟩
    · exfalso
      omega
    · have hdvd : Nat.card ↥Q ∣ Nat.card ↥(CxK x' K') := Subgroup.card_dvd_of_le hQle
      rw [hQcard] at hdvd
      have hne : Nat.card ↥(CxK x' K') ≠ 0 := Nat.card_pos.ne'
      have hge : sylVal x K ≤ sylVal x' K' :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
      refine isSylowOf_of_card hQle ?_
      rw [hQcard]
      exact congrArg (2 ^ ·) (le_antisymm hge hsyl)

theorem isTwoTerminal_of_noDiag {x : G} {K : Subgroup G} (hrig : IsPRigid 2 x K)
    (hgm : IsGilmanMax x K)
    (hnd : ∀ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' → x ∈ normalizer (K' : Set G)) :
    IsTwoTerminal x K := by
  refine isTwoTerminal_of_noDiag_of_immediate hrig.1 ?_ ?_ hnd
  · intro t K' hlt
    exact hrig.2 t K' (LongPumpUp.single' hlt)
  · intro t K' hlt
    exact hgm t K' (LongPumpUp.single' hlt)

theorem exists_twoTerminal_of_noDiag
    (hND : ∀ (x : G) (K : Subgroup G), IsPRigid 2 x K → IsGilmanMax x K →
      ∀ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' → x ∈ normalizer (K' : Set G))
    {x : G} {K : Subgroup G} (h : IsILo 2 x K) :
    ∃ (x' : G) (K' : Subgroup G), LongPumpUp 2 x K x' K' ∧ IsTwoTerminal x' K' := by
  obtain ⟨y, L, hyL, hrigL⟩ := exists_rigid h
  obtain ⟨z, M, hzM, hrigM, hgmM⟩ := exists_rigid_gilman hrigL
  exact ⟨z, M, LongPumpUp.trans' hyL hzM,
    isTwoTerminal_of_noDiag hrigM hgmM (hND z M hrigM hgmM)⟩

end Ord

end CFSG.GH74.GLS.C3.Layer1.PumpRigid
