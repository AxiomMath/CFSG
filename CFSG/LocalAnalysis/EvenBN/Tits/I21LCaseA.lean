module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCaseAMod
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCaseAGrp
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6Grp
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LThmDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section Transport

variable {Y : Type*} [Group Y] [Finite Y]

theorem caseA_pgl_transport (N : Subgroup Y) [N.Normal] (J : Subgroup Y) [J.Normal]
    (hJN : J ⊓ N = ⊥) (e : J ≃* alternatingGroup (Fin 6)) (hC : centralizer (J : Set Y) = ⊥)
    {L : Subgroup (Y ⧸ N)} (hLJ : ∀ j ∈ J, (QuotientGroup.mk j : Y ⧸ N) ∈ L)
    (hLP : IsPSLTwo L 9) {t : Y} (hpgl : PGLTwoSquareOuter L (QuotientGroup.mk t : Y ⧸ N)) :
    PGLTwoSquareOuter J t := by
  obtain ⟨-, -, F, instF, instFin, q, hq, hcard, eL, g, hg, hcompat⟩ := hpgl
  let f : J →* L := ((QuotientGroup.mk' N).comp J.subtype).codRestrict L fun j => hLJ j j.2
  have hfapply : ∀ j : J, ((f j : L) : Y ⧸ N) = QuotientGroup.mk (j : Y) := fun j => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h1 : (QuotientGroup.mk (j : Y) : Y ⧸ N) = 1 := by
      rw [← hfapply, hj]
      rfl
    have h2 : (j : Y) ∈ J ⊓ N := ⟨j.2, (QuotientGroup.eq_one_iff _).1 h1⟩
    rw [hJN, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  obtain ⟨eA⟩ := a6grp_equiv_A6 hLP
  have hJ360 : Nat.card J = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact a6grp_card_A6
  have hL360 : Nat.card L = 360 := by
    rw [Nat.card_congr eA.toEquiv]
    exact a6grp_card_A6
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [hJ360, hL360])
  let φ : J ≃* L := MulEquiv.ofBijective f hbij
  unfold PGLTwoSquareOuter
  refine ⟨inferInstance, hC, F, instF, instFin, q, hq, hcard, φ.trans eL, g, hg, ?_⟩
  intro a b hab
  refine hcompat (φ a) (φ b) ?_
  show ((f b : L) : Y ⧸ N) = (QuotientGroup.mk t : Y ⧸ N) * ((f a : L) : Y ⧸ N) *
    (QuotientGroup.mk t : Y ⧸ N)⁻¹
  rw [hfapply, hfapply, hab]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

end Transport

section P1P2

variable {Y : Type*} [Group Y] [Finite Y]

theorem caseA_p1_p2 (J Y₀ : Subgroup Y) (hJY : J ≤ Y₀) {t : Y} (htY : t ∉ Y₀)
    (h4 : J.index ≤ 4) (r : Y → ℕ) (hout : ∀ g : Y, g * g = 1 → g ∉ Y₀ → r g = 4)
    (hin : ∀ g ∈ Y₀, g ≠ 1 → 2 ≤ r g)
    (hJ : ∀ j ∈ J, j * j = 1 → j ≠ 1 → r j = 4) :
    (∀ j : Y, j * j = 1 → j ≠ 1 → 2 ≤ r j) ∧
      (∀ F : Subgroup Y, (∀ f ∈ F, f * f = 1) → Nat.card F = 4 →
        ∃ j ∈ F, j ≠ 1 ∧ 4 ≤ r j) := by
  refine ⟨fun j hj2 hj1 => ?_, fun F hF hF4 => ?_⟩
  · by_cases hjY : j ∈ Y₀
    · exact hin j hjY hj1
    · rw [hout j hj2 hjY]
      norm_num
  · by_cases hFY : F ≤ Y₀
    · have hY₀ne : Y₀ ≠ ⊤ := fun h => htY (h ▸ Subgroup.mem_top t)
      have hY₀idx : 2 ≤ Y₀.index := Subgroup.one_lt_index_of_ne_top hY₀ne
      have hrel := Subgroup.relIndex_mul_index hJY
      have hJidx0 : J.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hrel0 : J.relIndex Y₀ ≠ 0 := fun h => hJidx0 (by rw [← hrel, h, zero_mul])
      have hrel2 : J.relIndex Y₀ ≤ 2 := by
        by_contra hlt
        have : 3 * 2 ≤ J.relIndex Y₀ * Y₀.index := Nat.mul_le_mul (by omega) hY₀idx
        omega
      have hFrel : J.relIndex F ≤ 2 := (Subgroup.relIndex_le_of_le_right hFY hrel0).trans hrel2
      have hcard := Subgroup.relIndex_mul_card J F
      rw [hF4] at hcard
      have hJF : J ⊓ F ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcard
        omega
      obtain ⟨j, hj1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hJF
      have hj1' : (j : Y) ≠ 1 := fun h => hj1 (Subtype.ext h)
      have hjJ : (j : Y) ∈ J := j.2.1
      have hjF : (j : Y) ∈ F := j.2.2
      refine ⟨j, hjF, hj1', ?_⟩
      rw [hJ j hjJ (hF j hjF) hj1']
    · obtain ⟨f, hfF, hfY⟩ := SetLike.not_le_iff_exists.1 hFY
      have hf1 : f ≠ 1 := fun h => hfY (h ▸ Y₀.one_mem)
      exact ⟨f, hfF, hf1, by rw [hout f (hF f hfF) hfY]⟩

end P1P2

section Cases

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y] [Finite Y]
  (ρ : Y →* (V ≃ₗ[ZMod 2] V)) (t : Y)

variable {ρ t} {u x h : Y}

theorem case_A6 (H : HypYW ρ t u x h)
    (hxO : x ∉ standardComponentOddCore Y)
    (hL : ∃ L : Subgroup (Y ⧸ standardComponentOddCore Y), L.Normal ∧
      centralizer (L : Set (Y ⧸ standardComponentOddCore Y)) = ⊥ ∧ IsPSLTwo L 9 ∧
      (QuotientGroup.mk t : Y ⧸ standardComponentOddCore Y) ∉ L ∧
      (QuotientGroup.mk x : Y ⧸ standardComponentOddCore Y) ∈ L ∧
      (QuotientGroup.mk (u ^ 2) : Y ⧸ standardComponentOddCore Y) ∈ L ∧
      PGLTwoSquareOuter L (QuotientGroup.mk t : Y ⧸ standardComponentOddCore Y)) :
    (Nonempty (normalClosure ({x} : Set Y) ≃* alternatingGroup (Fin 6)) ∧
        PGLTwoSquareOuter (normalClosure ({x} : Set Y)) t) ∧ Thm107P ρ t := by
  obtain ⟨hbot, ⟨e⟩, -, -⟩ := a6_branch_structure H hxO hL
  obtain ⟨hcen, Y₀, hJY, htY, hout, hin, hJrk⟩ := caseA_module H e
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact H.sec.orderOf_t ▸ pow_orderOf_eq_one t
  obtain ⟨L, hLn, -, hLP, htL, hxL, -, hpgl⟩ := hL
  have hLJ : ∀ j ∈ normalClosure ({x} : Set Y),
      (QuotientGroup.mk j : Y ⧸ standardComponentOddCore Y) ∈ L := by
    have hle : normalClosure ({x} : Set Y) ≤
        L.comap (QuotientGroup.mk' (standardComponentOddCore Y)) :=
      normalClosure_le_normal (Set.singleton_subset_iff.2 hxL)
    exact fun j hj => hle hj
  have hC : centralizer ((normalClosure ({x} : Set Y) : Subgroup Y) : Set Y) = ⊥ := by
    rw [eq_bot_iff_forall]
    intro c hc
    exact hcen c fun j hj => (mem_centralizer_iff.1 hc j hj).symm
  have hpglJ := caseA_pgl_transport (standardComponentOddCore Y) (normalClosure ({x} : Set Y))
    hbot e hC hLJ hLP hpgl
  have htJ : t ∉ normalClosure ({x} : Set Y) := fun ht => htL (hLJ t ht)
  obtain ⟨h4, p3, e1, e2⟩ := caseA_group (normalClosure ({x} : Set Y)) e hC ht2 htJ hpglJ
  obtain ⟨p1, p2⟩ := caseA_p1_p2 (normalClosure ({x} : Set Y)) Y₀ hJY htY h4 (fun g => rk (ρ g))
    hout hin hJrk
  exact ⟨⟨⟨e⟩, hpglJ⟩, p1, p2, p3, e1, e2⟩

end Cases

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
