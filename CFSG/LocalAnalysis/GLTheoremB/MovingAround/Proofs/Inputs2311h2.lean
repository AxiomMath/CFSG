module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311h
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311f2
public import CFSG.HardMathSupport.Lang.Proving.SLTwoThreePrime
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Classes
public import CFSG.HardMathSupport.Lang.AnisoE8.Final
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.N2
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Native
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.NormalizerSmall
public import CFSG.HardMathSupport.Lang.AnisoF4.B4ConjEven
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c (UniPlaneGen uniPlaneClosure
  mem_uniPlaneClosure UniSeitzPlanes)

section PlaneCount

open Subgroup CFSG.RankThree.PartOne.SEITZ3

variable {G : Type*} [Group G]

theorem closure_uniCen_eq_top_of_maximal [Finite G] [IsSimpleGroup G] {p e r : ℕ} [Fact p.Prime]
    (M S E' : Subgroup G) (φ : ↥S ≃* (Fin 2 → Multiplicative (ZMod (p ^ e))))
    (hSM : S ≤ M) (hSp : IsPGroup p ↥S) (hSidx : ¬ p ∣ S.index)
    (hE'S : E' ≤ S) (hE'p : ∀ x ∈ E', x ^ p = 1) (hE'c : Nat.card E' = p ^ 2)
    (hmax : ∀ N : Subgroup G, M ≤ N → N = M ∨ N = ⊤)
    (hind : ¬ M.index ≡ 1 [MOD p])
    (hgen : M ≤ closure {k | ∃ x ∈ E', x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1})
    (F : Subgroup G) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    closure {k | ∃ x ∈ F, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤ := by
  have hp : p.Prime := Fact.out
  have hE'ne : E' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE'c
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hMbot : M ≠ ⊥ := fun h => hE'ne (by
    rw [eq_bot_iff]; exact (hE'S.trans hSM).trans h.le)
  have hMtop : M ≠ ⊤ := fun h => hind (by rw [h, index_top])
  have hNM : normalizer (M : Set G) = M := by
    rcases hmax _ (le_normalizer (H := M)) with h | h
    · exact h
    · exfalso
      have hnormal : M.Normal := normalizer_eq_top_iff.1 h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h' | h'
      · exact hMbot h'
      · exact hMtop h'
  have hmain : closure {k | ∃ x ∈ E', x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤ := by
    rcases hmax _ hgen with h | h
    · exfalso
      have hNS : ∀ n ∈ normalizer (S : Set G), n ∈ M := by
        intro n hn
        have hnS : cj S n = S := mem_normalizer_iff_cj.1 hn
        have h1 : cj E' n ≤ S := by
          intro x hx
          have : x ∈ cj S n := cj_le_cj hE'S n hx
          rwa [hnS] at this
        have h2 : cj E' n = E' :=
          plane_unique hp φ h1 hE'S (fun x hx => pow_eq_one_of_mem_cj hE'p hx) hE'p
            (by rw [card_cj]; exact hE'c) hE'c
        have h3 : closure {k | ∃ x ∈ E'.map (MulAut.conj n).toMonoidHom, x ≠ 1 ∧ Commute k x ∧
            ∃ m : ℕ, k ^ (r ^ m) = 1} =
            closure {k | ∃ x ∈ E', x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (r ^ m) = 1} := by
          have h2' : E'.map (MulAut.conj n).toMonoidHom = E' := h2
          rw [h2']
        rw [Inputs2311f.uniClosure_map_conj, h] at h3
        have h4 : cj M n = M := h3
        have h5 := mem_normalizer_iff_cj.2 h4
        rwa [hNM] at h5
      have hmod : Nat.card (G ⧸ M) ≡ Nat.card (MulAction.fixedPoints S (G ⧸ M)) [MOD p] :=
        hSp.card_modEq_card_fixedPoints (G ⧸ M)
      have hfixed_iff : ∀ g : G, ((g : G ⧸ M) ∈ MulAction.fixedPoints S (G ⧸ M)) ↔
          ∀ s ∈ S, g⁻¹ * s * g ∈ M := by
        intro g
        rw [MulAction.mem_fixedPoints]
        have key : ∀ s : ↥S, s • (g : G ⧸ M) = (g : G ⧸ M) ↔ g⁻¹ * (s : G)⁻¹ * g ∈ M := by
          intro s
          rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
          have e : ((s : G) * g)⁻¹ * g = g⁻¹ * (s : G)⁻¹ * g := by group
          rw [e]
        simp only [key]
        constructor
        · intro h s hs
          have h1 := h ⟨s⁻¹, S.inv_mem hs⟩
          have e2 : g⁻¹ * (((⟨s⁻¹, S.inv_mem hs⟩ : ↥S) : G))⁻¹ * g = g⁻¹ * s * g := by
            simp
          rwa [e2] at h1
        · intro h s
          exact h _ (S.inv_mem s.2)
      have hfix : MulAction.fixedPoints S (G ⧸ M) = {((1 : G) : G ⧸ M)} := by
        ext x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        rw [Set.mem_singleton_iff, hfixed_iff, QuotientGroup.eq]
        constructor
        · intro hg
          obtain ⟨m, hmM, hmn⟩ := exists_mem_normalizer_of_conj_le hSM hSp hSidx hg
          have hgm : g * m ∈ M := hNS _ hmn
          have h6 := M.mul_mem hgm (M.inv_mem hmM)
          have h7 : g⁻¹ * 1 = (g * m * (m : G)⁻¹)⁻¹ := by group
          rw [h7]
          exact M.inv_mem (by simpa using h6)
        · intro hg s hs
          have hgM : g ∈ M := by simpa using M.inv_mem hg
          exact M.mul_mem (M.mul_mem (M.inv_mem hgM) (hSM hs)) hgM
      have hcard : Nat.card (MulAction.fixedPoints S (G ⧸ M)) = 1 := by
        rw [hfix]
        exact Nat.card_unique
      rw [hcard] at hmod
      exact hind hmod
    · exact h
  have hFpg : IsPGroup p ↥F := IsPGroup.of_card hFc
  obtain ⟨Q, hQ⟩ := hFpg.exists_le_sylow
  let S₀ : Sylow p G := hSp.toSylow hSidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S₀ Q
  have hQS : (Q : Subgroup G) = cj S c := by
    have h1 : ((c • S₀ : Sylow p G) : Subgroup G) = (Q : Subgroup G) := by rw [hc]
    have hS₀ : ((S₀ : Sylow p G) : Subgroup G) = S := rfl
    rw [← h1, Sylow.coe_subgroup_smul, hS₀]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_cj]
    simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
  have hFS : cj F c⁻¹ ≤ S := by
    intro x hx
    have h1 : x ∈ cj (cj S c) c⁻¹ := cj_le_cj (hQ.trans hQS.le) c⁻¹ hx
    rwa [cj_cj] at h1
  have hF' : cj F c⁻¹ = E' :=
    plane_unique hp φ hFS hE'S (fun x hx => pow_eq_one_of_mem_cj hFp hx) hE'p
      (by rw [card_cj]; exact hFc) hE'c
  have hF'' : F = E'.map (MulAut.conj c).toMonoidHom := by
    have : F = cj E' c := by rw [← hF', cj_inv_cj]
    exact this
  rw [hF'', Inputs2311f.uniClosure_map_conj, hmain]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective

theorem closure_uniCen_eq_top_of_pair [Finite G] [IsSimpleGroup G] {p e r : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hAB : A ⊓ B = ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hpA : p ∣ Nat.card A) (hpB : p ∣ Nat.card B)
    (hshape : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e G)
    (hAr : A ≤ closure {x | x ∈ A ∧ ∃ n : ℕ, x ^ (r ^ n) = 1})
    (hBr : B ≤ closure {x | x ∈ B ∧ ∃ n : ℕ, x ^ (r ^ n) = 1})
    (hmax : ∀ N : Subgroup G, A ⊔ B ≤ N → N = A ⊔ B ∨ N = ⊤)
    (hnd : ¬ p ∣ (A ⊔ B).index) (hmod : ¬ (A ⊔ B).index ≡ 1 [MOD p])
    (F : Subgroup G) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    closure {k | ∃ x ∈ F, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' p hpA
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' p hpB
  have ha₀p : a₀ ^ p = 1 := by rw [← ha₀]; exact pow_orderOf_eq_one a₀
  have hb₀p : b₀ ^ p = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha₀
    exact hp.one_lt.ne ha₀
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb₀
    exact hp.one_lt.ne hb₀
  have hzpa : ∀ a ∈ Subgroup.zpowers a₀, a ^ p = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha₀p, one_zpow]
  have hzpb : ∀ b ∈ Subgroup.zpowers b₀, b ^ p = 1 := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb₀p, one_zpow]
  let Φ := pairHom A B hcomm
  have hΦ : Function.Injective Φ := pairHom_injective hAB hcomm
  let E'₀ : Subgroup (↥A × ↥B) := (Subgroup.zpowers a₀).prod (Subgroup.zpowers b₀)
  let E' : Subgroup G := E'₀.map Φ
  have hE'M : E' ≤ A ⊔ B := by
    rw [← pairHom_range A B hcomm]
    exact Subgroup.map_le_range _ _
  have hE'p : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    have hab : (a, b) ^ p = (a ^ p, b ^ p) := rfl
    rw [← map_pow, hab, hzpa a ha, hzpb b hb]
    exact map_one _
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hΦ]
    have h1 : Nat.card E'₀ = Nat.card (Subgroup.zpowers a₀) * Nat.card (Subgroup.zpowers b₀) :=
      (Nat.card_congr
        (Subgroup.prodEquiv (Subgroup.zpowers a₀) (Subgroup.zpowers b₀)).toEquiv).trans
        (Nat.card_prod _ _)
    rw [h1, Nat.card_zpowers, Nat.card_zpowers, ha₀, hb₀, sq]
  let M : Subgroup G := A ⊔ B
  have hEmp : IsPGroup p ↥(E'.subgroupOf M) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'M).toEquiv, hE'c]
  obtain ⟨Q, hQ⟩ := hEmp.exists_le_sylow
  let S : Subgroup G := (Q : Subgroup ↥M).map M.subtype
  have hSM : S ≤ M := Subgroup.map_subtype_le _
  have hE'S : E' ≤ S := by
    intro x hx
    exact ⟨⟨x, hE'M hx⟩, hQ hx, rfl⟩
  have hSp : IsPGroup p ↥S := Q.isPGroup'.map M.subtype
  have hSidx : ¬ p ∣ S.index := by
    have h1 : S.index = (Q : Subgroup ↥M).index * M.index := Subgroup.index_map_subtype _
    rw [h1]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact Q.not_dvd_index h
    · exact hnd h
  obtain ⟨φ⟩ := hshape S hSp hSidx
  have hb₀E : (b₀ : G) ∈ E' := ⟨(1, b₀), ⟨one_mem _, Subgroup.mem_zpowers b₀⟩, by
    rw [pairHom_apply]; simp⟩
  have ha₀E : (a₀ : G) ∈ E' := ⟨(a₀, 1), ⟨Subgroup.mem_zpowers a₀, one_mem _⟩, by
    rw [pairHom_apply]; simp⟩
  have hgen : M ≤ closure {k | ∃ x ∈ E', x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} := by
    refine sup_le (hAr.trans (closure_mono ?_)) (hBr.trans (closure_mono ?_))
    · rintro x ⟨hxA, n, hn⟩
      exact ⟨b₀, hb₀E, fun h => hb₀1 (Subtype.ext h), hcomm x hxA b₀ b₀.2, n, hn⟩
    · rintro x ⟨hxB, n, hn⟩
      exact ⟨a₀, ha₀E, fun h => ha₀1 (Subtype.ext h), (hcomm a₀ a₀.2 x hxB).symm, n, hn⟩
  exact closure_uniCen_eq_top_of_maximal M S E' φ hSM hSp hSidx hE'S hE'p hE'c hmax hmod hgen F hFp
    hFc

end PlaneCount

section G2

set_option linter.unusedSectionVars false

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.PartOne.SEITZ3

theorem g2UniNative_even (hmax : MaxSL2SL2G2) (X : Type) [Field X] [Finite X]
    [CharP X 2] [IsSimpleGroup (adjointGroup .G2 X)] {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : Nat.card X = 2 ^ m) (hm : 1 ≤ m) (hpq : p ∣ Nat.card X + 1)
    (E₁ : Subgroup (adjointGroup .G2 X)) (hE₁p : ∀ x ∈ E₁, x ^ p = 1)
    (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (2 ^ n) = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL .G2 X) := finite_modGL
  have hq1 : 1 ≤ Nat.card X := Nat.card_pos
  have hq4 : 4 ≤ Nat.card X := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    omega
  have hpq2 : p ∣ Nat.card X ^ 2 - 1 := by
    rw [CFSG.RankThree.PartOne.K128.sq_sub_one_eq _ hq1]
    exact Dvd.dvd.mul_left hpq _
  have hΦ : Function.Injective (a1a1Hom X) := a1a1Hom_injective
  have hcardM : Nat.card (stdA1A1 X) = (Nat.card X * (Nat.card X ^ 2 - 1)) ^ 2 := card_stdA1A1
  have hcardG : Nat.card (adjointGroup .G2 X) = ordG2 (Nat.card X) := card_adjointGroup_G2
  have hidx : (stdA1A1 X).index =
      Nat.card X ^ 4 * ((Nat.card X ^ 2) ^ 2 + Nat.card X ^ 2 + 1) := by
    have h1 := Subgroup.index_mul_card (stdA1A1 X)
    rw [hcardM, hcardG, ordG2_eq_index_mul hq1] at h1
    have hpos : 0 < (Nat.card X * (Nat.card X ^ 2 - 1)) ^ 2 := by
      have : 0 < Nat.card X ^ 2 - 1 := by
        have : 4 ≤ Nat.card X ^ 2 := by nlinarith
        omega
      positivity
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  obtain ⟨hnd, hmod⟩ := not_dvd_and_not_modEq_one hp hp5 hpq
  rw [← hidx] at hnd hmod
  have hdvdSL : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) X) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Dvd.dvd.mul_left hpq2 _
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' p hdvdSL
  have hep : e ^ p = 1 := by rw [← he]; exact pow_orderOf_eq_one e
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at he
    exact hp.one_lt.ne he
  have hzp : ∀ a ∈ Subgroup.zpowers e, a ^ p = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hep, one_zpow]
  let E'₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) X × Matrix.SpecialLinearGroup (Fin 2) X) :=
    (Subgroup.zpowers e).prod (Subgroup.zpowers e)
  let E' : Subgroup (adjointGroup .G2 X) := E'₀.map (a1a1Hom X)
  have hE'M : E' ≤ stdA1A1 X := Subgroup.map_le_range _ _
  have hE'p : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    have hab : (a, b) ^ p = (a ^ p, b ^ p) := rfl
    rw [← map_pow, hab, hzp a ha, hzp b hb]
    exact map_one _
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hΦ]
    have h1 : Nat.card E'₀ = Nat.card (Subgroup.zpowers e) * Nat.card (Subgroup.zpowers e) :=
      (Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers e) (Subgroup.zpowers e)).toEquiv).trans
        (Nat.card_prod _ _)
    rw [h1, Nat.card_zpowers, he, sq]
  let M : Subgroup (adjointGroup .G2 X) := stdA1A1 X
  have hEmp : IsPGroup p ↥(E'.subgroupOf M) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'M).toEquiv, hE'c]
  obtain ⟨Q, hQ⟩ := hEmp.exists_le_sylow
  let S : Subgroup (adjointGroup .G2 X) := (Q : Subgroup ↥M).map M.subtype
  have hSM : S ≤ M := Subgroup.map_subtype_le _
  have hE'S : E' ≤ S := by
    intro x hx
    exact ⟨⟨x, hE'M hx⟩, hQ hx, rfl⟩
  have hSp : IsPGroup p ↥S := Q.isPGroup'.map M.subtype
  have hSidx : ¬ p ∣ S.index := by
    have h1 : S.index = (Q : Subgroup ↥M).index * M.index := Subgroup.index_map_subtype _
    rw [h1]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact Q.not_dvd_index h
    · exact hnd h
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.K128.sylowShape_G2 X hp hp5 hX hm hpq2 S hSp hSidx
  have hmaxN : ∀ N : Subgroup (adjointGroup .G2 X), M ≤ N → N = M ∨ N = ⊤ := hmax X hq4
  set U := Subgroup.closure {k : adjointGroup .G2 X | ∃ x ∈ E', x ≠ 1 ∧ Commute k x ∧
    ∃ n : ℕ, k ^ (2 ^ n) = 1} with hU
  have hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) X,
      A ∈ Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin 2) X | g ^ 2 = 1} := by
    intro A
    rw [CFSG.HardMathSupport.Lang.Proving.closure_pow_char_eq_one_eq_top (p := 2)]
    exact Subgroup.mem_top _
  have hL : ∀ A : Matrix.SpecialLinearGroup (Fin 2) X, a1a1Hom X (A, 1) ∈ U := by
    intro A
    refine (Subgroup.closure_le (U.comap ((a1a1Hom X).comp (MonoidHom.inl _ _)))).2 ?_ (hsl A)
    intro g hg
    have hg2 : g ^ 2 = 1 := hg
    refine Subgroup.subset_closure ⟨a1a1Hom X (1, e), ⟨(1, e), ⟨one_mem _, Subgroup.mem_zpowers e⟩, rfl⟩,
      ?_, ?_, 1, ?_⟩
    · intro h
      have := hΦ (h.trans (map_one _).symm)
      exact he1 (congrArg Prod.snd this)
    · show a1a1Hom X (g, 1) * a1a1Hom X (1, e) = a1a1Hom X (1, e) * a1a1Hom X (g, 1)
      rw [← map_mul, ← map_mul]
      simp
    · show (a1a1Hom X (g, 1)) ^ (2 ^ 1) = 1
      rw [pow_one, ← map_pow]
      have : ((g, 1) : Matrix.SpecialLinearGroup (Fin 2) X × Matrix.SpecialLinearGroup (Fin 2) X) ^ 2 =
          (g ^ 2, 1 ^ 2) := rfl
      rw [this, hg2, one_pow]
      exact map_one _
  have hR : ∀ B : Matrix.SpecialLinearGroup (Fin 2) X, a1a1Hom X (1, B) ∈ U := by
    intro B
    refine (Subgroup.closure_le (U.comap ((a1a1Hom X).comp (MonoidHom.inr _ _)))).2 ?_ (hsl B)
    intro g hg
    have hg2 : g ^ 2 = 1 := hg
    refine Subgroup.subset_closure ⟨a1a1Hom X (e, 1), ⟨(e, 1), ⟨Subgroup.mem_zpowers e, one_mem _⟩, rfl⟩,
      ?_, ?_, 1, ?_⟩
    · intro h
      have := hΦ (h.trans (map_one _).symm)
      exact he1 (congrArg Prod.fst this)
    · show a1a1Hom X (1, g) * a1a1Hom X (e, 1) = a1a1Hom X (e, 1) * a1a1Hom X (1, g)
      rw [← map_mul, ← map_mul]
      simp
    · show (a1a1Hom X (1, g)) ^ (2 ^ 1) = 1
      rw [pow_one, ← map_pow]
      have : ((1, g) : Matrix.SpecialLinearGroup (Fin 2) X × Matrix.SpecialLinearGroup (Fin 2) X) ^ 2 =
          (1 ^ 2, g ^ 2) := rfl
      rw [this, hg2, one_pow]
      exact map_one _
  have hgen : M ≤ U := by
    rintro _ ⟨⟨A, B⟩, rfl⟩
    have e1 : a1a1Hom X (A, B) = a1a1Hom X (A, 1) * a1a1Hom X (1, B) := by
      rw [← map_mul]; simp
    rw [e1]
    exact U.mul_mem (hL A) (hR B)
  exact closure_uniCen_eq_top_of_maximal M S E' φ hSM hSp hSidx hE'S hE'p hE'c hmaxN hmod hgen E₁ hE₁p
    hE₁c

theorem not_dvd_sumLength_G2_of_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (h : p ∣ q - 1) : ¬ p ∣ geomSum 2 1 q * geomSum 6 1 q := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hq1 : (q : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 h
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
    exact this
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
  push_cast at h0
  rw [CFSG.LieType.SeitzGeneration.ExcHigh.geomSum_cast_of_cast_eq_one 2 1 q hq1,
    CFSG.LieType.SeitzGeneration.ExcHigh.geomSum_cast_of_cast_eq_one 6 1 q hq1] at h0
  have h12 : ((12 : ℕ) : ZMod p) = 0 := by
    push_cast at h0 ⊢
    linear_combination h0
  have h12' : p ∣ 12 := (ZMod.natCast_eq_zero_iff 12 p).1 h12
  have h12'' : p ∣ 2 ^ 2 * 3 := by norm_num; exact h12'
  rcases (Nat.Prime.dvd_mul hp).1 h12'' with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem normalizesRSubgroup_G2_of_dvd_sub_one (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q.card - 1) {E : Subgroup (MulAut (Cat ⟨.G2 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.G2 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.G2 q, hv⟩ E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype (WeylGroup .G2) := Fintype.ofFinite _
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hr : ∃ n, Nat.card K = q.p ^ n := ⟨q.exponent, by rw [hK, PrimePower.card_def]⟩
  have hJ : (∅ : Set (Fin Tag.G2.rank)) ≠ Set.univ := by
    intro h
    have : (0 : Fin Tag.G2.rank) ∈ (∅ : Set (Fin Tag.G2.rank)) := by rw [h]; trivial
    exact this
  have hidx : ¬ p ∣ (parabolicSubgroup .G2 K (∅ : Set (Fin Tag.G2.rank))).relIndex
      (adjointGroup .G2 K) := by
    have h := parabolicSum_univ_eq_mul_index (τ := .G2) (K := K) (∅ : Set (Fin Tag.G2.rank))
    rw [parabolicSum_empty, one_mul, parabolicSum_univ, sum_length_G2] at h
    rw [← h, hK]
    exact not_dvd_sumLength_G2_of_dvd_sub_one hp hp5 (by
      rw [PrimePower.card_def]
      exact Nat.one_le_pow _ _ q.prime_p.pos) hpq
  obtain ⟨R, hR0, hRr, hR⟩ :=
    exists_normalized_of_not_dvd_relIndex e hr hJ hidx hEp hin
  exact ⟨R, hR0, by simpa using hRr, hR⟩

end G2

section FramesEven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open scoped MatrixGroups

theorem isSolvable_of_isSolvable_closure_two_pow {H : Type*} [Group H] [Finite H]
    (h : Group.IsSolvable ↥(Subgroup.closure {x : H | ∃ n : ℕ, x ^ (2 ^ n) = 1})) :
    Group.IsSolvable H := by
  classical
  set N := Subgroup.closure {x : H | ∃ n : ℕ, x ^ (2 ^ n) = 1} with hN
  haveI hNn : N.Normal := by
    constructor
    intro n hn g
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := hx
      exact Subgroup.subset_closure ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have h1 := N.mul_mem hx hy
      have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      rw [e]
      exact h1
    | inv x _ hx =>
      have h1 := N.inv_mem hx
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact h1
  have hodd : Odd (Nat.card (H ⧸ N)) := by
    rw [Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ Nat.card (H ⧸ N) := by omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hu : (x ^ m) ^ (2 ^ k) = 1 := by rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
    have huN : x ^ m ∈ N := Subgroup.subset_closure ⟨k, hu⟩
    have hym : (QuotientGroup.mk x : H ⧸ N) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact huN
    have h3 := orderOf_dvd_of_pow_eq_one hym
    rw [hy] at h3
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h3)
  haveI : Group.IsSolvable (H ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  haveI : Group.IsSolvable ↥N := h
  exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem not_isSolvable_closure_two_pow_of_le {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : ¬ Group.IsSolvable ↥P) :
    ¬ Group.IsSolvable ↥(Subgroup.closure {x | x ∈ P ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1}) := by
  intro hsol
  apply hP
  apply isSolvable_of_isSolvable_closure_two_pow
  set S' : Set ↥P := {x | ∃ n : ℕ, x ^ (2 ^ n) = 1} with hS'
  have hle : (Subgroup.closure S').map P.subtype ≤
      Subgroup.closure {x | x ∈ P ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨n, hn⟩, rfl⟩
    exact ⟨x.2, n, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hn, Subgroup.coe_one]⟩
  let φ : ↥(Subgroup.closure S') →* ↥(Subgroup.closure {x | x ∈ P ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1}) :=
    (Subgroup.inclusion hle).comp
      (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).toMonoidHom
  have hφ : Function.Injective φ :=
    (Subgroup.inclusion_injective hle).comp (MulEquiv.injective _)
  haveI := hsol
  exact solvable_of_solvable_injective hφ

theorem closure_two_pow_SL_eq_top (n : ℕ) (K : Type) [Field K] [CharP K 2] :
    Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin n) K | ∃ m : ℕ, g ^ (2 ^ m) = 1} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin n) K → Matrix.SpecialLinearGroup (Fin n) K)) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top _
  refine Subgroup.closure_mono ?_ hy
  rintro _ ⟨t, rfl⟩
  refine ⟨1, ?_⟩
  have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.transvection_pow_ringChar t.hij t.c
  rw [ringChar.eq K 2] at h
  rw [pow_one, Matrix.TransvectionStruct.toSpecialLinearGroup_def]
  exact h

theorem closure_two_pow_eq_top_of_quasisimple {G : Type} [Group G] {X : Subgroup G} [Finite X]
    (hX : CFSG.IsQuasisimple ↥X) :
    Subgroup.closure {x : ↥X | ∃ n : ℕ, x ^ (2 ^ n) = 1} = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card X := by
    by_contra hodd
    have hs : Group.IsSolvable ↥X :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd))
    obtain ⟨-, hsimple, a, b, hab⟩ := hX
    have : Group.IsSolvable (↥X ⧸ Subgroup.center ↥X) :=
      Group.isSolvable_of_surjective (f := QuotientGroup.mk' (Subgroup.center ↥X))
        (QuotientGroup.mk'_surjective _)
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := ↥X ⧸ Subgroup.center ↥X)).2 this a b)
  have hle := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.le_closure_pow_of_quasisimple hX hdvd
  rw [eq_top_iff]
  intro y _
  have hy := hle y.2
  have h1 : Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} =
      (Subgroup.closure {x : ↥X | ∃ n : ℕ, x ^ (2 ^ n) = 1}).map X.subtype := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨hx, n, hn⟩
      exact ⟨⟨x, hx⟩, ⟨n, Subtype.ext (by simpa using hn)⟩, rfl⟩
    · rintro ⟨z, ⟨n, hn⟩, rfl⟩
      exact ⟨z.2, n, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hn, Subgroup.coe_one]⟩
  rw [h1] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [show z = y from Subtype.ext hzy] at hz

variable {G M₁ M₂ : Type} [Group G] [Group M₁] [Group M₂] [Finite G] [Finite M₁] [Finite M₂]
  {p : ℕ} [hp : Fact p.Prime]

theorem uniClosure_eq_top_of_twoFrames_even (ψA : M₁ →* G) (ψB : M₂ →* G)
    (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hC : ∀ H : Subgroup G, ψA.range ⊔ ψB.range ≤ H →
      ¬ H ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) → H = ⊤)
    (hN : ∀ P : Subgroup G, P ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) →
      Group.IsSolvable ↥(P ⊓ (ψA.range ⊔ ψB.range)) → Group.IsSolvable ↥P)
    (hcycA : ∀ g : M₁, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₁)))
    (hcycB : ∀ g : M₂, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₂)))
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range))
    (hcard : (Nat.card G).factorization p =
      (Nat.card M₁).factorization p + (Nat.card M₂).factorization p)
    (hthird : ∀ E : Subgroup G, Nat.card E = p ^ 2 → (∀ x ∈ E, x ^ p = 1) →
      ∀ a b : G, a ∈ E → b ∈ E → a ≠ 1 → b ≠ 1 →
        ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
          ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({e} : Set G) ∧ ¬ Group.IsSolvable ↥P)
    (hgA : Subgroup.closure {x : M₁ | ∃ n : ℕ, x ^ (2 ^ n) = 1} = ⊤)
    (hgB : Subgroup.closure {x : M₂ | ∃ n : ℕ, x ^ (2 ^ n) = 1} = ⊤)
    (E : Subgroup G) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (2 ^ n) = 1} = ⊤ := by
  classical
  obtain ⟨g, a, b, hao, hbo, hEg⟩ :=
    exists_conj_plane_of_twoFrames ψA ψB hA hB hcomm hcycA hcycB hAB hcard E hEp hEc
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  set H := Subgroup.closure {k : G | ∃ x ∈ E', x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (2 ^ n) = 1}
    with hH
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hao
    exact hp.out.one_lt.ne hao
  have hb1 : b ≠ 1 := fun h => by
    rw [h, orderOf_one] at hbo
    exact hp.out.one_lt.ne hbo
  have hA1 : ψA a ≠ 1 := fun h => ha1 (hA (h.trans (map_one ψA).symm))
  have hB1 : ψB b ≠ 1 := fun h => hb1 (hB (h.trans (map_one ψB).symm))
  have haE : ψA a ∈ E' := by
    rw [hEg]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hbE : ψB b ∈ E' := by
    rw [hEg]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hXH : ψA.range ⊔ ψB.range ≤ H := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      have hy : y ∈ Subgroup.closure {x : M₁ | ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
        rw [hgA]
        exact Subgroup.mem_top y
      refine (Subgroup.closure_le (H.comap ψA)).2 ?_ hy
      rintro z ⟨n, hn⟩
      exact Subgroup.subset_closure ⟨ψB b, hbE, hB1, hcomm z b, n, by rw [← map_pow, hn, map_one]⟩
    · rintro _ ⟨y, rfl⟩
      have hy : y ∈ Subgroup.closure {x : M₂ | ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
        rw [hgB]
        exact Subgroup.mem_top y
      refine (Subgroup.closure_le (H.comap ψB)).2 ?_ hy
      rintro z ⟨n, hn⟩
      exact Subgroup.subset_closure ⟨ψA a, haE, hA1, (hcomm a z).symm, n,
        by rw [← map_pow, hn, map_one]⟩
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]
  have hE'p : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hEp y hy, map_one]
  obtain ⟨e, heE, hea, heb, P, hPC, hPs⟩ := hthird E' hE'c hE'p (ψA a) (ψB b) haE hbE hA1 hB1
  have he1 : e ≠ 1 := fun h => hea (h ▸ Subgroup.one_mem _)
  set P' := Subgroup.closure {x | x ∈ P ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} with hP'
  have hP'P : P' ≤ P := (Subgroup.closure_le _).2 fun x hx => hx.1
  have hP's : ¬ Group.IsSolvable ↥P' := not_isSolvable_closure_two_pow_of_le hPs
  have hP'C : P' ≤ Subgroup.centralizer ({e} : Set G) := hP'P.trans hPC
  have hP'H : P' ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro z ⟨hzP, n, hn⟩
    exact Subgroup.subset_closure ⟨e, heE, he1,
      (commute_iff_eq _ _).2 (Subgroup.mem_centralizer_singleton_iff.1 (hPC hzP)), n, hn⟩
  have hzc : ∀ h ∈ Subgroup.zpowers (ψA a), ∀ k ∈ Subgroup.zpowers (ψB b), Commute h k := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((hcomm a b).zpow_left i).zpow_right j
  have heE' := heE
  rw [hEg] at heE'
  obtain ⟨_, ⟨i, hi0⟩, _, ⟨j, hj0⟩, hce⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.exists_mul_of_mem_sup_of_commute hzc heE'
  simp only at hi0 hj0
  rw [← hi0, ← hj0] at hce
  have hi : orderOf (a ^ i) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hao,
        pow_orderOf_eq_one, one_zpow]
    · intro h
      apply heb
      have : ψA a ^ i = 1 := by rw [← map_zpow, h, map_one]
      rw [hce, this, one_mul]
      exact Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩
  have hj : orderOf (b ^ j) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hbo,
        pow_orderOf_eq_one, one_zpow]
    · intro h
      apply hea
      have : ψB b ^ j = 1 := by rw [← map_zpow, h, map_one]
      rw [hce, this, mul_one]
      exact Subgroup.mem_zpowers_iff.2 ⟨i, rfl⟩
  have heq : e = ψA (a ^ i) * ψB (b ^ j) := by rw [hce, map_zpow, map_zpow]
  have hnot : ¬ H ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) := by
    intro hle
    have hPN : P' ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) :=
      hP'H.trans hle
    have hsol : Group.IsSolvable ↥(P' ⊓ (ψA.range ⊔ ψB.range)) := by
      apply Group.isSolvable_of_comm
      rintro ⟨z, hzP, hzX⟩ ⟨z', hz'P, hz'X⟩
      apply Subtype.ext
      have hwe : Commute z (ψA (a ^ i) * ψB (b ^ j)) := by
        rw [← heq]
        exact (commute_iff_eq _ _).2 (Subgroup.mem_centralizer_singleton_iff.1 (hP'C hzP))
      have hw'e : Commute z' (ψA (a ^ i) * ψB (b ^ j)) := by
        rw [← heq]
        exact (commute_iff_eq _ _).2 (Subgroup.mem_centralizer_singleton_iff.1 (hP'C hz'P))
      exact (commute_of_mem_centralizer_twoFrames ψA ψB hA hB hcomm hcycA hcycB hAB hi hj hzX hz'X
        hwe hw'e).eq
    exact hP's (hN P' hPN hsol)
  exact hC H hXH hnot

end FramesEven

section FrameNatives

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem uniClosure_eq_top_of_splitFrame_even {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {S : Set (Fin τ.rank → ℤ)} {ψA ψB : SL(n, K) →* ModGL τ K} (hA : Function.Injective ψA)
    (hB : Function.Injective ψB) (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hrange : ψA.range ⊔ ψB.range = rootSpan τ K S) (hC : FrameClosing τ K S)
    (hN : FrameNormalizerSolvable τ K S) {p : ℕ} [hp : Fact p.Prime] (hpn : n < p)
    (hcyc : ∀ g : SL(n, K), orderOf g = p →
      IsCyclic (Subgroup.centralizer ({g} : Set SL(n, K))))
    (hcard : (Nat.card (adjointGroup τ K)).factorization p =
      2 * (Nat.card SL(n, K)).factorization p)
    (hthird : ∀ E : Subgroup (adjointGroup τ K), Nat.card E = p ^ 2 → (∀ x ∈ E, x ^ p = 1) →
      ∀ a b : adjointGroup τ K, a ∈ E → b ∈ E → a ≠ 1 → b ≠ 1 →
        ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
          ∃ P : Subgroup (adjointGroup τ K),
            P ≤ Subgroup.centralizer ({e} : Set (adjointGroup τ K)) ∧ ¬ Group.IsSolvable ↥P)
    (E : Subgroup (adjointGroup τ K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : adjointGroup τ K | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧
      ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  have hAG : ∀ x, ψA x ∈ adjointGroup τ K := fun x =>
    rootSpan_le_adjointGroup K S (hrange ▸ Subgroup.mem_sup_left ⟨x, rfl⟩)
  have hBG : ∀ x, ψB x ∈ adjointGroup τ K := fun x =>
    rootSpan_le_adjointGroup K S (hrange ▸ Subgroup.mem_sup_right ⟨x, rfl⟩)
  let ψA' : SL(n, K) →* adjointGroup τ K := ψA.codRestrict (adjointGroup τ K) hAG
  let ψB' : SL(n, K) →* adjointGroup τ K := ψB.codRestrict (adjointGroup τ K) hBG
  have hA' : Function.Injective ψA' := fun x y h => hA (congrArg Subtype.val h)
  have hB' : Function.Injective ψB' := fun x y h => hB (congrArg Subtype.val h)
  have hcomm' : ∀ x y, Commute (ψA' x) (ψB' y) := fun x y => Subtype.ext (hcomm x y).eq
  have hAB : ¬ p ∣ Nat.card ↥(ψA'.range ⊓ ψB'.range) := by
    intro hdvd
    have hle : ψA'.range ⊓ ψB'.range ≤ (Subgroup.center SL(n, K)).map ψA' := by
      rintro z ⟨⟨c, rfl⟩, hcB⟩
      exact ⟨c, Subgroup.mem_center_iff.2 fun x => (commute_of_frame_mem_range hA' hcomm' hcB x).eq,
        rfl⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective hA'] at h1
    have h2 := CFSG.HardMathSupport.Foote.Proving.natCard_center_SL_le (Fin n) K
    have h3 : p ≤ Nat.card ↥(ψA'.range ⊓ ψB'.range) := Nat.le_of_dvd Nat.card_pos hdvd
    simp only [Fintype.card_fin] at h2
    have := hp.out.two_le
    omega
  have hXS : (ψA'.range ⊔ ψB'.range).map (adjointGroup τ K).subtype = rootSpan τ K S := by
    rw [Subgroup.map_sup, ← hrange]
    congr 1
    · rw [← MonoidHom.range_comp]
      rfl
    · rw [← MonoidHom.range_comp]
      rfl
  exact uniClosure_eq_top_of_twoFrames_even ψA' ψB' hA' hB' hcomm' (closing_of_map hXS hC)
    (normalizerSolvable_of_map hXS hN) hcyc hcyc hAB (by rw [hcard, two_mul]) hthird
    (closure_two_pow_SL_eq_top n K) (closure_two_pow_SL_eq_top n K) E hEp hEc

theorem uniClosure_eq_top_of_twSubgroups_even {τ : Tag} {K : Type} [Field K] [Finite K]
    {X₁ X₂ : Subgroup (ModGL τ K)} (h₁ : X₁ ≤ adjointGroup τ K) (h₂ : X₂ ≤ adjointGroup τ K)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (hC : TwFrameClosing τ K (X₁ ⊔ X₂)) (hN : TwFrameNormalizerSolvable τ K (X₁ ⊔ X₂))
    {p : ℕ} [Fact p.Prime] (hD : TwFramePlaneData τ K X₁ X₂ p) (hthird : TwThirdLine τ K p)
    (hq : TwQuasi X₁ X₂)
    (E : Subgroup ↥(adjointGroup τ K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : ↥(adjointGroup τ K) | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧
      ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  have : Finite (ModGL τ K) := CFSG.LieType.Chevalley.finite_modGL
  have hinj : Function.Injective (adjointGroup τ K).subtype :=
    (adjointGroup τ K).subtype_injective
  have hY : ((Subgroup.inclusion h₁).range ⊔ (Subgroup.inclusion h₂).range).map
      (adjointGroup τ K).subtype = X₁ ⊔ X₂ := by
    rw [Subgroup.map_sup, Subgroup.inclusion_range, Subgroup.inclusion_range,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h₁,
      inf_eq_left.2 h₂]
  have hAB : ¬ p ∣ Nat.card ↥((Subgroup.inclusion h₁).range ⊓ (Subgroup.inclusion h₂).range) := by
    have hmap : ((Subgroup.inclusion h₁).range ⊓ (Subgroup.inclusion h₂).range).map
        (adjointGroup τ K).subtype = X₁ ⊓ X₂ := by
      rw [Subgroup.map_inf _ _ _ hinj, Subgroup.inclusion_range, Subgroup.inclusion_range,
        Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h₁,
        inf_eq_left.2 h₂]
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hD.inter
  exact uniClosure_eq_top_of_twoFrames_even (Subgroup.inclusion h₁) (Subgroup.inclusion h₂)
    (Subgroup.inclusion_injective h₁) (Subgroup.inclusion_injective h₂)
    (fun x y => Subtype.ext (hcomm _ x.2 _ y.2)) (closing_of_map hY hC)
    (normalizerSolvable_of_map hY hN) hD.cyclic₁ hD.cyclic₂ hAB hD.card hthird
    (closure_two_pow_eq_top_of_quasisimple hq.1) (closure_two_pow_eq_top_of_quasisimple hq.2) E hEp hEc

theorem f4ThreeUniNative_even (K : Type) [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 3)
    (E : Subgroup (adjointGroup .F4 K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : adjointGroup .F4 K | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧
      ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f', -, hf'⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f' : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf'
  have hf : 1 ≤ (f' : ℕ) := f'.pos
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := exists_splitFrame_F4 K
  obtain ⟨-, hq1, hq3⟩ := not_dvd_and_ne_one_of_orderOf (by norm_num) (by norm_num) hord
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
    have hmul : (((Nat.card K : ℕ) : ZMod p) - 1) *
        (((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1) = 0 := by
      linear_combination hq3
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd (sub_eq_zero.1 h) hq1
    · exact h
  have hcard : (Nat.card (adjointGroup .F4 K)).factorization p =
      2 * (Nat.card SL(3, K)).factorization p := by
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
      padicValNat_ordF4_of_orderOf_eq_three hp hp5 hq2 hord,
      padicValNat_card_SL_of_orderOf_eq K hp (by norm_num)
        (by rw [← Nat.card_eq_fintype_card]; exact hord), Nat.card_eq_fintype_card]
  refine uniClosure_eq_top_of_splitFrame_even hA hB hcomm hrange
    (frameClosing_of_detection_F4 K (by omega) (DetectF4.frameDetection_F4 K (by omega)))
    (frameNormalizerSolvable_F4 K hK4) (by omega)
    (fun g hg => isCyclic_centralizer_of_orderOf_eq K hp (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hord) hg) hcard ?_ E hEp hEc
  intro F hFc hFp a b haF hbF ha1 hb1
  exact exists_offLine_nonsolvable_F4 K hf hK hp (by omega) hΦ F hFc hFp haF hbF ha1 hb1

theorem e8FiveUniNative_even (K : Type) [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 5)
    (E : Subgroup (adjointGroup .E8 K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : adjointGroup .E8 K | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧
      ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f', -, hf'⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f' : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf'
  have hf : 1 ≤ (f' : ℕ) := f'.pos
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := exists_splitFrame_E8 K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp11 : 11 ≤ p := by
    obtain ⟨hpq, -, -⟩ := not_dvd_and_ne_one_of_orderOf (by norm_num) (by norm_num) hord
    have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h =>
      hpq ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have hdvd : 5 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
    obtain ⟨k, hk⟩ := hdvd
    have h2 := hp.two_le
    rcases k with _ | _ | k
    · omega
    · have : p = 6 := by omega
      subst this
      exact absurd hp (by norm_num)
    · omega
  have hcard : (Nat.card (adjointGroup .E8 K)).factorization p =
      2 * (Nat.card SL(5, K)).factorization p := by
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8,
      padicValNat_ordE8_of_orderOf_eq_five hp (by omega) hq2 hord,
      padicValNat_card_SL_of_orderOf_eq K hp (by norm_num)
        (by rw [← Nat.card_eq_fintype_card]; exact hord), Nat.card_eq_fintype_card]
  have hN : FrameNormalizerSolvable .E8 K (cosetRoots .E8 4 5) := by
    rcases (show 4 ≤ Nat.card K ∨ Nat.card K = 3 ∨ Nat.card K = 2 by omega) with h4 | h3 | h2'
    · exact frameNormalizerSolvable_E8 K h4
    · exact frameNormalizerSolvable_E8_three K h3
    · exact DetectE8.frameNormalizerSolvable_E8_two K h2'
  refine uniClosure_eq_top_of_splitFrame_even hA hB hcomm hrange
    (frameClosing_of_detection_E8 K (DetectE8.frameDetection_E8 K)) hN (by omega)
    (fun g hg => isCyclic_centralizer_of_orderOf_eq K hp (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hord) hg) hcard ?_ E hEp hEc
  intro F hFc hFp a b haF hbF ha1 hb1
  exact exists_offLine_nonsolvable_E8 K hf hK hp (by omega) hord F hFc hFp haF hbF ha1 hb1

theorem twClassUniNative_even (c : TwClass) (h : TwClassLeaves c) (K : Type) [Field K] [Finite K]
    (hK : c.minQ ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = c.e) (E : Subgroup ↥(adjointGroup c.tag K))
    (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : ↥(adjointGroup c.tag K) | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧
      ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  obtain ⟨D⟩ := h.lang K
  have hb := h.basic K hK D
  haveI : Fact p.Prime := ⟨hp⟩
  exact uniClosure_eq_top_of_twSubgroups_even hb.le₁ hb.le₂ hb.comm (h.closing K hK D)
    (h.normalizer K hK D) (h.planeData K hK D p hp hp5 hord) (h.third K hK p hp hp5 hord)
    (twQuasi c K hK D) E hEp hEc

end FrameNatives

section F4B4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.ComponentClassification.CatLeafProof CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false

theorem iSup_b4Chain_le_uniClosure_of_sp {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (Ψ : StatedSp 4 K →* adjointGroup .F4 K) (hker : Ψ.ker ≤ Subgroup.center (StatedSp 4 K))
    (hrange : Ψ.range = ⨆ k, b4Chain K k)
    (E : Subgroup (adjointGroup .F4 K)) (hE : E ≤ ⨆ k, b4Chain K k) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEc : Nat.card E = p ^ 2) :
    ⨆ k, b4Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x ∧
      ∃ m : ℕ, g ^ (ringChar K ^ m) = 1} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : Finite (StatedSp 4 K) := inferInstance
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (StatedSp 4 K)) := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      show (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedSp 4 K) =
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 4 K from rfl,
      CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K (by norm_num)]
    intro hd
    have h2 := (Nat.dvd_prime Nat.prime_two).1 (hd.trans (Nat.gcd_dvd_left 2 _))
    omega
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := fun hd => hcen (hd.trans (Subgroup.card_dvd_of_le hker))
  have hpℓ : p ≠ ringChar K := by
    intro h
    apply hpK
    rw [hK, ← h]
    exact dvd_pow_self p n.ne_zero
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hrange ▸ hE
  set Ψ' : StatedSp 4 K →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [hE1def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv, hEc]
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← hcardE1, ← hmapE', card_map_eq_of_disjoint_ker Ψ' hdisE']
  have : CFSG.IsElementaryAbelian p E' :=
    { toIsMulCommutative := hE'ea.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE'ea.2 x x.2) }
  have htop := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e.uniClosure_spPlane_five
    (⟨hℓ, n.pos, hK, hp, by omega, hpℓ, by norm_num, by omega, this, hcardE'⟩ :
      CFSG.RankThree.PartOne.KCSpFull.SpPlaneSetup (ringChar K) n p 4 K E')
  intro g hg
  rw [← hrange] at hg
  obtain ⟨h, rfl⟩ := hg
  have hh : h ∈ Subgroup.closure {g : StatedSp 4 K | ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g ∧
      g ^ ringChar K = 1} := by
    have h1 : CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e.spUniSpan E' = ⊤ := htop
    rw [CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e.spUniSpan] at h1
    rw [h1]
    exact Subgroup.mem_top _
  have hmap : (Subgroup.closure {g : StatedSp 4 K | ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g ∧
      g ^ ringChar K = 1}).map Ψ ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x ∧
        ∃ m : ℕ, g ^ (ringChar K ^ m) = 1} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k, ⟨x, hx, hx1, hkx, hkr⟩, rfl⟩
    have hxE : Ψ x ∈ E := by
      have h1 : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
      exact h1
    have hx1' : Ψ x ≠ 1 := by
      intro h1
      apply hx1
      refine Subgroup.disjoint_def.mp hdisE' hx ?_
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    refine Subgroup.subset_closure ⟨Ψ x, hxE, hx1', ?_, 1, ?_⟩
    · change Ψ k * Ψ x = Ψ x * Ψ k
      rw [← map_mul, ← map_mul, hkx]
    · rw [pow_one, ← map_pow, hkr, map_one]
  exact hmap ⟨h, hh, rfl⟩

theorem f4TwoUniNative_even (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ) [hpF : Fact p.Prime]
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) (E₀ : Subgroup (adjointGroup .F4 K))
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hK4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hpF.out.one_lt.ne' (Nat.dvd_one.mp h1)
  obtain ⟨Ψ, hker, hrange, -, -⟩ := exists_psi_B4_F4_frame_even hK hK4
  have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_two_conj (p := p)
    (r := ringChar K) (⨆ k, b4Chain K k) (f4FrameGroup K)
    (CFSG.LieType.Chevalley.weylElement .F4 K (f4Node 3)) f4FrameGroup_le_b4 f4FrameGroup_le_conj_b4
    (fun M hX hn => eq_top_of_b4Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_b4Chain_le_uniClosure_of_sp hpF.out hp5 hpK Ψ hker hrange E hE hEp hEc)
    E₀ hE₀p hE₀c (f4TwoSylow K p hp5 hpq E₀ hE₀p hE₀c)
  rwa [ringChar.eq K 2] at h

theorem rootGroupF4_pow_two_eq_one {K : Type} [Field K] [CharP K 2] {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) {y : adjointGroup .F4 K}
    (hy : y ∈ (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup γ) : y ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff hγ y).1 hy
  rw [pow_two, ← CFSG.LieType.Steinberg.Adjoint.xPar_add, CharTwo.add_self_eq_zero,
    CFSG.LieType.Steinberg.Adjoint.xPar_zero]

theorem f4FourUniNative_even (K : Type) [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    (p : ℕ) [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K ^ 2 + 1)
    (E₀ : Subgroup (adjointGroup .F4 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ Nat.card K ^ 2 := dvd_pow hd two_ne_zero
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hpq
    exact hpF.out.one_lt.ne' (Nat.dvd_one.mp h2)
  obtain ⟨Ψ, hker, hrange, -, -⟩ := exists_psi_B4_F4_frame_even hK hK4
  obtain ⟨e, heA, heo, hec⟩ := exists_e1_F4_four (K := K) (p := p) (by omega) hpq
  have heX : e ∈ ⨆ k, b4Chain K k :=
    (sup_le (sup_le (le_iSup (b4Chain K) 0) (le_iSup (b4Chain K) 1)) (le_iSup (b4Chain K) 2)) heA
  obtain ⟨g, hgX, hge⟩ := exists_conj_plane_b4_even hK4 hp5 hpq heX heo E₀ hE₀p hE₀c
  have hE₁p : ∀ x ∈ E₀.map (MulAut.conj g).toMonoidHom, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at heo
    omega
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  apply eq_top_of_b4Chain_le_of_delta_le
  · have h := iSup_b4Chain_le_uniClosure_of_sp hpF.out hp5 hpK Ψ hker hrange _ hgX hE₁p hE₁c
    rwa [ringChar.eq K 2] at h
  · have hδ : IsRoot .F4 f4Delta := isRoot_f4Delta
    have hδ' : IsRoot .F4 (-f4Delta) := by
      simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
      decide +kernel
    refine sup_le ?_ ?_
    · intro y hy
      exact Subgroup.subset_closure ⟨e, hge, he1, (hec y (Subgroup.mem_sup_left hy)).symm, 1,
        by rw [pow_one]; exact rootGroupF4_pow_two_eq_one hδ hy⟩
    · intro y hy
      exact Subgroup.subset_closure ⟨e, hge, he1, (hec y (Subgroup.mem_sup_right hy)).symm, 1,
        by rw [pow_one]; exact rootGroupF4_pow_two_eq_one hδ' hy⟩

end F4B4

section E8D8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false

theorem not_two_dvd_card_center_spin_quadPlus_even {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 3 ≤ n) [Finite (spinGroup (quadPlus n K))] :
    ¬ 2 ∣ Nat.card (Subgroup.center (spinGroup (quadPlus n K))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := n) (K := K) hn
  refine not_dvd_card_center_of_forall (p := 2) fun x hx hx2 => ?_
  have hx' : x ∈ (StatedScalars _ K).comap (spinMatrix (quadPlus n K)) := by
    rw [← hcomap, hZ]
    exact hx
  obtain ⟨c, hc⟩ := Subgroup.mem_comap.mp hx'
  have hc2 : c ^ 2 = 1 := by
    apply scalar_injective_of_nonempty (ι := Fin n ⊕ Fin n)
    rw [map_pow, hc, ← map_pow, hx2, map_one, map_one]
  have hc1 : c = 1 := by
    have h1 : ((c : K)) ^ 2 = 1 := by
      have := congrArg Units.val hc2
      simpa using this
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : ((c : K) - 1) ^ 2 = 0 := by linear_combination h1 + (1 - (c : K)) * h2
    exact Units.ext (by simpa [sub_eq_zero] using pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h3)
  have hxm : spinMatrix (quadPlus n K) x = 1 := by
    rw [← hc, hc1, map_one]
  have hk : x ∈ (spinMatrix (quadPlus n K)).ker := hxm
  rw [ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero] at hk
  exact hk

theorem iSup_d8Chain_le_uniClosure_even {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (hpq1 : ¬ p ∣ Nat.card K - 1)
    (Ψ : spinGroup (CFSG.LieType.Universal.Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (CFSG.LieType.Universal.Spin.quadPlus 8 K)))
    (hrange : Ψ.range = ⨆ k, e8D8Chain K k)
    (E : Subgroup (adjointGroup .E8 K)) (hE : E ≤ ⨆ k, e8D8Chain K k)
    (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ⨆ k, e8D8Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x ∧
      ∃ m : ℕ, g ^ (2 ^ m) = 1} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hn3 : 3 ≤ 8 := by norm_num
  have : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 8) (K := K) hn3
  set π := spinToStatedProj (quadPlus 8 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 8 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hcen2 := not_two_dvd_card_center_spin_quadPlus_even (K := K) hn3
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) := by
      rw [hZ]
    exact hd.trans this
  have hrcop : (Nat.card π.ker).Coprime (ringChar K ^ 2) := by
    have h' : ¬ 2 ∣ Nat.card π.ker := by
      intro hd
      apply hcen2
      have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) := by
        rw [hZ]
      exact hd.trans this
    rw [hring]
    exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h').symm
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    apply hcen
    exact hd.trans (Subgroup.card_dvd_of_le hker)
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus 8 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hrange ▸ hE
  set Ψ' : spinGroup (quadPlus 8 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker Ψ' hdisE', hmapE',
      hcardE1]
  set Ebar : Subgroup _ := E'.map π with hEbar
  have hEbarea : IsElemAbelian p Ebar :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE'ea π
  have hcardEbar : Nat.card Ebar = p ^ 2 := by
    rw [hEbar, CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker π
      (disjoint_ker_of_exponent π hπcop hE'ea.2), hcardE']
  have hmodel := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e.orthSq_plusPlanes (r := 8)
    (by norm_num) hp hp5 hpK Ebar hEbarea hcardEbar
  have hG := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_quotient π
    hπsurj hZ.le hπcop hrcop hperf E' hE'ea.2 hmodel
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  rw [← hrange, MonoidHom.range_eq_map, ← hG, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨x, hx, hx1, hg, hgr⟩, rfl⟩
  refine ⟨Ψ x, ?_, ?_, ?_, 2, ?_⟩
  · have : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
    exact this
  · intro h1
    exact hx1 (Subgroup.disjoint_def.mp hdisΨ hx (MonoidHom.mem_ker.mpr h1))
  · show Ψ g * Ψ x = Ψ x * Ψ g
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ hg
  · rw [hring] at hgr
    rw [← map_pow, hgr, map_one]

theorem e8TwoUniNative_even (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ)
    [hpF : Fact p.Prime] (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2)
    (hN : ¬ NormalizesRGroup 2 E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hpF.out.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hSyl : ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8FrameGroup K := by
    rcases (by omega : p = 7 ∨ 11 ≤ p ∨ p = 8 ∨ p = 9 ∨ p = 10) with rfl | h11 | h | h | h
    · exact e8TwoSylowSeven K hpq E₀ hE₀p hE₀c (by rw [hring]; exact hN)
    · exact e8TwoSylow K p h11 hpq E₀ hE₀p hE₀c
    all_goals subst h; exact absurd hpF.out (by norm_num)
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_two_conj (p := p)
    (⨆ k, e8D8Chain K k) (e8FrameGroup K)
    (weylWordElt .E8 K e8Word) e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_d8Chain_le_uniClosure_even hpF.out (by omega) hpK hpq1 Ψ hker
      hrange E hE hEp hEc) E₀ hE₀p hE₀c hSyl

theorem e8FourUniNative_even (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ)
    [hpF : Fact p.Prime] (hp7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_two_conj (p := p)
    (⨆ k, e8D8Chain K k) (e8D4Group K)
    (weylWordElt .E8 K e8Word) e8D4Group_le_d8 e8D4Group_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_d8Chain_le_uniClosure_even hpF.out (by omega)
      (not_dvd_of_orderOf_eq_four hpF.out he) (not_dvd_pred_of_orderOf_eq_four hpF.out hq1 he)
      Ψ hker hrange E hE hEp hEc) E₀ hE₀p hE₀c (e8FourSylow K p hp7 he E₀ hE₀p hE₀c)

theorem rootGroupE8_pow_two_eq_one {K : Type} [Field K] [CharP K 2] {γ : Fin (Tag.rank .E8) → ℤ}
    (hγ : IsRoot .E8 γ) {y : adjointGroup .E8 K}
    (hy : y ∈ (CFSG.LieType.Steinberg.Adjoint.e8Datum K).rootGroup γ) : y ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff hγ y).1 hy
  rw [pow_two, ← CFSG.LieType.Steinberg.Adjoint.xPar_add, CharTwo.add_self_eq_zero,
    CFSG.LieType.Steinberg.Adjoint.xPar_zero]

theorem e8EightUniNative_even (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ}
    [hpF : Fact p.Prime] (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  have hfam := exists_e8D8_family K
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family hfam
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := hfam
  have hp2 : p ≠ 2 := ne_two_of_orderOf_eq_eight hpF.out he
  have hpq : p ∣ Nat.card K ^ 4 + 1 := dvd_pow_four_add_one_of_orderOf_eq_eight hpF.out he
  have hpK : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_eq_eight hpF.out he
  have hpq1 : ¬ p ∣ Nat.card K - 1 := not_dvd_pred_of_orderOf_eq_eight hpF.out Nat.card_pos he
  have hp5 : 5 ≤ p := by
    have h8 : 8 ∣ p - 1 := by
      have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h =>
        hpK ((ZMod.natCast_eq_zero_iff _ _).1 h)
      exact he ▸ ZMod.orderOf_dvd_card_sub_one hq0
    have := hpF.out.two_le
    obtain ⟨k, hk⟩ := h8
    rcases k with _ | k
    · omega
    · omega
  obtain ⟨e, heA, heo, hec⟩ := exists_e1_E8_eight_of_family hp2 hpq ρ hρ hcomm hψ
  have hle : (⨆ k : Fin 7, e8D8Chain K k.castSucc) ≤ ⨆ k, e8D8Chain K k :=
    iSup_le fun k => le_iSup (e8D8Chain K) k.castSucc
  have heX : e ∈ ⨆ k, e8D8Chain K k := hle heA
  obtain ⟨g, hgX, hge⟩ :=
    exists_conj_plane_d8_of_family ⟨ρ, hρ, hcomm, hψ⟩ he heX heo E₀ hE₀p hE₀c
  have hE₁p : ∀ x ∈ E₀.map (MulAut.conj g).toMonoidHom, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at heo
    exact hpF.out.one_lt.ne heo
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  apply eq_top_of_d8Chain_le_of_delta_le
  · exact iSup_d8Chain_le_uniClosure_even hpF.out hp5 hpK hpq1 Ψ hker hrange _ hgX hE₁p hE₁c
  · have hδ : IsRoot .E8 e8Delta := isRoot_e8Delta
    have hδ' : IsRoot .E8 (-e8Delta) := by
      rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
      decide +kernel
    refine sup_le ?_ ?_
    · intro y hy
      exact Subgroup.subset_closure ⟨e, hge, he1, (hec y (Subgroup.mem_sup_left hy)).symm, 1,
        by rw [pow_one]; exact rootGroupE8_pow_two_eq_one hδ hy⟩
    · intro y hy
      exact Subgroup.subset_closure ⟨e, hge, he1, (hec y (Subgroup.mem_sup_right hy)).symm, 1,
        by rw [pow_one]; exact rootGroupE8_pow_two_eq_one hδ' hy⟩

theorem e8TwoUniNative_five_even (K : Type) [Field K] [Finite K]
    [CharP K 2] (hpq : 5 ∣ Nat.card K + 1) (E₀ : Subgroup (adjointGroup .E8 K))
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀c : Nat.card E₀ = 5 ^ 2) (hN : ¬ NormalizesRGroup 2 E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hpK : ¬ 5 ∣ Nat.card K := by omega
  have hpq1 : ¬ 5 ∣ Nat.card K - 1 := by omega
  have hn' : ¬ CFSG.LieType.SeitzGeneration.ExcHighThree.NormalizesRNative Tag.E8 K E₀ := fun h => hN (by
    rw [← hring]
    exact CFSG.LieType.SeitzGeneration.ExcHigh.normalizesRGroup_of_native h)
  obtain ⟨D, hD⟩ := e8Five_regular_datum hpK hE₀p hE₀c hn'
  by_cases hw : ∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -u
  · obtain ⟨k, hk⟩ := exists_conj_le_of_frameDatum hE₀p D
      (e8FiveTwoFrameDatum_holds K hpq D.Fr D.hFr D.w hw)
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_two_conj (p := 5)
      (⨆ k, e8D8Chain K k) (e8FrameGroup K)
      (weylWordElt .E8 K e8Word) e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
      (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
      (fun E hE hEp hEc => iSup_d8Chain_le_uniClosure_even Nat.prime_five le_rfl hpK hpq1 Ψ
        hker hrange E hE hEp hEc) E₀ hE₀p hE₀c ⟨k, hk⟩
  · obtain ⟨u, hu⟩ := not_forall.1 hw
    obtain ⟨F, D', ζ, hζ, hzbc⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.exists_e8FiveFrameElt_twisted K hpq
    obtain ⟨w₀, hw₀⟩ := E8FiveSq.exists_weyl_neg_E8_five
    have key : Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧
        ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
      refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.e8FiveUniClose_of_frameElt
        (V := w₀ * D.w) hpK hE₀p hE₀c D hD ?_ ?_ F
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.closingFrameAt_twistedE8 K hpq D' ζ hζ
          F.z hzbc)
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.frameIn_twistedE8_le_closure K D')
      · intro h1
        apply hu
        rw [eq_inv_of_mul_eq_one_right h1, inv_smul_eq_iff, hw₀, neg_neg]
      · intro x hx a ha v
        rw [mul_smul, hw₀, ← neg_one_zsmul, CFSG.LieType.Chevalley.rootChar_zsmul, zpow_neg_one,
          E8FiveSq.rootChar_smul_eq_pow_of_mem D hx ha v]
        obtain ⟨m, hm⟩ := hpq
        have h5 := E8FiveSq.rootChar_pow_five_of_mem hE₀p D hx ha v
        rw [show Nat.card K = 5 * (m - 1) + 4 by omega, pow_add, pow_mul, h5, one_pow, one_mul,
          inv_eq_iff_mul_eq_one, ← pow_succ]
        exact h5
    rwa [hring] at key

theorem e8FourUniNative_five_even
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4) (E₀ : Subgroup (adjointGroup .E8 K))
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀c : Nat.card E₀ = 5 ^ 2) (hN : ¬ NormalizesRGroup 2 E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpK : ¬ 5 ∣ Nat.card K := e8Five_not_dvd_of_orderOf_eq_four he
  have hpq1 : ¬ 5 ∣ Nat.card K - 1 := e8Five_not_dvd_pred_of_orderOf_eq_four hq1 he
  have hn' : ¬ CFSG.LieType.SeitzGeneration.ExcHighThree.NormalizesRNative Tag.E8 K E₀ := fun h => hN (by
    rw [← hring]
    exact CFSG.LieType.SeitzGeneration.ExcHigh.normalizesRGroup_of_native h)
  obtain ⟨D, hD⟩ := e8Five_regular_datum hpK hE₀p hE₀c hn'
  obtain ⟨k, hk⟩ := exists_conj_le_of_frameDatum hE₀p D
    (e8FiveFourFrameDatum_holds K he D.Fr D.hFr D.w
      (e8FiveFourSquare_holds K he E₀ hE₀p hE₀c D hD))
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_two_conj (p := 5)
    (⨆ k, e8D8Chain K k) (e8D4Group K)
    (weylWordElt .E8 K e8Word) e8D4Group_le_d8 e8D4Group_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_d8Chain_le_uniClosure_even Nat.prime_five le_rfl hpK hpq1 Ψ hker
      hrange E hE hEp hEc) E₀ hE₀p hE₀c ⟨k, hk⟩

end E8D8

section E7TwoEven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem closure_uniCen_prod_of_plane {A B : Type*} [Group A] [Group B] {p r : ℕ} [hp : Fact p.Prime]
    (hA : ∀ F : Subgroup A, IsElemAbelian p F → Nat.card F ≤ p)
    (hAr : Subgroup.closure {a : A | ∃ n : ℕ, a ^ (r ^ n) = 1} = ⊤)
    (hBr : Subgroup.closure {b : B | ∃ n : ℕ, b ^ (r ^ n) = 1} = ⊤)
    (hB : ∀ F : Subgroup B, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {b : B | ∃ x ∈ F, x ≠ 1 ∧ Commute b x ∧ ∃ n : ℕ, b ^ (r ^ n) = 1} = ⊤)
    (F : Subgroup (A × B)) (hF : IsElemAbelian p F) (hc : Nat.card F = p ^ 2) :
    Subgroup.closure {h : A × B | ∃ x ∈ F, x ≠ 1 ∧ Commute h x ∧ ∃ n : ℕ, h ^ (r ^ n) = 1} = ⊤ := by
  classical
  set S : Set (A × B) := {h | ∃ x ∈ F, x ≠ 1 ∧ Commute h x ∧ ∃ n : ℕ, h ^ (r ^ n) = 1} with hS
  have h1 : ∃ y ∈ F, y ≠ 1 ∧ y.1 = 1 := by
    by_contra hcon
    push Not at hcon
    have hdis : Disjoint F (MonoidHom.fst A B).ker := by
      rw [Subgroup.disjoint_def]
      intro x hx hx1
      by_contra hne
      exact hcon x hx hne (MonoidHom.mem_ker.1 hx1)
    have hcard := CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker
      (MonoidHom.fst A B) hdis
    have hle := hA _ (hF.map (MonoidHom.fst A B))
    rw [hcard, hc] at hle
    have hp2 := hp.out.two_le
    nlinarith
  obtain ⟨y, hyF, hy1, hyfst⟩ := h1
  have hA1 : ∀ a : A, (a, (1 : B)) ∈ Subgroup.closure S := by
    intro a
    have ha : a ∈ Subgroup.closure {a : A | ∃ n : ℕ, a ^ (r ^ n) = 1} := by
      rw [hAr]
      exact Subgroup.mem_top _
    have hmap := Subgroup.mem_map_of_mem (MonoidHom.inl A B) ha
    rw [MonoidHom.map_closure] at hmap
    refine Subgroup.closure_mono ?_ hmap
    rintro _ ⟨a', ⟨n, hn⟩, rfl⟩
    refine ⟨y, hyF, hy1, Prod.ext (by simp [hyfst]) (by simp), n, ?_⟩
    rw [← map_pow, hn, map_one]
  have hB1 : ∀ b : B, ((1 : A), b) ∈ Subgroup.closure S := by
    by_cases hx : ∃ x ∈ F, x ≠ 1 ∧ x.2 = 1
    · obtain ⟨x, hxF, hx1, hx2⟩ := hx
      intro b
      have hb : b ∈ Subgroup.closure {b : B | ∃ n : ℕ, b ^ (r ^ n) = 1} := by
        rw [hBr]
        exact Subgroup.mem_top _
      have hmap := Subgroup.mem_map_of_mem (MonoidHom.inr A B) hb
      rw [MonoidHom.map_closure] at hmap
      refine Subgroup.closure_mono ?_ hmap
      rintro _ ⟨b', ⟨n, hn⟩, rfl⟩
      refine ⟨x, hxF, hx1, Prod.ext (by simp) (by simp [hx2]), n, ?_⟩
      rw [← map_pow, hn, map_one]
    · push Not at hx
      have hdis : Disjoint F (MonoidHom.snd A B).ker := by
        rw [Subgroup.disjoint_def]
        intro x hx' hx1
        by_contra hne
        exact hx x hx' hne (MonoidHom.mem_ker.1 hx1)
      have hFB : IsElemAbelian p (F.map (MonoidHom.snd A B)) := hF.map _
      have hcardFB : Nat.card (F.map (MonoidHom.snd A B)) = p ^ 2 := by
        rw [CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker _ hdis, hc]
      have htop := hB _ hFB hcardFB
      intro b
      have hb : b ∈ Subgroup.closure {b : B | ∃ f ∈ F.map (MonoidHom.snd A B), f ≠ 1 ∧
          Commute b f ∧ ∃ n : ℕ, b ^ (r ^ n) = 1} := by
        rw [htop]
        exact Subgroup.mem_top _
      have hmap := Subgroup.mem_map_of_mem (MonoidHom.inr A B) hb
      rw [MonoidHom.map_closure] at hmap
      refine Subgroup.closure_mono ?_ hmap
      rintro _ ⟨b', ⟨_, ⟨x, hxF, rfl⟩, hf1, hcb, n, hn⟩, rfl⟩
      refine ⟨x, hxF, fun h => hf1 (by simp [h]), ?_, n, ?_⟩
      · exact Prod.ext (by simp) (by simpa using hcb.eq)
      · rw [← map_pow, hn, map_one]
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have := (Subgroup.closure S).mul_mem (hA1 a) (hB1 b)
  simpa using this

theorem range_le_uniClosure_of_cover {H G : Type*} [Group H] [Group G] [Finite H] {p r : ℕ}
    [Fact p.Prime] (ψ : H →* G) (hker : ¬ p ∣ Nat.card ψ.ker)
    (hH : ∀ F : Subgroup H, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H | ∃ x ∈ F, x ≠ 1 ∧ Commute h x ∧ ∃ n : ℕ, h ^ (r ^ n) = 1} = ⊤)
    (F : Subgroup G) (hF : F ≤ ψ.range) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    ψ.range ≤ Subgroup.closure {g | ∃ x ∈ F, x ≠ 1 ∧ Commute g x ∧ ∃ n : ℕ, g ^ (r ^ n) = 1} := by
  classical
  set ψ' : H →* ψ.range := ψ.rangeRestrict with hψ'
  have hker' : ¬ p ∣ Nat.card ψ'.ker := by
    rw [hψ', ψ.ker_rangeRestrict]
    exact hker
  have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup F := IsPGroup.commGroupOfCardEqPrimeSq hFc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : F) ⟨b, hb⟩)
  set F1 : Subgroup ψ.range := F.subgroupOf ψ.range with hF1def
  have hF1 : IsElemAbelian p F1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hFp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker ψ' ψ.rangeRestrict_surjective hker' hF1
  have hcardF1 : Nat.card F1 = p ^ 2 := by
    rw [← hFc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← hcardF1, ← hmapE', CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker ψ' hdisE']
  have htop := hH E' hE'ea hcardE'
  intro g hg
  obtain ⟨h, rfl⟩ := hg
  have hh : h ∈ Subgroup.closure {h : H | ∃ x ∈ E', x ≠ 1 ∧ Commute h x ∧
      ∃ n : ℕ, h ^ (r ^ n) = 1} := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmap : (Subgroup.closure {h : H | ∃ x ∈ E', x ≠ 1 ∧ Commute h x ∧
      ∃ n : ℕ, h ^ (r ^ n) = 1}).map ψ ≤
      Subgroup.closure {g | ∃ x ∈ F, x ≠ 1 ∧ Commute g x ∧ ∃ n : ℕ, g ^ (r ^ n) = 1} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k, ⟨x, hx, hx1, hkx, n, hn⟩, rfl⟩
    have hxF : ψ x ∈ F := by
      have h1 : ψ' x ∈ F1 := hmapE' ▸ ⟨x, hx, rfl⟩
      exact h1
    have hx1' : ψ x ≠ 1 := by
      intro h1
      apply hx1
      refine Subgroup.disjoint_def.mp hdisE' hx ?_
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    exact Subgroup.subset_closure ⟨ψ x, hxF, hx1', hkx.map ψ, n, by rw [← map_pow, hn, map_one]⟩
  exact hmap ⟨h, hh, rfl⟩

theorem closure_two_pow_eq_top_of_isQuasisimple {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) :
    Subgroup.closure {x : X | ∃ n : ℕ, x ^ (2 ^ n) = 1} = ⊤ := by
  have hq : CFSG.IsQuasisimple ↥(⊤ : Subgroup X) :=
    CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hX
  have h := closure_two_pow_eq_top_of_quasisimple (G := X) (X := ⊤) hq
  rw [eq_top_iff]
  intro y _
  have hy : (⟨y, Subgroup.mem_top y⟩ : ↥(⊤ : Subgroup X)) ∈
      Subgroup.closure {x : ↥(⊤ : Subgroup X) | ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
    rw [h]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem (⊤ : Subgroup X).subtype hy
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨z, ⟨n, hn⟩, rfl⟩
  exact ⟨n, by rw [← map_pow, hn, map_one]⟩

theorem closure_uniCen_spinPlus_even {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hpq1 : ¬ p ∣ Nat.card K - 1) (F : Subgroup (spinGroup (quadPlus n K))) (hF : IsElemAbelian p F)
    (hc : Nat.card F = p ^ 2) :
    Subgroup.closure {g | ∃ x ∈ F, x ≠ 1 ∧ Commute g x ∧ ∃ m : ℕ, g ^ (2 ^ m) = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn3 : 3 ≤ n := by omega
  have hring : ringChar K = 2 := ringChar.eq K 2
  haveI : NeZero n := ⟨by omega⟩
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have : Finite (spinGroup (quadPlus n K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := n) (K := K) hn3
  set π := spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus n K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus n K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hcen2 := not_two_dvd_card_center_spin_quadPlus_even (K := K) hn3
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus n K))) := by
      rw [hZ]
    exact hd.trans this
  have hrcop : (Nat.card π.ker).Coprime (ringChar K ^ 2) := by
    have h' : ¬ 2 ∣ Nat.card π.ker := by
      intro hd
      apply hcen2
      have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus n K))) := by
        rw [hZ]
      exact hd.trans this
    rw [hring]
    exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h').symm
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus n K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hEbarea : IsElemAbelian p (F.map π) := hF.map π
  have hcardEbar : Nat.card (F.map π) = p ^ 2 := by
    rw [CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker π
      (disjoint_ker_of_exponent π hπcop hF.2), hc]
  have hmodel := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e.orthSq_plusPlanes (r := n)
    hn hp hp5 hpK (F.map π) hEbarea hcardEbar
  have hG := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_quotient π
    hπsurj hZ.le hπcop hrcop hperf F hF.2 hmodel
  rw [eq_top_iff, ← hG]
  refine Subgroup.closure_mono ?_
  rintro g ⟨x, hx, hx1, hg, hgr⟩
  rw [hring] at hgr
  exact ⟨x, hx, hx1, hg, 2, hgr⟩

theorem not_seven_dvd_two_pow_add_one_even (f : ℕ) : ¬ 7 ∣ 2 ^ f + 1 := by
  have h : 2 ^ f % 7 = 1 ∨ 2 ^ f % 7 = 2 ∨ 2 ^ f % 7 = 4 := by
    induction f with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  intro hd
  generalize 2 ^ f = x at h hd
  omega

theorem e7A1D6_le_uniClosure_even {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (F : Subgroup (adjointGroup .E7 K)) (hF : F ≤ e7A1D6 K) (hFp : ∀ x ∈ F, x ^ p = 1)
    (hFc : Nat.card F = p ^ 2) :
    e7A1D6 K ≤ Subgroup.closure {g | ∃ x ∈ F, x ≠ 1 ∧ Commute g x ∧ ∃ m : ℕ, g ^ (2 ^ m) = 1} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hpK0 : (p : K) ≠ 0 :=
    CFSG.LieType.SeitzGeneration.ExcHigh.natCast_ne_zero_of_not_dvd_card hp hpK
  have hn3 : 3 ≤ 6 := by norm_num
  have : Nonempty (Fin 6 ⊕ Fin 6) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 6 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D6_E7 K
  obtain ⟨ρ, hρi, hρr⟩ := exists_sl2_hom_rootPairE7 (K := K)
    CFSG.ComponentClassification.CatLeafProof.isRoot_e7Theta
  have hcentr : e7D6Group K ≤ Subgroup.centralizer
      (rootPairE7 K CFSG.ComponentClassification.CatLeafProof.e7Theta : Set (adjointGroup .E7 K)) := by
    refine iSup_le fun k => ?_
    intro y hy x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := e7Theta_orth k
    exact CFSG.ComponentClassification.CatLeafProof.commutes_rootPair_of_noG2 (K := K)
      CFSG.LieType.Steinberg.Adjoint.noG2_E7 CFSG.ComponentClassification.CatLeafProof.isRoot_e7Theta
      (isRoot_single _ _) h1 h2 h3 h4 h5 x hx y hy
  have hcomm : ∀ (a : SL(2, K)) (t : spinGroup (quadPlus 6 K)), Commute (ρ a) (Ψ t) := by
    intro a t
    have hx : ρ a ∈ rootPairE7 K CFSG.ComponentClassification.CatLeafProof.e7Theta := hρr ▸ ⟨a, rfl⟩
    have hy : Ψ t ∈ e7D6Group K := hrange ▸ ⟨t, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (hcentr hy) _ hx
  let ψ : SL(2, K) × spinGroup (quadPlus 6 K) →* adjointGroup .E7 K :=
    MonoidHom.noncommCoprod ρ Ψ hcomm
  have hrangeψ : ψ.range = e7A1D6 K := by
    rw [MonoidHom.noncommCoprod_range, hρr, hrange, e7A1D6, sup_comm]
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 6) (K := K) hn3
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 6 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 6 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hψker : ¬ p ∣ Nat.card ψ.ker := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
    obtain ⟨⟨a, s⟩, hxk⟩ := x
    have hxk' : ρ a * Ψ s = 1 := hxk
    have hxp : (a, s) ^ p = 1 := by
      have := pow_orderOf_eq_one (⟨(a, s), hxk⟩ : ψ.ker)
      rw [hx] at this
      exact congrArg Subtype.val this
    have hap : a ^ p = 1 := congrArg Prod.fst hxp
    have hsp : s ^ p = 1 := congrArg Prod.snd hxp
    have hacent : a ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro b
      have h1 : ρ a = (Ψ s)⁻¹ := eq_inv_of_mul_eq_one_left hxk'
      have h2 : Commute (ρ b) (ρ a) := by
        rw [h1]
        exact (hcomm b s).inv_right
      apply hρi
      rw [map_mul, map_mul]
      exact h2.eq
    obtain ⟨c, hc, hca⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hacent
    simp only [Fintype.card_fin] at hc
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hca, ← map_mul, ← pow_two, hc, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have ha1 : a = 1 := by
      have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
      have hd2 : orderOf a ∣ Nat.gcd 2 p :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rwa [pow_two])) (orderOf_dvd_of_pow_eq_one hap)
      rw [hcop] at hd2
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd2)
    have hΨs : Ψ s = 1 := by
      rw [ha1, map_one, one_mul] at hxk'
      exact hxk'
    have hs1 : s = 1 :=
      eq_one_of_pow_eq_one_of_not_dvd hcen (hker (MonoidHom.mem_ker.2 hΨs)) hsp
    have hx1 : (⟨(a, s), hxk⟩ : ψ.ker) = 1 := Subtype.ext (Prod.ext ha1 hs1)
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hH : ∀ F' : Subgroup (SL(2, K) × spinGroup (quadPlus 6 K)), IsElemAbelian p F' →
      Nat.card F' = p ^ 2 → Subgroup.closure {h | ∃ x ∈ F', x ≠ 1 ∧ Commute h x ∧
        ∃ n : ℕ, h ^ (2 ^ n) = 1} = ⊤ :=
    fun F' hF' hc' => closure_uniCen_prod_of_plane
      (fun F'' hF'' => card_le_of_isElemAbelian_specialLinear_two hpK0 hF'')
      (closure_two_pow_SL_eq_top 2 K)
      (closure_two_pow_eq_top_of_isQuasisimple (isQuasisimple_spinGroup_quadPlus hn3))
      (fun F'' hF'' hc'' => closure_uniCen_spinPlus_even (by norm_num) hp hp5 hpK hpq1 F'' hF'' hc'')
      F' hF' hc'
  have h := range_le_uniClosure_of_cover ψ hψker hH F (hrangeψ ▸ hF) hFp hFc
  rwa [hrangeψ] at h

theorem e7TwoUniNative_even (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ) [hpF : Fact p.Prime]
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E7 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2)
    (hN : ¬ NormalizesRGroup 2 E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hSyl : ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K := by
    rcases (by omega : p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ 11 ≤ p) with
      rfl | h | rfl | h | h | h | h11
    · exact e7TwoSylowFive K hpq E₀ hE₀p hE₀c (by rw [hring]; exact hN)
    · subst h; exact absurd hpF.out (by norm_num)
    · exfalso
      have : Fintype K := Fintype.ofFinite K
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨f, -, hf⟩ := FiniteField.card K 2
      have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
      rw [hK] at hpq
      exact not_seven_dvd_two_pow_add_one_even f hpq
    · subst h; exact absurd hpF.out (by norm_num)
    · subst h; exact absurd hpF.out (by norm_num)
    · subst h; exact absurd hpF.out (by norm_num)
    · exact e7TwoSylow K p h11 hpq E₀ hE₀p hE₀c
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_two_conj (p := p)
    (e7A1D6 K) (e7FrameGroup K)
    (weylWordElt .E7 K e7Word) e7FrameGroup_le_e7A1D6 e7FrameGroup_le_conj_e7A1D6
    (fun M hX hn => eq_top_of_e7A1D6_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => e7A1D6_le_uniClosure_even hpF.out hp5 hpq E hE hEp hEc) E₀ hE₀p hE₀c hSyl

end E7TwoEven

section CatEven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

set_option linter.unusedSectionVars false

theorem dvd_sub_one_of_orderOf_eq_one_even {p q : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) = 1) : p ∣ q - 1 := by
  have h1 : ((q : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.1 h
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, h1, Nat.cast_one, sub_self]

theorem dvd_add_one_of_orderOf_eq_two_even {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 2) : p ∣ q + 1 := by
  haveI := Fact.mk hp
  have h2 : ((q : ℕ) : ZMod p) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
  have h1 : ((q : ℕ) : ZMod p) ≠ 1 := fun h1 => by rw [h1, orderOf_one] at h; omega
  have hm : (((q : ℕ) : ZMod p) - 1) * (((q : ℕ) : ZMod p) + 1) = 0 := by linear_combination h2
  have hz : ((q : ℕ) : ZMod p) + 1 = 0 := (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 h1)
  exact (ZMod.natCast_eq_zero_iff (q + 1) p).1 (by push_cast; exact hz)

theorem prime_eq_of_orderOf_two {p : ℕ} (hp : p.Prime) :
    (orderOf ((2 : ℕ) : ZMod p) = 3 → p = 7) ∧ (orderOf ((2 : ℕ) : ZMod p) = 4 → p ∣ 15) := by
  haveI := Fact.mk hp
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h3 : ((2 : ℕ) : ZMod p) ^ 3 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    have h7 : ((7 : ℕ) : ZMod p) = 0 := by
      have e : ((7 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) ^ 3 - 1 := by push_cast; ring
      rw [e, h3, sub_self]
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 ((ZMod.natCast_eq_zero_iff 7 p).1 h7)
  · have h4 : ((2 : ℕ) : ZMod p) ^ 4 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    have h15 : ((15 : ℕ) : ZMod p) = 0 := by
      have e : ((15 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) ^ 4 - 1 := by push_cast; ring
      rw [e, h4, sub_self]
    exact (ZMod.natCast_eq_zero_iff 15 p).1 h15

theorem degCount_F4_two_le {e : ℕ} (h : 2 ≤ CFSG.LieType.SeitzGeneration.degCount Tag.F4 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 := CFSG.LieType.SeitzGeneration.le_thirty_of_degCount_pos (τ := Tag.F4) (e := e)
    (by simp) (by omega)
  have key : ∀ e ≤ 30, 2 ≤ CFSG.LieType.SeitzGeneration.degCount Tag.F4 e →
      e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by decide
  exact key e h30 h

theorem degCount_E6_two_le {e : ℕ} (h : 2 ≤ CFSG.LieType.SeitzGeneration.degCount Tag.E6 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 := CFSG.LieType.SeitzGeneration.le_thirty_of_degCount_pos (τ := Tag.E6) (e := e)
    (by simp) (by omega)
  have key : ∀ e ≤ 30, 2 ≤ CFSG.LieType.SeitzGeneration.degCount Tag.E6 e →
      e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by decide
  exact key e h30 h

theorem degCount_E7_two_le {e : ℕ} (h : 2 ≤ CFSG.LieType.SeitzGeneration.degCount Tag.E7 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 := CFSG.LieType.SeitzGeneration.le_thirty_of_degCount_pos (τ := Tag.E7) (e := e)
    (by simp) (by omega)
  have key : ∀ e ≤ 30, 2 ≤ CFSG.LieType.SeitzGeneration.degCount Tag.E7 e →
      e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by decide
  exact key e h30 h

theorem degCount_E8_two_le {e : ℕ} (h : 2 ≤ CFSG.LieType.SeitzGeneration.degCount Tag.E8 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by
  have h30 := CFSG.LieType.SeitzGeneration.le_thirty_of_degCount_pos (τ := Tag.E8) (e := e)
    (by simp) (by omega)
  have key : ∀ e ≤ 30, 2 ≤ CFSG.LieType.SeitzGeneration.degCount Tag.E8 e →
      e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by decide
  exact key e h30 h

theorem uniPlaneGen_cat_even {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (hchar : ∀ q, (c q).characteristic = q.p)
    {q : PrimePower} (hv : (c q).Valid) (hq2 : q.p = 2) {p : ℕ}
    (hnat : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = q.card →
      (Cat ⟨c q, hv⟩ ≃* ↥(adjointGroup τ K)) →
      ∀ E₀ : Subgroup ↥(adjointGroup τ K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
        (¬ ∃ R : Subgroup ↥(adjointGroup τ K), R ≠ ⊥ ∧ IsPGroup 2 R ∧
          ∀ g ∈ E₀, R.map (MulAut.conj g).toMonoidHom = R) →
        Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤)
    {E : Subgroup (MulAut (Cat ⟨c q, hv⟩))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hin : InnerPlane ⟨c q, hv⟩ p E) (hn : ¬ NormalizesRSubgroup ⟨c q, hv⟩ E) :
    UniPlaneGen (c q).characteristic E := by
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  haveI : CharP K 2 := hq2 ▸ hKchar
  rw [hchar, hq2]
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_of_native_uniClosure
    (p := p) (r := 2) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 h3 => hnat K hKq e E₀ h1 h2 h3) hE hc hin ?_
  rintro ⟨R, hR1, hRp, hRn⟩
  exact hn ⟨R, hR1, by rw [hchar, hq2]; exact hRp, hRn⟩

theorem isElementaryAbelian_of_exponent_card {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {E₀ : Subgroup G} (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    CFSG.IsElementaryAbelian p E₀ := by
  let _ : CommGroup E₀ := IsPGroup.commGroupOfCardEqPrimeSq hE₀c
  exact { toIsMulCommutative := IsMulCommutative.of_comm fun a b => mul_comm a b
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
            Subtype.ext (hE₀p x x.2) }

end CatEven

section G2Cat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti

set_option linter.unusedSectionVars false

theorem uniSeitzPlanes_G2_inner_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ IsG2Index d.1 ∧ d.1.characteristic = 2 ∧
      ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq⟩, hch, hn⟩
  obtain rfl : d = .G2 q := hq
  have hq2 : q.p = 2 := by simpa using hch
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  by_cases hpq1 : p ∣ q.card - 1
  · exact absurd (normalizesRSubgroup_G2_of_dvd_sub_one q hv hp hp5 hpq1 (IsPGroup.of_card hc) hin) hn
  refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2
    LieTypeIndex.characteristic_G2 hv hq2 ?_ hE hc hin hn
  intro K _ _ _ hKq e E₀ hE₀p hE₀c _
  have hm : Nat.card K = 2 ^ q.exponent := by rw [hKq, PrimePower.card_def, hq2]
  haveI := (finite_isSimpleGroup_cat_G2 hv).2
  haveI : IsSimpleGroup (adjointGroup .G2 K) := MulEquiv.isSimpleGroup e.symm
  by_cases hpq : p ∣ Nat.card K + 1
  · exact g2UniNative_even (RankThree.PartOne.SEITZ6.maxSL2SL2G2_of_top
      CFSG.Goldschmidt.topStatement) K hp hp5 hm
      q.exponent_pos hpq E₀ hE₀p hE₀c
  · exfalso
    have hK1 : 1 ≤ Nat.card K := Nat.card_pos
    have hnd : ¬ p ∣ Nat.card K ^ 2 - 1 := by
      rw [CFSG.RankThree.PartOne.K128.sq_sub_one_eq _ hK1]
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hpq1 (by rwa [← hKq])
      · exact hpq h
    have : Finite (ModGL .G2 K) := finite_modGL
    have hdvd : p ∣ Nat.card (adjointGroup .G2 K) := by
      have h1 := Subgroup.card_subgroup_dvd_card E₀
      rw [hE₀c] at h1
      exact (dvd_pow_self p two_ne_zero).trans h1
    have h1 := CFSG.RankThree.PartOne.K128.pRank_le_one_G2 K hp hp5 hm q.exponent_pos hdvd hnd
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt E₀
      (isElementaryAbelian_of_exponent_card hE₀p hE₀c) hE₀c
    omega

end G2Cat

section ExcCat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.Timmesfeld.ExceptionalOrders

set_option linter.unusedSectionVars false

theorem uniSeitzPlanes_F4_inner_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : PrimePower, d.1 = .F4 q ∧ ¬ (q.card = 2 ∧ (p = 5 ∨ p = 7))) ∧
      d.1.characteristic = 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, hq57⟩, hch, hn⟩
  obtain rfl : d = .F4 q := hq
  have hq2 : q.p = 2 := by simpa using hch
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ≠ q.p := fun h => hpd (by rw [LieTypeIndex.characteristic_F4]; exact h)
  have hq1 : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  set e := orderOf ((q.card : ℕ) : ZMod p) with he
  by_cases hcnt : CFSG.LieType.SeitzGeneration.degCount Tag.F4 e ≤ 1
  · exact (false_of_inner_plane_of_rankLE1 hp (conj_injective_cat_F4 q hv)
      (rankLE1_cat_F4 q hv hp hpq hcnt) hE hc hin).elim
  have hq4 : q.card ≠ 2 → 4 ≤ q.card := by
    intro h2
    rw [PrimePower.card_def, hq2] at h2 ⊢
    rcases (show q.exponent = 1 ∨ 2 ≤ q.exponent by have := q.exponent_pos; omega) with h1 | h1
    · rw [h1] at h2
      exact absurd rfl h2
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h1
  rcases degCount_F4_two_le (e := e) (by omega) with h1 | h2 | h3 | h4 | h6
  · exact absurd (normalizesRSubgroup_F4_of_dvd_sub_one q hv hp hp5
      (dvd_sub_one_of_orderOf_eq_one_even hq1 (he ▸ h1)) (IsPGroup.of_card hc) hin) hn
  · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
      LieTypeIndex.characteristic_F4 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c _
    exact f4TwoUniNative_even K p hp5 (by rw [hKq]; exact dvd_add_one_of_orderOf_eq_two_even hp (he ▸ h2))
      E₀ hE₀p hE₀c
  · have hq4' : 4 ≤ q.card := hq4 fun h => hq57 ⟨h, Or.inr
      ((prime_eq_of_orderOf_two hp).1 (by rw [← h]; exact he ▸ h3))⟩
    refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
      LieTypeIndex.characteristic_F4 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c _
    exact f4ThreeUniNative_even K (by rw [hKq]; exact hq4') hp hp5 (by rw [hKq]; exact he ▸ h3) E₀ hE₀p hE₀c
  · have hq4' : 4 ≤ q.card := hq4 fun h => by
      have h15 := (prime_eq_of_orderOf_two hp).2 (by rw [← h]; exact he ▸ h4)
      have h15' : p ∣ 3 * 5 := by norm_num; exact h15
      rcases (Nat.Prime.dvd_mul hp).1 h15' with h3' | h5'
      · have := Nat.le_of_dvd (by norm_num) h3'
        omega
      · exact hq57 ⟨h, Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5')⟩
    refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
      LieTypeIndex.characteristic_F4 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c _
    exact f4FourUniNative_even K (by rw [hKq]; exact hq4') p hp5
      (by rw [hKq]; exact CFSG.LieType.SeitzGeneration.dvd_sq_add_one_of_orderOf_eq_four hp (he ▸ h4))
      E₀ hE₀p hE₀c
  · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
      LieTypeIndex.characteristic_F4 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c _
    have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 6 := by rw [hKq]; exact he ▸ h6
    exact twClassUniNative_even TwClass.f4Six twClassLeaves_f4Six K
      (three_le_of_orderOf_six hp hp5 hordK) hp hp5 hordK E₀ hE₀p hE₀c

theorem uniSeitzPlanes_E8_inner_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : PrimePower, d.1 = .E8 q ∧ ¬ (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨
        orderOf ((q.card : ℕ) : ZMod p) = 6)) ∧
      d.1.characteristic = 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, hcls⟩, hch, hn⟩
  obtain rfl : d = .E8 q := hq
  have hq2 : q.p = 2 := by simpa using hch
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ≠ q.p := fun h => hpd (by rw [LieTypeIndex.characteristic_E8]; exact h)
  have hq1 : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  set e := orderOf ((q.card : ℕ) : ZMod p) with he
  by_cases hcnt : CFSG.LieType.SeitzGeneration.degCount Tag.E8 e ≤ 1
  · exact (false_of_inner_plane_of_rankLE1 hp (conj_injective_cat_E8 q hv)
      (rankLE1_cat_E8 q hv hp hpq hcnt) hE hc hin).elim
  rcases degCount_E8_two_le (e := e) (by omega) with h1 | h2 | h3 | h4 | h5 | h6 | h8 | h10 | h12
  · have hpq1 := dvd_sub_one_of_orderOf_eq_one_even hq1 (he ▸ h1)
    rcases (by omega : p = 5 ∨ p = 6 ∨ 7 ≤ p) with rfl | rfl | hp7
    · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
        LieTypeIndex.characteristic_E8 hv hq2 ?_ hE hc hin hn
      intro K _ _ _ hKq _ E₀ hE₀p hE₀c hN
      have hrc : ringChar K = 2 := ringChar.eq K 2
      have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.e8OneUniNative_five K
        (by rw [hKq]; exact hpq1) E₀ hE₀p hE₀c (by rw [hrc]; exact hN)
      rwa [hrc] at h
    · exact absurd hp (by norm_num)
    · exact absurd (normalizesRSubgroup_E8_of_dvd_sub_one q hv hp hp7 hpq1 (IsPGroup.of_card hc) hin) hn
  · have hpq1 := dvd_add_one_of_orderOf_eq_two_even hp (he ▸ h2)
    refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      LieTypeIndex.characteristic_E8 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c hN
    rcases (by omega : p = 5 ∨ p = 6 ∨ 7 ≤ p) with rfl | rfl | hp7
    · exact e8TwoUniNative_five_even K (by rw [hKq]; exact hpq1) E₀ hE₀p hE₀c hN
    · exact absurd hp (by norm_num)
    · exact e8TwoUniNative_even K p hp7 (by rw [hKq]; exact hpq1) E₀ hE₀p hE₀c hN
  · exact absurd (Or.inl (he ▸ h3)) hcls
  · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      LieTypeIndex.characteristic_E8 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c hN
    have he4 : orderOf ((Nat.card K : ℕ) : ZMod p) = 4 := by rw [hKq]; exact he ▸ h4
    rcases (by omega : p = 5 ∨ p = 6 ∨ 7 ≤ p) with rfl | rfl | hp7
    · exact e8FourUniNative_five_even K he4 E₀ hE₀p hE₀c hN
    · exact absurd hp (by norm_num)
    · exact e8FourUniNative_even K p hp7 he4 E₀ hE₀p hE₀c
  · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      LieTypeIndex.characteristic_E8 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c _
    exact e8FiveUniNative_even K hp (by rw [hKq]; exact he ▸ h5) E₀ hE₀p hE₀c
  · exact absurd (Or.inr (he ▸ h6)) hcls
  · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      LieTypeIndex.characteristic_E8 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c _
    exact e8EightUniNative_even K (by rw [hKq]; exact he ▸ h8) E₀ hE₀p hE₀c
  · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      LieTypeIndex.characteristic_E8 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c _
    exact twClassUniNative_even TwClass.e8Ten twClassLeaves_e8Ten K Finite.one_lt_card hp hp5
      (by rw [hKq]; exact he ▸ h10) E₀ hE₀p hE₀c
  · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      LieTypeIndex.characteristic_E8 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c _
    exact twClassUniNative_even TwClass.e8Twelve twClassLeaves_e8Twelve K Finite.one_lt_card hp hp5
      (by rw [hKq]; exact he ▸ h12) E₀ hE₀p hE₀c

theorem uniSeitzPlanes_E6_inner_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : PrimePower, d.1 = .E6 q ∧ orderOf ((q.card : ℕ) : ZMod p) ≠ 3) ∧
      d.1.characteristic = 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, hcls⟩, hch, hn⟩
  obtain rfl : d = .E6 q := hq
  have hq2 : q.p = 2 := by simpa using hch
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ≠ q.p := fun h => hpd (by rw [LieTypeIndex.characteristic_E6]; exact h)
  have hq1 : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  set e := orderOf ((q.card : ℕ) : ZMod p) with he
  by_cases hcnt : CFSG.LieType.SeitzGeneration.degCount Tag.E6 e ≤ 1
  · exact (false_of_inner_plane_of_rankLE1 hp (conj_injective_cat_E6 q hv)
      (rankLE1_cat_E6 q hv hp hpq hcnt) hE hc hin).elim
  have hsq : q.card ^ 2 - 1 = (q.card - 1) * (q.card + 1) := by
    have : 1 ≤ q.card ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hq1, this]
    ring
  rcases degCount_E6_two_le (e := e) (by omega) with h1 | h2 | h3 | h4 | h6
  · refine absurd (normalizesRSubgroup_E6_of_dvd_sq_sub_one q hv hp hp5 ?_ (IsPGroup.of_card hc) hin) hn
    rw [hsq]
    exact Dvd.dvd.mul_right (dvd_sub_one_of_orderOf_eq_one_even hq1 (he ▸ h1)) _
  · refine absurd (normalizesRSubgroup_E6_of_dvd_sq_sub_one q hv hp hp5 ?_ (IsPGroup.of_card hc) hin) hn
    rw [hsq]
    exact Dvd.dvd.mul_left (dvd_add_one_of_orderOf_eq_two_even hp (he ▸ h2)) _
  · exact absurd (he ▸ h3) hcls
  · exact absurd (CFSG.LieType.SeitzGeneration.normalizesRSubgroup_E6_phi4 q hv hp
      (CFSG.LieType.SeitzGeneration.dvd_sq_add_one_of_orderOf_eq_four hp (he ▸ h4))
      (IsPGroup.of_card hc) hin) hn
  · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
      LieTypeIndex.characteristic_E6 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c _
    have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 6 := by rw [hKq]; exact he ▸ h6
    exact twClassUniNative_even TwClass.e6Six twClassLeaves_e6Six K
      (three_le_of_orderOf_six hp hp5 hordK) hp hp5 hordK E₀ hE₀p hE₀c

theorem uniSeitzPlanes_E7_inner_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : PrimePower, d.1 = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) ≠ 6) ∧
      d.1.characteristic = 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, hcls⟩, hch, hn⟩
  obtain rfl : d = .E7 q := hq
  have hq2 : q.p = 2 := by simpa using hch
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ≠ q.p := fun h => hpd (by rw [LieTypeIndex.characteristic_E7]; exact h)
  have hq1 : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  set e := orderOf ((q.card : ℕ) : ZMod p) with he
  by_cases hcnt : CFSG.LieType.SeitzGeneration.degCount Tag.E7 e ≤ 1
  · exact (false_of_inner_plane_of_rankLE1 hp (conj_injective_cat_E7 q hv)
      (rankLE1_cat_E7 q hv hp hpq hcnt) hE hc hin).elim
  rcases degCount_E7_two_le (e := e) (by omega) with h1 | h2 | h3 | h4 | h6
  · exfalso
    have hc1 : ((q.card : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.1 (he ▸ h1)
    by_cases hp7 : p = 7
    · subst hp7
      refine hn (normalizesRSubgroup_E7_A6_of_not_dvd_index q hv hp ?_ (IsPGroup.of_card hc) hin)
      intro hd
      have h0 := (ZMod.natCast_eq_zero_iff _ 7).2 hd
      push_cast at h0
      rw [geomSum_cast_of_cast_eq_one 2 4 _ hc1, geomSum_cast_of_cast_eq_one 2 5 _ hc1,
        geomSum_cast_of_cast_eq_one 2 7 _ hc1, geomSum_cast_of_cast_eq_one 4 3 _ hc1,
        geomSum_cast_of_cast_eq_one 18 1 _ hc1] at h0
      have h576 : ((576 : ℕ) : ZMod 7) = 0 := by
        push_cast at h0 ⊢
        linear_combination h0
      have h7 := (ZMod.natCast_eq_zero_iff 576 7).1 h576
      norm_num at h7
    · refine hn (normalizesRSubgroup_E7_of_not_dvd_index q hv hp ?_ (IsPGroup.of_card hc) hin)
      intro hd
      have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
      push_cast at h0
      rw [geomSum_cast_of_cast_eq_one 2 5 _ hc1, geomSum_cast_of_cast_eq_one 2 9 _ hc1,
        geomSum_cast_of_cast_eq_one 14 1 _ hc1] at h0
      have h56 : ((56 : ℕ) : ZMod p) = 0 := by
        push_cast at h0 ⊢
        linear_combination h0
      have h56' : p ∣ 2 ^ 3 * 7 := by
        have := (ZMod.natCast_eq_zero_iff 56 p).1 h56
        norm_num
        exact this
      rcases (Nat.Prime.dvd_mul hp).1 h56' with h2' | h7'
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2')
        omega
      · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7')
  · refine uniPlaneGen_cat_even CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
      LieTypeIndex.characteristic_E7 hv hq2 ?_ hE hc hin hn
    intro K _ _ _ hKq _ E₀ hE₀p hE₀c hN
    exact e7TwoUniNative_even K p hp5
      (by rw [hKq]; exact dvd_add_one_of_orderOf_eq_two_even hp (he ▸ h2)) E₀ hE₀p hE₀c hN
  · exact absurd (normalizesRSubgroup_E7_of_not_dvd_index q hv hp
      (not_dvd_index_E7_of_orderOf_eq_three hp hp5 (he ▸ h3)) (IsPGroup.of_card hc) hin) hn
  · exact absurd (CFSG.LieType.SeitzGeneration.normalizesRSubgroup_E7_phi4 q hv hp hp2
      (CFSG.LieType.SeitzGeneration.dvd_sq_add_one_of_orderOf_eq_four hp (he ▸ h4))
      (IsPGroup.of_card hc) hin) hn
  · exact absurd (he ▸ h6) hcls

theorem uniSeitzPlanes_twE6_inner_vacuous_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : PrimePower, d.1 = .twistedE6 q ∧ (p ∣ q.card - 1 ∨
        CFSG.LieType.SeitzGeneration.degCountTw (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1)) ∧
      ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, hcls⟩, hn⟩
  obtain rfl : d = .twistedE6 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ≠ q.p := fun h => hpd (by rw [LieTypeIndex.characteristic_twistedE6]; exact h)
  exfalso
  rcases hcls with h1 | hcnt
  · exact hn (normalizesRSubgroup_twistedE6_of_dvd_sub_one q hv hp hp5 h1 (IsPGroup.of_card hc) hin)
  · exact false_of_inner_plane_of_rankLE1 hp (conj_injective_cat_twistedE6 q hv)
      (rankLE1_cat_twistedE6 q hv hp hpq hcnt) hE hc hin

end ExcCat

section TrialityEven

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.K1214
open CFSG.RankThree.PartOne.Census3 (IsoLie)

set_option linter.unusedSectionVars false

theorem trialityUni_qplus_even (hmax : Max3D4A1A1Big) {q : PrimePower} (hq : q.p = 2) {K : Type}
    [Group K] [Finite K] [IsSimpleGroup K] (hiso : IsoLie K (.trialityD4 q)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ q.card + 1) (E₁ : Subgroup K) (hE₁p : ∀ x ∈ E₁, x ^ p = 1)
    (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (2 ^ n) = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ q.card := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    omega
  obtain ⟨A, B, F₃, F₁, _, _, hF₃f, hF₁f, ⟨eA⟩, ⟨eB⟩, hcomm, hAB, hmaxAB⟩ :=
    hmax q hq h4 K hiso
  have hQ : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq]
  obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ := CFSG.RankThree.PartOne.CTP.exists_trialityD4_model hq hiso
  have hpq' : p ∣ 2 ^ q.exponent + 1 := by rwa [hQ] at hpq
  have hshape : SylowShape p 2 ((2 ^ q.exponent + 1).factorization p) K :=
    (CFSG.RankThree.PartOne.K128.sylowShape_D4_qplus (ℓ := 2) q.exponent_pos X hX σ hσ hp hp5
      hpq').of_mulEquiv e
  have hKcard := card_isoLie_trialityD4 hq hiso
  have : Finite F₃ := Nat.finite_of_card_ne_zero (by rw [hF₃f]; positivity)
  have : Finite F₁ := Nat.finite_of_card_ne_zero (by rw [hF₁f]; positivity)
  haveI : CharP F₃ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := q.exponent * 3) (by have := q.exponent_pos; omega) (by rw [hF₃f, hQ, ← pow_mul])
  haveI : CharP F₁ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      q.exponent_pos (by rw [hF₁f, hQ])
  have hcardA : Nat.card A = q.card ^ 3 * ((q.card ^ 3) ^ 2 - 1) := by
    rw [Nat.card_congr eA.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF₃f]
  have hcardB : Nat.card B = q.card * (q.card ^ 2 - 1) := by
    rw [Nat.card_congr eB.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF₁f]
  have hcardM : Nat.card ↥(A ⊔ B) = (q.card ^ 3 * ((q.card ^ 3) ^ 2 - 1)) *
      (q.card * (q.card ^ 2 - 1)) := by
    rw [card_sup_pair hAB hcomm, hcardA, hcardB]
  have hidx : (A ⊔ B).index = q.card ^ 8 * (q.card ^ 8 + q.card ^ 4 + 1) := by
    have h1 := Subgroup.index_mul_card (A ⊔ B)
    rw [hcardM, hKcard] at h1
    have hpos : 0 < (q.card ^ 3 * ((q.card ^ 3) ^ 2 - 1)) * (q.card * (q.card ^ 2 - 1)) := by
      have h4 : 4 ≤ q.card ^ 2 := by nlinarith
      have h64 : 4 ≤ (q.card ^ 3) ^ 2 := by
        have : 4 ≤ q.card ^ 3 := by nlinarith [pow_pos (by omega : 0 < q.card) 3]
        nlinarith
      have h5 : 0 < q.card ^ 2 - 1 := by omega
      have h6 : 0 < (q.card ^ 3) ^ 2 - 1 := by omega
      positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    have e6 : (q.card ^ 3) ^ 2 = q.card ^ 6 := by rw [← pow_mul]
    rw [e6]
    ring
  obtain ⟨hnd, hmod⟩ := d4_index_arith hp hp5 hpq
  rw [← hidx] at hnd hmod
  have hQpq : p ∣ q.card ^ 2 - 1 := by
    rw [sq_sub_one_eq_mul (by omega)]
    exact Dvd.dvd.mul_right hpq _
  have hQ3 : p ∣ q.card ^ 3 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow q.card 1 (by decide : Odd 3)
    simpa using hpq.trans h
  have hpA : p ∣ Nat.card A := by
    rw [hcardA, sq_sub_one_eq_mul (Nat.one_le_pow _ _ (by omega))]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hQ3 _) _
  have hpB : p ∣ Nat.card B := by
    rw [hcardB]
    exact Dvd.dvd.mul_left hQpq _
  have hgenSub : ∀ (H : Subgroup K) (F : Type) [Field F] [Finite F] [CharP F 2]
      (eH : H ≃* Matrix.SpecialLinearGroup (Fin 2) F),
      H ≤ Subgroup.closure {x | x ∈ H ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
    intro H F _ _ _ eH x hx
    have hy : eH ⟨x, hx⟩ ∈ Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin 2) F | g ^ 2 = 1} := by
      rw [CFSG.HardMathSupport.Lang.Proving.closure_pow_char_eq_one_eq_top (p := 2)]
      exact Subgroup.mem_top _
    have hle : Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin 2) F | g ^ 2 = 1} ≤
        (Subgroup.closure {x | x ∈ H ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1}).comap
          (H.subtype.comp eH.symm.toMonoidHom) := by
      rw [Subgroup.closure_le]
      intro g hg
      have hg2 : g ^ 2 = 1 := hg
      refine Subgroup.subset_closure ⟨(eH.symm g).2, 1, ?_⟩
      show ((eH.symm g : H) : K) ^ (2 ^ 1) = 1
      rw [pow_one, ← Subgroup.coe_pow, ← map_pow, hg2, map_one, Subgroup.coe_one]
    have := hle hy
    simpa using this
  exact closure_uniCen_eq_top_of_pair A B hAB hcomm hpA hpB hshape (hgenSub A F₃ eA)
    (hgenSub B F₁ eB) hmaxAB hnd hmod E₁ hE₁p hE₁c

theorem trialityBorel_le_normalizer_posUnipotent {K : Type} [Field K] (σ : K →+* K) :
    (graphFixedRootBorel TwistTag.D4 K σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ) ≤
      Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ) : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ)) := by
  intro b hb
  have hbN := graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent (t := TwistTag.D4) (K := K)
    (σ := σ) (Subgroup.mem_subgroupOf.1 hb)
  rw [Subgroup.mem_normalizer_iff] at hbN ⊢
  intro w
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using hbN (w : CFSG.Blueprint.Chevalley.ModGL TwistTag.D4.tag K)

theorem normalizesRSubgroup_trialityD4_of_dvd_pred (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q.card - 1) {E : Subgroup (MulAut (Cat ⟨.trialityD4 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.trialityD4 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.trialityD4 q, hv⟩ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hK3 : Nat.card K = q.p ^ (q.exponent * 3) := by rw [hK, pow_mul]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p (by
      have := q.exponent_pos; omega) hK3
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL TwistTag.D4.tag K) := finite_modGL
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := conj_injective_of_mulEquiv e
    (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot hZ)
  have hpq' : p ∣ q.p ^ q.exponent - 1 := by rw [← PrimePower.card_def]; exact hpq
  have hidx := CFSG.RankThree.PartOne.CTP.not_dvd_index_borel_D4 q.p q.exponent q.prime_p
    q.exponent_pos K hK σ hσ p hp hp5 hpq'
  obtain ⟨-, -, hU⟩ := triality_both_orientations_exact_finite_order q.p q.exponent q.prime_p
    q.exponent_pos K hK 1 (Or.inl rfl) σ.toRingHom (by simpa using hσ)
  have hcardQ : Nat.card ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = (q.p ^ q.exponent) ^ 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).toEquiv, hU]
  have hQ0 : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardQ
    have : 1 < (q.p ^ q.exponent) ^ 12 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt)
    omega
  have hQr : IsPGroup q.p ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    IsPGroup.of_card (n := q.exponent * 12) (by rw [hcardQ, ← pow_mul])
  obtain ⟨R, hR0, hRr, hR⟩ := CFSG.LieType.SeitzGeneration.exists_normalized_of_inner e hidx
    (trialityBorel_le_normalizer_posUnipotent σ.toRingHom) hQ0 hQr hinj hEp hin
  refine ⟨R, hR0, ?_, hR⟩
  simpa [LieTypeIndex.characteristic_trialityD4] using hRr

theorem uniSeitzPlanes_triality_inner_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ d.1.characteristic = 2 ∧
      ¬ NormalizesRSubgroup d E ∧ ∃ q : PrimePower, d.1 = .trialityD4 q ∧
        ¬ (p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, hch, hn, q, hq, h36⟩
  obtain rfl : d = .trialityD4 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_trialityD4 q).symm)
  have h2 : (LieTypeIndex.trialityD4 q).characteristic = 2 := hch
  have hq2 : q.p = 2 := by rwa [LieTypeIndex.characteristic_trialityD4] at h2
  have hq1 : 1 ≤ q.card := by rw [PrimePower.card_def]; exact Nat.one_le_pow _ _ q.prime_p.pos
  by_cases hm : p ∣ q.card - 1
  · exact absurd (normalizesRSubgroup_trialityD4_of_dvd_pred q hv hp hp5 hm (IsPGroup.of_card hc)
      hin) hn
  have hfs := finite_isSimpleGroup_cat_trialityD4 hv
  haveI := hfs.1
  haveI := hfs.2
  have hinj := CFSG.HardMathSupport.Timmesfeld.CrossChar.conj_injective_cat_trialityD4 q hv
  by_cases hp1 : p ∣ q.card + 1
  · show UniPlaneGen (LieTypeIndex.trialityD4 q).characteristic E
    rw [h2]
    refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_of_native_uniClosure
      (p := p) (r := 2) (MulEquiv.refl _) hinj (fun E₀ h1 h3 _ =>
        trialityUni_qplus_even CFSG.RankThree.PartOne.SEITZ7.max3D4A1A1Big_of_certificates hq2
          ⟨hv, ⟨MulEquiv.refl _⟩⟩ hp hp5 hp1 E₀ h1 h3) hE hc hin ?_
    rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (LieTypeIndex.trialityD4 q).characteristic R
    rw [h2]
    exact hRp
  · exfalso
    have hnd : ¬ p ∣ q.card ^ 6 - 1 := by
      intro hd
      have h6 : q.card ^ 6 - 1 = (q.card - 1) * ((q.card + 1) * ((q.card ^ 2 + q.card + 1) *
          (q.card ^ 2 - q.card + 1))) := by
        have hle : q.card ≤ q.card ^ 2 := Nat.le_self_pow (by norm_num) _
        zify [hq1, hle, Nat.one_le_pow 6 _ hq1]
        ring
      rw [h6] at hd
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | hd
      · exact hm h
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | hd
      · exact hp1 h
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · exact h36 (Or.inl h)
      · exact h36 (Or.inr h)
    exact CFSG.LieType.SeitzGeneration.false_of_inner_plane_of_rankLE1 hp hinj
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE1_cat_trialityD4 q hv hp hp2 hpq hnd) hE hc hin

end TrialityEven

section ReeF4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.Open TauCeti

set_option linter.unusedSectionVars false

theorem not_dvd_reeBorel_index_of_dvd_pred {p Q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : 1 ≤ Q)
    (hpq : p ∣ Q - 1) :
    ¬ p ∣ (Q + 1) ^ 2 * (Q ^ 2 + 1) ^ 2 * (Q ^ 2 - Q + 1) * (Q ^ 4 - Q ^ 2 + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : (Q : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff (Q - 1) p).2 hpq
    rw [Nat.cast_sub hQ, Nat.cast_one, sub_eq_zero] at this
    exact this
  have h2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 : Q ^ 2 ≤ Q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  intro hd
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
  push_cast [Nat.cast_sub h2, Nat.cast_sub h4] at h0
  rw [h1] at h0
  have h16 : ((16 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h0
  have h16' : p ∣ 2 ^ 4 := by
    have := (ZMod.natCast_eq_zero_iff 16 p).1 h16
    norm_num
    exact this
  have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h16')
  omega

theorem normalizesRSubgroup_reeF4_of_dvd_pred {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * m + 1) - 1)
    {E : Subgroup (MulAut (Cat ⟨.reeF4 m, hv⟩))} (hEp : IsPGroup p E)
    (hin : InnerPlane ⟨.reeF4 m, hv⟩ p E) : NormalizesRSubgroup ⟨.reeF4 m, hv⟩ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, -, hX, -, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  haveI : Finite (ModGL F4.tag X) := finite_modGL
  have hBΓ : F4.reeFixedBorel X m ≤ F4.reeGamma X m := reeFixedBorel_le_reeGamma
  have hUΓ : F4.reeFixedPosUnipotent X m ≤ F4.reeGamma X m := reeFixedPosUnipotent_le_reeGamma
  have hN := reeGamma_inf_normalizer_reeFixedPosUnipotent (t := F4) (K := X) (a := m)
  have hQ1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have hQ2 : 2 ≤ 2 ^ (2 * m + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcardP : Nat.card ((F4.reeFixedBorel X m).subgroupOf (F4.reeGamma X m)) =
      (2 ^ (2 * m + 1)) ^ 12 * (2 ^ (2 * m + 1) - 1) ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBΓ).toEquiv]
    exact CFSG.RankThree.LargeReeOrder.card_reeFixedBorel hX
  have hcardΓ :=
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion m X hX).1
  have hidx : ((F4.reeFixedBorel X m).subgroupOf (F4.reeGamma X m)).index =
      (2 ^ (2 * m + 1) + 1) ^ 2 * ((2 ^ (2 * m + 1)) ^ 2 + 1) ^ 2 *
        ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1) *
        ((2 ^ (2 * m + 1)) ^ 4 - (2 ^ (2 * m + 1)) ^ 2 + 1) := by
    have h1 := Subgroup.index_mul_card ((F4.reeFixedBorel X m).subgroupOf (F4.reeGamma X m))
    rw [hcardP, hcardΓ] at h1
    have hpos : 0 < (2 ^ (2 * m + 1)) ^ 12 * (2 ^ (2 * m + 1) - 1) ^ 2 := by
      have : 0 < 2 ^ (2 * m + 1) - 1 := by omega
      positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    ring
  have hP : ¬ p ∣ ((F4.reeFixedBorel X m).subgroupOf (F4.reeGamma X m)).index := by
    rw [hidx]
    exact not_dvd_reeBorel_index_of_dvd_pred hp hp5 hQ1 hpq
  have hPQ : (F4.reeFixedBorel X m).subgroupOf (F4.reeGamma X m) ≤
      Subgroup.normalizer (((F4.reeFixedPosUnipotent X m).subgroupOf (F4.reeGamma X m) :
        Subgroup ↥(F4.reeGamma X m)) : Set ↥(F4.reeGamma X m)) := by
    intro b hb
    have hbN : (b : ModGL F4.tag X) ∈
        Subgroup.normalizer (F4.reeFixedPosUnipotent X m : Set (ModGL F4.tag X)) :=
      (hN.symm.le.trans inf_le_right) (Subgroup.mem_subgroupOf.1 hb)
    rw [Subgroup.mem_normalizer_iff] at hbN ⊢
    intro w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hbN (w : ModGL F4.tag X)
  have hcardQ : Nat.card ((F4.reeFixedPosUnipotent X m).subgroupOf (F4.reeGamma X m)) =
      (2 ^ (2 * m + 1)) ^ 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUΓ).toEquiv]
    exact CFSG.LieType.Ree.LargeReeInvolution.card_reeFixedPosUnipotent hX
  have hQ0 : (F4.reeFixedPosUnipotent X m).subgroupOf (F4.reeGamma X m) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardQ
    have : 1 < (2 ^ (2 * m + 1)) ^ 12 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hQr : IsPGroup 2 ((F4.reeFixedPosUnipotent X m).subgroupOf (F4.reeGamma X m)) :=
    IsPGroup.of_card (n := (2 * m + 1) * 12) (by rw [hcardQ, ← pow_mul])
  have hZ := large_Ree_fixed_group_center_trivial m X hX
  have hinj := CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv e
    (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot hZ)
  obtain ⟨R, hR0, hRr, hR⟩ := CFSG.LieType.SeitzGeneration.exists_normalized_of_inner e hP hPQ hQ0
    hQr hinj hEp hin
  refine ⟨R, hR0, ?_, hR⟩
  show IsPGroup (LieTypeIndex.reeF4 m).characteristic R
  rw [LieTypeIndex.characteristic_reeF4]
  exact hRr

theorem uniSeitzPlanes_reeF4_inner_vacuous_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ ¬ NormalizesRSubgroup d E ∧
      ∃ m : ℕ, d.1 = .reeF4 m ∧ (p ∣ 2 ^ (2 * m + 1) - 1 ∨ ¬ p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, hn, m, hm, hcls⟩
  obtain rfl : d = .reeF4 m := hm
  exfalso
  rcases hcls with h1 | hnd
  · exact hn (normalizesRSubgroup_reeF4_of_dvd_pred hv hp hp5 h1 (IsPGroup.of_card hc) hin)
  · obtain ⟨X, _, _, _, -, hX, -, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
    have hinj := CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv e
      (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
        (large_Ree_fixed_group_center_trivial m X hX))
    exact CFSG.LieType.SeitzGeneration.false_of_inner_plane_of_rankLE1 hp hinj
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE1_cat_reeF4 hv hp hp2 hnd) hE hc hin

end ReeF4Even

section Residual

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open TauCeti

set_option linter.unusedSectionVars false

@[expose] def Input23_11TwoRest3 : Prop :=
  Inputs2311c.UniSeitzPlanes fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧ CentralPrimeFree p d.1 ∧
    InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E ∧
    ((∃ q : PrimePower, d.1 = .F4 q ∧ q.card = 2 ∧ (p = 5 ∨ p = 7)) ∨
      (∃ q : PrimePower, d.1 = .E6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 3) ∨
      (∃ q : PrimePower, d.1 = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6) ∨
      (∃ q : PrimePower, d.1 = .E8 q ∧ (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨
        orderOf ((q.card : ℕ) : ZMod p) = 6)) ∨
      (∃ q : PrimePower, d.1 = .twistedE6 q ∧ ¬ p ∣ q.card - 1 ∧
        2 ≤ CFSG.LieType.SeitzGeneration.degCountTw (orderOf ((q.card : ℕ) : ZMod p))) ∨
      (∃ q : PrimePower, d.1 = .trialityD4 q ∧
        (p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1)) ∨
      (IsReeF4Index d.1 ∧ ¬ (p = 5 ∧ d.1 = LieTypeIndex.reeF4 2) ∧ ∃ m : ℕ, d.1 = .reeF4 m ∧
        (p ∣ 2 ^ (2 * m + 1) + 1 ∨ p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1)))

theorem input23_11TwoRest2_of_rest3 (h : Input23_11TwoRest3) : Inputs2311e.Input23_11TwoRest2 := by
  refine ⟨?_, input23_11TwoOn_unitary_nonCpf_even⟩
  intro d p hp hp2 hpd hex E hE hc hs
  obtain ⟨hch, hp5, hcpf, hin, hfam, hn⟩ := hs
  have hres := fun hcls => h d p hp hp2 hpd hex E hE hc ⟨hch, hp5, hcpf, hin, hn, hcls⟩
  obtain ⟨d, hv⟩ := d
  rcases hfam with ((hG | hF | hE6 | hE7 | hE8) | (hD4 | hTw)) | ⟨hR, hR5⟩
  · exact uniSeitzPlanes_G2_inner_even ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hp5, hG, hch, hn⟩
  · obtain ⟨q, rfl⟩ := hF
    by_cases h2 : q.card = 2 ∧ (p = 5 ∨ p = 7)
    · exact hres (Or.inl ⟨q, rfl, h2⟩)
    · exact uniSeitzPlanes_F4_inner_even ⟨_, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hin, hp5, ⟨q, rfl, h2⟩, hch, hn⟩
  · obtain ⟨q, rfl⟩ := hE6
    by_cases h3 : orderOf ((q.card : ℕ) : ZMod p) = 3
    · exact hres (Or.inr (Or.inl ⟨q, rfl, h3⟩))
    · exact uniSeitzPlanes_E6_inner_even ⟨_, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hin, hp5, ⟨q, rfl, h3⟩, hch, hn⟩
  · obtain ⟨q, rfl⟩ := hE7
    by_cases hcl : orderOf ((q.card : ℕ) : ZMod p) = 6
    · exact hres (Or.inr (Or.inr (Or.inl ⟨q, rfl, hcl⟩)))
    · exact uniSeitzPlanes_E7_inner_even ⟨_, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hin, hp5, ⟨q, rfl, hcl⟩, hch, hn⟩
  · obtain ⟨q, rfl⟩ := hE8
    by_cases hcl : orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 6
    · exact hres (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, hcl⟩))))
    · exact uniSeitzPlanes_E8_inner_even ⟨_, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hin, hp5, ⟨q, rfl, hcl⟩, hch, hn⟩
  · obtain ⟨q, rfl⟩ := hD4
    by_cases h36 : p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1
    · exact hres (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, h36⟩))))))
    · exact uniSeitzPlanes_triality_inner_even ⟨_, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hin, hp5, hch, hn, q, rfl, h36⟩
  · obtain ⟨q, rfl⟩ := hTw
    by_cases hcl : ¬ p ∣ q.card - 1 ∧
        2 ≤ CFSG.LieType.SeitzGeneration.degCountTw (orderOf ((q.card : ℕ) : ZMod p))
    · exact hres (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, hcl⟩)))))
    · refine uniSeitzPlanes_twE6_inner_vacuous_even ⟨_, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hin, hp5, ⟨q, rfl, ?_⟩, hn⟩
      by_cases h1 : p ∣ q.card - 1
      · exact Or.inl h1
      · exact Or.inr (by omega)
  · obtain ⟨m, hm⟩ := hR
    by_cases hcl : p ∣ 2 ^ (2 * m + 1) - 1 ∨ ¬ p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1
    · exact uniSeitzPlanes_reeF4_inner_vacuous_even ⟨d, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hin, hp5, hn, m, hm, hcl⟩
    · push Not at hcl
      obtain ⟨h1, h4⟩ := hcl
      have hQ1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
      have hfac : (2 ^ (2 * m + 1)) ^ 4 - 1 = (2 ^ (2 * m + 1) - 1) *
          ((2 ^ (2 * m + 1) + 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1)) := by
        have h4' : 1 ≤ (2 ^ (2 * m + 1)) ^ 4 := Nat.one_le_pow _ _ hQ1
        zify [hQ1, h4']
        ring
      rw [hfac] at h4
      rcases (Nat.Prime.dvd_mul hp).1 h4 with h | h
      · exact absurd h h1
      · exact hres (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨⟨m, hm⟩, hR5, m, hm, (Nat.Prime.dvd_mul hp).1 h⟩))))))

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h
