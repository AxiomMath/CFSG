module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearGen

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCLinPlane

section Fixed

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] [Finite K]

theorem orderOf_add_one_le_finrank_range_avgOp {E0 : Subgroup (SpecialLinearGroup (Fin n) K)}
    [Fintype E0] [IsMulCommutative E0] (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)
    {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (hLne : projLine (planeRep E0) L ≠ 0)
    {v : Fin n → K} (hv0 : v ≠ 0)
    (hv : ∀ a ∈ E0, (a : Matrix (Fin n) (Fin n) K).mulVec v = v) :
    orderOf ((Nat.card K : ℕ) : ZMod p) + 1 ≤
      finrank K (LinearMap.range (avgOp (planeRep E0) L)) := by
  set ρ := planeRep E0 with hρ
  have hvtop : v ∈ LinearMap.range (projTop ρ) := by
    rw [range_projTop ρ hP hpK, mem_fixedSpace]
    intro y _
    rw [hρ, act_planeRep, Matrix.toLin'_apply]
    exact hv _ y.2
  have h1 : 1 ≤ finrank K (LinearMap.range (projTop ρ)) := by
    have h := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem v _).2 hvtop)
    rwa [finrank_span_singleton hv0] at h
  have h2 : orderOf ((Nat.card K : ℕ) : ZMod p) ≤ finrank K (LinearMap.range (projLine ρ L)) :=
    orderOf_le_finrank_range_projLine E0 hP hpK hL hLne
  have hdisj : LinearMap.range (projTop ρ) ⊓ LinearMap.range (projLine ρ L) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := Submodule.mem_inf.1 hw
    have e1 : projTop ρ (projTop ρ a) = projTop ρ a := by
      simpa using LinearMap.congr_fun (projTop_mul_self ρ hP hpK) a
    have e2 : projTop ρ (projLine ρ L b) = 0 := by
      simpa using LinearMap.congr_fun (projTop_mul_projLine ρ hP hpK (mem_lines.mp hL)) b
    rw [Submodule.mem_bot, ← e1, ← hb, e2]
  have hle : LinearMap.range (projTop ρ) ⊔ LinearMap.range (projLine ρ L) ≤
      LinearMap.range (avgOp ρ L) := by
    refine sup_le ?_ (range_projLine_le_range_avgOp hpK hL)
    have h : projTop ρ = avgOp ρ L * avgOp ρ ⊤ := (avgOp_mul_top ρ hpK (mem_lines.mp hL)).symm
    rw [h, Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (projTop ρ))
    (LinearMap.range (projLine ρ L))
  rw [hdisj, finrank_bot, add_zero] at h3
  have h4 := Submodule.finrank_mono hle
  omega

end Fixed

section Main

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_top_of_good_blocks_le_fix (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hpcard : ¬ p ∣ Nat.card K) (hpq : ¬ p ∣ Nat.card K - 1)
    (E0 : Subgroup (SpecialLinearGroup (Fin n) K)) [IsElementaryAbelian p E0]
    (hE0 : Nat.card E0 = p ^ 2)
    (hp4 : 3 < p ∨ 4 ≤ Nat.card K ∨ ∃ v : Fin n → K, v ≠ 0 ∧
      ∀ a ∈ E0, (a : Matrix (Fin n) (Fin n) K).mulVec v = v)
    (𝒢 : Subgroup (SpecialLinearGroup (Fin n) K))
    (hblocks : ∀ a ∈ E0, a ≠ 1 →
      ∀ (hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))
        (h : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))), GoodBlock h →
        p ∣ Nat.card (blockImage hsq h) → blockImage hsq h ≤ 𝒢.map SpecialLinearGroup.toGL) :
    𝒢 = ⊤ := by
  have : Fintype ↥E0 := Fintype.ofFinite _
  have hP : IsPlane p E0 := isPlane E0 hp hE0
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hd2 : 2 ≤ orderOf ((Nat.card K : ℕ) : ZMod p) :=
    two_le_orderOf_natCast hp (by omega) hpcard hpq
  have hgeL : ∀ L ∈ lines p E0, projLine (planeRep E0) L ≠ 0 →
      orderOf ((Nat.card K : ℕ) : ZMod p) ≤
        finrank K (LinearMap.range (avgOp (planeRep E0) L)) := fun L hL hLne =>
    (orderOf_le_finrank_range_projLine E0 hP hpK hL hLne).trans
      (Submodule.finrank_mono (range_projLine_le_range_avgOp hpK hL))
  have hd3 : ∀ L ∈ lines p E0, projLine (planeRep E0) L ≠ 0 → Nat.card K ≤ 3 →
      3 ≤ finrank K (LinearMap.range (avgOp (planeRep E0) L)) := by
    intro L hL hLne hq3
    rcases hp4 with hp3 | h4 | ⟨v, hv0, hv⟩
    · exact (three_le_orderOf_of_le_three hp hp3 hq2 hq3 hd2).trans (hgeL L hL hLne)
    · omega
    · have := orderOf_add_one_le_finrank_range_avgOp hP hpK hL hLne hv0 hv
      omega
  have hidem := planeIdem_idem E0 hP hpK
  have horth : ∀ i j, i ≠ j → planeIdem E0 p i * planeIdem E0 p j = 0 := fun i j h =>
    planeIdem_orth E0 hP hpK h
  have hsum := planeIdem_sum E0 hP hpK
  set A : Finset (PlaneIdx E0 p) :=
    Finset.univ.filter (fun o => o ≠ none ∧ planeIdem E0 p o ≠ 0) with hA
  have hzA : (none : PlaneIdx E0 p) ∉ A := by
    simp [hA]
  have hAne : A.Nonempty := by
    obtain ⟨L, hL, hLne⟩ := exists_active E0 hP hpK
    exact ⟨some ⟨L, hL⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Option.some_ne_none _, hLne⟩⟩
  have hinact : ∀ o, o ≠ none → o ∉ A → planeIdem E0 p o = 0 := by
    intro o hon hoA
    by_contra hne
    exact hoA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon, hne⟩)
  have hdim : ∀ o ∈ A, 2 ≤ finrank K (LinearMap.range (planeIdem E0 p o)) := by
    intro o ho
    obtain ⟨hon, hne⟩ := (Finset.mem_filter.mp ho).2
    obtain ⟨L, rfl⟩ := Option.ne_none_iff_exists'.mp hon
    exact hd2.trans (orderOf_le_finrank_range_projLine E0 hP hpK L.2 hne)
  set b₀ := Pi.basisFun K (Fin n) with hb₀
  set G : Subgroup ((Fin n → K) ≃ₗ[K] (Fin n → K)) := 𝒢.map (slAction b₀) with hG
  have hGdet : ∀ g ∈ G, LinearEquiv.det g = 1 := by
    rintro _ ⟨s, -, rfl⟩
    exact det_slAction b₀ s
  have hsupp : ∀ o ∈ A, suppGroup (planeIdem E0 p none + planeIdem E0 p o) ≤ G := by
    intro o ho
    obtain ⟨hon, hne⟩ := (Finset.mem_filter.mp ho).2
    obtain ⟨L, rfl⟩ := Option.ne_none_iff_exists'.mp hon
    have hLne : projLine (planeRep E0) L.1 ≠ 0 := hne
    have hsumL : planeIdem E0 p none + planeIdem E0 p (some L) = avgOp (planeRep E0) L.1 := by
      change projTop (planeRep E0) + projLine (planeRep E0) L.1 = _
      unfold projTop projLine
      abel
    rw [hsumL]
    intro g hg
    obtain ⟨A', hA'⟩ := exists_slAction_eq b₀ ((det_eq_one_iff g).mpr
      ((det_eq_one_iff g).mp hg.1))
    obtain ⟨b, hbL, hb1⟩ := exists_ne_one_mem E0 L.2 hP
    have hbp : act (planeRep E0) b ^ p = 1 := by
      rw [← act_pow, hP.pow b, act_one]
    have hsq : Squarefree (minpoly K (act (planeRep E0) b)) :=
      squarefree_minpoly_of_pow_eq_one hpK hbp
    have hXmem := X_sub_one_mem E0 hLne hbL
    have : Fact (Irreducible (X - C 1 : K[X])) := ⟨irreducible_X_sub_C 1⟩
    have hmult : mult (act (planeRep E0) b) ⟨X - C 1, hXmem⟩ =
        finrank K (LinearMap.range (avgOp (planeRep E0) L.1)) := by
      have h1 := finrank_primaryComponent (act (planeRep E0) b) (X - C 1)
      rw [natDegree_X_sub_C, one_mul] at h1
      have h2 : finrank K (primaryComponent (act (planeRep E0) b) (X - C 1)) =
          finrank K (LinearMap.range (avgOp (planeRep E0) L.1)) := by
        rw [primaryComponent_X_sub_one E0 hP hpK L.2 hbL hb1]
      exact h1.symm.trans h2
    have hge : orderOf ((Nat.card K : ℕ) : ZMod p) ≤
        finrank K (LinearMap.range (avgOp (planeRep E0) L.1)) := hgeL L.1 L.2 hLne
    have hgood : GoodBlock (⟨X - C 1, hXmem⟩ : primaryFactors (act (planeRep E0) b)) := by
      by_cases hq3 : Nat.card K ≤ 3
      · left
        rw [hmult]
        exact hd3 L.1 L.2 hLne hq3
      · right
        refine ⟨by rw [hmult]; exact hd2.trans hge, ?_⟩
        change 3 < Nat.card (AdjoinRoot (X - C 1))
        rw [natCard_adjoinRoot, natDegree_X_sub_C, pow_one]
        omega
    have hcardE : Nat.card (Efac (act (planeRep E0) b) ⟨X - C 1, hXmem⟩) = Nat.card K := by
      change Nat.card (AdjoinRoot (X - C 1)) = _
      rw [natCard_adjoinRoot, natDegree_X_sub_C, pow_one]
    have hpd1 : p ∣ Nat.card (blockImage hsq ⟨X - C 1, hXmem⟩) := by
      refine dvd_card_blockImage_of_pow hp hsq _ (e := orderOf ((Nat.card K : ℕ) : ZMod p))
        (by rw [hcardE]; exact hpq) (by omega) ?_ ?_
      · rw [hmult]; exact hge
      · rw [hcardE]; exact dvd_pow_sub_one_orderOf hp
    have hAv : ∀ v, Matrix.toLin' (A' : Matrix (Fin n) (Fin n) K) v = g v := fun v => by
      rw [toLin'_apply_eq_slAction, hA']
    have hmem := fixedBlock_mem E0 hP hpK L.2 hLne hbL hb1 hsq hg hAv
    have hb1' : (b : SpecialLinearGroup (Fin n) K) ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨s, hs𝒢, hs⟩ := hblocks b b.2 hb1' hsq ⟨X - C 1, hXmem⟩ hgood hpd1 hmem
    have hsA : s = A' := SpecialLinearGroup.toGL_injective hs
    exact ⟨s, hs𝒢, hsA ▸ hA'⟩
  have hmix : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∃ β : Module.End K (Fin n → K),
      planeIdem E0 p i * β = β ∧ β * planeIdem E0 p j = β ∧ β ≠ 0 ∧
        ∃ u ∈ G, ∀ v, u v = v + β v := by
    intro i hi j hj hij
    obtain ⟨hion, hine⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hjon, hjne⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨L, rfl⟩ := Option.ne_none_iff_exists'.mp hion
    obtain ⟨M, rfl⟩ := Option.ne_none_iff_exists'.mp hjon
    have hLne : projLine (planeRep E0) L.1 ≠ 0 := hine
    have hMne : projLine (planeRep E0) M.1 ≠ 0 := hjne
    have hLM : L.1 ≠ M.1 := fun h => hij (by rw [Subtype.ext h])
    have hML : M.1 ≠ L.1 := Ne.symm hLM
    obtain ⟨a, ha1, h, hh, hdeg, hLP, hMP⟩ :=
      exists_mixing_block E0 hP hpK L.2 M.2 hLM hLne hMne
    have hxpa : act (planeRep E0) a ^ p = 1 := by rw [← act_pow, hP.pow a, act_one]
    have hsqa := squarefree_minpoly_of_pow_eq_one hpK hxpa
    obtain ⟨β, hβ, hβ1, hβ2, hβ0, hββ, hkill, hdet, hmult⟩ := exists_mixing_unipotent hsqa hh
      (e := projLine (planeRep E0) M.1) (e' := projLine (planeRep E0) L.1)
      (commute_act_projLine E0 a M.1).symm (commute_act_projLine E0 a L.1).symm
      (projLine_mul_self (planeRep E0) hP hpK (mem_lines.mp M.2))
      (projLine_mul_self (planeRep E0) hP hpK (mem_lines.mp L.2))
      (projLine_mul_projLine_of_ne (planeRep E0) hP hpK (mem_lines.mp M.2) (mem_lines.mp L.2) hML)
      hMP hLP
    obtain ⟨g', hg'mem, hg'v⟩ := exists_mem_blockImage_one_add hsqa
      (a0 := SpecialLinearGroup.toGL (a : SpecialLinearGroup (Fin n) K)) rfl ⟨h, hh⟩ β hβ hββ
      hkill hdet
    have hgood := goodBlock_of_mixing hh hd2 hdeg hmult
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hdvdX : h ∣ X ^ p - 1 :=
      (mem_primaryFactors.mp hh).2.2.trans (minpoly.dvd K _ (by simp [hxpa]))
    have hpd2 : p ∣ Nat.card (blockImage hsqa ⟨h, hh⟩) :=
      dvd_card_blockImage_of_sub_one hp hsqa ⟨h, hh⟩ (by change 2 ≤ finrank _ _; exact hmult)
        (by change p ∣ Nat.card (AdjoinRoot h) - 1
            exact dvd_card_adjoinRoot_sub_one hp hdvdX (hd2.trans hdeg))
    have ha1' : (a : SpecialLinearGroup (Fin n) K) ≠ 1 := fun h' => ha1 (Subtype.ext h')
    obtain ⟨s, hs𝒢, hs⟩ := hblocks a a.2 ha1' hsqa ⟨h, hh⟩ hgood hpd2 hg'mem
    refine ⟨β, hβ1, hβ2, hβ0, slAction b₀ s, ⟨s, hs𝒢, rfl⟩, fun v => ?_⟩
    have hsmat : (s : Matrix (Fin n) (Fin n) K) = (g' : Matrix (Fin n) (Fin n) K) :=
      congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hs
    rw [← toLin'_apply_eq_slAction, hsmat]
    exact hg'v v
  have hmain := generation_of_blocks (planeIdem E0 p) hidem horth hsum none A hzA hAne hinact
    hdim G hGdet hsupp hmix
  refine eq_top_iff.mpr fun s _ => ?_
  obtain ⟨s', hs'𝒢, hs'⟩ := hmain (slAction b₀ s) (det_slAction b₀ s)
  have : s' = s := slAction_injective b₀ hs'
  exact this ▸ hs'𝒢

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
