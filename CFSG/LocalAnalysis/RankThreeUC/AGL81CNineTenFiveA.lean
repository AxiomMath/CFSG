module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveW
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoEasy

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem map_subtype_closure_orderOf (W : Subgroup X) (p : ℕ) :
    (closure {x : ↥W | orderOf x = p}).map W.subtype = closure {x : X | x ∈ W ∧ orderOf x = p} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by
      show orderOf (y : X) = p
      rwa [Subgroup.orderOf_coe]⟩
  · rintro ⟨hxW, hxp⟩
    exact ⟨⟨x, hxW⟩, by
      show orderOf (⟨x, hxW⟩ : ↥W) = p
      rw [Subgroup.orderOf_mk]
      exact hxp, rfl⟩

theorem map_subtype_oPPrimeHull_top (W : Subgroup X) (p : ℕ) :
    (oPPrimeHull p (⊤ : Subgroup ↥W)).map W.subtype = oPPrimeHull p W := by
  rw [oPPrimeHull, MonoidHom.map_closure, oPPrimeHull]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨-, k, hk⟩, rfl⟩
    exact ⟨y.2, k, by
      show orderOf (y : X) = p ^ k
      rwa [Subgroup.orderOf_coe]⟩
  · rintro ⟨hxW, k, hk⟩
    exact ⟨⟨x, hxW⟩, ⟨trivial, k, by
      show orderOf (⟨x, hxW⟩ : ↥W) = p ^ k
      rw [Subgroup.orderOf_mk]
      exact hk⟩, rfl⟩

theorem oPPrimeHull_eq_closure_of_le {Y W : Subgroup X} (hYW : Y ≤ W)
    (hVY : closure {x : X | x ∈ W ∧ orderOf x = p} ≤ Y)
    (hWV : oPPrimeHull p W = closure {x : X | x ∈ W ∧ orderOf x = p}) :
    oPPrimeHull p Y = closure {x : X | x ∈ W ∧ orderOf x = p} := by
  apply le_antisymm
  · rw [oPPrimeHull, ← hWV]
    apply Subgroup.closure_mono
    rintro x ⟨hxY, k, hk⟩
    exact ⟨hYW hxY, k, hk⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨hxW, hxp⟩
    exact Subgroup.subset_closure ⟨hVY (Subgroup.subset_closure ⟨hxW, hxp⟩), 1, by rwa [pow_one]⟩

theorem exists_mem_inf_ne_one_of_le_sup (hp : p.Prime) {L E : Subgroup X} (hLn : L.Normal)
    (hrkL : CFSG.Open.pRank p L ≤ 1)
    (hZ : ∀ z ∈ L, z ∈ centralizer (L : Set X) → z ^ p = 1 → z = 1)
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hEL : E ≤ L ⊔ centralizer (L : Set X)) :
    ∃ x ∈ E, x ∈ centralizer (L : Set X) ∧ x ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hLn
  let Y : Subgroup X := centralizer (L : Set X)
  have hYn : Y.Normal := by
    change (centralizer (L : Set X)).Normal
    infer_instance
  haveI : Y.Normal := hYn
  by_contra h
  have hEY : E ⊓ Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx.1, hx.2, hx1⟩
  have hpN : ¬ p ∣ Nat.card (Y.subgroupOf L) := by
    intro hdvd
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hzp : (((x : ↥L)) : X) ^ p = 1 := by
      have hxp : x ^ p = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
      have h := congrArg (fun y : ↥(Y.subgroupOf L) => ((y : ↥L) : X)) hxp
      simpa using h
    have hz1 : ((x : ↥L) : X) = 1 :=
      hZ _ (x : ↥L).2 (Subgroup.mem_subgroupOf.mp x.2) hzp
    have hx1 : x = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hz1
    rw [hx1, orderOf_one] at hxord
    exact hp.one_lt.ne hxord
  let N : Subgroup ↥L := Y.subgroupOf L
  haveI : N.Normal := by change (Y.subgroupOf L).Normal; infer_instance
  have hN : ¬ p ∣ Nat.card N := hpN
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ N)) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_quotient_eq N hN]
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hrkL
  let ψ : ↥E →* (↥(L ⊔ Y) ⧸ Y.subgroupOf (L ⊔ Y)) :=
    (QuotientGroup.mk' (Y.subgroupOf (L ⊔ Y))).comp (Subgroup.inclusion hEL)
  let φ : ↥E →* (↥L ⧸ N) :=
    (QuotientGroup.quotientInfEquivProdNormalQuotient L Y).symm.toMonoidHom.comp ψ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff φ, Subgroup.eq_bot_iff_forall]
    intro e he
    have hψ1 : ψ e = 1 := by
      have h1 : (QuotientGroup.quotientInfEquivProdNormalQuotient L Y) (φ e) = 1 := by
        rw [MonoidHom.mem_ker.mp he, map_one]
      rw [← h1]
      simp [φ, MonoidHom.comp_apply]
    have hmemY : (e : X) ∈ Y := by
      have h2 : QuotientGroup.mk' (Y.subgroupOf (L ⊔ Y)) (Subgroup.inclusion hEL e) = 1 := by
        simpa [ψ] using hψ1
      have h3 : Subgroup.inclusion hEL e ∈ Y.subgroupOf (L ⊔ Y) :=
        (QuotientGroup.eq_one_iff _).mp h2
      simpa using Subgroup.mem_subgroupOf.mp h3
    have hmem : (e : X) ∈ E ⊓ Y := Subgroup.mem_inf.mpr ⟨e.2, hmemY⟩
    rw [hEY, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hErank : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥E) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup E]
    exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hEc
  have := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt φ hφinj
  omega

private theorem oPPrimeHull_top_normal_aux {G : Type} [Group G] (p : ℕ) :
    (oPPrimeHull p (⊤ : Subgroup G)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h : (oPPrimeHull p (⊤ : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤
      oPPrimeHull p (⊤ : Subgroup G) := by
    rw [oPPrimeHull, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨-, k, hk⟩, rfl⟩
    refine ⟨trivial, k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  exact h ⟨n, hn, rfl⟩

namespace IsSplitCover

variable {L W : Subgroup X}

theorem oPPrimeHull_eq (h661 : SixSixOneRank) (hp : p.Prime) (hp3 : 3 < p) (hLn : L.Normal)
    (hW : IsSplitCover p L W) (hZ : ∀ z ∈ L, z ∈ centralizer (L : Set X) → z ^ p = 1 → z = 1)
    (hRY : CFSG.pCore p X ≤ centralizer (L : Set X))
    (hYR : centralizer (L : Set X) ⊓ centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (hV : ¬ IsPGroup p ↥(closure {x : X | x ∈ W ∧ orderOf x = p})) :
    oPPrimeHull p W = closure {x : X | x ∈ W ∧ orderOf x = p} ∧
      oPPrimeHull p (centralizer (L : Set X)) = closure {x : X | x ∈ W ∧ orderOf x = p} ∧
      IsExtNotation (fun B _ => IsSLType 2 (ZMod p) B) (fun B _ => IsHomocyclicRank2 p B)
        ↥(closure {x : X | x ∈ W ∧ orderOf x = p}) := by
  let VW : Subgroup ↥W := closure {x : ↥W | orderOf x = p}
  let V : Subgroup X := closure {x : X | x ∈ W ∧ orderOf x = p}
  have hX : centralizer (CFSG.pCore p ↥W : Set ↥W) ≤ CFSG.pCore p ↥W :=
    centralizer_pCore_le hLn hW hRY hYR
  have hrkW : CFSG.Open.pRank p (⊤ : Subgroup ↥W) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup W]
    exact pRank_le_two hp hLn hW hZ hrk
  have hmaps : VW.map W.subtype = V := by
    change (closure {x : ↥W | orderOf x = p}).map W.subtype =
      closure {x : X | x ∈ W ∧ orderOf x = p}
    exact map_subtype_closure_orderOf W p
  have eV : ↥VW ≃* ↥V :=
    (VW.equivMapOfInjective W.subtype W.subtype_injective).trans
      (MulEquiv.subgroupCongr hmaps)
  have hVW : ¬ IsPGroup p ↥VW := fun hpV => hV (IsPGroup.of_equiv hpV eV)
  obtain ⟨h1, h2, h3⟩ := rankTwo_structure_of_sixSixOne (X := ↥W) h661 hp hp3 hX hrkW hVW
  have hWV : oPPrimeHull p W = V := by
    have h := congrArg (Subgroup.map W.subtype) h1
    rw [map_subtype_oPPrimeHull_top, map_subtype_closure_orderOf] at h
    simpa only [V] using h
  have hVV : ⁅V, V⁆ = V := by
    have h := congrArg (Subgroup.map W.subtype) h3
    rw [Subgroup.map_commutator, map_subtype_closure_orderOf] at h
    simpa only [V] using h
  have hVleW : V ≤ W := by
    change closure {x : X | x ∈ W ∧ orderOf x = p} ≤ W
    rw [Subgroup.closure_le]
    rintro x ⟨hxW, -⟩
    exact hxW
  have hVY : V ≤ centralizer (L : Set X) :=
    le_centralizer_of_commutator_eq hLn hW hVleW hVV
  refine ⟨hWV, ?_, isExtNotation_SL_homocyclic_of_mulEquiv eV h2⟩
  exact oPPrimeHull_eq_closure_of_le hW.1 hVY hWV

theorem oPPrimeHull_top_eq (hp : p.Prime) (hLn : L.Normal) (hW : IsSplitCover p L W)
    (hZ : ∀ z ∈ L, z ∈ centralizer (L : Set X) → z ^ p = 1 → z = 1)
    (hLq : CFSG.IsQuasisimple ↥L) :
    oPPrimeHull p (⊤ : Subgroup X) = L ⊔ oPPrimeHull p W := by
  apply le_antisymm
  · change Subgroup.closure {x : X | x ∈ ⊤ ∧ ∃ k : ℕ, orderOf x = p ^ k} ≤
      L ⊔ oPPrimeHull p W
    rw [Subgroup.closure_le]
    rintro x ⟨-, k, hk⟩
    have hx1 : x ^ (p ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    have hxLW : x ∈ L ⊔ W := hW.2.2.1 (Subgroup.subset_closure ⟨trivial, k, hk⟩)
    obtain ⟨l, hl, w, hw, hwp, rfl⟩ :=
      exists_mul_of_mem_sup hp hLn (fun y hy => hW.coprime_orderOf hp hZ hy) hxLW hx1
    have hwV : w ∈ oPPrimeHull p W := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hwp)
      exact Subgroup.subset_closure ⟨hw, j, hj⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hwV)
  · apply sup_le
    · let P : Subgroup ↥L := (oPPrimeHull p (⊤ : Subgroup X)).subgroupOf L
      have hPn : P.Normal := (oPPrimeHull_top_normal_aux p).subgroupOf L
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hPn with hP | hP
      · intro x hxL
        have hxP : (⟨x, hxL⟩ : ↥L) ∈ P := by rw [hP]; exact Subgroup.mem_top _
        have := Subgroup.mem_subgroupOf.mp hxP
        simpa using this
      · exfalso
        obtain ⟨z, hzL, hzord, -⟩ :=
          hW.2.2.2.2 1 (one_mem W) (by rw [one_pow]; exact one_mem _)
        have hzP : (⟨z, hzL⟩ : ↥L) ∈ P :=
          Subgroup.mem_subgroupOf.mpr
            (Subgroup.subset_closure ⟨trivial, 1, by rw [pow_one]; exact hzord⟩)
        have hzcent : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := hP hzP
        have hzY : z ∈ centralizer (L : Set X) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hcomm := (Subgroup.mem_center_iff.mp hzcent) (⟨y, hy⟩ : ↥L)
          exact congrArg Subtype.val hcomm
        have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
        have hz1 : z = 1 := hZ z hzL hzY hzp
        rw [hz1, orderOf_one] at hzord
        exact hp.one_lt.ne hzord
    · change Subgroup.closure {x : X | x ∈ W ∧ ∃ k : ℕ, orderOf x = p ^ k} ≤
        Subgroup.closure {x : X | x ∈ ⊤ ∧ ∃ k : ℕ, orderOf x = p ^ k}
      rw [Subgroup.closure_le]
      rintro x ⟨-, k, hk⟩
      exact Subgroup.subset_closure ⟨trivial, k, hk⟩

end IsSplitCover

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
