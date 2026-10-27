module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThirteen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.OPPrimeHullStar
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThirteenI
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmAltPerm

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_oPPrimeHull_three_eq_bot {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 5 ≤ n)
    (e : ↥(oPPrimeHull 3 (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore 3 X))) ≃*
      alternatingGroup (Fin n)) :
    Subgroup.centralizer ((oPPrimeHull 3 (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore 3 X)) :
      Set (X ⧸ CFSG.pPrimeCore 3 X))) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y := X ⧸ CFSG.pPrimeCore 3 X
  let O : Subgroup Y := oPPrimeHull 3 (⊤ : Subgroup Y)
  let C : Subgroup Y := Subgroup.centralizer (O : Set Y)
  haveI hOnormal : O.Normal := oPPrimeHull_top_normal 3
  haveI hCnormal : C.Normal := Subgroup.normal_centralizer
  have hAncenter : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)
  have hcenter : Subgroup.center O = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hAncenter, Subgroup.card_bot]
  have hCO : C ⊓ O = ⊥ := by
    have h := CFSG.GroupTheory.inf_centralizer_eq_map_center O
    rw [hcenter, Subgroup.map_bot] at h
    rw [inf_comm]
    exact h
  have h3 : ¬ 3 ∣ Nat.card C := by
    intro hdvd
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hdvd
    have hxC : (x : Y) ∈ C := x.2
    have hxordY : orderOf (x : Y) = 3 := by rw [Subgroup.orderOf_coe, hxord]
    have hxO : (x : Y) ∈ O := by
      have hxmem : (x : Y) ∈ oPPrimeHull 3 (⊤ : Subgroup Y) :=
        Subgroup.subset_closure ⟨trivial, 1, by simpa using hxordY⟩
      simpa [O] using hxmem
    have hxbot : (x : Y) ∈ C ⊓ O := ⟨hxC, hxO⟩
    rw [hCO, Subgroup.mem_bot] at hxbot
    have hx1 : x = 1 := Subtype.ext hxbot
    rw [hx1, orderOf_one] at hxord
    omega
  have hcop : Nat.Coprime 3 (Nat.card C) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hCle : C ≤ CFSG.pPrimeCore 3 Y := le_sSup ⟨hCnormal, hcop⟩
  have hO3 : CFSG.pPrimeCore 3 Y = ⊥ := by
    simpa [Y] using CFSG.pPrimeCore_quotient_eq_bot (G := X) (p := 3) Nat.prime_three
  have hCbot : C = ⊥ := by
    have hle : C ≤ (⊥ : Subgroup Y) := hCle.trans (le_of_eq hO3)
    exact le_antisymm hle bot_le
  simpa [C, O, Y] using hCbot

theorem nonempty_quotient_mulEquiv_of_alternating {X : Type} [Group X] [Finite X]
    (h9 : Nat.factorial 9 ∣ Nat.card (X ⧸ CFSG.pPrimeCore 3 X)) {n : ℕ} (hn : n = 9 ∨ n = 11)
    (e : ↥(oPPrimeHull 3 (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore 3 X))) ≃*
      alternatingGroup (Fin n)) :
    Nonempty (X ⧸ CFSG.pPrimeCore 3 X ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (X ⧸ CFSG.pPrimeCore 3 X ≃* alternatingGroup (Fin 11)) ∨
      Nonempty (X ⧸ CFSG.pPrimeCore 3 X ≃* Equiv.Perm (Fin 11)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y := X ⧸ CFSG.pPrimeCore 3 X
  let O : Subgroup Y := oPPrimeHull 3 (⊤ : Subgroup Y)
  haveI hOnormal : O.Normal := oPPrimeHull_top_normal 3
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn6 : n ≠ 6 := by rcases hn with rfl | rfl <;> norm_num
  have hC : Subgroup.centralizer (O : Set Y) = ⊥ := by
    simpa [Y, O] using centralizer_oPPrimeHull_three_eq_bot (X := X) (n := n) hn5 e
  obtain ⟨ι, hιinj, hιN⟩ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.Alt.exists_perm_embedding
      hn5 hn6 e hC
  let R : Subgroup (Equiv.Perm (Fin n)) := ι.range
  have hAle : alternatingGroup (Fin n) ≤ R := by
    intro a ha
    obtain ⟨x, hx⟩ := e.surjective ⟨a, ha⟩
    refine MonoidHom.mem_range.mpr ⟨(x : Y), ?_⟩
    rw [hιN x]
    exact congrArg Subtype.val hx
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hRindex_dvd : R.index ∣ 2 := by
    have h := Subgroup.index_dvd_of_le hAle
    rwa [alternatingGroup.index_eq_two] at h
  have hR : R = alternatingGroup (Fin n) ∨ R = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hRindex_dvd with h1 | h2
    · exact Or.inr (Subgroup.index_eq_one.mp h1)
    · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2)
  let eR : Y ≃* R := MonoidHom.ofInjective hιinj
  rcases hn with rfl | rfl
  · rcases hR with hRA | hRtop
    · exfalso
      have hcardY : Nat.card Y = Nat.factorial 9 / 2 := by
        rw [Nat.card_congr eR.toEquiv, hRA, nat_card_alternatingGroup, Nat.card_fin]
      rw [hcardY] at h9
      norm_num [Nat.factorial] at h9
    · left
      exact ⟨eR.trans ((MulEquiv.subgroupCongr hRtop).trans Subgroup.topEquiv)⟩
  · rcases hR with hRA | hRtop
    · right; left
      exact ⟨eR.trans (MulEquiv.subgroupCongr hRA)⟩
    · right; right
      exact ⟨eR.trans ((MulEquiv.subgroupCongr hRtop).trans Subgroup.topEquiv)⟩

theorem card_dvd_factorial_eleven_of_nonempty {Y : Type*} [Group Y] [Finite Y]
    (h : Nonempty (Y ≃* Equiv.Perm (Fin 9)) ∨ Nonempty (Y ≃* alternatingGroup (Fin 11)) ∨
      Nonempty (Y ≃* Equiv.Perm (Fin 11))) : Nat.card Y ∣ Nat.factorial 11 := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    exact Nat.factorial_dvd_factorial (by norm_num)
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    have h2 : 2 ∣ Nat.factorial 11 := by norm_num [Nat.factorial]
    exact ⟨2, (Nat.div_mul_cancel h2).symm⟩
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]

theorem S14Choice.factorial_nine_dvd_card_quotient {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet) :
    Nat.factorial 9 ∣ Nat.card (↥M ⧸ CFSG.pPrimeCore 3 ↥M) := by
  classical
  obtain ⟨θ, hθsurj, hker⟩ := h.exists_surjection_perm_nine h2 hK hU hL hKF
  let J : Subgroup G := kSub 3 M H ⊓ M
  let f : ↥J →* (↥M ⧸ CFSG.pPrimeCore 3 ↥M) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)).comp
      (Subgroup.inclusion (inf_le_right : J ≤ M))
  have hker' : f.ker ≤ θ.ker := by simpa [f, J] using hker
  let g : ↥J ⧸ f.ker →* Equiv.Perm (Fin 9) := QuotientGroup.lift f.ker θ hker'
  have hg : g.comp (QuotientGroup.mk' f.ker) = θ :=
    QuotientGroup.lift_comp_mk' f.ker θ hker'
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hθsurj y
    exact ⟨QuotientGroup.mk' f.ker x, by rw [← MonoidHom.comp_apply, hg, hx]⟩
  have h1 : Nat.card (Equiv.Perm (Fin 9)) ∣ Nat.card (↥J ⧸ f.ker) :=
    Subgroup.card_dvd_of_surjective hgsurj
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  have hdiv : Nat.card (Equiv.Perm (Fin 9)) ∣
      Nat.card (↥M ⧸ CFSG.pPrimeCore 3 ↥M) :=
    h1.trans (Subgroup.card_subgroup_dvd_card f.range)
  rwa [Nat.card_perm, Nat.card_fin] at hdiv

theorem S14Choice.caseTwo_quotient {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use) (h525 : FiveTwentyFiveS11Use)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (h73 : SevenThreeInput)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne) :
    ∃ n : ℕ, (n = 9 ∨ n = 11) ∧
      Nonempty (↥(oPPrimeHull 3 (⊤ : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M))) ≃*
        alternatingGroup (Fin n)) ∧
      (Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
        Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
        Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : Nat.factorial 9 ∣ Nat.card (↥M ⧸ CFSG.pPrimeCore 3 ↥M) :=
    h.factorial_nine_dvd_card_quotient h2 hK hU hL hKF
  have h13 := h.fourteenThirteen hA h2 hpre hK hU hL hKF h514 h525 hX h73 h711
  obtain ⟨eT⟩ := nonempty_threeStar_oPPrimeHull_mulEquiv M
  rcases h13 with h13 | h13
  · obtain ⟨e9⟩ := h13
    refine ⟨9, Or.inl rfl, ⟨eT.symm.trans e9⟩, ?_⟩
    exact nonempty_quotient_mulEquiv_of_alternating (X := ↥M) h9 (Or.inl rfl) (eT.symm.trans e9)
  · obtain ⟨e11⟩ := h13
    refine ⟨11, Or.inr rfl, ⟨eT.symm.trans e11⟩, ?_⟩
    exact nonempty_quotient_mulEquiv_of_alternating (X := ↥M) h9 (Or.inr rfl) (eT.symm.trans e11)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
