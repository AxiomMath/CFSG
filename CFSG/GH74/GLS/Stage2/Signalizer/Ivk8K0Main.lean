module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Odd
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
open scoped commutatorElement

theorem kayk_ghList (hc : Cells813) (k : Kind) {Y : Type} [Group Y] [Finite Y]
    (hF : GHList Y) (hs : IsSimpleGroup Y) (α : MulAut Y) (hα2 : α * α = 1) (hα1 : α ≠ 1)
    (hk : KFixOK k α) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup (MulAut Y))
    (hP : IsPGroup p ↥P) (hP1 : P ≠ ⊥) (hcomm : ∀ e ∈ P, e * α = α * e)
    (hnorm : ∀ c ∈ fixSub α, Odd (orderOf c) → MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) :
    (∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) ∧
      (IsCyclic ↥P ∨ (LieModel Y .PSL 3 2 2 ∧ p = 3 ∧ UnitaryFix α)) := by
  rcases ghList_cases hF with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact hc.alt k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.spor k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.mcly k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.two k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.l2 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.l3 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.u3 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.sp4 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.g2 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.d4 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.l4 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.u4 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.l5 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.u5 k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm
  · exact hc.ree k Y h hs α hα2 hα1 hk p hp hp2 P hP hP1 hcomm hnorm


theorem ivk813_of_cells (hMin : MinIndexL34) (hInv : InvSec)
    (hc : Cells813) (hkb : KB813) : IVK_8_13_lift := by
  intro G _ _ z k S hctx H J hH hJ hz2' hzN hJz p P hp hp2 hPp hPHN hPz hPnorm hPnc
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2', pow_two] at this
  have hq : IsQuasisimple ↥J := quasisimple_of_isCompIn hJ
  have hperf : Group.IsPerfect ↥J := hq.1
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hq
  have hPN : P ≤ normalizer (J : Set G) := fun x hx => (hPHN hx).2
  have hJH : J ≤ H := hJ.1
  have hJtop : J ≠ ⊤ := fun h => hH (top_le_iff.mp (h ▸ hJH))
  have hGH : GHList (↥J ⧸ center ↥J) :=
    Generic.ghList_of_surjection hctx.std.kgh hJtop (QuotientGroup.mk' (center ↥J))
      (QuotientGroup.mk'_surjective _) hs hq.2.2
  have hα2 : alphaZ J hzN * alphaZ J hzN = 1 := by
    rw [← map_mul]
    have : (⟨z, hzN⟩ * ⟨z, hzN⟩ : ↥(normalizer (J : Set G))) = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hα1 : alphaZ J hzN ≠ 1 := by
    intro h
    have hzC : z ∈ centralizer (J : Set G) := (YCfg.yAct_eq_one_iff J ⟨z, hzN⟩).mp h
    have h1 : J ≤ centralizer ((zpowers z : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hzC)
    have h2 : ⁅J, zpowers z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [hJz] at h2
    have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot J).mp this h2
  have hPbp : IsPGroup p ↥(Pbar J P) := isPGroup_Pbar hPp
  have hPb1 : Pbar J P ≠ ⊥ := Pbar_ne_bot hPN hPnc
  have hcomm : ∀ e ∈ Pbar J P, e * alphaZ J hzN = alphaZ J hzN * e :=
    fun e he => comm_Pbar hzN hPz he
  have hnorm : ∀ c ∈ fixSub (alphaZ J hzN), Odd (orderOf c) →
      MulAut.conj c ∈ normalizer ((Pbar J P : Subgroup (MulAut (↥J ⧸ center ↥J))) : Set _) := by
    intro c hcfix hodd
    obtain ⟨y, hyz, hyc⟩ := lift_fixed_odd J hzN hz2 hcfix hodd
    have hy : (y : G) ∈ normalizer (P : Set G) :=
      hPnorm (y : G) ⟨hJH y.2, le_normalizer y.2⟩ hyz
    rw [← hyc]
    exact conj_mem_normalizer_Pbar hy
  have hKF : KFixOK k (alphaZ J hzN) :=
    kfixok_of_invsec hzN hz2 (fun T _ _ hns' hsec => hInv G z k S hctx z hz2' T hns' hsec)
  obtain ⟨hcell1, hcell2⟩ := kayk_ghList hc k hGH hs _ hα2 hα1 hKF p hp hp2 (Pbar J P) hPbp hPb1
    hcomm hnorm
  refine ⟨fun x hx => comm_mem_sup hx.2 hzN (hcell1 _), ?_⟩
  by_cases hcyc : IsCyclic ↥(Pbar J P)
  · exact Or.inl (exists_gen_of_cyclic hPN hcyc)
  · right
    obtain ⟨hLie, hp3, hU⟩ := hcell2.resolve_left hcyc
    subst hp3
    have hZodd : Odd (Nat.card (center ↥J)) :=
      odd_center_of_l34 hMin hq (fun x hx T _ _ hns' hsec => hInv G z k S hctx x hx T hns' hsec)
        hLie
    have hnormAll : ∀ c ∈ fixSub (alphaZ J hzN),
        MulAut.conj c ∈ normalizer ((Pbar J P : Subgroup (MulAut (↥J ⧸ center ↥J))) : Set _) := by
      intro c hcfix
      obtain ⟨y, hyz, hyc⟩ := lift_fixed_of_card_odd J hzN hz2 hZodd hcfix
      have hy : (y : G) ∈ normalizer (P : Set G) :=
        hPnorm (y : G) ⟨hJH y.2, le_normalizer y.2⟩ hyz
      rw [← hyc]
      exact conj_mem_normalizer_Pbar hy
    have hle9 : Nat.card ↥(Pbar J P) ≤ 9 :=
      (((hkb _ hLie).2.2 _ hα2 hU).2 (Pbar J P) hPbp hcomm hnormAll)
    have hge9 : 9 ≤ Nat.card ↥(Pbar J P) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨m, hm⟩ := hPbp.exists_card_eq
      rw [hm]
      by_contra hlt
      have hm2 : m ≤ 1 := by
        by_contra h2
        have h9 : 9 ≤ 3 ^ m := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases m
      · have hsub : Subsingleton ↥(Pbar J P) :=
          (Nat.card_eq_one_iff_unique.mp (by simpa using hm)).1
        exact hcyc inferInstance
      · exact hcyc (isCyclic_of_prime_card (by rw [hm]))
    refine ⟨hLie, rfl, ?_, ?_⟩
    · rw [relIndex_eq_card_Pbar hPN]
      omega
    · obtain ⟨F, hF1, hF2, hF4, ⟨e⟩⟩ := hU
      exact ⟨hzN, F, hF1, hF2, hF4, ⟨e⟩⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
