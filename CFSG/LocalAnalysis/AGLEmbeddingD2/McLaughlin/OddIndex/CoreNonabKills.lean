module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreNonab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Lift
public import CFSG.RankThree.PartOne.N143.CaseB1Theta
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreQ

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open SemidirectProduct CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Generic

variable {G : Type} [Group G]

theorem conjClass_conj {Y : Subgroup G} {a c y : G} (hc : c ∈ conjClass Y a) (hy : y ∈ Y) :
    y * c * y⁻¹ ∈ conjClass Y a := by
  obtain ⟨z, hz, rfl | rfl⟩ := hc
  · exact ⟨y * z, Y.mul_mem hy hz, Or.inl (by group)⟩
  · exact ⟨y * z, Y.mul_mem hy hz, Or.inr (by group)⟩

theorem conj_mem_closure_conjClass {Y : Subgroup G} {a n y : G}
    (hn : n ∈ Subgroup.closure (conjClass Y a)) (hy : y ∈ Y) :
    y * n * y⁻¹ ∈ Subgroup.closure (conjClass Y a) := by
  have : (Subgroup.closure (conjClass Y a)).map (MulAut.conj y).toMonoidHom ≤
      Subgroup.closure (conjClass Y a) := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.subset_closure (conjClass_conj hc hy)
  exact this ⟨n, hn, rfl⟩

end Generic

section Kills

variable {Y I : Type} [Group Y] [Group I]

theorem kills_of_isLThreeTwo [Finite Y] (hY : IsLThreeTwo (Y ⧸ CFSG.pCore 2 Y)) {a₀ : Y}
    (ha : orderOf a₀ = 3) (ρ : Y →* MulAut I) :
    ∀ (Q : Type) [Group Q] [Group.IsSolvable Q]
      (ψ : ↥(Subgroup.closure (conjClass (inr : Y →* I ⋊[ρ] Y).range (inr a₀))) →* Q),
      ψ ⟨inr a₀, Subgroup.subset_closure (a_mem_conjClass _ _)⟩ = 1 := by
  set Gy : Subgroup (I ⋊[ρ] Y) := (inr : Y →* I ⋊[ρ] Y).range with hGy
  set Cl : Subgroup (I ⋊[ρ] Y) := Subgroup.closure (conjClass Gy (inr a₀)) with hCl
  intro Q _ _ ψ
  set TY : Subgroup Y := Cl.comap (inr : Y →* I ⋊[ρ] Y) with hTY
  set P := CFSG.pCore 2 Y with hP
  have hPn : P.Normal := CFSG.pCore_normal
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hsimple : IsSimpleGroup (Y ⧸ P) := isLThreeTwo_simple hY
  have hperf : Group.IsPerfect (Y ⧸ P) := by
    refine CFSG.RankThree.PartOne.N143.isPerfect_of_simple_of_not_prime ?_
    rw [isLThreeTwo_card_eq hY]
    norm_num
  have ha3 : a₀ ^ 3 = 1 := by
    have := pow_orderOf_eq_one a₀
    rwa [ha] at this
  have haP : a₀ ∉ P := by
    intro h
    obtain ⟨k, hk⟩ := hP2 ⟨a₀, h⟩
    have h1 : orderOf a₀ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [ha] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have haTY : a₀ ∈ TY := Subgroup.subset_closure (a_mem_conjClass _ _)
  have hTYn : TY.Normal := ⟨fun n hn g => by
    have hn' : (inr n : I ⋊[ρ] Y) ∈ Cl := hn
    have := conj_mem_closure_conjClass hn' (y := inr g) ⟨g, rfl⟩
    simpa [hTY] using this⟩
  have hT : ∀ y : Y, ∃ t ∈ TY, ∃ p ∈ P, y = t * p := by
    have hN : (TY.map (QuotientGroup.mk' P)).Normal :=
      Subgroup.Normal.map hTYn _ (QuotientGroup.mk'_surjective P)
    have hne : TY.map (QuotientGroup.mk' P) ≠ ⊥ := by
      intro h
      have : (QuotientGroup.mk' P) a₀ ∈ TY.map (QuotientGroup.mk' P) := ⟨a₀, haTY, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact haP ((QuotientGroup.eq_one_iff _).1 this)
    have htop : TY.map (QuotientGroup.mk' P) = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne
    intro y
    have : (QuotientGroup.mk' P) y ∈ TY.map (QuotientGroup.mk' P) := by rw [htop]; trivial
    obtain ⟨t, ht, hty⟩ := this
    refine ⟨t, ht, t⁻¹ * y, ?_, by group⟩
    exact QuotientGroup.eq.1 hty
  let ψ' : ↥TY →* Q := ψ.comp ((inr : Y →* I ⋊[ρ] Y).comp TY.subtype |>.codRestrict Cl (fun x => x.2))
  have hord : ¬ 2 ∣ orderOf (⟨a₀, haTY⟩ : ↥TY) := by
    rw [Subgroup.orderOf_mk, ha]; omega
  exact map_eq_one_of_solvable P hP2 hperf TY hT ψ' ⟨a₀, haTY⟩ hord

end Kills

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
