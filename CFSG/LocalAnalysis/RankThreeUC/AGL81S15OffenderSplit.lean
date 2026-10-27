module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

section Center

theorem center_pow_three {F : Type*} [Field F] {Q : Type*} [Group Q]
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) F) : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1 := by
  intro z hz
  have hs : e z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    Subgroup.map_center_le_center (f := e) e.surjective ⟨z, hz, rfl⟩
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hs
  rw [Fintype.card_fin] at hr
  have h3 : (e z) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrg, ← map_pow, hr, map_one]
    rfl
  apply e.injective
  rw [map_pow, h3, map_one]

end Center

section PCore

theorem pCore_two_eq_bot_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hperf : commutator Q = ⊤) (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (hZ : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1) : CFSG.pCore 2 Q = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (CFSG.pCore 2 Q).Normal := CFSG.pCore_normal
  have hP : IsPGroup 2 (CFSG.pCore 2 Q) := CFSG.pCore_isPGroup
  have hmap : ((CFSG.pCore 2 Q).map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal
    ((CFSG.pCore 2 Q).map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · rw [eq_bot_iff]
    intro z hz
    have hzc : z ∈ Subgroup.center Q := by
      have h1 : QuotientGroup.mk' (Subgroup.center Q) z ∈
          (CFSG.pCore 2 Q).map (QuotientGroup.mk' (Subgroup.center Q)) := ⟨z, hz, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff z).mp h1
    obtain ⟨k, hk⟩ := hP ⟨z, hz⟩
    have hk' : z ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h3 : z ^ 3 = 1 := hZ z hzc
    have hord : orderOf z = 1 := by
      have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have h2 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
      have := Nat.dvd_gcd h2 h1
      rw [hcop] at this
      exact Nat.dvd_one.mp this
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hord)
  · exfalso
    have hpS : IsPGroup 2 (Q ⧸ Subgroup.center Q) := by
      intro x
      have hx : x ∈ (CFSG.pCore 2 Q).map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [h]
        trivial
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨k, hk⟩ := hP ⟨n, hn⟩
      refine ⟨k, ?_⟩
      have hk' : n ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
      rw [← map_pow, hk', map_one]
    haveI : Group.IsNilpotent (Q ⧸ Subgroup.center Q) := hpS.isNilpotent
    haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
    haveI : Group.IsPerfect Q := ⟨hperf⟩
    haveI : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center Q))
    exact Group.IsPerfect.not_isNilpotent (Q ⧸ Subgroup.center Q) ‹_›

variable {L B : Type*} [Group L] [Group B]

theorem pCore_prod_eq_ker_fst (hB : IsPGroup 2 B) (hL : CFSG.pCore 2 L = ⊥) :
    CFSG.pCore 2 (L × B) = (MonoidHom.fst L B).ker := by
  apply le_antisymm
  · intro x hx
    have hN : (CFSG.pCore 2 (L × B)).Normal := CFSG.pCore_normal
    have hP : IsPGroup 2 (CFSG.pCore 2 (L × B)) := CFSG.pCore_isPGroup
    have hmapN : ((CFSG.pCore 2 (L × B)).map (MonoidHom.fst L B)).Normal :=
      hN.map _ fun l => ⟨(l, 1), rfl⟩
    have hmapP : IsPGroup 2 ((CFSG.pCore 2 (L × B)).map (MonoidHom.fst L B)) := hP.map _
    have hle : (CFSG.pCore 2 (L × B)).map (MonoidHom.fst L B) ≤ CFSG.pCore 2 L :=
      le_sSup ⟨hmapN, hmapP⟩
    have h1 : (MonoidHom.fst L B) x ∈ (CFSG.pCore 2 (L × B)).map (MonoidHom.fst L B) :=
      ⟨x, hx, rfl⟩
    have h2 := hle h1
    rw [hL, Subgroup.mem_bot] at h2
    exact h2
  · have hn : (MonoidHom.fst L B).ker.Normal := MonoidHom.normal_ker _
    have hp : IsPGroup 2 (MonoidHom.fst L B).ker := by
      intro x
      obtain ⟨k, hk⟩ := hB x.1.2
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : x.1.1 = 1 := x.2
      apply Prod.ext
      · simp [h1]
      · simpa using hk
    exact le_sSup ⟨hn, hp⟩

theorem exists_quotientEquiv_fst (hB : IsPGroup 2 B) (hL : CFSG.pCore 2 L = ⊥) :
    ∃ e : (L × B) ⧸ CFSG.pCore 2 (L × B) ≃* L,
      ∀ x : L × B, e (QuotientGroup.mk x) = x.1 := by
  have h := pCore_prod_eq_ker_fst hB hL
  haveI : (MonoidHom.fst L B).ker.Normal := MonoidHom.normal_ker _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans
    (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.fst L B) fun l => ⟨(l, 1), rfl⟩),
    fun x => rfl⟩

end PCore

section Graph

variable {L B : Type*} [Group L] [Group B]

@[expose] def graphSub (lB : B →* L) : Subgroup (L × B) :=
  (lB.prod (MonoidHom.id B)).range

theorem mem_graphSub {lB : B →* L} {x : L × B} : x ∈ graphSub lB ↔ ∃ b : B, (lB b, b) = x :=
  Iff.rfl

theorem graphSub_isElementaryAbelian (lB : B →* L) (hc : ∀ b c : B, b * c = c * b)
    (h2 : ∀ b : B, b * b = 1) : CFSG.IsElementaryAbelian 2 (graphSub lB) := by
  refine CFSG.IsElementaryAbelian.two_of_forall_mul_self ?_ ?_
  · rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul, hc b c]
  · rintro _ ⟨b, rfl⟩
    rw [← map_mul, h2 b, map_one]

theorem not_graphSub_le_pCore (hB : IsPGroup 2 B) (hL : CFSG.pCore 2 L = ⊥) (lB : B →* L)
    (h : ∃ b : B, lB b ≠ 1) : ¬ graphSub lB ≤ CFSG.pCore 2 (L × B) := by
  rw [pCore_prod_eq_ker_fst hB hL]
  obtain ⟨b, hb⟩ := h
  intro hle
  exact hb (hle ⟨b, rfl⟩)

end Graph

end CFSG.LocalAnalysis.RankThreeUC.S15
