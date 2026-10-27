module

public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockLift
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockPure
import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer
import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerPGroup
import CFSG.RankThree.OddKernel.CentralCoverComponentModels
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open Subgroup

theorem two_le_pRank_of_perfect_of_commute {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {I H : Subgroup X} (hIH : I ≤ H) (hI : ⁅I, I⁆ = I)
    (hpI : p ∣ Nat.card I) {a : X} (haH : a ∈ H) (hao : orderOf a = p)
    (hac : ∀ x ∈ I, a * x = x * a) : 2 ≤ CFSG.Open.pRank p H := by
  have hp : p.Prime := Fact.out
  have hap : a ^ p = 1 := hao ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h => hp.one_lt.ne' (hao ▸ h ▸ orderOf_one)
  by_cases haI : a ∈ I
  · haveI : Group.IsPerfect I :=
      (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq I).mpr hI
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p I))
    have hz : (⟨a, haI⟩ : I) ∈ center I :=
      mem_center_iff.mpr fun g => Subtype.ext (hac g g.2).symm
    have hnc := CFSG.LocalAnalysis.RankThreeTheoremC.not_isCyclic_sylow_of_isPerfect
      inferInstance S hz (fun h => ha1 (congrArg Subtype.val h)) (Subtype.ext hap)
    obtain ⟨D, -, hD, hDc⟩ :=
      GL83.I243.Inner.exists_isElemAbelian_card_sq_of_not_isCyclic hp2 S.isPGroup' hnc
    refine CFSG.SectionRank.le_pRank hp.one_lt (E := D.map I.subtype)
      ((Subgroup.map_subtype_le D).trans hIH)
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hD _) ?_
    rw [Subgroup.card_map_of_injective I.subtype_injective, hDc]
  · obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' p hpI
    have hbo : orderOf (b : X) = p := by rw [Subgroup.orderOf_coe, hb]
    have hbI : zpowers (b : X) ≤ I := zpowers_le.mpr b.2
    have h := CFSG.RankThree.OddKernel.succ_le_pRank_of_commute hp (H := H)
      (CFSG.RankThree.OddKernel.isElemAbelian_zpowers_of_orderOf hbo).1 (r := 1)
      (CFSG.RankThree.OddKernel.isElemAbelian_zpowers_of_orderOf hbo).2
      (fun e he => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
        exact ((Commute.zpow_left (hac b b.2).symm k)))
      hap (fun h => haI (hbI h)) (hbI.trans hIH) haH
    simpa using h

private theorem eq_top_or_le_center' {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (N : Subgroup Q) (hN : N.Normal) : N = ⊤ ∨ N ≤ center Q := by
  obtain ⟨hp, hs⟩ := hQ
  haveI := hs
  haveI := hN.map (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center Q)))
    with h | h
  · right
    intro x hx
    have : (QuotientGroup.mk' (center Q)) x = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_map_of_mem _ hx
    exact (QuotientGroup.eq_one_iff x).mp this
  · left
    rw [eq_top_iff, ← hp, _root_.commutator_def, commutator_le]
    intro x _ y _
    obtain ⟨n, hn, hnx⟩ : (QuotientGroup.mk' (center Q)) x ∈
        N.map (QuotientGroup.mk' (center Q)) := h ▸ Subgroup.mem_top _
    have hz : n⁻¹ * x ∈ center Q := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hnx
      rw [hnx, inv_mul_cancel]
    have hx : x = n * (n⁻¹ * x) := by group
    rw [hx, commutatorElement_def]
    have hc := mem_center_iff.mp hz
    have e : n * (n⁻¹ * x) * y * (n * (n⁻¹ * x))⁻¹ * y⁻¹ = n * (y * n⁻¹ * y⁻¹) := by
      calc n * (n⁻¹ * x) * y * (n * (n⁻¹ * x))⁻¹ * y⁻¹
          = n * ((n⁻¹ * x) * y) * (n⁻¹ * x)⁻¹ * n⁻¹ * y⁻¹ := by group
        _ = n * (y * (n⁻¹ * x)) * (n⁻¹ * x)⁻¹ * n⁻¹ * y⁻¹ := by rw [hc y]
        _ = n * (y * n⁻¹ * y⁻¹) := by group
    rw [e]
    exact N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) y)

private theorem le_pCore' {X : Type*} [Group X] {q : ℕ} {K : Subgroup X} (hK : K.Normal)
    (hq : IsPGroup q K) : K ≤ CFSG.pCore q X :=
  le_sSup (show K ∈ {K : Subgroup X | K.Normal ∧ IsPGroup q K} from ⟨hK, hq⟩)

theorem joinIrreducible_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f)
    (h : ∀ N₁ N₂ : Subgroup A, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) :
    ∀ N₁ N₂ : Subgroup B, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤ := by
  intro N₁ N₂ h₁ h₂ h12
  have htop : ∀ N : Subgroup B, N.comap f = ⊤ → N = ⊤ := fun N hN => by
    rw [← Subgroup.map_comap_eq_self_of_surjective hf N, hN, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hf]
  rcases h (N₁.comap f) (N₂.comap f) (h₁.comap f) (h₂.comap f)
      (by rw [Subgroup.comap_sup_eq f N₁ N₂ hf, h12, Subgroup.comap_top]) with h | h
  · exact Or.inl (htop N₁ h)
  · exact Or.inr (htop N₂ h)

theorem joinIrreducible_of_isQuasisimple {A Q : Type*} [Group A] [Group Q] [Finite A] {q : ℕ}
    [Fact q.Prime] (hA : commutator A = ⊤) (ψ : A →* Q) (hψ : Function.Surjective ψ)
    (hQ : CFSG.Open.IsQuasisimple Q) (hk : IsPGroup q ψ.ker) :
    ∀ N₁ N₂ : Subgroup A, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤ := by
  have hQne : ¬ (⊤ : Subgroup Q) ≤ center Q := by
    intro h
    haveI := hQ.2
    have : Subsingleton (Q ⧸ center Q) := ⟨fun x y => by
      induction x using QuotientGroup.induction_on
      induction y using QuotientGroup.induction_on
      exact QuotientGroup.eq.mpr (h (mem_top _))⟩
    exact not_subsingleton _ this
  have hfull : ∀ N : Subgroup A, N.Normal → N.map ψ = ⊤ → N = ⊤ := by
    intro N hN hNt
    have hsup : N ⊔ ψ.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hNt, Subgroup.comap_top]
    set π := QuotientGroup.mk' N with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
    have hp : IsPGroup q (A ⧸ N) := by
      have h1 : ψ.ker.map π = ⊤ := by
        rw [eq_top_iff, ← Subgroup.map_top_of_surjective π hπs, ← hsup, Subgroup.map_sup]
        rw [show N.map π = ⊥ from by
          rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'], bot_sup_eq]
      have h2 := hk.map π
      intro g
      obtain ⟨k, hk'⟩ := h2 ⟨g, h1 ▸ Subgroup.mem_top g⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk'⟩
    have hcomm : commutator (A ⧸ N) = ⊤ := by
      rw [eq_top_iff, ← Subgroup.map_top_of_surjective π hπs, ← hA, _root_.commutator_def,
        _root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπs]
    obtain ⟨n, hn⟩ := _root_.nilpotent_iff_lowerCentralSeries.mp hp.isNilpotent
    have hl : ∀ k, (⊤ : Subgroup (A ⧸ N)).lowerCentralSeries k = ⊤ := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih, ← _root_.commutator_def, hcomm]
    rw [hl n] at hn
    rw [eq_top_iff]
    intro x _
    rw [← QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_bot).mp (hn ▸ Subgroup.mem_top _)
  intro N₁ N₂ h₁ h₂ h12
  have h12' : N₁.map ψ ⊔ N₂.map ψ = ⊤ := by
    rw [← Subgroup.map_sup, h12, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ]
  rcases eq_top_or_le_center' hQ _ (h₁.map ψ hψ) with h1 | h1
  · exact Or.inl (hfull N₁ h₁ h1)
  rcases eq_top_or_le_center' hQ _ (h₂.map ψ hψ) with h2 | h2
  · exact Or.inr (hfull N₂ h₂ h2)
  exact (hQne (h12' ▸ sup_le h1 h2)).elim

theorem nonempty_quotient_pCore_equiv_alt5 {A Q : Type}
    [Group A] [Group Q] [Finite A] (hA : commutator A = ⊤) (ψ : A →* Q)
    (hψ : Function.Surjective ψ) (hk2 : IsPGroup 2 ψ.ker) (hQ : CFSG.Open.IsQuasisimple Q)
    (f : A →* alternatingGroup (Fin 5)) (hf : Function.Surjective f) :
    Nonempty (A ⧸ CFSG.pCore 2 A ≃* alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  set O := CFSG.pCore 2 A with hO
  have hψO : ψ.ker ≤ O := le_pCore' ψ.normal_ker hk2
  have hle : O ≤ f.ker := by
    haveI : (O.map f).Normal := CFSG.pCore_normal.map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.map f) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      apply CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Pure.not_isPGroup_alt5
      intro y
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup.map f) ⟨y, h ▸ Subgroup.mem_top y⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcen : f.ker.map ψ ≤ center Q := by
    rcases eq_top_or_le_center' hQ _ (f.normal_ker.map ψ hψ) with h | h
    · exfalso
      have hall : ∀ x : A, x ∈ f.ker := fun x => by
        obtain ⟨k, hk, hkx⟩ := (show ψ x ∈ f.ker.map ψ from h ▸ Subgroup.mem_top _)
        have hn : k⁻¹ * x ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
        have := f.ker.mul_mem hk (hle (hψO hn))
        rwa [mul_inv_cancel_left] at this
      exact not_subsingleton (alternatingGroup (Fin 5)) ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hf a
        obtain ⟨y, rfl⟩ := hf b
        rw [(MonoidHom.mem_ker).mp (hall x), (MonoidHom.mem_ker).mp (hall y)]⟩
    · exact h
  set f' : A ⧸ O →* alternatingGroup (Fin 5) := QuotientGroup.lift O f hle with hf'
  have hf's : Function.Surjective f' := fun y => by
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨(x : A ⧸ O), rfl⟩
  have hZ : f'.ker ≤ center (A ⧸ O) := by
    intro z hz
    induction z using QuotientGroup.induction_on with | H z => ?_
    have hzf : z ∈ f.ker := hz
    have hzc := mem_center_iff.mp (hcen ⟨z, hzf, rfl⟩)
    refine mem_center_iff.mpr fun y => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply hψO
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hzc (ψ y), inv_mul_cancel]
  have hO2 : CFSG.pCore 2 (A ⧸ O) = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.pCore_quotient_pCore_eq_bot
  have hodd : Odd (Nat.card f'.ker) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hzc : (z : A ⧸ O) ∈ center (A ⧸ O) := hZ z.2
    have hzn : (zpowers (z : A ⧸ O)).Normal := ⟨fun n hn y => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
      have hc : Commute y (z : A ⧸ O) := mem_center_iff.mp hzc y
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers _) k⟩
    have hzp : IsPGroup 2 (zpowers (z : A ⧸ O)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    have hz1 : (z : A ⧸ O) ∈ CFSG.pCore 2 (A ⧸ O) := le_pCore' hzn hzp (mem_zpowers _)
    rw [hO2, Subgroup.mem_bot] at hz1
    have : orderOf z = 1 := by rw [← Subgroup.orderOf_coe, hz1, orderOf_one]
    omega
  have hA' : commutator (A ⧸ O) = ⊤ := by
    have hs := QuotientGroup.mk'_surjective O
    rw [eq_top_iff, ← Subgroup.map_top_of_surjective _ hs, ← hA, _root_.commutator_def,
      _root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hs]
  have hq : Nonempty (((A ⧸ O) ⧸ f'.ker) ≃* ↥(alternatingGroup (Fin 5))) :=
    ⟨QuotientGroup.quotientKerEquivOfSurjective f' hf's⟩
  have hgb : f'.ker = ⊥ := CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Lift.a5_no_odd_cext_aux
    hA' f'.ker hZ hodd hq
  exact ⟨MulEquiv.ofBijective f' ⟨(MonoidHom.ker_eq_bot_iff f').mp hgb, hf's⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
