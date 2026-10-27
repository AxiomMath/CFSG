module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem not_isCyclic_of_two_le_pRank {p : ℕ} (hprime : p.Prime) {S : Subgroup G}
    (h2 : 2 ≤ CFSG.Open.pRank p S) : ¬ IsCyclic S := by
  intro hS
  obtain ⟨E, hES, hE, hEc⟩ := pRank_attained p S (by omega)
  have hEcyc : IsCyclic E :=
    isCyclic_of_surjective (subgroupOfEquivOfLe hES).toMonoidHom
      (subgroupOfEquivOfLe hES).surjective
  obtain ⟨g, hg⟩ := hEcyc.exists_generator
  have hdvd : p ^ CFSG.Open.pRank p S ∣ p := by
    rw [← hEc, ← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hE.2 g g.2))
  have hle := (Nat.pow_le_pow_right hprime.pos h2).trans (Nat.le_of_dvd hprime.pos hdvd)
  nlinarith [hprime.two_le]

theorem not_isCyclic_of_isAlperinSubgroup {p : ℕ} [hfact : Fact p.Prime] {S Q : Subgroup G}
    (hSp : IsPGroup p S) (hS : ¬ IsCyclic S)
    (hQ : CFSG.RankTwoShapes.IsAlperinSubgroup p S Q) : ¬ IsCyclic Q := by
  classical
  intro hQc
  obtain ⟨hQS, -, hcent, hrad⟩ := hQ
  set N := normalizer (Q : Set G) with hN
  set C := centralizer (Q : Set G) with hC
  have hQab : IsMulCommutative Q :=
    ⟨⟨fun a b => (IsCyclic.commGroup (α := Q)).mul_comm a b⟩⟩
  have hQC : Q ≤ C := Subgroup.le_centralizer_iff_isMulCommutative.mpr hQab
  have hCN : C ≤ N := centralizer_le_normalizer _
  have hQlt : Q < S := lt_of_le_of_ne hQS fun h => hS (h ▸ hQc)
  have hgrow : Q < S ⊓ N :=
    pGroup_proper_subgroup_lt_internal_normalizer p hfact.out S Q hSp hQlt
  set ψ := Q.normalizerMonoidHom with hψ
  have hψker : ∀ x : N, ψ x = 1 ↔ (x : G) ∈ C := by
    intro x
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf]
  have hcomm : ∀ a b : MulAut Q, a * b = b * a := by
    intro a b
    apply (IsCyclic.mulAutMulEquiv Q).injective
    rw [map_mul, map_mul, mul_comm]
  set O : Subgroup (MulAut Q) := ((S ⊓ N).subgroupOf N).map ψ with hO
  have hOn : O.Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  set R : Subgroup G := (O.comap ψ).map N.subtype with hR
  have hRN : R ≤ N := map_subtype_le _
  have hCR : C ≤ R := by
    intro c hc
    refine ⟨⟨c, hCN hc⟩, ?_, rfl⟩
    change ψ ⟨c, hCN hc⟩ ∈ O
    rw [(hψker ⟨c, hCN hc⟩).mpr hc]
    exact O.one_mem
  have hNR : N ≤ normalizer (R : Set G) := by
    have : (O.comap ψ).Normal := hOn.comap ψ
    intro n hn
    apply Subgroup.le_normalizer_map N.subtype
    refine ⟨⟨n, hn⟩, ?_, rfl⟩
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hsup : Q ⊔ C = C := sup_eq_right.mpr hQC
  have hidx : ∃ k : ℕ, ((Q ⊔ C).subgroupOf R).index = p ^ k := by
    rw [hsup]
    let ξ : R →* MulAut Q := ψ.comp (Subgroup.inclusion hRN)
    have hξker : ξ.ker = C.subgroupOf R := by
      ext r
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hψker (Subgroup.inclusion hRN r)
    have hξrange : ξ.range ≤ O := by
      rintro _ ⟨⟨r, hr⟩, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hr
      exact hx
    have hOp : IsPGroup p O := (hSp.to_inf_left.comap_subtype (K := N)).map ψ
    obtain ⟨k, hk⟩ := hOp.exists_card_eq
    have hdvd : (C.subgroupOf R).index ∣ p ^ k := by
      rw [← hξker, Subgroup.index_ker, ← hk]
      exact Subgroup.card_dvd_of_le hξrange
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hfact.out).mp hdvd
    exact ⟨i, hi⟩
  have hRC : R = C := (hrad R (by rw [hsup]; exact hCR) hRN hNR hidx).trans hsup
  have hSN : S ⊓ N ≤ Q := by
    intro t ht
    have htR : t ∈ R := ⟨⟨t, ht.2⟩, ⟨⟨t, ht.2⟩, ht, rfl⟩, rfl⟩
    rw [hRC] at htR
    exact hcent ⟨htR, ht.1⟩
  exact hgrow.not_ge hSN

theorem mem_of_alperinDecomposition (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {A : Subgroup G} {c : G}
    (hdec : CFSG.RankTwoShapes.AlperinDecomposition p (P : Subgroup G) A c) : c ∈ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hPnc : ¬ IsCyclic (P : Subgroup G) := not_isCyclic_of_two_le_pRank hprime (by omega)
  induction hdec with
  | one => exact M.one_mem
  | step _ hQ _ hn ih =>
    have hQp : IsPGroup p _ := P.isPGroup'.to_le hQ.1
    exact M.mul_mem ih (normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hQp (hQ.1.trans hPM)
      (two_le_pRank_of_not_isCyclic hprime (sigmaA_odd p hp) hQp
        (not_isCyclic_of_isAlperinSubgroup P.isPGroup' hPnc hQ)) hn)

theorem exists_mem_conj_eq_of_map_le (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {A : Subgroup G} (hA : A ≤ P) {g : G} (hg : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ P) :
    ∃ c ∈ M, ∀ a ∈ A, c⁻¹ * a * c = g⁻¹ * a * g := by
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨c, hdec, hc⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion P hA hg
  exact ⟨c, mem_of_alperinDecomposition hS hU0 hp hM hdec, hc⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
