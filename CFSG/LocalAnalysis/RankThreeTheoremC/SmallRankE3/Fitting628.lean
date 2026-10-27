module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Delta
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem fit3_exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {Q R : Subgroup G}
    (hR : IsPGroup p R) (hQR : Q < R) : ∃ y ∈ R, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQR.ne ?_
    exact le_antisymm hQR.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQR.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

private theorem fit3_mem_normalizer_primeCore (q : ℕ) [Fact q.Prime] (D : Subgroup G) {g : G}
    (hg : g ∈ normalizer (D : Set G)) : g ∈ normalizer (rankThreePrimeCore q D : Set G) := by
  obtain ⟨hOD, hDO, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec q D
  have key : ∀ g ∈ normalizer (D : Set G), ∀ y ∈ rankThreePrimeCore q D,
      g * y * g⁻¹ ∈ rankThreePrimeCore q D := by
    intro g hg y hy
    have h1 : D.map (MulAut.conj g).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hg
    have h2 : (normalizer (rankThreePrimeCore q D : Set G)).map (MulAut.conj g).toMonoidHom =
        normalizer (((rankThreePrimeCore q D).map (MulAut.conj g).toMonoidHom : Subgroup G) :
          Set G) :=
      Subgroup.map_equiv_normalizer_eq (rankThreePrimeCore q D) (MulAut.conj g)
    have hle : (rankThreePrimeCore q D).map (MulAut.conj g).toMonoidHom ≤
        rankThreePrimeCore q D := by
      have hsub : (rankThreePrimeCore q D).map (MulAut.conj g).toMonoidHom ≤ D := by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp hg y).mp (hOD hy)
      refine le_sSup ⟨hsub, (normal_subgroupOf_iff_le_normalizer hsub).mpr ?_, ?_⟩
      · calc D = D.map (MulAut.conj g).toMonoidHom := h1.symm
          _ ≤ (normalizer (rankThreePrimeCore q D : Set G)).map (MulAut.conj g).toMonoidHom :=
            map_mono hDO
          _ = _ := h2
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hcop
    exact hle ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
private theorem fit3_normalizer_le_of_characteristic {H : Subgroup G} (K : Subgroup H)
    [hK : K.Characteristic] :
    normalizer (H : Set G) ≤ normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ x ∈ K.map H.subtype,
      g * x * g⁻¹ ∈ K.map H.subtype := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let φ : H ≃* H := H.normalizerMonoidHom ⟨g, hg⟩
    have hfix := Subgroup.characteristic_iff_map_eq.mp hK φ
    have hyK : φ y ∈ K := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem _ hy
    exact Subgroup.mem_map.mpr ⟨φ y, hyK, H.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ y⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

private theorem fit3_isNilpotent (H : Subgroup G) :
    Group.IsNilpotent (CFSG.fittingSubgroupOf H) := by
  have h : Group.IsNilpotent (CFSG.fittingSubgroup H) := inferInstance
  exact Group.nilpotent_of_mulEquiv
    ((CFSG.fittingSubgroup H).equivMapOfInjective H.subtype H.subtype_injective)

private theorem fit3_exists_pGroup {F : Subgroup G} [Group.IsNilpotent F] {q : ℕ}
    [Fact q.Prime] {g : G} (hgF : g ∈ F) (hg : orderOf g = q) :
    ∃ Q : Subgroup G, IsPGroup q Q ∧ Q ≤ F ∧ g ∈ Q ∧
      normalizer (F : Set G) ≤ normalizer (Q : Set G) := by
  have hzp : IsPGroup q (zpowers (⟨g, hgF⟩ : F)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, pow_one]
    exact hg
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  have hSc : (S : Subgroup F).Characteristic := Sylow.characteristic_of_normal S inferInstance
  exact ⟨(S : Subgroup F).map F.subtype, S.isPGroup'.map F.subtype, Subgroup.map_subtype_le _,
    ⟨⟨g, hgF⟩, hS (mem_zpowers _), rfl⟩, fit3_normalizer_le_of_characteristic _⟩

theorem fitting628_three (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hL62 : GL83SmallRankLemma62At3 G) {P M x z T}
    (hf : Prop627Failure G 3 P M x z T)
    (hR : Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2)) :
    CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD 3 x)) ⊓ M = ⊥ := by
  have hα : HasPrimeConstraint (G := M) 3 :=
    (hL62 hS hU0 P M hf.situation x z hf.point hf.central).resolve_right
      (lemma628_ii_three hS hU0 hf hR)
  show CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (rankThreePrimeCore 3
    (centralizer ({x} : Set G)))) ⊓ M = ⊥
  set C : Subgroup G := centralizer ({x} : Set G)
  set D : Subgroup G := rankThreePrimeCore 3 C
  set O : Subgroup G := rankThreePrimeCore 2 D
  set F : Subgroup G := CFSG.fittingSubgroupOf O
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥(F ⊓ M) ≠ 1 from fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqd
  have hgo : orderOf (g : G) = q := by rw [Subgroup.orderOf_coe]; exact hg
  have hgF : (g : G) ∈ F := g.2.1
  have hgM : (g : G) ∈ M := g.2.2
  have hDspec := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 C
  have hOspec := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D
  have hCO : C ≤ normalizer (O : Set G) := fun c hc =>
    fit3_mem_normalizer_primeCore 2 D (hDspec.2.1 hc)
  have hOF : normalizer (O : Set G) ≤ normalizer (F : Set G) :=
    fit3_normalizer_le_of_characteristic (CFSG.fittingSubgroup O)
  have := fit3_isNilpotent O
  obtain ⟨Q, hQp, hQF, hgQ, hFQ⟩ := fit3_exists_pGroup hgF hgo
  have hCQ : C ≤ normalizer (Q : Set G) := hCO.trans (hOF.trans hFQ)
  have hFO : F ≤ O := Subgroup.map_subtype_le _
  have hxz : x * z = z * x := mem_centralizer_iff.mp hf.central.centralizes x hf.point.mem
  have hBC : zpowers x ⊔ zpowers z ≤ C :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz.symm))
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hf.situation.mem_sigmaA hf.situation.isCoreMaxLocal).1
  have hBM : zpowers x ⊔ zpowers z ≤ M :=
    (sup_le (zpowers_le.mpr hf.point.mem) (zpowers_le.mpr hf.central.mem)).trans hPM
  have hBQ₁ : zpowers x ⊔ zpowers z ≤ normalizer ((Q ⊓ M : Subgroup G) : Set G) :=
    (le_inf (hBC.trans hCQ) (hBM.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hQ₁ne : Q ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem : (g : G) ∈ (⊥ : Subgroup G) := hbot ▸ (⟨hgQ, hgM⟩ : (g : G) ∈ Q ⊓ M)
    rw [Subgroup.mem_bot] at hmem
    have h1 : orderOf (g : G) = 1 := by rw [hmem, orderOf_one]
    exact hq.one_lt.ne' (hgo.symm.trans h1)
  have hcop : Nat.Coprime (Nat.card ↥(Q ⊓ M)) 6 := by
    have hdvd : Nat.card ↥(Q ⊓ M) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le ((inf_le_left.trans hQF).trans hFO)
    have hdvd' : Nat.card O ∣ Nat.card D := Subgroup.card_dvd_of_le hOspec.1
    have h2 : Nat.Coprime (Nat.card ↥(Q ⊓ M)) 2 :=
      (Nat.Coprime.coprime_dvd_right hdvd hOspec.2.2).symm
    have h3 : Nat.Coprime (Nat.card ↥(Q ⊓ M)) 3 :=
      (Nat.Coprime.coprime_dvd_right (hdvd.trans hdvd') hDspec.2.2).symm
    exact (show (6 : ℕ) = 2 * 3 by norm_num) ▸ Nat.Coprime.mul_right h2 h3
  have hN₁ : normalizer ((Q ⊓ M : Subgroup G) : Set G) ≤ M :=
    prop65Alpha_of_kfacts hS hU0 hK1 hK2 P M hf.situation hα x z hf.point hf.central
      (Q ⊓ M) inf_le_right hQ₁ne hcop hBQ₁
  have hQM : Q ≤ M := by
    by_contra hQM
    have hlt : Q ⊓ M < Q :=
      lt_of_le_of_ne inf_le_left fun heq => hQM (heq.symm.le.trans inf_le_right)
    obtain ⟨y, hyQ, hyN, hyY⟩ := fit3_exists_mem_normalizer_not_mem hQp hlt
    exact hyY ⟨hyQ, hN₁ hyN⟩
  rw [inf_eq_left.mpr hQM] at hN₁
  exact hf.point.not_centralizer_le (hCQ.trans hN₁)


end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
