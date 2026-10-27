module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632NearCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Faithful
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Good
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl
public import CFSG.LocalAnalysis.RankThreeTheoremC.StrongEmbeddingCase
public import Mathlib.GroupTheory.Focal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem commutator_eq_top_step0 [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with
    h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

theorem sylow_le_commutator_of_situation (hS : Setting G) (hU0 : FullCoreLocal G)
    {P : Sylow 3 G} {M : Subgroup G} (hs : SmallRankSituation G 3 P M) :
    (P : Subgroup G) ≤ ⁅M, M⁆ := by
  have := hS.simple
  have hfoc := Subgroup.commutator_inf_eq_focalSubgroup P
  rw [commutator_eq_top_step0 hS.nonab, top_inf_eq] at hfoc
  rw [hfoc, Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro _ ⟨hgP, x, hxP, u, rfl⟩
  have hux : u * x * u⁻¹ ∈ (P : Subgroup G) := by
    have h := (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hxP) hgP
    rw [commutatorElement_def] at h
    simpa [mul_assoc] using (P : Subgroup G).inv_mem h
  have hmap : (zpowers x).map (MulAut.conj u⁻¹⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    simpa [MulAut.conj_apply] using hux
  obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le hS hU0 hs.mem_sigmaA hs.isCoreMaxLocal
    (zpowers_le.mpr hxP) hmap
  have hcx : c⁻¹ * x * c = u * x * u⁻¹ := by
    simpa using hc x (mem_zpowers x)
  have heq : ⁅x, u⁆ = ⁅x, c⁻¹⁆ := by
    rw [commutatorElement_def, commutatorElement_def, inv_inv]
    calc x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
      _ = x * (c⁻¹ * x * c)⁻¹ := by rw [hcx]
      _ = x * c⁻¹ * x⁻¹ * c := by group
  rw [heq]
  exact commutator_mem_commutator
    ((sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal).1 hxP) (M.inv_mem hcM)

theorem not_dvd_relIndex_of_commutator_le_of_situation (hS : Setting G) (hU0 : FullCoreLocal G)
    {P : Sylow 3 G} {M : Subgroup G} (hs : SmallRankSituation G 3 P M) {N : Subgroup G}
    (hNM : N ≤ M) (hcomm : ⁅M, M⁆ ≤ N) : ¬ 3 ∣ N.relIndex M := by
  have hPN : (P : Subgroup G) ≤ N := (sylow_le_commutator_of_situation hS hU0 hs).trans hcomm
  have hPM : (P : Subgroup G) ≤ M := hPN.trans hNM
  intro hdvd
  have h1 : N.relIndex M ∣ (P : Subgroup G).relIndex M := relIndex_dvd_of_le_left M hPN
  have h2 : (P : Subgroup G).relIndex M ∣ (P : Subgroup G).index := by
    rw [← relIndex_top_right, ← relIndex_mul_relIndex (P : Subgroup G) M ⊤ hPM le_top]
    exact dvd_mul_right _ _
  exact P.not_dvd_index (hdvd.trans (h1.trans h2))

theorem no_normal_index_three_of_situation (hS : Setting G) (hU0 : FullCoreLocal G)
    {P : Sylow 3 G} {M : Subgroup G} (hs : SmallRankSituation G 3 P M) :
    ∀ K : Subgroup M, K.Normal → K.index ≠ 3 := by
  intro K hK h3
  have hcyc : IsCyclic (M ⧸ K) := by
    apply isCyclic_of_prime_card (p := 3)
    rw [← Subgroup.index, h3]
  have hab : IsMulCommutative (M ⧸ K) :=
    ⟨⟨fun a b => (IsCyclic.commGroup (α := M ⧸ K)).mul_comm a b⟩⟩
  have hcK : commutator M ≤ K := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hab
  have hNM : K.map M.subtype ≤ M := map_subtype_le K
  have hcomm : ⁅M, M⁆ ≤ K.map M.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hmem : ⁅(⟨a, ha⟩ : M), (⟨b, hb⟩ : M)⁆ ∈ K :=
      hcK (commutator_mem_commutator (mem_top _) (mem_top _))
    exact ⟨_, hmem, rfl⟩
  have hidx : (K.map M.subtype).relIndex M = 3 := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      comap_map_eq_self_of_injective M.subtype_injective, h3]
  exact not_dvd_relIndex_of_commutator_le_of_situation hS hU0 hs hNM hcomm (by rw [hidx])

theorem pRank_le_two_of_situation (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) :
    CFSG.Open.pRank q M ≤ 2 := by
  by_contra hlt
  have hq2 : q ≠ 2 := by omega
  have hM := hs.isCoreMaxLocal.1.1
  have hle := local_pRank_le_evenRank q hq hq2 M hM
  have hloc := local_pRank_le_localRank q hq.one_lt M hM
  have hlocle := rankThreeLocalRank_le_evenRank (G := G) q hq hq2
  have h3le := rankThreeLocalRank_le_evenRank (G := G) 3 Nat.prime_three (by norm_num)
  rw [hS.rank] at hle hlocle h3le
  have hdvd := prime_dvd_card_of_pRank_pos q M (by omega)
  have h3 := hs.mem_sigmaA
  dsimp only [rankThreeSigmaA] at h3
  split_ifs at h3 with h₁ h₂ h₃
  · exact absurd h3.2.2.2 (by omega)
  · exact absurd h3.2.1 (by norm_num)
  · exact absurd h3.2.1 (by norm_num)
  · exact h₃ ⟨q, hq, by omega, hdvd, by omega⟩

private theorem exists_smallRankCentral_of_ne_bot_step0 {P : Sylow 3 G}
    (hP : (P : Subgroup G) ≠ ⊥) : ∃ z : G, SmallRankCentral P z := by
  have hnt : Nontrivial (P : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hP
  have hZ : Nontrivial (center (P : Subgroup G)) := P.isPGroup'.center_nontrivial
  have hdvd : 3 ∣ Nat.card (center (P : Subgroup G)) :=
    (P.isPGroup'.to_subgroup _).card_eq_or_dvd.resolve_left fun h =>
      (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hc' : orderOf ((c : P) : G) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  refine ⟨((c : P) : G), (c : P).2, ?_, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨h, hh⟩)
  · intro h1
    rw [h1, orderOf_one] at hc'
    omega
  · have h := pow_orderOf_eq_one ((c : P) : G)
    rwa [hc'] at h

theorem exists_smallRankCentral {P : Sylow 3 G} (hP : (P : Subgroup G) ≠ ⊥) :
    ∃ z : G, SmallRankCentral P z :=
  exists_smallRankCentral_of_ne_bot_step0 hP

private theorem exists_transvection_step0 (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) :
    ∃ g ∈ (P : Subgroup G), ∃ b : ℕ, ¬ 3 ∣ b ∧ g * x * g⁻¹ = x * z ^ b := by
  have hB := SmallRankPlane.of_situation hS hs hx hz
  obtain ⟨-, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal
  have hA : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ CFSG.IsElementaryAbelian 3 A ∧
      Nat.card A = 3 ^ 3 := by
    obtain ⟨A, hAP, hAe, hAc⟩ := pRank_attained 3 (P : Subgroup G) (by omega)
    exact ⟨A, hAP, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe,
      by rwa [hP3] at hAc⟩
  obtain ⟨hcomm, h, hh, hne⟩ := hB.exists_transvection Nat.prime_three P.isPGroup'
    hz.centralizes hz.ne_one hz.pow_eq_one hA
  obtain ⟨k, hk⟩ : ∃ k : ℕ, z ^ k = h * x * h⁻¹ * x⁻¹ :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hcomm h hh))
  refine ⟨h, hh.1, k, ?_, ?_⟩
  · rintro ⟨j, rfl⟩
    apply hne
    rw [← hk, pow_mul, hz.pow_eq_one, one_pow]
  · have hxz : Commute x z := mem_centralizer_iff.mp hz.centralizes x hx.mem
    rw [(hxz.pow_right k).eq, hk]
    group

private theorem isKleinOrQ8Central_step0 (h627 : GL83SmallRankProp627 G) {P : Sylow 3 G}
    {M : Subgroup G} (hs : SmallRankSituation G 3 P M) {x : G} (hx : SmallRankPoint P M x)
    {T : Subgroup G} (hT : SmallRankSylowTwo P M T) :
    IsKleinOrQ8Central (T ⊓ centralizer ({x} : Set G)) := by
  rcases (h627 3 P M hs).2 x hx T hT with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem not_le_centralizer_step0 (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {T : Subgroup G} (hT : SmallRankSylowTwo P M T) :
    ¬ (T ⊓ centralizer ({x} : Set G)) ≤ centralizer ({z} : Set G) := by
  intro hle
  obtain ⟨v, hv, hzv⟩ := exists_mem_inf_centralizer_not_commute hS hs hx hz hT
  exact hzv (mem_centralizer_singleton_iff.mp (hle hv)).symm

private theorem mem_normalizer_inf_centralizer_step0 {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {T : Subgroup G}
    (hT : SmallRankSylowTwo P M T) :
    z ∈ normalizer ((T ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have hzx : z ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.centralizes x hx.mem).symm
  exact inf_normalizer_le_normalizer_inf ⟨hT.normalized hz.mem, le_normalizer hzx⟩

omit [Finite G] in
private theorem centralizer_sup_zpowers_step0 (x z : G) :
    centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) =
      centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) := by
  rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union, centralizer_closure]
  ext g
  simp [mem_centralizer_iff, and_comm]

theorem exists_smallRank3Data (hS : Setting G) (hU0 : FullCoreLocal G)
    (h627 : GL83SmallRankProp627 G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) :
    ∃ (x z g : G) (T : Subgroup G), SmallRank3Data P M x z g T := by
  obtain ⟨x, hx⟩ := exists_smallRankPoint hS hU0 hs.mem_sigmaA hs.isCoreMaxLocal
    hs.not_gamma_one_le hs.largeObstruction_empty
  have hP : (P : Subgroup G) ≠ ⊥ := fun h => hx.ne_one (by simpa [h] using hx.mem)
  obtain ⟨z, hz⟩ := exists_smallRankCentral_of_ne_bot_step0 hP
  obtain ⟨T, hT⟩ := exists_smallRankSylowTwo hS hs.mem_sigmaA hs.isCoreMaxLocal
  obtain ⟨g, hgP, hg⟩ := exists_transvection_step0 hS hs hx hz
  have hKQ := isKleinOrQ8Central_step0 h627 hs hx hT
  have hnc := not_le_centralizer_step0 hS hs hx hz hT
  have hcyc := isCyclic_inf_centralizer_of_isKleinOrQ8Central hKQ hz.pow_eq_one
    (mem_normalizer_inf_centralizer_step0 hx hz hT) hnc
  refine ⟨x, z, g, T, hx, hz, hT, hgP, hg, hKQ, hnc, NearCyclic.of_isKleinOrQ8Central hKQ, ?_⟩
  rwa [centralizer_sup_zpowers_step0, ← inf_assoc]

end CFSG.LocalAnalysis.RankThreeTheoremC
