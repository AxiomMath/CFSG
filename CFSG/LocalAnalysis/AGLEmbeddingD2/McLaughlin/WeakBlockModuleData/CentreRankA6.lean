module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CyclicSylow
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Equiv CFSG.AGLEmbedding CFSG.QuasithinUnique

theorem alt6_five_cycle : ∀ g : alternatingGroup (Fin 6), g ^ 5 = 1 → g ≠ 1 →
    ∃ x : Fin 6, Function.Injective fun i : Fin 5 => ((g : Perm (Fin 6)) ^ (i : ℕ)) x := by
  decide +kernel

theorem alt6_transitive : ∀ y z : Fin 6, ∃ g : alternatingGroup (Fin 6), (g : Perm (Fin 6)) y = z := by
  decide +kernel

theorem alt6_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem alt6_no_order_forty (K : Subgroup (alternatingGroup (Fin 6))) (hK : Nat.card K = 40) :
    False := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 (by rw [hK]; norm_num)
  have hg5 : (g : alternatingGroup (Fin 6)) ^ 5 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have hg1 : (g : alternatingGroup (Fin 6)) ≠ 1 := fun h => by
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    omega
  obtain ⟨x, hx⟩ := alt6_five_cycle _ hg5 hg1
  have hmem : ∀ i : Fin 5, ((((g : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ (i : ℕ)) x) ∈
      MulAction.orbit K x := fun i => ⟨g ^ (i : ℕ), by simp [Subgroup.smul_def]⟩
  have hO5 : 5 ≤ Nat.card (MulAction.orbit K x) := by
    have := Nat.card_le_card_of_injective
      (fun i : Fin 5 => (⟨_, hmem i⟩ : MulAction.orbit K x))
      (fun a b hab => hx (congrArg Subtype.val hab))
    simpa using this
  have hO6 : Nat.card (MulAction.orbit K x) ≤ 6 := by
    have := Nat.card_le_card_of_injective (Subtype.val : MulAction.orbit K x → Fin 6)
      Subtype.val_injective
    simpa using this
  have hstab := MulAction.card_orbit_mul_card_stabilizer_eq_card_group K x
  simp only [← Nat.card_eq_fintype_card] at hstab
  rw [hK] at hstab
  have hdvd : Nat.card (MulAction.orbit K x) ∣ 40 := ⟨_, hstab.symm⟩
  have hO : Nat.card (MulAction.orbit K x) = 5 := by
    interval_cases h : Nat.card (MulAction.orbit K x) <;> simp_all
  have hncard : (MulAction.orbit K x).ncard = 5 := by
    rw [← Nat.card_coe_set_eq]; exact hO
  have hcompl := Set.ncard_add_ncard_compl (MulAction.orbit K x)
  have hc1 : ((MulAction.orbit K x)ᶜ).ncard = 1 := by
    rw [hncard, Nat.card_eq_fintype_card, Fintype.card_fin] at hcompl
    omega
  obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp hc1
  have hyc : y ∈ (MulAction.orbit K x)ᶜ := by rw [hy]; rfl
  have hfix : ∀ k : K, k • y = y := by
    intro k
    have hk : k • y ∈ (MulAction.orbit K x)ᶜ := by
      intro hmem
      apply hyc
      obtain ⟨a, ha⟩ := hmem
      have ha' : a • x = k • y := ha
      exact ⟨k⁻¹ * a, by
        show (k⁻¹ * a) • x = y
        rw [mul_smul, ha', ← mul_smul]; simp⟩
    rw [hy] at hk
    exact hk
  have hle : K ≤ MulAction.stabilizer (alternatingGroup (Fin 6)) y := fun k hk => hfix ⟨k, hk⟩
  have horbA : MulAction.orbit (alternatingGroup (Fin 6)) y = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨g, hg⟩ := alt6_transitive y z
    exact ⟨g, hg⟩
  have hA := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (alternatingGroup (Fin 6)) y
  simp only [← Nat.card_eq_fintype_card] at hA
  rw [horbA, alt6_card] at hA
  have hAo : Nat.card (Set.univ : Set (Fin 6)) = 6 := by simp
  rw [hAo] at hA
  have hstab60 : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 6)) y) = 60 := by omega
  have := Subgroup.card_dvd_of_le hle
  rw [hK, hstab60] at this
  omega

theorem a6_no_normal_three_complement {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* alternatingGroup (Fin 6)) (T J : Subgroup Y) (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set Y) ≤ J) (hJne : J ≠ Subgroup.normalizer (T : Set Y))
    (K : Subgroup Y) (hKJ : K ≤ J) (hKn : (K.subgroupOf J).Normal) (hK3 : ¬ 3 ∣ Nat.card K)
    (hidx : ∃ k : ℕ, (K.subgroupOf J).index = 3 ^ k) : False := by
  have hY : Nat.card Y = 360 := by rw [Nat.card_congr e.toEquiv]; exact alt6_card
  have hTJ : T ≤ J := le_trans Subgroup.le_normalizer hNJ
  have hTcard : Nat.card T = 8 := by
    have h1 := Subgroup.card_mul_index T
    obtain ⟨a, ha⟩ := hT.2.1.exists_card_eq
    have hidxT : ¬ 2 ∣ T.index := by
      have := hT.2.2
      change ¬ 2 ∣ T.relIndex ⊤ at this
      rwa [Subgroup.relIndex_top_right] at this
    rw [ha, hY] at h1
    have ha3 : a ≤ 3 := by
      by_contra hlt
      have : 2 ^ 4 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
      have : 2 ^ 4 ∣ 360 := by rw [← h1]; exact this.mul_right _
      omega
    rw [ha]
    interval_cases a <;> omega
  haveI := hKn
  obtain ⟨k, hk⟩ := hidx
  have hTK : T ≤ K := by
    intro t ht
    have htJ : t ∈ J := hTJ ht
    obtain ⟨s, hs⟩ := hT.2.1 ⟨t, ht⟩
    have hts : t ^ 2 ^ s = 1 := congrArg Subtype.val hs
    set q : J ⧸ K.subgroupOf J := QuotientGroup.mk ⟨t, htJ⟩ with hq
    have hq1 : q ^ 2 ^ s = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have : (⟨t, htJ⟩ : J) ^ 2 ^ s = 1 := Subtype.ext hts
      rw [this, QuotientGroup.mk_one]
    have hcardQ : Nat.card (J ⧸ K.subgroupOf J) = 3 ^ k := by
      rw [← hk]; rfl
    have h1 : orderOf q ∣ 2 ^ s := orderOf_dvd_of_pow_eq_one hq1
    have h2 : orderOf q ∣ 3 ^ k := hcardQ ▸ orderOf_dvd_natCard q
    have hself : Nat.Coprime (orderOf q) (orderOf q) := by
      have hc : Nat.Coprime (2 ^ s) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
      exact (hc.coprime_dvd_left h1).coprime_dvd_right h2
    have hq1' : q = 1 := orderOf_eq_one_iff.mp (Nat.coprime_self _ |>.mp hself)
    have : (⟨t, htJ⟩ : J) ∈ K.subgroupOf J := (QuotientGroup.eq_one_iff _).mp hq1'
    exact this
  have hK360 : Nat.card K ∣ 360 := hY ▸ Subgroup.card_subgroup_dvd_card K
  have hcop : Nat.Coprime (Nat.card K) (3 ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK3).symm
  have hK40 : Nat.card K ∣ 40 :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop (by simpa using hK360)
  have hK8 : 8 ∣ Nat.card K := hTcard ▸ Subgroup.card_dvd_of_le hTK
  have hle40 : Nat.card K ≤ 40 := Nat.le_of_dvd (by norm_num) hK40
  have hKc : Nat.card K = 8 ∨ Nat.card K = 40 := by
    interval_cases h : Nat.card K <;> omega
  rcases hKc with h8 | h40
  · have hTeq : T = K := Subgroup.eq_of_le_of_card_ge hTK (by rw [hTcard, h8])
    have hJN : J ≤ Subgroup.normalizer (K : Set Y) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mp hKn
    rw [← hTeq] at hJN
    exact hJne (le_antisymm hJN hNJ)
  · exact alt6_no_order_forty (K.map e.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e.injective, h40])

open CFSG.Open in
set_option maxHeartbeats 800000 in
theorem two_le_pRank_of_A6_extension {X : Type} [Group X] [Finite X] (P : Subgroup X)
    (hZP : Subgroup.center X ≤ P) (h3 : 3 ∣ Nat.card (Subgroup.center X))
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6))
    {T : Subgroup (X ⧸ Subgroup.center X)} (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set (X ⧸ Subgroup.center X)) ≤
      P.map (QuotientGroup.mk' (Subgroup.center X)))
    (hJne : P.map (QuotientGroup.mk' (Subgroup.center X)) ≠
      Subgroup.normalizer (T : Set (X ⧸ Subgroup.center X))) :
    2 ≤ Open.pRank 3 P := by
  classical
  by_contra hlt
  push Not at hlt
  have h3p : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3p⟩
  set π := QuotientGroup.mk' (Subgroup.center X) with hπ
  obtain ⟨R⟩ : Nonempty (Sylow 3 ↥P) := inferInstance
  have hrk : CFSG.pRank 3 ↥P ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    omega
  have hcycS : IsCyclic ↥((R : Subgroup ↥P).map P.subtype) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one h3p (by norm_num) (Subgroup.map_subtype_le _)
      (R.isPGroup'.map P.subtype) hrk
  have hcyc : IsCyclic ↥(R : Subgroup ↥P) :=
    ((Subgroup.equivMapOfInjective (R : Subgroup ↥P) P.subtype P.subtype_injective).isCyclic).mpr
      hcycS
  obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 h3
  set z0 : ↥P := ⟨(z' : X), hZP z'.2⟩ with hz0
  have hz0ord : orderOf z0 = 3 := by
    have : orderOf z0 = orderOf (z' : X) := (Subgroup.orderOf_mk _ _)
    rw [this, Subgroup.orderOf_coe, hz']
  have hz0c : ∀ g : ↥P, g * z0 = z0 * g := fun g =>
    Subtype.ext ((Subgroup.mem_center_iff.mp z'.2 (g : X)))
  have hz0R : z0 ∈ (R : Subgroup ↥P) := by
    have hpg : IsPGroup 3 (Subgroup.zpowers z0) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz0ord]; norm_num)
    haveI : (Subgroup.zpowers z0).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have : g * z0 ^ k * g⁻¹ = z0 ^ k := by
        rw [(Commute.zpow_right (show Commute g z0 from hz0c g) k).eq]; group
      rw [this]
      exact Subgroup.zpow_mem_zpowers z0 k
    exact hpg.le_sylow_of_normal R (Subgroup.mem_zpowers z0)
  obtain ⟨K, hKn, hKc⟩ := exists_normal_complement_of_cyclic_sylow R hcyc hz0R hz0ord hz0c
  set J := P.map π with hJ
  set φ : ↥P →* ↥J := π.subgroupMap P with hφ
  have hφs : Function.Surjective φ := π.subgroupMap_surjective P
  set K' : Subgroup ↥J := K.map φ with hK'
  set Kb : Subgroup (X ⧸ Subgroup.center X) := K'.map J.subtype with hKb
  have hKbJ : Kb ≤ J := Subgroup.map_subtype_le K'
  have hKbsub : Kb.subgroupOf J = K' := by
    rw [hKb, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective J.subtype_injective]
  haveI := hKn
  have hK'norm : K'.Normal := Subgroup.Normal.map hKn φ hφs
  have hKbnorm : (Kb.subgroupOf J).Normal := by rw [hKbsub]; exact hK'norm
  have hKcard : Nat.card K = (R : Subgroup ↥P).index := (hKc.index_eq_card).symm
  have hK3 : ¬ 3 ∣ Nat.card K := by rw [hKcard]; exact R.not_dvd_index
  have hKb3 : ¬ 3 ∣ Nat.card Kb := by
    intro h
    apply hK3
    refine h.trans ?_
    rw [hKb, Subgroup.card_map_of_injective J.subtype_injective]
    exact (Subgroup.card_map_dvd (H := K) φ : Nat.card (K.map φ) ∣ Nat.card K)
  have hKidx : K.index = Nat.card R := by
    have h1 := Subgroup.card_mul_index K
    have h2 := hKc.card_mul_card
    have hpos : 0 < Nat.card K := Nat.card_pos
    have : Nat.card K * K.index = Nat.card K * Nat.card R := by rw [h1, h2]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hidx : ∃ k : ℕ, (Kb.subgroupOf J).index = 3 ^ k := by
    obtain ⟨a, ha⟩ := R.isPGroup'.exists_card_eq
    have hdvd : (Kb.subgroupOf J).index ∣ 3 ^ a := by
      rw [hKbsub, ← ha, ← hKidx]
      exact Subgroup.index_map_dvd K hφs
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow h3p).mp hdvd
    exact ⟨j, hj⟩
  exact a6_no_normal_three_complement e T J hT hNJ hJne Kb hKbJ hKbnorm hKb3 hidx

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
