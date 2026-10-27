module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Walter.J1Props.Janko
public import CFSG.Walter.Models
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionFusion

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

@[expose] def TheoremTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
    InvolutionPointLocalEmbedding H z → InvolutionPointCentralSylow z →
      fusionStronglyEmbedded (H.subgroupOf (involutionPointHull z))

structure CoreSetting (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) :
    Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  rank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G)
  proper : H ≠ ⊤
  sylow_le : (S : Subgroup G) ≤ H
  core_le : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H

@[expose] def IsCentralInvolution {G : Type} [Group G] (S : Subgroup G) (z : G) : Prop :=
  z ∈ S ∧ orderOf z = 2 ∧ ∀ s ∈ S, s * z = z * s

@[expose] def CentralCentralizerStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
      Subgroup.centralizer ({z} : Set G) ≤ H ∨ Nonempty (CFSG.Walter.J1Props.JankoHyp₀ G)

@[expose] def GeneratedCentralizerStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G),
    IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G) →
    properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤ → IsCentralInvolution (S : Subgroup G) z →
    properTwoGenCoreGamma (S : Subgroup G) 2 ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ →
      Nonempty (CFSG.Walter.J1Props.JankoHyp₀ G)

@[expose] def EscapingCentralizerStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
      Subgroup.centralizer ({z} : Set G) ≤ H →
      ∀ u : G, orderOf u = 2 → Commute u z → ¬ Subgroup.centralizer ({u} : Set G) ≤ H →
        u ∉ localInvolutionPointHull z u

theorem theoremTwo_of_no_minimal_failure
    (h : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z) : TheoremTwo := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n →
      ∀ (H : Subgroup G) (z : G), InvolutionPointLocalEmbedding H z →
        InvolutionPointCentralSylow z →
          fusionStronglyEmbedded (H.subgroupOf (involutionPointHull z)) by
    intro G _ _ H z hloc hcen
    exact key _ G rfl H z hloc hcen
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro G _ _ hcard H z hloc hcen
    by_contra hfail
    exact h G H z
      { local_datum := hloc
        central_sylow := hcen
        failure := hfail
        smaller := fun Y _ _ hY A a ha hb => IH _ (hcard ▸ hY) Y rfl A a ha hb }

variable {G : Type} [Group G] [Finite G]

theorem exists_centralInvolution (S : Sylow 2 G) (hrank : 1 ≤ CFSG.Open.pRank 2 (S : Subgroup G)) :
    ∃ z : G, IsCentralInvolution (S : Subgroup G) z := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial (S : Subgroup G) := by
    obtain ⟨E, hES, hE, hcard⟩ :=
      CFSG.SectionRank.exists_pRank (by decide : 1 < 2) (S : Subgroup G)
    have h2 : 1 < Nat.card E := by
      rw [hcard]
      exact Nat.one_lt_two_pow (by omega)
    have hEnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp h2
    obtain ⟨⟨x, hxE⟩, hx1⟩ := exists_ne (1 : E)
    refine ⟨⟨⟨x, hES hxE⟩, 1, fun h => hx1 ?_⟩⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  have hcenter : Nontrivial (Subgroup.center (S : Subgroup G)) :=
    IsPGroup.center_nontrivial S.isPGroup'
  have hdvd : 2 ∣ Nat.card (Subgroup.center (S : Subgroup G)) := by
    obtain ⟨n, hn⟩ := (S.isPGroup'.to_subgroup (Subgroup.center (S : Subgroup G))).exists_card_eq
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr hcenter).ne' hn
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨((c : (S : Subgroup G)) : G), ((c : (S : Subgroup G))).property, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  · intro s hs
    have hcomm := Subgroup.mem_center_iff.mp c.property ⟨s, hs⟩
    exact congrArg Subtype.val hcomm

theorem unique_containment_of_centralizer_le (S : Sylow 2 G) (H : Subgroup G)
    (hSH : (S : Subgroup G) ≤ H) (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    {z : G} (hzH : z ∈ H) (hz : orderOf z = 2)
    (hC : Subgroup.centralizer ({z} : Set G) ≤ H) (g : G) :
    z ∈ rightConjugate H g ↔ g ∈ H := by
  constructor
  · intro hmem
    have hconj : g * z * g⁻¹ ∈ H := by
      obtain ⟨h, hh, hhz⟩ := Subgroup.mem_map.mp hmem
      have : h = g * z * g⁻¹ := by
        rw [← hhz]
        simp [mul_assoc]
      exact this ▸ hh
    obtain ⟨h, hh, hhz⟩ :=
      two_generated_core_controls_involution_fusion
        S H hSH hcore z hzH hz g⁻¹ (by simpa only [inv_inv] using hconj)
    simp only [inv_inv] at hhz
    have hcent : h * g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzg : z * (h * g) = (h * g) * z := by
        calc z * (h * g) = h * (h⁻¹ * z * h) * g := by group
          _ = h * (g * z * g⁻¹) * g := by rw [hhz]
          _ = (h * g) * z := by group
      exact hzg.symm
    have hhg : h * g ∈ H := hC hcent
    simpa using H.mul_mem (H.inv_mem hh) hhg
  · intro hg
    refine Subgroup.mem_map.mpr ⟨g * z * g⁻¹, H.mul_mem (H.mul_mem hg hzH) (H.inv_mem hg), ?_⟩
    simp [mul_assoc]

theorem two_le_pRank_of_commuting_involutions {K : Subgroup G} {a b : G}
    (haK : a ∈ K) (hbK : b ∈ K) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hne : a ≠ b) (hab : Commute a b) : 2 ≤ CFSG.Open.pRank 2 K := by
  have haa : a * a = 1 := by simpa only [ha, pow_two] using pow_orderOf_eq_one a
  have hbb : b * b = 1 := by simpa only [hb, pow_two] using pow_orderOf_eq_one b
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    norm_num at ha
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    norm_num at hb
  let F := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a b haa hbb hab
  have hF : IsKleinFour F := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    a b haa hbb ha1 hb1 hne hab
  have hFK : F ≤ K := by
    intro x hx
    change x ∈ ({a * b, a, b, 1} : Set G) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact K.mul_mem haK hbK
    · exact haK
    · exact hbK
    · exact K.one_mem
  have hFelem : IsElemAbelian 2 F := by
    refine ⟨hF.isMulCommutative, fun x hx => ?_⟩
    have hexp : (⟨x, hx⟩ : F) ^ 2 = 1 := by
      rw [← hF.exponent_two]
      exact Monoid.pow_exponent_eq_one _
    exact congrArg Subtype.val hexp
  exact CFSG.SectionRank.le_pRank (by decide : 1 < 2) hFK hFelem
    (by rw [hF.card_four]; norm_num)

theorem local_embedding_of_not_mem (S : Sylow 2 G) (H : Subgroup G)
    (hSH : (S : Subgroup G) ≤ H) (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    {z : G} (hzH : z ∈ H) (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (hzC : Subgroup.centralizer ({z} : Set G) ≤ H)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hesc : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hnot : u ∉ localInvolutionPointHull z u) :
    fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := localInvolutionPointHull z u with hL
  have hzL : z ∈ L := distinguished_mem_localInvolutionPointHull huz
  have huH : u ∈ H := hzC (Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq.symm)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro htop
    obtain ⟨m, hmC, hmH⟩ := Set.not_subset.mp hesc
    have hxL : rightConjugateElem z m ∈ L := by
      apply mem_localInvolutionPointHull ⟨m, rfl⟩
      have hmu : Commute m u := Subgroup.mem_centralizer_singleton_iff.mp hmC
      exact (hmu.inv_left.mul_left huz.symm).mul_left hmu
    have hxH : rightConjugateElem z m ∈ H := by
      have : (⟨_, hxL⟩ : L) ∈ H.subgroupOf L := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have hmem : z ∈ rightConjugate H m⁻¹ := by
      refine Subgroup.mem_map.mpr ⟨rightConjugateElem z m, hxH, ?_⟩
      simp [rightConjugateElem, mul_assoc]
    exact hmH (by simpa using (huniq m⁻¹).mp hmem)
  ·
    have hzK : (⟨z, hzL⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hzH
    have horder : orderOf (⟨⟨z, hzL⟩, hzK⟩ : H.subgroupOf L) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact hz
    rw [even_iff_two_dvd, ← horder]
    exact orderOf_dvd_natCard _
  ·
    intro g hg
    by_contra hodd
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hodd
    have htK : ((t : L) : G) ∈ H := by
      have := t.property
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp this).1
    have htconj : ((t : L) : G) ∈ H.conjBy (g : G)⁻¹ := by
      obtain ⟨k, hk, hkt⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp t.property).2
      refine Subgroup.mem_map.mpr ⟨(k : G), Subgroup.mem_subgroupOf.mp hk, ?_⟩
      rw [← hkt]
      rfl
    have hgH : (g : G) ∉ H := fun h => hg (Subgroup.mem_subgroupOf.mpr h)
    have hlt := conjugate_intersection_rank_lt S H (k := 2) (by decide) hSH hcore (g : G) hgH
    have htord : orderOf ((t : L) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact ht
    have huconj : u ∈ H.conjBy (g : G)⁻¹ := by
      have hgu : (g : G) * u = u * (g : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (localInvolutionPointHull_le_centralizer z u g.property)
      refine Subgroup.mem_map.mpr ⟨u, huH, ?_⟩
      change (g : G)⁻¹ * u * (g : G)⁻¹⁻¹ = u
      rw [inv_inv, mul_assoc, ← hgu, ← mul_assoc, inv_mul_cancel, one_mul]
    have htu : Commute ((t : L) : G) u :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (localInvolutionPointHull_le_centralizer z u (t : L).property)
    have htne : ((t : L) : G) ≠ u := fun h => hnot (h ▸ (t : L).property)
    have h2 := two_le_pRank_of_commuting_involutions (K := H ⊓ H.conjBy (g : G)⁻¹)
      (Subgroup.mem_inf.mpr ⟨htK, htconj⟩) (Subgroup.mem_inf.mpr ⟨huH, huconj⟩)
      htord hu htne htu
    omega

theorem localEmbedding_of_steps (hB : EscapingCentralizerStep)
    (S : Sylow 2 G) (H : Subgroup G) (z : G) (hset : CoreSetting G S H)
    (hz : IsCentralInvolution (S : Subgroup G) z)
    (hzC : Subgroup.centralizer ({z} : Set G) ≤ H) :
    InvolutionPointLocalEmbedding H z := by
  have hzH : z ∈ H := hset.sylow_le hz.1
  have huniq := unique_containment_of_centralizer_le S H hset.sylow_le hset.core_le hzH hz.2.1 hzC
  exact
    { proper := hset.proper
      distinguished_mem := hzH
      distinguished_order := hz.2.1
      unique_containment := huniq
      local_embedding := fun u hu huz hesc =>
        local_embedding_of_not_mem S H hset.sylow_le hset.core_le hzH hz.2.1 huniq hzC u hu huz
          hesc (hB G S H z hset hz hzC u hu huz hesc) }

omit [Finite G] in
theorem centralSylow_of_isCentralInvolution (S : Sylow 2 G) {z : G}
    (hz : IsCentralInvolution (S : Subgroup G) z) : InvolutionPointCentralSylow z := by
  refine ⟨S, hz.1, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro s
  exact Subtype.ext (hz.2.2 s s.property)

omit [Finite G] in
theorem involutionPointHull_eq_top [IsSimpleGroup G] {z : G} (hz : z ≠ 1) :
    involutionPointHull z = ⊤ := by
  have hnormal := minimalLocalFailure_hull_normal z
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · exact absurd ((Subgroup.mem_bot.mp (hbot ▸ localPointHull_distinguished_mem z))) hz
  · exact htop

theorem fusionStronglyEmbedded_of_subgroupOf_top {H : Subgroup G}
    (h : fusionStronglyEmbedded (H.subgroupOf (⊤ : Subgroup G))) : fusionStronglyEmbedded H := by
  have hmap := h.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  have himage : (H.subgroupOf (⊤ : Subgroup G)).map
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom = H := by
    change (H.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = H
    rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
  rwa [himage] at hmap

theorem gamma_one_le_of_stronglyEmbedded (S : Sylow 2 G) {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) (hH : fusionStronglyEmbedded H) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≤ H := by
  rw [gamma_le_iff]
  intro Q hQS hQrank g hg
  by_contra hgH
  obtain ⟨E, hEQ, -, hEcard⟩ := CFSG.SectionRank.exists_pRank (by decide : 1 < 2) Q
  have hEeven : 2 ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self 2 (by omega)
  have hQle : Q ≤ H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hSH (hQS hx), Subgroup.mem_map.mpr ⟨g * x * g⁻¹, ?_, ?_⟩⟩
    · exact hSH (hQS ((Subgroup.mem_normalizer_iff.mp hg x).mp hx))
    · simp [mul_assoc]
  have hdvd : 2 ∣ Nat.card ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom) :=
    hEeven.trans ((Subgroup.card_dvd_of_le hEQ).trans (Subgroup.card_dvd_of_le hQle))
  exact (Nat.not_even_iff_odd.mpr (hH.2.2 g hgH)) (even_iff_two_dvd.mpr hdvd)

theorem canonical_of_steps (h2 : TheoremTwo) (hA : CentralCentralizerStep)
    (hB : EscapingCentralizerStep)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) := by
  set H := properTwoGenCoreGamma (S : Subgroup G) 2 with hHdef
  have hset : CoreSetting G S H :=
    ⟨inferInstance, hnonab, hrank, hcore, sylow_le_gamma S (by omega), le_rfl⟩
  obtain ⟨z, hz⟩ := exists_centralInvolution S (by omega)
  rcases hA G S H z hset hz with hzC | hJne
  · left
    have hloc := localEmbedding_of_steps hB S H z hset hz hzC
    have hstrong := h2 G H z hloc (centralSylow_of_isCentralInvolution S hz)
    have hz1 : z ≠ 1 := by
      intro h
      have := hz.2.1
      rw [h, orderOf_one] at this
      norm_num at this
    rw [involutionPointHull_eq_top hz1] at hstrong
    have hH := fusionStronglyEmbedded_of_subgroupOf_top hstrong
    intro hΓ
    apply hset.proper
    exact top_unique (hΓ ▸ gamma_one_le_of_stronglyEmbedded S hset.sylow_le hH)
  · right
    obtain ⟨hJ⟩ := hJne
    obtain ⟨e⟩ := hJ.nonempty_mulEquiv_walterJ1
    exact ⟨e.trans (MulEquiv.subgroupCongr CFSG.Walter.walterJ1_eq_properTwoGenCoreJ1)⟩

theorem generatedCentralizerStep_of_central (hA : CentralCentralizerStep) :
    GeneratedCentralizerStep := by
  intro G _ _ S z hsimple hnonab hrank hcore hz hjoin
  have hset : CoreSetting G S (properTwoGenCoreGamma (S : Subgroup G) 2) :=
    ⟨hsimple, hnonab, hrank, hcore, sylow_le_gamma S (by omega), le_rfl⟩
  rcases hA G S _ z hset hz with hzC | hJ
  · exact absurd (by rw [← hjoin, sup_eq_left.mpr hzC]) hcore
  · exact hJ

theorem canonical_of_generated_steps (h2 : TheoremTwo) (hA : GeneratedCentralizerStep)
    (hB : EscapingCentralizerStep)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) := by
  obtain ⟨z, hz⟩ := exists_centralInvolution S (by omega)
  by_cases hjoin : properTwoGenCoreGamma (S : Subgroup G) 2 ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤
  · right
    obtain ⟨hJ⟩ := hA G S z inferInstance hnonab hrank hcore hz hjoin
    obtain ⟨e⟩ := hJ.nonempty_mulEquiv_walterJ1
    exact ⟨e.trans (MulEquiv.subgroupCongr CFSG.Walter.walterJ1_eq_properTwoGenCoreJ1)⟩
  · left
    set H := properTwoGenCoreGamma (S : Subgroup G) 2 ⊔ Subgroup.centralizer ({z} : Set G)
      with hHdef
    have hset : CoreSetting G S H :=
      ⟨inferInstance, hnonab, hrank, hjoin,
        (sylow_le_gamma S (by omega)).trans le_sup_left, le_sup_left⟩
    have hzC : Subgroup.centralizer ({z} : Set G) ≤ H := le_sup_right
    have hloc := localEmbedding_of_steps hB S H z hset hz hzC
    have hstrong := h2 G H z hloc (centralSylow_of_isCentralInvolution S hz)
    have hz1 : z ≠ 1 := by
      intro h
      have := hz.2.1
      rw [h, orderOf_one] at this
      norm_num at this
    rw [involutionPointHull_eq_top hz1] at hstrong
    have hH := fusionStronglyEmbedded_of_subgroupOf_top hstrong
    intro hΓ
    apply hset.proper
    exact top_unique (hΓ ▸ gamma_one_le_of_stronglyEmbedded S hset.sylow_le hH)

end CFSG.ProperTwoGeneratedCore.Assembly
