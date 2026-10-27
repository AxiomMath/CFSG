module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Main

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open Subgroup

section General

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem op_facts [Fact p.Prime] (M : Subgroup G) :
    (∀ m ∈ M, ∀ r ∈ (CFSG.Op_p'p p ↥M).map M.subtype,
        m * r * m⁻¹ ∈ (CFSG.Op_p'p p ↥M).map M.subtype) ∧
    (∀ m ∈ M, ∀ t ∈ (CFSG.pPrimeCore p ↥M).map M.subtype,
        m * t * m⁻¹ ∈ (CFSG.pPrimeCore p ↥M).map M.subtype) ∧
    Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p ↥M).map M.subtype)) ∧
    (∀ r ∈ (CFSG.Op_p'p p ↥M).map M.subtype,
        ∃ n : ℕ, r ^ (p ^ n) ∈ (CFSG.pPrimeCore p ↥M).map M.subtype) ∧
    (CFSG.pPrimeCore p ↥M).map M.subtype ≤ (CFSG.Op_p'p p ↥M).map M.subtype := by
  have hOpn : (CFSG.Op_p'p p ↥M).Normal := inferInstance
  have hTn : (CFSG.pPrimeCore p ↥M).Normal := CFSG.pPrimeCore_normal
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m hm r hr
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
    refine Subgroup.mem_map.mpr ⟨(⟨m, hm⟩ : ↥M) * r' * (⟨m, hm⟩ : ↥M)⁻¹,
      hOpn.conj_mem _ hr' _, rfl⟩
  · intro m hm t ht
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
    refine Subgroup.mem_map.mpr ⟨(⟨m, hm⟩ : ↥M) * t' * (⟨m, hm⟩ : ↥M)⁻¹,
      hTn.conj_mem _ ht' _, rfl⟩
  · have hinj : Function.Injective M.subtype := M.subtype_injective
    rw [Subgroup.card_map_of_injective hinj]
    exact CFSG.pPrimeCore_coprime_card
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
    have hmem : (QuotientGroup.mk' (CFSG.pPrimeCore p ↥M) r') ∈
        CFSG.pCore p (↥M ⧸ CFSG.pPrimeCore p ↥M) := hr'
    have hpg : IsPGroup p (CFSG.pCore p (↥M ⧸ CFSG.pPrimeCore p ↥M)) :=
      CFSG.pCore_isPGroup
    obtain ⟨n, hn⟩ := hpg ⟨_, hmem⟩
    refine ⟨n, Subgroup.mem_map.mpr ⟨r' ^ (p ^ n), ?_, rfl⟩⟩
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore p ↥M) (r' ^ (p ^ n)) = 1 := by
      rw [map_pow]
      have h2 := congrArg Subtype.val hn
      simpa using h2
    exact (QuotientGroup.eq_one_iff _).mp h1
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
    refine Subgroup.mem_map.mpr ⟨t', ?_, rfl⟩
    have : (QuotientGroup.mk' (CFSG.pPrimeCore p ↥M) t') = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ht'
    show (QuotientGroup.mk' (CFSG.pPrimeCore p ↥M) t') ∈ CFSG.pCore p _
    rw [this]
    exact Subgroup.one_mem _

theorem mem_Op_of_isPConstrained [Fact p.Prime] {M : Subgroup G}
    (hpc : CFSG.ABGLocalTools.IsPConstrained p ↥M) (P : Sylow p G)
    (hPM : (P : Subgroup G) ≤ M) {z : G} (hzP : z ∈ (P : Subgroup G))
    (hzc : ∀ g ∈ (P : Subgroup G), g * z = z * g) :
    (⟨z, hPM hzP⟩ : ↥M) ∈ CFSG.Op_p'p p ↥M := by
  set R : Subgroup ↥M := CFSG.Op_p'p p ↥M with hR
  set PM : Subgroup ↥M := (P : Subgroup G).subgroupOf M with hPMdef
  have hPMsyl : CFSG.ABGLocalTools.IsSylowOf p PM ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, P.isPGroup'.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    have h1 : (PM).index = (P : Subgroup G).relIndex M := rfl
    rw [h1]
    exact fun h => P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPM))
  have hRn : R.Normal := inferInstance
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p (PM ⊓ R) R :=
    hPMsyl.inf_of_le_normalizer le_top (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hRn).symm)
  have := hpc (PM ⊓ R) hsyl
  refine this ?_
  rw [mem_centralizer_iff]
  intro h hh
  have hhP : (h : G) ∈ (P : Subgroup G) := (Subgroup.mem_inf.mp hh).1
  exact Subtype.ext (hzc h hhP)

theorem false_of_mem_Opp [Fact p.Prime] {H N R O : Subgroup G} (hs : S622IsSimpleSection H N)
    {z : G} (hzH : z ∈ H) (hzN : z ∉ N) (hzp : z ^ p = 1)
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hOn : ∀ h ∈ H, ∀ o ∈ O, h * o * h⁻¹ ∈ O)
    (hO : Nat.Coprime p (Nat.card O)) (hRO : ∀ r ∈ R, ∃ n : ℕ, r ^ (p ^ n) ∈ O)
    (hzR : z ∈ R) : False := by
  classical
  haveI hNn : (N.subgroupOf H).Normal := hs.2.1
  haveI hsimp : IsSimpleGroup (↥H ⧸ N.subgroupOf H) := L613.isSimpleGroup_quotient_of_section hs
  have hnab := L613.not_comm_quotient_of_section hs
  set π : ↥H →* (↥H ⧸ N.subgroupOf H) := QuotientGroup.mk' (N.subgroupOf H) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set z' : ↥H := ⟨z, hzH⟩ with hz'
  have hπz : π z' ≠ 1 := by
    intro h
    exact hzN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hπzp : π z' ^ p = 1 := by
    rw [← map_pow]
    have : z' ^ p = 1 := Subtype.ext (by simpa using hzp)
    rw [this, map_one]
  set U : Subgroup ↥H := (R.subgroupOf H) with hU
  set V : Subgroup ↥H := (O.subgroupOf H) with hV
  have hUn : U.Normal := ⟨fun r hr h => by
    show (h * r * h⁻¹ : ↥H).1 ∈ R
    have hr' : (r : G) ∈ R := hr
    exact hRn h h.2 r hr'⟩
  have hVn : V.Normal := ⟨fun r hr h => by
    show (h * r * h⁻¹ : ↥H).1 ∈ O
    have hr' : (r : G) ∈ O := hr
    exact hOn h h.2 r hr'⟩
  have hAn : (U.map π).Normal := Subgroup.Normal.map hUn π hπsurj
  have hBn : (V.map π).Normal := Subgroup.Normal.map hVn π hπsurj
  have hz'U : z' ∈ U := hzR
  have hAtop : U.map π = ⊤ := by
    haveI := hAn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U.map π) with h | h
    · exfalso
      apply hπz
      have : π z' ∈ U.map π := Subgroup.mem_map_of_mem _ hz'U
      rw [h] at this
      exact this
    · exact h
  haveI := hBn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V.map π) with hB | hB
  ·
    have hpgrp : IsPGroup p (↥H ⧸ N.subgroupOf H) := by
      intro g
      have hg : g ∈ U.map π := by rw [hAtop]; exact Subgroup.mem_top g
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
      have hu' : (u : G) ∈ R := hu
      obtain ⟨n, hn⟩ := hRO _ hu'
      refine ⟨n, ?_⟩
      have hunO : ((u ^ (p ^ n) : ↥H) : G) ∈ O := by simpa using hn
      have hmemV : (u ^ (p ^ n)) ∈ V := hunO
      have : π (u ^ (p ^ n)) ∈ V.map π := Subgroup.mem_map_of_mem _ hmemV
      rw [hB, Subgroup.mem_bot] at this
      rw [← map_pow]
      exact this
    have hnt : Nontrivial (↥H ⧸ N.subgroupOf H) := hsimp.toNontrivial
    have hcen : Nontrivial (Subgroup.center (↥H ⧸ N.subgroupOf H)) := hpgrp.center_nontrivial
    have hcenne : Subgroup.center (↥H ⧸ N.subgroupOf H) ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).mp hcen
    have hctop : Subgroup.center (↥H ⧸ N.subgroupOf H) = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (↥H ⧸ N.subgroupOf H))).resolve_left hcenne
    apply hnab
    intro a b
    have hb : b ∈ Subgroup.center (↥H ⧸ N.subgroupOf H) := hctop ▸ Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hb a
  ·
    have hzV : π z' ∈ V.map π := by rw [hB]; exact Subgroup.mem_top _
    obtain ⟨v, hv, hvz⟩ := Subgroup.mem_map.mp hzV
    have hv' : (v : G) ∈ O := hv
    have h1 : orderOf (π z') ∣ p := orderOf_dvd_of_pow_eq_one hπzp
    have h2 : orderOf (π z') ∣ Nat.card O := by
      rw [← hvz]
      refine (orderOf_map_dvd π v).trans ?_
      have : orderOf (v : G) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hv'
      rwa [Subgroup.orderOf_coe] at this
    have h3 : orderOf (π z') = 1 := Nat.eq_one_of_dvd_coprimes hO h1 h2
    exact hπz (orderOf_eq_one_iff.mp h3)

theorem not_isPConstrained_of_section [Fact p.Prime] {M H N : Subgroup G} (P : Sylow p G)
    (hPM : (P : Subgroup G) ≤ M) {z : G} (hzP : z ∈ (P : Subgroup G))
    (hzc : ∀ g ∈ (P : Subgroup G), g * z = z * g) (hzp : z ^ p = 1) (hHM : H ≤ M)
    (hs : S622IsSimpleSection H N) (hzH : z ∈ H) (hzN : z ∉ N) :
    ¬ CFSG.ABGLocalTools.IsPConstrained p ↥M := by
  intro hpc
  have hz := mem_Op_of_isPConstrained hpc P hPM hzP hzc
  obtain ⟨hRn, hOn, hOc, hRO, -⟩ := op_facts (p := p) M
  refine false_of_mem_Opp hs hzH hzN hzp (R := (CFSG.Op_p'p p ↥M).map M.subtype)
    (O := (CFSG.pPrimeCore p ↥M).map M.subtype) (fun h hh r hr => hRn h (hHM hh) r hr)
    (fun h hh o ho => hOn h (hHM hh) o ho) hOc hRO ?_
  exact Subgroup.mem_map.mpr ⟨_, hz, rfl⟩

end General

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
