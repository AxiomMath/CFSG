module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup

@[expose] def SigmaSixSectionFact : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ], IsInvolvedIn Γ (Equiv.Perm (Fin 6)) → 15 ∣ Nat.card Γ →
    ∃ S : Subgroup Γ, S.Normal ∧ S.index ∣ 2 ∧ IsSimpleGroup S ∧ 2 ∣ Nat.card S ∧
      15 ∣ Nat.card S ∧ ¬ ∀ a b : S, a * b = b * a

theorem simple_le_of_pow_four_mem {Q : Type} [Group Q] [Finite Q] {S L : Subgroup Q}
    [S.Normal] [IsSimpleGroup S] (h3 : 3 ∣ Nat.card S) [L.Normal]
    (hpow : ∀ q : Q, q ^ 4 ∈ L) : S ≤ L := by
  have hT : ((S ⊓ L).subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.mem_inf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact S.mul_mem (S.mul_mem g.2 hn.1) (S.inv_mem g.2)
    · exact (inferInstance : L.Normal).conj_mem _ hn.2 _
  rcases Subgroup.Normal.eq_bot_or_eq_top ((S ⊓ L).subgroupOf S) with hbot | htop
  ·
    exfalso
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have h4 : t ^ 4 = 1 := by
      have hmem : ((t ^ 4 : S) : Q) ∈ S ⊓ L := by
        refine ⟨?_, ?_⟩
        · exact S.pow_mem t.2 4
        · exact hpow _
      have hmem' : (t ^ 4 : S) ∈ (S ⊓ L).subgroupOf S := Subgroup.mem_subgroupOf.mpr hmem
      rw [hbot, Subgroup.mem_bot] at hmem'
      exact hmem'
    have hdvd : orderOf t ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    rw [ht] at hdvd
    norm_num at hdvd
  · intro s hs
    have hmem : (⟨s, hs⟩ : S) ∈ (S ⊓ L).subgroupOf S := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2

theorem isSimpleSection_of_surjective {G : Type} [Group G] {H K : Subgroup G} {Sg : Type}
    [Group Sg] [IsSimpleGroup Sg] (hnab : ¬ ∀ a b : Sg, a * b = b * a) (ρ : H →* Sg)
    (hsurj : Function.Surjective ρ) (hKH : K ≤ H) (hker : ∀ h : H, (h : G) ∈ K ↔ ρ h = 1) :
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622IsSimpleSection H K := by
  refine ⟨hKH, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn1 : ρ n = 1 := (hker n).mp hn
    apply (hker _).mpr
    simp [map_mul, map_inv, hn1]
  ·
    intro hKeq
    obtain ⟨s, hs⟩ := exists_ne (1 : Sg)
    obtain ⟨h, hh⟩ := hsurj s
    have hmem : (h : G) ∈ K := by
      rw [hKeq]
      exact h.2
    have := (hker h).mp hmem
    rw [hh] at this
    exact hs this
  ·
    intro N' hKN' hN'H hN'n
    have hN'n' : (N'.subgroupOf H).Normal := hN'n
    have hY : ((N'.subgroupOf H).map ρ).Normal := Subgroup.Normal.map hN'n' ρ hsurj
    rcases Subgroup.Normal.eq_bot_or_eq_top ((N'.subgroupOf H).map ρ) with hbot | htop
    · left
      apply le_antisymm
      · intro g hg
        have hgH : g ∈ H := hN'H hg
        have hmem : ρ ⟨g, hgH⟩ ∈ (N'.subgroupOf H).map ρ :=
          Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact (hker ⟨g, hgH⟩).mpr hmem
      · exact hKN'
    · right
      apply le_antisymm hN'H
      intro h hh
      have hmem : ρ ⟨h, hh⟩ ∈ (N'.subgroupOf H).map ρ := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnρ⟩ := Subgroup.mem_map.mp hmem
      have hnN : (n : G) ∈ N' := Subgroup.mem_subgroupOf.mp hn
      have hk : ((n⁻¹ * ⟨h, hh⟩ : H) : G) ∈ K := by
        apply (hker _).mpr
        simp only [map_mul, map_inv, hnρ]
        exact inv_mul_cancel _
      have hk' : ((n⁻¹ * ⟨h, hh⟩ : H) : G) ∈ N' := hKN' hk
      have heq : h = (n : G) * ((n⁻¹ * ⟨h, hh⟩ : H) : G) := by
        simp
      rw [heq]
      exact N'.mul_mem hnN hk'
  ·
    intro hall
    apply hnab
    intro s t
    obtain ⟨a, ha⟩ := hsurj s
    obtain ⟨b, hb⟩ := hsurj t
    have hc : ((a * b * a⁻¹ * b⁻¹ : H) : G) ∈ K := hall a a.2 b b.2
    have h1 : ρ (a * b * a⁻¹ * b⁻¹) = 1 := (hker _).mp hc
    simp only [map_mul, map_inv, ha, hb] at h1
    calc s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
      _ = t * s := by rw [h1, one_mul]

theorem relIndex_eq_card_of_surjective {G : Type} [Group G] {H K : Subgroup G} {Sg : Type}
    [Group Sg] [Finite Sg] (ρ : H →* Sg) (hsurj : Function.Surjective ρ) (hKH : K ≤ H)
    (hker : ∀ h : H, (h : G) ∈ K ↔ ρ h = 1) : K.relIndex H = Nat.card Sg := by
  have hkerEq : K.subgroupOf H = ρ.ker := by
    ext h
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact hker h
  show (K.subgroupOf H).index = Nat.card Sg
  rw [hkerEq, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]

theorem sectionOfPowerCover {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] [Finite Q]
    (N : Subgroup G) (Φ : N →* Q) (hΦ : Function.Surjective Φ) (X1 : Subgroup G)
    (hX1N : X1 ≤ N) (S : Subgroup Q) [S.Normal] [IsSimpleGroup S]
    (hnab : ¬ ∀ a b : S, a * b = b * a) (h3 : 3 ∣ Nat.card S)
    (hLn : ((X1.subgroupOf N).map Φ).Normal)
    (hpow : ∀ q : Q, q ^ 4 ∈ (X1.subgroupOf N).map Φ) :
    ∃ H K : Subgroup G, H ≤ X1 ∧
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622IsSimpleSection H K ∧
        K.relIndex H = Nat.card S := by
  classical
  haveI := hLn
  have hSL : S ≤ (X1.subgroupOf N).map Φ := simple_le_of_pow_four_mem h3 hpow
  set TH : Subgroup N := S.comap Φ ⊓ X1.subgroupOf N with hTH
  set TK : Subgroup N := (⊥ : Subgroup Q).comap Φ ⊓ X1.subgroupOf N with hTK
  set H : Subgroup G := TH.map N.subtype with hH
  set K : Subgroup G := TK.map N.subtype with hK
  have hHN : H ≤ N := Subgroup.map_subtype_le _
  have hHX1 : H ≤ X1 := by
    intro h hh
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hh
    exact (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp ht).2)
  have hTKH : TK ≤ TH := by
    intro t ht
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp ht
    refine Subgroup.mem_inf.mpr ⟨?_, h2⟩
    rw [Subgroup.mem_comap] at h1 ⊢
    rw [Subgroup.mem_bot] at h1
    rw [h1]
    exact S.one_mem
  have hKH : K ≤ H := Subgroup.map_mono hTKH
  have hρS : ∀ h : H, Φ (Subgroup.inclusion hHN h) ∈ S := by
    intro h
    obtain ⟨t, ht, hth⟩ := Subgroup.mem_map.mp h.2
    have hit : Subgroup.inclusion hHN h = t := by
      apply Subtype.ext
      exact hth.symm
    rw [hit]
    exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp ht).1
  let ρ : H →* S := (Φ.comp (Subgroup.inclusion hHN)).codRestrict S hρS
  have hsurj : Function.Surjective ρ := by
    intro s
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp (hSL s.2)
    have htS : t ∈ TH :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [hts]; exact s.2), ht⟩
    refine ⟨⟨N.subtype t, Subgroup.mem_map.mpr ⟨t, htS, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show Φ t = (s : Q)
    exact hts
  have hker : ∀ h : H, (h : G) ∈ K ↔ ρ h = 1 := by
    intro h
    constructor
    · intro hh
      obtain ⟨t, ht, hth⟩ := Subgroup.mem_map.mp hh
      have hΦt : Φ t = 1 := by
        have h1 := (Subgroup.mem_inf.mp ht).1
        rw [Subgroup.mem_comap, Subgroup.mem_bot] at h1
        exact h1
      apply Subtype.ext
      show Φ (Subgroup.inclusion hHN h) = 1
      have hit : Subgroup.inclusion hHN h = t := by
        apply Subtype.ext
        exact hth.symm
      rw [hit]
      exact hΦt
    · intro hρ1
      have hΦ1 : Φ (Subgroup.inclusion hHN h) = 1 := congrArg Subtype.val hρ1
      refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion hHN h, ?_, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_comap, Subgroup.mem_bot]
        exact hΦ1
      · exact Subgroup.mem_subgroupOf.mpr (hHX1 h.2)
  refine ⟨H, K, hHX1, isSimpleSection_of_surjective hnab ρ hsurj hKH hker, ?_⟩
  exact relIndex_eq_card_of_surjective ρ hsurj hKH hker

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
