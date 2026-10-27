module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitMono1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem lit_le_oddCore_of_normal_normal {M L : Subgroup G} [M.Normal] (hLM : L ≤ M)
    (hL : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hodd : Odd (Nat.card L)) :
    L ≤ CFSG.oddCore G := by
  haveI hnorm : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hLM).mpr fun h k hh hk => hL k hk h hh
  have hcard : Nat.card (L.subgroupOf M) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  have hle : L.subgroupOf M ≤ CFSG.oddCore ↥M :=
    lit_le_oddCore ↥M hnorm (hcard.symm ▸ hodd)
  have hmap : (L.subgroupOf M).map M.subtype ≤ (CFSG.oddCore ↥M).map M.subtype :=
    Subgroup.map_mono hle
  rw [Subgroup.map_subgroupOf_eq_of_le hLM] at hmap
  have hnormint := CFSG.ComponentClassification.OddCore.normal_intersection G M
  rw [← lit_oddCore_eq ↥M, ← lit_oddCore_eq G] at hnormint
  rw [hnormint] at hmap
  exact hmap.trans inf_le_right

variable {A : Subgroup G} {φ : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 6)}

private theorem lit_A_ne_bot (h : LitBar A φ) : A ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card A = 1 := by rw [hbot, Subgroup.card_bot]
  rw [h.card] at hcard
  norm_num at hcard

private theorem lit_step_A (h : LitBar A φ) {M : Subgroup G} (hM : LitMinNormal M)
    {L : Subgroup G} (hLM : L ≤ M) (hL : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hLne : L ≠ ⊥) : A ≤ L := by
  haveI : M.Normal := hM.1
  have hAM : A ≤ M := lit_mono_le h hM
  have hEven : Even (Nat.card L) := by
    by_contra hnot
    have hodd : Odd (Nat.card L) := Nat.not_even_iff_odd.mp hnot
    have hLodd : L ≤ CFSG.oddCore G := lit_le_oddCore_of_normal_normal hLM hL hodd
    have hMinf : M ⊓ CFSG.oddCore G = ⊥ := by
      rcases hM.2.2 (M ⊓ CFSG.oddCore G) inferInstance inf_le_left with hbot | htop
      · exact hbot
      · exfalso
        have hMle : M ≤ CFSG.oddCore G := by rw [← htop]; exact inf_le_right
        have h16 : 16 ∣ Nat.card M := by
          rw [← h.card]; exact Subgroup.card_dvd_of_le hAM
        have hoddM : Odd (Nat.card M) :=
          (lit_odd_card_oddCore G).of_dvd_nat (Subgroup.card_dvd_of_le hMle)
        have hevenM : Even (Nat.card M) :=
          even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 16).trans h16)
        exact (Nat.not_even_iff_odd.mpr hoddM) hevenM
    have hLbot : L ≤ ⊥ := by
      rw [← hMinf]
      exact le_inf hLM hLodd
    exact hLne (le_bot_iff.mp hLbot)
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [h.card]; norm_num)
  obtain ⟨T, hAT⟩ := IsPGroup.exists_le_sylow hA2
  let U : Subgroup G := M ⊓ (T : Subgroup G)
  have hUsylow := lit_inf_normal_sylow T M
  have hU2 : IsPGroup 2 U := hUsylow.1
  have hUidx : ¬ 2 ∣ U.relIndex M := hUsylow.2
  have hUM : U ≤ M := inf_le_left
  have hAUM : A ≤ U := le_inf hAM hAT
  have hULne : U ⊓ L ≠ ⊥ :=
    lit_inf_ne_bot_of_sylow hUM hU2 hUidx hLM hL hEven
  have hNnorm : ∀ t ∈ U, ∀ n ∈ U ⊓ L, t * n * t⁻¹ ∈ U ⊓ L := by
    intro t ht n hn
    exact ⟨U.mul_mem (U.mul_mem ht hn.1) (U.inv_mem ht), hL t (hUM ht) n hn.2⟩
  obtain ⟨z, hzN, hz1, hzcent⟩ :=
    lit_normal_inf_center (T := U) (N := U ⊓ L) hU2 inf_le_left hNnorm hULne
  have hzU : z ∈ U := hzN.1
  have hzL : z ∈ L := hzN.2
  have hzC : z ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hzcent a (hAUM ha)).symm
  have hz2 : ∃ k : ℕ, z ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hU2 ⟨z, hzU⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hzA : z ∈ A := h.two_mem z hzC hz2
  have hWne : A ⊓ L ≠ ⊥ := by
    intro hbot
    have hzbot : z ∈ (⊥ : Subgroup G) := hbot ▸ (show z ∈ A ⊓ L from ⟨hzA, hzL⟩)
    exact hz1 (Subgroup.mem_bot.mp hzbot)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard_alt : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num
  obtain ⟨σ, hσ⟩ :=
    exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 6)) 5 (by rw [hcard_alt]; norm_num)
  obtain ⟨g, hgM, hφg⟩ := lit_mono_five h hM σ σ.2
  have hgN : (g : G) ∈ normalizer (A : Set G) := g.2
  have hn : ∀ x, x ∈ A ↔ (g : G) * x * (g : G)⁻¹ ∈ A :=
    Subgroup.mem_normalizer_iff.mp hgN
  have hg5φ : φ (g ^ 5) = 1 := by
    rw [map_pow, hφg]
    have hσ5 : σ ^ 5 = 1 := hσ ▸ pow_orderOf_eq_one σ
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hσ5
  have h5 : ∀ a ∈ A, (g : G) ^ 5 * a * ((g : G) ^ 5)⁻¹ = a := by
    intro a ha
    have h1 := (h.ker (g ^ 5)).mp hg5φ a ha
    simp only [Subgroup.coe_pow] at h1
    rw [h1]
    group
  have hg1 : φ g ≠ 1 := by
    intro h1
    have hσ1 : σ = 1 := Subtype.ext (by simpa using (hφg.symm.trans h1))
    rw [hσ1, orderOf_one] at hσ
    omega
  have hnt : ¬ ∀ a ∈ A, (g : G) * a * (g : G)⁻¹ = a := by
    intro hcon
    apply hg1
    rw [h.ker g]
    intro a ha
    have hh := hcon a ha
    calc (g : G) * a = (g : G) * a * (g : G)⁻¹ * (g : G) := by group
      _ = a * (g : G) := by rw [hh]
  have hgL : ∀ x, x ∈ L ↔ (g : G) * x * (g : G)⁻¹ ∈ L := by
    intro x
    constructor
    · intro hx
      exact hL (g : G) hgM x hx
    · intro hx
      have hx' := hL (g : G)⁻¹ (M.inv_mem hgM) ((g : G) * x * (g : G)⁻¹) hx
      convert hx' using 1
      group
  have hW : ∀ x, x ∈ A ⊓ L ↔ (g : G) * x * (g : G)⁻¹ ∈ A ⊓ L := by
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hn x, hgL x]
  rcases lit_irreducible_of_five h.card hn h5 hnt inf_le_left hW with hbot | htop
  · exact absurd hbot hWne
  · rw [← htop]
    exact inf_le_right

theorem lit_mono_simple (h : LitBar A φ) {M : Subgroup G} (hM : LitMinNormal M) :
    IsSimpleGroup ↥M := by
  haveI : M.Normal := hM.1
  have hAM : A ≤ M := lit_mono_le h hM
  have hAne : A ≠ ⊥ := lit_A_ne_bot h
  rw [Subgroup.isSimpleGroup_iff]
  refine ⟨?_, ?_⟩
  · intro hbot
    exact hAne (le_bot_iff.mp (hbot ▸ hAM))
  · intro H' hH'M hH'norm
    by_cases hH' : H' = ⊥
    · exact Or.inl hH'
    · right
      have hH'conj : ∀ h k, h ∈ H' → k ∈ M → k * h * k⁻¹ ∈ H' :=
        (Subgroup.normal_subgroupOf_iff hH'M).mp hH'norm
      have hAleCore : A ≤ H'.normalCore := by
        rw [Subgroup.normalCore_eq_iInf_map_conj]
        refine le_iInf fun x => lit_step_A h hM ?_ ?_ ?_
        · exact (Subgroup.map_mono hH'M).trans (le_of_eq (Subgroup.Normal.map_conj_eq M x))
        · intro m hm l hl
          obtain ⟨c, hcH', rfl⟩ := Subgroup.mem_map.mp hl
          have hm' : x⁻¹ * m * x ∈ M := by simpa using hM.1.conj_mem m hm x⁻¹
          refine Subgroup.mem_map.mpr
            ⟨(x⁻¹ * m * x) * c * (x⁻¹ * m * x)⁻¹,
              hH'conj c (x⁻¹ * m * x) hcH' hm', ?_⟩
          change x * ((x⁻¹ * m * x) * c * (x⁻¹ * m * x)⁻¹) * x⁻¹
            = m * (x * c * x⁻¹) * m⁻¹
          have hmx : m * x = x * (x⁻¹ * m * x) := by group
          calc x * ((x⁻¹ * m * x) * c * (x⁻¹ * m * x)⁻¹) * x⁻¹
              = (x * (x⁻¹ * m * x)) * c * (x * (x⁻¹ * m * x))⁻¹ := by group
            _ = (m * x) * c * (m * x)⁻¹ := by rw [hmx]
            _ = m * (x * c * x⁻¹) * m⁻¹ := by group
        · intro hbot
          rw [Subgroup.map_eq_bot_iff_of_injective H' (MulAut.conj x).injective] at hbot
          exact hH' hbot
      have hCoreNe : H'.normalCore ≠ ⊥ := by
        intro hbot
        exact hAne (le_bot_iff.mp (hbot ▸ hAleCore))
      have hCoreLeM : H'.normalCore ≤ M := (Subgroup.normalCore_le H').trans hH'M
      rcases hM.2.2 H'.normalCore inferInstance hCoreLeM with hcore | hcore
      · exact absurd hcore hCoreNe
      · exact le_antisymm hH'M (hcore ▸ Subgroup.normalCore_le H')

theorem lit_mono_unique (h : LitBar A φ) {M : Subgroup G} (hM : LitMinNormal M)
    {K : Subgroup G} [K.Normal] (hK : K ≠ ⊥) : M ≤ K := by
  obtain ⟨M₀, hM₀, hM₀K⟩ := lit_exists_minNormal_le (K := K) hK
  haveI : M.Normal := hM.1
  haveI : M₀.Normal := hM₀.1
  have hAM : A ≤ M := lit_mono_le h hM
  have hAM₀ : A ≤ M₀ := lit_mono_le h hM₀
  have hAne : A ≠ ⊥ := lit_A_ne_bot h
  have hMM₀ne : M ⊓ M₀ ≠ ⊥ := by
    intro hbot
    exact hAne (le_bot_iff.mp (hbot ▸ le_inf hAM hAM₀))
  rcases hM₀.2.2 (M ⊓ M₀) inferInstance inf_le_right with h | h
  · exact absurd h hMM₀ne
  · have hM₀M : M₀ ≤ M := by rw [← h]; exact inf_le_left
    rcases hM.2.2 M₀ inferInstance hM₀M with h' | h'
    · exact absurd h' hM₀.2.1
    · rw [← h']; exact hM₀K

theorem lit_mono_centralizer (h : LitBar A φ) {M : Subgroup G} (hM : LitMinNormal M) :
    centralizer (M : Set G) = ⊥ := by
  haveI : M.Normal := hM.1
  haveI : (centralizer (M : Set G)).Normal := inferInstance
  by_contra hne
  have hMleC : M ≤ centralizer (M : Set G) := lit_mono_unique h hM hne
  haveI : IsMulCommutative ↥M := IsMulCommutative.of_comm fun a b => by
    have ha : (a : G) ∈ centralizer (M : Set G) := hMleC a.2
    have hh := (Subgroup.mem_centralizer_iff.mp ha) (b : G) b.2
    exact Subtype.ext hh.symm
  have hprime : (Nat.card M).Prime :=
    (Group.is_simple_iff_prime_card (α := ↥M)).mp (lit_mono_simple h hM)
  have h16 : 16 ∣ Nat.card M := by
    rw [← h.card]
    exact Subgroup.card_dvd_of_le (lit_mono_le h hM)
  rcases hprime.eq_one_or_self_of_dvd 16 h16 with h1 | hp
  · norm_num at h1
  · exfalso
    rw [← hp] at hprime
    norm_num at hprime

theorem lit_mono (h : LitBar A φ) :
    ∃ M : Subgroup G, M.Normal ∧ IsSimpleGroup ↥M ∧ A ≤ M ∧ centralizer (M : Set G) = ⊥ ∧
      (∀ K : Subgroup G, K.Normal → K ≠ ⊥ → M ≤ K) ∧
      ∀ σ ∈ alternatingGroup (Fin 6), ∃ g : ↥(normalizer (A : Set G)), (g : G) ∈ M ∧ φ g = σ := by
  have hAne : A ≠ ⊥ := lit_A_ne_bot h
  have htop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro hbot
    exact hAne (le_bot_iff.mp (hbot ▸ le_top))
  obtain ⟨M, hM, _⟩ := lit_exists_minNormal_le (K := ⊤) htop
  refine ⟨M, hM.1, lit_mono_simple h hM, lit_mono_le h hM, lit_mono_centralizer h hM, ?_,
    lit_mono_five h hM⟩
  intro K hK hKne
  letI : K.Normal := hK
  exact lit_mono_unique h hM hKne

end CFSG.OddStandard.HigherRank.YamadaG23
