module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.Quasithin.Background.A3Structure38Part3

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.Quasithin.A38

theorem false_of_extra_of_rank {G : Type} [Group G] [Finite G]
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup G) ≤ 2)
    {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G)) (hO2 : CFSG.pCore 2 ↥L = ⊥) {t : G}
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hgf : CFSG.generalizedFitting ↥L = CFSG.fittingSubgroup ↥L) (hextra : A36Extra ↥L) :
    False := by
  have hnt : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr (ne_bot_of_mem_cComp hL)
  have hFne := fitting_ne_bot_of_gf_eq hgf
  obtain ⟨q, hq, hqF⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥(CFSG.fittingSubgroup ↥L))
    (fun h => hFne (Subgroup.card_eq_one.mp h))
  obtain ⟨P, hsup, -, hcases, hker⟩ := hextra q hq hqF
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h1 : Nat.card ↥(CFSG.pCore 2 ↥L) = 1 := by
      rw [hO2]
      exact Subgroup.card_bot
    have h2 : Nat.card ↥P ≤ 1 := h1 ▸ Subgroup.card_le_card_group P
    rcases hcases with hE | ⟨-, hcard, -⟩
    · have h3 := card_eq_of_isElemAbelianOfRank Nat.prime_two hE
      rw [h3] at h2
      norm_num at h2
    · rw [hcard] at h2
      norm_num at h2
  have hFact : Fact q.Prime := ⟨hq⟩
  let ι : ↥(CFSG.pCore q ↥L) →* ↥L := (CFSG.pCore q ↥L).subtype
  have hexp : ∀ x ∈ P, x ^ q = 1 := hsup.pow_eq_one
  have hnc : ∃ x ∈ P, x ∉ (Subgroup.center ↥L).comap ι := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ y : ↥L, y ∈ CFSG.fittingSubgroup ↥L := by
      intro y
      refine (hker y).mp ?_
      rintro _ ⟨d₀, hd₀, rfl⟩
      have hc : ∀ g : ↥L, g * ι d₀ = ι d₀ * g := Subgroup.mem_center_iff.mp (hcon d₀ hd₀)
      have h1 : (ι d₀)⁻¹ * (y * ι d₀ * y⁻¹) = 1 := by
        rw [hc y]
        group
      show (ι d₀)⁻¹ * (y * ι d₀ * y⁻¹) ∈ _
      rw [h1]
      exact Subgroup.one_mem _
    have hFtop : CFSG.fittingSubgroup ↥L = ⊤ := eq_top_iff.mpr fun y _ => hall y
    have hnil : Group.IsNilpotent ↥(CFSG.fittingSubgroup ↥L) := inferInstance
    rw [hFtop] at hnil
    have hnil' : Group.IsNilpotent ↥L := Group.nilpotent_of_mulEquiv (Subgroup.topEquiv : _ ≃* ↥L)
    exact not_isSolvable_of_mem_cComp hL inferInstance
  obtain ⟨a, haP, b, hbP, haN, hab, hind⟩ :=
    exists_pair (X := ↥(CFSG.pCore q ↥L)) hq ((Subgroup.center ↥L).comap ι) hexp hnc hcases
  have hlq : ∀ r : ↥(CFSG.pCore q ↥L), r ∈ P → ((ι r : ↥L) : G) ^ q = 1 := by
    intro r hr
    have h1 : (ι r) ^ q = 1 := by rw [← map_pow, hexp r hr, map_one]
    simpa using congrArg Subtype.val h1
  have hcomm' : Commute ((ι a : ↥L) : G) ((ι b : ↥L) : G) := by
    have h1 : ((ι a : ↥L) : G) * ((ι b : ↥L) : G) = ((ι b : ↥L) : G) * ((ι a : ↥L) : G) := by
      have := congrArg (fun r => ((ι r : ↥L) : G)) hab
      simpa [map_mul] using this
    exact h1
  have hnc' : ∃ l ∈ L, ((ι a : ↥L) : G) * l ≠ l * ((ι a : ↥L) : G) := by
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff] at haN
    push Not at haN
    obtain ⟨g, hg⟩ := haN
    exact ⟨(g : G), g.2, fun h => hg (Subtype.ext h.symm)⟩
  have hind' : ∀ n : ℕ, ((ι a : ↥L) : G) ^ n ≠ ((ι b : ↥L) : G) := by
    intro n hn
    apply hind n
    have h1 : (ι a) ^ n = ι b := Subtype.ext (by simpa using hn)
    have h2 : ι (a ^ n) = ι b := by rw [map_pow]; exact h1
    exact (CFSG.pCore q ↥L).subtype_injective h2
  have h3 := three_le_pRank_conj (q := q) (L := L) (t := t) hcomm (a := ((ι a : ↥L) : G))
    (b := ((ι b : ↥L) : G)) (ι a).2 (ι b).2 (hlq a haP) (hlq b hbP) hcomm' hnc' hind'
  have h4 := hrank q hq hq2
  omega

theorem isQuasisimple_of_commuting_conj_of_rank {G : Type} [Group G] [Finite G]
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup G) ≤ 2)
    {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G)) (hO2 : CFSG.pCore 2 ↥L = ⊥)
    (hcases : CFSG.IsComponent L ∨ A36Case3 ↥L ∨ A36Case4 ↥L)
    (hextra : (A36Case3 ↥L ∨ A36Case4 ↥L) → A36Extra ↥L) {t : G}
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥) : CFSG.IsQuasisimple ↥L := by
  rcases hcases with hc | h3 | h4
  · exact hc.1
  · have hgf : CFSG.generalizedFitting ↥L = CFSG.fittingSubgroup ↥L := by
      obtain ⟨p, -, -, hgf, -⟩ := h3
      exact hgf
    exact (false_of_extra_of_rank hrank hL hO2 hcomm hgf (hextra (Or.inl h3))).elim
  · exact (false_of_extra_of_rank hrank hL hO2 hcomm h4.1 (hextra (Or.inr h4))).elim

theorem false_of_pSquared_of_rank {G : Type} [Group G] [Finite G]
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup G) ≤ 2)
    {L : Subgroup G} {t : G}
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥) (hZ : Subgroup.center ↥L = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hrk : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L)) :
    False := by
  have hFact : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp.one_lt (⊤ : Subgroup ↥L)
  have hE2 : p ^ 2 ≤ Nat.card ↥E := by
    rw [hcard]
    exact Nat.pow_le_pow_right hp.pos hrk
  have hp1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : E = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    rw [this, Subgroup.card_bot] at hE2
    omega
  have hzp : Nat.card ↥(Subgroup.zpowers a) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hE.2 a haE))
  obtain ⟨b, hbE, hb⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers a := fun y hy => hcon y hy
    have h1 : Nat.card ↥E ≤ Nat.card ↥(Subgroup.zpowers a) := Subgroup.card_le_of_le hle
    nlinarith [hp.two_le]
  have hab : a * b = b * a := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩)
  have hnc : ∃ l ∈ L, ((a : ↥L) : G) * l ≠ l * ((a : ↥L) : G) := by
    have hnot : a ∉ Subgroup.center ↥L := by
      rw [hZ]
      exact fun h => ha1 (Subgroup.mem_bot.mp h)
    rw [Subgroup.mem_center_iff] at hnot
    push Not at hnot
    obtain ⟨g, hg⟩ := hnot
    exact ⟨(g : G), g.2, fun h => hg (Subtype.ext h.symm)⟩
  have h3 := three_le_pRank_conj (q := p) (L := L) (t := t) hcomm (a := ((a : ↥L) : G))
    (b := ((b : ↥L) : G)) a.2 b.2 (by simpa using congrArg Subtype.val (hE.2 a haE))
    (by simpa using congrArg Subtype.val (hE.2 b hbE))
    (by
      have h1 : ((a : ↥L) : G) * ((b : ↥L) : G) = ((b : ↥L) : G) * ((a : ↥L) : G) := by
        simpa using congrArg Subtype.val hab
      exact h1)
    hnc
    (fun n hn => hb (by
      have h1 : a ^ n = b := Subtype.ext (by simpa using hn)
      exact h1 ▸ Subgroup.npow_mem_zpowers a n))
  have h4 := hrank p hp hp2
  omega

theorem isQuasithin_of_rank {G : Type} [Group G] [Finite G]
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup G) ≤ 2) :
    IsQuasithin G := by
  unfold IsQuasithin evenRank
  refine csSup_le' ?_
  rintro k ⟨p, H, hp, hp2, -, rfl⟩
  exact (pRank_mono hp.one_lt (le_top : H ≤ ⊤)).trans (hrank p hp hp2)

theorem part12_strong_of_a134 (hmult2 : Mult2Fact) {H : Type} [Group H] [Finite H]
    (ha134 : A134For H) {K : Subgroup H} (hKc : CFSG.IsComponent K) (hO2 : CFSG.pCore 2 ↥K = ⊥)
    (hnorm : ¬ K.Normal) :
    ∃ t : H, t ∉ Subgroup.normalizer (K : Set H) ∧
      (∀ g : H, K.map (MulAut.conj g).toMonoidHom = K ∨
        K.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) ∧
      ((Subgroup.center ↥K = ⊥ ∧ A134Types ↥K) ∨
        (IsSU3 8 ↥K ∧ 3 ≤ CFSG.Open.pRank 3 (K ⊔ K.map (MulAut.conj t).toMonoidHom))) := by
  obtain ⟨t, ht⟩ := exists_not_mem_normalizer hnorm
  have hK'c : CFSG.IsComponent (K.map (MulAut.conj t).toMonoidHom) := isComponent_conj hKc
  have hne : K ≠ K.map (MulAut.conj t).toMonoidHom := fun h => ht (map_conj_eq_iff.mp h.symm)
  obtain ⟨h2, h3⟩ := ha134 K (K.map (MulAut.conj t).toMonoidHom) hKc hK'c hne ⟨conjEquiv t K⟩
  refine ⟨t, ht, fun g => ?_, ?_⟩
  · exact h2 _ (isComponent_conj hKc) ⟨(conjEquiv g K).symm⟩
  · rcases h3 with h3 | ⟨h3, h3r⟩
    · left
      have hcenter : IsPGroup 2 (Subgroup.center ↥K) := hmult2 ↥K hKc.1 h3
      have hle : Subgroup.center ↥K ≤ CFSG.pCore 2 ↥K :=
        le_sSup ⟨inferInstance, hcenter⟩
      have hbot : Subgroup.center ↥K = ⊥ := le_bot_iff.mp (hO2 ▸ hle)
      refine ⟨hbot, ?_⟩
      exact A134Types.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm h3
    · exact Or.inr ⟨h3, h3r.ge⟩

theorem nonnormal_package_of_a134 (hmult2 : Mult2Fact) {G : Type} [Group G] [Finite G]
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup G) ≤ 2)
    (ha134 : A134For G) (h37 : A37Statement G) {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) (hO2 : CFSG.pCore 2 ↥L = ⊥)
    (hcases : CFSG.IsComponent L ∨ A36Case3 ↥L ∨ A36Case4 ↥L)
    (hextra : (A36Case3 ↥L ∨ A36Case4 ↥L) → A36Extra ↥L) (hnorm : ¬ L.Normal) :
    ∃ t : G, t ∉ Subgroup.normalizer (L : Set G) ∧
      (∀ g : G, L.map (MulAut.conj g).toMonoidHom = L ∨
        L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom) ∧
      ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
      L ⊓ L.map (MulAut.conj t).toMonoidHom = ⊥ ∧ A38Types ↥L := by
  obtain ⟨t₀, ht₀⟩ := exists_not_mem_normalizer hnorm
  have hcomm₀ : ⁅L, L.map (MulAut.conj t₀).toMonoidHom⁆ = ⊥ :=
    h37 L hL _ (cComp_conj hL) (fun h => ht₀ (map_conj_eq_iff.mp h.symm))
  have hqs := isQuasisimple_of_commuting_conj_of_rank hrank hL hO2 hcases hextra hcomm₀
  have hcomp : CFSG.IsComponent L := ⟨hqs, A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hL)⟩
  obtain ⟨t, ht, hconj, hlist⟩ := part12_strong_of_a134 hmult2 ha134 hcomp hO2 hnorm
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ cComp (⊤ : Subgroup G) := cComp_conj hL
  have hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ :=
    h37 L hL _ hLt (fun h => ht (map_conj_eq_iff.mp h.symm))
  rcases hlist with ⟨hZ, htypes⟩ | ⟨-, h3⟩
  · refine ⟨t, ht, hconj, hcomm, ?_, ?_⟩
    · refine eq_bot_iff.mpr fun x hx => ?_
      have hxZ : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        show (g : G) * x = x * (g : G)
        exact (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm g.2) x hx.2).symm
      rw [hZ] at hxZ
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hxZ))
    · rcases htypes with ⟨n, h⟩ | ⟨n, h⟩ | h | ⟨p, e, hp, hp3, he1, he2, h⟩
      · exact Or.inl ⟨n, h⟩
      · exact Or.inr (Or.inl ⟨n, h⟩)
      · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inr ⟨p, hp, hp3, ?_⟩))
        rcases (by omega : e = 1 ∨ e = 2) with rfl | rfl
        · exact h
        · exfalso
          have hr := (classical_model_rank (G := ↥L) (t := .PSL) (n := 2) (p := p) (f := 2)
            (by omega) h).2.2
          have hrank' : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
            rcases hr with ⟨-, h1 | h1 | h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | h1
            · exact h1.2
            · exact absurd h1.1 (by norm_num)
            · omega
            · cases h1
            · cases h1
            · omega
          exact false_of_pSquared_of_rank hrank hcomm hZ hp (by omega) hrank'
  · exfalso
    have := (pRank_mono Nat.prime_three.one_lt
      (le_top : L ⊔ L.map (MulAut.conj t).toMonoidHom ≤ ⊤)).trans
      (hrank 3 Nat.prime_three (by norm_num))
    omega

theorem a38_part3_of_package {G : Type} [Group G] [Finite G] (h37 : A37Statement G)
    (hpkg : ∀ L ∈ cComp (⊤ : Subgroup G), ¬ L.Normal →
      ∃ t : G, t ∉ Subgroup.normalizer (L : Set G) ∧
        (∀ g : G, L.map (MulAut.conj g).toMonoidHom = L ∨
          L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom) ∧
        ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
        L ⊓ L.map (MulAut.conj t).toMonoidHom = ⊥ ∧ A38Types ↥L) :
    A38Part3 G := by
  intro L hL
  have hone : ∀ K : Subgroup G, K.map (MulAut.conj (1 : G)).toMonoidHom = K := fun K =>
    map_conj_eq_iff.mpr (Subgroup.one_mem _)
  by_cases hnorm : L.Normal
  · have hnmem : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) := fun g => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
      exact Subgroup.mem_top g
    refine ⟨Or.inl hnorm, fun T hT => Or.inl ⟨hnorm, ?_, ?_⟩⟩
    · ext K'
      constructor
      · rintro ⟨s, -, hs⟩
        exact hs.trans (map_conj_eq_iff.mpr (hnmem s))
      · intro h
        exact ⟨1, T.one_mem, h.trans (hone L).symm⟩
    · refine Set.eq_singleton_iff_unique_mem.mpr ⟨cComp_mem_of_le hL le_sup_left le_top,
        fun K hK => ?_⟩
      have hTs : Group.IsSolvable ↥T := by
        have : Group.IsNilpotent ↥T := hT.2.1.isNilpotent
        infer_instance
      have hpc : perfectCore (L ⊔ T) ≤ L :=
        perfectCore_le_of_sup_solvable le_sup_left Subgroup.normal_subgroupOf rfl hTs
      have hKL : K ≤ L :=
        (le_perfectCore_of_perfect (le_of_mem_cComp hK) (perfect_of_mem_cComp hK)).trans hpc
      have hKL' : K ∈ cComp L := cComp_mem_of_le hK hKL le_sup_left
      rw [cComp_self_eq_singleton hL] at hKL'
      exact hKL'
  · obtain ⟨t₀, ht₀, hconj, hcomm, hinf, htypes⟩ := hpkg L hL hnorm
    refine ⟨Or.inr ⟨htypes, t₀, ht₀, hcomm, hinf, conjClosure_eq_sup hconj⟩, fun T hT => Or.inr ?_⟩
    have hexists : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
      by_contra hcon
      push Not at hcon
      have hTN : T ≤ Subgroup.normalizer (L : Set G) := fun t ht => hcon t ht
      have h2 : (Subgroup.normalizer (L : Set G)).index = 2 := index_normalizer_eq_two hconj ht₀
      have h3 := Subgroup.index_dvd_of_le hTN
      have h4 : ¬ 2 ∣ T.index := by
        have := hT.2.2
        change ¬ 2 ∣ T.relIndex ⊤ at this
        rwa [Subgroup.relIndex_top_right] at this
      rw [h2] at h3
      exact h4 h3
    obtain ⟨t, htT, htn⟩ := hexists
    have hLt : L.map (MulAut.conj t).toMonoidHom = L.map (MulAut.conj t₀).toMonoidHom :=
      (hconj t).resolve_left fun h => htn (map_conj_eq_iff.mp h)
    have hXnorm : (L ⊔ L.map (MulAut.conj t₀).toMonoidHom).Normal := by
      rw [← conjClosure_eq_sup hconj]
      exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (le_normalizer_conjClosure L ⊤))
    have hLtT : L.map (MulAut.conj t).toMonoidHom ≤ L ⊔ T := by
      rintro _ ⟨y, hy, rfl⟩
      have : t * y * t⁻¹ ∈ L ⊔ T :=
        (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right htT) (Subgroup.mem_sup_left hy))
          ((L ⊔ T).inv_mem (Subgroup.mem_sup_right htT))
      simpa [MulAut.conj_apply] using this
    have hXT : L ⊔ T = (L ⊔ L.map (MulAut.conj t₀).toMonoidHom) ⊔ T := by
      refine le_antisymm (sup_le_sup_right le_sup_left T) (sup_le (sup_le le_sup_left ?_)
        le_sup_right)
      rw [← hLt]
      exact hLtT
    refine ⟨t, htT, htn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      ext K'
      constructor
      · rintro ⟨s, -, hs⟩
        rw [hs, hLt]
        exact hconj s
      · intro h
        rcases h with h | h
        · exact ⟨1, T.one_mem, h.trans (hone L).symm⟩
        · exact ⟨t, htT, h⟩
    ·
      have hLtc : L.map (MulAut.conj t).toMonoidHom ∈ cComp (⊤ : Subgroup G) := cComp_conj hL
      ext K
      constructor
      · intro hK
        have hTs : Group.IsSolvable ↥T := by
          have : Group.IsNilpotent ↥T := hT.2.1.isNilpotent
          infer_instance
        have hpc : perfectCore (L ⊔ T) ≤ L ⊔ L.map (MulAut.conj t₀).toMonoidHom := by
          have := perfectCore_le_of_sup_solvable
            (A := L ⊔ L.map (MulAut.conj t₀).toMonoidHom) (B := T) (Y := L ⊔ T)
            (hXT ▸ le_sup_left) Subgroup.normal_subgroupOf hXT hTs
          exact this
        have hKX : K ≤ L ⊔ L.map (MulAut.conj t₀).toMonoidHom :=
          (le_perfectCore_of_perfect (le_of_mem_cComp hK) (perfect_of_mem_cComp hK)).trans hpc
        have hXLT : L ⊔ L.map (MulAut.conj t₀).toMonoidHom ≤ L ⊔ T := hXT ▸ le_sup_left
        have hKX' : K ∈ cComp (L ⊔ L.map (MulAut.conj t₀).toMonoidHom) :=
          cComp_mem_of_le hK hKX hXLT
        have hKtop : K ∈ cComp (⊤ : Subgroup G) :=
          cComp_mem_of_subnormal (A3.subnormal_of_normal le_top Subgroup.normal_subgroupOf) hKX'
        by_contra hKne
        have hKL : K ≠ L := fun h => hKne (Or.inl h)
        have hKLt : K ≠ L.map (MulAut.conj t).toMonoidHom := fun h => hKne (Or.inr h)
        have h1 := h37 K hKtop L hL hKL
        have h2 := h37 K hKtop _ hLtc hKLt
        have hcL : ∀ k ∈ K, ∀ l ∈ L, l * k = k * l := fun k hk l hl =>
          Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 hk) l hl
        have hcLt : ∀ k ∈ K, ∀ l ∈ L.map (MulAut.conj t₀).toMonoidHom, l * k = k * l :=
          fun k hk l hl => Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hLt ▸ h2) hk) l hl
        have hKabel : ⁅K, K⁆ = ⊥ := by
          refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun k hk => ?_
          rw [Subgroup.mem_centralizer_iff]
          intro k' hk'
          have hle : L ⊔ L.map (MulAut.conj t₀).toMonoidHom ≤
              Subgroup.centralizer ({k} : Set G) := by
            refine sup_le (fun l hl => ?_) (fun l hl => ?_)
            · rw [Subgroup.mem_centralizer_iff]
              intro y hy
              rw [Set.mem_singleton_iff] at hy
              rw [hy]
              exact (hcL k hk l hl).symm
            · rw [Subgroup.mem_centralizer_iff]
              intro y hy
              rw [Set.mem_singleton_iff] at hy
              rw [hy]
              exact (hcLt k hk l hl).symm
          have := Subgroup.mem_centralizer_iff.mp (hle (hKX hk')) k rfl
          exact this.symm
        exact ne_bot_of_mem_cComp hK (by rw [← perfect_of_mem_cComp hK]; exact hKabel)
      · rintro (h | h)
        · rw [h]
          exact cComp_mem_of_le hL le_sup_left le_top
        · rw [h]
          exact cComp_mem_of_le hLtc hLtT le_top
    · rw [hLt]
      exact hcomm
    · rw [hLt]
      exact hinf
    · rw [hLt]
      exact (Subgroup.normalizer_eq_top_iff.mpr hXnorm ▸ le_top)
    · rw [hLt]
      exact hXT

theorem a38ForSQTKCat_of_facts (hmult2 : Mult2Fact) (ha134 : A134SQTKFactCat)
    (h36 : A36CoreForSQTKCat) (h37 : A37ForSQTKCat) : A38ForSQTKCat := fun Q _ hQ => by
  have := hQ.finite
  have hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup Q) ≤ 2 :=
    fun q hq hq2 => hQ.rank_top hq hq2
  have h36Q := h36 Q hQ
  have h37Q := h37 Q hQ
  refine a38_part3_of_package h37Q fun L hL hnorm => ?_
  have hL36 := h36Q L hL
  exact nonnormal_package_of_a134 hmult2 hrank (ha134 Q hQ)
    h37Q hL (hQ.pCore_two_of_subnormal (subnormal_of_mem_cComp hL)) hL36.1 hL36.2.2 hnorm

end CFSG.QuasithinUnique.Vol2Native
