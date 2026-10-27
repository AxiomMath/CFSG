module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialClauses

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open Subgroup

theorem exists_normal_isComplement'_of_primewise {R : Type*} [Group R] [Finite R]
    (X : Subgroup R)
    (hM : ∀ p ∈ (Nat.card X).primeFactors, ∃ M : Subgroup R, M.Normal ∧
      ¬ p ∣ Nat.card (M ⊓ X : Subgroup R) ∧ M.index ≤ p ^ (Nat.card X).factorization p) :
    ∃ M : Subgroup R, M.Normal ∧ IsComplement' M X := by
  classical
  choose Mf hMf using hM
  let M : Subgroup R := ⨅ i : (Nat.card X).primeFactors, Mf i.1 i.2
  have hMn : M.Normal := normal_iInf_normal fun i => (hMf i.1 i.2).1
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hdisj : Disjoint M X := by
    rw [disjoint_iff, ← Subgroup.card_eq_one]
    by_contra h1
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    have hpX : p ∣ Nat.card X := hpd.trans (Subgroup.card_dvd_of_le inf_le_right)
    have hpm : p ∈ (Nat.card X).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpX, hX0⟩
    apply (hMf p hpm).2.1
    refine hpd.trans (Subgroup.card_dvd_of_le (inf_le_inf_right _ ?_))
    exact iInf_le (fun i : (Nat.card X).primeFactors => Mf i.1 i.2) ⟨p, hpm⟩
  have hle : M.index ≤ Nat.card X := by
    calc M.index ≤ ∏ i : (Nat.card X).primeFactors, (Mf i.1 i.2).index :=
          Subgroup.index_iInf_le _
      _ ≤ ∏ i : (Nat.card X).primeFactors, (i : ℕ) ^ (Nat.card X).factorization i :=
          Finset.prod_le_prod fun i _ => (hMf i.1 i.2).2.2
      _ = Nat.card X := (Nat.prod_primeFactors_coe_pow_factorization hX0).symm
  have hrel : M.relIndex X = Nat.card X := by
    rw [Subgroup.relIndex, show M.subgroupOf X = ⊥ from ?_, Subgroup.index_bot]
    rw [eq_bot_iff]
    intro x hx
    have : (x : R) ∈ M ⊓ X := ⟨hx, x.2⟩
    rw [disjoint_iff.mp hdisj] at this
    exact (Subgroup.mem_bot.mpr (Subtype.ext ((Subgroup.mem_bot.mp this))))
  have hdvd : Nat.card X ∣ M.index := hrel ▸ Subgroup.relIndex_dvd_index_of_normal M X
  have heq : M.index = Nat.card X :=
    le_antisymm hle (Nat.le_of_dvd (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite)) hdvd)
  refine ⟨M, hMn, isComplement'_of_card_mul_and_disjoint ?_ hdisj⟩
  rw [← heq, Subgroup.card_mul_index]


theorem exists_normal_complement_of_subgroupOf {G : Type*} [Group G] [Finite G]
    {R X : Subgroup G} (hXR : X ≤ R) {M' : Subgroup R} (hM'n : M'.Normal)
    (hM' : IsComplement' M' (X.subgroupOf R)) :
    ∃ M : Subgroup G, M ≤ R ∧ R ≤ Subgroup.normalizer (M : Set G) ∧ Disjoint M X ∧
      M ⊔ X = R ∧ Nat.card M * Nat.card X = Nat.card R := by
  refine ⟨M'.map R.subtype, map_subtype_le M', ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨r, hr⟩ * m * ⟨r, hr⟩⁻¹, hM'n.conj_mem m hm ⟨r, hr⟩, rfl⟩
    · rintro ⟨m, hm, hmg⟩
      have hgR : g ∈ R := by
        have : g = r⁻¹ * (m : G) * r := by
          rw [show (R.subtype m : G) = m from rfl] at hmg
          rw [hmg]; group
        rw [this]
        exact R.mul_mem (R.mul_mem (R.inv_mem hr) m.2) hr
      refine ⟨⟨g, hgR⟩, ?_, rfl⟩
      have h1 := hM'n.conj_mem m hm ⟨r, hr⟩⁻¹
      have h2 : (⟨r, hr⟩⁻¹ * m * (⟨r, hr⟩⁻¹)⁻¹ : R) = ⟨g, hgR⟩ := by
        apply Subtype.ext
        change r⁻¹ * (m : G) * r⁻¹⁻¹ = g
        rw [show (R.subtype m : G) = m from rfl] at hmg
        rw [hmg]; group
      rwa [h2] at h1
  · rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨⟨m, hm, rfl⟩, hgX⟩
    have hm1 : m ∈ M' ⊓ X.subgroupOf R := ⟨hm, hgX⟩
    rw [disjoint_iff.mp hM'.disjoint] at hm1
    rw [Subgroup.mem_bot.mp hm1]
    exact (R.subtype).map_one ▸ Subgroup.one_mem _
  · have htop : (⊤ : Subgroup R).map R.subtype = R := by
      ext g
      exact ⟨fun ⟨x, _, hx⟩ => hx ▸ x.2, fun hg => ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩⟩
    have h := congrArg (Subgroup.map R.subtype) hM'.sup_eq_top
    rwa [Subgroup.map_sup, subgroupOf_map_subtype, inf_of_le_left hXR, htop] at h
  · rw [Subgroup.card_map_of_injective R.subtype_injective, ← hM'.card_mul_card,
      Nat.card_congr (subgroupOfEquivOfLe hXR).toEquiv]

theorem exists_normal_pComplement {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (P : Sylow p R)
    (hP : Subgroup.normalizer (P : Set R) ≤ Subgroup.centralizer (P : Set R)) :
    ∃ M : Subgroup R, M.Normal ∧ ¬ p ∣ Nat.card M ∧ M.index = Nat.card P :=
  ⟨(MonoidHom.transferSylow P hP).ker, MonoidHom.normal_ker _,
    MonoidHom.not_dvd_card_ker_transferSylow P hP,
    (MonoidHom.ker_transferSylow_isComplement' P hP).symm.index_eq_card⟩


theorem le_of_relIndex_eq_two_of_odd {G : Type*} [Group G] [Finite G] {H K X : Subgroup G}
    (hK2 : K.relIndex H = 2) (hXH : X ≤ H) (hX : Odd (Nat.card X)) : X ≤ K := by
  have h1 : K.relIndex X ≤ 2 := hK2 ▸ relIndex_le_of_le_right hXH (by rw [hK2]; norm_num)
  have h2 : K.relIndex X ∣ Nat.card X := relIndex_dvd_card K X
  have h3 : Odd (K.relIndex X) := Odd.of_dvd_nat hX h2
  have h4 : K.relIndex X ≠ 0 := fun h => by rw [h] at h3; exact absurd h3 (by decide)
  have h5 : K.relIndex X = 1 := by
    rcases h3 with ⟨k, hk⟩
    omega
  exact relIndex_eq_one.mp h5

theorem exists_sylow_le_central_of_hall {G : Type*} [Group G] [Finite G]
    {W H K R : Subgroup G} (hK2 : K.relIndex H = 2)
    (hKW : K ≤ Subgroup.centralizer (W : Set G))
    (hNW : ∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ → Subgroup.normalizer (W₀ : Set G) ≤ H)
    (hR : Odd (Nat.card R)) (hWR : W ≤ R)
    (hHall : Nat.Coprime (Nat.card W) (W.relIndex (R ⊓ H)))
    {p : ℕ} [hp : Fact p.Prime] (hpW : p ∣ Nat.card W) :
    ∃ S : Sylow p R, (S : Subgroup R) ≤ W.subgroupOf R ∧
      Subgroup.normalizer (S : Set R) ≤ Subgroup.centralizer (S : Set R) ∧
      Nat.card S = p ^ (Nat.card W).factorization p := by
  set a := (Nat.card W).factorization p with ha
  obtain ⟨P₀⟩ : Nonempty (Sylow p W) := inferInstance
  set P : Subgroup G := (P₀ : Subgroup W).map W.subtype with hP
  have hPcard : Nat.card P = p ^ a := by
    rw [hP, Subgroup.card_map_of_injective W.subtype_injective, Sylow.card_eq_multiplicity]
  have hPW : P ≤ W := map_subtype_le _
  have hPR : P ≤ R := hPW.trans hWR
  have hW0 : Nat.card W ≠ 0 := Nat.card_pos.ne'
  have ha1 : 1 ≤ a := (hp.out.dvd_iff_one_le_factorization hW0).mp hpW
  have hPbot : P ≠ ⊥ := by
    intro h
    have : Nat.card P = 1 := by rw [h, Subgroup.card_bot]
    rw [hPcard] at this
    have := Nat.pow_eq_one.mp this
    rcases this with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · omega
  have hWbot : W ≠ ⊥ := fun h => hPbot (le_bot_iff.mp (h ▸ hPW))
  have hWH : W ≤ H := le_normalizer.trans (hNW W le_rfl hWbot)
  have hNP : Subgroup.normalizer (P : Set G) ≤ H := hNW P hPW hPbot
  have hRH : ¬ p ^ (a + 1) ∣ Nat.card (R ⊓ H : Subgroup G) := by
    intro hdvd
    have hWRH : W ≤ R ⊓ H := le_inf hWR hWH
    have hcard : Nat.card (R ⊓ H : Subgroup G) = W.relIndex (R ⊓ H) * Nat.card W := by
      rw [← relIndex_mul_card (H := W) (K := R ⊓ H), inf_of_le_left hWRH]
    rw [hcard] at hdvd
    have hcop : Nat.Coprime (p ^ (a + 1)) (W.relIndex (R ⊓ H)) := by
      apply Nat.Coprime.pow_left
      exact (Nat.Coprime.coprime_dvd_left hpW hHall)
    exact Nat.pow_succ_factorization_not_dvd hW0 hp.out (hcop.dvd_of_dvd_mul_left hdvd)
  set PR : Subgroup R := P.subgroupOf R with hPRdef
  have hPRcard : Nat.card PR = p ^ a := by
    rw [hPRdef, Nat.card_congr (subgroupOfEquivOfLe hPR).toEquiv, hPcard]
  have hNPR : (Subgroup.normalizer (PR : Set R)).map R.subtype ≤
      R ⊓ Subgroup.normalizer (P : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨r.2, ?_⟩
    have hr' : r ∈ Subgroup.normalizer (PR : Set R) := hr
    change (r : G) ∈ Subgroup.normalizer (P : Set G)
    rw [mem_normalizer_iff] at hr' ⊢
    replace hr := hr'
    intro g
    constructor
    · intro hg
      have := (hr ⟨g, hPR hg⟩).mp hg
      exact this
    · intro hg
      have hgR : g ∈ R := by
        have h := R.mul_mem (R.mul_mem (R.inv_mem r.2) (hPR hg)) r.2
        rwa [show (r : G)⁻¹ * ((r : G) * g * (r : G)⁻¹) * r = g by group] at h
      exact (hr ⟨g, hgR⟩).mpr hg
  have hRp : ¬ p ^ (a + 1) ∣ Nat.card R := by
    intro hdvd
    have hmod := Sylow.card_normalizer_modEq_card hPRcard
    have h1 : p ^ (a + 1) ∣ Nat.card (Subgroup.normalizer (PR : Set R)) :=
      (Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))
    apply hRH
    refine h1.trans ?_
    rw [← Subgroup.card_map_of_injective R.subtype_injective]
    exact Subgroup.card_dvd_of_le (hNPR.trans (inf_le_inf_left _ hNP))
  have hPRp : IsPGroup p PR := IsPGroup.of_card hPRcard
  have hPRi : ¬ p ∣ PR.index := by
    intro h
    apply hRp
    rw [← Subgroup.card_mul_index PR, hPRcard, pow_succ]
    exact Nat.mul_dvd_mul_left _ h
  set S : Sylow p R := hPRp.toSylow hPRi with hSdef
  have hS : (S : Subgroup R) = PR := IsPGroup.toSylow_coe hPRp hPRi
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hS]
    exact fun x hx => hPW hx
  · show Subgroup.normalizer ((S : Subgroup R) : Set R) ≤
      Subgroup.centralizer ((S : Subgroup R) : Set R)
    rw [hS]
    intro r hr
    have hX : (Subgroup.normalizer (PR : Set R)).map R.subtype ≤ K := by
      apply le_of_relIndex_eq_two_of_odd hK2
      · exact (hNPR.trans inf_le_right).trans hNP
      · rw [Subgroup.card_map_of_injective R.subtype_injective]
        exact Odd.of_dvd_nat hR (Subgroup.card_subgroup_dvd_card _)
    have hrK : (r : G) ∈ K := hX ⟨r, hr, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    have := (mem_centralizer_iff.mp (hKW hrK)) x (hPW hx)
    simpa using this
  · rw [hS, hPRcard]


theorem odd_hall_normal_complement {G : Type*} [Group G] [Finite G]
    {W H K R : Subgroup G} (hK2 : K.relIndex H = 2)
    (hKW : K ≤ Subgroup.centralizer (W : Set G))
    (hNW : ∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ → Subgroup.normalizer (W₀ : Set G) ≤ H)
    (hR : Odd (Nat.card R)) (hWR : W ≤ R)
    (hHall : Nat.Coprime (Nat.card W) (W.relIndex (R ⊓ H))) :
    Nat.Coprime (Nat.card W) (W.relIndex R) ∧
      ∃ M : Subgroup G, M ≤ R ∧ R ≤ Subgroup.normalizer (M : Set G) ∧ Disjoint M W ∧
        M ⊔ W = R ∧ Nat.card M * Nat.card W = Nat.card R := by
  have hXcard : Nat.card (W.subgroupOf R) = Nat.card W :=
    Nat.card_congr (subgroupOfEquivOfLe hWR).toEquiv
  have key : ∀ p : ℕ, p.Prime → p ∣ Nat.card W → ∃ S : Sylow p R,
      (S : Subgroup R) ≤ W.subgroupOf R ∧
      Subgroup.normalizer (S : Set R) ≤ Subgroup.centralizer (S : Set R) ∧
      Nat.card S = p ^ (Nat.card W).factorization p := by
    intro p hp hpW
    have : Fact p.Prime := ⟨hp⟩
    exact exists_sylow_le_central_of_hall hK2 hKW hNW hR hWR hHall hpW
  refine ⟨Nat.coprime_of_dvd fun p hp hpW hpi => ?_, ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨S, hSX, -, -⟩ := key p hp hpW
    apply S.not_dvd_index
    rw [← relIndex_mul_index hSX]
    exact Dvd.dvd.mul_left hpi _
  · obtain ⟨M', hM'n, hM'⟩ := exists_normal_isComplement'_of_primewise (W.subgroupOf R)
      (fun p hp => by
        rw [hXcard] at hp ⊢
        have hp' := Nat.prime_of_mem_primeFactors hp
        have : Fact p.Prime := ⟨hp'⟩
        obtain ⟨S, -, hSn, hScard⟩ := key p hp' (Nat.dvd_of_mem_primeFactors hp)
        obtain ⟨M, hMn, hMp, hMi⟩ := exists_normal_pComplement S hSn
        exact ⟨M, hMn, fun h => hMp (h.trans (Subgroup.card_dvd_of_le inf_le_left)),
          (hMi.trans hScard).le⟩)
    exact exists_normal_complement_of_subgroupOf hWR hM'n hM'

theorem odd_subgroup_torus_hall_normal_complement {G : Type} [Group G] [Finite G]
    {t s₀ d : G} {q : ℕ} {F' : Type} [Field F'] [Finite F']
    {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
    (hcl : TorusNormalizerClauses G t s₀ d q F' φ)
    (R : Subgroup G) (hR : Odd (Nat.card R)) (hWR : torusW G t s₀ ≤ R)
    (hHall : Nat.Coprime (Nat.card (torusW G t s₀))
      ((torusW G t s₀).relIndex (R ⊓ torusH G t s₀))) :
    Nat.Coprime (Nat.card (torusW G t s₀)) ((torusW G t s₀).relIndex R) ∧
      ∃ M : Subgroup G, M ≤ R ∧ R ≤ Subgroup.normalizer (M : Set G) ∧
        Disjoint M (torusW G t s₀) ∧ M ⊔ torusW G t s₀ = R ∧
        Nat.card M * Nat.card (torusW G t s₀) = Nat.card R := by
  obtain ⟨-, -, -, -, -, hK2, -, -, -, -, hNW, -⟩ := hcl
  exact odd_hall_normal_complement hK2 le_rfl (fun W₀ h1 h2 => (hNW W₀ h1 h2).le) hR hWR hHall

end CFSG.Semidihedral.FixedCoreNontrivial
