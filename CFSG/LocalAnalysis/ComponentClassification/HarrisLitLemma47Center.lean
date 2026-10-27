module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46dii
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Center47

theorem card_center_dvd_card_griessHopfMultiplier {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) :
    Nat.card ↥(center Q) ∣ Nat.card (Open.griessHopfMultiplier (Q ⧸ center Q)) := by
  have : Group.IsPerfect Q := hQ.1
  have : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center Q))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨-, ⟨h, -, -, -, -, e, -⟩, -⟩ :=
    RankThree.PerfectCover.perfect_central_kernel_quotient_of_schur_multiplier
      (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk'])
  have h1 : Nat.card ↥(QuotientGroup.mk' (center Q)).ker = Nat.card ↥(center Q) := by
    rw [QuotientGroup.ker_mk']
  calc Nat.card ↥(center Q) = Nat.card ↥(QuotientGroup.mk' (center Q)).ker := h1.symm
    _ = _ := (Nat.card_congr e.toEquiv).symm
    _ ∣ _ := Subgroup.card_quotient_dvd_card _
    _ = _ := (Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv).symm

theorem card_griessHopfMultiplier_congr (hGA : TBLit.GriessMultipliersOdd) {Y Y' : Type}
    [Group Y] [Group Y'] (e : Y ≃* Y') {τ : Assembly.LowTwoRank.StatedLieTag} {n p r : ℕ}
    (hn : n ≠ 0) (hm : Blueprint.LieModel Y τ n p r) (hp2 : p ≠ 2)
    (hrow : τ = .PSL ∨ (τ = .PSU ∧ Even n)) :
    Nat.card (Open.griessHopfMultiplier Y) = Nat.card (Open.griessHopfMultiplier Y') := by
  rw [card_griessHopfMultiplier_eq_odd hGA (models_lieModel_of_lieModel_of_ne_zero hn hm) hp2
      hrow,
    card_griessHopfMultiplier_eq_odd hGA (models_lieModel_of_lieModel_of_ne_zero hn
      (GSThmB.OddQuot.lieModel_of_equiv e hm)) hp2 hrow]

theorem isMTypeSchur_of_surjective' (hGA : TBLit.GriessMultipliersOdd) {A B : Type}
    [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} (hp2 : p ≠ 2)
    (f : A →* B) (hf : Function.Surjective f) (hker : ¬ 2 ∣ Nat.card f.ker)
    (hA : Group.IsPerfect A) (hB : IsQuasisimple B) (hO : pPrimeCore 2 B = ⊥)
    (hch : IsSimpleChevalleyOver p (B ⧸ center B)) (hev : Even (Nat.card ↥(center B)))
    (h2 : ordProj[2] (Nat.card ↥(center B)) =
      ordProj[2] (Nat.card (Open.griessHopfMultiplier (B ⧸ center B)))) :
    IsMTypeSchur p A := by
  obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective f hf hker
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective f hf hker
  have hZB := fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
  have eC : A ⧸ Open.fusionZStar A ≃* B ⧸ center B :=
    eZ.trans (QuotientGroup.quotientMulEquivOfEq hZB)
  have hcard : Nat.card ↥(Open.fusionZStar A) = Nat.card f.ker * Nat.card ↥(center B) := by
    rw [card_fusionZStar_of_surjective f hf hker, hZB]
  have hkodd : Odd (Nat.card f.ker) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hker)
  have hZ0 : Nat.card ↥(center B) ≠ 0 := Nat.card_pos.ne'
  have hord : ordProj[2] (Nat.card ↥(Open.fusionZStar A)) = ordProj[2] (Nat.card ↥(center B)) := by
    rw [hcard, mul_comm, factorization_two_mul_odd hZ0 hkodd]
  have hBq : IsQuasisimple (B ⧸ pPrimeCore 2 B) :=
    LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO.symm)) hB
  obtain ⟨τ, n, r, hm⟩ := hch
  refine .inl ⟨⟨hA, LocalCores.isQuasisimple_of_mulEquiv eO.symm hBq⟩,
    ⟨τ, n, r, GSThmB.OddQuot.lieModel_of_equiv eC.symm hm⟩, ?_, fun n' r' hn' _ hm' => ?_⟩
  · rw [hcard]
    exact Nat.even_mul.mpr (Or.inr hev)
  · rw [hord, h2]
    rcases hm' with hm' | hm'
    · rw [card_griessHopfMultiplier_congr hGA eC (by omega) hm' hp2 (Or.inl rfl)]
    · rw [card_griessHopfMultiplier_congr hGA eC (by omega) hm' hp2
        (Or.inr ⟨rfl, even_two_mul n'⟩)]

theorem exists_intrinsic_isMTypeSchur' {X : Type} [Group X] [Finite X]
    (hGA : TBLit.GriessMultipliersOdd) {β : X}
    (hβ2 : orderOf β = 2) {K₀ : Subgroup (MBar β)} (hK₀ : IsComponent K₀)
    (hβK₀ : betaBar β ∈ K₀) {p : ℕ} (hp2 : p ≠ 2)
    (hch : IsSimpleChevalleyOver p (↥K₀ ⧸ center ↥K₀))
    (hev : Even (Nat.card ↥(center ↥K₀)))
    (h2 : ordProj[2] (Nat.card ↥(center ↥K₀)) =
      ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥K₀ ⧸ center ↥K₀)))) :
    ∃ J : Subgroup X, IsTwoComponentIn J (centralizer {β}) ∧ β ∈ J ∧ IsMTypeSchur p ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (MBar β) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hK₀p : IsPComponent 2 K₀ :=
    (isTwoComponent_iff_isPComponent K₀).mp ((isTwoComponent_iff_isComponent hO K₀).mpr hK₀)
  obtain ⟨-, hlift, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X))))
    (QuotientGroup.mk'_surjective _)
    (GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥(centralizer ({β} : Set X))))
  obtain ⟨hJ₀, hJ₀map⟩ := hlift K₀ hK₀p
  set J₀ := closure {x : ↥(centralizer ({β} : Set X)) |
    x ∈ K₀.comap (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))) ∧
      ∃ k : ℕ, orderOf x = 2 ^ k} with hJ₀def
  have hβJ₀ : (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({β} : Set X))) ∈ J₀ :=
    subset_closure ⟨hβK₀, 1, by rw [pow_one, Subgroup.orderOf_mk]; exact hβ2⟩
  have hJM : J₀.map (centralizer ({β} : Set X)).subtype ≤ centralizer ({β} : Set X) :=
    map_subtype_le J₀
  have hsub : (J₀.map (centralizer ({β} : Set X)).subtype).subgroupOf
      (centralizer ({β} : Set X)) = J₀ :=
    comap_map_eq_self_of_injective (centralizer ({β} : Set X)).subtype_injective J₀
  have hJ : IsTwoComponentIn (J₀.map (centralizer ({β} : Set X)).subtype) (centralizer {β}) :=
    (isTwoComponentIn_iff hJM).mpr (by rw [hsub]; exact hJ₀)
  refine ⟨J₀.map (centralizer ({β} : Set X)).subtype, hJ, ⟨_, hβJ₀, rfl⟩, ?_⟩
  set ρ := (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))).comp
    (Subgroup.inclusion hJM) with hρ
  have hrange : ρ.range = K₀ := by
    rw [hρ, MonoidHom.range_comp, Subgroup.inclusion_range, hsub, hJ₀map]
  set g := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ρ.rangeRestrict with hg
  have hgs : Function.Surjective g := by
    rw [hg, MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp ρ.rangeRestrict_surjective
  have hgk : g.ker = ρ.ker := by
    rw [hg, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _),
      MonoidHom.ker_rangeRestrict]
  have hker : ¬ 2 ∣ Nat.card g.ker := by
    rw [hgk, hρ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    intro h2
    have hdvd := Subgroup.card_comap_dvd_of_injective
      (pPrimeCore 2 ↥(centralizer ({β} : Set X))) (Subgroup.inclusion hJM)
      (Subgroup.inclusion_injective hJM)
    exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) (h2.trans hdvd)
  have hO₀ : pPrimeCore 2 ↥K₀ = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hK₀.2
  exact isMTypeSchur_of_surjective' hGA hp2 g hgs hker hJ.2.2.1 hK₀.1 hO₀ hch hev h2

theorem gcd_four_cases {m : ℕ} (hm : Even m) :
    (Nat.gcd 4 m = 2 ∨ Nat.gcd 4 m = 4) ∧ (Nat.gcd 4 m = 4 ↔ 4 ∣ m) := by
  obtain ⟨c, rfl⟩ := hm
  refine ⟨?_, ⟨fun h => h ▸ Nat.gcd_dvd_right 4 _, fun h => Nat.gcd_eq_left h⟩⟩
  have h2 : 2 ∣ Nat.gcd 4 (c + c) := Nat.dvd_gcd (by norm_num) ⟨c, by ring⟩
  have h4 : Nat.gcd 4 (c + c) ∣ 4 := Nat.gcd_dvd_left 4 _
  have hle : Nat.gcd 4 (c + c) ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  interval_cases h : Nat.gcd 4 (c + c) <;> simp_all

end Center47

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem center_layer_cases [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hGA : TBLit.GriessMultipliersOdd) (hT1 : Harris82Theorem1KProper) (hσ : Setup42 h hS w z)
    (i j : ℕ) {k : ℕ}
    (hc : IsLemma46c L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hE : IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hm : Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 p k ∨
      Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 p k) :
    (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 p k ∧
      (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 1 ∨
        (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2 ∧
          4 ∣ p ^ k - 1))) ∨
    (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 p k ∧
      (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 1 ∨
        (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2 ∧
          4 ∣ p ^ k + 1))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set E := layer (MBar β) with hEdef
  have hp2 : p ≠ 2 := h.config.ne_two
  have hp : p.Prime := h.config.prime
  have hO : pPrimeCore 2 (MBar β) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hEn : E.Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hEc : IsComponent E := ⟨hE, hEn.isSubnormal⟩
  have hZ2 : IsPGroup 2 ↥(center ↥E) :=
    isPGroup_center_of_pPrimeCore_eq_bot (pPrimeCore_eq_bot_of_isSubnormal hO hEn.isSubnormal)
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hZ2
  have hdvd := Center47.card_center_dvd_card_griessHopfMultiplier hE
  have hsodd : Odd (p ^ k) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have key : ∀ (d : ℕ), (d = 2 ∨ d = 4) →
      (Nat.card (Open.griessHopfMultiplier (↥E ⧸ center ↥E))).factorization 2 =
        d.factorization 2 →
      IsSimpleChevalleyOver p (↥E ⧸ center ↥E) →
      Nat.card ↥(center ↥E) = 1 ∨ (Nat.card ↥(center ↥E) = 2 ∧ d = 4) := by
    intro d hd hfac hch
    by_cases hZ1 : center ↥E = ⊥
    · left
      rw [hZ1, card_bot]
    right
    have hβE : betaBar β ∈ E := by
      obtain ⟨y, -, hy⟩ := hc.2.2 hZ1
      rw [← hy]
      exact y.2
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · exfalso
        apply hZ1
        rw [h0, pow_zero] at he
        exact (card_eq_one.mp he)
      · exact h0
    have hd2 : (d = 2 ∧ d.factorization 2 = 1) ∨ (d = 4 ∧ d.factorization 2 = 2) := by
      rcases hd with rfl | rfl
      · exact .inl ⟨rfl, Nat.prime_two.factorization_self⟩
      · refine .inr ⟨rfl, ?_⟩
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.prime_two.factorization_pow]
        simp
    have hM0 : Nat.card (Open.griessHopfMultiplier (↥E ⧸ center ↥E)) ≠ 0 := by
      intro h0
      rw [h0, Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply] at hfac
      rcases hd2 with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    have hele : e ≤ d.factorization 2 := by
      rw [← hfac]
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hM0).mp (he ▸ hdvd)
    have hne : e ≠ d.factorization 2 := by
      intro heq
      have hev : Even (Nat.card ↥(center ↥E)) := by
        rw [he]
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have h2 : ordProj[2] (Nat.card ↥(center ↥E)) =
          ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥E ⧸ center ↥E))) := by
        rw [hfac, he, Nat.prime_two.factorization_pow, Finsupp.single_eq_same, heq]
      obtain ⟨J, hJ, hβJ, hMt⟩ :=
        Center47.exists_intrinsic_isMTypeSchur' hGA (hσ.orderOf_beta i j) hEc hβE hp2 hch hev
          h2
      exact not_isMTypeSchur_of_kProper hT1 hnonab hK hcat (hσ.orderOf_beta i j) hJ hβJ hp
        hp2 hMt
    rcases hd2 with ⟨hd', h1⟩ | ⟨hd', h1⟩
    · omega
    · have he_eq : e = 1 := by omega
      exact ⟨by rw [he, he_eq, pow_one], hd'⟩
  rcases hm with hm | hm
  · left
    refine ⟨hm, ?_⟩
    have hev : Even (p ^ k - 1) := by
      obtain ⟨c, hc⟩ := hsodd; exact ⟨c, by omega⟩
    obtain ⟨hcase, hiff⟩ := Center47.gcd_four_cases hev
    rcases key (Nat.gcd 4 (p ^ k - 1)) hcase
      (factorization_card_griessHopfMultiplier_psl hGA hp2 four_ne_zero hm)
      ⟨.PSL, 4, k, hm⟩ with h1 | ⟨h2, h4⟩
    · exact .inl h1
    · exact .inr ⟨h2, hiff.mp h4⟩
  · right
    refine ⟨hm, ?_⟩
    have hev : Even (p ^ k + 1) := hsodd.add_one
    obtain ⟨hcase, hiff⟩ := Center47.gcd_four_cases hev
    rcases key (Nat.gcd 4 (p ^ k + 1)) hcase
      (factorization_card_griessHopfMultiplier_psu hGA hp2 four_ne_zero ⟨2, rfl⟩ hm)
      ⟨.PSU, 4, k, hm⟩ with h1 | ⟨h2, h4⟩
    · exact .inl h1
    · exact .inr ⟨h2, hiff.mp h4⟩

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
