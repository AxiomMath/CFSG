module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndL34Facts
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem HarrisEnd.eq_seven_of_lieModel_card {Y : Type} [Group Y] {p m : ℕ}
    (hp2 : p ≠ 2) (h : Blueprint.LieModel Y .PSL 2 p m) (hc : Nat.card Y = 168) :
    p = 7 ∧ m = 1 := by
  obtain ⟨hp, hm, h4, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two hp hp2 hF] at hc
  have h7 : p ^ m = 7 := by
    set q := p ^ m with hq
    have hq8 : q < 8 := by
      by_contra hlt
      have h63 : 63 ≤ q ^ 2 - 1 := by
        have : 64 ≤ q ^ 2 := by nlinarith
        omega
      have h31 : 31 ≤ (q ^ 2 - 1) / 2 := by omega
      have : 8 * 31 ≤ q * ((q ^ 2 - 1) / 2) := Nat.mul_le_mul (by omega) h31
      omega
    interval_cases q <;> first | rfl | (norm_num at hc)
  exact (Nat.Prime.pow_eq_iff (by norm_num)).mp h7

namespace Setting46e

theorem lieModel_layerIn_fixedPoints (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints (conjOn
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j)))) .PSL 2 p
        (f / 2) := by
  rw [layerIn_fixedPoints_conjOn, h412.layerIn_layer_centralizer]
  exact lieModel_psl2_of_mulEquiv (subgroupOfEquivOfLe hs.KBar_le_layer) (hs.lieModel_KBar h412)

theorem orderOf_conjOn_tBar (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    orderOf (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j)) =
      2 := by
  have htb := hs.tBar_not_mem_centralizer_layer h412
  refine orderOf_eq_prime ?_ fun h => htb (conjOn_eq_one_iff.mp h)
  rw [← map_pow, hs.tBar_sq, map_one]

theorem layer_inf_centralizer_eq_KBar (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (h : GSThmB.layerIn (fixedPoints (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      (hs.setup.tBar i j))) = fixedPoints (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i *
        z ^ j))) (hs.setup.tBar i j))) :
    layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} =
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  rw [layerIn_fixedPoints_conjOn, fixedPoints_conjOn_eq, h412.layerIn_layer_centralizer,
    subgroupOf_inj, inf_of_le_left hs.KBar_le_layer] at h
  rw [h, inf_comm]

theorem l34_structure (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2)
    (hout : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} =
        KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∧
      Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 168 ∧ p = 7 ∧ f / 2 = 1 ∧
      Nonempty (↥(S ⊓ L) ≃* DihedralGroup (2 ^ 3)) := by
  obtain ⟨⟨hlay, hcard⟩, -⟩ := l34_outer_facts hY (hs.orderOf_conjOn_tBar h412) hout
    hs.p_ne_two hs.sixteen_dvd (hs.lieModel_layerIn_fixedPoints h412)
  have hEK := hs.layer_inf_centralizer_eq_KBar h412 hlay
  have hK : Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 168 := by
    rw [← hEK, ← map_fixedPoints_conjOn, Subgroup.card_map_of_injective (subtype_injective _),
      hcard]
  obtain ⟨hp7, hf⟩ := eq_seven_of_lieModel_card hs.p_ne_two (hs.lieModel_KBar h412) hK
  obtain ⟨m, -, ⟨e⟩⟩ := hs.setup.dihedral
  have hm := hs.factorization_card_KBar h412 e
  rw [hK, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)] at hm
  subst hm
  exact ⟨hEK, hK, hp7, hf, ⟨e⟩⟩

theorem card_T_eq (hs : Setting46e t L p f S w z V i j) :
    Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) = 2 * Nat.card ↥(S ⊓ L) * orderOf w := by
  have h1 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (zpowers t ⊔ (S ⊓ L)) (zpowers w)
    hs.setup.zpowers_w_le_normalizer (disjoint_iff.mpr hs.setup.disj)
  have hn : zpowers t ≤ normalizer ((S ⊓ L : Subgroup X) : Set X) := by
    rw [zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun d hd => ?_)
    exact (mem_centralizer_singleton_iff.mp (hs.standing.config.le_centralizer hd.2))
  have hd : Disjoint (S ⊓ L) (zpowers t) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    exact (mem_bot).mpr (hs.standing.eq_one_of_mem_zpowers_of_mem hx.2 hx.1.2)
  have h2 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (S ⊓ L) (zpowers t) hn hd
  rw [h1, sup_comm, h2, Nat.card_zpowers, Nat.card_zpowers, hs.standing.config.orderOf_eq]
  ring

theorem l34_orderOf_w (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2)
    (hout : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    orderOf w = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨e⟩⟩ := hs.l34_structure h412 hY hout
  obtain ⟨-, -, h32, -⟩ := l34_outer_facts hY (hs.orderOf_conjOn_tBar h412) hout
    hs.p_ne_two hs.sixteen_dvd (hs.lieModel_layerIn_fixedPoints h412)
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have hT1 : IsSylowOf 2 T (centralizer ({t} : Set X) ⊓ M) := hs.lemma45.isSylowOf_T
  have hTM : T ≤ M := hT1.le.trans inf_le_right
  have hTH : T ≤ centralizer ({t} : Set X) := hT1.le.trans inf_le_left
  set Tb := (T.subgroupOf M).map π with hTb
  have hTp : IsPGroup 2 (T.subgroupOf M) :=
    hT1.isPGroup.of_equiv (subgroupOfEquivOfLe hTM).symm
  have hcardT : Nat.card Tb = Nat.card T := by
    rw [hTb, GSThmB.OddQuot.card_map_of_isPGroup hTp,
      Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv]
  have hTbC : Tb ≤ centralizer {hs.setup.tBar i j} := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hgt : g * ⟨t, hs.setup.t_mem_centralizer_beta i j⟩ =
        ⟨t, hs.setup.t_mem_centralizer_beta i j⟩ * g :=
      Subtype.ext (mem_centralizer_singleton_iff.mp (hTH hg))
    change π g * π ⟨t, _⟩ = π ⟨t, _⟩ * π g
    rw [← map_mul, ← map_mul, hgt]
  set φ : ↥Tb →* MulAut ↥E := (conjOn E).comp Tb.subtype with hφ
  have hker : Nat.card φ.ker ≤ 2 := by
    have hle : φ.ker.map Tb.subtype ≤ zpowers (betaBar β) := by
      rintro _ ⟨g, hg, rfl⟩
      replace hg := MonoidHom.mem_ker.mp hg
      have h1 : (g : MBar β) ∈ centralizer (E : Set (MBar β)) ⊓ centralizer {hs.setup.tBar i j} :=
        ⟨conjOn_eq_one_iff.mp hg, hTbC g.2⟩
      rw [hs.centralizer_layer_inf_centralizer_tBar h412] at h1
      exact h1
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (subtype_injective _), Nat.card_zpowers] at h1
    have h2 : orderOf (betaBar β) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
      have hb : (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥M) ^ 2 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, hβ2, Subgroup.coe_one])
      change π ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ ^ 2 = 1
      rw [← map_pow, hb, map_one]
    exact h1.trans (Nat.le_of_dvd (by norm_num) h2)
  have hrange : Nat.card φ.range ≤ 32 := by
    refine h32 φ.range ?_ ?_
    · rintro _ ⟨g, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hgt : (g : MBar β) * hs.setup.tBar i j = hs.setup.tBar i j * g :=
        mem_centralizer_singleton_iff.mp (hTbC g.2)
      change conjOn E g * conjOn E (hs.setup.tBar i j) = conjOn E (hs.setup.tBar i j) * conjOn E g
      rw [← map_mul, ← map_mul, hgt]
    · have hTbp : IsPGroup 2 Tb := hTp.map π
      exact (hTbp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
  have hTb64 : Nat.card Tb ≤ 64 := by
    rw [← Subgroup.card_ker_mul_card_range φ]
    calc Nat.card φ.ker * Nat.card φ.range ≤ 2 * 32 := Nat.mul_le_mul hker hrange
      _ = 64 := by norm_num
  rw [hcardT, hs.card_T_eq, Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hTb64
  norm_num at hTb64
  have hw := hs.setup.orderOf_w_eq
  have hw1 : orderOf w ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite w)
  have hw2 : orderOf w ≠ 1 := fun h => hs.setup.w_ne_one (orderOf_eq_one_iff.mp h)
  omega

end Setting46e

end CFSG.ComponentClassification.HarrisLit
