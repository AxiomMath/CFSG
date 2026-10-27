module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBLayer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413L34a

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB

theorem card_eq_168_of_lieModel_dvd {Z : Type} [Group Z] {p m : ℕ} (hp2 : p ≠ 2)
    (h16 : 16 ∣ p ^ (2 * m) - 1) (h : Blueprint.LieModel Z .PSL 2 p m)
    (hdvd : Nat.card Z ∣ 336) : Nat.card Z = 168 := by
  obtain ⟨hp, -, h4, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two hp hp2 hF] at hdvd ⊢
  set q := p ^ m with hq
  have hq2 : p ^ (2 * m) = q ^ 2 := by rw [hq, ← pow_mul, mul_comm]
  rw [hq2] at h16
  have hq9 : q ≤ 9 := by
    by_contra hlt
    have h1 : 100 ≤ q ^ 2 := by nlinarith
    have h2 : 49 ≤ (q ^ 2 - 1) / 2 := by omega
    have h3 : 10 * 49 ≤ q * ((q ^ 2 - 1) / 2) := Nat.mul_le_mul (by omega) h2
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases q
  all_goals (revert h16 hdvd; decide)

namespace JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem seven (hJ : JLayer hs π)
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) :
    Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 168 ∧ p = 7 ∧ f / 2 = 1 ∧
      Nonempty (↥(S ⊓ L) ≃* DihedralGroup (2 ^ 3)) := by
  have hKle : KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} := by
    rw [← hJ.h412.layerIn_layer_centralizer]
    exact map_subtype_le _
  have hK := card_eq_168_of_lieModel_dvd hs.p_ne_two hs.sixteen_dvd (hs.lieModel_KBar hJ.h412)
    (by rw [← hcent]; exact Subgroup.card_dvd_of_le hKle)
  obtain ⟨hp7, hf⟩ := eq_seven_of_lieModel_card hs.p_ne_two (hs.lieModel_KBar hJ.h412) hK
  obtain ⟨m, -, ⟨e⟩⟩ := hs.setup.dihedral
  have hm := hs.factorization_card_KBar hJ.h412 e
  rw [hK, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)] at hm
  subst hm
  exact ⟨hK, hp7, hf, ⟨e⟩⟩

theorem card_T_le
    (hJ : JLayer hs π) :
    Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set πM := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπM
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have hT1 : IsSylowOf 2 T (centralizer ({t} : Set X) ⊓ M) := hs.lemma45.isSylowOf_T
  have hTM : T ≤ M := hT1.le.trans inf_le_right
  have hTH : T ≤ centralizer ({t} : Set X) := hT1.le.trans inf_le_left
  set Tb := (T.subgroupOf M).map πM with hTb
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
    change πM g * πM ⟨t, _⟩ = πM ⟨t, _⟩ * πM g
    rw [← map_mul, ← map_mul, hgt]
  set φ : ↥Tb →* MulAut P := hJ.theta.comp Tb.subtype with hφ
  have hker : Nat.card φ.ker ≤ 2 := by
    have hle : φ.ker.map Tb.subtype ≤ zpowers (betaBar β) := by
      rintro _ ⟨g, hg, rfl⟩
      replace hg := MonoidHom.mem_ker.mp hg
      have h1 : (g : MBar β) ∈ pCore 2 (MBar β) ⊓ centralizer {hs.setup.tBar i j} :=
        ⟨(hJ.theta_eq_one_iff g).mp hg, hTbC g.2⟩
      rw [hJ.h412.pCore_inf_centralizer] at h1
      exact h1
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (subtype_injective _), Nat.card_zpowers] at h1
    have h2 : orderOf (betaBar β) ∣ 2 := orderOf_dvd_of_pow_eq_one hs.betaBar_sq
    exact h1.trans (Nat.le_of_dvd (by norm_num) h2)
  have hrange : Nat.card φ.range ≤ 32 := by
    have hle : φ.range ≤ centralizer {hJ.theta (hs.setup.tBar i j)} := by
      rintro _ ⟨g, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hgt : (g : MBar β) * hs.setup.tBar i j = hs.setup.tBar i j * g :=
        mem_centralizer_singleton_iff.mp (hTbC g.2)
      change hJ.theta g * hJ.theta (hs.setup.tBar i j) =
        hJ.theta (hs.setup.tBar i j) * hJ.theta g
      rw [← map_mul, ← map_mul, hgt]
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [card_centralizer_outer hJ.orderOf_alpha hJ.alpha_not_mem] at hdvd
    have hTbp : IsPGroup 2 Tb := hTp.map πM
    exact card_le_32_of_dvd (hTbp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective) hdvd
  rw [← hcardT, ← Subgroup.card_ker_mul_card_range φ]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 2 * 32 := Nat.mul_le_mul hker hrange
    _ = 64 := by norm_num

theorem orderOf_w
    (hJ : JLayer hs π)
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) : orderOf w = 2 := by
  obtain ⟨-, -, -, ⟨e⟩⟩ := hJ.seven hcent
  have h := hJ.card_T_le
  rw [hs.card_T_eq, Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h
  norm_num at h
  have hw := hs.setup.orderOf_w_eq
  have hw1 : orderOf w ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite w)
  have hw2 : orderOf w ≠ 1 := fun h => hs.setup.w_ne_one (orderOf_eq_one_iff.mp h)
  omega

theorem card_T
    (hJ : JLayer hs π)
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) :
    Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) = 64 := by
  obtain ⟨-, -, -, ⟨e⟩⟩ := hJ.seven hcent
  rw [hs.card_T_eq, Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hJ.orderOf_w hcent]
  norm_num

theorem card_S_le
    (hJ : JLayer hs π)
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) : Nat.card S ≤ 128 := by
  obtain ⟨-, -, -, -, hcardS, -⟩ :=
    hs.standing.lemma41_of_lift hs.sylow hs.setup.lift hs.setup.gen3
  rw [hJ.card_T hcent] at hcardS
  omega

end JLayer

end EndB

end CFSG.ComponentClassification.HarrisLit
