module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Ld
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Le
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29La
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover82A
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerOut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCover
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sj

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.CatFactsL4U4 DiagL CSL

theorem inf_centralizer_eq_bot {P : Type*} [Group P] {K : Subgroup P} (hK : center ↥K = ⊥) :
    K ⊓ centralizer (K : Set P) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxc⟩
  have : (⟨x, hx⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxc g g.2)
  rw [hK, mem_bot] at this
  rw [mem_bot]
  exact congrArg Subtype.val this

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (h : center A = ⊥) : center B = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  have : φ.symm b ∈ center A := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.mem_center_iff.mp hb]
  rw [h, mem_bot] at this
  rw [mem_bot, ← φ.apply_symm_apply b, this, map_one]

theorem center_eq_bot_of_sec8 {H : Type} [Group H] [Finite H] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {J₁ : Subgroup H} (hO : pPrimeCore 2 ↥J₁ = ⊥)
    (hJt : IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f) : center ↥J₁ = ⊥ := by
  have hZ := Cover82.center_eq_bot_of_isSec8JType hp hp2 hf hJt
  rw [eq_bot_iff]
  intro c hc
  have : (QuotientGroup.mk c : ↥J₁ ⧸ pPrimeCore 2 ↥J₁) ∈ center (↥J₁ ⧸ pPrimeCore 2 ↥J₁) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hc g']
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff, hO, mem_bot] at this
  rw [mem_bot]
  exact this

theorem cf82Prop29L4Corr : CF82Prop29L4Corr := by
  intro H _ _ p f hp hp2 hf _ hC hL hq3 ι hιF hι J₁ hJC hJ hJt S₁ hS
  classical
  have : (generalizedFitting H).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := H)).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hFq, hneg, hJF, hO, hcard, e, hek, hJK⟩ :=
    exists_std_L4 hp hp2 hf hC hL hιF hι hJC hJ hJt
  set q := p ^ f with hqdef
  have hqodd : Odd q := (hp.odd_of_ne_two hp2).pow
  have hq3' : 3 ≤ q := by omega
  have hF : Nat.card F = q := by rw [Nat.card_eq_fintype_card, hFq]
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_odd (hFq ▸ hqodd)
  set m := padicValNat 2 (q + 1) with hmdef
  have hm1 : 2 ^ m ∣ q + 1 := pow_padicValNat_dvd
  have hm2 : ¬ 2 ^ (m + 1) ∣ q + 1 := pow_succ_padicValNat_not_dvd (by omega)
  have hm : 2 ≤ m := (padicValNat_dvd_iff_le (by omega)).mp (by norm_num; omega)
  have hv1 : padicValNat 2 (q - 1) = 1 := by
    rw [← Nat.factorization_def _ Nat.prime_two]
    exact factorization_two_eq (by omega) (by norm_num; omega) (by norm_num; omega)
  have hv2 : padicValNat 2 (q ^ 2 - 1) = m + 1 := by
    have e2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [(by omega : 1 ≤ q), Nat.one_le_pow 2 q (by omega)]
      ring
    rw [e2, padicValNat.mul (by omega) (by omega), hv1]
    omega
  have hFcard : Nat.card ↥(generalizedFitting H) = Open.ordA 3 q :=
    GH74.card_of_lieModel_PSL (by norm_num) hL
  have hvF : padicValNat 2 (Nat.card ↥(generalizedFitting H)) = 2 * m + 3 := by
    rw [hFcard, P211.v2_ordA_three hqodd hq3' (by omega), hv2]
    ring
  have hP : Nat.card (projectiveSL 4 F) = Nat.card ↥(generalizedFitting H) :=
    (Nat.card_congr e.toEquiv).symm
  have hL1 : 2 ^ (2 * m + 3) ∣ Nat.card (projectiveSL 4 F) := by
    rw [hP, ← hvF]
    exact pow_padicValNat_dvd
  have hL2 : ¬ 2 ^ (2 * m + 4) ∣ Nat.card (projectiveSL 4 F) := by
    rw [hP, show 2 * m + 4 = padicValNat 2 (Nat.card ↥(generalizedFitting H)) + 1 by omega]
    exact pow_succ_padicValNat_not_dvd Nat.card_pos.ne'
  have hJcard : Nat.card (JK F neg_one_ne_zero') = Nat.card J₁ := by
    rw [← hJK, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJF).toEquiv]
  have hJc : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤
      2 * Nat.card (JK F neg_one_ne_zero') := by
    rw [hJcard, hcard, hF, show (q ^ 2) ^ 2 = q ^ 4 by ring]
  have h4 : q ^ 4 - 1 ≠ 0 := by
    have : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hJ2 : ¬ 2 ^ (m + 2) ∣ Nat.card (JK F neg_one_ne_zero') := by
    rw [hJcard]
    intro h
    have h' : 2 ^ (m + 3) ∣ q ^ 2 * (q ^ 4 - 1) := by
      rw [← hcard, show m + 3 = (m + 2) + 1 by ring, pow_succ, mul_comm (2 ^ (m + 2))]
      exact Nat.mul_dvd_mul_left 2 h
    have hv : padicValNat 2 (q ^ 2 * (q ^ 4 - 1)) = m + 2 := by
      rw [padicValNat.mul (by positivity) h4, padicValNat.pow q 2,
        P211.v2_odd hqodd, P211.v2_four hqodd hq3', hv2]
      ring
    have := pow_succ_padicValNat_not_dvd (p := 2) (n := q ^ 2 * (q ^ 4 - 1))
      (Nat.mul_ne_zero (by positivity) h4)
    rw [hv] at this
    exact this h'
  have hJp : ⁅J₁, J₁⁆ = J₁ := P211.commutator_eq_of_isPComp hJC hJ
  have hJp' : ⁅JK F neg_one_ne_zero', JK F neg_one_ne_zero'⁆ = JK F neg_one_ne_zero' := by
    rw [← hJK, ← Subgroup.map_commutator, AZ.subgroupOf_perfect hJF hJp]
  have φ : ↥J₁ ≃* ↥(JK F neg_one_ne_zero') :=
    (Subgroup.subgroupOfEquivOfLe hJF).symm.trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hJK))
  have hJZ : JK F neg_one_ne_zero' ⊓
      centralizer (JK F neg_one_ne_zero' : Set (projectiveSL 4 F)) = ⊥ :=
    inf_centralizer_eq_bot (center_eq_bot_of_mulEquiv φ (center_eq_bot_of_sec8 hp hp2 hf hO hJt))
  obtain ⟨x, y, hxy, hZ⟩ := L4M.exists_zM (F := F) (m := m) (by rw [hFq]; exact hq3) (by omega)
    (by rw [hFq]; exact hm1) (by rw [hFq]; exact hm2)
  obtain ⟨M⟩ := L4M.nonempty_model h2 hneg hxy hm hZ hJp' hJc hJZ hL1 hL2 hJ2
  set ψ : projectiveSL 4 F →* H := (generalizedFitting H).subtype.comp e.symm.toMonoidHom
    with hψ
  have hψinj : Function.Injective ψ :=
    (generalizedFitting H).subtype_injective.comp e.symm.injective
  have hψr : ψ.range = generalizedFitting H := by
    ext h
    constructor
    · rintro ⟨w, rfl⟩
      exact (e.symm w).2
    · intro hh
      exact ⟨e ⟨h, hh⟩, by simp [hψ]⟩
  have hψι : ψ (proj 4 F kSL) = ι := by
    rw [hψ, MonoidHom.comp_apply, ← hek]
    simp
  have hψJ : (JK F neg_one_ne_zero').map ψ = J₁ := by
    rw [← hJK]
    ext h
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa [hψ] using Subgroup.mem_subgroupOf.mp hw
    · intro hh
      exact ⟨e ⟨h, hJF hh⟩, ⟨⟨h, hJF hh⟩, hh, rfl⟩, by simp [hψ]⟩
  exact prop29ConclCorr_of_map M ψ hψinj hψr hψι hψJ hO hS

end CFSG.ComponentClassification.GSThmB.P29
