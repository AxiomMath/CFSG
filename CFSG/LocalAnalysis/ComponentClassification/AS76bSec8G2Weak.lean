module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2JData
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Four
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3 JData)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)

section Weak

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite K] [CharP K 2] in
theorem nolong_of_isSylowOf
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hnolong : ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c)) (R₁ : Subgroup G) :
    ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R₁ T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c) := by
  rintro ⟨T', g', hc', hp, ha⟩
  exact hnolong (exists_sec3_of_isSylowOf hψ hc' hR hp ha)

theorem inf_eq_bot_or_card_eq
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184) (h184s : G2Centr184s)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hnolong : ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c)) :
    T ⊓ A = ⊥ ∨ Nat.card R = Nat.card K := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨p, y, J, hJ, hJc, -⟩ :=
    exists_jData_of_nolong hf hK h4 h32 h184 h184s hc hOut hZA hψ hnolong
  obtain ⟨p', y', J', hJ', -, -⟩ := exists_jData_of_nolong hf hK h4 h32 h184 h184s hc.swap hOut
    hZA hψ (nolong_of_isSylowOf hψ hc.sylowR hnolong _)
  rcases hc.dichotomy h32 h4 h34 hJ hJ' with h | h
  · exact Or.inl h
  · right
    rw [hc.inf_sec3V_eq h32 h4 h34 hJ] at h
    rw [← hc.card_eq, h, hJc]

theorem star36_of_nolong
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184) (h184s : G2Centr184s)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hnolong : ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c))
    {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) : Star36 A R (sec3V R T) := by
  classical
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hV := hc.sec3V_eq_sup h32 h4 h34 hJ
  obtain ⟨w, hw⟩ := hc.exists_conj
  have hVe : IsElemAbelian 2 (sec3V R T) :=
    isElemAbelian_sec3V (hc.elemR h32) hc.le_centralizer ⟨w, hw⟩
  have hRV : R ≤ sec3V R T := le_sup_left.trans (le_sec3V_of ⟨w, hw⟩)
  have hVp : IsPGroup 2 (sec3V R T) := fun v => ⟨1, Subtype.ext (by simpa using hVe.2 v v.2)⟩
  have hRJ : R ≤ normalizer (J : Set G) := fun r hr => centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun j hj => mem_centralizer_iff.1 (hc.sylowR.le hr) j (hJ.le hj))
  have hRA := inf_eq_bot_sec3 hc hZA
  intro x hx
  by_cases hxR : rightConjugate R x = R
  · have hxN : x ∈ normalizer (A : Set G) := by
      have h1 := Lemma36.normalizer_le hc.hyp hc.sylowR 1
        (by rw [rightConjugate_one]; exact (rightConjugate_eq_self_iff R x).1 hxR)
      rwa [rightConjugate_one] at h1
    have hAx : rightConjugate A x = A := (rightConjugate_eq_self_iff A x).2 hxN
    have d := hc.conjData_R h32 h4 h34 hJ
    rw [hAx]
    exact ⟨y, mem_inf.2 ⟨d.mem, d.mem_normalizer⟩, d.odd, d.trans, hc.normalizer_R h32 h4 h34 hJ⟩
  have hxN : x ∉ normalizer (A : Set G) := by
    intro hxN
    apply hxR
    have hKx : rightConjugate (centralizer (A : Set G)) x = centralizer (A : Set G) := by
      rw [← centralizer_rightConjugate, (rightConjugate_eq_self_iff A x).2 hxN]
    have hle : R ⊔ rightConjugate R x ≤ centralizer (A : Set G) :=
      sup_le hc.sylowR.le (hKx ▸ map_mono hc.sylowR.le)
    have hp : IsPGroup 2 (R ⊔ rightConjugate R x : Subgroup G) := hVp.to_le (sup_le hRV hx)
    have h1 := hc.sylowR.eq_of_le le_sup_left hle hp
    exact eq_of_le_of_card_ge (le_sup_right.trans h1.le) (by rw [rightConjugate_card])
  have hcx : Sec3 A R (rightConjugate R x) x :=
    ⟨hc.hyp, hc.sylowR, hxN, AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR x,
      hx.trans ((le_centralizer_self_of_isElemAbelian hVe).trans
        (centralizer_le fun v hv => hRV hv))⟩
  have hnle : ¬ rightConjugate R x ≤ R := fun h =>
    hxR (eq_of_le_of_card_ge h (by rw [rightConjugate_card]))
  obtain ⟨t, htx, htR⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hmulV : ∀ v ∈ sec3V R T, ∃ r ∈ R, ∃ j ∈ J, r * j = v := by
    intro v hv
    have hv' : v ∈ ((R ⊔ J : Subgroup G) : Set G) := hV ▸ hv
    rw [coe_mul_of_left_le_normalizer_right R J hRJ] at hv'
    obtain ⟨r, hr, j, hj, hrj⟩ := hv'
    exact ⟨r, hr, j, hj, hrj⟩
  obtain ⟨r, hr, j, hj, rfl⟩ := hmulV t (hx htx)
  have hj1 : j ≠ 1 := fun h => htR (by rw [h, mul_one]; exact hr)
  obtain ⟨a, ha, haj⟩ := hJ.trans p hJ.mem hJ.ne_one j hj hj1
  obtain ⟨haA, haJ⟩ := mem_inf.1 ha
  have hJa := hJ.rightConjugate hc.sylowR.le (inv_mem haA)
  rw [inv_inv, haj, (rightConjugate_eq_self_iff J a⁻¹).2 (inv_mem haJ)] at hJa
  have hJx : JData A R (rightConjugate R x) j J (a * y * a⁻¹) := by
    refine hJa.of_aParts ⟨r * j, htx, ?_⟩ ?_
    · have hrj : r * j = j * r :=
        (mem_centralizer_iff.1 (hc.sylowR.le hr) j (hJ.le hj)).symm
      have e : (r * j)⁻¹ * j = r⁻¹ := by rw [hrj]; group
      rw [e]
      exact inv_mem hr
    · intro t' ht' p' hp'A hp'
      obtain ⟨r', hr', j', hj', rfl⟩ := hmulV t' (hx ht')
      have hrj : r' * j' = j' * r' := (mem_centralizer_iff.1 (hc.sylowR.le hr') j' (hJ.le hj')).symm
      have h1 : j'⁻¹ * p' ∈ R ⊓ A := by
        refine mem_inf.2 ⟨?_, mul_mem (inv_mem (hJ.le hj')) hp'A⟩
        have e : j'⁻¹ * p' = r' * ((r' * j')⁻¹ * p') := by
          rw [hrj]
          group
        rw [e]
        exact mul_mem hr' hp'
      rw [hRA, mem_bot, inv_mul_eq_one] at h1
      rw [← h1]
      exact hj'
  have hVx : sec3V R (rightConjugate R x) = sec3V R T := by
    rw [hcx.sec3V_eq_sup h32 h4 h34 hJx, hV]
  obtain ⟨p', y', J', hJ', -, -⟩ := exists_jData_of_nolong hf hK h4 h32 h184 h184s hcx.swap hOut
    hZA hψ (nolong_of_isSylowOf hψ hc.sylowR hnolong _)
  have d := hcx.conjData_T h32 h4 h34 hJ'
  have hn := hcx.normalizer_T h32 h4 h34 hJ'
  rw [hVx] at d hn
  exact ⟨x⁻¹ * y' * x, mem_inf.2 ⟨d.mem, d.mem_normalizer⟩, d.odd, d.trans, hn⟩

theorem sec3V_case_two
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184) (h184s : G2Centr184s)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v))
    (hnolong : ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c)) (hTA : T ⊓ A = ⊥) :
    sec3V R T = R ⊔ twoLift ψ (rootSubgroup .G2 K g2v) ∧
      (∀ v ∈ sec3V R T, v ∉ A ↔
        ∃ x : G, rightConjugate R x ≤ sec3V R T ∧ v ∈ rightConjugate R x ∧ v ≠ 1) ∧
      ∀ x₁ x₂ x₁' x₂' : G, rightConjugate R x₁ ≤ sec3V R T → rightConjugate R x₂ ≤ sec3V R T →
        rightConjugate R x₁' ≤ sec3V R T → rightConjugate R x₂' ≤ sec3V R T →
        rightConjugate R x₁ ≠ rightConjugate R x₂ →
        rightConjugate R x₁' ≠ rightConjugate R x₂' →
        ∃ n ∈ normalizer ((sec3V R T : Subgroup G) : Set G),
          rightConjugate (rightConjugate R x₁) n = rightConjugate R x₁' ∧
            rightConjugate (rightConjugate R x₂) n = rightConjugate R x₂' := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨p, y, hJ⟩ := jData_of_actsIn hf hK h4 h32 hc hZA hψ hTv
  have hV := hc.sec3V_eq_sup h32 h4 h34 hJ
  have d := hc.conjData_R h32 h4 h34 hJ
  have hcomm := d.commutator_eq
  have hstar := star36_of_nolong hf hK h4 h32 h184 h184s hc hOut hZA hψ hnolong hJ
  rcases AS76b.lemma36 h32 (lemma33Two_of h32 h4 h34) G A R T g hc.hyp hc.sylowR hc.not_mem
    hc.sylowT hc.le_centralizer hstar with ⟨h1, -, -⟩ | ⟨-, h2, h3⟩
  · exfalso
    rw [hcomm] at h1
    apply hc.T_ne_bot
    rw [← inf_eq_left.2 (h1.symm.le.trans inf_le_right), hTA]
  · refine ⟨hV, fun v hv => ?_, h3⟩
    rw [← h2 v hv, hcomm]
    constructor
    · intro hvA hvVA
      exact hvA (mem_inf.1 hvVA).2
    · intro hvVA hvA
      exact hvVA (mem_inf.2 ⟨hv, hvA⟩)

end Weak

end CFSG.ComponentClassification.RankTwoExceptional
