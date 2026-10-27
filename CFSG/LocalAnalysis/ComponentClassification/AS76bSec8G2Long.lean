module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Levi
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInnerInvolutions
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
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Pair

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

section NoInv

variable {K : Type} [Field K] [Finite K] [CharP K 2] {L : Subgroup (ModGL .G2 K)}

theorem eq_one_of_fix_g2
    {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (h184 : G2Centr184) (hLC : L ≤ adjointGroup .G2 K) (hXcL : rootSubgroup .G2 K g2c ≤ L)
    (hCodd : Odd (Nat.card (g2Centralizer K ((g2TorusR K ⊔ L : Subgroup (ModGL .G2 K)) :
      Set (ModGL .G2 K))))) {α : MulAut ↥(adjointGroup .G2 K)} {k : ℕ} (hα : α ^ 2 ^ k = 1)
    (hfixH : ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ g2TorusR K → α y = y)
    (hfixL : ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ L → α y = y) : α = 1 := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨-, hcent⟩ := h184 K hK4
  obtain ⟨hNF, Θ, hΘ, -, hker, -⟩ :=
    UnbalancedCatalog.even_G2_exact_automorphism_normal_form hm K hK
  obtain ⟨⟨g₀, σ⟩, hgσ, -⟩ := hNF α
  have hXc : ∀ s : K, (g₀ : ModGL .G2 K) * pinnedX .G2 K g2c (σ s) * (g₀ : ModGL .G2 K)⁻¹ =
      pinnedX .G2 K g2c s := by
    intro s
    have h1 := hgσ ⟨pinnedX .G2 K g2c s, pinnedX_mem_adjointGroup g2c s⟩
    rw [hfixL _ (hXcL (mem_rootSubgroup.2 ⟨s, rfl⟩))] at h1
    simp only at h1
    rw [units_map_entrywise_pinnedX] at h1
    exact h1.symm
  have hg₀ : (g₀ : ModGL .G2 K) ∈ g2LongCent K := by
    refine mem_inf.2 ⟨g₀.2, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hXc 1
    rw [map_one] at h1
    calc (g₀ : ModGL .G2 K) * pinnedX .G2 K g2c 1 =
        (g₀ : ModGL .G2 K) * pinnedX .G2 K g2c 1 * (g₀ : ModGL .G2 K)⁻¹ * g₀ := by group
      _ = pinnedX .G2 K g2c 1 * g₀ := by rw [h1]
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun s => ?_
    show σ s = s
    have h1 := hXc s
    have hmem : pinnedX .G2 K g2c (σ s) ∈ g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) := by
      rw [hcent]
      exact mem_rootSubgroup.2 ⟨_, rfl⟩
    have hcomm : (g₀ : ModGL .G2 K) * pinnedX .G2 K g2c (σ s) =
        pinnedX .G2 K g2c (σ s) * g₀ := mem_centralizer_iff.1 (mem_inf.1 hmem).2 _ hg₀
    rw [hcomm, mul_inv_cancel_right] at h1
    have h2 : g2N (0 : K) 0 0 0 0 (σ s) = g2N 0 0 0 0 0 s := by
      rw [← pinnedX_c_eq_g2N, ← pinnedX_c_eq_g2N, h1]
    exact (g2N_injective h2).2.2.2.2.2
  obtain ⟨y, hy⟩ : α ∈
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range := by
    rw [← hker, MonoidHom.mem_ker, hΘ α g₀ σ hgσ, hσ]
  have hle : g2TorusR K ⊔ L ≤ centralizer {(y : ModGL .G2 K)} := by
    have key : ∀ x : ↥(adjointGroup .G2 K), α x = x → (x : ModGL .G2 K) ∈
        centralizer {(y : ModGL .G2 K)} := by
      intro x hx
      rw [← hy, MulAut.conj_apply] at hx
      rw [mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val hx
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc (x : ModGL .G2 K) * y = (y : ModGL .G2 K) * x * (y : ModGL .G2 K)⁻¹ * y := by
            rw [h1]
        _ = y * x := by group
    refine sup_le (fun h hh => ?_) (fun l hl => ?_)
    · have hhC : h ∈ adjointGroup .G2 K := (g2TorusR_le_g2LongCent hh).1
      exact key ⟨h, hhC⟩ (hfixH ⟨h, hhC⟩ hh)
    · exact key ⟨l, hLC hl⟩ (hfixL ⟨l, hLC hl⟩ hl)
  have hy' : (y : ModGL .G2 K) ∈ g2Centralizer K ((g2TorusR K ⊔ L : Subgroup (ModGL .G2 K)) :
      Set (ModGL .G2 K)) :=
    mem_inf.2 ⟨y.2, mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 (hle hh)⟩
  have hodd : Odd (orderOf α) := by
    have h1 := RankTwoL3Even.odd_orderOf_of_mem hCodd hy'
    rw [Subgroup.orderOf_coe] at h1
    rw [← hy]
    exact h1.of_dvd_nat (orderOf_map_dvd _ y)
  exact RankTwoL3Even.eq_one_of_odd_of_pow_two hodd hα

end NoInv

section Hyp38

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)} {L : Subgroup (ModGL .G2 K)}

theorem isSylowOf_g2
    {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (h184 : G2Centr184) (hLC : L ≤ adjointGroup .G2 K) (hXcL : rootSubgroup .G2 K g2c ≤ L)
    (hCodd : Odd (Nat.card (g2Centralizer K ((g2TorusR K ⊔ L : Subgroup (ModGL .G2 K)) :
      Set (ModGL .G2 K))))) (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {Q L₀ : Subgroup G} (hQA : Q ≤ A) (hL₀A : L₀ ≤ A)
    (hQ : ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ g2TorusR K →
      ∃ w ∈ Q, ∃ hwN : w ∈ normalizer (A : Set G), ψ ⟨w, hwN⟩ = MulAut.conj y)
    (hL₀ : ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ L →
      ∃ l ∈ L₀, ∃ hlN : l ∈ normalizer (A : Set G), ψ ⟨l, hlN⟩ = MulAut.conj y) :
    IsSylowOf 2 R (centralizer (Q : Set G) ⊓ centralizer (L₀ : Set G) ⊓
      normalizer (R : Set G)) := by
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAR : A ≤ centralizer (R : Set G) := le_centralizer_iff.1 hR.le
  have hRH : R ≤ centralizer (Q : Set G) ⊓ centralizer (L₀ : Set G) ⊓ normalizer (R : Set G) :=
    le_inf (le_inf (le_centralizer_iff.2 (hQA.trans hAR)) (le_centralizer_iff.2 (hL₀A.trans hAR)))
      (Subgroup.le_normalizer)
  obtain ⟨S, hS, hRS⟩ := AS76b.exists_isSylowOf_le hRH hR.isPGroup
  have hNA : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
    have h := Lemma36.normalizer_le hA hR 1
    rwa [rightConjugate_one, rightConjugate_one] at h
  have hfix : ∀ s (hsN : s ∈ normalizer (A : Set G)) (w : G) (hwN : w ∈ normalizer (A : Set G))
      (y : ↥(adjointGroup .G2 K)), w * s = s * w → ψ ⟨w, hwN⟩ = MulAut.conj y →
        ψ ⟨s, hsN⟩ y = y := by
    intro s hsN w hwN y hsw hwψ
    have h1 := congrArg ψ (Subtype.ext hsw :
      (⟨w * s, mul_mem hwN hsN⟩ : normalizer (A : Set G)) = ⟨s * w, mul_mem hsN hwN⟩)
    rw [psi_mul hwN hsN, psi_mul hsN hwN, hwψ] at h1
    apply hinj
    rw [RankTwoHypIIY.conj_apply_eq_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
  have hSK : S ≤ centralizer (A : Set G) := by
    intro s hs
    obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hsH := hS.le hs
    have hsQ := (mem_inf.1 (mem_inf.1 hsH).1).1
    have hsL := (mem_inf.1 (mem_inf.1 hsH).1).2
    have hsN := hNA (mem_inf.1 hsH).2
    refine (hψ.eq_one_iff ⟨s, hsN⟩).1 (eq_one_of_fix_g2 hm hK h184 hLC hXcL hCodd (k := k) ?_
      (fun y hy => ?_) (fun y hy => ?_))
    · rw [← psi_pow hsN]
      have h1 : (⟨s ^ 2 ^ k, pow_mem hsN _⟩ : normalizer (A : Set G)) = 1 := Subtype.ext hk'
      rw [h1, map_one]
    · obtain ⟨w, hw, hwN, hwψ⟩ := hQ y hy
      exact hfix s hsN w hwN y (mem_centralizer_iff.1 hsQ w hw) hwψ
    · obtain ⟨l, hl, hlN, hlψ⟩ := hL₀ y hy
      exact hfix s hsN l hlN y (mem_centralizer_iff.1 hsL l hl) hlψ
  have hSR := hR.eq_of_le hRS hSK hS.isPGroup
  subst hSR
  exact hS

theorem g2_not_conj_le
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184)
    (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hLinv : ∀ x ∈ L, x ^ 2 = 1 → x ≠ 1 →
      ∃ h ∈ adjointGroup .G2 K, h * x * h⁻¹ = pinnedX .G2 K g2c 1) (c : G) :
    ¬ R.map (MulAut.conj c).toMonoidHom ≤ leviLift ψ (g2Inn K L) := by
  intro hle
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hRc : R.map (MulAut.conj c).toMonoidHom = rightConjugate R c⁻¹ := by
    rw [rightConjugate, inv_inv]
  rw [hRc] at hle
  have hLA : rightConjugate R c⁻¹ ≤ A := hle.trans leviLift_le
  have hsec : Sec3 A R (rightConjugate R c⁻¹) c⁻¹ := by
    refine ⟨hc.hyp, hc.sylowR, fun hcN => ?_,
      AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR c⁻¹,
      hLA.trans (le_centralizer_iff.1 hc.sylowR.le)⟩
    have hKc : rightConjugate (centralizer (A : Set G)) c⁻¹ = centralizer (A : Set G) :=
      (rightConjugate_eq_self_iff _ _).2 (by
        rw [normalizer_centralizer_eq hc.hyp.standard]
        exact hcN)
    obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      (isSylowOf_ne_bot_of_even (AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR c⁻¹)
        (by rw [rightConjugate_card]; exact (tightlyEmbedded_centralizer hc.hyp.standard).1))
    have hrK : r ∈ centralizer (A : Set G) := by
      have := map_mono (f := (MulAut.conj c⁻¹⁻¹).toMonoidHom) hc.sylowR.le hr
      rwa [← rightConjugate, hKc] at this
    have hr2 : r ^ 2 ^ 1 = 1 := by
      have h1 := (mem_rightConjugate_iff R c⁻¹ r).1 hr
      have h2 := (hc.elemR h32).2 _ h1
      rw [pow_one]
      calc r ^ 2 = c * (c⁻¹ * r * c⁻¹⁻¹) ^ 2 * c⁻¹ := by rw [inv_inv, sq, sq]; group
        _ = 1 := by rw [h2, mul_one, mul_inv_cancel]
    exact hr1 (Subtype.ext (RankTwoL3Even.eq_one_of_odd_of_pow_two
      (RankTwoL3Even.odd_orderOf_of_mem hZA' (mem_inf.2 ⟨hLA hr, hrK⟩)) hr2))
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hsec.T_ne_bot
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrN := hsec.le_normalizer hr
  obtain ⟨x, hx⟩ := exists_psi_eq_conj hsec h32 h4 h34 hψ hr hrN
  have hxL : (x : ModGL .G2 K) ∈ L := by
    have h1 : ψ ⟨r, hrN⟩ ∈ g2Inn K L := psi_mem_of_mem_leviLift (hle hr)
    rw [hx] at h1
    exact coe_mem_of_conj_mem_g2Inn h1
  have hx2 := sq_eq_one_of_psi_eq_conj hZ hsec h32 hr hrN hx
  have hx1 := ne_one_of_psi_eq_conj hsec h32 hψ hr hr1' hrN hx
  obtain ⟨h, hhC, hhx⟩ := hLinv _ hxL (by simpa using congrArg Subtype.val hx2)
    (fun h1 => hx1 (Subtype.ext h1))
  have hconj : IsConj x ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ :=
    isConj_iff.2 ⟨⟨h, hhC⟩, Subtype.ext hhx⟩
  obtain ⟨a, ha, t, ht, ht1, htN, hψt⟩ := exists_conj_psi_eq hψ hr hr1' hrN hx hconj
  obtain ⟨hperf, hcent⟩ := h184 K hK4
  have hsec' := sec3_conj hsec ha
  have hbot := g2_inf_eq_bot_of_long h4 h32 h184 hsec' hOut hZA hK4 hψ
    (actsIn_of_perfect h4 h32 h34 hsec' hOut hψ ht ht1 htN hψt inf_le_left hperf inf_le_right
      fun y hy _ => hcent ▸ hy)
  have htA : t ∈ A := by
    have h1 := hLA ((mem_rightConjugate_iff _ a t).1 ht)
    have h2 : t = a⁻¹ * (a * t * a⁻¹) * a := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem ha) h1) ha
  have h3 : t ∈ rightConjugate (rightConjugate R c⁻¹) a ⊓ A := mem_inf.2 ⟨ht, htA⟩
  rw [hbot, mem_bot] at h3
  exact ht1 h3

end Hyp38

section NotLe

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)} {L : Subgroup (ModGL .G2 K)}

omit [Finite G] [CharP K 2] in
theorem odd_orderOf_of_psi_mem
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hZA : Odd (Nat.card (center A))) {S : Subgroup (ModGL .G2 K)} (hS : Odd (Nat.card S))
    {w : G} (hwA : w ∈ A) (hw : ψ ⟨w, le_normalizer hwA⟩ ∈ g2Inn K S) : Odd (orderOf w) := by
  obtain ⟨y, hyS, hy⟩ := mem_g2Inn.1 hw
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hyo : Odd (orderOf (y : ModGL .G2 K)) := RankTwoL3Even.odd_orderOf_of_mem hS hyS
  rw [Subgroup.orderOf_coe] at hyo
  set n := orderOf y
  have hwn : w ^ n ∈ A ⊓ centralizer (A : Set G) := by
    refine mem_inf.2 ⟨pow_mem hwA n, (hψ.eq_one_iff ⟨w ^ n, le_normalizer (pow_mem hwA n)⟩).1 ?_⟩
    rw [psi_pow (le_normalizer hwA), ← hy, ← map_pow, pow_orderOf_eq_one, map_one]
  have hz := RankTwoL3Even.odd_orderOf_of_mem hZA' hwn
  have h1 : w ^ (n * orderOf (w ^ n)) = 1 := by rw [pow_mul, pow_orderOf_eq_one]
  exact (hyo.mul hz).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

omit [Finite K] [CharP K 2] in
theorem odd_card_g2TorusR
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 1 ≤ m) :
    Odd (Nat.card (g2TorusR K)) := by
  have h1 := Subgroup.card_range_dvd (LieType.Chevalley.torusEltHom .G2 K g2ir)
  rw [Nat.card_units, hK] at h1
  refine Odd.of_dvd_nat ?_ h1
  have h2 : Even (2 ^ m) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one

theorem g2Q_ne_bot
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184)
    (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) : g2Q ψ T ≠ ⊥ := by
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZ
  have h1 : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨t, ht⟩ := exists_ne (1 : Kˣ)
  have hy1 : torusElt .G2 K g2ir t ≠ 1 := by
    intro h2
    have h3 := torus_r_v t (1 : K)
    rw [h2, one_mul, inv_one, mul_one, mul_one] at h3
    have h5 : g2N (0 : K) 0 0 1 0 0 = g2N 0 0 0 (t : K) 0 0 := by
      rw [← pinnedX_v_eq_g2N, ← pinnedX_v_eq_g2N, h3]
    exact ht (Units.ext (g2N_injective h5).2.2.2.1.symm)
  obtain ⟨w, hw, hwψ⟩ := exists_mem_g2Q h4 h32 h184 hK4 hc hψ hT
    (y := ⟨_, torusElt_mem_adjointGroup g2ir t⟩) (⟨t, rfl⟩ : torusElt .G2 K g2ir t ∈ g2TorusR K)
  intro hbot
  have hw1 : w = 1 := by
    have := hw
    rw [hbot, mem_bot] at this
    exact this
  subst hw1
  have h6 : ψ (1 : normalizer (A : Set G)) =
      MulAut.conj (⟨_, torusElt_mem_adjointGroup g2ir t⟩ : ↥(adjointGroup .G2 K)) := hwψ
  rw [map_one, ← map_one (MulAut.conj : ↥(adjointGroup .G2 K) →* _)] at h6
  exact hy1 (congrArg Subtype.val (hinj h6)).symm

theorem g2_not_le_normalizer
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (htc : G2TorusConj) (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) (hRp : G2Pinned ψ (rightConjugate R g⁻¹) g2c)
    (hR : ActsIn ψ (rightConjugate R g⁻¹) (rootSubgroup .G2 K g2c))
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 1 ≤ m) (hLC : L ≤ adjointGroup .G2 K)
    (hLperf : ⁅L, L⁆ = L) (hLH : L ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)))
    (hXcL : rootSubgroup .G2 K g2c ≤ L) (hLZ : Odd (Nat.card (center ↥L))) :
    ¬ centralizer (g2Q ψ T : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G) := by
  intro hle
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZ
  obtain ⟨hperf, hcent⟩ := h184 K hK4
  have hsw := hc.swap
  have hX : CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) = rightConjugate
      (CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G))) g := by
    rw [hc.perfectCore_eq h32 h4 h34 hOut, RankTwoClassical.rightConjugate_perfectCore,
      RankTwoClassical.rightConjugate_inf, ← AS76b.centralizer_rightConjugate,
      RankTwoClassical.rightConjugate_inv_rightConjugate]
  have hM₁ : ∀ x ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)),
      g * x * g⁻¹ ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G)) :=
    fun x hx => by
      rw [hX, mem_rightConjugate_iff] at hx
      exact hx
  have hM₁' : ∀ x ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G)),
      g⁻¹ * x * g ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) := fun x hx => by
    rw [hX, mem_rightConjugate_iff]
    simpa [mul_assoc] using hx
  have hMA : ∀ x ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)), x ∈ A :=
    fun x hx => (mem_inf.1 (CFSG.Quasithin.perfectCore_le _ hx)).1
  have hM₁A : ∀ x ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G)),
      x ∈ A := fun x hx => (mem_inf.1 (CFSG.Quasithin.perfectCore_le _ hx)).1
  have hMAg : ∀ x ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)),
      x ∈ rightConjugate A g := fun x hx => (mem_rightConjugate_iff A g x).2 (hM₁A _ (hM₁ x hx))
  have hMT := leviLift_g2LongCent_le h4 h32 h184 hK4 hc hψ hT
  have hMR := leviLift_g2LongCent_le h4 h32 h184 hK4 hsw hψ hR
  have hH : g2TorusR K ≤ adjointGroup .G2 K := fun _ h => (g2TorusR_le_g2LongCent h).1
  have hQodd : ∀ w ∈ g2Q ψ T, Odd (orderOf w) := fun w hw =>
    odd_orderOf_of_psi_mem hψ hZA (odd_card_g2TorusR hK hm) (g2Q_le hw) (psi_mem_of_mem_g2Q hw)
  have key : ∀ x ∈ A, Odd (orderOf x) →
      (∀ y ∈ leviLift ψ (g2Inn K (g2LongCent K)), x * y = y * x) →
        x ∈ centralizer (A : Set G) := by
    intro x hxA hxo hxc
    obtain ⟨z, hz⟩ := hψ.map_mem x hxA
    have hzC : (z : ModGL .G2 K) ∈ g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) := by
      refine mem_inf.2 ⟨z.2, mem_centralizer_iff.2 fun d hd => ?_⟩
      have hdC : d ∈ adjointGroup .G2 K := (mem_inf.1 hd).1
      obtain ⟨l, hl, hlψ⟩ := exists_mem_leviLift hψ (g2Inn_le_range _)
        (commutator_g2Inn inf_le_left hperf) (conj_mem_g2Inn (y := ⟨d, hdC⟩) hd)
      have hlN := le_normalizer (leviLift_le hl)
      have hxN := le_normalizer hxA
      have h1 := congrArg ψ (Subtype.ext (hxc l hl) :
        (⟨x * l, mul_mem hxN hlN⟩ : normalizer (A : Set G)) = ⟨l * x, mul_mem hlN hxN⟩)
      rw [psi_mul hxN hlN, psi_mul hlN hxN, ← hz, hlψ, ← map_mul, ← map_mul] at h1
      exact (congrArg Subtype.val (hinj h1)).symm
    rw [hcent] at hzC
    obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hzC
    have hz2 : z ^ 2 ^ 1 = 1 := by
      apply Subtype.ext
      rw [pow_one, SubgroupClass.coe_pow, ← hs, sq, pinnedX_mul_self]
      rfl
    have hzo : Odd (orderOf z) := by
      rw [← orderOf_injective _ hinj z, hz]
      refine hxo.of_dvd_nat ?_
      have h1 := orderOf_map_dvd ψ ⟨x, le_normalizer hxA⟩
      rwa [Subgroup.orderOf_mk] at h1
    have hz1 := RankTwoL3Even.eq_one_of_odd_of_pow_two hzo hz2
    refine (hψ.eq_one_iff ⟨x, le_normalizer hxA⟩).1 ?_
    rw [← hz, hz1, map_one]
  have hQ₁A : ∀ w ∈ g2Q ψ T, g * w * g⁻¹ ∈ A := fun w hw => hM₁A _ (hM₁ w (mem_inf.1 hw).1)
  have hker : ∀ w ∈ g2Q ψ T,
      w ∈ centralizer (A : Set G) ↔ g * w * g⁻¹ ∈ centralizer (A : Set G) := by
    intro w hw
    constructor
    · intro hwK
      refine key _ (hQ₁A w hw) ?_ fun y hy => ?_
      · rw [show g * w * g⁻¹ = MulAut.conj g w from rfl, MulEquiv.orderOf_eq]
        exact hQodd w hw
      · have hy' : g⁻¹ * y * g ∈ A := hMA _ (hM₁' y (hMR hy))
        have h1 : g⁻¹ * y * g * w = w * (g⁻¹ * y * g) := mem_centralizer_iff.1 hwK _ hy'
        calc g * w * g⁻¹ * y = g * (w * (g⁻¹ * y * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * y * g * w) * g⁻¹ := by rw [h1]
          _ = y * (g * w * g⁻¹) := by group
    · intro hwK
      have hwKg : w ∈ centralizer (rightConjugate A g : Set G) :=
        (RankTwoL3Even.mem_centralizer_rightConjugate_iff A g w).2 hwK
      exact key w (g2Q_le hw) (hQodd w hw) fun y hy =>
        (mem_centralizer_iff.1 hwKg y (hMAg y (hMT hy))).symm
  let f₁ : ↥(g2Q ψ T) →* MulAut ↥(adjointGroup .G2 K) :=
    ψ.comp (inclusion ((g2Q_le (ψ := ψ) (T := T)).trans le_normalizer))
  let φ : ↥(g2Q ψ T) →* normalizer (A : Set G) :=
    { toFun := fun w => ⟨g * w * g⁻¹, le_normalizer (hQ₁A w w.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change g * (x * y : G) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)
        group) }
  let f₂ := ψ.comp φ
  have hkereq : f₁.ker = f₂.ker := by
    ext w
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change ψ ⟨w, _⟩ = 1 ↔ ψ ⟨g * w * g⁻¹, _⟩ = 1
    rw [hψ.eq_one_iff, hψ.eq_one_iff]
    exact hker w w.2
  have hcard : Nat.card f₁.range = Nat.card f₂.range := by
    rw [← Subgroup.index_ker, ← Subgroup.index_ker, hkereq]
  have hrange₁ : f₁.range = g2Inn K (g2TorusR K) := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact psi_mem_of_mem_g2Q w.2
    · intro φ' hφ'
      obtain ⟨y, hy, rfl⟩ := mem_g2Inn.1 hφ'
      obtain ⟨w, hw, hwψ⟩ := exists_mem_g2Q h4 h32 h184 hK4 hc hψ hT hy
      exact ⟨⟨w, hw⟩, hwψ⟩
  have hcardS : Nat.card f₂.range = Nat.card (g2TorusR K) := by
    rw [← hcard, hrange₁]
    exact Nat.card_congr (g2InnEquiv hH).toEquiv.symm
  obtain ⟨r₁, hr₁, -, hr₁N, y₀, hy₀, hψr₁⟩ := hRp
  have hf₂X : f₂.range ≤
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range := by
    rintro _ ⟨w, rfl⟩
    exact hψ.map_mem _ (hQ₁A w w.2)
  have hS'le : (f₂.range.comap (MulAut.conj : ↥(adjointGroup .G2 K) →*
      MulAut ↥(adjointGroup .G2 K))).map (adjointGroup .G2 K).subtype ≤ g2LongCent K := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hwy⟩ := mem_comap.1 hy
    refine mem_inf.2 ⟨y.2, mem_centralizer_singleton_iff.2 ?_⟩
    have hwM := hM₁ w (mem_inf.1 w.2).1
    have hwr : g * w * g⁻¹ * r₁ = r₁ * (g * w * g⁻¹) :=
      (mem_centralizer_iff.1 (mem_inf.1 (CFSG.Quasithin.perfectCore_le _ hwM)).2 r₁ hr₁).symm
    have hwN := le_normalizer (hQ₁A w w.2)
    have h1 := congrArg ψ (Subtype.ext hwr :
      (⟨_, mul_mem hwN hr₁N⟩ : normalizer (A : Set G)) = ⟨_, mul_mem hr₁N hwN⟩)
    rw [psi_mul hwN hr₁N, psi_mul hr₁N hwN, hψr₁,
      show ψ ⟨g * w * g⁻¹, hwN⟩ = MulAut.conj y from hwy, ← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val (hinj h1)
    simp only [Subgroup.coe_mul] at h2
    rw [hy₀] at h2
    exact h2
  have hS'card : Nat.card ((f₂.range.comap (MulAut.conj : ↥(adjointGroup .G2 K) →*
      MulAut ↥(adjointGroup .G2 K))).map (adjointGroup .G2 K).subtype) =
        Nat.card (g2TorusR K) := by
    rw [card_map_of_injective (adjointGroup .G2 K).subtype_injective, ← hcardS,
      ← card_map_of_injective hinj, map_comap_eq_self hf₂X]
  obtain ⟨h, hh, hS'eq⟩ := htc K hK4 _ hS'le hS'card
  have hhC : h ∈ adjointGroup .G2 K := (mem_inf.1 hh).1
  have hD₀C : L.map (MulAut.conj h).toMonoidHom ≤ adjointGroup .G2 K := by
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem hhC (hLC hl)) (inv_mem hhC)
  have hD₀perf : ⁅L.map (MulAut.conj h).toMonoidHom, L.map (MulAut.conj h).toMonoidHom⁆ =
      L.map (MulAut.conj h).toMonoidHom := by
    rw [← map_commutator, hLperf]
  have hhX : ∀ x ∈ rootSubgroup .G2 K g2c, h * x * h⁻¹ = x := by
    intro x hx
    have hxC : x ∈ g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) := by
      rw [hcent]
      exact hx
    have h1 : h * x = x * h := mem_centralizer_iff.1 (mem_inf.1 hxC).2 h hh
    rw [h1, mul_inv_cancel_right]
  have hXcD₀ : rootSubgroup .G2 K g2c ≤ L.map (MulAut.conj h).toMonoidHom :=
    fun x hx => ⟨x, hXcL hx, hhX x hx⟩
  have hD₀S : ∀ s ∈ (f₂.range.comap (MulAut.conj : ↥(adjointGroup .G2 K) →*
      MulAut ↥(adjointGroup .G2 K))).map (adjointGroup .G2 K).subtype,
      ∀ d ∈ L.map (MulAut.conj h).toMonoidHom, s * d = d * s := by
    intro s hs d hd
    rw [hS'eq] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    obtain ⟨l, hl, rfl⟩ := hd
    have h1 : k * l = l * k := mem_centralizer_iff.1 (hLH hl) k hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * k * h⁻¹ * (h * l * h⁻¹) = h * (k * l) * h⁻¹ := by group
      _ = h * (l * k) * h⁻¹ := by rw [h1]
      _ = h * l * h⁻¹ * (h * k * h⁻¹) := by group
  have hP₁ := commutator_g2Inn hD₀C hD₀perf
  have hL₁Q : ∀ w ∈ g2Q ψ T, ∀ l ∈ leviLift ψ (g2Inn K (L.map (MulAut.conj h).toMonoidHom)),
      l * (g * w * g⁻¹) = g * w * g⁻¹ * l := by
    intro w hw l hl
    refine mem_centralizer_singleton_iff.1 (leviLift_le_centralizer hψ
      (le_normalizer (hQ₁A w hw)) (fun s hs => ?_) hl)
    obtain ⟨d, hd, rfl⟩ := mem_g2Inn.1 hs
    obtain ⟨y, hyr⟩ := hψ.map_mem _ (hQ₁A w hw)
    have hyS : (y : ModGL .G2 K) ∈ (f₂.range.comap (MulAut.conj : ↥(adjointGroup .G2 K) →*
        MulAut ↥(adjointGroup .G2 K))).map (adjointGroup .G2 K).subtype :=
      ⟨y, mem_comap.2 (by rw [hyr]; exact ⟨⟨w, hw⟩, rfl⟩), rfl⟩
    rw [← hyr, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD₀S _ hyS _ hd)
  have hL₁N : ∀ l ∈ leviLift ψ (g2Inn K (L.map (MulAut.conj h).toMonoidHom)),
      l ∈ normalizer (rightConjugate R g⁻¹ : Set G) := by
    intro l hl
    have hlA : l ∈ A := leviLift_le hl
    have h1 : g⁻¹ * l * g ∈ centralizer (g2Q ψ T : Set G) ⊓ centralizer (T : Set G) := by
      refine mem_inf.2 ⟨mem_centralizer_iff.2 fun w hw => ?_, mem_centralizer_iff.2 fun t ht => ?_⟩
      · have h2 := hL₁Q w hw l hl
        calc w * (g⁻¹ * l * g) = g⁻¹ * (g * w * g⁻¹ * l) * g := by group
          _ = g⁻¹ * (l * (g * w * g⁻¹)) * g := by rw [h2]
          _ = g⁻¹ * l * g * w := by group
      · have hgt : g * t * g⁻¹ ∈ centralizer (A : Set G) :=
          hsw.sylowR.le (conj_mem_rightConjugate_inv ht g)
        have h2 : g * t * g⁻¹ * l = l * (g * t * g⁻¹) := (mem_centralizer_iff.1 hgt l hlA).symm
        calc t * (g⁻¹ * l * g) = g⁻¹ * (g * t * g⁻¹ * l) * g := by group
          _ = g⁻¹ * (l * (g * t * g⁻¹)) * g := by rw [h2]
          _ = g⁻¹ * l * g * t := by group
    rw [AS76b.mem_normalizer_rightConjugate_iff, inv_inv]
    exact hle h1
  have hR₁L₁ : ∀ r ∈ rightConjugate R g⁻¹,
      r ∈ normalizer (leviLift ψ (g2Inn K (L.map (MulAut.conj h).toMonoidHom)) : Set G) := by
    intro r hr
    have hrN := hsw.le_normalizer hr
    obtain ⟨y, hy⟩ := exists_psi_eq_conj hsw h32 h4 h34 hψ hr hrN
    refine mem_normalizer_leviLift hrN ?_
    rw [hy]
    exact conj_mem_normalizer_g2Inn (le_normalizer (hXcD₀ (hR r hr hrN y hy)))
  have hR₁A := g2_inf_eq_bot_of_long h4 h32 h184 hsw hOut hZA hK4 hψ hR
  have hL₁R₁ : ∀ l ∈ leviLift ψ (g2Inn K (L.map (MulAut.conj h).toMonoidHom)),
      ∀ r ∈ rightConjugate R g⁻¹, l * r = r * l := by
    intro l hl r hr
    have hlA : l ∈ A := leviLift_le hl
    have h1 : l * r * l⁻¹ * r⁻¹ ∈ rightConjugate R g⁻¹ :=
      mul_mem ((mem_normalizer_iff.1 (hL₁N l hl) r).1 hr) (inv_mem hr)
    have h2 : l * r * l⁻¹ * r⁻¹ ∈ A := by
      have h3 := (mem_normalizer_iff.1 (hR₁L₁ r hr) _).1 (inv_mem hl)
      have he : l * r * l⁻¹ * r⁻¹ = l * (r * l⁻¹ * r⁻¹) := by group
      rw [he]
      exact mul_mem hlA (leviLift_le h3)
    have h5 : l * r * l⁻¹ * r⁻¹ ∈ rightConjugate R g⁻¹ ⊓ A := mem_inf.2 ⟨h1, h2⟩
    rw [hR₁A, mem_bot] at h5
    calc l * r = l * r * l⁻¹ * r⁻¹ * (r * l) := by group
      _ = r * l := by rw [h5, one_mul]
  have hX1L : pinnedX .G2 K g2c 1 ∈ L := hXcL (mem_rootSubgroup.2 ⟨1, rfl⟩)
  have hZL : (⟨pinnedX .G2 K g2c 1, hX1L⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro l
    apply Subtype.ext
    have hdC : (h * l * h⁻¹ : ModGL .G2 K) ∈ adjointGroup .G2 K := hD₀C ⟨l, l.2, rfl⟩
    obtain ⟨l₁, hl₁, hl₁ψ⟩ := exists_mem_leviLift hψ (g2Inn_le_range _) hP₁
      (conj_mem_g2Inn (y := ⟨_, hdC⟩) ⟨l, l.2, rfl⟩)
    have hl₁N := le_normalizer (leviLift_le hl₁)
    have h1 := congrArg ψ (Subtype.ext (hL₁R₁ l₁ hl₁ r₁ hr₁) :
      (⟨l₁ * r₁, mul_mem hl₁N hr₁N⟩ : normalizer (A : Set G)) = ⟨r₁ * l₁, mul_mem hr₁N hl₁N⟩)
    rw [psi_mul hl₁N hr₁N, psi_mul hr₁N hl₁N, hl₁ψ, hψr₁, ← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val (hinj h1)
    simp only [Subgroup.coe_mul] at h2
    rw [hy₀] at h2
    have hXh : h * pinnedX .G2 K g2c 1 * h⁻¹ = pinnedX .G2 K g2c 1 :=
      hhX _ (mem_rootSubgroup.2 ⟨1, rfl⟩)
    show (l : ModGL .G2 K) * pinnedX .G2 K g2c 1 = pinnedX .G2 K g2c 1 * l
    calc (l : ModGL .G2 K) * pinnedX .G2 K g2c 1 =
        h⁻¹ * ((h * l * h⁻¹) * (h * pinnedX .G2 K g2c 1 * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * l * h⁻¹) * pinnedX .G2 K g2c 1) * h := by rw [hXh]
      _ = h⁻¹ * (pinnedX .G2 K g2c 1 * (h * l * h⁻¹)) * h := by rw [h2]
      _ = h⁻¹ * ((h * pinnedX .G2 K g2c 1 * h⁻¹) * (h * l * h⁻¹)) * h := by rw [hXh]
      _ = pinnedX .G2 K g2c 1 * l := by group
  have hX2 : (⟨pinnedX .G2 K g2c 1, hX1L⟩ : ↥L) ^ 2 ^ 1 = 1 := by
    apply Subtype.ext
    simp only [pow_one, OneMemClass.coe_one, sq]
    exact pinnedX_mul_self g2c 1
  have hX1 := RankTwoL3Even.eq_one_of_odd_of_pow_two (RankTwoL3Even.odd_orderOf_of_mem hLZ hZL) hX2
  have hX1' : pinnedX .G2 K g2c (1 : K) = 1 := congrArg Subtype.val hX1
  have h6 : g2N (0 : K) 0 0 0 0 1 = g2N 0 0 0 0 0 0 := by
    rw [← pinnedX_c_eq_g2N, hX1', g2N_zero]
  exact one_ne_zero (g2N_injective h6).2.2.2.2.2

end NotLe

section Config

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

theorem g2_config814_of_longLong
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (h187 : G2Levi187) (htc : G2TorusConj) {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m)
    (e : RankTwoStandard.rankTwoQuot A ≃* Blueprint.AdjointQuotient .G2 K) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) (hRp : G2Pinned ψ (rightConjugate R g⁻¹) g2c)
    (hR : ActsIn ψ (rightConjugate R g⁻¹) (rootSubgroup .G2 K g2c)) :
    Config814 (ExcModel.g2 m hm K hK e) g R T (g2Q ψ T) := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨L, hLC, hXcL, hLperf, hLH, hCdec, hLZ, hLt, hCodd, hLinv, -⟩ := h187 K m hK hm
  have hLq : CFSG.Open.IsQuasisimple ↥L := by
    split_ifs at hLt
    · exact open_isQuasisimple_of_psl hLperf hLt
    · exact open_isQuasisimple_of_psl hLperf hLt
  have hlay := g2_layerCentralizer_eq h4 h32 h184 hK4 hc hψ hT hLC hLperf hLH hCdec hLq
  have hTA := g2_inf_eq_bot_of_long h4 h32 h184 hc hOut hZA hK4 hψ hT
  refine ⟨hc.not_mem, hc.sylowR, hc.sylowT, hc.le_normalizer,
    (commutator_eq_bot_iff_le_centralizer).2 hc.le_centralizer, ?_, g2Q_le,
    g2Q_ne_bot h4 h32 h184 hK4 hc hψ hT, ?_, ?_, ?_, ?_, ?_, ?_,
    g2_not_le_normalizer h4 h32 h184 htc hK4 hc hOut hZA hψ hT hRp hR hK (by omega) hLC hLperf
      hLH hXcL hLZ, ?_, fun h => h.elim⟩
  · show 2 < 2 ^ m
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · rw [hlay]
    exact isQuasisimple_leviLift_of_open hψ (g2Inn_le_range L) (commutator_g2Inn hLC hLperf)
      (isQuasisimple_of_equiv (g2InnEquiv hLC) hLq)
  · rw [hlay]
    exact odd_card_center_leviLift_g2 hψ hZA hLC hLperf hLZ
  · simp only [ExcModel.LeviType]
    rw [hlay]
    split_ifs at hLt ⊢ <;> exact levi_type_g2 hψ hLC hLperf hLt
  · rw [hlay]
    refine isSylowOf_g2 hm hK h184 hLC hXcL hCodd hc.hyp hc.sylowR hψ g2Q_le leviLift_le
      (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨w, hw, hwψ⟩ := exists_mem_g2Q h4 h32 h184 hK4 hc hψ hT hy
      exact ⟨w, hw, _, hwψ⟩
    · obtain ⟨l, hl, hlψ⟩ := exists_mem_leviLift hψ (g2Inn_le_range L)
        (commutator_g2Inn hLC hLperf) (conj_mem_g2Inn hy)
      exact ⟨l, hl, _, hlψ⟩
  · rw [hlay]
    exact le_sup_leviLift_g2 h4 h32 h34 hc hψ hT hZA hLC hLperf hXcL
  · rw [hlay, eq_bot_iff, ← hTA]
    exact inf_le_inf_left T leviLift_le
  · intro n _ _ c
    rw [hlay]
    exact g2_not_conj_le h4 h32 h184 hK4 hc hOut hZA hψ hLinv c

end Config

end CFSG.ComponentClassification.RankTwoExceptional
