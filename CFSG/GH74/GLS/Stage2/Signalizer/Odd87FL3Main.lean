module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Inner
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CellField
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GField
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphOrth
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Char
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3S4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4Kill

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps CFSG.GH74.GLS.Bg CFSG.Blueprint
open scoped commutatorElement

theorem normalizer_of_layerAut_fixed {A : Type} [Group A] [Finite A] {zb : A} {p : ℕ} {X : Subgroup A}
    (hd : CellData zb p X) {j : ↥(layer A)} (hj : layerAut zb j = j) : (j : A) ∈ normalizer (X : Set A) := by
  have h1 := congrArg Subtype.val hj
  rw [coe_layerAut] at h1
  have hzi : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hd.z2
  rw [hzi] at h1
  refine hd.A4.inv (j : A) (Subgroup.mem_top _) (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  calc (j : A) * zb = (zb * (j : A) * zb) * zb := by rw [h1]
    _ = zb * j := by rw [mul_assoc (zb * (j : A)) _ _, hd.z2, mul_one]

theorem two_ne_zero_of_odd_card_fl3 {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := fun h2 => by
    have h' := (FiniteField.even_card_iff_char_two (F := F)).1 h2
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨k, hk⟩ := h
    omega
  exact Ring.two_ne_zero hF2

theorem fl3_main {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (hctx : Stage2Ctx G z k S) {H₀ : Subgroup G} {H₁ : Subgroup ↥H₀} [H₁.Normal]
    {hz : z ∈ H₀} {p : ℕ} {X : Subgroup (Sec H₀ H₁)} (hsig : Sig4B G z H₀ H₁ hz p X)
    (hyp : Hyp42 (zSec z H₀ hz H₁) X)
    (hF : FL3 (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁)))) :
    ∃ n : ℕ, 1 ≤ n ∧ LieModel ↥(layer (Sec H₀ H₁)) .PSL 3 p n ∧
      zSec z H₀ hz H₁ ∈ layer (Sec H₀ H₁) ⊔
        centralizer ((layer (Sec H₀ H₁) : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁)) ∧
      IsElementaryAbelian p ↥X ∧ Nat.card ↥X = p ^ (2 * n) ∧
      ∃ P : Subgroup (Sec H₀ H₁), IsMaxParabolicP p (layer (Sec H₀ H₁)) P ∧ X = Op p P ∧
        P = X ⊔ layer (Sec H₀ H₁) ⊓ centralizer ({zSec z H₀ hz H₁} : Set (Sec H₀ H₁)) := by
  classical
  have hd := CellData.of_ctx hctx hsig hyp
  obtain ⟨p0, f, hp0, hf, hp02, hL⟩ := hF
  obtain ⟨hZ, F, hFfield, hFfin, hcard, e, α, hαα, hαne, hcomm⟩ := fl3_frame hd hp02 hL
  have hp0f : Fact p0.Prime := ⟨hp0⟩
  have hpf : Fact p.Prime := ⟨hd.A4.prime⟩
  have hFodd : Odd (Nat.card F) := by rw [hcard]; exact (hp0.odd_of_ne_two hp02).pow
  have h3 : 3 ≤ Nat.card F := by
    rw [hcard]
    calc 3 ≤ p0 := by have := hp0.two_le; omega
      _ ≤ p0 ^ f := Nat.le_self_pow (by omega) p0
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card_fl3 hFodd
  rcases linear3_involution_cases h2 α hαα hαne with
    ⟨y, hy2, hy1, hαy⟩ | ⟨A', σ, hσ, hαeq⟩ | ⟨B, hB, hαeq⟩ | ⟨A', σ, hσ, hαeq⟩
  ·
    have hact : ∀ x, e (layerAut (zSec z H₀ hz H₁) x) = y * e x * y⁻¹ := fun x => by
      rw [hcomm, hαy]; rfl
    obtain ⟨e', hXK, hJ, hcomm', heq, hzbmem⟩ := fl3_inner_data hd hZ h2 e hy2 hy1 hact
    by_cases hpF : p ∣ Nat.card F
    · have hpp0 : p = p0 := by
        rw [hcard] at hpF
        exact (Nat.prime_dvd_prime_iff_eq hd.A4.prime hp0).1 (hd.A4.prime.dvd_of_dvd_pow hpF)
      obtain ⟨P, hP, hXP, hPeq, hel, hcardX⟩ :=
        fl3_inner_char (layer (Sec H₀ H₁)) hFodd h3 e' p hpF X hd.A4.pgroup hd.A4.ne_bot hXK hJ
      subst hpp0
      refine ⟨f, hf, ?_, hzbmem, hel, ?_, P, hP, hXP, ?_⟩
      · exact lieModel_of_mulEquiv
          ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hL
      · rw [hcardX, hcard]; ring
      · rw [hPeq, heq]
    · exact (fl3_inner_cross_false hFodd h3 e' hd.A4.odd hpF hd.A4.pgroup hd.A4.ne_bot hXK hJ hcomm').elim
  · exact (fl3_field_false hctx hsig hp0 hp02 hf hcard e α hcomm hαα A' σ hσ hαeq).elim
  ·
    exfalso
    have : (layer (Sec H₀ H₁)).Normal := layer_normal
    have hJ' : ∀ j : ↥(layer (Sec H₀ H₁)), layerAut (zSec z H₀ hz H₁) j = j →
        (j : Sec H₀ H₁) ∈ normalizer (X : Set (Sec H₀ H₁)) := fun j hj => normalizer_of_layerAut_fixed hd hj
    exact fl3_graph_false (K := layer (Sec H₀ H₁)) hFodd h3 e (layerAut (zSec z H₀ hz H₁)) B hB
      (fun x => by rw [hcomm, hαeq]) hd.A4.odd hd.A4.pgroup hd.A4.ne_bot
      hd.inf_centralizer_layer hJ'
  ·
    exfalso
    have hsq : (conjAut 3 F A' * fieldAut 3 F σ * dualAut 3 F) ^ 2 = 1 := by rw [← hαeq, sq]; exact hαα
    obtain ⟨e0, hf2, he1, Q, hQperf, hQfix, c, hc⟩ :=
      fl3_gfield_section hp0 hp02 hf hcard α hαα A' σ hσ hαeq
    have hKcard : Nat.card F = (p0 ^ e0) ^ 2 := by rw [hcard, hf2, mul_comm, pow_mul]
    by_cases h5 : 5 ≤ p0 ^ e0
    · have hker : e.toMonoidHom.ker ≤ center ↥(layer (Sec H₀ H₁)) := by
        rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
        exact bot_le
      have hQ : Group.IsPerfect ↥Q := hQperf
      have hCS : CentSection (zSec z H₀ hz H₁)
          (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p0 ^ e0) F)) :=
        centSection_of_fixed_perfect (π := e.toMonoidHom) e.surjective hker (α := α) hcomm Q hQfix c hc
      have hT : IsSimpleGroup
          (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p0 ^ e0) F)) :=
        isSimpleGroup_statedProj_three_odd hKcard (by omega)
      have hTp : Group.IsPerfect
          (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p0 ^ e0) F)) :=
        Group.IsPerfect.ofSurjective hc
      have : Nontrivial
          (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p0 ^ e0) F)) :=
        IsSimpleGroup.toNontrivial
      have hns : ¬ Group.IsSolvable
          (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p0 ^ e0) F)) :=
        Group.IsPerfect.not_isSolvable _
      have hKF := kindFactor_of_section_sec hctx hsig hns hCS.isSection
      have hcharF : CharP F p0 := by
        have := Fintype.ofFinite F
        exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
      exact not_kindFactor hp02 (involved_qdSL_statedProj_three hKcard)
        (not_card_dvd_factorial_statedProj_three_odd (by omega) hKcard (Nat.odd_iff.mp (hp0.odd_of_ne_two hp02).pow) h5) hKF
    ·
      have hq3 : p0 ^ e0 = 3 := by
        have h1 : 3 ≤ p0 ^ e0 := by
          calc 3 ≤ p0 := by have := hp0.two_le; omega
            _ ≤ p0 ^ e0 := Nat.le_self_pow (by omega) p0
        have hodd0 : (p0 ^ e0) % 2 = 1 := Nat.odd_iff.mp (hp0.odd_of_ne_two hp02).pow
        omega
      have hF9 : Nat.card F = 9 := by rw [hKcard, hq3]; norm_num
      obtain ⟨-, hσpow, H, hH⟩ :=
        odd_linear_graph_field_involution_conjugacy hp0 hf hcard (le_refl 3) A' σ hσ hsq
      have hσ3 : ∀ x, σ x = x ^ 3 := by
        intro x
        rw [hσpow, show f / 2 = e0 by omega, hq3]
      let e'' : ↥(layer (Sec H₀ H₁)) ≃* projectiveSL 3 F := e.trans (conjAut 3 F H)⁻¹
      have hcomm'' : ∀ x : ↥(layer (Sec H₀ H₁)), e'' (layerAut (zSec z H₀ hz H₁) x) =
          (fieldAut 3 F σ * dualAut 3 F) (e'' x) := by
        intro x
        change (conjAut 3 F H)⁻¹ (e (layerAut (zSec z H₀ hz H₁) x)) =
          (fieldAut 3 F σ * dualAut 3 F) ((conjAut 3 F H)⁻¹ (e x))
        rw [hcomm, hαeq, hH]
        simp [MulAut.mul_apply]
      have : (layer (Sec H₀ H₁)).Normal := layer_normal
      refine fl3_s4_false (layer (Sec H₀ H₁)) hF9 e'' hd.A4.odd hd.A4.pgroup hd.A4.ne_bot
        hd.inf_centralizer_layer (fun j hj => normalizer_of_layerAut_fixed hd ?_)
      have hfix := s4img_fixed_gf hF9 σ hσ3 (e'' j) hj
      apply e''.injective
      rw [hcomm'', hfix]

theorem cell87_FL3 : Cell87 FL3 := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hF
  obtain ⟨n, hn, hL, hzK, hel, hcardX, P, hP, hXP, hPeq⟩ := fl3_main hctx hsig hyp hF
  refine Or.inr (Or.inr (Or.inl ?_))
  first
    | exact ⟨n, hn, hL, P, hP, hXP⟩
    | exact ⟨n, hn, hL, hzK, hel, hcardX, P, hP, hXP, hPeq⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
