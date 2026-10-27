module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011P2Data
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Mod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec1011_p2_false [Finite G] (hB5 : Asc82FactB5) {L B' : Subgroup G} {c1 c2 : G}
    (hpsp : IsPSp43 L) (hd : Sec1011P2Data L B' c1 c2) (hBL : B' ≤ L) : False := by
  have hB'2 : IsPGroup 2 B' := IsPGroup.of_card (p := 2) (n := 4) hd.card
  obtain ⟨P', hP', hB'P'⟩ := exists_isSylow2Of_ge hB'2 hBL
  obtain ⟨B0, -, -, hunique, -, φ, hperm, -, -, hS5⟩ := hB5 G L hpsp P' hP'
  have hB'comm : IsMulCommutative B' :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hd.comm a a.2 b b.2)
  have hB0eq : B' = B0 := hunique B' hB'P' hB'comm hd.card
  subst B0
  obtain ⟨σ1, hact1⟩ := hS5 c1 ⟨hd.c1N, hd.c1B⟩
  obtain ⟨σ2, hact2⟩ := hS5 c2 ⟨hd.c2N, hd.c2B⟩
  have hmem : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → φ v ∈ B' :=
    fun v hv => (hperm.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
  have hcomm : σ1 * σ2 = σ2 * σ1 := by
    apply permVec_injective_five
    intro v hv
    have hv1 : IsEvenVec (permVec σ1 v) := isEvenVec_permVec σ1 hv
    have hv2 : IsEvenVec (permVec σ2 v) := isEvenVec_permVec σ2 hv
    have hcc := hd.cc (φ v) (hmem v hv)
    have e1 : c2 * (c1 * φ v * c1⁻¹) * c2⁻¹ = φ (permVec σ2 (permVec σ1 v)) := by
      rw [hact1 v hv]
      exact hact2 (permVec σ1 v) hv1
    have e3 : c1 * (c2 * φ v * c2⁻¹) * c1⁻¹ = φ (permVec σ1 (permVec σ2 v)) := by
      rw [hact2 v hv]
      exact hact1 (permVec σ2 v) hv2
    rw [e3, e1] at hcc
    have hφcomm := hperm.2.1 _ _ (isEvenVec_permVec σ1 hv2) (isEvenVec_permVec σ2 hv1) hcc
    simpa only [permVec_mul] using hφcomm
  have hcube : ∀ (c : G) (σ : Equiv.Perm (Fin 5)),
      (∀ v, IsEvenVec v → c * φ v * c⁻¹ = φ (permVec σ v)) →
      (∀ b ∈ B', c ^ 3 * b * (c ^ 3)⁻¹ = b) → σ ^ 3 = 1 := by
    intro c σ hact hc3
    apply permVec_injective_five
    intro v hv
    have hv1 : IsEvenVec (permVec σ v) := isEvenVec_permVec σ hv
    have hv2 : IsEvenVec (permVec σ (permVec σ v)) := isEvenVec_permVec σ hv1
    have e1 : c * φ v * c⁻¹ = φ (permVec σ v) := hact v hv
    have e2 : c * φ (permVec σ v) * c⁻¹ = φ (permVec σ (permVec σ v)) := hact _ hv1
    have e3 : c * φ (permVec σ (permVec σ v)) * c⁻¹
        = φ (permVec σ (permVec σ (permVec σ v))) := hact _ hv2
    have hc3pow : c ^ 3 = c * (c * c) := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
        show (2 : ℕ) = 1 + 1 by norm_num, pow_succ, pow_one, mul_assoc]
    have hσ3pow : σ ^ 3 = σ * (σ * σ) := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
        show (2 : ℕ) = 1 + 1 by norm_num, pow_succ, pow_one, mul_assoc]
    have hact3 : c ^ 3 * φ v * (c ^ 3)⁻¹ = φ (permVec (σ ^ 3) v) := by
      rw [hc3pow, hσ3pow, permVec_mul, permVec_mul]
      rw [show (c * (c * c)) * φ v * (c * (c * c))⁻¹
          = c * (c * (c * φ v * c⁻¹) * c⁻¹) * c⁻¹ by group]
      rw [e1, e2, e3]
    have hfix : φ (permVec (σ ^ 3) v) = φ v := by
      rw [← hact3]
      exact hc3 (φ v) (hmem v hv)
    have hvec : permVec (σ ^ 3) v = v :=
      hperm.2.1 _ _ (isEvenVec_permVec (σ ^ 3) hv) hv hfix
    rw [hvec, permVec_one]
  have h1 : σ1 ^ 3 = 1 := hcube c1 σ1 hact1 hd.cube1
  have h2 : σ2 ^ 3 = 1 := hcube c2 σ2 hact2 hd.cube2
  obtain ⟨b1, hb1, b2, hb2, hspan⟩ :=
    hd.span (φ (sec1011_wfour 0)) (hmem _ (sec1011_wfour_even 0))
  obtain ⟨w1, hw1, hw1eq⟩ := (hperm.2.2.1 b1).mp hb1
  obtain ⟨w2, hw2, hw2eq⟩ := (hperm.2.2.1 b2).mp hb2
  have hsum1 : IsEvenVec (w1 + permVec σ1 w1) :=
    sec1011_isEvenVec_add hw1 (isEvenVec_permVec σ1 hw1)
  have hsum2 : IsEvenVec (w2 + permVec σ2 w2) :=
    sec1011_isEvenVec_add hw2 (isEvenVec_permVec σ2 hw2)
  have hadd1 : φ (w1 + permVec σ1 w1) = φ w1 * φ (permVec σ1 w1) :=
    hperm.1 w1 (permVec σ1 w1) hw1 (isEvenVec_permVec σ1 hw1)
  have hadd2 : φ (w2 + permVec σ2 w2) = φ w2 * φ (permVec σ2 w2) :=
    hperm.1 w2 (permVec σ2 w2) hw2 (isEvenVec_permVec σ2 hw2)
  have hadd3 : φ ((w1 + permVec σ1 w1) + (w2 + permVec σ2 w2))
      = φ (w1 + permVec σ1 w1) * φ (w2 + permVec σ2 w2) :=
    hperm.1 _ _ hsum1 hsum2
  have hφeq : φ (sec1011_wfour 0) = φ ((w1 + permVec σ1 w1) + (w2 + permVec σ2 w2)) := by
    rw [hspan, ← hw1eq, ← hw2eq, hact1 w1 hw1, hact2 w2 hw2, ← hadd1, ← hadd2, ← hadd3]
  have hveceq : sec1011_wfour 0 = (w1 + permVec σ1 w1) + (w2 + permVec σ2 w2) :=
    hperm.2.1 _ _ (sec1011_wfour_even 0) (sec1011_isEvenVec_add hsum1 hsum2) hφeq
  have hle := sec1011_five_comm_cube σ1 σ2 h1 h2 hcomm w1 w2 hw1 hw2
  rw [← hveceq, sec1011_wfour_weight 0] at hle
  omega

end CFSG.OddStandard.SmallF3.Omega
