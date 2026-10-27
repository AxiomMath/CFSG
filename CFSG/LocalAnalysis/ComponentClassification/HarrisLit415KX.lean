module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415K
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415JY

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd DihedralGroup

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem card_pCore_le [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) (hA : AutPSL2RCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≤ 4 := by
  have hQ2 := hc.pCore_sq hnab hKC hA h412
  rcases h412.pCore_shape with hcyc | ⟨k, hk, ⟨e⟩⟩
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(pCore 2
      (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    have h1 : Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = orderOf g := by
      rw [← Nat.card_zpowers g, (Subgroup.eq_top_iff' (zpowers g)).mpr hg, Subgroup.card_top]
    have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [sq]
      exact Subtype.ext (hQ2 g g.2))
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have h1 : (DihedralGroup.r 1 : DihedralGroup (2 ^ k)) ^ 2 = 1 := by
      have h2 := hQ2 (e.symm (DihedralGroup.r 1)) (e.symm (DihedralGroup.r 1)).2
      have h3 : e.symm (DihedralGroup.r 1) * e.symm (DihedralGroup.r 1) = 1 := Subtype.ext h2
      rw [sq, ← e.apply_symm_apply (DihedralGroup.r 1), ← map_mul, h3, map_one]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [DihedralGroup.orderOf_r_one] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega

theorem sq_eq_one_of_normal_T (hKC : AutPSL2CentralizerInput) {E : Subgroup X}
    (hET : E ≤ W ⊓ centralizer {t})
    (hEn : ∀ g ∈ W ⊓ centralizer {t}, ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hzE : z ∉ E) :
    ∀ e ∈ E, e ^ 2 = 1 := by
  have hσ := hs.setup
  have hCWt := hσ.inf_W_t hKC hs.beta hc.isSylowOf_W hc.U_le
  rw [hCWt] at hET hEn
  have h1 := (hσ.le_X_of_normal hET hEn hzE).1
  exact fun e he => hσ.sq_eq_one_of_mem_X (h1 he)

theorem conj_mem_of_normalizer_W [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) (hA : AutPSL2RCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    {g : X} (hg : g ∈ normalizer (W : Set X)) :
    g * z₁ * g⁻¹ = z₁ ∨ g * z₁ * g⁻¹ = t * z₁ * t⁻¹ := by
  have hσ := hs.setup
  have h45 := hs.lemma45
  obtain ⟨e₁⟩ := hc.equiv₁
  have hlie := GSThmB.OddQuot.lieModel_of_equiv e₁.symm (hs.lieModel_KBar h412)
  obtain ⟨m, hm, ⟨eDs⟩⟩ := h45.dihedral_Dstar
  have hzc : ∀ d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      z * d = d * z := by
    intro d hd
    have hz : z ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
      rw [hσ.center_D]
      exact mem_zpowers z
    exact ((Subgroup.mem_centralizer_iff.mp (mem_inf.mp hz).2) d (mem_inf.mp hd).1).symm
  have hW₀z₂ : ∀ y ∈ W, y * z₁ = z₁ * y → y * (t * z₁ * t⁻¹) = (t * z₁ * t⁻¹) * y :=
    fun y hy hyz => mem_centralizer_singleton_iff.mp
      (hc.W₀_le_z₂ (mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr hyz⟩))
  have hβW := hc.T_le_W (hσ.X_le_T hs.beta.mem_X)
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have hβ1 : w ^ (orderOf w / 2) * t ^ i * z ^ j ≠ 1 := by
    intro h1
    apply hs.betaBar_ne_one
    rw [betaBar]
    have : (⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, mem_centralizer_singleton_iff.mpr rfl⟩ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) = 1 := Subtype.ext h1
    rw [this, QuotientGroup.mk_one]
  exact L415.conj_mem_of_normalizer_W_of (hc.isSylowOf_W.le hc.t_mem_W)
    (by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]) hc.prod hc.isSylowOf_W
    hc.t_mem_W hc.z₁_mem hc.sq_z₁ hc.z₁_ne hc.z_eq hc.mk_z₁ hc.comm_iff hc.mul_t hW₀z₂
    (fun y hy => hc.comm_z hy) hc.Dstar_le_W hc.isSylowOf_Dstar_bar hm eDs h45.z_mem hzc hA
    hs.prime_p hs.p_ne_two hlie (hc.eight_le_card_inf h412)
    (h412.pCore_eq.1.trans h412.pCore_eq.2) (hc.card_pCore_le hnab hKC hA h412)
    h412.pCore_inf_centralizer hβW hβ1 hβ2 (fun E hET hEn hzE => hc.sq_eq_one_of_normal_T hKC hET
      hEn hzE) hg

end Config415

end CFSG.ComponentClassification.HarrisLit
