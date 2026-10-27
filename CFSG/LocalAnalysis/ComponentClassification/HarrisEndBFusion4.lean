module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBFusion3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB

theorem seven_dvd_of_lieModel {Z : Type} [Group Z] (h : Blueprint.LieModel Z .PSL 2 7 1) :
    7 ∣ Nat.card Z := by
  obtain ⟨hp, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two hp (by norm_num) hF]
  norm_num

namespace JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem not_conj_of_mem_sup
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput) (hJ : JLayer hs π)
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) (g : X)
    (hτM : g * t * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (hτ : (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : False := by
  have hc : ∀ k ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      ∀ n ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), k * n = n * k := by
    intro k hk n hn
    rw [← hs.centralizer_layer_eq hJ.h412] at hn
    exact mem_centralizer_iff.mp hn k hk
  obtain ⟨e, he, q, hq, hτeq⟩ := M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute hc hτ
  set e' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := ⟨e, he⟩ with he'
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hτ2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
    group
  by_cases he1 : π e' = 1
  ·
    have hez : e' ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
      rw [← hJ.ker]
      exact he1
    have heQ : e ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rw [← hs.centralizer_layer_eq hJ.h412]
      refine mem_centralizer_iff.mpr fun l hl => ?_
      have := mem_center_iff.mp hez ⟨l, hl⟩
      exact (congrArg Subtype.val this)
    exact hJ.not_conj_of_mem_pCore hcent g hτM (hτeq ▸ mul_mem heQ hq)
  ·
    have hτ2' : (QuotientGroup.mk ⟨g * t * g⁻¹, hτM⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨g * t * g⁻¹, hτM⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
          Set X))) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hτ2, Subgroup.coe_one])
      rw [this, QuotientGroup.mk_one]
    have he2c : e' ^ 2 ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
      have hcomm : Commute e q := hc e he q hq
      rw [hτeq, hcomm.mul_pow] at hτ2'
      have heq2 : e ^ 2 = (q ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hτ2'
      have hq2 : e ^ 2 ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
        rw [heq2]
        exact inv_mem (pow_mem hq 2)
      rw [← hs.centralizer_layer_eq hJ.h412] at hq2
      refine mem_center_iff.mpr fun l => Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow]
      exact mem_centralizer_iff.mp hq2 l l.2
    have he2 : orderOf (π e') = 2 := by
      refine orderOf_eq_prime ?_ he1
      rw [← map_pow]
      have : e' ^ 2 ∈ π.ker := by rw [hJ.ker]; exact he2c
      exact this
    have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 :=
      hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
    have hβC : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ centralizer ({g * t * g⁻¹} : Set X) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hτM).symm
    have hβne : w ^ (orderOf w / 2) * t ^ i * z ^ j ≠ g * t * g⁻¹ :=
      fun h => hs.beta.not_conj g h.symm
    have h44 := hs.lemma44_conj hFC hKC hI hKF g hβC hβ2 hs.beta.ne_one hβne
    obtain ⟨-, hp7, hf1, -⟩ := hJ.seven hcent
    rw [hp7, hf1] at h44
    obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ := bar_centralizer_equiv hτM hτ2
    rw [hτeq] at e₁ e₂
    rcases h44 with h | h
    · exact hJ.not_isPGroup_bar hq he2 (h.of_equiv e₁.symm)
    · have h7 := seven_dvd_of_lieModel (lieModel_psl2_of_mulEquiv e₂ h)
      apply hJ.not_seven_dvd hq he2
      refine h7.trans ((Subgroup.card_quotient_dvd_card _).trans ?_)
      exact Subgroup.card_dvd_of_le (map_subtype_le _)

theorem not_isSylowOf_W [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput) (hJ : JLayer hs π)
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) (htW : t ∈ W) :
    ¬ IsSylowOf 2 W ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hWX
  set M := centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) with hM
  set N := layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
    pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hN
  set Y := W ⊓ preimageOf M N with hY
  have hWM : W ≤ M := hW.le
  have htN : hs.setup.tBar i j ∉ N := by
    rw [hN, ← hJ.theta_mem_inner_iff]
    exact hJ.alpha_not_mem
  have hNidx : N.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨(hs.setup.tBar i j)⁻¹, fun b => ?_⟩
    rcases hJ.mem_sup_or b with hb | hb
    · refine Or.inr ⟨hb, fun h => htN ?_⟩
      have := mul_mem (inv_mem h) hb
      rwa [show (b * (hs.setup.tBar i j)⁻¹)⁻¹ * b = hs.setup.tBar i j by group] at this
    · refine Or.inl ⟨hb, fun h => htN ?_⟩
      have := mul_mem (inv_mem hb) h
      rwa [show (b * (hs.setup.tBar i j)⁻¹)⁻¹ * b = hs.setup.tBar i j by group] at this
  have hNn : N.Normal := Subgroup.normal_of_index_eq_two hNidx
  have htWb : hs.setup.tBar i j ∈ barOf M W := mk_mem_barOf _ htW
  have hrel : N.relIndex (barOf M W) = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal N (barOf M W)
    rw [hNidx] at hdvd
    have hne : N.relIndex (barOf M W) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun h => htN (h htWb)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hYW : Y ≤ W := inf_le_left
  have hY2 : IsPGroup 2 Y := hW.isPGroup.to_le hYW
  have hcardW : Nat.card W = 2 * Nat.card Y := by
    have h1 := Subgroup.relIndex_mul_card N (barOf M W)
    rw [hrel] at h1
    rw [← card_barOf hWM hW.isPGroup, ← card_barOf (hYW.trans hWM) hY2, hY,
      barOf_inf_preimageOf, inf_comm, h1]
  have hidx : Y.relIndex W = 2 := by
    have h := Subgroup.relIndex_mul_card Y W
    rw [inf_of_le_left hYW, hcardW] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have htY : t ∉ Y := by
    intro h
    exact htN ((mem_preimageOf (hWM htW)).mp (mem_inf.mp h).2)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hWidx : ¬ 2 ∣ W.index := by
    have h := (isSylowOf_iff.mp hWX).2.2
    rwa [Subgroup.relIndex_top_right] at h
  obtain ⟨g, hgY, -, -⟩ := exists_extremal_conj_of_relIndex_two hnab hW.isPGroup hWidx hYW hidx
    htW htY ht2
  have hg' : g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ := by rw [inv_inv]
  rw [hg'] at hgY
  have hτM : g⁻¹ * t * g⁻¹⁻¹ ∈ M := hWM (mem_inf.mp hgY).1
  exact hJ.not_conj_of_mem_sup hFC hKC hI hKF hcent g⁻¹ hτM
    ((mem_preimageOf hτM).mp (mem_inf.mp hgY).2)

end JLayer

end EndB

end CFSG.ComponentClassification.HarrisLit
