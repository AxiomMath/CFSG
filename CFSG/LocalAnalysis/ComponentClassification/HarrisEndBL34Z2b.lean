module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Z2a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSubGen
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Orbit

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem exists_y_of_not_sylow (hKC : AutPSL2CentralizerInput) (hs : Setting46e t L p f S w z V i j)
    {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W)
    (hnot : ¬ IsSylowOf 2 W ⊤) :
    ∃ y ∈ normalizer (W : Set X),
      y ∉ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ∧
      z ∈ W ⊓ centralizer (W : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyN, hyW, -, hy2grp⟩ := exists_mem_normalizer_sq_mem hW.isPGroup hnot
  have hyM : y ∉ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
    intro hyM
    have hle : W ⊔ zpowers y ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
      sup_le hW.le (zpowers_le.mpr hyM)
    have := hW.eq_of_le le_sup_left hle hy2grp
    exact hyW (this ▸ mem_sup_right (mem_zpowers y))
  obtain ⟨hβZ, hZle⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 :=
    hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hs.lemma45.z_mem.2
  have hβz : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z =
      z * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := (mem_centralizer_singleton_iff.mp hzM).symm
  have hyβ := conj_mem_zW y hyN _ hβZ
  refine ⟨y, hyN, hyM, ?_⟩
  rcases mem_closure_pair hβ2 hz2 hβz (hZle hyβ) with h | h | h | h
  · exfalso
    apply hs.beta.ne_one
    calc w ^ (orderOf w / 2) * t ^ i * z ^ j =
        y⁻¹ * (y * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply hyM
    rw [mem_centralizer_singleton_iff]
    calc y * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        (y * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * y⁻¹) * y := by group
      _ = (w ^ (orderOf w / 2) * t ^ i * z ^ j) * y := by rw [h]
  · exact h ▸ hyβ
  · have := mul_mem (inv_mem hβZ) (h ▸ hyβ)
    rwa [inv_mul_cancel_left] at this

theorem false_of_lambda (hKC : AutPSL2CentralizerInput) (hs : Setting46e t L p f S w z V i j)
    {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W)
    (hzZ : z ∈ W ⊓ centralizer (W : Set X))
    (htz : ∀ c : X, c * t * c⁻¹ ≠ t * z)
    (htβ : ∀ c : X, c * t * c⁻¹ ≠ t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) {l : X}
    (hlN : l ∈ normalizer (W : Set X))
    (hlM : l ∉ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (hlt : l * t * l⁻¹ = t) : False := by
  obtain ⟨hβZ, hZle⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 :=
    hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hs.lemma45.z_mem.2
  have hβz : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z =
      z * (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    (mem_centralizer_singleton_iff.mp hzM).symm
  have hzL : z ∈ L := (mem_inf.mp hs.lemma45.z_mem.1).2
  have hβS : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ S :=
    hs.setup.T_le (hs.setup.X_le_T (beta_mem_X i j))
  have hβL : w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ L :=
    fun h => hs.beta.not_mem (mem_sup_right (mem_inf.mpr ⟨hβS, h⟩))
  have hz1 : z ≠ 1 := by
    intro h
    have := hs.setup.z_order
    rw [h, orderOf_one] at this
    norm_num at this
  have hβnz : w ^ (orderOf w / 2) * t ^ i * z ^ j ≠ z := fun h => hs.beta.not_mem (by
    rw [h]
    exact mem_sup_right hs.lemma45.z_mem.1)
  have hlH : l ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc l * t = (l * t * l⁻¹) * l := by group
      _ = t * l := by rw [hlt]
  have hlzL : l * z * l⁻¹ ∈ L :=
    (mem_normalizer_iff.mp (hs.standing.centralizer_le_normalizer hlH) z).mp hzL
  have hlz : l * z * l⁻¹ = z := by
    rcases mem_closure_pair hβ2 hz2 hβz (hZle (conj_mem_zW l hlN z hzZ)) with h | h | h | h
    · exfalso
      apply hz1
      calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
        _ = 1 := by rw [h]; group
    · exact absurd (h ▸ hlzL) hβL
    · exact h
    · exfalso
      apply hβL
      have : w ^ (orderOf w / 2) * t ^ i * z ^ j = (l * z * l⁻¹) * z⁻¹ := by rw [h]; group
      rw [this]
      exact mul_mem hlzL (inv_mem hzL)
  have hlβ : l * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * l⁻¹ =
      (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z := by
    have hback : w ^ (orderOf w / 2) * t ^ i * z ^ j =
        l⁻¹ * (l * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * l⁻¹) * l := by group
    rcases mem_closure_pair hβ2 hz2 hβz (hZle (conj_mem_zW l hlN _ hβZ)) with h | h | h | h
    · exfalso
      apply hs.beta.ne_one
      rw [hback, h]
      group
    · exfalso
      apply hlM
      rw [mem_centralizer_singleton_iff]
      calc l * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
          (l * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * l⁻¹) * l := by group
        _ = (w ^ (orderOf w / 2) * t ^ i * z ^ j) * l := by rw [h]
    · exfalso
      apply hβnz
      calc w ^ (orderOf w / 2) * t ^ i * z ^ j =
          l⁻¹ * (l * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * l⁻¹) * l := hback
        _ = l⁻¹ * (l * z * l⁻¹) * l := by rw [h, hlz]
        _ = z := by group
    · exact h
  obtain ⟨v, -, -, -, hvt⟩ := hs.beta.exists_mem
  rcases hvt with h | h
  · exact htz v h
  · apply htβ (l⁻¹ * v)
    calc l⁻¹ * v * t * (l⁻¹ * v)⁻¹ = l⁻¹ * (v * t * v⁻¹) * l := by group
      _ = l⁻¹ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z) * l := by rw [h]
      _ = l⁻¹ * ((l * t * l⁻¹) * (l * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * l⁻¹)) * l := by
          rw [hlt, hlβ]; group
      _ = t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by group

theorem false_of_Z2a [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hFF : L34FieldSylowFusionFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβE : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    obtain ⟨b, -, hb⟩ := hL.h412.lemma46c.2.2 hZ
    rw [← hb]
    exact b.2
  have hQE : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [hQ]
    exact zpowers_le.mpr hβE
  have hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [hQ]
    infer_instance
  obtain ⟨W, hW, hUW⟩ := hs.exists_W
  have h2W := hL.two_dvd_index_W hnab hFC hKC hI hKF hZ hQc hW hUW
  have hnot : ¬ IsSylowOf 2 W ⊤ := fun h => (isSylowOf_iff.mp h).2.2
    (by rw [Subgroup.relIndex_top_right]; exact h2W)
  obtain ⟨y, hyN, hyM, hzZ⟩ := exists_y_of_not_sylow hKC hs hW hUW hnot
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hs.beta.lt.le.trans hUW
  have htW : t ∈ W := hTW (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hτW : y * t * y⁻¹ ∈ W := conj_mem_W y hyN t htW
  have hτM := hW.le hτW
  have hT1 := hs.lemma45.isSylowOf_T
  have hTH : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({t} : Set X) :=
    hT1.le.trans inf_le_left
  have hR₀ : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).map (MulAut.conj y).toMonoidHom ≤
      centralizer ({y * t * y⁻¹} : Set X) ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} := by
    rintro _ ⟨s', hs', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
      hW.le (conj_mem_W y hyN _ (hTW hs'))⟩
    have h1 := mem_centralizer_singleton_iff.mp (hTH hs')
    calc y * s' * y⁻¹ * (y * t * y⁻¹) = y * (s' * t) * y⁻¹ := by group
      _ = y * (t * s') * y⁻¹ := by rw [h1]
      _ = y * t * y⁻¹ * (y * s' * y⁻¹) := by group
  have hR₀2 := hT1.isPGroup.map (MulAut.conj y).toMonoidHom
  have h64 : 64 ≤ Nat.card ↥((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).map
      (MulAut.conj y).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hL.card_T hZ]
  have hψ := hL.psi_eq_t_of_conj hFC hKC hI hKF hUC hZ hQc hQE hW hUW y hτM hτW hR₀ hR₀2 h64
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hτ2 : (y * t * y⁻¹) ^ 2 = 1 := by
    rw [sq, show y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ by group, ← sq, ht2]
    group
  obtain ⟨q, hqW, b, hb, hqb⟩ := hL.exists_conj_field_coset hFF hFC hKC hZ h2 hQE hW hUW hτW hτ2
    hψ
  have htz := hL.not_conj_tz hFC hKC hI hKF hUC hZ hQE
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hs.lemma45.z_mem.2
  have hβM : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈
      centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    mem_centralizer_singleton_iff.mpr rfl
  have hzE : (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    hs.KBar_le_layer ⟨⟨z, hzM⟩, hs.lemma45.z_mem.2, rfl⟩
  have hβz' : ∀ c : X, c * t * c⁻¹ ≠ w ^ (orderOf w / 2) * t ^ i * z ^ j * z := by
    intro c hc
    have hcM : c * t * c⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
      hc ▸ mul_mem hβM hzM
    refine hL.false_of_conj_inner hZ hQc c hcM (mem_sup_left ?_)
    have : (QuotientGroup.mk ⟨c * t * c⁻¹, hcM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
        betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * QuotientGroup.mk ⟨z, hzM⟩ := by
      rw [betaBar, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hc
    rw [this]
    exact mul_mem hβE hzE
  have htβ := EndB.not_conj_tbeta hKF hs htz hs.setup.conj_t_ne_z hβz'
  have hl0 : (q * y) * t * (q * y)⁻¹ = b * t := by
    rw [show (q * y) * t * (q * y)⁻¹ = q * (y * t * y⁻¹) * q⁻¹ by group, hqb]
  have hqN : q ∈ normalizer (W : Set X) := le_normalizer_self hqW
  have hnotM : ∀ w₁ ∈ W,
      w₁ * y ∉ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
    intro w₁ hw₁ h
    apply hyM
    rw [show y = w₁⁻¹ * (w₁ * y) by group]
    exact mul_mem (inv_mem (hW.le hw₁)) h
  have htβc : t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      (w ^ (orderOf w / 2) * t ^ i * z ^ j) * t := mem_centralizer_singleton_iff.mp htM
  have htS : t ∈ S := hs.setup.T_le (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hzt : t * z = z * t := hs.setup.z_comm htS
  rcases hb with rfl | rfl | rfl | rfl
  · exact false_of_lambda hKC hs hW hUW hzZ htz htβ (mul_mem hqN hyN) (hnotM q hqW)
      (by rw [hl0, one_mul])
  · exact htβ (q * y) (by rw [hl0, htβc])
  · exact htz (q * y) (by rw [hl0, hzt])
  · obtain ⟨v, hv, -, -, hvt⟩ := hs.beta.exists_mem
    rcases hvt with h | h
    · exact htz v h
    · have hvW : v ∈ W := hUW hv
      refine false_of_lambda hKC hs hW hUW hzZ htz htβ
        (mul_mem (inv_mem (le_normalizer_self hvW)) (mul_mem hqN hyN)) ?_ ?_
      · rw [← mul_assoc]
        exact hnotM _ (mul_mem (inv_mem hvW) hqW)
      · calc v⁻¹ * (q * y) * t * (v⁻¹ * (q * y))⁻¹ = v⁻¹ * ((q * y) * t * (q * y)⁻¹) * v := by
              group
          _ = v⁻¹ * (v * t * v⁻¹) * v := by
              have hcomm : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z * t =
                  t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z := by
                rw [mul_assoc (w ^ (orderOf w / 2) * t ^ i * z ^ j) z t, ← hzt,
                  ← mul_assoc (w ^ (orderOf w / 2) * t ^ i * z ^ j) t z, ← htβc]
              rw [hl0, hcomm, h]
          _ = t := by group

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
