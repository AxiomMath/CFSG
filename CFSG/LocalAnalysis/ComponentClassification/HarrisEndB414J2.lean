module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd414
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelExternal
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBFusion4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem index_sup_eq_two
    (hJ : JLayer hs π) :
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).index = 2 := by
  have htN : hs.setup.tBar i j ∉ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [← hJ.theta_mem_inner_iff]
    exact hJ.alpha_not_mem
  rw [Subgroup.index_eq_two_iff]
  refine ⟨(hs.setup.tBar i j)⁻¹, fun b => ?_⟩
  rcases hJ.mem_sup_or b with hb | hb
  · refine Or.inr ⟨hb, fun h => htN ?_⟩
    have := mul_mem (inv_mem h) hb
    rwa [show (b * (hs.setup.tBar i j)⁻¹)⁻¹ * b = hs.setup.tBar i j by group] at this
  · refine Or.inl ⟨hb, fun h => htN ?_⟩
    have := mul_mem (inv_mem hb) h
    rwa [show (b * (hs.setup.tBar i j)⁻¹)⁻¹ * b = hs.setup.tBar i j by group] at this

theorem pCore_ne_zpowers
    (hJ : JLayer hs π)
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336)
    (hβE : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
    pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≠
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hQ
  set M := centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) with hM
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have hT1 : IsSylowOf 2 T (centralizer ({t} : Set X) ⊓ M) := hs.lemma45.isSylowOf_T
  have hTM : T ≤ M := hT1.le.trans inf_le_right
  have hTt : T ≤ centralizer ({t} : Set X) := hT1.le.trans inf_le_left
  have hT64 : Nat.card (barOf M T) = 64 := by
    rw [card_barOf hTM hT1.isPGroup, hJ.card_T hcent]
  have hidx : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).index = 2 := by
    have h := hJ.index_sup_eq_two
    rwa [hQ, sup_of_le_left (zpowers_le.mpr hβE)] at h
  have hrel := Subgroup.relIndex_dvd_index_of_normal
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (barOf M T)
  rw [hidx] at hrel
  have hTbC : layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ barOf M T ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} := by
    rintro _ ⟨hxE, ⟨x, hxT, rfl⟩⟩
    refine ⟨hxE, mem_centralizer_singleton_iff.mpr ?_⟩
    have hxt : (x : X) * t = t * x := mem_centralizer_singleton_iff.mp (hTt hxT)
    change (QuotientGroup.mk (x * ⟨t, hs.setup.t_mem_centralizer_beta i j⟩) :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
        QuotientGroup.mk (⟨t, hs.setup.t_mem_centralizer_beta i j⟩ * x)
    rw [show x * (⟨t, hs.setup.t_mem_centralizer_beta i j⟩ : ↥M) =
      ⟨t, hs.setup.t_mem_centralizer_beta i j⟩ * x from Subtype.ext hxt]
  have h336 := Subgroup.card_dvd_of_le hTbC
  rw [hcent] at h336
  have hp2 : IsPGroup 2 ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ barOf M T) :=
    ((isPGroup_subgroupOf hTM hT1.isPGroup).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥M))).to_le inf_le_right
  obtain ⟨k, hk⟩ := hp2.exists_card_eq
  have h16 : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ barOf M T) ≤ 16 := by
    rw [hk] at h336 ⊢
    have hcop : Nat.Coprime (2 ^ k) 21 := Nat.Coprime.pow_left _ (by norm_num)
    have h16 : 2 ^ k ∣ 2 ^ 4 :=
      hcop.dvd_of_dvd_mul_right (by rw [show (2 : ℕ) ^ 4 * 21 = 336 by norm_num]; exact h336)
    exact Nat.le_of_dvd (by norm_num) h16
  have h := Subgroup.relIndex_mul_card (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (barOf M T)
  rw [hT64] at h
  have hrel2 := Nat.le_of_dvd (by norm_num) hrel
  have := Nat.mul_le_mul hrel2 h16
  omega

end EndB.JLayer

namespace EndB

theorem card_layer_inf_centralizer_cover
    {hs : Setting46e t L p f S w z V i j}
    {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P} (hJ : JLayer hs π)
    (hβE : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = zpowers ⟨_, hβE⟩) :
    Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336 := by
  have hβ2 := orderOf_eq_prime hs.betaBar_sq hs.betaBar_ne_one
  have ht : orderOf (⟨_, hβE⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2 := by
    rw [Subgroup.orderOf_mk, hβ2]
  have hLq : CFSG.Assembly.IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    ⟨hJ.quasi.1.commutator_eq_top, hJ.quasi.2.1⟩
  have hpN : hs.setup.tBar i j ∈ normalizer
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [Subgroup.normalizer_eq_top]
    exact mem_top _
  have hpC : ∀ l ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      l * hs.setup.tBar i j ∉ centralizer
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    intro l hl h
    apply hJ.alpha_not_mem
    have h1 : hJ.theta (l * hs.setup.tBar i j) = 1 := (hJ.theta_spec.2 _).mpr h
    rw [map_mul] at h1
    have h2 : hJ.theta (hs.setup.tBar i j) = (hJ.theta l)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, show l = ((⟨l, hl⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) from rfl, hJ.theta_conj]
    exact inv_mem ⟨_, rfl⟩
  obtain ⟨-, hsupA, hinfA, -, hAcard, -⟩ :=
    CyclicKernel.j2_outer_involution_fixed_factor hLq ht hZ π hJ.surj (hJ.ker.trans hZ) hpN
      hs.orderOf_tBar hpC (hJ.theta (hs.setup.tBar i j)) (hJ.theta_apply _) rfl
  rw [← hsupA, M12Cover.CyclicKernel.card_sup_of_commute (fun k hk n _ => ?_) hinfA,
    Nat.card_zpowers, hAcard]
  · change orderOf (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * 168 = 336
    rw [hβ2]
  · have hkZ : k ∈ center (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
      zpowers_le.mpr (betaBar_mem_center _) hk
    exact (mem_center_iff.mp hkZ n).symm

theorem exists_pi_of_equiv
    {E : Type} [Group E] (eJ : E ⧸ center E ≃* Blueprint.NativeSporadic.J2) :
    ∃ π : E →* P, Function.Surjective π ∧ π.ker = center E := by
  set e : E ⧸ center E ≃* P := eJ.trans nativeEquivP with he
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center E)), fun y => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center E) (e.symm y)
    refine ⟨x, ?_⟩
    rw [MonoidHom.comp_apply, hx, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

namespace JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem center_eq_zpowers (hJ : JLayer hs π)
    (hZ2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2) :
    ∃ hβE : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = zpowers ⟨_, hβE⟩ := by
  have hZne : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hZ2
    exact absurd hZ2 (by norm_num)
  obtain ⟨c, hcZ, hcβ⟩ := hJ.h412.lemma46c.2.2 hZne
  have hβE : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [← hcβ]
    exact c.2
  refine ⟨hβE, ?_⟩
  have hcβ' : c = ⟨_, hβE⟩ := Subtype.ext hcβ
  have hle : zpowers (⟨_, hβE⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ≤
      center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    zpowers_le.mpr (hcβ' ▸ hcZ)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hZ2, Nat.card_zpowers, Subgroup.orderOf_mk,
    orderOf_eq_prime hs.betaBar_sq hs.betaBar_ne_one]

theorem false_of_center_two [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput) (hJ : JLayer hs π)
    (hZ2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2) :
    False := by
  obtain ⟨hβE, hZ⟩ := hJ.center_eq_zpowers hZ2
  have hcent := card_layer_inf_centralizer_cover hJ hβE hZ
  have hQ := hJ.pCore_ne_zpowers hcent hβE
  obtain ⟨W, hW, hUW⟩ := hs.exists_W
  have htW : t ∈ W := hUW (hs.beta.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t))))
  exact hJ.not_isSylowOf_W hnab hFC hKC hI hKF hcent hW htW
    (isSylowOf_top_of_normalizer_le hW (hJ.normalizer_W_le hKC hQ hW hUW))

end JLayer

theorem harris414_J2
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput) : Harris414J2Case := by
  intro X _ _ _ hnab hK hcat t L p f S w z V i j hhyp hJ2
  obtain ⟨hs, h412, h47, hq, -, hout⟩ := hhyp
  obtain ⟨⟨eJ⟩, hZ2⟩ := hJ2
  obtain ⟨π, hπs, hker⟩ := exists_pi_of_equiv eJ
  exact JLayer.false_of_center_two (hs := hs) (π := π) hnab hFC hKC hI hKF
    ⟨h412, h47, hq, hout, hπs, hker, hZ2.le⟩ hZ2

end EndB

end CFSG.ComponentClassification.HarrisLit
