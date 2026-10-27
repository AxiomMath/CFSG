module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34U
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Lam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34TT

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem false_of_conj_unitary_Z2
    (hKF : AutPSL2FusionInput) (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2)
    {x : X} (hxD : x ∈ S ⊓ L) (hx2 : x ^ 2 = 1)
    (hxM : x ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (h0 : ((hL.rho (QuotientGroup.mk ⟨x, hxM⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∉
      PSL3Four.S)
    (h1 : ((hL.rho (QuotientGroup.mk ⟨x, hxM⟩ * hs.setup.tBar i j) : PSL3Four.R) :
      Equiv.Perm (Fin 42)) ∉ PSL3Four.S) {c : X} (hc : c * t * c⁻¹ = x * t)
    {d : Equiv.Perm (Fin 42)} (hd : d ∈ PSL3Four.R)
    (hdu : ((hL.rho (QuotientGroup.mk ⟨x, hxM⟩ * hs.setup.tBar i j) : PSL3Four.R) :
      Equiv.Perm (Fin 42)) = d * PSL3Four.r₄ * d⁻¹) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hxtM : x * t ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    mul_mem hxM htM
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer (mem_inf.mp hxD).2)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hxt2 : (x * t) ^ 2 = 1 := by rw [(show Commute x t from hxt).mul_pow, hx2, ht2, one_mul]
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzK : z ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := hs.lemma45.z_mem.2
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hzK
  have hβM : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈
      centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    mem_centralizer_singleton_iff.mpr rfl
  have hz1 : z ≠ 1 := by
    intro h
    have := hs.setup.z_order
    rw [h, orderOf_one] at this
    norm_num at this
  have hβz : w ^ (orderOf w / 2) * t ^ i * z ^ j ≠ z := fun h => hs.beta.not_mem (by
    rw [h]
    exact mem_sup_right hs.lemma45.z_mem.1)
  obtain ⟨hR₀p, hR₀le, hxR₀, htR₀, hβR₀, hzR₀⟩ := hs.l34_R0 hxD
  obtain ⟨R, hR, hR₀R⟩ := exists_isSylowOf_ge hR₀p hR₀le
  have hRM : R ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    hR.le.trans inf_le_right
  have hRp := hR.isPGroup
  have hxtR : x * t ∈ R := mul_mem (hR₀R hxR₀) (hR₀R htR₀)
  have htR : t ∈ R := hR₀R htR₀
  have hβR : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ R := hR₀R hβR₀
  have hzR : z ∈ R := hR₀R hzR₀
  have hRb := isSylowOf_barOf_centralizer hxtM hxt2 hR
  have hxb2 := EndB.mk_sq hxM hx2
  have hxbt : (QuotientGroup.mk ⟨x, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
      hs.setup.tBar i j = hs.setup.tBar i j * QuotientGroup.mk ⟨x, hxM⟩ :=
    EndB.mk_comm hxM htM hxt
  have hg2 : ((QuotientGroup.mk ⟨x, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
      hs.setup.tBar i j) ^ 2 = 1 := by
    rw [(show Commute _ _ from hxbt).mul_pow, hxb2, hs.tBar_sq, one_mul]
  obtain ⟨-, hrtS⟩ := hL.rho_t_facts
  obtain ⟨U', hU', hU'2, h32⟩ := hL.exists_card_ge_32 hUC hg2 hd hdu
    (a := QuotientGroup.mk ⟨x, hxM⟩) (b := hs.setup.tBar i j)
    (by rw [mem_centralizer_singleton_iff]; exact ((Commute.refl _).mul_right hxbt).eq)
    (by rw [mem_centralizer_singleton_iff]
        exact ((show Commute (hs.setup.tBar i j) (QuotientGroup.mk ⟨x, hxM⟩) from
          hxbt.symm).mul_right (Commute.refl _)).eq)
    hxb2 hs.tBar_sq hxbt (fun h => h0 ((hL.rho_mem_S_iff _).mpr h))
    (fun h => hrtS ((hL.rho_mem_S_iff _).mpr h)) (fun h => h1 ((hL.rho_mem_S_iff _).mpr h))
  have hcardR : Nat.card ↥(barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
      R) = Nat.card R := card_barOf hRM hRp
  have h32R : 32 ≤ Nat.card R := by
    rw [← hcardR, hRb.card_eq]
    exact h32.trans (card_le_twoPart hU'2 hU')
  have hβc : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ centralizer ({c * t * c⁻¹} : Set X) := by
    rw [hc]
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxtM).symm
  have h64 : 64 ≤ Nat.card R := by
    by_contra hlt
    refine EndB.false_of_conj_t_twoPart hKF hs (hL.orderOf_w hZ) (hL.card_T hZ)
      (hL.card_S_le hZ) hβc (R := R) (by rw [hc]; exact hR.le) hRp
      (by rw [hc]; exact hR.card_eq) (by omega) (by omega)
  have hzE : (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    hs.KBar_le_layer ⟨⟨z, hzM⟩, hzK, rfl⟩
  have hzQ : (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∉
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    intro h
    rcases hL.eq_of_mem_layer_pCore hZ h2 hzE h with h' | h'
    · exact hz1 (mk_injOn hRM hRp hzR (one_mem R) h')
    · exact hβz (mk_injOn hRM hRp hzR hβR h').symm
  obtain ⟨hzc, hdisj⟩ := hL.witnesses_of_unitary hUC hZ h2 hg2 hd hdu (U := barOf
    (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) R) hRb
    (mk_mem_barOf hxtM hxtR) (mk_mem_barOf htM htR) (mk_mem_barOf hβM hβR)
    (mk_mem_barOf hzM hzR) hzE (EndB.mk_sq hzM hz2) hzQ (by rw [hcardR]; exact h64)
  set φ := barHom hRM with hφ
  have hφinj := barHom_injective hRM hRp
  have hlift : ∀ u ∈ barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) R,
      ∃ u' : ↥R, φ u' = u := fun u hu => by
    rw [← range_barHom hRM] at hu
    exact hu
  have hφz : φ ⟨z, hzR⟩ = QuotientGroup.mk ⟨z, hzM⟩ := rfl
  have hzcX : ∀ r ∈ R, r * z = z * r := by
    intro r hr
    have h1 : φ (⟨r, hr⟩ * ⟨z, hzR⟩ * (⟨r, hr⟩)⁻¹) = φ ⟨z, hzR⟩ := by
      rw [map_mul, map_mul, map_inv, hφz]
      exact hzc _ (mk_mem_barOf (hRM hr) hr)
    have h2' := congrArg Subtype.val (hφinj h1)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2'
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h2']
  obtain ⟨d', hd'⟩ := EndB.exists_conj_le_T hs (hL.orderOf_w hZ) (hL.card_T hZ) hxD hx2 hc hR.le
    hRp hβR hxtR hzR hzcX h64
  obtain ⟨-, -, -, ⟨eD⟩⟩ := hL.seven hZ
  have hw2 := hL.orderOf_w hZ
  have hu : w ^ (orderOf w / 2) = w := by rw [hw2]; norm_num
  have hw2' : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  have htw : t * w = w * t :=
    (mem_centralizer_singleton_iff.mp (hs.sylow.le hs.setup.w_mem)).symm
  have hAo := le_omegaCenter_sup ht2 hw2' htw
  have hAD : zpowers t ⊔ zpowers w ≤ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
    refine sup_le (zpowers_le.mpr (mem_centralizer_iff.mpr fun d hd => ?_))
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun d hd => ?_))
    · exact mem_centralizer_singleton_iff.mp (hs.standing.config.le_centralizer hd.2)
    · have := hs.setup.lift.comm_D d hd
      rwa [hu] at this
  have hA2 : ∀ g ∈ zpowers t ⊔ zpowers w, g ^ 2 = 1 := fun g hg => (hAo hg).2.2
  have hAD' : ∀ g ∈ zpowers t ⊔ zpowers w, ∀ y ∈ S ⊓ L, g * y = y * g :=
    fun g hg y hy => (mem_centralizer_iff.mp (hAD hg) y hy).symm
  have hAA : ∀ g ∈ zpowers t ⊔ zpowers w, ∀ y ∈ zpowers t ⊔ zpowers w, g * y = y * g :=
    fun g hg y hy => (hAo hy).2.1 g hg
  have hT' : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w = (S ⊓ L) ⊔ (zpowers t ⊔ zpowers w) := by
    rw [sup_comm (zpowers t), sup_assoc]
  have hmem : ∀ u : ↥R, d'⁻¹ * (u : X) * d' ∈ (S ⊓ L) ⊔ (zpowers t ⊔ zpowers w) := fun u => by
    rw [← hT']
    exact hd' u u.2
  have hcp : ∀ (u : X) (n : ℕ), (d'⁻¹ * u * d') ^ n = d'⁻¹ * u ^ n * d' := fun u n => by
    have := conj_pow (a := d'⁻¹) (b := u) (i := n)
    simpa using this
  have hne1 : ∀ (u : ↥R) (n : ℕ), φ u ^ n ≠ 1 → (d'⁻¹ * (u : X) * d') ^ n ≠ 1 := by
    intro u n hu hc'
    apply hu
    rw [hcp] at hc'
    have hun : (u : X) ^ n = 1 := by
      calc (u : X) ^ n = d' * (d'⁻¹ * (u : X) ^ n * d') * d'⁻¹ := by group
        _ = 1 := by rw [hc']; group
    have : u ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hun, Subgroup.coe_one])
    rw [← map_pow, this, map_one]
  rcases hdisj with ⟨a, haR, b, hbR, ha2, hb2, hab⟩ | ⟨a, haR, y, hyR, k, ha2, ha22, hy2, hk1, hk2,
      hka⟩
  · obtain ⟨a', rfl⟩ := hlift a haR
    obtain ⟨b', rfl⟩ := hlift b hbR
    have hcomm := commute_of_sq_ne_one eD hA2 hAD' hAA (hmem a') (hmem b') (hne1 a' 2 ha2)
      (hne1 b' 2 hb2)
    apply hab
    have hab' : (a' : X) * b' = b' * a' := by
      calc (a' : X) * b' = d' * ((d'⁻¹ * (a' : X) * d') * (d'⁻¹ * (b' : X) * d')) * d'⁻¹ := by
            group
        _ = d' * ((d'⁻¹ * (b' : X) * d') * (d'⁻¹ * (a' : X) * d')) * d'⁻¹ := by rw [hcomm]
        _ = b' * a' := by group
    rw [← map_mul, ← map_mul, show a' * b' = b' * a' from Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hab'])]
  · obtain ⟨a', rfl⟩ := hlift a haR
    obtain ⟨y', rfl⟩ := hlift y hyR
    have hφeq : ∀ (u : ↥R) (n : ℕ), (φ u ^ n) ^ 2 = 1 → ((d'⁻¹ * (u : X) * d') ^ n) ^ 2 = 1 := by
      intro u n h
      have h' : (u ^ n) ^ 2 = 1 := hφinj (by rw [map_pow, map_pow, h, map_one])
      rw [hcp, hcp, ← pow_mul]
      have : (u : X) ^ (n * 2) = 1 := by
        rw [pow_mul, ← Subgroup.coe_pow, ← Subgroup.coe_pow, h', Subgroup.coe_one]
      rw [this]
      group
    have hy := EndB.pow_eq_of_dihedral eD hA2 hAD' (hmem y') (hne1 y' 2 hy2) (hne1 y' k hk1)
      (hφeq y' k hk2)
    have ha := EndB.pow_eq_of_dihedral eD hA2 hAD' (hmem a') (hne1 a' 2 ha2) (hne1 a' 2 ha2)
      (hφeq a' 2 ha22)
    apply hka
    rw [← map_pow, ← map_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow]
    have h3 : d'⁻¹ * (y' : X) ^ k * d' = d'⁻¹ * (a' : X) ^ 2 * d' := by
      rw [← hcp, ← hcp, hy, ha]
    calc (y' : X) ^ k = d' * (d'⁻¹ * (y' : X) ^ k * d') * d'⁻¹ := by group
      _ = d' * (d'⁻¹ * (a' : X) ^ 2 * d') * d'⁻¹ := by rw [h3]
      _ = (a' : X) ^ 2 := by group

theorem false_of_Z2b
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≠
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : False := by
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hs.lemma45.z_mem.2
  obtain ⟨m, hm⟩ := hL.exists_conj_zt_of_Q hQ hzM
  obtain ⟨x, hxD, hx2, hxM, h0, h1⟩ := hL.exists_x hZ
  have hx1 : x ≠ 1 := by
    rintro rfl
    have : (QuotientGroup.mk ⟨1, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 1 := rfl
    exact h0 ((hL.rho_mem_S_iff _).mpr (by rw [this]; exact one_mem _))
  obtain ⟨c, hc⟩ := EndB.exists_conj_xt hKF hs hzM m hm hxD hx2 hx1
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer (mem_inf.mp hxD).2)
  have hxb2 := EndB.mk_sq hxM hx2
  have hxbt : (QuotientGroup.mk ⟨x, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
      hs.setup.tBar i j = hs.setup.tBar i j * QuotientGroup.mk ⟨x, hxM⟩ :=
    EndB.mk_comm hxM htM hxt
  have hτM : c * t * c⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
    rw [hc]
    exact mul_mem hxM htM
  have hτb : (QuotientGroup.mk ⟨c * t * c⁻¹, hτM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      QuotientGroup.mk ⟨x, hxM⟩ * hs.setup.tBar i j := by
    rw [show hs.setup.tBar i j = (QuotientGroup.mk ⟨t, htM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) from rfl, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hc
  rcases hL.graph_unitary hxb2 hxbt h0 h1 with ⟨-, ⟨d, hd, hdu⟩⟩ | ⟨-, ⟨d, hd, hdg⟩⟩
  · exact hL.false_of_conj_unitary_Z2 hKF hUC hZ h2 hxD hx2 hxM h0 h1 hc hd hdu
  · exact hL.false_of_graph_conj hFC hKC hI hKF hZ hτM ⟨d, hd, by rw [hτb]; exact hdg⟩

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
