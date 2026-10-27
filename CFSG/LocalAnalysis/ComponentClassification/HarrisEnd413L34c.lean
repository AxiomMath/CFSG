module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413L34b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndQuat

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace Setting46e

theorem l34_R0 (hs : Setting46e t L p f S w z V i j) {x : X} (hxD : x ∈ S ⊓ L) :
    IsPGroup 2 ↥((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ centralizer {x * t}) ∧
      (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ centralizer {x * t} ≤
        centralizer ({x * t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ∧
      x ∈ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ centralizer {x * t} ∧
      t ∈ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ centralizer {x * t} ∧
      w ^ (orderOf w / 2) * t ^ i * z ^ j ∈
        (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ centralizer {x * t} ∧
      z ∈ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ centralizer {x * t} := by
  have hT := hs.lemma45.isSylowOf_T
  have hTM := hT.le.trans inf_le_right
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer hxD.2)
  have hxM := hs.setup.D_le_centralizer_beta i j hxD
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hxt' : Commute x t := hxt
  have hβC : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ centralizer ({x * t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : Commute x (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
      mem_centralizer_singleton_iff.mp hxM
    have h2 : Commute t (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
      mem_centralizer_singleton_iff.mp htM
    exact (h1.symm.mul_right h2.symm).eq
  have hzx : Commute x z := hs.setup.z_comm_D hxD
  have hzt : Commute z t := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer hs.setup.z_mem.2)
  refine ⟨hT.isPGroup.to_le inf_le_left, fun g hg => mem_inf.mpr ⟨(mem_inf.mp hg).2,
    hTM (mem_inf.mp hg).1⟩, mem_inf.mpr ⟨mem_sup_left (mem_sup_right hxD), ?_⟩,
    mem_inf.mpr ⟨mem_sup_left (mem_sup_left (mem_zpowers t)), ?_⟩,
    mem_inf.mpr ⟨hs.setup.X_le_T (beta_mem_X i j), hβC⟩,
    mem_inf.mpr ⟨mem_sup_left (mem_sup_right hs.setup.z_mem), ?_⟩⟩
  · exact mem_centralizer_singleton_iff.mpr ((Commute.refl x).mul_right hxt').eq
  · exact mem_centralizer_singleton_iff.mpr (hxt'.symm.mul_right (Commute.refl t)).eq
  · exact mem_centralizer_singleton_iff.mpr (hzx.symm.mul_right hzt).eq

theorem l34_sylow_R (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hs : Setting46e t L p f S w z V i j)
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))]
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hY : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 3 2 2)
    (hout : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
      innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    {x : X} (hxD : x ∈ S ⊓ L) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hxρ : ∀ k ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
        ∀ (hx : x ∈ centralizer ({t} : Set X)) (hk : k ∈ centralizer ({t} : Set X)),
          hs.standing.rho ⟨x, hx⟩ ≠ hs.standing.rho ⟨k, hk⟩) :
    ∃ R : Subgroup X, R ≤ centralizer ({x * t} : Set X) ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ∧ IsPGroup 2 R ∧
      w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ R ∧ x * t ∈ R ∧ z ∈ R ∧ (∀ r ∈ R, r * z = z * r) ∧
      64 ≤ Nat.card R ∧ ∃ a ∈ R, ∃ b ∈ R, a ^ 2 ≠ 1 ∧ b ^ 2 ≠ 1 ∧ a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  have hxM : x ∈ M := hs.setup.D_le_centralizer_beta i j hxD
  have htM : t ∈ M := hs.setup.t_mem_centralizer_beta i j
  have hβM : β ∈ M := mem_centralizer_singleton_iff.mpr rfl
  have hzK : z ∈ centralizerResidual L β := hs.lemma45.z_mem.2
  have hzM : z ∈ M := K_le_centralizer_beta i j hzK
  have hxtM : x * t ∈ M := mul_mem hxM htM
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer hxD.2)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hxt2 : (x * t) ^ 2 = 1 := by
    rw [(show Commute x t from hxt).mul_pow, hx2, ht2, one_mul]
  obtain ⟨hR₀p, hR₀le, hxR₀, htR₀, hβR₀, hzR₀⟩ := hs.l34_R0 hxD
  obtain ⟨R, hR, hR₀R⟩ := exists_isSylowOf_ge hR₀p hR₀le
  have hRle := hR.le
  have hRM : R ≤ M := hRle.trans inf_le_right
  have hRp := hR.isPGroup
  have hyy : (⟨x * t, hxtM⟩ : ↥M) * ⟨x * t, hxtM⟩ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hxt2, Subgroup.coe_one])
  have hR' : IsSylowOf 2 (R.subgroupOf M) (centralizer {(⟨x * t, hxtM⟩ : ↥M)}) := by
    rw [← isSylowOf_map_subtype_iff M, map_subtype_centralizer hxtM, subgroupOf_map_subtype,
      inf_of_le_left hRM]
    exact hR
  have hR'p : IsPGroup 2 (R.subgroupOf M) := hR'.isPGroup
  have hRb : IsSylowOf 2 ((R.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
      (centralizer {(QuotientGroup.mk ⟨x * t, hxtM⟩ : MBar β)}) := by
    have h1 := HarrisLit.isSylowOf_map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) hR'
    rwa [← GSThmB.OddQuot.centralizer_singleton_map_eq hyy] at h1
  set Rb := (R.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) with hRbdef
  set Cb := centralizer {(QuotientGroup.mk ⟨x * t, hxtM⟩ : MBar β)} with hCb
  have hCbN : Cb ≤ normalizer ((E ⊓ Cb : Subgroup (MBar β)) : Set (MBar β)) := by
    intro g hg
    refine mem_normalizer_iff.mpr fun a => ⟨fun ha => mem_inf.mpr
      ⟨(inferInstance : E.Normal).conj_mem a (mem_inf.mp ha).1 g,
        mul_mem (mul_mem hg (mem_inf.mp ha).2) (inv_mem hg)⟩, fun ha => ?_⟩
    have h1 : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ ∈ E ⊓ Cb := mem_inf.mpr
      ⟨(inferInstance : E.Normal).conj_mem _ (mem_inf.mp ha).1 g⁻¹,
        mul_mem (mul_mem (inv_mem hg) (mem_inf.mp ha).2) (inv_mem (inv_mem hg))⟩
    rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at h1
  have hQb : IsSylowOf 2 (Rb ⊓ (E ⊓ Cb)) (E ⊓ Cb) := hRb.inf_of_le_normalizer inf_le_right hCbN
  have hquat := hs.l34_quaternion hFC hKC hI hKF h412 hY hout hxD hx2 hx1 hxρ hxtM
  have hmap := map_fixedPoints_conjOn (N := E) (QuotientGroup.mk ⟨x * t, hxtM⟩ : MBar β)
  have eN : ↥(fixedPoints (conjOn E (QuotientGroup.mk ⟨x * t, hxtM⟩ : MBar β))) ≃* ↥(E ⊓ Cb) :=
    ((fixedPoints (conjOn E (QuotientGroup.mk ⟨x * t, hxtM⟩ : MBar β))).equivMapOfInjective
      E.subtype E.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨Q₀, hQ₀⟩ := hQb
  obtain ⟨eQ₀⟩ := nonempty_quaternion_sylow_of_equiv hquat eN Q₀
  have eQ : QuaternionGroup 2 ≃* ↥(Rb ⊓ (E ⊓ Cb)) :=
    eQ₀.trans (((Q₀ : Subgroup ↥(E ⊓ Cb)).equivMapOfInjective (E ⊓ Cb).subtype
      (E ⊓ Cb).subtype_injective).trans (MulEquiv.subgroupCongr hQ₀))
  have hzR : z ∈ R := hR₀R hzR₀
  have hzR' : (⟨z, hzM⟩ : ↥M) ∈ R.subgroupOf M := hzR
  have hzbR : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ∈ Rb := ⟨_, hzR', rfl⟩
  have hzbE : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ∈ E :=
    hs.KBar_le_layer ⟨⟨z, hzM⟩, hzK, rfl⟩
  have hzxt : z * (x * t) = (x * t) * z := by
    have h1 : Commute x z := hs.setup.z_comm_D hxD
    have h2 : Commute z t := mem_centralizer_singleton_iff.mp
      (hs.standing.config.le_centralizer hs.setup.z_mem.2)
    exact (h1.symm.mul_right h2).eq
  have hzbC : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ∈ Cb := by
    rw [hCb, mem_centralizer_singleton_iff]
    change (QuotientGroup.mk (⟨z, hzM⟩ * ⟨x * t, hxtM⟩) : MBar β) =
      QuotientGroup.mk (⟨x * t, hxtM⟩ * ⟨z, hzM⟩)
    rw [show (⟨z, hzM⟩ * ⟨x * t, hxtM⟩ : ↥M) = ⟨x * t, hxtM⟩ * ⟨z, hzM⟩ from Subtype.ext hzxt]
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by
    have := hs.setup.z_order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hzb2 : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    rw [show (⟨z, hzM⟩ : ↥M) ^ 2 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, hz2, Subgroup.coe_one]), QuotientGroup.mk_one]
  have hzb1 : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ≠ 1 := by
    intro h
    have h1 := GSThmB.OddQuot.injOn_of_isPGroup hR'p hzR' (one_mem _)
      (by rw [map_one]; exact h)
    exact hz1 (congrArg Subtype.val h1)
  have hcz : ∀ r ∈ Rb, r * QuotientGroup.mk ⟨z, hzM⟩ * r⁻¹ =
      (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) := fun r hr =>
    conj_eq_of_quaternion (hRb.le.trans hCbN) eQ (mem_inf.mpr ⟨hzbR, mem_inf.mpr ⟨hzbE, hzbC⟩⟩)
      hzb2 hzb1 hr
  have hzc : ∀ r ∈ R, r * z = z * r := by
    intro r hr
    have hrM := hRM hr
    have hr' : (⟨r, hrM⟩ : ↥M) ∈ R.subgroupOf M := hr
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M)
        ((⟨r, hrM⟩ : ↥M) * ⟨z, hzM⟩ * (⟨r, hrM⟩ : ↥M)⁻¹) =
        QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨z, hzM⟩ := by
      rw [map_mul, map_mul, map_inv]
      exact hcz _ ⟨_, hr', rfl⟩
    have h2 := GSThmB.OddQuot.injOn_of_isPGroup hR'p
      (mul_mem (mul_mem hr' hzR') (inv_mem hr')) hzR' h1
    have h3 : r * z * r⁻¹ = z := congrArg Subtype.val h2
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h3]
  obtain ⟨hqa, hqb, hqab, -⟩ := quaternion_facts
  have hlift : ∀ q : QuaternionGroup 2, ∃ a : ↥M, (a : X) ∈ R ∧
      (QuotientGroup.mk a : MBar β) = (eQ q : MBar β) := by
    intro q
    obtain ⟨a, ha, h⟩ := (mem_inf.mp (eQ q).2).1
    exact ⟨a, ha, h⟩
  obtain ⟨a, haR, ha⟩ := hlift (QuaternionGroup.a 1)
  obtain ⟨b, hbR, hb⟩ := hlift (QuaternionGroup.xa 0)
  have hsq : ∀ (c : ↥M) (q : QuaternionGroup 2), (QuotientGroup.mk c : MBar β) = (eQ q : MBar β) →
      q ^ 2 ≠ 1 → (c : X) ^ 2 ≠ 1 := by
    intro c q hc hq h
    apply hq
    apply eQ.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, ← hc, ← QuotientGroup.mk_pow,
      show c ^ 2 = 1 from Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one]),
      QuotientGroup.mk_one, map_one, Subgroup.coe_one]
  refine ⟨R, hRle, hRp, hR₀R hβR₀, mul_mem (hR₀R hxR₀) (hR₀R htR₀), hzR, hzc, ?_, a, haR, b, hbR,
    hsq a _ ha hqa,
    hsq b _ hb hqb, ?_⟩
  ·
    have hcard : Nat.card R = Nat.card Rb := by
      rw [hRbdef, GSThmB.OddQuot.card_map_of_isPGroup hR'p,
        Nat.card_congr (subgroupOfEquivOfLe hRM).toEquiv]
    have hQ8 : Nat.card ↥(Rb ⊓ (E ⊓ Cb)) = 8 := by
      rw [← Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hβR : β ∈ R := hR₀R hβR₀
    have hβbR : betaBar β ∈ Rb := ⟨⟨β, hβM⟩, hβR, rfl⟩
    have hβbC : betaBar β ∈ centralizer (E : Set (MBar β)) :=
      mem_centralizer_iff.mpr fun g _ => ((mem_center_iff.mp h412.betaBar_mem.2) g)
    have htbR : hs.setup.tBar i j ∈ Rb := ⟨⟨t, htM⟩, hR₀R htR₀, rfl⟩
    have hxbR : (QuotientGroup.mk ⟨x, hxM⟩ : MBar β) ∈ Rb := ⟨⟨x, hxM⟩, hR₀R hxR₀, rfl⟩
    have hxbt : (QuotientGroup.mk ⟨x, hxM⟩ : MBar β) * hs.setup.tBar i j =
        hs.setup.tBar i j * QuotientGroup.mk ⟨x, hxM⟩ := by
      change (QuotientGroup.mk (⟨x, hxM⟩ * ⟨t, htM⟩) : MBar β) =
        QuotientGroup.mk (⟨t, htM⟩ * ⟨x, hxM⟩)
      rw [show (⟨x, hxM⟩ * ⟨t, htM⟩ : ↥M) = ⟨t, htM⟩ * ⟨x, hxM⟩ from Subtype.ext hxt]
    have hxout := hs.l34_x_outer h412 hY hout hxD hxρ (Or.inl rfl) hxM
    have hxtout := hs.l34_x_outer h412 hY hout hxD hxρ (Or.inr rfl) hxtM
    have h64 := le_card_of_outer hs.KBar_le_layer
      (nonabelian_of_lieModel_psl2 (hs.lieModel_KBar h412)) (R := Rb)
      (Q := Rb ⊓ (E ⊓ Cb)) inf_le_left (inf_le_right.trans inf_le_left) hQ8 hβbR hβbC
      hs.betaBar_ne_one htbR hxbR hs.tBar_sq hxbt hout hxout hxtout
    rw [hcard]
    exact h64
  ·
    intro hab
    apply hqab
    apply eQ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      show a * b = b * a from Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hab])]

end Setting46e

end CFSG.ComponentClassification.HarrisLit
