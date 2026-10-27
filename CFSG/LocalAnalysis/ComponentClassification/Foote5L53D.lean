module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53C
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Foote81L6.Lemma1
public import CFSG.CGT.Stroth77.AmbientSplit
public import CFSG.CGT.Stroth77.Section223Sylow
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CGT.Timmesfeld75.Sec3Conj
public import CFSG.CGT.Timmesfeld75.Sec62Orbit
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.ClassicalInvolution.NormalQuaternion
public import CFSG.GroupTheory.CharacteristicNormalizer
public import CFSG.GroupTheory.DisjointSupCard
public import CFSG.GroupTheory.SubgroupTransport
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.Foote5AutFour
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51D
public import CFSG.LocalAnalysis.ComponentClassification.Foote5TypesC
public import CFSG.LocalAnalysis.ComponentClassification.Sol78NoStrongEmb
public import CFSG.LocalAnalysis.GH72.WalterE16
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.Mathlib.GroupTheory.ConjCentralizer
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.EmptyFaithful.S152N2Z15
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5L2T
public import CFSG.RankThree.OddKernel.OddLift
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.TwoSignalizer
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.J4SBinary
public import CFSG.Walter.PSL2Facts

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem exists_inner_of_klein (h𝕊 : FooteSimpleType 𝕊) {A₁ A₂ : G} (h1S : A₁ ∈ S)
    (h2S : A₂ ∈ S) (h12 : A₁ * A₂ = A₂ * A₁) (h11 : A₁ * A₁ = 1) (h22 : A₂ * A₂ = 1)
    (h1Q : A₁ ∉ Q) (h2Q : A₂ ∉ Q) (h12Q : A₁ * A₂ ∉ Q) :
    actG L ε A₁ ∈ innAut5 𝕊 ∨ actG L ε A₂ ∈ innAut5 𝕊 ∨ actG L ε (A₁ * A₂) ∈ innAut5 𝕊 := by
  have hA11 : A₁ ≠ 1 := fun h1 => h1Q (h1 ▸ one_mem _)
  have hA21 : A₂ ≠ 1 := fun h1 => h2Q (h1 ▸ one_mem _)
  have hA12 : A₁ ≠ A₂ := fun h1 => h12Q (by rw [h1, h22]; exact one_mem _)
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions A₁ A₂ h11 h22 h12 with hV
  have hVmem : ∀ e, e ∈ V ↔ e = A₁ * A₂ ∨ e = A₁ ∨ e = A₂ ∨ e = 1 := fun e => by
    change e ∈ ({A₁ * A₂, A₁, A₂, 1} : Set G) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hV4 : IsKleinFour V :=
    GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions A₁ A₂ h11 h22 hA11 hA21 hA12 h12
  have hVS : V ≤ S := fun e he => by
    rcases (hVmem e).mp he with rfl | rfl | rfl | rfl
    · exact mul_mem h1S h2S
    · exact h1S
    · exact h2S
    · exact one_mem _
  have hVN : V ≤ normalizer (L : Set G) := hVS.trans h.S_le
  have hVC : V ⊓ coreActionKernel L = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    have heQ : e ∈ Q := by
      rw [← h.inf_coreActionKernel]
      exact mem_inf.mpr ⟨hVS (mem_inf.mp he).1, (mem_inf.mp he).2⟩
    rcases (hVmem e).mp (mem_inf.mp he).1 with rfl | rfl | rfl | rfl
    · exact absurd heQ h12Q
    · exact absurd heQ h1Q
    · exact absurd heQ h2Q
    · exact one_mem _
  have hcard := card_eq_card_inf_mul_card_actImage ε hVN
  rw [hVC, card_bot, one_mul, IsKleinFour.card_four] at hcard
  have hsq : ∀ α ∈ actImage L ε V, α * α = 1 := by
    intro α hα
    obtain ⟨e, he, rfl⟩ := (mem_actImage ε hVN).mp hα
    have hee : e * e = 1 := congrArg Subtype.val (IsKleinFour.mul_self (G := V) ⟨e, he⟩)
    rw [← actG_mul ε (hVN he) (hVN he), hee, actG_one]
  have hne := fourgroup_inf_innAut_ne_bot h𝕊 hcard.symm hsq
  obtain ⟨α, hα1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨e, he, hαe⟩ := (mem_actImage ε hVN).mp (mem_inf.mp α.2).1
  have hinn : actG L ε e ∈ innAut5 𝕊 := hαe ▸ (mem_inf.mp α.2).2
  rcases (hVmem e).mp he with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr hinn)
  · exact Or.inl hinn
  · exact Or.inr (Or.inl hinn)
  · exact absurd (Subtype.ext (by rw [← hαe, actG_one]; rfl)) hα1

theorem eq_one_or_eq_t_of_pgl (hD : Foote5AutData 𝕊 Lin) {y : G} (hyS : y ∈ S)
    (hy2 : y * y = 1) (hlin : actG L ε y ∈ Lin) (hinn : actG L ε y ∉ innAut5 𝕊) {r : G}
    (hr : r ∈ S ⊓ L) (hry : r * y = y * r) : r = 1 ∨ r = t := by
  have hyN := h.S_le hyS
  have hsq : actG L ε y * actG L ε y = 1 := by rw [← actG_mul ε hyN hyN, hy2, actG_one]
  have hfix2 := hD.pgl_fixed (h.Rbar ε) _ hlin hinn hsq (h.actG_map_Rbar ε hyS)
  have hfixed : ∀ x (hx : x ∈ S ⊓ L), x * y = y * x → psi L ε ⟨x, (mem_inf.mp hx).2⟩ ∈
      ((h.Rbar ε : Subgroup 𝕊) ⊓ MonoidHom.eqLocus (actG L ε y).toMonoidHom
        (MonoidHom.id 𝕊)) := by
    intro x hx hxy
    refine mem_inf.mpr ⟨h.psi_mem_Rbar ε hx, ?_⟩
    show actG L ε y (psi L ε ⟨x, (mem_inf.mp hx).2⟩) = psi L ε ⟨x, (mem_inf.mp hx).2⟩
    rw [actG_psi ε hyN]
    congr 1
    apply Subtype.ext
    change y * x * y⁻¹ = x
    rw [← hxy, mul_inv_cancel_right]
  have hne1 : ∀ x (hx : x ∈ S ⊓ L), x ≠ 1 → psi L ε ⟨x, (mem_inf.mp hx).2⟩ ≠ 1 := by
    intro x hx hx1 h1
    apply hx1
    have h2 : psi L ε ⟨x, (mem_inf.mp hx).2⟩ = psi L ε ⟨1, one_mem _⟩ := by
      rw [h1]
      exact (map_one (psi L ε)).symm
    exact h.eq_of_psi_eq ε hx (one_mem _) h2
  by_contra hrt
  push Not at hrt
  have h3 := three_le_card_of_ne (hfixed r hr hry) (hfixed t h.tR (h.tZ y hyS).symm)
    (hne1 r hr hrt.1) (hne1 t h.tR h.t_ne_one) (fun h1 => hrt.2 (h.eq_of_psi_eq ε hr h.tR h1))
  omega

theorem exists_noncentral_involution_R (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) :
    ∃ y ∈ S ⊓ L, y * y = 1 ∧ ∃ r ∈ S ⊓ L, r * y ≠ y * r := by
  obtain ⟨m, -, ⟨e⟩⟩ := h.exists_dihedral_R
  obtain ⟨a, ha, b, hb, hab⟩ := hna
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁2, ha₂2, rfl⟩ := exists_mul_of_dihedral e ha
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁2, hb₂2, rfl⟩ := exists_mul_of_dihedral e hb
  by_contra hno
  push Not at hno
  have hc : ∀ y ∈ S ⊓ L, y * y = 1 → ∀ r ∈ S ⊓ L, r * y = y * r := hno
  apply hab
  have e1 := hc a₁ ha₁ ha₁2
  have e2 := hc a₂ ha₂ ha₂2
  calc a₁ * a₂ * (b₁ * b₂) = b₁ * b₂ * (a₁ * a₂) := by
        rw [show a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * (b₁ * b₂)) by group,
          ← e2 _ (mul_mem hb₁ hb₂), ← mul_assoc, ← e1 _ (mul_mem hb₁ hb₂), mul_assoc]

include ε in
theorem t_mem_commutator_R (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) : t ∈ ⁅S ⊓ L, S ⊓ L⁆ := by
  obtain ⟨y, hyR, hy2, hnc⟩ := h.exists_noncentral_involution_R hna
  obtain ⟨c, hcR, hc⟩ := h.exists_conj_mul_t ε hD (mem_inf.mp hyR).1 hy2 hnc
  have h1 : t = ⁅y⁻¹, c⁻¹⁆ := by
    rw [commutatorElement_def, inv_inv, inv_inv,
      show y⁻¹ * c⁻¹ * y * c = y⁻¹ * (c⁻¹ * y * c) by group, hc]
    group
  rw [h1]
  exact commutator_mem_commutator (inv_mem hyR) (inv_mem hcR)

theorem open_pRank_R_le : CFSG.Open.pRank 2 (S ⊓ L) ≤ 2 := by
  have h1 := pRank_subgroup_mono (inf_le_right : S ⊓ L ≤ L)
  rw [h.sec4.hrank2 L h.memF] at h1
  rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1

include ε in
theorem exists_U (hD : Foote5AutData 𝕊 Lin) {A₁ A₂ q ρ : G} (h1S : A₁ ∈ S)
    (h11 : A₁ * A₁ = 1) (h1inn : actG L ε A₁ ∉ innAut5 𝕊) (hqQ : q ∈ Q) (hρR : ρ ∈ S ⊓ L)
    (hρ2 : ρ * ρ = 1) (hA₂ : A₂ = q * ρ) (h12 : A₁ * A₂ = A₂ * A₁) (hq1 : q * A₁ = A₁ * q) :
    ∃ U : G, (U = A₁ ∨ U = A₂ ∨ U = A₁ * A₂) ∧
      (∀ x ∈ S ⊓ L ⊔ zpowers A₁, x * U = U * x) ∧ t ∈ ⁅S ⊓ L ⊔ zpowers A₁, S ⊓ L ⊔ zpowers A₁⁆ := by
  have h1N := h.S_le h1S
  have hρ1 : ρ * A₁ = A₁ * ρ := by
    have h2 : q * (ρ * A₁) = q * (A₁ * ρ) := by
      calc q * (ρ * A₁) = A₂ * A₁ := by rw [hA₂, mul_assoc]
        _ = A₁ * A₂ := h12.symm
        _ = q * (A₁ * ρ) := by rw [hA₂, ← mul_assoc, ← hq1, mul_assoc]
    exact mul_left_cancel h2
  have hcent : ∀ U, (∀ r ∈ S ⊓ L, r * U = U * r) → A₁ * U = U * A₁ →
      ∀ x ∈ S ⊓ L ⊔ zpowers A₁, x * U = U * x := by
    intro U hUR hU1 x hx
    have hle : S ⊓ L ⊔ zpowers A₁ ≤ centralizer ({U} : Set G) :=
      sup_le (fun r hr => mem_centralizer_singleton_iff.mpr (hUR r hr))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hU1))
    exact mem_centralizer_singleton_iff.mp (hle hx)
  have hcomm_le : ⁅S ⊓ L, S ⊓ L⁆ ≤ ⁅S ⊓ L ⊔ zpowers A₁, S ⊓ L ⊔ zpowers A₁⁆ :=
    commutator_mono le_sup_left le_sup_left
  have hA₂R : ∀ r ∈ S ⊓ L, ρ * r = r * ρ → r * A₂ = A₂ * r := by
    intro r hr hρr
    rw [hA₂, ← mul_assoc, ← h.commute_Q_R hqQ hr, mul_assoc, ← hρr, mul_assoc]
  have hconj : ∀ U r : G, U * r * U⁻¹ = r → r * U = U * r := fun U r h2 => by
    calc r * U = U * r * U⁻¹ * U := by rw [h2]
      _ = U * r := by group
  have hA2act : ∀ r ∈ S ⊓ L, A₂ * r * A₂⁻¹ = ρ * r * ρ⁻¹ := by
    intro r hr
    have h2 := h.commute_Q_R hqQ (h.conj_mem_R (mem_inf.mp hρR).1 hr)
    rw [hA₂, show q * ρ * r * (q * ρ)⁻¹ = q * (ρ * r * ρ⁻¹) * q⁻¹ by group, h2,
      mul_inv_cancel_right]
  by_cases hpgl : actG L ε A₁ ∈ Lin
  ·
    have hρt := h.eq_one_or_eq_t_of_pgl ε hD h1S h11 hpgl h1inn hρR hρ1
    have hUR : ∀ r ∈ S ⊓ L, r * A₂ = A₂ * r := by
      intro r hr
      refine hA₂R r hr ?_
      rcases hρt with rfl | rfl
      · rw [one_mul, mul_one]
      · exact (h.tZ r (mem_inf.mp hr).1).symm
    have hnc : ∃ r ∈ S ⊓ L, r * A₁ ≠ A₁ * r := by
      by_contra hno
      push Not at hno
      have hsq : actG L ε A₁ * actG L ε A₁ = 1 := by rw [← actG_mul ε h1N h1N, h11, actG_one]
      have hfix2 := hD.pgl_fixed (h.Rbar ε) _ hpgl h1inn hsq (h.actG_map_Rbar ε h1S)
      have hle : (h.Rbar ε : Subgroup 𝕊) ≤ (h.Rbar ε : Subgroup 𝕊) ⊓
          MonoidHom.eqLocus (actG L ε A₁).toMonoidHom (MonoidHom.id 𝕊) := by
        refine le_inf le_rfl fun ρ' hρ' => ?_
        exact (h.actG_fix_iff ε h1S).mpr (fun r hr => (hno r hr).symm) ρ' hρ'
      have h3 := card_le_of_le hle
      rw [h.card_Rbar ε] at h3
      have h4 := h.four_le_card_R
      omega
    obtain ⟨c, hcR, hc⟩ := h.exists_conj_mul_t ε hD h1S h11 hnc
    refine ⟨A₂, Or.inr (Or.inl rfl), hcent A₂ hUR h12, ?_⟩
    have h5 : t = ⁅A₁⁻¹, c⁻¹⁆ := by
      rw [commutatorElement_def, inv_inv, inv_inv,
        show A₁⁻¹ * c⁻¹ * A₁ * c = A₁⁻¹ * (c⁻¹ * A₁ * c) by group, hc]
      group
    rw [h5]
    exact commutator_mem_commutator (inv_mem (mem_sup_right (mem_zpowers A₁)))
      (inv_mem (mem_sup_left hcR))
  ·
    have hsq : actG L ε A₁ * actG L ε A₁ = 1 := by rw [← actG_mul ε h1N h1N, h11, actG_one]
    obtain ⟨γ, hγ⟩ := hD.conj_centralizer (h.Rbar ε) _ hpgl hsq
    have hna := h.nonabelian_R_of_fix ε hD (β := MulAut.conj γ * actG L ε A₁ * (MulAut.conj γ)⁻¹)
      (fun h2 => hpgl (by
        have h3 := hD.normal.conj_mem _ h2 (MulAut.conj γ)⁻¹
        rwa [show (MulAut.conj γ)⁻¹ * (MulAut.conj γ * actG L ε A₁ * (MulAut.conj γ)⁻¹) *
          (MulAut.conj γ)⁻¹⁻¹ = actG L ε A₁ by group] at h3))
      (by rw [show MulAut.conj γ * actG L ε A₁ * (MulAut.conj γ)⁻¹ *
          (MulAut.conj γ * actG L ε A₁ * (MulAut.conj γ)⁻¹) =
          MulAut.conj γ * (actG L ε A₁ * actG L ε A₁) * (MulAut.conj γ)⁻¹ by group, hsq]
          group) hγ
    have htR := hcomm_le (h.t_mem_commutator_R ε hD hna)
    obtain ⟨r₀, hr₀, hr₀2, hact⟩ :=
      h.exists_inner_action ε hD h1S h11 fun h2 => hpgl h2.1
    by_cases hρc : ∀ r ∈ S ⊓ L, ρ * r = r * ρ
    · exact ⟨A₂, Or.inr (Or.inl rfl), hcent A₂ (fun r hr => hA₂R r hr (hρc r hr)) h12, htR⟩
    push Not at hρc
    obtain ⟨r₁, hr₁, hρr₁⟩ := hρc
    have hρ1' : ρ ≠ 1 := fun h2 => hρr₁ (by rw [h2, one_mul, mul_one])
    have hρt : ρ ≠ t := fun h2 => hρr₁ (by rw [h2]; exact (h.tZ r₁ (mem_inf.mp hr₁).1).symm)
    have hr₀ρ : r₀ * ρ = ρ * r₀ := by
      have h2 := hact ρ hρR
      rw [show A₁ * ρ * A₁⁻¹ = ρ by rw [← hρ1, mul_inv_cancel_right]] at h2
      calc r₀ * ρ = r₀ * ρ * r₀⁻¹ * r₀ := by group
        _ = ρ * r₀ := by rw [← h2]
    have ht2 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
    rcases mem_four_of_pRank_le_two h.open_pRank_R_le hρR h.tR hr₀ hρ2 ht2 hr₀2 hρ1'
      h.t_ne_one hρt (h.tZ ρ (mem_inf.mp hρR).1) hr₀ρ (h.tZ r₀ (mem_inf.mp hr₀).1)
      with h3 | h3 | h3 | h3
    · refine ⟨A₁, Or.inl rfl, hcent A₁ (fun r hr => ?_) rfl, htR⟩
      have h4 := hact r hr
      rw [h3, one_mul, inv_one, mul_one] at h4
      exact hconj A₁ r h4
    ·
      refine ⟨A₁ * A₂, Or.inr (Or.inr rfl), hcent _ (fun r hr => ?_) (by
        rw [← mul_assoc, h11, one_mul, h12, mul_assoc, h11, mul_one]), htR⟩
      refine hconj _ r ?_
      rw [show A₁ * A₂ * r * (A₁ * A₂)⁻¹ = A₁ * (A₂ * r * A₂⁻¹) * A₁⁻¹ by group, hA2act r hr,
        hact _ (h.conj_mem_R (mem_inf.mp hρR).1 hr), h3]
      calc ρ * (ρ * r * ρ⁻¹) * ρ⁻¹ = (ρ * ρ) * r * (ρ * ρ)⁻¹ := by group
        _ = r := by rw [hρ2, one_mul, inv_one, mul_one]
    · refine ⟨A₁, Or.inl rfl, hcent A₁ (fun r hr => ?_) rfl, htR⟩
      have h4 := hact r hr
      rw [h3, show t * r * t⁻¹ = r by rw [← h.tZ r (mem_inf.mp hr).1, mul_inv_cancel_right]] at h4
      exact hconj A₁ r h4
    · refine ⟨A₁ * A₂, Or.inr (Or.inr rfl), hcent _ (fun r hr => ?_) (by
        rw [← mul_assoc, h11, one_mul, h12, mul_assoc, h11, mul_one]), htR⟩
      refine hconj _ r ?_
      have hX := h.conj_mem_R (mem_inf.mp hρR).1 hr
      rw [show A₁ * A₂ * r * (A₁ * A₂)⁻¹ = A₁ * (A₂ * r * A₂⁻¹) * A₁⁻¹ by group, hA2act r hr,
        hact _ hX, h3]
      have htX : t * (ρ * r * ρ⁻¹) = ρ * r * ρ⁻¹ * t := (h.tZ _ (mem_inf.mp hX).1).symm
      calc ρ * t * (ρ * r * ρ⁻¹) * (ρ * t)⁻¹ = ρ * (t * (ρ * r * ρ⁻¹)) * t⁻¹ * ρ⁻¹ := by group
        _ = ρ * (ρ * r * ρ⁻¹ * t) * t⁻¹ * ρ⁻¹ := by rw [htX]
        _ = (ρ * ρ) * r * (ρ * ρ)⁻¹ := by group
        _ = r := by rw [hρ2, one_mul, inv_one, mul_one]

end Sec5

end CFSG.ComponentClassification.Foote5
