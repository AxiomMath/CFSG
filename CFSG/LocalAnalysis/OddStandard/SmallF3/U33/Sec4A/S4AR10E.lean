module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR10C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR10D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41UA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise
open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

section Abstract

variable {G : Type} [Group G]

theorem r10_nonabelian_of_dq {K : Subgroup G}
    (hK : Nonempty (↥K ≃* DihedralGroup 4) ∨ Nonempty (↥K ≃* QuaternionGroup 2)) :
    ∃ d₁ ∈ K, ∃ d₂ ∈ K, d₁ * d₂ ≠ d₂ * d₁ := by
  have key : ∀ {D : Type} [Group D] (e : ↥K ≃* D) (a b : D), a * b ≠ b * a →
      ∃ d₁ ∈ K, ∃ d₂ ∈ K, d₁ * d₂ ≠ d₂ * d₁ := by
    intro D _ e a b hab
    refine ⟨(e.symm a : G), (e.symm a).2, (e.symm b : G), (e.symm b).2, fun hc => hab ?_⟩
    have h1 : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext hc
    simpa using congrArg e h1
  rcases hK with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact key e (DihedralGroup.r 1) (DihedralGroup.sr 0) (by decide)
  · exact key e (QuaternionGroup.a 1) (QuaternionGroup.xa 0) (by decide)

variable [Finite G] {R Z X Y : Subgroup G} {t ρ : G}

theorem r10_tau_false {τ : G} (H : R10Hyp R Z X Y t ρ) (hZt : ∀ z ∈ Z, z * t = t * z)
    (hTZ : ∀ z ∈ Z, ∃ r ∈ R, r * t * r⁻¹ = t * z) (hτ2 : τ * τ = 1)
    (hτ : τ ∈ R ∨ ∃ k ∈ R, τ = t * k)
    (hno : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 2 E → Nat.card E = 16 →
      E ≤ centralizer ({τ} : Set G) → False)
    (hRτ : ∀ r ∈ R, r * t * r⁻¹ ≠ τ) : False := by
  by_cases hτR : τ ∈ R
  · rcases H.sl.invol τ hτR hτ2 with hX | hY
    · exact hno X H.sl.X_elem H.sl.card_X fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (H.sl.X_comm x hx τ hX)
    · exact hno Y H.sl.Y_elem H.sl.card_Y fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (H.sl.Y_comm y hy τ hY)
  · obtain ⟨k, hk, hτk⟩ := hτ.resolve_left hτR
    by_cases hkZ : k ∈ Z
    · obtain ⟨r, hr, hrk⟩ := hTZ k hkZ
      exact hRτ r hr (by rw [hrk, hτk])
    · exact r10_no_tau H hZt hτ2 hτR hk hτk hkZ hno

theorem r10_conj_mem_F {V F : Subgroup G} (hFV : F ≤ V) (hF : m11AutInv V F) {w : G}
    (hw : w ∈ normalizer (V : Set G)) {f : G} (hf : f ∈ F) : w * f * w⁻¹ ∈ F := by
  have h1 := hF (V.normalizerMonoidHom ⟨w, hw⟩) ⟨f, hFV hf⟩ hf
  rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1

end Abstract

section Main

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem r10_t_orbit (h : L41GPh8 t L S x₁ x₂ lam rho) {r : G} (hr : r ∈ l41R t x₁ x₂ rho) :
    ∃ z ∈ fourGrp x₁ x₂, r * t * r⁻¹ = t * z := by
  have h1 : r * t * r⁻¹ ∈ conjIn (l41R t x₁ x₂ rho) t := ⟨r, hr, rfl⟩
  rw [h.rfacts.orbit_t] at h1
  obtain ⟨z, hz, hzt⟩ := h1
  exact ⟨z, hz, hzt.symm⟩

theorem r10_t_orbit' (h : L41GPh8 t L S x₁ x₂ lam rho) {z : G} (hz : z ∈ fourGrp x₁ x₂) :
    ∃ r ∈ l41R t x₁ x₂ rho, r * t * r⁻¹ = t * z := by
  have h1 : t * z ∈ t • (fourGrp x₁ x₂ : Set G) := ⟨z, hz, rfl⟩
  rw [← h.rfacts.orbit_t] at h1
  obtain ⟨r, hr, hrt⟩ := h1
  exact ⟨r, hr, hrt⟩


theorem r10_hyp (h : L41GPh9 t L S x₁ x₂ lam rho) (e : ↥(l41R t x₁ x₂ rho) ≃* UT3 F4c) :
    R10Hyp (l41R t x₁ x₂ rho) (fourGrp x₁ x₂) (r10X e) (r10Y e) t rho := by
  have hρ3 : rho * rho * rho = 1 := by
    have := n4_rho_cube h.toCtx0
    rwa [pow_succ, pow_two] at this
  have sl := sl34Data_of_iso e h.rfacts.fourGrp_le h.rfacts.fourGrp_central
    (n4_card_four h.toCtx0)
  have hρR : ∀ r ∈ l41R t x₁ x₂ rho, rho * r * rho⁻¹ ∈ l41R t x₁ x₂ rho := fun r hr =>
    m11_rho_conj_R h.toL41GPh8 hr
  obtain ⟨hρX, hρY⟩ := r10_rho_inv sl hρ3 hρR
  have hB : ∀ a ∈ l41R t x₁ x₂ rho, a * t = t * a → a ∈ baseGrp x₁ x₂ := by
    intro a ha hat
    have : a ∈ l41R t x₁ x₂ rho ⊓ invCent t :=
      Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr hat⟩
    rwa [h.rfacts.cent_t] at this
  have hΩ : ∀ a ∈ baseGrp x₁ x₂, a * a = 1 → a ∈ fourGrp x₁ x₂ := by
    intro a ha ha2
    rw [h.wreath.fourGrp_eq_omega.1]
    exact Subgroup.subset_closure ⟨ha, by rw [pow_two]; exact ha2⟩
  exact
    { sl := sl
      comm_le := fun r hr s hs => r10_comm_mem h.toL41GPh8 hr hs
      t_orbit := fun r hr => r10_t_orbit h.toL41GPh8 hr
      t_cent_X := fun a ha hat => hΩ a (hB a (sl.X_le ha) hat) (sl.X_sq a ha)
      t_cent_Y := fun a ha hat => hΩ a (hB a (sl.Y_le ha) hat) (sl.Y_sq a ha)
      rho_cube := hρ3
      rho_R := hρR
      rho_Z := fun z hz => m11_rho_conj_F2 h.toL41GPh8 hz
      rho_X := hρX
      rho_Y := hρY
      rho_fix := fun r hr hρ => m11_fix_R h.toL41GPh8 hr hρ
      rho_t := (m13_t_comm_L h.toL41GPh5 h.rho_mem).symm }

theorem r10_cent_sylow (h : Ctx0 t L S x₁ x₂ lam rho) {𝒮 : Subgroup G} (h𝒮 : IsPGroup 2 𝒮)
    (hV𝒮 : l41V S t x₁ x₂ ≤ 𝒮) {c : G} (hc : c ∈ 𝒮) (hct : c * t = t * c) :
    c ∈ l41V S t x₁ x₂ := by
  have hSV : S ≤ l41V S t x₁ x₂ := le_sup_right
  have hK_le : S ⊔ zpowers c ≤ invCent t :=
    sup_le h.le_invCent
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hct))
  have hK𝒮 : S ⊔ zpowers c ≤ 𝒮 :=
    sup_le (hSV.trans hV𝒮) (Subgroup.zpowers_le.mpr hc)
  have hEq := eq_of_isPGroup_of_odd_relIndex le_sup_left hK_le (h𝒮.to_le hK𝒮) h.relIndex_odd
  have hmem : c ∈ S ⊔ zpowers c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  rw [hEq] at hmem
  exact hSV hmem

theorem r10_case_ii (h : L41GPh9 t L S x₁ x₂ lam rho)
    (hnab : ∃ d₁ ∈ l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G),
      ∃ d₂ ∈ l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G), d₁ * d₂ ≠ d₂ * d₁)
    (e : ↥(l41R t x₁ x₂ rho) ≃* UT3 F4c) : False := by
  have H := r10_hyp h e
  have hRV := m11_R_le_V h.toL41GPh8
  have hF := r10_autInv_F h H.sl.comm_Z H.sl.cent_pair hnab
  obtain ⟨𝒮, h𝒮⟩ := exists_sylow_gt h.normalizerFacts.V_pGroup h.normalizerFacts.V_not_sylow
  have h𝒮p : IsPGroup 2 (𝒮 : Subgroup G) := 𝒮.isPGroup'
  obtain ⟨w, hw𝒮, hwN, hwV⟩ := exists_mem_normalizer_not_mem h𝒮p h𝒮
  have htF : t ∈ l41F t x₁ x₂ rho := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hτF := r10_conj_mem_F (m11_F_le_V h.toL41GPh8) hF hwN htF
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have hτ2 : w * t * w⁻¹ * (w * t * w⁻¹) = 1 := by
    calc w * t * w⁻¹ * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  refine r10_tau_false H (fun z hz => (m13_t_comm_base h.toL41GPh5
    (m11_fourGrp_le_B x₁ x₂ hz)).symm) (fun z hz => r10_t_orbit' h.toL41GPh8 hz) hτ2
    (m13_mem_F h.toL41GPh8 hτF) ?_ ?_
  · intro E hE hc hle
    exact l41_no_e16_cent_conj h.toL41GPh1 hE hc w hle
  · intro r hr hrτ
    apply hwV
    have hr𝒮 : r ∈ (𝒮 : Subgroup G) := h𝒮.le (hRV hr)
    have hc𝒮 : r⁻¹ * w ∈ (𝒮 : Subgroup G) := (𝒮 : Subgroup G).mul_mem
      ((𝒮 : Subgroup G).inv_mem hr𝒮) hw𝒮
    have hct : (r⁻¹ * w) * t = t * (r⁻¹ * w) := by
      have h1 : (r⁻¹ * w) * t * (r⁻¹ * w)⁻¹ = t := by
        calc (r⁻¹ * w) * t * (r⁻¹ * w)⁻¹ = r⁻¹ * (w * t * w⁻¹) * r := by group
          _ = r⁻¹ * (r * t * r⁻¹) * r := by rw [hrτ]
          _ = t := by group
      exact mul_inv_eq_iff_eq_mul.mp h1
    have hcV := r10_cent_sylow h.toCtx0 h𝒮p h𝒮.le hc𝒮 hct
    have hw : w = r * (r⁻¹ * w) := by group
    rw [hw]
    exact (l41V S t x₁ x₂).mul_mem (hRV hr) hcV

theorem l41_rabelian_of (h : L41GPh9 t L S x₁ x₂ lam rho) :
    IsMulCommutative (l41R t x₁ x₂ rho) := by
  rcases h.hs29 with hab | ⟨⟨e₀⟩, hlam, -⟩
  · exact hab
  · exact (r10_case_ii h (r10_nonabelian_of_dq hlam) (e₀.trans sylLCongr)).elim

end Main

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l41_rabelian_holds : L41RAbelianStmt :=
  fun h => S4A.l41_rabelian_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
