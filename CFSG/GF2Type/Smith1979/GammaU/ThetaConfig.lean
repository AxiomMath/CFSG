module

public import CFSG.LargeExtraspecial.S10EightM
public import CFSG.GF2Type.Smith1979.GammaU.Dict2
public import CFSG.GF2Type.Smith1980Orth.Setup
public import CFSG.LargeExtraspecial.S10FourW6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU.Dict

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S10
  CFSG.LargeExtraspecial.S6 CFSG.GF2Type.Smith1980Orth CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem act_Γ₁_ne_E00 : ∀ s : Gm, s.2 = 1 → s ^ 3 = 1 → s ≠ 1 → act s E00 ≠ E00 := by
  decide +kernel

theorem pf_act_Γ₁ : ∀ s : Gm, s.2 = 1 → pf E00 (act s E00) = 0 := by decide +kernel

theorem act_Γ₁_ne_act_Γ₂' : ∀ s : Gm, s.2 = 1 → s ^ 3 = 1 → s ≠ 1 → ∀ δ : Gm, δ.1 = 1 →
    act s E00 ≠ act δ E00 := by
  decide +kernel

theorem act_Γ₁_ne_act_Γ₂ (s δ : Gm) (h2 : s.2 = 1) (h3 : s ^ 3 = 1) (h1 : s ≠ 1) (hδ : δ.1 = 1) :
    act s E00 ≠ act δ E00 :=
  act_Γ₁_ne_act_Γ₂' s h2 h3 h1 δ hδ

theorem Γ₁_gen_conj : ∀ s : Gm, s.2 = 1 → s ^ 3 = 1 → s ≠ 1 → ∀ γ : Gm, γ.2 = 1 →
    ∃ i < 3, ∃ j < 2, γ = τ₁ ^ j * (τ₁ * (s * τ₁ * s⁻¹)) ^ i := by
  decide +kernel

theorem τ₁_mem_stabA : τ₁ ∈ stabA := (act_E00_iff τ₁).2 (Or.inr (Or.inl rfl))

theorem τ₂_mem_stabA : τ₂ ∈ stabA := (act_E00_iff τ₂).2 (Or.inr (Or.inr (Or.inl rfl)))

theorem config_of_dec108 (I : TimInputs) (hw : S.width = 6) (hP : NoPGL25 S g) {t : S.O}
    {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb) {θ : S.O}
    (hθ : θ ∈ ⁅Yb, Yb⁆) (hθ1 : θ ≠ 1) :
    ∀ s ∈ S.Lbar g, s ≠ 1 → s * θ = θ * s → 4 ≤ finrank (ZMod 2) (Vt S g s) →
      ∃ h : S.M, s ∈ S.Lbar ((h : G) * g) ∧
        (∀ l ∈ S.Lbar ((h : G) * g), l * θ * l⁻¹ = θ ∨ l * θ * l⁻¹ = θ⁻¹) ∧
        aT S ((h : G) * g) ∈ Dt S g ∧
        (∃ v, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = aT S ((h : G) * g)) ∧
        aT S ((h : G) * g) ≠ aT S g ∧
        aT S ((h : G) * g) ≠ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) ∧
        aT S ((h : G) * g) ≠ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g)) ∧
        aT S g ∈ Dt S ((h : G) * g) ∧
        Nat.card (Subgroup.closure ((S.Lbar g : Set S.O) ∪ (S.Lbar ((h : G) * g) : Set S.O) ∪
          {θ})) = 1152 := by
  intro s hs hs1 hsθ hdim
  have hsE : s ∈ S.Lbar g ⊓ Xb := ⟨hs, D.mem_Xb_of_commute I.hCE hθ hθ1 hs hsθ⟩
  have Y : Hyp10 S g s := by
    rcases D.Rbar_eq_or_hyp10 I.hCE hP hsE hs1 with ⟨-, -, h2⟩ | Y
    · omega
    · exact Y
  obtain ⟨Xτ, Yτ, ⟨Dτ⟩, -, hYY⟩ := D.exists_dec108_of_hyp10 I.hCE hsE Y
  have hθ' : θ ∈ ⁅Yτ, Yτ⁆ := hYY ▸ hθ
  obtain ⟨F, hFY, hXF, -⟩ := Dτ.exists_frame I.hCE
  obtain ⟨hσ2, hσ3, hσ1⟩ := σ₁_spec
  obtain ⟨k, hk, -, hkπ⟩ := F.exists_cube_lift I.hCE hσ3
  have hkX : S.ρ k ∈ Xτ := by
    rw [hXF]
    exact F.mem_pre.2 ⟨hk, by rw [hkπ]; exact mem_Γ₁.2 hσ2⟩
  have hkW : S.ρ k ∈ fixWstar Y := ⟨hk, Dτ.fixW _ hkX⟩
  have hinf := Abar_inf_Lbar_conj Y F hk hkW (by rw [hkπ]; exact hσ2) (by rw [hkπ]; exact hσ3)
    (by rw [hkπ]; exact hσ1)
  have hN := Nbar_eq_sup_of_inf I.hCE Y hk hinf
  have hsk : s ∈ S.Lbar ((k : G) * g) := mem_Lbar_mul_of_mem_Rbar Y.H Y.ht hk
  have hLk : S.Lbar ((k : G) * g) ≤ Rbar S g s := Lbar_mul_le_Rbar hsk
  have hL : S.Lbar g ≤ Rbar S g s := Lbar_le_Rbar hs
  have hθY : θ ∈ Yτ := ((Dτ.dec.mem_commutator_iff).1 hθ').1
  have hθR : θ ∈ Rbar S g s := Dτ.dec.le_Rbar_right hθY
  have hφe : F.φ (bV hsk) = act σ₁ E00 := by rw [bV_eq_resV Y hk hsk, F.φ_resV_aV, hkπ]
  obtain ⟨hθπ1, -, -⟩ := Dτ.dec.pi_spec I.hCE hFY hθ' hθ1
  have hθθR : θ * θ ∈ Rbar S g s := mul_mem hθR hθR
  have hθa : (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) =
      ((resV Y.haQ s ⟨θ, hθR⟩ (aV Y.ht) : Vt S g s) : S.Qt) := rfl
  have hθθa : (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g)) =
      ((resV Y.haQ s ⟨θ * θ, hθθR⟩ (aV Y.ht) : Vt S g s) : S.Qt) := rfl
  have hπθθ : (F.π ⟨θ * θ, hθθR⟩).1 = 1 := by
    have : (⟨θ * θ, hθθR⟩ : Rbar S g s) = ⟨θ, hθR⟩ * ⟨θ, hθR⟩ := rfl
    rw [this, map_mul, Prod.fst_mul, hθπ1, one_mul]
  have hcP : aT S ((k : G) * g) ∈ Dt S g := by
    have h1 := (beta_aV_eq_zero_iff Y.H Y.C Y.ht Y.ht1 Y.hVQ (bV hsk)).mp (by
      rw [F.beta_eq, F.base, hφe]
      exact pf_act_Γ₁ σ₁ hσ2)
    rwa [coe_bV] at h1
  have hea : aT S ((k : G) * g) ≠ aT S g := fun h => by
    have h1 : bV hsk = aV Y.ht := Subtype.ext (by rw [coe_bV]; exact h)
    have h2 := congrArg F.φ h1
    rw [hφe, F.base] at h2
    exact act_Γ₁_ne_E00 σ₁ hσ2 hσ3 hσ1 h2
  have haPc : aT S g ∈ Dt S ((k : G) * g) := by
    have haQ := X.haQ
    have hcQ : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k.2 haQ
    have hca' : (k : G) * g * S.z * ((k : G) * g)⁻¹ ≠ g * S.z * g⁻¹ := fun e =>
      hea (by simp only [aT, e])
    have hzQa : S.z ∈ S.Qa g := S.z_mem_Qa_of_mem_QG rfl haQ X.H.conj_ne
    have hcQa := mem_Qa_of_cl_mem' hzQa hcQ hcP
    have haQc := S.mem_Qa_symm hca' hcQa
    exact S.cl_mem_clSub ⟨haQ, haQc⟩ haQ
  refine ⟨k, hsk, ?_, hcP, ?_, hea, ?_, ?_, haPc, ?_⟩
  ·
    intro l hl
    have hmem := Dτ.dec.conj_mem_commutator (hLk hl) hθ'
    have hne : l * θ * l⁻¹ ≠ 1 := fun h => hθ1 (by
      calc θ = l⁻¹ * (l * θ * l⁻¹) * l := by group
        _ = 1 := by rw [h]; group)
    exact Dτ.dec.eq_or_eq_inv_of_mem_commutator hθ' hθ1 hmem hne
  ·
    exact mem_commSpace.1 (Vt_le_commSpace Y.H hs1 (bV hsk).2)
  · intro h
    have h1 : bV hsk = resV Y.haQ s ⟨θ, hθR⟩ (aV Y.ht) :=
      Subtype.ext (by rw [coe_bV]; exact h.trans hθa)
    have h2 := congrArg F.φ h1
    rw [hφe, F.φ_resV_aV] at h2
    exact act_Γ₁_ne_act_Γ₂ σ₁ _ hσ2 hσ3 hσ1 hθπ1 h2
  · intro h
    have h1 : bV hsk = resV Y.haQ s ⟨θ * θ, hθθR⟩ (aV Y.ht) :=
      Subtype.ext (by rw [coe_bV]; exact h.trans hθθa)
    have h2 := congrArg F.φ h1
    rw [hφe, F.φ_resV_aV] at h2
    exact act_Γ₁_ne_act_Γ₂ σ₁ _ hσ2 hσ3 hσ1 hπθθ h2
  ·
    let H : Subgroup S.O :=
      Subgroup.closure ((S.Lbar g : Set S.O) ∪ (S.Lbar ((k : G) * g) : Set S.O) ∪ {θ})
    have hLH : S.Lbar g ≤ H := fun x hx => subset_closure (Or.inl (Or.inl hx))
    have hLkH : S.Lbar ((k : G) * g) ≤ H := fun x hx => subset_closure (Or.inl (Or.inr hx))
    have hθH : θ ∈ H := subset_closure (Or.inr rfl)
    have hHR : H ≤ Rbar S g s := by
      rw [closure_le]
      rintro x ((hx | hx) | hx)
      · exact hL hx
      · exact hLk hx
      · rw [Set.mem_singleton_iff.1 hx]
        exact hθR
    have hNH : Nbar S g s ≤ H := by
      rw [hN]
      exact sup_le (inf_le_left.trans hLH) (inf_le_left.trans hLkH)
    let Γ' : Subgroup Gm := (H.subgroupOf (Rbar S g s)).map F.π
    have hmemΓ' : ∀ x (hx : x ∈ H) (hxR : x ∈ Rbar S g s), F.π ⟨x, hxR⟩ ∈ Γ' :=
      fun x hx hxR => ⟨⟨x, hxR⟩, mem_subgroupOf.2 hx, rfl⟩
    obtain ⟨x₁, hx₁, hπx₁⟩ := F.exists_Lbar_of_stab τ₁_mem_stabA
    obtain ⟨x₂, hx₂, hπx₂⟩ := F.exists_Lbar_of_stab τ₂_mem_stabA
    have hx₁' : S.ρ k * x₁ * (S.ρ k)⁻¹ ∈ S.Lbar ((k : G) * g) := conj_mem_Lbar_mul S k hx₁
    have hτ₁ : τ₁ ∈ Γ' := hπx₁ ▸ hmemΓ' _ (hLH hx₁) _
    have hτ₂ : τ₂ ∈ Γ' := hπx₂ ▸ hmemΓ' _ (hLH hx₂) _
    have hτ₁' : σ₁ * τ₁ * σ₁⁻¹ ∈ Γ' := by
      have h := hmemΓ' _ (hLkH hx₁') (hLk hx₁')
      have e : (⟨S.ρ k * x₁ * (S.ρ k)⁻¹, hLk hx₁'⟩ : Rbar S g s) =
          ⟨S.ρ k, hk⟩ * ⟨x₁, Lbar_le_Rbar Y.ht hx₁⟩ * (⟨S.ρ k, hk⟩)⁻¹ := rfl
      rwa [e, map_mul, map_mul, map_inv, hkπ, hπx₁] at h
    have hθΓ' : F.π ⟨θ, hθR⟩ ∈ Γ' := hmemΓ' _ hθH hθR
    obtain ⟨hθπ1', hθπ3, hθπne⟩ := Dτ.dec.pi_spec I.hCE hFY hθ' hθ1
    have htop : Γ' = ⊤ := by
      refine eq_top_iff.2 fun γ _ => ?_
      rw [eq_mul_of_factors γ]
      refine mul_mem ?_ ?_
      · obtain ⟨i, -, j, -, hij⟩ := Γ₁_gen_conj σ₁ hσ2 hσ3 hσ1 ((γ.1, 1) : Gm) rfl
        rw [hij]
        exact mul_mem (pow_mem hτ₁ j) (pow_mem (mul_mem hτ₁ hτ₁') i)
      · obtain ⟨i, -, j, -, hij⟩ := Γ₂_gen (F.π ⟨θ, hθR⟩) hθπ1' hθπ3 hθπne ((1, γ.2) : Gm) rfl
        rw [hij]
        exact mul_mem (pow_mem hτ₂ j) (pow_mem hθΓ' i)
    have hRH : Rbar S g s ≤ H := by
      intro r hr
      obtain ⟨w, hw, hwr⟩ : F.π ⟨r, hr⟩ ∈ Γ' := htop ▸ mem_top _
      have hker : ((⟨r, hr⟩ * w⁻¹ : Rbar S g s) : S.O) ∈ Nbar S g s :=
        (F.ker _).1 (by rw [map_mul, map_inv, hwr, mul_inv_cancel])
      have h1 := mul_mem (hNH hker) (mem_subgroupOf.1 hw)
      simpa using h1
    have hEq : H = Rbar S g s := le_antisymm hHR hRH
    change Nat.card H = 1152
    rw [hEq, F.card_Rbar]
    have h2 := two_mul_card_Nbar I.hCE Y
    rw [Y.card_Abar, hw] at h2
    norm_num at h2
    omega

end CFSG.GF2Type.Smith1979.GammaU.Dict
