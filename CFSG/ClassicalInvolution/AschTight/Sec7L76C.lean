module

public import CFSG.ClassicalInvolution.AschTight.Sec7L76B
public import CFSG.ClassicalInvolution.AschTight.Sec7Key
public import CFSG.ClassicalInvolution.AschTight.Sec7L76A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem conjSub_iSup_eq_of_forall_mem {η : Set (Subgroup G)} {x : G}
    (h : ∀ U ∈ η, conjSub x U ∈ η) : conjSub x (⨆ U ∈ η, U) = ⨆ U ∈ η, U := by
  refine conjSub_eq_of_le_self ?_
  rw [conjSub_le_iff]
  refine iSup₂_le fun U hU => ?_
  rw [← conjSub_le_iff]
  exact le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) _ (h U hU) le_rfl

theorem two_of_sylow (hΩ : ConjInvariant Ω) {S S' : Sylow 2 G}
    (h2 : ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω) :
    ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S' : Subgroup G)) → K ⊓ (S' : Subgroup G) ∈ RSet Ω := by
  obtain ⟨k, hk⟩ := exists_conjSub_eq_of_sylow S S'
  intro K hK hKS
  have e : K ⊓ (S' : Subgroup G) = conjSub k (conjSub k⁻¹ K ⊓ (S : Subgroup G)) := by
    rw [conjSub_inf, conjSub_conjSub_inv, hk]
  have hc : 2 < Nat.card ↥(conjSub k⁻¹ K ⊓ (S : Subgroup G)) := by
    have := natCard_conjSub (conjSub k⁻¹ K ⊓ (S : Subgroup G)) k
    rw [← e] at this
    omega
  rw [e]
  exact RSet.conj hΩ (h2 _ (hΩ k⁻¹ K hK) hc) k

theorem commutator_mem_of_two (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h611 : EtaMeets Ω)
    (h610 : EtaActsR Ω) (h67 : RCommute Ω) (hkey : KeyOn Ω) {S : Sylow 2 G}
    (h2 : ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R T : Subgroup G} (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) {r t : G} (hr : r ∈ R) (ht : t ∈ T) :
    r * t * r⁻¹ * t⁻¹ ∈ W ⊔ OCW W := by
  have hW2 := isPGroup_of_mem_WSet hW
  obtain ⟨η, hη, hWη⟩ := hW
  have hηW : ∀ V ∈ η, V ≤ W := fun V hV =>
    hWη ▸ le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) V hV le_rfl
  obtain ⟨S₁, hS₁⟩ :=
    (IsPGroup.to_sup_of_normal_right' (isPGroup_of_mem_RSet hR.1) hW2 hR.2).exists_le_sylow
  obtain ⟨S₂, hS₂⟩ :=
    (IsPGroup.to_sup_of_normal_right' (isPGroup_of_mem_RSet hT.1) hW2 hT.2).exists_le_sylow
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT.1
  have h8 := hΩ.eight_le_of_mem_RSet hp hT.1
  have hJS₂ : 2 < Nat.card ↥(J ⊓ (S₂ : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hTJ.1 (le_sup_left.trans hS₂))
    omega
  have hA : J ⊓ W ∈ η := by
    have := h611 S₂ η hη (fun V hV => (hηW V hV).trans (le_sup_right.trans hS₂)) J hJ hJS₂
    rwa [← hWη] at this
  have hAU := mem_USet_of_mem_etaG hη hA
  obtain ⟨-, -, -, -, -, -, -, -, hA4⟩ := hΩ.exists_data_of_mem_USet hp hAU
  have hWS₁ : W ≤ (S₁ : Subgroup G) := le_sup_right.trans hS₁
  have hAT₁ : J ⊓ W ≤ J ⊓ (S₁ : Subgroup G) := inf_le_inf_left J hWS₁
  have hJS₁ : 2 < Nat.card ↥(J ⊓ (S₁ : Subgroup G)) := by
    have := Subgroup.card_le_of_le hAT₁
    omega
  have hT₁ : J ⊓ (S₁ : Subgroup G) ∈ RSet Ω := two_of_sylow hΩ.conjInvariant h2 J hJ hJS₁
  have hT₁D : J ⊓ (S₁ : Subgroup G) ∈ DSet Ω W := by
    refine ⟨hT₁, fun x hx => ?_⟩
    rw [mem_normalizer_iff_conjSub_eq, hWη]
    exact conjSub_iSup_eq_of_forall_mem (h610 S₁ η hη (fun V hV => (hηW V hV).trans hWS₁) _ hT₁
      inf_le_right x hx)
  have hkT := hkey W ⟨η, hη, hWη⟩ _ hT₁D T hT J hJ inf_le_left hTJ.1
  have hRT₁ : ∀ t₁ ∈ J ⊓ (S₁ : Subgroup G), r * t₁ * r⁻¹ * t₁⁻¹ ∈ W := by
    by_cases hRe : R = J ⊓ (S₁ : Subgroup G)
    · obtain ⟨J', hJ', hT₁J'⟩ := exists_isSylow2In_of_mem_RSet hT₁
      have h8' := hΩ.eight_le_of_mem_RSet hp hT₁
      have hJJ' : J' = J :=
        hΩ.eq_of_le_of_le hJ' hJ hT₁J'.2.1 (by omega) hT₁J'.1 inf_le_left
      rw [hJJ'] at hT₁J'
      have hcard := natCard_eq_two_mul_of_mem_USet hp hΩ hAU hJ hT₁J'
      have hidx : (J ⊓ W).relIndex (J ⊓ (S₁ : Subgroup G)) = 2 := by
        have h1 := Subgroup.relIndex_mul_card (J ⊓ W) (J ⊓ (S₁ : Subgroup G))
        rw [inf_eq_left.mpr hAT₁, hcard] at h1
        have hpos : 0 < Nat.card ↥(J ⊓ W) := Nat.card_pos
        exact Nat.eq_of_mul_eq_mul_right hpos h1
      intro t₁ ht₁
      exact (inf_le_right : J ⊓ W ≤ W) (commutator_mem_of_relIndex_two hidx (hRe ▸ hr) ht₁)
    · have hc := h67 S₁ R hR.1 _ hT₁ (le_sup_left.trans hS₁) inf_le_right hRe
      intro t₁ ht₁
      rw [hc r hr t₁ ht₁]
      simp
  have hNW := normalizer_le_normalizer_sup_OCW W
  have hrN : r ∈ Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G) := hNW (hR.2 hr)
  have hle : J ⊓ (S₁ : Subgroup G) ⊔ W ⊔ OCW W ≤ modCent (W ⊔ OCW W) _ le_rfl {r} := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro t₁ ht₁
      refine ⟨hNW (hT₁D.2 ht₁), fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact comm_mem_symm ((le_sup_left : W ≤ W ⊔ OCW W) (hRT₁ t₁ ht₁))
    · intro w hw
      refine ⟨hNW (Subgroup.le_normalizer hw), fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (le_sup_left : W ≤ W ⊔ OCW W) (comm_mem_of_left_mem hw (hR.2 hr))
    · intro x hx
      refine ⟨hNW (OCW_le_normalizer W hx), fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact comm_mem_of_left_mem ((le_sup_right : OCW W ≤ W ⊔ OCW W) hx) hrN
  exact comm_mem_symm ((hle (hkT ht)).2 r rfl)

theorem isMulCommutative_muGroup_of_two (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (h611 : EtaMeets Ω) (h610 : EtaActsR Ω) (h67 : RCommute Ω) (hkey : KeyOn Ω)
    {S : Sylow 2 G}
    (h2 : ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) : IsMulCommutative ↥(muGroup Ω W) :=
  isMulCommutative_muGroup (forall_comm_mem_of_generators fun _ hR _ hT _ hr _ ht =>
    commutator_mem_of_two hp hΩ h611 h610 h67 hkey h2 hW hR hT hr ht)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
