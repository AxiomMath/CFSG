module

public import CFSG.GH74.GLS.Stage1.Main.BrG2Ctx
public import CFSG.GH74.GLS.Stage1.Main.BrG2Shape
public import CFSG.GH74.GLS.Stage1.Main.BrFusedStmt

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

namespace CFSG.GH74.GLS.Stage1.Main

theorem baseBridgeG2_of_shape (hshape : G2SylowShapeFact) : BaseBridgeG2 := by
  intro G _ _ z S hcen hT
  obtain ⟨C⟩ := G2Ctx.exists hshape hT
  have hSC : S ≤ Cen z := hcen.sylow.le
  have hSN : S ⊓ OddCore z = ⊥ := cen2_S_inf_oddCore hcen
  set β : ↥S ≃* ↥(barOf z S) := barEquiv z S hSC hSN with hβdef
  have hβ : ∀ s : ↥S, ((β s : ↥(barOf z S)) : CentralizerBar z) = toBar z ⟨s, hSC s.2⟩ :=
    fun s => rfl
  have hRidx : ((RC S z).subgroupOf S).index = 2 := C.relIndex_RC hcen
  obtain ⟨hTcard, hTrel⟩ := C.sylow_inf hcen
  set ρ : ↥S →* C.Gs := C.S'.subtype.comp C.eS.toMonoidHom with hρ
  have hρinj : Function.Injective ρ := Subtype.coe_injective.comp C.eS.injective
  have hρS : ∀ s : ↥S, ρ s ∈ C.S' := fun s => (C.eS s).2
  have hSle := ShapeConds.le_S C.shape
  refine ⟨fun hR => ?_, fun U hUS hU4 hUn => ?_⟩
  · by_contra hno
    push Not at hno
    have hinv : ∀ s : ↥S, orderOf s = 2 → (s : G) ∈ LC z := by
      intro s hs
      by_contra hL
      exact hno s s.2 (fun h => hL h.2) (by rw [Subgroup.orderOf_coe]; exact hs)
    set M₀ : Subgroup C.Gs := ((RC S z).subgroupOf S).map ρ with hM₀
    have hM₀S : M₀ ≤ C.S' := by
      rintro _ ⟨s, -, rfl⟩
      exact hρS s
    have hM₀idx : M₀.relIndex C.S' = 2 := by
      have h1 : M₀.subgroupOf C.S' = ((RC S z).subgroupOf S).map C.eS.toMonoidHom := by
        ext x
        simp only [Subgroup.mem_subgroupOf, hM₀, Subgroup.mem_map]
        constructor
        · rintro ⟨s, hs, hsx⟩
          exact ⟨s, hs, Subtype.ext hsx⟩
        · rintro ⟨s, hs, rfl⟩
          exact ⟨s, hs, rfl⟩
      show (M₀.subgroupOf C.S').index = 2
      rw [h1, Subgroup.index_map_of_bijective C.eS.bijective]
      exact hRidx
    have hM₀inv : ∀ g ∈ C.S', orderOf g = 2 → g ∈ M₀ := by
      intro g hg hg2
      obtain ⟨s, hs⟩ := C.eS.surjective ⟨g, hg⟩
      have hsg : ρ s = g := congrArg Subtype.val hs
      have hs2 : orderOf s = 2 := by
        rw [← MulEquiv.orderOf_eq C.eS s, hs, Subgroup.orderOf_mk]
        exact hg2
      refine ⟨s, ?_, hsg⟩
      exact ⟨s.2, hinv s hs2⟩
    obtain ⟨u₁, u₂, hu₁, hu₂, hu₁o, hu₂o, hne, hcomm⟩ :=
      ShapeConds.central_invols C.shape C.two_le hM₀S hM₀idx hM₀inv
    obtain ⟨s₁, hs₁⟩ := C.eS.surjective ⟨u₁, hu₁⟩
    obtain ⟨s₂, hs₂⟩ := C.eS.surjective ⟨u₂, hu₂⟩
    have hρs₁ : ρ s₁ = u₁ := congrArg Subtype.val hs₁
    have hρs₂ : ρ s₂ = u₂ := congrArg Subtype.val hs₂
    have hs₁o : orderOf s₁ = 2 := by
      rw [← MulEquiv.orderOf_eq C.eS s₁, hs₁, Subgroup.orderOf_mk]; exact hu₁o
    have hs₂o : orderOf s₂ = 2 := by
      rw [← MulEquiv.orderOf_eq C.eS s₂, hs₂, Subgroup.orderOf_mk]; exact hu₂o
    have hs₁₂ : s₁ ≠ s₂ := by
      intro h
      apply hne
      rw [← hρs₁, ← hρs₂, h]
    have hcommS : ∀ r : ↥S, (r : G) ∈ LC z → r * s₁ = s₁ * r ∧ r * s₂ = s₂ * r := by
      intro r hr
      have hrM : ρ r ∈ M₀ := ⟨r, ⟨r.2, hr⟩, rfl⟩
      obtain ⟨h1, h2⟩ := hcomm (ρ r) hrM
      rw [← hρs₁] at h1
      rw [← hρs₂] at h2
      exact ⟨hρinj (by rw [map_mul, map_mul]; exact h1), hρinj (by rw [map_mul, map_mul]; exact h2)⟩
    set K : Subgroup (CentralizerBar z) := C.K₁ ⊔ C.K₂ with hK
    have hbar_mem : ∀ s : ↥S, (s : G) ∈ LC z → toBar z ⟨s, hSC s.2⟩ ∈ K := fun s hs =>
      (C.mem_LC_iff hcen s.2 (hSC s.2)).1 hs
    have hbar_inv : ∀ s : ↥S, orderOf s = 2 → orderOf (toBar z ⟨s, hSC s.2⟩) = 2 := by
      intro s hs
      have hsq : s * s = 1 := by
        have := pow_orderOf_eq_one s
        rwa [hs, pow_two] at this
      have h1 : toBar z ⟨s, hSC s.2⟩ ≠ 1 := by
        intro h
        have h2 : β s = 1 := Subtype.ext (by rw [hβ]; exact h)
        have : s = 1 := β.injective (by rw [h2, map_one])
        rw [this, orderOf_one] at hs
        omega
      refine orderOf_eq_prime ?_ h1
      rw [pow_two, ← map_mul]
      have : (⟨s, hSC s.2⟩ * ⟨s, hSC s.2⟩ : ↥(Cen z)) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hsq)
      rw [this, map_one]
    have hR' : barOf z S ⊓ K ≤ K := inf_le_right
    have hcen_k : ∀ r ∈ barOf z S ⊓ K, r * toBar z ⟨s₁, hSC s₁.2⟩ = toBar z ⟨s₁, hSC s₁.2⟩ * r ∧
        r * toBar z ⟨s₂, hSC s₂.2⟩ = toBar z ⟨s₂, hSC s₂.2⟩ * r := by
      intro r hr
      obtain ⟨c, hc, rfl⟩ := hr.1
      have hcS : (c : G) ∈ S := hc
      have hcL : (c : G) ∈ LC z := by
        rw [C.mem_LC_iff hcen hcS c.2]
        exact hr.2
      obtain ⟨h1, h2⟩ := hcommS ⟨c, hcS⟩ hcL
      refine ⟨?_, ?_⟩
      · rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (by simpa using congrArg Subtype.val h1)
      · rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (by simpa using congrArg Subtype.val h2)
    have hu := inv_central_unique C.odd₁ C.five C.odd₂ C.v₁ C.v₂ C.e₁ C.e₂ C.comm C.inf_card
      hR' hTcard (toBar z ⟨s₁, hSC s₁.2⟩) (hbar_mem s₁ (hinv s₁ hs₁o)) (hbar_inv s₁ hs₁o)
      (fun r hr => (hcen_k r hr).1) (toBar z ⟨s₂, hSC s₂.2⟩) (hbar_mem s₂ (hinv s₂ hs₂o))
      (hbar_inv s₂ hs₂o) (fun r hr => (hcen_k r hr).2)
    apply hs₁₂
    apply β.injective
    exact Subtype.ext (by rw [hβ, hβ]; exact hu)
  ·
    set V : Subgroup C.Gs := (U.subgroupOf S).map ρ with hV
    have hVS : V ≤ C.S' := by
      rintro _ ⟨x, -, rfl⟩
      exact hρS x
    have hUe : IsElementaryAbelian 2 ↥U := hU4.1
    have hUsub : IsElementaryAbelian 2 ↥(U.subgroupOf S) := IsElementaryAbelian.subgroupOf hUS
    have hV4 : IVK.IsFourSubgroup V := by
      refine ⟨IsElementaryAbelian.map ρ, ?_⟩
      rw [hV, Subgroup.card_map_of_injective hρinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv]
      exact hU4.2
    have hVn : ∀ s ∈ C.S', ∀ v ∈ V, s * v * s⁻¹ ∈ V := by
      intro s hs' v hv
      obtain ⟨x, hx, rfl⟩ := hv
      obtain ⟨s₀, hs₀⟩ := C.eS.surjective ⟨s, hs'⟩
      have hx' : (x : G) ∈ U := hx
      have hmem : (s₀ : G) * (x : G) * (s₀ : G)⁻¹ ∈ U := hUn (s₀ : G) s₀.2 (x : G) hx'
      refine ⟨s₀ * x * s₀⁻¹, hmem, ?_⟩
      show ρ (s₀ * x * s₀⁻¹) = s * ρ x * s⁻¹
      rw [map_mul, map_mul, map_inv]
      have : ρ s₀ = s := congrArg Subtype.val hs₀
      rw [this]
    have hsq := ShapeConds.four_sq C.shape C.two_le hVS hV4 hVn
    intro u hu
    obtain ⟨x, hxA, hx⟩ := hsq (ρ ⟨u, hUS hu⟩) ⟨⟨u, hUS hu⟩, hu, rfl⟩
    obtain ⟨s₀, hs₀⟩ := C.eS.surjective ⟨x, hSle.1 hxA⟩
    have hρs₀ : ρ s₀ = x := congrArg Subtype.val hs₀
    have h1 : (⟨u, hUS hu⟩ : ↥S) = s₀ * s₀ := hρinj (by rw [hx, map_mul, hρs₀])
    have h2 : s₀ * s₀ ∈ (RC S z).subgroupOf S := by
      rw [Subgroup.mul_mem_iff_of_index_two hRidx]
    rw [← h1] at h2
    exact (inf_le_right : RC S z ≤ LC z) h2

end CFSG.GH74.GLS.Stage1.Main
