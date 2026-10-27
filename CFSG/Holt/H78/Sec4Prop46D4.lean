module

public import CFSG.Holt.H78.Sec4Prop46D3

public section

namespace CFSG.Holt.H78

namespace CaseAD

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

namespace DCase

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]
  {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)} {hS : Sec4Setting G Ω}
  {hP : Prop46Setup G Ω α v P} (H : DCase hS hP)

theorem false_of_odd (hodd : Odd (Nat.card (twoPointKernel G Ω α H.β₁))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set k₀ := H.k₀
  have hk₀ : k₀ ≠ H.i₀ := H.ne
  set γk := H.A₁.D.coord H.γ₁Δ k₀
  have hvJ := H.vk_mem_longInvAt k₀
  obtain ⟨κ, hκA, hκ2, hκv, hκγ, hκ1, hκz⟩ := exists_klein (H.A₁.D.five_le_card k₀) hvJ
  set M₄ := Subgroup.closure ({H.vk k₀, κ} : Set (Equiv.Perm (H.A₁.D.Ψc k₀))) with hM₄
  have hgen2 : ∀ s ∈ ({H.vk k₀, κ} : Set (Equiv.Perm (H.A₁.D.Ψc k₀))), s * s = 1 := by
    rintro s (rfl | rfl)
    · exact Equiv.ext fun c => by rw [Equiv.Perm.mul_apply, H.vk_vk, Equiv.Perm.one_apply]
    · exact hκ2
  have hgenc : ∀ s ∈ ({H.vk k₀, κ} : Set (Equiv.Perm (H.A₁.D.Ψc k₀))),
      ∀ t ∈ ({H.vk k₀, κ} : Set (Equiv.Perm (H.A₁.D.Ψc k₀))), Commute s t := by
    rintro s (rfl | rfl) t (rfl | rfl)
    exacts [Commute.refl _, hκv.symm, hκv, Commute.refl _]
  have hM₄2 : IsPGroup 2 M₄ := isPGroup_of_mul_self (mul_self_eq_one_of_mem_closure hgen2 hgenc)
  have hM₄v : ∀ m ∈ M₄, Commute m (H.vk k₀) := by
    have hle : M₄ ≤ Subgroup.centralizer ({H.vk k₀} : Set (Equiv.Perm (H.A₁.D.Ψc k₀))) :=
      (Subgroup.closure_le _).mpr (by
        rintro s (rfl | rfl)
        · exact Subgroup.mem_centralizer_iff.mpr fun t ht => by rw [Set.mem_singleton_iff.mp ht]
        · exact Subgroup.mem_centralizer_iff.mpr fun t ht => by
            rw [Set.mem_singleton_iff.mp ht]; exact hκv.symm.eq)
    exact fun m hm => (Subgroup.mem_centralizer_iff.mp (hle hm) _ rfl).symm
  have hM₄γ : ∀ m ∈ M₄, m γk = γk := by
    have hle : M₄ ≤ MulAction.stabilizer (Equiv.Perm (H.A₁.D.Ψc k₀)) γk :=
      (Subgroup.closure_le _).mpr (by
        rintro s (rfl | rfl)
        · exact hvJ.2
        · exact hκγ)
    exact fun m hm => hle hm
  have hvA : H.vk k₀ ∈ alternatingGroup (H.A₁.D.Ψc k₀) :=
    (mem_alternatingGroup_iff_of_mem_longInv_perm hvJ.1).mpr (H.A₁.mod4 k₀)
  have hM₄A : M₄ ≤ H.A₁.D.M k₀ := by
    have hMeq : H.A₁.D.M k₀ = alternatingGroup (H.A₁.D.Ψc k₀) := H.A₁.alt k₀
    rw [hMeq]
    exact (Subgroup.closure_le _).mpr (by rintro s (rfl | rfl); exacts [hvA, hκA])
  have hM₄card : 4 ≤ Nat.card M₄ := by
    have hsub : (({1, H.vk k₀, κ, κ * H.vk k₀} : Finset (Equiv.Perm (H.A₁.D.Ψc k₀))) :
        Set (Equiv.Perm (H.A₁.D.Ψc k₀))) ⊆ M₄ := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact M₄.one_mem
      · exact Subgroup.subset_closure (Or.inl rfl)
      · exact Subgroup.subset_closure (Or.inr rfl)
      · exact mul_mem (Subgroup.subset_closure (Or.inr rfl))
          (Subgroup.subset_closure (Or.inl rfl))
    have hv1 : H.vk k₀ ≠ 1 := fun h => by have := hvJ.1.1; rw [h, orderOf_one] at this; omega
    have hc4 : ({1, H.vk k₀, κ, κ * H.vk k₀} : Finset (Equiv.Perm (H.A₁.D.Ψc k₀))).card = 4 := by
      have h1 : κ * H.vk k₀ ≠ 1 := fun h => hκz (eq_inv_of_mul_eq_one_left h |>.trans
        (inv_eq_self_of_mem_longInv hvJ.1))
      have h2 : κ * H.vk k₀ ≠ H.vk k₀ := fun h => hκ1 (mul_right_cancel (h.trans (one_mul _).symm))
      have h3 : κ * H.vk k₀ ≠ κ := fun h => hv1 (mul_left_cancel (h.trans (mul_one _).symm))
      rw [Finset.card_insert_of_notMem (by simp [hv1.symm, hκ1.symm, h1.symm]),
        Finset.card_insert_of_notMem (by simp [hκz.symm, h2.symm]),
        Finset.card_pair (Ne.symm h3)]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset, hc4, ← Nat.card_coe_set_eq] at this
  set φ := (coordPermHom H.A₁).comp (MonoidHom.mulSingle (fun k => Equiv.Perm (H.A₁.D.Ψc k)) k₀)
    with hφ
  have hφx : ∀ m, φ m = coordPerm H.A₁ (Pi.mulSingle k₀ m) := fun m => rfl
  have hφinj : Function.Injective φ := fun m m' h => by
    rw [hφx, hφx, coordPerm_eq_iff] at h
    exact Pi.mulSingle_injective k₀ h
  set F := M₄.map φ with hF
  have hF2 : IsPGroup 2 F := hM₄2.map φ
  have hFcard : Nat.card F = Nat.card M₄ := Subgroup.card_map_of_injective hφinj
  have hcoordφ : ∀ m δ k, H.A₁.D.coord (φ m δ) k =
      if k = k₀ then (Pi.mulSingle k₀ m : ∀ k, Equiv.Perm (H.A₁.D.Ψc k)) k (H.A₁.D.coord δ k)
      else H.A₁.D.coord δ k := fun m δ k => by
    rw [hφx, coord_coordPerm]
    split_ifs with hk
    · rfl
    · rw [Pi.mulSingle_eq_of_ne hk, Equiv.Perm.one_apply]
  have hFN : inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀) ≤
      Subgroup.normalizer (F : Set (Equiv.Perm (holtDelta G Ω α H.β₁))) := by
    intro π hπ
    obtain ⟨g, hg, hgπ⟩ := mem_inducedPerm.mp hπ
    have hgV := (Subgroup.mem_inf.mp hg).1
    have hgk := H.mapsDir_k₀ hg
    obtain ⟨σ, hσ⟩ := exists_mapsDir H.A₁ (H.V_le_pair hgV)
    have hσk : σ k₀ = k₀ := MapsDir.eq H.A₁ (H.V_le_pair hgV) H.γ₁Δ (hσ k₀) hgk
    have hcomm : ∀ m, π * φ m = φ m * π := fun m => Equiv.ext fun δ =>
      CaseAData.coord_injective H.A₁ (funext fun j => by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hcoordφ]
        obtain ⟨j', rfl⟩ := σ.surjective j
        by_cases hj : j' = k₀
        · subst hj
          rw [hσk, ite_eq_left rfl]
          have e1 := H.coord_smul_eq H.big_k₀ hgV hgk (φ m δ) (π (φ m δ)) (hgπ _)
          have e2 := H.coord_smul_eq H.big_k₀ hgV hgk δ (π δ) (hgπ _)
          rw [e1, e2, hcoordφ, ite_eq_left rfl]
        · have hσj : σ j' ≠ k₀ := fun h => hj (σ.injective (h.trans hσk.symm))
          rw [ite_eq_right hσj]
          exact (hσ j' (φ m δ) δ (π (φ m δ)) (π δ) (hgπ _) (hgπ _)).mpr
            (by rw [hcoordφ, ite_eq_right hj]))
    have hcF : ∀ f ∈ F, π * f = f * π := by
      rintro _ ⟨m, -, rfl⟩
      exact hcomm m
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      rw [hcF f hf, mul_inv_cancel_right]
      exact hf
    · intro hf
      have h1 := hcF _ hf
      have h2 : π * f * π⁻¹ = f := by
        have h3 : π * (π * f * π⁻¹) = π * f := by rw [h1]; group
        exact mul_left_cancel h3
      rw [← h2]
      exact hf
  have hFK : F ≤ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀) := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨ℓ, hℓc, hℓk, hℓo⟩ := CaseAData.exists_commElt H.A₁ k₀ (hM₄A hm)
    have hℓ : ((ℓ : twoPointSection G Ω α H.β₁) : Equiv.Perm (holtDelta G Ω α H.β₁)) =
        coordPerm H.A₁ (Pi.mulSingle k₀ m) :=
      Equiv.ext fun δ => CaseAData.coord_injective H.A₁ (funext fun j => by
        rw [coord_coordPerm]
        show H.A₁.D.coord ((ℓ : twoPointSection G Ω α H.β₁) • δ) j = _
        rw [H.A₁.D.coord_smul ℓ δ j]
        by_cases hj : j = k₀
        · subst hj; rw [hℓk, Pi.mulSingle_eq_same]
        · rw [hℓo j hj, Pi.mulSingle_eq_of_ne hj])
    rw [hφx]
    refine H.coordPerm_mem_of_odd hodd (hℓ ▸ hℓc) (fun k => ?_) (fun k => ?_) ?_
    · by_cases hk : k = k₀
      · subst hk; rw [Pi.mulSingle_eq_same]; exact hM₄v m hm
      · rw [Pi.mulSingle_eq_of_ne hk]; exact Commute.one_left _
    · by_cases hk : k = k₀
      · subst hk; rw [Pi.mulSingle_eq_same]; exact hM₄γ m hm
      · rw [Pi.mulSingle_eq_of_ne hk, Equiv.Perm.one_apply]
    · exact Pi.mulSingle_eq_of_ne (M := fun k => Equiv.Perm (H.A₁.D.Ψc k)) (Ne.symm hk₀) m
  have hFV : ∀ g (hg : g ∈ H.V), ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
      Equiv.Perm (holtDelta G Ω α H.β₁)) ∈ F →
      ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
        Equiv.Perm (holtDelta G Ω α H.β₁)) = 1 := by
    rintro g hg ⟨m, -, hgm⟩
    have hcoord : ∀ δ δ' : holtDelta G Ω α H.β₁, (δ' : Ω) = g • (δ : Ω) →
        H.A₁.D.coord δ' k₀ = m (H.A₁.D.coord δ k₀) := fun δ δ' h => by
      have : δ' = φ m δ := by rw [hgm]; exact Subtype.ext h
      rw [this, hcoordφ, ite_eq_left rfl, Pi.mulSingle_eq_same]
    have hgk : MapsDir H.A₁ g k₀ k₀ := fun δ₁ δ₂ δ₁' δ₂' e₁ e₂ => by
      rw [hcoord δ₁ δ₁' e₁, hcoord δ₂ δ₂' e₂]
      exact m.injective.eq_iff
    have hm1 : m = 1 := Equiv.ext fun c => by
      obtain ⟨δ, rfl⟩ := H.A₁.D.exists_coord_apply_eq k₀ c
      have h1 := H.coord_smul_eq H.big_k₀ hg hgk δ (twoPointElt (H.V_le_pair hg) • δ) rfl
      rw [hcoord δ _ rfl] at h1
      exact h1
    rw [← hgm, hm1, map_one]
  have h1 := H.card_Vdir_mul_card_le hF2 hFN hFK hFV
  have h2 := H.card_V_le H.big_i₀
  have hfilt : (Finset.univ.filter fun k => 4 ≤ (proj H.A₁ H.V k).ncard) = {H.i₀, k₀} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact H.big_iff k
  rw [hfilt, Finset.card_pair (Ne.symm hk₀)] at h2
  have hpos : 0 < Nat.card (H.Vdir H.i₀) := Nat.card_pos
  rw [hFcard] at h1
  have := Nat.mul_le_mul_left (Nat.card (H.Vdir H.i₀)) hM₄card
  omega

theorem card_mul_card_mul_le {F : Subgroup (Equiv.Perm (holtDelta G Ω α H.β₁))}
    (hF2 : IsPGroup 2 F)
    (hFN : inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀) ≤
      Subgroup.normalizer (F : Set (Equiv.Perm (holtDelta G Ω α H.β₁))))
    (hFK : F ≤ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀))
    (hFV : ∀ g (hg : g ∈ H.V), ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
      Equiv.Perm (holtDelta G Ω α H.β₁)) ∈ F →
      ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
        Equiv.Perm (holtDelta G Ω α H.β₁)) = 1)
    {E : Subgroup G} (hE2 : IsPGroup 2 E)
    (hE𝒞 : E ≤ caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
    (hEΔ : inducedPerm E (holtDelta G Ω α H.β₁) (hE𝒞.trans (H.𝒞_le_stab H.i₀)) ≤
      inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀)) :
    Nat.card (inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀)) *
        Nat.card F * Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf E) ≤
      Nat.card H.V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 (H.Vdir H.i₀) := H.sylow.2.1.to_le inf_le_left
  set U := inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀) with hU
  set Q := U ⊔ F with hQ
  have hQ2 : IsPGroup 2 Q := (isPGroup_inducedPerm hV2 _).to_sup_of_normal_right' hF2 hFN
  have hQK : Q ≤ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀) :=
    sup_le (inducedPerm_mono (H.Vdir_le H.big_i₀)) hFK
  obtain ⟨R, hR𝒞, hER, hR2, hRQ⟩ := exists_le_inducedPerm_eq hQ2 hQK hE2 hE𝒞
    (hEΔ.trans le_sup_left)
  have hRV := H.card_le_of_line (H.proj_eq_univ H.big_i₀).1 hR𝒞 hR2
  have hRcard := card_inducedPerm_mul_card_ker (K := R) (Ψ := holtDelta G Ω α H.β₁)
    (h := hR𝒞.trans (H.𝒞_le_stab H.i₀))
  rw [hRQ] at hRcard
  have hker : Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf E) ≤
      Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf R) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨⟨x.1.1, hER x.1.2⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp x.2)⟩) fun x y h => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥((fixingSubgroup G
      (holtDelta G Ω α H.β₁)).subgroupOf R) => ((z : R) : G)) h))
  have hQcard : Nat.card U * Nat.card F ≤ Nat.card Q := by
    have hinj : Function.Injective (fun x : U × F =>
        (⟨(x.1 : Equiv.Perm (holtDelta G Ω α H.β₁)) * x.2,
          mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩ : Q)) := by
      rintro ⟨u, f⟩ ⟨u', f'⟩ h
      have h1 : (u : Equiv.Perm (holtDelta G Ω α H.β₁)) * f = u' * f' := congrArg Subtype.val h
      have h2 : (u' : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ * u =
          (f' : Equiv.Perm (holtDelta G Ω α H.β₁)) * (f : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ := by
        calc (u' : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ * u
            = (u' : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ * (u * f) *
                (f : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ := by group
          _ = _ := by rw [h1]; group
      obtain ⟨g, hg, hgπ⟩ := mem_inducedPerm.mp (mul_mem (inv_mem u'.2) u.2)
      have hgV := (Subgroup.mem_inf.mp hg).1
      have hgψ : ((twoPointElt (H.V_le_pair hgV) : twoPointSection G Ω α H.β₁) :
          Equiv.Perm (holtDelta G Ω α H.β₁)) = (u' : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ * u :=
        Equiv.ext fun δ => Subtype.ext (hgπ δ).symm
      have h3 := hFV g hgV (by rw [hgψ, h2]; exact mul_mem f'.2 (inv_mem f.2))
      rw [hgψ] at h3
      have hu : (u : Equiv.Perm (holtDelta G Ω α H.β₁)) = u' := by
        have := congrArg ((u' : Equiv.Perm (holtDelta G Ω α H.β₁)) * ·) h3
        simpa using this
      have hf : (f : Equiv.Perm (holtDelta G Ω α H.β₁)) = f' := by
        rw [hu] at h1; exact mul_left_cancel h1
      rw [Subtype.ext hu, Subtype.ext hf]
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod] at this
  calc Nat.card U * Nat.card F *
        Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf E)
      ≤ Nat.card Q * Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf R) :=
        Nat.mul_le_mul hQcard hker
    _ = Nat.card R := hRcard
    _ ≤ Nat.card H.V := hRV

abbrev VΔ : Subgroup G := H.V ⊓ twoPointKernel G Ω α H.β₁

abbrev Zc : Subgroup G := caseACentralizer G Ω α H.β₁ v (holtDelta G Ω α H.β₁)

omit [Finite G] [FaithfulSMul G Ω] in
theorem VΔ_le_Zc : H.VΔ ≤ H.Zc := fun g hg => by
  obtain ⟨hgV, hgK⟩ := Subgroup.mem_inf.mp hg
  exact ⟨⟨(H.sylow.1 hgV).1.1, H.V_le hgV⟩, (Subgroup.mem_inf.mp hgK).2⟩

omit [Finite G] [FaithfulSMul G Ω] in
theorem Zc_le_𝒞 (j : H.A₁.D.ι) : H.Zc ≤ caseACentralizer G Ω α H.β₁ v (H.line j) :=
  fun g hg => ⟨(Subgroup.mem_inf.mp hg).1, (mem_fixingSubgroup_iff G).mpr fun _ hl => by
    obtain ⟨δ, -, rfl⟩ := hl
    exact (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp hg).2 δ δ.2⟩

omit [Finite G] [FaithfulSMul G Ω] in
theorem mem_normalizer_Zc {g : G} (hgv : Commute g v) (hgα : g • α = α)
    (hgβ : g • H.β₁ = H.β₁) : g ∈ Subgroup.normalizer (H.Zc : Set G) := by
  have hg2 : g ∈ stabilizer G ({α, H.β₁} : Set Ω) :=
    stabilizer_inf_le_stabilizer_pair α H.β₁ ⟨hgα, hgβ⟩
  have hΔ : ∀ (h : G), h ∈ stabilizer G ({α, H.β₁} : Set Ω) → ∀ δ ∈ holtDelta G Ω α H.β₁,
      h • δ ∈ holtDelta G Ω α H.β₁ := fun h hh δ hδ => by
    have := stabilizer_pair_le (G := G) α H.β₁ hh
    rw [mem_stabilizer_iff] at this
    rw [← this]; exact Set.smul_mem_smul_set hδ
  have key : ∀ h : G, Commute h v → h • α = α → h • H.β₁ = H.β₁ → ∀ z ∈ H.Zc,
      h * z * h⁻¹ ∈ H.Zc := by
    intro h hhv hhα hhβ z hz
    obtain ⟨⟨hzv, hzα, hzβ⟩, hzΔ⟩ := hz
    have hh2 : h⁻¹ ∈ stabilizer G ({α, H.β₁} : Set Ω) :=
      inv_mem (stabilizer_inf_le_stabilizer_pair α H.β₁ ⟨hhα, hhβ⟩)
    refine ⟨⟨Subgroup.mem_centralizer_iff.mpr ?_, ?_, ?_⟩, (mem_fixingSubgroup_iff G).mpr ?_⟩
    · rintro _ ⟨n, rfl⟩
      have h1 := (Subgroup.mem_centralizer_iff.mp hzv _ ⟨n, rfl⟩)
      have h2 : h * v ^ n = v ^ n * h := (hhv.zpow_right n).eq
      have h3 : h⁻¹ * v ^ n = v ^ n * h⁻¹ := (hhv.inv_left.zpow_right n).eq
      calc v ^ n * (h * z * h⁻¹) = h * (v ^ n * z) * h⁻¹ := by
            rw [← mul_assoc, ← mul_assoc, ← h2]; group
        _ = h * (z * v ^ n) * h⁻¹ := by rw [h1]
        _ = h * z * h⁻¹ * v ^ n := by rw [mul_assoc h, mul_assoc z, ← h3]; group
    · show (h * z * h⁻¹) • α = α
      rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hhα.symm, hzα, hhα]
    · show (h * z * h⁻¹) • H.β₁ = H.β₁
      rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hhβ.symm, hzβ, hhβ]
    · intro δ hδ
      rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hzΔ _ (hΔ _ hh2 δ hδ),
        smul_inv_smul]
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key g hgv hgα hgβ z, fun hz => ?_⟩
  have := key g⁻¹ hgv.inv_left (inv_smul_eq_iff.mpr hgα.symm) (inv_smul_eq_iff.mpr hgβ.symm) _ hz
  rwa [inv_inv, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this

omit [Finite G] [FaithfulSMul G Ω] in
theorem VΔ_eq : H.VΔ = H.V ⊓ H.Zc := by
  refine le_antisymm (le_inf inf_le_left H.VΔ_le_Zc) fun g hg => ?_
  obtain ⟨hgV, ⟨-, hgα, hgβ⟩, hgΔ⟩ := hg
  exact ⟨hgV, ⟨hgα, hgβ⟩, hgΔ⟩

omit [FaithfulSMul G Ω] in
theorem two_le_card_RT : 2 ≤ Nat.card (H.RT H.Tbig) := by
  classical
  have hk : H.k₀ ∈ H.Tbig := by
    simp only [Tbig, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨H.ne, H.big_k₀⟩
  have hne : H.eS {H.k₀} ≠ 1 := fun h => by
    obtain ⟨δ, hδk, -⟩ := exists_pair_update H.A₁ H.γ₁Δ H.k₀
    have h1 := congrArg (fun π : Equiv.Perm (holtDelta G Ω α H.β₁) => H.A₁.D.coord (π δ) H.k₀) h
    simp only [coord_eS, Finset.mem_singleton, ite_true, Equiv.Perm.one_apply] at h1
    exact hδk (H.vk_fix h1)
  have hmem : H.eS {H.k₀} ∈ H.RT H.Tbig := ⟨{H.k₀}, by simpa using hk, rfl⟩
  have : (⟨H.eS {H.k₀}, hmem⟩ : H.RT H.Tbig) ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hnt : Nontrivial (H.RT H.Tbig) := ⟨⟨_, 1, this⟩⟩
  exact Finite.one_lt_card_iff_nontrivial.mpr hnt

theorem sylow_VΔ (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α H.β₁))) :
    fusionIsSylowIn 2 H.VΔ H.Zc := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hns
  have hV2 : IsPGroup 2 (H.Vdir H.i₀) := H.sylow.2.1.to_le inf_le_left
  have hVΔ2 : IsPGroup 2 H.VΔ := H.sylow.2.1.to_le inf_le_left
  have hVdN : H.Vdir H.i₀ ≤ Subgroup.normalizer (H.Zc : Set G) := fun g hg => by
    have hgV := (Subgroup.mem_inf.mp hg).1
    exact H.mem_normalizer_Zc (Subgroup.mem_centralizer_iff.mp (H.sylow.1 hgV).1.1 v
      (Subgroup.mem_zpowers v)).symm (H.V_le hgV).1 (H.V_le hgV).2
  have hVdNV : H.Vdir H.i₀ ≤ Subgroup.normalizer (H.VΔ : Set G) := fun g hg => by
    rw [H.VΔ_eq]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (Subgroup.mem_inf.mp hg).1, hVdN hg⟩
  obtain ⟨W, hVW, hW, hWN⟩ := exists_fusionIsSylowIn_ge_le_normalizer hVΔ2 H.VΔ_le_Zc hV2 hVdN
    hVdNV
  have hWne : H.VΔ ≠ W := fun h => hns (h ▸ hW)
  have hW2 : 2 * Nat.card H.VΔ ≤ Nat.card W := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hVW
    have h1 : m ≠ 1 := fun h => hWne (Subgroup.eq_of_le_of_card_ge hVW (by rw [hm, h, mul_one]))
    have h0 : m ≠ 0 := fun h => by
      have := (Nat.card_pos : 0 < Nat.card W)
      rw [hm, h, mul_zero] at this
      omega
    rw [hm]
    have : 2 ≤ m := by omega
    nlinarith
  set E := H.Vdir H.i₀ ⊔ W with hEdef
  have hE2 : IsPGroup 2 E := hV2.to_sup_of_normal_right' hW.2.1 hWN
  have hE𝒞 : E ≤ caseACentralizer G Ω α H.β₁ v (H.line H.i₀) :=
    sup_le (H.Vdir_le H.big_i₀) (hW.1.trans (H.Zc_le_𝒞 H.i₀))
  let Tg : Subgroup G :=
    { carrier := {x | ∃ g ∈ H.Vdir H.i₀, ∀ δ ∈ holtDelta G Ω α H.β₁, x • δ = g • δ}
      mul_mem' := by
        rintro x y ⟨g, hg, hxg⟩ ⟨h, hh, hyh⟩
        refine ⟨g * h, mul_mem hg hh, fun δ hδ => ?_⟩
        have hhδ : h • δ ∈ holtDelta G Ω α H.β₁ := by
          have := H.Vdir_le_stab H.i₀ hh
          rw [mem_stabilizer_iff] at this
          rw [← this]; exact Set.smul_mem_smul_set hδ
        rw [mul_smul, mul_smul, hyh δ hδ, hxg _ hhδ]
      one_mem' := ⟨1, one_mem _, fun δ _ => rfl⟩
      inv_mem' := by
        rintro x ⟨g, hg, hxg⟩
        refine ⟨g⁻¹, inv_mem hg, fun δ hδ => ?_⟩
        have hgδ : g⁻¹ • δ ∈ holtDelta G Ω α H.β₁ := by
          have := H.Vdir_le_stab H.i₀ (inv_mem hg)
          rw [mem_stabilizer_iff] at this
          rw [← this]; exact Set.smul_mem_smul_set hδ
        rw [inv_smul_eq_iff, hxg _ hgδ, smul_inv_smul] }
  have hETg : E ≤ Tg := sup_le (fun g hg => ⟨g, hg, fun _ _ => rfl⟩)
    (fun w hw => ⟨1, one_mem _, fun δ hδ => by
      rw [one_smul]; exact (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp (hW.1 hw)).2 δ hδ⟩)
  have hEΔ : inducedPerm E (holtDelta G Ω α H.β₁) (hE𝒞.trans (H.𝒞_le_stab H.i₀)) ≤
      inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀) := by
    intro π hπ
    obtain ⟨x, hx, hxπ⟩ := mem_inducedPerm.mp hπ
    obtain ⟨g, hg, hxg⟩ := hETg hx
    exact mem_inducedPerm.mpr ⟨g, hg, fun δ => (hxπ δ).trans (hxg δ δ.2)⟩
  have hFK : H.RT H.Tbig ≤ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀) := by
    rintro _ ⟨S, hS, rfl⟩
    exact H.eS_mem_of_even hT (fun h => by have := hS h; simp [Tbig] at this)
  have hFV : ∀ g (hg : g ∈ H.V), ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
      Equiv.Perm (holtDelta G Ω α H.β₁)) ∈ H.RT H.Tbig →
      ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
        Equiv.Perm (holtDelta G Ω α H.β₁)) = 1 := by
    rintro g hg ⟨S, hS, hgS⟩
    have := H.eq_empty_of_eS hg (U := S) (fun k hk => by
      have := hS hk
      simp only [Tbig, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.2) hgS
    rw [hgS, this, H.eS_empty]
  have hF := H.card_mul_card_mul_le (H.isPGroup_RT _) H.Vdir_le_normalizer_RT hFK hFV hE2 hE𝒞
    hEΔ
  have hkerE : Nat.card W ≤
      Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf E) := by
    refine Nat.card_le_card_of_injective (fun w => ⟨⟨w.1, le_sup_right (a := H.Vdir H.i₀) w.2⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (hW.1 w.2)).2⟩) fun x y h => ?_
    exact Subtype.ext (congrArg (fun z : ↥((fixingSubgroup G
      (holtDelta G Ω α H.β₁)).subgroupOf E) => ((z : E) : G)) h)
  have hkerV : Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf (H.Vdir H.i₀)) ≤
      Nat.card H.VΔ := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, (Subgroup.mem_inf.mp x.1.2).1,
      ⟨H.V_le (Subgroup.mem_inf.mp x.1.2).1, Subgroup.mem_subgroupOf.mp x.2⟩⟩) fun x y h => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : H.VΔ => (z : G)) h))
  have hVcard := card_inducedPerm_mul_card_ker (K := H.Vdir H.i₀) (Ψ := holtDelta G Ω α H.β₁)
    (h := H.Vdir_le_stab H.i₀)
  have hVle := H.card_V_le H.big_i₀
  have hfilt : (Finset.univ.filter fun k => 4 ≤ (proj H.A₁ H.V k).ncard) = {H.i₀, H.k₀} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact H.big_iff k
  rw [hfilt, Finset.card_pair (Ne.symm H.ne)] at hVle
  have hRT := H.two_le_card_RT
  have hU0 : 0 < Nat.card (inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁)
    (H.Vdir_le_stab H.i₀)) := Nat.card_pos
  have hW0 : 0 < Nat.card W := Nat.card_pos
  set u := Nat.card (inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀))
  set kV := Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf (H.Vdir H.i₀))
  have e1 : u * 2 * Nat.card W ≤ Nat.card H.V := (Nat.mul_le_mul (Nat.mul_le_mul_left u hRT)
    hkerE).trans hF
  have e2 : Nat.card H.V ≤ u * kV * 2 := by rw [hVcard]; exact hVle
  have e3 : u * kV * 2 * 2 ≤ u * Nat.card W * 2 := by
    have := Nat.mul_le_mul_left u ((Nat.mul_le_mul_left 2 hkerV).trans hW2)
    nlinarith
  nlinarith

end DCase

section Sep

variable {K : Type*} [Group K] [Finite K] {X : Type*}
  [MulAction K X] (D : HoltData K X) {Y : Type*} [Fintype Y] [DecidableEq Y]

theorem exists_sep (hK : IsStarGroup K X) {a b : X} {L : Set X}
    (hL : L ⊆ holtDelta K X a b) (x : X → Y)
    (hinj : ∀ l ∈ L, ∀ l' ∈ L, x l = x l' → l = l') (hsurj : ∀ p, ∃ l ∈ L, x l = p)
    (hodd : Odd (Fintype.card Y)) (h5 : 5 ≤ Fintype.card Y) (c : Equiv.Perm Y → K)
    (hc : ∀ y ∈ longInv (Equiv.Perm Y) Y, c y ∈ longInvSwap K X a b)
    (hcL : ∀ y ∈ longInv (Equiv.Perm Y) Y, ∀ l ∈ L, c y • l ∈ L)
    (hcx : ∀ y ∈ longInv (Equiv.Perm Y) Y, ∀ ω ∈ holtDelta K X a b, x (c y • ω) = y (x ω))
    (hcc : ∀ y ∈ longInv (Equiv.Perm Y) Y, ∀ y' ∈ longInv (Equiv.Perm Y) Y,
      ∀ ω ∈ holtDelta K X a b, y (y' (x ω)) = x ω → c y • c y' • ω = ω) :
    ∃ k, (∀ l ∈ L, ∀ l' ∈ L, D.coord l k = D.coord l' k → l = l') ∧
      ∀ k', k' ≠ k → ∀ l ∈ L, ∀ l' ∈ L, D.coord l k' = D.coord l' k' := by
  classical
  have hJ : ∀ y ∈ longInv (Equiv.Perm Y) Y, ∀ y' ∈ longInv (Equiv.Perm Y) Y,
      c y * c y' ∈ jHull K X := fun y hy y' hy' =>
    mul_mem (mem_jHull_of_mem_longInv (hc y hy).1) (mem_jHull_of_mem_longInv (hc y' hy').1)
  have hfib : ∀ y (hy : y ∈ longInv (Equiv.Perm Y) Y) y' (hy' : y' ∈ longInv (Equiv.Perm Y) Y)
      k (ω ω' : X), D.coord ω k = D.coord ω' k →
        D.coord ((c y * c y') • ω) k = D.coord ((c y * c y') • ω') k := by
    intro y hy y' hy' k ω ω' h
    rw [D.coord_smul ⟨_, hJ y hy y' hy'⟩, D.coord_smul ⟨_, hJ y hy y' hy'⟩, h]
  have hgL : ∀ y ∈ longInv (Equiv.Perm Y) Y, ∀ y' ∈ longInv (Equiv.Perm Y) Y, ∀ l ∈ L,
      (c y * c y') • l ∈ L ∧ x ((c y * c y') • l) = y (y' (x l)) := by
    intro y hy y' hy' l hl
    rw [mul_smul]
    exact ⟨hcL y hy _ (hcL y' hy' l hl), by rw [hcx y hy _ (hL (hcL y' hy' l hl)),
      hcx y' hy' l (hL hl)]⟩
  have hK3 : ∀ k, ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → D.coord l₁ k = D.coord l₂ k →
      ∀ l ∈ L, D.coord l k = D.coord l₁ k := by
    intro k l₁ hl₁ l₂ hl₂ hne heq l hl
    by_cases hll : x l = x l₁
    · rw [hinj l hl l₁ hl₁ hll]
    have hq : x l₂ ≠ x l₁ := fun h => hne (hinj l₁ hl₁ l₂ hl₂ h.symm)
    obtain ⟨y, hy, y', hy', hyy⟩ := CCL.exists_mem_longInvAt_perm_apply_apply_eq hodd h5 hq hll
    have h1 : (c y * c y') • l₁ = l₁ := by
      rw [mul_smul]
      refine hcc y hy.1 y' hy'.1 l₁ (hL hl₁) ?_
      rw [show y' (x l₁) = x l₁ from hy'.2]
      exact hy.2
    obtain ⟨hgl₂, hgx⟩ := hgL y hy.1 y' hy'.1 l₂ hl₂
    have h2 : (c y * c y') • l₂ = l := hinj _ hgl₂ l hl (by rw [hgx, hyy])
    rw [← h2, ← h1]
    exact hfib y hy.1 y' hy'.1 k _ _ heq.symm
  have hK4 : ∀ l ∈ L, ∀ l' ∈ L, D.coord l = D.coord l' → l = l' := by
    intro l hl l' hl' hco
    by_contra hne
    have hμ : x l' ≠ x l := fun h => hne (hinj l hl l' hl' h.symm)
    obtain ⟨y, hy, y', hy', hww, hw⟩ :=
      CCL.exists_mem_longInvAt_perm_mul_mul_self_eq_one hodd h5 hμ
    have hfix : ∀ z ∈ longInvAt (Equiv.Perm Y) Y (x l), c z • l = l := fun z hz =>
      hinj _ (hcL z hz.1 l hl) l hl (by rw [hcx z hz.1 l (hL hl)]; exact hz.2)
    obtain ⟨m, hm, hmB⟩ := exists_odd_pow_smul_eq_of_mem_longInvAt hK
      (⟨(hc y' hy'.1).1, hfix y' hy'⟩ : c y' ∈ longInvAt K X l)
      (⟨(hc y hy.1).1, hfix y hy⟩ : c y ∈ longInvAt K X l)
    have h1 := hmB l' ((D.coord_eq_iff l l').mp hco)
    obtain ⟨hg1, hgx1⟩ := hgL y hy.1 y' hy'.1 l' hl'
    obtain ⟨hg2, hgx2⟩ := hgL y hy.1 y' hy'.1 _ hg1
    have hsq : (c y * c y') ^ 2 • l' = l' := by
      rw [sq, mul_smul]
      refine hinj _ hg2 l' hl' ?_
      rw [hgx2, hgx1]
      have := congrArg (fun π : Equiv.Perm Y => π (x l')) hww
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using this
    have hst : (c y * c y') ^ 2 ∈ stabilizer K l' := hsq
    obtain ⟨r, rfl⟩ := hm
    have h2 : (c y * c y') ^ (2 * r + 1) • l' = (c y * c y') • l' := by
      rw [pow_succ', mul_smul, pow_mul, show ((c y * c y') ^ 2) ^ r • l' = l' from
        pow_mem hst r]
    rw [h2] at h1
    exact hw (by rw [Equiv.Perm.mul_apply, ← hgx1, h1])
  have hK1 : ∀ k, (∀ l ∈ L, ∀ l' ∈ L, D.coord l k = D.coord l' k → l = l') →
      ∀ ω ∈ holtDelta K X a b, ∀ l ∈ L, D.coord ω k = D.coord l k → x ω = x l := by
    intro k hk ω hω l hl heq
    by_contra hne
    obtain ⟨y, hy, y', hy', -, hw⟩ :=
      CCL.exists_mem_longInvAt_perm_mul_mul_self_eq_one hodd h5 (Ne.symm hne)
    have hgω : (c y * c y') • ω = ω := by
      rw [mul_smul]
      refine hcc y hy.1 y' hy'.1 ω hω ?_
      rw [show y' (x ω) = x ω from hy'.2]
      exact hy.2
    obtain ⟨hgl, hgx⟩ := hgL y hy.1 y' hy'.1 l hl
    refine hw ?_
    rw [Equiv.Perm.mul_apply, ← hgx]
    refine congrArg x (hk _ hgl l hl ?_)
    rw [← hfib y hy.1 y' hy'.1 k ω l heq, hgω, heq]
  obtain ⟨p₁, p₂, hp⟩ : ∃ p₁ p₂ : Y, p₁ ≠ p₂ := by
    obtain ⟨p₁, p₂, h⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Y)
    exact ⟨p₁, p₂, h⟩
  obtain ⟨l₁, hl₁, rfl⟩ := hsurj p₁
  obtain ⟨l₂, hl₂, rfl⟩ := hsurj p₂
  have hl₁₂ : l₁ ≠ l₂ := fun h => hp (by rw [h])
  have hinjk : ∀ k, (∃ m₁ ∈ L, ∃ m₂ ∈ L, D.coord m₁ k ≠ D.coord m₂ k) →
      ∀ l ∈ L, ∀ l' ∈ L, D.coord l k = D.coord l' k → l = l' := by
    rintro k ⟨m₁, hm₁, m₂, hm₂, hm⟩ l hl l' hl' heq
    by_contra hne
    exact hm ((hK3 k l hl l' hl' hne heq m₁ hm₁).trans (hK3 k l hl l' hl' hne heq m₂ hm₂).symm)
  obtain ⟨k, hk⟩ : ∃ k, D.coord l₁ k ≠ D.coord l₂ k := by
    by_contra h
    push Not at h
    exact hl₁₂ (hK4 l₁ hl₁ l₂ hl₂ (funext h))
  have hinj₁ := hinjk k ⟨l₁, hl₁, l₂, hl₂, hk⟩
  refine ⟨k, hinj₁, fun k' hk' m hm m' hm' => ?_⟩
  by_contra hne'
  have hinj' := hinjk k' ⟨m, hm, m', hm', hne'⟩
  have hmem : Function.update (D.coord l₁) k' (D.coord l₂ k') ∈
      D.coord '' holtDelta K X a b := by
    rw [D.coord_holtDelta_eq a b]
    intro i _
    by_cases hi : i = k'
    · subst hi
      rw [Function.update_self]
      exact D.coord_mem_holtDelta (hL hl₂) i
    · rw [Function.update_of_ne hi]
      exact D.coord_mem_holtDelta (hL hl₁) i
  obtain ⟨ω, hω, hωc⟩ := hmem
  have e1 := hK1 k hinj₁ ω hω l₁ hl₁ (by rw [hωc, Function.update_of_ne hk'.symm])
  have e2 := hK1 k' hinj' ω hω l₂ hl₂ (by rw [hωc, Function.update_self])
  exact hl₁₂ (hinj l₁ hl₁ l₂ hl₂ (e1.symm.trans e2))

end Sep

section NoParallel

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]
  {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

theorem not_parallel (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) {β' : Ω}
    {Λ' : Set Ω} {U : Subgroup G} (hU : fusionIsSylowIn 2 U (caseACentralizer G Ω α β' v Λ'))
    (hU1 : U ≠ ⊥) (h3 : 3 ≤ Nat.card (fixSet Ω U)) {w : G} (hw : w ∈ longInv G Ω)
    (hwv : w * v ∈ longInv G Ω) (hwU : w ∈ Subgroup.normalizer (U : Set G))
    (DK : HoltData (centralizerImage Ω U) (fixSet Ω U))
    (hker : jOrbitKernel (centralizerImage Ω U) (fixSet Ω U) =
      jOddCore (centralizerImage Ω U) (fixSet Ω U))
    (a : fixSet Ω U) (ha : (a : Ω) = α) (k : DK.ι)
    (hpar : ∀ ω : fixSet Ω U, ((ω : Ω) = β' ∨ (ω : Ω) ∈ Λ') → DK.coord ω k = DK.coord a k) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  have hvU : v ∈ Subgroup.centralizer (U : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun g hg => (Subgroup.mem_centralizer_iff.mp (hU.1 hg).1.1 v (Subgroup.mem_zpowers v)).symm
  obtain ⟨W, hUW, hW, -, x, hxW, hx2, hxv, hxc⟩ :=
    hS.exists_sylow_centralizer_mul hU.2.1 h3 hv2 hvU hw hwv hwU
      (zpowers_isPGroup_two_of_pow_eq_one (n := 1) (by rw [pow_one, sq]; exact hv2))
      (Subgroup.mem_zpowers v) (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hvU))
  have hxbar : restrictCentralizer Ω U ⟨x, Subgroup.centralizer_le hUW hxW⟩ =
      restrictCentralizer Ω U ⟨v, hvU⟩ :=
    Subtype.ext (Equiv.ext fun ω => Subtype.ext (hxv ω ω.2))
  have hxS : (restrictCentralizer Ω U ⟨x, Subgroup.centralizer_le hUW hxW⟩ :
      centralizerImage Ω U) ∈ DK.socPre := by
    rw [hxbar]
    exact hS.restrict_mem_socPre hU.2.1 hU1 h3 hvU hw hwv hwU DK
  have hxJ := DK.socPre_le_jHull hxS
  set xJ : jHull (centralizerImage Ω U) (fixSet Ω U) := ⟨_, hxJ⟩
  have hxx : xJ * xJ = 1 := Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
    show x • x • (ω : Ω) = ω
    have h1 : x • (ω : Ω) ∈ fixSet Ω U := smul_mem_fixSet_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hUW hxW)) ω.2
    rw [hxv _ h1, hxv _ ω.2, ← mul_smul, hv2, one_smul])))
  have hxa : DK.ρ k xJ (DK.coord a k) = DK.coord a k := by
    rw [← DK.coord_smul xJ a k]
    congr 2
    exact Subtype.ext ((hxv a a.2).trans (by rw [ha]; exact hP.typeL.smul_eq))
  have h24 := DK.socInvFixesBlocks_of_below (hS.star_centralizerImage hU.2.1 h3)
    (hS.holtTheorem1Below_centralizerImage hU.2.1 hU1 h3)
  have hxω : ∀ ω ∈ orbit (jOddCore (centralizerImage Ω U) (fixSet Ω U)) a,
      x • (ω : Ω) = ω := fun ω hω => by
    have hxa' : ∀ i, DK.ρ i xJ (DK.coord a i) = DK.coord a i := fun i => by
      rw [← DK.coord_smul xJ a i]
      congr 2
      exact Subtype.ext ((hxv a a.2).trans (by rw [ha]; exact hP.typeL.smul_eq))
    have h1 := h24 xJ hxS (by rw [← Subgroup.coe_mul, hxx, Subgroup.coe_one]) a
      (by rw [DK.smul_eq_of_rho_eq h24 hxS hxx hxa']; exact mem_orbit_self a) ω hω
    exact congrArg Subtype.val h1
  obtain ⟨m, hmM, hm1, hm2, hmp, hmx⟩ : ∃ m ∈ DK.M k, m ≠ 1 ∧ m * m = 1 ∧
      m (DK.coord a k) = DK.coord a k ∧ (DK.ρ k xJ = 1 ∨ DK.ρ k xJ = m) := by
    by_cases hx1 : DK.ρ k xJ = 1
    · obtain ⟨m, hm, h1, h2, h3⟩ := DK.exists_involution_fix k (DK.coord a k)
      exact ⟨m, hm, h1, h2, h3, Or.inl hx1⟩
    · refine ⟨_, DK.rho_mem_M_of_mem_socPre hxS k, hx1, ?_, hxa, Or.inr rfl⟩
      rw [← map_mul, hxx, map_one]
  obtain ⟨ℓ, hℓL, hℓk, hℓo⟩ := DK.exists_mem_L_rho_eq hmM
  have hlc : LiftsCommute (psiHom DK).range (psiHom DK ℓ) (psiHom DK xJ) := by
    rcases hmx with h | h
    · exact DK.liftsCommute_of_rho_eq_one hxS hℓo 0 (by rw [h, pow_zero, inv_one, one_mul])
    · exact DK.liftsCommute_of_rho_eq_one hxS hℓo 1 (by rw [pow_one, hℓk, h, inv_mul_cancel])
  have hq2 : psiHom DK ℓ * psiHom DK ℓ = 1 := funext fun i => by
    show DK.ρ i ℓ * DK.ρ i ℓ = 1
    by_cases hi : i = k
    · subst hi; rw [hℓk, hm2]
    · rw [hℓo i hi, mul_one]
  have hqfix : ∀ ω : fixSet Ω U, DK.coord ω k = DK.coord a k →
      ∀ i, psiHom DK ℓ i (DK.coord ω i) = DK.coord ω i := fun ω hω i => by
    show DK.ρ i ℓ (DK.coord ω i) = DK.coord ω i
    by_cases hi : i = k
    · subst hi; rw [hℓk, hω, hmp]
    · rw [hℓo i hi]; rfl
  obtain ⟨e, he, hex, he2, heα, hJ, heq⟩ := hS.exists_lift_elt hU.2.1 h3 hUW hW DK hker hxW
    hx2 hxJ (q := psiHom DK ℓ) ⟨ℓ, rfl⟩ (s := 1) (by rw [pow_one, sq]; exact hq2) hlc a hxω
    (hqfix a rfl)
  set ē : jHull (centralizerImage Ω U) (fixSet Ω U) := ⟨_, hJ⟩
  have hēS : (ē : centralizerImage Ω U) ∈ DK.socPre := by
    have hk : ((ℓ⁻¹ * ē : jHull (centralizerImage Ω U) (fixSet Ω U)) :
        centralizerImage Ω U) ∈ jOddCore (centralizerImage Ω U) (fixSet Ω U) := by
      rw [← hker, DK.mem_jOrbitKernel_iff_rho]
      intro i
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact (congrFun heq i).symm
    have := mul_mem (DK.L_le_socPre k hℓL) (DK.jOddCore_le_socPre hk)
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
  have hēē : ē * ē = 1 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp he2) ⟨e, Subgroup.mem_zpowers e⟩
    have hen : e ^ 2 ^ n = 1 := by
      have := pow_orderOf_eq_one (⟨e, Subgroup.mem_zpowers e⟩ : Subgroup.zpowers e)
      rw [hn] at this
      exact congrArg Subtype.val this
    have hēn : (ē * ē) ^ 2 ^ n = 1 := by
      rw [← sq, ← pow_mul, mul_comm, pow_mul]
      have : ē ^ 2 ^ n = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        show (restrictCentralizer Ω U ⟨e, _⟩) ^ 2 ^ n = 1
        rw [← map_pow, show (⟨e, Subgroup.centralizer_le hUW he⟩ :
          Subgroup.centralizer (U : Set G)) ^ 2 ^ n = 1 from Subtype.ext (by
            rw [Subgroup.coe_pow]; exact hen), map_one])
      rw [this, one_pow]
    have hk : ((ē * ē : jHull (centralizerImage Ω U) (fixSet Ω U)) :
        centralizerImage Ω U) ∈ jOddCore (centralizerImage Ω U) (fixSet Ω U) := by
      rw [← hker, DK.mem_jOrbitKernel_iff_rho]
      intro i
      rw [map_mul]
      have h1 := congrFun hq2 i
      have h2 := congrFun heq i
      simp only [psiHom, MonoidHom.pi_apply, Pi.mul_apply, Pi.one_apply] at h1 h2
      rw [h2, h1]
    exact Subtype.ext (eq_one_of_pow_two_pow_eq_one_of_mem odd_card_jOddCore hk
      (by rw [← Subgroup.coe_pow, hēn, Subgroup.coe_one]))
  have hfixē : ∀ ω : fixSet Ω U, DK.coord ω k = DK.coord a k → e • (ω : Ω) = ω :=
    fun ω hω => congrArg Subtype.val (DK.smul_eq_of_rho_eq h24 hēS hēē fun i => by
      have := hqfix ω hω i
      rw [← heq] at this
      exact this)
  have hβU : β' ∈ fixSet Ω U := fun g hg => (hU.1 hg).1.2.2
  have hΛU : ∀ δ ∈ Λ', δ ∈ fixSet Ω U := fun δ hδ g hg =>
    (mem_fixingSubgroup_iff G).mp (hU.1 hg).2 δ hδ
  have he𝒞 : e ∈ caseACentralizer G Ω α β' v Λ' := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨n, rfl⟩
      exact ((hxc e he hex).zpow_right n).eq.symm
    · show e • α = α
      rw [← ha]; exact heα
    · exact hfixē ⟨β', hβU⟩ (hpar _ (Or.inl rfl))
    · exact (mem_fixingSubgroup_iff G).mpr fun δ hδ =>
        hfixē ⟨δ, hΛU δ hδ⟩ (hpar _ (Or.inr hδ))
  have heU' : e ∈ Subgroup.centralizer (U : Set G) := Subgroup.centralizer_le hUW he
  have heU : e ∈ U := by
    have h2 : IsPGroup 2 (U ⊔ Subgroup.zpowers e : Subgroup G) :=
      hU.2.1.to_sup_of_normal_left' he2
        (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ heU'))
    have := hU.2.2 _ (sup_le hU.1 (Subgroup.zpowers_le.mpr he𝒞)) h2 le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hē1 : ē = 1 := Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
    show e • (ω : Ω) = ω
    exact ω.2 e heU)))
  have := congrFun heq k
  rw [hē1, map_one] at this
  have h1 : (1 : Equiv.Perm (DK.Ψc k)) = DK.ρ k ℓ := this
  rw [hℓk] at h1
  exact hm1 h1.symm

end NoParallel

namespace DCase

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]
  {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)} {hS : Sec4Setting G Ω}
  {hP : Prop46Setup G Ω α v P} (H : DCase hS hP)

omit [Finite G] [FaithfulSMul G Ω] in
theorem VΔ_fix : α ∈ fixSet Ω H.VΔ ∧ H.β₁ ∈ fixSet Ω H.VΔ ∧
    ∀ δ ∈ holtDelta G Ω α H.β₁, δ ∈ fixSet Ω H.VΔ :=
  ⟨fun _ hg => (H.VΔ_le_Zc hg).1.2.1, fun _ hg => (H.VΔ_le_Zc hg).1.2.2,
    fun δ hδ _ hg => (mem_fixingSubgroup_iff G).mp (H.VΔ_le_Zc hg).2 δ hδ⟩

omit [Finite G] [FaithfulSMul G Ω] in
theorem three_le_VΔ : 3 ≤ Nat.card (fixSet Ω H.VΔ) := by
  obtain ⟨hα, hβ, hΔ⟩ := H.VΔ_fix
  rw [Nat.card_coe_set_eq]
  have hγα : H.γ₁ ≠ α := fun h => left_notMem_holtDelta H.αβ₁ (h ▸ H.γ₁_mem)
  have hγβ : H.γ₁ ≠ H.β₁ := fun h => right_notMem_holtDelta H.αβ₁ (h ▸ H.γ₁_mem)
  exact (Set.ncard_eq_three.mpr ⟨α, H.β₁, H.γ₁, H.αβ₁, hγα.symm, hγβ.symm, rfl⟩).symm.le.trans
    (Set.ncard_le_ncard (Set.insert_subset hα (Set.insert_subset hβ
      (Set.singleton_subset_iff.mpr (hΔ _ H.γ₁_mem)))) (Set.toFinite _))

theorem VΔ_ne_bot (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α H.β₁))) : H.VΔ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨E, hE, hEZ, hE1⟩ := H.X₀.exists_isPGroup_le_caseACentralizer_holtDelta hP hT
  obtain ⟨R, hER, hR⟩ := exists_fusionIsSylowIn_ge hE hEZ
  obtain ⟨z, -, hz⟩ := exists_mem_conj_of_fusionIsSylowIn (H.sylow_VΔ hT) hR
  refine hE1 (eq_bot_iff.mpr fun e he => ?_)
  have h1 := (hz e).mp (hER he)
  rw [h, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  have h2 : e = z * (z⁻¹ * e * z) * z⁻¹ := by group
  rw [h2, h1, mul_one, mul_inv_cancel]

theorem exists_w₂ (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α H.β₁))) :
    ∃ w₂ ∈ longInv G Ω, w₂ * v ∈ longInv G Ω ∧ w₂ ∈ Subgroup.normalizer (H.VΔ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w := H.X₀.w
  have hw2 : IsPGroup 2 (Subgroup.zpowers w) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, sq]; exact mul_self_eq_one_of_mem_longInv H.X₀.w_mem.1)
  have hwΔ : w • holtDelta G Ω α H.β₁ = holtDelta G Ω α H.β₁ := by
    have := stabilizer_pair_le (G := G) α H.X₀.β H.X₀.w_mem_pair
    rwa [mem_stabilizer_iff] at this
  obtain ⟨T₁, -, hT₁, hwT₁⟩ := exists_fusionIsSylowIn_ge_mem_normalizer (V := ⊥)
    IsPGroup.of_bot bot_le hw2 (H.X₀.w_mem_normalizer_caseACentralizer hwΔ)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normal_bot)]; exact Subgroup.mem_top _)
  obtain ⟨z, hzZ, hz⟩ := exists_mem_conj_of_fusionIsSylowIn (H.sylow_VΔ hT) hT₁
  have hzv : Commute z v :=
    (Subgroup.mem_centralizer_iff.mp hzZ.1.1 v (Subgroup.mem_zpowers v)).symm
  have hww : w * w = 1 := mul_self_eq_one_of_mem_longInv H.X₀.w_mem.1
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have key : ∀ u ∈ H.VΔ, (z⁻¹ * w * z) * u * (z⁻¹ * w * z)⁻¹ ∈ H.VΔ := by
    intro u hu
    have h1 : z * u * z⁻¹ ∈ T₁ := (hz _).mpr (by simpa [mul_assoc] using hu)
    have h2 : w * (z * u * z⁻¹) * w⁻¹ ∈ T₁ := (Subgroup.mem_normalizer_iff.mp hwT₁ _).mp h1
    have h3 := (hz _).mp h2
    convert h3 using 1
    group
  refine ⟨z⁻¹ * w * z, ?_, ?_, Subgroup.mem_normalizer_iff.mpr fun u => ⟨key u, fun hu => ?_⟩⟩
  · simpa using conj_mem_longInv H.X₀.w_mem.1 z⁻¹
  · have h := conj_mem_longInv H.X₀.wv_mem z⁻¹
    rw [inv_inv] at h
    convert h using 1
    rw [mul_assoc (z⁻¹ * w) z v, hzv.eq]
    group
    rfl
  · have h := key _ hu
    convert h using 1
    rw [mul_inv_rev, mul_inv_rev, inv_inv, hwinv]
    calc u = z⁻¹ * (w * w) * z * u * (z⁻¹ * (w * w) * z) := by rw [hww]; group
      _ = _ := by group

end DCase

end CaseAD

end CFSG.Holt.H78
