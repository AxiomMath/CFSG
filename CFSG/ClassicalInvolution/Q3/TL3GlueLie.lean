module

public import CFSG.ClassicalInvolution.Q3.TL3GlueCoc
public import CFSG.ClassicalInvolution.Q3.TL3GlueLayer
public import CFSG.ClassicalInvolution.Q3.Q3NLExact
public import CFSG.ClassicalInvolution.Q3.Q3NMInner
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.GlueLie

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Basic

variable {X : Type} [Group X] [Finite X]

theorem classicalInvolutionOddCore_eq_bot_of_isSubnormal
    (hO : oddCoreIn (⊤ : Subgroup X) = ⊥) {H : Subgroup X} (hH : IsSubnormal H ⊤) :
    classicalInvolutionOddCore H = ⊥ := by
  have h1 : oddCoreIn H ≤ oddCoreIn ⊤ := oddCoreIn_le_of_isSubnormal hH
  rw [hO] at h1
  have h2 : (componentClassificationOddCore H).map H.subtype = ⊥ := le_bot_iff.mp h1
  have h3 : componentClassificationOddCore H = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h2
  exact h3

theorem mem_oddCoreIn_centralizer_subgroupOf {K : Subgroup X} {z : X} (hz : z ∈ K) {w : K}
    (hw : (w : X) ∈ oddCoreIn (Subgroup.centralizer ({z} : Set X))) :
    w ∈ oddCoreIn (Subgroup.centralizer ({(⟨z, hz⟩ : K)} : Set K)) := by
  set O : Subgroup X := oddCoreIn (Subgroup.centralizer ({z} : Set X)) with hO
  have hle : O.subgroupOf K ≤ Subgroup.centralizer ({(⟨z, hz⟩ : K)} : Set K) := by
    intro x hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp
      (oddCoreIn_le _ (Subgroup.mem_subgroupOf.mp hx))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext h1
  have hnorm : Subgroup.centralizer ({(⟨z, hz⟩ : K)} : Set K) ≤
      Subgroup.normalizer ((O.subgroupOf K : Subgroup K) : Set K) := by
    refine le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
    have hcz : (c : X) * z = z * c :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
    rw [Subgroup.mem_subgroupOf]
    exact conj_mem_oddCoreIn (Subgroup.mem_centralizer_singleton_iff.mpr hcz)
      (Subgroup.mem_subgroupOf.mp hx)
  have hodd : Odd (Nat.card (O.subgroupOf K)) := by
    have h1 : Nat.card (O.subgroupOf K) = Nat.card (O ⊓ K : Subgroup X) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]
    rw [h1]
    exact (odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact le_oddCoreIn_of_normalizes hle hnorm hodd (Subgroup.mem_subgroupOf.mpr hw)

end Basic

section Lie


theorem exists_component_eq_of_member {X : Type} [Group X] [Finite X]
    (hO : oddCoreIn (⊤ : Subgroup X) = ⊥) (hBelow : CIT3Below (Nat.card X + 1))
    {L : Subgroup X} {z : X} (hL : IsClassicalMember3 L z) :
    ∃ Q : Subgroup X, z ∈ Q ∧ L ≤ Q ∧
      ∀ K : Subgroup X, IsComponentOf K ⊤ → (∃ y ∈ K, y * z ≠ z * y) → K = Q := by
  classical
  set 𝒮 : Set (Subgroup X) := Set.range fun g : X => conjSub g L with h𝒮
  set H : Subgroup X := ⨆ L' ∈ 𝒮, L' with hH
  have hinv : ConjInvariant 𝒮 := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul n g L⟩
  have hHn : H.Normal := normal_biSup hinv
  have hHs : IsSubnormal H ⊤ := isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hle : ∀ L' ∈ 𝒮, L' ≤ H := fun L' hL' => le_iSup₂_of_le L' hL' le_rfl
  have hLH : L ≤ H := hle L ⟨1, conjSub_one L⟩
  have hzH : z ∈ H := hLH hL.mem
  have hcl : InClass3 (restrictFamily 𝒮 H) := by
    refine Q3NL.inClass3_of_isClassicalMember3In ⟨L, 1, conjSub_one L⟩ hle
      (fun n _ L' hL' => hinv n L' hL') rfl ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨g * z * g⁻¹, _, (hL.conj g).subgroupOf (hle _ ⟨g, rfl⟩)⟩
  have hcard : Nat.card H < Nat.card X + 1 := Nat.lt_succ_of_le (Subgroup.card_le_card_group H)
  have hmod : LieSystemMod3 (restrictFamily 𝒮 H) := hBelow H hcard _ hcl
  have hOH : classicalInvolutionOddCore H = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_isSubnormal hO hHs
  obtain ⟨ι, _, ⟨D⟩⟩ := lieSystem3_of_lieSystemMod3_corefree hOH hmod
  have hL'mem : L.subgroupOf H ∈ restrictFamily 𝒮 H := ⟨L, ⟨1, conjSub_one L⟩, hLH, rfl⟩
  obtain ⟨j, R, -, hLR⟩ := D.fundamental _ hL'mem
  set N : Subgroup H := (D.hom j).range with hN
  have hLN : L.subgroupOf H ≤ N := by
    rw [hLR]
    exact Subgroup.map_le_range _ _
  have hzN : (⟨z, hzH⟩ : H) ∈ N := hLN (Subgroup.mem_subgroupOf.mpr hL.mem)
  have hNn : N.Normal := Q3W.range_normal3 D j
  have hNs : IsSubnormal N ⊤ := isSubnormal_of_normal_subgroupOf le_top inferInstance
  refine ⟨N.map H.subtype, ⟨⟨z, hzH⟩, hzN, rfl⟩, fun x hx =>
    ⟨⟨x, hLH hx⟩, hLN (Subgroup.mem_subgroupOf.mpr hx), rfl⟩, ?_⟩
  intro K hK hKz
  have hKH : K ≤ H := component_le_of_not_commute hHs hzH hK hKz
  have hK' : IsComponentOf (K.subgroupOf H) ⊤ :=
    CFSG.ComponentClassification.LocalComponents.of_overgroup hK hKH
  have hKcomm : ¬ ⁅K.subgroupOf H, N⁆ = ⊥ := by
    intro h
    obtain ⟨y, hy, hyz⟩ := hKz
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hy' : (⟨y, hKH hy⟩ : H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.mpr hy
    have h1 := (Subgroup.mem_centralizer_iff.mp (hcen hy')) _ hzN
    exact hyz (congrArg Subtype.val h1).symm
  by_cases hA1 : Q3W.IsA1Comp3 D j
  · have : Group.IsSolvable N := isSolvable_range_of_sl23 hA1 (D.hom j)
    exact absurd (CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
      _ N hK' hNs) hKcomm
  · have hNq : CFSG.Open.IsQuasisimple N :=
      Q3W.isQuasisimple_range3 D j (Q3W.isQuasisimple_of_not_a1 D hA1)
    have hNc : IsComponentOf N ⊤ := ⟨le_top, hNs, hNq⟩
    have heq : K.subgroupOf H = N := by
      by_contra hne
      exact hKcomm (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK' hNc hne)
    rw [← heq, Subgroup.map_subgroupOf_eq_of_le hKH]

end Lie

section Rigid


theorem rigid_of_member {X : Type} [Group X] [Finite X] (hBelow : CIT3Below (Nat.card X + 1))
    {K : Subgroup X} (hKq : CFSG.Open.IsQuasisimple K) {L : Subgroup X} {z : X}
    (hL : IsClassicalMember3 L z) (hLK : L ≤ K) (α : MulAut X) {m : ℕ} (hm : Odd m)
    (hαm : α ^ m = 1) (hαK : ∀ y ∈ K, α y ∈ K)
    (hC : ∀ c ∈ Subgroup.centralizer ({z} : Set X),
      c⁻¹ * α c ∈ oddCoreIn (Subgroup.centralizer ({z} : Set X))) :
    ∀ y ∈ K, α y = y := by
  classical
  set β : MulAut K := Q3TIY.restrictAut K α hαK with hβdef
  have hβm : β ^ m = 1 := Q3TIY.restrictAut_pow_eq_one K α hαK hαm
  have hzK : z ∈ K := hLK hL.mem
  set zK : K := ⟨z, hzK⟩ with hzKdef
  have hz2 : zK * zK = 1 := by
    apply Subtype.ext
    show z * z = 1
    rw [← sq, ← hL.orderOf_eq_two, pow_orderOf_eq_one]
  have hfix : ∀ c : K, c * zK = zK * c →
      c⁻¹ * β c ∈ oddCoreIn (Subgroup.centralizer ({zK} : Set K)) := by
    intro c hc
    have hcz : (c : X) * z = z * c := congrArg Subtype.val hc
    exact mem_oddCoreIn_centralizer_subgroupOf hzK
      (hC c (Subgroup.mem_centralizer_singleton_iff.mpr hcz))
  set φ : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hφ
  have hXq : CFSG.Open.IsQuasisimple (K ⧸ Subgroup.center K) :=
    CFSG.ComponentClassification.Quasisimple.central_quotient hKq (Subgroup.center K) le_rfl
  have hXZ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    Q3NM.center_quotient_center_eq_bot_of_isQuasisimple hKq
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hKq.2
  have hclK : IsClassicalMember3 (L.subgroupOf K) zK := hL.subgroupOf hLK
  have hzc : zK ∉ Subgroup.center K := hclK.not_mem_center_of_quasisimple hKq
  have hz1 : φ zK ≠ 1 := fun h => hzc ((QuotientGroup.eq_one_iff _).mp h)
  have hker : φ.ker ≤ Subgroup.center K := by rw [hφ, QuotientGroup.ker_mk']
  have hcl : IsClassicalMember3 ((L.subgroupOf K).map φ) (φ zK) :=
    hclK.map_central φ (QuotientGroup.mk'_surjective _) hker hz1
  have hΛ := inClass3_conjugates hcl
  have hcardX : Nat.card (K ⧸ Subgroup.center K) < Nat.card X + 1 := by
    have h1 : Nat.card (K ⧸ Subgroup.center K) ≤ Nat.card K :=
      Nat.card_le_card_of_surjective φ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card K ≤ Nat.card X := Subgroup.card_le_card_group K
    omega
  have hLie := hBelow _ hcardX _ hΛ
  have hodd : Odd (orderOf (Q3TIY.centerQuotAut β)) :=
    hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one (Q3TIY.centerQuotAut_pow_eq_one _ hβm))
  have hhyp : ∀ c ∈ Subgroup.centralizer ({φ zK} : Set (K ⧸ Subgroup.center K)),
      c⁻¹ * Q3TIY.centerQuotAut β c ∈
        oddCoreIn (Subgroup.centralizer ({φ zK} : Set (K ⧸ Subgroup.center K))) := by
    intro c hc
    obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) c
    exact cocycle_mem_oddCoreIn_of_mod β hm hβm hz2 hfix c' hc
  have hrigid : Q3TIY.centerQuotAut β = 1 :=
    Q3T.modelOddAutRigid_proved _ hXq hXZ _ hΛ hLie (φ zK) _ ⟨1, conjSub_one _⟩ hcl _ hodd hhyp
  have hβ1 : β = 1 := by
    refine Q3TIY.eq_one_of_perfect_of_central_ratio hKq.1 _ fun q => ?_
    have h1 : Q3TIY.centerQuotAut β (φ q) = φ q := by
      rw [hrigid]
      rfl
    rw [Q3TIY.centerQuotAut_mk] at h1
    have h2 : φ (q⁻¹ * β q) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h2
  intro y hy
  have h3 : β ⟨y, hy⟩ = ⟨y, hy⟩ := by
    rw [hβ1]
    rfl
  exact congrArg Subtype.val h3

end Rigid

end CFSG.ClassicalInvolution.Q3.GlueLie

namespace CFSG.ClassicalInvolution.Q3.TightDatum

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.GlueLie


variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
  (d : TightDatum R S t)

theorem layerRigidAt_of_member (hBelow : CIT3Below (Nat.card d.Dbar + 1)) {ub : d.Dbar}
    {L : Subgroup d.Dbar} (hL : IsClassicalMember3 L ub) : d.LayerRigidAt ub := by
  obtain ⟨Q, -, hLQ, hQ⟩ := exists_component_eq_of_member d.oddCoreIn_top_dbar_eq_bot hBelow hL
  refine d.layerRigidAt_of_subnormal (IsSubnormal.refl ⊤) (Subgroup.mem_top ub)
    (fun K₁ K₂ h₁ h₂ _ _ hu₁ hu₂ => (hQ K₁ h₁ hu₁).trans (hQ K₂ h₂ hu₂).symm) ?_
  intro K hK _ hKu α k hα _ hC hαK
  have hKQ : K = Q := hQ K hK hKu
  have hLK : L ≤ K := hKQ ▸ hLQ
  have hαK' : ∀ y ∈ K, α y ∈ K := fun y hy => by
    rw [← hαK]
    exact ⟨y, hy, rfl⟩
  refine ⟨1, K.one_mem, fun y hy => ?_⟩
  rw [rigid_of_member hBelow hK.2.2 hL hLK α (Odd.pow (by decide)) hα hαK' hC y hy]
  group

theorem good_of_section_member (hBelow : CIT3Below (Nat.card d.Dbar + 1)) {u : G}
    (hut : u ∈ Subgroup.centralizer ({t} : Set G))
    (huK : (⟨u, hut⟩ : Subgroup.centralizer ({t} : Set G)) ∈ d.act.ker) (hu2 : u * u = 1)
    (htu : t ∈ Subgroup.centralizer ({u} : Set G))
    (hg : GoodThreeElement (R.subgroupOf (Subgroup.centralizer ({u} : Set G))) (⟨t, htu⟩ : _))
    {L : Subgroup d.Dbar} (hL : IsClassicalMember3 L (d.toDbar ⟨_, huK⟩)) :
    GoodThreeElement R t :=
  d.good_of_section hut huK hu2 htu hg (d.layerRigidAt_of_member hBelow hL)

end CFSG.ClassicalInvolution.Q3.TightDatum
