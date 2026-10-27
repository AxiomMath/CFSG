module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lay

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance

namespace S289

variable {G : Type} [Group G] {Λ : Subgroup G} {a : G}

@[expose] noncomputable def vtxHom (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G)) :
    ↥Λ →* OddQuot a :=
  (oddQuotMk a).comp (Subgroup.inclusion hΛ)

theorem vtxHom_apply (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G)) (y : ↥Λ) :
    vtxHom hΛ y = oddQuotMk a ⟨y, hΛ y.2⟩ :=
  rfl

theorem range_vtxHom (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G)) :
    (vtxHom hΛ).range = modOdd a Λ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y, hΛ y.2⟩, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩

theorem oddCoreOf_eq_inf [Finite G] (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G))
    (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ) :
    oddCoreOf Λ = Λ ⊓ oddCoreOf (Subgroup.centralizer ({a} : Set G)) := by
  refine le_antisymm (le_inf (oddCoreOf_le_self Λ) ?_) (inf_oddCoreOf_le hΛ)
  refine le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self Λ).trans hΛ) (fun c hc => ?_)
    (oddCoreOf_odd_natCard Λ)
  refine mem_normalizer_oddCore_of_mem_normalizer ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hN c hc y
  · intro hy
    have h1 := hN c⁻¹ ((Subgroup.centralizer ({a} : Set G)).inv_mem hc) _ hy
    rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h1

theorem ker_vtxHom [Finite G] (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G))
    (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ) :
    (vtxHom hΛ).ker = classicalInvolutionOddCore ↥Λ := by
  ext y
  rw [MonoidHom.mem_ker, vtxHom_apply, oddQuotMk_eq_one_iff]
  have e := oddCoreOf_eq_inf hΛ hN
  constructor
  · intro hy
    have h1 : (y : G) ∈ oddCoreOf (Subgroup.centralizer ({a} : Set G)) :=
      mem_oddCoreOf_iff.mpr ⟨hΛ y.2, hy⟩
    have h2 : (y : G) ∈ oddCoreOf Λ := by
      rw [e]
      exact ⟨y.2, h1⟩
    obtain ⟨_, h3⟩ := mem_oddCoreOf_iff.mp h2
    exact h3
  · intro hy
    have h1 : (y : G) ∈ oddCoreOf Λ := mem_oddCoreOf_iff.mpr ⟨y.2, hy⟩
    rw [e] at h1
    obtain ⟨_, h2⟩ := mem_oddCoreOf_iff.mp h1.2
    exact h2

@[expose] noncomputable def vtxEquiv [Finite G] (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G))
    (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ) :
    ↥Λ ⧸ classicalInvolutionOddCore ↥Λ ≃* ↥(modOdd a Λ) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_vtxHom hΛ hN)).symm.trans
    ((QuotientGroup.quotientKerEquivRange (vtxHom hΛ)).trans
      (MulEquiv.subgroupCongr (range_vtxHom hΛ)))

theorem vtxEquiv_mk [Finite G] (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G))
    (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ) (y : ↥Λ) :
    ((vtxEquiv hΛ hN (QuotientGroup.mk y) : ↥(modOdd a Λ)) : OddQuot a) =
      oddQuotMk a ⟨y, hΛ y.2⟩ :=
  rfl

theorem modOdd_normal (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ) :
    (modOdd a Λ).Normal := by
  have hn : (Λ.subgroupOf (Subgroup.centralizer ({a} : Set G))).Normal :=
    ⟨fun y hy c => Subgroup.mem_subgroupOf.mpr (by
      simpa using hN c c.2 y (Subgroup.mem_subgroupOf.mp hy))⟩
  exact hn.map _ (QuotientGroup.mk'_surjective _)

theorem le_of_moved {Q : Type} [Group Q] [Finite Q] {N L : Subgroup Q} (hN : N.Normal)
    (hL : IsComponent L) {x : Q} (hx : x ∈ N) (hm : ∃ y ∈ L, x * y ≠ y * x) : L ≤ N := by
  rcases LocalCores.component_normal_subgroup hL hN with h | h
  · exact h
  · exfalso
    obtain ⟨y, hy, hne⟩ := hm
    have hc := Subgroup.commutator_mem_commutator hy hx
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hne hc.symm

theorem eq_top_of_isComponent {Q : Type} [Group Q] (hQ : IsQuasisimple Q) {K : Subgroup Q}
    (hK : IsComponent K) : K = ⊤ := by
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hQ hK.2 with h | h
  · exact h
  · exfalso
    have : Nontrivial K := LocalCores.isQuasisimple_nontrivial hK.1
    have hcomm : ∀ x y : K, x * y = y * x := fun x y =>
      Subtype.ext (Subgroup.mem_center_iff.mp (h x.2) y).symm
    have : Group.IsPerfect K := hK.1.1
    exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_comm hcomm)

theorem isComponent_transfer [Finite G] (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G))
    (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ)
    {L : Subgroup (OddQuot a)} (hL : IsComponent L) (hLN : L ≤ modOdd a Λ) :
    IsComponent ((L.subgroupOf (modOdd a Λ)).map (vtxEquiv hΛ hN).symm.toMonoidHom) :=
  LocalCores.isComponent_map_mulEquiv _ (LocalCores.component_overgroup hL hLN)

theorem eq_of_isQuasisimple [Finite G] (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G))
    (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ)
    (hq : IsQuasisimple (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) {L : Subgroup (OddQuot a)}
    (hL : IsComponent L) (hLN : L ≤ modOdd a Λ) : L = modOdd a Λ := by
  have h1 := eq_top_of_isComponent hq (isComponent_transfer hΛ hN hL hLN)
  have h2 : L.subgroupOf (modOdd a Λ) = ⊤ := by
    have h4 := LocalCores.map_map_symm (vtxEquiv hΛ hN).symm (L.subgroupOf (modOdd a Λ))
    rw [MulEquiv.symm_symm, h1,
      Subgroup.map_top_of_surjective _ (MulEquiv.surjective (vtxEquiv hΛ hN))] at h4
    exact h4.symm
  exact le_antisymm hLN (Subgroup.subgroupOf_eq_top.mp h2)

theorem commute_of_trivialOn [Finite G] (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G))
    (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ) {b : G}
    (hbC : b ∈ Subgroup.centralizer ({a} : Set G))
    (htriv : ∀ y ∈ Λ, b * y * b⁻¹ * y⁻¹ ∈ oddCoreOf Λ) :
    ∀ x ∈ modOdd a Λ, oddQuotMk a ⟨b, hbC⟩ * x = x * oddQuotMk a ⟨b, hbC⟩ := by
  rintro _ ⟨k, hk, rfl⟩
  have hkΛ : (k : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hk
  have h1 := htriv k hkΛ
  rw [oddCoreOf_eq_inf hΛ hN] at h1
  obtain ⟨_, h2⟩ := mem_oddCoreOf_iff.mp h1.2
  rw [← map_mul, ← map_mul]
  refine (QuotientGroup.eq_iff_div_mem).mpr ?_
  have e : (⟨b, hbC⟩ * k : ↥(Subgroup.centralizer ({a} : Set G))) / (k * ⟨b, hbC⟩) =
      ⟨b * k * b⁻¹ * k⁻¹, (Subgroup.centralizer ({a} : Set G)).mul_mem
        ((Subgroup.centralizer ({a} : Set G)).mul_mem
          ((Subgroup.centralizer ({a} : Set G)).mul_mem hbC k.2)
          ((Subgroup.centralizer ({a} : Set G)).inv_mem hbC))
        ((Subgroup.centralizer ({a} : Set G)).inv_mem k.2)⟩ := by
    apply Subtype.ext
    simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    group
  rw [e]
  exact h2

theorem not_movedByAll_of_trivialOn [Finite G] (hΛ : Λ ≤ Subgroup.centralizer ({a} : Set G))
    (hN : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ)
    {B : Subgroup G} {b : G} (hbB : b ∈ B) (hbC : b ∈ Subgroup.centralizer ({a} : Set G))
    (hbZ : oddQuotMk a ⟨b, hbC⟩ ∉ modOdd a (Subgroup.zpowers a))
    (htriv : ∀ y ∈ Λ, b * y * b⁻¹ * y⁻¹ ∈ oddCoreOf Λ) {L : Subgroup (OddQuot a)}
    (hLN : L ≤ modOdd a Λ) : ¬ MovedByAll B a L := by
  intro hm
  obtain ⟨y, hy, hne⟩ := hm _ (oddQuotMk_mem_modOdd hbB hbC) hbZ
  exact hne (commute_of_trivialOn hΛ hN hbC htriv y (hLN hy))

end S289

end CFSG.ClassicalInvolution.Q3.TL4
