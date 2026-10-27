module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDD8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS4

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppC

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem {T M₀ : Subgroup G} (hT : IsPGroup 2 T) (hMT : M₀ ≤ T)
    (hne : M₀ ≠ T) : ∃ y ∈ T, y ∈ Subgroup.normalizer (M₀ : Set G) ∧ y ∉ M₀ := by
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnc : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent
  have hIne : M₀.subgroupOf T ≠ ⊤ := by
    intro htop
    apply hne
    refine le_antisymm hMT fun t ht => ?_
    have : (⟨t, ht⟩ : ↥T) ∈ M₀.subgroupOf T := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  have hlt := hnc _ (lt_top_iff_ne_top.2 hIne)
  obtain ⟨y, hyN, hyI⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨y, y.2, ?_, fun h => hyI (Subgroup.mem_subgroupOf.2 h)⟩
  have : y ∈ (Subgroup.normalizer (M₀ : Set G)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hMT]
    exact hyN
  exact Subgroup.mem_subgroupOf.1 this

omit [Finite G] in
theorem mem_normalizer_sup_of {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer, C5.conjSubgroup_sup, C5.conjSubgroup_eq_self hA,
    C5.conjSubgroup_eq_self hB]

namespace GMate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : GCfg T M H S L) (m : GMate S T M₀ x)
include C m

theorem card_S_eq : Nat.card S = 2 * Nat.card (baum S) := by
  have hQB := m.Q_le_B C
  have hBS : baum S ≤ S := inf_le_left
  have hQC : pCoreOf 2 H ≤ Subgroup.centralizer (C.U : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U hq hu).symm
  have hinf : ∀ K : Subgroup G, K ≤ S → pCoreOf 2 H ≤ K →
      K ⊓ Subgroup.centralizer (C.U : Set G) = pCoreOf 2 H := fun K hKS hQK =>
    le_antisymm (fun a ha => by rw [← C.hQ]; exact ⟨C.hSH (hKS ha.1), ha.2⟩) (le_inf hQK hQC)
  have h1 := C.P.card_im_mul (A := S) le_rfl
  have h2 := C.P.card_im_mul (A := baum S) (hBS)
  rw [C.hS, Dstd_card, hinf S le_rfl C.hQS] at h1
  rw [C.hB, Estd_card, hinf (baum S) hBS hQB] at h2
  omega

omit [Finite G] C in
theorem baum_le_Γ : baum S ≤ T ⊓ Subgroup.normalizer (M₀ : Set G) :=
  le_inf ((inf_le_left : baum S ≤ S).trans (m.hSM.trans m.hMT))
    ((inf_le_left : baum S ≤ S).trans (m.hSM.trans Subgroup.le_normalizer))

theorem card_Γ_ge (hT : IsPGroup 2 T) (hne : M₀ ≠ T) :
    8 * Nat.card (baum S) ≤ Nat.card ↥(T ⊓ Subgroup.normalizer (M₀ : Set G)) := by
  obtain ⟨y, hyT, hyN, hyM⟩ := exists_mem_normalizer_not_mem hT m.hMT hne
  have hle : M₀ ≤ T ⊓ Subgroup.normalizer (M₀ : Set G) := le_inf m.hMT Subgroup.le_normalizer
  have hlt : Nat.card M₀ < Nat.card ↥(T ⊓ Subgroup.normalizer (M₀ : Set G)) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun h => ?_
    have := Subgroup.eq_of_le_of_card_ge hle h.ge
    exact hyM (this ▸ (⟨hyT, hyN⟩ : y ∈ T ⊓ Subgroup.normalizer (M₀ : Set G)))
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hMpos : 0 < Nat.card M₀ := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hk'
    push Not at hk'
    interval_cases k
    · omega
    · omega
  have hM₀ : Nat.card M₀ = 2 * Nat.card S := by
    have := Subgroup.relIndex_mul_card (H := S) (K := M₀)
    rw [m.h2, inf_eq_left.2 m.hSM] at this
    omega
  have hS := m.card_S_eq C
  have h3 : Nat.card M₀ * 2 ≤ Nat.card M₀ * k := Nat.mul_le_mul_left _ hk2
  omega

theorem card_range_rho
    (F : GFour C x) (hT : IsPGroup 2 T) (hne : M₀ ≠ T) :
    Nat.card (m.rho C F).range = 8 := by
  set ρ := m.rho C F with hρ
  have hker : ρ.ker = (baum S).subgroupOf (T ⊓ Subgroup.normalizer (M₀ : Set G)) := by
    ext γ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hρ]
    exact m.rho_eq_one_iff C F γ
  have hkcard : Nat.card ρ.ker = Nat.card (baum S) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (m.baum_le_Γ)).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range ρ
  have h2 := m.card_Γ_ge C hT hne
  have hΓ : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (M₀ : Set G)) := hT.to_le inf_le_left
  have hR : IsPGroup 2 ↥ρ.range := hΓ.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have h3 := card_le_eight hR
  have hBpos : 0 < Nat.card (baum S) := Nat.card_pos
  rw [hkcard] at h1
  have h4 : 8 ≤ Nat.card ρ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (baum S) * Nat.card ρ.range < Nat.card (baum S) * 8 :=
      Nat.mul_lt_mul_of_pos_left hlt hBpos
    omega
  omega

theorem rho_dihedral
    (F : GFour C x) (hT : IsPGroup 2 T) (hne : M₀ ≠ T) :
    ∃ f : ↥(T ⊓ Subgroup.normalizer (M₀ : Set G)) →* DihedralGroup 4,
      Function.Surjective f ∧
        f.ker = (baum S).subgroupOf (T ⊓ Subgroup.normalizer (M₀ : Set G)) := by
  obtain ⟨e⟩ := exists_mulEquiv_dihedral (m.card_range_rho C F hT hne)
  refine ⟨e.symm.toMonoidHom.comp (m.rho C F).rangeRestrict, ?_, ?_⟩
  · exact e.symm.surjective.comp (m.rho C F).rangeRestrict_surjective
  · ext γ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show e.symm ((m.rho C F).rangeRestrict γ) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← m.rho_eq_one_iff C F γ]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h

theorem card_normalizer_pair
    (F : GFour C x) (hT : IsPGroup 2 T) (hne : M₀ ≠ T) {i : Fin 4}
    (hi : i ≠ 0) :
    Nat.card S ≤ Nat.card ↥(T ⊓ Subgroup.normalizer ((F.A4 i ⊔ pCoreOf 2 H : Subgroup G) :
      Set G)) := by
  obtain ⟨g, hgP, hg1, hg⟩ := exists_pair_stabilizer (m.card_range_rho C F hT hne) hi.symm
  obtain ⟨γ, rfl⟩ := hgP
  have hγB : (γ : G) ∉ baum S := fun h => hg1 ((m.rho_eq_one_iff C F γ).2 h)
  have hγN : (γ : G) ∈ Subgroup.normalizer ((F.A4 i ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    have hQ0 : F.A4 0 = pCoreOf 2 H := rfl
    have key : conjSubgroup (F.A4 i ⊔ F.A4 0) (γ : G)⁻¹ = F.A4 i ⊔ F.A4 0 := by
      rw [C5.conjSubgroup_sup, ← m.rho_apply C F γ i, ← m.rho_apply C F γ 0]
      rcases hg with ⟨h0, hi'⟩ | ⟨h0, hi'⟩
      · rw [h0, hi']
      · rw [h0, hi', sup_comm]
    rw [hQ0] at key
    have := conjSubgroup_eq_iff_mem_normalizer.1 key
    have := (Subgroup.normalizer _).inv_mem this
    rwa [inv_inv] at this
  set N := T ⊓ Subgroup.normalizer ((F.A4 i ⊔ pCoreOf 2 H : Subgroup G) : Set G) with hN
  have hBN : baum S ≤ N := by
    refine le_inf ((inf_le_left : baum S ≤ S).trans (m.hSM.trans m.hMT)) fun b hb => ?_
    exact mem_normalizer_sup_of (m.B_le_normalizer_A4 C F i hb) (m.B_le_normalizer_A4 C F 0 hb)
  have hγN' : (γ : G) ∈ N := ⟨γ.2.1, hγN⟩
  have hlt : Nat.card (baum S) < Nat.card N := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hBN) fun h => ?_
    have := Subgroup.eq_of_le_of_card_ge hBN h.ge
    exact hγB (this ▸ hγN')
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBN
  have hBpos : 0 < Nat.card (baum S) := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hk'
    push Not at hk'
    interval_cases k
    · omega
    · omega
  have hS := m.card_S_eq C
  have h3 : Nat.card (baum S) * 2 ≤ Nat.card (baum S) * k := Nat.mul_le_mul_left _ hk2
  omega

end GMate

end CFSG.QuasithinUnique.AppD
