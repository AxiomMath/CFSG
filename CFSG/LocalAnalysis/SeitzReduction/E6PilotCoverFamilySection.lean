module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilyLevi
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Generic

variable {E Q : Type*} [Group E] [Group Q]

theorem commute_of_comp_commute_of_ker_le_center {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect A] {p : E →* Q} (hp : p.ker ≤ center E) (φ : A →* E) (ψ : B →* E)
    (h : ∀ a b, Commute (p (φ a)) (p (ψ b))) (a : A) (b : B) : Commute (φ a) (ψ b) := by
  have hc : ∀ x : A, ⁅φ x, ψ b⁆ ∈ center E := fun x => hp (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (h x b).eq)
  let δ : A →* center E :=
    { toFun := fun x => ⟨⁅φ x, ψ b⁆, hc x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [map_mul, Subgroup.coe_mul]
        have h1 := mem_center_iff.mp (hc y) (φ x)
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def] at *
        calc φ x * φ y * ψ b * (φ x * φ y)⁻¹ * (ψ b)⁻¹
            = φ x * (φ y * ψ b * (φ y)⁻¹ * (ψ b)⁻¹) * (ψ b * (φ x)⁻¹ * (ψ b)⁻¹) := by group
          _ = φ y * ψ b * (φ y)⁻¹ * (ψ b)⁻¹ * φ x * (ψ b * (φ x)⁻¹ * (ψ b)⁻¹) := by rw [h1]
          _ = φ x * ψ b * (φ x)⁻¹ * (ψ b)⁻¹ * (φ y * ψ b * (φ y)⁻¹ * (ψ b)⁻¹) := by
            have h2 := mem_center_iff.mp (hc y) (φ x * ψ b * (φ x)⁻¹ * (ψ b)⁻¹)
            rw [commutatorElement_def] at h2
            calc φ y * ψ b * (φ y)⁻¹ * (ψ b)⁻¹ * φ x * (ψ b * (φ x)⁻¹ * (ψ b)⁻¹)
                = φ y * ψ b * (φ y)⁻¹ * (ψ b)⁻¹ * (φ x * ψ b * (φ x)⁻¹ * (ψ b)⁻¹) := by group
              _ = _ := h2.symm }
  have hker : commutator A ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  have ha : δ a = 1 := hker (mem_top a)
  have ha' : ⁅φ a, ψ b⁆ = 1 := congrArg Subtype.val ha
  exact commutatorElement_eq_one_iff_mul_comm.1 ha'

theorem eq_range_of_perfect_of_map_eq {p : E →* Q} (hp : p.ker ≤ center E) {H : Subgroup Q}
    (s : H →* E) (hs : ∀ x, p (s x) = x) {M : Subgroup E} (hM : ⁅M, M⁆ = M) (hMH : M.map p = H) :
    M = s.range := by
  have hdec : ∀ m ∈ M, ∃ x : H, (s x)⁻¹ * m ∈ center E := by
    intro m hm
    have hpm : p m ∈ H := hMH ▸ mem_map_of_mem p hm
    refine ⟨⟨p m, hpm⟩, hp ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
  have hle : M ≤ s.range := by
    rw [← hM, commutator_le]
    intro a ha b hb
    obtain ⟨x, hx⟩ := hdec a ha
    obtain ⟨y, hy⟩ := hdec b hb
    have e1 : a = s x * ((s x)⁻¹ * a) := by group
    have e2 : b = s y * ((s y)⁻¹ * b) := by group
    rw [e1, e2, CFSG.SeitzReduction.E6Pilot.commutatorElement_mul_left_of_mem_center hx,
      CFSG.SeitzReduction.E6Pilot.commutatorElement_mul_right_of_mem_center hy,
      ← map_commutatorElement]
    exact ⟨_, rfl⟩
  refine le_antisymm hle ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨m, hm, hmx⟩ : (x : Q) ∈ M.map p := hMH ▸ x.2
  obtain ⟨y, hy⟩ := hle hm
  have hyx : y = x := by
    apply Subtype.ext
    rw [← hs y, hy, hmx]
  rw [← hyx, hy]
  exact hm

theorem injective_of_forall_comp_eq_self {p : E →* Q} {H : Subgroup Q} (s : H →* E)
    (hs : ∀ x, p (s x) = x) :
    Function.Injective s := fun x y hxy => Subtype.ext (by rw [← hs x, hxy, hs y])

theorem section_eq_of_perfect {p : E →* Q} (hp : p.ker ≤ center E) {H₁ H₂ P : Subgroup Q}
    (hP : ⁅P, P⁆ = P) (h₁ : P ≤ H₁) (h₂ : P ≤ H₂) (s₁ : H₁ →* E) (s₂ : H₂ →* E)
    (hs₁ : ∀ x, p (s₁ x) = x) (hs₂ : ∀ x, p (s₂ x) = x) (x : P) :
    s₁ (inclusion h₁ x) = s₂ (inclusion h₂ x) := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.2 hP
  have h := LinearPilot.eq_of_comp_eq_of_ker_le_center hp (φ := s₁.comp (inclusion h₁))
    (ψ := s₂.comp (inclusion h₂)) (fun y => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs₁, hs₂]
      rfl)
  exact DFunLike.congr_fun h x

end Generic

section Cover

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem commutator_pieceCore (J : Finset (Fin (Tag.rank .E6))) :
    ⁅pieceCore e J, pieceCore e J⁆ = pieceCore e J :=
  CFSG.Quasithin.perfectCore_perfect _

theorem FieldNeighbourCover.pieceCore_subgroupOf_eq_range {N : E6Neighbour}
    (h : FieldNeighbourCover σ e N) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2)
    (s : leviPiece K N J →* neighbourCore e N) (hs : ∀ x, h.p (s x) = x) :
    (pieceCore e J).subgroupOf (neighbourCore e N) = s.range := by
  refine eq_range_of_perfect_of_map_eq h.ker_le_center s hs ?_ (h.map_pieceCore hq hJ hJ2)
  apply map_injective (neighbourCore e N).subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left (pieceCore_le_neighbourCore e N hJ),
    commutator_pieceCore]

theorem FieldNeighbourCover.range_section_eq_pieceCore {N : E6Neighbour}
    (h : FieldNeighbourCover σ e N) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2)
    (s : leviPiece K N J →* neighbourCore e N) (hs : ∀ x, h.p (s x) = x) :
    ((neighbourCore e N).subtype.comp s).range = pieceCore e J ∧
      Function.Injective ((neighbourCore e N).subtype.comp s) := by
  refine ⟨?_, Subtype.val_injective.comp (injective_of_forall_comp_eq_self s hs)⟩
  rw [MonoidHom.range_comp, ← h.pieceCore_subgroupOf_eq_range hq hJ hJ2 s hs,
    subgroupOf_map_subtype, inf_of_le_left (pieceCore_le_neighbourCore e N hJ)]

theorem FieldNeighbourCover.eq_of_mem_pieceCore {N : E6Neighbour}
    (h : FieldNeighbourCover σ e N) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2)
    (s : leviPiece K N J →* neighbourCore e N) (hs : ∀ x, h.p (s x) = x)
    {a b : neighbourCore e N} (ha : (a : G) ∈ pieceCore e J) (hb : (b : G) ∈ pieceCore e J)
    (hab : h.p a = h.p b) : a = b := by
  have hrange := h.pieceCore_subgroupOf_eq_range hq hJ hJ2 s hs
  obtain ⟨x, rfl⟩ : a ∈ s.range := hrange ▸ (mem_subgroupOf.2 ha)
  obtain ⟨y, rfl⟩ : b ∈ s.range := hrange ▸ (mem_subgroupOf.2 hb)
  rw [hs, hs] at hab
  rw [Subtype.ext hab]

theorem symm_mem_pieceCore_of_mem_rootSpan (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .E6))} (hJ2 : J.card ≤ 2) {x : adjointGroup .E6 (fixSubfield σ)}
    (hx : (x : ModGL .E6 (fixSubfield σ)) ∈ rootSpan .E6 (fixSubfield σ) (amalgamRoots J)) :
    ((e.symm x : L) : G) ∈ pieceCore e J := by
  set H := rootSpan .E6 (fixSubfield σ) (amalgamRoots J) with hH
  have hlevi := perfectCore_inf_centralizer_leviTorus_inf hq hJ2
  have hHperf : ⁅H, H⁆ = H := by
    rw [hH, ← hlevi]
    exact CFSG.Quasithin.perfectCore_perfect _
  have hHle : H ≤ adjointGroup .E6 (fixSubfield σ) ⊓
      centralizer ((leviTorus (fixSubfield σ) J ⊓ adjointGroup .E6 (fixSubfield σ) :
        Subgroup (ModGL .E6 (fixSubfield σ))) :
        Set (ModGL .E6 (fixSubfield σ))) := by
    rw [hH, ← hlevi]
    exact CFSG.Quasithin.perfectCore_le _
  have hsub : ⁅H.subgroupOf (adjointGroup .E6 (fixSubfield σ)),
      H.subgroupOf (adjointGroup .E6 (fixSubfield σ))⁆ =
      H.subgroupOf (adjointGroup .E6 (fixSubfield σ)) := by
    apply map_injective (adjointGroup .E6 (fixSubfield σ)).subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left (hHle.trans inf_le_left), hHperf]
  have hperf : ⁅modelToG e H, modelToG e H⁆ = modelToG e H := by
    rw [modelToG, ← map_commutator, ← map_commutator, hsub]
  rw [pieceCore_eq_inf]
  exact F4Pilot.le_centralizerPerfectCore hperf
    (modelToG_le_centralizer e (hHle.trans inf_le_right))
    (symm_mem_modelToG e hx)

end Cover

end CFSG.SeitzReduction.E6Pilot
