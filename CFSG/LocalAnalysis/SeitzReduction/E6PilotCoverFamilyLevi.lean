module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotStep3Lift
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignField
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Generic

variable {E D : Type*} [Group E] [Group D]

theorem perfectCore_le_map_perfectCore_of_commutator_mem [Finite E] [Finite D] (p : E →* D)
    (hp : Function.Surjective p) {C₀ : Subgroup E} {F : Subgroup D}
    (h : ∀ a b : E, p a ∈ F → p b ∈ F → ⁅a, b⁆ ∈ C₀) :
    perfectCore F ≤ (perfectCore C₀).map p := by
  have hFF : ⁅F, F⁆ ≤ C₀.map p := by
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hp x
    obtain ⟨b, rfl⟩ := hp y
    exact ⟨⁅a, b⁆, h a b hx hy, map_commutatorElement p a b⟩
  have hP := CFSG.Quasithin.perfectCore_perfect F
  have hPF : perfectCore F ≤ ⁅F, F⁆ := by
    rw [← hP]
    exact commutator_mono (CFSG.Quasithin.perfectCore_le F) (CFSG.Quasithin.perfectCore_le F)
  rw [CFSG.Quasithin.map_perfectCore]
  exact CFSG.Quasithin.le_perfectCore_of_perfect (hPF.trans hFF) hP

end Generic

section Equivariance


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem FieldNeighbourCover.exists_map_conj [Finite K] [CharP K 2] {N : E6Neighbour}
    (h : FieldNeighbourCover σ e N) {d : adjointGroup .E6 (fixSubfield σ)}
    (hd : (d : ModGL .E6 (fixSubfield σ)) ∈ torusGroup .E6 (fixSubfield σ))
    (y : neighbourCore e N) :
    ∃ y' : neighbourCore e N,
      (y' : G) = ((e.symm d : L) : G) * y * ((e.symm d : L) : G)⁻¹ ∧
      (((h.p y' : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
        baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)) *
          (((h.p y : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) *
            (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)))⁻¹ := by
  obtain ⟨d₁, hd₁, d₂, ⟨x₂, hx₂, rfl⟩, he⟩ := exists_eq_mul_of_mem_torusGroup N hd
  simp only [Subgroup.coe_subtype] at he
  have hdd : d = ⟨d₁, N.torus_le_adjointGroup hd₁⟩ * x₂ := Subtype.ext he
  have hι₁ := baseChangeGL_mem_torus (fixSubfield σ).subtype N hd₁
  have hc₁ : ∀ z : N.levi K, Commute (baseChangeGL (fixSubfield σ).subtype d₁)
      ((z : adjointGroup .E6 K) : ModGL .E6 K) := by
    intro z
    have hz : ((z : adjointGroup .E6 K) : ModGL .E6 K) ∈
        (N.levi K).map (adjointGroup .E6 K).subtype := ⟨z, z.2, rfl⟩
    exact mem_centralizer_iff.1 (levi_le_centralizer_torus N hz) _ hι₁
  have hd₁G := symm_mem_modelToG e (x := ⟨d₁, N.torus_le_adjointGroup hd₁⟩) hd₁
  have hc₂ : ∀ z : neighbourCore e N, Commute
      ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G) (z : G) := by
    intro z
    exact mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ z.2) _ hd₁G
  obtain ⟨w, hw, hpw⟩ := h.fix ⟨x₂, hx₂⟩
  refine ⟨w * y * w⁻¹, ?_, ?_⟩
  · rw [hdd, map_mul, L.coe_mul, coe_mul, coe_mul, coe_inv, hw]
    have hc := hc₂ (w * y * w⁻¹)
    rw [coe_mul, coe_mul, coe_inv, hw] at hc
    calc ((e.symm x₂ : L) : G) * (y : G) * ((e.symm x₂ : L) : G)⁻¹
        = ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G) *
            (((e.symm x₂ : L) : G) * (y : G) * ((e.symm x₂ : L) : G)⁻¹) *
              ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G)⁻¹ := by
          rw [hc.eq, mul_inv_cancel_right]
      _ = _ := by group
  · have hpw' : (((h.p w : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
        baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .E6 (fixSubfield σ)) := by
      rw [hpw, coe_leviInclusion]
    have hpy : (((h.p (w * y * w⁻¹) : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
        baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .E6 (fixSubfield σ)) *
          (((h.p y : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) *
            (baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .E6 (fixSubfield σ)))⁻¹ := by
      rw [map_mul, map_mul, map_inv, coe_mul, coe_mul, coe_inv, coe_mul, coe_mul, coe_inv, hpw']
    have hc := hc₁ (h.p (w * y * w⁻¹))
    rw [hpy] at hc
    rw [he, map_mul (baseChangeGL (fixSubfield σ).subtype), hpy]
    calc baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .E6 (fixSubfield σ)) *
          (((h.p y : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) *
            (baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .E6 (fixSubfield σ)))⁻¹
        = baseChangeGL (fixSubfield σ).subtype d₁ *
            (baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .E6 (fixSubfield σ)) *
              (((h.p y : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) *
                (baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .E6 (fixSubfield σ)))⁻¹) *
              (baseChangeGL (fixSubfield σ).subtype d₁)⁻¹ := by
          rw [hc.eq, mul_inv_cancel_right]
      _ = _ := by group

end Equivariance

section Image


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem FieldNeighbourCover.map_pieceCore {N : E6Neighbour} (h : FieldNeighbourCover σ e N)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes)
    (hJ2 : J.card ≤ 2) :
    ((pieceCore e J).subgroupOf (neighbourCore e N)).map h.p = leviPiece K N J := by
  set E := neighbourCore e N with hE
  set T : Subgroup G := modelToG e (leviTorus (fixSubfield σ) J) with hT
  set C₀ : Subgroup E := (centralizer (T : Set G)).subgroupOf E with hC₀
  set j : N.levi K →* ModGL .E6 K := (adjointGroup .E6 K).subtype.comp (N.levi K).subtype
    with hj
  have hjinj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  set Tι : Subgroup (ModGL .E6 K) :=
    (leviTorus (fixSubfield σ) J ⊓ adjointGroup .E6 (fixSubfield σ)).map
      (baseChangeGL (fixSubfield σ).subtype) with hTι
  set C' : Subgroup (N.levi K) := (centralizer (Tι : Set (ModGL .E6 K))).comap j with hC'
  have hM : (pieceCore e J).subgroupOf E = perfectCore C₀ := by
    apply map_injective E.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, subgroupOf_map_subtype, hC₀, subgroupOf_map_subtype,
      inf_of_le_left (pieceCore_le_neighbourCore e N hJ), pieceCore_eq e N hJ, inf_comm]
  have hrange : (⊤ : Subgroup (N.levi K)).map j =
      (N.levi K).map (adjointGroup .E6 K).subtype := by
    rw [hj, ← map_map, ← MonoidHom.range_eq_map, range_subtype]
  have hmapC : C'.map j = (N.levi K).map (adjointGroup .E6 K).subtype ⊓
      centralizer (Tι : Set (ModGL .E6 K)) := by
    rw [hC', map_comap_eq, MonoidHom.range_eq_map, hrange, inf_comm]
  have hpiece : (leviPiece K N J).map j = rootSpan .E6 K (amalgamRoots J) := by
    have hle : rootSpan .E6 K (amalgamRoots J) ≤
        (N.levi K).map (adjointGroup .E6 K).subtype := by
      rw [← map_subtype_levi_adjDatumE6 J]
      exact map_mono (levi_le_neighbourLevi hJ)
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      obtain ⟨y, hy, rfl⟩ := hle hg
      exact ⟨⟨y, hy⟩, hg, rfl⟩
  have hP : perfectCore C' = leviPiece K N J := by
    apply map_injective hjinj
    rw [CFSG.Quasithin.map_perfectCore, hmapC, hpiece]
    exact perfectCore_levi_inf_centralizer_map_leviTorus_inf (fixSubfield σ).subtype hq hJ2 N hJ
  have htw : ∀ t ∈ T, ∃ d : adjointGroup .E6 (fixSubfield σ),
      (d : ModGL .E6 (fixSubfield σ)) ∈ torusGroup .E6 (fixSubfield σ) ∧
        baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)) ∈ Tι ∧
          ((e.symm d : L) : G) = t := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 ht
    exact ⟨x, leviTorus_inf_adjointGroup_le_torusGroup J ⟨hx, x.2⟩, ⟨_, ⟨hx, x.2⟩, rfl⟩, rfl⟩
  have hmove : ∀ (a : E) (t : G), t ∈ T → h.p a ∈ C' →
      ∃ a' : E, (a' : G) = t * a * t⁻¹ ∧ a⁻¹ * a' ∈ center E := by
    intro a t ht ha
    obtain ⟨d, hd, hdT, rfl⟩ := htw t ht
    obtain ⟨a', ha', hpa'⟩ := h.exists_map_conj hd a
    refine ⟨a', ha', h.ker_le_center ?_⟩
    have hc : baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)) *
        j (h.p a) = j (h.p a) * baseChangeGL (fixSubfield σ).subtype
          (d : ModGL .E6 (fixSubfield σ)) := (mem_centralizer_iff.1 ha) _ hdT
    have h1 : j (h.p a') = j (h.p a) := by
      change (((h.p a' : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) = _
      rw [hpa']
      change _ * j (h.p a) * _ = _
      rw [hc, mul_inv_cancel_right]
    rw [MonoidHom.mem_ker, map_mul, map_inv, hjinj h1, inv_mul_cancel]
  have hle : C₀.map h.p ≤ C' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hC', mem_comap, mem_centralizer_iff]
    rintro _ ⟨d₀, hd₀, rfl⟩
    set d : adjointGroup .E6 (fixSubfield σ) := ⟨d₀, hd₀.2⟩ with hd
    have hdT : ((e.symm d : L) : G) ∈ T := symm_mem_modelToG e hd₀.1
    obtain ⟨y', hy', hpy'⟩ := h.exists_map_conj (d := d)
      (leviTorus_inf_adjointGroup_le_torusGroup J hd₀) y
    have hcomm : ((e.symm d : L) : G) * (y : G) = (y : G) * ((e.symm d : L) : G) :=
      mem_centralizer_iff.1 (mem_subgroupOf.1 hy) _ hdT
    have hyy : y' = y := by
      apply Subtype.ext
      rw [hy', hcomm, mul_inv_cancel_right]
    rw [hyy] at hpy'
    change baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)) * j (h.p y) =
      j (h.p y) * baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ))
    change j (h.p y) = _ * j (h.p y) * _ at hpy'
    calc baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)) * j (h.p y)
        = baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)) * j (h.p y) *
            (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)))⁻¹ *
              baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)) := by group
      _ = _ := by rw [← hpy']
  have hge : ∀ a b : E, h.p a ∈ C' → h.p b ∈ C' → ⁅a, b⁆ ∈ C₀ := by
    intro a b ha hb
    rw [hC₀, mem_subgroupOf, mem_centralizer_iff]
    intro t ht
    obtain ⟨a', ha', hza⟩ := hmove a t ht ha
    obtain ⟨b', hb', hzb⟩ := hmove b t ht hb
    have hab : ⁅a', b'⁆ = ⁅a, b⁆ := by
      rw [show a' = a * (a⁻¹ * a') by group, show b' = b * (b⁻¹ * b') by group,
        commutatorElement_mul_left_of_mem_center hza,
        commutatorElement_mul_right_of_mem_center hzb]
    have h1 : t * ((⁅a, b⁆ : E) : G) * t⁻¹ = ((⁅a, b⁆ : E) : G) := by
      calc t * ((⁅a, b⁆ : E) : G) * t⁻¹ = ⁅t * (a : G) * t⁻¹, t * (b : G) * t⁻¹⁆ := by
            change t * ⁅(a : G), (b : G)⁆ * t⁻¹ = _
            simp only [commutatorElement_def]
            group
        _ = ((⁅a', b'⁆ : E) : G) := by rw [← ha', ← hb']; rfl
        _ = ((⁅a, b⁆ : E) : G) := by rw [hab]
    calc t * ((⁅a, b⁆ : E) : G) = t * ((⁅a, b⁆ : E) : G) * t⁻¹ * t := by group
      _ = ((⁅a, b⁆ : E) : G) * t := by rw [h1]
  rw [hM, ← hP]
  refine le_antisymm ?_ (perfectCore_le_map_perfectCore_of_commutator_mem h.p h.surjective hge)
  rw [CFSG.Quasithin.map_perfectCore]
  exact CFSG.Quasithin.perfectCore_mono hle

end Image

end CFSG.SeitzReduction.E6Pilot
