module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

open CFSG.Open

@[expose] def KerConcl {G : Type} [Group G] (E : Subgroup G) : Prop :=
  ∃ F ≤ E, Nat.card F = 9 ∧ ∃ H : Subgroup G,
    H ≤ Subgroup.centralizer (F : Set G) ∧
    CFSG.Open.IsSubnormal H (Subgroup.centralizer (F : Set G)) ∧
    CFSG.Open.IsQuasisimple ↥H ∧ 3 ∣ Nat.card (↥H ⧸ Subgroup.center ↥H)

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem map_center_equiv (φ : G ≃* G') :
    (Subgroup.center G).map φ.toMonoidHom = Subgroup.center G' := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨h, rfl⟩ := φ.surjective g
    have h2 := congrArg φ (hx h)
    simpa [map_mul] using h2
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    have h2 := congrArg φ.symm (hy (φ g))
    simpa [map_mul] using h2

theorem isSubnormal_map (φ : G ≃* G') {H K : Subgroup G}
    (h : CFSG.Open.IsSubnormal H K) :
    CFSG.Open.IsSubnormal (H.map φ.toMonoidHom) (K.map φ.toMonoidHom) := by
  induction h with
  | refl H => exact CFSG.Open.IsSubnormal.refl _
  | @step H M K hHM hnorm _ ih =>
    refine CFSG.Open.IsSubnormal.step (Subgroup.map_mono hHM) ?_ ih
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx, hxn⟩ := Subgroup.mem_map.mp hn
    obtain ⟨m, hm, hmg⟩ := Subgroup.mem_map.mp g.2
    have hxM : x ∈ M := hHM hx
    have h1 : (⟨m, hm⟩ : ↥M) * ⟨x, hxM⟩ * (⟨m, hm⟩ : ↥M)⁻¹ ∈ H.subgroupOf M :=
      hnorm.conj_mem ⟨x, hxM⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨m, hm⟩
    rw [Subgroup.mem_subgroupOf] at h1
    refine Subgroup.mem_map.mpr ⟨m * x * m⁻¹, by simpa using h1, ?_⟩
    have hmg' : φ m = (g : G') := hmg
    have hxn' : φ x = (n : G') := hxn
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      hmg', hxn']

theorem isQuasisimple_equiv {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hcomm, hsimp⟩ := hA
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.map_commutator (⊤ : Subgroup A) (⊤ : Subgroup A) φ.toMonoidHom
    rw [Subgroup.map_top_of_surjective _ φ.surjective] at h1
    have h2 : commutator B = (commutator A).map φ.toMonoidHom := by
      rw [commutator, commutator, h1]
    rw [h2, hcomm, Subgroup.map_top_of_surjective _ φ.surjective]
  · haveI := hsimp
    exact MulEquiv.isSimpleGroup
      (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) φ (map_center_equiv φ)).symm

theorem card_quotient_center_equiv {A B : Type} [Group A] [Group B] (φ : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) :=
  Nat.card_congr (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) φ
    (map_center_equiv φ)).toEquiv

theorem centralizer_map_equiv (φ : G ≃* G') (F : Subgroup G) :
    (Subgroup.centralizer (F : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((F.map φ.toMonoidHom : Subgroup G') : Set G') := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro s hs
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hs
    rw [← map_mul, ← map_mul, hx f hf]
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro f hf
    apply φ.injective
    have := hy (φ f) (Subgroup.mem_map.mpr ⟨f, hf, rfl⟩)
    simpa [map_mul] using this

theorem kerConcl_of_equiv (φ : G ≃* G') (E : Subgroup G)
    (h : KerConcl (E.map φ.toMonoidHom)) : KerConcl E := by
  obtain ⟨F', hF'E, hF'card, H', hH'C, hH'sub, hH'q, hH'dvd⟩ := h
  refine ⟨F'.map φ.symm.toMonoidHom, ?_, ?_, H'.map φ.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hF'E hy)
    have hyz : φ.symm y = z := by rw [← hzy]; simp
    rw [MulEquiv.coe_toMonoidHom, hyz]
    exact hz
  · rw [Subgroup.card_map_of_injective φ.symm.injective]
    exact hF'card
  · rw [← centralizer_map_equiv φ.symm F']
    exact Subgroup.map_mono hH'C
  · rw [← centralizer_map_equiv φ.symm F']
    exact isSubnormal_map φ.symm hH'sub
  · exact isQuasisimple_equiv (MulEquiv.subgroupMap φ.symm H') hH'q
  · have hc := card_quotient_center_equiv (MulEquiv.subgroupMap φ.symm H').symm
    exact (congrArg (fun n => 3 ∣ n) hc).mpr hH'dvd

end Transport

end CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

end
