module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25Bar1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux8

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {Y : Type} [Group Y]

@[expose] def NormalPrime (X N : Subgroup Y) : Prop :=
  N ≤ X ∧ (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) ∧ Nat.Coprime 3 (Nat.card N)

@[expose] def NormalSimple (X L : Subgroup Y) : Prop :=
  L ≤ X ∧ (∀ x ∈ X, ∀ n ∈ L, x * n * x⁻¹ ∈ L) ∧ IsSimpleGroup ↥L ∧
    (∃ a b : ↥L, a * b ≠ b * a) ∧ 3 ∣ Nat.card L

@[expose] def IsPiece (X K : Subgroup Y) : Prop := NormalPrime X K ∨ NormalSimple X K

@[expose] def goodGamma (A : Subgroup (MulAut Y)) : Subgroup Y :=
  ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S) (K : Subgroup Y)
    (_ : IsPiece (c25Fix S) K), K

theorem le_glaPPrimeCoreOf_of_normalPrime {X N : Subgroup Y} (h : NormalPrime X N) :
    N ≤ GLAPPrimeCoreOf 3 X := by
  obtain ⟨hNX, hnorm, hcop⟩ := h
  have hnormal : (N.subgroupOf X).Normal := by
    refine ⟨fun m hm g => ?_⟩
    have := hnorm g g.2 m (Subgroup.mem_subgroupOf.1 hm)
    exact Subgroup.mem_subgroupOf.2 this
  have hcard : Nat.card (N.subgroupOf X) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
  have hle : N.subgroupOf X ≤ GLAPPrimeCore 3 ↥X :=
    le_sSup ⟨hnormal, by rw [hcard]; exact hcop⟩
  intro n hn
  exact ⟨⟨n, hNX hn⟩, hle (Subgroup.mem_subgroupOf.2 hn), rfl⟩

theorem le_glaPLayer_of_normalSimple [Finite Y] {X L : Subgroup Y} (h : NormalSimple X L) :
    L ≤ GLAPLayer 3 X := by
  obtain ⟨hLX, hnorm, hsimple, hnab, hdvd⟩ := h
  have hnormal : (L.subgroupOf X).Normal := by
    refine ⟨fun m hm g => ?_⟩
    have := hnorm g g.2 m (Subgroup.mem_subgroupOf.1 hm)
    exact Subgroup.mem_subgroupOf.2 this
  have hsn : IsSubnormal L X :=
    IsSubnormal.step hLX hnormal (IsSubnormal.refl X)
  exact le_sSup (glaPComponent_of_simple Nat.prime_three hLX hsn hsimple hnab hdvd)

theorem le_goodGamma {A S : Subgroup (MulAut Y)} (hSA : S ≤ A) (hcard : Nat.card A ≤ 3 * Nat.card S)
    {K : Subgroup Y} (hK : IsPiece (c25Fix S) K) : K ≤ goodGamma A :=
  le_iSup₂_of_le S ⟨hSA, hcard⟩ (le_iSup₂_of_le K hK le_rfl)

theorem c25Fix_map {Y' : Type} [Group Y'] (φ : Y ≃* Y') (S : Subgroup (MulAut Y)) :
    c25Fix (S.map (MulAut.congr φ).toMonoidHom) = (c25Fix S).map φ.toMonoidHom := by
  ext y
  simp only [mem_c25Fix, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    refine ⟨φ.symm y, fun α hα => ?_, φ.apply_symm_apply y⟩
    have := h (MulAut.congr φ α) ⟨α, hα, rfl⟩
    have h2 : (MulAut.congr φ α) y = φ (α (φ.symm y)) := by
      simp [MulAut.congr_apply]
    rw [h2] at this
    exact φ.injective (by rw [this, φ.apply_symm_apply])
  · rintro ⟨x, hx, rfl⟩ β ⟨α, hα, rfl⟩
    have h2 : (MulAut.congr φ α) (φ x) = φ (α x) := by
      simp [MulAut.congr_apply]
    rw [h2, hx α hα]

theorem isPiece_map {Y' : Type} [Group Y'] (φ : Y ≃* Y') {X K : Subgroup Y} (h : IsPiece X K) :
    IsPiece (X.map φ.toMonoidHom) (K.map φ.toMonoidHom) := by
  rcases h with ⟨hKX, hnorm, hcop⟩ | ⟨hLX, hnorm, hsimple, hnab, hdvd⟩
  · left
    refine ⟨Subgroup.map_mono hKX, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨n, hn, rfl⟩
      exact ⟨x * n * x⁻¹, hnorm x hx n hn, by simp⟩
    · rwa [Subgroup.card_map_of_injective φ.injective]
  · right
    have e : ↥K ≃* ↥(K.map φ.toMonoidHom) := (φ.subgroupMap K)
    refine ⟨Subgroup.map_mono hLX, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨n, hn, rfl⟩
      exact ⟨x * n * x⁻¹, hnorm x hx n hn, by simp⟩
    · exact (MulEquiv.isSimpleGroup_congr e).1 hsimple
    · obtain ⟨a, b, hab⟩ := hnab
      refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
      rw [map_mul, map_mul]; exact h
    · rwa [Subgroup.card_map_of_injective φ.injective]

theorem map_goodGamma_le {Y' : Type} [Group Y'] (φ : Y ≃* Y') (A : Subgroup (MulAut Y)) :
    (goodGamma A).map φ.toMonoidHom ≤ goodGamma (A.map (MulAut.congr φ).toMonoidHom) := by
  rw [goodGamma, Subgroup.map_iSup]
  refine iSup_le fun S => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hS => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun K => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hK => ?_
  have hS' : S.map (MulAut.congr φ).toMonoidHom ≤ A.map (MulAut.congr φ).toMonoidHom :=
    Subgroup.map_mono hS.1
  have hinj := (MulAut.congr φ).injective
  have hcard : Nat.card (A.map (MulAut.congr φ).toMonoidHom) ≤
      3 * Nat.card (S.map (MulAut.congr φ).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj]
    exact hS.2
  refine le_goodGamma hS' hcard ?_
  rw [c25Fix_map]
  exact isPiece_map φ hK

theorem top_le_goodGamma_map {Y' : Type} [Group Y'] (φ : Y ≃* Y') {A : Subgroup (MulAut Y)}
    (htop : ⊤ ≤ goodGamma A) : ⊤ ≤ goodGamma (A.map (MulAut.congr φ).toMonoidHom) := by
  have h1 := map_goodGamma_le φ A
  have h2 : (goodGamma A).map φ.toMonoidHom = ⊤ := by
    rw [eq_top_iff.2 htop]
    exact Subgroup.map_top_of_surjective _ φ.surjective
  rw [h2] at h1
  exact h1

theorem map_map_congr_symm {Y' : Type} [Group Y'] (φ : Y ≃* Y') (A : Subgroup (MulAut Y)) :
    (A.map (MulAut.congr φ).toMonoidHom).map (MulAut.congr φ.symm).toMonoidHom = A := by
  rw [Subgroup.map_map]
  ext α
  constructor
  · rintro ⟨β, hβ, h⟩
    have : ((MulAut.congr φ.symm).toMonoidHom.comp (MulAut.congr φ).toMonoidHom) β = β := by
      ext x
      simp [MulAut.congr_apply]
    rw [this] at h
    rwa [← h]
  · intro hα
    refine ⟨α, hα, ?_⟩
    ext x
    simp [MulAut.congr_apply]

theorem top_le_goodGamma_of_map {Y' : Type} [Group Y'] (φ : Y ≃* Y') {A : Subgroup (MulAut Y)}
    {A' : Subgroup (MulAut Y')} (h : A.map (MulAut.congr φ).toMonoidHom = A')
    (htop : ⊤ ≤ goodGamma A') : ⊤ ≤ goodGamma A := by
  have := top_le_goodGamma_map φ.symm htop
  rwa [← h, map_map_congr_symm] at this

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
