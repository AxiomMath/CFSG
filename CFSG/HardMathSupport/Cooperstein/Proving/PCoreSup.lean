module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.HardMathSupport.Cooperstein.Transport

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] {X L S : Subgroup G}

theorem le_pCoreOf_of_normal_in {p : ℕ} {H A : Subgroup G} (hAH : A ≤ H)
    (hnorm : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A) (hA : IsPGroup p ↥A) :
    A ≤ CFSG.Open.pCoreOf p H := by
  set B : Subgroup ↥H := A.subgroupOf H with hBdef
  have hBn : B.Normal := by
    refine ⟨fun b hb h => ?_⟩
    rw [hBdef, Subgroup.mem_subgroupOf] at hb ⊢
    simpa using hnorm _ h.2 _ hb
  let ϕ : ↥B →* ↥A :=
    ((H.subtype.comp B.subtype).codRestrict A fun b => Subgroup.mem_subgroupOf.mp b.2)
  have hϕ : Function.Injective ϕ := by
    intro b c hbc
    have h2 : ((ϕ b : ↥A) : G) = ((ϕ c : ↥A) : G) := congrArg Subtype.val hbc
    exact Subtype.ext (Subtype.ext h2)
  have hBp : IsPGroup p ↥B := IsPGroup.of_injective hA ϕ hϕ
  have hBle : B ≤ CFSG.Open.pCore p ↥H :=
    le_sSup ⟨hBn, hBp⟩
  intro a ha
  exact Subgroup.mem_map.mpr ⟨⟨a, hAH ha⟩, hBle (Subgroup.mem_subgroupOf.mpr ha), rfl⟩

theorem mem_pCoreOf_iff {p : ℕ} {H : Subgroup G} {x : G} :
    x ∈ CFSG.Open.pCoreOf p H ↔ ∃ y ∈ CFSG.pCore p ↥H, (y : G) = x := by
  rw [CFSG.Open.pCoreOf,
    Subgroup.mem_map]
  rfl

theorem map_conj_pCoreOf {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    (CFSG.Open.pCoreOf p L).map (MulAut.conj g).toMonoidHom = CFSG.Open.pCoreOf p L := by
  have hL : L.map (MulAut.conj g).toMonoidHom = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr ?_, ?_⟩
      · have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
        rw [e]
        exact hx
      · show g * (g⁻¹ * x * g) * g⁻¹ = x
        group
  have h := CFSG.HardMathSupport.Cooperstein.Transport.pCoreOf_map_mulEquiv p (MulAut.conj g) L
  rw [hL] at h
  exact h.symm

theorem conj_mem_pCoreOf {p : ℕ} {L : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hx : x ∈ CFSG.Open.pCoreOf p L) :
    g * x * g⁻¹ ∈ CFSG.Open.pCoreOf p L := by
  have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  rw [map_conj_pCoreOf hg] at h
  exact h

theorem inf_pCoreOf_sup (hL : IsTwoPrimeComponent X L) (hSX : S ≤ X) (hS : IsPGroup 2 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) : L ⊓ pCoreOf 2 (L ⊔ S) = pCoreOf 2 L := by
  have hLnorm : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hTnorm : L ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le hLnorm hSL
  apply le_antisymm
  · intro x hx
    obtain ⟨hxL, hxT⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, hy, hyx⟩ := mem_pCoreOf_iff.mp hxT
    let ι : ↥L →* ↥(L ⊔ S) := Subgroup.inclusion le_sup_left
    have hιinj : Function.Injective ι := Subgroup.inclusion_injective _
    let M : Subgroup ↥L := (CFSG.pCore 2 ↥(L ⊔ S)).comap ι
    have hMn : M.Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥(L ⊔ S))).comap ι
    have hMp : IsPGroup 2 ↥M :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(L ⊔ S))).comap_of_injective ι hιinj
    have hM : M ≤ CFSG.pCore 2 ↥L := le_sSup ⟨hMn, hMp⟩
    have hz : (⟨x, hxL⟩ : ↥L) ∈ M := by
      show ι ⟨x, hxL⟩ ∈ CFSG.pCore 2 ↥(L ⊔ S)
      have : ι ⟨x, hxL⟩ = y := Subtype.ext hyx.symm
      rw [this]
      exact hy
    exact mem_pCoreOf_iff.mpr ⟨⟨x, hxL⟩, hM hz, rfl⟩
  · refine le_inf ?_ ?_
    · intro x hx
      obtain ⟨y, -, rfl⟩ := mem_pCoreOf_iff.mp hx
      exact y.2
    · have hAL : CFSG.Open.pCoreOf 2 L ≤ L := by
        intro x hx
        obtain ⟨y, -, rfl⟩ := mem_pCoreOf_iff.mp hx
        exact y.2
      have hAp : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L) := by
        unfold CFSG.Open.pCoreOf
        exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
      exact le_pCoreOf_of_normal_in (hAL.trans le_sup_left)
        (fun h hh a ha => conj_mem_pCoreOf (hTnorm hh) ha) hAp

end CFSG.HardMathSupport.Cooperstein.Proving

end
