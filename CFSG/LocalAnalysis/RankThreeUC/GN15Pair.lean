module

public import CFSG.Quasithin.Background.C118WeakPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem c118Univ_sharpen {G : Type*} [Group G] {B C₁ C₂ : Subgroup G}
    (h2 : (C₂.subgroupOf B).Characteristic) (h : C118Univ B C₁ C₂) :
    C118Univ B
      (((⨆ σ : MulAut ↥B, (C₁.subgroupOf B).map σ.toMonoidHom : Subgroup ↥B)).map B.subtype) C₂ := by
  intro Ω _ _ H ι hι hcl
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2', h3⟩ := hcon
  have key : ∀ σ : MulAut ↥B, ((C₁.subgroupOf B).map σ.toMonoidHom).map ι ≤ centerOf H := by
    intro σ
    have hinj : Function.Injective (ι.comp σ.toMonoidHom) := hι.comp σ.injective
    have hrange : (ι.comp σ.toMonoidHom).range = ι.range := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨σ y, rfl⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨z, rfl⟩ := σ.surjective y
        exact ⟨z, rfl⟩
    have := h Ω H (ι.comp σ.toMonoidHom) hinj (by rwa [hrange])
    rcases this with a | b | c
    · rw [Subgroup.map_map]
      exact a
    · exfalso
      apply h2'
      have hC : ((C₂.subgroupOf B).map σ.toMonoidHom) = C₂.subgroupOf B := by
        ext x
        rw [Subgroup.mem_map_equiv]
        have e := h2.fixed σ.symm
        constructor
        · intro hx
          have : x ∈ (C₂.subgroupOf B).comap σ.symm.toMonoidHom := hx
          rwa [e] at this
        · intro hx
          have : x ∈ (C₂.subgroupOf B).comap σ.symm.toMonoidHom := by rwa [e]
          exact this
      rw [← Subgroup.map_map, hC] at b
      exact b
    · exact absurd c h3
  apply h1
  have hsub : ((⨆ σ : MulAut ↥B, (C₁.subgroupOf B).map σ.toMonoidHom : Subgroup ↥B).map
      B.subtype).subgroupOf B = (⨆ σ : MulAut ↥B, (C₁.subgroupOf B).map σ.toMonoidHom) :=
    Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
  rw [hsub, Subgroup.map_iSup]
  exact iSup_le key

theorem isC118Pair_sharpen {G : Type*} [Group G] [Finite G] {T T₁ T₂ : Subgroup G}
    (hT : IsPGroup 2 T) (h : IsC118Pair T T₁ T₂) :
    ∃ C₁' C : Subgroup G, T₁ ≤ C₁' ∧ IsC118Pair T C₁' T₂ ∧ C₁' = centerOf T ⊓ C ∧ T₁ ≤ C ∧
      C ≤ baum T ∧ (C.subgroupOf (baum T)).Characteristic ∧ C ≤ omegaOneCenterOf (baum T) ∧
      C118Univ (baum T) C T₂ := by
  obtain ⟨h1ne, h1Z, -, h2ne, h2B, h2ch, hU⟩ := h
  have hbb : baum (baum T) = baum T := C1GN.baum_baum T
  have hBT : baum T ≤ T := C1GN.baum_le T
  have hT₁B : T₁ ≤ baum T := h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)
  have hT₁Ω : T₁ ≤ omegaOneCenterOf (baum T) :=
    h1Z.trans (omegaOneCenterOf_le_omegaOneCenterOf_of_baum_le le_rfl hBT)
  set S : Subgroup ↥(baum T) :=
    ⨆ σ : MulAut ↥(baum T), (T₁.subgroupOf (baum T)).map σ.toMonoidHom with hS
  set C : Subgroup G := S.map (baum T).subtype with hC
  have hCsub : C.subgroupOf (baum T) = S :=
    Subgroup.comap_map_eq_self_of_injective (baum T).subtype_injective _
  have hCB : C ≤ baum T := Subgroup.map_subtype_le _
  have hT₁C : T₁ ≤ C := by
    intro a ha
    refine ⟨⟨a, hT₁B ha⟩, ?_, rfl⟩
    exact Subgroup.mem_iSup_of_mem (MulEquiv.refl _) ⟨⟨a, hT₁B ha⟩, ha, rfl⟩
  have hCchar : (C.subgroupOf (baum T)).Characteristic := by
    rw [hCsub, hS, Subgroup.characteristic_iff_map_le]
    intro φ
    rw [Subgroup.map_iSup]
    refine iSup_le fun α => ?_
    rw [Subgroup.map_map]
    exact le_iSup (fun β : MulAut ↥(baum T) => (T₁.subgroupOf (baum T)).map β.toMonoidHom)
      (α.trans φ)
  have hCΩ : C ≤ omegaOneCenterOf (baum T) := by
    rintro _ ⟨x, hx, rfl⟩
    have hle : S ≤ (omegaOneCenterOf (baum T)).subgroupOf (baum T) := by
      refine iSup_le fun α => ?_
      have h1 := Subgroup.characteristic_iff_map_le.1
        (Setup.characteristic_omegaOneCenterOf (baum T)) α
      exact (Subgroup.map_mono (show T₁.subgroupOf (baum T) ≤
        (omegaOneCenterOf (baum T)).subgroupOf (baum T) from fun a ha => hT₁Ω ha)).trans h1
    exact hle hx
  have hCU : C118Univ (baum T) C T₂ := c118Univ_sharpen h2ch hU
  have hP' : IsC118Pair (baum T) C T₂ := by
    refine ⟨?_, hCΩ, hCchar, h2ne, ?_, ?_, ?_⟩
    · exact fun hbot => h1ne (le_bot_iff.mp (hbot ▸ hT₁C))
    · rw [hbb]; exact h2B
    · rw [hbb]; exact h2ch
    · rw [hbb]; exact hCU
  exact ⟨centerOf T ⊓ C, C,
    le_inf (h1Z.trans (C1GN.omegaOneCenterOf_le_centerOf T)) hT₁C,
    isC118Pair_of_baum hT hP', rfl, hT₁C, hCB, hCchar, hCΩ, hCU⟩

variable {X : Type} [Group X] [Finite X]

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
