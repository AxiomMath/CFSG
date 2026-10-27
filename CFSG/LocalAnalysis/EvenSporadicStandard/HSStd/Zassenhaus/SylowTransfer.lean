module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open

theorem exists_conj_le_sylow {W : Type*} [Group W] [Finite W] {F T : Subgroup W}
    (hF : IsPGroup 2 F) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    ∃ g : W, ∀ y ∈ F, g⁻¹ * y * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₂, hP₂⟩ := hF.exists_le_sylow
  let P₁ : Sylow 2 W := hT.toSylow hTi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W P₁ P₂
  refine ⟨g, fun y hy => ?_⟩
  have h1 : y ∈ (P₂ : Subgroup W) := hP₂ hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : ∀ x : W, x ∈ (P₁ : Subgroup W) ↔ x ∈ T := fun x => hT.mem_toSylow hTi
  rw [h2] at h1
  simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using h1

theorem isElemAbelian_map {M M' : Type*} [Group M] [Group M'] (f : M →* M')
    (_hf : Function.Injective f) {E : Subgroup M} (h : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map f) := CFSG.Open.IsElemAbelian.map h _

theorem exists_conj_of_core {W : Type*} [Group W] [Finite W] {T : Subgroup W} {z : W}
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hzc : ∀ t ∈ T, z * t = t * z)
    {Adm : Subgroup W → Prop}
    (hAdm₁ : ∀ F, Adm F → IsPGroup 2 F ∧ F ≤ centralizer ({z} : Set W))
    (hAdm₂ : ∀ (F : Subgroup W) (c : W), c ∈ centralizer ({z} : Set W) → Adm F →
      Adm (F.map (MulAut.conj c).toMonoidHom))
    (hcore : ∀ F₁ F₂ : Subgroup W, F₁ ≤ T → F₂ ≤ T → Adm F₁ → Adm F₂ →
      ∃ t ∈ T, F₁.map (MulAut.conj t).toMonoidHom = F₂)
    {F₁ F₂ : Subgroup W} (h₁ : Adm F₁) (h₂ : Adm F₂) :
    ∃ c ∈ centralizer ({z} : Set W), F₁.map (MulAut.conj c).toMonoidHom = F₂ := by
  set C : Subgroup W := centralizer ({z} : Set W) with hC
  have hTC : T ≤ C := fun t ht => by
    rw [hC, mem_centralizer_singleton_iff]
    exact (hzc t ht).symm
  have hTi' : ¬ 2 ∣ (T.subgroupOf C).index := by
    intro hd
    apply hTi
    rw [← relIndex_mul_index hTC]
    exact Dvd.dvd.mul_right hd _
  have hT' : IsPGroup 2 (T.subgroupOf C) := hT.comap_subtype
  have key : ∀ F : Subgroup W, Adm F →
      ∃ c ∈ C, Adm (F.map (MulAut.conj c⁻¹).toMonoidHom) ∧
        F.map (MulAut.conj c⁻¹).toMonoidHom ≤ T := by
    intro F hF
    obtain ⟨hFp, hFC⟩ := hAdm₁ F hF
    obtain ⟨g, hg⟩ := exists_conj_le_sylow (F := F.subgroupOf C) hFp.comap_subtype hT' hTi'
    refine ⟨(g : W), g.2, ?_, ?_⟩
    · have := hAdm₂ F ((g : W)⁻¹) (C.inv_mem g.2) hF
      exact this
    · rintro _ ⟨x, hx, rfl⟩
      have := hg ⟨x, hFC hx⟩ hx
      have h' : (((g⁻¹ * ⟨x, hFC hx⟩ * g : C)) : W) ∈ T := this
      simpa [MulAut.conj_apply, mul_assoc] using h'
  obtain ⟨c₁, hc₁, hA₁, hle₁⟩ := key F₁ h₁
  obtain ⟨c₂, hc₂, hA₂, hle₂⟩ := key F₂ h₂
  obtain ⟨t, ht, hteq⟩ := hcore _ _ hle₁ hle₂ hA₁ hA₂
  refine ⟨c₂ * t * c₁⁻¹, ?_, ?_⟩
  · exact C.mul_mem (C.mul_mem hc₂ (hTC ht)) (C.inv_mem hc₁)
  · have e : ((MulAut.conj (c₂ * t * c₁⁻¹)).toMonoidHom : W →* W) =
        (MulAut.conj c₂).toMonoidHom.comp
          ((MulAut.conj t).toMonoidHom.comp (MulAut.conj c₁⁻¹).toMonoidHom) := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e, ← Subgroup.map_map, ← Subgroup.map_map, hteq, Subgroup.map_map]
    have e2 : ((MulAut.conj c₂).toMonoidHom : W →* W).comp (MulAut.conj c₂⁻¹).toMonoidHom =
        MonoidHom.id W := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e2, Subgroup.map_id]

theorem uniq_ambient_of_internal {G : Type*} [Group G] {L : Subgroup G} {z : G} (hzL : z ∈ L)
    (h : ∀ F₁ F₂ : Subgroup ↥L, IsElemAbelian 2 F₁ → IsElemAbelian 2 F₂ → Nat.card F₁ = 16 →
      Nat.card F₂ = 16 → (⟨z, hzL⟩ : ↥L) ∈ F₁ → (⟨z, hzL⟩ : ↥L) ∈ F₂ →
      (∀ e ∈ F₁, e ≠ 1 → ∃ a : ↥L, a * ⟨z, hzL⟩ * a⁻¹ = e) →
      (∀ e ∈ F₂, e ≠ 1 → ∃ a : ↥L, a * ⟨z, hzL⟩ * a⁻¹ = e) →
      ∃ c ∈ centralizer ({(⟨z, hzL⟩ : ↥L)} : Set ↥L),
        F₁.map (MulAut.conj c).toMonoidHom = F₂)
    {F₁ F₂ : Subgroup G} (h₁ : F₁ ≤ L) (h₂ : F₂ ≤ L) (hab₁ : IsElemAbelian 2 F₁)
    (hab₂ : IsElemAbelian 2 F₂) (hc₁ : Nat.card F₁ = 16) (hc₂ : Nat.card F₂ = 16)
    (hz₁ : z ∈ F₁) (hz₂ : z ∈ F₂)
    (hcj₁ : ∀ e ∈ F₁, e ≠ 1 → ∃ a ∈ L, a * z * a⁻¹ = e)
    (hcj₂ : ∀ e ∈ F₂, e ≠ 1 → ∃ a ∈ L, a * z * a⁻¹ = e) :
    ∃ c ∈ L ⊓ centralizer ({z} : Set G), F₁.map (MulAut.conj c : G →* G) = F₂ := by
  have ab : ∀ F : Subgroup G, F ≤ L → IsElemAbelian 2 F → IsElemAbelian 2 (F.subgroupOf L) := by
    intro F hFL hF
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have hc := congrArg (fun x : F => (x : G))
        (hF.1.is_comm.comm ⟨((a : L) : G), a.2⟩ ⟨((b : L) : G), b.2⟩)
      exact hc
    · intro x hx
      apply Subtype.ext
      have := hF.2 (x : G) hx
      simpa using this
  have card : ∀ F : Subgroup G, F ≤ L → Nat.card (F.subgroupOf L) = Nat.card F := fun F hFL =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFL).toEquiv
  have cj : ∀ F : Subgroup G, (∀ e ∈ F, e ≠ 1 → ∃ a ∈ L, a * z * a⁻¹ = e) →
      ∀ e ∈ F.subgroupOf L, e ≠ 1 → ∃ a : ↥L, a * ⟨z, hzL⟩ * a⁻¹ = e := by
    intro F hF e he he1
    obtain ⟨a, haL, ha⟩ := hF (e : G) he (fun h0 => he1 (Subtype.ext h0))
    exact ⟨⟨a, haL⟩, Subtype.ext ha⟩
  obtain ⟨c, hcC, hc⟩ := h (F₁.subgroupOf L) (F₂.subgroupOf L) (ab F₁ h₁ hab₁) (ab F₂ h₂ hab₂)
    ((card F₁ h₁).trans hc₁) ((card F₂ h₂).trans hc₂) hz₁ hz₂ (cj F₁ hcj₁) (cj F₂ hcj₂)
  refine ⟨(c : G), ⟨c.2, ?_⟩, ?_⟩
  · rw [mem_centralizer_singleton_iff] at hcC
    have h3 := congrArg Subtype.val hcC
    show (c : G) ∈ centralizer ({z} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact h3
  · ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hmem : (⟨x, h₁ hx⟩ : ↥L) ∈ F₁.subgroupOf L := hx
      have : (MulAut.conj c).toMonoidHom ⟨x, h₁ hx⟩ ∈ F₂.subgroupOf L := by
        rw [← hc]
        exact ⟨_, hmem, rfl⟩
      exact this
    · intro hw
      have hmem : (⟨w, h₂ hw⟩ : ↥L) ∈ F₂.subgroupOf L := hw
      rw [← hc] at hmem
      obtain ⟨y, hy, hyw⟩ := hmem
      refine ⟨(y : G), hy, ?_⟩
      have := congrArg Subtype.val hyw
      simpa [MulAut.conj_apply] using this

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
