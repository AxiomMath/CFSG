module

public import CFSG.FeitThompson.Definitions.DadeData
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {A : Set G} {L : Subgroup G} {a b : G}

theorem mem_normalizer_iff_conjInv_image_eq {g : G} :
    g ∈ Subgroup.normalizer A ↔ (fun x => g⁻¹ * x * g) '' A = A := by
  rw [← Subgroup.inv_mem_iff (H := Subgroup.normalizer A),
    Subgroup.mem_normalizer_iff_conj_image_eq,
    Set.image_congr' (g := fun x => g⁻¹ * x * g) (fun x => by simp) (s := A)]

namespace IsTIWithNormalizer

theorem subset_coe (h : IsTIWithNormalizer A L) : A ⊆ (L : Set G) := by
  intro a ha
  refine h.not_disjoint_conj_image_iff_mem.1 fun hd => ?_
  exact Set.disjoint_left.1 hd ha ⟨a, ha, by simp⟩

theorem mem_of_conj_mem (h : IsTIWithNormalizer A L) (ha : a ∈ A) {g : G}
    (hg : g * a * g⁻¹ ∈ A) : g ∈ L := by
  refine h.not_disjoint_conj_image_iff_mem.1 fun hd => ?_
  exact Set.disjoint_left.1 hd hg ⟨a, ha, by simp⟩

theorem conj_mem (h : IsTIWithNormalizer A L) (ha : a ∈ A) {x : G} (hx : x ∈ L) :
    x * a * x⁻¹ ∈ A := by
  rw [← h.conj_image_eq_of_mem hx]
  exact ⟨a, ha, by simp⟩

theorem fusion (h : IsTIWithNormalizer A L) (ha : a ∈ A) (hb : b ∈ A) (hab : IsConj a b) :
    ∃ x ∈ L, x * a * x⁻¹ = b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hab
  exact ⟨c, h.mem_of_conj_mem ha (hc ▸ hb), hc⟩

theorem centralizer_le (h : IsTIWithNormalizer A L) (ha : a ∈ A) :
    Subgroup.centralizer ({a} : Set G) ≤ L := by
  intro x hx
  refine h.mem_of_conj_mem ha ?_
  have h1 : a * x = x * a := hx a rfl
  have h2 : x * a * x⁻¹ = a := by rw [← h1]; simp [mul_assoc]
  rwa [h2]

theorem inf_centralizer_eq (h : IsTIWithNormalizer A L) (ha : a ∈ A) :
    L ⊓ Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({a} : Set G) :=
  inf_eq_right.2 (h.centralizer_le ha)

theorem isDadeData [Finite G] (h : IsTIWithNormalizer A L) :
    IsDadeData L A (fun _ => ⊥) where
  subset_sdiff a ha := ⟨h.subset_coe ha, by simpa using fun hc : a = 1 => h.one_notMem (hc ▸ ha)⟩
  conj_mem := fun {_} ha {_} hx => h.conj_mem ha hx
  fusion := fun {_} ha {_} hb hab => h.fusion ha hb hab
  le_centralizer := fun {_} _ => bot_le
  normal_subgroupOf := fun {_} _ => by rw [Subgroup.bot_subgroupOf]; infer_instance
  inf_eq_bot := fun {_} _ => bot_inf_eq _
  mul_eq := fun {_} ha => by simp [h.inf_centralizer_eq ha]
  coprime_card := fun {_} _ {_} _ => by simp

end IsTIWithNormalizer

theorem isTIWithNormalizer_normalizer (hne : A.Nonempty) (h1 : (1 : G) ∉ A)
    (hTI : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ∨ (fun x => g⁻¹ * x * g) '' A ∩ A = ∅) :
    IsTIWithNormalizer A (Subgroup.normalizer A) where
  nonempty := hne
  one_notMem := h1
  normalizer_eq := rfl
  disjoint_conj_image g hg := by
    have key : (fun x => (g⁻¹)⁻¹ * x * g⁻¹) '' A = MulAut.conj g '' A :=
      Set.image_congr' (fun x => by simp)
    rcases hTI g⁻¹ with h | h
    · rw [key] at h
      exact absurd (Subgroup.mem_normalizer_iff_conj_image_eq.2 h) hg
    · rw [key] at h
      rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
      exact h

theorem isDadeData_normalizer_of_conj_image_eq_or_disjoint [Finite G] (hne : A.Nonempty)
    (h1 : (1 : G) ∉ A)
    (hTI : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ∨ (fun x => g⁻¹ * x * g) '' A ∩ A = ∅) :
    IsDadeData (Subgroup.normalizer A) A (fun _ => ⊥) :=
  (isTIWithNormalizer_normalizer hne h1 hTI).isDadeData

end CFSG.FeitThompson
