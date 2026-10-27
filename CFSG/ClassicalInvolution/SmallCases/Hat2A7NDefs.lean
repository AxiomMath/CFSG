module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Induction

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

section Families

variable {F : Type} [Group F]

@[expose] def IsConjSubgroup (K L : Subgroup F) : Prop :=
  ∃ g : F, L = K.map (MulAut.conj g).toMonoidHom

theorem IsConjSubgroup.refl (K : Subgroup F) : IsConjSubgroup K K :=
  ⟨1, (map_conj_one K).symm⟩

theorem IsConjSubgroup.trans {K K' L : Subgroup F} (h₁ : IsConjSubgroup K K')
    (h₂ : IsConjSubgroup K' L) : IsConjSubgroup K L := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨h, rfl⟩ := h₂
  exact ⟨h * g, map_map_conj K g h⟩

theorem isConjSubgroup_map_conj (K : Subgroup F) (g : F) :
    IsConjSubgroup K (K.map (MulAut.conj g).toMonoidHom) := ⟨g, rfl⟩

@[expose] def IsCommProd (z x : F) : Prop :=
  ∃ S : Set F, S ⊆ classOf z ∧ (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) ∧ x ∈ Subgroup.closure S

theorem isCommProd_of_mem_classOf {z v : F} (hv : v ∈ classOf z) : IsCommProd z v :=
  ⟨{v}, Set.singleton_subset_iff.mpr hv, by rintro a rfl b rfl; rfl, Subgroup.subset_closure rfl⟩

theorem IsCommProd.congr {z x : F} (hx : x ∈ classOf z) {y : F} :
    IsCommProd x y ↔ IsCommProd z y := by
  rw [IsCommProd, IsCommProd, classOf_eq_of_mem hx]

@[expose] def IsTwinDiag (K : Subgroup F) (x : F) (L : Subgroup F) : Prop :=
  ∃ K' : Subgroup F, IsConjSubgroup K K' ∧
    ∃ h : (∀ k ∈ K', ∀ k' ∈ K', k * (x * k' * x⁻¹) = (x * k' * x⁻¹) * k),
      L = (diagHom K' x h).range

theorem IsTwinDiag.of_isConjSubgroup {K K' : Subgroup F} (h : IsConjSubgroup K K') {x : F}
    {L : Subgroup F} (hL : IsTwinDiag K' x L) : IsTwinDiag K x L := by
  obtain ⟨K'', h'', hc, rfl⟩ := hL
  exact ⟨K'', h.trans h'', hc, rfl⟩

end Families

section Narrowed

@[expose] def LocalOddCentral2A7N (G : Type) [Group G] (K : Subgroup G) (z : G) : Prop :=
  ∀ x : G, orderOf x = 2 → IsCommProd z x → Subgroup.centralizer ({x} : Set G) ≠ ⊤ →
    ∀ (L M : Subgroup G) (u v : G), (IsConjSubgroup K L ∨ IsTwinDiag K x L) →
      IsConjSubgroup K M →
      IsClassical2A7 (Subgroup.centralizer ({x} : Set G)) L u →
      IsClassical2A7 (Subgroup.centralizer ({x} : Set G)) M v →
      classicalInvolutionOddCore
          ↥(normalClosureIn2A7 (Subgroup.centralizer ({x} : Set G)) (L ⊔ M)) ≤
        Subgroup.center
          ↥(normalClosureIn2A7 (Subgroup.centralizer ({x} : Set G)) (L ⊔ M))

@[expose] def LocalOddCentralStep2A7N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassical2A7 ⊤ K z → CITBelow2A7 (Nat.card G) →
      (Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) →
        LocalOddCentral2A7N G K z) ∧
      (¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) →
        LocalOddCentral2A7 G)

theorem LocalOddCentral2A7N.of_full {G : Type} [Group G] (h : LocalOddCentral2A7 G)
    (K : Subgroup G) (z : G) : LocalOddCentral2A7N G K z :=
  fun x hx _ hne L M u v _ _ hL hM => h x hx hne L M u v hL hM

theorem localOddCentralStep2A7N_of_full (h : LocalOddCentralStep2A7) :
    LocalOddCentralStep2A7N :=
  fun G _ _ _ hnab K z hK hB =>
    ⟨fun _ => LocalOddCentral2A7N.of_full (h G hnab K z hK hB) K z, fun _ => h G hnab K z hK hB⟩

end Narrowed

section Tight

variable {F : Type} [Group F]

@[expose] def TightIH (K : Subgroup F) (z : F) : Prop :=
  ∀ x : F, orderOf x = 2 → IsCommProd z x → ∀ (L M : Subgroup F) (u v : F),
    (IsConjSubgroup K L ∨ IsTwinDiag K x L) → IsConjSubgroup K M →
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) L u →
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) M v → CommOrEq L M

@[expose] def TightP1 (K : Subgroup F) : Prop :=
  ∀ (L : Subgroup F) (u : F), IsConjSubgroup K L → IsClassical2A7 ⊤ L u →
    classicalInvolutionOddCore ↥L ≤ Subgroup.center ↥L

structure TightSettingN (F : Type) [Group F] (K : Subgroup F) (z : F) : Prop where
  tight : IsTight K z
  center_trivial : ∀ x : F, (∀ y : F, x * y = y * x) → x = 1
  IH : TightIH K z
  P1 : TightP1 K

theorem tightSettingN_of_tightSetting {K : Subgroup F} {z : F} (S : TightSetting F K z) :
    TightSettingN F K z :=
  ⟨S.tight, S.center_trivial,
    fun x hx _ L M u v _ _ hL hM => S.IH x hx
      (S.centralizer_ne_top (by rintro rfl; rw [orderOf_one] at hx; omega)) L M u v hL hM,
    fun L u _ hL => S.P1 L u hL⟩

end Tight

end CFSG.ClassicalInvolution.Hat2A7N
