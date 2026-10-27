module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Adapters.WholeGroupLayer
public import CFSG.Goldschmidt.Setup
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.Open

theorem goldschmidtLayer_eq_layer (Y : Type*) [Group Y] : goldschmidtLayer Y = CFSG.layer Y :=
  CFSG.Adapters.goldschmidtLayer_eq_foundations Y

theorem goldschmidtLayer_map_mulEquiv {Y Z : Type*} [Group Y] [Group Z] (φ : Y ≃* Z) :
    (goldschmidtLayer Y).map φ.toMonoidHom = goldschmidtLayer Z := by
  rw [goldschmidtLayer_eq_layer, goldschmidtLayer_eq_layer]
  have hbij := (CFSG.LocalCores.component_isomorphism φ).2
  change MulEquiv.mapSubgroup φ (sSup {K : Subgroup Y | CFSG.IsComponent K}) = CFSG.layer Z
  rw [OrderIso.map_sSup, ← sSup_image]
  exact congrArg sSup hbij.image_eq

theorem goldschmidtSimpleType_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L') : goldschmidtSimpleType L := by
  unfold goldschmidtSimpleType at h ⊢
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ |
      ⟨p, f, hp, hodd, hf, h5, h8, ⟨e'⟩⟩ | ⟨k, hk, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hodd, hf, h5, h8, ⟨e.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, hk, (Nat.card_congr e.toEquiv).trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩))))

theorem goldschmidt_core (h : CFSG.Goldschmidt.TopStatement) (Y : Type) [Group Y] [Finite Y]
    (S : Sylow 2 Y) (A : Subgroup Y) (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hcl : fusionStronglyClosed (A : Set Y) (S : Subgroup Y))
    (htop : Subgroup.normalClosure (A : Set Y) = ⊤) (hO : goldschmidtOddCore Y = ⊥) :
    CFSG.Open.pCore 2 Y ⊔ goldschmidtLayer Y = ⊤ ∧
    A = CFSG.Open.pCore 2 Y ⊔
      Subgroup.closure {t | t ∈ (S : Subgroup Y) ⊓ goldschmidtLayer Y ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K) := by
  obtain ⟨h1, h2, h3⟩ := h Y S A hAS hAab hcl htop
  set N := goldschmidtOddCore Y with hN
  set π := QuotientGroup.mk' N with hπ
  set φ : Y ⧸ N ≃* Y := (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    with hφ
  have hφπ : ∀ y : Y, φ (π y) = y := fun _ => rfl
  have hφπK : ∀ K : Subgroup Y, (K.map π).map φ.toMonoidHom = K := by
    intro K
    rw [Subgroup.map_map]
    convert Subgroup.map_id K
    ext y
    exact hφπ y
  have hpc : (CFSG.Open.pCore 2 (Y ⧸ N)).map φ.toMonoidHom = CFSG.Open.pCore 2 Y :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 φ
  have hlay : (goldschmidtLayer (Y ⧸ N)).map φ.toMonoidHom = goldschmidtLayer Y :=
    goldschmidtLayer_map_mulEquiv φ
  refine ⟨?_, ?_, ?_⟩
  ·
    have h1' := congrArg (Subgroup.map φ.toMonoidHom) h1
    rwa [Subgroup.map_sup, hpc, hlay, Subgroup.map_top_of_surjective _ φ.surjective] at h1'
  ·
    have h2' := congrArg (Subgroup.map φ.toMonoidHom) h2
    rw [hφπK, Subgroup.map_sup, hpc, MonoidHom.map_closure] at h2'
    rw [h2']
    congr 2
    ext t
    constructor
    · rintro ⟨s, ⟨⟨hs, hsE⟩, hs2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← hφπK S]
        exact Subgroup.mem_map_of_mem _ hs
      · rw [← hlay]
        exact Subgroup.mem_map_of_mem _ hsE
      · rw [← map_pow, hs2, map_one]
    · rintro ⟨⟨htS, htE⟩, ht2⟩
      refine ⟨φ.symm t, ⟨⟨?_, ?_⟩, ?_⟩, by simp⟩
      · rw [← hφπK S] at htS
        obtain ⟨s, hs, rfl⟩ := htS
        simpa using hs
      · rw [← hlay] at htE
        obtain ⟨s, hs, rfl⟩ := htE
        simpa using hs
      · rw [← map_pow, ht2, map_one]
  ·
    intro K hK
    have hK' : IsComponentOf (K.map φ.symm.toMonoidHom) ⊤ := by
      have := (CFSG.isComponent_iff_open K).mpr hK
      exact (CFSG.isComponent_iff_open _).mp (CFSG.LocalCores.isComponent_map_mulEquiv φ.symm this)
    have htype := h3 _ hK'
    set e : K ≃* K.map φ.symm.toMonoidHom :=
      K.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective with he
    exact goldschmidtSimpleType_of_mulEquiv
      (QuotientGroup.congr (Subgroup.center K) (Subgroup.center _) e
        (Subgroup.map_center_eq e)) htype

theorem goldschmidt_subgroup (h : CFSG.Goldschmidt.TopStatement) {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) {A L : Subgroup X} (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ x : X, x⁻¹ * a * x ∈ (S : Subgroup X) → x⁻¹ * a * x ∈ A)
    (hL : Subgroup.normalClosure (A : Set X) = L) (hO : CFSG.oddCore L = ⊥) :
    CFSG.Open.pCore 2 L ⊔ goldschmidtLayer L = ⊤ ∧
    A.subgroupOf L = CFSG.Open.pCore 2 L ⊔
      Subgroup.closure {t | t ∈ (S : Subgroup X).subgroupOf L ⊓ goldschmidtLayer L ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup L, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K) := by
  subst hL
  set M := Subgroup.normalClosure (A : Set X) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hMn.isSubnormal
  have hPeq : (P : Subgroup M) = (S : Subgroup X).subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hP, Subgroup.subgroupOf_map_subtype]
  have hAP : A.subgroupOf M ≤ (P : Subgroup M) := by
    rw [hPeq]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hAS (Subgroup.mem_subgroupOf.1 hx))
  have hcl' := CFSG.Goldschmidt.stronglyClosed_subgroupOf S hcl hAM P hAP
  have htop := CFSG.Goldschmidt.normalClosure_subgroupOf_eq_top S hAS hcl (M := M) rfl
  have hC := goldschmidt_core h M P (A.subgroupOf M) hAP
    (CFSG.Goldschmidt.isMulCommutative_subgroupOf hAab M) hcl' htop hO
  rw [hPeq] at hC
  exact hC

end CFSG.ComponentClassification.AschbacherTheorem3
