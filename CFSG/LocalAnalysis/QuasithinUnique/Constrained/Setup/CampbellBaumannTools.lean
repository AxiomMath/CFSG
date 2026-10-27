module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2

section Iso

theorem pRank_set_subset {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p r : ℕ)
    (h : ∃ A : Subgroup X, IsElementaryAbelian p A ∧ Nat.card A = p ^ r) :
    ∃ A : Subgroup Y, IsElementaryAbelian p A ∧ Nat.card A = p ^ r := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A.map e.toMonoidHom, isElementaryAbelian_map hA e.toMonoidHom,
    by rw [Subgroup.card_map_of_injective e.injective, hc]⟩

theorem pRank_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    pRank p X = pRank p Y := CFSG.pRank_congr_of_mulEquiv e p

theorem mem_elemThompsonFamily_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ)
    {A : Subgroup X} (hA : A ∈ elemThompsonFamily X p) :
    A.map e.toMonoidHom ∈ elemThompsonFamily Y p :=
  ⟨isElementaryAbelian_map hA.1 e.toMonoidHom, by
    rw [Subgroup.card_map_of_injective e.injective, hA.2, pRank_eq_of_mulEquiv e p]⟩

theorem elemThompsonCenterTorsion_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] (e : X ≃* Y) (p : ℕ) [Fact p.Prime] :
    (elemThompsonCenterTorsion X p).map e.toMonoidHom = elemThompsonCenterTorsion Y p := by
  rw [elemThompsonCenterTorsion_eq_sInf, elemThompsonCenterTorsion_eq_sInf]
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_sInf, Subgroup.mem_sInf]
  constructor
  · intro h B hB
    obtain ⟨b, hb, hby⟩ := h _ (mem_elemThompsonFamily_map e.symm p hB)
    have : b = y := e.symm.injective hby
    rwa [← this]
  · intro h A hA
    obtain ⟨a, ha, hay⟩ := h _ (mem_elemThompsonFamily_map e p hA)
    have : e.symm y = a := by rw [← hay]; exact e.symm_apply_apply a
    rwa [this]

theorem elemCenterIn_map_subtype {S : Type*} [Group S] [Finite S] (p : ℕ) [Fact p.Prime]
    {A : Subgroup S} (B : Subgroup A) :
    (elemCenterIn p B).map A.subtype = elemCenterIn p (B.map A.subtype) := by
  unfold elemCenterIn
  rw [Subgroup.map_map]
  let e : B ≃* B.map A.subtype := B.equivMapOfInjective A.subtype A.subtype_injective
  have hcomp : A.subtype.comp B.subtype = (B.map A.subtype).subtype.comp e.toMonoidHom := by
    ext x; rfl
  rw [hcomp, ← Subgroup.map_map, elemThompsonCenterTorsion_map_mulEquiv e p]

theorem elemCenterIn_normal {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Q : Subgroup G) [Q.Normal] : (elemCenterIn p Q).Normal := by
  constructor
  rintro _ ⟨y, hy, rfl⟩ g
  have hchar := Subgroup.characteristic_iff_le_comap.mp
    (elemThompsonCenterTorsion_characteristic Q p) (MulAut.conjNormal (H := Q) g)
  have := Subgroup.mem_comap.mp (hchar hy)
  exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩

theorem elemCenterIn_isElementaryAbelian {S : Type*} [Group S] [Finite S] (p : ℕ) [Fact p.Prime]
    (Q : Subgroup S) : IsElementaryAbelian p (elemCenterIn p Q) := by
  obtain ⟨A₀, hA₀⟩ := elemThompsonFamily_nonempty Q p
  have hle : elemThompsonCenterTorsion Q p ≤ A₀ := fun x hx =>
    mem_elemThompsonCenterTorsion_iff_forall.mp hx A₀ hA₀
  exact isElementaryAbelian_map (isElementaryAbelian_of_le hle hA₀.1) Q.subtype

end Iso

section Index

variable {G : Type*} [Group G]

theorem relIndex_iInf_le_prod {ι : Type*} [DecidableEq ι] (N : Subgroup G) (D : ι → Subgroup G) :
    ∀ s : Finset ι, (⨅ i ∈ s, D i).relIndex N ≤ ∏ i ∈ s, (D i).relIndex N := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.prod_insert ha]
    exact (Subgroup.relIndex_inf_le).trans (Nat.mul_le_mul_left _ ih)

theorem centralizer_iSup_eq_iInf {ι : Type*} (X : ι → Subgroup G) :
    Subgroup.centralizer ((⨆ i, X i : Subgroup G) : Set G) =
      ⨅ i, Subgroup.centralizer (X i : Set G) := by
  ext x
  rw [Subgroup.mem_iInf]
  constructor
  · intro hx i
    exact Subgroup.centralizer_le (le_iSup X i) hx
  · intro hx
    refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
    have hle : (⨆ i, X i : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
      refine iSup_le fun i y hy => ?_
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp (hx i) y hy).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hj) x (Set.mem_singleton x)).symm

variable [Finite G]

theorem relIndex_ne_zero_of_finite (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [h, zero_mul] at h1
  have : 0 < Nat.card K := Nat.card_pos
  omega

theorem saturation_index (N : Subgroup G) {n : ℕ} (X : Fin n → Subgroup G) (L : Subgroup G)
    (hL : L ≤ ⨆ i, X i)
    (hge : ∏ i, (N ⊓ Subgroup.centralizer (X i : Set G)).relIndex N ≤
      (N ⊓ Subgroup.centralizer (L : Set G)).relIndex N) :
    N ⊓ Subgroup.centralizer (L : Set G) =
        N ⊓ Subgroup.centralizer ((⨆ i, X i : Subgroup G) : Set G) ∧
      (N ⊓ Subgroup.centralizer (L : Set G)).relIndex N =
        ∏ i, (N ⊓ Subgroup.centralizer (X i : Set G)).relIndex N := by
  classical
  set I : Subgroup G := ⨆ i, X i with hI
  have hCI : Subgroup.centralizer (I : Set G) ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.centralizer_le hL
  have hprod : (Subgroup.centralizer (I : Set G)).relIndex N ≤
      ∏ i, (Subgroup.centralizer (X i : Set G)).relIndex N := by
    rw [hI, centralizer_iSup_eq_iInf]
    have := relIndex_iInf_le_prod N (fun i => Subgroup.centralizer (X i : Set G)) Finset.univ
    simpa using this
  simp only [Subgroup.inf_relIndex_left] at hge ⊢
  have hnz : (Subgroup.centralizer (I : Set G)).relIndex N ≠ 0 := relIndex_ne_zero_of_finite _ _
  have hdvd : (Subgroup.centralizer (L : Set G)).relIndex N ∣
      (Subgroup.centralizer (I : Set G)).relIndex N := Subgroup.relIndex_dvd_of_le_left N hCI
  have hle1 : (Subgroup.centralizer (L : Set G)).relIndex N ≤
      (Subgroup.centralizer (I : Set G)).relIndex N := Nat.le_of_dvd (Nat.pos_of_ne_zero hnz) hdvd
  have heq1 : (Subgroup.centralizer (L : Set G)).relIndex N =
      (Subgroup.centralizer (I : Set G)).relIndex N := by omega
  have heq2 : (Subgroup.centralizer (L : Set G)).relIndex N =
      ∏ i, (Subgroup.centralizer (X i : Set G)).relIndex N := by omega
  refine ⟨?_, heq2⟩
  have hHK : N ⊓ Subgroup.centralizer (I : Set G) ≤ N ⊓ Subgroup.centralizer (L : Set G) :=
    inf_le_inf_left _ hCI
  have hmul := Subgroup.relIndex_mul_relIndex (N ⊓ Subgroup.centralizer (I : Set G))
    (N ⊓ Subgroup.centralizer (L : Set G)) N hHK inf_le_left
  simp only [Subgroup.inf_relIndex_left] at hmul
  rw [← heq1] at hmul
  have hpos : (Subgroup.centralizer (L : Set G)).relIndex N ≠ 0 := relIndex_ne_zero_of_finite _ _
  have h1 : (N ⊓ Subgroup.centralizer (I : Set G)).relIndex
      (N ⊓ Subgroup.centralizer (L : Set G)) = 1 := by
    have : (N ⊓ Subgroup.centralizer (I : Set G)).relIndex
        (N ⊓ Subgroup.centralizer (L : Set G)) * (Subgroup.centralizer (L : Set G)).relIndex N =
        1 * (Subgroup.centralizer (L : Set G)).relIndex N := by rw [one_mul]; exact hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) this
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hHK

theorem relIndex_inf_eq_relIndex_of_sup {W V A : Subgroup G} (hAW : A ≤ W) (hsup : A ⊔ V = W)
    (hc : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a) : (A ⊓ V).relIndex V = A.relIndex W := by
  have hprod := card_sup_mul_card_inf hc
  rw [hsup] at hprod
  have h1 := Subgroup.relIndex_mul_card (A ⊓ V) V
  rw [inf_assoc, inf_idem] at h1
  have h2 := Subgroup.relIndex_mul_card A W
  rw [inf_of_le_left hAW] at h2
  have hA : 0 < Nat.card A := Nat.card_pos
  have hAV : 0 < Nat.card (A ⊓ V : Subgroup G) := Nat.card_pos
  have key : A.relIndex W * (Nat.card A * Nat.card (A ⊓ V : Subgroup G)) =
      (A ⊓ V).relIndex V * (Nat.card A * Nat.card (A ⊓ V : Subgroup G)) := by
    calc A.relIndex W * (Nat.card A * Nat.card (A ⊓ V : Subgroup G))
        = (A.relIndex W * Nat.card A) * Nat.card (A ⊓ V : Subgroup G) := by ring
      _ = Nat.card W * Nat.card (A ⊓ V : Subgroup G) := by rw [h2]
      _ = Nat.card A * Nat.card V := hprod
      _ = ((A ⊓ V).relIndex V * Nat.card (A ⊓ V : Subgroup G)) * Nat.card A := by rw [h1]; ring
      _ = (A ⊓ V).relIndex V * (Nat.card A * Nat.card (A ⊓ V : Subgroup G)) := by ring
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hA hAV) key).symm

theorem relIndex_inf_le_of_le {V W : Subgroup G} (hVW : V ≤ W) (H : Subgroup G) :
    (V ⊓ H).relIndex V ≤ (W ⊓ H).relIndex W := by
  have h1 : (V ⊓ H).relIndex V = H.relIndex V := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right H V
  have h2 : (W ⊓ H).relIndex W = H.relIndex W := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right H W
  rw [h1, h2]
  exact Subgroup.relIndex_le_of_le_right hVW (relIndex_ne_zero_of_finite _ _)

end Index

end CFSG.QuasithinUnique.Setup.Campbell
