module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Indep

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Solvable

variable {G : Type*} [Group G]

theorem isSolvable_sup_of_le_normalizer {A B : Subgroup G} (hA : Group.IsSolvable ↥A)
    (hB : Group.IsSolvable ↥B) (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    Group.IsSolvable ↥(A ⊔ B) := by
  set Λ : Subgroup G := A ⊔ B
  have hAΛ : A ≤ Λ := le_sup_left
  have hBΛ : B ≤ Λ := le_sup_right
  have hUN : Λ ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hBA
  have hN' : (A.subgroupOf Λ).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAΛ).2 hUN
  have hmul : ∀ g ∈ Λ, ∃ u ∈ A, ∃ l ∈ B, g = u * l := by
    intro g hg
    have : g ∈ ((A : Set G) * (B : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hBA]
      exact hg
    obtain ⟨u, hu, l, hl, rfl⟩ := this
    exact ⟨u, hu, l, hl, rfl⟩
  let ι : ↥B →* ↥Λ ⧸ A.subgroupOf Λ :=
    (QuotientGroup.mk' (A.subgroupOf Λ)).comp (Subgroup.inclusion hBΛ)
  have hι : Function.Surjective ι := by
    intro s
    induction s using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨u, hu, l, hl, hg⟩ := hmul g.1 g.2
      refine ⟨⟨l, hl⟩, ?_⟩
      have hg' : g = ⟨u, hAΛ hu⟩ * ⟨l, hBΛ hl⟩ := Subtype.ext hg
      show QuotientGroup.mk (⟨l, hBΛ hl⟩ : ↥Λ) = QuotientGroup.mk g
      rw [hg', QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff (⟨u, hAΛ hu⟩ : ↥Λ)).2 (Subgroup.mem_subgroupOf.2 hu), one_mul]
  have h1 : Group.IsSolvable ↥(A.subgroupOf Λ) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hAΛ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAΛ).injective
  have h2 : Group.IsSolvable (↥Λ ⧸ A.subgroupOf Λ) := Group.isSolvable_of_surjective hι
  exact Group.isSolvable_of_ker_le_range (A.subgroupOf Λ).subtype
    (QuotientGroup.mk' (A.subgroupOf Λ))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem le_normalizer_of_le_centralizer {A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G)) : A ≤ Subgroup.normalizer (B : Set G) :=
  h.trans (Subgroup.centralizer_le_normalizer _)

theorem isSolvable_sup_iSup {ι : Type*} {V : Subgroup G} (hV : Group.IsSolvable ↥V)
    {L : ι → Subgroup G} (s : Finset ι) (hL : ∀ j ∈ s, Group.IsSolvable ↥(L j))
    (hN : ∀ j ∈ s, L j ≤ Subgroup.normalizer (V : Set G))
    (hc : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → L j ≤ Subgroup.centralizer (L k : Set G)) :
    Group.IsSolvable ↥(V ⊔ ⨆ j ∈ s, L j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (⨆ j ∈ (∅ : Finset ι), L j) = ⊥ := by simp
    rw [h0, sup_bot_eq]
    exact hV
  | insert a s ha ih =>
    have ih' := ih (fun j hj => hL j (Finset.mem_insert_of_mem hj))
      (fun j hj => hN j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk hjk => hc j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
    have hLa : L a ≤ Subgroup.normalizer ((V ⊔ ⨆ j ∈ s, L j : Subgroup G) : Set G) := by
      refine CFSG.LieType.Steinberg.le_normalizer_sup (hN a (Finset.mem_insert_self a s)) ?_
      refine le_normalizer_of_le_centralizer ?_
      rw [Subgroup.le_centralizer_iff]
      refine iSup₂_le fun j hj => ?_
      rw [← Subgroup.le_centralizer_iff]
      exact hc a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
        (fun e => ha (e ▸ hj))
    have key := isSolvable_sup_of_le_normalizer ih' (hL a (Finset.mem_insert_self a s)) hLa
    rw [Finset.iSup_insert, sup_left_comm, sup_comm (L a)]
    exact key

end Solvable

section Commutator

variable {G : Type*} [Group G]

theorem commutator_sup_sup_le {N A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (N : Set G))
    (hB : B ≤ Subgroup.normalizer (N : Set G)) (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    ⁅N ⊔ A, N ⊔ B⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N A hA] at hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N B hB] at hy
  obtain ⟨u, hu, a, ha, rfl⟩ := hx
  obtain ⟨v, hv, b, hb, rfl⟩ := hy
  have hab : a * b = b * a := (Subgroup.mem_centralizer_iff.1 (hAB ha) b hb).symm
  have hba : b * a⁻¹ = a⁻¹ * b := by
    calc b * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ := by group
      _ = a⁻¹ * (b * a) * a⁻¹ := by rw [hab]
      _ = a⁻¹ * b := by group
  have e : ⁅u * a, v * b⁆ = u * (a * v * a⁻¹) * (b * u⁻¹ * b⁻¹) * v⁻¹ := by
    calc ⁅u * a, v * b⁆ = u * a * v * (b * a⁻¹) * u⁻¹ * b⁻¹ * v⁻¹ := by
          rw [commutatorElement_def]; group
      _ = u * a * v * (a⁻¹ * b) * u⁻¹ * b⁻¹ * v⁻¹ := by rw [hba]
      _ = u * (a * v * a⁻¹) * (b * u⁻¹ * b⁻¹) * v⁻¹ := by group
  rw [e]
  exact N.mul_mem (N.mul_mem (N.mul_mem hu ((Subgroup.mem_normalizer_iff.1 (hA ha) v).1 hv))
    ((Subgroup.mem_normalizer_iff.1 (hB hb) u⁻¹).1 (N.inv_mem hu))) (N.inv_mem hv)

end Commutator

section PCore

variable {G : Type*} [Group G]

theorem le_pCoreOf_two {W Q : Subgroup G} (hQW : Q ≤ W)
    (hn : W ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 ↥Q) : Q ≤ pCoreOf 2 W := by
  have hnorm : (Q.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQW).2 hn
  have hp : IsPGroup 2 ↥(Q.subgroupOf W) := hQ.comap_subtype
  have hle : Q.subgroupOf W ≤ CFSG.pCore 2 ↥W := le_sSup ⟨hnorm, hp⟩
  intro x hx
  exact ⟨⟨x, hQW hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

end PCore

section PElement

variable {G : Type*} [Group G]

theorem le_pElementSubgroup_two_of_isPGroup {A B : Subgroup G} (hBA : B ≤ A)
    (hB : IsPGroup 2 ↥B) : B ≤ pElementSubgroup 2 A := fun x hx =>
  Subgroup.subset_closure ⟨hBA hx, (IsPGroup.iff_orderOf.1 hB) ⟨x, hx⟩ |>.imp fun k hk => by
    rw [← hk, ← Subgroup.orderOf_coe]⟩

end PElement

section Map

theorem isSolvable_map_equiv_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (X : Subgroup G) : Group.IsSolvable ↥(X.map e.toMonoidHom) ↔ Group.IsSolvable ↥X := by
  let φ := X.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨fun hs => Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective,
    fun hs => Group.isSolvable_of_surjective (f := φ.toMonoidHom) φ.surjective⟩

theorem commutator_map_eq_of_perfect {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {X : Subgroup G} (hX : commutator ↥X = ⊤) : ⁅X.map f, X.map f⁆ = X.map f := by
  have h1 : ⁅X, X⁆ = X := by
    rw [← Subgroup.map_subtype_commutator, hX, Subgroup.map_top, Subgroup.range_subtype]
  rw [← Subgroup.map_commutator, h1]

end Map

end CFSG.AGLEmbeddingD2.Tits.GN516.Indep
