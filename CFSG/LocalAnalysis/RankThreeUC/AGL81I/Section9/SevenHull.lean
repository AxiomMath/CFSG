module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

theorem oPPrimeHull_top_eq_top_of_dichotomy {S : Type*} [Group S] [Finite S] {d : ℕ}
    (hd : d.Prime) (hdich : ∀ N : Subgroup S, N.Normal → N ≤ center S ∨ N = ⊤) {g : S}
    (hg : g ^ d = 1) (hgZ : g ∉ center S) : oPPrimeHull d (⊤ : Subgroup S) = ⊤ := by
  have : Fact d.Prime := ⟨hd⟩
  rcases hdich _ (oPPrimeHull_top_normal d) with h | h
  · exfalso
    have hg1 : g ≠ 1 := fun h1 => hgZ (h1 ▸ Subgroup.one_mem _)
    refine hgZ (h (Subgroup.subset_closure ⟨Subgroup.mem_top g, 1, ?_⟩))
    rw [pow_one]
    exact orderOf_eq_prime hg hg1
  · exact h

theorem oPPrimeHull_range_eq_of_top {S T : Type*} [Group S] [Finite S] [Group T] {d : ℕ}
    [Fact d.Prime] (f : S →* T) (h : oPPrimeHull d (⊤ : Subgroup S) = ⊤) :
    oPPrimeHull d f.range = f.range := by
  rw [MonoidHom.range_eq_map]
  exact S631.oPPrimeHull_map_eq f h

theorem oPPrimeHull_top_eq_top_of_mulEquiv {S T : Type*} [Group S] [Finite S] [Group T] {d : ℕ}
    [Fact d.Prime] (e : S ≃* T) (h : oPPrimeHull d (⊤ : Subgroup S) = ⊤) :
    oPPrimeHull d (⊤ : Subgroup T) = ⊤ := by
  have h1 := oPPrimeHull_range_eq_of_top e.toMonoidHom h
  rwa [MonoidHom.range_eq_top_of_surjective _ e.surjective] at h1

theorem le_oPPrimeHull_sup_of_hom {G Γ : Type*} [Group G] [Finite G] [Group Γ] {d : ℕ}
    [Fact d.Prime] {A N : Subgroup G} (φ : ↥A →* Γ) (hker : ∀ a : ↥A, φ a = 1 → (a : G) ∈ N)
    (hgen : φ.range ≤ oPPrimeHull d φ.range) : A ≤ oPPrimeHull d A ⊔ N := by
  intro a ha
  have h1 : φ.range ≤ (oPPrimeHull d (⊤ : Subgroup ↥A)).map φ := by
    rw [S631.map_oPPrimeHull, ← MonoidHom.range_eq_map]
    exact hgen
  obtain ⟨b, hb, hba⟩ := h1 ⟨⟨a, ha⟩, rfl⟩
  have hb' : (b : G) ∈ oPPrimeHull d A := by
    have h2 := S631.map_oPPrimeHull (p := d) A.subtype ⊤
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    rw [← h2]
    exact ⟨b, hb, rfl⟩
  have hN : ((b⁻¹ * ⟨a, ha⟩ : ↥A) : G) ∈ N :=
    hker _ (by rw [map_mul, map_inv, hba, inv_mul_cancel])
  have hab : a = (b : G) * ((b⁻¹ * ⟨a, ha⟩ : ↥A) : G) := by simp
  rw [hab]
  exact Subgroup.mul_mem_sup hb' hN

theorem oPPrimeHull_normal {Y : Type*} [Group Y] (d : ℕ) {X : Subgroup Y} (hX : X.Normal) :
    (oPPrimeHull d X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h : (oPPrimeHull d X).map (MulAut.conj g).toMonoidHom ≤ oPPrimeHull d X := by
    rw [oPPrimeHull, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hx, k, hk⟩, rfl⟩
    refine ⟨hX.conj_mem x hx g, k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  exact h ⟨n, hn, rfl⟩

theorem oPPrimeHull_subgroupOf_normal {G : Type*} [Group G] (d : ℕ) {H K : Subgroup G}
    (hKH : K ≤ H) (hK : (K.subgroupOf H).Normal) :
    ((oPPrimeHull d K).subgroupOf H).Normal := by
  have hJK : oPPrimeHull d K ≤ K := (Subgroup.closure_le _).mpr fun x hx => hx.1
  rw [Subgroup.normal_subgroupOf_iff hKH] at hK
  rw [Subgroup.normal_subgroupOf_iff (hJK.trans hKH)]
  intro x c hx hc
  have h : (oPPrimeHull d K).map (MulAut.conj c).toMonoidHom ≤ oPPrimeHull d K := by
    rw [oPPrimeHull, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, ⟨hy, j, hj⟩, rfl⟩
    refine ⟨hK y c hy hc, j, ?_⟩
    rw [← hj]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
  exact h ⟨x, hx, rfl⟩

theorem map_le_pCore_of_isPGroup {Y : Type*} [Group Y] {p : ℕ} {X : Subgroup Y} (hX : X.Normal)
    {T : Subgroup ↥X} (hT : T.Normal) (hTp : IsPGroup p ↥T) :
    T.map X.subtype ≤ CFSG.pCore p Y := by
  have := hX
  have h1 : T ≤ CFSG.pCore p ↥X := le_sSup ⟨hT, hTp⟩
  exact (Subgroup.map_mono h1).trans
    (le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, CFSG.pCore_isPGroup.map _⟩)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
