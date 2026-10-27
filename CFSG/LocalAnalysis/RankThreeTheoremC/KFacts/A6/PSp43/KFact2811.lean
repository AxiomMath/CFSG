module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.Gen2811
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsA6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.Transport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6

open CFSG.Open CFSG.GH74.Exceptional Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

namespace PSp43

theorem map_map_conj {G G' : Type*} [Group G] [Group G'] (f : G →* G') (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map f = (H.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

end PSp43

theorem kFact2811_holds : KFact2811 := by
  intro T _ _ L ⟨e⟩ z hzL hz2 hz1 hzc x hxL hx3 hxc A hA1 hA hAle
  set φ := modelHom e
  have hφ := modelHom_injective e
  set z₀ : L := ⟨z, hzL⟩
  set x₀ : L := ⟨x, hxL⟩
  have hAL : A ≤ L := hAle.trans ((pCoreOf_le_self 2 _).trans inf_le_left)
  set A₀ := A.comap L.subtype
  have hA₀ : A₀.map L.subtype = A := map_comap_subtype hAL
  set A' := A₀.map φ
  have hz2' : φ z₀ ^ 2 = 1 := by
    rw [← map_pow]
    have : z₀ ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    rw [this, map_one]
  have hz1' : φ z₀ ≠ 1 := fun h => hz1 (congrArg Subtype.val (hφ (h.trans (map_one φ).symm)))
  have hx3' : φ x₀ ^ 3 = 1 := by
    rw [← map_pow]
    have : x₀ ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hzc' := card_model_centralizer e z₀
  rw [hzc] at hzc'
  have hxc' := card_model_centralizer e x₀
  rw [hxc] at hxc'
  have hA₀le : A₀ ≤ pCoreOf 2 (centralizer ({z₀} : Set L)) := by
    rw [← Subgroup.map_le_map_iff_of_injective L.subtype_injective, hA₀,
      ← pCoreOf_map_of_injective' L.subtype_injective, map_subtype_centralizer]
    exact hAle
  have hA'le : A' ≤ pCoreOf 2 (P ⊓ centralizer ({φ z₀} : Set (Equiv.Perm (Fin 45)))) := by
    rw [← map_model_centralizer, pCoreOf_map_of_injective' hφ]
    exact Subgroup.map_mono hA₀le
  have hA'el : IsElemAbelian 2 A' := by
    refine ⟨isMulCommutative_iff.2 fun a b => Subtype.ext ?_, ?_⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      exact comm_of_map (fun u hu v hv => L.subtype_injective (by
        rw [map_mul, map_mul]; exact comm_of_isElemAbelian hA _ hu _ hv)) a ha b hb
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by simpa using hA.2 _ ha)
      rw [this, map_one]
  have hA'1 : A' ≠ ⊥ := by
    intro h
    apply hA1
    rw [← hA₀]
    have : A₀ = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h
    rw [this, Subgroup.map_bot]
  have key : ∀ p ∈ P, ∃ ℓ : L, φ ℓ = p := fun p hp => (range_modelHom e ▸ hp : p ∈ φ.range)
  have hconjT : ∀ ℓ : L, (A₀.map (MulAut.conj ℓ).toMonoidHom).map L.subtype =
      A.map (MulAut.conj (ℓ : T)).toMonoidHom := fun ℓ => by
    rw [PSp43.map_map_conj, hA₀]
    rfl
  constructor
  · intro hAz
    have hA'z : ¬ A' ≤ zpowers (φ z₀) := by
      intro h
      apply hAz
      rw [← MonoidHom.map_zpowers, Subgroup.map_le_map_iff_of_injective hφ] at h
      rw [← hA₀, show zpowers z = (zpowers z₀).map L.subtype by
        rw [MonoidHom.map_zpowers]; rfl]
      exact Subgroup.map_mono h
    obtain ⟨p₁, hp₁, p₂, hp₂, hmem⟩ :=
      gen_two_of_model (modelHom_mem e z₀) hz2' hz1' hzc' (modelHom_mem e x₀) hx3' hxc'
        hA'el hA'le hA'z
    obtain ⟨ℓ₁, rfl⟩ := key p₁ hp₁
    obtain ⟨ℓ₂, rfl⟩ := key p₂ hp₂
    refine ⟨ℓ₁, ℓ₁.2, ℓ₂, ℓ₂.2, ?_⟩
    rw [← PSp43.map_map_conj, ← PSp43.map_map_conj, ← Subgroup.map_sup] at hmem
    have hmem₀ := (Subgroup.mem_map_iff_mem hφ).1 hmem
    have := Subgroup.mem_map_of_mem L.subtype hmem₀
    rwa [Subgroup.map_sup, hconjT, hconjT] at this
  · obtain ⟨p, hp, hmem⟩ :=
      gen_four_of_model (modelHom_mem e z₀) hz2' hz1' hzc' (modelHom_mem e x₀) hx3' hxc'
        hA'1 hA'el hA'le
    choose ℓ hℓ using fun i => key (p i) (hp i)
    refine ⟨fun i => ℓ i, fun i => (ℓ i).2, ?_⟩
    have h1 : ∀ i, A'.map (MulAut.conj (p i)).toMonoidHom =
        (A₀.map (MulAut.conj (ℓ i)).toMonoidHom).map φ := fun i => by
      rw [← hℓ i, PSp43.map_map_conj]
    simp_rw [h1, ← Subgroup.map_iSup] at hmem
    have hmem₀ := (Subgroup.mem_map_iff_mem hφ).1 hmem
    have := Subgroup.mem_map_of_mem L.subtype hmem₀
    rw [Subgroup.map_iSup] at this
    simp only [hconjT] at this
    exact this

end CFSG.LocalAnalysis.RankThreeTheoremC.A6
