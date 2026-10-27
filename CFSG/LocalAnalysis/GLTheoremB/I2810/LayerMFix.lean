module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM

variable {V : Type} [Group V] [Finite V]

theorem fixV'_mem_iff {X : Subgroup (MulAut V)} {v : V} : v ∈ fixV' X ↔ ∀ x ∈ X, x v = v :=
  Iff.rfl

theorem fix_index_conj_aux {s : ℕ} (g : Fin s → MulAut V) (E : Subgroup (MulAut V)) :
    (fixV' (⨆ i, E.map (MulAut.conj (g i)).toMonoidHom)).index ≤ (fixV' E).index ^ s := by
  have hb : ∀ i, (fixV' (E.map (MulAut.conj (g i)).toMonoidHom)).index = (fixV' E).index := by
    intro i
    have hset : fixV' (E.map (MulAut.conj (g i)).toMonoidHom) =
        (fixV' E).comap ((g i)⁻¹ : MulAut V).toMonoidHom := by
      ext v
      rw [Subgroup.mem_comap, fixV'_mem_iff, fixV'_mem_iff]
      constructor
      · intro h x hx
        have h1 : (MulAut.conj (g i) x) v = v := h _ (Subgroup.mem_map_of_mem _ hx)
        have h2 : (g i) (x ((g i)⁻¹ v)) = (g i) ((g i)⁻¹ v) := by
          rw [MulAut.apply_inv_self]
          exact h1
        exact (g i).injective h2
      · intro h y hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        have h3 : x ((g i)⁻¹ v) = (g i)⁻¹ v := h x hx
        show (g i) (x ((g i)⁻¹ v)) = v
        rw [h3, MulAut.apply_inv_self]
    have hsurj : Function.Surjective ((g i)⁻¹ : MulAut V).toMonoidHom :=
      fun y => ⟨(g i) y, MulAut.inv_apply_self V (g i) y⟩
    rw [hset]
    exact Subgroup.index_comap_of_surjective (fixV' E) hsurj
  have ha : (⨅ i, fixV' (E.map (MulAut.conj (g i)).toMonoidHom)) ≤
      fixV' (⨆ i, E.map (MulAut.conj (g i)).toMonoidHom) := by
    intro v hv
    refine fixV'_mem_iff.mpr fun x hx => ?_
    exact Subgroup.iSup_induction (C := fun y : MulAut V => y v = v)
      (fun i => E.map (MulAut.conj (g i)).toMonoidHom) hx
      (fun i y hy => (fixV'_mem_iff.mp (Subgroup.mem_iInf.mp hv i)) y hy) rfl
      (fun a b (ha' : a v = v) (hb' : b v = v) => by
        show a (b v) = v
        rw [hb', ha'])
  have h1 : (fixV' (⨆ i, E.map (MulAut.conj (g i)).toMonoidHom)).index ≤
      (⨅ i, fixV' (E.map (MulAut.conj (g i)).toMonoidHom)).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le ha)
  calc (fixV' (⨆ i, E.map (MulAut.conj (g i)).toMonoidHom)).index
        ≤ (⨅ i, fixV' (E.map (MulAut.conj (g i)).toMonoidHom)).index := h1
    _ ≤ ∏ i, (fixV' (E.map (MulAut.conj (g i)).toMonoidHom)).index :=
        Subgroup.index_iInf_le _
    _ = ∏ _i : Fin s, (fixV' E).index := Finset.prod_congr rfl fun i _ => hb i
    _ = (fixV' E).index ^ s := by simp

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM
