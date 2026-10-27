module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.LayerMPermRF
public import CFSG.LocalAnalysis.GLTheoremB.I2810.LayerMPermGen

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM

theorem map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (y x : G) :
    H.map (MulAut.conj (y * x)).toMonoidHom =
      (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_zpowers {G : Type*} [Group G] (g v : G) :
    (Subgroup.zpowers v).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g * v * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem perm_gen_nine_base_aux {V₄ Vv : Subgroup ↥(alternatingGroup (Fin 9))}
    (hV₄ : IsRootFour V₄) (hVv : Vv ≤ V₄) (hc : Nat.card ↥Vv = 2 ∨ Nat.card ↥Vv = 4) :
    ∃ (s : ℕ) (xs : Fin s → ↥(alternatingGroup (Fin 9))), Nat.card ↥Vv ^ s ≤ 2 ^ 6 ∧
      ⊤ ≤ ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom := by
  obtain ⟨W, a, hW, ha, ha1, ⟨y4, h4⟩, ⟨y3, h3⟩⟩ := gen_nine
  rcases hc with hc | hc
  · obtain ⟨v, hv, hv1, rfl⟩ := exists_zpowers_of_card_two hc
    obtain ⟨x, hx⟩ := rootFour_elem_conj (by norm_num) hV₄ hW (hVv hv) hv1 ha ha1
    refine ⟨4, fun i => y4 i * x, by rw [hc]; norm_num, ?_⟩
    refine h4.trans (le_of_eq (iSup_congr fun i => ?_))
    rw [map_conj_mul, map_conj_zpowers, map_conj_zpowers, map_conj_zpowers, hx]
  · have hVveq : Vv = V₄ := Subgroup.eq_of_le_of_card_ge hVv (by rw [hc, hV₄.1])
    subst hVveq
    obtain ⟨x, hx⟩ := rootFour_conj (by norm_num) hV₄ hW
    refine ⟨3, fun i => y3 i * x, by rw [hc]; norm_num, ?_⟩
    refine h3.trans (le_of_eq (iSup_congr fun i => ?_))
    rw [map_conj_mul, hx]

theorem perm_gen_seven_aux {Vv V₄ : Subgroup ↥(alternatingGroup (Fin 7))}
    (hV₄ : IsRootFour V₄) (hVv : Vv ≤ V₄) (hc : Nat.card ↥Vv = 2 ∨ Nat.card ↥Vv = 4) :
    ∃ (s : ℕ) (xs : Fin s → ↥(alternatingGroup (Fin 7))), Nat.card ↥Vv ^ s ≤ 16 ∧
      (Nat.card ↥Vv = 2 → Nat.card ↥Vv ^ s ≤ 8) ∧
        ⊤ ≤ ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom := by
  obtain ⟨W, a, hW, ha, ha1, ⟨y3, h3⟩, ⟨y2, h2⟩⟩ := gen_seven
  rcases hc with hc | hc
  · obtain ⟨v, hv, hv1, rfl⟩ := exists_zpowers_of_card_two hc
    obtain ⟨x, hx⟩ := rootFour_elem_conj (by norm_num) hV₄ hW (hVv hv) hv1 ha ha1
    refine ⟨3, fun i => y3 i * x, by rw [hc]; norm_num, fun _ => by rw [hc]; norm_num, ?_⟩
    refine h3.trans (le_of_eq (iSup_congr fun i => ?_))
    rw [map_conj_mul, map_conj_zpowers, map_conj_zpowers, map_conj_zpowers, hx]
  · have hVveq : Vv = V₄ := Subgroup.eq_of_le_of_card_ge hVv (by rw [hc, hV₄.1])
    subst hVveq
    obtain ⟨x, hx⟩ := rootFour_conj (by norm_num) hV₄ hW
    refine ⟨2, fun i => y2 i * x, by rw [hc]; norm_num, fun h => by omega, ?_⟩
    refine h2.trans (le_of_eq (iSup_congr fun i => ?_))
    rw [map_conj_mul, hx]

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM
