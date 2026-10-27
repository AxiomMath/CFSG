module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5Tits
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dA8Trans
public import CFSG.GroupTheory.GL52.Simple
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dL5Proof

noncomputable def slEquivGL5 : SL5 ≃* GL (Fin 5) (ZMod 2) :=
  MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) →* _)
    CFSG.GroupTheory.GL52.bijective_toGL_G52

theorem card_SL5 : Nat.card SL5 = 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by
  rw [Nat.card_congr slEquivGL5.toEquiv]
  exact CFSG.GroupTheory.GL52.card_G52

theorem factorization_card_SL5_two : (Nat.card SL5).factorization 2 = 10 := by
  rw [card_SL5]
  have h1 : (2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 : ℕ) = 2 ^ 10 * 9765 := by norm_num
  rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ (2 ∣ 9765) by norm_num)]
  simp

theorem factorization_card_SL5_three : (Nat.card SL5).factorization 3 = 2 := by
  rw [card_SL5]
  have h1 : (2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 : ℕ) = 3 ^ 2 * 1085 * 2 ^ 10 := by norm_num
  rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 ∣ 1085) by norm_num),
    Nat.factorization_eq_zero_of_not_dvd (show ¬ (3 ∣ 2 ^ 10) by norm_num)]
  simp

theorem ub5_diag {g : SL5} (hg : g ∈ upperSub5) (i : Fin (4 + 1)) : (g : Mat5) i i = 1 := by
  rw [ub5_mem_iff] at hg
  have hut : (g : Mat5).IsUpperTriangular := fun ⦃i j⦄ h => hg i j h
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_of_isUpperTriangular hut, Fin.prod_univ_five] at hdet
  have key : ∀ u v w x y : ZMod 2, u * v * w * x * y = 1 →
      u = 1 ∧ v = 1 ∧ w = 1 ∧ x = 1 ∧ y = 1 := by decide
  obtain ⟨h0, h1, h2, h3, h4⟩ := key _ _ _ _ _ hdet
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

@[expose] def Mu5 (v : Fin 10 → ZMod 2) : Mat5 :=
  !![1, v 0, v 1, v 2, v 3;
     0, 1, v 4, v 5, v 6;
     0, 0, 1, v 7, v 8;
     0, 0, 0, 1, v 9;
     0, 0, 0, 0, 1]

theorem Mu5_upper (v : Fin 10 → ZMod 2) : (Mu5 v).IsUpperTriangular := by
  intro i j h
  have h' : j < i := h
  fin_cases i <;> fin_cases j <;> simp_all [Mu5]

theorem det_Mu5 (v : Fin 10 → ZMod 2) : (Mu5 v).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (Mu5_upper v), Fin.prod_univ_five]
  simp [Mu5]

@[expose] def mu5 (v : Fin 10 → ZMod 2) : upperSub5 :=
  ⟨⟨Mu5 v, det_Mu5 v⟩, fun i j h => Mu5_upper v h⟩

theorem mu5_injective : Function.Injective mu5 := by
  intro v w h
  have e : ∀ i j, Mu5 v i j = Mu5 w i j := fun i j => by
    have := congrArg (fun x : upperSub5 => ((x : SL5) : Mat5) i j) h
    simpa [mu5] using this
  funext k
  fin_cases k
  · simpa [Mu5] using e 0 1
  · simpa [Mu5] using e 0 2
  · simpa [Mu5] using e 0 3
  · simpa [Mu5] using e 0 4
  · simpa [Mu5] using e 1 2
  · simpa [Mu5] using e 1 3
  · simpa [Mu5] using e 1 4
  · simpa [Mu5] using e 2 3
  · simpa [Mu5] using e 2 4
  · simpa [Mu5] using e 3 4

theorem mu5_surjective : Function.Surjective mu5 := by
  rintro ⟨g, hg⟩
  have hd := ub5_diag hg
  have hb := (ub5_mem_iff.1 hg)
  refine ⟨![(g : Mat5) 0 1, (g : Mat5) 0 2, (g : Mat5) 0 3, (g : Mat5) 0 4, (g : Mat5) 1 2,
    (g : Mat5) 1 3, (g : Mat5) 1 4, (g : Mat5) 2 3, (g : Mat5) 2 4, (g : Mat5) 3 4], ?_⟩
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  show Mu5 _ i j = (g : Mat5) i j
  fin_cases i <;> fin_cases j <;>
    simp [Mu5, hd 0, hd 1, hd 2, hd 3, hd 4, hb 1 0 (by decide), hb 2 0 (by decide),
      hb 3 0 (by decide), hb 4 0 (by decide), hb 2 1 (by decide), hb 3 1 (by decide),
      hb 4 1 (by decide), hb 3 2 (by decide), hb 4 2 (by decide), hb 4 3 (by decide)]

theorem card_upperSub5 : Nat.card upperSub5 = 2 ^ 10 := by
  rw [← Nat.card_congr (Equiv.ofBijective mu5 ⟨mu5_injective, mu5_surjective⟩)]
  simp [Nat.card_eq_fintype_card]

open K21dA8Proof

theorem exists_conj_upperSub5 {U : Subgroup SL5} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) :
    ∃ c : SL5, U = upperSub5.map (MulAut.conj c).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcU : Nat.card U = 2 ^ (Nat.card SL5).factorization 2 := by
    have := hU.card_eq
    rwa [Subgroup.card_top] at this
  have hcB : Nat.card upperSub5 = 2 ^ (Nat.card SL5).factorization 2 := by
    rw [factorization_card_SL5_two]
    exact card_upperSub5
  let P : Sylow 2 SL5 := Sylow.ofCard U hcU
  let P' : Sylow 2 SL5 := Sylow.ofCard upperSub5 hcB
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq SL5 P' P
  refine ⟨c, ?_⟩
  have hsm : ((c • P' : Sylow 2 SL5) : Subgroup SL5) =
      (P' : Subgroup SL5).map (MulAut.conj c).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have h1 : (P : Subgroup SL5) = U := rfl
  have h2 : (P' : Subgroup SL5) = upperSub5 := rfl
  rw [← h1, ← hc, hsm, h2]

theorem factorization_three_of_card_nine {G F : Subgroup SL5} (hF : F ≤ G) (h9 : Nat.card F = 9) :
    (Nat.card G).factorization 3 = 2 := by
  have hdvd : Nat.card G ∣ Nat.card SL5 := Subgroup.card_subgroup_dvd_card G
  have hle : (Nat.card G).factorization 3 ≤ (Nat.card SL5).factorization 3 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd 3
  have hge : 2 ≤ (Nat.card G).factorization 3 := by
    have h9G : 3 ^ 2 ∣ Nat.card G := by
      have := Subgroup.card_dvd_of_le hF
      rw [h9] at this
      simpa using this
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1 h9G
  rw [factorization_card_SL5_three] at hle
  omega

theorem exists_conj_of_card_nine {G F F' : Subgroup SL5} (hF : F ≤ G) (hF' : F' ≤ G)
    (h9 : Nat.card F = 9) (h9' : Nat.card F' = 9) :
    ∃ d ∈ G, F = F'.map (MulAut.conj d).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ {K : Subgroup SL5}, K ≤ G → Nat.card K = 9 →
      Nat.card (K.subgroupOf G) = 3 ^ (Nat.card G).factorization 3 := by
    intro K hK h
    rw [factorization_three_of_card_nine hK h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv,
      h]
    norm_num
  let P : Sylow 3 G := Sylow.ofCard (F.subgroupOf G) (hc hF h9)
  let P' : Sylow 3 G := Sylow.ofCard (F'.subgroupOf G) (hc hF' h9')
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq G P' P
  refine ⟨d, d.2, ?_⟩
  have hsm : ((d • P' : Sylow 3 G) : Subgroup G) =
      (P' : Subgroup G).map (MulAut.conj d).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have h1 : (P : Subgroup G) = F.subgroupOf G := rfl
  have h2 : (P' : Subgroup G) = F'.subgroupOf G := rfl
  rw [← hd, hsm, h2] at h1
  have h3 := congrArg (Subgroup.map G.subtype) h1
  rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hF] at h3
  have h4 : (F'.subgroupOf G).map G.subtype = F' := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hF']
  have h5 : G.subtype.comp (MulAut.conj d).toMonoidHom =
      (MulAut.conj (d : SL5)).toMonoidHom.comp G.subtype := by
    ext x
    rfl
  calc F = Subgroup.map (G.subtype.comp (MulAut.conj d).toMonoidHom) (F'.subgroupOf G) := h3.symm
    _ = Subgroup.map ((MulAut.conj (d : SL5)).toMonoidHom.comp G.subtype) (F'.subgroupOf G) := by
      rw [h5]
    _ = Subgroup.map (MulAut.conj (d : SL5)).toMonoidHom ((F'.subgroupOf G).map G.subtype) := by
      rw [← Subgroup.map_map]
    _ = Subgroup.map (MulAut.conj (d : SL5)).toMonoidHom F' := by rw [h4]

theorem map_conj_mul {G : Type} [Group G] (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_inv_conj {G : Type} [Group G] (H : Subgroup G) (q : G) :
    (H.map (MulAut.conj q).toMonoidHom).map (MulAut.conj q⁻¹).toMonoidHom = H := by
  rw [← map_conj_mul, inv_mul_cancel]
  ext x
  simp

theorem map_conj_of_mem_normalizer {G : Type} [Group G] {H : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj n).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 hn

theorem concl_of_levi {G E0 E : Subgroup SL5}
    (hG : ∀ d ∈ G, ∃ q ∈ upperSub5, ∃ n ∈ Subgroup.normalizer (E0 : Set SL5), d = q * n)
    (hE0 : E0 ≤ G) (hE0c : Nat.card E0 = 9) (hE : E ≤ G) (hEc : Nat.card E = 9)
    (hc : K21dConcl upperSub5 E0) : K21dConcl upperSub5 E := by
  obtain ⟨d, hdG, hdE⟩ := exists_conj_of_card_nine hE hE0 hEc hE0c
  obtain ⟨q, hq, n, hn, hdqn⟩ := hG d hdG
  rw [hdqn, map_conj_mul, map_conj_of_mem_normalizer hn] at hdE
  have hU : upperSub5.map (MulAut.conj q⁻¹).toMonoidHom = upperSub5 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer (upperSub5.inv_mem hq))
  have hE' : E.map (MulAut.conj q⁻¹).toMonoidHom = E0 := by
    rw [hdE, map_conj_inv_conj]
  have := hc
  rw [← hU, ← hE'] at this
  exact K21dConcl.of_map (MulAut.conj q⁻¹) this

end K21dL5Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
