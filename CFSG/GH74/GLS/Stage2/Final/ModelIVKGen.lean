module

public import CFSG.GH74.GLS.Stage2.Final.ModelIVKBase
public import CFSG.GH74.GLS.Stage2.Final.ModelClsFam

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {F : Type} [Field F]

theorem tP_not_mem_normalizer [Finite F] {M : ModelData F} (hG : GoodModel M) :
    tP M ∉ Subgroup.normalizer (K1 M : Set (PG M)) := by
  intro htN
  have htN' := Subgroup.mem_normalizer_iff.1 htN
  have hK21 : K2 M ≤ K1 M := by
    intro x hx
    rw [← tP_swap M] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    rw [← hyx]
    exact (htN' y).1 hy
  have hK : K2 M = K1 M :=
    Subgroup.eq_of_le_of_card_ge hK21 (by rw [card_K1_eq, card_K2_eq])
  exact K1_ne_K2 hG hK.symm

theorem all_inv_classes [Finite F] {M : ModelData F} (hG : GoodModel M) (hZ : ZsTwo M)
    (hC : ClsFacts M) {u : PG M} (hu : orderOf u = 2) :
    IsConj (yP M) u ∨ IsConj (tP M * yP M) u := by
  obtain ⟨g, hg⟩ := exists_conj_mem_Cg M hG.odd_index hu
  rw [centralizer_yP] at hg
  obtain ⟨n, hn, hnu⟩ := Subgroup.mem_map.1 hg
  have hnu' : mkP M n = g * u * g⁻¹ := hnu
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu, pow_two] at this
  have hsq : mkP M n * mkP M n = 1 := by
    rw [hnu']
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hne : mkP M n ≠ 1 := by
    intro h
    rw [hnu'] at h
    have : u = 1 := by
      have e : u = g⁻¹ * (g * u * g⁻¹) * g := by group
      rw [e, h]; group
    rw [this, orderOf_one] at hu
    omega
  have h1 := inv_classes hG hZ hC hn hsq hne
  rw [hnu'] at h1
  have hc : IsConj (g * u * g⁻¹) u := isConj_iff.2 ⟨g⁻¹, by group⟩
  rcases h1 with h1 | h1
  · exact Or.inl (h1.trans hc)
  · exact Or.inr (h1.trans hc)

theorem E_fus_generic [Finite F] {M : ModelData F} (hG : GoodModel M) {q : ℕ} (hq : Odd q)
    (hSL : HasSL2Model ↥M.H2 (fun r => r = q)) (hJ : J0 F ∈ M.H2)
    (hjj : ∃ k ∈ M.K4, k * diagGL (J0 F) (J0 F) * k⁻¹ = swapGL F * yGL F) :
    ∀ x ∈ K1 M ⊔ K2 M, orderOf x = 2 → x ≠ yP M → IsConj (tP M * yP M) x := by
  intro x hx hx2 hxz
  have hxJ2 : orderOf (xJ M hJ) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact xJ_sq hG hJ) (xJ_ne_one hG hJ)
  obtain ⟨k, -, hkx⟩ := K_one_class_E hG hq hSL (xJ_mem_E M hJ) hx hxJ2 hx2 (xJ_ne_y hG hJ) hxz
  exact (xJ_conj_of_jj hJ hjj).symm.trans (isConj_iff.2 ⟨k, hkx⟩)

theorem central_inv_conj {G : Type*} [Group G] [Finite G] {S₀ : Sylow 2 G} {y : G}
    (hy : orderOf y = 2) (hc : CenterIs (S₀ : Subgroup G) y) {x : G}
    (hx : CFSG.GH74.IsCentralInvolution x) : IsConj y x := by
  obtain ⟨hx2, S', hxS, hxc⟩ := hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S₀
  have hcoe : ((g • S' : Sylow 2 G) : Subgroup G) =
      (S' : Subgroup G).map (MulAut.conj g).toMonoidHom := toSubmonoid_inj.mp rfl
  have hS : (S' : Subgroup G).map (MulAut.conj g).toMonoidHom = (S₀ : Subgroup G) := by
    rw [← hcoe, hg]
  have hgx : g * x * g⁻¹ ∈ (S₀ : Subgroup G) := by
    rw [← hS]
    exact ⟨x, hxS, rfl⟩
  have hgc : ∀ s ∈ (S₀ : Subgroup G), s * (g * x * g⁻¹) = (g * x * g⁻¹) * s := by
    intro s hs
    rw [← hS] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    show g * s' * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * s' * g⁻¹)
    calc g * s' * g⁻¹ * (g * x * g⁻¹) = g * (s' * x) * g⁻¹ := by group
      _ = g * (x * s') * g⁻¹ := by rw [hxc s' hs']
      _ = g * x * g⁻¹ * (g * s' * g⁻¹) := by group
  have hmem := (hc _).1 ⟨hgx, hgc⟩
  have hord : orderOf (g * x * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) x
    rw [MulAut.conj_apply] at this
    rw [this]; exact hx2
  have := eq_of_mem_zpowers_of_orderOf_two hy hord hmem
  exact (isConj_iff.2 ⟨g, this⟩).symm

theorem det_of_sq_neg_one {M : ModelData F} (hC : ClsFacts M) {a : GL (Fin 2) F} (ha : a ∈ M.U2)
    (haa : a * a = -1) : (a : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have hc1 : a * a = sc2 (-1 : Fˣ) := by rw [haa, sc2_neg_one]
  rcases ch_sq hc1 with ⟨l, hl, hll⟩ | ⟨-, hd⟩
  · exact absurd hll (hC.no_scalar_i l (hl ▸ ha))
  · simpa using hd

theorem D_plus_class [Finite F] {M : ModelData F} (hG : GoodModel M) (hZ : ZsTwo M)
    (hC : ClsFacts M) {a b : GL (Fin 2) F} (ha : a ∈ M.U2) (hb : b ∈ M.U2)
    (hda : (a : Matrix (Fin 2) (Fin 2) F).det = -1) (hdb : (b : Matrix (Fin 2) (Fin 2) F).det = -1)
    (hK : diagGL a b ∈ M.K4) (hsq : mkP M ⟨diagGL a b, hK⟩ * mkP M ⟨diagGL a b, hK⟩ = 1)
    (hne : mkP M ⟨diagGL a b, hK⟩ ≠ 1) : IsConj (yP M) (mkP M ⟨diagGL a b, hK⟩) := by
  have h2 := hG.two_ne_zero
  set n : ↥M.K4 := ⟨diagGL a b, hK⟩ with hn
  have hnsq : n * n ∈ Zs M := (QuotientGroup.eq_one_iff (n * n)).1 (by
    show mkP M (n * n) = 1
    rw [map_mul]; exact hsq)
  have hZn : (n : GL (Fin 4) F) * (n : GL (Fin 4) F) = diagGL (1 : GL (Fin 2) F) 1 ∨
      (n : GL (Fin 4) F) * (n : GL (Fin 4) F) = diagGL (-1 : GL (Fin 2) F) (-1) := by
    rcases hZ _ hnsq with h | h
    · left; rw [diagGL_one]; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val h
  have hnn : (n : GL (Fin 4) F) * (n : GL (Fin 4) F) = diagGL (a * a) (b * b) := by
    show diagGL a b * diagGL a b = _
    rw [diagGL_mul]
  rw [hnn] at hZn
  rcases hZn with h1 | h1
  · obtain ⟨haa, hbb⟩ := diagGL_inj h1
    have hnz : ¬ ∃ s : Fˣ, diagGL a b = sc4 s := by
      rintro ⟨s, hs⟩
      apply hne
      exact (QuotientGroup.eq_one_iff _).2 (mem_Zs.2 ⟨s, hs.symm⟩)
    exact isConj_y_of_ConjMod' (n := n)
      (D_plus_conj hC h2 ha hb (by rw [hda, hdb]; norm_num) haa hbb hnz)
  · obtain ⟨haa, -⟩ := diagGL_inj h1
    exfalso
    have := det_of_sq_neg_one hC ha haa
    rw [hda] at this
    apply h2
    linear_combination -this

theorem E_mul_w_conj_y [Finite F] {M : ModelData F} (hG : GoodModel M) (hZ : ZsTwo M)
    (hC : ClsFacts M) {d : GL (Fin 2) F} (hd : d ∈ M.U2) (hdd : d * d = 1)
    (hdet : (d : Matrix (Fin 2) (Fin 2) F).det = -1) {x : PG M} (hx : x ∈ K1 M ⊔ K2 M)
    (hxw : orderOf (x * dP M d hd) = 2) : IsConj (yP M) (x * dP M d hd) := by
  obtain ⟨a, b, rfl⟩ := (mem_E_iff M).1 hx
  have hab := diagGL_mem_K4_of_H2 M a b
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  obtain ⟨haU, hadet⟩ := (M.mem_H2 _).1 a.2
  obtain ⟨hbU, hbdet⟩ := (M.mem_H2 _).1 b.2
  have had : (a : GL (Fin 2) F) * d ∈ M.U2 := M.U2.mul_mem haU hd
  have hbd : (b : GL (Fin 2) F) * d ∈ M.U2 := M.U2.mul_mem hbU hd
  have hdetA : (((a : GL (Fin 2) F) * d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = -1 := by
    rw [Units.val_mul, Matrix.det_mul, hadet, hdet, one_mul]
  have hdetB : (((b : GL (Fin 2) F) * d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = -1 := by
    rw [Units.val_mul, Matrix.det_mul, hbdet, hdet, one_mul]
  have hK : diagGL ((a : GL (Fin 2) F) * d) ((b : GL (Fin 2) F) * d) ∈ M.K4 :=
    M.diagGL_mem_K4_iff.2 ⟨had, hbd, by rw [hdetA, hdetB]; norm_num⟩
  have hprod : iota1 M a * iota2 M b * dP M d hd =
      mkP M ⟨diagGL ((a : GL (Fin 2) F) * d) ((b : GL (Fin 2) F) * d), hK⟩ := by
    rw [iota_mul_eq_mkP_diag M a b hab, dP, ← map_mul]
    congr 1
    apply Subtype.ext
    show diagGL (a : GL (Fin 2) F) b * diagGL d d⁻¹ = _
    rw [diagGL_mul, hdi]
  rw [hprod] at hxw ⊢
  have hsq : mkP M ⟨diagGL ((a : GL (Fin 2) F) * d) ((b : GL (Fin 2) F) * d), hK⟩ *
      mkP M ⟨diagGL ((a : GL (Fin 2) F) * d) ((b : GL (Fin 2) F) * d), hK⟩ = 1 := by
    have := pow_orderOf_eq_one (mkP M ⟨diagGL ((a : GL (Fin 2) F) * d) ((b : GL (Fin 2) F) * d), hK⟩)
    rwa [hxw, pow_two] at this
  have hne : mkP M ⟨diagGL ((a : GL (Fin 2) F) * d) ((b : GL (Fin 2) F) * d), hK⟩ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxw
    omega
  exact D_plus_class hG hZ hC had hbd hdetA hdetB hK hsq hne


theorem tP_mul_dP_conj_y {M : ModelData F} (hC : ClsFacts M) {a : GL (Fin 2) F} (ha : a ∈ M.U2) :
    IsConj (yP M) (tP M * dP M a ha) := by
  rw [tP_mul_dP M ha]
  exact isConj_yP_of_ConjMod _ (hC.plus_W a ha)

@[expose] def PglStmt (M : ModelData F) (q : ℕ) (w : PG M) : Prop :=
  ∀ Ei ∈ ({K1 M, K2 M} : Set (Subgroup (PG M))),
    ∃ _ : ((zpowers (yP M)).subgroupOf (Ei ⊔ zpowers w)).Normal,
      IVK.IsPGL2 (↥(Ei ⊔ zpowers w) ⧸ (zpowers (yP M)).subgroupOf (Ei ⊔ zpowers w))
        (fun r => r = q)

theorem dat410_generic [Finite F] {M : ModelData F} (hG : GoodModel M) (hZ : ZsTwo M)
    (hC : ClsFacts M) {q : ℕ} (hq : Odd q) (hSL : HasSL2Model ↥M.H2 (fun r => r = q))
    (hJ : J0 F ∈ M.H2)
    (hjj : ∃ k ∈ M.K4, k * diagGL (J0 F) (J0 F) * k⁻¹ = swapGL F * yGL F)
    {S : Subgroup (PG M)} {w : PG M} (htS : tP M ∈ S) (hwS : w ∈ S) (hw2 : w = 1 ∨ orderOf w = 2)
    (hwC : w ∈ C0 M) (hwN : w ∈ Subgroup.normalizer (K1 M : Set (PG M)))
    (hwE : w = 1 ∨ w ∉ K1 M ⊔ K2 M) (hcomm : tP M * w = w * tP M)
    (hdec : ∀ s ∈ S, ∃ k ∈ S ⊓ (K1 M ⊔ K2 M),
      s = k ∨ s = k * tP M ∨ s = k * w ∨ s = k * (tP M * w))
    (ht : IsConj (yP M) (tP M)) (hpgl : w ≠ 1 → PglStmt M q w)
    (hwfus : w ≠ 1 → IsConj (yP M) (tP M * w) ∧
      ∀ x ∈ S ⊓ (K1 M ⊔ K2 M), orderOf (x * w) = 2 → IsConj (yP M) (x * w)) :
    Dat410 q (yP M) S (tP M) w (K1 M) (K2 M) := by
  have h2 := hG.two_ne_zero
  have hww : w * w = 1 := by
    rcases hw2 with h | h
    · rw [h, one_mul]
    · have := pow_orderOf_eq_one w
      rwa [h, pow_two] at this
  have hEz := Ez_yP hG
  refine
    { t_mem := htS
      w_mem := hwS
      t_ord := orderOf_tP M h2
      w_ord := hw2
      comm := hcomm
      prod := ?_
      inter := ?_
      t_conj := ht
      Ez_eq := hEz
      E₂_eq := (tP_swap M).symm
      sl2 := (luComps_PG hG q hSL).sl₁
      inter_E := K1_inf_K2 hG
      comm_E := fun a ha b hb => K1_K2_comm M ha hb
      norm_E := ?_
      classes := fun x hx => all_inv_classes hG hZ hC hx
      tz_ne := not_isConj_y_wy hZ h2
      E_fus := ?_
      pgl := hpgl
      w_fus := ?_ }
  · rw [hEz]
    apply le_antisymm
    · intro s hs
      obtain ⟨k, hk, hcase⟩ := hdec s hs
      have hk' : k ∈ (S ⊓ (K1 M ⊔ K2 M)) ⊔ zpowers (tP M) ⊔ zpowers w :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_left hk)
      have ht' : tP M ∈ (S ⊓ (K1 M ⊔ K2 M)) ⊔ zpowers (tP M) ⊔ zpowers w :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      have hw' : w ∈ (S ⊓ (K1 M ⊔ K2 M)) ⊔ zpowers (tP M) ⊔ zpowers w :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rcases hcase with h | h | h | h <;> rw [h]
      · exact hk'
      · exact Subgroup.mul_mem _ hk' ht'
      · exact Subgroup.mul_mem _ hk' hw'
      · exact Subgroup.mul_mem _ hk' (Subgroup.mul_mem _ ht' hw')
    · exact sup_le (sup_le inf_le_left (Subgroup.zpowers_le.2 htS)) (Subgroup.zpowers_le.2 hwS)
  · rw [hEz, eq_bot_iff]
    rintro x ⟨hxE, hxV⟩
    rw [Subgroup.mem_bot]
    rcases mem_sup_pair_of_comm hcomm (tP_sq M) hww hxV with h | h | h | h
    · exact h
    · exact absurd (h ▸ hxE) (tP_not_mem_E M h2)
    · rcases hwE with hw1 | hwE
      · rw [h, hw1]
      · exact absurd (h ▸ hxE) hwE
    · exact absurd (h ▸ hxE) (tP_mul_not_mem_E M h2 hwC)
  · rw [hEz]
    apply le_antisymm
    · rintro x ⟨hxN, hxS⟩
      obtain ⟨k, hk, hcase⟩ := hdec x hxS
      have hkN : k ∈ Subgroup.normalizer (K1 M : Set (PG M)) :=
        normalizer_K1_of_C0 M h2 (E_le_C0 M hk.2)
      have hk' : k ∈ (S ⊓ (K1 M ⊔ K2 M)) ⊔ zpowers w := Subgroup.mem_sup_left hk
      have hw' : w ∈ (S ⊓ (K1 M ⊔ K2 M)) ⊔ zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rcases hcase with h | h | h | h
      · rw [h]; exact hk'
      · exfalso
        apply tP_not_mem_normalizer hG
        have : tP M = k⁻¹ * x := by rw [h]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hxN
      · rw [h]; exact Subgroup.mul_mem _ hk' hw'
      · exfalso
        apply tP_not_mem_normalizer hG
        have h1 : tP M * w = k⁻¹ * x := by rw [h]; group
        have h3 : tP M * w ∈ Subgroup.normalizer (K1 M : Set (PG M)) := by
          rw [h1]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hxN
        have := Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hwN)
        rwa [mul_inv_cancel_right] at this
    · refine sup_le (fun x hx => Subgroup.mem_inf.2 ⟨normalizer_K1_of_C0 M h2 (E_le_C0 M hx.2), hx.1⟩)
        (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hwN, hwS⟩))
  · rw [hEz]
    exact E_fus_generic hG hq hSL hJ hjj
  · intro hw1
    rw [hEz]
    exact hwfus hw1

theorem sp410 [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) :
    ∃ S : Sylow 2 (PG (ModelData.sp F)),
      CenterIs (S : Subgroup (PG (ModelData.sp F))) (yP _) ∧
      Dat410 (Nat.card F) (yP _) (S : Subgroup (PG (ModelData.sp F))) (tP _) 1 (K1 _) (K2 _) := by
  have hG := goodModel_sp h2 h5
  have hZ : ZsTwo (ModelData.sp F) := zsTwo_sp
  have hq : Odd (Nat.card F) := ModelSp.odd_card_of_two_ne_zero h2
  have hCodd : Odd (Cg (ModelData.sp F)).index := by rw [index_C]; exact hG.odd_index
  have hEn := layer_normal_Cg (ModelData.sp F) h2 hG.qs
  have hord : ∃ i : ℕ, tP (ModelData.sp F) ^ 2 ^ i = 1 := ⟨1, by simpa [pow_two] using tP_sq _⟩
  have hW : IsPGroup 2 ↥(zpowers (tP (ModelData.sp F))) := by
    obtain ⟨j, hj⟩ := ModelSylowQ.card_zpowers_two_pow hord
    exact IsPGroup.of_card hj
  have hU : Nat.card ↥(ModelData.sp F).U2 = Nat.card ↥(ModelData.sp F).H2 * 1 := card_U2_sp
  have hidx := index_E_Cg_eq (ModelData.sp F) (card_Cg_eq hG hZ hU)
  obtain ⟨S, hSC, haS, -, -, hdec⟩ := exists_sylow_le_quot2 (Cg (ModelData.sp F))
    (K1 (ModelData.sp F) ⊔ K2 (ModelData.sp F)) hCodd (E_le_Cg _) hEn (o := 1) odd_one hidx
    (a := tP (ModelData.sp F)) hW (Subgroup.mem_zpowers _)
    (Subgroup.zpowers_le.2 (tP_mem_Cg _)) (tP_not_mem_E _ h2)
  refine ⟨S, sylow_center_of_le_Cg hG S hSC, ?_⟩
  have hwc : IsConj (yP (ModelData.sp F)) (tP (ModelData.sp F)) := by
    obtain ⟨k, hk, hkc⟩ := w_conj_sp h2
    exact isConj_yP_of_ConjMod (ModelData.sp F).swapGL_mem_K4 (ConjMod.of_conj hk hkc)
  exact dat410_generic hG hZ (clsFacts_sp h2 h5) hq (hasSL2Model_H2_sp F) (J0_mem_H2_sp F)
    (jj_conj_sp h2) haS (Subgroup.one_mem _) (Or.inl rfl) (Subgroup.one_mem _) (Subgroup.one_mem _)
    (Or.inl rfl) (by rw [mul_one, one_mul])
    (fun s hs => by
      obtain ⟨k, hk, h⟩ := hdec s hs
      refine ⟨k, hk, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    hwc (fun h => absurd rfl h) (fun h => absurd rfl h)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
