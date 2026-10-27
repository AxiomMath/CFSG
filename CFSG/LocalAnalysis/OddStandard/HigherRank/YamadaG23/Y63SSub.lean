module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63SCard
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Prod

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk

variable {D : Data} [Group Y63TG]

theorem y63_mem_nn {n : ℕ} : n ∈ D.nn ↔ n ∈ D.m0 ∧ D.mt n n = 0 := by
  simp [Data.nn, List.mem_filter]

theorem y63_card_M1 (hM : D.MSpec) (M₁ : Subgroup Y63TG)
    (hMset : ∀ x : Y63TG, x ∈ M₁ ↔ x.val ∈ D.m0) : Nat.card M₁ = 64 := by
  obtain ⟨hnd, hlen, hlt, -⟩ := hM
  rw [Nat.card_congr (Equiv.subtypeEquivRight hMset), y63_card_list hnd hlt, hlen]

theorem y63_S_inter (hM : D.MSpec) (hn8 : D.nn.length = 8) (M₁ : Subgroup Y63TG) [M₁.Normal]
    (hMset : ∀ x : Y63TG, x ∈ M₁ ↔ x.val ∈ D.m0) (B : Subgroup Y63TG) (hB : Nat.card B = 64)
    (hN : ∀ x : Y63TG, x.val ∈ D.nn → x ∈ B) (hBM : B ⊔ M₁ = ⊤) :
    ∀ x : Y63TG, x ∈ B → x ∈ M₁ → x.val ∈ D.nn := by
  classical
  have hM64 := y63_card_M1 hM M₁ hMset
  obtain ⟨hnd, -, hlt, -⟩ := hM
  have hndn : D.nn.Nodup := hnd.filter _
  have hltn : ∀ a ∈ D.nn, a < 512 := fun a ha => hlt a (List.mem_of_mem_filter ha)
  have hprod := y63_card_mul_of_sup hBM
  rw [hB, hM64, Y63TG.card] at hprod
  have h8 : Nat.card ↥(B ⊓ M₁) = 8 := by omega
  have hNcard : (Finset.univ.filter fun x : Y63TG => x.val ∈ D.nn).card = 8 := by
    have := y63_card_list hndn hltn
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    rw [this, hn8]
  have hKcard : (Finset.univ.filter fun x : Y63TG => x ∈ B ⊓ M₁).card = 8 := by
    rw [← h8, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : (Finset.univ.filter fun x : Y63TG => x.val ∈ D.nn) ⊆
      Finset.univ.filter fun x : Y63TG => x ∈ B ⊓ M₁ := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_inf] at hx ⊢
    exact ⟨hN x hx, (hMset x).mpr (y63_mem_nn.mp hx).1⟩
  have hEq := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro x hxB hxM
  have hx : x ∈ Finset.univ.filter fun x : Y63TG => x ∈ B ⊓ M₁ := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_inf]
    exact ⟨hxB, hxM⟩
  rw [← hEq] at hx
  simpa using hx

theorem y63_S_rep (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val) (hM : D.MSpec)
    (hS : D.SSpec) (M₁ : Subgroup Y63TG) [M₁.Normal]
    (hMset : ∀ x : Y63TG, x ∈ M₁ ↔ x.val ∈ D.m0) (B : Subgroup Y63TG)
    (hN : ∀ x : Y63TG, x.val ∈ D.nn → x ∈ B) (hBM : B ⊔ M₁ = ⊤) (x : Y63TG) :
    ∃ i ∈ D.reps, ∃ mi : Y63TG, mi.val = i ∧ x * mi ∈ B := by
  obtain ⟨-, -, hrepM, hcov, -⟩ := hS
  have hx : x ∈ B ⊔ M₁ := by rw [hBM]; trivial
  obtain ⟨b, hb, m, hm, hbm⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨i, hi, n, hn, hin⟩ := hcov _ ((hMset _).mp (inv_mem hm))
  have hlt := hM.2.2.1
  let mi : Y63TG := ⟨i, hlt i (hrepM i hi)⟩
  let nE : Y63TG := ⟨n, hlt n (y63_mem_nn.mp hn).1⟩
  have hmin : m⁻¹ = mi * nE := Y63TG.ext (by rw [hmul]; exact hin.symm)
  refine ⟨i, hi, mi, rfl, ?_⟩
  have hm' : m = nE⁻¹ * mi⁻¹ := by
    calc m = (m⁻¹)⁻¹ := (inv_inv m).symm
      _ = (mi * nE)⁻¹ := by rw [hmin]
      _ = nE⁻¹ * mi⁻¹ := mul_inv_rev _ _
  have hxm : x * mi = b * nE⁻¹ := by
    rw [← hbm, hm']
    group
  rw [hxm]
  exact mul_mem hb (inv_mem (hN nE hn))

theorem y63_S_classify (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val)
    (h1 : (1 : Y63TG).val = 0) (hI : D.InvSpec) (hM : D.MSpec) (hS : D.SSpec)
    (gen : Fin 5 → Y63TG) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hg0 : (gen 0).val = D.T 0 0) (hg1 : (gen 1).val = D.T 0 2) (hg2 : (gen 2).val = D.T 0 4)
    (hg3 : (gen 3).val = D.T 0 6) (hg4 : (gen 4).val = D.T 0 8)
    (M₁ : Subgroup Y63TG) [M₁.Normal] (hMset : ∀ x : Y63TG, x ∈ M₁ ↔ x.val ∈ D.m0)
    (B : Subgroup Y63TG) (hB : Nat.card B = 64) (hN : ∀ x : Y63TG, x.val ∈ D.nn → x ∈ B)
    (hBM : B ⊔ M₁ = ⊤) :
    ∃ k < 4, ∃ g : Y63TG, ∀ x : Y63TG, x ∈ B ↔ (g⁻¹ * x * g).val ∈ D.sk k := by
  classical
  have hS' := hS
  obtain ⟨hn8, hsk, hrepM, -, hpair⟩ := hS'
  have hinter := y63_S_inter hM hn8 M₁ hMset B hB hN hBM
  have hM64 := y63_card_M1 hM M₁ hMset
  have hM' := hM
  obtain ⟨hnd, -, hlt, hu, hv, hw, -⟩ := hM'
  have hndn : D.nn.Nodup := hnd.filter _
  have hltn : ∀ a ∈ D.nn, a < 512 := fun a ha => hlt a (List.mem_of_mem_filter ha)
  obtain ⟨i, hi, mi, hmi, hri⟩ := y63_S_rep hmul hM hS M₁ hMset B hN hBM (gen 3)
  obtain ⟨j, hj, mj, hmj, hsj⟩ := y63_S_rep hmul hM hS M₁ hMset B hN hBM (gen 4)
  obtain ⟨a, ha⟩ : ∃ a : Y63TG, a = gen 3 * mi := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Y63TG, b = gen 4 * mj := ⟨_, rfl⟩
  have haB : a ∈ B := by rw [ha]; exact hri
  have hbB : b ∈ B := by rw [hb]; exact hsj
  have hav : a.val = D.pa i := by rw [ha, hmul, hg3, hmi]; rfl
  have hbv : b.val = D.pb j := by rw [hb, hmul, hg4, hmj]; rfl
  have hcases : (D.cj i j).1 < 4 ∧ (D.cj i j).2 < 512 ∧
      D.mt (D.mt (D.iv (D.cj i j).2) (D.pa i)) (D.cj i j).2 ∈ D.sk (D.cj i j).1 ∧
      D.mt (D.mt (D.iv (D.cj i j).2) (D.pb j)) (D.cj i j).2 ∈ D.sk (D.cj i j).1 := by
    rcases hpair i hi j hj with ⟨hm0, hnn⟩ | ⟨hm0, hnn⟩ | ⟨hm0, hnn⟩ | h4
    · exfalso
      refine hnn ?_
      have hM1 : a * a ∈ M₁ := (hMset _).mpr (by rw [hmul, hav]; exact hm0)
      have := hinter _ (mul_mem haB haB) hM1
      rwa [hmul, hav] at this
    · exfalso
      refine hnn ?_
      have hM1 : b ^ 4 ∈ M₁ := (hMset _).mpr (by rw [y63_pow4_val hmul, hbv]; exact hm0)
      have := hinter _ (pow_mem hbB 4) hM1
      rwa [y63_pow4_val hmul, hbv] at this
    · exfalso
      refine hnn ?_
      have hM1 : a * b * (a * b) ∈ M₁ :=
        (hMset _).mpr (by rw [hmul, hmul, hav, hbv]; exact hm0)
      have := hinter _ (mul_mem (mul_mem haB hbB) (mul_mem haB hbB)) hM1
      rwa [hmul, hmul, hav, hbv] at this
    · exact h4
  obtain ⟨hk4, hg512, hak, hbk⟩ := hcases
  obtain ⟨hsknd, hsklen, hsklt, hsk0, hskcl, hskinv, hsknn⟩ := hsk _ hk4
  let gE : Y63TG := ⟨(D.cj i j).2, hg512⟩
  refine ⟨(D.cj i j).1, hk4, gE, ?_⟩
  let Sk : Subgroup Y63TG := y63ListSub hmul h1 hI hsk0 hskcl hskinv
  have hSkcard : Nat.card Sk = 64 := by
    rw [y63ListSub_card hmul h1 hI hsk0 hskcl hskinv hsknd hsklt, hsklen]
  let C : Subgroup Y63TG := Sk.comap (MulAut.conj gE⁻¹).toMonoidHom
  have hCmem : ∀ x : Y63TG, x ∈ C ↔ (gE⁻¹ * x * gE).val ∈ D.sk (D.cj i j).1 := by
    intro x
    show (MulAut.conj gE⁻¹) x ∈ Sk ↔ _
    rw [MulAut.conj_apply, inv_inv]
    exact Iff.rfl
  have hCcard : Nat.card C = 64 := by
    show Nat.card ↥(Sk.comap (MulAut.conj gE⁻¹).toMonoidHom) = 64
    rw [Subgroup.comap_equiv_eq_map_symm' (MulAut.conj gE⁻¹),
      Subgroup.card_map_of_injective (MulEquiv.injective _), hSkcard]
  have hNC : ∀ x : Y63TG, x.val ∈ D.nn → x ∈ C := by
    intro x hx
    rw [hCmem]
    obtain ⟨hxm, hxsq⟩ := y63_mem_nn.mp hx
    have hxM : x ∈ M₁ := (hMset x).mpr hxm
    have hyM : gE⁻¹ * x * gE ∈ M₁ := by
      have := (inferInstance : M₁.Normal).conj_mem x hxM gE⁻¹
      simpa using this
    have hxx : x * x = 1 := Y63TG.ext (by rw [hmul, h1]; exact hxsq)
    have hysq : (gE⁻¹ * x * gE) * (gE⁻¹ * x * gE) = 1 := by
      calc (gE⁻¹ * x * gE) * (gE⁻¹ * x * gE) = gE⁻¹ * (x * x) * gE := by group
        _ = 1 := by rw [hxx]; group
    have hyv : D.mt (gE⁻¹ * x * gE).val (gE⁻¹ * x * gE).val = 0 := by
      rw [← hmul, hysq, h1]
    exact hsknn _ (y63_mem_nn.mpr ⟨(hMset _).mp hyM, hyv⟩)
  have haC : a ∈ C := (hCmem a).mpr (by rw [hmul, hmul, y63_inv_val hmul h1 hI, hav]; exact hak)
  have hbC : b ∈ C := (hCmem b).mpr (by rw [hmul, hmul, y63_inv_val hmul h1 hI, hbv]; exact hbk)
  let T : Subgroup Y63TG := Subgroup.closure ({a, b} ∪ {x : Y63TG | x.val ∈ D.nn})
  have hTB : T ≤ B := by
    refine (Subgroup.closure_le _).mpr (Set.union_subset ?_ ?_)
    · intro x hx
      rcases hx with rfl | hx
      · exact haB
      · rw [Set.mem_singleton_iff.mp hx]; exact hbB
    · intro x hx
      exact hN x hx
  have hTC : T ≤ C := by
    refine (Subgroup.closure_le _).mpr (Set.union_subset ?_ ?_)
    · intro x hx
      rcases hx with rfl | hx
      · exact haC
      · rw [Set.mem_singleton_iff.mp hx]; exact hbC
    · intro x hx
      exact hNC x hx
  have haT : a ∈ T := Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have hbT : b ∈ T := Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hTM : T ⊔ M₁ = ⊤ := by
    have hmiM : mi ∈ M₁ := (hMset _).mpr (by rw [hmi]; exact hrepM i hi)
    have hmjM : mj ∈ M₁ := (hMset _).mpr (by rw [hmj]; exact hrepM j hj)
    have h3 : gen 3 ∈ T ⊔ M₁ := by
      have : gen 3 = a * mi⁻¹ := by rw [ha]; group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left haT) (Subgroup.mem_sup_right (inv_mem hmiM))
    have h4 : gen 4 ∈ T ⊔ M₁ := by
      have : gen 4 = b * mj⁻¹ := by rw [hb]; group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hbT) (Subgroup.mem_sup_right (inv_mem hmjM))
    have h0 : gen 0 ∈ T ⊔ M₁ := Subgroup.mem_sup_right ((hMset _).mpr (by rw [hg0]; exact hu))
    have h1' : gen 1 ∈ T ⊔ M₁ := Subgroup.mem_sup_right ((hMset _).mpr (by rw [hg1]; exact hv))
    have h2 : gen 2 ∈ T ⊔ M₁ := Subgroup.mem_sup_right ((hMset _).mpr (by rw [hg2]; exact hw))
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    fin_cases c
    exacts [h0, h1', h2, h3, h4]
  have h8 : 8 ≤ Nat.card ↥(T ⊓ M₁) := by
    have hcard := y63_card_list hndn hltn
    rw [hn8] at hcard
    rw [← hcard]
    exact Nat.card_le_card_of_injective
      (fun x : {x : Y63TG // x.val ∈ D.nn} => (⟨x.1, Subgroup.mem_inf.mpr
        ⟨Subgroup.subset_closure (Or.inr x.2), (hMset _).mpr (y63_mem_nn.mp x.2).1⟩⟩ :
          ↥(T ⊓ M₁)))
      (fun x y h => Subtype.ext (congrArg (Subtype.val : ↥(T ⊓ M₁) → Y63TG) h))
  have hBC : B = C := y63_squeeze Y63TG.card hM64 hB hCcard hTB hTC hTM h8
  intro x
  rw [hBC]
  exact hCmem x

end CFSG.OddStandard.HigherRank.YamadaG23
