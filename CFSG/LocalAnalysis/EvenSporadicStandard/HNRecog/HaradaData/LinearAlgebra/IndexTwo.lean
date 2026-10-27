module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.OrthData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

theorem eq_omegaOf_of_card {q : V6 → ZMod 2} (hq : IsQF q) (hTG : OrthOf q = TG q)
    (htrans : ∀ u v : V6, q u = 1 → q v = 1 → ∃ g ∈ OrthOf q, g u = v)
    {N : Subgroup (Equiv.Perm V6)} (hN : N ≤ OrthOf q)
    (hc : Nat.card N * 2 = Nat.card (OrthOf q)) : N = OmegaOf q := by
  have hOmega_def : OmegaOf q = Subgroup.closure
      {g : Equiv.Perm V6 | ∃ u v : V6, q u = 1 ∧ q v = 1 ∧ g = transv u * transv v} := rfl
  have hTG_def : TG q = Subgroup.closure
      {g : Equiv.Perm V6 | ∃ u : V6, q u = 1 ∧ g = transv u} := rfl
  let N' : Subgroup (OrthOf q) := N.subgroupOf (OrthOf q)
  have hcard' : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  have hcm : Nat.card N' * 2 = Nat.card (OrthOf q) := by rw [hcard', hc]
  have hci : Nat.card N' * N'.index = Nat.card (OrthOf q) :=
    Subgroup.card_mul_index (H := N')
  haveI : Nonempty N' := ⟨1⟩
  have hpos' : 0 < Nat.card N' := Nat.card_pos
  have hindex : N'.index = 2 :=
    Nat.mul_left_cancel hpos' (by rw [hci, hcm])
  have hnormal : N'.Normal := Subgroup.normal_of_index_eq_two hindex
  have hconjO : ∀ a ∈ OrthOf q, ∀ w ∈ OmegaOf q, a * w * a⁻¹ ∈ OmegaOf q := by
    intro a ha w hw
    rw [hOmega_def] at hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨u, v, hu, hv, rfl⟩ := hx
        have hau : q (a u) = 1 := by rw [ha.2 u, hu]
        have hav : q (a v) = 1 := by rw [ha.2 v, hv]
        have hc1 : a * transv u * a⁻¹ = transv (a u) := conj_transv hq ha u
        have hc2 : a * transv v * a⁻¹ = transv (a v) := conj_transv hq ha v
        rw [show a * (transv u * transv v) * a⁻¹
              = (a * transv u * a⁻¹) * (a * transv v * a⁻¹) by group, hc1, hc2]
        exact Subgroup.subset_closure ⟨a u, a v, hau, hav, rfl⟩
    | one => simp
    | mul x y _ _ ihx ihy =>
        rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group]
        exact mul_mem ihx ihy
    | inv x _ ihx =>
        rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
        exact inv_mem ihx
  have key : ∀ u, q u = 1 → transv u ∉ N := by
    intro u0 hu0 hTu0N
    have hTu0O : transv u0 ∈ OrthOf q := transv_mem_orthOf hq hu0
    have hTu0N' : (⟨transv u0, hTu0O⟩ : OrthOf q) ∈ N' := hTu0N
    have hTGle : TG q ≤ N := by
      rw [hTG_def]
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨u, hu, rfl⟩
      obtain ⟨g, hgO, hgu⟩ := htrans u0 u hu0 hu
      have hconj : g * transv u0 * g⁻¹ = transv u := by
        rw [conj_transv hq hgO u0, hgu]
      rw [← hconj]
      have hconjN : (⟨g, hgO⟩ : OrthOf q) * ⟨transv u0, hTu0O⟩
          * (⟨g, hgO⟩ : OrthOf q)⁻¹ ∈ N' :=
        hnormal.conj_mem ⟨transv u0, hTu0O⟩ hTu0N' ⟨g, hgO⟩
      exact hconjN
    have hON : OrthOf q ≤ N := by rw [hTG]; exact hTGle
    have hNO : N = OrthOf q := le_antisymm hN hON
    have hcard : Nat.card N = Nat.card (OrthOf q) :=
      congrArg (fun H : Subgroup (Equiv.Perm V6) => Nat.card H) hNO
    have hx2 : Nat.card N * 2 = Nat.card N := hc.trans hcard.symm
    have hzero : Nat.card N = 0 := by omega
    haveI : Nonempty N := ⟨1⟩
    have hpos : 0 < Nat.card N := Nat.card_pos
    omega
  have hgen_mem_N : ∀ u v, q u = 1 → q v = 1 → transv u * transv v ∈ N := by
    intro u v hu hv
    have huO : transv u ∈ OrthOf q := transv_mem_orthOf hq hu
    have hvO : transv v ∈ OrthOf q := transv_mem_orthOf hq hv
    have huN : (⟨transv u, huO⟩ : OrthOf q) ∉ N' := fun h => key u hu h
    have hvN : (⟨transv v, hvO⟩ : OrthOf q) ∉ N' := fun h => key v hv h
    have hkey := Subgroup.mul_mem_iff_of_index_two (H := N') hindex
      (a := (⟨transv u, huO⟩ : OrthOf q)) (b := (⟨transv v, hvO⟩ : OrthOf q))
    have hmem : (⟨transv u, huO⟩ : OrthOf q) * ⟨transv v, hvO⟩ ∈ N' := by
      rw [hkey]
      exact ⟨fun h => (huN h).elim, fun h => (hvN h).elim⟩
    exact hmem
  have hOmega_le_N : OmegaOf q ≤ N := by
    rw [hOmega_def]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨u, v, hu, hv, rfl⟩
    exact hgen_mem_N u v hu hv
  have hNleOmega : N ≤ OmegaOf q := by
    by_cases hex : ∃ u : V6, q u = 1
    · obtain ⟨u0, hu0⟩ := hex
      have hT0O : transv u0 ∈ OrthOf q := transv_mem_orthOf hq hu0
      have hT0inv : (transv u0)⁻¹ = transv u0 :=
        (eq_inv_of_mul_eq_one_right (transv_mul_self u0)).symm
      have hmain : ∀ g ∈ TG q, g ∈ OmegaOf q ∨ g * transv u0 ∈ OmegaOf q := by
        intro g hg
        rw [hTG_def] at hg
        induction hg using Subgroup.closure_induction with
        | mem x hx =>
            obtain ⟨u, hu, rfl⟩ := hx
            exact Or.inr (Subgroup.subset_closure ⟨u, u0, hu, hu0, rfl⟩)
        | one => exact Or.inl (one_mem _)
        | mul x y _ _ ihx ihy =>
            rcases ihx with hx1 | hx1 <;> rcases ihy with hy1 | hy1
            · exact Or.inl (mul_mem hx1 hy1)
            · exact Or.inr (by
                rw [show x * y * transv u0 = x * (y * transv u0) by group]
                exact mul_mem hx1 hy1)
            · exact Or.inr (by
                have hcy : (transv u0)⁻¹ * y * transv u0 ∈ OmegaOf q := by
                  simpa [hT0inv] using hconjO (transv u0) hT0O y hy1
                rw [show x * y * transv u0
                      = (x * transv u0) * ((transv u0)⁻¹ * y * transv u0) by group]
                exact mul_mem hx1 hcy)
            · exact Or.inl (by
                have hTy : transv u0 * y ∈ OmegaOf q := by
                  have hc := hconjO (transv u0) hT0O (y * transv u0) hy1
                  have h1 : transv u0 * (y * transv u0) * (transv u0)⁻¹ = transv u0 * y := by
                    rw [hT0inv]
                    rw [show transv u0 * (y * transv u0) * transv u0
                          = (transv u0 * y) * (transv u0 * transv u0) by group,
                        transv_mul_self u0, mul_one]
                  rwa [h1] at hc
                have hxy : (x * transv u0) * (transv u0 * y) = x * y := by
                  rw [show (x * transv u0) * (transv u0 * y)
                        = x * (transv u0 * transv u0) * y by group,
                      transv_mul_self u0, mul_one]
                rw [← hxy]
                exact mul_mem hx1 hTy)
        | inv x _ ihx =>
            rcases ihx with hx1 | hx1
            · exact Or.inl (inv_mem hx1)
            · refine Or.inr ?_
              have hw : transv u0 * (x * transv u0)⁻¹ * (transv u0)⁻¹ ∈ OmegaOf q :=
                hconjO (transv u0) hT0O ((x * transv u0)⁻¹) (inv_mem hx1)
              have hEq : transv u0 * (x * transv u0)⁻¹ * (transv u0)⁻¹ = x⁻¹ * transv u0 := by
                have h1 : transv u0 * (x * transv u0)⁻¹ * (transv u0)⁻¹
                    = (transv u0 * transv u0) * x⁻¹ * transv u0 := by
                  rw [mul_inv_rev, hT0inv]
                  group
                rw [h1, transv_mul_self u0, one_mul]
              rwa [hEq] at hw
      intro g hgN
      have hgO : g ∈ OrthOf q := hN hgN
      have hgTG : g ∈ TG q := by rw [← hTG]; exact hgO
      rcases hmain g hgTG with hgΩ | hgT0Ω
      · exact hgΩ
      · have hgT0N : g * transv u0 ∈ N := hOmega_le_N hgT0Ω
        have hT0N : transv u0 ∈ N := by
          have h := mul_mem (inv_mem hgN) hgT0N
          rwa [← mul_assoc, inv_mul_cancel, one_mul] at h
        exact absurd hT0N (key u0 hu0)
    · have hTGbot : TG q = ⊥ := by
        rw [hTG_def]
        refine le_antisymm ?_ bot_le
        refine (Subgroup.closure_le _).mpr ?_
        rintro x ⟨u, hu, rfl⟩
        exact (hex ⟨u, hu⟩).elim
      have hObot : OrthOf q = ⊥ := hTG.trans hTGbot
      exact hN.trans (by rw [hObot]; exact bot_le)
  exact le_antisymm hNleOmega hOmega_le_N

theorem eq_omegaMinus_of_card {N : Subgroup (Equiv.Perm V6)} (hN : N ≤ OrthMinus)
    (hc : Nat.card N = 25920) : N = OmegaMinus := by
  refine eq_omegaOf_of_card isQF_qm orthMinus_eq_TG orthMinus_transitive hN ?_
  show Nat.card N * 2 = Nat.card OrthMinus
  rw [hc, card_orthMinus]

theorem eq_omegaPlus_of_card {N : Subgroup (Equiv.Perm V6)} (hN : N ≤ OrthPlus)
    (hc : Nat.card N = 20160) : N = OmegaPlus := by
  refine eq_omegaOf_of_card isQF_qp orthPlus_eq_TG orthPlus_transitive hN ?_
  show Nat.card N * 2 = Nat.card OrthPlus
  rw [hc, card_orthPlus]

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
