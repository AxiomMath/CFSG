module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocKer
public import CFSG.Quasithin.H13.A5Setting

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431

theorem card_Vsub_le : Nat.card Vsub ≤ 16 := by
  choose! Tel hTel using fun (i : ℕ) (hi : i < 64) => exists_Tel (i := i) hi
  have hmem : ∀ i ∈ vFin, Tel i ∈ Vsub := by
    intro i hi
    simp only [vFin, Finset.mem_filter, Finset.mem_range] at hi
    have h := hTel i hi.1
    exact mem_Vsub_of_fix h.1 ((fixL0_iff h.2).1 hi.2)
  let f : vFin → Vsub := fun i => ⟨Tel i, hmem i i.2⟩
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨i, hi, hrep⟩ := (mem_T_iff (g : Y)).1 (Vsub_le_T g.2)
    have hfix : fixL0 (Tl.getD i []) = true := (fixL0_iff hrep).2 (mem_Vsub_iff.1 g.2).2
    refine ⟨⟨i, ?_⟩, ?_⟩
    · simp only [vFin, Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, hfix⟩
    · exact Subtype.ext (Subtype.ext (eq_of_repL (hTel i hi).2 hrep))
  have h := Nat.card_le_card_of_surjective f hsurj
  have h2 : Nat.card vFin = 16 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_vFin]
  exact h.trans h2.le

theorem card_Vsub_eq : Nat.card Vsub = 16 :=
  le_antisymm card_Vsub_le card_Vsub_ge

@[expose] def bitF (s : ℕ) (j : Fin 5) : ZMod 2 := ((s / 2 ^ (j : ℕ) % 2 : ℕ) : ZMod 2)

@[expose] def wtF (s : ℕ) : ZMod 2 :=
  bitF s 0 + bitF s 1 + bitF s 2 + bitF s 3 + bitF s 4

@[expose] def FV (s : ℕ) : Fin 5 → ZMod 2 := fun j => bitF s j + wtF s

theorem FV_mem (s : ℕ) : FV s ∈ Ev := by
  rw [mem_Ev]
  simp only [FV, wtF, Fin.sum_univ_five]
  generalize bitF s 0 = a0
  generalize bitF s 1 = a1
  generalize bitF s 2 = a2
  generalize bitF s 3 = a3
  generalize bitF s 4 = a4
  revert a0 a1 a2 a3 a4
  decide

theorem FV_zero : FV 0 = 0 := by decide +kernel

theorem chkFVxor : ∀ s < 32, ∀ t < 32, FV (s ^^^ t) = FV s + FV t := by
  decide +kernel

theorem chkXlt : ∀ s < 32, ∀ t < 32, s ^^^ t < 32 := by
  decide +kernel

theorem chkFVsub : ∀ s < 32, ∀ t < 32,
    (subProdL L0 s = subProdL L0 t ↔ FV s = FV t) := by
  decide +kernel

theorem chkSubXor : ∀ s < 32, ∀ t < 32,
    compL (subProdL L0 s) (subProdL L0 t) = subProdL L0 (s ^^^ t) := by
  decide +kernel

theorem chkSingle : ∀ j < 5, subProdL L0 (2 ^ j) = tpTab.getD (L0.getD j 0) [] := by
  decide +kernel

theorem chkSub_zero : subProdL L0 0 = List.range 45 := by decide +kernel

@[expose] def ptL (j : Fin 5) : Fin 45 := ⟨L0.getD j 0 % 45, Nat.mod_lt _ (by norm_num)⟩

theorem ptL_val (j : Fin 5) : (ptL j : ℕ) = L0.getD j 0 := by
  have h : ∀ j : Fin 5, L0.getD j 0 < 45 := by decide
  simp only [ptL]
  exact Nat.mod_eq_of_lt (h j)

theorem ptL_inj : Function.Injective ptL := by decide

theorem mem_L0S_ptL (p : Fin 45) : p ∈ L0S ↔ ∃ j : Fin 5, ptL j = p := by
  rw [mem_L0S_iff]
  revert p
  decide

theorem exists_sub {v : Y} (hv : v ∈ Vsub) :
    ∃ s : ℕ, s < 32 ∧ RepL (subProdL L0 s) (v : P45) := by
  obtain ⟨i, hi, hrep⟩ := (mem_T_iff v).1 (Vsub_le_T hv)
  have hf : fixL0 (Tl.getD i []) = true := (fixL0_iff hrep).2 (mem_Vsub_iff.1 hv).2
  have h := chkVprod_true
  simp only [chkVprod, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, beq_iff_eq] at h
  rcases h i hi with h1 | ⟨s, hs, hse⟩
  · rw [hf] at h1
    exact absurd h1 (by simp)
  · exact ⟨s, hs, by rw [hse]; exact hrep⟩

noncomputable def sOf (v : Vsub) : ℕ :=
  Classical.choose (exists_sub v.2)

theorem sOf_spec (v : Vsub) :
    sOf v < 32 ∧ RepL (subProdL L0 (sOf v)) (v : P45) :=
  Classical.choose_spec (exists_sub v.2)

noncomputable def psiF (v : Vsub) : W5 :=
  Multiplicative.ofAdd ⟨FV (sOf v), FV_mem _⟩

theorem psiF_eq (v : Vsub) {s : ℕ} (hs : s < 32)
    (hrep : RepL (subProdL L0 s) (v : P45)) :
    psiF v = Multiplicative.ofAdd ⟨FV s, FV_mem s⟩ := by
  have hlist : subProdL L0 (sOf v) = subProdL L0 s :=
    repL_unique (sOf_spec v).2 hrep
  have hFV : FV (sOf v) = FV s := (chkFVsub _ (sOf_spec v).1 s hs).1 hlist
  show Multiplicative.ofAdd (⟨FV (sOf v), FV_mem _⟩ : ↥Ev) = Multiplicative.ofAdd ⟨FV s, FV_mem s⟩
  exact congrArg _ (Subtype.ext hFV)

theorem psiF_mul (v w : Vsub) :
    psiF (v * w) = psiF v * psiF w := by
  have hv := sOf_spec v
  have hw := sOf_spec w
  have hm : RepL (subProdL L0 (sOf v ^^^ sOf w)) ((v * w : Vsub) : P45) := by
    rw [← chkSubXor (sOf v) hv.1 (sOf w) hw.1]
    exact repL_mul hv.2 hw.2
  rw [psiF_eq (v * w) (chkXlt _ hv.1 _ hw.1) hm, psiF_eq v hv.1 hv.2, psiF_eq w hw.1 hw.2,
    ← ofAdd_add]
  exact congrArg _ (Subtype.ext (chkFVxor _ hv.1 _ hw.1))

theorem psiF_one : psiF 1 = 1 := by
  rw [psiF_eq 1 (s := 0) (by norm_num) (by rw [chkSub_zero]; exact repL_one 45), ← ofAdd_zero]
  exact congrArg _ (Subtype.ext FV_zero)

end CFSG.GH74.QTGen4.U42
