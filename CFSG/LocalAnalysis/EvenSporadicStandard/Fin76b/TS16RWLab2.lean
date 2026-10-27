module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWLab

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

section Facts

@[expose] def Dlist : List ℕ := [0, 21, 32, 53, 64, 85, 96, 117]

theorem mem_Dlist {c : ℕ} : c ∈ Dlist ↔ (c = 0 ∨ c = 21 ∨ c = 32 ∨ c = 53 ∨ c = 64 ∨ c = 85 ∨
    c = 96 ∨ c = 117) := by
  simp [Dlist]

theorem Dset_ix_fwd : ∀ i < 8, ixP i 0 ∈ Dlist := by decide +kernel

theorem Dset_ix_bwd : ∀ c < 128, c ∈ Dlist → ∃ i < 8, ixP i 0 = c := by decide +kernel

theorem commE_Dset : ∀ c < 32, ∀ d < 128, d ∈ Dlist → mulC c d = mulC d c := by decide +kernel

theorem cent_Dset : ∀ x < 128, (∀ d < 128, d ∈ Dlist → mulC x d = mulC d x) → x < 32 := by
  decide +kernel

theorem decD_lt32 : ∀ c < 32, decD c = 0 := by decide +kernel

theorem decD_32 : decD 32 = 1 := by decide

theorem decD_53 : decD 53 = 1 := by decide

end Facts

section Lab2

variable {M : Type*} [Group M] {D E : Subgroup M} {eD : D ≃* DihedralGroup 4} {t : M}
  {eltE : ℕ → M}

namespace DECtx

variable (hctx : DECtx D E eD t eltE)

include hctx

theorem t_ne : t ≠ 1 := by
  intro h
  apply eT_ne
  apply hctx.L.inj eT eT_lt 0 (by norm_num)
  rw [hctx.L.at_tI, hctx.L.one, h]

theorem a_ne_inv : sElt eD 1 ≠ (sElt eD 1)⁻¹ := by
  intro h
  have h1 : sElt eD 1 * sElt eD 1 = 1 := by
    calc sElt eD 1 * sElt eD 1 = sElt eD 1 * (sElt eD 1)⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  rw [sElt_mul eD (by norm_num) (by norm_num), show dMul 1 1 = 2 by decide, ← hctx.t_eq] at h1
  exact hctx.t_ne h1

theorem lab_inj0 {a b : ℕ} (ha : a < 128) (hb : b < 128)
    (h : labD eD eltE a = labD eD eltE b) : a = b :=
  hctx.tabLab.inj a ha b hb h

theorem lab_32 : labD eD eltE 32 = sElt eD 1 := by
  show sElt eD (decD 32) * eltE (32 % 32) = _
  rw [decD_32, show 32 % 32 = 0 by norm_num, hctx.L.one, mul_one]

theorem lab_53 : labD eD eltE 53 = (sElt eD 1)⁻¹ := by
  show sElt eD (decD 53) * eltE (53 % 32) = _
  rw [decD_53, show 53 % 32 = 21 by norm_num, show (21 : ℕ) = eT from rfl, hctx.L.at_tI,
    hctx.t_eq, sElt_mul eD (by norm_num) (by norm_num), show dMul 1 2 = 3 by decide, sElt_three]

theorem lab_E {c : ℕ} (hc : c < 32) : labD eD eltE c = eltE c := by
  show sElt eD (decD c) * eltE (c % 32) = _
  rw [decD_lt32 c hc, sElt_zero, one_mul, Nat.mod_eq_of_lt hc]

theorem lab_mem_D {c : ℕ} (hc : c < 128) : labD eD eltE c ∈ D ↔ c ∈ Dlist := by
  constructor
  · intro hcD
    obtain ⟨i, hi, hsi⟩ := dih_surj (eD ⟨_, hcD⟩)
    have hsE : labD eD eltE c = sElt eD i := by
      unfold sElt
      rw [hsi]
      simp
    obtain ⟨-, -, hlt, -⟩ := redP_facts i hi 0 (by norm_num)
    have h2 : labD eD eltE (ixP i 0) = sElt eD i := by
      rw [hctx.lab_ixP hi (by norm_num), hctx.L.one, mul_one]
    have hc2 : c = ixP i 0 := hctx.lab_inj0 hc hlt (hsE.trans h2.symm)
    rw [hc2]
    exact Dset_ix_fwd i hi
  · intro hc'
    obtain ⟨i, hi, rfl⟩ := Dset_ix_bwd c hc hc'
    rw [hctx.lab_ixP hi (by norm_num), hctx.L.one, mul_one]
    exact sElt_mem eD i

theorem lab_mem_E {c : ℕ} (hc : c < 128) : labD eD eltE c ∈ E ↔ c < 32 := by
  constructor
  · intro hcE
    obtain ⟨k, hk, hke⟩ := hctx.L.surj _ hcE
    have h1 : labD eD eltE k = labD eD eltE c := by rw [hctx.lab_E hk, hke]
    exact hctx.lab_inj0 (hk.trans (by norm_num)) hc h1 ▸ hk
  · intro hc'
    rw [hctx.lab_E hc']
    exact hctx.L.mem c hc'


end DECtx

end Lab2

end CFSG.EvenSporadicStandard.Fin76b.W16
