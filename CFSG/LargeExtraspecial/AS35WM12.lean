module

public import CFSG.LargeExtraspecial.AS35WCheck
public import CFSG.LargeExtraspecial.AS35WList
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12

public section

namespace CFSG.LargeExtraspecial

open Subgroup Equiv CFSG.ClassicalInvolution CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.Blueprint

namespace AS35W

@[expose] def m12X : Perm (Fin 12) := swap 1 8 * swap 2 9 * swap 4 10 * swap 6 7

@[expose] def m12Word : List Bool :=
  [true, true, false, true, false, true, false, true, false, true, false, true, true, false,
    true, true, false, true, true, false, true, false, true]

@[expose] def m12C : Perm (Fin 12) := (m12Word.map fun b => if b then m12gB else m12gA).prod

set_option maxRecDepth 100000 in
theorem m12X_mem : m12X ∈ permClosureList m12UGens1 20 := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12C_conj : m12C * m12Rep1 * m12C⁻¹ = m12X := by decide +kernel

set_option maxRecDepth 100000 in
theorem m12X_ne : m12X ≠ m12Rep1 := by decide +kernel

theorem m12C_mem : m12C ∈ m12Certificate.originalSubgroup := by
  refine m12Certificate.originalSubgroup.list_prod_mem fun g hg => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
  cases b
  · exact m12_gens_mem m12gA (by simp)
  · exact m12_gens_mem m12gB (by simp)

theorem m12W2Input :
    M12W2Input := by
  intro X _ _ hX z hz
  exfalso
  obtain ⟨e⟩ := hX
  set H := m12Certificate.originalSubgroup
  have e' : X ≃* H := e.trans (MulEquiv.subgroupCongr m12Certificate_originalSubgroup.symm)
  have hz' := hz.map e'
  obtain ⟨hcov, hcent⟩ := m12_cover_and_centralizers
  have hw2 : orderOf ((e' z : H) : Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hz'.orderOf_eq
  obtain ⟨d, hd, c, hcH, hwc⟩ := hcov _ (by simp) hw2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  have hdH : ∀ {r : Perm (Fin 12)}, (e' z : Perm (Fin 12)) = c * r * c⁻¹ → r ∈ H := by
    intro r hr
    have : r = c⁻¹ * (e' z : Perm (Fin 12)) * c := by rw [hr]; group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hcH) (e' z).2) hcH
  have hconj : ∀ {r : Perm (Fin 12)} (hr : (e' z : Perm (Fin 12)) = c * r * c⁻¹),
      MulAut.conj (⟨c, hcH⟩ : H)⁻¹ (e' z) = ⟨r, hdH hr⟩ := by
    intro r hr
    apply Subtype.ext
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hr]
    group
  rcases hd with rfl | rfl
  ·
    dsimp only at hwc
    have hz'' := hz'.map (MulAut.conj (⟨c, hcH⟩ : H)⁻¹)
    rw [hconj hwc] at hz''
    have hQ1 := (m12_oddcore_cent1).1
    have h1 : centralizerIn H m12Rep1 = m12CentQ1.originalSubgroup :=
      hcent (m12Rep1, m12CentQ1.originalSubgroup) (by simp)
    refine hz''.false_of_check (KL := enumerationTab m12CentQ1) ?_ m12_U1_check m12X_mem
      m12X_ne m12C_mem m12C_conj
    intro g
    rw [mem_enumerationTab_iff m12CentQ1 hQ1 g, ← h1]
    simp only [centralizerIn, Subgroup.mem_inf, mem_centralizer_singleton_iff]
  ·
    dsimp only at hwc
    have h2 : centralizerIn H m12Rep2 = m12CentQ2.originalSubgroup :=
      hcent (m12Rep2, m12CentQ2.originalSubgroup) (by simp)
    have hc240 : Nat.card m12CentQ2.originalSubgroup = 240 := (m12_rep_data2).2.2.2.1
    have hcard : Nat.card (centralizer ({e' z} : Set H)) = 240 := by
      have hic : IsConj (⟨m12Rep2, hdH hwc⟩ : H) (e' z) :=
        isConj_iff.2 ⟨(⟨c, hcH⟩ : H), Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hwc.symm)⟩
      rw [← card_centralizer_of_isConj hic, card_centralizer_subtype (hdH hwc)]
      rw [show (H ⊓ centralizer ({m12Rep2} : Set (Perm (Fin 12)))) = centralizerIn H m12Rep2
        from rfl, h2, hc240]
    have hH : Nat.card H = 95040 := by
      rw [show H = NativeSporadic.M12 from m12Certificate_originalSubgroup, m12_card]
    have := hz'.pow_dvd (k := 6) (by rw [hH]; norm_num)
    rw [hcard] at this
    revert this
    decide

end AS35W

end CFSG.LargeExtraspecial
