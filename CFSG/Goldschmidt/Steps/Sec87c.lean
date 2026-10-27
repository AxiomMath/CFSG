module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8LemmaA
import CFSG.Walter.Bender1970.S38.NotCyclic
import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem three_le_pRank (hset : GoldSetting G S A) : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, -, hBel, hB8⟩ := hset.rank
  have hBp : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using hBel.2 _ x.2)⟩
  obtain ⟨h, -, hh⟩ := Walter.exists_conj_le_sylow_of_isPGroup S le_top le_top hBp
  have hle : conjSub h B ≤ S := fun z hz => by
    have := hh _ (mem_conjSub.mp hz)
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hk' : Nat.card (conjSub h B) = 2 ^ k := by rw [card_conjSub, hk]
  have hel : IsElemAbelian 2 (conjSub h B) :=
    CFSG.SectionRank.isElemAbelian_map hBel (MulAut.conj h⁻¹).toMonoidHom
  have h3 : 3 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact h3.trans (CFSG.SectionRank.le_pRank one_lt_two hle hel hk')

theorem pRank_le_three (h4 : Nat.card A = 4)
    (hC1 : ∀ u ∈ (S : Subgroup G), ∀ v ∈ (S : Subgroup G), u ^ 2 = 1 → v ^ 2 = 1 →
      u * v = v * u → u ∉ A → v ∉ A → u * v ∈ A) :
    CFSG.Open.pRank 2 (S : Subgroup G) ≤ 3 := by
  classical
  refine CFSG.SectionRank.pRank_le one_lt_two fun E hES hE => ?_
  have hEA : Nat.card (E ⊓ A : Subgroup G) ≤ 4 := h4 ▸ Subgroup.card_le_of_le inf_le_right
  by_cases hEle : E ≤ A
  · exact (Subgroup.card_le_of_le hEle).trans (by rw [h4]; norm_num)
  obtain ⟨u, huE, huA⟩ := Set.not_subset.mp hEle
  have hu2 : u ^ 2 = 1 := hE.2 u huE
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  let f : E → (E ⊓ A : Subgroup G) × Bool := fun v =>
    if hv : (v : G) ∈ A then (⟨v, v.2, hv⟩, false)
    else (⟨u * v, E.mul_mem huE v.2, hC1 u (hES huE) v (hES v.2) hu2 (hE.2 v v.2)
      (hcomm u huE v v.2) huA hv⟩, true)
  have hf : Function.Injective f := by
    intro v w hvw
    by_cases hv : (v : G) ∈ A <;> by_cases hw : (w : G) ∈ A <;> simp [f, hv, hw] at hvw
    · exact Subtype.ext (Subtype.mk.inj hvw)
    · exact Subtype.ext (mul_left_cancel (Subtype.mk.inj hvw))
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  calc Nat.card E ≤ Nat.card (E ⊓ A : Subgroup G) * 2 := h1
    _ ≤ 4 * 2 := Nat.mul_le_mul_right _ hEA
    _ = 2 ^ 3 := by norm_num

theorem exists_conj_normalizer_of_le {b g : G}
    (hSb : (S : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G))
    (hSc : (S : Subgroup G) ≤ Subgroup.centralizer ({g⁻¹ * b * g} : Set G)) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n⁻¹ * b * n = g⁻¹ * b * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := g⁻¹ * b * g with hc
  set K := Subgroup.centralizer ({c} : Set G) with hK
  have hS'K : Quasithin.conjSubgroup (S : Subgroup G) g ≤ K := by
    intro x hx
    rw [Quasithin.mem_conjSubgroup_iff] at hx
    show x ∈ Subgroup.centralizer ({c} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxb := Subgroup.mem_centralizer_singleton_iff.mp (hSb hx)
    calc x * c = g⁻¹ * ((g * x * g⁻¹) * b) * g := by rw [hc]; group
      _ = g⁻¹ * (b * (g * x * g⁻¹)) * g := by rw [hxb]
      _ = c * x := by rw [hc]; group
  obtain ⟨d, hdK, y, hy1, hy2⟩ := Quasithin.exists_conj_le_sylow_of_isPGroup S hSc hS'K
    S.isPGroup' (S.isPGroup'.map _)
  have hcard : ∀ {z : G}, Quasithin.conjSubgroup (S : Subgroup G) z ≤ S →
      z ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := fun {z} hz => by
    have heq : Quasithin.conjSubgroup (S : Subgroup G) z = S :=
      Subgroup.eq_of_le_of_card_ge hz (by
        rw [Quasithin.conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj z⁻¹).injective])
    exact Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp heq
  have hyN := hcard hy1
  rw [Quasithin.conjSubgroup_conjSubgroup] at hy2
  have hgdy := hcard hy2
  refine ⟨g * d, ?_, ?_⟩
  · have := Subgroup.mul_mem _ hgdy (Subgroup.inv_mem _ hyN)
    simpa [mul_assoc] using this
  · have hdc := Subgroup.mem_centralizer_singleton_iff.mp hdK
    calc (g * d)⁻¹ * b * (g * d) = d⁻¹ * c * d := by rw [hc]; group
      _ = c := by rw [mul_assoc, ← hdc, ← mul_assoc, inv_mul_cancel, one_mul]

theorem normalizer_le_normalizer (hset : GoldSetting G S A) :
    Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.normalizer (A : Set G) :=
  fun g hg => mem_normalizer_of_conjSub_le hset fun z hz => by
    have h1 := hset.le (mem_conjSub.mp hz)
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp h1

theorem exists_mem_normalizer_sylow (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) :
    ∃ x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), x⁻¹ * a * x ∈ A ∧ x⁻¹ * a * x ≠ a := by
  obtain ⟨n, hn, hnc⟩ := exists_not_mem_centralizer hset h4
  obtain ⟨hca, -⟩ := conj_conj_eq_mul hset h4 hn hnc ha ha1
  obtain ⟨x, -, hxS, hxa⟩ := exists_conj_normalizer hset h4 (N := ⊤) le_top ha
    (Subgroup.mem_top n⁻¹) (by simpa using conj_mem hn ha)
  refine ⟨x, hxS, ?_, ?_⟩
  · rw [hxa]
    simpa using conj_mem hn ha
  · rw [hxa]
    simpa using hca

end CFSG.Goldschmidt.Sec8
