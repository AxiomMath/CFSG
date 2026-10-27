module

public import CFSG.LieType.SeitzGeneration.ExcPrimeSplit
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcTorusRank

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
  CFSG.Open CFSG.AGLEmbeddingD2

theorem false_of_inner_plane_of_rankLE1 {C : Type*} [Group C] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) (hr : RankLE1 p C)
    {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hin : E ≤ (MulAut.conj : C →* MulAut C).range) : False := by
  have hmap : (E.comap (MulAut.conj : C →* MulAut C)).map (MulAut.conj : C →* MulAut C) = E :=
    Subgroup.map_comap_eq_self hin
  have hE₀ : IsElemAbelian p (E.comap (MulAut.conj : C →* MulAut C)) :=
    isElemAbelian_comap_of_injective _ hinj hE
  have hcard : Nat.card (E.comap (MulAut.conj : C →* MulAut C)) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hc]
  have h := hr _ hE₀
  rw [hcard] at h
  have h2 := hp.two_le
  nlinarith

section Centreless


theorem conj_injective_cat_F4 (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨.F4 q, hv⟩ →* MulAut (Cat ⟨.F4 q, hv⟩)) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := .F4) (K := K)))

theorem conj_injective_cat_E6 (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨.E6 q, hv⟩ →* MulAut (Cat ⟨.E6 q, hv⟩)) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := .E6) (K := K)))

theorem conj_injective_cat_E7 (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨.E7 q, hv⟩ →* MulAut (Cat ⟨.E7 q, hv⟩)) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := .E7) (K := K)))

theorem conj_injective_cat_E8 (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨.E8 q, hv⟩ →* MulAut (Cat ⟨.E8 q, hv⟩)) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := .E8) (K := K)))

end Centreless

theorem degCount_F4_eq_two {e : ℕ} (h : degCount Tag.F4 e = 2) : e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.F4) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.F4 e = 2 → e = 3 ∨ e = 4 ∨ e = 6 := by decide
  exact key e h30 h

theorem degCount_E6_eq_two {e : ℕ} (h : degCount Tag.E6 e = 2) : e = 4 ∨ e = 6 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E6) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.E6 e = 2 → e = 4 ∨ e = 6 := by decide
  exact key e h30 h

theorem degCount_E7_eq_two {e : ℕ} (h : degCount Tag.E7 e = 2) : e = 4 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E7) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.E7 e = 2 → e = 4 := by decide
  exact key e h30 h

theorem degCount_E8_eq_two {e : ℕ} (h : degCount Tag.E8 e = 2) :
    e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E8) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.E8 e = 2 → e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by decide
  exact key e h30 h

theorem dvd_sq_add_one_of_orderOf_eq_four {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 4) : p ∣ q ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h4 : ((q : ZMod p)) ^ 4 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h2 : ((q : ZMod p)) ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hm : ((q : ZMod p) ^ 2 - 1) * ((q : ZMod p) ^ 2 + 1) = 0 := by linear_combination h4
  have hz : (q : ZMod p) ^ 2 + 1 = 0 := (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 h2)
  exact (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) p).1 (by push_cast; exact hz)

@[expose] def ClassRange (c : PrimePower → LieTypeIndex) (X : PrimePower → Prop) (e : ℕ) :
    LieTypeIndex → ℕ → Prop :=
  fun d p => 5 ≤ p ∧ ∃ q : PrimePower, d = c q ∧ X q ∧ orderOf ((q.card : ℕ) : ZMod p) = e

theorem seitzExcAnisotropicForAt_geFive_of_classes {c : PrimePower → LieTypeIndex}
    {X : PrimePower → Prop} {F : LieTypeIndex → Prop} {τ : Tag} {S : ℕ → Prop}
    (hchar : ∀ q, (c q).characteristic = q.p)
    (hinj : ∀ (q : PrimePower) (hv : (c q).Valid),
      Function.Injective (MulAut.conj : Cat ⟨c q, hv⟩ →* MulAut (Cat ⟨c q, hv⟩)))
    (h1 : ∀ (q : PrimePower) (hv : (c q).Valid) (p : ℕ), p.Prime → p ≠ q.p →
      degCount τ (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1 → RankLE1 p (Cat ⟨c q, hv⟩))
    (h3 : ∀ (q : PrimePower) (hv : (c q).Valid) (p : ℕ), p.Prime → 3 < p → p ≠ q.p →
      3 ≤ degCount τ (orderOf ((q.card : ℕ) : ZMod p)) → ¬ RankLE2 p (Cat ⟨c q, hv⟩))
    (h2 : ∀ e, degCount τ e = 2 → S e)
    (hS : ∀ e, S e → SeitzExcAnisotropicForAt F (ClassRange c X e)) :
    SeitzExcAnisotropicForAt F fun d p => 5 ≤ p ∧ ∃ q, d = c q ∧ X q := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨hp5, q, hdq, hX⟩, hr, hn⟩
  obtain rfl : d = c q := hdq
  have hpq : p ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  rcases Nat.lt_or_ge (degCount τ (orderOf ((q.card : ℕ) : ZMod p))) 3 with hlt | hge
  · rcases (by omega : degCount τ (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1 ∨
        degCount τ (orderOf ((q.card : ℕ) : ZMod p)) = 2) with hle | heq
    · exact (false_of_inner_plane_of_rankLE1 hp (hinj q hv) (h1 q hv p hp hpq hle) hE hc hin).elim
    · exact hS _ (h2 _ heq) ⟨c q, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hin, hF, ⟨hp5, q, rfl, hX, rfl⟩, hr, hn⟩
  · exact absurd hr (h3 q hv p hp (by omega) hpq hge)

end CFSG.LieType.SeitzGeneration
