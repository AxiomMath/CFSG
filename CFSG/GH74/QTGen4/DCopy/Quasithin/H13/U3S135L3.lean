module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135Gen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma3

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem hyp1281One_of_F4 (h1332 : Stmt13_3_2_F4) {T L V : Subgroup G} (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) [IsMulCommutative ↥V]
    (hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1)
    (hnat : BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1) : Hyp1281One G T L V 3 where
  hyp := hyp1223_of_F4 h1332 hH hV
  n_mem := Or.inl rfl
  quot := nonempty_equiv_SL32_of_lieModel hlin
  natural := ⟨inferInstance, hnat⟩
  not_linear := fun hL => hH.not_excluded (Or.inr (Or.inl (Or.inl hL)))
  not_alt9 := fun hA => hH.not_excluded (Or.inr (Or.inr (Or.inl hA)))
  not_m24 := fun hM => hH.not_excluded
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM))))))

theorem l32_centralizer_not_le_F4 (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G} (hH : QTH13 G T L)
    (h : Hyp1281One G T L V 3) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v₀, hv₀, hv₀1, hM⟩ := exists_centralizer_not_le_F4 h12213 hH h.hyp
  obtain ⟨-, hsq, -⟩ := h.card_sq
  have hc : ∀ w ∈ V, w ≠ 1 → Nat.card (zpowers w) = 2 ^ 1 := fun w hw hw1 => by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (hsq w hw) hw1
  obtain ⟨l, hl, hlZ⟩ := lemma12_8_3_two h (zpowers_le.2 hv₀) (zpowers_le.2 hv)
    (hc v₀ hv₀ hv₀1) (hc v hv hv1)
  have h1 : l * v * l⁻¹ ∈ zpowers v₀ := by
    rw [← SteinbergBS.mem_conjugate_iff, hlZ]
    exact mem_zpowers v
  rcases eq_one_or_eq_of_mem_zpowers (hsq v₀ hv₀) h1 with h2 | h2
  · exfalso
    apply hv1
    calc v = l⁻¹ * (l * v * l⁻¹) * l := by group
      _ = 1 := by rw [h2]; group
  · exact not_centralizer_le_of_conj (inv_mem (le_normalizer hl)) (by rw [← h2]; group) hM

theorem l32_isTSub_V1_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} (h : Hyp1281One G T L V 3) :
    IsTSub T V (fsuV1 T V) 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVT, -⟩ := h.hyp.le_and_normalizes_F4 h1222
  obtain ⟨-, hsq, -⟩ := h.card_sq
  obtain ⟨V₁, hV₁V, hV₁c, hTV₁⟩ := exists_v1_of_hyp1281One_F4 h1222 h
  have : Nontrivial ↥V₁ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hV₁c]; norm_num)
  obtain ⟨⟨w, hw⟩, hw1⟩ := exists_ne (1 : ↥V₁)
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hw2 : w ^ 2 = 1 := hsq w (hV₁V hw)
  have hV₁w : zpowers w = V₁ := eq_of_le_of_card_ge (zpowers_le.2 hw)
    (le_of_eq (by rw [hV₁c, Nat.card_zpowers, orderOf_eq_prime hw2 hw1', pow_one]))

  have hwT : w ∈ centralizer (T : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    have h1 : t * w * t⁻¹ ∈ zpowers w := by
      rw [hV₁w]
      exact (mem_normalizer_iff.1 (hTV₁ ht) w).1 hw
    rcases eq_one_or_eq_of_mem_zpowers hw2 h1 with h2 | h2
    · exfalso
      apply hw1'
      calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
        _ = 1 := by rw [h2]; group
    · calc t * w = t * w * t⁻¹ * t := by group
        _ = w * t := by rw [h2]
  have hwV1 : w ∈ fsuV1 T V :=
    ⟨hV₁V hw, mem_quasithinOmegaOneCenter_iff.2 ⟨hVT (hV₁V hw), hwT, hw2⟩⟩

  have hTb : ∀ b ∈ fsuV1 T V, T ≤ normalizer ((zpowers b : Subgroup G) : Set G) := by
    intro b hb t ht
    obtain ⟨-, hbT, -⟩ := mem_quasithinOmegaOneCenter_iff.1 hb.2
    refine centralizer_le_normalizer_zpowers b ?_
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hbT) t ht
  have hV1 : fsuV1 T V = zpowers w := by
    refine le_antisymm (fun b hb => ?_) (zpowers_le.2 hwV1)
    rcases tinv_comparable_of_hyp1281One_F4 h1222 h (zpowers_le.2 hb.1) hV₁V (hTb b hb) hTV₁ with
      hle | hle
    · rw [hV₁w]
      exact hle (mem_zpowers b)
    · rcases eq_one_or_eq_of_mem_zpowers (hsq b hb.1) (hle hw) with h2 | h2
      · exact absurd h2 hw1'
      · rw [← h2]
        exact mem_zpowers w
  refine ⟨inf_le_left, ?_, ?_⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime hw2 hw1', pow_one]
  · rw [hV1]
    exact hTb w hwV1

end CFSG.Quasithin.H13.U3
