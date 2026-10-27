module

public import CFSG.GH74.Conclusion
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs

public section

namespace CFSG.GH74

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordRee ordSuzuki
  gorensteinHarada74Orders)

@[expose] def ModelsFormStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G →
    (∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) →
    GH74Conclusion G

@[expose] def OrderFormStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G →
    (∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) →
    Nat.card G ∈ gorensteinHarada74Orders

theorem mem_orders_of_oddLie {m p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : m = ordG2 (p ^ f) ∨ m = ordTrialityD4 (p ^ f) ∨ m = ordBC 2 (p ^ f) ∨
      (p ^ f % 8 ≠ 1 ∧ m = ordA 3 (p ^ f)) ∨ (p ^ f % 8 ≠ 7 ∧ m = ordTwistedA 3 (p ^ f)) ∨
      (p ^ f % 4 = 3 ∧ m = ordA 4 (p ^ f)) ∨ (p ^ f % 4 = 1 ∧ m = ordTwistedA 4 (p ^ f))) :
    m ∈ gorensteinHarada74Orders :=
  Set.mem_union_left _ <| Set.mem_union_left _ <| Set.mem_union_left _ <|
    Set.mem_union_left _ ⟨p, f, hp, hp2, hf, h⟩

theorem mem_orders_of_ree {m k : ℕ} (hk : 1 ≤ k) (h : m = ordRee (3 ^ (2 * k + 1))) :
    m ∈ gorensteinHarada74Orders :=
  Set.mem_union_left _ <| Set.mem_union_left _ <| Set.mem_union_left _ <|
    Set.mem_union_right _ ⟨k, hk, h⟩

theorem mem_orders_of_small {m : ℕ}
    (h : m = ordA 1 8 ∨ m = ordA 1 16 ∨ m = ordA 2 4 ∨ m = ordSuzuki 8) :
    m ∈ gorensteinHarada74Orders :=
  Set.mem_union_left _ <| Set.mem_union_left _ <| Set.mem_union_right _ h

theorem mem_orders_of_alternating {m n : ℕ} (hn : 8 ≤ n) (hn' : n ≤ 11)
    (h : m = Nat.factorial n / 2) : m ∈ gorensteinHarada74Orders :=
  Set.mem_union_left _ <| Set.mem_union_right _ ⟨n, hn, hn', h⟩

theorem mem_orders_of_sporadic {m : ℕ}
    (h : m = 2 ^ 6 * 3 ^ 3 * 5 * 11 ∨ m = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 ∨
      m = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23 ∨ m = 2 ^ 3 * 3 * 5 * 7 * 11 * 19 ∨
      m = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 ∨ m = 2 ^ 7 * 3 ^ 5 * 5 * 17 * 19 ∨
      m = 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11 ∨ m = 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67) :
    m ∈ gorensteinHarada74Orders :=
  Set.mem_union_right _ h

theorem ne_two_of_pow_mod_four {p f : ℕ} (hf : 1 ≤ f) (h : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) :
    p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  omega

theorem card_mem_gorensteinHarada74Orders
    {G : Type} [Group G] [Finite G]
    (h : GH74Conclusion G) : Nat.card G ∈ gorensteinHarada74Orders := by
  rcases h with ⟨p, f, hp, hp2, hf, h | h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
      ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hf, hq, h⟩ |
      ⟨p, f, hp, hf, hq, h⟩ | (h | h | h | h) | ⟨n, hn, hn', h⟩ |
      (h | h | h | h | h | h | h | h)
  ·
    exact mem_orders_of_oddLie hp hp2 hf (Or.inl (card_of_lieModel_G2 hp2 h))
  ·
    exact mem_orders_of_oddLie hp hp2 hf (Or.inr (Or.inl (card_of_lieModel_trialityD4 hp2 h)))
  ·
    exact mem_orders_of_oddLie hp hp2 hf
      (Or.inr (Or.inr (Or.inl (card_of_lieModel_PSp (by norm_num) hp2 h))))
  ·
    obtain ⟨k, hk, hcard⟩ := card_of_lieModel_twistedG2 h
    exact mem_orders_of_ree hk hcard
  ·
    exact mem_orders_of_oddLie hp hp2 hf
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, card_of_lieModel_PSL (by norm_num) h⟩))))
  ·
    exact mem_orders_of_oddLie hp hp2 hf
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hq, card_of_lieModel_PSU (by norm_num) hp2 h⟩)))))
  ·
    exact mem_orders_of_oddLie hp (ne_two_of_pow_mod_four hf (Or.inr hq)) hf
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hq, card_of_lieModel_PSL (by norm_num) h⟩))))))
  ·
    have hp2 := ne_two_of_pow_mod_four hf (Or.inl hq)
    exact mem_orders_of_oddLie hp hp2 hf
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hq, card_of_lieModel_PSU (by norm_num) hp2 h⟩))))))
  ·
    exact mem_orders_of_small (Or.inl (card_of_lieModel_PSL (by norm_num) h))
  ·
    exact mem_orders_of_small (Or.inr (Or.inl (card_of_lieModel_PSL (by norm_num) h)))
  ·
    exact mem_orders_of_small (Or.inr (Or.inr (Or.inl (card_of_lieModel_PSL (by norm_num) h))))
  ·
    exact mem_orders_of_small (Or.inr (Or.inr (Or.inr (card_of_lieModel_twistedB2 h))))
  ·
    obtain ⟨e⟩ := h
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    refine mem_orders_of_alternating hn hn' ?_
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  · exact mem_orders_of_sporadic (Or.inl (card_of_isSporadic_M12 h))
  · exact mem_orders_of_sporadic (Or.inr (Or.inl (card_of_isSporadic_M22 h)))
  · exact mem_orders_of_sporadic (Or.inr (Or.inr (Or.inl (card_of_isSporadic_M23 h))))
  · exact mem_orders_of_sporadic (Or.inr (Or.inr (Or.inr (Or.inl (card_of_isSporadic_J1 h)))))
  · exact mem_orders_of_sporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (card_of_isSporadic_J2 h))))))
  · exact mem_orders_of_sporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (card_of_isSporadic_J3 h)))))))
  · exact mem_orders_of_sporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (card_of_isSporadic_McL h))))))))
  · exact mem_orders_of_sporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (card_of_isSporadic_Ly h))))))))

theorem orderForm_of_modelsForm
    (h : ModelsFormStatement) : OrderFormStatement := by
  intro G _ _ _ hnonab hrank hsect
  exact card_mem_gorensteinHarada74Orders (h G hnonab hrank hsect)

end CFSG.GH74
