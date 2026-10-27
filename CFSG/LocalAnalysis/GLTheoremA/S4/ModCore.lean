module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_sup_eq_of_commutator_le {p : ℕ} (hp : p.Prime) {W O P : Subgroup G}
    (hP : IsPGroup p P) (hO : ¬ p ∣ Nat.card O) (hOW : O ≤ W)
    (hWO : W ≤ Subgroup.normalizer (O : Set G)) (hPO : P ≤ Subgroup.normalizer (O : Set G))
    (hc : ∀ w ∈ W, ∀ g ∈ P, ⁅w, g⁆ ∈ O) :
    (W ⊓ Subgroup.centralizer (P : Set G)) ⊔ O = W := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm (sup_le inf_le_left hOW)
  intro l hl
  have hmem : ∀ g ∈ P, ∀ o ∈ O, l⁻¹ * (g * (l * o) * g⁻¹) ∈ O := by
    intro g hg o ho
    have h1 : ⁅l⁻¹, g⁆ ∈ O := hc l⁻¹ (W.inv_mem hl) g hg
    have h2 : g * o * g⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hPO hg) o).1 ho
    have h3 : l⁻¹ * (g * (l * o) * g⁻¹) = ⁅l⁻¹, g⁆ * (g * o * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact O.mul_mem h1 h2
  letI act : MulAction P O :=
    { smul := fun g o => ⟨l⁻¹ * ((g : G) * (l * (o : G)) * (g : G)⁻¹), hmem g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (show l⁻¹ * (((1 : P) : G) * (l * (o : G)) *
          ((1 : P) : G)⁻¹) = (o : G) by simp)
      mul_smul := fun g h o => Subtype.ext (show l⁻¹ * (((g * h : P) : G) * (l * (o : G)) *
          ((g * h : P) : G)⁻¹) = l⁻¹ * ((g : G) * (l * (l⁻¹ * ((h : G) * (l * (o : G)) *
          (h : G)⁻¹))) * (g : G)⁻¹) by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨o, ho⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card O hO
  have hfa : ∀ g ∈ P, l⁻¹ * (g * (l * (o : G)) * g⁻¹) = o := fun g hg =>
    congrArg Subtype.val (ho ⟨g, hg⟩)
  have hy : ∀ g ∈ P, g * (l * (o : G)) * g⁻¹ = l * o := by
    intro g hg
    calc g * (l * (o : G)) * g⁻¹ = l * (l⁻¹ * (g * (l * (o : G)) * g⁻¹)) := by group
      _ = l * o := by rw [hfa g hg]
  have hyW : l * (o : G) ∈ W := W.mul_mem hl (hOW o.2)
  have hyC : l * (o : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    calc h * (l * (o : G)) = (h * (l * (o : G)) * h⁻¹) * h := by group
      _ = (l * (o : G)) * h := by rw [hy h hh]
  have hl' : l = (l * (o : G)) * (o : G)⁻¹ := by group
  rw [hl']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hyW, hyC⟩)
    (Subgroup.mem_sup_right (O.inv_mem o.2))

private theorem mem_normalizer_inf_of_mem {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (hA h) (hB h)

theorem exists_le_of_le_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S K O P : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSKO : S ≤ K ⊔ O) (hSO : ¬ S ≤ O) (hO : ¬ p ∣ Nat.card O)
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hSN : S ≤ Subgroup.normalizer (O : Set G))
    (hP : IsPGroup p P) (hPS : P ≤ Subgroup.normalizer ((S ⊔ O : Subgroup G) : Set G))
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hPO : P ≤ Subgroup.normalizer (O : Set G)) :
    ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ P ≤ Subgroup.normalizer (T : Set G) ∧ ¬ T ≤ O := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hS2.exists_card_eq
  have hpS : ¬ p ∣ Nat.card S := by
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hXp : ¬ p ∣ Nat.card (S ⊔ O : Subgroup G) := by
    rw [sup_comm]
    exact CFSG.LocalAnalysis.GLTheoremA.not_dvd_card_sup_of_le_normalizer hp hSN hO hpS
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G, Y = (S ⊔ O) ⊓ K := ⟨_, rfl⟩
  have hYmem : ∀ x, x ∈ Y ↔ x ∈ S ⊔ O ∧ x ∈ K := fun x => by
    simp only [hYdef, Subgroup.mem_inf]
  have hYX : Y ≤ S ⊔ O := fun x hx => ((hYmem x).1 hx).1
  have hYK : Y ≤ K := fun x hx => ((hYmem x).1 hx).2
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) := hYK.trans hKO
  have hYp : ¬ p ∣ Nat.card Y := fun h => hXp (h.trans (Subgroup.card_dvd_of_le hYX))
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) := by
    intro g hg
    rw [hYdef]
    exact mem_normalizer_inf_of_mem (hPS hg) (hPK hg)
  obtain ⟨T₀, hT₀⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_sylow_normalized (r := 2) hPY hP hYp
  refine ⟨(T₀ : Subgroup Y).map Y.subtype, ?_, ?_, hT₀, ?_⟩
  · exact (Subgroup.map_subtype_le (T₀ : Subgroup Y)).trans hYK
  · exact T₀.isPGroup'.map Y.subtype
  intro hTO
  have hSYO : S ≤ Y ⊔ O := by
    intro s hs
    have hsKO : s ∈ K ⊔ O := hSKO hs
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K O hKO] at hsKO
    obtain ⟨k, hk, o, ho, hko⟩ := Set.mem_mul.1 hsKO
    have hk' : k = s * o⁻¹ := by rw [← hko, mul_inv_cancel_right]
    have hkY : k ∈ Y := (hYmem k).2 ⟨by rw [hk']; exact Subgroup.mul_mem_sup hs (O.inv_mem ho), hk⟩
    rw [← hko]
    exact Subgroup.mul_mem_sup hkY ho
  have hSYO' : S ≤ O ⊔ Y := hSYO.trans (le_of_eq (sup_comm Y O))
  have hOY : O ⊔ Y = O ⊔ S := le_antisymm
    (sup_le le_sup_left (hYX.trans (le_of_eq (sup_comm S O))))
    (sup_le le_sup_left hSYO')
  have h1 : Nat.card (O ⊔ S : Subgroup G) * Nat.card (O ⊓ Y : Subgroup G) =
      Nat.card O * Nat.card Y := by
    rw [← hOY]
    exact CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hYO
  have h2 : Nat.card (O ⊔ S : Subgroup G) * Nat.card (O ⊓ S : Subgroup G) =
      Nat.card O * Nat.card S :=
    CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hSN
  have hcardN : Nat.card (O.subgroupOf Y) = Nat.card (O ⊓ Y : Subgroup G) := by
    have hmap : (O.subgroupOf Y).map Y.subtype = O ⊓ Y := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨Subgroup.mem_subgroupOf.1 hy, y.2⟩
      · rintro ⟨hxO, hxY⟩
        exact ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.2 hxO, rfl⟩
    rw [← hmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective).toEquiv
  have hN3 : (O.subgroupOf Y).index * Nat.card (O ⊓ Y : Subgroup G) = Nat.card Y := by
    rw [← hcardN]
    exact Subgroup.index_mul_card _
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hOYpos : 0 < Nat.card (O ⊓ Y : Subgroup G) := Nat.card_pos
  have hA : Nat.card (O ⊔ S : Subgroup G) = Nat.card O * (O.subgroupOf Y).index := by
    refine Nat.eq_of_mul_eq_mul_right hOYpos ?_
    rw [h1, ← hN3]
    ring
  have hB : (O.subgroupOf Y).index * Nat.card (O ⊓ S : Subgroup G) = Nat.card S := by
    refine Nat.eq_of_mul_eq_mul_left hOpos ?_
    calc Nat.card O * ((O.subgroupOf Y).index * Nat.card (O ⊓ S : Subgroup G))
        = (Nat.card O * (O.subgroupOf Y).index) * Nat.card (O ⊓ S : Subgroup G) := by ring
      _ = Nat.card (O ⊔ S : Subgroup G) * Nat.card (O ⊓ S : Subgroup G) := by rw [hA]
      _ = Nat.card O * Nat.card S := h2
  have hdvd : (O.subgroupOf Y).index ∣ 2 ^ n := by
    rw [← hn]
    exact ⟨Nat.card (O ⊓ S : Subgroup G), hB.symm⟩
  have hTN : (T₀ : Subgroup Y) ≤ O.subgroupOf Y := by
    intro t ht
    rw [Subgroup.mem_subgroupOf]
    exact hTO (Subgroup.mem_map_of_mem Y.subtype ht)
  have hdiv : (O.subgroupOf Y).index ∣ (T₀ : Subgroup Y).index := Subgroup.index_dvd_of_le hTN
  have hodd : ¬ 2 ∣ (T₀ : Subgroup Y).index := Sylow.not_dvd_index T₀
  have h2N : ¬ 2 ∣ (O.subgroupOf Y).index := fun h => hodd (h.trans hdiv)
  have hcop : Nat.Coprime (O.subgroupOf Y).index (2 ^ n) :=
    Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2N).symm
  have hidx : (O.subgroupOf Y).index = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  have hNtop : O.subgroupOf Y = ⊤ := Subgroup.index_eq_one.1 hidx
  have hYO' : Y ≤ O := by
    intro y hy
    have hmem : (⟨y, hy⟩ : Y) ∈ O.subgroupOf Y := by
      rw [hNtop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem
  exact hSO (hSYO.trans (sup_le hYO' le_rfl))

end CFSG.LocalAnalysis.GLTheoremA
