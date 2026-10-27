module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIL2P
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvLie

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Equiv Equiv.Perm Subgroup CFSG.GorensteinWalter CFSG.EvenSporadicStandard.HSStd.HOv

theorem mul_eq_one_of_card_two {G : Type*} [Group G] (h : Nat.card G = 2) {g k : G} (hg : g ≠ 1)
    (hk : k ≠ 1) : g * k = 1 := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : G)).1 h
  have hgy := huniq g hg
  have hky := huniq k hk
  have hy2 : y ^ 2 = 1 := by
    have := pow_card_eq_one' (G := G) (x := y)
    rwa [h] at this
  rw [hgy, hky, ← sq]
  exact hy2

theorem false_of_good_triple_psl_two_twentyfive {D : Type} [Group D] [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) {a b : D}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (ea : Nonempty (↥(centralizer ({a} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eb : Nonempty (↥(centralizer ({b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eab : Nonempty (↥(centralizer ({a * b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (hL : CFSG.Blueprint.LieModel ↥(commutator D) .PSL 2 5 2) : False := by
  have hM := statedClassicalModel_of_lieModel (by norm_num) hL
  have hordS := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
    ↥(commutator D) 2 5 2 hM).1
  have hcardS : Nat.card ↥(commutator D) = 7800 := by rw [hordS]; decide
  have hC := centralizer_eq_bot_of_normal_of_card hZ ha ea (commutator D)
    (by rw [hcardS]; norm_num) (by rw [hcardS]; norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e1⟩⟩ := hM
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK25 : Nat.card K = 5 ^ 2 := hK
  have hodd : IsOddPrimePower (Nat.card K) := ⟨5, 2, by norm_num, by decide, by norm_num, hK25⟩
  have h3 : 3 < Nat.card K := by rw [hK25]; norm_num
  have hchar : CharP K 5 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK25])
  have hAut : Nat.card (RingAut K) = 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (by norm_num : Nat.Prime 5) K
      hK25).1
  let φ : ↥(commutator D) ≃* PSL2 K :=
    e1.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  let Φ : PGammaL2 K ≃* MulAut (PSL2 K) := MulEquiv.ofBijective
    (pGammaL2ToMulAutPSL2 K hodd h3)
    ⟨pGammaL2ToMulAutPSL2_injective K hodd h3, pGammaL2ToMulAutPSL2_surjective K hK25 hodd h3⟩
  let ι : D →* PGammaL2 K := Φ.symm.toMonoidHom.comp (HL34.actionHom (commutator D) φ)
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : HL34.actionHom (commutator D) φ d = 1 := by
      have : Φ.symm (HL34.actionHom (commutator D) φ d) = 1 := hd
      exact Φ.symm.injective (this.trans (map_one _).symm)
    have h2 := (HL34.actionHom_eq_one_iff (commutator D) φ d).1 h1
    rw [hC, mem_bot] at h2
    exact h2
  let π : D →* RingAut K := (SemidirectProduct.rightHom : PGammaL2 K →* RingAut K).comp ι
  have key : ∀ {x : D}, orderOf x = 2 →
      Nonempty (↥(centralizer ({x} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)) →
        π x ≠ 1 := by
    intro x hx ex hπx
    have hx2 : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
    have h5 : 5 ∣ Nat.card ↥(centralizer ({x} : Set D)) := by
      rw [card_centralizer_of_good ex]; norm_num
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer ({x} : Set D))) 5 h5
    have hy5 : orderOf (y' : D) = 5 := by rw [Subgroup.orderOf_coe]; exact hy'
    have hxy : x * (y' : D) = (y' : D) * x := mem_centralizer_iff.1 y'.2 x rfl
    have hπy : π (y' : D) = 1 := by
      have h5' : π (y' : D) ^ 5 = 1 := by
        rw [← map_pow, ← hy5, pow_orderOf_eq_one, map_one]
      have h2 : ∀ g : RingAut K, g ^ 2 = 1 := fun g => by
        have := pow_card_eq_one' (G := RingAut K) (x := g)
        rwa [hAut] at this
      have : π (y' : D) = π (y' : D) ^ 5 := by
        calc π (y' : D) = π (y' : D) * (π (y' : D) ^ 2) ^ 2 := by rw [h2, mul_one]
          _ = π (y' : D) ^ 5 := by group
      rw [this, h5']
    have hrange : ∀ g : D, π g = 1 → ∃ G₀ : PGL2 K, SemidirectProduct.inl G₀ = ι g := by
      intro g hg
      have : ι g ∈ (SemidirectProduct.rightHom : PGammaL2 K →* RingAut K).ker := hg
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at this
      exact this
    obtain ⟨Y₀, hY₀⟩ := hrange _ hπy
    obtain ⟨X₀, hX₀⟩ := hrange _ hπx
    have hι1 : ∀ g : D, g ≠ 1 → ι g ≠ 1 := fun g hg h => hg (hι (h.trans (map_one ι).symm))
    refine false_of_commute_five_two (y := Y₀) (z := X₀) ?_ ?_ ?_ ?_ ?_
    · apply SemidirectProduct.inl_injective (N := PGL2 K) (G := RingAut K)
      rw [map_pow, hY₀, ← map_pow, ← hy5, pow_orderOf_eq_one, map_one, map_one]
    · rintro rfl
      apply hι1 (y' : D) (fun h => by rw [h, orderOf_one] at hy5; omega)
      rw [← hY₀, map_one]
    · apply SemidirectProduct.inl_injective (N := PGL2 K) (G := RingAut K)
      rw [map_mul, hX₀, ← map_mul, hx2, map_one, map_one]
    · rintro rfl
      apply hι1 x hx1
      rw [← hX₀, map_one]
    · apply SemidirectProduct.inl_injective (N := PGL2 K) (G := RingAut K)
      rw [map_mul, map_mul, hX₀, hY₀, ← map_mul, ← map_mul, hxy]
  have h1 := key ha ea
  have h2 := key hb eb
  have h3' := key (orderOf_mul_eq_two ha hb hab hcomm) eab
  exact h3' (by rw [map_mul]; exact mul_eq_one_of_card_two hAut h1 h2)

end CFSG.EvenSporadicStandard.HSStd.HFI
