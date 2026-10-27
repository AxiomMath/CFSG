module

public import CFSG.RankThree.PartOne.K133.G2Char
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Lvl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Res

public section


namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {τ : Tag} {K : Type} [Field K]

theorem card_parabolicSubgroup_singleton [Finite K] (i : Fin τ.rank) :
    Nat.card (parabolicSubgroup τ K {i}) =
      Nat.card (torusGroup τ K) *
        Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard * (1 + Nat.card K) := by
  rw [(standard_parabolic_cells τ K).2.2.2.2.2.2 {i}]
  congr 1
  have hset : ((parabolicWeylGroup τ {i} : Subgroup (WeylGroup τ)) : Set (WeylGroup τ)) =
      {1, simple τ i} := by
    ext w
    constructor
    · intro hw
      rcases mem_parabolicWeylGroup_singleton hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact simple_mem_parabolicWeylGroup_iff.2 rfl
  have hne : (1 : WeylGroup τ) ≠ simple τ i := by
    intro h
    have h1 : (coxeterSystem τ).length (simple τ i) = 1 := (coxeterSystem τ).length_simple i
    rw [← h, CoxeterSystem.length_one] at h1
    omega
  calc ∑ᶠ w : ↥(parabolicWeylGroup τ {i}), Nat.card K ^ (coxeterSystem τ).length (w : WeylGroup τ)
      = ∑ᶠ w ∈ ((parabolicWeylGroup τ {i} : Subgroup (WeylGroup τ)) : Set (WeylGroup τ)),
          Nat.card K ^ (coxeterSystem τ).length w :=
        finsum_set_coe_eq_finsum_mem (f := fun w => Nat.card K ^ (coxeterSystem τ).length w)
          ((parabolicWeylGroup τ {i} : Subgroup (WeylGroup τ)) : Set (WeylGroup τ))
    _ = ∑ᶠ w ∈ ({1, simple τ i} : Set (WeylGroup τ)), Nat.card K ^ (coxeterSystem τ).length w := by
        rw [hset]
    _ = Nat.card K ^ (coxeterSystem τ).length 1 +
          Nat.card K ^ (coxeterSystem τ).length (simple τ i) := finsum_mem_pair hne
    _ = 1 + Nat.card K := by
        have h1 : (coxeterSystem τ).length (simple τ i) = 1 := (coxeterSystem τ).length_simple i
        rw [CoxeterSystem.length_one, h1]
        simp


theorem torusGroup_pow_seven [Finite K] (hK : Nat.card K = 8) {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) : h ^ 7 = 1 := by
  have hcomm := (triangular_borel_structure.{0, 0} τ K).1
  have hunit : ∀ t : Kˣ, t ^ 7 = 1 := by
    intro t
    have : Fintype K := Fintype.ofFinite K
    have h1 := pow_card_eq_one' (G := Kˣ) (x := t)
    rwa [Nat.card_units, hK] at h1
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨j, t⟩, rfl⟩ := hx
    show (torusEltHom τ K j t) ^ 7 = 1
    rw [← map_pow, hunit t, map_one]
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := hcomm x hx y hy
    rw [hc.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx =>
    rw [inv_pow, ihx, inv_one]

theorem three_not_dvd_card_torusGroup [Finite K] (hK : Nat.card K = 8) :
    ¬ 3 ∣ Nat.card (torusGroup τ K) := by
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL τ K) := inferInstance
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(torusGroup τ K)) 3 h3
  have h7 : ((x : ModGL τ K)) ^ 7 = 1 := torusGroup_pow_seven hK x.2
  have hd : orderOf (x : ModGL τ K) ∣ 7 := orderOf_dvd_of_pow_eq_one h7
  rw [Subgroup.orderOf_coe, hx] at hd
  omega


open scoped MatrixGroups

theorem card_SL2_eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    Nat.card (SL(2, K)) = 504 := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have h : Nat.card (SL(2, K)) = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
        Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
      Nat.mul_div_cancel _ (by omega), mul_comm]
  rw [h, hK]
  norm_num

theorem rankOne_injective [CharP K 2] {ρ : SL2 K →* ModGL τ K}
    (hker : ∀ g ∈ ρ.ker, ∃ l : Kˣ, (l : K) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K)) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨l, hl, hgl⟩ := hker g hg
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have hl1 : (l : K) = 1 := by
    have h0 : ((l : K) - 1) ^ 2 = 0 := by linear_combination hl + (1 - (l : K)) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
  apply Subtype.ext
  rw [hgl, hl1, one_smul]
  rfl


theorem card_le_three_of_le_parabolic_singleton [Finite K] [CharP K 2] (hK : Nat.card K = 8)
    (i : Fin τ.rank) {E : Subgroup (ModGL τ K)} (hE : E ≤ parabolicSubgroup τ K {i})
    (hcomm : ∀ a b : E, a * b = b * a) (h3 : ∀ x : E, x ^ 3 = 1) : Nat.card E ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := parabolicSubgroup τ K {i} with hP
  have hPcard := card_parabolicSubgroup_singleton (τ := τ) (K := K) i
  have h3H := three_not_dvd_card_torusGroup (τ := τ) hK
  have hq : ¬ 3 ∣ Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
    rw [hK]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have h27 : ¬ 27 ∣ Nat.card P := by
    rw [hPcard, hK]
    intro h
    have h' : (3 * 9) ∣ (Nat.card (torusGroup τ K) *
        8 ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) * 9 := by
      simpa [mul_comm, mul_assoc] using h
    have h'' := Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 9) h'
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h'' with h1 | h1
    · exact h3H h1
    · exact hq (by rwa [hK])
  obtain ⟨ρ, -, -, -, -, hrange, hker, -, -⟩ :=
    exceptional_ordinary_rank_one_central_image (τ := τ) (K := K) i
  have hinj : Function.Injective ρ := rankOne_injective hker
  have hρP : ∀ g : SL2 K, ρ g ∈ P := by
    intro g
    have hg : ρ g ∈ ρ.range := ⟨g, rfl⟩
    rw [hrange] at hg
    refine (Subgroup.closure_le P).2 ?_ hg
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact borelGroup_le_parabolicSubgroup _ (xUnit_mem_borelGroup i c)
    · exact yUnit_mem_parabolicSubgroup i c
  let ρP : SL2 K →* ↥P := ρ.codRestrict P hρP
  have hρPinj : Function.Injective ρP := fun a b h => hinj (congrArg Subtype.val h)
  haveI : Finite (SL2 K) := inferInstance
  haveI : Finite ↥P := inferInstance
  obtain ⟨R⟩ : Nonempty (Sylow 3 (SL2 K)) := inferInstance
  have hRcard : Nat.card R = 9 := by
    rw [Sylow.card_eq_multiplicity R, card_SL2_eight hK]
    have h504 : (504 : ℕ).factorization 3 = 2 := by
      rw [Nat.factorization_def _ Nat.prime_three]
      decide +kernel
    rw [h504]
    norm_num
  set R₁ : Subgroup ↥P := (R : Subgroup (SL2 K)).map ρP with hR₁
  have hR₁card : Nat.card R₁ = 9 := by
    rw [hR₁, Subgroup.card_map_of_injective hρPinj, hRcard]
  have hR₁p : IsPGroup 3 R₁ := R.isPGroup'.map ρP
  have hR₁idx : ¬ 3 ∣ R₁.index := by
    intro hdvd
    have hmul := Subgroup.card_mul_index R₁
    rw [hR₁card] at hmul
    apply h27
    rw [← hmul]
    obtain ⟨c, hc⟩ := hdvd
    rw [hc]
    exact ⟨c, by ring⟩
  let S₁ : Sylow 3 ↥P := hR₁p.toSylow hR₁idx
  let EP : Subgroup ↥P := E.subgroupOf P
  have hEPmem : ∀ x : ↥P, x ∈ EP ↔ (x : ModGL τ K) ∈ E := fun x => Subgroup.mem_subgroupOf
  have hEP3 : IsPGroup 3 EP := by
    intro x
    refine ⟨1, ?_⟩
    have h := h3 ⟨(x.1 : ModGL τ K), (hEPmem x.1).1 x.2⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  obtain ⟨Q, hQ⟩ := hEP3.exists_le_sylow
  let ψ : ↥Q ≃* ↥S₁ := Sylow.equiv Q S₁
  have hEPcomm : ∀ a b : EP, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have := hcomm ⟨(a.1 : ModGL τ K), (hEPmem a.1).1 a.2⟩ ⟨(b.1 : ModGL τ K), (hEPmem b.1).1 b.2⟩
    simpa using congrArg Subtype.val this
  have hEP3' : ∀ x : EP, x ^ 3 = 1 := by
    intro x
    have h := h3 ⟨(x.1 : ModGL τ K), (hEPmem x.1).1 x.2⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  let Φ : ↥EP →* SL2 K :=
    (Subgroup.subtype (R : Subgroup (SL2 K))).comp
      ((Subgroup.equivMapOfInjective (R : Subgroup (SL2 K)) ρP hρPinj).symm.toMonoidHom.comp
        (ψ.toMonoidHom.comp (Subgroup.inclusion hQ)))
  have hΦinj : Function.Injective Φ := by
    have e1 : Function.Injective (Subgroup.inclusion hQ) := Subgroup.inclusion_injective hQ
    have e2 : Function.Injective ψ.toMonoidHom := ψ.injective
    have e3 : Function.Injective
        (Subgroup.equivMapOfInjective (R : Subgroup (SL2 K)) ρP hρPinj).symm.toMonoidHom :=
      MulEquiv.injective _
    have e4 : Function.Injective (Subgroup.subtype (R : Subgroup (SL2 K))) :=
      Subtype.val_injective
    exact e4.comp (e3.comp (e2.comp e1))
  have hAcomm : IsMulCommutative Φ.range := by
    refine ⟨⟨fun u v => ?_⟩⟩
    obtain ⟨u, x, rfl⟩ := u
    obtain ⟨v, y, rfl⟩ := v
    apply Subtype.ext
    show Φ x * Φ y = Φ y * Φ x
    rw [← map_mul, ← map_mul, hEPcomm]
  have hA3 : ∀ x ∈ Φ.range, x ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, hEP3' y, map_one]
  have hle := SL2Char2.sl2_card_le_three Φ.range hAcomm hA3
  have hcard1 : Nat.card EP = Nat.card Φ.range := Nat.card_congr (Equiv.ofInjective Φ hΦinj)
  have hcard2 : Nat.card E = Nat.card EP :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).symm.toEquiv
  rw [hcard2, hcard1]
  exact hle


open CFSG.RankThree.PartOne.K133 CFSG.Open

theorem g2_card_le_three [Finite K] [CharP K 2] (hK : Nat.card K = 8)
    {E T : Subgroup ↥(adjointGroup .G2 K)} (hE : IsElemAbelian 3 E) (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    (hEN : E ≤ Subgroup.normalizer (T : Set ↥(adjointGroup .G2 K))) : Nat.card E ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, J, hJ, hk⟩ := exists_conj_le_parabolic_G2 K hT hT2
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  obtain ⟨i, hi⟩ : ∃ i : Fin Tag.G2.rank, ∀ j, j ≠ k0 → j = i := by
    fin_cases k0
    · exact ⟨⟨1, by decide⟩, by decide⟩
    · exact ⟨⟨0, by decide⟩, by decide⟩
  have hJi : J ⊆ {i} := fun j hj => Set.mem_singleton_iff.2 (hi j (fun h => hk0 (h ▸ hj)))
  have hPJ : parabolicSubgroup .G2 K J ≤ parabolicSubgroup .G2 K {i} :=
    parabolicSubgroup_le_parabolicSubgroup_iff.2 hJi
  let ι : ↥(adjointGroup .G2 K) →* ModGL .G2 K :=
    (adjointGroup .G2 K).subtype.comp (MulAut.conj g⁻¹).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (MulAut.conj g⁻¹).injective
  set E' : Subgroup (ModGL .G2 K) := E.map ι with hE'
  have hE'P : E' ≤ parabolicSubgroup .G2 K {i} := by
    rintro _ ⟨x, hx, rfl⟩
    apply hPJ
    have := hk x (hEN hx)
    simpa [ι, MulAut.conj_apply] using this
  have hcomm : ∀ a b : ↥E', a * b = b * a := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show ι a * ι b = ι b * ι a
    rw [← map_mul, ← map_mul]
    have := hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun z : E => ι (z : ↥(adjointGroup .G2 K))) this
  have h3 : ∀ x : ↥E', x ^ 3 = 1 := by
    rintro ⟨_, a, ha, rfl⟩
    apply Subtype.ext
    show (ι a) ^ 3 = 1
    rw [← map_pow, hE.2 a ha, map_one]
  have hcard : Nat.card E = Nat.card E' := (Subgroup.card_map_of_injective hι).symm
  rw [hcard]
  exact card_le_three_of_le_parabolic_singleton hK i hE'P hcomm h3

section G2ResSection

open CFSG.Blueprint TauCeti

theorem g2Res_of_ctx (ctx : LvCtx) : G2Res := by
  intro q hv hq2 hq8 E T hE hT hT1 hN
  have hM : LieModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 0 2 q.exponent :=
    model_G2 ctx hv hq2 (MulEquiv.refl _)
  obtain ⟨-, hm⟩ := LieModel.chevalleyExceptionalModel hM (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  have hK8 : Nat.card K = 8 := by
    have hc := PrimePower.card_def q
    rw [hq2] at hc
    rw [hK, ← hc, hq8]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent) (by
    rw [← Nat.card_eq_fintype_card, hK])
  set E' : Subgroup ↥(adjointGroup .G2 K) := E.map e.toMonoidHom with hE'
  set T' : Subgroup ↥(adjointGroup .G2 K) := T.map e.toMonoidHom with hT'
  have hT'1 : T' ≠ ⊥ := by
    intro h
    apply hT1
    rw [hT'] at h
    exact (Subgroup.map_eq_bot_iff_of_injective T e.injective).mp h
  have hT'p : IsPGroup 2 T' := hT.map e.toMonoidHom
  have hEN : E' ≤ Subgroup.normalizer (T' : Set ↥(adjointGroup .G2 K)) :=
    (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map e.toMonoidHom)
  have hE'abel : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE e.toMonoidHom
  have hcardE : Nat.card E = Nat.card E' :=
    Nat.card_congr (E.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  rw [hcardE]
  exact g2_card_le_three hK8 hE'abel hT'p hT'1 hEN

end G2ResSection

end CFSG.LocalAnalysis.GLTheoremA.HDesc
