module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeEnd

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Prod

variable {Y : Type} [Group Y]

def prodCentral (K A : Subgroup Y) (hcomm : ∀ k ∈ K, ∀ a ∈ A, k * a = a * k) : Subgroup Y where
  carrier := {x | ∃ k ∈ K, ∃ a ∈ A, x = k * a}
  mul_mem' := by
    rintro _ _ ⟨k, hk, a, ha, rfl⟩ ⟨k', hk', a', ha', rfl⟩
    refine ⟨k * k', K.mul_mem hk hk', a * a', A.mul_mem ha ha', ?_⟩
    calc k * a * (k' * a') = k * (a * k') * a' := by group
      _ = k * (k' * a) * a' := by rw [hcomm k' hk' a ha]
      _ = k * k' * (a * a') := by group
  one_mem' := ⟨1, K.one_mem, 1, A.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨k, hk, a, ha, rfl⟩
    refine ⟨k⁻¹, K.inv_mem hk, a⁻¹, A.inv_mem ha, ?_⟩
    have h := hcomm k⁻¹ (K.inv_mem hk) a⁻¹ (A.inv_mem ha)
    calc (k * a)⁻¹ = a⁻¹ * k⁻¹ := by group
      _ = k⁻¹ * a⁻¹ := h.symm

variable {K A : Subgroup Y} {hcomm : ∀ k ∈ K, ∀ a ∈ A, k * a = a * k}

theorem le_prodCentral_left : K ≤ prodCentral K A hcomm := fun k hk =>
  ⟨k, hk, 1, A.one_mem, by simp⟩

theorem le_prodCentral_right : A ≤ prodCentral K A hcomm := fun a ha =>
  ⟨1, K.one_mem, a, ha, by simp⟩

theorem prodCentral_le {W : Subgroup Y} (hK : K ≤ W) (hAW : A ≤ W) :
    prodCentral K A hcomm ≤ W := by
  rintro _ ⟨k, hk, a, ha, rfl⟩
  exact W.mul_mem (hK hk) (hAW ha)

theorem mem_normalizer_prodCentral {t : Y} (htK : t ∈ Subgroup.normalizer (K : Set Y))
    (htA : t ∈ Subgroup.normalizer (A : Set Y)) :
    t ∈ Subgroup.normalizer (prodCentral K A hcomm : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, hk, a, ha, rfl⟩
    refine ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp htK k).mp hk, t * a * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp htA a).mp ha, by group⟩
  · rintro ⟨k, hk, a, ha, he⟩
    refine ⟨t⁻¹ * k * t, ?_, t⁻¹ * a * t, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htK) k).mp hk
      simpa using this
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htA) a).mp ha
      simpa using this
    · calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
        _ = t⁻¹ * k * t * (t⁻¹ * a * t) := by rw [he]; group

theorem commutator_prodCentral_le (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ⁅prodCentral K A hcomm, prodCentral K A hcomm⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨k, hk, a, ha, rfl⟩ _ ⟨k', hk', a', ha', rfl⟩
  rw [commutatorElement_def]
  have c1 := hcomm k' hk' a ha
  have c2 := hcomm k⁻¹ (K.inv_mem hk) a' ha'
  have c4 := hA a ha a' ha'
  have e : k * a * (k' * a') * (k * a)⁻¹ * (k' * a')⁻¹ = k * k' * k⁻¹ * k'⁻¹ := by
    calc k * a * (k' * a') * (k * a)⁻¹ * (k' * a')⁻¹
        = k * (a * k') * a' * a⁻¹ * k⁻¹ * a'⁻¹ * k'⁻¹ := by group
      _ = k * (k' * a) * a' * a⁻¹ * k⁻¹ * a'⁻¹ * k'⁻¹ := by rw [c1]
      _ = k * k' * (a * a') * a⁻¹ * k⁻¹ * a'⁻¹ * k'⁻¹ := by group
      _ = k * k' * (a' * a) * a⁻¹ * k⁻¹ * a'⁻¹ * k'⁻¹ := by rw [c4]
      _ = k * k' * (a' * k⁻¹) * a'⁻¹ * k'⁻¹ := by group
      _ = k * k' * (k⁻¹ * a') * a'⁻¹ * k'⁻¹ := by rw [c2]
      _ = k * k' * k⁻¹ * k'⁻¹ := by group
  rw [e]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')

theorem le_or_le_of_layer {W K₀ : Subgroup Y} (hAW : A ≤ W)
    (hAc : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a) (hAder : A ≤ ⁅W, W⁆) {t : Y}
    (htA : t ∈ Subgroup.normalizer (A : Set Y))
    (hlay : ∀ Y₀ : Subgroup Y, A ≤ Y₀ → Y₀ ≤ W → t ∈ Subgroup.normalizer (Y₀ : Set Y) →
      Y₀ = A ∨ Y₀ = W)
    (hK₀W : K₀ ≤ W) (htK₀ : t ∈ Subgroup.normalizer (K₀ : Set Y)) : K₀ ≤ A ∨ W ≤ K₀ := by
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hAc a ha b (hAW hb)
  have hc₀ : ∀ k ∈ K₀, ∀ a ∈ A, k * a = a * k := fun k hk a ha => (hAc a ha k (hK₀W hk)).symm
  rcases hlay (prodCentral K₀ A hc₀) le_prodCentral_right (prodCentral_le hK₀W hAW)
      (mem_normalizer_prodCentral htK₀ htA) with h | h
  · exact Or.inl (h ▸ le_prodCentral_left)
  · have hder : ⁅W, W⁆ ≤ K₀ := h ▸ commutator_prodCentral_le hAab
    exact Or.inr (h ▸ prodCentral_le le_rfl (hAder.trans hder))

end Prod

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem relIndex_normalizer_le_three (h : D1PhaseThree 3 P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hrank : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (h3d : ¬ Nat.Coprime 3 (Nat.card Lb)) (W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
    (W ⊓ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex W ≤ 3 := by
  by_contra hlt
  push Not at hlt
  set NA := (W ⊓ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))).subgroupOf W with hNA
  have hidx : (W ⊓ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex W =
      Nat.card (↥W ⧸ NA) := by
    rw [Subgroup.relIndex, Subgroup.index]
  rw [hidx] at hlt
  have : Fintype (↥W ⧸ NA) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hlt
  let e : Fin 4 → ↥W ⧸ NA := fun i =>
    (Fintype.equivFin (↥W ⧸ NA)).symm (Fin.castLE (by omega) i)
  have he : Function.Injective e := fun i j hij =>
    Fin.castLE_injective _ ((Fintype.equivFin (↥W ⧸ NA)).symm.injective hij)
  let g : Fin 4 → ↥M ⧸ CFSG.pCore 2 ↥M := fun j => ((Quotient.out (e j) : W) : _)
  refine false_of_four_conj_components h hB3 hrank hperf hLb h3d g ?_
  intro i j hij
  simp only at hij
  have hn : (g j)⁻¹ * g i ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have heq : Lb.map (MulAut.conj ((g j)⁻¹ * g i)).toMonoidHom = Lb := by
      rw [map_conj_mul, hij, ← map_conj_mul, inv_mul_cancel, map_conj_one]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have hmem : (Quotient.out (e j))⁻¹ * Quotient.out (e i) ∈ NA := by
    refine Subgroup.mem_subgroupOf.mpr ⟨W.mul_mem (W.inv_mem (Quotient.out (e j)).2)
      (Quotient.out (e i)).2, ?_⟩
    simpa [g] using hn
  have heq : (e j) = (e i) := by
    rw [← Quotient.out_eq (e j), ← Quotient.out_eq (e i)]
    exact QuotientGroup.eq.mpr hmem
  exact he heq.symm

theorem le_centralizer_threeComponents_of_pair (hKB : KFactBlockThreeCentCoprime)
    (h3 : D1PhaseThree 3 P M H R) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hrank : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {zb : ↥M ⧸ CFSG.pCore 2 ↥M} (hzb3 : zb ^ 3 = 1)
    (hZ : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → D = ⊥)
    {A W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hAW : A ≤ W)
    (hAc : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a) (hAder : A ≤ ⁅W, W⁆) (hidx : 4 ≤ A.relIndex W)
    {t : ↥M ⧸ CFSG.pCore 2 ↥M} (ht6 : Nat.Coprime 6 (orderOf t))
    (htz : t ∈ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (htW : t ∈ Subgroup.normalizer (W : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (htA : t ∈ Subgroup.normalizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hnt : ∃ w ∈ W, t * w * t⁻¹ * w⁻¹ ∉ A)
    (hlay : ∀ Y₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ Y₀ → Y₀ ≤ W →
      t ∈ Subgroup.normalizer (Y₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → Y₀ = A ∨ Y₀ = W)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (h3d : ¬ Nat.Coprime 3 (Nat.card Lb)) :
    W ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have htL := mem_normalizer_of_coprime_six h3 hB3 hrank hperf hLb h3d ht6
  have hWN : W ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have htK₀ : t ∈ Subgroup.normalizer
        ((W ⊓ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :
          Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨htW, Subgroup.le_normalizer htL⟩
    rcases le_or_le_of_layer hAW hAc hAder htA hlay inf_le_left htK₀ with h | h
    · exfalso
      have hdvd := Subgroup.relIndex_dvd_of_le_left W h
      have hpos : (W ⊓ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex W ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd
      have := relIndex_normalizer_le_three h3 hB3 hrank hperf hLb h3d W
      omega
    · exact h.trans inf_le_right
  obtain ⟨L, hL, rfl⟩ := (weakSBlock_or_coprime_of_component h3 hperf hLb).resolve_right h3d
  have htC := mem_centralizer_weakSBlock_of_kFact hKB h3 h85 h93 hD2 hperf hzb3 hZ hL htL htz ht6
  have hNC : Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have htC₀ : t ∈ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htW, hNC htL⟩
  rcases le_or_le_of_layer hAW hAc hAder htA hlay inf_le_left htC₀ with h | h
  · exfalso
    obtain ⟨w, hw, hwA⟩ := hnt
    exact hwA (h ⟨W.mul_mem ((Subgroup.mem_normalizer_iff.mp htW w).mp hw) (W.inv_mem hw),
      conj_mul_inv_mem_centralizer htC (hWN hw)⟩)
  · exact h.trans inf_le_right

end CFSG.AGLEmbedding
