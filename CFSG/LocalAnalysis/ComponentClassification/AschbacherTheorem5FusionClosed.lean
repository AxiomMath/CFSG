module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionBasic

public section

open CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Fusion

open SectionSix Involution

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem two_power_of_mem {X : Subgroup G} (hX : IsPGroup 2 X) {x : G} (hx : x ∈ X) :
    ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem overlapClosure_le (hC : Counterexample G D r Abar) {i₀ i₁ : Fin r}
    {T₀ T₁ : Subgroup G} (hT₀ : T₀ ≤ aschbacherThm5Preimage D (Abar i₀))
    (hT₁ : T₁ ≤ aschbacherThm5Preimage D (Abar i₁)) (h₀ : IsPGroup 2 T₀)
    (h₁ : IsPGroup 2 T₁) :
    overlapClosure T₀ T₁ ≤ Subgroup.normalizer (D : Set G) := by
  have hyp := hC.hyp
  have hfac : ∀ X ∈ ({T₀, T₁} : Set (Subgroup G)),
      ∃ a, X ≤ aschbacherThm5Preimage D (Abar a) ∧ IsPGroup 2 X := by
    intro X hX
    rcases hX with rfl | hX
    · exact ⟨i₀, hT₀, h₀⟩
    · rw [Set.mem_singleton_iff] at hX
      subst hX
      exact ⟨i₁, hT₁, h₁⟩
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨X, hX, Y, hY, hXY⟩
  obtain ⟨a, hXa, hX2⟩ := hfac X hX
  obtain ⟨b, hYb, -⟩ := hfac Y hY
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXY
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.mp hx
  have htX : g * x * g⁻¹ ∈ X := (mem_rightConjugate_iff X g x).mp hxX
  have ht1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1'
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨a', ha'⟩ := exists_ne hC a
  obtain ⟨b', hb'⟩ := exists_ne hC b
  have hcent : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar a')) (g * x * g⁻¹) :=
    cross_factor_centralizes D Abar hyp.hcomm a' a ha' _ (hXa htX)
  have hcent' : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar b')) (g⁻¹ * (g * x * g⁻¹) * g) := by
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [this]
    exact cross_factor_centralizes D Abar hyp.hcomm b' b hb' _ (hYb hxY)
  refine hyp.hi a' b' (g * x * g⁻¹) g (two_power_of_mem hX2 htX) ?_ hcent hcent'
  rw [hC.center, Subgroup.mem_bot]
  exact ht1

theorem inf_factor_eq {k : Fin r} {T S : Subgroup G}
    (hT : IsSylowOf 2 T (aschbacherThm5Preimage D (Abar k))) (hTS : T ≤ S)
    (hS : IsPGroup 2 S) : S ⊓ aschbacherThm5Preimage D (Abar k) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hT.eq_of_le (le_inf hTS hT.le) inf_le_right (hS.to_le inf_le_left)

theorem normalizer_le (hC : Counterexample G D r Abar) {k : Fin r} {T : Subgroup G}
    (hT : IsSylowOf 2 T (aschbacherThm5Preimage D (Abar k))) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hC.hyp
  have hTne : T ≠ ⊥ := by
    intro hbot
    have hcard := hT.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have heven := Involution.factor_even hyp k
    have hv : (Nat.card (aschbacherThm5Preimage D (Abar k))).factorization 2 = 0 :=
      (Nat.pow_eq_one.mp hcard.symm).resolve_left (by norm_num)
    rw [Nat.factorization_eq_zero_iff] at hv
    rcases hv with h | h | h
    · exact h Nat.prime_two
    · exact h (even_iff_two_dvd.mp heven)
    · have := Nat.card_pos (α := aschbacherThm5Preimage D (Abar k))
      omega
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨k', hk'⟩ := exists_ne hC k
  intro n hn
  have hnw : n⁻¹ * w * n ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem hn) w).mp
      hw
    simpa using this
  refine hyp.hi k' k' w n (two_power_of_mem hT.isPGroup hw) ?_
    (cross_factor_centralizes D Abar hyp.hcomm k' k hk' w (hT.le hw))
    (cross_factor_centralizes D Abar hyp.hcomm k' k hk' _ (hT.le hnw))
  rw [hC.center, Subgroup.mem_bot]
  exact hw1'

omit [Finite G] in
@[expose] noncomputable def factorQuot (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    aschbacherThm5Preimage D Ā →* Ā :=
  ((QuotientGroup.mk' (aschbacherThm5OddCore D)).comp
    (Subgroup.inclusion (preimage_le D Ā))).codRestrict Ā (fun a =>
      (mem_preimage_iff D Ā (Subgroup.inclusion (preimage_le D Ā) a)).mp a.2)

omit [Finite G] in
theorem factorQuot_coe (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D))
    (a : aschbacherThm5Preimage D Ā) :
    ((factorQuot Ā a : Ā) : D ⧸ aschbacherThm5OddCore D) =
      QuotientGroup.mk' (aschbacherThm5OddCore D) (Subgroup.inclusion (preimage_le D Ā) a) :=
  rfl

omit [Finite G] in
theorem factorQuot_surjective (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    Function.Surjective (factorQuot Ā) := by
  rintro ⟨q, hq⟩
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) q
  exact ⟨⟨d, (mem_preimage_iff D Ā d).mpr hq⟩, Subtype.ext rfl⟩

theorem exists_sylow_image (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (aschbacherThm5Preimage D Ā)) :
    ∃ P : Sylow 2 Ā, Nonempty (T ≃* (P : Subgroup Ā)) ∧
      ∀ p ∈ (P : Subgroup Ā), ∃ t ∈ T, ∃ htD : t ∈ D,
        (p : D ⧸ aschbacherThm5OddCore D) =
          QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨t, htD⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hT
  set φ := factorQuot Ā
  have hφ : Function.Surjective φ := factorQuot_surjective Ā
  refine ⟨Q.mapSurjective hφ, ?_, ?_⟩
  ·
    set ψ := φ.comp (Q : Subgroup (aschbacherThm5Preimage D Ā)).subtype
    have hψ : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : QuotientGroup.mk' (aschbacherThm5OddCore D)
          (Subgroup.inclusion (preimage_le D Ā) (x : aschbacherThm5Preimage D Ā)) = 1 :=
        congrArg Subtype.val hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hodd := Subgroup.orderOf_dvd_natCard (aschbacherThm5OddCore D) h1
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') x
      rw [Subgroup.mem_bot]
      have hxo : orderOf x = orderOf (Subgroup.inclusion (preimage_le D Ā)
          (x : aschbacherThm5Preimage D Ā)) := by
        rw [← Subgroup.orderOf_coe x]
        exact (orderOf_injective _ (Subgroup.inclusion_injective _) _).symm
      rw [← hxo, hn] at hodd
      have : n = 0 := by
        by_contra h0
        have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 h0
        exact (Nat.not_even_iff_odd.mpr (oddCore_odd D)) (even_iff_two_dvd.mpr (h2.trans hodd))
      rw [this, pow_zero, orderOf_eq_one_iff] at hn
      exact hn
    have hrange : ψ.range = (Q : Subgroup (aschbacherThm5Preimage D Ā)).map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    refine ⟨((MulEquiv.subgroupCongr hQ).symm.trans ((Q : Subgroup _).equivMapOfInjective _
      (aschbacherThm5Preimage D Ā).subtype_injective).symm).trans
        ((MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange))⟩
  · intro p hp
    rw [Sylow.coe_mapSurjective] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, ?_, (preimage_le D Ā q.2), rfl⟩
    rw [← hQ]
    exact ⟨q, hq, rfl⟩

theorem false_of_sylow_le (hyp : Hyp61 G D r Abar) {k l : Fin r} (hkl : k ≠ l)
    {T : Subgroup G} (hT : IsSylowOf 2 T (aschbacherThm5Preimage D (Abar k)))
    (hTl : T ≤ aschbacherThm5Preimage D (Abar l)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, -, hP⟩ := exists_sylow_image (Abar k) hT
  have hperf : Group.IsPerfect (Abar k) := semisimple_perfect _ (hyp.hsemisimple k)
  have : Nontrivial (Abar k) := semisimple_nontrivial _ (hyp.hsemisimple k)
  have hPc : (P : Subgroup (Abar k)) ≤ Subgroup.center (Abar k) := by
    intro p hp
    obtain ⟨t, htT, htD, hpt⟩ := hP p hp
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : D ⧸ aschbacherThm5OddCore D) * p = p * y
    rw [hpt]
    exact hyp.hcomm k l hkl y y.2 _ ((mem_preimage_iff D _ ⟨t, htD⟩).mp (hTl htT))
  have h8 := AschbacherToolkit.central_sylow_commutator P hPc P.isPGroup'
  rw [hperf.commutator_eq_top, inf_top_eq] at h8
  have hab : commutator (P : Subgroup (Abar k)) = ⊥ := by
    rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hPc y.2) x)
  rw [hab, Subgroup.map_bot, inf_bot_eq] at h8
  have heven : Even (Nat.card (Abar k)) := even_card_of_perfect
  exact P.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven) h8

theorem mem_union_of_conj_mem (hyp : Hyp61 G D r Abar)
    (hfin : ∀ i j m : Fin r, i ≠ j → m ≠ i → m = j) {i₀ i₁ : Fin r} (h01 : i₀ ≠ i₁)
    {T₀ T₁ : Subgroup G} (hT₀ : IsSylowOf 2 T₀ (aschbacherThm5Preimage D (Abar i₀)))
    (hT₁ : IsSylowOf 2 T₁ (aschbacherThm5Preimage D (Abar i₁))) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hT₀S : T₀ ≤ S) (hT₁S : T₁ ≤ S) {x y : G}
    (hx : x ∈ (T₀ : Set G) ∪ T₁) (hy : y ∈ Subgroup.normalizer (D : Set G))
    (hxy : y⁻¹ * x * y ∈ S) : y⁻¹ * x * y ∈ (T₀ : Set G) ∪ T₁ := by
  have hfac : ∃ a, x ∈ aschbacherThm5Preimage D (Abar a) := by
    rcases hx with hx | hx
    · exact ⟨i₀, hT₀.le hx⟩
    · exact ⟨i₁, hT₁.le hx⟩
  obtain ⟨a, hxa⟩ := hfac
  obtain ⟨b, hb⟩ := hyp.hperm y⁻¹ ((Subgroup.normalizer (D : Set G)).inv_mem hy) a
  have hxb : y⁻¹ * x * y ∈ aschbacherThm5Preimage D (Abar b) := by
    rw [← hb]
    refine ⟨x, hxa, ?_⟩
    simp
  by_cases hb0 : b = i₀
  · subst hb0
    left
    rw [← inf_factor_eq hT₀ hT₀S hS]
    exact Subgroup.mem_inf.mpr ⟨hxy, hxb⟩
  · have hb1 := hfin i₀ i₁ b h01 hb0
    subst hb1
    right
    rw [← inf_factor_eq hT₁ hT₁S hS]
    exact Subgroup.mem_inf.mpr ⟨hxy, hxb⟩

theorem closed_in_normalizer (hin : SectionSevenInputs) (hC : Counterexample G D r Abar)
    (hfin : ∀ i j m : Fin r, i ≠ j → m ≠ i → m = j) {i₀ i₁ : Fin r} (h01 : i₀ ≠ i₁)
    {T₀ T₁ : Subgroup G} (hT₀ : IsSylowOf 2 T₀ (aschbacherThm5Preimage D (Abar i₀)))
    (hT₁ : IsSylowOf 2 T₁ (aschbacherThm5Preimage D (Abar i₁))) (S : Sylow 2 G)
    (hT₀S : T₀ ≤ S) (hT₁S : T₁ ≤ S) {k : Fin r} {T : Subgroup G}
    (hT : IsSylowOf 2 T (aschbacherThm5Preimage D (Abar k))) :
    relStronglyClosed ⊤ ((T₀ : Set G) ∪ T₁)
      ((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G)) := by
  have hyp := hC.hyp
  intro x hx y _ hxy
  obtain ⟨hxyS, hxyN⟩ := Subgroup.mem_inf.mp hxy
  by_cases hx1 : x = 1
  · left
    rw [hx1, mul_one, inv_mul_cancel]
    exact T₀.one_mem
  by_cases hyH : y ∈ Subgroup.normalizer (D : Set G)
  · exact mem_union_of_conj_mem hyp hfin h01 hT₀ hT₁ S.isPGroup' hT₀S hT₁S hx hyH hxyS
  exfalso
  obtain ⟨a, hxa, X, hxX, hX2⟩ : ∃ a, x ∈ aschbacherThm5Preimage D (Abar a) ∧
      ∃ X : Subgroup G, x ∈ X ∧ X ≤ aschbacherThm5Preimage D (Abar a) ∧ IsPGroup 2 X := by
    rcases hx with hx | hx
    · exact ⟨i₀, hT₀.le hx, T₀, hx, hT₀.le, hT₀.isPGroup⟩
    · exact ⟨i₁, hT₁.le hx, T₁, hx, hT₁.le, hT₁.isPGroup⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hX2.2) ⟨x, hxX⟩
  rw [Subgroup.orderOf_mk] at hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hx1 hn
  set x₀ := x ^ (2 ^ (n - 1)) with hx₀
  have hx₀2 : orderOf x₀ = 2 := by
    rw [hx₀, orderOf_pow_of_dvd (by positivity) (by rw [hn]; exact Nat.pow_dvd_pow 2 (by omega)),
      hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  have hx₀a : x₀ ∈ aschbacherThm5Preimage D (Abar a) := Subgroup.pow_mem _ hxa _
  obtain ⟨a', ha'⟩ := exists_ne hC a
  have hx₀c : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar a')) x₀ :=
    cross_factor_centralizes D Abar hyp.hcomm a' a ha' x₀ hx₀a
  have ht₀ : y⁻¹ * x₀ * y = (y⁻¹ * x * y) ^ (2 ^ (n - 1)) := by
    rw [hx₀]
    have := (conj_pow (a := y⁻¹) (b := x) (i := 2 ^ (n - 1))).symm
    simpa using this
  have ht₀N : y⁻¹ * x₀ * y ∈ Subgroup.normalizer (T : Set G) := by
    rw [ht₀]
    exact Subgroup.pow_mem _ hxyN _
  have ht₀H := normalizer_le hC hT ht₀N
  rcases lemma_8_1 hin hC hx₀2 hx₀c with h1 | ⟨-, -, hmove⟩
  · apply hyH
    have hmem : x₀ ∈ rightConjugate (Subgroup.normalizer (D : Set G)) y⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv]
      exact ht₀H
    simpa using (Subgroup.normalizer (D : Set G)).inv_mem ((h1 y⁻¹).mp hmem)
  · have hmk := hmove y hyH ht₀H k
    obtain ⟨m, hm⟩ := hyp.hperm _ ht₀H k
    have hmk' : m ≠ k := by
      rintro rfl
      exact hmk hm
    apply false_of_sylow_le hyp hmk'.symm hT
    rw [← hm]
    intro w hw
    refine ⟨(MulAut.conj (y⁻¹ * x₀ * y))⁻¹ w, hT.le ?_, by simp; group⟩
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (T : Set G)).inv_mem ht₀N) w).mp hw
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem lemma_8_4 (hin : SectionSevenInputs) (hC : Counterexample G D r Abar) {i₀ i₁ : Fin r}
    (h01 : i₀ ≠ i₁) {T₀ T₁ : Subgroup G}
    (hT₀ : IsSylowOf 2 T₀ (aschbacherThm5Preimage D (Abar i₀)))
    (hT₁ : IsSylowOf 2 T₁ (aschbacherThm5Preimage D (Abar i₁))) (S : Sylow 2 G)
    (hT₀S : T₀ ≤ S) (hT₁S : T₁ ≤ S) :
    relStronglyClosed (overlapClosure T₀ T₁) ((T₀ : Set G) ∪ T₁)
        (overlapClosure T₀ T₁ ⊓ S) ∧
      relStronglyClosed ⊤ ((T₀ : Set G) ∪ T₁)
        ((S : Subgroup G) ⊓ Subgroup.normalizer (T₀ : Set G)) ∧
      relStronglyClosed ⊤ ((T₀ : Set G) ∪ T₁)
        ((S : Subgroup G) ⊓ Subgroup.normalizer (T₁ : Set G)) := by
  have hr2 := hin.lemma_8_2 hC
  have hfin : ∀ i j m : Fin r, i ≠ j → m ≠ i → m = j := by
    intro i j m hij hmi
    rw [Ne, Fin.ext_iff] at hij hmi
    rw [Fin.ext_iff]
    omega
  refine ⟨?_, closed_in_normalizer hin hC hfin h01 hT₀ hT₁ S hT₀S hT₁S hT₀,
    closed_in_normalizer hin hC hfin h01 hT₀ hT₁ S hT₀S hT₁S hT₁⟩
  intro x hx y hy hxy
  exact mem_union_of_conj_mem hC.hyp hfin h01 hT₀ hT₁ S.isPGroup' hT₀S hT₁S hx
    (overlapClosure_le hC hT₀.le hT₁.le hT₀.isPGroup hT₁.isPGroup hy) (Subgroup.mem_inf.mp hxy).2

end Fusion

end CFSG.ComponentClassification.AschbacherTheorem5
