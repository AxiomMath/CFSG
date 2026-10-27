module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSixSetup

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal

open SectionSix SectionSix.BarTools RankOne SixConj SixTools

namespace Six

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem IsQ8Pair.q_mul_p' {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) :
    q * p = p * q * p ^ 2 := by
  rw [h.q_mul_p, h.inv_eq, mul_assoc, ← h.mul_comm_sq, ← mul_assoc]

theorem lift_q8Pair {Y : Subgroup G} (hY2 : IsPGroup 2 Y)
    (hYH : Y ≤ Subgroup.normalizer (D : Set G)) {p q : Bar D} (hp : p ∈ bar D Y)
    (hq : q ∈ bar D Y) (h : IsQ8Pair p q) :
    ∃ P Q : Subgroup.normalizer (D : Set G), (P : G) ∈ Y ∧ (Q : G) ∈ Y ∧ toBar D P = p ∧
      toBar D Q = q ∧ IsQ8Pair (P : G) (Q : G) := by
  set e := barEquiv hY2 hYH with hedef
  have h' : IsQ8Pair (⟨p, hp⟩ : bar D Y) ⟨q, hq⟩ :=
    IsQ8Pair.of_map (bar D Y).subtype (bar D Y).subtype_injective h
  have h'' := h'.map (Y.subtype.comp e.symm.toMonoidHom) (Y.subtype_injective.comp e.symm.injective)
  refine ⟨⟨_, hYH (e.symm ⟨p, hp⟩).2⟩, ⟨_, hYH (e.symm ⟨q, hq⟩).2⟩, (e.symm ⟨p, hp⟩).2,
    (e.symm ⟨q, hq⟩).2, ?_, ?_, h''⟩
  · have h1 := barEquiv_apply hY2 hYH (e.symm ⟨p, hp⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  · have h1 := barEquiv_apply hY2 hYH (e.symm ⟨q, hq⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm

theorem commute_of_bar {Y : Subgroup G} (hY2 : IsPGroup 2 Y) {x y : Subgroup.normalizer (D : Set G)}
    (hx : (x : G) ∈ Y) (hy : (y : G) ∈ Y) (h : toBar D x * toBar D y = toBar D y * toBar D x) :
    (x : G) * y = y * x := by
  have h1 : x * y = y * x := toBar_injOn_of_isPGroup hY2 (Y.mul_mem hx hy) (Y.mul_mem hy hx)
    (by rw [map_mul, map_mul, h])
  exact congrArg Subtype.val h1

theorem caseShared2 {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hC : Counterexample G D 2 Abar)
    (hrank : ∀ m, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar m)) ≤ 1)
    {U : Subgroup G} {p q : Fin 2 → Bar D} (hP : ∀ j, PairAt D U Abar j (p j) (q j))
    (hz : p 0 ^ 2 = p 1 ^ 2) : False := by
  have hW : aschbacherThm5Preimage D (Abar 0) ⊓ aschbacherThm5Preimage D (Abar 1) ≤
      Subgroup.normalizer (D : Set G) :=
    inf_le_left.trans ((preimage_le D _).trans Subgroup.le_normalizer)
  have hzW : p 0 ^ 2 ∈ bar D (aschbacherThm5Preimage D (Abar 0) ⊓
      aschbacherThm5Preimage D (Abar 1)) := by
    rw [bar_inf_of_core_le (core_le_preimage D _)]
    exact ⟨Subgroup.pow_mem _ (hP 0).2.1 2, hz ▸ Subgroup.pow_mem _ (hP 1).2.1 2⟩
  obtain ⟨s, hsW, hso, -⟩ := exists_lift_involution hW hzW
    (by rw [← pow_mul]; exact (hP 0).1.1) (hP 0).1.2.2.2
  refine hC.fails (conclusion_of_shared_involution hC.hyp hrank hso fun i => ?_)
  fin_cases i
  · exact hsW.1
  · exact hsW.2

theorem lift_elemAbelian_eight {W : Subgroup G} (hWH : W ≤ Subgroup.normalizer (D : Set G))
    {Eb : Subgroup (Bar D)} (hEb : IsElemAbelian 2 Eb) (hEb8 : Nat.card Eb = 8)
    (hEbW : Eb ≤ bar D W) :
    ∃ E : Subgroup G, E ≤ W ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ bar D E = Eb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEb2 : IsPGroup 2 Eb := IsPGroup.of_card (n := 3) (by rw [hEb8]; norm_num)
  obtain ⟨E, hEW, hE2, hEEb⟩ := lift_two_subgroup hWH hEb2 hEbW
  have hEH := hEW.trans hWH
  have e := barEquiv hE2 hEH
  rw [hEEb] at e
  refine ⟨E, hEW, isElemAbelian_of_equiv e hEb, ?_, hEEb⟩
  rw [← card_bar_of_isPGroup hE2 hEH, hEEb, hEb8]

theorem caseSharedRank (hC : Counterexample G D r Abar) (hin : SectionSixInputs) {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {U : Subgroup G} (hU : U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g))
    (hrank : ∀ m, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar m)) ≤ 1)
    {p q : Fin r → Bar D} (hP : ∀ j, PairAt D U Abar j (p j) (q j)) {j k l : Fin r}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hz : p j ^ 2 = p k ^ 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hpq_j, hpj, hqj, hpjC, hqjC, hzj, -⟩ := hP j
  obtain ⟨hpq_k, hpk, hqk, hpkC, hqkC, -, -⟩ := hP k
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU.2.2.1]; norm_num)
  set Aj := aschbacherThm5Preimage D (Abar j) with hAjdef
  set Ak := aschbacherThm5Preimage D (Abar k) with hAkdef
  have hcross : ∀ {x y : Bar D}, x ∈ bar D Aj → y ∈ bar D Ak → x * y = y * x :=
    fun hx hy => cross_commute hC.hyp hjk hx hy
  set z := p j ^ 2 with hzdef
  have hzAj : z ∈ bar D Aj := Subgroup.pow_mem _ hpj 2
  have hzc : ∀ y ∈ bar D Aj, z * y = y * z := fun y hy =>
    ((Subgroup.mem_centralizer_iff.mp hzj) y hy).symm
  have hz2 : z ^ 2 = 1 := by rw [hzdef, ← pow_mul]; exact hpq_j.1
  have hz1 : z ≠ 1 := hpq_j.2.2.2
  have hkey : ∀ y : Bar D, y * p j = p j * y → y⁻¹ * q j ∈ bar D Ak → False := by
    intro y hy hyq
    apply hpq_j.not_commute
    have h1 : (y⁻¹ * q j) * p j = p j * (y⁻¹ * q j) := (hcross hpj hyq).symm
    calc q j * p j = y * ((y⁻¹ * q j) * p j) := by group
      _ = y * (p j * (y⁻¹ * q j)) := by rw [h1]
      _ = (y * p j) * (y⁻¹ * q j) := by group
      _ = (p j * y) * (y⁻¹ * q j) := by rw [hy]
      _ = p j * q j := by group
  have hpjAk : p j ∉ bar D Ak := fun h => hpq_j.not_commute (hcross hqj h)
  set b := p j * p k with hbdef
  set c := q j * q k with hcdef
  have hb2 : b ^ 2 = 1 := by
    rw [hbdef, (show Commute (p j) (p k) from hcross hpj hpk).mul_pow, ← hz, ← pow_two, hz2]
  have hc2 : c ^ 2 = 1 := by
    rw [hcdef, (show Commute (q j) (q k) from hcross hqj hqk).mul_pow, hpq_j.2.1, hpq_k.2.1,
      ← hz, ← pow_two, hz2]
  have hb1 : b ≠ 1 := by
    intro h
    apply hpjAk
    rw [eq_inv_of_mul_eq_one_left h]
    exact Subgroup.inv_mem _ hpk
  have hzb : z ≠ b := by
    intro h
    apply hpjAk
    have h1 : p j = p k := mul_left_cancel (a := p j) (by rw [← pow_two]; exact h)
    rw [h1]
    exact hpk
  have hzbc : z * b = b * z := by
    rw [hbdef, ← mul_assoc, hzc _ hpj, mul_assoc, hcross hzAj hpk, ← mul_assoc]
  have hzcc : z * c = c * z := by
    rw [hcdef, ← mul_assoc, hzc _ hqj, mul_assoc, hcross hzAj hqk, ← mul_assoc]
  have hbc : b * c = c * b := by
    have hqp_j := IsQ8Pair.q_mul_p' hpq_j
    have hqp_k := IsQ8Pair.q_mul_p' hpq_k
    have h1 : p k * q j = q j * p k := (hcross hqj hpk).symm
    have h2 : q k * p j = p j * q k := (hcross hpj hqk).symm
    have hzk : p k ^ 2 = z := hz.symm
    rw [hzk] at hqp_k
    have hzpkqk : z * (p k * q k) = (p k * q k) * z := by
      rw [← mul_assoc, hcross hzAj hpk, mul_assoc, hcross hzAj hqk, ← mul_assoc]
    calc b * c = p j * (p k * q j) * q k := by rw [hbdef, hcdef]; group
      _ = p j * (q j * p k) * q k := by rw [h1]
      _ = (p j * q j) * (p k * q k) := by group
      _ = (p j * q j) * (p k * q k) * (z * z) := by rw [← pow_two, hz2, mul_one]
      _ = (p j * q j) * ((p k * q k) * z) * z := by group
      _ = (p j * q j) * (z * (p k * q k)) * z := by rw [← hzpkqk]
      _ = (p j * q j * z) * (p k * q k * z) := by group
      _ = (q j * p j) * (q k * p k) := by rw [hqp_j, hqp_k]
      _ = q j * (p j * q k) * p k := by group
      _ = q j * (q k * p j) * p k := by rw [h2]
      _ = c * b := by rw [hbdef, hcdef]; group
  have hcE : c ∉ ({1, z, b, z * b} : Set (Bar D)) := by
    intro hc
    rcases hc with h | h | h | h
    · refine hkey 1 (by group) ?_
      have : (1 : Bar D)⁻¹ * q j = (q k)⁻¹ := by
        rw [inv_one, one_mul]
        exact eq_inv_of_mul_eq_one_left h
      rw [this]
      exact Subgroup.inv_mem _ hqk
    · refine hkey z (hzc _ hpj) ?_
      have : z⁻¹ * q j = (q k)⁻¹ := by
        calc z⁻¹ * q j = z⁻¹ * (q j * q k) * (q k)⁻¹ := by group
          _ = (q k)⁻¹ := by rw [show q j * q k = z from h]; group
      rw [this]
      exact Subgroup.inv_mem _ hqk
    · refine hkey (p j) rfl ?_
      have : (p j)⁻¹ * q j = p k * (q k)⁻¹ := by
        calc (p j)⁻¹ * q j = (p j)⁻¹ * (q j * q k) * (q k)⁻¹ := by group
          _ = p k * (q k)⁻¹ := by rw [show q j * q k = p j * p k from h]; group
      rw [this]
      exact Subgroup.mul_mem _ hpk (Subgroup.inv_mem _ hqk)
    · have hzpj : z * p j * p j = p j * (z * p j) := by
        calc z * p j * p j = p j * z * p j := by rw [hzc _ hpj]
          _ = p j * (z * p j) := by group
      refine hkey (z * p j) hzpj ?_
      have : (z * p j)⁻¹ * q j = p k * (q k)⁻¹ := by
        calc (z * p j)⁻¹ * q j = (z * p j)⁻¹ * (q j * q k) * (q k)⁻¹ := by group
          _ = p k * (q k)⁻¹ := by rw [show q j * q k = z * (p j * p k) from h]; group
      rw [this]
      exact Subgroup.mul_mem _ hpk (Subgroup.inv_mem _ hqk)
  obtain ⟨hEbel, hEb8⟩ := elemAbelian_eight hz2 hb2 hc2 hz1 hb1 hzb hzbc hzcc hbc hcE
  have hAjH : Aj ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hAkH : Ak ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  set W := centralizerJoinH D U ⊓ (Aj ⊔ Ak) with hWdef
  have hWH : W ≤ Subgroup.normalizer (D : Set G) := inf_le_left.trans (centralizerJoinH_le D U)
  have hbarW : bar D W =
      AschbacherToolkit.centralizerJoin (bar D U) ⊓ (bar D Aj ⊔ bar D Ak) := by
    rw [hWdef, bar_inf_of_core_le ((core_le_preimage D _).trans le_sup_left),
      bar_centralizerJoinH hU2, bar_sup hAjH hAkH]
  have hEbW : (Subgroup.zpowers z ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers c ≤ bar D W := by
    rw [hbarW]
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact ⟨Subgroup.pow_mem _ hpjC 2, Subgroup.mem_sup_left hzAj⟩
    · exact ⟨Subgroup.mul_mem _ hpjC hpkC,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hpj) (Subgroup.mem_sup_right hpk)⟩
    · exact ⟨Subgroup.mul_mem _ hqjC hqkC,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hqj) (Subgroup.mem_sup_right hqk)⟩
  obtain ⟨E, hEW, hEel, hE8, -⟩ := lift_elemAbelian_eight hWH hEbel hEb8 hEbW
  have hEcen : E ≤ centralizing D (Abar l) :=
    hEW.trans (inf_le_right.trans (sup_le (factor_le_centralizing hC.hyp.hcomm hjl.symm)
      (factor_le_centralizing hC.hyp.hcomm hkl.symm)))
  refine false_of_elemAbelian_eight hC hin hg hrank j hEel hE8
    (hEW.trans (inf_le_left.trans (centralizerJoinH_le_conj hU))) fun e he he1 => ?_
  exact centralizer_le hC l ⟨1, by rw [pow_one]; exact hEel.2 e he⟩ he1
    (centralizes_of_mem_centralizing (hEcen he))

theorem caseCentralRank (hC : Counterexample G D r Abar) (hin : SectionSixInputs) {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {U : Subgroup G} (hU : U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g))
    (hrank : ∀ m, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar m)) ≤ 1)
    {p q : Fin r → Bar D} (hP : ∀ j, PairAt D U Abar j (p j) (q j)) {j k l : Fin r}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hzjk : p j ^ 2 ≠ p k ^ 2)
    (hzl : p l ^ 2 ∉ ({1, p j ^ 2, p k ^ 2, p j ^ 2 * p k ^ 2} : Set (Bar D))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU.2.2.1]; norm_num)
  have hz2 : ∀ m, (p m ^ 2) ^ 2 = 1 := fun m => by rw [← pow_mul]; exact (hP m).1.1
  have hzA : ∀ m, p m ^ 2 ∈ bar D (aschbacherThm5Preimage D (Abar m)) := fun m =>
    Subgroup.pow_mem _ (hP m).2.1 2
  have hcomm : ∀ {m m'}, m ≠ m' → p m ^ 2 * p m' ^ 2 = p m' ^ 2 * p m ^ 2 := fun h =>
    cross_commute hC.hyp h (hzA _) (hzA _)
  have hzC : ∀ m, p m ^ 2 ∈
      Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar j)) : Set (Bar D)) := by
    intro m
    by_cases hm : m = j
    · subst hm
      exact (hP m).2.2.2.2.2.1
    · exact Strong.bar_factor_le_centralizer hC.hyp (Ne.symm hm) (hzA m)
  obtain ⟨hEbel, hEb8⟩ := elemAbelian_eight (hz2 j) (hz2 k) (hz2 l) (hP j).1.2.2.2
    (hP k).1.2.2.2 hzjk (hcomm hjk) (hcomm hjl) (hcomm hkl) hzl
  set Eb := (Subgroup.zpowers (p j ^ 2) ⊔ Subgroup.zpowers (p k ^ 2)) ⊔
    Subgroup.zpowers (p l ^ 2) with hEbdef
  have hEbW : Eb ≤ bar D (centralizerJoinH D U) := by
    rw [bar_centralizerJoinH hU2]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (hP j).2.2.2.1 2))
      (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (hP k).2.2.2.1 2)))
      (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (hP l).2.2.2.1 2))
  have hEbC : Eb ≤ Subgroup.centralizer
      (bar D (aschbacherThm5Preimage D (Abar j)) : Set (Bar D)) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr (hzC j)) (Subgroup.zpowers_le.mpr (hzC k)))
      (Subgroup.zpowers_le.mpr (hzC l))
  obtain ⟨E, hEW, hEel, hE8, hEEb⟩ :=
    lift_elemAbelian_eight (centralizerJoinH_le D U) hEbel hEb8 hEbW
  refine false_of_elemAbelian_eight hC hin hg hrank j hEel hE8
    (hEW.trans (centralizerJoinH_le_conj hU)) fun e he he1 => ?_
  have heH : e ∈ Subgroup.normalizer (D : Set G) := (hEW.trans (centralizerJoinH_le D U)) he
  have hec : aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
      e := (centralizes_iff_mem_centralizer D _ (preimage_le D _) ⟨e, heH⟩).mpr
    (hEbC (hEEb ▸ toBar_mem_bar D (h := ⟨e, heH⟩) he))
  exact centralizer_le hC j ⟨1, by rw [pow_one]; exact hEel.2 e he⟩ he1 hec

omit [Finite G] in
theorem isElemAbelian_sup_zpowers {X : Type} [Group X] {a b : X} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hc : a * b = b * a) :
    IsElemAbelian 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  refine TwoGroups.isElemAbelian_of_sq fun x hx => sq_eq_one_of_mem_sup ?_ ?_ ?_ hx
  · intro y hy z hz
    rcases mem_zpowers_of_sq ha hy with h | h <;> rcases mem_zpowers_of_sq hb hz with h' | h' <;>
      rw [h, h'] <;> simp [hc]
  · intro y hy
    rcases mem_zpowers_of_sq ha hy with h | h <;> rw [h] <;> simp [ha]
  · intro z hz
    rcases mem_zpowers_of_sq hb hz with h | h <;> rw [h] <;> simp [hb]

theorem exists_lift_pairs (hC : Counterexample G D r Abar) {g : G}
    {U : Subgroup G} (hU : U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g))
    {p q : Fin r → Bar D} (hP : ∀ j, PairAt D U Abar j (p j) (q j)) {j k : Fin r}
    (hjk : j ≠ k) :
    ∃ (Qj Qk : Subgroup (Bar D)) (Y : Subgroup G),
      AschbacherTheorem3.IsQuaternionTwoGroup Qj ∧ AschbacherTheorem3.IsQuaternionTwoGroup Qk ∧
      Qj ≤ bar D (aschbacherThm5Preimage D (Abar j)) ∧
      Qk ≤ bar D (aschbacherThm5Preimage D (Abar k)) ∧
      p j ∈ Qj ∧ q j ∈ Qj ∧ p k ∈ Qk ∧ q k ∈ Qk ∧
      Y ≤ centralizerJoinH D U ∧
      Y ≤ aschbacherThm5Preimage D (Abar j) ⊔ aschbacherThm5Preimage D (Abar k) ∧
      IsPGroup 2 Y ∧ bar D Y = Qj ⊔ Qk := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU.2.2.1]; norm_num)
  obtain ⟨Qj, hpQj, hqQj, hQjq, hQjmin⟩ := (hP j).1.exists_quaternion
  obtain ⟨Qk, hpQk, hqQk, hQkq, hQkmin⟩ := (hP k).1.exists_quaternion
  have hQjA := hQjmin _ (hP j).2.1 (hP j).2.2.1
  have hQkA := hQkmin _ (hP k).2.1 (hP k).2.2.1
  have hQjC := hQjmin _ (hP j).2.2.2.1 (hP j).2.2.2.2.1
  have hQkC := hQkmin _ (hP k).2.2.2.1 (hP k).2.2.2.2.1
  have hYb2 : IsPGroup 2 (Qj ⊔ Qk : Subgroup (Bar D)) :=
    isPGroup_sup_of_commute (isPGroup_of_quaternion hQjq) (isPGroup_of_quaternion hQkq)
      fun x hx y hy => cross_commute hC.hyp hjk (hQjA hx) (hQkA hy)
  set Aj := aschbacherThm5Preimage D (Abar j) with hAjdef
  set Ak := aschbacherThm5Preimage D (Abar k) with hAkdef
  have hAjH : Aj ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hAkH : Ak ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  set W := centralizerJoinH D U ⊓ (Aj ⊔ Ak) with hWdef
  have hWH : W ≤ Subgroup.normalizer (D : Set G) := inf_le_left.trans (centralizerJoinH_le D U)
  have hYbW : Qj ⊔ Qk ≤ bar D W := by
    rw [hWdef, bar_inf_of_core_le ((core_le_preimage D _).trans le_sup_left),
      bar_centralizerJoinH hU2, bar_sup hAjH hAkH]
    exact sup_le (le_inf hQjC (hQjA.trans le_sup_left)) (le_inf hQkC (hQkA.trans le_sup_right))
  obtain ⟨Y, hYW, hY2, hYYb⟩ := lift_two_subgroup hWH hYb2 hYbW
  exact ⟨Qj, Qk, Y, hQjq, hQkq, hQjA, hQkA, hpQj, hqQj, hpQk, hqQk, hYW.trans inf_le_left,
    hYW.trans inf_le_right, hY2, hYYb⟩

theorem exists_lifted_elements (hC : Counterexample G D r Abar) {U Y : Subgroup G}
    {Qj Qk : Subgroup (Bar D)} {p q : Fin r → Bar D} (hP : ∀ j, PairAt D U Abar j (p j) (q j))
    {j k : Fin r} (hjk : j ≠ k) (hQjA : Qj ≤ bar D (aschbacherThm5Preimage D (Abar j)))
    (hQkA : Qk ≤ bar D (aschbacherThm5Preimage D (Abar k))) (hpQj : p j ∈ Qj) (hqQj : q j ∈ Qj)
    (hpQk : p k ∈ Qk) (hqQk : q k ∈ Qk) (hYH : Y ≤ Subgroup.normalizer (D : Set G))
    (hY2 : IsPGroup 2 Y) (hYYb : bar D Y = Qj ⊔ Qk) :
    ∃ P Q P' Q' : Subgroup.normalizer (D : Set G), (P : G) ∈ Y ∧ (Q : G) ∈ Y ∧ (P' : G) ∈ Y ∧
      (Q' : G) ∈ Y ∧ toBar D P = p j ∧ toBar D P' = p k ∧ IsQ8Pair (P : G) (Q : G) ∧
      IsQ8Pair (P' : G) (Q' : G) ∧ Commute (P : G) (P' : G) ∧ Commute (P : G) (Q' : G) ∧
      Commute (Q : G) (P' : G) ∧ Commute (Q : G) (Q' : G) := by
  have hmemj : ∀ {x}, x ∈ Qj → x ∈ bar D Y := fun hx => hYYb ▸ Subgroup.mem_sup_left hx
  have hmemk : ∀ {x}, x ∈ Qk → x ∈ bar D Y := fun hx => hYYb ▸ Subgroup.mem_sup_right hx
  obtain ⟨P, Q, hPY, hQY, hPp, hQq, hPQ⟩ :=
    lift_q8Pair hY2 hYH (hmemj hpQj) (hmemj hqQj) (hP j).1
  obtain ⟨P', Q', hP'Y, hQ'Y, hP'p, hQ'q, hP'Q'⟩ :=
    lift_q8Pair hY2 hYH (hmemk hpQk) (hmemk hqQk) (hP k).1
  have hc : ∀ {x y : Subgroup.normalizer (D : Set G)}, (x : G) ∈ Y → (y : G) ∈ Y →
      toBar D x ∈ Qj → toBar D y ∈ Qk → Commute (x : G) (y : G) := by
    intro x y hx hy hxj hyk
    exact commute_of_bar hY2 hx hy (cross_commute hC.hyp hjk (hQjA hxj) (hQkA hyk))
  refine ⟨P, Q, P', Q', hPY, hQY, hP'Y, hQ'Y, hPp, hP'p, hPQ, hP'Q', ?_, ?_, ?_, ?_⟩
  · exact hc hPY hP'Y (hPp ▸ hpQj) (hP'p ▸ hpQk)
  · exact hc hPY hQ'Y (hPp ▸ hpQj) (hQ'q ▸ hqQk)
  · exact hc hQY hP'Y (hQq ▸ hqQj) (hP'p ▸ hpQk)
  · exact hc hQY hQ'Y (hQq ▸ hqQj) (hQ'q ▸ hqQk)

theorem fourGroup_of_pairs {P Q P' Q' : G} (hPQ : IsQ8Pair P Q) (hP'Q' : IsQ8Pair P' Q')
    (hPP' : Commute P P') (hne : P ^ 2 ≠ P' ^ 2) :
    IsElemAbelian 2 (Subgroup.zpowers (P ^ 2) ⊔ Subgroup.zpowers (P' ^ 2)) ∧
      Nat.card (Subgroup.zpowers (P ^ 2) ⊔ Subgroup.zpowers (P' ^ 2) : Subgroup G) = 4 := by
  have ha : (P ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hPQ.1
  have hb : (P' ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hP'Q'.1
  have hc : P ^ 2 * P' ^ 2 = P' ^ 2 * P ^ 2 := ((hPP'.pow_left 2).pow_right 2).eq
  exact ⟨isElemAbelian_sup_zpowers ha hb hc,
    card_sup_zpowers ha hb hPQ.2.2.2 hP'Q'.2.2.2 hne hc⟩

omit [Finite G] in
theorem mem_centralizer_sup_zpowers {a b x : G} (ha : a * x = x * a) (hb : b * x = x * b) :
    x ∈ Subgroup.centralizer
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr ha))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hb))
  rw [Subgroup.mem_centralizer_iff]
  exact fun e he => Subgroup.mem_centralizer_singleton_iff.mp (hle he)

theorem caseOdd (hC : Counterexample G D r Abar) (hin : SectionSixInputs) {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {U : Subgroup G} (hU : U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g))
    (hrank : ∀ m, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar m)) ≤ 1)
    {p q : Fin r → Bar D} (hP : ∀ j, PairAt D U Abar j (p j) (q j)) (hr : Odd r)
    {j k l : Fin r} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hzjk : p j ^ 2 ≠ p k ^ 2) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Qj, Qk, Y, -, -, hQjA, hQkA, hpQj, hqQj, hpQk, hqQk, hYJ, hYA, hY2, hYYb⟩ :=
    exists_lift_pairs hC hU hP hjk
  have hYH : Y ≤ Subgroup.normalizer (D : Set G) := hYJ.trans (centralizerJoinH_le D U)
  have hYHg : Y ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g :=
    hYJ.trans (centralizerJoinH_le_conj hU)
  have hYcen : Y ≤ centralizing D (Abar l) :=
    hYA.trans (sup_le (factor_le_centralizing hC.hyp.hcomm hjl.symm)
      (factor_le_centralizing hC.hyp.hcomm hkl.symm))
  obtain ⟨P, Q, P', Q', hPY, hQY, hP'Y, -, hPp, hP'p, hPQ, hP'Q', hPP', -, hQP', -⟩ :=
    exists_lifted_elements hC hP hjk hQjA hQkA hpQj hqQj hpQk hqQk hYH hY2 hYYb
  have hC' := hC.conj g
  have hYH' : Y ≤ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) :=
    (normalizer_rightConjugate D g).symm ▸ hYHg
  obtain ⟨m, hm⟩ := exists_fixed_factor hC'.hyp hr hYH' hY2
  have hfaith : ∀ y ∈ Y, y ≠ 1 → ¬ aschbacherThm5Centralizes
      (aschbacherThm5Core (rightConjugate D g))
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)) y := by
    intro y hy hy1 hyc
    obtain ⟨n, hn⟩ := hY2 ⟨y, hy⟩
    exact hg (AschbacherTheorem3.rightConjugate_eq_of_mem (mem_normalizer_of_fusion_conj hC
      ⟨n, congrArg Subtype.val hn⟩ hy1 (centralizes_of_mem_centralizing (hYcen hy)) hyc))
  obtain ⟨X, hPX, hQX, hXq, hXmin⟩ := hPQ.exists_quaternion
  have hXY : X ≤ Y := hXmin Y hPY hQY
  have hne : (P : G) ^ 2 ≠ (P' : G) ^ 2 := by
    intro h
    apply hzjk
    rw [← hPp, ← hP'p, ← map_pow, ← map_pow]
    congr 1
    exact Subtype.ext (by simpa using h)
  obtain ⟨hEel, hE4⟩ := fourGroup_of_pairs hPQ hP'Q' hPP' hne
  set E := Subgroup.zpowers ((P : G) ^ 2) ⊔ Subgroup.zpowers ((P' : G) ^ 2) with hEdef
  have hEY : E ≤ Y := sup_le (Subgroup.zpowers_le.mpr (Y.pow_mem hPY 2))
    (Subgroup.zpowers_le.mpr (Y.pow_mem hP'Y 2))
  have hXE : X ≤ Subgroup.centralizer (E : Set G) := by
    refine hXmin _ (mem_centralizer_sup_zpowers ?_ ?_) (mem_centralizer_sup_zpowers ?_ ?_)
    · rw [← pow_succ, ← pow_succ']
    · exact ((hPP'.pow_right 2).eq).symm
    · exact (hPQ.mul_comm_sq).symm
    · exact ((hQP'.pow_right 2).eq).symm
  refine false_of_faithful_quaternion hC hin hg hrank m hXq (hXY.trans hYHg) (hXY.trans hm)
    (fun x hx => hfaith x (hXY hx)) hEel hE4 (hEY.trans hYHg) (hEY.trans hm)
    (fun e he => hfaith e (hEY he)) (fun e he he1 => ?_)
    (Subgroup.le_centralizer_iff.mp hXE)
  exact centralizer_le hC l ⟨1, by rw [pow_one]; exact hEel.2 e he⟩ he1
    (centralizes_of_mem_centralizing (hYcen (hEY he)))

theorem sq_eq_one_mem_centralizer {U : Subgroup G} (hyp : Hyp61 G D r Abar)
    {p q : Fin r → Bar D} (hP : ∀ j, PairAt D U Abar j (p j) (q j)) {j k : Fin r}
    (hjk : j ≠ k) (hz : p j ^ 2 ≠ p k ^ 2) {Qj Qk : Subgroup (Bar D)}
    (hQjq : AschbacherTheorem3.IsQuaternionTwoGroup Qj)
    (hQkq : AschbacherTheorem3.IsQuaternionTwoGroup Qk)
    (hQjA : Qj ≤ bar D (aschbacherThm5Preimage D (Abar j)))
    (hQkA : Qk ≤ bar D (aschbacherThm5Preimage D (Abar k))) {t : Bar D} (ht : t ∈ Qj ⊔ Qk)
    (ht2 : t ^ 2 = 1) :
    t ∈ Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar j)) : Set (Bar D)) := by
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := mem_sup_of_commute
    (fun x hx y hy => cross_commute hyp hjk (hQjA hx) (hQkA hy)) ht
  have hc : Commute y₀ y₁ := cross_commute hyp hjk (hQjA hy₀) (hQkA hy₁)
  rw [hc.mul_pow] at ht2
  have h1 : y₀ ^ 2 = (y₁ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left ht2
  have h1' : y₁ ^ 2 = (y₀ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right ht2
  have hy₀A1 : y₀ ^ 2 ∈ bar D (aschbacherThm5Preimage D (Abar k)) := by
    rw [h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (hQkA hy₁) 2)
  have hy₁A0 : y₁ ^ 2 ∈ bar D (aschbacherThm5Preimage D (Abar j)) := by
    rw [h1']
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (hQjA hy₀) 2)
  have hsq₀ : (y₀ ^ 2) ^ 2 = 1 := sq_eq_one_of_central hQjq (Subgroup.pow_mem _ hy₀ 2)
    fun w hw => (cross_commute hyp hjk (hQjA hw) hy₀A1).symm
  have hsq₁ : (y₁ ^ 2) ^ 2 = 1 := sq_eq_one_of_central hQkq (Subgroup.pow_mem _ hy₁ 2)
    fun w hw => cross_commute hyp hjk hy₁A0 (hQkA hw)
  have heq : y₀ ^ 2 = y₁ ^ 2 := by
    rw [h1, inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hsq₁)]
  have hy₀2 : y₀ ^ 2 = 1 := by
    rcases (hP j).2.2.2.2.2.2 _ (Subgroup.pow_mem _ (hQjA hy₀) 2) hsq₀ with h | h
    · exact h
    · exfalso
      rcases (hP k).2.2.2.2.2.2 _ (Subgroup.pow_mem _ (hQkA hy₁) 2) hsq₁ with h' | h'
      · exact (hP j).1.2.2.2 (h.symm.trans (heq.trans h'))
      · exact hz (h.symm.trans (heq.trans h'))
  have hy₀C : y₀ ∈ Subgroup.centralizer
      (bar D (aschbacherThm5Preimage D (Abar j)) : Set (Bar D)) := by
    rcases (hP j).2.2.2.2.2.2 _ (hQjA hy₀) hy₀2 with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact (hP j).2.2.2.2.2.1
  exact Subgroup.mul_mem _ hy₀C (Strong.bar_factor_le_centralizer hyp hjk (hQkA hy₁))

theorem caseTwo {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hC : Counterexample G D 2 Abar) (hin : SectionSixInputs) {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {U : Subgroup G} (hU : U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g))
    (hrank : ∀ m, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar m)) ≤ 1)
    {p q : Fin 2 → Bar D} (hP : ∀ j, PairAt D U Abar j (p j) (q j))
    (hz : p 0 ^ 2 ≠ p 1 ^ 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨Qj, Qk, Y, hQjq, hQkq, hQjA, hQkA, hpQj, hqQj, hpQk, hqQk, hYJ, -, hY2, hYYb⟩ :=
    exists_lift_pairs hC hU hP h01
  have hYH : Y ≤ Subgroup.normalizer (D : Set G) := hYJ.trans (centralizerJoinH_le D U)
  have hYHg : Y ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g :=
    hYJ.trans (centralizerJoinH_le_conj hU)
  obtain ⟨P, Q, P', Q', hPY, hQY, hP'Y, hQ'Y, hPp, hP'p, hPQ, hP'Q', hPP', hPQ', hQP', hQQ'⟩ :=
    exists_lifted_elements hC hP h01 hQjA hQkA hpQj hqQj hpQk hqQk hYH hY2 hYYb
  have hC' := hC.conj g
  have hH' := normalizer_rightConjugate D g
  have hYH' : Y ≤ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := hH' ▸ hYHg
  set A0' := aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g 0) with hA0'def
  set W := Y ⊓ Subgroup.normalizer (A0' : Set G) with hWdef
  have hW : ∀ x ∈ Y, ∀ y ∈ Y, x ∉ W → y ∉ W → x * y ∈ W := by
    intro x hx y hy hxW hyW
    exact ⟨Y.mul_mem hx hy, mul_mem_normalizer_of_two hC'.hyp (hYH' hx) (hYH' hy)
      (fun h => hxW ⟨hx, h⟩) (fun h => hyW ⟨hy, h⟩)⟩
  have hne : (P : G) ^ 2 ≠ (P' : G) ^ 2 := by
    intro h
    apply hz
    rw [← hPp, ← hP'p, ← map_pow, ← map_pow]
    congr 1
    exact Subtype.ext (by simpa using h)
  have hne1 : (P : G) ^ 2 * (P' : G) ^ 2 ≠ 1 := by
    intro h
    apply hne
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_left
      (by rw [← pow_two, ← pow_mul]; exact hP'Q'.1)]
  obtain ⟨x, hxW, y, hyW, hxy⟩ :=
    exists_q8Pair_of_index_two hPQ hP'Q' hPP' hPQ' hQP' hQQ' hne1 hPY hQY hP'Y hQ'Y hW
  obtain ⟨X, hxX, hyX, hXq, hXmin⟩ := hxy.exists_quaternion
  have hXW : X ≤ W := hXmin W hxW hyW
  obtain ⟨hEel, hE4⟩ := fourGroup_of_pairs hPQ hP'Q' hPP' hne
  set E := Subgroup.zpowers ((P : G) ^ 2) ⊔ Subgroup.zpowers ((P' : G) ^ 2) with hEdef
  have hEY : E ≤ Y := sup_le (Subgroup.zpowers_le.mpr (Y.pow_mem hPY 2))
    (Subgroup.zpowers_le.mpr (Y.pow_mem hP'Y 2))
  set A0 := aschbacherThm5Preimage D (Abar 0) with hA0def
  have hECA : E ≤ Exclusion.centralizerIn D A0 := by
    have hz0 : toBar D P ^ 2 ∈ Subgroup.centralizer (bar D A0 : Set (Bar D)) := by
      rw [hPp]
      exact (hP 0).2.2.2.2.2.1
    have hz1 : toBar D P' ^ 2 ∈ Subgroup.centralizer (bar D A0 : Set (Bar D)) := by
      rw [hP'p]
      exact Strong.bar_factor_le_centralizer hC.hyp h01 (Subgroup.pow_mem _ (hP 1).2.1 2)
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact (Exclusion.mem_centralizerIn_iff D A0 _).mpr ⟨_, by rw [← map_pow] at hz0; exact hz0⟩
    · exact (Exclusion.mem_centralizerIn_iff D A0 _).mpr ⟨_, by rw [← map_pow] at hz1; exact hz1⟩
  have hEcen : ∀ e ∈ E, aschbacherThm5Centralizes (aschbacherThm5Core D) A0 e := by
    intro e he
    obtain ⟨heH, hec⟩ := (Exclusion.mem_centralizerIn_iff D A0 e).mp (hECA he)
    exact (centralizes_iff_mem_centralizer D A0 (preimage_le D _) ⟨e, heH⟩).mpr hec
  have hEC : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.normalizer (D : Set G) := fun e he he1 =>
    centralizer_le hC 0 ⟨1, by rw [pow_one]; exact hEel.2 e he⟩ he1 (hEcen e he)
  have hinv := conj_normalizer_inv (D := D) g
  have hg' : rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
      g⁻¹ ≠ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := by
    rw [hinv, hH']
    exact Ne.symm hg
  have hEfour : E ∈ fourGroupsInto
      (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
      (rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) g⁻¹) :=
    ⟨hEY.trans hYH', hEel, hE4, fun e he he1 => hinv ▸ hEC e he he1⟩
  have hEN : E ≤ Subgroup.normalizer (A0' : Set G) := lemma_6_5_one hC' hg' hEfour 0
  have hzcen : ∀ {z : Subgroup.normalizer (D : Set G)}, (z : G) ∈ Y →
      toBar D z ∈ Subgroup.centralizer ((Qj ⊔ Qk : Subgroup (Bar D)) : Set (Bar D)) →
      (z : G) ∈ Subgroup.centralizer (Y : Set G) := by
    intro z hzY hzc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨w', hw', hww'⟩ : ∃ w' : Subgroup.normalizer (D : Set G), (w' : G) ∈ Y ∧ (w' : G) = w :=
      ⟨⟨w, hYH hw⟩, hw, rfl⟩
    rw [← hww']
    refine commute_of_bar hY2 hw' hzY ?_
    exact (Subgroup.mem_centralizer_iff.mp hzc) _ (hYYb ▸ toBar_mem_bar D hw')
  have hzC : ∀ i : Fin 2, p i ^ 2 ∈
      Subgroup.centralizer ((Qj ⊔ Qk : Subgroup (Bar D)) : Set (Bar D)) := by
    intro i
    have hle : Qj ⊔ Qk ≤ Subgroup.centralizer ({p i ^ 2} : Set (Bar D)) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_) <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      · fin_cases i
        · exact (Subgroup.mem_centralizer_iff.mp (hP 0).2.2.2.2.2.1) w (hQjA hw)
        · exact (cross_commute hC.hyp h01 (hQjA hw) (Subgroup.pow_mem _ (hP 1).2.1 2))
      · fin_cases i
        · exact (cross_commute hC.hyp h01 (Subgroup.pow_mem _ (hP 0).2.1 2) (hQkA hw)).symm
        · exact (Subgroup.mem_centralizer_iff.mp (hP 1).2.2.2.2.2.1) w (hQkA hw)
    rw [Subgroup.mem_centralizer_iff]
    exact fun w hw => Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hEYC : E ≤ Subgroup.centralizer (Y : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact hzcen (z := P ^ 2) (Y.pow_mem hPY 2) (by rw [map_pow, hPp]; exact hzC 0)
    · exact hzcen (z := P' ^ 2) (Y.pow_mem hP'Y 2) (by rw [map_pow, hP'p]; exact hzC 1)
  have hEX : E ≤ Subgroup.centralizer (X : Set G) :=
    hEYC.trans (Subgroup.centralizer_le (hXW.trans inf_le_left))
  have hfaith : ∀ w ∈ W, w ≠ 1 → ¬ aschbacherThm5Centralizes
      (aschbacherThm5Core (rightConjugate D g)) A0' w := by
    intro w hw hw1 hwc
    obtain ⟨n, hn⟩ := hY2 ⟨w, hw.1⟩
    have hn' : w ^ 2 ^ n = 1 := congrArg Subtype.val hn
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn')
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hm
      exact hw1 hm
    set w' := w ^ 2 ^ (m - 1) with hw'def
    have hw'o : orderOf w' = 2 := by
      rw [hw'def, orderOf_pow_of_dvd (by positivity) (hm ▸ Nat.pow_dvd_pow 2 (Nat.sub_le m 1)),
        hm, Nat.pow_div (Nat.sub_le m 1) (by norm_num), show m - (m - 1) = 1 by omega, pow_one]
    have hw'Y : w' ∈ Y := Y.pow_mem hw.1 _
    have hwH' := hYH' hw.1
    have hw'H' := hYH' hw'Y
    have hcD' : aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g)) A0' w' := by
      have h1 := (centralizes_iff_mem_centralizer (rightConjugate D g) A0' (preimage_le _ _)
        ⟨w, hwH'⟩).mp hwc
      refine (centralizes_iff_mem_centralizer (rightConjugate D g) A0' (preimage_le _ _)
        ⟨w', hw'H'⟩).mpr ?_
      have h2 : toBar (rightConjugate D g) ⟨w', hw'H'⟩ =
          toBar (rightConjugate D g) ⟨w, hwH'⟩ ^ 2 ^ (m - 1) := by
        rw [← map_pow]
        rfl
      rw [h2]
      exact Subgroup.pow_mem _ h1 _
    have hw'H := hYH hw'Y
    have hcD : aschbacherThm5Centralizes (aschbacherThm5Core D) A0 w' := by
      refine (centralizes_iff_mem_centralizer D A0 (preimage_le D _) ⟨w', hw'H⟩).mpr ?_
      refine sq_eq_one_mem_centralizer hC.hyp hP h01 hz hQjq hQkq hQjA hQkA
        (hYYb ▸ toBar_mem_bar D (h := ⟨w', hw'H⟩) hw'Y) ?_
      rw [← map_pow, show (⟨w', hw'H⟩ : Subgroup.normalizer (D : Set G)) ^ 2 = 1 from
        Subtype.ext (by rw [Subgroup.coe_pow]; rw [← hw'o]; exact pow_orderOf_eq_one w'), map_one]
    exact hg (AschbacherTheorem3.rightConjugate_eq_of_mem (mem_normalizer_of_fusion_conj hC
      ⟨1, by rw [pow_one, ← hw'o]; exact pow_orderOf_eq_one w'⟩
      (TwoGroups.ne_one_of_orderOf hw'o) hcD hcD'))
  exact false_of_faithful_quaternion hC hin hg hrank 0 hXq
    ((hXW.trans inf_le_left).trans hYHg) (hXW.trans inf_le_right)
    (fun x hx => hfaith x (hXW hx)) hEel hE4 (hEY.trans hYHg) hEN
    (fun e he => hfaith e ⟨hEY he, hEN he⟩) hEC hEX

end Six

end DeltaLocal

end CFSG.ComponentClassification.AschbacherTheorem5
