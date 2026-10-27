module

public import CFSG.CGT.T75H.LocalA
public import CFSG.CGT.T75H.PartBFrattini

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {R : Type} [Group R] [Finite R]

theorem mem_pCore_of_mem_ker_of_sq_mem {w : R} (hw : w ∈ (jMap R).ker)
    (hw2 : w * w ∈ CFSG.pCore 2 R) : w ∈ CFSG.pCore 2 R := by
  classical
  set O := CFSG.pCore 2 R with hO
  have hO2 : ∀ N : Subgroup (R ⧸ O), N.Normal → IsPGroup 2 N → N = ⊥ :=
    normal_pGroup_quot_pCore_eq_bot
  have hZodd := odd_card_center hO2
  have hz : QuotientGroup.mk' O w ∈ Subgroup.center (R ⧸ O) :=
    (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hw)
  have hzz : QuotientGroup.mk' O w * QuotientGroup.mk' O w = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).2 hw2
  have h1 := eq_one_of_mul_self_of_odd_card hZodd hz hzz
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem lift_mem_normalizer {T : Subgroup R} (hT : IsWC T) {g : R}
    (hg : jMap R g ∈ Subgroup.normalizer
      ((T.map (jMap R) : Subgroup (jQuot R)) : Set (jQuot R))) :
    g ∈ Subgroup.normalizer (T : Set R) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 R with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hOp : IsPGroup 2 O := CFSG.pCore_isPGroup
  have hTp : IsPGroup 2 T := isPGroup_two_of_isElemAbelian hT.1
  have hS : IsPGroup 2 (T ⊔ O : Subgroup R) := hTp.to_sup_of_normal_right hOp
  have hle : conjSubgroup g T ≤ T ⊔ O := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    have himg : jMap R g * jMap R t * (jMap R g)⁻¹ ∈ T.map (jMap R) :=
      (Subgroup.mem_normalizer_iff.1 hg (jMap R t)).1 (Subgroup.mem_map_of_mem _ ht)
    obtain ⟨t', ht', ht'e⟩ := Subgroup.mem_map.1 himg
    set w : R := t'⁻¹ * (g * t * g⁻¹) with hwdef
    have hw : w ∈ (jMap R).ker := by
      rw [MonoidHom.mem_ker, hwdef]
      simp only [map_mul, map_inv, ht'e]
      group
    have htt : t * t = 1 := elemAbelian_mul_self hT.1 ht
    have ht'2 : t' * t' = 1 := elemAbelian_mul_self hT.1 ht'
    have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
    have hgtt : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have hx' : (MulAut.conj g) t = t' * w := by
      rw [MulAut.conj_apply, hwdef]
      group
    have hcomm : ⁅w, t'⁆ ∈ O := mem_ker_jMap.1 hw t'
    have hww : w * w ∈ O := by
      have e1 : t' * w * t' * w = 1 := by
        have : (t' * w) * (t' * w) = 1 := by
          rw [← hx', MulAut.conj_apply]
          exact hgtt
        simpa [mul_assoc] using this
      have e2 : ⁅w, t'⁆ = w * w := by
        rw [commutatorElement_def]
        have : t' * w * t'⁻¹ = w⁻¹ := by
          rw [ht'inv]
          exact (eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using e1))
        calc w * t' * w⁻¹ * t'⁻¹ = w * (t' * w⁻¹ * t'⁻¹) := by group
          _ = w * (t' * w * t'⁻¹)⁻¹ := by group
          _ = w * (w⁻¹)⁻¹ := by rw [this]
          _ = w * w := by rw [inv_inv]
      rw [← e2]
      exact hcomm
    have hwO : w ∈ O := mem_pCore_of_mem_ker_of_sq_mem hw hww
    change (MulAut.conj g) t ∈ T ⊔ O
    rw [hx']
    exact Subgroup.mul_mem_sup ht' hwO
  have heq : conjSubgroup g T = T := eq_of_conj_le_pGroup hT hS le_sup_left hle
  exact mem_normalizer_of_conjSubgroup_eq heq

theorem normalizer_transitive_of_jCore {n : ℕ} (hInd : SimpleCaseUpTo n) (h215 : Lemma215Stmt)
    {T : Subgroup R} (hT : IsWC T) (hcl : Subgroup.normalClosure (T : Set R) = ⊤)
    (hTO : T ⊓ CFSG.pCore 2 R = ⊥) (h4 : 4 ≤ Nat.card T) (hn : Nat.card R < n) {a ℓ b : R}
    (ha : a ∈ T) (ha1 : a ≠ 1) (hab : ℓ * b * ℓ⁻¹ * b⁻¹ = a) :
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set R), g * x * g⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 R with hO
  have hker : T ⊓ (QuotientGroup.mk' O).ker = ⊥ := by rw [QuotientGroup.ker_mk', hTO]
  have h4' : 4 ≤ Nat.card (T.map (QuotientGroup.mk' O)) := by
    rw [card_map_eq_of_inf_ker_eq_bot' _ hker]
    exact h4
  have hn' : Nat.card (R ⧸ O) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective O)) hn
  obtain ⟨hsimple, hlist, hWC, h4Y, hkerY⟩ := jCore' hInd h215 hT hcl h4' hn'
  have : IsSimpleGroup (jQuot R) := hsimple
  have : Finite (jQuot R) := Finite.of_surjective _ (jMap_surjective (R := R))
  have hkerT : T ⊓ (jMap R).ker = ⊥ := by rw [hkerY, hTO]
  have hlt : Nat.card (jQuot R) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (jMap_surjective (R := R))) hn
  have hinj : ∀ z ∈ T, jMap R z = 1 → z = 1 := by
    intro z hz hz1
    have : z ∈ T ⊓ (jMap R).ker := ⟨hz, hz1⟩
    rw [hkerT, Subgroup.mem_bot] at this
    exact this
  have hnab : ∃ s t : jQuot R, s * t ≠ t * s := by
    refine ⟨jMap R ℓ, jMap R b, fun h => ?_⟩
    have h1 : jMap R a = 1 := by
      have hc : ⁅jMap R ℓ, jMap R b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
      rw [← hab]
      simpa [commutatorElement_def] using hc
    exact ha1 (hinj a ha h1)
  obtain ⟨-, htrans⟩ := hInd (jQuot R) hlt hnab _ hWC h4Y
  intro x hx hx1 y hy hy1
  obtain ⟨ĝ, hĝN, hĝ⟩ := htrans (jMap R x) (Subgroup.mem_map_of_mem _ hx)
    (fun h => hx1 (hinj x hx h)) (jMap R y) (Subgroup.mem_map_of_mem _ hy)
    (fun h => hy1 (hinj y hy h))
  obtain ⟨g, rfl⟩ := jMap_surjective ĝ
  have hgN := lift_mem_normalizer hT hĝN
  refine ⟨g, hgN, ?_⟩
  have hgx : g * x * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hgN x).1 hx
  have hmem : (g * x * g⁻¹) * y⁻¹ ∈ T ⊓ (jMap R).ker := by
    refine ⟨T.mul_mem hgx (T.inv_mem hy), ?_⟩
    show (g * x * g⁻¹) * y⁻¹ ∈ (jMap R).ker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv] at hĝ ⊢
    rw [hĝ, mul_inv_cancel]
  rw [hkerT, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.1 hmem

omit [Finite R] in
theorem LocalCfg.ell_mem_pCore {T : Subgroup R} {ℓ a b y x₁ : R} (C : LocalCfg T ℓ a b y x₁)
    (hT : IsWC T) (h : T ⊓ CFSG.pCore 2 R ≠ ⊥) : ℓ ∈ CFSG.pCore 2 R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 R with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hℓinv : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right C.ℓℓ
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right C.aa
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right C.yy
  have hbb : b * b = 1 := elemAbelian_mul_self hT.1 C.hb
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hbO_imp : b ∈ O → a ∈ O := by
    intro hbO
    have h1 : ℓ * b * ℓ⁻¹ ∈ O := hOn.conj_mem b hbO ℓ
    rw [hℓinv, C.conj_b_ℓ] at h1
    have : a = b⁻¹ * (b * a) := by group
    rw [this]
    exact O.mul_mem (O.inv_mem hbO) h1
  have haO_imp : a ∈ O → ℓ ∈ O := by
    intro haO
    have h1 : y⁻¹ * a * y⁻¹⁻¹ ∈ O := hOn.conj_mem a haO y⁻¹
    have e : y⁻¹ * a * y⁻¹⁻¹ * a = ℓ := by
      calc y⁻¹ * a * y⁻¹⁻¹ * a = y⁻¹ * (a * y * a) := by group
        _ = y⁻¹ * (y * ℓ) := by rw [C.conj_a_y]
        _ = ℓ := by group
    rw [← e]
    exact O.mul_mem h1 haO
  obtain ⟨t₀, ht₀⟩ : ∃ t : ↥(T ⊓ O), t ≠ 1 := (Subgroup.ne_bot_iff_exists_ne_one).1 h
  have ht₀T : (t₀ : R) ∈ T := t₀.2.1
  have ht₀O : (t₀ : R) ∈ O := t₀.2.2
  have ht₀1 : (t₀ : R) ≠ 1 := fun h => ht₀ (Subtype.ext h)
  apply haO_imp
  rcases C.hT _ ht₀T with h' | h' | h' | h'
  · exact absurd h' ht₀1
  · rw [← h']; exact ht₀O
  · exact hbO_imp (h' ▸ ht₀O)
  · have hbaO : b * a ∈ O := h' ▸ ht₀O
    have h1 : ℓ * (b * a) * ℓ⁻¹ ∈ O := hOn.conj_mem _ hbaO ℓ
    have e1 : ℓ * a * ℓ = a := by
      calc ℓ * a * ℓ = (a * ℓ) * ℓ := by rw [C.comm_aℓ]
        _ = a * (ℓ * ℓ) := by group
        _ = a := by rw [C.ℓℓ, mul_one]
    have e : ℓ * (b * a) * ℓ⁻¹ = b := by
      calc ℓ * (b * a) * ℓ⁻¹ = (ℓ * b * ℓ⁻¹) * (ℓ * a * ℓ⁻¹) := by group
        _ = (ℓ * b * ℓ) * (ℓ * a * ℓ) := by rw [hℓinv]
        _ = (b * a) * a := by rw [C.conj_b_ℓ, e1]
        _ = b := by rw [mul_assoc, C.aa, mul_one]
    rw [e] at h1
    exact hbO_imp h1

omit [Finite R] in
theorem eq_one_of_mem_pCore_of_odd {z : R} (hz : z ∈ CFSG.pCore 2 R) (hodd : Odd (orderOf z)) :
    z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (CFSG.pCore 2 R) := CFSG.pCore_isPGroup
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hp) ⟨z, hz⟩
  have hm' : orderOf z = 2 ^ m := (Subgroup.orderOf_coe ⟨z, hz⟩).trans hm
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact orderOf_eq_one_iff.1 (by simpa using hm')
  · exfalso
    rw [hm'] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hmpos.ne'⟩)

end CFSG.CGT.T75H
