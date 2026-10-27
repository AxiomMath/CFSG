module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdL2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup

theorem card_le_four_of_sq_eq_one_psl2 {F : Type} [Field F] [Finite F]
    (hpp : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (E : Subgroup (GorensteinWalter.PSL2 F)) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := fun x => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hE _ x.2)⟩
  obtain ⟨S, hES⟩ := hE2.exists_le_sylow
  obtain ⟨m, hm, ⟨eD⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hpp S
  have h := QuasithinUnique.dihedral_card_le_four hm ((E.subgroupOf S).map eD.toMonoidHom)
    (by
      rintro _ ⟨y, hy, rfl⟩
      rw [pow_two, ← map_mul]
      have : y * y = 1 := Subtype.ext (hE _ (mem_subgroupOf.mp hy))
      rw [this, map_one])
  rwa [QuasithinUnique.natCard_map_subgroupOf hES] at h

theorem closure_sq_eq_one {G : Type*} [Group G] {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    ∀ x ∈ closure ({a, b, c} : Set G), x * x = 1 := by
  have hpair : ({a, b, c} : Set G).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact hab | exact hab.symm | exact hac | exact hac.symm | exact hbc | exact hbc.symm
  have hcomm := Subgroup.isMulCommutative_closure hpair
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x :=
      congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : closure ({a, b, c} : Set G)) ⟨y, hy⟩)
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

@[expose] def e8a : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def e8b : Equiv.Perm (Fin 8) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def e8c : Equiv.Perm (Fin 8) := Equiv.swap 4 5 * Equiv.swap 6 7

theorem e8_facts : e8a * e8a = 1 ∧ e8b * e8b = 1 ∧ e8c * e8c = 1 ∧ e8a * e8b = e8b * e8a ∧
    e8a * e8c = e8c * e8a ∧ e8b * e8c = e8c * e8b ∧
    [1, e8a, e8b, e8c, e8a * e8b, e8a * e8c, e8b * e8c, e8a * e8b * e8c].Nodup := by
  unfold e8a e8b e8c
  decide

theorem sign_e8 : Equiv.Perm.sign e8a = 1 ∧ Equiv.Perm.sign e8b = 1 ∧
    Equiv.Perm.sign e8c = 1 := by
  unfold e8a e8b e8c
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)] <;>
    rfl

theorem false_of_injective_alt8_psl2 {F : Type} [Field F] [Finite F]
    (hpp : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (ψ : alternatingGroup (Fin 8) →* GorensteinWalter.PSL2 F) (hψ : Function.Injective ψ) :
    False := by
  classical
  obtain ⟨ha2, hb2, hc2, hab, hac, hbc, hnd⟩ := e8_facts
  obtain ⟨hsa, hsb, hsc⟩ := sign_e8
  set a : alternatingGroup (Fin 8) := ⟨e8a, hsa⟩ with ha
  set b : alternatingGroup (Fin 8) := ⟨e8b, hsb⟩ with hb
  set c : alternatingGroup (Fin 8) := ⟨e8c, hsc⟩ with hc
  set E8 := closure ({a, b, c} : Set (alternatingGroup (Fin 8))) with hE8
  have hE8sq := closure_sq_eq_one (Subtype.ext ha2 : a * a = 1) (Subtype.ext hb2 : b * b = 1)
    (Subtype.ext hc2 : c * c = 1) (Subtype.ext hab : a * b = b * a)
    (Subtype.ext hac : a * c = c * a) (Subtype.ext hbc : b * c = c * b)
  have h4 := card_le_four_of_sq_eq_one_psl2 hpp (E8.map ψ) (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE8sq x hx, map_one])
  rw [Subgroup.card_map_of_injective hψ] at h4
  set l : List (alternatingGroup (Fin 8)) :=
    [1, a, b, c, a * b, a * c, b * c, a * b * c] with hl
  have hlnd : l.Nodup := by
    apply List.Nodup.of_map Subtype.val
    exact hnd
  have hlE : ∀ x ∈ l, x ∈ E8 := by
    have hga : a ∈ E8 := subset_closure (by simp)
    have hgb : b ∈ E8 := subset_closure (by simp)
    have hgc : c ∈ E8 := subset_closure (by simp)
    intro x hx
    simp only [hl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hga
    · exact hgb
    · exact hgc
    · exact mul_mem hga hgb
    · exact mul_mem hga hgc
    · exact mul_mem hgb hgc
    · exact mul_mem (mul_mem hga hgb) hgc
  have hlen : l.length = 8 := rfl
  let f : Fin 8 → E8 := fun i => ⟨l.get (Fin.cast hlen.symm i), hlE _ (List.get_mem _ _)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : l.get (Fin.cast hlen.symm i) = l.get (Fin.cast hlen.symm j) :=
      congrArg Subtype.val hij
    have h2 := (List.Nodup.get_inj_iff hlnd).mp h1
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  have h8E := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at h8E
  omega

theorem false_of_injective_alt_psl2 {α : Type*} [Fintype α] [DecidableEq α]
    (h8 : 8 ≤ Fintype.card α) {F : Type} [Field F] [Finite F]
    (hpp : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (ψ : alternatingGroup α →* GorensteinWalter.PSL2 F) (hψ : Function.Injective ψ) : False := by
  classical
  obtain ⟨ι⟩ : Nonempty (Fin 8 ↪ α) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h8)
  set χ : Equiv.Perm (Fin 8) →* Equiv.Perm α := Equiv.Perm.viaEmbeddingHom ι with hχ
  have hχi : Function.Injective χ := Equiv.Perm.viaEmbeddingHom_injective ι
  have hsign : ∀ σ : Equiv.Perm (Fin 8), Equiv.Perm.sign σ = 1 →
      Equiv.Perm.sign (χ σ) = 1 := fun σ hσ => by
    rw [hχ, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding,
      Equiv.Perm.sign_extendDomain, hσ]
  let χA : alternatingGroup (Fin 8) →* alternatingGroup α :=
    (χ.comp (alternatingGroup (Fin 8)).subtype).codRestrict (alternatingGroup α)
      fun σ => hsign _ σ.2
  have hχA : Function.Injective χA := fun σ τ h =>
    Subtype.ext (hχi (congrArg Subtype.val h))
  exact false_of_injective_alt8_psl2 hpp (ψ.comp χA) (hψ.comp hχA)

variable {H : Type} [Group H] [Finite H]

theorem rowAlt : RowAlt := by
  intro H _ _ c n hn ⟨θ0⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : generalizedFitting H = GeneralizedFitting.subgroup H :=
    CFSG.generalizedFitting_eq_componentClassification H
  let θ : GeneralizedFitting.subgroup H ≃* alternatingGroup (Fin n) :=
    (MulEquiv.subgroupCongr hF.symm).trans θ0
  have : IsSimpleGroup (GeneralizedFitting.subgroup H) :=
    (MulEquiv.subgroupCongr hF).isSimpleGroup_congr.mp c.simple
  have hnonab : ∃ x y : GeneralizedFitting.subgroup H, x * y ≠ y * x := by
    obtain ⟨u, v, huv⟩ := c.exists_ne_commute_G
    refine ⟨MulEquiv.subgroupCongr hF u, MulEquiv.subgroupCongr hF v, fun h => huv ?_⟩
    apply (MulEquiv.subgroupCongr hF).injective
    rw [map_mul, map_mul]
    exact h
  obtain ⟨Kp, hAlt, e, -⟩ :=
    CatalogueBAlternating.generalizedFitting_between_alternating_symmetric hnonab (Or.inr hn) θ
  have hb' : orderOf (e c.b) = 2 := by rw [MulEquiv.orderOf_eq, c.orderOf_b]
  set P : Subgroup Kp := zpowers (e c.b) with hPdef
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb', pow_one])
  have hN : normalizer (P : Set Kp) = centralizer ({e c.b} : Set Kp) :=
    UnbalancedCorr.normalizer_zpowers_eq_centralizer hb'
  have hCmap : (centralizer ({c.b} : Set H)).map e.toMonoidHom =
      centralizer ({e c.b} : Set Kp) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff, ← map_mul, ← map_mul, e.injective.eq_iff]
  set Ke := c.K.map e.toMonoidHom with hKe
  have hKeN : Ke ≤ normalizer (P : Set Kp) := by
    rw [hN, ← hCmap]
    exact map_mono c.K_le
  have hL := (Sp4Rec.isPComponent_subgroupOf_map_iff e c.K_le).mp c.isPComponent_K
  rw [hCmap, ← hN] at hL
  obtain ⟨hdeg, heq, -⟩ := CatalogueBAlternating.between_normalizer_pComponent Kp hAlt 2 P hP2
    (Ke.subgroupOf (normalizer (P : Set Kp))) hL
  set Ω := MulAction.fixedPoints (↥P) (Fin n) with hΩ
  have heq' : Ke.map Kp.subtype = (alternatingGroup Ω).map Equiv.Perm.ofSubtype := by
    rw [← heq, ← Subgroup.map_map, map_subgroupOf_eq_of_le hKeN]
  let ε : alternatingGroup Ω ≃* c.K :=
    ((alternatingGroup Ω).equivMapOfInjective Equiv.Perm.ofSubtype
      Equiv.Perm.ofSubtype_injective).trans
      ((MulEquiv.subgroupCongr heq'.symm).trans
        ((Ke.equivMapOfInjective Kp.subtype Kp.subtype_injective).symm.trans
          (c.K.equivMapOfInjective e.toMonoidHom e.injective).symm))
  have hΩ5 : 5 ≤ Nat.card Ω := hdeg
  have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hKs : IsSimpleGroup c.K := ε.isSimpleGroup_congr.mp (alternatingGroup.isSimpleGroup hΩ5)
  have hKc : Nat.card c.K = (Nat.card Ω).factorial / 2 := by
    rw [← Nat.card_congr ε.toEquiv, nat_card_alternatingGroup]
  have hbar := c.card_K_bar
  have h7800 : ordL2sq 5 ≤ ordL2sq (c.p ^ c.f) := ordL2sq_mono c.five_le
  have h7800' : ordL2sq 5 = 7800 := by decide
  have hK1 := card_quot_eq_of_simple hKs (by rw [hbar]; omega)
  rw [hbar, hKc] at hK1
  have hm8 : 8 ≤ Nat.card Ω := by
    by_contra hlt
    push Not at hlt
    have : (Nat.card Ω).factorial / 2 ≤ 2520 := by
      interval_cases (Nat.card Ω) <;> decide
    omega
  obtain ⟨-, -, -, -, F, _, _, hFK, ⟨eK⟩⟩ := AutL2Facts.lieModel_psl2_data c.type_K
  have hf1 := c.one_le
  have hpp : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    AutL2Facts.isOddPrimePower_of c.prime c.ne_two (by omega) hFK
  have hcore : pPrimeCore 2 c.K = ⊥ := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 c.K)
    rw [hbar, hK1, hKc] at hc
    have hpos : 0 < (Nat.card Ω).factorial / 2 := by
      have := Nat.factorial_pos (Nat.card Ω)
      have : 2 ≤ (Nat.card Ω).factorial := by
        calc 2 = Nat.factorial 2 := rfl
          _ ≤ (Nat.card Ω).factorial := Nat.factorial_le (by omega)
      omega
    have h1 : Nat.card (pPrimeCore 2 c.K) = 1 := by
      rcases Nat.eq_zero_or_pos (Nat.card (pPrimeCore 2 c.K)) with h0 | h0
      · rw [h0, mul_zero] at hc; omega
      · nlinarith
    exact Subgroup.eq_bot_of_card_eq _ h1
  let ψ : alternatingGroup Ω →* GorensteinWalter.PSL2 F :=
    eK.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 c.K)).comp ε.toMonoidHom)
  have hmk : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 c.K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hcore])
  have hψ : Function.Injective ψ := fun x y h => ε.injective (hmk (eK.injective h))
  exact false_of_injective_alt_psl2 (by rwa [← Nat.card_eq_fintype_card]) hpp ψ hψ

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
