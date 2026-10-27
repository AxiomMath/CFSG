module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi23FiveGen
public import CFSG.Sporadic.Fi24.Generate

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Sporadic.Fi24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem closure_centSet_eq_top_of_card {S : Type*} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hcard : (Nat.card S).factorization p = 2) {P₀ : Subgroup S} (hP₀card : Nat.card P₀ = p ^ 2)
    (hgen : Subgroup.closure (centSet P₀) = ⊤) {P : Subgroup S} (hPcard : Nat.card P = p ^ 2) :
    Subgroup.closure (centSet P) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  let S₀ : Sylow p S := Sylow.ofCard P₀ (by rw [hP₀card, hcard])
  let S₁ : Sylow p S := Sylow.ofCard P (by rw [hPcard, hcard])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S S₀ S₁
  have hPeq : P = P₀.map (MulAut.conj g).toMonoidHom := by
    have h1 : (S₁ : Subgroup S) = P := Sylow.coe_ofCard _ _
    have h2 : (S₀ : Subgroup S) = P₀ := Sylow.coe_ofCard _ _
    rw [← h1, ← hg, Sylow.coe_subgroup_smul, h2]
    rfl
  rw [hPeq]
  exact closure_centSet_map (MulAut.conj g) hgen

theorem le_closure_centSet_of_equiv {G' G : Type*} [Group G'] {S : Subgroup G'} [Finite S]
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hS : (Nat.card S).factorization p = 2) {P₀ : Subgroup S}
    (hP₀ : Nat.card P₀ = p ^ 2) (hgen₀ : Subgroup.closure (centSet P₀) = ⊤) {H : Subgroup G}
    (φ : S ≃* H) {Q : Subgroup G} (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ 2) :
    H ≤ Subgroup.closure (centSet Q) := by
  have hcardH : (Nat.card H).factorization p = 2 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hS
  have hP₁ : Nat.card (P₀.map φ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective, hP₀]
  have hQ' : Nat.card (Q.subgroupOf H) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, hQ]
  have hgen := closure_centSet_eq_top_of_card hp hcardH hP₁ (closure_centSet_map φ hgen₀) hQ'
  have hsub : H.subtype '' centSet (Q.subgroupOf H) ⊆ centSet Q := by
    rintro _ ⟨σ, ⟨e, he, he1, hc⟩, rfl⟩
    refine ⟨e, Subgroup.mem_subgroupOf.1 he, fun h => he1 (Subtype.ext h), ?_⟩
    exact congrArg Subtype.val hc
  intro h hh
  have hmem : (⟨h, hh⟩ : H) ∈ Subgroup.closure (centSet (Q.subgroupOf H)) := by
    rw [hgen]
    exact Subgroup.mem_top _
  have hm := Subgroup.mem_map_of_mem H.subtype hmem
  rw [MonoidHom.map_closure] at hm
  exact Subgroup.closure_mono hsub hm

theorem stabilizer_smul_le_closure {G' G α : Type*} [Group G'] {S : Subgroup G'} [Finite S]
    [Group G] [Finite G] [MulAction G α] {p : ℕ} (hp : p.Prime) (hS : (Nat.card S).factorization p = 2)
    {P₀ : Subgroup S} (hP₀ : Nat.card P₀ = p ^ 2) (hgen₀ : Subgroup.closure (centSet P₀) = ⊤)
    {x : α} (φ : S ≃* MulAction.stabilizer G x) (g : G) {Q : Subgroup G}
    (hQH : Q ≤ MulAction.stabilizer G (g • x)) (hQ : Nat.card Q = p ^ 2) :
    MulAction.stabilizer G (g • x) ≤ Subgroup.closure (centSet Q) := by
  have hM1 := MulAction.stabilizer_smul_eq_stabilizer_map_conj g x
  exact le_closure_centSet_of_equiv hp hS hP₀ hgen₀
    ((φ.trans ((MulAction.stabilizer G x).equivMapOfInjective _ (MulAut.conj g).injective)).trans
      (MulEquiv.subgroupCongr hM1.symm)) hQH hQ

theorem card_stabilizer_smul {G α : Type*} [Group G] [MulAction G α] (g : G) (x : α) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mem_normalizer_of_stabilizer_eq {G α : Type*} [Group G] [MulAction G α] {g : G} {x : α}
    (h : MulAction.stabilizer G (g • x) = MulAction.stabilizer G x) :
    g ∈ Subgroup.normalizer (MulAction.stabilizer G x : Set G) := by
  have hg : g⁻¹ ∈ Subgroup.normalizer (MulAction.stabilizer G x : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    have h1 : k ∈ MulAction.stabilizer G x ↔ k ∈ MulAction.stabilizer G (g • x) := by rw [h]
    rw [h1, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, inv_inv, mul_smul,
      mul_smul, inv_smul_eq_iff]
  simpa using Subgroup.inv_mem _ hg

theorem exists_map_of_equiv {G' G : Type*} [Group G'] [Group G] {S : Subgroup G'}
    {H : Subgroup G} (φ : H ≃* S) (K : Subgroup S) :
    ∃ Q : Subgroup G, Nat.card Q = Nat.card K ∧ ∀ q ∈ Q, ∃ m : H, (m : G) = q ∧ φ m ∈ K := by
  refine ⟨(K.map φ.symm.toMonoidHom).map H.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective φ.symm.injective]
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨φ.symm k, rfl, by simpa using hk⟩

theorem exists_le_card_pow {G : Type*} [Group G] [Finite G] (C : Subgroup G) (p : ℕ) {n : ℕ}
    [Fact p.Prime] (h : p ^ n ∣ Nat.card C) : ∃ K : Subgroup G, K ≤ C ∧ Nat.card K = p ^ n := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p h
  exact ⟨K.map C.subtype, Subgroup.map_subtype_le K,
    by rw [Subgroup.card_map_of_injective C.subtype_injective, hK]⟩

theorem exists_fi23_gen :
    ∃ P₀ : Subgroup CFSG.Sporadic.Fi23.J, Nat.card P₀ = 5 ^ 2 ∧
      Subgroup.closure (centSet P₀) = ⊤ := by
  obtain ⟨e, f, s₁, s₂, hs, he, hf, hef, he1, hfe, h₁, h₂⟩ := fi23CG_spec
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hG : ¬ 5 ^ 3 ∣ Nat.card CFSG.Sporadic.Fi23.J := by
    rw [CFSG.Sporadic.Fi23.card_J]
    norm_num
  refine ⟨Subgroup.closure {e, f},
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair.card_closure_pair_eq_sq
      hef he hf he1 hfe hG, ?_⟩
  have heP : e ∈ Subgroup.closure ({e, f} : Set CFSG.Sporadic.Fi23.J) :=
    Subgroup.subset_closure (by simp)
  have hfP : f ∈ Subgroup.closure ({e, f} : Set CFSG.Sporadic.Fi23.J) :=
    Subgroup.subset_closure (by simp)
  have hf1 : f ≠ 1 := by simpa using hfe 0 (by norm_num)
  have hsub : ({s₁, s₂} : Set CFSG.Sporadic.Fi23.J) ⊆
      centSet (Subgroup.closure ({e, f} : Set CFSG.Sporadic.Fi23.J)) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨e, heP, he1, h₁⟩
    · exact ⟨f, hfP, hf1, h₂⟩
  rw [eq_top_iff, ← hs]
  exact Subgroup.closure_mono hsub

theorem centGen_fi24J_five_of_fi23 :
    CentGen 5 CFSG.Sporadic.Fi24.J := by
  obtain ⟨P₀, hP₀, hgen₀⟩ := exists_fi23_gen
  have hsb : fi23EquivM ⟨tJ, tJ_mem_M⟩ ∈ CFSG.Sporadic.Fi23.D23 := by
    rw [fi23EquivM_tJ]
    exact sb_mem_D23
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨K, hKC, hK⟩ := exists_le_card_pow
    (Subgroup.centralizer ({fi23EquivM ⟨tJ, tJ_mem_M⟩} : Set CFSG.Sporadic.Fi23.J)) 5 (n := 2)
    (by
      rw [CFSG.Sporadic.Fi23.card_centralizer_of_mem hsb]
      norm_num)
  obtain ⟨Q, hQcard, hQm⟩ := exists_map_of_equiv fi23EquivM K
  rw [hK] at hQcard
  have hQ : ∀ q ∈ Q, q ∈ M ∧ q * tJ = tJ * q := by
    intro q hq
    obtain ⟨m, rfl, hm⟩ := hQm q hq
    have hc := Subgroup.mem_inf.1 ((mem_centralizer_inf_M_iff tJ_mem_M m).1 (hKC hm))
    exact ⟨hc.2, mem_centralizer_J.1 hc.1⟩
  have hQM : Q ≤ M := fun q hq => (hQ q hq).1
  have hQ1 : Q ≤ MulAction.stabilizer CFSG.Sporadic.Fi24.J (a • root) := by
    intro q hq
    obtain ⟨hqM, hqt⟩ := hQ q hq
    have h1 : jR q * tR = tR * jR q := (commute_tR_iff q).2 hqM
    have h2 : jR q * (tR * xb) = tR * xb * jR q := by
      rw [← jR_tJ, ← map_mul, ← map_mul, hqt]
    have h3 : jR q * xb = xb * jR q := by
      apply mul_left_cancel (a := tR)
      rw [← mul_assoc, ← h1, mul_assoc, h2, mul_assoc]
    rw [MulAction.mem_stabilizer_iff]
    apply cls_injective
    rw [cls_smul, ← xb_eq, h3, mul_inv_cancel_right]
  have hΓM : M ≤ Subgroup.closure (centSet Q) :=
    le_closure_centSet_of_equiv Nat.prime_five fi23J_card_five hP₀ hgen₀ fi23EquivM.symm hQM
      hQcard
  have hΓ1 : MulAction.stabilizer CFSG.Sporadic.Fi24.J (a • root) ≤
      Subgroup.closure (centSet Q) :=
    stabilizer_smul_le_closure Nat.prime_five fi23J_card_five hP₀ hgen₀ fi23EquivM.symm a hQ1
      hQcard
  have htop : Subgroup.closure (centSet Q) = ⊤ := by
    rcases isCoatom_M.le_iff.1 hΓM with h | h
    · exact h
    exfalso
    rw [h] at hΓ1
    have heq : MulAction.stabilizer CFSG.Sporadic.Fi24.J (a • root) = M :=
      Subgroup.eq_of_le_of_card_ge hΓ1 (card_stabilizer_smul a root).ge
    have haN : a ∈ Subgroup.normalizer (M : Set CFSG.Sporadic.Fi24.J) :=
      mem_normalizer_of_stabilizer_eq heq
    have hN : Subgroup.normalizer (M : Set CFSG.Sporadic.Fi24.J) = M := by
      rcases isCoatom_M.le_iff.1 Subgroup.le_normalizer with hN | hN
      · exfalso
        have hs : IsSimpleGroup CFSG.Sporadic.Fi24.J := isSimpleGroup_J
        rcases (Subgroup.normalizer_eq_top_iff.1 hN).eq_bot_or_eq_top with hb | ht
        · have hc := card_M
          rw [hb, Subgroup.card_bot] at hc
          norm_num at hc
        · exact isCoatom_M.1 ht
      · exact hN
    rw [hN] at haN
    apply tR_ne_xb
    rw [xb_eq, ← cls_root]
    exact congrArg cls (MulAction.mem_stabilizer_iff.1 haN).symm
  have h5 : (Nat.card CFSG.Sporadic.Fi24.J).factorization 5 = 2 :=
    factorization_sq_of_eq Nat.prime_five
      (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num :
        Nat.card CFSG.Sporadic.Fi24.J = 5 ^ 2 * 50208228367626468851712) (by norm_num)
  exact centGen_of_sylow Nat.prime_five h5 hQcard htop

end CFSG.HardMathSupport.Dickson.I271
