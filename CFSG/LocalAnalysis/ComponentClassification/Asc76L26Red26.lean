module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26AlphaG
public import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingMap

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.AschbacherTightEmbedding

section OddKernel

variable {A B : Type*} [Group A] [Group B] [Finite A]

theorem quotient_oddCore_equiv (f : A →* B) (hf : Function.Surjective f)
    (hk : Odd (Nat.card f.ker)) :
    Nonempty ((A ⧸ CFSG.Assembly.oddCore A) ≃* (B ⧸ CFSG.Assembly.oddCore B)) := by
  have : Finite B := Finite.of_surjective f hf
  set M := (CFSG.Assembly.oddCore B).comap f with hM
  have hMn : M.Normal := (CFSG.Assembly.oddCore_normal B).comap f
  have hle : CFSG.Assembly.oddCore A ≤ M := by
    have hcard := Asc76X.card_map_mul_card_inf_ker f (CFSG.Assembly.oddCore A)
    have hodd : Odd (Nat.card ((CFSG.Assembly.oddCore A).map f)) :=
      (odd_card_oddCore A).of_dvd_nat (Dvd.intro _ hcard)
    have h1 : (CFSG.Assembly.oddCore A).map f ≤ CFSG.Assembly.oddCore B :=
      le_oddCore ((CFSG.Assembly.oddCore_normal A).map f hf) hodd
    exact map_le_iff_le_comap.mp h1
  have hge : M ≤ CFSG.Assembly.oddCore A := by
    apply le_oddCore hMn
    have hcard := Asc76X.card_map_mul_card_inf_ker f M
    rw [map_comap_eq_self_of_surjective hf, inf_eq_left.mpr (ker_le_comap f _)] at hcard
    rw [← hcard]
    exact (odd_card_oddCore B).mul hk
  have heq : CFSG.Assembly.oddCore A = M := le_antisymm hle hge
  set φ := (QuotientGroup.mk' (CFSG.Assembly.oddCore B)).comp f with hφdef
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hker : φ.ker = M := by
    ext x
    simp [φ, M, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (heq.trans hker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end OddKernel

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {𝒯 : Set (Subgroup G)}
  {R : Subgroup G}

omit [Finite G] in
theorem normalClosure_map_mk (N : Subgroup G) [N.Normal] (R : Subgroup G) :
    normalClosure ((R.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
      (normalClosure (R : Set G)).map (QuotientGroup.mk' N) := by
  rw [map_normalClosure _ _ (QuotientGroup.mk'_surjective N), coe_map]

theorem concl26_lift {N : Subgroup G} [N.Normal] (hRN : R ⊓ N = ⊥)
    (hodd : Odd (Nat.card (N ⊓ normalClosure (R : Set G) : Subgroup G)))
    (hsyl : IsSylowOf 2 (R.map (QuotientGroup.mk' N))
      (normalClosure ((R.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))))
    (hsz : IsSzOrU3
      (↥(normalClosure ((R.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) ⧸
        CFSG.Assembly.oddCore
          ↥(normalClosure ((R.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)))))
    (hshape : SylowShape (R.map (QuotientGroup.mk' N))) :
    IsSylowOf 2 R (normalClosure (R : Set G)) ∧
      IsSzOrU3 (↥(normalClosure (R : Set G)) ⧸
        CFSG.Assembly.oddCore ↥(normalClosure (R : Set G))) ∧ SylowShape R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  set L := normalClosure (R : Set G) with hLdef
  rw [normalClosure_map_mk N R] at hsyl hsz
  set f := π.subgroupMap L with hfdef
  have hf : Function.Surjective f := π.subgroupMap_surjective L
  have hfker : f.ker = N.subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro hx
      have := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).mp this
    · intro hx
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
  have hk : Odd (Nat.card f.ker) := by
    rw [hfker, ← card_map_of_injective L.subtype_injective, subgroupOf_map_subtype]
    exact hodd
  have hRL : R ≤ L := subset_normalClosure
  refine ⟨?_, ?_, hshape.of_mulEquiv (equivMapMk hRN).symm⟩
  · apply isSylowOf_of_card hRL
    rw [Nat.card_congr (equivMapMk hRN).toEquiv, hsyl.card_eq]
    congr 1
    have hcard := Asc76X.card_map_mul_card_inf_ker π L
    rw [QuotientGroup.ker_mk'] at hcard
    have h1 : Nat.card (L.map π) ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card (N ⊓ L : Subgroup G) ≠ 0 := Nat.card_pos.ne'
    have h3 : (Nat.card (N ⊓ L : Subgroup G)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        rw [← even_iff_two_dvd]
        exact Nat.not_even_iff_odd.mpr hodd)
    rw [← hcard, Nat.factorization_mul h1 h2, Finsupp.add_apply, h3, add_zero]
  · obtain ⟨e⟩ := quotient_oddCore_equiv f hf hk
    exact IsSzOrU3.of_mulEquiv hsz e

omit [Finite G] in
theorem eq_of_map_mk_eq {N : Subgroup G} [N.Normal] {A B : Subgroup G} (hA : A ≤ S) (hB : B ≤ S)
    (hSN : S ⊓ N = ⊥)
    (h : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) : A = B := by
  have key : ∀ {X Y : Subgroup G}, X ≤ S → Y ≤ S →
      X.map (QuotientGroup.mk' N) = Y.map (QuotientGroup.mk' N) → X ≤ Y := by
    intro X Y hX hY hXY x hx
    have hmem : QuotientGroup.mk' N x ∈ Y.map (QuotientGroup.mk' N) :=
      hXY ▸ mem_map_of_mem _ hx
    obtain ⟨y, hy, hyx⟩ := hmem
    have h1 : y⁻¹ * x ∈ N := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      exact hyx
    have h2 : y⁻¹ * x ∈ S ⊓ N := mem_inf.mpr ⟨S.mul_mem (S.inv_mem (hY hy)) (hX hx), h1⟩
    rw [hSN, mem_bot] at h2
    have : x = y := by
      calc x = y * (y⁻¹ * x) := by group
        _ = y := by rw [h2, mul_one]
    rw [this]
    exact hy
  exact le_antisymm (key hA hB h) (key hB hA h.symm)

theorem concl26_of_oddCore_ne_bot (IH : Statement26 (Nat.card G - 1)) (h : Hyp26 S 𝒯 R)
    (hO : CFSG.Assembly.oddCore G ≠ ⊥) : Concl26 𝒯 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Assembly.oddCore G with hNdef
  have hSN : S ⊓ N = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_odd_of_isPGroup (odd_card_oddCore G) h.sylow.isPGroup
  have hN : ∀ T ∈ 𝒯, T ⊓ N = ⊥ := fun T hT =>
    eq_bot_iff.mpr ((inf_le_inf_right N (h.le T hT)).trans hSN.le)
  have hcard : Nat.card (G ⧸ N) ≤ Nat.card G - 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h2 : 1 < Nat.card N := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hO
    have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    have h4 : Nat.card (G ⧸ N) < Nat.card G := by
      rw [h1]
      exact lt_mul_of_one_lt_right h3 h2
    omega
  obtain ⟨E, hER, hE4, hEe⟩ := exists_four_le h.big.1
  have hNH : N ≤ fusionGen (memberSet 𝒯) :=
    oddCore_le_fusionGen hE4 hEe fun e he he1 => mem_memberSet h.mem (hER he) he1
  rcases IH _ hcard _ _ _ (h.quot hN) with htop | ⟨huniq, hsyl, hsz, hshape⟩
  · exact Or.inl (fusionGen_eq_top_of_quot h.toHypCore hN hNH htop)
  · right
    have hRS : R ≤ S := h.le R h.mem
    refine ⟨fun R' hR' hbig' => ?_, concl26_lift (hN R h.mem)
      ((odd_card_oddCore G).of_dvd_nat (card_dvd_of_le inf_le_left)) hsyl hsz hshape⟩
    have h1 := huniq _ ⟨R', hR', rfl⟩ (hbig'.of_mulEquiv (equivMapMk (hN R' hR')))
    exact eq_of_map_mk_eq (h.le R' hR') hRS hSN h1

theorem not_mem_commutator_of_index_two {X : Type*} [Group X] [Finite X] {P R : Subgroup X}
    (hP : ¬ 2 ∣ P.index) (hRi : (R.subgroupOf P).index = 2) {u : X} (hu : u ∈ center X)
    (huR : u ∉ R) (hu2 : u ^ 2 = 1) : u ∉ commutator X := by
  classical
  set R' := R.subgroupOf P with hR'
  let ϕ : P →* Multiplicative (ZMod 2) :=
    { toFun := fun p => if p ∈ R' then 1 else Multiplicative.ofAdd 1
      map_one' := by simp
      map_mul' := fun a b => by
        have h := mul_mem_iff_of_index_two hRi (a := a) (b := b)
        by_cases ha : a ∈ R'
        · by_cases hb : b ∈ R'
          · simp [ha, hb, h]
          · simp [ha, hb, h]
        · by_cases hb : b ∈ R'
          · simp [ha, hb, h]
          · simp only [ha, hb, h, iff_self, ↓reduceIte]
            decide }
  have hpow : u ^ P.index = u := by
    obtain ⟨m, hm⟩ : Odd P.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hP)
    rw [hm, pow_succ, pow_mul, hu2, one_pow, one_mul]
  have hV := MonoidHom.transfer_eq_pow ϕ u (fun k g₀ _ => by
    have hc : u ^ k ∈ center X := pow_mem hu k
    rw [mul_assoc, ← (mem_center_iff.mp hc g₀), inv_mul_cancel_left])
  intro hu'
  have h1 : MonoidHom.transfer ϕ u = 1 := Abelianization.commutator_subset_ker _ hu'
  rw [hV] at h1
  obtain ⟨p, hp1, hpu⟩ : ∃ p : P, ϕ p = 1 ∧ (p : X) = u ^ P.index := ⟨_, h1, rfl⟩
  have hpR : p ∉ R' := by
    rw [hR', mem_subgroupOf, hpu, hpow]
    exact huR
  have : ϕ p = Multiplicative.ofAdd 1 := by simp [ϕ, hpR]
  rw [this] at hp1
  exact absurd hp1 (by decide)

end CFSG.ComponentClassification.Asc76.L26
