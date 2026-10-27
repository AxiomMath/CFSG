module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsA7Quaternion
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2PGL
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.Open CFSG.GorensteinWalter

theorem card_ringEquiv_of_card {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) : Nat.card (K ≃+* K) = f := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K p := charP_of_card_eq_prime_pow hKF
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let e : (K ≃+* K) ≃ (K ≃ₐ[ZMod p] K) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (by
        intro x
        have h : (σ.toRingHom.comp (algebraMap (ZMod p) K) : ZMod p →+* K) =
            algebraMap (ZMod p) K := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
      invFun := fun σ => σ.toRingEquiv
      left_inv := fun σ => by ext x; rfl
      right_inv := fun σ => by ext x; rfl }
  rw [Nat.card_congr e, IsGalois.card_aut_eq_finrank]
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := K)
  rw [hK, Nat.card_zmod] at h1
  exact (Nat.pow_right_injective hp.two_le h1).symm

theorem sq_eq_one_of_card_le_two {A : Type*} [Group A] [Finite A] (hA : Nat.card A ≤ 2)
    (x : A) : x ^ 2 = 1 := by
  have h := orderOf_dvd_natCard x
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h' : orderOf x ∣ 2 := by
    interval_cases hc : Nat.card A
    · rw [Nat.dvd_one] at h
      rw [h]
      norm_num
    · exact h
  exact orderOf_dvd_iff_pow_eq_one.mp h'

theorem eq_of_ne_one_of_card_le_two {A : Type*} [Group A] [Finite A] (hA : Nat.card A ≤ 2)
    {x y : A} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  let _ : Fintype A := Fintype.ofFinite A
  have hsub : ({1, x, y} : Finset A).card ≤ Fintype.card A := Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem, Finset.card_pair hxy] at hsub
  · rw [← Nat.card_eq_fintype_card] at hsub
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx, Ne.symm hy⟩

theorem quaternion_pair_swap {G : Type*} [Group G] {c d : G}
    (hd : d ^ 2 = c ^ 2) (hdc : d * c * d⁻¹ = c⁻¹) : c * d * c⁻¹ = d⁻¹ := by
  have h1 : d * c = c⁻¹ * d := by
    calc d * c = d * c * d⁻¹ * d := by group
      _ = c⁻¹ * d := by rw [hdc]
  have h2 : d * c * d = c := by
    calc d * c * d = c⁻¹ * (d * d) := by rw [h1]; group
      _ = c⁻¹ * c ^ 2 := by rw [← pow_two, hd]
      _ = c := by group
  calc c * d * c⁻¹ = d⁻¹ * (d * c * d) * c⁻¹ := by group
    _ = d⁻¹ := by rw [h2]; group

theorem quaternion_pair_mul {G : Type*} [Group G] {c d : G} (hc4 : c ^ 4 = 1)
    (hd : d ^ 2 = c ^ 2) (hdc : d * c * d⁻¹ = c⁻¹) :
    (c * d) ^ 2 = c ^ 2 ∧ c * (c * d) * c⁻¹ = (c * d)⁻¹ := by
  have h1 : d * c = c⁻¹ * d := by
    calc d * c = d * c * d⁻¹ * d := by group
      _ = c⁻¹ * d := by rw [hdc]
  constructor
  · calc (c * d) ^ 2 = c * (d * c) * d := by rw [pow_two]; group
      _ = c * (c⁻¹ * d) * d := by rw [h1]
      _ = d ^ 2 := by rw [pow_two]; group
      _ = c ^ 2 := hd
  · have hd4 : d ^ 4 = 1 := by
      rw [show 4 = 2 * 2 by norm_num, pow_mul, hd, ← pow_mul]
      exact hc4
    have hdinv : d⁻¹ = d * c ^ 2 := by
      have : d * (d * c ^ 2) = 1 := by
        rw [← mul_assoc, ← pow_two, hd, ← pow_add]
        exact hc4
      exact inv_eq_of_mul_eq_one_right this
    have hc2 : c ^ 2 * d = d * c ^ 2 := by rw [← hd]; group
    calc c * (c * d) * c⁻¹ = c ^ 2 * d * c⁻¹ := by rw [pow_two]; group
      _ = d * c ^ 2 * c⁻¹ := by rw [hc2]
      _ = d⁻¹ * c⁻¹ := by rw [hdinv]
      _ = (c * d)⁻¹ := by group

theorem orderOf_eq_four {G : Type*} [Group G] {x : G} (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) :
    orderOf x = 4 := by
  have hdvd := orderOf_dvd_of_pow_eq_one h4
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : orderOf x
  · exact absurd (orderOf_eq_zero_iff'.mp h 4 (by norm_num)) (not_not.mpr h4)
  · exact absurd (by rw [orderOf_eq_one_iff.mp h, one_pow]) h2
  · exact absurd (by rw [← h]; exact pow_orderOf_eq_one x) h2
  · omega
  · rfl

theorem pGammaL2_quaternion_centralizer {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hAut : Nat.card (K ≃+* K) ≤ 2) {c d v : PGammaL2 K}
    (hc : orderOf c = 4) (hd : d ^ 2 = c ^ 2) (hdc : d * c * d⁻¹ = c⁻¹) (hv : v ^ 2 = 1)
    (hvc : v * c = c * v) (hvd : v * d = d * v) : v = 1 ∨ v = c ^ 2 := by
  classical
  let : Finite (K ≃+* K) := Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
    intro e f h
    ext x
    exact congrFun h x)
  let π : PGammaL2 K →* (K ≃+* K) := SemidirectProduct.rightHom
  have hlin : ∀ x : PGammaL2 K, π x = 1 → x = SemidirectProduct.inl x.left := by
    intro x hx
    exact SemidirectProduct.ext (by simp) (by simpa [π] using hx)
  have hc4 : c ^ 4 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc2 : c ^ 2 ≠ 1 := sq_ne_one_of_orderOf_eq_four hc
  obtain ⟨c₁, d₁, hc₁4, hc₁sq, hd₁sq, hd₁c₁, hπc₁, hvc₁, hvd₁⟩ :
      ∃ c₁ d₁ : PGammaL2 K, c₁ ^ 4 = 1 ∧ c₁ ^ 2 = c ^ 2 ∧ d₁ ^ 2 = c ^ 2 ∧
        d₁ * c₁ * d₁⁻¹ = c₁⁻¹ ∧ π c₁ = 1 ∧ v * c₁ = c₁ * v ∧ v * d₁ = d₁ * v := by
    by_cases hπc : π c = 1
    · exact ⟨c, d, hc4, rfl, hd, hdc, hπc, hvc, hvd⟩
    by_cases hπd : π d = 1
    · refine ⟨d, c, ?_, hd, rfl, quaternion_pair_swap hd hdc, hπd, hvd, hvc⟩
      rw [show 4 = 2 * 2 by norm_num, pow_mul, hd, ← pow_mul]
      exact hc4
    · obtain ⟨hcd2, hccd⟩ := quaternion_pair_mul hc4 hd hdc
      refine ⟨c * d, c, ?_, hcd2, rfl, hccd, ?_, ?_, hvc⟩
      · rw [show 4 = 2 * 2 by norm_num, pow_mul, hcd2, ← pow_mul]
        exact hc4
      · rw [map_mul, eq_of_ne_one_of_card_le_two hAut hπc hπd, ← pow_two]
        exact sq_eq_one_of_card_le_two hAut _
      · calc v * (c * d) = c * (v * d) := by rw [← mul_assoc, hvc, mul_assoc]
          _ = c * d * v := by rw [hvd, mul_assoc]
  have hc₁2 : c₁ ^ 2 ≠ 1 := hc₁sq ▸ hc2
  have hc₁ord : orderOf c₁ = 4 := orderOf_eq_four hc₁4 hc₁2
  set g₁ := c₁.left with hg₁
  have hc₁e : c₁ = SemidirectProduct.inl g₁ := hlin c₁ hπc₁
  have hg₁ord : orderOf g₁ = 4 := by
    rw [← orderOf_injective (SemidirectProduct.inl : PGL2 K →* PGammaL2 K)
      SemidirectProduct.inl_injective g₁, ← hc₁e, hc₁ord]
  by_cases hπv : π v = 1
  ·
    have hve : v = SemidirectProduct.inl v.left := hlin v hπv
    have hv2 : v.left ^ 2 = 1 := by
      apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
      rw [map_pow, ← hve, hv, map_one]
    have hcomm : g₁ * v.left = v.left * g₁ := by
      apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
      rw [map_mul, map_mul, ← hve, ← hc₁e, hvc₁]
    rcases pgl2_eq_of_commute_orderOf_four hK hg₁ord hv2 hcomm with h | h
    · left
      rw [hve, h, map_one]
    · right
      rw [hve, h, map_pow, ← hc₁e, hc₁sq]
  · exfalso
    have hπd₁ : π d₁ ≠ 1 := by
      intro hπd₁
      have hd₁e : d₁ = SemidirectProduct.inl d₁.left := hlin d₁ hπd₁
      apply pgl2_not_quaternion_pair hK hg₁ord (d := d₁.left)
      · apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
        rw [map_pow, map_pow, ← hd₁e, ← hc₁e, hd₁sq, hc₁sq]
      · apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
        rw [map_mul, map_mul, map_inv, map_inv, ← hd₁e, ← hc₁e, hd₁c₁]
    have hπvd : π (v * d₁) = 1 := by
      rw [map_mul, eq_of_ne_one_of_card_le_two hAut hπv hπd₁, ← pow_two]
      exact sq_eq_one_of_card_le_two hAut _
    have hvde : v * d₁ = SemidirectProduct.inl (v * d₁).left := hlin _ hπvd
    apply pgl2_not_quaternion_pair hK hg₁ord (d := (v * d₁).left)
    · apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
      rw [map_pow, map_pow, ← hvde, ← hc₁e]
      calc (v * d₁) ^ 2 = v ^ 2 * d₁ ^ 2 := by
            rw [pow_two, pow_two, pow_two]
            calc v * d₁ * (v * d₁) = v * (d₁ * v) * d₁ := by group
              _ = v * (v * d₁) * d₁ := by rw [hvd₁]
              _ = v * v * (d₁ * d₁) := by group
        _ = c₁ ^ 2 := by rw [hv, one_mul, hd₁sq, hc₁sq]
    · apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
      rw [map_mul, map_mul, map_inv, map_inv, ← hvde, ← hc₁e]
      calc v * d₁ * c₁ * (v * d₁)⁻¹ = v * (d₁ * c₁ * d₁⁻¹) * v⁻¹ := by group
        _ = v * c₁⁻¹ * v⁻¹ := by rw [hd₁c₁]
        _ = c₁⁻¹ := by
          have : v * c₁⁻¹ = c₁⁻¹ * v := by
            calc v * c₁⁻¹ = c₁⁻¹ * (c₁ * v) * c₁⁻¹ := by group
              _ = c₁⁻¹ * (v * c₁) * c₁⁻¹ := by rw [hvc₁]
              _ = c₁⁻¹ * v := by group
          rw [this]
          group

theorem conjNormal_injective_of_centralizer_eq_bot {X : Type*} [Group X] (N : Subgroup X)
    [N.Normal] (hC : Subgroup.centralizer (N : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := N) : X →* MulAut N) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (N : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨n, hn⟩)
    rw [MulAut.conjNormal_apply] at h1
    change x * n * x⁻¹ = n at h1
    calc n * x = x * n * x⁻¹ * x := by rw [h1]
      _ = x * n := by group
  rw [hC] at hxC
  exact Subgroup.mem_bot.mp hxC

theorem small_aut_quaternion_holds : ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X),
    N.Normal → Subgroup.centralizer (N : Set X) = ⊥ → IsSmallDihedralSimple N →
    ∀ (Q : Subgroup X) (k : ℕ), 1 ≤ k → Nonempty (Q ≃* QuaternionGroup (2 ^ k)) →
      Open.pRank 2 (Subgroup.centralizer (Q : Set X)) ≤ 1 := by
  intro X _ _ N hNn hC hsmall Q k hk ⟨eQ⟩
  classical
  obtain ⟨hc₀, hd₀, hdc₀⟩ := quaternion_pair k hk
  set c₀ := (QuaternionGroup.a ((2 ^ (k - 1) : ℕ) : ZMod (2 * 2 ^ k)) :
    QuaternionGroup (2 ^ k)) with hc₀def
  set d₀ := (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ k)) with hd₀def
  let ι : QuaternionGroup (2 ^ k) →* X := Q.subtype.comp eQ.symm.toMonoidHom
  have hι : Function.Injective ι := Q.subtype_injective.comp eQ.symm.injective
  have hιQ : ∀ g, ι g ∈ Q := fun g => (eQ.symm g).2
  set c := ι c₀ with hcdef
  set d := ι d₀ with hddef
  have hc : orderOf c = 4 := by rw [hcdef, orderOf_injective ι hι, hc₀]
  have hd : d ^ 2 = c ^ 2 := by rw [hcdef, hddef, ← map_pow, ← map_pow, hd₀]
  have hdc : d * c * d⁻¹ = c⁻¹ := by
    rw [hcdef, hddef, ← map_inv, ← map_mul, ← map_mul, hdc₀, map_inv]
  have hcent : ∀ v ∈ Subgroup.centralizer (Q : Set X), v * c = c * v ∧ v * d = d * v := by
    intro v hv
    exact ⟨((Subgroup.mem_centralizer_iff.mp hv) c (hιQ c₀)).symm,
      ((Subgroup.mem_centralizer_iff.mp hv) d (hιQ d₀)).symm⟩
  have hinv : ∀ v ∈ Subgroup.centralizer (Q : Set X), v ^ 2 = 1 → v = 1 ∨ v = c ^ 2 := by
    intro v hv hv2
    obtain ⟨hvc, hvd⟩ := hcent v hv
    rcases hsmall with hA7 | ⟨p, f, hpf, hmodel⟩
    ·
      exfalso
      obtain ⟨eA⟩ := hA7
      have hc7 := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
        (by norm_num) (by norm_num)
      let eAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
        MulEquiv.ofBijective _ hc7
      let χ : X →* Equiv.Perm (Fin 7) := eAut.symm.toMonoidHom.comp
        ((MulAut.congr eA).toMonoidHom.comp (MulAut.conjNormal (H := N)))
      have hχ : Function.Injective χ :=
        eAut.symm.injective.comp ((MulAut.congr eA).injective.comp
          (conjNormal_injective_of_centralizer_eq_bot N hC))
      exact quaternion_not_injective_perm hk (by norm_num) (χ.comp ι) (hχ.comp hι)
    ·
      obtain ⟨⟨hp, hf, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
      let eN : N ≃* PSL2 K :=
        e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
      have hq : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 := by simpa using hpf
      have hp2 := hp.two_le
      have hf2 : f ≤ 2 := by
        by_contra hf3
        push Not at hf3
        have h1 : p ^ 3 ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf3
        have h2 : p ^ f ≤ 9 := by omega
        have hp2' : p = 2 := by
          by_contra hp3
          have : 3 ≤ p := by omega
          have : 27 ≤ p ^ 3 := by
            calc 27 = 3 ^ 3 := by norm_num
              _ ≤ p ^ 3 := Nat.pow_le_pow_left this 3
          omega
        subst hp2'
        have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      have hpodd : Odd p := by
        apply hp.odd_of_ne_two
        rintro rfl
        have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      have hKodd : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hpodd, hf, hK⟩
      have hcard : 3 < Nat.card K := by rw [hK]; omega
      have hAut : Nat.card (K ≃+* K) ≤ 2 := by rw [card_ringEquiv_of_card hp hK]; exact hf2
      have : Fact p.Prime := ⟨hp⟩
      have hsurj := pGammaL2ToMulAutPSL2_surjective K hK hKodd hcard
      let ψ := normalPSL2ToPGammaL2 N K hKodd hcard eN hsurj
      have hψ : Function.Injective ψ :=
        normalPSL2ToPGammaL2_injective N K hKodd hcard eN hC hsurj
      have hc' : orderOf (ψ c) = 4 := by rw [orderOf_injective ψ hψ, hc]
      have hd' : (ψ d) ^ 2 = (ψ c) ^ 2 := by rw [← map_pow ψ d 2, ← map_pow ψ c 2, hd]
      have hdc' : ψ d * ψ c * (ψ d)⁻¹ = (ψ c)⁻¹ := by
        rw [← map_inv ψ d, ← map_mul ψ d c, ← map_mul ψ (d * c) d⁻¹, hdc, map_inv]
      have hv2' : (ψ v) ^ 2 = 1 := by rw [← map_pow ψ v 2, hv2, map_one]
      have hvc' : ψ v * ψ c = ψ c * ψ v := by rw [← map_mul ψ v c, ← map_mul ψ c v, hvc]
      have hvd' : ψ v * ψ d = ψ d * ψ v := by rw [← map_mul ψ v d, ← map_mul ψ d v, hvd]
      rcases pGammaL2_quaternion_centralizer hKodd hAut hc' hd' hdc' hv2' hvc' hvd' with h | h
      · left
        exact hψ (h.trans (map_one ψ).symm)
      · right
        exact hψ (h.trans (map_pow ψ c 2).symm)
  apply CFSG.SectionRank.pRank_le (by norm_num)
  intro E hEC hE
  have hsub : (E : Set X) ⊆ {1, c ^ 2} := by
    intro x hx
    rcases hinv x (hEC hx) (hE.2 x hx) with h | h
    · rw [h]
      exact Set.mem_insert _ _
    · rw [h]
      exact Set.mem_insert_of_mem _ rfl
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, c ^ 2} : Set X).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h3 : Nat.card E = (E : Set X).ncard := Nat.card_coe_set_eq (E : Set X)
  rw [h3, pow_one]
  omega

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
