module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCHeAct

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_normalizer_inf {S A B : Subgroup X} (hA : S ≤ normalizer (A : Set X))
    (hB : S ≤ normalizer (B : Set X)) : S ≤ normalizer ((A ⊓ B : Subgroup X) : Set X) :=
  fun s hs => mem_normalizer_iff.mpr fun y => by
    have h1 := mem_normalizer_iff.mp (hA hs) y
    have h2 := mem_normalizer_iff.mp (hB hs) y
    simp only [mem_inf] at h1 h2 ⊢
    rw [h1, h2]

theorem eq_one_of_mem_oddIn {J : Subgroup X} {x : X} (hx : x ∈ (pPrimeCore 2 J).map J.subtype)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy, rfl⟩ := hx
  set w : ↥(pPrimeCore 2 ↥J) := ⟨y, hy⟩
  have h1 : orderOf w ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf w = 1 := (Nat.Coprime.coprime_dvd_left h1
    (Nat.Coprime.pow_left k pPrimeCore_coprime_card)).eq_one_of_dvd (orderOf_dvd_natCard w)
  have h3 : w = 1 := orderOf_eq_one_iff.mp h2
  have h4 : y = 1 := congrArg Subtype.val h3
  rw [h4, map_one]

theorem le_coreActionKernel_of_component_ne {C K K' : Subgroup X} (hKC : K ≤ C)
    (hK'C : K' ≤ C) (hK : IsPComponent 2 (K.subgroupOf C))
    (hK' : IsPComponent 2 (K'.subgroupOf C)) (hne : K ≠ K') : K' ≤ coreActionKernel K := by
  have hc := commutator_le_oddIn_of_ne hKC hK'C hK hK' hne
  have hne' : K.subgroupOf C ≠ K'.subgroupOf C := by
    intro h
    apply hne
    have h1 := congrArg (Subgroup.map C.subtype) h
    rwa [map_subgroupOf_eq_of_le hKC, map_subgroupOf_eq_of_le hK'C] at h1
  obtain ⟨-, h2⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two
    _ _ hK hK'
  obtain ⟨hN, -, -, -⟩ := h2 hne'
  have hO := UnbalancedCorr.map_pPrimeCore_eq_inf_of_subgroupOf hKC hK.choose_spec.2.1
  intro x hx
  have hxN : x ∈ normalizer (K : Set X) :=
    mem_normalizer_of_subgroupOf hKC (g := ⟨x, hK'C hx⟩)
      (hN (show (⟨x, hK'C hx⟩ : ↥C) ∈ K'.subgroupOf C from hx))
  refine mem_coreActionKernel.mpr ⟨hxN, fun k hk => ?_⟩
  have h1 : k⁻¹ * x⁻¹ * k * x ∈ ⁅K, K'⁆ := by
    have := commutator_mem_commutator (inv_mem hk) (inv_mem hx)
    rwa [commutatorElement_def, inv_inv, inv_inv] at this
  have h3 : k⁻¹ * x⁻¹ * k * x ∈ K := by
    have := (mem_normalizer_iff.mp (inv_mem hxN) k).mp hk
    rw [inv_inv] at this
    rw [show k⁻¹ * x⁻¹ * k * x = k⁻¹ * (x⁻¹ * k * x) by group]
    exact mul_mem (inv_mem hk) this
  rw [hO]
  exact mem_inf.mpr ⟨h3, hc h1⟩

omit [Finite X] in
theorem card_inf_centralizer_eq (D : Subgroup X) :
    Nat.card ↥(D ⊓ centralizer (D : Set X)) = Nat.card (center ↥D) :=
  Nat.card_congr
    { toFun := fun x => ⟨⟨x, (mem_inf.mp x.2).1⟩, mem_center_iff.mpr fun d => Subtype.ext
        (mem_centralizer_iff.mp (mem_inf.mp x.2).2 d d.2)⟩
      invFun := fun z => ⟨z.1, mem_inf.mpr ⟨z.1.2, mem_centralizer_iff.mpr fun d hd =>
        congrArg Subtype.val (mem_center_iff.mp z.2 ⟨d, hd⟩)⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

namespace Config

variable {a : X} {J E : Subgroup X}

omit [Finite X] in
theorem mem_oddIn_of_mem_coreActionKernel (h : Config a J E) {x : X} (hxJ : x ∈ J)
    (hxK : x ∈ coreActionKernel J) : x ∈ (pPrimeCore 2 J).map J.subtype := by
  obtain ⟨e7⟩ := h.equiv
  have hc : ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
    rw [mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H j =>
      obtain ⟨o, ho, hoe⟩ := (mem_coreActionKernel.mp hxK).2 j j.2
      have hoe' : (o : X) = (j : X)⁻¹ * x⁻¹ * j * x := hoe
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have he : (j * ⟨x, hxJ⟩)⁻¹ * (⟨x, hxJ⟩ * j) = o⁻¹ := by
        apply Subtype.ext
        rw [coe_mul, coe_inv, coe_mul, coe_mul, coe_inv, hoe']
        group
      rw [he]
      exact inv_mem ho
  have hc' : e7 ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) ∈ center (alternatingGroup (Fin 7)) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨q, rfl⟩ := e7.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hc q]
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot, map_eq_one_iff e7 e7.injective,
    QuotientGroup.eq_one_iff] at hc'
  exact ⟨⟨x, hxJ⟩, hc', rfl⟩

theorem not_mem (h : Config a J E) : a ∉ J := by
  intro haJ
  have haK : a ∈ coreActionKernel J := by
    refine mem_coreActionKernel.mpr ⟨Subgroup.le_normalizer haJ, fun j hj => ?_⟩
    have hja : j * a = a * j := mem_centralizer_singleton_iff.mp (h.le_centralizer hj)
    rw [show j⁻¹ * a⁻¹ * j * a = j⁻¹ * (a⁻¹ * (j * a)) by group, hja, inv_mul_cancel_left,
      inv_mul_cancel]
    exact one_mem _
  have h2 : a ^ 2 ^ 1 = 1 := by rw [pow_one, ← h.orderOf_eq, pow_orderOf_eq_one]
  have h3 := eq_one_of_mem_oddIn (h.mem_oddIn_of_mem_coreActionKernel haJ haK) h2
  have h4 := h.orderOf_eq
  rw [h3, orderOf_one] at h4
  exact absurd h4 (by norm_num)

theorem card_inf (h : Config a J E) {S : Subgroup X}
    (hSH : S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) :
    Nat.card ↥(S ⊓ J) = 8 ∧
      Nat.card ↥(S ⊓ J ⊓ centralizer ((S ⊓ J : Subgroup X) : Set X)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 ((P₀ : Subgroup _).map
        (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)).subtype) := P₀.isPGroup'.map _
    rwa [hP₀, map_subgroupOf_eq_of_le hSH] at h1
  obtain ⟨T, hT⟩ := UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer hSH hSsyl
    (le_inf h.le_centralizer Subgroup.le_normalizer) inf_le_right
  obtain ⟨e7⟩ := h.equiv
  set f : ↥J →* alternatingGroup (Fin 7) :=
    e7.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J)) with hf_def
  have hf : Function.Surjective f := e7.surjective.comp (QuotientGroup.mk'_surjective _)
  set T' := T.mapSurjective hf with hT'
  obtain ⟨m, -, ⟨eD⟩⟩ := GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven T'
  set ι : ↥(S ⊓ J) →* ↥J := inclusion (inf_le_right : S ⊓ J ≤ J) with hι
  set g := f.comp ι with hg_def
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h0 : e7 (QuotientGroup.mk' (pPrimeCore 2 ↥J) (ι d)) = 1 := hd
    have h1 := (map_eq_one_iff e7 e7.injective).mp h0
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (d : X) ∈ (pPrimeCore 2 ↥J).map J.subtype := ⟨ι d, h1, rfl⟩
    obtain ⟨k, hk⟩ := hS2 ⟨d, (mem_inf.mp d.2).1⟩
    have h3 : (d : X) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subtype.ext (eq_one_of_mem_oddIn h2 h3)
  have hrange : g.range = (T' : Subgroup (alternatingGroup (Fin 7))) := by
    ext y
    constructor
    · rintro ⟨d, rfl⟩
      show g d ∈ (T : Subgroup ↥J).map f
      refine ⟨ι d, ?_, rfl⟩
      rw [hT]
      exact d.2
    · intro hy
      obtain ⟨t, ht, rfl⟩ : y ∈ (T : Subgroup ↥J).map f := hy
      have ht' : (t : X) ∈ S ⊓ J := by
        rw [hT] at ht
        exact ht
      exact ⟨⟨t, ht'⟩, rfl⟩
  set ψ : ↥(S ⊓ J) ≃* DihedralGroup (2 ^ m) :=
    ((MonoidHom.ofInjective hg).trans (MulEquiv.subgroupCongr hrange)).trans eD with hψ
  have hT'8 : Nat.card ↥(T' : Subgroup (alternatingGroup (Fin 7))) = 8 := by
    rw [Sylow.card_eq_multiplicity, GSThmB.card_alternatingGroup_seven,
      show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by norm_num)]
  have hDm : Nat.card ↥(S ⊓ J) = 2 * 2 ^ m := by
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
  have hTm : Nat.card ↥(T' : Subgroup (alternatingGroup (Fin 7))) = 2 * 2 ^ m := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hm : m = 2 := by
    have h1 : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl h1
  subst hm
  have hcen : Nat.card (center (DihedralGroup (2 ^ 2))) = 2 := by
    rw [DihedralGroup.center_eq_closure_of_even_ne_two ⟨2, by norm_num⟩ (by norm_num),
      Nat.card_zpowers]
    exact orderOf_eq_prime (by decide) (by decide)
  refine ⟨by rw [hDm]; norm_num, ?_⟩
  rw [card_inf_centralizer_eq, Nat.card_congr (Subgroup.centerCongr ψ).toEquiv, hcen]

theorem card_le_sixteen (h : Config a J E) {S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ normalizer (J : Set X)) :
    Nat.card S ≤ 16 * Nat.card ↥(S ⊓ coreActionKernel J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e7⟩ := h.equiv
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7))
  have hc : Function.Bijective c :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)
  have hAut : Nat.card (MulAut (↥J ⧸ pPrimeCore 2 ↥J)) = 5040 := by
    rw [Nat.card_congr (MulAut.congr e7).toEquiv,
      ← Nat.card_congr (MulEquiv.ofBijective c hc).toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm]
    norm_num
  let ρ : ↥S →* MulAut (↥J ⧸ pPrimeCore 2 ↥J) := (oddQuotConj J).comp (inclusion hSN)
  have hker : Nat.card ρ.ker ≤ Nat.card ↥(S ⊓ coreActionKernel J) := by
    have hle : ρ.ker ≤ (S ⊓ coreActionKernel J).subgroupOf S := by
      intro s hs
      rw [mem_subgroupOf]
      exact mem_inf.mpr ⟨s.2, (oddQuotConj_eq_one_iff (inclusion hSN s)).mp
        (MonoidHom.mem_ker.mp hs)⟩
    calc Nat.card ρ.ker ≤ Nat.card ((S ⊓ coreActionKernel J).subgroupOf S) := card_le_of_le hle
      _ = Nat.card ↥(S ⊓ coreActionKernel J) :=
        Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card ρ.range ≤ 16 := by
    have h2 : IsPGroup 2 ρ.range := hS2.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hdvd : Nat.card ρ.range ∣ 16 * 315 := by
      rw [show (16 * 315 : ℕ) = 5040 by norm_num, ← hAut]
      exact card_subgroup_dvd_card ρ.range
    rw [hk] at hdvd ⊢
    have hcop : Nat.Coprime (2 ^ k) 315 := Nat.Coprime.pow_left k (by norm_num)
    exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)
  have h1 := card_ker_mul_card_range ρ
  calc Nat.card S = Nat.card ρ.ker * Nat.card ρ.range := h1.symm
    _ ≤ Nat.card ↥(S ⊓ coreActionKernel J) * 16 := Nat.mul_le_mul hker hrange
    _ = 16 * Nat.card ↥(S ⊓ coreActionKernel J) := mul_comm _ _

end Config

end CFSG.ComponentClassification.GSThmB.CorC
