module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7Std
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem normalizer_le_normalizer_centralizer' {K : Subgroup H} :
    normalizer (K : Set H) ≤ normalizer (centralizer (K : Set H) : Set H) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hg) k).mp hk
      rwa [inv_inv] at this
    have h1 := hx _ hk'
    calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * k := by group
  · intro hx k hk
    have hk' : g * k * g⁻¹ ∈ K := (mem_normalizer_iff.mp hg k).mp hk
    have h1 := hx _ hk'
    calc k * x = g⁻¹ * ((g * k * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * k * g⁻¹)) * g := by rw [h1]
      _ = x * k := by group

theorem isStandardSubgroup_of_sylow {K : Subgroup H} {b : H} (hb : orderOf b = 2)
    (hKq : IsQuasisimple ↥K) (hKb : K ≤ centralizer ({b} : Set H))
    (hbN : centralizer ({b} : Set H) ≤ normalizer (K : Set H))
    (hsyl : IsSylowIn (zpowers b) (centralizer (K : Set H)))
    (hV : ∃ V : Subgroup H, V ≤ K ∧ IsPGroup 2 V ∧ Nat.card V = 4) :
    IsStandardSubgroup K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (K : Set H) with hC
  have hbC : b ∈ C := by
    rw [hC, mem_centralizer_iff]
    intro k hk
    exact (mem_centralizer_singleton_iff.mp (hKb hk))
  have hCN : C ≤ normalizer (K : Set H) := centralizer_le_normalizer _
  obtain ⟨hbC', R, hR⟩ := hsyl
  have hconjb : ∀ A : Subgroup H, A ≤ C → IsPGroup 2 A →
      ∃ c ∈ C, ∀ x ∈ A, c * x * c⁻¹ ∈ zpowers b := by
    intro A hAC hA2
    obtain ⟨R', hR'⟩ := (hA2.comap_subtype (K := C)).exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥C) R' R
    have hmap : (R' : Subgroup ↥C).map (MulAut.conj c).toMonoidHom = (R : Subgroup ↥C) := by
      rw [← hc]
      rfl
    refine ⟨(c : H), c.2, fun x hx => ?_⟩
    have h1 : (⟨x, hAC hx⟩ : ↥C) ∈ R' := hR' (show (⟨x, hAC hx⟩ : ↥C) ∈ A.comap C.subtype from hx)
    have h2 := hmap ▸ mem_map_of_mem (MulAut.conj c).toMonoidHom h1
    rw [hR] at h2
    exact mem_subgroupOf.mp h2
  have hinv : ∀ t ∈ C, orderOf t = 2 → ∃ c ∈ C, c * t * c⁻¹ = b := by
    intro t htC ht
    obtain ⟨c, hc, hct⟩ := hconjb (zpowers t) ((zpowers_le).mpr htC)
      (IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]))
    refine ⟨c, hc, ?_⟩
    have h1 := hct t (mem_zpowers t)
    rcases eq_one_or_of_mem_zpowers hb h1 with h2 | h2
    · exfalso
      have : t = 1 := by
        calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
          _ = 1 := by rw [h2]; group
      rw [this, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · exact h2
  have hNC : normalizer (C : Set H) ≤ normalizer (K : Set H) := by
    intro g hg
    have h1 : g * b * g⁻¹ ∈ C := (mem_normalizer_iff.mp hg b).mp hbC
    have h2 : orderOf (g * b * g⁻¹) = 2 := by
      rw [← hb]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective b
    obtain ⟨c, hcC, hc⟩ := hinv _ h1 h2
    have hm : c * g ∈ centralizer ({b} : Set H) := by
      rw [mem_centralizer_singleton_iff]
      calc c * g * b = (c * (g * b * g⁻¹) * c⁻¹) * (c * g) := by group
        _ = b * (c * g) := by rw [hc]
    have := mul_mem (inv_mem (hCN hcC)) (hbN hm)
    rwa [inv_mul_cancel_left] at this
  refine ⟨hKq, ?_, ?_, ?_, ?_⟩
  ·
    rw [even_iff_two_dvd]
    have h1 : orderOf (⟨b, hbC⟩ : ↥C) = 2 := by rw [Subgroup.orderOf_mk, hb]
    rw [← h1]
    exact orderOf_dvd_natCard _
  ·
    intro g hg
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨⟨t, ht⟩, htord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(C ⊓ conjugate C g)) 2 h2
    rw [Subgroup.orderOf_mk] at htord
    obtain ⟨htC, htCg⟩ := mem_inf.mp ht
    rw [mem_conjugate_iff] at htCg
    obtain ⟨c, hcC, hc⟩ := hinv t htC htord
    have h3 : orderOf (g * t * g⁻¹) = 2 := by
      rw [← htord]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t
    obtain ⟨c', hc'C, hc'⟩ := hinv _ htCg h3
    have hm : c' * g * c⁻¹ ∈ centralizer ({b} : Set H) := by
      rw [mem_centralizer_singleton_iff]
      calc c' * g * c⁻¹ * b = c' * g * c⁻¹ * (c * t * c⁻¹) := by rw [hc]
        _ = (c' * (g * t * g⁻¹) * c'⁻¹) * (c' * g * c⁻¹) := by group
        _ = b * (c' * g * c⁻¹) := by rw [hc']
    have hmN : c' * g * c⁻¹ ∈ normalizer (C : Set H) :=
      normalizer_le_normalizer_centralizer' (hbN hm)
    apply hg
    have := mul_mem (mul_mem (inv_mem (le_normalizer hc'C)) hmN) (le_normalizer hcC)
    rwa [show c'⁻¹ * (c' * g * c⁻¹) * c = g by group] at this
  · exact le_antisymm hNC normalizer_le_normalizer_centralizer'
  ·
    intro g hKK
    obtain ⟨V, hVK, hV2, hV4⟩ := hV
    have hVg : conjugate V g ≤ C := by
      intro x hx
      rw [hC, mem_centralizer_iff]
      intro k hk
      have hxK : x ∈ conjugate K g := map_mono hVK hx
      have hKK' : ⁅conjugate K g, K⁆ = ⊥ := by rw [commutator_comm]; exact hKK
      have := (commutator_eq_bot_iff_le_centralizer.mp hKK') hxK
      exact (mem_centralizer_iff.mp this k hk)
    obtain ⟨c, -, hc⟩ := hconjb _ hVg (hV2.map _)
    have hle : (conjugate V g).map (MulAut.conj c).toMonoidHom ≤ zpowers b := by
      rintro _ ⟨x, hx, rfl⟩
      exact hc x hx
    have h4 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, card_conjugate, hV4,
      Nat.card_zpowers, hb] at h4
    omega

theorem IsSylowIn.of_le {R M M' : Subgroup H} (h : IsSylowIn R M) (hRM' : R ≤ M')
    (hM' : M' ≤ M) : IsSylowIn R M' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, P₀, hP₀⟩ := h
  have hidx : ¬ 2 ∣ (R.subgroupOf M).index := by
    rw [← hP₀]
    exact P₀.not_dvd_index
  have hR2 : IsPGroup 2 R := IsSylowIn.isPGroup ⟨hRM'.trans hM', P₀, hP₀⟩
  have h1 : ¬ 2 ∣ (R.subgroupOf M').index := by
    intro h2
    apply hidx
    have h3 := Subgroup.relIndex_mul_relIndex R M' M hRM' hM'
    change 2 ∣ R.relIndex M
    rw [← h3]
    exact Dvd.dvd.mul_right h2 _
  exact ⟨hRM', (hR2.comap_subtype (K := M')).toSylow h1, rfl⟩

omit [Finite H] in
theorem isTwoPComponent_of_isPComponent' {L : Subgroup H} (hL : IsPComponent 2 L) :
    Assembly.ComponentType.IsTwoPComponent L := by
  have key : ∀ (N : Subgroup H) [N.Normal], N = pPrimeCore 2 H →
      ((∃ K : Subgroup (H ⧸ N), CFSG.Assembly.IsComponentOf K ⊤ ∧
        CFSG.Assembly.IsSubnormal L ⊤ ∧ L.map (QuotientGroup.mk' N) = K ∧
        ∀ J : Subgroup H, J < L → CFSG.Assembly.IsSubnormal J ⊤ →
          J.map (QuotientGroup.mk' N) ≠ K) ↔ IsPComponent 2 L) := by
    rintro N _ rfl
    unfold IsPComponent
    simp only [AssemblyBPredicates.isComponentOf_top_iff_native,
      AssemblyBPredicates.isSubnormal_top_iff_mathlib]
  exact (key _ (B5a.assembly_oddCore_eq H)).mpr hL

end Seven

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem K_eq_V (hKa : conjugate h.K h.a = h.K) : h.K = h.toHyp52.V := by
  have h1 := h.layer_eq_K
  rw [hKa, sup_idem] at h1
  exact h1

theorem isQuasisimple_K (hLB : Assembly.ComponentType.LocalBProperty H) : IsQuasisimple ↥h.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKW, hKpc⟩ := h.isPComponent_K
  have hB2 : IsPGroup 2 h.B := h.toHyp52.isPGroup_S.to_le h.toHyp52.B_le_S
  obtain ⟨-, -, hq⟩ := hLB h.B h.B_ne_bot hB2 (h.K.subgroupOf (normalizer (h.B : Set H)))
    (Seven.isTwoPComponent_of_isPComponent' hKpc)
  have hq' := (AssemblyBPredicates.isQuasisimple_iff_native _).mp hq
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe hKW)).mp hq'

omit [Finite H] in
theorem centralizer_le_coreActionKernel (K : Subgroup H) :
    centralizer (K : Set H) ≤ coreActionKernel K := by
  intro g hg
  refine ⟨centralizer_le_normalizer _ hg, fun j hj => ?_⟩
  have h1 : j * g = g * j := mem_centralizer_iff.mp hg j hj
  rw [show j⁻¹ * g⁻¹ * j * g = 1 by
    calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
      _ = j⁻¹ * g⁻¹ * (g * j) := by rw [h1]
      _ = 1 := by group]
  exact one_mem _

theorem isStandardSubgroup_K
    (hLB : Assembly.ComponentType.LocalBProperty H)
    (hB : Nat.card h.B = 2) (hKa : conjugate h.K h.a = h.K) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKL : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSL 2 p (2 * f)) :
    IsStandardSubgroup h.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hBb⟩ := exists_eq_zpowers_of_card_two hB
  have hWb : normalizer (h.B : Set H) = centralizer ({b} : Set H) := by
    rw [hBb]
    exact UnbalancedCorr.normalizer_zpowers_eq_centralizer hb
  obtain ⟨hKW, -⟩ := h.isPComponent_K
  have hKV := h.K_eq_V hKa
  have hKb : h.K ≤ centralizer ({b} : Set H) := hWb ▸ hKW
  have hbN : centralizer ({b} : Set H) ≤ normalizer (h.K : Set H) := by
    rw [← hWb, hKV]
    exact le_normalizer_layerIn_self _
  have hsyl : Seven.IsSylowIn (zpowers b) (centralizer (h.K : Set H)) := by
    obtain ⟨hBC, R, hR⟩ := h.toHyp52.sylow_kernel
    have h1 : Seven.IsSylowIn h.B (coreActionKernel h.toHyp52.V) := ⟨hBC, R, hR⟩
    rw [← hKV] at h1
    have hBcent : h.B ≤ centralizer (h.K : Set H) := by
      rw [hBb, zpowers_le, mem_centralizer_iff]
      intro k hk
      exact mem_centralizer_singleton_iff.mp (hKb hk)
    rw [← hBb]
    exact h1.of_le hBcent (centralizer_le_coreActionKernel _)
  have hV : ∃ V : Subgroup H, V ≤ h.K ∧ IsPGroup 2 V ∧ Nat.card V = 4 := by
    have e : ↥h.K ⧸ CFSG.oddCore ↥h.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K :=
      QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two h.K)
    have hA : IsQuasisimple (↥h.K ⧸ CFSG.oddCore ↥h.K) :=
      LocalCores.isQuasisimple_of_mulEquiv e.symm h.toHyp52.isQuasisimple_K
    have h2 := UnbalancedGS.small_source_models_force_rank_at_least_two hA
      (Or.inl ⟨p, 2 * f, hp, hp.odd_of_ne_two hp2, by omega,
        SectionRank.statedClassicalModel_of_mulEquiv e
          (GSLit.statedClassicalModel_of_lieModel_psl_two hKL)⟩)
    obtain ⟨E, hE, hE4⟩ := UnbalancedCorr.exists_four_of_two_le_pRank h2
    refine ⟨E.map h.K.subtype, map_subtype_le _, ?_, ?_⟩
    · exact (IsPGroup.of_card (p := 2) (n := 2) (by rw [hE4]; norm_num)).map _
    · rw [Subgroup.card_map_of_injective h.K.subtype_injective, hE4]
  exact Seven.isStandardSubgroup_of_sylow hb (h.isQuasisimple_K hLB) hKb hbN hsyl hV

theorem not_normal_K (hLB : Assembly.ComponentType.LocalBProperty H)
    (hB : Nat.card h.B = 2) : ¬ h.K.Normal := by
  intro hKn
  obtain ⟨b, hb, hBb⟩ := exists_eq_zpowers_of_card_two hB
  obtain ⟨hKW, -⟩ := h.isPComponent_K
  have hWb : normalizer (h.B : Set H) = centralizer ({b} : Set H) := by
    rw [hBb]
    exact UnbalancedCorr.normalizer_zpowers_eq_centralizer hb
  obtain ⟨-, -, hC, -, huniq⟩ := h.generalizedFitting_simple
  have hKc : IsComponent h.K := ⟨h.isQuasisimple_K hLB, hKn.isSubnormal⟩
  have hKeq := huniq h.K hKc
  have hbC : b ∈ centralizer (h.K : Set H) := by
    rw [mem_centralizer_iff]
    intro k hk
    have := hWb ▸ hKW hk
    exact mem_centralizer_singleton_iff.mp this
  rw [hKeq, hC, mem_bot] at hbC
  rw [hbC, orderOf_one] at hb
  exact absurd hb (by norm_num)

theorem lieModel_psp_of_eq
    (hRS : RestrictedStandardInput) (hRec : CFSp4RecognitionStd)
    (hKG : SectionRank.IsKGroupCat H) (hLB : Assembly.ComponentType.LocalBProperty H)
    (hB : Nat.card h.B = 2) (hKa : conjugate h.K h.a = h.K) (hP8 : 8 ≤ Nat.card h.toHyp52.P)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hJL : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f)
    (hKL : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSL 2 p (2 * f)) :
    Blueprint.LieModel ↥(generalizedFitting H) .PSp 2 p f := by
  have hstd := h.isStandardSubgroup_K hLB hB hKa hp hp2 hf hKL
  have h5' : 5 ≤ p ^ (2 * f) := le_trans h5 (Nat.pow_le_pow_right hp.pos (by omega))
  have hres := hRS H hKG h.oddCore_eq_bot h.K hstd (h.not_normal_K hLB hB)
    (Or.inl ⟨p, 2 * f, hp, hp2, by omega, h5', hKL⟩)
  exact hRec H h hres hB hKa hP8 p f hp hp2 hf h5 hJL hKL

end Hyp59

end CFSG.ComponentClassification.GSThmB
