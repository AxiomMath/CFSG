module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

open scoped commutatorElement

def a7s_five : Finset (Fin 7) := {0, 3, 4, 5, 6}

theorem a7s_map_ofSubtype :
    (alternatingGroup a7s_five).map (Perm.ofSubtype : Perm a7s_five →* Perm (Fin 7)) =
      a7Five := by
  rw [alternatingGroup.map_ofSubtype]
  ext σ
  rw [Subgroup.mem_inf, Perm.mem_range_ofSubtype_iff, mem_a7Five_iff, and_comm]
  refine and_congr_right fun _ => ⟨fun h => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ x hx => ?_⟩
  · by_contra h1
    exact absurd (h (Perm.mem_support.mpr h1)) (by decide)
  · by_contra h1
    exact absurd (h (Perm.mem_support.mpr h1)) (by decide)
  · have hx' : σ x ≠ x := Perm.mem_support.mp hx
    change x ∈ a7s_five
    fin_cases x <;> simp_all [a7s_five]

noncomputable def a7s_fiveEquiv : alternatingGroup a7s_five ≃* a7Five :=
  ((alternatingGroup a7s_five).equivMapOfInjective _ Perm.ofSubtype_injective).trans
    (MulEquiv.subgroupCongr a7s_map_ofSubtype)

theorem a7s_card_five : 5 ≤ Nat.card a7s_five := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

instance a7s_isSimpleGroup_a7Five : IsSimpleGroup a7Five :=
  have : IsSimpleGroup (alternatingGroup a7s_five) :=
    alternatingGroup.isSimpleGroup a7s_card_five
  a7s_fiveEquiv.symm.isSimpleGroup

instance a7s_isPerfect_a7Five : Group.IsPerfect a7Five :=
  have : Group.IsPerfect (alternatingGroup a7s_five) :=
    ⟨commutator_alternatingGroup_eq_top a7s_card_five⟩
  Group.IsPerfect.ofSurjective (f := a7s_fiveEquiv.toMonoidHom) a7s_fiveEquiv.surjective

theorem a7s_not_isSolvable_a7Five : ¬ Group.IsSolvable a7Five :=
  Group.IsPerfect.not_isSolvable _

theorem a7s_vOne_le_a7Five : vOne ≤ a7Five := by
  rintro _ ⟨m, rfl⟩
  have h : ∀ m : Fin 4, vOneF m 1 = 1 ∧ vOneF m 2 = 2 := by decide
  exact mem_a7Five_iff.mpr ⟨(vOneF_spec m).2, (h m).1, (h m).2⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a7s_isSubnormal_of_open {A B : Subgroup G} (h : CFSG.Open.IsSubnormal A B)
    (hB : B.IsSubnormal) : A.IsSubnormal :=
  h.mathlib hB

omit [Finite G] in
theorem a7s_isSubnormal_subgroupOf {A B : Subgroup G} (h : CFSG.Open.IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal := by
  have h1 : CFSG.Open.IsSubnormal (A.subgroupOf B) (B.subgroupOf B) :=
    CFSG.Quasithin.A3.subnormal_comap B.subtype h
  rw [Subgroup.subgroupOf_self] at h1
  exact a7s_isSubnormal_of_open h1 Subgroup.IsSubnormal.top

omit [Finite G] in
theorem a7s_eq_bot_or_eq_of_isSubnormal {A B : Subgroup G} [hB : IsSimpleGroup B]
    (h : CFSG.Open.IsSubnormal A B) : A = ⊥ ∨ A = B := by
  have hAB := CFSG.Quasithin.A3.subnormal_le h
  rcases (a7s_isSubnormal_subgroupOf h).eq_bot_or_top_of_isSimpleGroup hB with h1 | h1
  · exact Or.inl ((Subgroup.subgroupOf_eq_bot.mp h1).eq_bot_of_le hAB)
  · exact Or.inr (le_antisymm hAB (Subgroup.subgroupOf_eq_top.mp h1))

theorem a7s_mem_normalizer_of_map_le {N : Subgroup G} {g : G}
    (h : N.map (MulAut.conj g).toMonoidHom ≤ N) : g ∈ normalizer (N : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]))

omit [Finite G] in
theorem a7s_le_normalizer_sup {A B L : Subgroup G} (hA : L ≤ normalizer (A : Set G))
    (hB : L ≤ normalizer (B : Set G)) : L ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hg)]

theorem a7s_le_of_isPGroup {p : ℕ} [hp : Fact p.Prime] {N L P : Subgroup G} (hNL : N ≤ L)
    (hLN : L ≤ normalizer (N : Set G)) (hidx : ¬ p ∣ N.relIndex L) (hPL : P ≤ L)
    (hP : IsPGroup p P) : P ≤ N := by
  have hN : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have hP' : IsPGroup p (P.subgroupOf L) := hP.comap_subtype
  obtain ⟨k, hk⟩ := hP'.exists_card_eq
  have h1 : (N.subgroupOf L).relIndex (P.subgroupOf L) = 1 := by
    apply Nat.eq_one_of_dvd_coprimes (a := N.relIndex L) (b := p ^ k)
    · exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hidx).symm
    · exact Subgroup.relIndex_dvd_index_of_normal _ _
    · rw [← hk]
      exact Subgroup.relIndex_dvd_card _ _
  have h2 := Subgroup.relIndex_eq_one.mp h1
  intro x hx
  exact h2 (show (⟨x, hPL hx⟩ : L) ∈ P.subgroupOf L from hx)

omit [Finite G] in
theorem a7s_relIndex_dvd {M L K S : Subgroup G} (hML : M ≤ L)
    (hLM : L ≤ normalizer (M : Set G)) (hLMK : L ≤ M ⊔ K) (hKL : K ≤ L) (hSM : S ≤ M) :
    M.relIndex L ∣ S.relIndex K := by
  have hN : (M.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hML).mpr hLM
  have htop : K.subgroupOf L ⊔ M.subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKL hML, Subgroup.subgroupOf_eq_top]
    exact hLMK.trans (sup_comm M K).le
  have h1 : M.relIndex L = M.relIndex K := by
    rw [← Subgroup.relIndex_subgroupOf hKL, ← Subgroup.relIndex_sup_right (K.subgroupOf L)
      (M.subgroupOf L), htop, Subgroup.relIndex_top_right]
    rfl
  rw [h1]
  exact Subgroup.relIndex_dvd_of_le_left K hSM

theorem a7s_perfectCore_eq_of_isSubnormal {A B Y P : Subgroup G}
    (h : CFSG.Open.IsSubnormal A B) (hYA : Y ≤ A) (hBY : B ≤ Y ⊔ P)
    (hBP : B ≤ normalizer (P : Set G)) (hP : Group.IsSolvable P) :
    CFSG.Quasithin.perfectCore A = CFSG.Quasithin.perfectCore B := by
  induction h with
  | refl => rfl
  | @step A M B hAM hAn hMB ih =>
    have hMB' : M ≤ B := CFSG.Quasithin.A3.subnormal_le hMB
    rw [← ih (hYA.trans hAM) hBY hBP]
    refine le_antisymm (CFSG.Quasithin.perfectCore_mono hAM)
      (CFSG.Quasithin.le_perfectCore_of_perfect ?_ (CFSG.Quasithin.perfectCore_perfect M))
    refine CFSG.Quasithin.perfectCore_le_of_sup_solvable hAM hAn
      (CFSG.Quasithin.A3.eq_sup_inf_of_le_sup (hAM.trans (hMB'.trans hBP)) hAM
        (hMB'.trans (hBY.trans (sup_le_sup_right hYA P)))) ?_
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_right)

theorem a7s_commutator_mem {I Y S K : Subgroup G} (hYI : Y ≤ I) (hKI : K ≤ I)
    (hSn : I ≤ normalizer (S : Set G)) (hKn : I ≤ normalizer (K : Set G))
    (hYs : (Y.subgroupOf I).IsSubnormal) (hK : Group.IsSolvable K) {N : Subgroup Y}
    [N.Normal] (hN : N = S.subgroupOf Y) (hQ : CFSG.IsQuasisimple (↥Y ⧸ N)) :
    ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ S := by
  set S' : Subgroup I := S.subgroupOf I with hS'
  have hS'n : S'.Normal := ⟨fun n hn g => by
    rw [hS', Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hSn g.2) n).mp hn⟩
  set π : I →* I ⧸ S' := QuotientGroup.mk' S' with hπ
  set φ : Y →* I ⧸ S' := π.comp (Subgroup.inclusion hYI) with hφ
  have hker : φ.ker = N := by
    rw [hN]
    ext y
    simp [hφ, hπ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, hS', Subgroup.mem_subgroupOf]
  have hcomp : CFSG.IsComponent φ.range := by
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange φ)) hQ, ?_⟩
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hYs.map (QuotientGroup.mk'_surjective S')
  set K' : Subgroup (I ⧸ S') := (K.subgroupOf I).map π with hK'
  have hKIn : (K.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKI).mpr hKn
  have hK'n : K'.Normal := hKIn.map π (QuotientGroup.mk'_surjective S')
  have hK's : Group.IsSolvable K' := by
    have : Group.IsSolvable (K.subgroupOf I) := Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hKI).toMonoidHom) (MulEquiv.injective _)
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective (K.subgroupOf I))
  have hc := (CFSG.LocalCores.component_solvable_centralizer hK's hK'n.isSubnormal).1 _ hcomp
  intro y hy k hk
  have hmem : ⁅φ ⟨y, hy⟩, π ⟨k, hKI hk⟩⁆ ∈ ⁅φ.range, K'⁆ :=
    Subgroup.commutator_mem_commutator ⟨_, rfl⟩ (Subgroup.mem_map_of_mem _ hk)
  rw [hc, Subgroup.mem_bot] at hmem
  have h2 : π ⁅(⟨y, hYI hy⟩ : I), ⟨k, hKI hk⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact hmem
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hS', Subgroup.mem_subgroupOf] at h2
  simpa [commutatorElement_def] using h2

omit [Finite G] in
theorem a7s_le_normalizer_K (H : Subgroup G) : H ≤ normalizer (a7K H : Set G) := by
  have : ((a7K H).subgroupOf H).Normal := by
    rw [a7K, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (a7K_le H)).mp this

omit [Finite G] in
theorem a7s_K_le_I {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι) :
    a7K H ≤ a7I H ι := by
  rintro _ ⟨k, hk, rfl⟩
  refine mem_a7I_iff.mpr ⟨k, ?_, rfl⟩
  have hk' : ι k = 1 := by
    rw [← MonoidHom.mem_ker, hF.ker_eq]
    exact hk
  rw [hk']
  exact one_mem _

omit [Finite G] in
theorem a7s_map_I {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι) :
    ((a7I H ι).subgroupOf H).map ι = a7Five := by
  rw [a7I, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective,
    Subgroup.map_comap_eq_self (a7Five_le_alternatingGroup.trans hF.A7_le)]

omit [Finite G] in
theorem a7s_le_K_of_map_eq_bot {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {X : Subgroup G} (hXH : X ≤ H) (h : (X.subgroupOf H).map ι = ⊥) :
    X ≤ a7K H := by
  intro x hx
  have hmem : ι ⟨x, hXH hx⟩ ∈ (X.subgroupOf H).map ι := Subgroup.mem_map_of_mem ι hx
  rw [h, Subgroup.mem_bot] at hmem
  have hk : (⟨x, hXH hx⟩ : H) ∈ primeComplementCore (G := H) 3 := by
    rw [← hF.ker_eq]
    exact hmem
  exact ⟨_, hk, rfl⟩

omit [Finite G] in
theorem a7s_le_sup_K {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι)
    {X : Subgroup G} (h : (X.subgroupOf H).map ι = a7Five) : a7I H ι ≤ X ⊔ a7K H := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := mem_a7I_iff.mp hg
  rw [← h] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hk : y⁻¹ * x ∈ primeComplementCore (G := H) 3 := by
    rw [← hF.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have hxy : (x : G) = (y : G) * ((y⁻¹ * x : H) : G) := by simp
  rw [hxy]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))
    (Subgroup.mem_sup_right ⟨_, hk, rfl⟩)

theorem a7s_isSolvable_K {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) : Group.IsSolvable (a7K H) := by
  have hSK := hF.sylow.le
  have hKS : a7K H ≤ normalizer (pCoreOf 2 H : Set G) := (a7K_le H).trans hF.H_norm.ge
  have hidx : ¬ 2 ∣ (pCoreOf 2 H).relIndex (a7K H) :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hF.sylow).2.2
  set N : Subgroup (a7K H) := (pCoreOf 2 H).subgroupOf (a7K H)
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSK).mpr hKS
  have h1 : Group.IsSolvable N := by
    have : IsPGroup 2 N := hF.sylow.isPGroup.comap_subtype
    have := this.isNilpotent
    infer_instance
  have h2 : Group.IsSolvable (↥(a7K H) ⧸ N) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx)
  exact Group.isSolvable_of_subgroup_quotient N

omit [Finite G] in
theorem a7s_map_eq_bot_or_eq {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {X : Subgroup G} (hX : CFSG.Open.IsSubnormal X (a7I H ι)) :
    (X.subgroupOf H).map ι = ⊥ ∨ (X.subgroupOf H).map ι = a7Five := by
  have h1 : CFSG.Open.IsSubnormal ((X.subgroupOf H).map ι) (((a7I H ι).subgroupOf H).map ι) :=
    CFSG.Quasithin.A3.subnormal_map ι (CFSG.Quasithin.A3.subnormal_comap H.subtype hX)
  rw [a7s_map_I hF] at h1
  exact a7s_eq_bot_or_eq_of_isSubnormal h1

omit [Finite G] in
theorem a7s_V_le_I {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι) :
    V ≤ a7I H ι := by
  intro v hv
  refine mem_a7I_iff.mpr ⟨⟨v, hF.V_le hv⟩, ?_, rfl⟩
  have : ι ⟨v, hF.V_le hv⟩ ∈ (V.subgroupOf H).map ι := Subgroup.mem_map_of_mem ι hv
  rw [hF.V_img] at this
  exact a7s_vOne_le_a7Five this

theorem a7s_pCore_eq {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι)
    {Y : Subgroup G} (hYI : Y ≤ a7I H ι) (hYs : CFSG.Open.IsSubnormal Y (a7I H ι)) :
    CFSG.pCore 2 Y = (pCoreOf 2 H).subgroupOf Y := by
  have hYH : Y ≤ H := hYI.trans (a7I_le H ι)
  have hHS : H ≤ normalizer (pCoreOf 2 H : Set G) := hF.H_norm.ge
  apply le_antisymm
  · set T : Subgroup G := (CFSG.pCore 2 Y).map Y.subtype with hT
    have hTY : T ≤ Y := Subgroup.map_subtype_le _
    have hT2 : IsPGroup 2 T := CFSG.pCore_isPGroup.map Y.subtype
    have hTs : CFSG.Open.IsSubnormal T (a7I H ι) := by
      refine CFSG.Open.IsSubnormal.step hTY ?_ hYs
      rw [hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
      infer_instance
    have hTK : T ≤ a7K H := by
      rcases a7s_map_eq_bot_or_eq hF hTs with h | h
      · exact a7s_le_K_of_map_eq_bot hF (hTY.trans hYH) h
      · exfalso
        have h2 : IsPGroup 2 ((T.subgroupOf H).map ι) := hT2.comap_subtype.map ι
        rw [h] at h2
        have := h2.isNilpotent
        exact a7s_not_isSolvable_a7Five inferInstance
    have hTS : T ≤ pCoreOf 2 H :=
      a7s_le_of_isPGroup hF.sylow.le ((a7K_le H).trans hHS)
        (CFSG.ABGLocalTools.isSylowOf_iff.mp hF.sylow).2.2 hTK hT2
    intro y hy
    exact hTS ⟨y, hy, rfl⟩
  · refine le_sSup ⟨⟨fun n hn g => ?_⟩, hF.sylow.isPGroup.comap_subtype⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hHS (hYH g.2)) n).mp hn

theorem A7Frame.exists_perfect_normal {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {Y : Subgroup G} (hYI : Y ≤ a7I H ι)
    (hYs : IsSubnormal Y (a7I H ι)) (hYx : CFSG.AGLEmbedding.InClassXBlock Y) :
    ∃ Y₁ : Subgroup G, Y₁ ≤ Y ∧ a7I H ι ≤ normalizer (Y₁ : Set G) ∧ Group.IsPerfect Y₁ ∧
      (Y₁.subgroupOf H).map ι = a7Five ∧
      (∀ y ∈ Y₁, ∀ k ∈ a7K H, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) ∧ V ≤ Y₁ ⊔ pCoreOf 2 H := by
  have hIH : a7I H ι ≤ H := a7I_le H ι
  have hKI : a7K H ≤ a7I H ι := a7s_K_le_I hF
  have hSI : pCoreOf 2 H ≤ a7I H ι := hF.sylow.le.trans hKI
  have hHS : H ≤ normalizer (pCoreOf 2 H : Set G) := hF.H_norm.ge
  have hYH : Y ≤ H := hYI.trans hIH
  have hSs : Group.IsSolvable (pCoreOf 2 H) := by
    have := hF.sylow.isPGroup.isNilpotent
    infer_instance
  have hYsolv : Y ≤ a7K H → Group.IsSolvable Y := fun h =>
    have := a7s_isSolvable_K hF
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
  have hsolv_map : Group.IsSolvable Y → Group.IsSolvable ((Y.subgroupOf H).map ι) := fun h => by
    have : Group.IsSolvable (Y.subgroupOf H) := Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hYH).toMonoidHom) (MulEquiv.injective _)
    exact Group.isSolvable_of_surjective (ι.subgroupMap_surjective (Y.subgroupOf H))
  have hqs : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 Y) := by
    rcases hYx.1.2.2.2.1 with h | h
    · exact h
    · exfalso
      have hY3 : Group.IsSolvable Y := by
        have : Group.IsSolvable (CFSG.pCore 2 Y) := by
          have := (CFSG.pCore_isPGroup (p := 2) (G := Y)).isNilpotent
          infer_instance
        have : Group.IsSolvable (↥Y ⧸ CFSG.pCore 2 Y) := by
          have : Fact (Nat.Prime (Nat.card (↥Y ⧸ CFSG.pCore 2 Y))) := ⟨h ▸ Nat.prime_three⟩
          have := isCyclic_of_prime_card (α := ↥Y ⧸ CFSG.pCore 2 Y) rfl
          infer_instance
        exact Group.isSolvable_of_subgroup_quotient (CFSG.pCore 2 Y)
      rcases a7s_map_eq_bot_or_eq hF hYs with h0 | h1
      · have hdvd : 3 ∣ Nat.card (a7K H) := by
          refine dvd_trans ?_ (Subgroup.card_dvd_of_le (a7s_le_K_of_map_eq_bot hF hYH h0))
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 Y), h]
          exact dvd_mul_right 3 _
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hF.K_coprime hdvd
      · have := hsolv_map hY3
        rw [h1] at this
        exact a7s_not_isSolvable_a7Five this
  have hιY : (Y.subgroupOf H).map ι = a7Five := by
    rcases a7s_map_eq_bot_or_eq hF hYs with h0 | h1
    · exfalso
      have := hYsolv (a7s_le_K_of_map_eq_bot hF hYH h0)
      have : Nontrivial (↥Y ⧸ CFSG.pCore 2 Y) := CFSG.LocalCores.isQuasisimple_nontrivial hqs
      have : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 Y) := hqs.1
      exact Group.IsPerfect.not_isSolvable (↥Y ⧸ CFSG.pCore 2 Y) inferInstance
    · exact h1
  have hcomm : ∀ y ∈ Y, ∀ k ∈ a7K H, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
    a7s_commutator_mem hYI hKI (hIH.trans hHS) (hIH.trans (a7s_le_normalizer_K H))
      (a7s_isSubnormal_subgroupOf hYs) (a7s_isSolvable_K hF) (a7s_pCore_eq hF hYI hYs) hqs
  have hIN : a7I H ι ≤ normalizer ((Y ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    refine (a7s_le_sup_K hF hιY).trans (sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_)
    intro k hk
    apply a7s_mem_normalizer_of_map_le
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hky : (MulAut.conj k).toMonoidHom y = (y * k * y⁻¹ * k⁻¹)⁻¹ * y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hky]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ (hcomm y hy k hk)))
        (Subgroup.mem_sup_left hy)
    · rintro _ ⟨s, hs, rfl⟩
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (hHS (hIH (hKI hk))) s).mp hs)
  have hNI : Y ⊔ pCoreOf 2 H ≤ a7I H ι := sup_le hYI hSI
  have hpc : CFSG.Quasithin.perfectCore Y = CFSG.Quasithin.perfectCore (Y ⊔ pCoreOf 2 H) :=
    a7s_perfectCore_eq_of_isSubnormal
      (CFSG.Quasithin.A3.subnormal_of_le_of_le hYs le_sup_left hNI) le_rfl le_rfl
      (hNI.trans (hIH.trans hHS)) hSs
  set Y₁ := CFSG.Quasithin.perfectCore Y with hY₁
  have hY₁Y : Y₁ ≤ Y := CFSG.Quasithin.perfectCore_le Y
  have hY₁I : Y₁ ≤ a7I H ι := hY₁Y.trans hYI
  have hIY₁ : a7I H ι ≤ normalizer (Y₁ : Set G) := by
    rw [hpc]
    exact hIN.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)
  have hιY₁ : (Y₁.subgroupOf H).map ι = a7Five := by
    have h1 : Y₁.subgroupOf H = CFSG.Quasithin.perfectCore (Y.subgroupOf H) := by
      have := CFSG.Quasithin.map_perfectCore H.subtype (Y.subgroupOf H)
      rw [Subgroup.map_subgroupOf_eq_of_le hYH] at this
      rw [hY₁, ← this, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [h1, CFSG.Quasithin.map_perfectCore, hιY,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect Subgroup.commutator_eq_self]
  refine ⟨Y₁, hY₁Y, hIY₁, Subgroup.isPerfect_iff.mpr (CFSG.Quasithin.perfectCore_perfect Y),
    hιY₁, fun y hy k hk => hcomm y (hY₁Y hy) k hk, ?_⟩
  have hMI : Y₁ ⊔ pCoreOf 2 H ≤ a7I H ι := sup_le hY₁I hSI
  have hIM : a7I H ι ≤ normalizer ((Y₁ ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    a7s_le_normalizer_sup hIY₁ (hIH.trans hHS)
  have hIMK : a7I H ι ≤ (Y₁ ⊔ pCoreOf 2 H) ⊔ a7K H :=
    (a7s_le_sup_K hF hιY₁).trans (sup_le_sup_right le_sup_left _)
  have hdvd := a7s_relIndex_dvd hMI hIM hIMK hKI le_sup_right
  have hodd : ¬ 2 ∣ (Y₁ ⊔ pCoreOf 2 H).relIndex (a7I H ι) := fun h =>
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hF.sylow).2.2 (h.trans hdvd)
  exact a7s_le_of_isPGroup hMI hIM hodd (a7s_V_le_I hF) hF.V_two

end CFSG.LocalAnalysis.RankThreeTheoremC
