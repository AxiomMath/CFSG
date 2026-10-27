module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2
public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (map_gLAPPrimeCore)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Vc (p : ℕ) (K : Subgroup G) : Subgroup K := ⁅(⊤ : Subgroup K), GLAPPrimeCore p ↥K⁆

instance vc_normal (p : ℕ) (K : Subgroup G) : (Vc p K).Normal := by
  unfold Vc
  infer_instance

@[expose] def actW (W K : Subgroup G) (hWN : W ≤ Subgroup.normalizer (K : Set G)) :
    ↥W →* MulAut ↥K :=
  K.normalizerMonoidHom.comp (Subgroup.inclusion hWN)

theorem coe_actW (W K : Subgroup G) (hWN : W ≤ Subgroup.normalizer (K : Set G)) (w : W) (k : K) :
    ((actW W K hWN w k : K) : G) = (w : G) * k * (w : G)⁻¹ := rfl

theorem map_Vc (p : ℕ) (W K : Subgroup G) (hWN : W ≤ Subgroup.normalizer (K : Set G)) (w : W) :
    (Vc p K).map (actW W K hWN w).toMonoidHom = Vc p K := by
  unfold Vc
  have htop : (⊤ : Subgroup K).map (actW W K hWN w).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective (actW W K hWN w).toMonoidHom (actW W K hWN w).surjective
  rw [Subgroup.map_commutator, htop, map_gLAPPrimeCore p (actW W K hWN w)]

@[expose] noncomputable def actQ (p : ℕ) (W K : Subgroup G) (hWN : W ≤ Subgroup.normalizer (K : Set G)) :
    ↥W →* MulAut (↥K ⧸ Vc p K) :=
  quotAutHom (Vc p K) (actW W K hWN) (map_Vc p W K hWN)

theorem vc_le_core (p : ℕ) (K : Subgroup G) : Vc p K ≤ GLAPPrimeCore p ↥K :=
  Subgroup.commutator_le_right _ _

@[expose] def ktoBar (p : ℕ) (K : Subgroup G) : (↥K ⧸ Vc p K) →* (↥K ⧸ GLAPPrimeCore p ↥K) :=
  QuotientGroup.map (Vc p K) (GLAPPrimeCore p ↥K) (MonoidHom.id _) (vc_le_core p K)

theorem ktoBar_surjective (p : ℕ) (K : Subgroup G) : Function.Surjective (ktoBar p K) := by
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk k, rfl⟩

theorem ktoBar_ker_central (p : ℕ) (K : Subgroup G) :
    (ktoBar p K).ker ≤ Subgroup.center (↥K ⧸ Vc p K) := by
  intro z hz
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective z
  have hk₀ : k₀ ∈ GLAPPrimeCore p ↥K := by
    have : (QuotientGroup.mk k₀ : ↥K ⧸ GLAPPrimeCore p ↥K) = 1 := hz
    exact (QuotientGroup.eq_one_iff _).1 this
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have : (k * k₀)⁻¹ * (k₀ * k) = (⁅k⁻¹, k₀⁻¹⁆)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact (Vc p K).inv_mem
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) ((GLAPPrimeCore p ↥K).inv_mem hk₀))

section Marked

variable [Finite G]

theorem hasLabel_ktilde {p : ℕ} (hp : p.Prime) {W K : Subgroup G} (hK : GLAPComponent p W K)
    (hchev : IsChevSimple 2 (PSimple p K)) : HasLabel (↥K ⧸ Vc p K) (fun _ => True) := by
  have hperfK : Group.IsPerfect ↥K := by
    refine ⟨?_⟩
    have h1 : ⁅K, K⁆ = K := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hK
    apply Subgroup.map_injective K.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact h1
  haveI : Group.IsPerfect (↥K ⧸ Vc p K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Vc p K)) (QuotientGroup.mk'_surjective _)
  have hqs : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) :=
    isQuasisimple_pQuot_of_glaPComponent hp hK
  obtain ⟨e⟩ := quotEquiv_of_perfect_central (ktoBar p K) (ktoBar_surjective p K) inferInstance
    (ktoBar_ker_central p K)
  have hq : CFSG.Open.IsQuasisimple (↥K ⧸ Vc p K) :=
    ⟨Group.IsPerfect.commutator_eq_top, (MulEquiv.isSimpleGroup_congr e).2 hqs.2⟩
  exact CFSG.StandardType.ChevTwo.ys08_holds _ hq (isChevSimple_two_of_equiv e hchev)

theorem mem_normalizer_T {M K : Subgroup G} [Finite G] {g : G} (hgM : g ∈ M)
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((pCoreOf 2 M ⊓ K : Subgroup G) : Set G) := by
  have hP : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M hgM
  rw [Subgroup.mem_normalizer_iff] at hP hgK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hP h, hgK h]

@[expose] def Ttilde (p : ℕ) (M K : Subgroup G) : Subgroup (↥K ⧸ Vc p K) :=
  ((pCoreOf 2 M ⊓ K : Subgroup G).subgroupOf K).map (QuotientGroup.mk' (Vc p K))

theorem conj_mem_ttilde (p : ℕ) {M K : Subgroup G} [Finite G] (k : K)
    (hk : (k : G) ∈ Subgroup.normalizer ((pCoreOf 2 M ⊓ K : Subgroup G) : Set G))
    {y : ↥K ⧸ Vc p K} (hy : y ∈ Ttilde p M K) :
    (QuotientGroup.mk k : ↥K ⧸ Vc p K) * y * (QuotientGroup.mk k)⁻¹ ∈ Ttilde p M K := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
  have htT : (t : G) ∈ (pCoreOf 2 M ⊓ K : Subgroup G) := ht
  have h1 := (Subgroup.mem_normalizer_iff.1 hk (t : G)).1 htT
  refine ⟨k * t * k⁻¹, ?_, ?_⟩
  · show ((k * t * k⁻¹ : K) : G) ∈ (pCoreOf 2 M ⊓ K : Subgroup G)
    simpa using h1
  · simp [QuotientGroup.mk'_apply]

theorem i2315bAt_of_seitzGen (h : SeitzGen) : I2315bAt G := by
  intro p q hp hp2 hq hq2 hqp W K V M Fo hK hchev hWN hVq hVK hWV hVO hFoq hFoW hFomax hrk hFoM
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hKW : K ≤ W := hK.1
  have hlab := hasLabel_ktilde hp hK hchev
  have hVc : ¬ q ∣ Nat.card (Vc p K) := by
    have h1 : (Vc p K).map K.subtype ≤ V := by
      have : (Vc p K).map K.subtype = ⁅K, GLAPPrimeCoreOf p K⁆ := by
        unfold Vc
        rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
        rfl
      rw [this]; exact hVO
    have h2 : Nat.card (Vc p K) ∣ Nat.card V := by
      rw [← card_map_subtype (Vc p K)]
      exact Subgroup.card_dvd_of_le h1
    exact fun hd => ((Nat.Prime.coprime_iff_not_dvd hq).1 hVq) (hd.trans h2)
  obtain ⟨E₀, hE₀Fo, hE₀el, k, hk3, hE₀c⟩ := exists_elem_of_le_pRank hq.one_lt hrk
  have hdvd : q ^ 3 ∣ Nat.card E₀ := by rw [hE₀c]; exact pow_dvd_pow q hk3
  obtain ⟨E₁, hE₁⟩ := Sylow.exists_subgroup_card_pow_prime q hdvd
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = E₁.map E₀.subtype := ⟨_, rfl⟩
  have hEFo : E ≤ Fo := by rw [hEdef]; exact (map_subtype_le E₁).trans hE₀Fo
  have hEel : IsElemAbelian q E := by rw [hEdef]; exact isElemAbelian_mono hE₀el (map_subtype_le E₁)
  have hEc : Nat.card E = q ^ 3 := by rw [hEdef, card_map_subtype]; exact hE₁
  have hEW : E ≤ W := hEFo.trans hFoW
  have hEM : E ≤ M := by
    have h2 : 2 ≤ CFSG.Open.pRank q E :=
      (by norm_num : 2 ≤ 3).trans (le_pRank_of_elem hq.one_lt le_rfl hEel hEc)
    have hsub : E ≤ E ⊔ (Fo ⊓ Subgroup.centralizer (E : Set G)) := le_sup_left
    have h3 : 3 ≤ CFSG.Open.pRank q (E ⊔ (Fo ⊓ Subgroup.centralizer (E : Set G))) :=
      le_pRank_of_elem hq.one_lt hsub hEel hEc
    have := hFoM E hEFo h2 h3
    intro e he
    exact this ⟨Subgroup.le_normalizer he, hEW he⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2G : IsPGroup 2 ↥(pCoreOf 2 M ⊓ K : Subgroup G) :=
    IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) inf_le_left
  have hT2 : IsPGroup 2 ↥(Ttilde p M K) :=
    isPGroup_map_hom _ ((isPGroup_subgroupOf_iff inf_le_right).2 hT2G)
  have hE'el : IsElemAbelian q (E.subgroupOf W) := (isElemAbelian_subgroupOf_iff hEW).2 hEel
  have hTinv : ∀ e ∈ E.subgroupOf W, ∀ t ∈ Ttilde p M K, actQ p W K hWN e t ∈ Ttilde p M K := by
    intro e he t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.1 ht
    have heM : (e : G) ∈ M := hEM he
    have hnT := mem_normalizer_T (K := K) heM (hWN e.2)
    have htT : (t₀ : G) ∈ (pCoreOf 2 M ⊓ K : Subgroup G) := ht₀
    have h1 := (Subgroup.mem_normalizer_iff.1 hnT (t₀ : G)).1 htT
    refine ⟨actW W K hWN e t₀, ?_, ?_⟩
    · show ((actW W K hWN e t₀ : K) : G) ∈ (pCoreOf 2 M ⊓ K : Subgroup G)
      rw [coe_actW]; exact h1
    · exact (quotAutHom_mk (Vc p K) (actW W K hWN) (map_Vc p W K hWN) e t₀).symm
  have hnorm : ∀ F : Subgroup ↥W, F ≤ E.subgroupOf W → F.relIndex (E.subgroupOf W) ≤ q →
      centFixAct (actQ p W K hWN) F ≤ Subgroup.normalizer (Ttilde p M K : Set (↥K ⧸ Vc p K)) := by
    intro F hFE hFi x hx
    set FG : Subgroup G := F.map W.subtype with hFG
    have hFGE : FG ≤ E := by
      have h1 : F.map W.subtype ≤ (E.subgroupOf W).map W.subtype := Subgroup.map_mono hFE
      rwa [subgroupOf_map_subtype_of_le hEW] at h1
    have hFGFo : FG ≤ Fo := hFGE.trans hEFo
    have hFGel : IsElemAbelian q FG := isElemAbelian_mono hEel hFGE
    have hFGi : FG.relIndex E ≤ q := by
      have h1 : FG.relIndex ((E.subgroupOf W).map W.subtype) = F.relIndex (E.subgroupOf W) :=
        Subgroup.relIndex_map_map_of_injective F (E.subgroupOf W) W.subtype_injective
      rw [subgroupOf_map_subtype_of_le hEW] at h1
      rw [h1]; exact hFi
    obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian hq hFGel
    have hj2 : 2 ≤ j := by
      have hmul := card_mul_relIndex hFGE
      rw [hEc, hj] at hmul
      by_contra hlt
      have hj1 : j ≤ 1 := by omega
      have h5 : q ^ j * FG.relIndex E ≤ q ^ 1 * q :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hq.pos hj1) hFGi
      have h6 : q ^ 1 * q < q ^ 3 := by
        rw [← pow_succ]
        exact Nat.pow_lt_pow_right hq.one_lt (by omega)
      omega
    have h2 : 2 ≤ CFSG.Open.pRank q FG := hj2.trans (le_pRank_of_elem hq.one_lt le_rfl hFGel hj)
    have hsub : E ≤ FG ⊔ (Fo ⊓ Subgroup.centralizer (FG : Set G)) := by
      refine le_trans ?_ le_sup_right
      intro e he
      refine ⟨hEFo he, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro g hg
      exact isElemAbelian_commute hEel (hFGE hg) he
    have h3 : 3 ≤ CFSG.Open.pRank q (FG ⊔ (Fo ⊓ Subgroup.centralizer (FG : Set G))) :=
      le_pRank_of_elem hq.one_lt hsub hEel hEc
    have hFGM := hFoM FG hFGFo h2 h3
    have hFp : IsPGroup q ↥F := isPGroup_of_isElemAbelian (isElemAbelian_mono hE'el hFE)
    obtain ⟨k₁, hk₁x, hk₁fix⟩ := exists_fixed_lift (Vc p K) (actW W K hWN) (map_Vc p W K hWN) hFp hVc x
      (fun f hf => mem_centFixAct.1 hx f hf)
    have hk₁M : (k₁ : G) ∈ M := by
      apply hFGM
      refine ⟨?_, hKW k₁.2⟩
      have hc : (k₁ : G) ∈ Subgroup.centralizer (FG : Set G) := by
        refine Subgroup.mem_centralizer_iff.2 ?_
        rintro _ ⟨f, hf, rfl⟩
        have h1 := congrArg Subtype.val (hk₁fix f hf)
        rw [coe_actW] at h1
        show (f : G) * (k₁ : G) = (k₁ : G) * (f : G)
        calc (f : G) * (k₁ : G) = (f : G) * k₁ * (f : G)⁻¹ * (f : G) := by group
          _ = (k₁ : G) * (f : G) := by rw [h1]
      exact Subgroup.centralizer_le_normalizer _ hc
    have hnT := mem_normalizer_T (K := K) hk₁M (Subgroup.le_normalizer k₁.2)
    rw [← hk₁x, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact conj_mem_ttilde p k₁ hnT hy
    · intro hy
      have hinvT : ((k₁⁻¹ : K) : G) ∈ Subgroup.normalizer ((pCoreOf 2 M ⊓ K : Subgroup G) : Set G) := by
        simpa using Subgroup.inv_mem _ hnT
      have := conj_mem_ttilde p (k₁⁻¹) hinvT hy
      simpa [QuotientGroup.mk_inv, mul_assoc] using this
  have hcardW : Nat.card (E.subgroupOf W) ≤ q ^ 3 := (card_subgroupOf hEW).le.trans hEc.le
  have hcardE : Nat.card ((E.subgroupOf W).map (actQ p W K hWN)) ≤ q ^ 3 :=
    (card_map_le_of_finite (actQ p W K hWN) (E.subgroupOf W)).trans hcardW
  have hcent := seitz_core h hlab hq hq2 (actQ p W K hWN) hE'el hcardE hT2 hTinv hnorm
  intro t ht
  have htK : t ∈ K := ht.2
  have h1 : (QuotientGroup.mk (⟨t, htK⟩ : K) : ↥K ⧸ Vc p K) ∈ Subgroup.center (↥K ⧸ Vc p K) :=
    hcent ⟨⟨t, htK⟩, ht, rfl⟩
  have h2 : (QuotientGroup.mk (⟨t, htK⟩ : K) : ↥K ⧸ GLAPPrimeCore p ↥K) ∈
      Subgroup.center (↥K ⧸ GLAPPrimeCore p ↥K) :=
    Subgroup.map_center_le_center (ktoBar_surjective p K) ⟨_, h1, rfl⟩
  have hbot : GLAPPrimeCore p (↥K ⧸ GLAPPrimeCore p ↥K) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) p
  obtain ⟨n, hn⟩ := hT2G ⟨t, ht⟩
  have ht2 : t ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hz1 : (QuotientGroup.mk (⟨t, htK⟩ : K) : ↥K ⧸ GLAPPrimeCore p ↥K) = 1 := by
    refine eq_one_of_central_two_power hp hp2 hbot h2 (n := n) ?_
    rw [← QuotientGroup.mk_pow]
    have : (⟨t, htK⟩ : K) ^ (2 ^ n) = 1 := Subtype.ext (by simpa using ht2)
    rw [this]; rfl
  have ht0 : (⟨t, htK⟩ : K) ∈ GLAPPrimeCore p ↥K := (QuotientGroup.eq_one_iff _).1 hz1
  exact ⟨⟨t, htK⟩, ht0, rfl⟩
end Marked

end CFSG.LocalAnalysis.GLTheoremA.Y10F
