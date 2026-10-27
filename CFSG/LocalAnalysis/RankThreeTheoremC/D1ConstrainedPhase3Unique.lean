module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Conj
public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal D1Escape D1PhaseThree glbPrimeCore_le glbPrimeCore_normal
  glbPrimeCore_coprime le_normalizer_glbPrimeCore glbIsMaxTwoLocal_map_mulAut
  le_normalizer_of_forall_map_conj_le le_of_map_conj_le
  exists_mem_inv_mul_mem_normalizer_of_not_dvd_index)

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt {p : ℕ} [Fact p.Prime] {A T : Subgroup G}
    (hT : IsPGroup p T) (hAT : A < T) :
    ∃ x ∈ T, x ∈ Subgroup.normalizer (A : Set G) ∧ x ∉ A := by
  have hne : A.subgroupOf T ≠ ⊤ := fun htop =>
    absurd (fun x hxT => (Subgroup.mem_subgroupOf.mp (htop ▸ trivial : (⟨x, hxT⟩ : T) ∈
      A.subgroupOf T))) (not_le_of_gt hAT)
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent (G := T)
  have hlt : A.subgroupOf T < Subgroup.normalizer ((A.subgroupOf T : Subgroup T) : Set T) :=
    hnc _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, ?_, fun hxA => hxnot (Subgroup.mem_subgroupOf.mpr hxA)⟩
  have hxsub : x ∈ (Subgroup.normalizer (A : Set G)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hAT.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem _root_.CFSG.AGLEmbedding.D1Extremal.of_maxTwoLocal_ge {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1Extremal p P M H R) {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H')
    (hRH' : R ≤ H') (hH'M : ¬ H' ≤ M) : D1Extremal p P M H' R := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hR' : IsPGroup p (R.subgroupOf H') := h.toD1Escape.isPGroup.comap_subtype
  obtain ⟨T, hRT⟩ := hR'.exists_le_sylow
  have hRT' : R ≤ (T : Subgroup H').map H'.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRH']
    exact Subgroup.map_mono hRT
  have hTR : (T : Subgroup H').map H'.subtype = R := by
    by_contra hne
    have hlt : R < (T : Subgroup H').map H'.subtype := lt_of_le_of_ne hRT' (Ne.symm hne)
    obtain ⟨x, hxT, hxN, hxR⟩ :=
      exists_mem_normalizer_not_mem_of_lt (T.isPGroup'.map H'.subtype) hlt
    have hXT : R ⊔ Subgroup.zpowers x ≤ (T : Subgroup H').map H'.subtype :=
      sup_le hRT' (Subgroup.zpowers_le.mpr hxT)
    have hXM : R ⊔ Subgroup.zpowers x ≤ M :=
      sup_le h.le_M (Subgroup.zpowers_le.mpr (h.toD1Escape.normalizer_le hxN))
    have hXH : R ⊔ Subgroup.zpowers x ≤ H' ⊓ M :=
      le_inf (hXT.trans (Subgroup.map_subtype_le _)) hXM
    have hcard := h.extremal H' hH'.1 hH'M (h.three_le_pRank.trans
      (pRank_mono p hp (le_inf hRH' h.le_M))) _ hXH ((T.isPGroup'.map H'.subtype).to_le hXT)
    have hRX : R < R ⊔ Subgroup.zpowers x :=
      lt_of_le_of_ne le_sup_left fun heq => hxR (heq ▸ Subgroup.mem_sup_right
        (Subgroup.mem_zpowers x))
    exact (Subgroup.card_lt_of_lt hRX).not_ge hcard
  exact
    { prime := h.prime
      ne_two := h.ne_two
      sylow_le := h.sylow_le
      weakCore_le := h.weakCore_le
      maxTwoLocal_M := h.maxTwoLocal_M
      maxTwoLocal_H := hH'
      le_H := hRH'
      le_P := h.le_P
      isSylow := ⟨T, hTR⟩
      three_le_pRank := h.three_le_pRank
      not_le := hH'M
      extremal := h.extremal
      extremal3 := h.extremal3 }

theorem exists_mul_normalizer_of_sylow {p : ℕ} [Fact p.Prime] {X L R : Subgroup G}
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hLX : L ≤ X) (hRL : R ≤ L)
    (hR : IsPGroup p R) (hidx : ¬ p ∣ (R.subgroupOf L).index) :
    ∀ x ∈ X, ∃ l ∈ L, ∃ m ∈ X, m ∈ Subgroup.normalizer (R : Set G) ∧ x = l * m := by
  intro x hx
  obtain ⟨l, hl, hlx⟩ := exists_mem_inv_mul_mem_normalizer_of_not_dvd_index hRL hR hidx (hXL hx)
  exact ⟨l, hl, l⁻¹ * x, X.mul_mem (X.inv_mem (hLX hl)) hx, hlx, by group⟩

omit [Finite G] in
theorem not_dvd_index_subgroupOf_of_le {p : ℕ} {R L H : Subgroup G} (hRL : R ≤ L) (hLH : L ≤ H)
    (h : ¬ p ∣ (R.subgroupOf H).index) : ¬ p ∣ (R.subgroupOf L).index := fun hd =>
  h (hd.trans (Dvd.intro (L.relIndex H) (Subgroup.relIndex_mul_relIndex R L H hRL hLH)))

omit [Finite G] in
theorem conj_eq_of_mem_centralizer_of_mem_zpowers {z c h : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hh : h ∈ Subgroup.zpowers z) :
    c * h * c⁻¹ = h := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hz : c * z * c⁻¹ = z := by rw [hc]; group
  simp only [← conj_zpow, hz]

omit [Finite G] in
theorem mem_normalizer_zpowers_of_mem_centralizer {z c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    c ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · rwa [conj_eq_of_mem_centralizer_of_mem_zpowers hc hh]
  · have h1 := conj_eq_of_mem_centralizer_of_mem_zpowers (Subgroup.inv_mem _ hc) hh
    have h2 : h = c * h * c⁻¹ := by
      calc h = c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ := by group
        _ = c * h * c⁻¹ := h1
    rwa [← h2] at hh

theorem exists_decomposition_primeCore {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) {z : G} (hzR : z ∈ R)
    (hzc : z ∈ Subgroup.centralizer (R : Set G)) (hzp : orderOf z = p) :
    ∀ g ∈ H, ∃ n ∈ GLBPrimeCore p H,
      ∃ w ∈ Subgroup.closure {x : G | ∃ c ∈ H ⊓ Subgroup.centralizer ({z} : Set G), ∃ r ∈ R,
        x = c⁻¹ * r * c}, ∃ m ∈ H, m ∈ Subgroup.normalizer (R : Set G) ∧ g = n * w * m := by
  have : Fact p.Prime := ⟨h.prime⟩
  set C₁ : Subgroup G := H ⊓ Subgroup.centralizer ({z} : Set G) with hC₁
  set W : Subgroup G := Subgroup.closure {x : G | ∃ c ∈ C₁, ∃ r ∈ R, x = c⁻¹ * r * c} with hW
  have hRC₁ : R ≤ C₁ := fun r hr => ⟨h.le_H hr, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hzc r hr)⟩
  have hWC₁ : W ≤ C₁ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨c, hc, r, hr, rfl⟩
    exact C₁.mul_mem (C₁.mul_mem (C₁.inv_mem hc) (hRC₁ hr)) hc
  have hRW : R ≤ W := fun r hr => Subgroup.subset_closure ⟨1, C₁.one_mem, r, hr, by simp⟩
  have hCW : C₁ ≤ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_forall_map_conj_le fun c₀ hc₀ => ?_
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨c, hc, r, hr, rfl⟩
    refine Subgroup.subset_closure ⟨c * c₀⁻¹, C₁.mul_mem hc (C₁.inv_mem hc₀), r, hr, ?_⟩
    simp [MulAut.conj_apply]
    group
  have hidxH := h.toD1Escape.not_dvd_index_R
  have hidxC₁ := not_dvd_index_subgroupOf_of_le hRC₁ (inf_le_left : C₁ ≤ H) hidxH
  have hidxW := not_dvd_index_subgroupOf_of_le hRW (hWC₁.trans (inf_le_left : C₁ ≤ H)) hidxH
  have hRp := h.toD1Escape.isPGroup
  have hV₁C : H ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤
      Subgroup.normalizer (C₁ : Set G) := fun v hv => by
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hv.1, ?_⟩
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · exact conj_mem_centralizer_of_mem_normalizer_zpowers hv.2 hy
    · have := conj_mem_centralizer_of_mem_normalizer_zpowers (Subgroup.inv_mem _ hv.2) hy
      simpa [mul_assoc] using this
  have hC₁V : C₁ ≤ H ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun c hc =>
    ⟨hc.1, mem_normalizer_zpowers_of_mem_centralizer hc.2⟩
  intro g hg
  obtain ⟨n, hn, v, hvH, hvN, rfl⟩ :=
    h.toD1Escape.exists_mul_normalizer_zpowers hcon hzR hzc hzp g hg
  obtain ⟨l, hl, m₁, hm₁, hm₁N, rfl⟩ := exists_mul_normalizer_of_sylow hV₁C hC₁V hRC₁ hRp hidxC₁
    v ⟨hvH, hvN⟩
  obtain ⟨w, hw, m₂, hm₂, hm₂N, rfl⟩ := exists_mul_normalizer_of_sylow hCW hWC₁ hRW hRp hidxW
    l hl
  refine ⟨n, hn, w, hw, m₂ * m₁, H.mul_mem hm₂.1 hm₁.1, ?_, by group⟩
  exact (Subgroup.normalizer (R : Set G)).mul_mem hm₂N hm₁N

omit [Finite G] in
theorem mem_normalizer_of_map_conj_le [Finite G] {U : Subgroup G} {g : G}
    (hg : U.map (MulAut.conj g).toMonoidHom ≤ U) : g ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge hg ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

@[expose] def twoLocalsOver (M R : Subgroup G) : Set (Subgroup G) :=
  {K | GLBIsMaxTwoLocal K ∧ R ≤ K ∧ ¬ K ≤ M}

@[expose] def primeCoreJoin (p : ℕ) (M R : Subgroup G) : Subgroup G :=
  sSup ((fun K => GLBPrimeCore p K) '' twoLocalsOver M R)

omit [Finite G] in
theorem primeCore_le_primeCoreJoin {p : ℕ} {M R K : Subgroup G} (hK : K ∈ twoLocalsOver M R) :
    GLBPrimeCore p K ≤ primeCoreJoin p M R :=
  le_sSup ⟨K, hK, rfl⟩

omit [Finite G] in
theorem map_conj_mem_twoLocalsOver {M R K : Subgroup G} (hK : K ∈ twoLocalsOver M R) {m : G}
    (hmM : m ∈ M) (hmR : m ∈ Subgroup.normalizer (R : Set G)) :
    K.map (MulAut.conj m).toMonoidHom ∈ twoLocalsOver M R := by
  refine ⟨glbIsMaxTwoLocal_map_mulAut hK.1 (MulAut.conj m), ?_, fun hle =>
    hK.2.2 (le_of_map_conj_le hmM hle)⟩
  have := Subgroup.mem_normalizer_iff_map_conj_eq.mp hmR
  exact this ▸ Subgroup.map_mono hK.2.1

theorem mem_normalizer_primeCoreJoin_of_mem_normalizer {p : ℕ} {M R : Subgroup G} {m : G}
    (hmM : m ∈ M) (hmR : m ∈ Subgroup.normalizer (R : Set G)) :
    m ∈ Subgroup.normalizer (primeCoreJoin p M R : Set G) := by
  refine mem_normalizer_of_map_conj_le (Subgroup.map_le_iff_le_comap.mpr (sSup_le ?_))
  rintro _ ⟨K, hK, rfl⟩
  have h1 := glbPrimeCore_map_automorphism p K (MulAut.conj m)
  have h2 := primeCore_le_primeCoreJoin (p := p) (map_conj_mem_twoLocalsOver hK hmM hmR)
  rw [← Subgroup.map_le_iff_le_comap, h1]
  exact h2

theorem mem_normalizer_primeCoreJoin_of_forall_mem {p : ℕ} {M R : Subgroup G} {w : G}
    (hw : ∀ K ∈ twoLocalsOver M R, w ∈ K) :
    w ∈ Subgroup.normalizer (primeCoreJoin p M R : Set G) := by
  refine mem_normalizer_of_map_conj_le (Subgroup.map_le_iff_le_comap.mpr (sSup_le ?_))
  rintro _ ⟨K, hK, rfl⟩ y hy
  have hyU : w * y * w⁻¹ ∈ GLBPrimeCore p K :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_glbPrimeCore p K (hw K hK)) y).mp hy
  exact primeCore_le_primeCoreJoin hK hyU

theorem D1CentralizerInput3.eq_of_maxTwoLocal_ge {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} (hS : Setting G) (hz : D1CentralizerInput3 p P M z)
    (hlayer : CFSG.layer (ReducedCentralizer p z) = ⊥) (hzR : z ∈ R) (h : D1Extremal p P M H R)
    (hall : ∀ K : Subgroup G, GLBIsMaxTwoLocal K → R ≤ K → ¬ K ≤ M →
      HasPrimeConstraint (G := K) p)
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hRH' : R ≤ H') (hH'M : ¬ H' ≤ M) :
    H' = H := by
  have hp : p.Prime := Fact.out
  have hzc : z ∈ Subgroup.centralizer (R : Set G) :=
    Subgroup.centralizer_le h.le_P hz.mem_centralizer
  have hmem : ∀ K ∈ twoLocalsOver M R,
      D1Extremal p P M K R ∧ HasPrimeConstraint (G := K) p := fun K hK =>
    ⟨h.of_maxTwoLocal_ge hK.1 hK.2.1 hK.2.2, hall K hK.1 hK.2.1 hK.2.2⟩
  have hHmem : H ∈ twoLocalsOver M R := ⟨h.maxTwoLocal_H, h.le_H, h.not_le⟩
  have hH'mem : H' ∈ twoLocalsOver M R := ⟨hH', hRH', hH'M⟩
  have hUM : primeCoreJoin p M R ≤ M := sSup_le (by
    rintro _ ⟨K, hK, rfl⟩
    exact (hmem K hK).1.primeCore_le)
  have hnorm : ∀ K ∈ twoLocalsOver M R, K ≤ Subgroup.normalizer (primeCoreJoin p M R : Set G) := by
    intro K hK g hg
    obtain ⟨n, hn, w, hw, m, hm, hmR, rfl⟩ := exists_decomposition_primeCore (hmem K hK).1
      (hmem K hK).2 hzR hzc hz.orderOf_eq g hg
    have hwall : ∀ K' ∈ twoLocalsOver M R, w ∈ K' := fun K' hK' =>
      (Subgroup.closure_le K').mpr (by
        rintro _ ⟨c, hc, r, hr, rfl⟩
        exact hz.conj_le_of_extremal hS hlayer (hmem K' hK').1 (hmem K' hK').2 hzR c hc.2 r hr) hw
    exact (Subgroup.normalizer (primeCoreJoin p M R : Set G)).mul_mem
      ((Subgroup.normalizer (primeCoreJoin p M R : Set G)).mul_mem
        (Subgroup.le_normalizer (primeCore_le_primeCoreJoin hK hn))
        (mem_normalizer_primeCoreJoin_of_forall_mem hwall))
      (mem_normalizer_primeCoreJoin_of_mem_normalizer ((hmem K hK).1.toD1Escape.normalizer_le hmR)
        hmR)
  have hp2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr h.ne_two
  have hQH : pCoreOf 2 M ≤ GLBPrimeCore p H := by
    have hph := (hmem H hHmem).1.toPhaseThree3 hS (hmem H hHmem).2
    exact (hph.twoCore_M_le hph.twoCore_inf).trans (CFSG.AGLEmbedding.pCoreOf_le_glbPrimeCore
      Nat.prime_two hp2 H)
  have hQU : pCoreOf 2 M ≤ primeCoreJoin p M R := hQH.trans (primeCore_le_primeCoreJoin hHmem)
  have hQcore : pCoreOf 2 M ≤ pCoreOf 2 (primeCoreJoin p M R) :=
    normal_pGroup_le_pCoreOf 2 _ _ hQU
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQU).mpr
        (hUM.trans (localGroup_le_normalizer_pCoreOf 2 M)))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  have hne : pCoreOf 2 (primeCoreJoin p M R) ≠ ⊥ := fun hbot =>
    twoLocal_pCoreOf_ne_bot M h.maxTwoLocal_M.1 (le_bot_iff.mp (hbot ▸ hQcore))
  have h2 : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (primeCoreJoin p M R) : Set G)) :=
    ⟨pCoreOf 2 (primeCoreJoin p M R), hne,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _, rfl⟩
  have hle : ∀ K ∈ twoLocalsOver M R,
      K ≤ Subgroup.normalizer (pCoreOf 2 (primeCoreJoin p M R) : Set G) := fun K hK =>
    (hnorm K hK).trans (normalizer_localGroup_le_normalizer_pCoreOf 2 _)
  exact (hH'.2 _ h2 (hle H' hH'mem)).symm.trans (h.maxTwoLocal_H.2 _ h2 (hle H hHmem))

end CFSG.LocalAnalysis.RankThreeTheoremC
