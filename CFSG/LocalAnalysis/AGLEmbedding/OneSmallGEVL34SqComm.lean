module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUOdd
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

omit [Finite G] in
theorem L34Squeeze.eq_one_of_two_three {X : Type*} [Group X] {y : X} {a b : ℕ}
    (h2 : y ^ 2 ^ a = 1) (h3 : y ^ 3 ^ b = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h2
  have h1' : orderOf y ∣ 3 ^ b := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow a b (by norm_num)
  have : orderOf y ∣ 1 := by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd h1 h1'
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem D1OneSmallData.map_twoCore_inf_inf_eq_one (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    {y : H ⧸ primeComplementCore (G := H) p}
    (hyU : y ∈ ((pCoreOf 2 (H ⊓ M)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (hyK : y ∈ K) : y = 1 := by
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set U := pCoreOf 2 (H ⊓ M) with hU
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE (Or.inl ⟨rfl, hL⟩)
  have hD := KFactProofs.UPrimeExcL34.localData_of_isLinThreeFour hL T₁
  have hΓ := KFactProofs.UPrimeExcL34.glbCore_eq_normalizer hD
  have hUp : IsPGroup 2 ((U.subgroupOf H).map π) :=
    ((RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)).comap_subtype).map π
  have hUHM : U ≤ H ⊓ M := RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)
  have hHMU : H ⊓ M ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
  set k : K := ⟨y, hyK⟩ with hk
  have hyX : y ∈ d1X0 3 M H := by
    obtain ⟨u, hu, rfl⟩ := hyU
    exact ⟨u, Subgroup.mem_subgroupOf.mpr (hUHM (Subgroup.mem_subgroupOf.mp hu)), rfl⟩
  have hkN : k ∈ Subgroup.normalizer ((T₁ : Subgroup K) : Set K) := by
    rw [← hΓ, ← hY]
    exact Subgroup.mem_subgroupOf.mpr hyX
  have hRb := hd.cfg.toU.rbar
  have hRN : ∀ r ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      ∀ v ∈ (U.subgroupOf H).map π, r * v * r⁻¹ ∈ (U.subgroupOf H).map π := by
    intro r hr v hv
    rw [hRb] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    obtain ⟨v', hv', rfl⟩ := hv
    have hr'N : (r' : G) ∈ Subgroup.normalizer (U : Set G) :=
      hHMU ⟨r'.2, hd.cfg.ext.le_M (Subgroup.mem_subgroupOf.mp hr')⟩
    refine ⟨r' * v' * r'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp hr'N v').mp (Subgroup.mem_subgroupOf.mp hv')
    simpa using this
  have hcomm : ∀ t ∈ (T₁ : Subgroup K), k * t = t * k := by
    intro t ht
    have hc1 : k * t * k⁻¹ * t⁻¹ ∈ (T₁ : Subgroup K) := by
      have := (Subgroup.mem_normalizer_iff.mp hkN t).mp ht
      exact (T₁ : Subgroup K).mul_mem this ((T₁ : Subgroup K).inv_mem ht)
    have htR : (t : H ⧸ primeComplementCore (G := H) 3) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
      have : (t : H ⧸ primeComplementCore (G := H) 3) ∈ (T₁ : Subgroup K).map K.subtype :=
        ⟨t, ht, rfl⟩
      rw [hT₁] at this
      exact this.1
    have hc2 : ((k * t * k⁻¹ * t⁻¹ : K) : H ⧸ primeComplementCore (G := H) 3) ∈
        (U.subgroupOf H).map π := by
      have h1 := hRN _ htR _ (Subgroup.inv_mem _ hyU)
      have h2 := Subgroup.mul_mem _ hyU h1
      simpa [hk, mul_assoc] using h2
    obtain ⟨a, ha⟩ := hUp ⟨_, hc2⟩
    obtain ⟨b, hb⟩ := (T₁.isPGroup') ⟨_, hc1⟩
    have ha' : (k * t * k⁻¹ * t⁻¹) ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      exact Subtype.ext (by simpa using this)
    have hb' : (k * t * k⁻¹ * t⁻¹) ^ 3 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have h1 := L34Squeeze.eq_one_of_two_three ha' hb'
    calc k * t = k * t * k⁻¹ * t⁻¹ * t * k := by group
      _ = t * k := by rw [h1, one_mul]
  obtain ⟨t₀, ht₀, ht₀1⟩ : ∃ t ∈ (T₁ : Subgroup K), t ≠ 1 := by
    by_contra hcon
    have hbot : (T₁ : Subgroup K) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun t ht => by
      by_contra h1
      exact hcon ⟨t, ht, h1⟩
    have := hD.card_eq
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hkT : k ∈ (T₁ : Subgroup K) := hD.centralizer_le t₀ ht₀ ht₀1 k (hcomm t₀ ht₀)
  obtain ⟨b, hb⟩ := (T₁.isPGroup') ⟨k, hkT⟩
  obtain ⟨a, ha⟩ := hUp ⟨y, hyU⟩
  have hb' : y ^ 3 ^ b = 1 := by
    have := congrArg (fun x : ↥(T₁ : Subgroup K) => ((x : K) : H ⧸ primeComplementCore (G := H) 3))
      hb
    simpa [hk] using this
  have ha' : y ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  exact L34Squeeze.eq_one_of_two_three ha' hb'

theorem D1OneSmallData.commutator_mem_twoCore_of_d1LiftX (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    {u t : G} (hu : u ∈ pCoreOf 2 (H ⊓ M)) (ht : t ∈ d1LiftX p H R K) :
    u * t * u⁻¹ * t⁻¹ ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := pCoreOf 2 (H ⊓ M) with hUdef
  set W := GLBPrimeCore p H with hWdef
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hUHM : U ≤ H ⊓ M := RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)
  have hHMU : H ⊓ M ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
  have huH : u ∈ H := (hUHM hu).1
  have htH : t ∈ H := d1LiftX_le_H p H R K ht
  have htR : t ∈ R := d1LiftX_le p H R K ht
  have htHM : t ∈ H ⊓ M := ⟨htH, hd.cfg.ext.le_M htR⟩
  have hcU : u * t * u⁻¹ * t⁻¹ ∈ U := by
    have h1 : t * u⁻¹ * t⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hHMU htHM) u⁻¹).mp (U.inv_mem hu)
    have := U.mul_mem hu h1
    simpa [mul_assoc] using this
  have htK : π ⟨t, htH⟩ ∈ K := by
    obtain ⟨x, ⟨-, hxK⟩, hxt⟩ := ht
    have hx : x = ⟨t, htH⟩ := Subtype.ext hxt
    rw [← hx]
    exact hxK
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  set c : H := ⟨u, huH⟩ * ⟨t, htH⟩ * ⟨u, huH⟩⁻¹ * ⟨t, htH⟩⁻¹ with hc
  have hcK : π c ∈ K := by
    have h1 : π ⟨u, huH⟩ * π ⟨t, htH⟩ * (π ⟨u, huH⟩)⁻¹ ∈ K := hKn.conj_mem _ htK _
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact K.mul_mem h1 (K.inv_mem htK)
  have hcUb : π c ∈ (U.subgroupOf H).map π :=
    ⟨c, Subgroup.mem_subgroupOf.mpr (by simpa [hc] using hcU), rfl⟩
  have hc1 := hd.map_twoCore_inf_inf_eq_one hUE hp3 hL hcUb hcK
  have hcW : (c : G) ∈ W := (mk'_primeComplementCore_eq_one_iff p c).mp hc1
  have hcW' : u * t * u⁻¹ * t⁻¹ ∈ W := by simpa [hc] using hcW
  have hWHM : W ≤ H ⊓ M := _root_.le_inf (glbPrimeCore_le p H) hd.cfg.ext.primeCore_le
  have hD : W ⊓ U ≤ pCoreOf 2 W := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)).to_le inf_le_right)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxU := Subgroup.mem_normalizer_iff.mp (hHMU (hWHM hx)) y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨W.mul_mem (W.mul_mem hx hy1) (W.inv_mem hx), hxU.mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, hxU.mpr hy2⟩
      have := W.mul_mem (W.mul_mem (W.inv_mem hx) hy1) hx
      simpa [mul_assoc] using this
  have hWH : pCoreOf 2 W ≤ pCoreOf 2 H := by
    refine pCoreOf_le_of_normal_subgroupOf 2 W H (glbPrimeCore_le p H) ?_
    rw [glbPrimeCore_subgroupOf_eq]
    infer_instance
  exact hWH (hD ⟨hcW', hcU⟩)

theorem D1OneSmallData.not_le_of_normal_of_d1LiftX_le (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hp3 : p = 3) (hL : IsLinThreeFour K)
    {X : Subgroup G} (hXn : H ≤ Subgroup.normalizer (X : Set G))
    (hTX : d1LiftX p H R K ≤ X) : ¬ X ≤ M := by
  intro hXM
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  obtain ⟨T₁, hT₁, hY, -⟩ := hd.inf_eq_glbCore_of_exc hUE (Or.inl ⟨hp3, hL⟩)
  obtain ⟨T, hT, hsimple, -, -, -, hΓT, -⟩ := hd.exists_sylow
  obtain rfl : T₁ = T :=
    Sylow.ext (Subgroup.map_injective K.subtype_injective (hT₁.trans hT.symm))
  have hXn' : (X.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hgN := hXn g.2
    have := (Subgroup.mem_normalizer_iff.mp hgN x).mp (Subgroup.mem_subgroupOf.mp hx)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  set Xb := (X.subgroupOf H).map π with hXb
  have hXbn : Xb.Normal := Subgroup.Normal.map hXn' π (QuotientGroup.mk'_surjective _)
  have hXbX : Xb ≤ d1X0 p M H := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨x.2, hXM (Subgroup.mem_subgroupOf.mp hx)⟩
  have hTXb : ∀ k : K, k ∈ (T₁ : Subgroup K) → (k : H ⧸ primeComplementCore (G := H) p) ∈ Xb := by
    intro k hk
    have h1 : (k : H ⧸ primeComplementCore (G := H) p) ∈ (T₁ : Subgroup K).map K.subtype :=
      ⟨k, hk, rfl⟩
    rw [hT₁, ← hd.cfg.toU.map_d1LiftX_eq_inf] at h1
    obtain ⟨y, hy, hyk⟩ := h1
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (hTX (Subgroup.mem_subgroupOf.mp hy)), hyk⟩
  have hNK : (Xb.subgroupOf K).Normal := hXbn.subgroupOf K
  have hne : Xb.subgroupOf K ≠ ⊥ := by
    intro hbot
    have hT1 : (T₁ : Subgroup K) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun k hk => by
      have : k ∈ Xb.subgroupOf K := Subgroup.mem_subgroupOf.mpr (hTXb k hk)
      rw [hbot] at this
      exact (Subgroup.mem_bot).mp this
    exact hd.noncyclic (by
      rw [← hT₁, hT1, Subgroup.map_bot]
      exact isCyclic_of_subsingleton)
  have : IsSimpleGroup K := hsimple
  have htop : Xb.subgroupOf K = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Xb.subgroupOf K)).resolve_left hne
  apply hΓT
  rw [← hY, eq_top_iff]
  intro k _
  have : k ∈ Xb.subgroupOf K := htop ▸ Subgroup.mem_top k
  exact Subgroup.mem_subgroupOf.mpr (hXbX (Subgroup.mem_subgroupOf.mp this))

end CFSG.AGLEmbedding
