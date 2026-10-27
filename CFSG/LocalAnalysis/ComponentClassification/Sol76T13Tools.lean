module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma316

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem twoLayerIn_le_of_forall {H X : Subgroup G}
    (h : ∀ M : Subgroup G, IsTwoComponentIn M H → M ≤ X) : twoLayerIn H ≤ X := by
  rw [twoLayerIn, map_le_iff_le_comap]
  refine sSup_le fun P hP => ?_
  rw [← map_le_iff_le_comap]
  exact h _ ⟨map_subtype_le _, by
    rw [← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]; exact hP⟩

theorem exists_not_le_coreActionKernel_of_not_le_oddCoreIn {H J : Subgroup G}
    (hperf : ⁅J, J⁆ = J) (hJL : J ≤ twoLayerIn H) (hJO_input : ¬ J ≤ oddCoreIn H) :
    ∃ M : Subgroup G, IsTwoComponentIn M H ∧ ¬ J ≤ coreActionKernel M := by
  by_contra hcon
  push Not at hcon
  have hJN' : J ≤ H := hJL.trans (map_subtype_le _)
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  set Jbar := (J.subgroupOf H).map π with hJbar
  set Cen : Subgroup G := ((centralizer (Jbar : Set (↥H ⧸ pPrimeCore 2 ↥H))).comap π).map
    H.subtype with hCen
  have hMC : ∀ M : Subgroup G, IsTwoComponentIn M H → M ≤ Cen := by
    intro M hM m hm
    refine ⟨⟨m, hM.1 hm⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_iff]
    rintro _ ⟨⟨j, hjN⟩, hj, rfl⟩
    have h1 := (hcon M hM (mem_subgroupOf.mp hj)).2 m hm
    have h2 : m⁻¹ * j⁻¹ * m * j ∈ oddCoreIn H := oddCoreIn_le_of_isTwoComponentIn hM h1
    exact ((mk_mul_comm_iff (N := H) ⟨m, hM.1 hm⟩ ⟨j, hjN⟩).mpr h2).symm
  have hJC : J ≤ Cen := hJL.trans (twoLayerIn_le_of_forall hMC)
  have hJO : J ≤ oddCoreIn H := by
    rw [← hperf]
    refine commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨y, hy, hye⟩ := hJC (inv_mem hb)
    have hyb : y = ⟨b⁻¹, hJN' (inv_mem hb)⟩ := Subtype.ext hye
    rw [hyb, SetLike.mem_coe, mem_comap, mem_centralizer_iff] at hy
    have hab := hy (π ⟨a⁻¹, hJN' (inv_mem ha)⟩)
      ⟨⟨a⁻¹, hJN' (inv_mem ha)⟩, mem_subgroupOf.mpr (inv_mem ha), rfl⟩
    have h1 := (mk_mul_comm_iff (N := H) ⟨a⁻¹, hJN' (inv_mem ha)⟩
      ⟨b⁻¹, hJN' (inv_mem hb)⟩).mp hab
    simp only [inv_inv] at h1
    rw [commutatorElement_def]
    exact h1
  exact hJO_input hJO

theorem exists_not_le_coreActionKernel_of_le_twoLayerIn {H J : Subgroup G} (hperf : ⁅J, J⁆ = J)
    (hJL : J ≤ twoLayerIn H) (hJinv : ∃ b ∈ J, orderOf b = 2) :
    ∃ M : Subgroup G, IsTwoComponentIn M H ∧ ¬ J ≤ coreActionKernel M := by
  refine exists_not_le_coreActionKernel_of_not_le_oddCoreIn hperf hJL ?_
  intro hJO
  obtain ⟨b, hbJ, hb2⟩ := hJinv
  have h1 := orderOf_dvd_natCard (⟨b, hJO hbJ⟩ : oddCoreIn H)
  rw [Subgroup.orderOf_mk, hb2] at h1
  exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_oddCoreIn H) h1) (by norm_num)

theorem commutator_eq_bot_of_mem_kStarComponents_of_le {Y K K' : Subgroup G}
    (hO : oddCoreIn (solomonKStarOf Y) ≤ centralizer (solomonKStarOf Y : Set G))
    (hK : K ∈ kStarComponents Y) (hK' : K' ∈ kStarComponents Y) (hne : K ≠ K') :
    ⁅K, K'⁆ = ⊥ := by
  set D := solomonKStarOf Y with hD
  have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
  have hK'D : K' ≤ D := le_iSup₂_of_le K' hK' le_rfl
  have hDN : D ≤ Y := solomonKStarOf_le Y
  have h1 : ⁅K, K'⁆ ≤ oddCoreIn D := FooteLit.commutator_le_oddCoreIn_of_ne
    (isTwoComponentIn_of_le hK.1 hKD hDN) (isTwoComponentIn_of_le hK'.1 hK'D hDN) hne
  have h2 : ⁅K, K'⁆ ≤ centralizer (K : Set G) := (h1.trans hO).trans (centralizer_le hKD)
  have hperf : Group.IsPerfect ↥K :=
    Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2)
  exact LocalCores.perfect_double_commutator hperf (commutator_eq_bot_iff_le_centralizer.mpr h2)

theorem isQuasisimple_of_mem_kStarComponents_of_le {Y K : Subgroup G}
    (hO : oddCoreIn (solomonKStarOf Y) ≤ centralizer (solomonKStarOf Y : Set G))
    (hK : K ∈ kStarComponents Y) : IsQuasisimple ↥K := by
  have hKD : K ≤ solomonKStarOf Y := le_iSup₂_of_le K hK le_rfl
  have hKc := isTwoComponentIn_of_le hK.1 hKD (solomonKStarOf_le Y)
  exact isQuasisimple_of_oddCoreIn_le_centralizer hK.1
    (((oddCoreIn_le_of_isTwoComponentIn hKc).trans hO).trans (centralizer_le hKD))

theorem twoLayerIn_le_sup_centralizer {H K : Subgroup G} (hK : IsTwoComponentIn K H)
    (hOK : oddCoreIn K ≤ centralizer (K : Set G)) :
    twoLayerIn H ≤ K ⊔ centralizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥K :=
    Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hK.1 hK.2)
  refine twoLayerIn_le_of_forall fun M hM => ?_
  by_cases hMK : M = K
  · rw [hMK]
    exact le_sup_left
  refine le_trans ?_ le_sup_right
  have hMN : M ≤ normalizer (K : Set G) :=
    (le_twoLayerIn_of_isTwoComponentIn hM).trans (FooteLit.twoLayerIn_le_normalizer hK.1 hK.2)
  have h1 : ⁅K, M⁆ ≤ oddCoreIn H :=
    FooteLit.commutator_le_oddCoreIn_of_ne hK hM (Ne.symm hMK)
  have h2 : ⁅K, M⁆ ≤ K := commutator_le.mpr fun k hk m hm => by
    have hmk : m * k⁻¹ * m⁻¹ ∈ K := (mem_normalizer_iff.mp (hMN hm) _).mp (inv_mem hk)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact mul_mem hk (by simpa [mul_assoc] using hmk)
  have h3 : ⁅K, M⁆ ≤ oddCoreIn K := (le_inf h1 h2).trans (oddCoreIn_inf_le hK.1)
  have h4 : ⁅⁅K, M⁆, K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (h3.trans hOK)
  have h5 := LocalCores.perfect_double_commutator hperf h4
  rw [commutator_comm] at h5
  exact commutator_eq_bot_iff_le_centralizer.mp h5

omit [Finite G] in
theorem eq_of_le_normalizer_of_commutator_ne_bot {J K : Subgroup G} (hJq : IsQuasisimple ↥J)
    (hKq : IsQuasisimple ↥K) (hJK : J ≤ normalizer (K : Set G))
    (hKJ : K ≤ normalizer (J : Set G)) (hne : ⁅J, K⁆ ≠ ⊥) : J = K := by
  have key : ∀ {X Y : Subgroup G}, IsQuasisimple ↥Y → X ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (X : Set G) → ⁅X, Y⁆ ≠ ⊥ → Y ≤ X := by
    intro X Y hYq hXY hYX hXYne
    set I := X ⊓ Y with hI
    have hIn : (I.subgroupOf Y).Normal := ⟨fun i hi y => by
      rw [mem_subgroupOf] at hi ⊢
      obtain ⟨hiX, hiY⟩ := mem_inf.mp hi
      refine mem_inf.mpr ⟨?_, ?_⟩
      · simpa using (mem_normalizer_iff.mp (hYX y.2) i).mp hiX
      · exact mul_mem (mul_mem y.2 hiY) (inv_mem y.2)⟩
    have hcomm : ⁅X, Y⁆ ≤ I := by
      refine commutator_le.mpr fun x hx y hy => mem_inf.mpr ⟨?_, ?_⟩
      · have : y * x⁻¹ * y⁻¹ ∈ X := (mem_normalizer_iff.mp (hYX hy) _).mp (inv_mem hx)
        rw [commutatorElement_def, mul_assoc, mul_assoc]
        exact mul_mem hx (by simpa [mul_assoc] using this)
      · have : x * y * x⁻¹ ∈ Y := (mem_normalizer_iff.mp (hXY hx) _).mp hy
        rw [commutatorElement_def]
        exact mul_mem this (inv_mem hy)
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hYq
        hIn.isSubnormal with htop | hcen
    · intro y hy
      have : (⟨y, hy⟩ : ↥Y) ∈ I.subgroupOf Y := by rw [htop]; trivial
      exact (mem_inf.mp (mem_subgroupOf.mp this)).1
    · exfalso
      apply hXYne
      have hYperf : Group.IsPerfect ↥Y := hYq.1
      have h1 : ⁅⁅Y, X⁆, Y⁆ = ⊥ := by
        rw [commutator_comm Y X, commutator_eq_bot_iff_le_centralizer]
        intro c hc
        rw [mem_centralizer_iff]
        intro y hy
        have hcI : c ∈ I := hcomm hc
        have hcY : (⟨c, (mem_inf.mp hcI).2⟩ : ↥Y) ∈ center ↥Y := hcen (mem_subgroupOf.mpr hcI)
        exact (congrArg Subtype.val ((mem_center_iff.mp hcY) ⟨y, hy⟩))
      have h2 := LocalCores.perfect_double_commutator hYperf h1
      rwa [commutator_comm] at h2
  have hKJle : K ≤ J := key hKq hJK hKJ hne
  have hJKle : J ≤ K := key hJq hKJ hJK (by rwa [commutator_comm])
  exact le_antisymm hJKle hKJle

theorem le_centralizer_of_le_sup_centralizer {K J : Subgroup G} {b : G} (hKperf : ⁅K, K⁆ = K)
    (hbK : b ∈ K) (hJK : J ≤ K ⊔ centralizer (K : Set G))
    (hJb : J ≤ centralizer ({b} : Set G)) (hJperf : Group.IsPerfect ↥J)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) (hJm : ¬ J ≤ centralizer (K : Set G))
    (hcard : Nat.card (↥K ⧸ center ↥K) ≤ Nat.card (↥J ⧸ Open.fusionZStar ↥J)) :
    K ≤ centralizer ({b} : Set G) := by
  classical
  set C := centralizer (K : Set G) with hC
  have hKC : K ≤ normalizer (C : Set G) := le_normalizer_centralizer le_normalizer
  have hYN : K ⊔ C ≤ normalizer (K : Set G) := sup_le le_normalizer (centralizer_le_normalizer _)
  have hJN : J ≤ normalizer (K : Set G) := hJK.trans hYN
  set A := K ⊓ centralizer ({b} : Set G) with hA
  have hAN : A ≤ normalizer (K : Set G) := inf_le_left.trans le_normalizer
  set ρ := K.normalizerMonoidHom with hρ
  set φ : ↥J →* MulAut ↥K := ρ.comp (Subgroup.inclusion hJN) with hφ
  set ψ : ↥A →* MulAut ↥K := ρ.comp (Subgroup.inclusion hAN) with hψ
  set θ : ↥K →* MulAut ↥K := ρ.comp (Subgroup.inclusion le_normalizer) with hθ
  have hρapp : ∀ (x : ↥(normalizer (K : Set G))) (k : ↥K), ((ρ x) k : G) = x * k * x⁻¹ :=
    fun x k => Subgroup.normalizerMonoidHom_apply_apply_coe K x k
  have hφapp : ∀ (j : ↥J) (y : ↥K), ((φ j) y : G) = j * y * (j : G)⁻¹ := fun j y =>
    hρapp (Subgroup.inclusion hJN j) y
  have hψapp : ∀ (a : ↥A) (y : ↥K), ((ψ a) y : G) = a * y * (a : G)⁻¹ := fun a y =>
    hρapp (Subgroup.inclusion hAN a) y
  have hθapp : ∀ (k y : ↥K), ((θ k) y : G) = k * y * (k : G)⁻¹ := fun k y =>
    hρapp (Subgroup.inclusion le_normalizer k) y
  have hφψ : φ.range ≤ ψ.range := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨c, hc, k, hk, hjck⟩ :=
      exists_mul_of_mem_sup_normalizer hKC ((sup_comm K C) ▸ hJK j.2)
    have hcK : ∀ y ∈ K, y * c = c * y := fun y hy => (mem_centralizer_iff.mp hc) y hy
    have hjb : (j : G) * b = b * j := mem_centralizer_singleton_iff.mp (hJb j.2)
    have hcb : c⁻¹ * b = b * c⁻¹ := by
      have h1 := hcK b hbK
      calc c⁻¹ * b = c⁻¹ * (b * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * b) * c⁻¹ := by rw [h1]
        _ = b * c⁻¹ := by group
    have hkb : k ∈ centralizer ({b} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hk' : k = c⁻¹ * j := by rw [hjck]; group
      rw [hk', mul_assoc, hjb, ← mul_assoc, hcb, mul_assoc]
    refine ⟨⟨k, hk, hkb⟩, ?_⟩
    ext y
    rw [hψapp, hφapp]
    change k * (y : G) * k⁻¹ = j * y * (j : G)⁻¹
    rw [hjck]
    have hky : k * (y : G) * k⁻¹ ∈ K := mul_mem (mul_mem hk y.2) (inv_mem hk)
    have h1 := hcK _ hky
    calc k * (y : G) * k⁻¹ = (k * y * k⁻¹ * c) * c⁻¹ := by group
      _ = (c * (k * y * k⁻¹)) * c⁻¹ := by rw [h1]
      _ = c * k * y * (c * k)⁻¹ := by group
  have hψθ : ψ.range ≤ θ.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a, (mem_inf.mp a.2).1⟩, rfl⟩
  have hθker : θ.ker = center ↥K := by
    ext k
    rw [MonoidHom.mem_ker, mem_center_iff]
    constructor
    · intro hk y
      have h1 := congrArg (fun f : MulAut ↥K => ((f y : ↥K) : G)) hk
      simp only [MulAut.one_apply] at h1
      rw [hθapp] at h1
      apply Subtype.ext
      change (y : G) * k = k * y
      calc (y : G) * k = k * y * (k : G)⁻¹ * k := by rw [h1]
        _ = k * y := by group
    · intro hk
      ext y
      rw [hθapp]
      have h1 := congrArg Subtype.val (hk y)
      change (y : G) * k = k * y at h1
      change (k : G) * y * (k : G)⁻¹ = y
      rw [← h1]
      group
  have hφker : φ.ker = C.subgroupOf J := by
    ext j
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro hj y hy
      have h1 := congrArg (fun f : MulAut ↥K => ((f ⟨y, hy⟩ : ↥K) : G)) hj
      simp only [MulAut.one_apply] at h1
      rw [hφapp] at h1
      change (j : G) * y * (j : G)⁻¹ = y at h1
      calc y * (j : G) = j * y * (j : G)⁻¹ * j := by rw [h1]
        _ = j * y := by group
    · intro hj
      ext y
      rw [hφapp]
      change (j : G) * y * (j : G)⁻¹ = y
      rw [← hj y y.2]
      group
  have hθcard : Nat.card θ.range = Nat.card (↥K ⧸ center ↥K) := by
    rw [← Subgroup.index_ker, hθker]
    rfl
  have hφcard : Nat.card (↥J ⧸ Open.fusionZStar ↥J) ≤ Nat.card φ.range := by
    rw [← Subgroup.index_ker]
    have hne : φ.ker ≠ ⊤ := by
      intro htop
      apply hJm
      intro j hj
      have h1 : (⟨j, hj⟩ : ↥J) ∈ φ.ker := by rw [htop]; trivial
      rw [hφker, mem_subgroupOf] at h1
      exact h1
    have hle : φ.ker ≤ Open.fusionZStar ↥J := le_fusionZStar_of_normal hJperf hJq φ.normal_ker hne
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hle)
  have hcardψ : Nat.card θ.range ≤ Nat.card ψ.range :=
    calc Nat.card θ.range = Nat.card (↥K ⧸ center ↥K) := hθcard
      _ ≤ Nat.card (↥J ⧸ Open.fusionZStar ↥J) := hcard
      _ ≤ Nat.card φ.range := hφcard
      _ ≤ Nat.card ψ.range := Subgroup.card_le_of_le hφψ
  have heq : ψ.range = θ.range := Subgroup.eq_of_le_of_card_ge hψθ hcardψ
  have hsup : A.subgroupOf K ⊔ center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : θ k ∈ ψ.range := by rw [heq]; exact ⟨k, rfl⟩
    obtain ⟨a, ha⟩ := hk
    set a' : ↥K := ⟨a, (mem_inf.mp a.2).1⟩ with ha'
    have h1 : θ a' = θ k := ha
    have hz : a'⁻¹ * k ∈ center ↥K := by
      rw [← hθker, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have ha'A : a' ∈ A.subgroupOf K := by
      rw [mem_subgroupOf]
      exact a.2
    rw [show k = a' * (a'⁻¹ * k) by group]
    exact mul_mem (mem_sup_left ha'A) (mem_sup_right hz)
  have hcomm : commutator ↥K = ⊤ := by
    have := (Subgroup.isPerfect_iff.mpr hKperf)
    exact this.commutator_eq_top
  have htop := Sol76.eq_top_of_sup_center_eq_top' hcomm hsup
  intro k hk
  have h1 : (⟨k, hk⟩ : ↥K) ∈ A.subgroupOf K := by rw [htop]; trivial
  exact (mem_inf.mp (mem_subgroupOf.mp h1)).2

theorem le_normalizer_oddResidualIn (Y : Subgroup G) :
    Y ≤ normalizer (oddResidualIn Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CatalogueBPrimeJoin.primeResidual 2 ↥Y).Characteristic :=
    CatalogueBPrimeJoin.primeResidual_characteristic 2 ↥Y
  rw [oddResidualIn_eq_map_primeResidual]
  refine le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, Normal.conj_mem inferInstance y hy _, ?_⟩
  simp

omit [Finite G] in
theorem mem_of_mem_sup_of_coprime_index {W Y : Subgroup G} (hYW : Y ≤ normalizer (W : Set G))
    (hodd : Nat.Coprime 2 ((Y ⊓ W).subgroupOf Y).index) {x : G} (hx : x ∈ W ⊔ Y) {k : ℕ}
    (hk : orderOf x = 2 ^ k) : x ∈ W := by
  classical
  have hWn : W ⊔ Y ≤ normalizer (W : Set G) := sup_le le_normalizer hYW
  obtain ⟨w, hw, y, hy, rfl⟩ := exists_mul_of_mem_sup_normalizer hYW hx
  have hyk : y ^ (2 ^ k) ∈ W := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hWn
    set π := QuotientGroup.mk' (W.subgroupOf (W ⊔ Y)) with hπ
    have hw' : w ∈ W ⊔ Y := mem_sup_left hw
    have hy' : y ∈ W ⊔ Y := mem_sup_right hy
    have h1 : π ⟨w, hw'⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hw)
    have h2 : (⟨w, hw'⟩ * ⟨y, hy'⟩ : ↥(W ⊔ Y)) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, Subgroup.coe_mul, OneMemClass.coe_one, ← hk]
      exact pow_orderOf_eq_one _
    have h3 : π (⟨y, hy'⟩ ^ (2 ^ k)) = 1 := by
      have := congrArg π h2
      rwa [map_pow, map_mul, h1, one_mul, map_one, ← map_pow] at this
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf,
      SubgroupClass.coe_pow] at h3
    exact h3
  set N := (Y ⊓ W).subgroupOf Y with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, mem_subgroupOf] at hn ⊢
    obtain ⟨hnY, hnW⟩ := mem_inf.mp hn
    refine mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem (mul_mem g.2 hnY) (inv_mem g.2)
    · simp only [coe_mul, coe_inv]
      exact (mem_normalizer_iff.mp (hYW g.2) _).mp hnW
  set q := QuotientGroup.mk' N with hq
  have h4 : orderOf (q ⟨y, hy⟩) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, mem_subgroupOf]
    exact mem_inf.mpr ⟨by rw [SubgroupClass.coe_pow]; exact pow_mem hy _,
      by rw [SubgroupClass.coe_pow]; exact hyk⟩
  have h5 : orderOf (q ⟨y, hy⟩) ∣ N.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have h6 : Nat.Coprime (orderOf (q ⟨y, hy⟩)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left h5 hodd.symm)
  have h7 := Nat.Coprime.eq_one_of_dvd h6 h4
  rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN,
    mem_subgroupOf] at h7
  exact mul_mem hw (mem_inf.mp h7).2

theorem oddResidualIn_oddCoreIn_sup_eq {C Y : Subgroup G} (hYC : Y ≤ C)
    (hR : IsTwoComponentIn (oddResidualIn Y) C) :
    oddResidualIn (oddCoreIn C ⊔ Y) = oddResidualIn Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := oddResidualIn Y with hRdef
  set W := oddCoreIn C ⊔ R with hW
  have hRY : R ≤ Y := Sol76.oddResidualIn_le Y
  have hWres : oddResidualIn W = R := by
    rw [Sol78.oddResidualIn_eq_oPrimeResidualOf]
    exact Sol78.oPrimeResidualOf_core_sup_eq hR.1 hR.2
  have hYO : Y ≤ normalizer (oddCoreIn C : Set G) := hYC.trans (le_normalizer_oddCoreIn C)
  have hYR : Y ≤ normalizer (R : Set G) := le_normalizer_oddResidualIn Y
  have hYW : Y ≤ normalizer (W : Set G) := by
    intro y hy
    rw [mem_normalizer_iff_map_conj_eq] at *
    rw [hW, Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (hYO hy),
      mem_normalizer_iff_map_conj_eq.mp (hYR hy)]
  have hsup : oddCoreIn C ⊔ Y = W ⊔ Y := by
    rw [hW, sup_assoc, sup_eq_right.mpr hRY]
  have hodd : Nat.Coprime 2 ((Y ⊓ W).subgroupOf Y).index := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.index_dvd_of_le ?_)
      (coprime_index_oddResidualIn Y)
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact mem_inf.mpr ⟨hRY hx, mem_sup_right hx⟩
  apply le_antisymm
  · rw [← hWres]
    refine (closure_le _).mpr fun x hx => ?_
    obtain ⟨hxX, k, hk⟩ := hx
    exact subset_closure ⟨mem_of_mem_sup_of_coprime_index hYW hodd (hsup ▸ hxX) hk, k, hk⟩
  · exact closure_mono fun x hx => ⟨mem_sup_right hx.1, hx.2⟩

theorem isSolomonMember_of_twoLayerIn {L T : Subgroup G} (hLperf : ⁅L, L⁆ = L)
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTQ : T ≤ coreActionKernel L)
    (hK : IsTwoComponentIn (twoLayerIn (L ⊓ centralizer (T : Set G))) (centralizer (T : Set G))) :
    IsSolomonMember L := by
  obtain ⟨-, hLT, -, -⟩ := cover_facts hLq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hT2 hTQ)
  rw [hLT] at hK
  refine ⟨hLperf, T, hT, hT2, hTQ, ?_⟩
  rw [oddResidualIn_oddCoreIn_sup_eq inf_le_right hK]
  exact hK

theorem oddCoreIn_le_of_sup_eq {J L : Subgroup G} (hJL : J ≤ L) (hsup : J ⊔ oddCoreIn L = L) :
    oddCoreIn J ≤ oddCoreIn L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  have hOJL : oddCoreIn J ≤ L := (map_subtype_le _).trans hJL
  set X := (oddCoreIn J).subgroupOf L with hX
  have hJN : J ≤ normalizer (oddCoreIn J : Set G) := le_normalizer_oddCoreIn J
  have hON : J ≤ normalizer (oddCoreIn L : Set G) := hJL.trans (le_normalizer_oddCoreIn L)
  have hXn : (X.map π).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) g
    have hl : (l : G) ∈ J ⊔ oddCoreIn L := by rw [hsup]; exact l.2
    rw [sup_comm] at hl
    obtain ⟨o, ho, j, hj, hlo⟩ := exists_mul_of_mem_sup_normalizer hON hl
    obtain ⟨x, hx, rfl⟩ := hn
    have hjL : j ∈ L := hJL hj
    have hoL : o ∈ L := (map_subtype_le _) ho
    have hπo : π ⟨o, hoL⟩ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨o', ho', hoe⟩ := ho
      have : (⟨o, hoL⟩ : ↥L) = o' := Subtype.ext hoe.symm
      rw [this]
      exact ho'
    have hle : l = ⟨o, hoL⟩ * ⟨j, hjL⟩ := Subtype.ext hlo
    have hx' : (x : G) ∈ oddCoreIn J := by simpa [hX, mem_subgroupOf] using hx
    refine ⟨⟨j, hjL⟩ * x * ⟨j, hjL⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, hX, mem_subgroupOf]
      simp only [coe_mul, coe_inv]
      exact (mem_normalizer_iff.mp (hJN hj) _).mp hx'
    · rw [← hπ, hle]
      simp only [map_mul, map_inv, hπo, one_mul]
  have hXodd : Nat.Coprime 2 (Nat.card (X.map π)) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd X π) ?_
    have : Nat.card X = Nat.card (oddCoreIn J) := Nat.card_congr (subgroupOfEquivOfLe hOJL).toEquiv
    rw [this]
    exact coprime_card_oddCoreIn J
  have hXbot : X.map π ≤ ⊥ := by
    rw [← pPrimeCore_quotient_pPrimeCore_eq_bot 2]
    exact le_sSup ⟨hXn, hXodd⟩
  intro x hx
  have hxL : x ∈ L := hOJL hx
  have h1 : π ⟨x, hxL⟩ ∈ X.map π := mem_map_of_mem π (mem_subgroupOf.mpr hx)
  have h2 := hXbot h1
  rw [mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨⟨x, hxL⟩, h2, rfl⟩

omit [Finite G] in
theorem fusionZStar_eq_center_of_le' {Q : Type*} [Group Q] (hperf : commutator Q = ⊤)
    (hO : pPrimeCore 2 Q ≤ center Q) : Open.fusionZStar Q = center Q := by
  apply le_antisymm
  · intro z hz
    have hc : ∀ m : Q, ⁅z, m⁆ ∈ center Q := fun m =>
      hO ((GSThmB.OddQuot.mem_fusionZStar_iff.mp hz) m)
    let φ : Q →* Q :=
      { toFun := fun m => ⁅z, m⁆
        map_one' := by simp
        map_mul' := fun m₁ m₂ => by
          have h2 : m₁ * ⁅z, m₂⁆ * m₁⁻¹ = ⁅z, m₂⁆ := by
            rw [(mem_center_iff.mp (hc m₂) m₁), mul_inv_cancel_right]
          show ⁅z, m₁ * m₂⁆ = ⁅z, m₁⁆ * ⁅z, m₂⁆
          rw [← h2]
          simp only [commutatorElement_def]
          group }
    have hrange : φ.range ≤ center Q := by
      rintro _ ⟨m, rfl⟩
      exact hc m
    have h1 : (commutator Q).map φ = ⊥ := by
      rw [map_commutator_eq, commutator_eq_bot_iff_le_centralizer]
      exact hrange.trans (center_le_centralizer _)
    rw [hperf, ← MonoidHom.range_eq_map] at h1
    rw [mem_center_iff]
    intro m
    have hm : φ m = 1 := by
      have : φ m ∈ φ.range := ⟨m, rfl⟩
      rw [h1] at this
      exact this
    have hm' : ⁅z, m⁆ = 1 := hm
    rw [commutatorElement_eq_one_iff_mul_comm] at hm'
    exact hm'.symm
  · intro z hz
    refine GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun m => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz m).symm]
    exact one_mem _

end CFSG.ComponentClassification.Sol76T13
