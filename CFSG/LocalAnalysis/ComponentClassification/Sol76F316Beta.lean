module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316Alpha

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inv_pow_mul_pow_mem {O : Subgroup G} {y z : G} (hy : y ∈ normalizer (O : Set G))
    (hz : z ∈ O) (n : ℕ) : (y ^ n)⁻¹ * (y * z) ^ n ∈ O := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hyO : y⁻¹ * ((y ^ n)⁻¹ * (y * z) ^ n) * y⁻¹⁻¹ ∈ O :=
      (mem_normalizer_iff.mp (inv_mem hy) _).mp ih
    have e : (y ^ (n + 1))⁻¹ * (y * z) ^ (n + 1) =
        y⁻¹ * ((y ^ n)⁻¹ * (y * z) ^ n) * y⁻¹⁻¹ * z := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact mul_mem hyO hz

theorem le_inf_sup_oddCoreIn_of_covers_components {D K X : Subgroup G}
    (hK : IsTwoComponentIn K D)
    (hcov : ∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn D, a = x * o) :
    K ≤ (K ⊓ X) ⊔ oddCoreIn K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreIn D with hO
  have hKD : K ≤ D := hK.1
  have hKO : K ≤ normalizer (O : Set G) := hKD.trans (le_normalizer_oddCoreIn D)
  have hOK : O ≤ normalizer (K : Set G) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hKD hK.2
  have hodd : Nat.Coprime 2 ((O ⊓ K).subgroupOf O).index :=
    Nat.Coprime.coprime_dvd_right (Subgroup.index_dvd_card _) (coprime_card_oddCoreIn D)
  calc K = oddResidualIn K := (oddResidualIn_eq_self_of_isPComponent hK.1 hK.2).symm
    _ ≤ (K ⊓ X) ⊔ oddCoreIn K := by
      refine (closure_le _).mpr ?_
      rintro a ⟨haK, e, hae⟩
      obtain ⟨x, hxX, o, ho, hax⟩ := hcov a haK
      have hx : x = a * o⁻¹ := by rw [hax]; group
      obtain ⟨f, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
      have hcop : m.Coprime (orderOf a) := by
        rw [hae]
        exact Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hm)
      obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
      set x₂ := (x ^ m) ^ k with hx₂
      have hx₂X : x₂ ∈ X := pow_mem (pow_mem hxX m) k
      have hxm : (x ^ m) ^ (2 ^ f) = 1 := by
        rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
      have hx₂2 : x₂ ^ (2 ^ f) = 1 := by
        rw [hx₂, ← pow_mul, mul_comm, pow_mul, hxm, one_pow]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx₂2)
      have hxKO : x ∈ K ⊔ O := by
        rw [hx]
        exact mul_mem (mem_sup_left haK) (mem_sup_right (inv_mem ho))
      have hx₂KO : x₂ ∈ K ⊔ O := pow_mem (pow_mem hxKO m) k
      have hx₂K : x₂ ∈ K := mem_of_mem_sup_of_coprime_index hOK hodd hx₂KO hj
      have h1 : (a ^ (m * k))⁻¹ * (a * o⁻¹) ^ (m * k) ∈ O :=
        inv_pow_mul_pow_mem (hKO haK) (inv_mem ho) (m * k)
      have h2 : a⁻¹ * x₂ ∈ O := by
        rw [pow_mul, hk, ← hx, pow_mul] at h1
        exact h1
      have h3 : x₂⁻¹ * a ∈ oddCoreIn K := by
        have h4 : x₂⁻¹ * a ∈ O := by
          have := inv_mem h2
          rwa [mul_inv_rev, inv_inv] at this
        exact oddCoreIn_inf_le hKD (mem_inf.mpr ⟨h4, mul_mem (inv_mem hx₂K) haK⟩)
      rw [show a = x₂ * (x₂⁻¹ * a) by group]
      exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hx₂K, hx₂X⟩)) (mem_sup_right h3)

theorem le_inf_sup_oddCoreIn_of_covers {N K X : Subgroup G} (hK : K ∈ kStarComponents N)
    (hcov : ∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (solomonKStarOf N), a = x * o) :
    K ≤ (K ⊓ X) ⊔ oddCoreIn K := by
  have hKD : K ≤ solomonKStarOf N := le_iSup₂_of_le K hK le_rfl
  exact le_inf_sup_oddCoreIn_of_covers_components
    (isTwoComponentIn_of_le hK.1 hKD (solomonKStarOf_le N)) hcov

theorem le_of_moved_twoComponent_of_le {M₁ M₂ K L : Subgroup G} (hKM : K ≤ M₂)
    (hO : oddCoreIn M₂ ≤ M₁)
    (hCb : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M₁)
    (hL : IsTwoComponentIn L M₂) {u v : G} (huK : u ∈ K) (hvK : v ∈ K) (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u ≠ v) (hc : u * v = v * u)
    (hmove : u ∉ normalizer (L : Set G)) : L ≤ M₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥M₂)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  set u' : ↥M₂ := ⟨u, hKM huK⟩ with hu'def
  set v' : ↥M₂ := ⟨v, hKM hvK⟩ with hv'def
  have hu2 : u' ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hu]
    exact pow_orderOf_eq_one u)
  have hv2 : v' ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hv]
    exact pow_orderOf_eq_one v)
  have hc' : u' * v' = v' * u' := Subtype.ext hc
  set U : Subgroup ↥M₂ := zpowers u' ⊔ zpowers v' with hU
  have hUsq : ∀ w ∈ U, w ^ 2 = 1 :=
    FooteLit.sq_eq_one_of_mem_sup (fun x hx => FooteLit.sq_eq_one_of_mem_zpowers hu2 hx)
      (fun x hx => FooteLit.sq_eq_one_of_mem_zpowers hv2 hx) fun x hx y hy => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow hc' i j).eq
  have hU2 : IsPGroup 2 U := fun w => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hUsq w w.2)⟩
  have hUK : U ≤ K.subgroupOf M₂ :=
    sup_le (zpowers_le.mpr (show u' ∈ K.subgroupOf M₂ from huK))
      (zpowers_le.mpr (show v' ∈ K.subgroupOf M₂ from hvK))
  have hL₀c : IsPComponent 2 (L.subgroupOf M₂) := hL.2
  have hLbar : CFSG.Open.IsComponentOf
      ((L.subgroupOf M₂).map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂))) ⊤ :=
    ((CatalogueBAlternating.pComponent_iff_minimal_image 2 (L.subgroupOf M₂)).mp hL₀c).2.1
  have hinj : ∀ {x y : ↥M₂}, x ∈ U → y ∈ U →
      QuotientGroup.mk' (pPrimeCore 2 ↥M₂) x = QuotientGroup.mk' (pPrimeCore 2 ↥M₂) y →
        x = y := fun hx hy h =>
    AschbacherToolkit.quotient_injective_on_of_isPGroup _ hNodd hU2 hx hy h
  have huU : u' ∈ U := mem_sup_left (mem_zpowers u')
  have hvU : v' ∈ U := mem_sup_right (mem_zpowers v')
  have hu1 : u' ≠ 1 := fun h => by
    have h1 : u = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hu
    omega
  have hv1 : v' ≠ 1 := fun h => by
    have h1 : v = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hv
    omega
  have hub1 : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u' ≠ 1 := fun h =>
    hu1 (hinj huU U.one_mem (h.trans (map_one _).symm))
  have hvb1 : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v' ≠ 1 := fun h =>
    hv1 (hinj hvU U.one_mem (h.trans (map_one _).symm))
  have hubvb : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u' ≠ QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v' :=
    fun h => huv (congrArg Subtype.val (hinj huU hvU h))
  have hubub : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u' * QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u' =
      1 := by rw [← map_mul, ← sq, hu2, map_one]
  have hvbvb : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v' * QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v' =
      1 := by rw [← map_mul, ← sq, hv2, map_one]
  have hcomm : Commute (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u')
      (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v') := by
    change QuotientGroup.mk' _ u' * QuotientGroup.mk' _ v' =
      QuotientGroup.mk' _ v' * QuotientGroup.mk' _ u'
    rw [← map_mul, ← map_mul, hc']
  have hmoved : AschbacherComponentAction.rightComponent
      ((L.subgroupOf M₂).map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂)))
      (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u') ≠
        (L.subgroupOf M₂).map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂)) := by
    intro h
    have h2 : u' ∈ normalizer ((L.subgroupOf M₂ : Subgroup ↥M₂) : Set ↥M₂) :=
      UnbalancedLayer.mem_normalizer_of_map hL₀c
        ((AschbacherComponentAction.rightComponent_eq_iff_normalizer _ _).mp h)
    apply hmove
    rw [mem_normalizer_iff_map_conj_eq] at h2 ⊢
    change (L.subgroupOf M₂).map (MulAut.conj u').toMonoidHom = L.subgroupOf M₂ at h2
    change L.map (MulAut.conj u).toMonoidHom = L
    have h3 := map_subtype_map_conj_eq (L.subgroupOf M₂) u'
    rw [h2, map_subgroupOf_eq_of_le hL.1] at h3
    exact h3.symm
  have hle := AschbacherToolkit.moved_component_le_centralizerJoin
    (U.map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂)))
    ((L.subgroupOf M₂).map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂)))
    (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u') (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v') hLbar
    (mem_map_of_mem _ huU) (mem_map_of_mem _ hvU) hubub hvbvb hub1 hvb1 hubvb hcomm hmoved
  rw [AschbacherToolkit.centralizerJoin_quotient_of_isPGroup _ hNodd hU2] at hle
  have hL₀le : L.subgroupOf M₂ ≤ AschbacherToolkit.centralizerJoin U ⊔ pPrimeCore 2 ↥M₂ := by
    have h1 := map_le_iff_le_comap.mp hle
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hCJ : AschbacherToolkit.centralizerJoin U ≤ M₁.subgroupOf M₂ := by
    apply iSup₂_le
    intro w hw y hy
    have hw2 : ((w : ↥M₂) : G) ^ 2 = 1 := by
      rw [← SubgroupClass.coe_pow, hUsq w w.2, OneMemClass.coe_one]
    have hwo : orderOf ((w : ↥M₂) : G) = 2 := orderOf_eq_prime hw2 fun h => hw (Subtype.ext h)
    exact hCb ((w : ↥M₂) : G) (hUK w.2) hwo (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)))
  calc L = (L.subgroupOf M₂).map M₂.subtype := (map_subgroupOf_eq_of_le hL.1).symm
    _ ≤ (AschbacherToolkit.centralizerJoin U ⊔ pPrimeCore 2 ↥M₂).map M₂.subtype := map_mono hL₀le
    _ = (AschbacherToolkit.centralizerJoin U).map M₂.subtype ⊔ oddCoreIn M₂ := map_sup _ _ _
    _ ≤ M₁ := sup_le (map_le_iff_le_comap.mpr hCJ) hO

theorem le_normalizer_of_permutes_of_inf {M₁ M₂ X : Subgroup G}
    (hX : IsTwoComponentIn X (M₁ ⊓ M₂)) (hXr : 2 ≤ CFSG.Open.pRank 2 X)
    (hnc : ∃ q : ↥X ⧸ pPrimeCore 2 ↥X, orderOf q = 2 ∧ q ∉ center (↥X ⧸ pPrimeCore 2 ↥X))
    (hO : oddCoreIn M₂ ≤ M₁) (hCb : ∀ s ∈ X, orderOf s = 2 → centralizer ({s} : Set G) ≤ M₁)
    {𝒮 : Set (Subgroup G)} (h𝒮 : ∀ J ∈ 𝒮, IsTwoComponentIn J M₂)
    (hperm : ∀ k ∈ X, ∀ J ∈ 𝒮, J.map (MulAut.conj k).toMonoidHom ∈ 𝒮) :
    ∀ J ∈ 𝒮, X ≤ normalizer (J : Set G) := by
  by_contra hP
  push Not at hP
  have hXq := isQuasisimple_quotient_of_isPComponent hX.1 hX.2
  have hXres := oddResidualIn_eq_self_of_isPComponent hX.1 hX.2
  obtain ⟨u, huX, hu, J, hJ, hmove⟩ :=
    exists_involution_not_mem_normalizer hperm hXres hXq hnc hP
  obtain ⟨v, hvX, hv, hvu, huv⟩ := exists_commuting_involution_ne hXr huX hu
  have hXM₂ : X ≤ M₂ := hX.1.trans inf_le_right
  have hJM₁ : J ≤ M₁ :=
    le_of_moved_twoComponent_of_le hXM₂ hO hCb (h𝒮 J hJ) huX hvX hu hv (Ne.symm hvu) huv hmove
  have hJC : IsTwoComponentIn J (M₁ ⊓ M₂) := ⟨le_inf hJM₁ (h𝒮 J hJ).1,
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJM₁ (h𝒮 J hJ).1) inf_le_right
      (h𝒮 J hJ).2⟩
  have hne : J ≠ X := by
    rintro rfl
    exact hmove (le_normalizer huX)
  exact hmove (GSThmB.B5a.le_coreActionKernel_of_ne hJC.1 hX.1 hJC.2 hX.2 hne huX).1

theorem exists_noncentral_involution_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ q : B, orderOf q = 2 ∧ q ∉ center B) : ∃ q : A, orderOf q = 2 ∧ q ∉ center A := by
  obtain ⟨q, hq2, hqc⟩ := h
  refine ⟨e.symm q, by rw [MulEquiv.orderOf_eq]; exact hq2, fun hc => hqc ?_⟩
  rw [mem_center_iff] at hc ⊢
  intro y
  have h1 := congrArg e (hc (e.symm y))
  simpa using h1

theorem mem_normalizer_of_covers_modO
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hq : QuasisimpleTwoPartInput) (hG : KStarKProper G) {N : Subgroup G}
    (hr : ∃ K₁ ∈ kStarComponents N, ∃ K₂ ∈ kStarComponents N, K₁ ≠ K₂)
    (hKH : solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N)
    (hCb : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G))
    {K : Subgroup G} (hK : K ∈ kStarComponents N) {g : G} {X : Subgroup G}
    (hX : X ≤ conjugate (normalizer (solomonKStarOf N : Set G)) g)
    (hcov : ∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (solomonKStarOf N), a = x * o) :
    g ∈ normalizer (solomonKStarOf N : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := solomonKStarOf N with hD
  set M := normalizer (D : Set G) with hM
  set Mg := conjugate M g with hMg
  by_cases hα : (∃ K ∈ kStarComponents N, ∃ s ∈ K, orderOf s = 2 ∧
        ∃ L ∈ kStarComponents N, s ∈ coreActionKernel (conjugate L g)) ∨
      (∃ L ∈ kStarComponents N, ∃ s ∈ conjugate L g, orderOf s = 2 ∧
        ∃ K ∈ kStarComponents N, s ∈ coreActionKernel K)
  · exact mem_normalizer_of_caseAlpha_modO hq hG hr hKH hCb hα
  exfalso
  obtain ⟨hβ1, hβ2⟩ := not_or.mp hα
  push Not at hβ1 hβ2
  have hcomps : kStarComponents M = kStarComponents N :=
    kStarComponents_normalizer_eq_of_solomonKStarOf_eq hKH
  have hMgc : kStarComponents Mg = (fun J => conjugate J g) '' kStarComponents N := by
    rw [hMg, kStarComponents_conjugate, hcomps]
  have hLg : ∀ L ∈ kStarComponents N, conjugate L g ∈ kStarComponents Mg := by
    intro L hL
    rw [hMgc]
    exact ⟨L, hL, rfl⟩
  have hKMc : IsTwoComponentIn K M := (mem_kStarComponents_normalizer hK).1
  have hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
  have hsup : (K ⊓ Mg) ⊔ oddCoreIn K = K := by
    refine le_antisymm (sup_le inf_le_left (map_subtype_le _)) ?_
    exact (le_inf_sup_oddCoreIn_of_covers hK hcov).trans
      (sup_le_sup_right (inf_le_inf_left K hX) _)
  obtain ⟨hX₀2, -, hX₀sup, ⟨eX₀⟩⟩ := cover_facts hKq inf_le_left hsup
  set X₀ := oddResidualIn (K ⊓ Mg) with hX₀
  have hX₀C : IsTwoComponentIn X₀ (M ⊓ Mg) := isTwoComponentIn_inf_of_isTwoComponentIn hKMc hX₀2
  have hX₀K : X₀ ≤ K := hX₀2.1.trans inf_le_left
  have hX₀Mg : X₀ ≤ Mg := hX₀2.1.trans inf_le_right
  have hX₀M : X₀ ≤ M := hX₀C.1.trans inf_le_left
  have hX₀r : 2 ≤ CFSG.Open.pRank 2 X₀ :=
    (two_le_pRank_of_mem_solomonKStar hK.2).trans (pRank_le_of_sup_oddCoreIn hX₀K hX₀sup)
  have hX₀q : IsQuasisimple (↥X₀ ⧸ pPrimeCore 2 ↥X₀) :=
    isQuasisimple_quotient_of_isPComponent hX₀C.1 hX₀C.2
  have hX₀res : oddResidualIn X₀ = X₀ := oddResidualIn_eq_self_of_isPComponent hX₀C.1 hX₀C.2
  have hX₀perf : ⁅X₀, X₀⁆ = X₀ := UnbalancedCorr.commutator_eq_of_isPComponent hX₀C.1 hX₀C.2
  have hnc : ∃ q : ↥X₀ ⧸ pPrimeCore 2 ↥X₀, orderOf q = 2 ∧ q ∉ center (↥X₀ ⧸ pPrimeCore 2 ↥X₀) :=
    exists_noncentral_involution_of_mulEquiv eX₀
      (exists_noncentral_involution_coreQuot hq hG hK.1 hK.2)
  have hCX₀ : ∀ s ∈ X₀, orderOf s = 2 → centralizer ({s} : Set G) ≤ M := fun s hs hs2 =>
    hCb K hK s (hX₀K hs) hs2
  have hOMg : oddCoreIn Mg ≤ M :=
    le_of_coprime_of_pRank hX₀r hCX₀ (coprime_card_oddCoreIn Mg)
      (hX₀Mg.trans (le_normalizer_oddCoreIn Mg))
  have hnorm : ∀ J ∈ kStarComponents Mg, X₀ ≤ normalizer (J : Set G) :=
    le_normalizer_of_permutes_of_inf hX₀C hX₀r hnc hOMg hCX₀ (fun J hJ => hJ.1)
      fun k hk J hJ => map_conj_mem_kStarComponents hJ (hX₀Mg hk)
  obtain ⟨s, hsX₀, hs2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hX₀r)
  have hKgc := hLg K hK
  have hmove : ¬ X₀ ≤ coreActionKernel (conjugate K g) := fun h =>
    hβ1 K hK s (hX₀K hsX₀) hs2 K hK (h hsX₀)
  have hKgperf : ⁅conjugate K g, conjugate K g⁆ = conjugate K g :=
    UnbalancedCorr.commutator_eq_of_isPComponent hKgc.1.1 hKgc.1.2
  have hX₀N : X₀ ≤ normalizer (conjugate K g : Set G) := hnorm _ hKgc
  have hinner : X₀ ≤ conjugate K g ⊔ coreActionKernel (conjugate K g) :=
    le_sup_coreActionKernel_of_schreier hS hG hKgc.1 hKgc.2 hX₀perf hX₀N
  set Qg := coreActionKernel (conjugate K g) with hQg
  have hKgQ : conjugate K g ≤ normalizer (Qg : Set G) := fun k hk =>
    FooteLit.mem_normalizer_coreActionKernel (le_normalizer hk)
  have hX₀Q : X₀ ≤ normalizer (Qg : Set G) := fun k hk =>
    FooteLit.mem_normalizer_coreActionKernel (hX₀N hk)
  have hcard : Nat.card (↥(conjugate K g) ⧸ Open.fusionZStar ↥(conjugate K g)) =
      Nat.card (↥X₀ ⧸ Open.fusionZStar ↥X₀) := by
    set e : ↥K ≃* ↥(conjugate K g) :=
      K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective with he
    rw [← Nat.card_congr (Sol78.fusionZStarQuotCongr e).toEquiv,
      Nat.card_congr (Sol78.fusionZStarQuotOfCore eX₀).toEquiv]
  have hall : conjugate K g ≤ X₀ ⊔ Qg :=
    le_sup_coreActionKernel_of_card_fusionZStar hX₀q hX₀res hKgQ hX₀Q hinner hmove hcard
  have hOKg : oddCoreIn (conjugate K g) ≤ M :=
    le_of_coprime_of_pRank hX₀r hCX₀ (coprime_card_oddCoreIn _) fun x hx =>
      mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hX₀N hx))
  have hKgM : conjugate K g ≤ M :=
    le_of_mutual_cover hKgperf hX₀N hX₀M hOKg hCX₀ hX₀res hX₀q hnc hinner hall
  have hKgC : IsTwoComponentIn (conjugate K g) (M ⊓ Mg) :=
    ⟨le_inf hKgM hKgc.1.1, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      (le_inf hKgM hKgc.1.1) inf_le_right hKgc.1.2⟩
  have hX₀eq : conjugate K g = X₀ := by
    by_contra hne
    exact hmove (GSThmB.B5a.le_coreActionKernel_of_ne hKgC.1 hX₀C.1 hKgC.2 hX₀C.2 hne)
  obtain ⟨K', hK', hK'K⟩ := exists_mem_ne_of_two hr K
  have hsKg : s ∈ conjugate K g := hX₀eq ▸ hsX₀
  exact hβ2 K hK s hsKg hs2 K' hK'
    (mem_coreActionKernel_of_ne hK hK' (Ne.symm hK'K) (hX₀K hsX₀))

end CFSG.ComponentClassification.Sol76T13
