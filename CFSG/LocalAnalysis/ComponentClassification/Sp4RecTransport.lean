module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallCover

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.ComponentClassification.GSThmB
  CFSG.ComponentClassification.UnbalancedLayer

section Generic

variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

theorem isPComponent_subgroupOf_map_iff (e : A ≃* B) {L X : Subgroup A} (hLX : L ≤ X) :
    IsPComponent 2 (L.subgroupOf X) ↔
      IsPComponent 2 ((L.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom)) := by
  set f : X ≃* X.map e.toMonoidHom := X.equivMapOfInjective e.toMonoidHom e.injective with hf
  rw [(LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two f).1]
  congr! 1
  ext ⟨y, hy⟩
  simp only [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨⟨x, hxX⟩, hxL, hxy⟩
    refine ⟨x, hxL, ?_⟩
    have := congrArg Subtype.val hxy
    exact this
  · rintro ⟨x, hxL, rfl⟩
    exact ⟨⟨x, hLX hxL⟩, hxL, rfl⟩

omit [Finite A] [Finite B] in
theorem map_centralizer_singleton_equiv (e : A ≃* B) (x : A) :
    (centralizer ({x} : Set A)).map e.toMonoidHom = centralizer ({e x} : Set B) := by
  ext y
  obtain ⟨y, rfl⟩ := e.surjective y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  simp only [MulEquiv.symm_apply_apply]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    exact e.injective (by rw [map_mul, map_mul, h])

end Generic

section Ambient

variable {H : Type*} [Group H] [Finite H] {G : Subgroup H}

omit [Finite H] in
theorem inf_subgroupOf_self (X : Subgroup H) : (X ⊓ G).subgroupOf G = X.subgroupOf G := by
  ext x
  simp [mem_subgroupOf]

theorem isPComponent_subgroupOf_restrict {L X : Subgroup H} (hLX : L ≤ X) (hLG : L ≤ G)
    (h : IsPComponent 2 (L.subgroupOf X)) :
    IsPComponent 2 ((L.subgroupOf G).subgroupOf (X.subgroupOf G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPComponent 2 (L.subgroupOf (X ⊓ G)) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hLX hLG) inf_le_left h
  rw [← inf_subgroupOf_self X]
  exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
    Nat.prime_two).mpr h1

theorem isPComponent_subgroupOf_extend [G.Normal] {L X : Subgroup H} (hLX : L ≤ X) (hLG : L ≤ G)
    (h : IsPComponent 2 ((L.subgroupOf G).subgroupOf (X.subgroupOf G))) :
    IsPComponent 2 (L.subgroupOf X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← inf_subgroupOf_self X] at h
  have h1 : IsPComponent 2 (L.subgroupOf (X ⊓ G)) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two).mp h
  have hn : ((X ⊓ G).subgroupOf X).IsSubnormal := by
    have : ((X ⊓ G).subgroupOf X).Normal := by
      rw [show (X ⊓ G).subgroupOf X = G.subgroupOf X by ext x; simp [mem_subgroupOf]]
      infer_instance
    exact Subgroup.Normal.isSubnormal this
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal (le_inf hLX hLG) inf_le_left
    hn).mpr h1

end Ambient

structure PairConfig (M : Type*) [Group M] [Finite M] (x : M) (K K' : Subgroup M) : Prop where
  orderOf_x : orderOf x = 2
  K_le : K ≤ centralizer ({x} : Set M)
  isPComponent_K : IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set M)))
  K'_le : K' ≤ centralizer ({x} : Set M)
  isPComponent_K' : IsPComponent 2 (K'.subgroupOf (centralizer ({x} : Set M)))
  ne : K ≠ K'
  x_mem_K : x ∈ K
  x_mem_K' : x ∈ K'
  iso : Nonempty (K ≃* K')
  layer : ∀ L : Subgroup M, L ≤ centralizer ({x} : Set M) →
    IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set M))) → L = K ∨ L = K'
  involution_K : ∀ u ∈ K, orderOf u = 2 → u = x
  involution_K' : ∀ u ∈ K', orderOf u = 2 → u = x
  card_center : Nat.card (center (K ⧸ pPrimeCore 2 K)) = 2
  sylow : ∀ T : Subgroup M, IsPGroup 2 T → T ≤ centralizer ((K ⊔ K' : Subgroup M) : Set M) →
    Nat.card T ≤ 2

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Config H)

theorem isQuasisimple_K : IsQuasisimple (c.K ⧸ pPrimeCore 2 c.K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1 c.isPComponent_K
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe c.K_le))).1 hq

theorem type_K : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
      Nonempty (c.K ⧸ Open.fusionZStar c.K ≃* alternatingGroup (Fin n))) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (c.K ⧸ Open.fusionZStar c.K) .PSL 2 p f := by
  obtain ⟨eJK⟩ := c.quotient_J_K
  rcases c.type_J with ⟨n, hn, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · exact .inl ⟨n, hn, ⟨eJK.symm.trans e⟩⟩
  · exact .inr ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv eJK hL⟩

theorem pRank_quotient_le_one : CFSG.pRank 2 (c.K ⧸ pPrimeCore 2 c.K) ≤ 1 :=
  (rankOne_witness_of_doubleCover CatFactsSmall.cfDoubleCover c.K c.isQuasisimple_K
    c.card_center c.type_K).1

theorem b_mem_G : c.b ∈ generalizedFitting H := c.K_le_G c.b_mem_K

theorem a_mem_centralizer_b : c.a ∈ centralizer ({c.b} : Set H) :=
  mem_centralizer_singleton_iff.mpr c.mul_comm_ab

theorem conjugate_K_le_G : conjugate c.K c.a ≤ generalizedFitting H := by
  have : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  intro x hx
  have h1 := c.K_le_G (mem_conjugate_iff.mp hx)
  have h2 : x = c.a⁻¹ * (c.a * x * c.a⁻¹) * c.a⁻¹⁻¹ := by group
  rw [h2]
  exact Subgroup.Normal.conj_mem this _ h1 _

theorem conjugate_K_le : conjugate c.K c.a ≤ centralizer ({c.b} : Set H) :=
  UnbalancedCorr.conjugate_le_of_mem c.K_le c.a_mem_centralizer_b

theorem isPComponent_conjugate_K :
    IsPComponent 2 ((conjugate c.K c.a).subgroupOf (centralizer ({c.b} : Set H))) :=
  UnbalancedCorr.isPComponent_conjugate_subgroupOf c.a_mem_centralizer_b c.isPComponent_K

theorem b_mem_conjugate_K : c.b ∈ conjugate c.K c.a := by
  rw [mem_conjugate_iff, c.mul_comm_ab, mul_assoc, mul_inv_cancel, mul_one]
  exact c.b_mem_K

theorem involution_eq_b {u : H} (hu : u ∈ c.K) (hu2 : orderOf u = 2) : u = c.b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨z, -, hz⟩, -, -⟩ :=
    LocalAnalysis.ComponentInitial.quasisimple_rank_one_unique_central_involution
      c.isQuasisimple_K c.pRank_quotient_le_one
  set π := QuotientGroup.mk' (pPrimeCore 2 c.K) with hπ
  have himage : ∀ w : c.K, orderOf w = 2 → orderOf (π w) = 2 := by
    intro w hw
    have hdvd := orderOf_map_dvd π w
    rw [hw] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exfalso
      rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 := Subgroup.orderOf_dvd_natCard _ h1
      rw [hw] at h2
      exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2
        (pPrimeCore_coprime_card (p := 2))
    · exact h1
  have hu' : orderOf (⟨u, hu⟩ : c.K) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hb' : orderOf (⟨c.b, c.b_mem_K⟩ : c.K) = 2 := by
    rw [Subgroup.orderOf_mk]; exact c.orderOf_b
  have heq : π ⟨u, hu⟩ = π ⟨c.b, c.b_mem_K⟩ :=
    (hz _ (himage _ hu')).trans (hz _ (himage _ hb')).symm
  have hO : (⟨u, hu⟩ : c.K) * (⟨c.b, c.b_mem_K⟩ : c.K)⁻¹ ∈ pPrimeCore 2 c.K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact mul_inv_eq_one.mpr heq
  have hcomm : u * c.b = c.b * u := (mem_centralizer_singleton_iff.mp (c.K_le hu))
  have hbb : c.b * c.b = 1 := by
    have h := pow_orderOf_eq_one c.b
    rwa [c.orderOf_b, pow_two] at h
  have huu : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at h
  have hsq : ((⟨u, hu⟩ : c.K) * (⟨c.b, c.b_mem_K⟩ : c.K)⁻¹) ^ 2 = 1 := by
    apply Subtype.ext
    simp only [pow_two, coe_mul, coe_inv, OneMemClass.coe_one]
    have hbinv : c.b⁻¹ = c.b := inv_eq_of_mul_eq_one_right hbb
    rw [hbinv]
    calc u * c.b * (u * c.b) = u * (c.b * u) * c.b := by group
      _ = u * (u * c.b) * c.b := by rw [hcomm]
      _ = (u * u) * (c.b * c.b) := by group
      _ = 1 := by rw [huu, hbb, one_mul]
  have hord : orderOf (⟨_, hO⟩ : pPrimeCore 2 c.K) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hsq))
  have hodd : orderOf (⟨_, hO⟩ : pPrimeCore 2 c.K) ∣ Nat.card (pPrimeCore 2 c.K) :=
    orderOf_dvd_natCard _
  have h1 : orderOf (⟨_, hO⟩ : pPrimeCore 2 c.K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd fun hd => Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl hd
        (pPrimeCore_coprime_card (p := 2))
  rw [orderOf_eq_one_iff] at h1
  have h2 := congrArg (fun w : pPrimeCore 2 c.K => ((w : c.K) : H)) h1
  simp only [coe_mul, coe_inv, OneMemClass.coe_one] at h2
  exact mul_inv_eq_one.mp h2

theorem involution_eq_b' {u : H} (hu : u ∈ conjugate c.K c.a) (hu2 : orderOf u = 2) :
    u = c.b := by
  have h1 := c.involution_eq_b (mem_conjugate_iff.mp hu) (by
    rw [show c.a * u * c.a⁻¹ = (MulAut.conj c.a) u from rfl, MulEquiv.orderOf_eq]; exact hu2)
  have h2 : u = c.a⁻¹ * (c.a * u * c.a⁻¹) * c.a := by group
  rw [h2, h1, mul_assoc, ← c.mul_comm_ab, ← mul_assoc, inv_mul_cancel, one_mul]

theorem sylow_centralizer (T : Subgroup H) (hT : IsPGroup 2 T)
    (hTC : T ≤ centralizer ((c.K ⊔ conjugate c.K c.a : Subgroup H) : Set H)) :
    Nat.card T ≤ 2 := by
  refine c.sylow T hT fun t ht => mem_inf.mpr ⟨?_, B5a.centralizer_le_coreActionKernel _ (hTC ht)⟩
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp (hTC ht) c.b (mem_sup_left c.b_mem_K)).symm

theorem map_centralizer_b {M : Type*} [Group M] (θ : ↥(generalizedFitting H) ≃* M) :
    ((centralizer ({c.b} : Set H)).subgroupOf (generalizedFitting H)).map θ.toMonoidHom =
      centralizer ({θ ⟨c.b, c.b_mem_G⟩} : Set M) := by
  rw [← map_centralizer_singleton_equiv θ]
  congr 1
  ext x
  rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

theorem pairConfig {M : Type*} [Group M] [Finite M] (θ : ↥(generalizedFitting H) ≃* M) :
    PairConfig M (θ ⟨c.b, c.b_mem_G⟩) ((c.K.subgroupOf (generalizedFitting H)).map θ.toMonoidHom)
      (((conjugate c.K c.a).subgroupOf (generalizedFitting H)).map θ.toMonoidHom) := by
  classical
  have hGn : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  set W := centralizer ({c.b} : Set H) with hW
  have hCx := c.map_centralizer_b θ
  have hKWG : c.K.subgroupOf (generalizedFitting H) ≤ W.subgroupOf (generalizedFitting H) :=
    fun x hx => mem_subgroupOf.mpr (c.K_le (mem_subgroupOf.mp hx))
  have hKaWG : (conjugate c.K c.a).subgroupOf (generalizedFitting H) ≤
      W.subgroupOf (generalizedFitting H) :=
    fun x hx => mem_subgroupOf.mpr (c.conjugate_K_le (mem_subgroupOf.mp hx))
  have hround : ∀ L : Subgroup M,
      ((L.map θ.symm.toMonoidHom).map (generalizedFitting H).subtype).subgroupOf
        (generalizedFitting H) = L.map θ.symm.toMonoidHom := by
    intro L
    exact Subgroup.comap_map_eq_self_of_injective (generalizedFitting H).subtype_injective _
  have hback : ∀ L : Subgroup M, (L.map θ.symm.toMonoidHom).map θ.toMonoidHom = L := by
    intro L
    rw [Subgroup.map_map]
    convert Subgroup.map_id L
    ext y
    simp
  have hback' : ∀ L : Subgroup (generalizedFitting H),
      (L.map θ.toMonoidHom).map θ.symm.toMonoidHom = L := by
    intro L
    rw [Subgroup.map_map]
    convert Subgroup.map_id L
    ext y
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact c.orderOf_b
  · rw [← hCx]; exact map_mono hKWG
  · rw [← hCx]
    exact (isPComponent_subgroupOf_map_iff θ hKWG).mp
      (isPComponent_subgroupOf_restrict c.K_le c.K_le_G c.isPComponent_K)
  · rw [← hCx]; exact map_mono hKaWG
  · rw [← hCx]
    exact (isPComponent_subgroupOf_map_iff θ hKaWG).mp
      (isPComponent_subgroupOf_restrict c.conjugate_K_le c.conjugate_K_le_G
        c.isPComponent_conjugate_K)
  ·
    intro h
    have h1 := Subgroup.map_injective θ.injective h
    have h2 := subgroupOf_inj.mp h1
    rw [inf_of_le_left c.K_le_G, inf_of_le_left c.conjugate_K_le_G] at h2
    exact c.conjugate_ne h2.symm
  · exact ⟨⟨c.b, c.b_mem_G⟩, mem_subgroupOf.mpr c.b_mem_K, rfl⟩
  · exact ⟨⟨c.b, c.b_mem_G⟩, mem_subgroupOf.mpr c.b_mem_conjugate_K, rfl⟩
  ·
    refine ⟨((c.K.subgroupOf (generalizedFitting H)).equivMapOfInjective _ θ.injective).symm.trans
      ((subgroupOfEquivOfLe c.K_le_G).trans ((c.K.equivMapOfInjective
        (MulAut.conj c.a⁻¹).toMonoidHom (MulAut.conj c.a⁻¹).injective).trans
        ((subgroupOfEquivOfLe c.conjugate_K_le_G).symm.trans
          (((conjugate c.K c.a).subgroupOf (generalizedFitting H)).equivMapOfInjective _
            θ.injective))))⟩
  ·
    intro L hL hLpc
    set L₁ : Subgroup H := (L.map θ.symm.toMonoidHom).map (generalizedFitting H).subtype with hL₁
    have hL₁G : L₁ ≤ generalizedFitting H := map_subtype_le _
    have hL₀W : L.map θ.symm.toMonoidHom ≤ W.subgroupOf (generalizedFitting H) := by
      rw [← hback' (W.subgroupOf (generalizedFitting H)), hCx]
      exact map_mono hL
    have hL₁W : L₁ ≤ W := by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_subgroupOf.mp (hL₀W hy)
    have hpc : IsPComponent 2 ((L₁.subgroupOf (generalizedFitting H)).subgroupOf
        (W.subgroupOf (generalizedFitting H))) := by
      rw [hround]
      rw [← hCx] at hL hLpc
      have := (isPComponent_subgroupOf_map_iff θ.symm hL).mp hLpc
      rwa [hback'] at this
    rcases c.layer L₁ hL₁W (isPComponent_subgroupOf_extend hL₁W hL₁G hpc) with h | h
    · left
      rw [← hback L, ← hround L, ← hL₁, h]
    · right
      rw [← hback L, ← hround L, ← hL₁, h]
  · rintro _ ⟨u, hu, rfl⟩ hu2
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hu2
    have h1 := c.involution_eq_b (mem_subgroupOf.mp hu)
      (by rw [Subgroup.orderOf_coe]; exact hu2)
    exact congrArg θ (Subtype.ext h1)
  · rintro _ ⟨u, hu, rfl⟩ hu2
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hu2
    have h1 := c.involution_eq_b' (mem_subgroupOf.mp hu)
      (by rw [Subgroup.orderOf_coe]; exact hu2)
    exact congrArg θ (Subtype.ext h1)
  ·
    have e : ((c.K.subgroupOf (generalizedFitting H)).map θ.toMonoidHom) ≃* c.K :=
      ((c.K.subgroupOf (generalizedFitting H)).equivMapOfInjective _ θ.injective).symm.trans
        (subgroupOfEquivOfLe c.K_le_G)
    exact (Nat.card_congr (Subgroup.centerCongr
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e)).toEquiv).trans c.card_center
  ·
    intro T hT hTC
    set T₁ : Subgroup H := (T.map θ.symm.toMonoidHom).map (generalizedFitting H).subtype with hT₁
    have hcard : Nat.card T₁ = Nat.card T := by
      rw [hT₁, Subgroup.card_map_of_injective (generalizedFitting H).subtype_injective,
        Subgroup.card_map_of_injective θ.symm.injective]
    have hT₁2 : IsPGroup 2 T₁ := (hT.map _).map _
    have hT₁C : T₁ ≤ centralizer ((c.K ⊔ conjugate c.K c.a : Subgroup H) : Set H) := by
      rintro _ ⟨g, ⟨t, ht, rfl⟩, rfl⟩
      have htC := hTC ht
      have hK : c.K ≤ centralizer ({(θ.symm t : H)} : Set H) := by
        intro k hk
        rw [mem_centralizer_singleton_iff]
        have h1 := mem_centralizer_iff.mp htC (θ ⟨k, c.K_le_G hk⟩)
          (mem_sup_left ⟨⟨k, c.K_le_G hk⟩, mem_subgroupOf.mpr hk, rfl⟩)
        have h2 := congrArg (fun z => ((θ.symm z : generalizedFitting H) : H)) h1
        simpa using h2
      have hKa : conjugate c.K c.a ≤ centralizer ({(θ.symm t : H)} : Set H) := by
        intro k hk
        rw [mem_centralizer_singleton_iff]
        have h1 := mem_centralizer_iff.mp htC (θ ⟨k, c.conjugate_K_le_G hk⟩)
          (mem_sup_right ⟨⟨k, c.conjugate_K_le_G hk⟩, mem_subgroupOf.mpr hk, rfl⟩)
        have h2 := congrArg (fun z => ((θ.symm z : generalizedFitting H) : H)) h1
        simpa using h2
      rw [mem_centralizer_iff]
      intro v hv
      exact (mem_centralizer_singleton_iff.mp (sup_le hK hKa hv))
    exact hcard ▸ c.sylow_centralizer T₁ hT₁2 hT₁C

theorem exists_fixed_component {M : Type*} [Group M] [Finite M]
    (θ : ↥(generalizedFitting H) ≃* M) :
    ∃ α : MulAut M, α ^ 2 = 1 ∧ α ≠ 1 ∧ ∃ L : Subgroup M,
      L ≤ FixedCommutingProduct.fixedSubgroup α ∧
      IsPComponent 2 (L.subgroupOf (FixedCommutingProduct.fixedSubgroup α)) ∧
      Nonempty (L ≃* c.J) := by
  classical
  have hGn : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  set α : MulAut M := MulAut.congr θ (MulAut.conjNormal c.a) with hα
  have hfix : FixedCommutingProduct.fixedSubgroup α =
      ((centralizer ({c.a} : Set H)).subgroupOf (generalizedFitting H)).map θ.toMonoidHom := by
    ext y
    obtain ⟨g, rfl⟩ := θ.surjective y
    rw [mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply, mem_subgroupOf, mem_centralizer_singleton_iff]
    change α (θ g) = θ g ↔ _
    have hαg : α (θ g) = θ (MulAut.conjNormal c.a g) := by
      simp [hα, MulAut.congr_apply]
    rw [hαg, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · intro h
      have h1 : c.a * (g : H) * c.a⁻¹ = g := congrArg Subtype.val h
      calc (g : H) * c.a = c.a * g * c.a⁻¹ * c.a := by rw [h1]
        _ = c.a * g := by group
    · intro h
      apply Subtype.ext
      change c.a * (g : H) * c.a⁻¹ = g
      rw [← h]
      group
  have hJG : c.J.subgroupOf (generalizedFitting H) ≤
      (centralizer ({c.a} : Set H)).subgroupOf (generalizedFitting H) :=
    fun x hx => mem_subgroupOf.mpr (c.J_le (mem_subgroupOf.mp hx))
  refine ⟨α, ?_, ?_, (c.J.subgroupOf (generalizedFitting H)).map θ.toMonoidHom, ?_, ?_, ?_⟩
  · rw [hα, ← map_pow, ← map_pow, ← c.orderOf_a, pow_orderOf_eq_one, map_one, map_one]
  ·
    intro h1
    have h2 : MulAut.conjNormal c.a = (1 : MulAut (generalizedFitting H)) := by
      have := congrArg (MulAut.congr θ).symm h1
      rwa [hα, MulEquiv.symm_apply_apply, map_one] at this
    have haC : c.a ∈ centralizer (generalizedFitting H : Set H) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h3 := congrArg (fun φ : MulAut (generalizedFitting H) => ((φ ⟨w, hw⟩ : _) : H)) h2
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc w * c.a = c.a * w * c.a⁻¹ * c.a := by rw [h3]
        _ = c.a * w := by group
    rw [c.centralizer_eq_bot, mem_bot] at haC
    have := c.orderOf_a
    rw [haC, orderOf_one] at this
    exact absurd this (by norm_num)
  · rw [hfix]; exact map_mono hJG
  · rw [hfix]
    exact (isPComponent_subgroupOf_map_iff θ hJG).mp
      (isPComponent_subgroupOf_restrict c.J_le c.J_le_G c.isPComponent_J)
  · exact ⟨((c.J.subgroupOf (generalizedFitting H)).equivMapOfInjective _ θ.injective).symm.trans
      (subgroupOfEquivOfLe c.J_le_G)⟩

end Config

end CFSG.ComponentClassification.Sp4Rec
