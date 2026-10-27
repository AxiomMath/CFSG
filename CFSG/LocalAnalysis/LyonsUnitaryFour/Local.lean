module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Sylow
public import CFSG.LocalAnalysis.RankTwoShapes.CentralMovement
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralFourOddCore

public section

namespace CFSG.RankTwoShapes.UnitaryFourW

variable {K : Type} [Field K] {hK : Nat.card K = 16}

theorem sq_eq_one_iff_mem_center (w : unitaryFourW K hK) :
    w ^ 2 = 1 ↔ w ∈ Subgroup.center (unitaryFourW K hK) := by
  rw [center_eq_ker_firstCoord, mem_ker_firstCoord]
  constructor
  · intro h
    have h' := congrArg snd h
    rw [snd_sq, snd_one] at h'
    exact (pow_eq_zero_iff (by norm_num)).mp h'
  · intro h
    ext
    · rw [fst_sq, fst_one]
    · rw [snd_sq, h, snd_one, zero_pow (by norm_num)]

theorem sq_mem_center (w : unitaryFourW K hK) : w ^ 2 ∈ Subgroup.center (unitaryFourW K hK) := by
  rw [center_eq_ker_firstCoord, mem_ker_firstCoord, fst_sq]

end CFSG.RankTwoShapes.UnitaryFourW

namespace CFSG.LyonsUnitaryFour

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_center_iff_of_mulEquiv {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) (x : A) :
    ψ x ∈ Subgroup.center B ↔ x ∈ Subgroup.center A := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply ψ.injective
    rw [map_mul, map_mul, h]
  · intro h g
    obtain ⟨a, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul, h]

omit [Finite G] in
theorem mem_commutator_iff_of_mulEquiv {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) (x : A) :
    ψ x ∈ commutator B ↔ x ∈ commutator A := by
  have hmap : (commutator A).map ψ.toMonoidHom = commutator B := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr ψ.surjective, commutator_def]
  rw [← hmap]
  exact Subgroup.mem_map_iff_mem ψ.injective

omit [Finite G] in
theorem unitary_four_sylow_structure {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    Nat.card (S : Subgroup G) = 64 ∧
      Subgroup.center (S : Subgroup G) = commutator (S : Subgroup G) ∧
      (∀ y : (S : Subgroup G), y ^ 2 = 1 ↔ y ∈ Subgroup.center (S : Subgroup G)) ∧
      (∀ y : (S : Subgroup G), y ^ 2 ∈ Subgroup.center (S : Subgroup G)) ∧
      Nat.card (Subgroup.center (S : Subgroup G)) = 4 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩, -, hcard, hcz, -, hZcard, -, -, -, -⟩ :=
    CFSG.RankTwoShapes.unitaryFour_sylow_normCoordinates hT U
  obtain ⟨e₀⟩ := hSU
  set ψ := e₀.trans φ with hψ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr ψ.toEquiv, hcard]
  · ext y
    rw [← mem_center_iff_of_mulEquiv ψ, ← mem_commutator_iff_of_mulEquiv ψ, hcz]
  · intro y
    rw [← mem_center_iff_of_mulEquiv ψ,
      ← CFSG.RankTwoShapes.UnitaryFourW.sq_eq_one_iff_mem_center, ← map_pow]
    constructor
    · intro h; rw [h, map_one]
    · intro h; exact ψ.injective (by rw [h, map_one])
  · intro y
    rw [← mem_center_iff_of_mulEquiv ψ, map_pow]
    exact CFSG.RankTwoShapes.UnitaryFourW.sq_mem_center _
  · rw [← hZcard]
    exact Nat.card_congr (Subgroup.centerCongr ψ).toEquiv

theorem lyons_unitary_four_fusion_and_centralizers [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    Nat.card (S : Subgroup G) = 64 ∧
    (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype =
      ⁅(S : Subgroup G), (S : Subgroup G)⁆ ∧
    (∀ x ∈ (S : Subgroup G), x ^ 2 = 1 ↔
      x ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) ∧
    Nat.card (Subgroup.center (S : Subgroup G)) = 4 ∧
    (∀ w ∈ Subgroup.center (S : Subgroup G), w ^ 2 = 1) ∧
    Nat.card ((S : Subgroup G) ⧸ Subgroup.center (S : Subgroup G)) = 16 ∧
    (∀ x : (S : Subgroup G) ⧸ Subgroup.center (S : Subgroup G), x ^ 2 = 1) ∧
    (∀ P : Subgroup G, P ≤ (S : Subgroup G) → ∀ g : G,
      P.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) →
      ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
        ∀ x ∈ P, n⁻¹ * x * n = g⁻¹ * x * g) ∧
    ((Subgroup.centralizer (((Subgroup.center (S : Subgroup G)).map
        (S : Subgroup G).subtype : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3 ∧
    (∀ e ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype,
      ∀ f ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, e ≠ 1 → f ≠ 1 →
        ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * e * n⁻¹ = f) ∧
    (∀ t u : G, orderOf t = 2 → orderOf u = 2 → IsConj t u) ∧
    (∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ Subgroup.centralizer ({z} : Set G) =
        Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ Subgroup.centralizer
          (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
            Set G) ∧
      (∀ c ∈ Subgroup.centralizer ({z} : Set G),
        ∃ d ∈ Subgroup.centralizer
            (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
              Set G),
          ∃ k ∈ (CFSG.oddCore (Subgroup.centralizer ({z} : Set G))).map
              (Subgroup.centralizer ({z} : Set G)).subtype, c = d * k) ∧
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype).subgroupOf
          (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))) ≤
        Subgroup.center (Subgroup.centralizer ({z} : Set G) ⧸
          CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, hcz, hsq1, hsqZ, hZcard⟩ := unitary_four_sylow_structure hT S U hSU
  set Sg := (S : Subgroup G) with hSg
  set Z := (Subgroup.center Sg).map Sg.subtype with hZ
  have hZexp : ∀ w ∈ Subgroup.center Sg, w ^ 2 = 1 := fun w hw => (hsq1 w).mpr hw
  have hinv : ∀ t : Sg, orderOf t = 2 → t ∈ Subgroup.center Sg := fun t ht =>
    (hsq1 t).mp (by rw [← ht]; exact pow_orderOf_eq_one t)
  have hZcardG : Nat.card Z = 4 := by
    rw [hZ, Subgroup.card_map_of_injective Sg.subtype_injective, hZcard]
  have hZexpG : ∀ w ∈ Z, w ^ 2 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have h := congrArg Subtype.val (hZexp y hy)
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  have hZS : ∀ w ∈ Z, w ∈ Sg := fun w hw => (mem_map_center_iff.mp hw).1
  have hZcomm : Z = ⁅Sg, Sg⁆ := by
    rw [hZ, hcz, map_commutator_eq, Subgroup.range_subtype]
  have hsqG : ∀ x ∈ Sg, x ^ 2 = 1 ↔ x ∈ Z := by
    intro x hx
    constructor
    · intro h
      refine ⟨⟨x, hx⟩, (hsq1 ⟨x, hx⟩).mp (Subtype.ext ?_), rfl⟩
      rw [Subgroup.coe_pow]
      exact h
    · rintro ⟨y, hy, rfl⟩
      have h := congrArg Subtype.val ((hsq1 y).mpr hy)
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      exact h
  have hquot_card : Nat.card (Sg ⧸ Subgroup.center Sg) = 16 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Sg)
    rw [hcard, hZcard] at h
    omega
  have hquot_exp : ∀ x : Sg ⧸ Subgroup.center Sg, x ^ 2 = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hsqZ y
  have hinvcent : ∀ x ∈ Sg, x ^ 2 = 1 → ∀ s ∈ Sg, s * x = x * s := by
    intro x hx hx2 s hs
    exact (mem_map_center_iff.mp ((hsqG x hx).mp hx2)).2 s hs
  have hcommsq : ∀ a ∈ Sg, ∀ b ∈ Sg, (a⁻¹ * b⁻¹ * a * b) ^ 2 = 1 := by
    intro a ha b hb
    have hmem : a⁻¹ * b⁻¹ * a * b ∈ ⁅Sg, Sg⁆ := by
      have := Subgroup.commutator_mem_commutator (Sg.inv_mem ha) (Sg.inv_mem hb)
      rwa [commutatorElement_def, inv_inv, inv_inv] at this
    rw [← hZcomm] at hmem
    exact hZexpG _ hmem
  have hfusion : ∀ P : Subgroup G, P ≤ Sg → ∀ g : G,
      P.map (MulAut.conj g⁻¹).toMonoidHom ≤ Sg →
      ∃ n ∈ Subgroup.normalizer (Sg : Set G), ∀ x ∈ P, n⁻¹ * x * n = g⁻¹ * x * g :=
    fun P hP g hg => class_two_normalizer_fusion S hinvcent hcommsq hP hg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  have hSN : Sg ≤ N := Subgroup.le_normalizer
  have hfix : ∀ z ∈ Z, z ≠ 1 → ∀ n ∈ N, n * z * n⁻¹ = z → ∀ w ∈ Z, n * w * n⁻¹ = w :=
    fun z hz hz1 n hn hnz => normalizer_fix_centralizes_center_four S hZcardG hZexpG hz hz1 hn hnz
  have hconjZ : ∀ n ∈ N, ∀ w ∈ Z, n * w * n⁻¹ ∈ Z := fun n hn w hw => conj_mem_map_center hn hw
  obtain ⟨z₀, hz₀Z, hz₀1, -⟩ := exists_third_mem_four hZcardG (1 : G)
  obtain ⟨y₀, hy₀, hy₀z⟩ := hz₀Z
  have hy₀z' : (y₀ : G) = z₀ := hy₀z
  have hy₀ord : orderOf y₀ = 2 := by
    apply orderOf_eq_prime (hZexp y₀ hy₀)
    intro h; apply hz₀1; rw [← hy₀z', h]; rfl
  obtain ⟨g, hgS, hgz⟩ := CFSG.RankTwoShapes.simple_central_sylow_involution_movement hnonab S
    y₀ hy₀ hy₀ord
  rw [hy₀z'] at hgS hgz
  have hz₀Z : z₀ ∈ Z := ⟨y₀, hy₀, hy₀z⟩
  have hz₀S : z₀ ∈ Sg := hZS z₀ hz₀Z
  obtain ⟨n₀, hn₀N, hn₀⟩ := hfusion (Subgroup.zpowers z₀) (Subgroup.zpowers_le.mpr hz₀S) g
    (by
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      simpa [MulAut.conj_apply] using hgS)
  have hn₀z : n₀⁻¹ * z₀ * n₀ = g⁻¹ * z₀ * g := hn₀ z₀ (Subgroup.mem_zpowers z₀)
  let act : MulAction N G :=
    MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (n : N) (x : G), n • x = (n : G) * x * (n : G)⁻¹ := fun n x => rfl
  have hstab : MulAction.stabilizer N z₀ =
      (Subgroup.centralizer (Z : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' := hfix z₀ hz₀Z hz₀1 n n.2 h w hw
      calc w * n = (n * w * (n : G)⁻¹) * n := by rw [hw']
        _ = n * w := by group
    · intro h
      have h' := (Subgroup.mem_centralizer_iff.mp h) z₀ hz₀Z
      rw [← h']; group
  have hidx : ((Subgroup.centralizer (Z : Set G)).subgroupOf N).index =
      (MulAction.orbit N z₀).ncard := by
    rw [← hstab, MulAction.index_stabilizer]
  set Zst : Set G := (Z : Set G) \ {1} with hZst
  have hZst_card : Zst.ncard = 3 := by
    rw [hZst, Set.ncard_sdiff_singleton_of_mem (Z.one_mem), ← Nat.card_coe_set_eq]
    simp only [SetLike.coe_sort_coe]
    rw [hZcardG]
  have horb : MulAction.orbit N z₀ ⊆ Zst := by
    rintro _ ⟨n, rfl⟩
    refine ⟨?_, ?_⟩
    · change (n : G) * z₀ * (n : G)⁻¹ ∈ (Z : Set G)
      exact hconjZ n n.2 z₀ hz₀Z
    · change (n : G) * z₀ * (n : G)⁻¹ ∉ ({1} : Set G)
      intro h
      apply hz₀1
      have h' : (n : G) * z₀ * (n : G)⁻¹ = 1 := h
      calc z₀ = (n : G)⁻¹ * ((n : G) * z₀ * (n : G)⁻¹) * n := by group
        _ = 1 := by rw [h']; group
  have horb_le : (MulAction.orbit N z₀).ncard ≤ 3 :=
    hZst_card ▸ Set.ncard_le_ncard horb (Set.toFinite _)
  have hz' : g⁻¹ * z₀ * g ∈ MulAction.orbit N z₀ := by
    refine ⟨⟨n₀⁻¹, N.inv_mem hn₀N⟩, ?_⟩
    change n₀⁻¹ * z₀ * n₀⁻¹⁻¹ = _
    rw [inv_inv, hn₀z]
  have horb_ge : 2 ≤ (MulAction.orbit N z₀).ncard := by
    have hpair : ({z₀, g⁻¹ * z₀ * g} : Set G) ⊆ MulAction.orbit N z₀ := by
      intro x hx
      rcases hx with rfl | rfl
      · exact MulAction.mem_orbit_self _
      · exact hz'
    have := Set.ncard_le_ncard hpair (Set.toFinite _)
    rwa [Set.ncard_pair (Ne.symm hgz)] at this
  have hodd : Odd ((Subgroup.centralizer (Z : Set G)).subgroupOf N).index := by
    have hle : Sg.subgroupOf N ≤ (Subgroup.centralizer (Z : Set G)).subgroupOf N := by
      intro s hs
      rw [Subgroup.mem_subgroupOf] at hs ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact ((mem_map_center_iff.mp hw).2 s hs).symm
    have hSyl : ¬ 2 ∣ (Sg.subgroupOf N).index := by
      have := (S.subtype hSN).not_dvd_index
      rwa [Sylow.coe_subtype] at this
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSyl))
      (Subgroup.index_dvd_of_le hle)
  have hidx3 : ((Subgroup.centralizer (Z : Set G)).subgroupOf N).index = 3 := by
    rw [hidx] at hodd ⊢
    obtain ⟨k, hk⟩ := hodd
    omega
  have horb_eq : MulAction.orbit N z₀ = Zst :=
    Set.eq_of_subset_of_ncard_le horb (by rw [hZst_card, ← hidx, hidx3]) (Set.toFinite _)
  have htrans : ∀ e ∈ Z, ∀ f ∈ Z, e ≠ 1 → f ≠ 1 → ∃ n ∈ N, n * e * n⁻¹ = f := by
    intro e he f hf he1 hf1
    have he' : e ∈ MulAction.orbit N z₀ := horb_eq ▸ ⟨he, he1⟩
    have hf' : f ∈ MulAction.orbit N z₀ := horb_eq ▸ ⟨hf, hf1⟩
    obtain ⟨n₁, rfl⟩ := he'
    obtain ⟨n₂, rfl⟩ := hf'
    refine ⟨(n₂ : G) * (n₁ : G)⁻¹, N.mul_mem n₂.2 (N.inv_mem n₁.2), ?_⟩
    change (n₂ : G) * (n₁ : G)⁻¹ * ((n₁ : G) * z₀ * (n₁ : G)⁻¹) * ((n₂ : G) * (n₁ : G)⁻¹)⁻¹ =
      (n₂ : G) * z₀ * (n₂ : G)⁻¹
    group
  have hinvZ : ∀ t : G, orderOf t = 2 → ∃ h : G, h * t * h⁻¹ ∈ Z ∧ h * t * h⁻¹ ≠ 1 := by
    intro t ht
    obtain ⟨h, -, hhS⟩ := exists_conj_mem_sylow_of_le S le_top (Subgroup.mem_top t)
      ⟨1, by rw [pow_one, ← ht]; exact pow_orderOf_eq_one t⟩
    have hord : orderOf (h * t * h⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
    refine ⟨h, (hsqG _ hhS).mp (by rw [← hord]; exact pow_orderOf_eq_one _), ?_⟩
    intro h1
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hconj : ∀ t u : G, orderOf t = 2 → orderOf u = 2 → IsConj t u := by
    intro t u ht hu
    obtain ⟨h₁, h₁Z, h₁1⟩ := hinvZ t ht
    obtain ⟨h₂, h₂Z, h₂1⟩ := hinvZ u hu
    obtain ⟨n, -, hn⟩ := htrans _ h₁Z _ h₂Z h₁1 h₂1
    rw [isConj_iff]
    refine ⟨h₂⁻¹ * n * h₁, ?_⟩
    calc h₂⁻¹ * n * h₁ * t * (h₂⁻¹ * n * h₁)⁻¹
        = h₂⁻¹ * (n * (h₁ * t * h₁⁻¹) * n⁻¹) * h₂ := by group
      _ = u := by rw [hn]; group
  refine ⟨hcard, hZcomm, hsqG, hZcard, hZexp, hquot_card, hquot_exp, hfusion, hidx3,
    htrans, hconj, ?_⟩
  intro z hzZ hz1
  refine ⟨?_, ?_⟩
  · ext n
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hn, hnz⟩
      refine ⟨hn, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hnz' : n * z * n⁻¹ = z := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hnz, mul_inv_cancel_right]
      have hw' := hfix z hzZ hz1 n hn hnz' w hw
      calc w * n = (n * w * n⁻¹) * n := by rw [hw']
        _ = n * w := by group
    · rintro ⟨hn, hnZ⟩
      exact ⟨hn, Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hnZ) z hzZ).symm⟩
  · obtain ⟨y, hy, rfl⟩ := hzZ
    have hy1 : y ≠ 1 := fun h => hz1 (by rw [h]; rfl)
    obtain ⟨h1, h2, -⟩ := central_four_involution_centralizer_oddCore S hZcard hZexp hinv y hy hy1
    exact ⟨h1, h2⟩

end CFSG.LyonsUnitaryFour
