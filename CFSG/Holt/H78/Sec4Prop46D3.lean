module

public import CFSG.Holt.H78.Sec4Prop46D2

public section

namespace CFSG.Holt.H78

namespace CaseAD

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]
  {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

theorem exists_coordLift (X : CaseAStart G Ω α v P) (hS : Sec4Setting G Ω)
    (hP : Prop46Setup G Ω α v P) {i₀ : X.A.D.ι}
    (hΛ : X.Λ = (↑) '' {δ : holtDelta G Ω α X.β | ∀ j, j ≠ i₀ →
      X.A.D.coord δ j = X.A.D.coord X.γ j})
    (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α X.β))) (U : Finset X.A.D.ι) (hUi : i₀ ∉ U) :
    ∃ g ∈ caseACentralizer G Ω α X.β v X.Λ, ∀ (δ δ' : holtDelta G Ω α X.β),
      (δ' : Ω) = g • (δ : Ω) → ∀ k, X.A.D.coord δ' k = if k ∈ U then
        X.A.D.ρ k ⟨_, X.A.D.socPre_le_jHull (X.vDelta_mem_socPre hS hP)⟩ (X.A.D.coord δ k)
        else X.A.D.coord δ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Δ := holtDelta G Ω α X.β
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  have hw2 : IsPGroup 2 (Subgroup.zpowers X.w) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, sq]; exact mul_self_eq_one_of_mem_longInv X.w_mem.1)
  have hwΔ : X.w • Δ = Δ := by
    have := stabilizer_pair_le (G := G) α X.β X.w_mem_pair
    rwa [mem_stabilizer_iff] at this
  obtain ⟨T', -, hT', hwT'⟩ := exists_fusionIsSylowIn_ge_mem_normalizer (V := ⊥) IsPGroup.of_bot
    bot_le hw2 (X.w_mem_normalizer_caseACentralizer hwΔ)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normal_bot)]; exact Subgroup.mem_top _)
  have hstabΔ : caseACentralizer G Ω α X.β v Δ ≤ stabilizer G Δ := fun g hg => by
    have := stabilizer_pair_le (G := G) α X.β (stabilizer_inf_le_stabilizer_pair α X.β
      (Subgroup.mem_inf.mp hg).1.2)
    exact this
  have hT'1 : T' ≠ ⊥ := by
    obtain ⟨E₀, hE₀, hE₀𝒞, hE₀1⟩ := X.exists_isPGroup_le_caseACentralizer_holtDelta hP hT
    exact (fixSet_inter_subset_of_fusionIsSylowIn hT' hE₀ hE₀𝒞 hstabΔ
      (fun g hg => (Subgroup.mem_inf.mp hg).2) (fun δ hδ _ => hδ)).1 hE₀1
  have hT'v : v ∈ Subgroup.centralizer (T' : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun g hg => (Subgroup.mem_centralizer_iff.mp (hT'.1 hg).1.1 v (Subgroup.mem_zpowers v)).symm
  have hαT : α ∈ fixSet Ω T' := fun g hg => (hT'.1 hg).1.2.1
  have hβT : X.β ∈ fixSet Ω T' := fun g hg => (hT'.1 hg).1.2.2
  have hΔT : ∀ δ ∈ Δ, δ ∈ fixSet Ω T' := fun δ hδ g hg =>
    (mem_fixingSubgroup_iff G).mp (hT'.1 hg).2 δ hδ
  have h3 : 3 ≤ Nat.card (fixSet Ω T') := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_eq_three.mpr ⟨α, X.β, X.γ, X.α_ne, X.γ_ne.1.symm, X.γ_ne.2.symm,
      rfl⟩).symm.le.trans
      (Set.ncard_le_ncard (Set.insert_subset hαT (Set.insert_subset hβT
        (Set.singleton_subset_iff.mpr (hΔT _ X.γ.2)))) (Set.toFinite _))
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hT'.2.1 hT'1 h3
  set a : fixSet Ω T' := ⟨α, hαT⟩
  set b : fixSet Ω T' := ⟨X.β, hβT⟩
  set g₀ : fixSet Ω T' := ⟨X.γ, hΔT _ X.γ.2⟩
  have hnt : ∀ i, (Set.univ : Set (X.A.D.Ψc i)).Nontrivial := fun i =>
    Set.nontrivial_univ_iff.mpr (Fintype.one_lt_card_iff_nontrivial.mp
      (by have := X.A.D.five_le_card i; omega))
  obtain ⟨c, hcinj, hcalt, hcfib, hcpar⟩ := hS.exists_ccl X.α_ne X.A hT'.2.1 hT'1 h3
    (a := a) (b := b) rfl rfl (fun _ => Set.univ) (fun δ => iff_of_true (hΔT δ δ.2)
      fun _ => Set.mem_univ _) (fun i _ => by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card]; exact X.A.D.five_le_card i) DK
  set c' : X.A.D.ι → DK.ι := fun j => c ⟨j, hnt j⟩
  have hc'inj : Function.Injective c' := fun j j' h => congrArg Subtype.val (hcinj h)
  have hcard' : ∀ j, Fintype.card (DK.Ψc (c' j)) = Fintype.card (X.A.D.Ψc j) + 2 := fun j => by
    rw [(hcalt ⟨j, hnt j⟩).2.1, Set.ncard_univ, Nat.card_eq_fintype_card]
  have hout : IsOuterFactor (DK.M (c' i₀)) :=
    ⟨(hcalt ⟨i₀, hnt i₀⟩).1, by rw [hcard']; have := X.A.mod4 i₀; omega⟩
  have hker := DK.ker_outer ⟨c' i₀, hout⟩
  obtain ⟨W, hTW, hW, -, x, hxW, hx2, hxv, hxc⟩ :=
    hS.exists_sylow_centralizer_mul hT'.2.1 h3 hv2 hT'v X.w_mem.1 X.wv_mem hwT'
      (zpowers_isPGroup_two_of_pow_eq_one (n := 1) (by rw [pow_one, sq]; exact hv2))
      (Subgroup.mem_zpowers v) (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hT'v))
  have hxbar : restrictCentralizer Ω T' ⟨x, Subgroup.centralizer_le hTW hxW⟩ =
      restrictCentralizer Ω T' ⟨v, hT'v⟩ :=
    Subtype.ext (Equiv.ext fun ω => Subtype.ext (hxv ω ω.2))
  have hxS : (restrictCentralizer Ω T' ⟨x, Subgroup.centralizer_le hTW hxW⟩ :
      centralizerImage Ω T') ∈ DK.socPre := by
    rw [hxbar]
    exact hS.restrict_mem_socPre hT'.2.1 hT'1 h3 hT'v X.w_mem.1 X.wv_mem hwT' DK
  have hxJ := DK.socPre_le_jHull hxS
  set xJ : jHull (centralizerImage Ω T') (fixSet Ω T') := ⟨_, hxJ⟩
  have hxfix : ∀ ω : fixSet Ω T', v • (ω : Ω) = ω →
      ∀ k, DK.ρ k xJ (DK.coord ω k) = DK.coord ω k := fun ω hω k => by
    rw [← DK.coord_smul xJ ω k]
    congr 2
    exact Subtype.ext ((hxv ω ω.2).trans hω)
  have hxa := hxfix a hP.typeL.smul_eq
  have hxb := hxfix b (smul_eq_of_mem_p46Orbit X.mem)
  have hxg := hxfix g₀ X.v_fix
  have hxx : xJ * xJ = 1 := Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
    show x • x • (ω : Ω) = ω
    have h1 : x • (ω : Ω) ∈ fixSet Ω T' := smul_mem_fixSet_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTW hxW)) ω.2
    rw [hxv _ h1, hxv _ ω.2, ← mul_smul, hv2, one_smul])))
  have h24 := DK.socInvFixesBlocks_of_below (hS.star_centralizerImage hT'.2.1 h3)
    (hS.holtTheorem1Below_centralizerImage hT'.2.1 hT'1 h3)
  have hxω : ∀ ω ∈ orbit (jOddCore (centralizerImage Ω T') (fixSet Ω T')) a,
      x • (ω : Ω) = ω := fun ω hω => by
    have h1 := h24 xJ hxS (by rw [← Subgroup.coe_mul, hxx, Subgroup.coe_one]) a
      (by rw [DK.smul_eq_of_rho_eq h24 hxS hxx hxa]; exact mem_orbit_self a) ω hω
    exact congrArg Subtype.val h1
  choose ℓ hℓL hℓρ hℓk using fun j => DK.exists_mem_L_rho_eq
    (DK.rho_mem_M_of_mem_socPre (h := xJ) hxS (c' j))
  set S : Set (∀ k, Equiv.Perm (DK.Ψc k)) := (fun j => psiHom DK (ℓ j)) '' {j | j ≠ i₀}
  have hρℓ : ∀ j k, DK.ρ k (ℓ j) = if k = c' j then DK.ρ k xJ else 1 := fun j k => by
    split_ifs with hk
    · subst hk; exact hℓρ j
    · exact hℓk j k hk
  have hSsq : ∀ s ∈ S, s * s = 1 := by
    rintro _ ⟨j, -, rfl⟩
    funext k
    show DK.ρ k (ℓ j) * DK.ρ k (ℓ j) = 1
    rw [hρℓ]
    split_ifs
    · rw [← map_mul, hxx, map_one]
    · rw [mul_one]
  have hScomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t := by
    rintro _ ⟨j, -, rfl⟩ _ ⟨j', -, rfl⟩
    funext k
    show DK.ρ k (ℓ j) * DK.ρ k (ℓ j') = DK.ρ k (ℓ j') * DK.ρ k (ℓ j)
    rw [hρℓ, hρℓ]
    by_cases h1 : k = c' j <;> by_cases h2 : k = c' j' <;> simp [h1, h2]
  set Q := Subgroup.closure S
  have hQsq := mul_self_eq_one_of_mem_closure hSsq hScomm
  have hQ2 : IsPGroup 2 Q := isPGroup_of_mul_self hQsq
  have hSR : S ⊆ (psiHom DK).range := by rintro _ ⟨j, -, rfl⟩; exact ⟨ℓ j, rfl⟩
  have hQR : Q ≤ (psiHom DK).range := (Subgroup.closure_le _).mpr hSR
  have hlc : ∀ q ∈ Q, LiftsCommute (psiHom DK).range q (psiHom DK xJ) :=
    LiftsCommute.closure hSR (by
      rintro _ ⟨j, -, rfl⟩
      exact DK.liftsCommute_of_rho_eq_one hxS (i := c' j) (hℓk j) 1
        (by rw [pow_one, hℓρ j, inv_mul_cancel]))
  have hfixQ : ∀ y : ∀ k, DK.Ψc k, (∀ k, DK.ρ k xJ (y k) = y k) →
      ∀ q ∈ Q, ∀ k, q k (y k) = y k := by
    intro y hy
    have hle : Q ≤ Subgroup.pi Set.univ fun k =>
        MulAction.stabilizer (Equiv.Perm (DK.Ψc k)) (y k) :=
      (Subgroup.closure_le _).mpr (by
        rintro _ ⟨j, -, rfl⟩ k -
        show DK.ρ k (ℓ j) • y k = y k
        rw [hρℓ]
        split_ifs
        · exact hy k
        · rfl)
    exact fun q hq k => hle hq k (Set.mem_univ k)
  have hQi₀ : ∀ q ∈ Q, q (c' i₀) = 1 := by
    have hle : Q ≤ (Pi.evalMonoidHom (fun k => Equiv.Perm (DK.Ψc k)) (c' i₀)).ker :=
      (Subgroup.closure_le _).mpr (by
        rintro _ ⟨j, hj, rfl⟩
        show DK.ρ (c' i₀) (ℓ j) = 1
        rw [hρℓ, ite_eq_right (fun h => hj (hc'inj h).symm)])
    exact fun q hq => hle hq
  obtain ⟨E, hEW, hE2, hEx, hEα, hEψ, hEsurj⟩ := hS.exists_lift hT'.2.1 h3 hTW hW DK hker hxW
    hx2 hxJ hQ2 hQR hlc a hxω (hfixQ _ hxa)
  have hQsoc : Q ≤ (DK.socPre.subgroupOf (jHull (centralizerImage Ω T') (fixSet Ω T'))).map
      (psiHom DK) := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨j, -, rfl⟩
    exact ⟨ℓ j, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem (c' j) (hℓL j))), rfl⟩)
  have hEinv : ∀ (e : G) (he : e ∈ E), ∃ hJ : restrictCentralizer Ω T'
      ⟨e, Subgroup.centralizer_le hTW (hEW he)⟩ ∈ jHull (centralizerImage Ω T') (fixSet Ω T'),
      ((restrictCentralizer Ω T' ⟨e, Subgroup.centralizer_le hTW (hEW he)⟩ :
        centralizerImage Ω T') ∈ DK.socPre) ∧
      (⟨_, hJ⟩ : jHull (centralizerImage Ω T') (fixSet Ω T')) * ⟨_, hJ⟩ = 1 ∧
      psiHom DK ⟨_, hJ⟩ ∈ Q := by
    intro e he
    obtain ⟨hJ, hψ⟩ := hEψ e he
    set ē : jHull (centralizerImage Ω T') (fixSet Ω T') := ⟨_, hJ⟩
    refine ⟨hJ, ?_, ?_, hψ⟩
    · obtain ⟨s, hs, hsē⟩ := hQsoc hψ
      have hk : ((s⁻¹ * ē : jHull (centralizerImage Ω T') (fixSet Ω T')) :
          centralizerImage Ω T') ∈ jOddCore (centralizerImage Ω T') (fixSet Ω T') := by
        rw [← hker, DK.mem_jOrbitKernel_iff_rho]
        intro k
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact (congrFun hsē k)
      have := mul_mem (Subgroup.mem_subgroupOf.mp hs) (DK.jOddCore_le_socPre hk)
      rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
    · obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hE2) ⟨e, he⟩
      have hen : e ^ 2 ^ n = 1 := by
        have := pow_orderOf_eq_one (⟨e, he⟩ : E)
        rw [hn] at this
        exact congrArg Subtype.val this
      have hēn : (ē * ē) ^ 2 ^ n = 1 := by
        rw [← sq, ← pow_mul, mul_comm, pow_mul]
        have : ē ^ 2 ^ n = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          show (restrictCentralizer Ω T' ⟨e, _⟩) ^ 2 ^ n = 1
          rw [← map_pow, show (⟨e, Subgroup.centralizer_le hTW (hEW he)⟩ :
            Subgroup.centralizer (T' : Set G)) ^ 2 ^ n = 1 from Subtype.ext (by
              rw [Subgroup.coe_pow]; exact hen), map_one])
        rw [this, one_pow]
      have hk : ((ē * ē : jHull (centralizerImage Ω T') (fixSet Ω T')) :
          centralizerImage Ω T') ∈ jOddCore (centralizerImage Ω T') (fixSet Ω T') := by
        rw [← hker, DK.mem_jOrbitKernel_iff_rho]
        intro k
        rw [map_mul]
        exact congrFun (hQsq _ hψ) k
      exact Subtype.ext (eq_one_of_pow_two_pow_eq_one_of_mem odd_card_jOddCore hk
        (by rw [← Subgroup.coe_pow, hēn, Subgroup.coe_one]))
  have hrange : ∀ k, k ∉ Set.range c' → k ∉ Set.range c := fun k hk ⟨j, hj⟩ =>
    hk ⟨j.1, by rw [← hj]⟩
  have hE𝒞 : E ≤ caseACentralizer G Ω α X.β v X.Λ := by
    intro e he
    obtain ⟨hJ, hēS, hēē, hψ⟩ := hEinv e he
    set ē : jHull (centralizerImage Ω T') (fixSet Ω T') := ⟨_, hJ⟩
    have hfixē : ∀ ω : fixSet Ω T', (∀ k, DK.ρ k ē (DK.coord ω k) = DK.coord ω k) →
        e • (ω : Ω) = ω := fun ω hω =>
      congrArg Subtype.val (DK.smul_eq_of_rho_eq h24 hēS hēē hω)
    refine ⟨⟨?_, hEα e he, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨n, rfl⟩
      exact ((hxc e (hEW he) (hEx e he)).zpow_right n).eq.symm
    · exact hfixē b (hfixQ _ hxb _ hψ)
    · refine (mem_fixingSubgroup_iff G).mpr fun l hl => ?_
      rw [hΛ] at hl
      obtain ⟨δ, hδL, rfl⟩ := hl
      refine hfixē ⟨δ, hΔT δ δ.2⟩ fun k => ?_
      by_cases hk : k ∈ Set.range c'
      · obtain ⟨j, rfl⟩ := hk
        by_cases hj : j = i₀
        · subst hj
          show (psiHom DK ē) (c' j) _ = _
          rw [hQi₀ _ hψ, Equiv.Perm.one_apply]
        · have hco : DK.coord (⟨δ, hΔT δ δ.2⟩ : fixSet Ω T') (c' j) = DK.coord g₀ (c' j) :=
            ((hcfib ⟨j, hnt j⟩ _ g₀ δ.2 X.γ.2).1).mpr (hδL j hj)
          rw [hco]
          exact hfixQ _ hxg _ hψ (c' j)
      · rw [(hcpar k (hrange k hk) ⟨δ, hΔT δ δ.2⟩ δ.2).1]
        exact hfixQ _ hxa _ hψ k
  have hqQ : ∀ T : Finset X.A.D.ι, i₀ ∉ T →
      (fun k => if ∃ j ∈ T, c' j = k then DK.ρ k xJ else 1) ∈ Q := by
    intro T hT
    induction T using Finset.induction_on with
    | empty =>
      have : (fun k => if ∃ j ∈ (∅ : Finset X.A.D.ι), c' j = k then DK.ρ k xJ else 1) = 1 :=
        funext fun k => by simp
      rw [this]; exact Q.one_mem
    | insert j T hj ih =>
      have hj0 : j ≠ i₀ := fun h => hT (h ▸ Finset.mem_insert_self j T)
      have hT' : i₀ ∉ T := fun h => hT (Finset.mem_insert_of_mem h)
      have heq : (fun k => if ∃ j' ∈ insert j T, c' j' = k then DK.ρ k xJ else 1) =
          psiHom DK (ℓ j) * (fun k => if ∃ j' ∈ T, c' j' = k then DK.ρ k xJ else 1) := by
        funext k
        show (if ∃ j' ∈ insert j T, c' j' = k then DK.ρ k xJ else 1) =
          DK.ρ k (ℓ j) * (if ∃ j' ∈ T, c' j' = k then DK.ρ k xJ else 1)
        rw [hρℓ j k]
        by_cases hk : k = c' j
        · subst hk
          have hn : ¬ ∃ j' ∈ T, c' j' = c' j := fun ⟨j', hj', he⟩ => hj (hc'inj he ▸ hj')
          rw [ite_eq_left ⟨j, Finset.mem_insert_self j T, rfl⟩, ite_eq_left rfl, ite_eq_right hn,
            mul_one]
        · have hiff : (∃ j' ∈ insert j T, c' j' = k) ↔ ∃ j' ∈ T, c' j' = k := by
            constructor
            · rintro ⟨j', hj', he⟩
              rcases Finset.mem_insert.mp hj' with rfl | hj'
              · exact absurd he.symm hk
              · exact ⟨j', hj', he⟩
            · rintro ⟨j', hj', he⟩
              exact ⟨j', Finset.mem_insert_of_mem hj', he⟩
          rw [ite_eq_right hk, one_mul]
          exact if_congr hiff rfl rfl
      rw [heq]
      exact mul_mem (Subgroup.subset_closure ⟨j, hj0, rfl⟩) (ih hT')
  obtain ⟨g, hg, hJ, hgψ⟩ := hEsurj _ (hqQ U hUi)
  refine ⟨g, hE𝒞 hg, fun δ δ' hδ' k => ?_⟩
  have hgδ : g • (δ : Ω) ∈ Δ := X.smul_mem_holtDelta (stabilizer_inf_le_stabilizer_pair α X.β
    (Subgroup.mem_inf.mp (hE𝒞 hg)).1.2) δ.2
  have hvδ : v • (δ : Ω) ∈ Δ := X.smul_mem_holtDelta (X.v_mem_pair hP) δ.2
  rw [show δ' = ⟨g • (δ : Ω), hgδ⟩ from Subtype.ext hδ']
  set gJ : jHull (centralizerImage Ω T') (fixSet Ω T') := ⟨_, hJ⟩
  have e1 : (⟨g • (δ : Ω), hΔT _ hgδ⟩ : fixSet Ω T') =
      (gJ : centralizerImage Ω T') • (⟨δ, hΔT δ δ.2⟩ : fixSet Ω T') := rfl
  have hρg : DK.ρ (c' k) gJ = if ∃ j ∈ U, c' j = c' k then DK.ρ (c' k) xJ else 1 := by
    exact congrFun hgψ (c' k)
  by_cases hk : k ∈ U
  · rw [ite_eq_left hk]
    have h1 : DK.coord (⟨g • (δ : Ω), hΔT _ hgδ⟩ : fixSet Ω T') (c' k) =
        DK.coord (⟨v • (δ : Ω), hΔT _ hvδ⟩ : fixSet Ω T') (c' k) := by
      have e2 : (⟨v • (δ : Ω), hΔT _ hvδ⟩ : fixSet Ω T') =
          (xJ : centralizerImage Ω T') • (⟨δ, hΔT δ δ.2⟩ : fixSet Ω T') :=
        Subtype.ext (hxv _ (hΔT δ δ.2)).symm
      rw [e1, e2, DK.coord_smul gJ, DK.coord_smul xJ, hρg, ite_eq_left ⟨k, hk, rfl⟩]
    have h2 := ((hcfib ⟨k, hnt k⟩ _ _ hgδ hvδ).1).mp h1
    rw [show X.A.D.coord ⟨g • (δ : Ω), _⟩ k = X.A.D.coord ⟨g • (δ : Ω), hgδ⟩ k from rfl, h2]
    exact (X.coord_v hS hP).1 δ k
  · rw [ite_eq_right hk]
    have hn : ¬ ∃ j ∈ U, c' j = c' k := fun ⟨j, hj, he⟩ => hk (hc'inj he ▸ hj)
    have h1 : DK.coord (⟨g • (δ : Ω), hΔT _ hgδ⟩ : fixSet Ω T') (c' k) =
        DK.coord (⟨δ, hΔT δ δ.2⟩ : fixSet Ω T') (c' k) := by
      rw [e1, DK.coord_smul gJ, hρg, ite_eq_right hn, Equiv.Perm.one_apply]
    exact ((hcfib ⟨k, hnt k⟩ _ _ hgδ δ.2).1).mp h1

end Lift

section Klein

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem exists_klein (h5 : 5 ≤ Fintype.card Ψ) {z : Equiv.Perm Ψ} {γ : Ψ}
    (hz : z ∈ longInvAt (Equiv.Perm Ψ) Ψ γ) :
    ∃ κ : Equiv.Perm Ψ, κ ∈ alternatingGroup Ψ ∧ κ * κ = 1 ∧ Commute κ z ∧ κ γ = γ ∧
      κ ≠ 1 ∧ κ ≠ z := by
  have hzz := CCL.apply_apply_of_mem_longInv hz.1
  have hfix : ∀ x, z x = x ↔ x = γ := fun x => apply_eq_self_iff_of_mem_longInvAt_perm hz
  have : Nontrivial Ψ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, haγ⟩ := exists_ne γ
  set b := z a with hb
  have hba : b ≠ a := fun h => haγ ((hfix a).mp h)
  have hbγ : b ≠ γ := fun h => haγ (by rw [← hzz a, ← hb, h, (hfix γ).mpr rfl])
  obtain ⟨c, hcγ, hca, hcb⟩ := CCL.exists_ne_ne_ne_of_four_le (by omega) γ a b
  set d := z c with hd
  have hdc : d ≠ c := fun h => hcγ ((hfix c).mp h)
  have hdγ : d ≠ γ := fun h => hcγ (by rw [← hzz c, ← hd, h, (hfix γ).mpr rfl])
  have hda : d ≠ a := fun h => hcb (by rw [← hzz c, ← hd, h])
  have hdb : d ≠ b := fun h => hca (by rw [← hzz c, ← hd, h, hb, hzz])
  set κ := Equiv.swap a c * Equiv.swap b d with hκ
  have hdisj : Commute (Equiv.swap a c) (Equiv.swap b d) := by
    refine (Equiv.Perm.Disjoint.commute ?_)
    intro x
    by_cases hxa : x = a
    · subst hxa; right; exact Equiv.swap_apply_of_ne_of_ne hba.symm hda.symm
    · by_cases hxc : x = c
      · subst hxc; right; exact Equiv.swap_apply_of_ne_of_ne hcb hdc.symm
      · left; exact Equiv.swap_apply_of_ne_of_ne hxa hxc
  refine ⟨κ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, hκ, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Ne.symm hca), Equiv.Perm.sign_swap (Ne.symm hdb)]
    decide
  · rw [hκ, show Equiv.swap a c * Equiv.swap b d * (Equiv.swap a c * Equiv.swap b d) =
      Equiv.swap a c * Equiv.swap a c * (Equiv.swap b d * Equiv.swap b d) by
      rw [mul_assoc, ← mul_assoc (Equiv.swap b d), ← hdisj.eq]; group,
      Equiv.swap_mul_self, Equiv.swap_mul_self, one_mul]
  · show κ * z = z * κ
    have hzinv : z⁻¹ = z := inv_eq_self_of_mem_longInv hz.1
    have h1 : z * κ * z⁻¹ = κ := by
      rw [hκ, show z * (Equiv.swap a c * Equiv.swap b d) * z⁻¹ =
        (z * Equiv.swap a c * z⁻¹) * (z * Equiv.swap b d * z⁻¹) by group,
        ← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply, ← hb, ← hd, hzz, hzz]
      exact hdisj.eq.symm
    calc κ * z = (z * κ * z⁻¹) * z := by rw [h1]
      _ = z * κ := by group
  · rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hbγ.symm hdγ.symm,
      Equiv.swap_apply_of_ne_of_ne haγ.symm hcγ.symm]
  · intro h
    have := congrArg (fun π : Equiv.Perm Ψ => π a) h
    simp only [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hba.symm hda.symm,
      Equiv.swap_apply_left, Equiv.Perm.one_apply] at this
    exact hca this
  · intro h
    have := congrArg (fun π : Equiv.Perm Ψ => π a) h
    simp only [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hba.symm hda.symm,
      Equiv.swap_apply_left] at this
    exact hcb this

end Klein

@[expose] noncomputable def coordPermHom {G : Type} [Group G] {Ω : Type} [MulAction G Ω]
    {α β : Ω} (A : CaseAData G Ω α β) :
    (∀ k, Equiv.Perm (A.D.Ψc k)) →* Equiv.Perm (holtDelta G Ω α β) where
  toFun := coordPerm A
  map_one' := coordPerm_one A
  map_mul' := coordPerm_mul A

namespace DCase

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]
  {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)} {hS : Sec4Setting G Ω}
  {hP : Prop46Setup G Ω α v P} (H : DCase hS hP)

omit [Finite G] [FaithfulSMul G Ω] in
theorem 𝒞_le_stab (j : H.A₁.D.ι) : caseACentralizer G Ω α H.β₁ v (H.line j) ≤
    stabilizer G (holtDelta G Ω α H.β₁) := fun _ hg =>
  stabilizer_pair_le α H.β₁ (stabilizer_inf_le_stabilizer_pair α H.β₁ (Subgroup.mem_inf.mp
    (Subgroup.mem_inf.mp hg).1).2)

theorem card_Vdir_mul_card_le {F : Subgroup (Equiv.Perm (holtDelta G Ω α H.β₁))}
    (hF2 : IsPGroup 2 F)
    (hFN : inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀) ≤
      Subgroup.normalizer (F : Set (Equiv.Perm (holtDelta G Ω α H.β₁))))
    (hFK : F ≤ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀))
    (hFV : ∀ g (hg : g ∈ H.V), ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
      Equiv.Perm (holtDelta G Ω α H.β₁)) ∈ F →
      ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
        Equiv.Perm (holtDelta G Ω α H.β₁)) = 1) :
    Nat.card (H.Vdir H.i₀) * Nat.card F ≤ Nat.card H.V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 (H.Vdir H.i₀) := H.sylow.2.1.to_le inf_le_left
  set U := inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀) with hU
  set Q := U ⊔ F with hQ
  have hQ2 : IsPGroup 2 Q := (isPGroup_inducedPerm hV2 _).to_sup_of_normal_right' hF2 hFN
  have hQK : Q ≤ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀) :=
    sup_le (inducedPerm_mono (H.Vdir_le H.big_i₀)) hFK
  obtain ⟨R, hR𝒞, hVR, hR2, hRQ⟩ := exists_le_inducedPerm_eq hQ2 hQK hV2 (H.Vdir_le H.big_i₀)
    le_sup_left
  have hRV := H.card_le_of_line (H.proj_eq_univ H.big_i₀).1 hR𝒞 hR2
  have hRcard := card_inducedPerm_mul_card_ker (K := R) (Ψ := holtDelta G Ω α H.β₁)
    (h := hR𝒞.trans (H.𝒞_le_stab H.i₀))
  rw [hRQ] at hRcard
  have hVcard := card_inducedPerm_mul_card_ker (K := H.Vdir H.i₀) (Ψ := holtDelta G Ω α H.β₁)
    (h := H.Vdir_le_stab H.i₀)
  have hker : Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf (H.Vdir H.i₀)) ≤
      Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf R) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨⟨x.1.1, hVR x.1.2⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp x.2)⟩) fun x y h => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥((fixingSubgroup G
      (holtDelta G Ω α H.β₁)).subgroupOf R) => ((z : R) : G)) h))
  have hQcard : Nat.card U * Nat.card F ≤ Nat.card Q := by
    have hinj : Function.Injective (fun x : U × F =>
        (⟨(x.1 : Equiv.Perm (holtDelta G Ω α H.β₁)) * x.2,
          mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩ : Q)) := by
      rintro ⟨u, f⟩ ⟨u', f'⟩ h
      have h1 : (u : Equiv.Perm (holtDelta G Ω α H.β₁)) * f = u' * f' := congrArg Subtype.val h
      have h2 : (u' : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ * u =
          (f' : Equiv.Perm (holtDelta G Ω α H.β₁)) * (f : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ := by
        calc (u' : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ * u
            = (u' : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ * (u * f) *
                (f : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ := by group
          _ = _ := by rw [h1]; group
      obtain ⟨g, hg, hgπ⟩ := mem_inducedPerm.mp (mul_mem (inv_mem u'.2) u.2)
      have hgV := (Subgroup.mem_inf.mp hg).1
      have hgψ : ((twoPointElt (H.V_le_pair hgV) : twoPointSection G Ω α H.β₁) :
          Equiv.Perm (holtDelta G Ω α H.β₁)) = (u' : Equiv.Perm (holtDelta G Ω α H.β₁))⁻¹ * u :=
        Equiv.ext fun δ => Subtype.ext (hgπ δ).symm
      have h3 := hFV g hgV (by rw [hgψ, h2]; exact mul_mem f'.2 (inv_mem f.2))
      rw [hgψ] at h3
      have hu : (u : Equiv.Perm (holtDelta G Ω α H.β₁)) = u' := by
        have := congrArg ((u' : Equiv.Perm (holtDelta G Ω α H.β₁)) * ·) h3
        simpa using this
      have hf : (f : Equiv.Perm (holtDelta G Ω α H.β₁)) = f' := by
        rw [hu] at h1; exact mul_left_cancel h1
      rw [Subtype.ext hu, Subtype.ext hf]
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod] at this
  calc Nat.card (H.Vdir H.i₀) * Nat.card F
      = Nat.card U * Nat.card F *
          Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf (H.Vdir H.i₀)) := by
        rw [← hVcard]; ring
    _ ≤ Nat.card Q * Nat.card ((fixingSubgroup G (holtDelta G Ω α H.β₁)).subgroupOf R) :=
        Nat.mul_le_mul hQcard hker
    _ = Nat.card R := hRcard
    _ ≤ Nat.card H.V := hRV

theorem card_Vdir_mul_le
    (hlift : ∀ S ⊆ H.Tbig, H.eS S ∈ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀)) :
    Nat.card (H.Vdir H.i₀) * 2 ^ H.Tbig.card ≤ Nat.card H.V := by
  classical
  have hFV : ∀ g (hg : g ∈ H.V), ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
      Equiv.Perm (holtDelta G Ω α H.β₁)) ∈ H.RT H.Tbig →
      ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
        Equiv.Perm (holtDelta G Ω α H.β₁)) = 1 := by
    rintro g hg ⟨S, hS, hgS⟩
    have := H.eq_empty_of_eS hg (U := S) (fun k hk => by
      have := hS hk
      simp only [Tbig, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this.2) hgS
    rw [hgS, this, H.eS_empty]
  have hcard : 2 ^ H.Tbig.card ≤ Nat.card (H.RT H.Tbig) := by
    have hinj : Function.Injective (fun S : H.Tbig.powerset =>
        (⟨H.eS S, S, Finset.mem_powerset.mp S.2, rfl⟩ : H.RT H.Tbig)) := by
      rintro ⟨S, hS⟩ ⟨S', hS'⟩ h
      have h1 : H.eS S = H.eS S' := congrArg Subtype.val h
      have h2 : H.eS (symmDiff S S') = 1 := by
        rw [← H.eS_mul, h1, H.eS_mul_self]
      have h3 := H.eq_empty_of_eS (H.V.one_mem) (U := symmDiff S S') (fun k hk => by
        rcases Finset.mem_symmDiff.mp hk with ⟨hk, -⟩ | ⟨hk, -⟩
        · have := Finset.mem_powerset.mp hS hk
          simp only [Tbig, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
            true_and] at this
          exact this.2
        · have := Finset.mem_powerset.mp hS' hk
          simp only [Tbig, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
            true_and] at this
          exact this.2) (by
        rw [h2]; exact Equiv.ext fun δ => Subtype.ext (one_smul G (δ : Ω)))
      rw [← Finset.bot_eq_empty, symmDiff_eq_bot] at h3
      exact Subtype.ext h3
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := H.Tbig.powerset), Fintype.card_coe,
      Finset.card_powerset] at this
  have := H.card_Vdir_mul_card_le (H.isPGroup_RT _) H.Vdir_le_normalizer_RT
    (by rintro _ ⟨S, hS, rfl⟩; exact hlift S hS) hFV
  exact (Nat.mul_le_mul_left _ hcard).trans this

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [MulAction G Ω] in
theorem lt_two_pow_pred {n : ℕ} (hn : 3 ≤ n) : n < 2 ^ (n - 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> simp_all
    · have := ih h
      rw [Nat.succ_sub_one, show n = (n - 1) + 1 by omega, pow_succ]
      omega

theorem card_big_le_two
    (hlift : ∀ S ⊆ H.Tbig, H.eS S ∈ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀)) :
    (Finset.univ.filter fun k => 4 ≤ (proj H.A₁ H.V k).ncard).card ≤ 2 := by
  set n := (Finset.univ.filter fun k => 4 ≤ (proj H.A₁ H.V k).ncard).card with hn
  have hT : H.Tbig.card = n - 1 := by
    rw [Tbig, Finset.card_erase_of_mem (by simpa using H.big_i₀)]
  have h1 := H.card_V_le H.big_i₀
  rw [← hn] at h1
  have h2 := H.card_Vdir_mul_le hlift
  rw [hT] at h2
  have hpos : 0 < Nat.card (H.Vdir H.i₀) := Nat.card_pos
  by_contra hlt
  have h3 := lt_two_pow_pred (n := n) (by omega)
  have := Nat.mul_lt_mul_of_pos_left h3 hpos
  omega

omit [FaithfulSMul G Ω] in
theorem eS_mem_of_odd (hodd : Odd (Nat.card (twoPointKernel G Ω α H.β₁)))
    {S : Finset H.A₁.D.ι} (hSi : H.i₀ ∉ S) :
    H.eS S ∈ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀) := by
  classical
  have hcomm : ∀ T : Finset H.A₁.D.ι,
      H.eS T ∈ ⁅twoPointSection G Ω α H.β₁, twoPointSection G Ω α H.β₁⁆ := by
    intro T
    induction T using Finset.induction_on with
    | empty => rw [H.eS_empty]; exact one_mem _
    | insert k T hk ih =>
      obtain ⟨ℓ₀, hℓc, hℓk, hℓo⟩ := H.X₀.exists_coordElt hS hP k
      let ℓ : jHull (twoPointSection G Ω α H.β₁) (holtDelta G Ω α H.β₁) := ℓ₀
      have hℓk' : H.A₁.D.ρ k ℓ = H.vk k := hℓk
      have hℓo' : ∀ m, m ≠ k → H.A₁.D.ρ m ℓ = 1 := hℓo
      have hℓc' : ((ℓ : twoPointSection G Ω α H.β₁) : Equiv.Perm (holtDelta G Ω α H.β₁)) ∈
          ⁅twoPointSection G Ω α H.β₁, twoPointSection G Ω α H.β₁⁆ := hℓc
      have hℓ : ((ℓ : twoPointSection G Ω α H.β₁) : Equiv.Perm (holtDelta G Ω α H.β₁)) =
          H.eS {k} := Equiv.ext fun δ => CaseAData.coord_injective H.A₁ (funext fun m => by
        rw [coord_eS]
        show H.A₁.D.coord ((ℓ : twoPointSection G Ω α H.β₁) • δ) m = _
        rw [H.A₁.D.coord_smul ℓ δ m]
        by_cases hm : m = k
        · subst hm; rw [hℓk']; simp
        · rw [hℓo' m hm]; simp [hm])
      have heq : H.eS (insert k T) = H.eS {k} * H.eS T := by
        rw [H.eS_mul]
        congr 1
        ext x
        simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
        constructor
        · rintro (rfl | hx)
          · exact Or.inl ⟨rfl, hk⟩
          · exact Or.inr ⟨hx, fun h => hk (h ▸ hx)⟩
        · rintro (⟨rfl, -⟩ | ⟨hx, -⟩)
          · exact Or.inl rfl
          · exact Or.inr hx
      rw [heq, ← hℓ]
      exact mul_mem hℓc' ih
  obtain ⟨g, hgαβ, hg⟩ := exists_mem_stabilizer_eq_of_mem_commutator (hcomm S)
  have hvγ : ∀ k, H.vk k (H.A₁.D.coord H.γ₁Δ k) = H.A₁.D.coord H.γ₁Δ k := fun k =>
    (H.coord_v (δ := H.γ₁Δ) (δ' := H.γ₁Δ) H.v_γ₁.symm k).symm
  have hfixγ : H.eS S H.γ₁Δ = H.γ₁Δ := CaseAData.coord_injective H.A₁ (funext fun k => by
    rw [coord_eS]; split_ifs <;> simp [hvγ])
  have hgγ : g • H.γ₁ = H.γ₁ := by
    rw [← hg H.γ₁Δ, hfixγ]
  have hm : ∀ ε : holtDelta G Ω α H.β₁, v • (ε : Ω) ∈ holtDelta G Ω α H.β₁ := fun ε =>
    H.X₀.smul_mem_holtDelta (H.X₀.v_mem_pair hP) ε.2
  have hcv : ∀ δ ∈ holtDelta G Ω α H.β₁, g • v • δ = v • g • δ := by
    intro δ hδ
    set δ' : holtDelta G Ω α H.β₁ := ⟨δ, hδ⟩
    set vδ : holtDelta G Ω α H.β₁ := ⟨v • δ, hm δ'⟩
    have h1 : g • v • δ = (H.eS S vδ : Ω) := (hg vδ).symm
    have h2 : v • g • δ = (⟨v • (H.eS S δ' : Ω), hm _⟩ : holtDelta G Ω α H.β₁) := by
      rw [← hg δ']
    rw [h1, h2]
    congr 1
    refine CaseAData.coord_injective H.A₁ (funext fun k => ?_)
    rw [coord_eS, H.coord_v (δ := δ') (δ' := vδ) rfl,
      H.coord_v (δ := H.eS S δ') (δ' := ⟨v • (H.eS S δ' : Ω), hm _⟩) rfl, coord_eS]
    split_ifs <;> rfl
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one])
  obtain ⟨c, hc, hcvc, hcg⟩ := exists_commute_eqOn_of_odd_twoPointKernel H.γ₁_mem hodd
    (H.X₀.v_mem_stab hP) hv2 ⟨hgαβ, hgγ⟩ hcv
  refine mem_inducedPerm.mpr ⟨c, ⟨⟨Subgroup.mem_centralizer_iff.mpr ?_, hc.1⟩,
    (mem_fixingSubgroup_iff G).mpr ?_⟩, fun δ => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (hcvc.zpow_right n).eq.symm
  · rintro _ ⟨δ, hδ, rfl⟩
    rw [hcg _ δ.2, ← hg δ]
    congr 1
    refine CaseAData.coord_injective H.A₁ (funext fun k => ?_)
    rw [coord_eS]
    split_ifs with hk
    · have hki : k ≠ H.i₀ := fun h => hSi (h ▸ hk)
      rw [hδ k hki, hvγ]
    · rfl
  · rw [hcg _ δ.2, hg δ]

theorem eS_mem_of_even (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α H.β₁)))
    {S : Finset H.A₁.D.ι} (hSi : H.i₀ ∉ S) :
    H.eS S ∈ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀) := by
  obtain ⟨g, hg, hgc⟩ := exists_coordLift H.X₀ hS hP (i₀ := H.i₀) rfl hT S hSi
  refine mem_inducedPerm.mpr ⟨g, hg, fun δ => ?_⟩
  have hgδ : g • (δ : Ω) ∈ holtDelta G Ω α H.β₁ := H.X₀.smul_mem_holtDelta
    (stabilizer_inf_le_stabilizer_pair α H.β₁ (Subgroup.mem_inf.mp hg).1.2) δ.2
  refine congrArg Subtype.val (CaseAData.coord_injective H.A₁ (funext fun k => ?_) :
    H.eS S δ = ⟨g • (δ : Ω), hgδ⟩)
  rw [coord_eS]
  exact (hgc δ ⟨g • (δ : Ω), hgδ⟩ rfl k).symm

theorem big_iff (k : H.A₁.D.ι) : 4 ≤ (proj H.A₁ H.V k).ncard ↔ k = H.i₀ ∨ k = H.k₀ := by
  classical
  refine ⟨fun hk => ?_, fun h => h.elim (fun h => h ▸ H.big_i₀) (fun h => h ▸ H.big_k₀)⟩
  have hlift : ∀ S ⊆ H.Tbig, H.eS S ∈ inducedPerm (caseACentralizer G Ω α H.β₁ v
      (H.line H.i₀)) (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀) := fun S hS => by
    have hSi : H.i₀ ∉ S := fun h => by
      have := hS h
      simp [Tbig] at this
    by_cases hT : Odd (Nat.card (twoPointKernel G Ω α H.β₁))
    · exact H.eS_mem_of_odd hT hSi
    · exact H.eS_mem_of_even hT hSi
  have h2 := H.card_big_le_two hlift
  by_contra hne
  push Not at hne
  have h3 : ({H.i₀, H.k₀, k} : Finset H.A₁.D.ι) ⊆
      Finset.univ.filter fun k => 4 ≤ (proj H.A₁ H.V k).ncard := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    exacts [H.big_i₀, H.big_k₀, hk]
  have h4 := Finset.card_le_card h3
  rw [Finset.card_insert_of_notMem (by simp [H.ne.symm, hne.1.symm]),
    Finset.card_pair (Ne.symm hne.2)] at h4
  omega

omit [FaithfulSMul G Ω] in
theorem coordPerm_mem_of_odd (hodd : Odd (Nat.card (twoPointKernel G Ω α H.β₁)))
    {x : ∀ k, Equiv.Perm (H.A₁.D.Ψc k)}
    (hx : coordPerm H.A₁ x ∈ ⁅twoPointSection G Ω α H.β₁, twoPointSection G Ω α H.β₁⁆)
    (hxv : ∀ k, Commute (x k) (H.vk k))
    (hxγ : ∀ k, x k (H.A₁.D.coord H.γ₁Δ k) = H.A₁.D.coord H.γ₁Δ k) (hxi : x H.i₀ = 1) :
    coordPerm H.A₁ x ∈ inducedPerm (caseACentralizer G Ω α H.β₁ v (H.line H.i₀))
      (holtDelta G Ω α H.β₁) (H.𝒞_le_stab H.i₀) := by
  classical
  obtain ⟨g, hgαβ, hg⟩ := exists_mem_stabilizer_eq_of_mem_commutator hx
  have hfixγ : coordPerm H.A₁ x H.γ₁Δ = H.γ₁Δ :=
    CaseAData.coord_injective H.A₁ (funext fun k => by rw [coord_coordPerm, hxγ])
  have hgγ : g • H.γ₁ = H.γ₁ := by
    rw [← hg H.γ₁Δ, hfixγ]
  have hm : ∀ ε : holtDelta G Ω α H.β₁, v • (ε : Ω) ∈ holtDelta G Ω α H.β₁ := fun ε =>
    H.X₀.smul_mem_holtDelta (H.X₀.v_mem_pair hP) ε.2
  have hcv : ∀ δ ∈ holtDelta G Ω α H.β₁, g • v • δ = v • g • δ := by
    intro δ hδ
    set δ' : holtDelta G Ω α H.β₁ := ⟨δ, hδ⟩
    set vδ : holtDelta G Ω α H.β₁ := ⟨v • δ, hm δ'⟩
    have h1 : g • v • δ = (coordPerm H.A₁ x vδ : Ω) := (hg vδ).symm
    have h2 : v • g • δ = (⟨v • (coordPerm H.A₁ x δ' : Ω), hm _⟩ : holtDelta G Ω α H.β₁) := by
      rw [← hg δ']
    rw [h1, h2]
    congr 1
    refine CaseAData.coord_injective H.A₁ (funext fun k => ?_)
    rw [coord_coordPerm, H.coord_v (δ := δ') (δ' := vδ) rfl,
      H.coord_v (δ := coordPerm H.A₁ x δ') (δ' := ⟨v • (coordPerm H.A₁ x δ' : Ω), hm _⟩) rfl,
      coord_coordPerm, ← Equiv.Perm.mul_apply, (hxv k).eq, Equiv.Perm.mul_apply]
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one])
  obtain ⟨c, hc, hcvc, hcg⟩ := exists_commute_eqOn_of_odd_twoPointKernel H.γ₁_mem hodd
    (H.X₀.v_mem_stab hP) hv2 ⟨hgαβ, hgγ⟩ hcv
  refine mem_inducedPerm.mpr ⟨c, ⟨⟨Subgroup.mem_centralizer_iff.mpr ?_, hc.1⟩,
    (mem_fixingSubgroup_iff G).mpr ?_⟩, fun δ => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (hcvc.zpow_right n).eq.symm
  · rintro _ ⟨δ, hδ, rfl⟩
    rw [hcg _ δ.2, ← hg δ]
    congr 1
    refine CaseAData.coord_injective H.A₁ (funext fun k => ?_)
    rw [coord_coordPerm]
    by_cases hk : k = H.i₀
    · subst hk; rw [hxi, Equiv.Perm.one_apply]
    · rw [hδ k hk, hxγ]
  · rw [hcg _ δ.2, hg δ]

omit [FaithfulSMul G Ω] in
theorem vk_mem_longInvAt (k : H.A₁.D.ι) :
    H.vk k ∈ longInvAt (Equiv.Perm (H.A₁.D.Ψc k)) (H.A₁.D.Ψc k) (H.A₁.D.coord H.γ₁Δ k) := by
  have hvγ : H.vk k (H.A₁.D.coord H.γ₁Δ k) = H.A₁.D.coord H.γ₁Δ k :=
    (H.coord_v (δ := H.γ₁Δ) (δ' := H.γ₁Δ) H.v_γ₁.symm k).symm
  have : Nontrivial (H.A₁.D.Ψc k) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := H.A₁.D.five_le_card k; omega)
  obtain ⟨c, hc⟩ := exists_ne (H.A₁.D.coord H.γ₁Δ k)
  have hne : H.vk k ≠ 1 := fun h => hc (H.vk_fix (by rw [h, Equiv.Perm.one_apply]))
  have hsq : H.vk k ^ 2 = 1 := Equiv.ext fun x => by
    rw [sq, Equiv.Perm.mul_apply, H.vk_vk, Equiv.Perm.one_apply]
  exact ⟨⟨orderOf_eq_prime hsq hne, _, hvγ, fun x hx => H.vk_fix hx⟩, hvγ⟩

theorem mapsDir_k₀ {g : G} (hg : g ∈ H.Vdir H.i₀) : MapsDir H.A₁ g H.k₀ H.k₀ := by
  obtain ⟨hgV, hgN⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨σ, hσ⟩ := exists_mapsDir H.A₁ (H.V_le_pair hgV)
  have hσi₀ : σ H.i₀ = H.i₀ := MapsDir.eq H.A₁ (H.V_le_pair hgV) H.γ₁Δ (hσ H.i₀)
    (mapsDir_of_mem_twoPointNormalizer H.A₁ hgN)
  have hbig : 4 ≤ (proj H.A₁ H.V (σ H.k₀)).ncard := by
    rw [ncard_proj_eq_of_mapsDir H.A₁ (H.V_le_pair hgV) (Subgroup.le_normalizer hgV) (hσ H.k₀)]
    exact H.big_k₀
  rcases (H.big_iff _).mp hbig with h | h
  · exact absurd (σ.injective (h.trans hσi₀.symm)) H.ne
  · have := hσ H.k₀
    rwa [h] at this

end DCase

end CaseAD

end CFSG.Holt.H78
