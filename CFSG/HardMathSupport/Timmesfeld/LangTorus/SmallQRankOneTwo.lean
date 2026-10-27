module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false


section RankOneTwo

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

private theorem rootTorusSL2_conj_pinnedX_two {β α : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hα : IsRoot τ α) (c : Lˣ) (z : L) :
    rootTorusSL2 τ L β c * pinnedX τ L α z * (rootTorusSL2 τ L β c)⁻¹ =
      pinnedX τ L α (((c ^ (2 * iform β α / iform β β) : Lˣ) : L) * z) := by
  obtain ⟨-, hdH, -, -, hv, hH, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ L hβ
  obtain ⟨a, ha, -⟩ := hH _ (hdH c)
  have h1 := (hv c).2 α hα
  rw [ha] at h1
  change rootDiag a (rootVec τ L α) = _ at h1
  rw [rootDiag_rootVec a hα] at h1
  have hne : rootVec τ L α ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hα]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h2 := smul_left_injective L hne h1
  rw [ha, rootDiagUnit_conj_pinnedX a hα]
  congr 2

theorem exists_untwist_pair_torus_two (S : LangSetup τ L p) (hq : S.D.q = 2)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {m : ℕ} (hm : 0 < m)
    (hρ : (S.ρ : (Fin τ.rank → ℤ) → _)^[m] β = β) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L) (l0 l1 : L), (∀ c, σ c = c ^ (S.D.q ^ m)) ∧
      z ∈ torusGroup τ L ∧ l0 ≠ 0 ∧ l1 ≠ 0 ∧
      (∀ c : L, z * pinnedX τ L β c * z⁻¹ = pinnedX τ L β (l0 * c)) ∧
      (∀ c : L, z * pinnedX τ L (-β) c * z⁻¹ = pinnedX τ L (-β) (l1 * c)) ∧
      ∀ g ∈ rootSpan τ L {β, -β},
        iterHom S.D.step m (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
  classical
  have h2L : (2 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  have hneg : ∀ x : L, -x = x := fun x => by
    have h : (2 : L) * x = 0 := by rw [h2L, zero_mul]
    linear_combination (-1 : L) * h
  obtain ⟨r, e, hr, hchar, he, hqe⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * m)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ m) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * m) c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hqe, ← pow_mul]
  have hβn : IsRoot τ (-β) := IsRoot.neg hβ
  obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S m hβ
  obtain ⟨μ', hμ'0, hμ'⟩ := iter_step_pinnedX S m hβn
  rw [hρ] at hμ
  rw [rho_iterate_neg S m β, hρ] at hμ'
  obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  have hη1 : η = 1 := by
    have h : (η - 1) * (η - 1) = 0 := by linear_combination hη + (1 - η) * h2L
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h)
  have hs : ∀ x : L, (pinnedData τ β).2.2 • x = x := by
    intro x
    rcases pinnedSign_eq τ β with h | h <;> rw [h] <;> simp [hneg]
  have hu : ∀ c, iterHom S.D.step m (rootSL2 τ L β (uSL c)) =
      rootSL2 τ L β (uSL (μ * σ.toRingHom c)) := by
    intro c
    simp only [rootSL2_uSL_eq, hs, iterHom_eq_iterate, hμ, hσc, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
  have hv' : ∀ c, iterHom S.D.step m (rootSL2 τ L β (vSL c)) =
      rootSL2 τ L β (vSL (μ' * σ.toRingHom c)) := by
    intro c
    simp only [hv, hη1, one_mul, iterHom_eq_iterate, hμ', hσc, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
  have hμμ : μ * μ' = 1 := rank_one_scalar_compat hβ (iterHom S.D.step m) σ.toRingHom hμ0 hu hv'
  have hQ2 : 2 ≤ S.D.q ^ m := by
    rw [hq]
    exact Nat.le_self_pow hm.ne' 2
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq μ⁻¹ (show 0 < 2 * (S.D.q ^ m - 1) by omega)
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hc₀
    exact inv_ne_zero hμ0 hc₀.symm
  set cu : Lˣ := Units.mk0 c₀ hc₀ne with hcu
  have hl0 : μ * (c₀ ^ 2) ^ (S.D.q ^ m - 1) = 1 := by
    rw [← pow_mul, hc₀]
    exact mul_inv_cancel₀ hμ0
  have hl1 : μ' * ((c₀ ^ 2)⁻¹) ^ (S.D.q ^ m - 1) = 1 := by
    rw [inv_pow]
    have : (c₀ ^ 2) ^ (S.D.q ^ m - 1) = μ⁻¹ := by rw [← pow_mul, hc₀]
    rw [this, inv_inv, mul_comm]
    exact hμμ
  have hexp : 2 * iform β β / iform β β = 2 := Int.mul_ediv_cancel 2 (iform_self_pos_of_isRoot hβ).ne'
  have hexp' : 2 * iform β (-β) / iform β β = -2 := by
    rw [CFSG.LieType.Chevalley.iform_neg_right, show 2 * -(iform β β) = (-2) * iform β β by ring]
    exact Int.mul_ediv_cancel (-2) (iform_self_pos_of_isRoot hβ).ne'
  have hzU : ∀ c : L, rootTorusSL2 τ L β cu * pinnedX τ L β c * (rootTorusSL2 τ L β cu)⁻¹ =
      pinnedX τ L β (c₀ ^ 2 * c) := by
    intro c
    rw [rootTorusSL2_conj_pinnedX_two hβ hβ cu c, hexp]
    simp [hcu]
  have hzV : ∀ c : L, rootTorusSL2 τ L β cu * pinnedX τ L (-β) c * (rootTorusSL2 τ L β cu)⁻¹ =
      pinnedX τ L (-β) ((c₀ ^ 2)⁻¹ * c) := by
    intro c
    rw [rootTorusSL2_conj_pinnedX_two hβ hβn cu c, hexp']
    simp [hcu]
  have hzT : rootTorusSL2 τ L β cu ∈ torusGroup τ L :=
    (exceptional_Lang_root_rank_one_torus_transport τ L hβ).2.1 cu
  refine ⟨σ, rootTorusSL2 τ L β cu, c₀ ^ 2, (c₀ ^ 2)⁻¹, hσc, hzT, pow_ne_zero _ hc₀ne,
    inv_ne_zero (pow_ne_zero _ hc₀ne), hzU, hzV, ?_⟩
  set z := rootTorusSL2 τ L β cu with hz
  have hQ1 : S.D.q ^ m = (S.D.q ^ m - 1) + 1 := by omega
  have hrelU : ∀ c : L, iterHom S.D.step m (z * pinnedX τ L β c * z⁻¹) =
      z * frobGL σ (pinnedX τ L β c) * z⁻¹ := by
    intro c
    rw [hzU, iterHom_eq_iterate, hμ, frobGL_pinnedX, hzU, hσc, mul_pow]
    congr 1
    set k := S.D.q ^ m - 1
    have hpw : (c₀ ^ 2) ^ (S.D.q ^ m) = c₀ ^ 2 * (c₀ ^ 2) ^ k := by
      rw [hQ1, pow_succ']
    rw [hpw]
    linear_combination (c₀ ^ 2 * c ^ (S.D.q ^ m)) * hl0
  have hrelV : ∀ c : L, iterHom S.D.step m (z * pinnedX τ L (-β) c * z⁻¹) =
      z * frobGL σ (pinnedX τ L (-β) c) * z⁻¹ := by
    intro c
    rw [hzV, iterHom_eq_iterate, hμ', frobGL_pinnedX, hzV, hσc, mul_pow]
    congr 1
    set k := S.D.q ^ m - 1
    have hpw : ((c₀ ^ 2)⁻¹) ^ (S.D.q ^ m) = (c₀ ^ 2)⁻¹ * ((c₀ ^ 2)⁻¹) ^ k := by
      rw [hQ1, pow_succ']
    rw [hpw]
    linear_combination ((c₀ ^ 2)⁻¹ * c ^ (S.D.q ^ m)) * hl1
  have hle : rootSpan τ L {β, -β} ≤
      ((iterHom S.D.step m).comp (MulAut.conj z).toMonoidHom).eqLocus
        ((MulAut.conj z).toMonoidHom.comp (frobGL σ)) := by
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rcases hγ with rfl | hγ
    · exact hrelU c
    · rw [Set.mem_singleton_iff.1 hγ]
      exact hrelV c
  intro g hg
  exact hle hg

theorem norm_mem_bigComponentSet_of_rankOneOrbit_two (S : LangSetup τ L p)
    (hτ : SimplyLacedTag τ) {β : Fin τ.rank → ℤ} (hm : RankOneOrbit S.ρ β 3)
    (h3 : (S.ρ : (Fin τ.rank → ℤ) → _)^[3] β = β) (hq : S.D.q = 2) (hp : p = 7)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) :
    ∀ γ ∈ ({β, -β} : Set (Fin τ.rank → ℤ)), ∃ c₀ c₁ c₂ : L, c₀ ≠ 0 ∧ c₁ ≠ 0 ∧ c₂ ≠ 0 ∧
      pinnedX τ L γ c₀ * pinnedX τ L (S.ρ γ) c₁ * pinnedX τ L (S.ρ (S.ρ γ)) c₂ ∈
        bigComponentSet S D₁ := by
  classical
  have hm' := hm
  obtain ⟨hβ, hm0, hρm, -⟩ := hm'
  have hτ2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hlen : ∀ α, IsRoot τ α → iform α α = iform β β := fun α hα => by
    rw [iform_self_eq_two_of_simplyLaced hτ hα, iform_self_eq_two_of_simplyLaced hτ hβ]
  have hQ : S.D.q ^ 3 = 8 := by rw [hq]; norm_num
  have hQ4 : 4 ≤ S.D.q ^ 3 := by rw [hQ]; norm_num
  have hpm : p ∣ (S.D.q ^ 3) ^ 2 - 1 := by rw [hQ, hp]; norm_num
  obtain ⟨σ, z, l0, l1, hσ, hzT, hl0, hl1, hzU, hzV, hz⟩ :=
    exists_untwist_pair_torus_two S hq hβ (m := 3) (by norm_num) h3
  obtain ⟨hfinK, hKcard⟩ := exists_fixSubfield_fintype S (by norm_num : 0 < 3) hσ
  have := hfinK
  letI _inst : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have hKcard' : Fintype.card (fixSubfield σ) = S.D.q ^ 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hes : 0 < e * 3 := Nat.mul_pos he (by norm_num)
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * 3)) := fun c => by rw [hσ, hq', ← pow_mul]
  have hQ4' : 4 ≤ r ^ (e * 3) := by rw [pow_mul, ← hq']; exact hQ4
  obtain ⟨t0, ht0⟩ := exists_unit_sq_ne_one (L := L) σ hσ' hes hQ4'
  set χ := pairChar β with hχ
  have hker : kernelRoots χ = {β, -β} := kernelRoots_pairChar hβ hlen
  have hβk : β ∈ kernelRoots χ := by rw [hker]; exact Or.inl rfl
  set i : KernelComponent χ := ⟦⟨β, hβk⟩⟧ with hi
  have hcomp : componentRoots χ i = {β, -β} := componentRoots_pairChar hβ hlen hβk
  have hperf : Group.IsPerfect (componentRootSpan (fixSubfield σ) χ i) :=
    isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ) (χ := χ) ht0 i
  set Cg := componentRootSpan (fixSubfield σ) χ i with hCg
  have hCgspan : Cg = rootSpan τ (fixSubfield σ) {β, -β} := by rw [← hcomp]; rfl
  set P := pairFamily S hm with hP
  set ι := baseChangeGL (τ := τ) (fixSubfield σ).subtype with hι
  have hP0 : P.S 0 = rootSpan τ L {β, -β} := pairFamily_zero S hm
  have hιS : ∀ x ∈ Cg, ι x ∈ rootSpan τ L {β, -β} := fun x hx =>
    map_baseChangeGL_rootSpan_le (fixSubfield σ).subtype {β, -β}
      ⟨x, by rwa [hCgspan] at hx, rfl⟩
  have hιC : ∀ x ∈ Cg, ι x ∈ CQ σ i := by
    intro x hx
    rw [CQ_eq_map]
    exact ⟨x, hx, rfl⟩
  have hzn : ∀ g, g ∈ rootSpan τ L {β, -β} ↔ z * g * z⁻¹ ∈ rootSpan τ L {β, -β} := by
    have hT : torusGroup τ L ≤ Subgroup.normalizer (rootSpan τ L {β, -β} : Set (ModGL τ L)) :=
      CFSG.Quasithin.SmithCurtis.Chev.torusGroup_le_normalizer_rootSpan _ (by
        rintro γ (rfl | hγ)
        · exact hβ
        · rw [Set.mem_singleton_iff.1 hγ]; exact IsRoot.neg hβ)
    exact Subgroup.mem_normalizer_iff.1 (hT hzT)
  let θ₀ : Cg →* P.S 0 :=
    ((MulAut.conj z).toMonoidHom.comp (ι.comp Cg.subtype)).codRestrict (P.S 0) fun x => by
      rw [hP0]
      exact (hzn _).1 (hιS x.1 x.2)
  have hθ₀ : ∀ x : Cg, ((θ₀ x : P.S 0) : ModGL τ L) = z * ι x.1 * z⁻¹ := fun x => rfl
  let f : Cg →* ModGL τ L := P.norm.comp θ₀
  have hfix : ∀ x : Cg, iterHom S.D.step 3 ((θ₀ x : P.S 0) : ModGL τ L) = (θ₀ x : P.S 0) := by
    intro x
    rw [hθ₀, hz _ (hιS x.1 x.2), frobGL_eq_self_of_mem_CQ' σ i (hιC x.1 x.2)]
  have hfA : ∀ x : Cg, f x ∈ P.Afix := fun x => P.norm_mem_Afix (hfix x)
  have hAad : P.A ≤ adjointGroup τ L := by
    refine iSup_le fun k => ?_
    rw [pairFamily_S]
    refine iSup₂_le fun γ _ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_adjointGroup _ _
  have hM : ∀ x : Cg, f x ∈ S.D.model := fun x => ⟨hAad (hfA x).1, (hfA x).2⟩
  have hΓ : ∀ x : Cg, f x ∈ S.Γ := map_mem_commutator_of_perfect hperf f _ hM
  have hkey : ∀ γ ∈ ({β, -β} : Set (Fin τ.rank → ℤ)), ∀ t : fixSubfield σ,
      normElt S 3 (z * pinnedX τ L γ ((fixSubfield σ).subtype t) * z⁻¹) ∈ f.range := by
    intro γ hγ t
    have hx : pinnedX τ (fixSubfield σ) γ t ∈ Cg := by
      rw [hCgspan]
      exact pinnedX_mem_rootSpan hγ t
    refine ⟨⟨_, hx⟩, ?_⟩
    have hθ : ((θ₀ ⟨_, hx⟩ : P.S 0) : ModGL τ L) =
        z * pinnedX τ L γ ((fixSubfield σ).subtype t) * z⁻¹ := by
      rw [hθ₀, hι, baseChangeGL_pinnedX]
    show P.norm (θ₀ ⟨_, hx⟩) = _
    rw [norm_eq_list_prod, hθ]
    rfl
  have hdvd : p ∣ Nat.card (SL(2, fixSubfield σ)) := by
    rw [card_SL2_field, hKcard]
    exact Dvd.dvd.mul_left hpm _
  haveI : Fact p.Prime := ⟨S.hp⟩
  obtain ⟨B, hB⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hrk : ∀ B' : SL(2, fixSubfield σ), rootSL2 τ (fixSubfield σ) β B' ∈ Cg := by
    intro B'
    rw [hCgspan, ← rootRankOneGroup_eq_rootSpan_pair hβ]
    exact ⟨B', rfl⟩
  have hpow : (f ⟨_, hrk B⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨rootSL2 τ (fixSubfield σ) β B, hrk B⟩ : Cg) ^ p = 1 := by
      apply Subtype.ext
      show (rootSL2 τ (fixSubfield σ) β B) ^ p = 1
      rw [← map_pow, ← hB, pow_orderOf_eq_one, map_one]
    rw [this, map_one]
  have hord : orderOf (f ⟨_, hrk B⟩) = p := by
    refine orderOf_eq_prime hpow ?_
    intro h1
    have hZ := P.mem_Z_of_norm_eq_one (y := θ₀ ⟨_, hrk B⟩) h1
    have hBc : B ∈ Subgroup.center (SL(2, fixSubfield σ)) := by
      rw [Subgroup.mem_center_iff]
      intro B'
      have h2 := P.mem_Z.1 hZ ((θ₀ ⟨_, hrk B'⟩ : P.S 0) : ModGL τ L)
        (P.S_le_A 0 (θ₀ ⟨_, hrk B'⟩).2)
      rw [hθ₀, hθ₀] at h2
      have h3' : ι (rootSL2 τ (fixSubfield σ) β B') * ι (rootSL2 τ (fixSubfield σ) β B) =
          ι (rootSL2 τ (fixSubfield σ) β B) * ι (rootSL2 τ (fixSubfield σ) β B') := by
        have h4 : z * (ι (rootSL2 τ (fixSubfield σ) β B') * ι (rootSL2 τ (fixSubfield σ) β B)) *
            z⁻¹ = z * (ι (rootSL2 τ (fixSubfield σ) β B) *
              ι (rootSL2 τ (fixSubfield σ) β B')) * z⁻¹ := by
          calc _ = z * ι (rootSL2 τ (fixSubfield σ) β B') * z⁻¹ *
                (z * ι (rootSL2 τ (fixSubfield σ) β B) * z⁻¹) := by group
            _ = z * ι (rootSL2 τ (fixSubfield σ) β B) * z⁻¹ *
                (z * ι (rootSL2 τ (fixSubfield σ) β B') * z⁻¹) := h2
            _ = _ := by group
        exact mul_left_cancel (mul_right_cancel h4)
      have h5 : rootSL2 τ (fixSubfield σ) β (B' * B) = rootSL2 τ (fixSubfield σ) β (B * B') := by
        apply baseChangeGL_injective (fixSubfield σ).subtype
        simpa only [map_mul] using h3'
      exact rootSL2_injective_of_field β h5
    obtain ⟨r0, hr0, hr0B⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hBc
    have hBB : B ^ 2 = 1 := by
      apply Subtype.ext
      rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, ← hr0B, Matrix.SpecialLinearGroup.coe_one,
        ← map_mul, ← map_one (Matrix.scalar (Fin 2))]
      congr 1
      simpa [pow_two] using hr0
    have hp2 : p ∣ 2 := hB ▸ orderOf_dvd_of_pow_eq_one hBB
    have := Nat.le_of_dvd (by norm_num) hp2
    have := S.hp.two_le
    omega
  have hYΓ : f.range ≤ S.Γ := by
    rintro _ ⟨x, rfl⟩
    exact hΓ x
  have hYspan : f.range ≤ rootSpan τ L (rhoOrbitPM S.ρ β) := by
    rintro _ ⟨x, rfl⟩
    exact pairFamily_A_le S hm (hfA x).1
  have hbig : (f.range : Set (ModGL τ L)) ⊆ bigComponentSet S D₁ :=
    subset_bigComponentSet_of_perfect S hD₁E hD₁c hβ hYΓ (commutator_range_eq_of_perfect hperf f)
      hYspan ⟨⟨_, hrk B⟩, rfl⟩ hord
  intro γ hγ
  have hγr : IsRoot τ γ := by
    rcases hγ with h | h
    · rw [h]; exact hβ
    · rw [Set.mem_singleton_iff.1 h]; exact IsRoot.neg hβ
  have hmem := hkey γ hγ 1
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : L, lam ≠ 0 ∧
      z * pinnedX τ L γ (((fixSubfield σ).subtype) 1) * z⁻¹ = pinnedX τ L γ lam := by
    rcases hγ with h | h
    · rw [h]
      exact ⟨l0, hl0, by simpa using hzU 1⟩
    · rw [Set.mem_singleton_iff.1 h]
      exact ⟨l1, hl1, by simpa using hzV 1⟩
  rw [hlam] at hmem
  have hfac : ∀ κ : ZMod 3, ∃ c : L, c ≠ 0 ∧
      iterHom S.D.step κ.val (pinnedX τ L γ lam) =
        pinnedX τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[κ.val] γ) c := fun κ => by
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S κ.val hγr
    exact ⟨μ * lam ^ (S.D.q ^ κ.val), mul_ne_zero hμ0 (pow_ne_zero _ hlam0), by
      rw [iterHom_eq_iterate, hμ]⟩
  choose cc hcc0 hcc using hfac
  set f' : ZMod 3 → ModGL τ L := fun κ =>
    pinnedX τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[κ.val] γ) (cc κ) with hf'
  have hnorm : normElt S 3 (pinnedX τ L γ lam) =
      ((Finset.univ : Finset (ZMod 3)).toList.map f').prod := by
    unfold normElt
    exact congrArg List.prod (List.map_congr_left fun κ _ => hcc κ)
  have hperm : (Finset.univ : Finset (ZMod 3)).toList.Perm [0, 1, 2] := by
    rw [List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (by decide)]
    intro a
    simp only [Finset.mem_toList, Finset.mem_univ, true_iff]
    revert a
    decide
  have hS' : ∀ κ : ZMod 3, f' κ ∈ P.S κ := by
    intro κ
    rw [pairFamily_S]
    refine pinnedX_mem_rootSpan ?_ (cc κ)
    rcases hγ with h | h
    · rw [h]
      exact Or.inl rfl
    · rw [Set.mem_singleton_iff.1 h, rho_iterate_neg S κ.val β]
      exact Or.inr rfl
  have hpw : ((Finset.univ : Finset (ZMod 3)).toList.map f').Pairwise Commute := by
    rw [List.pairwise_map]
    exact (Finset.nodup_toList _).imp fun {a b} hne => P.comm a b hne _ (hS' a) _ (hS' b)
  rw [hnorm, (hperm.map f').prod_eq' hpw] at hmem
  refine ⟨cc 0, cc 1, cc 2, hcc0 0, hcc0 1, hcc0 2, ?_⟩
  have h0 : (S.ρ : (Fin τ.rank → ℤ) → _)^[(0 : ZMod 3).val] γ = γ := rfl
  have h1' : (S.ρ : (Fin τ.rank → ℤ) → _)^[(1 : ZMod 3).val] γ = S.ρ γ := rfl
  have h2' : (S.ρ : (Fin τ.rank → ℤ) → _)^[(2 : ZMod 3).val] γ = S.ρ (S.ρ γ) := rfl
  have e : ([0, 1, 2].map f').prod = pinnedX τ L γ (cc 0) * pinnedX τ L (S.ρ γ) (cc 1) *
      pinnedX τ L (S.ρ (S.ρ γ)) (cc 2) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hf', h0, h1',
      h2', mul_assoc]
  rw [e] at hmem
  exact hbig hmem

end RankOneTwo

end CFSG.HardMathSupport.Timmesfeld.LangTorus
