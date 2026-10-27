module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodCheck

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice
open scoped commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false


section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem isGoodRoot_of_rankOneOrbit_odd (hτ : SimplyLacedTag τ) {β : Fin τ.rank → ℤ} {m : ℕ}
    (hm : RankOneOrbit S.ρ β m) (hq3 : 3 ≤ S.D.q) (hp3 : 3 ≤ p)
    (hpm : p ∣ S.D.q ^ (2 * m) - 1) : IsGoodRoot S β := by
  classical
  have hm' := hm
  obtain ⟨hβ, hm0, hρm, -⟩ := hm'
  haveI : NeZero m := ⟨hm0.ne'⟩
  have hτ2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hlen : ∀ α, IsRoot τ α → iform α α = iform β β := fun α hα => by
    rw [iform_self_eq_two_of_simplyLaced hτ hα, iform_self_eq_two_of_simplyLaced hτ hβ]
  have hQ3 : 3 ≤ S.D.q ^ m := hq3.trans (Nat.le_self_pow hm0.ne' _)
  have hQ4 : 4 ≤ S.D.q ^ m := by
    by_contra hlt
    have hQeq : S.D.q ^ m = 3 := Nat.le_antisymm (Nat.lt_succ_iff.1 (not_le.1 hlt)) hQ3
    rw [pow_mul', hQeq] at hpm
    have h8 : p ≤ 8 := Nat.le_of_dvd (by norm_num) hpm
    have hpp := S.hp
    interval_cases p <;> first | omega | exact absurd hpp (by norm_num)
  have hpmQ : p ∣ (S.D.q ^ m) ^ 2 - 1 := by rwa [pow_mul'] at hpm
  obtain ⟨σ, z, hσ, hzZ, hz⟩ := exists_untwist_pair S hβ hlen hm0 hρm
  obtain ⟨hfinK, hKcard⟩ := exists_fixSubfield_fintype S hm0 hσ
  have := hfinK
  letI _inst : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have hKcard' : Fintype.card (fixSubfield σ) = S.D.q ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hes : 0 < e * m := Nat.mul_pos he hm0
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * m)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ4' : 4 ≤ r ^ (e * m) := by rw [pow_mul, ← hq]; exact hQ4
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
    have hzN : z ∈ Subgroup.normalizer (rootSpan τ L {β, -β} : Set (ModGL τ L)) :=
      (sup_le hT (Subgroup.le_normalizer) : _ ≤ _) hzZ
    exact Subgroup.mem_normalizer_iff.1 hzN
  let θ₀ : Cg →* P.S 0 :=
    ((MulAut.conj z).toMonoidHom.comp (ι.comp Cg.subtype)).codRestrict (P.S 0) fun x => by
      rw [hP0]
      exact (hzn _).1 (hιS x.1 x.2)
  have hθ₀ : ∀ x : Cg, ((θ₀ x : P.S 0) : ModGL τ L) = z * ι x.1 * z⁻¹ := fun x => rfl
  let f : Cg →* ModGL τ L := P.norm.comp θ₀
  have hfix : ∀ x : Cg, iterHom S.D.step m ((θ₀ x : P.S 0) : ModGL τ L) = (θ₀ x : P.S 0) := by
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
  have hroot : ∀ γ ∈ ({β, -β} : Set (Fin τ.rank → ℤ)), IsRoot τ γ := by
    rintro γ (rfl | hγ)
    · exact hβ
    · rw [Set.mem_singleton_iff.1 hγ]; exact IsRoot.neg hβ
  have hkey : ∀ γ ∈ ({β, -β} : Set (Fin τ.rank → ℤ)), ∀ t : fixSubfield σ,
      normElt S m (z * pinnedX τ L γ ((fixSubfield σ).subtype t) * z⁻¹) ∈ f.range := by
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
  have hcomm : ∀ z' : ModGL τ L, (∀ y ∈ f.range, Commute z' y) →
      ∀ x ∈ rootRankOneGroup τ L β, Commute z' x := by
    intro z' hc x hx
    have hγ : ∀ γ ∈ ({β, -β} : Set (Fin τ.rank → ℤ)), ∀ c : L,
        Commute z' (z * pinnedX τ L γ c * z⁻¹) := fun γ hγ c =>
      commute_conj_pinnedX_of_norm S hτ2 z (hroot γ hγ) (fixSubfield σ).subtype hKcard' hq3 hQ4
        (fun t => hc _ (hkey γ hγ t)) c
    rw [rootRankOneGroup_eq_rootSpan_pair hβ] at hx
    have hmap : (rootSpan τ L {β, -β}).map (MulAut.conj z).toMonoidHom ≤
        Subgroup.centralizer {z'} := by
      simp only [rootSpan, Subgroup.map_iSup]
      refine iSup₂_le fun γ hγ' => ?_
      rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hγ γ hγ' c).symm.eq
    have hg' : z⁻¹ * x * z ∈ rootSpan τ L {β, -β} := by
      refine (hzn _).2 ?_
      have : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
      rw [this]
      exact hx
    have hcalc : (MulAut.conj z).toMonoidHom (z⁻¹ * x * z) = x := by
      show z * (z⁻¹ * x * z) * z⁻¹ = x
      group
    have hmem : x ∈ Subgroup.centralizer {z'} := hmap (Subgroup.mem_map.2 ⟨_, hg', hcalc⟩)
    exact Commute.symm (Subgroup.mem_centralizer_singleton_iff.1 hmem)
  have hfield : ∀ (r' f' j : ℕ) [ExpChar L r'], r'.Prime → S.D.q = r' ^ f' → 0 < j → j < f' →
      ∀ z' : ModGL τ L, ¬ ∀ y ∈ f.range,
        z' * Units.map (entrywiseHom (iterateFrobenius L r' j)) y * z'⁻¹ = y := by
    intro r' f' j _ hr' hq' hj0 hjf z' hfixY
    exact false_of_fixed_by_twist_of_norm S hτ2 z hβ (fixSubfield σ).subtype hKcard' hr' hq'
      (Or.inr hτ) hj0 hjf z' (fun t => hfixY _ (hkey β (Or.inl rfl) t))
  have hdvd : p ∣ Nat.card (SL(2, fixSubfield σ)) := by
    rw [card_SL2_field, hKcard]
    exact Dvd.dvd.mul_left hpmQ _
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
      have h3 : ι (rootSL2 τ (fixSubfield σ) β B') * ι (rootSL2 τ (fixSubfield σ) β B) =
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
        simpa only [map_mul] using h3
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
    omega
  refine ⟨hβ, f.range, ?_, commutator_range_eq_of_perfect hperf f, ?_, ⟨_, ⟨_, rfl⟩, hord⟩,
    hcomm, hfield⟩
  · rintro _ ⟨x, rfl⟩
    exact hΓ x
  · rintro _ ⟨x, rfl⟩
    exact pairFamily_A_le S hm (hfA x).1

theorem isGoodRoot_of_goodM_odd (hτ : SimplyLacedTag τ) {C M : List (List ℤ)}
    (hC : toMat τ.rank C = τ.cartan)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = toMat τ.rank M *ᵥ γ)
    (hR : ∀ r ∈ τ.artifactRoots, r.length = τ.rank) (hq3 : 3 ≤ S.D.q) (hp3 : 3 ≤ p) {e : ℕ}
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) {b : List ℤ} {m : ℕ}
    (h : goodM τ.rank C M τ.artifactRoots b e = some m) : IsGoodRoot S (toVec τ.rank b) := by
  obtain ⟨hchk, hdvd⟩ := goodM_spec h
  exact isGoodRoot_of_rankOneOrbit_odd S hτ (rankOneOrbit_of_check S hτ hC hρ hR hchk) hq3 hp3
    (dvd_pow_sub_one_of_orderOf S.hp (by omega) he hdvd)

theorem goodRootsGenerate_of_classCheck_odd (hτ : SimplyLacedTag τ) {C M : List (List ℤ)}
    (hC : toMat τ.rank C = τ.cartan)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = toMat τ.rank M *ᵥ γ) (hq3 : 3 ≤ S.D.q) (hp3 : 3 ≤ p)
    {e : ℕ} (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) {cert : List (ℕ × ℕ × ℕ)}
    (h : classCheck τ.rank C M τ.artifactRoots e cert = true) : GoodRootsGenerate S := by
  unfold classCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hR, h⟩ := h
  split at h
  · rename_i kn' hkn'
    intro γ hγ
    have hγR : List.ofFn γ ∈ τ.artifactRoots := (isRoot_iff_mem_artifactRoots).1 hγ
    obtain ⟨i, hi, hiγ⟩ := List.getElem_of_mem hγR
    have hmem := List.all_eq_true.1 h i (List.mem_range.2 hi)
    have hbase : ∀ i ∈ (List.range τ.artifactRoots.length).filter (fun i =>
        (goodM τ.rank C M τ.artifactRoots (τ.artifactRoots.getD i []) e).isSome),
        i < τ.artifactRoots.length ∧
          ReflClosure τ {β | IsGoodRoot S β} (toVec τ.rank (τ.artifactRoots.getD i [])) := by
      intro i hi
      rw [List.mem_filter, List.mem_range] at hi
      obtain ⟨hiR, hi⟩ := hi
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (by simpa using hi)
      exact ⟨hiR, ReflClosure.base (isGoodRoot_of_goodM_odd S hτ hC hρ hR hq3 hp3 he hm)⟩
    obtain ⟨-, hcl⟩ := certStep_sound hτ hC hR _ _ _ hbase hkn' i (List.contains_iff_mem.1 hmem)
    have : toVec τ.rank (τ.artifactRoots.getD i []) = γ := by
      rw [List.getD_eq_getElem _ _ hi, hiγ]
      exact toVec_vofFn γ
    rwa [this] at hcl
  · exact absurd h (by simp)

end Main

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
