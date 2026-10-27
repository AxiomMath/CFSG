module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRoot
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodUntwist
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

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


section Orbit

variable {τ : Tag}

@[expose] def RankOneOrbit (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (β : Fin τ.rank → ℤ) (m : ℕ) : Prop :=
  IsRoot τ β ∧ 0 < m ∧
    ((ρ : (Fin τ.rank → ℤ) → _)^[m] β = β ∨ (ρ : (Fin τ.rank → ℤ) → _)^[m] β = -β) ∧
    ∀ j k, j < k → k < m →
      iform ((ρ : (Fin τ.rank → ℤ) → _)^[j] β) ((ρ : (Fin τ.rank → ℤ) → _)^[k] β) = 0 ∧
      ¬ IsRoot τ ((ρ : (Fin τ.rank → ℤ) → _)^[j] β + (ρ : (Fin τ.rank → ℤ) → _)^[k] β) ∧
      ¬ IsRoot τ ((ρ : (Fin τ.rank → ℤ) → _)^[j] β - (ρ : (Fin τ.rank → ℤ) → _)^[k] β)

@[expose] def pairSet (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (β : Fin τ.rank → ℤ) (j : ℕ) :
    Set (Fin τ.rank → ℤ) :=
  {(ρ : (Fin τ.rank → ℤ) → _)^[j] β, -((ρ : (Fin τ.rank → ℤ) → _)^[j] β)}

end Orbit

section Family

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {β : Fin τ.rank → ℤ} {m : ℕ}

theorem pairSet_add_period
    (h : (S.ρ : (Fin τ.rank → ℤ) → _)^[m] β = β ∨ (S.ρ : (Fin τ.rank → ℤ) → _)^[m] β = -β)
    (j : ℕ) : pairSet S.ρ β (j + m) = pairSet S.ρ β j := by
  unfold pairSet
  rw [Function.iterate_add_apply]
  rcases h with h | h
  · rw [h]
  · rw [h, rho_iterate_neg S, neg_neg, Set.pair_comm]

theorem pairSet_mod
    (h : (S.ρ : (Fin τ.rank → ℤ) → _)^[m] β = β ∨ (S.ρ : (Fin τ.rank → ℤ) → _)^[m] β = -β)
    (j : ℕ) : pairSet S.ρ β j = pairSet S.ρ β (j % m) := by
  have key : ∀ q r : ℕ, pairSet S.ρ β (r + m * q) = pairSet S.ρ β r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [Nat.mul_succ, ← add_assoc, pairSet_add_period S h, ih]
  conv_lhs => rw [← Nat.mod_add_div j m]
  exact key _ _

theorem pairSet_isRoot (hβ : IsRoot τ β) (j : ℕ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ pairSet S.ρ β j) :
    IsRoot τ γ := by
  have h := S.iterate_isRoot j hβ
  rcases hγ with rfl | hγ
  · exact h
  · rw [Set.mem_singleton_iff.1 hγ]
    exact IsRoot.neg h

theorem map_pairSet (j : ℕ) :
    (S.ρ : (Fin τ.rank → ℤ) → _) '' pairSet S.ρ β j = pairSet S.ρ β (j + 1) := by
  unfold pairSet
  rw [Set.image_pair, ← Function.iterate_succ_apply' (S.ρ : (Fin τ.rank → ℤ) → _) j β, S.frob.neg_eq,
    ← Function.iterate_succ_apply' (S.ρ : (Fin τ.rank → ℤ) → _) j β]

theorem commute_rootSpan_pairSets (hm : RankOneOrbit S.ρ β m) {j k : ℕ} (hjk : j < k) (hk : k < m) :
    ∀ x ∈ rootSpan τ L (pairSet S.ρ β j), ∀ y ∈ rootSpan τ L (pairSet S.ρ β k), x * y = y * x := by
  obtain ⟨hβ, -, -, horth⟩ := hm
  obtain ⟨h0, hp, hm'⟩ := horth j k hjk hk
  have hj := S.iterate_isRoot j hβ
  have hk' := S.iterate_isRoot k hβ
  intro x hx y hy
  have h := exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ L hj hk' h0 hp hm'
  rw [rootRankOneGroup_eq_rootSpan_pair hj] at h
  rw [rootRankOneGroup_eq_rootSpan_pair hk'] at h
  exact h x hx y hy

@[expose] noncomputable def pairFamily [NeZero m] (hm : RankOneOrbit S.ρ β m) :
    CycFamily S.D.step m where
  S k := rootSpan τ L (pairSet S.ρ β k.val)
  map_eq k := by
    rw [map_rootSpan_step S _ (fun γ hγ => pairSet_isRoot S hm.1 _ hγ), map_pairSet, val_add_one_eq,
      ← pairSet_mod S hm.2.2.1]
  comm j k hjk x hx y hy := by
    have hne : j.val ≠ k.val := fun h => hjk (ZMod.val_injective m h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact commute_rootSpan_pairSets S hm h (ZMod.val_lt k) x hx y hy
    · exact (commute_rootSpan_pairSets S hm h (ZMod.val_lt j) y hy x hx).symm

theorem pairFamily_S [NeZero m] (hm : RankOneOrbit S.ρ β m) (k : ZMod m) :
    (pairFamily S hm).S k = rootSpan τ L (pairSet S.ρ β k.val) := rfl

theorem pairFamily_zero [NeZero m] (hm : RankOneOrbit S.ρ β m) :
    (pairFamily S hm).S 0 = rootSpan τ L {β, -β} := by
  rw [pairFamily_S, ZMod.val_zero]
  rfl

theorem pairFamily_A_le [NeZero m] (hm : RankOneOrbit S.ρ β m) :
    (pairFamily S hm).A ≤ rootSpan τ L (rhoOrbitPM S.ρ β) := by
  refine iSup_le fun k => rootSpan_mono ?_
  rintro γ (rfl | rfl)
  · exact ⟨k.val, Or.inl rfl⟩
  · exact ⟨k.val, Or.inr (rho_iterate_neg S k.val β).symm⟩

end Family

section Field

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem exists_fixSubfield_fintype {m : ℕ} (hm : 0 < m) {σ : L ≃+* L}
    (hσ : ∀ c, σ c = c ^ (S.D.q ^ m)) :
    Finite (fixSubfield σ) ∧ Nat.card (fixSubfield σ) = S.D.q ^ m := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hes : 0 < e * m := Nat.mul_pos he hm
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * m)) := fun c => by rw [hσ, hq, ← pow_mul]
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * m) hes
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ (e * m)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  have hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σ) = r ^ (e * m) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]
  exact ⟨hfinK, by rw [hKcard, hq, ← pow_mul]⟩

theorem map_baseChangeGL_rootSpan_le {K : Type} [Field K] (ι : K →+* L)
    (T : Set (Fin τ.rank → ℤ)) :
    (rootSpan τ K T).map (baseChangeGL ι) ≤ rootSpan τ L T := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun γ hγ => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  show baseChangeGL ι (pinnedX τ K γ c) ∈ rootSpan τ L T
  rw [baseChangeGL_pinnedX]
  exact pinnedX_mem_rootSpan hγ _

theorem iform_self_eq_two_of_simplyLaced (hτ : SimplyLacedTag τ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  rcases hτ with rfl | rfl | rfl | rfl <;> simpa [Tag.symmetrizer] using hj

theorem card_SL2_field (K : Type) [Field K] [Finite K] :
    Nat.card (SL(2, K)) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [LinearFlag.card_SL_eq (by norm_num)]
  simp

theorem commutator_range_eq_of_perfect {C G : Type*} [Group C] [Group G] (hC : Group.IsPerfect C)
    (f : C →* G) : ⁅f.range, f.range⁆ = f.range := by
  calc ⁅f.range, f.range⁆ = ⁅(⊤ : Subgroup C).map f, (⊤ : Subgroup C).map f⁆ := by
        rw [MonoidHom.range_eq_map]
    _ = (⁅(⊤ : Subgroup C), (⊤ : Subgroup C)⁆).map f := (Subgroup.map_commutator _ _ _).symm
    _ = (⊤ : Subgroup C).map f := by
        rw [← commutator_def, Group.isPerfect_def.1 hC]
    _ = f.range := (MonoidHom.range_eq_map f).symm

end Field

section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem frobGL_eq_self_of_mem_CQ' {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (σ : L ≃+* L) (i : KernelComponent χ)
    {x : ModGL τ L} (hx : x ∈ CQ σ i) : frobGL σ x = x := by
  have : CQ σ i ≤ (frobGL σ).eqLocus (MonoidHom.id _) := by
    unfold CQ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, hc, rfl⟩
    show frobGL σ (pinnedX τ L γ c) = pinnedX τ L γ c
    rw [frobGL_pinnedX, hc]
  exact this hx

theorem isGoodRoot_of_rankOneOrbit (hτ : SimplyLacedTag τ) {β : Fin τ.rank → ℤ} {m : ℕ}
    (hm : RankOneOrbit S.ρ β m) (hq3 : 3 ≤ S.D.q) (hp7 : 7 ≤ p)
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

end Main

end CFSG.HardMathSupport.Timmesfeld.LangTorus
