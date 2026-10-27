module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE8EightSL2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Base

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


section Pair

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem exists_bigComponent_pair (hτ : SimplyLacedTag τ) {β : Fin τ.rank → ℤ} {m : ℕ}
    (hm : RankOneOrbit S.ρ β m) (hQ4 : 4 ≤ S.D.q ^ m) (hp7 : 7 ≤ p)
    (hpm : p ∣ S.D.q ^ (2 * m) - 1) (hL2 : (2 : L) = 0)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) :
    ∃ θ R : ModGL τ L, θ * R ∈ bigComponentSet S D₁ ∧ θ ∈ rootRankOneGroup τ L β ∧ θ ≠ 1 ∧
      θ * θ = 1 ∧ ∀ x ∈ rootRankOneGroup τ L β, Commute R x := by
  classical
  have hm' := hm
  obtain ⟨hβ, hm0, hρm, -⟩ := hm'
  haveI : NeZero m := ⟨hm0.ne'⟩
  have hτ2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hlen : ∀ α, IsRoot τ α → iform α α = iform β β := fun α hα => by
    rw [iform_self_eq_two_of_simplyLaced hτ hα, iform_self_eq_two_of_simplyLaced hτ hβ]
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
  have hYΓ : f.range ≤ S.Γ := by
    rintro _ ⟨x, rfl⟩
    exact hΓ x
  have hYspan : f.range ≤ rootSpan τ L (rhoOrbitPM S.ρ β) := by
    rintro _ ⟨x, rfl⟩
    exact pairFamily_A_le S hm (hfA x).1
  have hbig : (f.range : Set (ModGL τ L)) ⊆ bigComponentSet S D₁ :=
    subset_bigComponentSet_of_perfect S hD₁E hD₁c hβ hYΓ (commutator_range_eq_of_perfect hperf f)
      hYspan ⟨⟨_, hrk B⟩, rfl⟩ hord
  have hx₁ : pinnedX τ (fixSubfield σ) β 1 ∈ Cg := by
    rw [hCgspan]
    exact pinnedX_mem_rootSpan (Set.mem_insert _ _) 1
  set θ' : P.S 0 := θ₀ ⟨_, hx₁⟩ with hθ'
  have hsub1 : ((fixSubfield σ).subtype 1 : L) = 1 := map_one _
  have hθ'e : ((θ' : P.S 0) : ModGL τ L) = z * pinnedX τ L β 1 * z⁻¹ := by
    rw [hθ', hθ₀, hι, baseChangeGL_pinnedX, hsub1]
  have hnorm := norm_eq_list_prod P θ'
  set l := (Finset.univ : Finset (ZMod m)).toList with hl
  set g : ZMod m → ModGL τ L := fun κ => iterHom S.D.step κ.val ((θ' : P.S 0) : ModGL τ L)
    with hg
  have hgS : ∀ κ : ZMod m, g κ ∈ P.S κ := fun κ => by
    have := P.iterHom_mem κ.val θ'.2
    rwa [ZMod.natCast_zmod_val] at this
  have hpw : (l.map g).Pairwise Commute := by
    rw [List.pairwise_map]
    exact (Finset.nodup_toList _).imp fun {a b} hne => P.comm a b hne _ (hgS a) _ (hgS b)
  have hmem0 : (0 : ZMod m) ∈ l := Finset.mem_toList.2 (Finset.mem_univ _)
  have hperm : l.Perm (0 :: l.erase 0) := List.perm_cons_erase hmem0
  have hsplit : (l.map g).prod = g 0 * ((l.erase 0).map g).prod := by
    have := (hperm.map g).prod_eq' hpw
    simpa using this
  have hg0 : g 0 = ((θ' : P.S 0) : ModGL τ L) := by simp [hg]
  set R := ((l.erase 0).map g).prod with hR
  have hRc : ∀ x ∈ P.S 0, Commute x R := by
    intro x hx
    refine Commute.list_prod_right _ _ ?_
    intro y hy
    obtain ⟨κ, hκ, rfl⟩ := List.mem_map.1 hy
    have hκ0 : κ ≠ 0 := ((Finset.nodup_toList _).mem_erase_iff.1 hκ).1
    exact P.comm 0 κ (Ne.symm hκ0) x hx _ (hgS κ)
  have hP0' : rootRankOneGroup τ L β = P.S 0 := by
    rw [hP0]
    exact rootRankOneGroup_eq_rootSpan_pair hβ
  have hXX : pinnedX τ L β (1 : L) * pinnedX τ L β 1 = 1 := by
    rw [← pinnedX_add, one_add_one_eq_two, hL2, pinnedX_zero]
  refine ⟨((θ' : P.S 0) : ModGL τ L), R, ?_, ?_, ?_, ?_, ?_⟩
  · have hfy : ((P.norm θ' : ModGL τ L)) = ((θ' : P.S 0) : ModGL τ L) * R := by
      rw [hnorm, hsplit, hg0]
    exact hbig ⟨⟨_, hx₁⟩, by rw [← hfy]; rfl⟩
  · rw [hP0']
    exact θ'.2
  · intro h1
    rw [hθ'e] at h1
    have hX1 : pinnedX τ L β (1 : L) = 1 := by
      calc pinnedX τ L β (1 : L) = z⁻¹ * (z * pinnedX τ L β 1 * z⁻¹) * z := by group
        _ = 1 := by rw [h1]; group
    exact one_ne_zero (pinnedX_injective τ L β (hX1.trans (pinnedX_zero τ L β).symm))
  · rw [hθ'e]
    calc z * pinnedX τ L β (1 : L) * z⁻¹ * (z * pinnedX τ L β 1 * z⁻¹) =
        z * (pinnedX τ L β (1 : L) * pinnedX τ L β 1) * z⁻¹ := by group
      _ = 1 := by rw [hXX]; group
  · intro x hx
    rw [hP0'] at hx
    exact (hRc x hx).symm

end Pair

section Torus

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem rootChar_eq_one_of_commute_pair {a : Fin τ.rank → Lˣ} {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (haT : rootDiagUnit τ a ∈ torusGroup τ L) {θ R : ModGL τ L}
    (hθ : θ ∈ rootRankOneGroup τ L β) (hθ1 : θ ≠ 1) (hθθ : θ * θ = 1)
    (hR : ∀ x ∈ rootRankOneGroup τ L β, Commute R x)
    (hcomm : Commute (rootDiagUnit τ a) (θ * R)) : rootChar a β = 1 := by
  set z' := rootDiagUnit τ a with hz'
  have hT : torusGroup τ L ≤ Subgroup.normalizer (rootSpan τ L {β, -β} : Set (ModGL τ L)) :=
    CFSG.Quasithin.SmithCurtis.Chev.torusGroup_le_normalizer_rootSpan _ (by
      rintro γ (rfl | hγ)
      · exact hβ
      · rw [Set.mem_singleton_iff.1 hγ]; exact IsRoot.neg hβ)
  have hQ : rootRankOneGroup τ L β = rootSpan τ L {β, -β} :=
    rootRankOneGroup_eq_rootSpan_pair hβ
  have hnorm : ∀ g, g ∈ rootRankOneGroup τ L β ↔ z' * g * z'⁻¹ ∈ rootRankOneGroup τ L β := by
    intro g
    rw [hQ]
    exact Subgroup.mem_normalizer_iff.1 (hT haT) g
  have hnorm' : ∀ g, g ∈ rootRankOneGroup τ L β ↔
      z'⁻¹ * g * z'⁻¹⁻¹ ∈ rootRankOneGroup τ L β := by
    intro g
    rw [hQ]
    exact Subgroup.mem_normalizer_iff.1 (inv_mem (hT haT)) g
  have hB'Q : z' * θ * z'⁻¹ ∈ rootRankOneGroup τ L β := (hnorm θ).1 hθ
  have hR'c : ∀ x ∈ rootRankOneGroup τ L β, Commute (z' * R * z'⁻¹) x := by
    intro x hx
    have hx' : z'⁻¹ * x * z'⁻¹⁻¹ ∈ rootRankOneGroup τ L β := (hnorm' x).1 hx
    have h := (hR _ hx').eq
    show z' * R * z'⁻¹ * x = x * (z' * R * z'⁻¹)
    calc z' * R * z'⁻¹ * x = z' * (R * (z'⁻¹ * x * z'⁻¹⁻¹)) * z'⁻¹ := by group
      _ = z' * ((z'⁻¹ * x * z'⁻¹⁻¹) * R) * z'⁻¹ := by rw [h]
      _ = x * (z' * R * z'⁻¹) := by group
  have hBR : (z' * θ * z'⁻¹) * (z' * R * z'⁻¹) = θ * R := by
    have h := hcomm.eq
    calc (z' * θ * z'⁻¹) * (z' * R * z'⁻¹) = z' * (θ * R) * z'⁻¹ := by group
      _ = θ * R := by rw [h]; group
  have hxQ : θ⁻¹ * (z' * θ * z'⁻¹) ∈ rootRankOneGroup τ L β := mul_mem (inv_mem hθ) hB'Q
  have hxe : θ⁻¹ * (z' * θ * z'⁻¹) = R * (z' * R * z'⁻¹)⁻¹ := by
    calc θ⁻¹ * (z' * θ * z'⁻¹) =
          θ⁻¹ * ((z' * θ * z'⁻¹) * (z' * R * z'⁻¹)) * (z' * R * z'⁻¹)⁻¹ := by group
      _ = θ⁻¹ * (θ * R) * (z' * R * z'⁻¹)⁻¹ := by rw [hBR]
      _ = R * (z' * R * z'⁻¹)⁻¹ := by group
  have hxc : ∀ y ∈ rootRankOneGroup τ L β, Commute (θ⁻¹ * (z' * θ * z'⁻¹)) y := by
    intro y hy
    rw [hxe]
    exact (hR y hy).mul_left (hR'c y hy).inv_left
  have hx1 : θ⁻¹ * (z' * θ * z'⁻¹) = 1 := by
    obtain ⟨X, hX⟩ := hxQ
    have hcent : ∀ Z : SL(2, L), X * Z = Z * X := by
      intro Z
      apply rootSL2_injective_of_field β
      rw [map_mul, map_mul, hX]
      exact (hxc _ ⟨Z, rfl⟩).eq
    have hX1 : X = 1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5.sl2_eq_one_of_central_charTwo hcent
    rw [← hX, hX1, map_one]
  have hfixθ : z' * θ * z'⁻¹ = θ := (inv_mul_eq_one.1 hx1).symm
  obtain ⟨C, hC⟩ := hθ
  have hconj := rootDiagUnit_conj_rootSL2 a hβ C
  have hfix : CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne (rootChar a β)) C = C := by
    apply rootSL2_injective_of_field β
    rw [← hconj, hC]
    exact hfixθ
  have hC1 : C ≠ 1 := by
    rintro rfl
    apply hθ1
    rw [← hC, map_one]
  have hCC : C * C = 1 := by
    apply rootSL2_injective_of_field β
    rw [map_mul, hC, hθθ, map_one]
  exact SmallQ17.eq_one_of_conjSL_diagUnitOne_fixed (rootChar a β) C hC1 hCC hfix

end Torus

end CFSG.HardMathSupport.Timmesfeld.LangTorus

end
