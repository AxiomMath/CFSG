module

public import CFSG.LieType.SeitzGeneration.HyperCoverLinear
public import CFSG.LieType.SeitzGeneration.UnitaryHyperDiag
public import CFSG.LieType.Steinberg.CentralExt.UnitaryTwoMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.SectionRank.OddCover Matrix

section CoprimeLift

variable {K S : Type*} [Group K] [Group S]

theorem commute_of_map_commute_of_coprime {ρ : K →* S} (hker : ρ.ker ≤ Subgroup.center K)
    {p : ℕ} (hcop : Nat.Coprime (Nat.card ρ.ker) p) {f k : K} (hf : f ^ p = 1)
    (hfk : ρ f * ρ k = ρ k * ρ f) : f * k = k * f := by
  set c := k * f * k⁻¹ * f⁻¹ with hc
  have hck : c ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, ← hfk]
    group
  have hcf : Commute c f := ((Subgroup.mem_center_iff.1 (hker hck)) f).symm
  have hconj : k * f * k⁻¹ = c * f := by rw [hc]; group
  have hcp : c ^ p = 1 := by
    have h1 : (k * f * k⁻¹) ^ p = 1 := by rw [conj_pow, hf, mul_one, mul_inv_cancel]
    rwa [hconj, hcf.mul_pow, hf, mul_one] at h1
  have hord : orderOf c ∣ Nat.card ρ.ker := by
    have := orderOf_dvd_natCard (⟨c, hck⟩ : ρ.ker)
    rwa [Subgroup.orderOf_mk] at this
  have h1 := Nat.dvd_gcd hord (orderOf_dvd_of_pow_eq_one hcp)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  calc f * k = c⁻¹ * (k * f) := by rw [hc]; group
    _ = k * f := by rw [h1, inv_one, one_mul]

theorem hyperGen_of_map_of_coprime [Group.IsPerfect K] {p : ℕ} (ρ : K →* S)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center K)
    (hcop : Nat.Coprime (Nat.card ρ.ker) p) {E : Subgroup K} (hexp : ∀ x ∈ E, x ^ p = 1)
    (h : HyperGen p (⊤ : Subgroup S) (E.map ρ)) : HyperGen p (⊤ : Subgroup K) E := by
  have hinj : ∀ x ∈ E, ρ x = 1 → x = 1 := by
    intro x hx h1
    have hord : orderOf x ∣ Nat.card ρ.ker := by
      have h2 := orderOf_dvd_natCard (⟨x, MonoidHom.mem_ker.2 h1⟩ : ρ.ker)
      have h3 : orderOf (⟨x, MonoidHom.mem_ker.2 h1⟩ : ρ.ker) = orderOf x :=
        Subgroup.orderOf_mk x _
      rwa [h3] at h2
    have h2 := Nat.dvd_gcd hord (orderOf_dvd_of_pow_eq_one (hexp x hx))
    rwa [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h2
  set X : Set K := {k : K | k ∈ (⊤ : Subgroup K) ∧ ∃ F : Subgroup K, F ≤ E ∧ F.relIndex E = p ∧
    ∀ f ∈ F, f * k = k * f} with hX
  have hmem : ∀ k : K, ρ k ∈ {s : S | s ∈ (⊤ : Subgroup S) ∧ ∃ F : Subgroup S, F ≤ E.map ρ ∧
      F.relIndex (E.map ρ) = p ∧ ∀ f ∈ F, f * s = s * f} → k ∈ X := by
    rintro k ⟨-, F, hFE, hFi, hFc⟩
    refine ⟨Subgroup.mem_top k, E ⊓ F.comap ρ, inf_le_left, ?_, fun f hf => ?_⟩
    · have hmap : (E ⊓ F.comap ρ).map ρ = F := by
        refine le_antisymm ?_ fun y hy => ?_
        · rintro _ ⟨x, hx, rfl⟩
          exact hx.2
        · obtain ⟨x, hx, rfl⟩ := hFE hy
          exact ⟨x, ⟨hx, hy⟩, rfl⟩
      rw [← relIndex_map_of_injOn ρ inf_le_left hinj, hmap, hFi]
    · exact commute_of_map_commute_of_coprime hker hcop (hexp f hf.1) (hFc (ρ f) hf.2)
  have htop : (Subgroup.closure X).map ρ = ⊤ := by
    refine top_unique (h.trans ?_)
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    obtain ⟨k, rfl⟩ := hρ s
    exact ⟨k, Subgroup.subset_closure (hmem k hs), rfl⟩
  intro k _
  rw [eq_top_of_map_eq_top_of_perfect ρ hker htop]
  exact Subgroup.mem_top k

end CoprimeLift

section Section

open CFSG.LieType.Steinberg.CentralExt


theorem exists_su_cover_hom {F : Type} [Field F] [Finite F] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP F ℓ]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ} (hn : 4 ≤ n) {K : Type} [Group K]
    [Finite K] [Group.IsPerfect K] (ρ : K →* StatedProj (StatedSU n (ℓ ^ f) F))
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center K)
    (hcop : Even n → ℓ.Coprime (Nat.card ρ.ker)) :
    ∃ φ : StatedSU n (ℓ ^ f) F →* K, Function.Surjective φ ∧
      ∀ g, ρ (φ g) =
        QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (ℓ ^ f) F)) g := by
  set π := QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (ℓ ^ f) F))
  let P : Subgroup (K × StatedSU n (ℓ ^ f) F) :=
    MonoidHom.eqLocus (ρ.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _))
  let pr : P →* StatedSU n (ℓ ^ f) F := (MonoidHom.snd _ _).comp P.subtype
  have hpr : Function.Surjective pr := fun g => by
    obtain ⟨k, hk⟩ := hρ (π g)
    exact ⟨⟨(k, g), hk⟩, rfl⟩
  have hprk : pr.ker ≤ Subgroup.center P := by
    intro x hx
    have hx2 : (x : K × StatedSU n (ℓ ^ f) F).2 = 1 := hx
    have hxP : ρ (x : K × StatedSU n (ℓ ^ f) F).1 = π (x : K × StatedSU n (ℓ ^ f) F).2 := x.2
    have hx1 : (x : K × StatedSU n (ℓ ^ f) F).1 ∈ Subgroup.center K := by
      refine hker ?_
      rw [MonoidHom.mem_ker, hxP, hx2, map_one]
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.1 hx1 _
    · show (y : K × StatedSU n (ℓ ^ f) F).2 * (x : K × _).2 =
        (x : K × StatedSU n (ℓ ^ f) F).2 * (y : K × _).2
      rw [hx2, mul_one, one_mul]
  obtain ⟨σ, hσ⟩ : ∃ s : StatedSU n (ℓ ^ f) F →* P, ∀ g, pr (s g) = g := by
    by_cases he : Even n
    · refine SUClosed.statedSU_exists_section_of_coprime hF he (by omega) P pr hpr hprk ?_
      let ι : pr.ker →* ρ.ker :=
        { toFun := fun x => ⟨((x : P) : K × StatedSU n (ℓ ^ f) F).1, by
            have hx2 : ((x : P) : K × StatedSU n (ℓ ^ f) F).2 = 1 := x.2
            have hxP : ρ ((x : P) : K × StatedSU n (ℓ ^ f) F).1 =
                π ((x : P) : K × StatedSU n (ℓ ^ f) F).2 := (x : P).2
            rw [MonoidHom.mem_ker, hxP, hx2, map_one]⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hι : Function.Injective ι := by
        intro x y hxy
        have h1 : ((x : P) : K × StatedSU n (ℓ ^ f) F).1 = ((y : P) : K × StatedSU n (ℓ ^ f) F).1 :=
          congrArg Subtype.val hxy
        have hx2 : ((x : P) : K × StatedSU n (ℓ ^ f) F).2 = 1 := x.2
        have hy2 : ((y : P) : K × StatedSU n (ℓ ^ f) F).2 = 1 := y.2
        exact Subtype.ext (Subtype.ext (Prod.ext h1 (hx2.trans hy2.symm)))
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective ι hι) (hcop he)
    · exact SUOdd.statedSU_odd_exists_section_of_central hF hf (by omega) he
        (fun h => by
          have := congrArg Prod.fst h
          simp only at this
          omega) hpr hprk
  let φ : StatedSU n (ℓ ^ f) F →* K := (MonoidHom.fst _ _).comp (P.subtype.comp σ)
  have hφρ : ∀ g, ρ (φ g) = π g := by
    intro g
    have h1 : ρ ((σ g : K × StatedSU n (ℓ ^ f) F).1) = π ((σ g : K × StatedSU n (ℓ ^ f) F).2) :=
      (σ g).2
    have h2 : (σ g : K × StatedSU n (ℓ ^ f) F).2 = g := hσ g
    rw [h2] at h1
    exact h1
  refine ⟨φ, ?_, hφρ⟩
  have htop : φ.range = ⊤ := eq_top_of_map_eq_top_of_perfect ρ hker (by
    rw [← MonoidHom.range_comp, eq_top_iff]
    rintro x -
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (ℓ ^ f) F)) x
    exact ⟨g, hφρ g⟩)
  exact MonoidHom.range_eq_top.1 htop

end Section

section Cube

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem eq_one_of_mem_scalars_four (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : unitarySU ℓ f K 4}
    (hx : x ∈ (StatedScalars (Fin 4) K).subgroupOf (unitarySU ℓ f K 4)) (hxp : x ^ p = 1) :
    x = 1 := by
  have hZ : Nat.card ((StatedScalars (Fin 4) K).subgroupOf (unitarySU ℓ f K 4)) =
      Nat.gcd 4 (ℓ ^ f + 1) := by
    rw [← unitaryScalars_eq h (by norm_num), card_unitaryScalars h (by norm_num)]
  have hord : orderOf x ∣ 4 := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : (StatedScalars (Fin 4) K).subgroupOf
      (unitarySU ℓ f K 4))
    rw [Subgroup.orderOf_mk, hZ] at this
    exact this.trans (Nat.gcd_dvd_left _ _)
  have h4p : Nat.Coprime 4 p := by
    have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    simpa using Nat.Coprime.pow_left 2 h2p
  have h1 := Nat.dvd_gcd hord (orderOf_dvd_of_pow_eq_one hxp)
  rwa [h4p.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1

theorem exists_hyperGen_su (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 4 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2 ∨ 6 ≤ n) :
    ∃ A : Subgroup (unitarySU ℓ f K n), IsElemAbelian p A ∧ Nat.card A = p ^ 3 ∧
      (∀ x ∈ A, x ∈ (StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n) → x = 1) ∧
      HyperGen p (⊤ : Subgroup (unitarySU ℓ f K n)) A := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hfin := h.finite
  obtain ⟨ζ, hζr, hζ, hζu⟩ := exists_zeta_unitary h hp hpq
  have htoral : ∀ (m : ℕ), ℓ ^ f ≠ 2 →
      ∀ χ : Multiplicative (Fin 3 → ZMod p) →* unitarySU ℓ f K (m + 1), Function.Injective χ →
      (∀ u, χ u ∈ (StatedScalars (Fin (m + 1)) K).subgroupOf (unitarySU ℓ f K (m + 1)) →
        χ u = 1) →
      ∃ A : Subgroup (unitarySU ℓ f K (m + 1)), IsElemAbelian p A ∧ Nat.card A = p ^ 3 ∧
        (∀ x ∈ A, x ∈ (StatedScalars (Fin (m + 1)) K).subgroupOf (unitarySU ℓ f K (m + 1)) →
          x = 1) ∧ HyperGen p (⊤ : Subgroup (unitarySU ℓ f K (m + 1))) A := by
    intro m hq2 χ hχ hsc
    have hAel := isElemAbelian_range (p := p) χ
    have hAcard : Nat.card χ.range = p ^ 3 := by
      rw [card_range_of_injective hχ, card_multiplicative_zmod]
    have hcomm : ∀ x ∈ χ.range, ∀ y ∈ χ.range, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have htop := hyperClosure_eq_top_unitarySU_toral h hp hpq hq2 χ.range hcomm hAel.2 hAcard
    refine ⟨χ.range, hAel, hAcard, ?_, ?_⟩
    · rintro _ ⟨u, rfl⟩ hu
      exact hsc u hu
    · exact hyperGen_iff_le.2 (le_of_eq htop.symm)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases hq2 : ℓ ^ f = 2
  ·
    have hn6 : 6 ≤ m + 1 := hq.resolve_left (not_not.mpr hq2)
    have hℓ2 : ℓ = 2 := ((Nat.Prime.pow_eq_iff Nat.prime_two).mp hq2).1
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by
      rw [hq2] at hpq
      exact hpq)
    subst hp3
    have : Fact ℓ.Prime := ⟨h.prime⟩
    have := h.charP
    set σ := CFSG.LieType.BorelTits.unitaryInvolution K ℓ f with hσdef
    have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
    have hn5 : 5 ≤ m + 1 := by omega
    set χ := diagSU h hn5 ζ hζ hζu with hχdef
    have hinjP := diagSU_proj_injective h hn5 ζ hζ hζr hζu
    have hχinj : Function.Injective χ := fun a b hab => hinjP (by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hab])
    have hAel := isElemAbelian_range (p := 3) χ
    have hAcard : Nat.card χ.range = 3 ^ 3 := by
      rw [card_range_of_injective hχinj, card_multiplicative_zmod]
    refine ⟨χ.range, hAel, hAcard, ?_, ?_⟩
    · rintro _ ⟨u, rfl⟩ hu
      have h1 : (projSU' (ℓ := ℓ) (f := f) (K := K) (m + 1)).comp χ u = 1 := by
        rw [MonoidHom.comp_apply]
        exact (QuotientGroup.eq_one_iff _).2 hu
      rw [hinjP (h1.trans (map_one _).symm), map_one]
    · let e := MulEquiv.subgroupCongr (suid_unitaryInvolution_eq h (m + 1))
      set w : Fin (m + 1) → K := Pi.single ⟨3, by omega⟩ 1 + Pi.single ⟨5, by omega⟩ 1 with hw
      have hw0 : w ≠ 0 := by
        intro h0
        have := congrFun h0 ⟨3, by omega⟩
        simp [hw] at this
      have hww : herm σ w w = 0 := by
        subst hℓ2
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        simp only [hw, herm_add_left, herm_add_right, herm_single_left, map_one, one_mul,
          Pi.single_apply]
        simp only [Fin.mk.injEq, ite_true, ite_false, show (3 : ℕ) ≠ 5 by norm_num,
          show (5 : ℕ) ≠ 3 by norm_num, add_zero, zero_add]
        rw [← two_mul, h2, zero_mul]
      have hpK : ((3 : ℕ) : K) ≠ 0 := by
        subst hℓ2
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        have : ((3 : ℕ) : K) = 1 := by
          have : ((3 : ℕ) : K) = 2 + 1 := by push_cast; ring
          rw [this, h2, zero_add]
        rw [this]
        exact one_ne_zero
      refine hyperGen_top_of_isotropic_unitary hσ (by omega) (fun h3 => absurd h3 (by omega))
        e.toMonoidHom e.surjective ?_ Nat.prime_three (by norm_num) hpK hAel hAcard
        (W := K ∙ w) ?_ ?_ ?_
      · intro g hg
        have hg1 : g = 1 := e.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hg)
        exact ⟨1, by rw [hg1, one_smul]; rfl⟩
      · exact fun hW => hw0 (Submodule.span_singleton_eq_bot.mp hW)
      · intro x hx y hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [herm_smul_left, herm_smul_right, hww, mul_zero, mul_zero]
      · intro g hg x hx
        obtain ⟨u, hu⟩ := hg
        have hgmat : ((g : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
            ((torusWit ζ hζ (diagVec (m + 1)) u : GL (Fin (m + 1)) K) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
          have := congrArg (fun y : unitarySU ℓ f K (m + 1) =>
            ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) hu
          exact this.symm
        have hfix : g • w = w := by
          rw [smul_def σ, hgmat, hw]
          exact torusWit_diagVec_mulVec hn6 ζ hζ u
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [smul_comm, hfix]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  · by_cases h5 : 5 ≤ m + 1
    ·
      have hinjP := diagSU_proj_injective h h5 ζ hζ hζr hζu
      refine htoral m hq2 (diagSU h h5 ζ hζ hζu) (fun a b hab => hinjP (by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hab])) fun u hu => ?_
      have h1 : (projSU' (ℓ := ℓ) (f := f) (K := K) (m + 1)).comp (diagSU h h5 ζ hζ hζu) u =
          1 := by
        rw [MonoidHom.comp_apply]
        exact (QuotientGroup.eq_one_iff _).2 hu
      rw [hinjP (h1.trans (map_one _).symm), map_one]
    ·
      have hm : m = 3 := by omega
      subst hm
      let χ : Multiplicative (Fin 3 → ZMod p) →* unitarySU ℓ f K (3 + 1) :=
        (torusWit ζ hζ (sumZeroHom' 3)).codRestrict _ fun u =>
          torusWit_mem_SU (pow_ne_zero _ h.prime.ne_zero) hζ hζu (sumZeroHom' 3)
            (fun u => sum_sumZeroVec' u) u
      have hinjT := torusWit_injective (K := K) hζ hζr (sumZeroHom' 3) fun u hu =>
        funext fun j => by
          have := hu (Fin.castSucc j)
          simpa [sumZeroHom', sumZeroVec'] using this
      refine htoral 3 hq2 χ (fun a b hab => hinjT (congrArg Subtype.val hab)) fun u hu => ?_
      have hup : χ u ^ p = 1 := by rw [← map_pow, multiplicative_zmod_pow_eq_one, map_one]
      exact eq_one_of_mem_scalars_four h hp hp2 hu hup

end Cube

theorem exists_hyperGen_cover_unitary
    {r : ℕ} (hr : 3 ≤ r) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q.card + 1) (hq : q.card ≠ 2 ∨ 5 ≤ r) {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* Cat ⟨.twistedA r q, hv⟩) :
    ∃ E : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ HyperGen p ⊤ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ with hfdef
  have hf : 1 ≤ f := TauCeti.ValidLieTypeIndex.fieldExponent_pos _
  have hℓp : ℓ.Prime := by
    rw [hℓ]
    exact Fact.out
  have : Fact ℓ.Prime := ⟨hℓp⟩
  set F := GaloisField ℓ (2 * f)
  have hU : UnitaryFieldData ℓ f F :=
    CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f hf
  have := hU.finite
  have := hU.charP
  have hqc : ℓ ^ f = q.card := card_twistedA r q hv
  have hpl : p ≠ ℓ := by
    intro hpl
    have h1 : p ∣ q.card := by
      rw [← hqc, hpl]
      exact dvd_pow_self ℓ (by omega)
    have h2 : p ∣ q.card + 1 - q.card := Nat.dvd_sub hpq h1
    rw [show q.card + 1 - q.card = 1 by omega] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  let eU := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv
  let ρ₀ : K →* StatedProj (StatedSU (r + 1) (ℓ ^ f) F) :=
    (eU.toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ₀s : Function.Surjective ρ₀ :=
    (eU.surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective _)
  have hρ₀k : ∀ k : K, ρ₀ k = 1 ↔ k ∈ Subgroup.center K := by
    intro k
    change eU (e (QuotientGroup.mk' (Subgroup.center K) k)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  obtain ⟨S⟩ : Nonempty (Sylow ℓ (Subgroup.center K)) := inferInstance
  set N : Subgroup K := (S : Subgroup (Subgroup.center K)).map (Subgroup.center K).subtype
    with hNdef
  have hNc : N ≤ Subgroup.center K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hNn : N.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hNc hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  have : Finite (K ⧸ N) := Finite.of_surjective _ (QuotientGroup.mk'_surjective N)
  have hNk : N ≤ ρ₀.ker := fun x hx => (hρ₀k x).2 (hNc hx)
  let ρ : K ⧸ N →* StatedProj (StatedSU (r + 1) (ℓ ^ f) F) := QuotientGroup.lift N ρ₀ hNk
  have hρs : Function.Surjective ρ := QuotientGroup.lift_surjective_of_surjective N ρ₀ hρ₀s hNk
  have hρmk : ∀ k : K, ρ (k : K ⧸ N) = ρ₀ k := fun k => QuotientGroup.lift_mk N hNk k
  have hρk : ρ.ker = (Subgroup.center K).map (QuotientGroup.mk' N) := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [MonoidHom.mem_ker, hρmk, hρ₀k]
      constructor
      · intro hk
        exact ⟨k, hk, rfl⟩
      · rintro ⟨k', hk', hkk'⟩
        have h1 : k'⁻¹ * k ∈ N := QuotientGroup.eq.1 hkk'
        have := Subgroup.mul_mem _ hk' (hNc h1)
        simpa using this
  have hρc : ρ.ker ≤ Subgroup.center (K ⧸ N) := by
    rw [hρk]
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        Subgroup.mem_center_iff.1 hk y]
  have hcop : ℓ.Coprime (Nat.card ρ.ker) := by
    let g : Subgroup.center K →* K ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.center K).subtype
    have hgr : g.range = (Subgroup.center K).map (QuotientGroup.mk' N) := by
      show ((QuotientGroup.mk' N).comp (Subgroup.center K).subtype).range = _
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hgk : g.ker = (S : Subgroup (Subgroup.center K)) := by
      ext x
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' N (x : K) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)
    rw [hρk, ← hgr, ← Subgroup.index_ker, hgk]
    exact (Nat.Prime.coprime_iff_not_dvd hℓp).2 (Sylow.not_dvd_index S)
  obtain ⟨φ, hφs, hφρ⟩ := exists_su_cover_hom hU.card_eq_sq hf (by omega : 4 ≤ r + 1) ρ hρs hρc
    fun _ => hcop
  obtain ⟨A, hAa, hAc, hAsc, hAgen⟩ := exists_hyperGen_su hU (n := r + 1) (by omega) hp hp2
    (by rw [hqc]; exact hpq) (by
      rcases hq with hq | hq
      · exact Or.inl (by rw [hqc]; exact hq)
      · exact Or.inr (by omega))
  have hinj : ∀ x ∈ A, φ x = 1 → x = 1 := by
    intro x hx h1
    refine hAsc x hx ?_
    have h2 := hφρ x
    rw [h1, map_one, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  have hĒa : IsElemAbelian p (A.map φ) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hAa φ
  have hĒc : Nat.card (A.map φ) = p ^ 3 := by
    have hφA : Function.Injective (φ.comp A.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      exact Subtype.ext (hinj x x.2 hx)
    have hrange : (φ.comp A.subtype).range = A.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← hAc]
    exact (Nat.card_congr (MonoidHom.ofInjective hφA).toEquiv).symm
  have hĒgen := hyperGen_map_of_surjective φ hφs hinj hAgen
  have hcopN : Nat.Coprime (Nat.card (QuotientGroup.mk' N).ker) p := by
    rw [QuotientGroup.ker_mk', hNdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes hℓp hp).2 (Ne.symm hpl))
  obtain ⟨E₁, hE₁a, hE₁c, hE₁map⟩ := exists_lift_isElemAbelian hp (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hcopN hĒa hĒc
  refine ⟨E₁, hE₁a, hE₁c, hyperGen_of_map_of_coprime (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hNc) hcopN
    (fun x hx => hE₁a.2 x hx) ?_⟩
  rw [hE₁map]
  exact hĒgen

end CFSG.LieType.SeitzGeneration
