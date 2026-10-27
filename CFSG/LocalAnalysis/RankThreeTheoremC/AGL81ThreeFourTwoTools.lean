module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

universe u

section Generic

variable {G : Type*} [Group G]

theorem exists_iterate_commutator_le_of_isSubnormal {J H N : Subgroup G}
    (hJ : IsSubnormal J H) (hN : N ≤ H) :
    ∃ d : ℕ, (fun X : Subgroup G => ⁅X, J⁆)^[d] N ≤ J := by
  suffices h : ∀ {L U : Subgroup G}, IsSubnormal L U → N ≤ U → ∀ A : Subgroup G, A ≤ L →
      ∃ d : ℕ, (fun X : Subgroup G => ⁅X, A⁆)^[d] N ≤ L from h hJ hN J le_rfl
  intro L U hLU
  induction hLU with
  | refl U => exact fun hN _ _ => ⟨0, hN⟩
  | @step L M U hLM hn _ ih =>
    intro hN A hA
    obtain ⟨d, hd⟩ := ih hN A (hA.trans hLM)
    refine ⟨d + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
    rw [commutatorElement_def]
    exact L.mul_mem ((normal_subgroupOf_iff hLM).mp hn a x (hA ha) (hd hx)) (L.inv_mem (hA ha))

private theorem commutator_eq_bot_of_iterate_eq_bot {J N : Subgroup G} (hJ : ⁅J, J⁆ = J) :
    ∀ d : ℕ, (fun X : Subgroup G => ⁅X, J⁆)^[d + 1] N = ⊥ → ⁅N, J⁆ = ⊥
  | 0, h => by simpa using h
  | d + 1, h => by
    refine commutator_eq_bot_of_iterate_eq_bot hJ d ?_
    rw [Function.iterate_succ_apply'] at h ⊢
    rw [Function.iterate_succ_apply'] at h
    set X := (fun X : Subgroup G => ⁅X, J⁆)^[d] N
    have h1 : ⁅⁅J, X⁆, J⁆ = ⊥ := by rwa [Subgroup.commutator_comm J X]
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := J) (H₂ := J) (H₃ := X) h1 h
    rwa [hJ, Subgroup.commutator_comm] at h3

theorem le_centralizer_of_isSubnormal_of_perfect {J H N : Subgroup G} (hJ : IsSubnormal J H)
    (hJp : ⁅J, J⁆ = J) (hNH : N ≤ H) (hHN : H ≤ normalizer (N : Set G))
    (hc : ⁅J ⊓ N, J⁆ = ⊥) : J ≤ centralizer (N : Set G) := by
  obtain ⟨d, hd⟩ := exists_iterate_commutator_le_of_isSubnormal hJ hNH
  have hJN : J ≤ normalizer (N : Set G) := hJ.le.trans hHN
  have hiter : ∀ k : ℕ, (fun X : Subgroup G => ⁅X, J⁆)^[k] N ≤ N := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine Subgroup.commutator_le.mpr fun x hx j hj => ?_
      have hx' : x ∈ N := ih hx
      have h1 : j * x⁻¹ * j⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hJN hj) x⁻¹).mp (N.inv_mem hx')
      simpa only [commutatorElement_def, mul_assoc] using N.mul_mem hx' h1
  have hbot : (fun X : Subgroup G => ⁅X, J⁆)^[d + 1] N = ⊥ := by
    rw [Function.iterate_succ_apply']
    exact le_bot_iff.mp ((Subgroup.commutator_mono_left (le_inf hd (hiter d))).trans hc.le)
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact commutator_eq_bot_of_iterate_eq_bot hJp d hbot

private theorem eq_bot_of_perfect_of_le_of_isSolvable {J S : Subgroup G} (hJS : J ≤ S)
    (hS : Group.IsSolvable S) (hJ : ⁅J, J⁆ = J) : J = ⊥ := by
  haveI : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJS)
  haveI : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJ
  by_contra hne
  haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hne
  exact Group.IsPerfect.not_isSolvable J inferInstance

private theorem eq_bot_of_perfect_of_isPGroup {q : ℕ} [Fact q.Prime] {J : Subgroup G} [Finite J]
    (hJq : IsPGroup q J) (hJ : ⁅J, J⁆ = J) : J = ⊥ := by
  haveI : Group.IsNilpotent J := hJq.isNilpotent
  exact eq_bot_of_perfect_of_le_of_isSolvable le_rfl
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective le_rfl)) hJ

theorem commutator_inf_eq_bot_of_quasisimple_quotient [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {J N : Subgroup G} (hJN : J ≤ normalizer (N : Set G))
    (hN : IsPGroup p N) {Q : Type*} [Group Q] (f : J →* Q) (hf : Function.Surjective f)
    (hfk : IsPGroup q f.ker) (hQ : CFSG.Open.IsQuasisimple Q) : ⁅J ⊓ N, J⁆ = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  set M : Subgroup J := N.subgroupOf J
  have hMn : M.Normal := ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hJN g.2) n).mp hn⟩
  have hMp : IsPGroup p M := hN.comap_of_injective J.subtype J.subtype_injective
  have hMc : M.map f ≤ center Q := by
    haveI : (M.map f).Normal := hMn.map f hf
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ (M.map f) with
      h | h
    · exact h
    · exfalso
      haveI : Finite Q := Finite.of_surjective f hf
      have hQp : IsPGroup p Q :=
        ((hMp.map f).to_le (h ▸ le_rfl : (⊤ : Subgroup Q) ≤ M.map f)).of_equiv
          Subgroup.topEquiv
      haveI : Nontrivial Q := CFSG.ComponentClassification.Quasisimple.nontrivial hQ
      haveI : Group.IsPerfect Q := ⟨hQ.1⟩
      haveI : Group.IsNilpotent Q := hQp.isNilpotent
      exact Group.IsPerfect.not_isSolvable Q inferInstance
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx j hj
  have hxM : (⟨x, hx.1⟩ : J) ∈ M := hx.2
  have hcM : ⁅(⟨x, hx.1⟩ : J), ⟨j, hj⟩⁆ ∈ M := by
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc (⟨j, hj⟩ : J)]
    exact M.mul_mem hxM (hMn.conj_mem _ (M.inv_mem hxM) _)
  have hck : ⁅(⟨x, hx.1⟩ : J), ⟨j, hj⟩⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hMc (mem_map_of_mem f hxM)) (f ⟨j, hj⟩)).symm
  have h1 := (IsPGroup.disjoint_of_ne p q hpq M f.ker hMp hfk).le_bot ⟨hcM, hck⟩
  rw [Subgroup.mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

theorem le_centralizer_of_isSubnormal_of_quasisimple_quotient [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {J H N : Subgroup G} (hJ : IsSubnormal J H)
    (hJp : ⁅J, J⁆ = J) {Q : Type*} [Group Q] (f : J →* Q) (hf : Function.Surjective f)
    (hfk : IsPGroup q f.ker) (hQ : CFSG.Open.IsQuasisimple Q) (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set G)) (hN : IsPGroup p N) : J ≤ centralizer (N : Set G) :=
  le_centralizer_of_isSubnormal_of_perfect hJ hJp hNH hHN
    (commutator_inf_eq_bot_of_quasisimple_quotient hp hq hpq (hJ.le.trans hHN) hN f hf hfk hQ)

theorem eq_bot_of_isSubnormal_of_quasisimple_quotient [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {J H N : Subgroup G} (hJ : IsSubnormal J H)
    (hJp : ⁅J, J⁆ = J) {Q : Type*} [Group Q] (f : J →* Q) (hf : Function.Surjective f)
    (hfk : IsPGroup q f.ker) (hQ : CFSG.Open.IsQuasisimple Q) (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set G)) (hN : IsPGroup p N)
    (hCN : Group.IsSolvable (centralizer (N : Set G) ⊓ H : Subgroup G)) : J = ⊥ :=
  eq_bot_of_perfect_of_le_of_isSolvable
    (le_inf (le_centralizer_of_isSubnormal_of_quasisimple_quotient hp hq hpq hJ hJp f hf hfk hQ
      hNH hHN hN) hJ.le) hCN hJp

theorem exists_solvable_centralizer_of_isSolvable {p : ℕ} {H : Subgroup G}
    (hH : Group.IsSolvable H) :
    ∃ N : Subgroup G, N ≤ H ∧ IsPGroup p N ∧ H ≤ normalizer (N : Set G) ∧
      Group.IsSolvable (centralizer (N : Set G) ⊓ H : Subgroup G) :=
  ⟨⊥, bot_le, IsPGroup.of_bot, fun g _ => Subgroup.mem_normalizer_iff.mpr fun x => by
      simp only [Subgroup.mem_bot, conj_eq_one_iff],
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_right)⟩

theorem isSolvable_centralizer_inf_of_le [Finite G] {p : ℕ} (hp : p.Prime) {H N : Subgroup G}
    (hN : IsPGroup p N) (hCN : centralizer (N : Set G) ⊓ H ≤ N) :
    Group.IsSolvable (centralizer (N : Set G) ⊓ H : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent (centralizer (N : Set G) ⊓ H : Subgroup G) := (hN.to_le hCN).isNilpotent
  infer_instance

theorem solvable_centralizer_map_of_injective {G' : Type*} [Group G'] {p : ℕ} {χ : G →* G'}
    (hχ : Function.Injective χ) {H N : Subgroup G} (hNH : N ≤ H) (hN : IsPGroup p N)
    (hHN : H ≤ normalizer (N : Set G))
    (hCN : Group.IsSolvable (centralizer (N : Set G) ⊓ H : Subgroup G)) :
    N.map χ ≤ H.map χ ∧ IsPGroup p (N.map χ) ∧ H.map χ ≤ normalizer (N.map χ : Set G') ∧
      Group.IsSolvable (centralizer (N.map χ : Set G') ⊓ H.map χ : Subgroup G') := by
  refine ⟨Subgroup.map_mono hNH, hN.map χ,
    (Subgroup.map_mono hHN).trans (Subgroup.le_normalizer_map χ), ?_⟩
  have hle : centralizer (N.map χ : Set G') ⊓ H.map χ ≤ (centralizer (N : Set G) ⊓ H).map χ := by
    intro y hy
    obtain ⟨hyC, hyH⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hyH
    refine Subgroup.mem_map.mpr ⟨h, Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_iff.mpr fun n hn => hχ ?_, hh⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hyC (χ n) (Subgroup.mem_map_of_mem χ hn)
  haveI := hCN
  haveI : Group.IsSolvable ((centralizer (N : Set G) ⊓ H).map χ) :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective (centralizer (N : Set G) ⊓ H) χ hχ).toMonoidHom)
      (Subgroup.equivMapOfInjective _ χ hχ).surjective
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end Generic

section Reduction

theorem exists_quasisimple_quotient_range {I G : Type*} [Group I] [Finite I] [Group G]
    {T : Type u} [Group T] {q : ℕ} (hq : q.Prime) (hI : commutator I = ⊤) {ψ : I →* T}
    (hψ : Function.Surjective ψ) (hψk : IsPGroup q ψ.ker) (hT : CFSG.Open.IsQuasisimple T)
    (κ : I →* G) (hκ : κ.range ≠ ⊥) :
    ∃ (Q : Type u) (_ : Group Q) (f : κ.range →* Q), Function.Surjective f ∧
      IsPGroup q f.ker ∧ CFSG.Open.IsQuasisimple Q := by
  haveI : Fact q.Prime := ⟨hq⟩
  set M : Subgroup T := κ.ker.map ψ
  haveI : M.Normal := κ.normal_ker.map ψ hψ
  let f : κ.range →* T ⧸ M :=
    (QuotientGroup.map κ.ker M ψ (Subgroup.le_comap_map ψ κ.ker)).comp
      (QuotientGroup.quotientKerEquivRange κ).symm.toMonoidHom
  have hf : ∀ i : I, f (κ.rangeRestrict i) = ((ψ i : T) : T ⧸ M) := by
    intro i
    have hs : (QuotientGroup.quotientKerEquivRange κ).symm (κ.rangeRestrict i) =
        (i : I ⧸ κ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs, QuotientGroup.map_mk]
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨i, rfl⟩ := hψ t
    exact ⟨κ.rangeRestrict i, hf i⟩
  have hpow : ∀ i : I, ψ i ∈ M → ∃ k : ℕ, κ i ^ q ^ k = 1 := by
    intro i hi
    obtain ⟨n, hn, hψn⟩ := hi
    have hker : n⁻¹ * i ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψn, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hψk ⟨n⁻¹ * i, hker⟩
    refine ⟨k, ?_⟩
    have h1 : (n⁻¹ * i) ^ q ^ k = 1 := by
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val hk
    have h2 := congrArg κ h1
    rwa [map_pow, map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul, map_one] at h2
  have hfk : IsPGroup q f.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨i, rfl⟩ := κ.rangeRestrict_surjective x
    rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff] at hx
    obtain ⟨k, hk⟩ := hpow i hx
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one]
    exact hk
  have hMc : M ≤ center T := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hT M with h | h
    · exact h
    · exfalso
      haveI : Finite κ.range := Finite.of_surjective κ.rangeRestrict κ.rangeRestrict_surjective
      have hrq : IsPGroup q κ.range := by
        intro x
        obtain ⟨i, rfl⟩ := κ.rangeRestrict_surjective x
        obtain ⟨k, hk⟩ := hpow i (h ▸ Subgroup.mem_top _)
        refine ⟨k, Subtype.ext ?_⟩
        simp only [SubgroupClass.coe_pow, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one]
        exact hk
      have hrp : ⁅κ.range, κ.range⁆ = κ.range := by
        rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hI]
      exact hκ (eq_bot_of_perfect_of_isPGroup hrq hrp)
  exact ⟨T ⧸ M, inferInstance, f, hfs, hfk,
    CFSG.ComponentClassification.Quasisimple.central_quotient hT M hMc⟩

private theorem eq_one_of_mem_centralizer_of_mem {Y : Type*} [Group Y] {K : Subgroup Y}
    (hZ : center K = ⊥) {z : Y} (hzC : z ∈ centralizer (K : Set Y)) (hzK : z ∈ K) : z = 1 := by
  have h : (⟨z, hzK⟩ : K) ∈ center K :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC g g.2)
  rw [hZ, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

theorem exists_inner_hom_of_perfect {Y I : Type*} [Group Y] [Group I] {K : Subgroup Y}
    [K.Normal] (hZ : center K = ⊥) (hOut : Group.IsSolvable (Outer K)) (hI : commutator I = ⊤)
    (σ : I →* Y) :
    ∃ κ : I →* Y, κ.range ≤ K ∧ κ.ker = (centralizer (K : Set Y)).comap σ ∧
      ∀ i, (κ i)⁻¹ * σ i ∈ centralizer (K : Set Y) := by
  haveI : Group.IsPerfect I := ⟨hI⟩
  haveI := hOut
  set θ : Y →* MulAut K := MulAut.conjNormal with hθ
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    refine (injective_iff_map_eq_one _).mpr fun a ha => ?_
    have h : a ∈ center K := Subgroup.mem_center_iff.mpr fun g => by
      have h1 := congrArg (fun φ : MulAut K => φ g) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rwa [hZ, Subgroup.mem_bot] at h
  have hinn : ∀ i, (θ.comp σ) i ∈ (MulAut.conj : K →* MulAut K).range := fun i =>
    let ⟨k, hk⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
      (θ.comp σ) i
    ⟨k, hk.symm⟩
  let κ₀ : I →* K :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp ((θ.comp σ).codRestrict _ hinn)
  have hκ₀ : ∀ i, MulAut.conj (κ₀ i) = θ (σ i) := by
    intro i
    rw [← MonoidHom.ofInjective_apply hinj]
    change (((MonoidHom.ofInjective hinj) ((MonoidHom.ofInjective hinj).symm
      ⟨θ (σ i), hinn i⟩) : MulAut K)) = θ (σ i)
    rw [MulEquiv.apply_symm_apply]
  have hC : ∀ i, ((κ₀ i : K) : Y)⁻¹ * σ i ∈ centralizer (K : Set Y) := by
    intro i
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := congrArg (fun φ : MulAut K => ((φ ⟨m, hm⟩ : K) : Y)) (hκ₀ i)
    simp only [MulAut.conj_apply, hθ, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc m * ((κ₀ i : Y)⁻¹ * σ i) = (κ₀ i : Y)⁻¹ * ((κ₀ i : Y) * m * (κ₀ i : Y)⁻¹) * σ i := by
          group
      _ = (κ₀ i : Y)⁻¹ * (σ i * m * (σ i)⁻¹) * σ i := by rw [h1]
      _ = ((κ₀ i : Y)⁻¹ * σ i) * m := by group
  refine ⟨K.subtype.comp κ₀, ?_, ?_, hC⟩
  · rintro _ ⟨i, rfl⟩
    exact (κ₀ i).2
  · ext i
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_comap]
    constructor
    · intro h
      have h1 := hC i
      rwa [h, inv_one, one_mul] at h1
    · intro h
      have h1 : ((κ₀ i : K) : Y) ∈ centralizer (K : Set Y) := by
        have h2 := (centralizer (K : Set Y)).mul_mem h
          ((centralizer (K : Set Y)).inv_mem (hC i))
        simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using h2
      exact eq_one_of_mem_centralizer_of_mem hZ h1 (κ₀ i).2

private theorem range_props_of_inner {Y I : Type*} [Group Y] [Group I] [Finite I]
    {T : Type u} [Group T] {q : ℕ} (hq : q.Prime) {K Y₀ : Subgroup Y} [K.Normal]
    (hZ : center K = ⊥) (hC : centralizer (K : Set Y) ≤ Y₀) {σ : I →* Y}
    (hσs : IsSubnormal σ.range Y₀) (hI : commutator I = ⊤) {ψ : I →* T}
    (hψ : Function.Surjective ψ) (hψk : IsPGroup q ψ.ker) (hT : CFSG.Open.IsQuasisimple T)
    (hσC : ¬ σ.range ≤ centralizer (K : Set Y)) {κ : I →* Y} (hκK : κ.range ≤ K)
    (hκC : ∀ i, (κ i)⁻¹ * σ i ∈ centralizer (K : Set Y)) :
    κ.range ≤ K ⊓ Y₀ ∧ κ.range ≠ ⊥ ∧ ⁅κ.range, κ.range⁆ = κ.range ∧
      IsSubnormal κ.range (K ⊓ Y₀) ∧
      ∃ (Q : Type u) (_ : Group Q) (f : κ.range →* Q), Function.Surjective f ∧
        IsPGroup q f.ker ∧ CFSG.Open.IsQuasisimple Q := by
  set C := centralizer (K : Set Y)
  have hσY : σ.range ≤ Y₀ := hσs.le
  have hκY : κ.range ≤ K ⊓ Y₀ := by
    rintro _ ⟨i, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨hκK (MonoidHom.mem_range.mpr ⟨i, rfl⟩), ?_⟩
    have h1 := Y₀.mul_mem (hσY (MonoidHom.mem_range.mpr ⟨i, rfl⟩)) (hC (C.inv_mem (hκC i)))
    simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using h1
  have hne : κ.range ≠ ⊥ := by
    intro hbot
    refine hσC ?_
    rintro _ ⟨i, rfl⟩
    have h1 : κ i = 1 := by
      have h2 : κ i ∈ κ.range := MonoidHom.mem_range.mpr ⟨i, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at h2
    simpa only [h1, inv_one, one_mul] using hκC i
  have hperf : ⁅κ.range, κ.range⁆ = κ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hI]
  have heq : (σ.range ⊔ C) ⊓ K = κ.range := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx, hxK⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨_, ⟨i, rfl⟩, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      have h1 : (κ i)⁻¹ * (σ i * c) ∈ C := by
        rw [← mul_assoc]
        exact C.mul_mem (hκC i) hc
      have h2 : (κ i)⁻¹ * (σ i * c) ∈ K :=
        K.mul_mem (K.inv_mem (hκK (MonoidHom.mem_range.mpr ⟨i, rfl⟩))) hxK
      exact MonoidHom.mem_range.mpr
        ⟨i, inv_mul_eq_one.mp (eq_one_of_mem_centralizer_of_mem hZ h1 h2)⟩
    · rintro _ ⟨i, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, hκK (MonoidHom.mem_range.mpr ⟨i, rfl⟩)⟩
      have h1 := Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨i, rfl⟩ : σ i ∈ σ.range)
        (C.inv_mem (hκC i))
      simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using h1
  have hsub : IsSubnormal (σ.range ⊔ C) Y₀ := by
    have h := (hσs.map (QuotientGroup.mk' C)).comap (QuotientGroup.mk' C)
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr hC] at h
  have hsub' : IsSubnormal κ.range (K ⊓ Y₀) := by
    have h := hsub.inf K
    rwa [heq, inf_comm Y₀ K] at h
  exact ⟨hκY, hne, hperf, hsub', exists_quasisimple_quotient_range hq hI hψ hψk hT κ hne⟩

theorem exists_perfect_subnormal_of_not_le_centralizer {Y I : Type*} [Group Y] [Group I]
    [Finite I] {T : Type u} [Group T] {q : ℕ} (hq : q.Prime) {K Y₀ : Subgroup Y} [K.Normal]
    (hZ : center K = ⊥) (hOut : Group.IsSolvable (Outer K))
    (hC : centralizer (K : Set Y) ≤ Y₀) {σ : I →* Y} (hσs : IsSubnormal σ.range Y₀)
    (hI : commutator I = ⊤) {ψ : I →* T} (hψ : Function.Surjective ψ) (hψk : IsPGroup q ψ.ker)
    (hT : CFSG.Open.IsQuasisimple T) (hσC : ¬ σ.range ≤ centralizer (K : Set Y)) :
    ∃ κ : I →* Y, κ.ker = (centralizer (K : Set Y)).comap σ ∧ κ.range ≤ K ⊓ Y₀ ∧
      κ.range ≠ ⊥ ∧ ⁅κ.range, κ.range⁆ = κ.range ∧ IsSubnormal κ.range (K ⊓ Y₀) ∧
      ∃ (Q : Type u) (_ : Group Q) (f : κ.range →* Q), Function.Surjective f ∧
        IsPGroup q f.ker ∧ CFSG.Open.IsQuasisimple Q := by
  obtain ⟨κ, hκK, hκker, hκC⟩ := exists_inner_hom_of_perfect hZ hOut hI σ
  exact ⟨κ, hκker, range_props_of_inner hq hZ hC hσs hI hψ hψk hT hσC hκK hκC⟩

private theorem isComponentOf_top_of_isSimpleGroup {Y : Type*} [Group Y] {K : Subgroup Y}
    [K.Normal] (hK : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) : IsComponentOf K ⊤ := by
  haveI := hK
  haveI : Group.IsPerfect K := ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top K hnab⟩
  exact ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
    CFSG.ComponentClassification.Quasisimple.simple_of_perfect K⟩

end Reduction

section Criteria

private theorem center_outer_of_mulEquiv {K X : Type*} [Group K] [Group X] (e : K ≃* X)
    (hZ : center X = ⊥) (hout : Group.IsSolvable (Outer X)) :
    center K = ⊥ ∧ Group.IsSolvable (Outer K) := by
  haveI := hout
  refine ⟨?_, CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm⟩
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e,
    Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hZ
  exact hZ

theorem threeFourTwoAt_of_forall_of_center_eq_bot {p : ℕ} {X : Type*} [Group X]
    (hZ : center X = ⊥) (hout : Group.IsSolvable (Outer X))
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y),
      p.Prime → p ≠ 2 → K.Normal → Nonempty (K ≃* X) →
      pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
      E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
        else GLBCore p 1 E) ≤ Y₀ →
      (R : Subgroup Y) ≤ Y₀ →
      ∀ J : Subgroup Y, J ≤ K ⊓ Y₀ → J ≠ ⊥ → ⁅J, J⁆ = J → IsSubnormal J (K ⊓ Y₀) →
      (∃ (Q : Type) (_ : Group Q) (f : J →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
        CFSG.Open.IsQuasisimple Q) →
      ∃ iK iJ : TauCeti.CFSGIndex, IsThreeFourPair p iK iJ ∧ Nonempty (K ≃* iK.Group) ∧
        ∃ g : J →* iJ.Group, Function.Surjective g) :
    ThreeFourTwoAt p X := by
  intro Y _ _ K Y₀ E R I T _ _ _ σ ψ hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore _ hσs hI hψ
    hψk hT hσC
  haveI := hKn
  obtain ⟨e⟩ := hKX
  obtain ⟨hZK, hOutK⟩ := center_outer_of_mulEquiv e hZ hout
  have hRY : (R : Subgroup Y) ≤ Y₀ := (sylow_le_threeFourCore hp R hER hE hEc).trans hcore
  obtain ⟨κ, hκker, hκY, hne, hperf, hsub, hQ⟩ :=
    exists_perfect_subnormal_of_not_le_centralizer Nat.prime_two hZK hOutK hC hσs hI hψ hψk hT
      hσC
  obtain ⟨iK, iJ, hpair, hK, g, hg⟩ := h Y K Y₀ E R hp hp2 hKn ⟨e⟩ hrk hC hcomp hER hE hEc hcore
    hRY κ.range hκY hne hperf hsub hQ
  refine ⟨iK, iJ, hpair, hK, g.comp κ.rangeRestrict, hg.comp κ.rangeRestrict_surjective, ?_⟩
  intro i hi
  rw [← hκker] at hi
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  have h1 : κ.rangeRestrict i = 1 := Subtype.ext (MonoidHom.mem_ker.mp hi)
  rw [h1, map_one]

theorem threeFourTwoNoneAt_of_forall_of_center_eq_bot {p : ℕ} {X : Type*} [Group X]
    (hZ : center X = ⊥) (hout : Group.IsSolvable (Outer X))
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y),
      p.Prime → p ≠ 2 → K.Normal → Nonempty (K ≃* X) →
      pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
      E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
        else GLBCore p 1 E) ≤ Y₀ →
      (R : Subgroup Y) ≤ Y₀ →
      ∀ J : Subgroup Y, J ≤ K ⊓ Y₀ → J ≠ ⊥ → ⁅J, J⁆ = J → IsSubnormal J (K ⊓ Y₀) →
      (∃ (Q : Type) (_ : Group Q) (f : J →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
        CFSG.Open.IsQuasisimple Q) → False) :
    ThreeFourTwoNoneAt p X := by
  intro Y _ _ K Y₀ E R I T _ _ _ σ ψ hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore _ hσs hI hψ
    hψk hT
  haveI := hKn
  by_contra hσC
  obtain ⟨e⟩ := hKX
  obtain ⟨hZK, hOutK⟩ := center_outer_of_mulEquiv e hZ hout
  have hRY : (R : Subgroup Y) ≤ Y₀ := (sylow_le_threeFourCore hp R hER hE hEc).trans hcore
  obtain ⟨κ, -, hκY, hne, hperf, hsub, hQ⟩ :=
    exists_perfect_subnormal_of_not_le_centralizer Nat.prime_two hZK hOutK hC hσs hI hψ hψk hT
      hσC
  exact h Y K Y₀ E R hp hp2 hKn ⟨e⟩ hrk hC hcomp hER hE hEc hcore hRY κ.range hκY hne hperf hsub
    hQ

private theorem not_le_of_mulEquiv {Y X : Type*} [Group Y] [Group X] (hX : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {K Y₀ : Subgroup Y} [K.Normal] (e : K ≃* X)
    (hcomp : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) : ¬ K ≤ Y₀ := by
  haveI := hX
  refine hcomp K (isComponentOf_top_of_isSimpleGroup e.isSimpleGroup ?_) le_rfl
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h

theorem threeFourTwoAt_of_forall {p : ℕ} {X : Type*} [Group X] (hX : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y),
      p.Prime → p ≠ 2 → K.Normal → Nonempty (K ≃* X) →
      pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
      E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
        else GLBCore p 1 E) ≤ Y₀ →
      (R : Subgroup Y) ≤ Y₀ → ¬ K ≤ Y₀ →
      ∀ J : Subgroup Y, J ≤ K ⊓ Y₀ → J ≠ ⊥ → ⁅J, J⁆ = J → IsSubnormal J (K ⊓ Y₀) →
      (∃ (Q : Type) (_ : Group Q) (f : J →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
        CFSG.Open.IsQuasisimple Q) →
      ∃ iK iJ : TauCeti.CFSGIndex, IsThreeFourPair p iK iJ ∧ Nonempty (K ≃* iK.Group) ∧
        ∃ g : J →* iJ.Group, Function.Surjective g) :
    ThreeFourTwoAt p X := by
  haveI := hX
  refine threeFourTwoAt_of_forall_of_center_eq_bot
    (CFSG.ComponentClassification.Helpers.center_eq_bot X hnab) hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore hRY
  haveI := hKn
  obtain ⟨e⟩ := hKX
  exact h Y K Y₀ E R hp hp2 hKn ⟨e⟩ hrk hC hcomp hER hE hEc hcore hRY
    (not_le_of_mulEquiv hX hnab e hcomp)

theorem threeFourTwoNoneAt_of_forall {p : ℕ} {X : Type*} [Group X] (hX : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y),
      p.Prime → p ≠ 2 → K.Normal → Nonempty (K ≃* X) →
      pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
      E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
        else GLBCore p 1 E) ≤ Y₀ →
      (R : Subgroup Y) ≤ Y₀ → ¬ K ≤ Y₀ →
      ∀ J : Subgroup Y, J ≤ K ⊓ Y₀ → J ≠ ⊥ → ⁅J, J⁆ = J → IsSubnormal J (K ⊓ Y₀) →
      (∃ (Q : Type) (_ : Group Q) (f : J →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
        CFSG.Open.IsQuasisimple Q) → False) :
    ThreeFourTwoNoneAt p X := by
  haveI := hX
  refine threeFourTwoNoneAt_of_forall_of_center_eq_bot
    (CFSG.ComponentClassification.Helpers.center_eq_bot X hnab) hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore hRY
  haveI := hKn
  obtain ⟨e⟩ := hKX
  exact h Y K Y₀ E R hp hp2 hKn ⟨e⟩ hrk hC hcomp hER hE hEc hcore hRY
    (not_le_of_mulEquiv hX hnab e hcomp)

theorem threeFourTwoNoneAt_of_solvable_centralizer {p : ℕ} {X : Type*} [Group X]
    (hX : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y),
      p.Prime → p ≠ 2 → K.Normal → Nonempty (K ≃* X) →
      pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
      E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
        else GLBCore p 1 E) ≤ Y₀ →
      (R : Subgroup Y) ≤ Y₀ → ¬ K ≤ Y₀ →
      ∃ N : Subgroup Y, N ≤ K ⊓ Y₀ ∧ IsPGroup p N ∧ K ⊓ Y₀ ≤ normalizer (N : Set Y) ∧
        Group.IsSolvable (centralizer (N : Set Y) ⊓ (K ⊓ Y₀) : Subgroup Y)) :
    ThreeFourTwoNoneAt p X := by
  refine threeFourTwoNoneAt_of_forall hX hnab hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore hRY hKY J _ hne hJp hJs
    ⟨Q, _, f, hf, hfk, hQ⟩
  obtain ⟨N, hNH, hN, hHN, hCN⟩ :=
    h Y K Y₀ E R hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore hRY hKY
  exact hne (eq_bot_of_isSubnormal_of_quasisimple_quotient hp Nat.prime_two hp2 hJs hJp f hf hfk
    hQ hNH hHN hN hCN)

theorem threeFourTwoNoneAt_of_inf {p : ℕ} {X : Type*} [Group X] (hX : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y),
      p.Prime → p ≠ 2 → K.Normal → Nonempty (K ≃* X) →
      pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
      E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
        else GLBCore p 1 E) ≤ Y₀ →
      (R : Subgroup Y) ≤ Y₀ → ¬ K ≤ Y₀ →
      Group.IsSolvable (K ⊓ Y₀ : Subgroup Y) ∨
        ∃ N : Subgroup Y, N ≤ K ⊓ Y₀ ∧ IsPGroup p N ∧ K ⊓ Y₀ ≤ normalizer (N : Set Y) ∧
          centralizer (N : Set Y) ⊓ (K ⊓ Y₀) ≤ N) :
    ThreeFourTwoNoneAt p X := by
  refine threeFourTwoNoneAt_of_solvable_centralizer hX hnab hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore hRY hKY
  rcases h Y K Y₀ E R hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore hRY hKY with
    hsol | ⟨N, hNH, hN, hHN, hCN⟩
  · exact exists_solvable_centralizer_of_isSolvable hsol
  · exact ⟨N, hNH, hN, hHN, isSolvable_centralizer_inf_of_le hp hN hCN⟩

private theorem model_embedding {Y X : Type*} [Group Y] [Group X] {K : Subgroup Y}
    (e : K ≃* X) (Y₀ : Subgroup Y) :
    Function.Injective (K.subtype.comp e.symm.toMonoidHom) ∧
      (K.subtype.comp e.symm.toMonoidHom).range = K ∧
      (K ⊓ Y₀).comap (K.subtype.comp e.symm.toMonoidHom) = (Y₀.subgroupOf K).map e.toMonoidHom := by
  refine ⟨K.subtype_injective.comp e.symm.injective, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
  · rw [Subgroup.map_equiv_eq_comap_symm']
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, SetLike.coe_mem,
      true_and]

private theorem package_comap {X Y : Type*} [Group X] [Group Y] {χ : X →* Y}
    (hχ : Function.Injective χ) {J H : Subgroup Y} (hJχ : J ≤ χ.range) (hJH : J ≤ H)
    (hne : J ≠ ⊥) (hJp : ⁅J, J⁆ = J) (hJs : IsSubnormal J H)
    (hQ : ∃ (Q : Type) (_ : Group Q) (f : J →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      CFSG.Open.IsQuasisimple Q) :
    Nonempty (J.comap χ ≃* J) ∧ J.comap χ ≤ H.comap χ ∧ J.comap χ ≠ ⊥ ∧
      ⁅J.comap χ, J.comap χ⁆ = J.comap χ ∧ IsSubnormal (J.comap χ) (H.comap χ) ∧
      ∃ (Q : Type) (_ : Group Q) (f : J.comap χ →* Q), Function.Surjective f ∧
        IsPGroup 2 f.ker ∧ CFSG.Open.IsQuasisimple Q := by
  have hmap : (J.comap χ).map χ = J := Subgroup.map_comap_eq_self hJχ
  let ι : J.comap χ ≃* J :=
    (Subgroup.equivMapOfInjective (J.comap χ) χ hχ).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨⟨ι⟩, Subgroup.comap_mono hJH, ?_, ?_, hJs.comap χ, ?_⟩
  · intro hbot
    apply hne
    rw [← hmap, hbot, Subgroup.map_bot]
  · apply Subgroup.map_injective hχ
    rw [Subgroup.map_commutator, hmap, hJp]
  · obtain ⟨Q, _, f, hf, hfk, hQ⟩ := hQ
    refine ⟨Q, inferInstance, f.comp ι.toMonoidHom, hf.comp ι.surjective, ?_, hQ⟩
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hfk ⟨ι x, hx⟩
    refine ⟨k, Subtype.ext (ι.injective ?_)⟩
    have h1 : (ι x) ^ 2 ^ k = 1 := by
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val hk
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one, map_pow, map_one] using h1

theorem threeFourTwoAt_of_forall_model {p : ℕ} {X : Type*} [Group X] (hX : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y),
      p.Prime → p ≠ 2 → K.Normal → ∀ e : K ≃* X,
      pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
      E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
        else GLBCore p 1 E) ≤ Y₀ →
      (R : Subgroup Y) ≤ Y₀ → ¬ K ≤ Y₀ →
      ∀ J : Subgroup X, J ≤ (Y₀.subgroupOf K).map e.toMonoidHom → J ≠ ⊥ → ⁅J, J⁆ = J →
      IsSubnormal J ((Y₀.subgroupOf K).map e.toMonoidHom) →
      (∃ (Q : Type) (_ : Group Q) (f : J →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
        CFSG.Open.IsQuasisimple Q) →
      ∃ iK iJ : TauCeti.CFSGIndex, IsThreeFourPair p iK iJ ∧ Nonempty (K ≃* iK.Group) ∧
        ∃ g : J →* iJ.Group, Function.Surjective g) :
    ThreeFourTwoAt p X := by
  refine threeFourTwoAt_of_forall hX hnab hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore hRY hKY J hJ hne hJp hJs hQ
  obtain ⟨e⟩ := hKX
  obtain ⟨hχ, hrange, hH⟩ := model_embedding e Y₀
  obtain ⟨⟨ι⟩, h1, h2, h3, h4, h5⟩ :=
    package_comap hχ ((hJ.trans inf_le_left).trans hrange.ge) hJ hne hJp hJs hQ
  rw [hH] at h1 h4
  obtain ⟨iK, iJ, hpair, hK, g, hg⟩ :=
    h Y K Y₀ E R hp hp2 hKn e hrk hC hcomp hER hE hEc hcore hRY hKY _ h1 h2 h3 h4 h5
  exact ⟨iK, iJ, hpair, hK, g.comp ι.symm.toMonoidHom, hg.comp ι.symm.surjective⟩

theorem threeFourTwoNoneAt_of_model {p : ℕ} {X : Type*} [Group X] (hX : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y),
      p.Prime → p ≠ 2 → K.Normal → ∀ e : K ≃* X,
      pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
      E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
        else GLBCore p 1 E) ≤ Y₀ →
      (R : Subgroup Y) ≤ Y₀ → ¬ K ≤ Y₀ →
      ∃ N : Subgroup X, N ≤ (Y₀.subgroupOf K).map e.toMonoidHom ∧ IsPGroup p N ∧
        (Y₀.subgroupOf K).map e.toMonoidHom ≤ normalizer (N : Set X) ∧
        Group.IsSolvable
          (centralizer (N : Set X) ⊓ (Y₀.subgroupOf K).map e.toMonoidHom : Subgroup X)) :
    ThreeFourTwoNoneAt p X := by
  refine threeFourTwoNoneAt_of_solvable_centralizer hX hnab hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn hKX hrk hC hcomp hER hE hEc hcore hRY hKY
  obtain ⟨e⟩ := hKX
  obtain ⟨N, hNH, hN, hHN, hCN⟩ :=
    h Y K Y₀ E R hp hp2 hKn e hrk hC hcomp hER hE hEc hcore hRY hKY
  set χ : X →* Y := K.subtype.comp e.symm.toMonoidHom with hχ
  have hχi : Function.Injective χ := K.subtype_injective.comp e.symm.injective
  have hχe : χ.comp e.toMonoidHom = K.subtype := by
    ext x
    simp only [hχ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  have hH : ((Y₀.subgroupOf K).map e.toMonoidHom).map χ = K ⊓ Y₀ := by
    rw [Subgroup.map_map, hχe, Subgroup.subgroupOf_map_subtype, inf_comm]
  obtain ⟨h1, h2, h3, h4⟩ := solvable_centralizer_map_of_injective hχi hNH hN hHN hCN
  rw [hH] at h1 h3 h4
  exact ⟨N.map χ, h1, h2, h3, h4⟩

theorem ThreeFourTwoAt.of_mulEquiv {p : ℕ} {X X' : Type*} [Group X] [Group X']
    (e : X ≃* X') (h : ThreeFourTwoAt p X) : ThreeFourTwoAt p X' := by
  intro Y _ _ K Y₀ E R I T _ _ _ σ ψ hp hp2 hKn hKX
  obtain ⟨e'⟩ := hKX
  exact h Y K Y₀ E R I T σ ψ hp hp2 hKn ⟨e'.trans e.symm⟩

end Criteria

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
