module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434General
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PermPerfectCentralizer

public section

open Equiv Equiv.Perm
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

namespace I1434.Alt

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fixes_support_of_perfect_of_commute_isCycle {P : Subgroup (Perm α)} (hP : ⁅P, P⁆ = P)
    {c : Perm α} (hc : c.IsCycle) (hPc : ∀ g ∈ P, Commute g c) :
    ∀ g ∈ P, ∀ y ∈ c.support, g y = y := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  let f : P →* Perm c.support :=
    MonoidHom.mk' (fun g => (g : Perm α).subtypePerm (mem_support_iff_of_commute (hPc g g.2)))
      (by intro a b; ext x; rfl)
  have hrange : f.range ≤ Subgroup.zpowers c.subtypePermOfSupport := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨_, hmem⟩ := hc.commute_iff'.mp (hPc g g.2)
    exact hmem
  have : IsMulCommutative f.range := isMulCommutative_iff.mpr fun a b => Subtype.ext <| by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hrange a.2)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hrange b.2)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self _ i j).eq
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  intro g hg y hy
  have h1 : f ⟨g, hg⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨f ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩ : f.range) 1)
  have := congrArg (fun u : Perm c.support => (u ⟨y, hy⟩ : α)) h1
  simpa [f] using this

theorem commute_cycleFactors_of_perfect {σ : Perm α} (hk : Nat.card σ.cycleFactorsFinset ≤ 4)
    {P : Subgroup (Perm α)} (hP : ⁅P, P⁆ = P) (hPσ : P ≤ Subgroup.centralizer {σ}) :
    ∀ g ∈ P, ∀ c ∈ σ.cycleFactorsFinset, Commute g c := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  have : Group.IsSolvable (Perm σ.cycleFactorsFinset) := Equiv.Perm.isSolvable hk
  have hρ := CFSG.HardMathSupport.Curtis.UnitaryLevi.hom_eq_one_of_perfect_solvable
    ((OnCycleFactors.toPermHom σ).comp (Subgroup.inclusion hPσ))
  intro g hg
  refine (OnCycleFactors.mem_ker_toPermHom_iff σ (Subgroup.inclusion hPσ ⟨g, hg⟩)).mp ?_
  rw [MonoidHom.mem_ker]
  exact DFunLike.congr_fun hρ ⟨g, hg⟩

theorem fixes_support_of_perfect {σ : Perm α} (hk : Nat.card σ.cycleFactorsFinset ≤ 4)
    {P : Subgroup (Perm α)} (hP : ⁅P, P⁆ = P) (hPσ : P ≤ Subgroup.centralizer {σ}) :
    ∀ g ∈ P, ∀ y ∈ σ.support, g y = y := by
  intro g hg y hy
  have hc : σ.cycleOf y ∈ σ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.mpr hy
  refine fixes_support_of_perfect_of_commute_isCycle hP (mem_cycleFactorsFinset_iff.mp hc).1
    (fun g' hg' => commute_cycleFactors_of_perfect hk hP hPσ g' hg' _ hc) g hg y ?_
  rw [mem_support, cycleOf_apply_self]
  exact mem_support.mp hy

theorem orderOf_of_mem_cycleFactorsFinset {p : ℕ} [Fact p.Prime] {σ c : Perm α} (hσ : σ ^ p = 1)
    (hc : c ∈ σ.cycleFactorsFinset) : orderOf c = p :=
  orderOf_eq_prime (pow_prime_eq_one_iff.mpr fun n hn => pow_prime_eq_one_iff.mp hσ n
    (Multiset.mem_of_le (cycleType_le_of_mem_cycleFactorsFinset hc) hn))
    (mem_cycleFactorsFinset_iff.mp hc).1.ne_one

theorem sign_eq_one_of_pow_five_eq_one {g : Perm α} (hg : g ^ 5 = 1) : sign g = 1 := by
  rcases Int.units_eq_one_or (sign g) with h | h
  · exact h
  · have h5 : sign g ^ 5 = 1 := by rw [← map_pow, hg, map_one]
    rw [h] at h5
    exact absurd h5 (by decide)

theorem support_subset_compl_support_iff {g σ : Perm α} :
    g.support ⊆ σ.supportᶜ ↔ ∀ y ∈ σ.support, g y = y := by
  constructor
  · intro h y hy
    by_contra hne
    exact Finset.mem_compl.mp (h (mem_support.mpr hne)) hy
  · intro h y hy
    exact Finset.mem_compl.mpr fun hyσ => mem_support.mp hy (h y hyσ)

end Perm

section Transport

variable {α : Type*} [Fintype α] [DecidableEq α] {K : Type*} [Group K]

theorem exists_isElemAbelian_card_eq (e : K ≃* alternatingGroup α) {σ : Perm α} (hσ : σ ^ 5 = 1) :
    ∃ E : Subgroup K, CFSG.Open.IsElemAbelian 5 E ∧
      Nat.card E = 5 ^ Nat.card σ.cycleFactorsFinset := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let ι₀ : ((c : σ.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) →* Perm α :=
    (OnCycleFactors.kerParam σ).comp (MonoidHom.inr _ _)
  have hι₀ : Function.Injective ι₀ :=
    (OnCycleFactors.kerParam_injective σ).comp fun a b h => congrArg Prod.snd h
  have hexp : ∀ v : (c : σ.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α), v ^ 5 = 1 := by
    intro v
    funext c
    have h5 : Nat.card (Subgroup.zpowers (c : Perm α)) = 5 := by
      rw [Nat.card_zpowers, orderOf_of_mem_cycleFactorsFinset hσ c.2]
    rw [Pi.pow_apply, Pi.one_apply, ← h5]
    exact pow_card_eq_one'
  have hcomm : ∀ v w : (c : σ.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α),
      v * w = w * v := by
    intro v w
    funext c
    apply Subtype.ext
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (v c).2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (w c).2
    rw [Pi.mul_apply, Pi.mul_apply, Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self _ i j).eq
  have hmem : ∀ v, ι₀ v ∈ alternatingGroup α := fun v => by
    rw [mem_alternatingGroup]
    exact sign_eq_one_of_pow_five_eq_one (by rw [← map_pow, hexp, map_one])
  let ι := e.symm.toMonoidHom.comp (ι₀.codRestrict _ hmem)
  have hι : Function.Injective ι :=
    e.symm.injective.comp fun a b h => hι₀ (congrArg Subtype.val h)
  refine ⟨ι.range, ⟨isMulCommutative_iff.mpr ?_, ?_⟩, ?_⟩
  · rintro ⟨_, v, rfl⟩ ⟨_, w, rfl⟩
    apply Subtype.ext
    change ι v * ι w = ι w * ι v
    rw [← map_mul, ← map_mul, hcomm]
  · rintro _ ⟨v, rfl⟩
    rw [← map_pow, hexp, map_one]
  · have hprod : ∏ c : σ.cycleFactorsFinset, Nat.card (Subgroup.zpowers (c : Perm α)) =
        ∏ _c : σ.cycleFactorsFinset, 5 :=
      Finset.prod_congr rfl fun c _ => by
        rw [Nat.card_zpowers, orderOf_of_mem_cycleFactorsFinset hσ c.2]
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, Nat.card_pi, hprod,
      Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

def fixAlt (e : K ≃* alternatingGroup α) (σ : Perm α) : Subgroup K :=
  (e.symm.toMonoidHom.comp (alternatingGroup.ofSubtype σ.supportᶜ)).range

noncomputable def fixAltEquiv (e : K ≃* alternatingGroup α) (σ : Perm α) :
    alternatingGroup (σ.supportᶜ : Finset α) ≃* fixAlt e σ :=
  MonoidHom.ofInjective (f := e.symm.toMonoidHom.comp (alternatingGroup.ofSubtype σ.supportᶜ))
    (e.symm.injective.comp alternatingGroup.ofSubtype_injective)

theorem mem_fixAlt {e : K ≃* alternatingGroup α} {σ : Perm α} {g : K} :
    g ∈ fixAlt e σ ↔ ∀ y ∈ σ.support, (e g : Perm α) y = y := by
  have h : g ∈ fixAlt e σ ↔ e g ∈ (alternatingGroup.ofSubtype σ.supportᶜ).range := by
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, by simp⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, by simp [hu]⟩
  rw [h, alternatingGroup.mem_range_ofSubtype_iff, support_subset_compl_support_iff]

theorem fixAlt_le_centralizer (e : K ≃* alternatingGroup α) (x : K) :
    fixAlt e (e x : Perm α) ≤ Subgroup.centralizer {x} := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply e.injective
  apply Subtype.ext
  rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  have hd : (e g : Perm α).Disjoint (e x : Perm α) := by
    rw [disjoint_iff_disjoint_support, ← Finset.subset_compl_iff_disjoint_right,
      support_subset_compl_support_iff]
    exact mem_fixAlt.mp hg
  exact hd.commute.eq

theorem fixAlt_normal (e : K ≃* alternatingGroup α) (x : K) :
    ((fixAlt e (e x : Perm α)).subgroupOf (Subgroup.centralizer {x})).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (fixAlt_le_centralizer e x)]
  intro h k hh hk
  rw [mem_fixAlt] at hh ⊢
  intro y hy
  have hkx : Commute (e k : Perm α) (e x : Perm α) := by
    have := congrArg (fun g => (e g : Perm α)) (Subgroup.mem_centralizer_singleton_iff.mp hk)
    simp only [map_mul, Subgroup.coe_mul] at this
    exact this
  have hy' : (e k : Perm α)⁻¹ y ∈ (e x : Perm α).support :=
    (mem_support_iff_of_commute hkx.inv_left y).mpr hy
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
  rw [hh _ hy']
  simp

theorem le_fixAlt_of_perfect (e : K ≃* alternatingGroup α) {x : K}
    (hk : Nat.card (e x : Perm α).cycleFactorsFinset ≤ 4) {P : Subgroup K} (hP : ⁅P, P⁆ = P)
    (hPx : P ≤ Subgroup.centralizer {x}) : P ≤ fixAlt e (e x : Perm α) := by
  let φ : K →* Perm α := (alternatingGroup α).subtype.comp e.toMonoidHom
  have hP' : ⁅P.map φ, P.map φ⁆ = P.map φ := by rw [← Subgroup.map_commutator, hP]
  have hPσ : P.map φ ≤ Subgroup.centralizer {(e x : Perm α)} := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg φ (Subgroup.mem_centralizer_singleton_iff.mp (hPx hg))
    rw [map_mul, map_mul] at this
    exact this
  intro g hg
  rw [mem_fixAlt]
  exact fixes_support_of_perfect hk hP' hPσ (φ g) ⟨g, hg, rfl⟩

end Transport

theorem false_of_data {K : Type} [Group K] [Finite K] {n : ℕ} (e : K ≃* alternatingGroup (Fin n))
    {Q : Sylow 5 K} {x : K} {J₁ J₂ : Subgroup K} (hD : I1434.Data K Q x J₁ J₂) : False := by
  have hF := hD.five
  have hσ5 : (e x : Perm (Fin n)) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hD.pow_five, map_one, Subgroup.coe_one]
  have hk : Nat.card (e x : Perm (Fin n)).cycleFactorsFinset ≤ 3 := by
    obtain ⟨E, hE, hcard⟩ := exists_isElemAbelian_card_eq e hσ5
    have h := card_le_of_isElemAbelian hD.rank hE
    rw [hcard] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  set H := fixAlt e (e x : Perm (Fin n))
  set F : Finset (Fin n) := (e x : Perm (Fin n)).supportᶜ
  have hJ₁ : J₁ ≤ H := le_fixAlt_of_perfect e (by omega) hF.perfect₁ hF.le₁
  have hJ₂ : J₂ ≤ H := le_fixAlt_of_perfect e (by omega) hF.perfect₂ hF.le₂
  have h60 : 60 ∣ Nat.card H := hF.sixty_dvd_card₁.trans (Subgroup.card_dvd_of_le hJ₁)
  have hle60 : 60 ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos h60
  have hcardH : Nat.card H = Nat.card (alternatingGroup F) :=
    Nat.card_congr (fixAltEquiv e (e x : Perm (Fin n))).toEquiv.symm
  by_cases hs : Nat.card F ≤ 4
  ·
    have h1 := Subgroup.card_le_card_group (alternatingGroup F)
    rw [Nat.card_perm] at h1
    have h2 := (Nat.factorial_le hs).trans (by decide : Nat.factorial 4 ≤ 24)
    omega
  ·
    have : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup (by omega)
    have : IsSimpleGroup H := (fixAltEquiv e (e x : Perm (Fin n))).symm.isSimpleGroup
    have hnab : ∃ a b : H, a * b ≠ b * a := by
      refine CFSG.ComponentClassification.Helpers.nonabelian_of_equiv
        (fixAltEquiv e (e x : Perm (Fin n))).symm ?_
      by_contra! h
      have h3 : Nat.card F ≤ 3 :=
        alternatingGroup.isMulCommutative_iff_card_le_three.mp (isMulCommutative_iff.mpr h)
      omega
    have : Group.IsPerfect H := ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top _ hnab⟩
    have hq : CFSG.Open.IsQuasisimple H :=
      CFSG.ComponentClassification.Quasisimple.simple_of_perfect _
    have hsub : CFSG.Open.IsSubnormal H (Subgroup.centralizer {x}) :=
      CFSG.Open.IsSubnormal.step (fixAlt_le_centralizer e x) (fixAlt_normal e x)
        (CFSG.Open.IsSubnormal.refl _)
    have h5 : 5 ∣ Nat.card H := (by norm_num : 5 ∣ 60).trans h60
    have hG2 := card_quotient_eq_sixty_of_subnormal_quasisimple hF hsub hq h5
    have : (primeComplementCore (G := H) 5).Normal :=
      CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_normal 5
    have hbot : primeComplementCore (G := H) 5 = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right (primeComplementCore_ne_top h5)
    have hH60 : Nat.card H = 60 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (primeComplementCore (G := H) 5), hG2,
        hbot, Subgroup.card_bot]
    have hc₁ : Nat.card H ≤ Nat.card J₁ := hH60 ▸ Nat.le_of_dvd Nat.card_pos hF.sixty_dvd_card₁
    have hc₂ : Nat.card H ≤ Nat.card J₂ := hH60 ▸ Nat.le_of_dvd Nat.card_pos hF.sixty_dvd_card₂
    exact hF.ne ((Subgroup.eq_of_le_of_card_ge hJ₁ hc₁).trans
      (Subgroup.eq_of_le_of_card_ge hJ₂ hc₂).symm)

end I1434.Alt

theorem i1434AltCase_holds : I1434AltCase := by
  intro K _ _ n _ ⟨e⟩ Q x J₁ J₂ hD
  exact I1434.Alt.false_of_data e hD

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
