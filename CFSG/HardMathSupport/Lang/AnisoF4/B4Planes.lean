module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameB4
public import CFSG.LieType.SeitzGeneration.OrthDfourBig
public import CFSG.LieType.SeitzGeneration.ExcTorusF4
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.AnisoF4

section Descent

open scoped commutatorElement

theorem commutator_mul_central {G : Type*} [Group G] (c1 c2 z1 z2 : G) (h1 : ∀ g, g * z1 = z1 * g)
    (h2 : ∀ g, g * z2 = z2 * g) : ⁅c1 * z1, c2 * z2⁆ = ⁅c1, c2⁆ := by
  have hz1 : ∀ g, z1 * g * z1⁻¹ = g := fun g => by rw [← h1 g, mul_inv_cancel_right]
  have hz2 : ∀ g, z2 * g * z2⁻¹ = g := fun g => by rw [← h2 g, mul_inv_cancel_right]
  simp only [commutatorElement_def]
  calc c1 * z1 * (c2 * z2) * (c1 * z1)⁻¹ * (c2 * z2)⁻¹
      = c1 * (z1 * (c2 * z2) * z1⁻¹) * c1⁻¹ * (c2 * z2)⁻¹ := by group
    _ = c1 * (c2 * z2) * c1⁻¹ * (c2 * z2)⁻¹ := by rw [hz1]
    _ = c1 * c2 * (z2 * c1⁻¹ * z2⁻¹) * c2⁻¹ := by group
    _ = c1 * c2 * c1⁻¹ * c2⁻¹ := by rw [hz2]

variable {G Q : Type*} [Group G] [Group Q] {p : ℕ} [Fact p.Prime]

theorem eq_one_of_pow_eq_one_of_not_dvd {H : Subgroup G} [Finite H] (hcop : ¬ p ∣ Nat.card H)
    {c : G} (hc : c ∈ H) (hcp : c ^ p = 1) : c = 1 := by
  by_contra hne
  have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have h2 : orderOf (⟨c, hc⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
  have h3 : orderOf (⟨c, hc⟩ : H) = orderOf c := Subgroup.orderOf_mk _ _
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h1 with h | h
  · exact hne (orderOf_eq_one_iff.mp h)
  · exact hcop (h ▸ h3 ▸ h2)

theorem closure_centralizers_of_quotient [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hcop : ¬ p ∣ Nat.card π.ker)
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) (E : Subgroup G)
    (hE : ∀ x ∈ E, x ^ p = 1)
    (hQ : Subgroup.closure {k : Q | ∃ y ∈ E.map π, y ≠ 1 ∧ k * y = y * k} = ⊤) :
    Subgroup.closure {g : G | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  classical
  set S : Set G := {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} with hS
  set C : Subgroup G := Subgroup.closure S with hC
  have hne : ∀ x ∈ E, x ≠ 1 → π x ≠ 1 := by
    intro x hx hx1 h1
    exact hx1 (eq_one_of_pow_eq_one_of_not_dvd hcop (MonoidHom.mem_ker.mpr h1) (hE x hx))
  have hlift : ∀ (g x : G), x ∈ E → π g * π x = π x * π g → g * x = x * g := by
    intro g x hx h
    have hc : g * x * g⁻¹ * x⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [h]
      group
    have hcen := Subgroup.mem_center_iff.mp (hker hc)
    have hcp : (g * x * g⁻¹ * x⁻¹) ^ p = 1 := by
      set c := g * x * g⁻¹ * x⁻¹ with hcdef
      have hgx : g * x * g⁻¹ = c * x := by rw [hcdef]; group
      have h1 : g * x ^ p * g⁻¹ = (c * x) ^ p := by
        rw [← hgx, conj_pow]
      rw [hE x hx, mul_one, mul_inv_cancel, (Commute.mul_pow (hcen x).symm), hE x hx, mul_one] at h1
      exact h1.symm
    have := eq_one_of_pow_eq_one_of_not_dvd hcop hc hcp
    have h2 : g * x = x * g := by
      have := congrArg (· * (x * g)) this
      simpa [mul_assoc] using this
    exact h2
  have hmap : C.map π = ⊤ := by
    rw [eq_top_iff, ← hQ, Subgroup.closure_le]
    rintro k ⟨y, ⟨x, hx, rfl⟩, hy1, hk⟩
    obtain ⟨g, rfl⟩ := hπ k
    have hx1 : x ≠ 1 := fun h => hy1 (by rw [h, map_one])
    exact ⟨g, Subgroup.subset_closure ⟨x, hx, hx1, hlift g x hx hk⟩, rfl⟩
  have hCZ : ∀ g : G, ∃ c ∈ C, ∃ z ∈ Subgroup.center G, g = c * z := by
    intro g
    have : π g ∈ C.map π := hmap ▸ Subgroup.mem_top _
    obtain ⟨c, hcC, hc⟩ := this
    refine ⟨c, hcC, c⁻¹ * g, hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hc]; group), ?_⟩
    group
  rw [eq_top_iff, ← hperf, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨c1, hc1, z1, hz1, rfl⟩ := hCZ a
  obtain ⟨c2, hc2, z2, hz2, rfl⟩ := hCZ b
  rw [commutator_mul_central c1 c2 z1 z2 (Subgroup.mem_center_iff.mp hz1)
    (Subgroup.mem_center_iff.mp hz2)]
  rw [commutatorElement_def]
  exact C.mul_mem (C.mul_mem (C.mul_mem hc1 hc2) (C.inv_mem hc1)) (C.inv_mem hc2)

end Descent

section Center

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.Assembly.LowTwoRank

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem not_dvd_card_center_spin_of_not_dvd_pred [Nonempty ι] [Finite F]
    (Q : QuadraticForm F (ι → F)) {Q₀ : (ι → F) → F}
    (hR : (spinMatrix Q).range = StatedOmega Q₀) [Finite (spinGroup Q)]
    (hker : (spinToStatedProj Q hR).ker = Subgroup.center (spinGroup Q))
    (hcomap : (spinToStatedProj Q hR).ker = (StatedScalars ι F).comap (spinMatrix Q))
    (hker2 : ∀ x ∈ (spinMatrix Q).ker, x * x = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F - 1) : ¬ p ∣ Nat.card (Subgroup.center (spinGroup Q)) := by
  refine not_dvd_card_center_of_forall (p := p) fun x hx hxp => ?_
  have hx' : x ∈ (StatedScalars ι F).comap (spinMatrix Q) := by
    rw [← hcomap, hker]
    exact hx
  obtain ⟨c, hc⟩ := Subgroup.mem_comap.mp hx'
  have hcp : c ^ p = 1 := by
    apply scalar_injective_of_nonempty (ι := ι)
    rw [map_pow, hc, ← map_pow, hxp, map_one, map_one]
  have hc1 : c = 1 := by
    by_contra hne
    have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    have h2 : orderOf c ∣ Nat.card F - 1 := by
      have := orderOf_dvd_natCard c
      rwa [Nat.card_units] at this
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h1 with h | h
    · exact hne (orderOf_eq_one_iff.mp h)
    · exact hpq (h ▸ h2)
  have hxm : spinMatrix Q x = 1 := by
    rw [← hc, hc1, map_one]
  have hk : x * x = 1 := hker2 x hxm
  obtain ⟨k, hk'⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  calc x = x ^ p := by
        rw [hk', pow_succ, pow_mul, sq, hk, one_pow, one_mul]
    _ = 1 := hxp

end Center

section Rank

open CFSG.Open CFSG.LieType.SeitzGeneration

variable {G Q H : Type*} [Group G] [Group Q] [Group H] {p : ℕ} [Fact p.Prime]

theorem card_map_eq_of_disjoint {A B : Type*} [Group A] [Group B] (φ : A →* B) {E : Subgroup A}
    (h : Disjoint E φ.ker) : Nat.card (E.map φ) = Nat.card E := by
  have hinj : Function.Injective (φ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : A) ∈ φ.ker := hx
    exact Subtype.ext (Subgroup.disjoint_def.mp h x.2 hx')
  have hrange : (φ.comp E.subtype).range = E.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem disjoint_ker_of_exponent [Finite G] (φ : G →* Q) (hcop : ¬ p ∣ Nat.card φ.ker)
    {E : Subgroup G} (hE : ∀ x ∈ E, x ^ p = 1) : Disjoint E φ.ker := by
  rw [Subgroup.disjoint_def]
  intro x hx hxk
  exact eq_one_of_pow_eq_one_of_not_dvd hcop hxk (hE x hx)

theorem exists_lift_elemAbelian [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (hcop : ¬ p ∣ Nat.card π.ker) {F : Subgroup Q} (hF : IsElemAbelian p F) :
    ∃ E' : Subgroup G, E'.map π = F ∧ Disjoint E' π.ker ∧ IsElemAbelian p E' := by
  have hFp : IsPGroup p F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
  obtain ⟨E', hmap, hdis⟩ := CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker π hπ
    hcop F hFp
  have hmem : ∀ x ∈ E', π x ∈ F := fun x hx => hmap ▸ ⟨x, hx, rfl⟩
  have hexp : ∀ x ∈ E', x ^ p = 1 := by
    intro x hx
    refine Subgroup.disjoint_def.mp hdis (E'.pow_mem hx p) ?_
    rw [MonoidHom.mem_ker, map_pow]
    exact hF.2 _ (hmem x hx)
  have hcomm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' :=
      E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha)) (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := congrArg Subtype.val (hF.1.is_comm.comm ⟨π a, hmem a ha⟩ ⟨π b, hmem b hb⟩)
      have h : π a * π b = π b * π a := this
      rw [h]
      group
    have := Subgroup.disjoint_def.mp hdis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  exact ⟨E', hmap, hdis, IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩

theorem rankLE2_of_cover [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (hπc : ¬ p ∣ Nat.card π.ker) (Ψ : G →* H) (hΨc : ¬ p ∣ Nat.card Ψ.ker) (hH : RankLE2 p H) :
    RankLE2 p Q := by
  intro F hF
  obtain ⟨E', hmap, hdis, hE'⟩ := exists_lift_elemAbelian π hπ hπc hF
  have h1 : Nat.card F = Nat.card E' := by
    rw [← hmap]
    exact card_map_eq_of_disjoint π hdis
  have h2 : Nat.card (E'.map Ψ) = Nat.card E' :=
    card_map_eq_of_disjoint Ψ (disjoint_ker_of_exponent Ψ hΨc hE'.2)
  rw [h1, ← h2]
  exact hH _ (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE' Ψ)

end Rank

section Main

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.LieType.SeitzGeneration CFSG.Open
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut


theorem iSup_b4Chain_le_closure_centralizers {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K ^ 2 + 1)
    (E : Subgroup (adjointGroup .F4 K)) (hE : E ≤ ⨆ k, b4Chain K k) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEc : Nat.card E = p ^ 2) :
    ⨆ k, b4Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hℓ2 : ringChar K ≠ 2 := by
    intro h
    apply h2
    have : CharP K 2 := h ▸ ringChar.charP K
    exact CharTwo.two_eq_zero
  obtain ⟨Ψ, hΨker, hΨrange, -, -⟩ := exists_psi_B4_F4_frame hℓ hℓ2 hK h2
  have hn3 : 3 ≤ 4 := by norm_num
  have : Nonempty (Fin 4 ⊕ Fin 4 ⊕ Unit) := ⟨Sum.inr (Sum.inr ())⟩
  have : Finite (spinGroup (quadOdd 4 K)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadOdd (n := 4) h2 hn3
  set π := spinToStatedProj (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3) with hπdef
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h1 : Nat.card K ^ 2 + 1 = (Nat.card K - 1) * (Nat.card K + 1) + 2 := by
      obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
      rw [hm]; simp; ring
    have h3 : p ∣ (Nat.card K - 1) * (Nat.card K + 1) := dvd_mul_of_dvd_left hd _
    rw [h1] at hpq
    have : p ∣ 2 := (Nat.dvd_add_right h3).mp hpq
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)) hp2 hpq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) := by
      rw [hZ]
    exact hd.trans this
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    apply hcen
    exact hd.trans (Subgroup.card_dvd_of_le hΨker)
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadOdd 4 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadOdd h2 hn3).commutator_eq_top
  have hF4 : RankLE2 p (adjointGroup .F4 K) :=
    (sylowTorus_F4_four K hp (by omega) hpq).rankLE2 hp le_rfl
  have hrk : RankLE2 p (StatedProj (StatedOmega (StatedQuadOdd 4 K))) :=
    rankLE2_of_cover π hπsurj hπcop Ψ hΨcop hF4
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := by
      have := (Nat.dvd_add_right (dvd_pow hd (by norm_num : (2 : ℕ) ≠ 0))).mp hpq
      exact this
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hEpg : IsPGroup p E := IsPGroup.of_card hEc
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hΨrange ▸ hE
  set Ψ' : spinGroup (quadOdd 4 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ := exists_lift_elemAbelian Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← card_map_eq_of_disjoint Ψ' hdisE', hmapE', hcardE1]
  set Ebar : Subgroup _ := E'.map π with hEbar
  have hEbarea : IsElemAbelian p Ebar :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE'ea π
  have hcardEbar : Nat.card Ebar = p ^ 2 := by
    rw [hEbar, card_map_eq_of_disjoint π (disjoint_ker_of_exponent π hπcop hE'ea.2), hcardE']
  have hmodel := orthogonalOddLow_of_residual orthSelfDualTwoBlocks (r := 4) (by norm_num) hp hp2
    hpK h2 hrk Ebar hEbarea hcardEbar
  have hG := closure_centralizers_of_quotient π hπsurj hZ.le hπcop hperf E' hE'ea.2 hmodel
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  rw [← hΨrange, MonoidHom.range_eq_map, ← hG, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨x, hx, hx1, hg⟩, rfl⟩
  refine ⟨Ψ x, ?_, ?_, ?_⟩
  · have : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
    exact this
  · intro h1
    exact hx1 (Subgroup.disjoint_def.mp hdisΨ hx (MonoidHom.mem_ker.mpr h1))
  · show Ψ g * Ψ x = Ψ x * Ψ g
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ hg

end Main

end CFSG.HardMathSupport.Lang.AnisoF4
