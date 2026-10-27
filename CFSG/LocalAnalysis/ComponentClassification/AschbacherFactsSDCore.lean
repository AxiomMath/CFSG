module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CyclicFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourCentral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsSD

open CFSG.Open

@[expose] def SimpleFixedInvolutionPair : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    HasSemidihedralSylowTwo X → ∀ α : MulAut X, α ^ 2 = 1 →
      ∃ u w : X, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
        α u = u ∧ α w = w

theorem odd_card_center {L : Type} [Group L] [Finite L] (hq : Open.IsQuasisimple L)
    (hS : HasSemidihedralSylowTwo L) : Odd (Nat.card (Subgroup.center L)) := by
  obtain ⟨S, n, hn, hSe⟩ := hS
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 2
    (even_iff_two_dvd.mp hodd)
  exact AschbacherTheorem5.SevenFour.semidihedral_perfect_no_central_involution hperf S hn hSe
    x.2 (by rw [Subgroup.orderOf_coe, hx])

theorem exists_involution_pair_commuting {X : Type} [Group X] [Finite X]
    (hsd : HasSemidihedralSylowTwo X) {g : X} (hg : g ^ 2 = 1) :
    ∃ u w : X, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      u * g = g * u ∧ w * g = g * w := by
  classical
  obtain ⟨S, n, hn, ⟨e⟩⟩ := hsd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgp : IsPGroup 2 (Subgroup.zpowers g) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    change (g ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  obtain ⟨P, hPg⟩ := hgp.exists_le_sylow
  have hgP : g ∈ (P : Subgroup X) := hPg (Subgroup.mem_zpowers g)
  let f : SemidihedralGroup n ≃* (P : Subgroup X) :=
    ((Sylow.equiv P S).trans e).symm
  have hn3 : 3 ≤ n := by omega
  set zP : X := (f (Semidihedral.z n) : X) with hzP
  set sP : X := (f (Semidihedral.s n) : X) with hsP
  have hzc : ∀ y ∈ (P : Subgroup X), zP * y = y * zP := by
    intro y hy
    have h := Subgroup.mem_center_iff.mp (Semidihedral.z_mem_center n hn) (f.symm ⟨y, hy⟩)
    have h' := congrArg (fun t => (f t : X)) h
    simpa [map_mul, hzP] using h'.symm
  have hzP2 : zP ^ 2 = 1 := by
    have h : f (Semidihedral.z n) ^ 2 = 1 := by rw [← map_pow, Semidihedral.z_sq n hn3, map_one]
    simpa [hzP] using congrArg Subtype.val h
  have hsP2 : sP ^ 2 = 1 := by
    have h : f (Semidihedral.s n) ^ 2 = 1 := by rw [← map_pow, Semidihedral.s_sq, map_one]
    simpa [hsP] using congrArg Subtype.val h
  have hzP1 : zP ≠ 1 := by
    intro h
    apply Semidihedral.z_ne_one n hn3
    apply f.injective
    rw [map_one]
    exact Subtype.ext h
  have hsP1 : sP ≠ 1 := by
    intro h
    have h1 : Semidihedral.s n = 1 := by
      apply f.injective
      rw [map_one]
      exact Subtype.ext h
    have h2 := Semidihedral.orderOf_s n hn3
    rw [h1, orderOf_one] at h2
    omega
  have hzs : zP ≠ sP := by
    intro h
    have h1 : Semidihedral.z n = Semidihedral.s n := f.injective (Subtype.ext h)
    rw [Semidihedral.z_eq_element n hn3, Semidihedral.s_eq_element n hn3,
      Semidihedral.element_eq_iff] at h1
    exact absurd h1.2 (by decide)
  have hsPP : sP ∈ (P : Subgroup X) := (f (Semidihedral.s n)).2
  by_cases hg1 : g = 1 ∨ g = zP
  · refine ⟨zP, sP, hzP2, hsP2, hzP1, hsP1, hzs, hzc sP hsPP, hzc g hgP, ?_⟩
    rcases hg1 with rfl | rfl
    · rw [mul_one, one_mul]
    · exact (hzc sP hsPP).symm
  · push Not at hg1
    obtain ⟨hg1, hgz⟩ := hg1
    exact ⟨zP, g, hzP2, hg, hzP1, hg1, hgz.symm, hzc g hgP, hzc g hgP, rfl⟩

theorem exists_fixed_involution_pair (hsimple : SimpleFixedInvolutionPair) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} {a : G} (hq : Open.IsQuasisimple L)
    (hLs : HasSemidihedralSylowTwo L) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (ha2 : a ^ 2 = 1) :
    ∃ u w : G, u ∈ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
      w ∈ L ⊓ Subgroup.centralizer ({a} : Set G) ∧ u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧
      u ≠ w ∧ u * w = w * u := by
  classical
  have hZ := odd_card_center hq hLs
  set Z := Subgroup.center L with hZdef
  have hφL : ∀ x, x ∈ L ↔ MulAut.conj a x ∈ L := by
    intro x
    rw [MulAut.conj_apply]
    exact Subgroup.mem_normalizer_iff.mp haN x
  let β : MulAut L := FactsL2.restrictMulAut (MulAut.conj a) L hφL
  have hβ : ∀ x : L, (β x : G) = a * x * a⁻¹ := fun x => rfl
  have hββ : ∀ x, β (β x) = x := by
    intro x
    apply Subtype.ext
    rw [hβ, hβ]
    calc a * (a * (x : G) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [← pow_two, ha2]; group
  have hβfix : ∀ x : L, β x = x ↔ (x : G) * a = a * x := by
    intro x
    rw [Subtype.ext_iff, hβ]
    constructor
    · intro h
      calc (x : G) * a = a * x * a⁻¹ * a := by rw [h]
        _ = a * x := by group
    · intro h
      rw [← h]
      group
  have hβZ : Z.map (β : L →* L) = Z := Subgroup.map_center_eq β
  let α : MulAut (L ⧸ Z) := QuotientGroup.congr Z Z β hβZ
  have hα : ∀ x : L, α (x : L ⧸ Z) = ((β x : L) : L ⧸ Z) := fun x => rfl
  have hαα : ∀ q, α (α q) = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hα, hα, hββ]
  have hαsq : α ^ 2 = 1 := by
    ext q
    rw [pow_two, MulAut.mul_apply, hαα, MulAut.one_apply]
  have : IsSimpleGroup (L ⧸ Z) := hq.2
  have hnonab : ∃ x y : L ⧸ Z, x * y ≠ y * x := by
    by_contra hab
    push Not at hab
    have hle : commutator L ≤ Z := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [commutatorElement_def, ← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hab (x : L ⧸ Z) (y : L ⧸ Z)]
      group
    rw [hq.1] at hle
    have hsub : Subsingleton (L ⧸ Z) := by
      constructor
      intro u v
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
      rw [QuotientGroup.eq]
      exact hle (Subgroup.mem_top _)
    exact not_subsingleton (L ⧸ Z) hsub
  have hQs : HasSemidihedralSylowTwo (L ⧸ Z) := by
    obtain ⟨S, n, hn, ⟨eS⟩⟩ := hLs
    let π : L →* L ⧸ Z := QuotientGroup.mk' Z
    have hinj : Function.Injective (π.comp (S : Subgroup L).subtype) := by
      rw [injective_iff_map_eq_one]
      intro s hs
      have hsZ : (s : L) ∈ Z := (QuotientGroup.eq_one_iff _).mp hs
      have h2 : IsPGroup 2 (S : Subgroup L) := S.isPGroup'
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) s
      have hodd := FactsL2.odd_orderOf_of_mem_center hZ hsZ
      rw [Subgroup.orderOf_coe, hk] at hodd
      rcases k with _ | k
      · rw [pow_zero] at hk
        exact orderOf_eq_one_iff.mp hk
      · exact absurd hodd (by rw [pow_succ]; simp)
    refine ⟨S.mapSurjective (f := π) (QuotientGroup.mk'_surjective Z), n, hn, ⟨?_⟩⟩
    have hrange : (π.comp (S : Subgroup L).subtype).range = (S : Subgroup L).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact (((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm).trans eS
  obtain ⟨ub, wb, hu, hw, hu1, hw1, huw, hc, hαu, hαw⟩ := hsimple (L ⧸ Z) hnonab hQs α hαsq
  have hlift : ∀ q : L ⧸ Z, q ^ 2 = 1 → q ≠ 1 → α q = q →
      ∃ x : L, (x : L ⧸ Z) = q ∧ x ^ 2 = 1 ∧ β x = x := by
    intro q hq2 hq1 hαq
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (x₀ : L)⁻¹ * β x₀ ∈ Z := by
      rw [← QuotientGroup.eq, ← hα]
      exact hαq.symm
    obtain ⟨z, hz, hfix⟩ := FactsL2.exists_fixed_of_fixed_mod_center hZ β hββ x₀ h1
    set x₁ := x₀ * z
    have hx₁ : ((x₁ : L) : L ⧸ Z) = (x₀ : L ⧸ Z) := by
      rw [QuotientGroup.eq]
      simpa [x₁] using hz
    obtain ⟨k, hk⟩ := hZ
    refine ⟨x₁ ^ (2 * k + 1), ?_, ?_, ?_⟩
    · rw [QuotientGroup.mk_pow, hx₁, pow_succ, pow_mul, hq2, one_pow, one_mul]
    · have hsq : x₁ ^ 2 ∈ Z := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hx₁, hq2]
      have hpow : (x₁ ^ 2) ^ Nat.card Z = 1 := by
        have := pow_card_eq_one' (G := Z) (x := ⟨x₁ ^ 2, hsq⟩)
        exact congrArg Subtype.val this
      rw [← pow_mul, mul_comm, pow_mul, ← hk, hpow]
    · rw [map_pow, hfix]
  obtain ⟨u, hub, hu2, hβu⟩ := hlift ub hu hu1 hαu
  obtain ⟨w, hwb, hw2, hβw⟩ := hlift wb hw hw1 hαw
  have hu1' : u ≠ 1 := fun h => hu1 (by rw [← hub, h, QuotientGroup.mk_one])
  have hw1' : w ≠ 1 := fun h => hw1 (by rw [← hwb, h, QuotientGroup.mk_one])
  have huw' : u ≠ w := fun h => huw (by rw [← hub, ← hwb, h])
  have hc' : u * w = w * u := by
    set d := u * w * u⁻¹ * w⁻¹ with hd
    have hdZ : d ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [hd, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hub, hwb]
      rw [hc]
      group
    have hcomm : ∀ y : L, d * y = y * d := fun y => (Subgroup.mem_center_iff.mp hdZ y).symm
    have hd2 : d ^ 2 = 1 := by
      have h1 : u * w * u⁻¹ = d * w := by rw [hd]; group
      have h2 : w = u * (u * w * u⁻¹) * u⁻¹ := by
        calc w = (u * u) * w * (u * u)⁻¹ := by rw [← pow_two, hu2]; group
          _ = u * (u * w * u⁻¹) * u⁻¹ := by group
      rw [h1] at h2
      have h3 : w = d * (u * w * u⁻¹) := by
        calc w = u * (d * w) * u⁻¹ := h2
          _ = u * d * w * u⁻¹ := by group
          _ = d * u * w * u⁻¹ := by rw [← hcomm u]
          _ = d * (u * w * u⁻¹) := by group
      rw [h1] at h3
      have : d * d * w = 1 * w := by
        calc d * d * w = d * (d * w) := by group
          _ = w := h3.symm
          _ = 1 * w := by group
      rw [pow_two]
      exact mul_right_cancel this
    have hd1 := FactsL2.eq_one_of_sq_eq_one_of_mem_center hZ hdZ hd2
    calc u * w = d * w * u := by rw [hd]; group
      _ = w * u := by rw [hd1, one_mul]
  have hmem : ∀ x : L, β x = x → (x : G) ∈ L ⊓ Subgroup.centralizer ({a} : Set G) :=
    fun x hx => Subgroup.mem_inf.mpr ⟨x.2,
      Subgroup.mem_centralizer_singleton_iff.mpr ((hβfix x).mp hx)⟩
  refine ⟨u, w, hmem u hβu, hmem w hβw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hu2
  · simpa using congrArg Subtype.val hw2
  · exact fun h => hu1' (Subtype.ext (by simpa using h))
  · exact fun h => hw1' (Subtype.ext (by simpa using h))
  · exact fun h => huw' (Subtype.ext h)
  · simpa using congrArg Subtype.val hc'

theorem semidihedral_four_group_of_simple (hsimple : SimpleFixedInvolutionPair) :
    ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G),
      Open.IsQuasisimple L → HasSemidihedralSylowTwo L → U ≤ Subgroup.normalizer (L : Set G) →
      IsFourGroup U →
        ∃ u ∈ U, u ≠ 1 ∧ 2 ≤ Open.pRank 2 (L ⊓ Subgroup.centralizer ({u} : Set G)) := by
  intro G _ _ L U hq hLs hUN hU
  have hUbot : U ≠ ⊥ := by
    intro h
    have h4 := hU.2
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨u, huU⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hUbot
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : u ^ 2 = 1 := hU.1.2 u huU
  obtain ⟨x, y, hx, hy, hx2, hy2, hx1, hy1, hxy, hc⟩ :=
    exists_fixed_involution_pair hsimple hq hLs (hUN huU) hu2
  refine ⟨u, huU, hu1', ?_⟩
  apply Lemma38.two_le_pRank_of_fourGroup
    (Lemma38.isFourGroup_closure_pair hx2 hy2 hx1 hy1 hxy hc)
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact hx
  · exact hy

theorem semidihedral_no_cyclic_four_of_simple (hsimple : SimpleFixedInvolutionPair) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (a : G),
      Open.IsQuasisimple L → HasSemidihedralSylowTwo L →
      a ∈ Subgroup.normalizer (L : Set G) → a ^ 2 = 1 →
      ∀ P : Sylow 2 ↥(L ⊓ Subgroup.centralizer ({a} : Set G)),
        ¬ (IsCyclic (P : Subgroup ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) ∧
          Nat.card P = 4) := by
  rintro G _ _ L a hq hLs haN ha2 P ⟨hPc, -⟩
  obtain ⟨x, y, hx, hy, hx2, hy2, hx1, hy1, hxy, hc⟩ :=
    exists_fixed_involution_pair hsimple hq hLs haN ha2
  exact FactsL2.not_isCyclic_sylow_of_commuting_involutions (u := ⟨x, hx⟩) (w := ⟨y, hy⟩)
    (Subtype.ext (by simpa using hx2)) (Subtype.ext (by simpa using hy2))
    (fun h => hx1 (by simpa using congrArg Subtype.val h))
    (fun h => hy1 (by simpa using congrArg Subtype.val h))
    (fun h => hxy (by simpa using congrArg Subtype.val h))
    (Subtype.ext (by simpa using hc)) P hPc

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsSD
