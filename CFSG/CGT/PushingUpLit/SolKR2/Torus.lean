module

public import CFSG.RankThree.GF2n.Tim78S31Split
public import CFSG.CGT.PushingUpLit.T2KR.TorusPair
public import CFSG.CGT.Timmesfeld75.Sec3OddSubgroup

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

section Squares

theorem exists_mul_self_eq_of_mem_omegaOneSub {U : Subgroup G}
    (hc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hexp : ∀ x ∈ U, x ^ 4 = 1)
    (h16 : Nat.card ↥U = 16) (h4 : Nat.card ↥(PartTwo.omegaOneSub U) = 4) :
    ∀ w ∈ PartTwo.omegaOneSub U, ∃ s ∈ U, s * s = w := by
  let φ : ↥U →* ↥(PartTwo.omegaOneSub U) :=
    { toFun := fun u => ⟨(u : G) * u, by
        rw [mem_omegaOneSub_iff hc]
        refine ⟨U.mul_mem u.2 u.2, ?_⟩
        calc (u : G) * u * ((u : G) * u) = (u : G) ^ 4 := by
              rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
          _ = 1 := hexp u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show ((a * b : ↥U) : G) * ((a * b : ↥U) : G) = ((a : G) * a) * ((b : G) * b)
        rw [Subgroup.coe_mul]
        have hab := hc a a.2 b b.2
        calc (a : G) * b * ((a : G) * b) = (a : G) * (b * a) * b := by group
          _ = (a : G) * (a * b) * b := by rw [← hab]
          _ = ((a : G) * a) * ((b : G) * b) := by group) }
  have hker : φ.ker = (PartTwo.omegaOneSub U).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_omegaOneSub_iff hc]
    constructor
    · intro h
      exact ⟨u.2, congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (PartTwo.omegaOneSub_le U)).toEquiv, h4,
    h16] at h1
  have hrange : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [h4]
    omega
  intro w hw
  obtain ⟨s, hs⟩ : (⟨w, hw⟩ : ↥(PartTwo.omegaOneSub U)) ∈ φ.range := by
    rw [hrange]
    trivial
  exact ⟨s, s.2, congrArg Subtype.val hs⟩

end Squares

section Quotient

variable {X N : Subgroup G} [hN : (N.subgroupOf X).Normal]

omit [Finite G] in
theorem exists_eq_mul_of_mk_mem_map {W : Subgroup G} {y : G} (hy : y ∈ X)
    (h : QuotientGroup.mk' (N.subgroupOf X) ⟨y, hy⟩ ∈
      (W.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) :
    ∃ w ∈ W, ∃ n ∈ N, y = w * n := by
  obtain ⟨z, hz, hzy⟩ := h
  have h1 : (z : G)⁻¹ * y ∈ N := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hzy)
  exact ⟨z, Subgroup.mem_subgroupOf.1 hz, _, h1, by group⟩

omit [Finite G] in
theorem mk_mem_conjSubgroup_map {W : Subgroup G} {t y : G} (ht : t ∈ X) (hy : y ∈ X)
    (hyt : y ∈ conjSubgroup t W) :
    QuotientGroup.mk' (N.subgroupOf X) ⟨y, hy⟩ ∈
      conjSubgroup (QuotientGroup.mk' (N.subgroupOf X) ⟨t, ht⟩)
        ((W.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) := by
  rw [← map_conjSubgroup, conjSubgroup_subgroupOf]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hyt)

omit [Finite G] in
theorem mem_normalizer_of_mk_mem_normalizer {W : Subgroup G} (hWX : W ≤ X)
    (hcl : ∀ k ∈ X, conjSubgroup k W ≤ W ⊔ N → conjSubgroup k W = W) {k : G} (hk : k ∈ X)
    (h : QuotientGroup.mk' (N.subgroupOf X) ⟨k, hk⟩ ∈ Subgroup.normalizer
      (((W.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) :
        Subgroup (↥X ⧸ N.subgroupOf X)) : Set (↥X ⧸ N.subgroupOf X))) :
    k ∈ Subgroup.normalizer (W : Set G) := by
  refine mem_normalizer_of_conjSubgroup_eq (hcl k hk fun y hy => ?_)
  have hyX : y ∈ X := conjSubgroup_le_of_le_of_mem hWX hk hy
  have h1 := mk_mem_conjSubgroup_map (N := N) hk hyX hy
  rw [mem_normalizer_iff_conjSubgroup_eq.1 h] at h1
  obtain ⟨w, hw, n, hn, rfl⟩ := exists_eq_mul_of_mk_mem_map hyX h1
  exact Subgroup.mul_mem_sup hw hn

omit [Finite G] in
theorem mem_of_commutator_mem_of_isL2Pair {W W₀ : Subgroup G} (hWX : W ≤ X)
    (hW₀ : ∀ s ∈ W, s ∈ N → s ∈ W₀)
    (hL : IsL2Pair (↥X ⧸ N.subgroupOf X)
      ((W.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) 4)
    {k : G} (hk : k ∈ X) (hk3 : QuotientGroup.mk' (N.subgroupOf X) ⟨k, hk⟩ ^ 3 = 1)
    (hk1 : QuotientGroup.mk' (N.subgroupOf X) ⟨k, hk⟩ ≠ 1) {s : G} (hs : s ∈ W)
    (hks : k * s * k⁻¹ * s⁻¹ ∈ N) : s ∈ W₀ := by
  by_contra hs0
  have hsX : s ∈ X := hWX hs
  set π := QuotientGroup.mk' (N.subgroupOf X) with hπ
  have hsW : π ⟨s, hsX⟩ ∈ (W.subgroupOf X).map π :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  have hs1 : π ⟨s, hsX⟩ ≠ 1 := fun h1 =>
    hs0 (hW₀ s hs (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)))
  have hcomm : π ⟨k, hk⟩ * π ⟨s, hsX⟩ = π ⟨s, hsX⟩ * π ⟨k, hk⟩ := by
    have h1 : (⟨k, hk⟩ * ⟨s, hsX⟩ * ⟨k, hk⟩⁻¹ * ⟨s, hsX⟩⁻¹ : ↥X) ∈ N.subgroupOf X :=
      Subgroup.mem_subgroupOf.2 hks
    have h2 : π (⟨k, hk⟩ * ⟨s, hsX⟩ * ⟨k, hk⟩⁻¹ * ⟨s, hsX⟩⁻¹ : ↥X) = 1 :=
      (QuotientGroup.eq_one_iff _).2 h1
    simp only [map_mul, map_inv] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  have hcent : π ⟨k, hk⟩ ∈ Subgroup.centralizer ({π ⟨s, hsX⟩} : Set (↥X ⧸ N.subgroupOf X)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcomm
  rw [hL.centralizer_eq hsW hs1] at hcent
  have h4 : (⟨π ⟨k, hk⟩, hcent⟩ : ↥((W.subgroupOf X).map π)) ^
      Nat.card ↥((W.subgroupOf X).map π) = 1 := pow_card_eq_one'
  rw [hL.card_eq] at h4
  have h4' : π ⟨k, hk⟩ ^ 4 = 1 := congrArg Subtype.val h4
  rw [pow_succ, hk3, one_mul] at h4'
  exact hk1 h4'

end Quotient

omit [Finite G] in
theorem eq_one_of_fixed_of_squares {W N : Subgroup G}
    (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hWN : PartTwo.omegaOneSub W ≤ N)
    (hsq : ∀ w ∈ PartTwo.omegaOneSub W, ∃ s ∈ W, s * s = w) {k : G}
    (hkW : ∀ s ∈ W, k * s * k⁻¹ ∈ W)
    (hq : ∀ s ∈ W, k * s * k⁻¹ * s⁻¹ ∈ N → s ∈ PartTwo.omegaOneSub W) {w : G}
    (hw : w ∈ PartTwo.omegaOneSub W) (hkw : k * w * k⁻¹ = w) : w = 1 := by
  obtain ⟨s, hs, rfl⟩ := hsq w hw
  have hks : k * s * k⁻¹ ∈ W := hkW s hs
  have hcm : k * s * k⁻¹ * s⁻¹ ∈ PartTwo.omegaOneSub W := by
    rw [mem_omegaOneSub_iff hc]
    refine ⟨W.mul_mem hks (W.inv_mem hs), ?_⟩
    have hcomm := hc _ hks _ (W.inv_mem hs)
    calc k * s * k⁻¹ * s⁻¹ * (k * s * k⁻¹ * s⁻¹)
        = (k * s * k⁻¹) * (s⁻¹ * (k * s * k⁻¹)) * s⁻¹ := by group
      _ = (k * s * k⁻¹) * ((k * s * k⁻¹) * s⁻¹) * s⁻¹ := by rw [← hcomm]
      _ = k * (s * s) * k⁻¹ * (s * s)⁻¹ := by group
      _ = 1 := by rw [hkw]; group
  have hsW := hq s hs (hWN hcm)
  exact ((mem_omegaOneSub_iff hc).1 hsW).2


section Cert

open CFSG.CGT.PushingUpLit.T2KR (l2Pair_exists_twoPoint_torus)
open scoped MatrixGroups


theorem NCPair.exists_torus {U V : Subgroup G} (P : NCPair U V) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (h16 : Nat.card ↥U = 16)
    (h4 : Nat.card ↥(PartTwo.omegaOneSub U) = 4) :
    ∃ K : Subgroup G, K ≤ U ⊔ V ∧ Nat.card ↥K = 3 ∧
      K ≤ Subgroup.normalizer (U : Set G) ∧ K ≤ Subgroup.normalizer (V : Set G) ∧
      (∀ k ∈ K, k ≠ 1 → ∀ w ∈ PartTwo.omegaOneSub V, k * w * k⁻¹ = w → w = 1) ∧
      (∀ k ∈ K, k ≠ 1 → ∀ w ∈ PartTwo.omegaOneSub U, k * w * k⁻¹ = w → w = 1) ∧
      (∀ k ∈ K, k ≠ 1 → ∀ s ∈ U,
        k * s * k⁻¹ * s⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V →
          s ∈ PartTwo.omegaOneSub U) ∧
      (∀ k ∈ K, k ≠ 1 → ∀ s ∈ V,
        k * s * k⁻¹ * s⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V →
          s ∈ PartTwo.omegaOneSub V) := by
  classical
  have hNn : ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf (U ⊔ V)).Normal :=
    P.normal hCen hU
  have hUV : U ≤ U ⊔ V := le_sup_left
  have hVU : V ≤ U ⊔ V := le_sup_right
  obtain ⟨x₀, hx₀, hV⟩ := P.exists_conj hCen hU
  have hcU := P.setup.comm
  have hcV := P.setup.comm₁
  have h16V : Nat.card ↥V = 16 := by rw [hV, card_conjSubgroup, h16]
  have h4V : Nat.card ↥(PartTwo.omegaOneSub V) = 4 := by
    rw [hV, omegaOneSub_conj hcU, card_conjSubgroup, h4]
  have hrel : (PartTwo.omegaOneSub U).relIndex U = 4 := by
    have h1 := Subgroup.card_mul_index ((PartTwo.omegaOneSub U).subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (PartTwo.omegaOneSub_le U)).toEquiv, h4,
      h16] at h1
    unfold Subgroup.relIndex
    omega
  obtain ⟨e⟩ : Nonempty (↥(U ⊔ V) ⧸
      (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf (U ⊔ V) ≃*
        PSL(2, GaloisField 2 2)) := by
    rcases tim78_2_10_b hCen hU P.setup P.exp with hc | ⟨hN', hf | hsz | hdih⟩
    · exact absurd hc P.ncomm
    · obtain ⟨f, -, hfr, he⟩ := hf
      have hf2 : f = 2 := by
        have h2 : 2 ^ f = 2 ^ 2 := by
          calc 2 ^ f = (PartTwo.omegaOneSub U).relIndex U := hfr.symm
            _ = 4 := hrel
            _ = 2 ^ 2 := by norm_num
        exact Nat.pow_right_injective (le_refl 2) h2
      subst hf2
      exact he
    · obtain ⟨a, -, hfr, -⟩ := hsz
      have h2 : 2 ^ (2 * a + 1) = 2 ^ 2 := by
        calc 2 ^ (2 * a + 1) = (PartTwo.omegaOneSub U).relIndex U := hfr.symm
          _ = 4 := hrel
          _ = 2 ^ 2 := by norm_num
      have := Nat.pow_right_injective (le_refl 2) h2
      omega
    · obtain ⟨m, -, -, hfr, -⟩ := hdih
      omega
  have hUN : U ⊓ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) = PartTwo.omegaOneSub U := by
    refine le_antisymm (fun x hx => ?_) (le_inf (PartTwo.omegaOneSub_le U) le_sup_left)
    obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
    exact P.mem_U₀_of_mem_N hCen hU hxU hxN
  have hVN : V ⊓ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) = PartTwo.omegaOneSub V := by
    refine le_antisymm (fun x hx => ?_) (le_inf (PartTwo.omegaOneSub_le V) le_sup_right)
    obtain ⟨hxV, hxN⟩ := Subgroup.mem_inf.1 hx
    rw [sup_comm] at hxN
    exact P.symm.mem_U₀_of_mem_N hCen hU hxV hxN
  have hUb : Nat.card ↥((U.subgroupOf (U ⊔ V)).map (QuotientGroup.mk'
      ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf (U ⊔ V)))) = 4 := by
    have h1 := card_map_mk_mul (X := U ⊔ V) (H := U)
      (N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) hUV
    rw [hUN, h4, h16] at h1
    omega
  have hUb2 : IsPGroup 2 ↥((U.subgroupOf (U ⊔ V)).map (QuotientGroup.mk'
      ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf (U ⊔ V)))) :=
    P.setup.two.comap_subtype.map _
  obtain ⟨Q₂, hQ₂⟩ := hUb2.exists_le_sylow
  have hL₂ := IsL2Pair.of_psl_sylow (by norm_num : (2 : ℕ) ≠ 0) ⟨e⟩ Q₂
  have hUbeq : (U.subgroupOf (U ⊔ V)).map (QuotientGroup.mk'
      ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf (U ⊔ V))) =
        (Q₂ : Subgroup _) :=
    Subgroup.eq_of_le_of_card_ge hQ₂ (by rw [hUb, hL₂.card_eq]; norm_num)
  have hL : IsL2Pair (↥(U ⊔ V) ⧸ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf
      (U ⊔ V)) ((U.subgroupOf (U ⊔ V)).map (QuotientGroup.mk'
      ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf (U ⊔ V)))) 4 := by
    rw [hUbeq]
    exact hL₂
  set π := QuotientGroup.mk' ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf (U ⊔ V))
    with hπ
  have hconj : conjSubgroup (π ⟨x₀, hx₀⟩) ((U.subgroupOf (U ⊔ V)).map π) =
      (V.subgroupOf (U ⊔ V)).map π := by
    rw [← map_conjSubgroup, conjSubgroup_subgroupOf, ← hV]
  have hLV : IsL2Pair (↥(U ⊔ V) ⧸ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf
      (U ⊔ V)) ((V.subgroupOf (U ⊔ V)).map π) 4 := by
    rw [← hconj]
    exact hL.conj _
  have hne : conjSubgroup (π ⟨x₀, hx₀⟩) ((U.subgroupOf (U ⊔ V)).map π) ≠
      (U.subgroupOf (U ⊔ V)).map π := by
    rw [hconj]
    intro heq
    have hle : conjSubgroup x₀ U ≤
        conjSubgroup 1 U ⊔ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) := by
      rw [← hV, conjSubgroup_one]
      intro y hy
      have hyX : y ∈ U ⊔ V := hVU hy
      have hmem : π ⟨y, hyX⟩ ∈ (U.subgroupOf (U ⊔ V)).map π := by
        rw [← heq]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy)
      obtain ⟨u, hu, n, hn, rfl⟩ := exists_eq_mul_of_mk_mem_map hyX hmem
      exact Subgroup.mul_mem_sup hu hn
    have h1 := P.eq_of_le_sup hCen hU hx₀ (Subgroup.one_mem _) hle
    rw [conjSubgroup_one, ← hV] at h1
    exact P.ne h1.symm
  obtain ⟨Hb, hHbU, hHbV, hHbcard⟩ := l2Pair_exists_twoPoint_torus hL hne
  have hHb3 : Nat.card ↥Hb = 3 := by rw [hHbcard]
  have hN2 : IsPGroup 2 ↥(PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :=
    fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, sq]
      exact P.sq_N hCen hU g.2)⟩
  obtain ⟨K₀, hK₀card, hK₀H, hK₀1⟩ :=
    osg_exists_lift ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf (U ⊔ V))
      hN2.comap_subtype Hb (by rw [hHb3]; exact ⟨1, by norm_num⟩)
  have hπk3 : ∀ y ∈ K₀, π y ^ 3 = 1 := fun y hy => by
    have h := pow_card_eq_one' (G := ↥Hb) (x := (⟨π y, hK₀H y hy⟩ : ↥Hb))
    rw [hHb3] at h
    exact congrArg Subtype.val h
  have hπk1 : ∀ y ∈ K₀, y ≠ 1 → π y ≠ 1 := fun y hy hy1 h1 => hy1 (hK₀1 y hy h1)
  have hclU : ∀ k ∈ U ⊔ V,
      conjSubgroup k U ≤ U ⊔ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) →
        conjSubgroup k U = U := fun k hk hle => by
    have h1 := P.eq_of_le_sup hCen hU hk (Subgroup.one_mem _) (by rwa [conjSubgroup_one])
    rwa [conjSubgroup_one] at h1
  have hclV : ∀ k ∈ U ⊔ V,
      conjSubgroup k V ≤ V ⊔ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) →
        conjSubgroup k V = V := fun k hk hle => by
    have e1 : conjSubgroup k V = conjSubgroup (k * x₀) U := by
      rw [hV, conjSubgroup_conjSubgroup]
    have hle' : conjSubgroup (k * x₀) U ≤
        conjSubgroup x₀ U ⊔ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) := by
      rw [← e1, ← hV]
      exact hle
    have h1 := P.eq_of_le_sup hCen hU ((U ⊔ V).mul_mem hk hx₀) hx₀ hle'
    rw [e1, h1, ← hV]
  have hnU : ∀ y ∈ K₀, (y : G) ∈ Subgroup.normalizer (U : Set G) := fun y hy =>
    mem_normalizer_of_mk_mem_normalizer (X := U ⊔ V)
      (N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) hUV hclU y.2 (hHbU (hK₀H y hy))
  have hnV : ∀ y ∈ K₀, (y : G) ∈ Subgroup.normalizer (V : Set G) := fun y hy =>
    mem_normalizer_of_mk_mem_normalizer (X := U ⊔ V)
      (N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) hVU hclV y.2
      (by have := hHbV (hK₀H y hy); rwa [hconj] at this)
  have hqU : ∀ y ∈ K₀, y ≠ 1 → ∀ s ∈ U,
      (y : G) * s * (y : G)⁻¹ * s⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V →
        s ∈ PartTwo.omegaOneSub U := fun y hy hy1 s hs hks =>
    mem_of_commutator_mem_of_isL2Pair (X := U ⊔ V)
      (N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) (W := U)
      (W₀ := PartTwo.omegaOneSub U) hUV
      (fun s hs hsN => by rw [← hUN]; exact Subgroup.mem_inf.2 ⟨hs, hsN⟩) hL y.2 (hπk3 y hy)
      (hπk1 y hy hy1) hs hks
  have hqV : ∀ y ∈ K₀, y ≠ 1 → ∀ s ∈ V,
      (y : G) * s * (y : G)⁻¹ * s⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V →
        s ∈ PartTwo.omegaOneSub V := fun y hy hy1 s hs hks =>
    mem_of_commutator_mem_of_isL2Pair (X := U ⊔ V)
      (N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) (W := V)
      (W₀ := PartTwo.omegaOneSub V) hVU
      (fun s hs hsN => by rw [← hVN]; exact Subgroup.mem_inf.2 ⟨hs, hsN⟩) hLV y.2 (hπk3 y hy)
      (hπk1 y hy hy1) hs hks
  have hsqU := exists_mul_self_eq_of_mem_omegaOneSub hcU P.exp h16 h4
  have hsqV := exists_mul_self_eq_of_mem_omegaOneSub hcV P.exp₁ h16V h4V
  refine ⟨K₀.map (U ⊔ V).subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK₀card, hHb3]
  · rintro _ ⟨y, hy, rfl⟩
    exact hnU y hy
  · rintro _ ⟨y, hy, rfl⟩
    exact hnV y hy
  · rintro _ ⟨y, hy, rfl⟩ hy1 w hw hyw
    have hy1' : y ≠ 1 := fun h => hy1 (by rw [h]; rfl)
    exact eq_one_of_fixed_of_squares hcV le_sup_right hsqV
      (fun s hs => (Subgroup.mem_normalizer_iff.1 (hnV y hy) s).1 hs)
      (fun s hs hks => hqV y hy hy1' s hs hks) hw hyw
  · rintro _ ⟨y, hy, rfl⟩ hy1 w hw hyw
    have hy1' : y ≠ 1 := fun h => hy1 (by rw [h]; rfl)
    exact eq_one_of_fixed_of_squares hcU le_sup_left hsqU
      (fun s hs => (Subgroup.mem_normalizer_iff.1 (hnU y hy) s).1 hs)
      (fun s hs hks => hqU y hy hy1' s hs hks) hw hyw
  · rintro _ ⟨y, hy, rfl⟩ hy1 s hs hks
    have hy1' : y ≠ 1 := fun h => hy1 (by rw [h]; rfl)
    exact hqU y hy hy1' s hs hks
  · rintro _ ⟨y, hy, rfl⟩ hy1 s hs hks
    have hy1' : y ≠ 1 := fun h => hy1 (by rw [h]; rfl)
    exact hqV y hy hy1' s hs hks

end Cert

end CFSG.RankThree.GF2n.Tim78
