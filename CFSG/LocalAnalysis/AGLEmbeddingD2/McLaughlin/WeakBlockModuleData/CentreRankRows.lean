module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentrePLSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open

theorem perm4_inverting :
    ∀ g : Equiv.Perm (Fin 4), g ^ 3 = 1 → g ≠ 1 → ∃ s : Equiv.Perm (Fin 4), s * g * s⁻¹ = g⁻¹ := by
  decide +kernel

theorem perm4_pow_nine : ∀ g : Equiv.Perm (Fin 4), g ^ 9 = 1 → g ^ 3 = 1 := by
  decide +kernel

theorem two_le_pRank_of_S4_extension {X : Type} [Group X] [Finite X] (P : Subgroup X)
    (hc3 : Nat.card (Subgroup.center X) = 3) (hZP : Subgroup.center X ≤ P)
    (e : P.map (QuotientGroup.mk' (Subgroup.center X)) ≃* Equiv.Perm (Fin 4)) :
    2 ≤ Open.pRank 3 P := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  set Z := Subgroup.center X with hZ
  set π := QuotientGroup.mk' Z with hπ
  have hZ3 : ∀ w ∈ Z, w ^ 3 = 1 := by
    intro w hw
    have := pow_card_eq_one' (G := Z) (x := ⟨w, hw⟩)
    rw [hc3] at this
    exact congrArg Subtype.val this
  have key : ∀ x ∈ P, π x ^ 3 = 1 → x ^ 3 = 1 := by
    intro x hx hx3
    by_cases hx1 : π x = 1
    · exact hZ3 x ((QuotientGroup.eq_one_iff x).mp hx1)
    · by_contra hne
      set u : ↥(P.map π) := ⟨π x, Subgroup.mem_map_of_mem _ hx⟩ with hu
      have hu3 : e u ^ 3 = 1 := by
        rw [← map_pow]
        have : u ^ 3 = 1 := Subtype.ext hx3
        rw [this, map_one]
      have hu1 : e u ≠ 1 := fun h => hx1 (by
        have := e.injective (h.trans (map_one e).symm)
        exact congrArg Subtype.val this)
      obtain ⟨s, hs⟩ := perm4_inverting (e u) hu3 hu1
      obtain ⟨t, htP, hπt⟩ := Subgroup.mem_map.mp (e.symm s).2
      have hconj : e.symm s * u * (e.symm s)⁻¹ = u⁻¹ := by
        have := congrArg e.symm hs
        simpa [map_mul, map_inv] using this
      have hq : π (t * x * t⁻¹) = π x⁻¹ := by
        have := congrArg Subtype.val hconj
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        rw [map_mul, map_mul, map_inv, hπt, map_inv]
        exact this
      set w := t * x * t⁻¹ * x with hw
      have hwZ : w ∈ Z := by
        refine (QuotientGroup.eq_one_iff w).mp ?_
        show π w = 1
        rw [hw, map_mul, hq, map_inv, inv_mul_cancel]
      have hx3Z : x ^ 3 ∈ Z := by
        refine (QuotientGroup.eq_one_iff (x ^ 3)).mp ?_
        show π (x ^ 3) = 1
        rw [map_pow]
        exact hx3
      have htx : t * x * t⁻¹ = w * x⁻¹ := by
        rw [hw]; group
      have hc1 : t * x ^ 3 * t⁻¹ = x ^ 3 := by
        have := Subgroup.mem_center_iff.mp hx3Z t
        rw [this]
        group
      have hc2 : t * x ^ 3 * t⁻¹ = (t * x * t⁻¹) ^ 3 := by
        rw [conj_pow]
      have hcomm : Commute w x⁻¹ := (Subgroup.mem_center_iff.mp hwZ x⁻¹).symm
      have h6 : x ^ 3 = (x⁻¹) ^ 3 := by
        rw [← hc1, hc2, htx, hcomm.mul_pow, hZ3 w hwZ, one_mul]
      have h9 : (x ^ 3) ^ 3 = 1 := hZ3 _ hx3Z
      apply hne
      have h6' : x ^ 3 * x ^ 3 = 1 := by
        nth_rewrite 2 [h6]
        rw [inv_pow, mul_inv_cancel]
      calc x ^ 3 = x ^ 3 * (x ^ 3 * x ^ 3) := by rw [h6', mul_one]
        _ = (x ^ 3) ^ 3 := by group
        _ = 1 := h9
  have hcardP : Nat.card P = 72 := by
    let φ : P →* X ⧸ Z := π.comp P.subtype
    have hrange : φ.range = P.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : φ.ker = Z.subgroupOf P := by
      ext y
      simp [φ, hπ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 : Nat.card (P ⧸ φ.ker) = 24 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      have : Nat.card φ.range = Nat.card (P.map π) := by rw [hrange]
      rw [this, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    have h3 : Nat.card φ.ker = 3 := by
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hc3]
    rw [h1, h2, h3]
  obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 3 (n := 2)
    (by rw [hcardP]; norm_num)
  set E : Subgroup X := R.map P.subtype with hE
  have hEP : E ≤ P := Subgroup.map_subtype_le R
  have hEcard : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective P.subtype_injective, hR]
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    have h9 : (⟨r, hr⟩ : R) ^ 9 = 1 := by
      have := pow_card_eq_one' (G := R) (x := ⟨r, hr⟩)
      rwa [hR] at this
    have h9' : ((r : P) : X) ^ 9 = 1 := by
      have := congrArg (fun y : R => ((y : P) : X)) h9
      simpa using this
    have hπ9 : π ((r : P) : X) ^ 9 = 1 := by rw [← map_pow, h9', map_one]
    set u : ↥(P.map π) := ⟨π ((r : P) : X), Subgroup.mem_map_of_mem _ r.2⟩ with hu
    have hu9 : u ^ 9 = 1 := Subtype.ext hπ9
    have h39 : e u ^ 3 = 1 := by
      apply perm4_pow_nine
      rw [← map_pow, hu9, map_one]
    have hu3 : u ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, h39, map_one]
    exact key _ r.2 (congrArg Subtype.val hu3)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := R)
      (by rw [hR])).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun y : R => ((y : P) : X)) this
  have hEA : IsElemAbelian 3 E :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, hexp⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.le_pRank_of_elemAbelian_card (p := 3) hEP hEA hEcard

theorem perm_central_pow_three_eq_one {n : ℕ} (ζ : Equiv.Perm (Fin n)) (h3 : ζ ^ 3 = 1)
    (hc : ∀ σ : Equiv.Perm (Fin n), σ * ζ = ζ * σ) : ζ = 1 := by
  by_cases hn : 3 ≤ n
  · by_contra hne
    obtain ⟨a, ha⟩ : ∃ a, ζ a ≠ a := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    obtain ⟨c, hc1, hc2⟩ : ∃ c : Fin n, c ≠ a ∧ c ≠ ζ a := by
      have hcard : ({a, ζ a} : Finset (Fin n)).card < Fintype.card (Fin n) := by
        rw [Fintype.card_fin]
        have := Finset.card_le_two (a := a) (b := ζ a)
        omega
      obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
      exact ⟨c, hc.1, hc.2⟩
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ a) (hc (Equiv.swap a c))
    simp only [Equiv.Perm.mul_apply] at this
    rw [Equiv.swap_apply_of_ne_of_ne ha (Ne.symm hc2), Equiv.swap_apply_left] at this
    exact hc1 (ζ.injective this).symm
  · have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl | rfl <;> revert ζ <;> decide

theorem false_of_central_three_perm {Q : Type} [Group Q] [Finite Q] (P : Subgroup Q) (z : Q)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hzP : z ∈ P) (hzc : ∀ p ∈ P, p * z = z * p) {n : ℕ}
    (e : P ⧸ CFSG.pCore 2 P ≃* Equiv.Perm (Fin n)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z' : P := ⟨z, hzP⟩ with hz'
  have hz'3 : z' ^ 3 = 1 := Subtype.ext hz3
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hord : orderOf z' = 3 := orderOf_eq_prime hz'3 hz'1
  set ζ := e (QuotientGroup.mk z') with hζ
  have hζ3 : ζ ^ 3 = 1 := by
    rw [hζ, ← map_pow, ← QuotientGroup.mk_pow, hz'3, QuotientGroup.mk_one, map_one]
  have hζc : ∀ σ : Equiv.Perm (Fin n), σ * ζ = ζ * σ := by
    intro σ
    obtain ⟨q, rfl⟩ := e.surjective σ
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hζ, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext (hzc p p.2)
  have hζ1 := perm_central_pow_three_eq_one ζ hζ3 hζc
  have hmk : (QuotientGroup.mk z' : P ⧸ CFSG.pCore 2 P) = 1 := by
    apply e.injective
    rw [← hζ, hζ1, map_one]
  have hmem : z' ∈ CFSG.pCore 2 P := (QuotientGroup.eq_one_iff z').mp hmk
  have hpg : IsPGroup 2 (CFSG.pCore 2 P) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hpg) ⟨z', hmem⟩
  have : orderOf (⟨z', hmem⟩ : CFSG.pCore 2 P) = orderOf z' := Subgroup.orderOf_mk _ _
  rw [this, hord] at hk
  have h2 : 2 ∣ 3 := by
    rw [hk]
    exact dvd_pow_self 2 (by rintro rfl; norm_num at hk)
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactBlockCentreRankTwoTypeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeTwo M S L → BlockPLThreeSolv M S L →
    (NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) →
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    2 ≤ Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G) ⊓ L))

theorem kFactBlockCentreRankTwo_of_typeTwo (h2 : KFactBlockCentreRankTwoTypeTwo) :
    KFactBlockCentreRankTwo := by
  intro G _ _ M S L hL hconc hnot hSyl hsolv hZP hZ h9
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have hperfX : commutator ↥(barM M L) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect))
  have hnt : Nontrivial ↥(barM M L) := by
    haveI := hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
  have hcard := card_inf_centralizer_eq_card_center (barM M L)
  have hcentreless : Subgroup.center ↥(barM M L) = ⊥ → False := fun h => by
    apply (absurd hZ)
    rw [hcard, h, Subgroup.card_bot]
    norm_num
  rcases hconc with h1 | h2' | h3' | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hnot
  · exact h2 G M S L hL h2' hsolv hSyl hZP hZ h9
  · exfalso
    obtain ⟨-, horth, -⟩ := h3'
    haveI : Group.IsPerfect ↥(barM M L) := ⟨hperfX⟩
    have hnab : ∃ a b : ↥(barM M L), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact Group.IsPerfect.not_isMulCommutative (G := ↥(barM M L)) ⟨⟨fun a b => hcon a b⟩⟩
    exact hcentreless (center_eq_bot_of_isOrthogonalTwo ‹_› hnab horth)
  ·
    obtain ⟨-, hc3, ⟨eY⟩, -, ⟨eS⟩⟩ := h4
    have hPL : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L := barM_mono inf_le_right
    have hZP' : Subgroup.center ↥(barM M L) ≤
        (barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      apply hZP
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      have := Subgroup.mem_center_iff.mp hx ⟨h, hh⟩
      exact congrArg Subtype.val this
    have := two_le_pRank_of_S4_extension _ hc3 hZP' eS
    have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 h3
      (barM M L).subtype (barM M L).subtype_injective
      ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L))
    rw [Subgroup.map_subgroupOf_eq_of_le hPL] at hmap
    omega
  · exfalso
    obtain ⟨-, ⟨e⟩, -⟩ := h5
    exact hcentreless (center_eq_bot_of_alt (by norm_num) e)
  ·
    exfalso
    obtain ⟨-, n, -, ⟨eQ⟩⟩ := h6
    have hPL : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L := barM_mono inf_le_right
    obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) 3 hZ
    have hz3 : (z' : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 3 = 1 := by
      have := pow_orderOf_eq_one z'
      rw [hz'] at this
      exact congrArg Subtype.val this
    have hz1 : (z' : ↥M ⧸ CFSG.pCore 2 ↥M) ≠ 1 := by
      intro h
      have : z' = 1 := Subtype.ext h
      rw [this, orderOf_one] at hz'
      omega
    exact false_of_central_three_perm _ (z' : ↥M ⧸ CFSG.pCore 2 ↥M) hz3 hz1 (hZP z'.2)
      (fun p hp => (Subgroup.mem_centralizer_iff.mp z'.2.2 p (hPL hp)))  eQ
  · exfalso
    obtain ⟨-, n, ⟨e⟩, -⟩ := h7
    exact hcentreless (center_eq_bot_of_alt (by have := five_le_of_perfect_alt hperfX e; omega) e)
  · exfalso
    obtain ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩ := h8
    exact hcentreless (center_eq_bot_of_alt (by have := five_le_of_perfect_alt hperfX e; omega) e)

end CFSG.AGLEmbeddingD2.McLaughlin
