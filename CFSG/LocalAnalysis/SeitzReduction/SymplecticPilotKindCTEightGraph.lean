module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTOddParam

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {m ε : ℕ} {e : L ≃* StatedSp (m + 1) K}

omit [Finite K] in
theorem ctEmbed_spEmbed_mem_q2Block_eps (k : Fin (m + 1)) (y : StatedSp m K) :
    ctEmbed ε (spEmbed k.succAbove Fin.succAbove_right_injective y) ∈
      q2Block ε K ({k} : Finset (Fin (m + 1))) := by
  rw [ctEmbed_mem_q2Block_iff, spBlock_compl_singleton, complSp_eq_range_spEmbed]
  exact ⟨y, rfl⟩

omit [Finite G] in
theorem CtLinParam.exists_mulAut_conj (hK : 4 ≤ Nat.card K) {k : Fin (m + 1)}
    (P : CtLinParam ε e k)
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* q2Block ε K {k}),
      Function.Surjective π' → π'.ker ≤ center E' →
        ∃ s : q2Block ε K {k} →* E', ∀ g, π' (s g) = g)
    (hperf : ⁅q2Block ε K {k}, q2Block ε K {k}⁆ = q2Block ε K {k})
    {t : G} (htC : t ∈ centralizer (L : Set G)) :
    ∃ θ : MulAut (q2Block ε K {k}), (∀ x, t * P.Φ x * t⁻¹ = P.Φ (θ x)) ∧
      ∀ y : StatedSp m K,
        θ ⟨ctEmbed ε (spEmbed k.succAbove Fin.succAbove_right_injective y),
            ctEmbed_spEmbed_mem_q2Block_eps k y⟩ =
          ⟨ctEmbed ε (spEmbed k.succAbove Fin.succAbove_right_injective y),
            ctEmbed_spEmbed_mem_q2Block_eps k y⟩ := by
  set E : Subgroup G := neighbourCore e k with hE
  have hN : t ∈ normalizer (E : Set G) := le_normalizer_neighbourCore e htC k
  have hmemE : ∀ x, P.Φ x ∈ E := fun x => by
    rw [hE, ← P.range_eq]
    exact ⟨x, rfl⟩
  set Φ' : q2Block ε K {k} →* E := P.Φ.codRestrict E hmemE with hΦ'
  have hΦ'v : ∀ x, (Φ' x : G) = P.Φ x := fun x => rfl
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [hE, ← P.range_eq] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hkerΦ' : Φ'.ker ≤ center (q2Block ε K {k}) := by
    intro x hx
    apply P.ker_le
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [← hΦ'v, hx]
    rfl
  set c : MulAut E := E.normalizerMonoidHom ⟨t, hN⟩ with hc
  have hcv : ∀ y : E, ((c y : E) : G) = t * y * t⁻¹ := fun y => rfl
  set χ : q2Block ε K {k} →* E := c.toMonoidHom.comp Φ' with hχ
  have hχs : Function.Surjective χ := c.surjective.comp hΦ's
  have : Group.IsPerfect (q2Block ε K {k}) :=
    (Subgroup.isPerfect_iff (H := q2Block ε K {k})).2 hperf
  obtain ⟨θ₀, hθ₀s, hθ₀⟩ := F4Pilot.exists_lift_of_central χ hχs hsplit Φ' hΦ's hkerΦ'
  have hθ₀i : Function.Injective θ₀ := Finite.injective_iff_surjective.2 hθ₀s
  have hconj : ∀ x, t * P.Φ x * t⁻¹ = P.Φ (θ₀ x) := by
    intro x
    have h1 := congrArg Subtype.val (hθ₀ x)
    rw [hΦ'v] at h1
    rw [h1]
    rfl
  refine ⟨MulEquiv.ofBijective θ₀ ⟨hθ₀i, hθ₀s⟩, hconj, fun y => ?_⟩
  have : Group.IsPerfect (StatedSp m K) := isPerfect_statedSp_of_four_le hK m
  set ιB : StatedSp m K →* q2Block ε K ({k} : Finset (Fin (m + 1))) :=
    ((ctEmbed ε).comp (spEmbed k.succAbove Fin.succAbove_right_injective)).codRestrict _
      (ctEmbed_spEmbed_mem_q2Block_eps k) with hιB
  have heq : θ₀.comp ιB = ιB := by
    refine LinearPilot.eq_of_comp_eq_of_ker_le_center (S := StatedSp m K) hkerΦ' fun x => ?_
    apply Subtype.ext
    have hx : spEmbed k.succAbove Fin.succAbove_right_injective x ∈
        spBlock K ({k} : Finset (Fin (m + 1)))ᶜ := by
      rw [spBlock_compl_singleton, complSp_eq_range_spEmbed]
      exact ⟨x, rfl⟩
    have hN1 : P.Φ (ιB x) = ((e.symm (spEmbed k.succAbove Fin.succAbove_right_injective x) :
        L) : G) := P.N1 _ hx
    rw [MonoidHom.comp_apply, hΦ'v, ← hconj, hΦ'v, hN1]
    have hL : ((e.symm (spEmbed k.succAbove Fin.succAbove_right_injective x) : L) : G) ∈ L :=
      (e.symm _).2
    rw [← mem_centralizer_iff.1 htC _ hL, mul_inv_cancel_right]
  exact congrArg (fun F : StatedSp m K →* q2Block ε K ({k} : Finset (Fin (m + 1))) => F y) heq

end Lift

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem q2Block_zero_exists_section {m : ℕ} (hm : 3 ≤ m) (k : Fin (m + 1)) :
    ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* q2Block 0 K ({k} : Finset (Fin (m + 1)))),
      Function.Surjective π' → π'.ker ≤ center E' →
        ∃ s : q2Block 0 K ({k} : Finset (Fin (m + 1))) →* E', ∀ g, π' (s g) = g := by
  obtain ⟨m', hm'⟩ : ∃ m', 2 * m = m' + 1 := ⟨2 * m - 1, by omega⟩
  refine F4Pilot.forall_exists_section_of_mulEquiv
    ((ctNbrSL k).trans (LinearPilot.reindexSpecialLinear (finCongr hm'))) ?_
  intro E' _ _ π' hπ' hcen
  exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_four_le (by omega) hπ'
    hcen

omit [CharP K 2] in
theorem q2Block_one_exists_section {m : ℕ} (hm : 3 ≤ m) (k : Fin (m + 1)) :
    ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* q2Block 1 K ({k} : Finset (Fin (m + 1)))),
      Function.Surjective π' → π'.ker ≤ center E' →
        ∃ s : q2Block 1 K ({k} : Finset (Fin (m + 1))) →* E', ∀ g, π' (s g) = g := by
  refine F4Pilot.forall_exists_section_of_mulEquiv (ctNbrOdd k) ?_
  intro E' _ _ π' hπ' hcen
  exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_four_le (by omega) hπ'
    hcen

omit [Finite K] [CharP K 2] in
theorem card_compl_planeCoordsQ2_singleton {N ε : ℕ} (k : Fin N) :
    ((planeCoordsQ2 ε ({k} : Finset (Fin N)))ᶜ).card = 2 * N + ε - 2 := by
  rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_singleton, Fintype.card_fin]

omit [Finite K] [CharP K 2] in
theorem exists_plane_notMem_singleton {N : ℕ} (hN : 2 ≤ N) (k : Fin N) :
    ∃ p : Fin N, p ∉ ({k} : Finset (Fin N)) := by
  obtain ⟨p, hp⟩ : ({k}ᶜ : Finset (Fin N)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  exact ⟨p, Finset.mem_compl.1 hp⟩

omit [Finite K] in
theorem ctEight_eq_one_of_mul_self_eq_one {u : K} (h : u * u = 1) : u = 1 := by
  rcases mul_self_eq_one_iff.1 h with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

end Model

section Outer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem not_forall_conj_eq_of_linearUnitaryKind {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {κ : Sp2mKind}
    (hκ : IsLinearUnitaryKind κ) (hk : RootKindSp e t f k κ) :
    ¬ ∀ y ∈ neighbourCore e k, t * y * t⁻¹ = y := by
  intro hall
  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K k)) : Set G) :=
    le_normalizer_neighbourCore e htC k
  obtain ⟨S, _, ρ, τ, hρs, -, -, -, -, hρθ, -, hout, -⟩ :=
    exists_surjective_neighbourCore_linearUnitary hset hKc hf hm e htC ht k rfl rfl hκ hk hN
  apply hout
  refine ⟨1, ?_⟩
  ext1 z
  obtain ⟨y, rfl⟩ := hρs z
  have hy : (centralizerPerfectCore (modelToG e (rootTorusSp K k))).normalizerMonoidHom
      ⟨t, hN⟩ y = y := Subtype.ext (hall y y.2)
  rw [map_one, MulAut.one_apply, ← hρθ, hy]

end Outer

section Action

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_ctLinParam_conj_ctGraph {m f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (m + 1)) (hk : RootKindSp e t f k .linearEven) :
    ∃ P : CtLinParam 0 e k, ∀ x, t * P.Φ x * t⁻¹ = P.Φ (ctGraphBlock 0 {k} x) := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨P⟩ := nonempty_ctLinParam_linearEven hset hKc hf hm e htC ht k hk
  have hc := card_compl_planeCoordsQ2_singleton (ε := 0) k
  obtain ⟨θ, hθ, hfix⟩ := P.exists_mulAut_conj hq (q2Block_zero_exists_section hm k)
    (commutator_q2Block_eq (by omega)) htC
  have hfix' : ∀ s ∈ ctSpBlock 0 K ({k} : Finset (Fin (m + 1))), θ s = s := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := mem_ctSpBlock.1 hs
    rw [spBlock_compl_singleton, complSp_eq_range_spEmbed] at hy
    obtain ⟨x, rfl⟩ := hy
    have hs' : s = ⟨ctEmbed 0 (spEmbed k.succAbove Fin.succAbove_right_injective x),
        ctEmbed_spEmbed_mem_q2Block_eps k x⟩ := Subtype.ext hys.symm
    rw [hs']
    exact hfix x
  obtain ⟨p₀, hp₀⟩ := exists_plane_notMem_singleton (by omega) k
  rcases eq_one_or_eq_ctGraphBlock_of_fix (by omega) hp₀ θ hfix' with h1 | h1
  · refine absurd (fun y hy => ?_) (not_forall_conj_eq_of_linearUnitaryKind hset hKc hf
      (by omega) e htC ht k (Or.inl rfl) hk)
    rw [← P.range_eq] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [hθ x, h1, MulAut.one_apply]
  · exact ⟨P, fun x => by rw [hθ x, h1]⟩

theorem exists_ctLinParam_conj_ctTor_ctGraph {m f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (m + 1)) (hk : RootKindSp e t f k .linearOdd) :
    ∃ (P : CtLinParam 1 e k) (a : Kˣ), ∀ x : q2Block 1 K ({k} : Finset (Fin (m + 1))),
      t * P.Φ x * t⁻¹ = P.Φ ⟨ctTorAut a (ctGraph 1 (x : SpecialLinearGroup
        (Fin (2 * (m + 1) + 1)) K)), ctTorAut_mem_q2Block a (ctGraph_mem_q2Block x.2)⟩ := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨P⟩ := nonempty_ctLinParam_linearOdd hset hKc hf hm e htC ht k hk
  have hc := card_compl_planeCoordsQ2_singleton (ε := 1) k
  have hperf := commutator_q2Block_eq (K := K) (ε := 1) (R := ({k} : Finset (Fin (m + 1))))
    (by omega)
  obtain ⟨θ, hθ, hfix⟩ := P.exists_mulAut_conj hq (q2Block_one_exists_section hm k) hperf htC
  have hfix' : ∀ s ∈ ctSpBlock 1 K ({k} : Finset (Fin (m + 1))), θ s = s := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := mem_ctSpBlock.1 hs
    rw [spBlock_compl_singleton, complSp_eq_range_spEmbed] at hy
    obtain ⟨x, rfl⟩ := hy
    have hs' : s = ⟨ctEmbed 1 (spEmbed k.succAbove Fin.succAbove_right_injective x),
        ctEmbed_spEmbed_mem_q2Block_eps k x⟩ := Subtype.ext hys.symm
    rw [hs']
    exact hfix x
  obtain ⟨p₀, hp₀⟩ := exists_plane_notMem_singleton (by omega) k
  obtain ⟨a, h1 | h1⟩ := exists_ctTor_of_fix (by omega) hp₀ θ hfix'
  · exfalso
    have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have : Group.IsPerfect (q2Block 1 K ({k} : Finset (Fin (m + 1)))) :=
      (Subgroup.isPerfect_iff (H := q2Block 1 K ({k} : Finset (Fin (m + 1))))).2 hperf
    have hθθ : (θ * θ).toMonoidHom = MonoidHom.id _ := by
      refine LinearPilot.eq_of_comp_eq_of_ker_le_center P.ker_le fun x => ?_
      rw [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, ← hθ, ← hθ, MonoidHom.id_apply]
      calc t * (t * P.Φ x * t⁻¹) * t⁻¹ = (t * t) * P.Φ x * (t * t)⁻¹ := by group
        _ = P.Φ x := by rw [htt, one_mul, inv_one, mul_one]
    have hpv : q2Coord (m + 1) 1 (Sum.inl (Sum.inl p₀)) ∉ planeCoordsQ2 1 {k} :=
      q2Coord_inl_notMem (Finset.notMem_singleton.1 hp₀) _ rfl
    set x₀ : q2Block 1 K ({k} : Finset (Fin (m + 1))) :=
      ⟨SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p₀)) (1 : K),
        transvection_mem_q2Block _ hpv (q2Coord_inr_notMem 0) 1⟩ with hx₀
    have h2 := congrArg (fun z : q2Block 1 K ({k} : Finset (Fin (m + 1))) =>
      ((z : SpecialLinearGroup (Fin (2 * (m + 1) + 1)) K) :
        Matrix (Fin (2 * (m + 1) + 1)) (Fin (2 * (m + 1) + 1)) K)
          (q2Coord (m + 1) 1 (Sum.inl (Sum.inl p₀))) (ctV (m + 1)))
      (congrArg (fun F : q2Block 1 K ({k} : Finset (Fin (m + 1))) →*
        q2Block 1 K ({k} : Finset (Fin (m + 1))) => F x₀) hθθ)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MonoidHom.id_apply] at h2
    rw [h1, h1, ctTorAut_apply_apply, ctTorAut_apply_apply] at h2
    have hent : ((SpecialLinearGroup.transvection (q2Coord_inl_ne_ctV (Sum.inl p₀)) (1 : K) :
        SpecialLinearGroup (Fin (2 * (m + 1) + 1)) K) :
          Matrix (Fin (2 * (m + 1) + 1)) (Fin (2 * (m + 1) + 1)) K)
        (q2Coord (m + 1) 1 (Sum.inl (Sum.inl p₀))) (ctV (m + 1)) = 1 := by
      rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply_same,
        Matrix.one_apply_ne (q2Coord_inl_ne_ctV _), zero_add]
    rw [ctTorEntry_of_ne (q2Coord_inl_ne_ctV _), ctTorEntry_ctV, hent, one_mul, one_mul,
      one_mul] at h2
    have ha : ((a⁻¹ : Kˣ) : K) = 1 := ctEight_eq_one_of_mul_self_eq_one h2
    have ha1 : a = 1 := by
      have : a⁻¹ = 1 := Units.ext ha
      rwa [inv_eq_one] at this
    refine not_forall_conj_eq_of_linearUnitaryKind hset hKc hf (by omega) e htC ht k
      (Or.inr (Or.inr (Or.inl rfl))) hk fun y hy => ?_
    rw [← P.range_eq] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [hθ x]
    congr 1
    apply Subtype.ext
    rw [h1 x, ha1, ctTorAut_one, MulAut.one_apply]
  · exact ⟨P, a, fun x => by rw [hθ x]; exact congrArg P.Φ (Subtype.ext (h1 x))⟩

end Action

end CFSG.SeitzReduction.SymplecticPilot
