module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWSwap

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Helpers

variable {X : Type*} [Group X]

theorem card_sup_eq_mul_of_le_centralizer_of_inf_eq_bot {A B : Subgroup X}
    (hBA : B ≤ centralizer (A : Set X)) (hAB : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup X) = Nat.card A * Nat.card B := by
  have comm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (mem_centralizer_iff.1 (hBA b.2)) a a.2
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype comm
  rw [range_subtype, range_subtype] at hr
  have hinj : Function.Injective (A.subtype.noncommCoprod B.subtype comm) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    rw [MonoidHom.noncommCoprod_apply] at h
    have ha : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hmem : (a : X) ∈ A ⊓ B := mem_inf.2 ⟨a.2, ha ▸ B.inv_mem b.2⟩
    rw [hAB, mem_bot] at hmem
    have hb : (b : X) = 1 := by
      rw [ha] at hmem
      exact inv_eq_one.1 hmem
    have ha1 : a = 1 := Subtype.ext hmem
    have hb1 : b = 1 := Subtype.ext hb
    rw [ha1, hb1]
    rfl
  rw [← hr, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem map_conj_toMonoidHom_eq_self_of_mem_centralizer {Y : Subgroup X} {t : X}
    (ht : t ∈ centralizer (Y : Set X)) : Y.map (MulAut.conj t).toMonoidHom = Y := by
  have key : ∀ y ∈ Y, t * y * t⁻¹ = y := fun y hy => by
    rw [← mem_centralizer_iff.1 ht y hy, mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change t * y * t⁻¹ ∈ Y
    rw [key y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, key x hx⟩

end Helpers

section Schur

variable {K : Type} [Field K] [Finite K]

noncomputable def specialLinearEquivProjectiveSLOfCardTwo (hK : Nat.card K = 2) {n : ℕ}
    (hn : 1 ≤ n) : Matrix.SpecialLinearGroup (Fin n) K ≃* LinearFlag.projectiveSL n K := by
  have hscal : LinearFlag.scalars n K = ⊥ := by
    have h := LinearFlag.card_scalars_dvd (K := K) hn
    rw [hK] at h
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp h)
  exact MulEquiv.ofBijective (LinearFlag.proj n K)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [LinearFlag.ker_proj, hscal]),
      LinearFlag.proj_surjective n K⟩

theorem oddSchurTrivial_of_mulEquiv_projectiveSL_two
    [CharP K 2]
    (hK : Nat.card K = 2) {X : Type} [Group X] {m : ℕ}
    (e : X ≃* LinearFlag.projectiveSL (m + 1) K) : OddSchurTrivial X :=
  (SeitzQ2.oddSchurTrivial_specialLinearGroup m K).of_mulEquiv
    ((specialLinearEquivProjectiveSLOfCardTwo hK (by omega)).trans e.symm)

end Schur

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem commutator_modelToG_blockSL_pair_compl_and_ne_bot {n : ℕ} (hn : 5 ≤ n) {K : Type}
    [Field K] (e : L ≃* LinearFlag.projectiveSL n K) {a b : Fin n} (hab : a ≠ b) :
    ⁅modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ)),
        modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ))⁆ =
      modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ)) ∧
      modelToG e (blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ)) ≠ ⊥ := by
  have hcardI : 3 ≤ (({a, b} : Finset (Fin n))ᶜ).card := by
    rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    omega
  refine ⟨?_, ?_⟩
  · rw [modelToG, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_blockSL_eq_of_three_le hcardI]
  · have hS1 : blockSL (K := K) (({a, b} : Finset (Fin n))ᶜ) ≠ ⊥ := by
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (by omega :
        1 < (({a, b} : Finset (Fin n))ᶜ).card)
      intro h
      have hmem := proj_transvection_mem_blockSL (K := K) hij hi hj 1
      rw [h, mem_bot] at hmem
      exact proj_transvection_ne_one hij one_ne_zero hmem
    intro h
    apply hS1
    rw [modelToG] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1
      ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h)

theorem centralizerPerfectCore_le_sup_of_swapKind
    (hset : SeitzSetting G L)
    {n : ℕ} (hn : 5 ≤ n) {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1)
    (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hsw : LinearTwoSwapKindAt e t a b X₀ htX)
    {G₁ : Subgroup G} (hperf : ⁅G₁, G₁⁆ = G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    centralizerPerfectCore (modelToG e X₀) ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hL : IsSimpleGroup L := SeitzQ2.isSimpleGroup_of_seitzSetting hset
  have hq : CFSG.Open.IsQuasisimple G₁ := isQuasisimple_of_linearSwapDiag h₁₂ hperf hL hδ hsurj
  obtain ⟨Kc, hKc, hDKK, hne, hcomm, -, hiso⟩ := hsw
  obtain ⟨Q, hQinj, hQr⟩ := exists_swapParam_linear_two hset hK e hn htC ht hab hX₀ hX₀c htX hKc
    hDKK hne hcomm hiso
  set X := modelToG e X₀ with hXdef
  set D := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin (m + 1)))ᶜ)) with hDdef
  have hXL : X ≤ L := modelToG_le e X₀
  have hDL : D ≤ L := modelToG_le e _
  have hDX : D ≤ centralizer (X : Set G) :=
    modelToG_le_centralizer e (blockSL_compl_le_centralizer hX₀)
  have hDperf : ⁅D, D⁆ = D := (commutator_modelToG_blockSL_pair_compl_and_ne_bot hn e hab).1
  set δ := linearSwapDiag h₁₂ with hδdef
  have hmemL : ∀ x : G₁, δ x ∈ L := fun x => hδ x x.2
  set π : G₁ →* L := δ.codRestrict L hmemL with hπ
  have hπapp : ∀ x : G₁, (π x : G) = (x : G) * (t * x * t⁻¹) := fun x => rfl
  have hπs : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hπker : π.ker ≤ center G₁ := by
    intro x hx
    refine ker_linearSwapDiag_le_center h₁₂ ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  have hZodd : Odd (Nat.card (center G₁)) :=
    UnitaryPilot.odd_card_center_of_swapFactors hset.center_eq_bot ht hKt hq h₁₂ hδ hsurj
  have hkerodd : Odd (Nat.card π.ker) := Odd.of_dvd_nat hZodd (Subgroup.card_dvd_of_le hπker)
  have hπinj : Function.Injective π :=
    oddSchurTrivial_of_mulEquiv_projectiveSL_two hK e G₁ (Subgroup.isPerfect_iff.2 hperf) π hπs
      hπker hkerodd
  have hZ : ∀ x : G₁, (∀ y : G₁, y * x = x * y) → x = 1 := by
    intro x hx
    apply hπinj
    rw [map_one]
    have hc : π x ∈ center L := by
      rw [mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := hπs w
      rw [← map_mul, ← map_mul, hx y]
    rw [hset.center_eq_bot] at hc
    exact Subgroup.mem_bot.1 hc
  have hG₁₂ : G₁ ⊓ G₁.map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    have hxc : x ∈ centralizer (G₁ : Set G) := h₁₂ hx2
    have h1 := hZ ⟨x, hx1⟩ fun y => Subtype.ext (mem_centralizer_iff.1 hxc y y.2)
    exact mem_bot.2 (congrArg Subtype.val h1)
  set TD : Subgroup G₁ := (D.subgroupOf L).comap π with hTD
  set C : Subgroup G := TD.map G₁.subtype with hC
  have hCG₁ : C ≤ G₁ := map_subtype_le _
  have hTDmap : TD.map π = D.subgroupOf L := Subgroup.map_comap_eq_self_of_surjective hπs _
  have hDsub : ⁅D.subgroupOf L, D.subgroupOf L⁆ = D.subgroupOf L :=
    CFSG.SeitzReduction.commutator_subgroupOf_eq_self hDL hDperf
  have hTDperf : ⁅TD, TD⁆ = TD := by
    apply Subgroup.map_injective hπinj
    rw [Subgroup.map_commutator, hTDmap, hDsub]
  have hCperf : ⁅C, C⁆ = C := by
    rw [hC, ← Subgroup.map_commutator, hTDperf]
  have hcardC : Nat.card C = Nat.card D := by
    rw [hC, Subgroup.card_map_of_injective G₁.subtype_injective,
      ← Subgroup.card_map_of_injective hπinj, hTDmap]
    exact Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv
  have hCX : C ≤ centralizer (X : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hx⟩ := hπs ⟨y, hXL hy⟩
    have hcD : ((π c : L) : G) ∈ D := mem_subgroupOf.1 (mem_comap.1 hc)
    have hxX : ((π x : L) : G) ∈ X := by
      rw [hx]
      exact hy
    have hcx : c * x = x * c := by
      apply hπinj
      rw [map_mul, map_mul]
      exact Subtype.ext (mem_centralizer_iff.1 (hDX hcD) _ hxX).symm
    have hct : (c : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * c :=
      mem_centralizer_iff.1 (h₁₂ ⟨x, x.2, rfl⟩) c c.2
    have hyx : y = (x : G) * (t * x * t⁻¹) := by
      rw [← hπapp, hx]
    have hcx' : (c : G) * x = x * c := congrArg Subtype.val hcx
    rw [hyx]
    change (x : G) * (t * x * t⁻¹) * c = c * (x * (t * x * t⁻¹))
    calc (x : G) * (t * x * t⁻¹) * c = x * ((t * x * t⁻¹) * c) := by group
      _ = x * (c * (t * x * t⁻¹)) := by rw [hct]
      _ = (x * c) * (t * x * t⁻¹) := by group
      _ = (c * x) * (t * x * t⁻¹) := by rw [hcx']
      _ = c * (x * (t * x * t⁻¹)) := by group
  have hCE : C ≤ centralizerPerfectCore X := F4Pilot.le_centralizerPerfectCore hCperf hCX
  have hXt : X.map (MulAut.conj t).toMonoidHom = X :=
    map_conj_toMonoidHom_eq_self_of_mem_centralizer htX
  have hEt : (centralizerPerfectCore X).map (MulAut.conj t).toMonoidHom =
      centralizerPerfectCore X := by
    rw [F4Pilot.map_centralizerPerfectCore (MulAut.conj t) X, hXt]
  have hCtE : C.map (MulAut.conj t).toMonoidHom ≤ centralizerPerfectCore X := by
    rw [← hEt]
    exact map_mono hCE
  have hCt_cent : C.map (MulAut.conj t).toMonoidHom ≤ centralizer (C : Set G) :=
    (map_mono hCG₁).trans (h₁₂.trans (centralizer_le hCG₁))
  have hCinf : C ⊓ C.map (MulAut.conj t).toMonoidHom = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hCG₁ (map_mono hCG₁)).trans (eq_bot_iff.1 hG₁₂))
  have hcardE : Nat.card (centralizerPerfectCore X) = Nat.card D * Nat.card D := by
    rw [← hQr, ← Nat.card_prod]
    exact (Nat.card_congr (MonoidHom.ofInjective hQinj).toEquiv).symm
  have hcardsup : Nat.card (C ⊔ C.map (MulAut.conj t).toMonoidHom : Subgroup G) =
      Nat.card D * Nat.card D := by
    rw [card_sup_eq_mul_of_le_centralizer_of_inf_eq_bot hCt_cent hCinf,
      Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective,
      hcardC]
  have heq : C ⊔ C.map (MulAut.conj t).toMonoidHom = centralizerPerfectCore X :=
    Subgroup.eq_of_le_of_card_ge (sup_le hCE hCtE) (by rw [hcardE, hcardsup])
  rw [← heq]
  exact sup_le_sup hCG₁ (map_mono hCG₁)

theorem false_of_swapKind_of_gOne_linear_two
    (hset : SeitzSetting G L)
    {n : ℕ} (hn : 5 ≤ n) {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1)
    (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hsw : LinearTwoSwapKindAt e t a b X₀ htX)
    {G₁ : Subgroup G} (hperf : ⁅G₁, G₁⁆ = G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) : False := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hL : IsSimpleGroup L := SeitzQ2.isSimpleGroup_of_seitzSetting hset
  have hq : CFSG.Open.IsQuasisimple G₁ := isQuasisimple_of_linearSwapDiag h₁₂ hperf hL hδ hsurj
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv (by omega) e
  have hnorm := SeitzQ2.nonSwap_of_factorNormal hset ht hKt
    (SeitzQ2.factorNormal_of_swapPairExclusion hset hOut e
      (swapPairExclusion_projectiveSL_two hn hK) ht hKt) hq h₁₂ hδ hsurj
  have hE := centralizerPerfectCore_le_sup_of_swapKind hset hn hK e ht hKt hab hX₀ hX₀c htX hsw
    hperf h₁₂ hδ hsurj
  obtain ⟨hDperf, hD⟩ := commutator_modelToG_blockSL_pair_compl_and_ne_bot hn e (K := K) hab
  have : IsSimpleGroup G := hset.1
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple ht hq h₁₂ rfl
    (SeitzQ2.unique_of_swapFactors_of_neighbour hset hOut htC ht hq h₁₂ hδ hsurj
      (modelToG_le e X₀) (modelToG_le e _)
      (modelToG_le_centralizer e (blockSL_compl_le_centralizer hX₀)) hDperf hD hE hnorm)

theorem false_of_swapRow_of_gOne_linear_two
    (hset : SeitzSetting G L)
    {n : ℕ} (hn : 5 ≤ n) {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hall : ∀ (a b : Fin n) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL n K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX)
    {G₁ : Subgroup G} (hperf : ⁅G₁, G₁⁆ = G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) : False := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by
    simp only [Fin.mk.injEq] at h
    omega
  obtain ⟨X₀, hX₀, -, hX₀c⟩ := exists_torusQ1 (K := K) (n := n) hab
  have htX : t ∈ centralizer (modelToG e X₀ : Set G) := centralizer_le (modelToG_le e X₀) htC
  exact false_of_swapKind_of_gOne_linear_two hset hn hK e ht hKt hab hX₀ hX₀c htX
    (hall _ _ hab X₀ hX₀ hX₀c htX) hperf h₁₂ hδ hsurj

end Endgame

end CFSG.SeitzReduction.LinearPilot
