module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SeitzGeneration.ExcSeitzGaps
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2

set_option linter.unusedSectionVars false

@[expose] def ThreeRes (c : PrimePower → LieTypeIndex) (ε : ℕ) : LieTypeIndex → ℕ → Prop :=
  fun d p => p = 3 ∧ ∃ q : PrimePower, d = c q ∧ q.card % 3 = ε

theorem card_mod_three_of_ne {q : PrimePower} (h : 3 ≠ q.p) : q.card % 3 = 1 ∨ q.card % 3 = 2 := by
  have h3 : ¬ 3 ∣ q.card := by
    rw [PrimePower.card_def]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow hd)
    exact h this
  omega

theorem seitzExcHighForAt_three_of_residues {c : PrimePower → LieTypeIndex}
    {F : LieTypeIndex → Prop} (hF : ∀ d, F d → ∃ q, d = c q)
    (hchar : ∀ q, (c q).characteristic = q.p)
    (h1 : SeitzExcHighForAt F (ThreeRes c 1)) (h2 : SeitzExcHighForAt F (ThreeRes c 2)) :
    SeitzExcHighForAt F PrimeRange.three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hFd, hp3, hr, hn⟩
  obtain ⟨q, rfl⟩ := hF d hFd
  have hp3' : p = 3 := hp3
  subst hp3'
  have hq3 : 3 ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  rcases card_mod_three_of_ne hq3 with h | h
  · exact h1 ⟨c q, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hin, hFd, ⟨rfl, q, rfl, h⟩, hr, hn⟩
  · exact h2 ⟨c q, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hin, hFd, ⟨rfl, q, rfl, h⟩, hr, hn⟩

section Certified


theorem seitzExcHighForAt_top_three_of_cases
    (hF4p : SeitzExcHighForAt IsF4Index (ThreeRes LieTypeIndex.F4
        1)) (hF4m : SeitzExcHighForAt IsF4Index (ThreeRes LieTypeIndex.F4
        2))
    (hE6p : SeitzExcHighForAt IsE6Index (ThreeRes LieTypeIndex.E6
        1)) (hE6m : SeitzExcHighForAt IsE6Index (ThreeRes LieTypeIndex.E6
        2))
    (hE7 : SeitzExcHighForAt IsE7Index PrimeRange.three)
    (hE8 : SeitzExcHighForAt IsE8Index PrimeRange.three)
    (hTp : SeitzExcHighForAt IsTwistedE6Index (ThreeRes LieTypeIndex.twistedE6
        1)) (hTm : SeitzExcHighForAt IsTwistedE6Index (ThreeRes
        LieTypeIndex.twistedE6 2)) :
    SeitzExcHighForAt IsTopIndex PrimeRange.three :=
  SeitzExcHighForAt.top_of_families
    (seitzExcHighForAt_three_of_residues (c := LieTypeIndex.F4) (fun _ ⟨q, hq⟩ => ⟨q, hq⟩)
      LieTypeIndex.characteristic_F4 hF4p hF4m)
    (seitzExcHighForAt_three_of_residues (c := LieTypeIndex.E6) (fun _ ⟨q, hq⟩ => ⟨q, hq⟩)
      LieTypeIndex.characteristic_E6 hE6p hE6m)
    hE7 hE8
    (seitzExcHighForAt_three_of_residues (c := LieTypeIndex.twistedE6) (fun _ ⟨q, hq⟩ => ⟨q, hq⟩)
      LieTypeIndex.characteristic_twistedE6 hTp hTm)

end Certified

section Glue

open CFSG.LieType.Chevalley CFSG.TauCetiBridge

theorem exists_normalized_of_native {C N : Type*} [Group C] [Group N] (e : C ≃* N) {r : ℕ}
    {E₀C : Subgroup C}
    (h : ∃ R : Subgroup N, R ≠ ⊥ ∧ IsPGroup r R ∧
      ∀ g ∈ E₀C.map e.toMonoidHom, R.map (MulAut.conj g).toMonoidHom = R) :
    ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r R ∧
      ∀ ε ∈ E₀C.map (MulAut.conj : C →* MulAut C), R.map ε.toMonoidHom = R := by
  obtain ⟨R', hR'1, hR'p, hR'n⟩ := h
  refine ⟨R'.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro h
    exact hR'1 ((Subgroup.map_eq_bot_iff_of_injective R' e.symm.injective).mp h)
  · exact hR'p.of_surjective (e.symm.toMonoidHom.subgroupMap R')
      (e.symm.toMonoidHom.subgroupMap_surjective R')
  · rintro ε ⟨c, hc, rfl⟩
    have hcomp : (MulAut.conj c).toMonoidHom.comp e.symm.toMonoidHom =
        e.symm.toMonoidHom.comp (MulAut.conj (e c)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hR'n (e c) ⟨c, hc, rfl⟩]

theorem planeGen_of_native_closure_of_not_normalizes {C N : Type*} [Group C] [Group N]
    (e : C ≃* N) (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {p r : ℕ}
    (hnat : ∀ E₀ : Subgroup N, (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      ¬ (∃ R : Subgroup N, R ≠ ⊥ ∧ IsPGroup r R ∧
        ∀ g ∈ E₀, R.map (MulAut.conj g).toMonoidHom = R) →
      Subgroup.closure {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤)
    {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hin : E ≤ (MulAut.conj : C →* MulAut C).range)
    (hnorm : ¬ ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r R ∧ ∀ ε ∈ E, R.map ε.toMonoidHom = R) :
    PlaneGen E := by
  set E₀C : Subgroup C := E.comap (MulAut.conj : C →* MulAut C) with hE₀C
  have hmap : E₀C.map (MulAut.conj : C →* MulAut C) = E := Subgroup.map_comap_eq_self hin
  set E₀ : Subgroup N := E₀C.map e.toMonoidHom with hE₀
  have hE₀p : ∀ x ∈ E₀, x ^ p = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 : (MulAut.conj : C →* MulAut C) (c ^ p) = 1 := by
      rw [map_pow]
      exact hE.2 _ hc
    have h2 : c ^ p = 1 := hinj (h1.trans (map_one _).symm)
    rw [← map_pow, h2, map_one]
  have hE₀c : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective e.injective, ← hcard, ← hmap,
      Subgroup.card_map_of_injective hinj]
  have hnotN : ¬ ∃ R : Subgroup N, R ≠ ⊥ ∧ IsPGroup r R ∧
      ∀ g ∈ E₀, R.map (MulAut.conj g).toMonoidHom = R := fun h =>
    hnorm (hmap ▸ exists_normalized_of_native e h)
  have htop := hnat E₀ hE₀p hE₀c hnotN
  set T : Set C := {k | ∃ c ∈ E₀C, c ≠ 1 ∧ Commute k c} with hT
  have himage : e.toMonoidHom '' T = {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} := by
    ext k
    constructor
    · rintro ⟨k₀, ⟨c, hc, hc1, hkc⟩, rfl⟩
      exact ⟨e c, ⟨c, hc, rfl⟩, fun h => hc1 (e.injective (h.trans (map_one e).symm)),
        hkc.map e.toMonoidHom⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, hx1, hkx⟩
      refine ⟨e.symm k, ⟨c, hc, fun h => hx1 (by rw [h]; exact map_one e.toMonoidHom), ?_⟩, ?_⟩
      · have := hkx.map e.symm.toMonoidHom
        simpa using this
      · simp
  have hTtop : Subgroup.closure T = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : e.toMonoidHom k ∈ Subgroup.closure {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [← himage, ← MonoidHom.map_closure] at hk
    obtain ⟨k₀, hk₀, hk₀e⟩ := hk
    have : k₀ = k := e.injective hk₀e
    rw [← this]
    exact hk₀
  have hle : Subgroup.closure T ≤ planeClosure E := by
    rw [Subgroup.closure_le]
    rintro k ⟨c, hc, hc1, hkc⟩
    refine Subgroup.subset_closure ⟨MulAut.conj c, ?_, fun h => hc1 ?_, ?_⟩
    · rw [← hmap]
      exact ⟨c, hc, rfl⟩
    · exact hinj (h.trans (map_one _).symm)
    · rw [MulAut.conj_apply, ← hkc.eq]
      group
  rw [PlaneGen, eq_top_iff, ← hTtop]
  exact hle

end Glue

section NativeForms

open CFSG.LieType.Chevalley


@[expose] def E6ThreeNative (ε : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε →
    ∀ E₀ : Subgroup (adjointGroup .E6 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRNative .E6 K E₀ → planeCl E₀ = ⊤

@[expose] def TwE6ThreeNative (ε : ℕ) : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → q % 3 = ε →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRIn (ringChar K) E₀ → planeCl E₀ = ⊤

end NativeForms


section F4Glue

open CFSG.LieType.Chevalley CFSG.TauCetiBridge


theorem seitzExcHighThreeF4_of_native {ε : ℕ} (h : F4ThreeNative ε) :
    SeitzExcHighForAt IsF4Index (ThreeRes LieTypeIndex.F4 ε) := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp3, q, hdq, hmod⟩, -, hn⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  have hp3' : p = 3 := hp3
  subst hp3'
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  refine planeGen_of_native_closure_of_not_normalizes (p := 3) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 h3 => h K (by rw [hKq]; exact hmod) E₀ h1 h2
      (fun ⟨R, hR1, hRp, hRn⟩ => h3 ⟨R, hR1, hRp, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩))
    hE hcard hin ?_
  rintro ⟨R, hR1, hRp, hRn⟩
  refine hn ⟨R, hR1, ?_, hRn⟩
  rw [LieTypeIndex.characteristic_F4, ← hring]
  exact hRp

end F4Glue

section Vacuity

open CFSG.LieType.Chevalley CFSG.TauCetiBridge


theorem seitzExcHighThree_of_allParabolic {τ : Tag} {c : PrimePower → LieTypeIndex}
    {F : LieTypeIndex → Prop} (hB : Even.UntwistedBridgeAll τ c)
    (hF : ∀ d, F d → ∃ q, d = c q) (hchar : ∀ q, (c q).characteristic = q.p)
    (h : ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
      ∀ A : Subgroup (adjointGroup τ K), (∀ x ∈ A, x ^ 3 = 1) → Nat.card A = 3 ^ 2 →
        NormalizesRNative τ K A) :
    SeitzExcHighForAt F PrimeRange.three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hFd, hp3, hr, hn⟩
  obtain ⟨q, rfl⟩ := hF d hFd
  have hp3' : p = 3 := hp3
  subst hp3'
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq3 : 3 ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  have hnd : ¬ 3 ∣ Nat.card K := by
    rw [hKq, PrimePower.card_def]
    intro hd
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow hd))
  exfalso
  have hinj : Function.Injective (MulAut.conj : Cat ⟨c q, hv⟩ →* MulAut (Cat ⟨c q, hv⟩)) :=
    conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot)
  set E₀C : Subgroup (Cat ⟨c q, hv⟩) := E.comap (MulAut.conj : _ →* MulAut (Cat ⟨c q, hv⟩))
    with hE₀C
  have hmap : E₀C.map (MulAut.conj : _ →* MulAut (Cat ⟨c q, hv⟩)) = E :=
    Subgroup.map_comap_eq_self hin
  have hE₀p : ∀ x ∈ E₀C.map e.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj : _ →* MulAut (Cat ⟨c q, hv⟩)) (x ^ 3) = 1 := by
      rw [map_pow]
      exact hE.2 _ hx
    have h2 : x ^ 3 = 1 := hinj (h1.trans (map_one _).symm)
    rw [← map_pow, h2, map_one]
  have hE₀c : Nat.card (E₀C.map e.toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, ← hc, ← hmap,
      Subgroup.card_map_of_injective hinj]
  obtain ⟨R, hR1, hRp, hRn⟩ := h K hnd _ hE₀p hE₀c
  obtain ⟨R', hR'1, hR'p, hR'n⟩ := exists_normalized_of_native e
    ⟨R, hR1, by simpa [hring] using hRp, fun g hg => (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩
  rw [hmap] at hR'n
  refine hn ⟨R', hR'1, ?_, hR'n⟩
  rw [hchar q]
  exact hR'p

end Vacuity

section TwE6Glue

open CFSG.LieType.Chevalley CFSG.TauCetiBridge


theorem seitzExcHighThreeTwE6_of_native {ε : ℕ} (h : TwE6ThreeNative ε) :
    SeitzExcHighForAt IsTwistedE6Index (ThreeRes LieTypeIndex.twistedE6 ε) := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp3, q, hdq, hmod⟩, -, hn⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  have hp3' : p = 3 := hp3
  subst hp3'
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have hch : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hring : ringChar K = q.p := ringChar.eq K q.p
  refine planeGen_of_native_closure_of_not_normalizes (p := 3) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
      (center_graphFixedRootGroup_eq_bot σ.surjective)))
    (fun E₀ h1 h2 h3 => h _ K σ hK hσ (by rw [← TauCeti.PrimePower.card_def]; exact hmod) E₀ h1 h2
      (fun ⟨R, hR1, hRp, hRn⟩ => h3 ⟨R, hR1, hRp, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩))
    hE hcard hin ?_
  rintro ⟨R, hR1, hRp, hRn⟩
  refine hn ⟨R, hR1, ?_, hRn⟩
  rw [LieTypeIndex.characteristic_twistedE6, ← hring]
  exact hRp

end TwE6Glue

section E6Glue

open CFSG.LieType.Chevalley CFSG.TauCetiBridge


theorem seitzExcHighThreeE6_of_native {ε : ℕ} (h : E6ThreeNative ε) :
    SeitzExcHighForAt IsE6Index (ThreeRes LieTypeIndex.E6 ε) := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp3, q, hdq, hmod⟩, -, hn⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  have hp3' : p = 3 := hp3
  subst hp3'
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  refine planeGen_of_native_closure_of_not_normalizes (p := 3) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 h3 => h K (by rw [hKq]; exact hmod) E₀ h1 h2
      (fun ⟨R, hR1, hRp, hRn⟩ => h3 ⟨R, hR1, hRp, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩))
    hE hcard hin ?_
  rintro ⟨R, hR1, hRp, hRn⟩
  refine hn ⟨R, hR1, ?_, hRn⟩
  rw [LieTypeIndex.characteristic_E6, ← hring]
  exact hRp

end E6Glue

end CFSG.LieType.SeitzGeneration.ExcHighThree
