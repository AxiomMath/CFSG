module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256i2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j
import all CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256i2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256n

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
open scoped Pointwise

set_option linter.unusedSectionVars false

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_iSup_of_conj_mem {ι : Type*} {F : ι → Subgroup G} {u : G}
    (h : ∀ i, ∀ x ∈ F i, u * x * u⁻¹ ∈ F i) (h' : ∀ i, ∀ x ∈ F i, u⁻¹ * x * u ∈ F i) :
    u ∈ Subgroup.normalizer ((⨆ i, F i : Subgroup G) : Set G) := by
  have hle : ∀ v : G, (∀ i, ∀ x ∈ F i, v * x * v⁻¹ ∈ F i) →
      ∀ x ∈ ⨆ i, F i, v * x * v⁻¹ ∈ ⨆ i, F i := by
    intro v hv x hx
    have hsub : (⨆ i, F i) ≤ (⨆ i, F i).comap (MulAut.conj v).toMonoidHom :=
      iSup_le fun i y hy => by
        show v * y * v⁻¹ ∈ ⨆ i, F i
        exact le_iSup F i (hv i y hy)
    exact hsub hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hle u h x, fun hx => ?_⟩
  have h1 := hle u⁻¹ (fun i y hy => by simpa using h' i y hy) _ hx
  have e : u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x := by group
  rwa [e] at h1

end Generic

section Closure


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

@[expose] noncomputable def orbitCharClosure (ℓ : ℕ) (Ψ : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ L) :=
  Subgroup.closure {g | g ∈ rootSpan τ L Ψ ∧ g ∈ S.D.model ∧ ∃ n : ℕ, g ^ ℓ ^ n = 1}

theorem orbitCharClosure_le_rootSpan (ℓ : ℕ) (Ψ : Set (Fin τ.rank → ℤ)) :
    orbitCharClosure S ℓ Ψ ≤ rootSpan τ L Ψ :=
  (Subgroup.closure_le _).2 fun _ hg => hg.1

theorem mem_orbitCharClosure_of_charElem (ℓ : ℕ) {Ψ : Set (Fin τ.rank → ℤ)} {g : ModGL τ L}
    (hg : g ∈ rootSpan τ L Ψ) (hgM : g ∈ S.D.model) (hgn : ∃ n : ℕ, g ^ ℓ ^ n = 1) :
    g ∈ orbitCharClosure S ℓ Ψ :=
  Subgroup.subset_closure ⟨hg, hgM, hgn⟩

theorem conj_mem_orbitCharClosure (ℓ : ℕ) {Ψ : Set (Fin τ.rank → ℤ)} {u : ModGL τ L}
    (hu : u ∈ Subgroup.normalizer (rootSpan τ L Ψ : Set (ModGL τ L))) (huM : u ∈ S.D.model) {x : ModGL τ L}
    (hx : x ∈ orbitCharClosure S ℓ Ψ) : u * x * u⁻¹ ∈ orbitCharClosure S ℓ Ψ := by
  have hsub : orbitCharClosure S ℓ Ψ ≤ (orbitCharClosure S ℓ Ψ).comap (MulAut.conj u).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨hg, hgM, m, hm⟩
    show u * g * u⁻¹ ∈ orbitCharClosure S ℓ Ψ
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.1 hu g).1 hg,
      S.D.model.mul_mem (S.D.model.mul_mem huM hgM) (S.D.model.inv_mem huM), m, ?_⟩
    rw [conj_pow, hm, mul_one, mul_inv_cancel]
  exact hsub hx

end Closure

section Inner


variable {τ : Tag} {K : Type} [Field K] [Finite K] {ℓ : ℕ}

variable {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)

theorem charElem_mem_map_CQ (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (σ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (z : ModGL τ (AlgebraicClosure K))
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ (AlgebraicClosure K),
      g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {y : ModGL τ (AlgebraicClosure K)}
    (hy : y ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i))
    (hyF : iterHom S.D.step s y = y) {n : ℕ} (hn : y ^ ℓ ^ n = 1) :
    y ∈ (CQ σ i).map (MulAut.conj z).toMonoidHom := by
  classical
  set v := z⁻¹ * y * z with hv
  have hzv : z * v * z⁻¹ = y := by rw [hv]; group
  have hvS : v ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
    (hnorm i v).2 (by rw [hzv]; exact hy)
  have hvF : frobGL σ v = v := by
    have h1 := hz v hvS
    rw [hzv, hyF] at h1
    have h2 : frobGL σ v = z⁻¹ * y * z := by rw [h1]; group
    rw [h2]
  have hvn : v ^ ℓ ^ n = 1 := by
    have h1 : v ^ ℓ ^ n = (MulAut.conj z⁻¹) (y ^ ℓ ^ n) := by
      rw [map_pow]
      congr 1
    rw [h1, hn, map_one]
  have hvU : v ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a))) := by
    rw [unionRootSpan_singleton_charQ]
    exact hvS
  obtain ⟨t, ht, x, hx, hvtx, htF⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_decomp (σ := σ) hvU
    (one_mem _) (by rw [one_mul]; exact hvF)
  have hcen1 : ∀ w ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a))), w * 1 = 1 * w := fun _ _ => by
    rw [mul_one, one_mul]
  have hn' := torus_normalizes_CQ (σ := σ) ht hcen1 htF
  have htN' : t ∈ Subgroup.normalizer (CQ σ i : Set (ModGL τ (AlgebraicClosure K))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hn'.1 w hw, fun hw => ?_⟩
    have h1 := hn'.2 _ hw
    have e1 : t⁻¹ * (t * w * t⁻¹) * t = w := by group
    rwa [e1] at h1
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup ht)
  obtain ⟨Nt, hNt, hlN⟩ := exists_coprime_pow_eq_one_algClosure hℓp hK l
  have htN : t ^ Nt = 1 := by
    rw [hl]
    exact rootDiagUnit_pow_eq_one_of_forall hlN
  have hvC : v ∈ CQ σ i := by
    rw [hvtx]
    exact mem_of_charElem_of_mul htN' htN hNt hx (by rw [← hvtx]; exact hvn)
  exact ⟨v, hvC, hzv⟩

theorem compCharElem_inner_three (hK : ringChar K = 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hgood : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∨
      ∃ α ∈ componentRoots (rootCharHom a) i, ∃ δ ∈ componentRoots (rootCharHom a) i, δ ≠ α ∧ δ ≠ -α) :
    CompCharElem S 3 a i := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hqe⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hqe, ← pow_mul]
  have hes : 0 < e * s := Nat.mul_pos he hs0
  have hperfC : Group.IsPerfect (componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    rcases hgood with hQ | hbig
    · have hQ' : 4 ≤ r ^ (e * s) := by rw [pow_mul, ← hqe]; exact hQ
      obtain ⟨t₀, ht₀⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_unit_sq_ne_one
        (L := AlgebraicClosure K) σ hσ' hes hQ'
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.isPerfect_componentRootSpan_of_sq_ne_one
        (K := fixSubfield σ) (χ := rootCharHom a) ht₀ i
    · have hL3 : ringChar (AlgebraicClosure K) = 3 := by
        rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, hK]
      haveI : CharP (AlgebraicClosure K) 3 := hL3 ▸ ringChar.charP (AlgebraicClosure K)
      have h2L : (2 : AlgebraicClosure K) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : AlgebraicClosure K) = 0 := by exact_mod_cast h
        have := (CharP.cast_eq_zero_iff (AlgebraicClosure K) 3 2).1 h'
        omega
      have h2 : (2 : fixSubfield σ) ≠ 0 := fun h => h2L (by
        have h' := congrArg (fixSubfield σ).subtype h
        rwa [map_ofNat, map_zero] at h')
      have hTp := rootDiagUnit_pow_eq_one_of_forall hap
      have hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
        cases τ <;> simp
      rcases hτ with rfl | rfl | hτ | hτ | hτ | hτ
      · exfalso
        obtain ⟨α, hα, δ, hδ, hne1, hne2⟩ := hbig
        rcases g2_component_rank_one (rootCharHom a) hp hp5
            (fun γ hγ => rootChar_pow_eq_one_of_pow hTp hγ)
            (by obtain ⟨γ, hγ, hne⟩ := exists_rootChar_ne_one h1; exact ⟨γ, hγ, hne⟩) i α hα δ hδ with
          h | h
        · exact hne1 h
        · exact hne2 h
      · exact isPerfect_componentRootSpan_F4_of_two_ne_zero h2 i hbig
      all_goals exact isPerfect_componentRootSpan_simplyLaced (by simp [hτ]) i hbig
  have hperfCQ : ⁅CQ σ i, CQ σ i⁆ = CQ σ i := by
    rw [CQ_eq_map, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperfC]
  refine ⟨(CQ σ i).map (MulAut.conj z).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hnorm i x).1 (CQ_le_rootSpan σ i hx)
  · rintro _ ⟨x, hx, rfl⟩
    show iterHom S.D.step s (z * x * z⁻¹) = z * x * z⁻¹
    rw [hz x (CQ_le_rootSpan σ i hx), frobGL_eq_self_of_mem_CQ σ i hx]
  · rw [← Subgroup.map_commutator, hperfCQ]
  · intro y hy hyF ⟨n, hn⟩
    exact charElem_mem_map_CQ S hK Nat.prime_three i σ z hnorm hz hy hyF hn

theorem coprime_card_orbitCharClosure_rank_one (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4)
    (hrank : ∀ α ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      δ = α ∨ δ = -α) :
    Nat.Coprime (Nat.card (orbitCharClosure S ℓ (rationalRoots S.ρ (rootCharHom a) i))) p := by
  classical
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  obtain ⟨r, e, hr, hchar, he, hqe⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hq2 : 2 ≤ S.D.q := by
    rw [hqe]
    exact hr.two_le.trans (Nat.le_self_pow he.ne' r)
  have hs1 : s = 1 := by
    by_contra hne
    have h2 : 2 ≤ s := by omega
    have h4 : 4 ≤ S.D.q ^ s :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ S.D.q ^ 2 := Nat.pow_le_pow_left hq2 2
        _ ≤ S.D.q ^ s := Nat.pow_le_pow_right (by omega) h2
    omega
  have hρΨ : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    have h := hs
    rw [hs1, Function.iterate_one] at h
    exact h
  have hk : ∀ k : ℕ, ∀ δ ∈ componentRoots (rootCharHom a) i,
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ ∈ componentRoots (rootCharHom a) i := by
    intro k
    induction k with
    | zero => exact fun δ hδ => hδ
    | succ k ih =>
      intro δ hδ
      rw [Function.iterate_succ_apply', ← hρΨ]
      exact ⟨_, ih δ hδ, rfl⟩
  have hΨ : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      exact hk k δ hδ
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hqe, ← pow_mul]
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := AlgebraicClosure K) r (e * s) (Nat.mul_pos he hs0)
  have hset : (fixSubfield σ : Set (AlgebraicClosure K)) = {c : AlgebraicClosure K | c ^ (r ^ (e * s)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  haveI hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set (AlgebraicClosure K)).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σ) = r ^ (e * s) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set (AlgebraicClosure K)).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set (AlgebraicClosure K))
    rw [h1, hset, hcardset]
  have hKle : Nat.card (fixSubfield σ) ≤ 3 := by
    rw [hKcard, pow_mul, ← hqe]
    omega
  have hle : orbitCharClosure S ℓ (rationalRoots S.ρ (rootCharHom a) i) ≤
      (CQ σ i).map (MulAut.conj z).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨hg, hgM, n, hn⟩
    rw [hΨ] at hg
    have hgF : iterHom S.D.step s g = g := by
      rw [hs1, iterHom_eq_iterate, Function.iterate_one]
      exact hgM.2
    exact charElem_mem_map_CQ S hK hℓp i σ z hnorm hz hg hgF hn
  have hcard : Nat.card ((CQ σ i).map (MulAut.conj z).toMonoidHom) =
      Nat.card (componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj z).injective, CQ_eq_map,
      Subgroup.card_map_of_injective (baseChangeGL_injective _)]
  have hndvd := not_dvd_card_componentRootSpan_of_rank_one hKle i hrank hp hp5
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hpd
  exact hndvd (by rw [← hcard]; exact hpd.trans (Subgroup.card_dvd_of_le hle))

end Inner

section Assembly


variable {τ : Tag} {K : Type} [Field K] [Finite K]

variable {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)

theorem orbit_dichotomy_three (hK : ringChar K = 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a)) :
    (∃ P : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P, P⁆ = P ∧
        P ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
          (∃ n : ℕ, g ^ 3 ^ n = 1) → g ∈ P) ∨
      Nat.Coprime (Nat.card (orbitCharClosure S 3 (rationalRoots S.ρ (rootCharHom a) i))) p := by
  classical
  cases hkind : twistKind S.ρ (rootCharHom a) i with
  | inner =>
    by_cases hgood : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∨
        ∃ α ∈ componentRoots (rootCharHom a) i, ∃ δ ∈ componentRoots (rootCharHom a) i, δ ≠ α ∧ δ ≠ -α
    · exact Or.inl (exists_perfect_orbit_of_comp S hK Nat.prime_three hT i
        (compCharElem_inner_three S hK hp hp5 hT hap h1 i hkind hgood))
    · push Not at hgood
      refine Or.inr (coprime_card_orbitCharClosure_rank_one S hK Nat.prime_three hp hp5 hT i hkind hgood.1
        fun α hα δ hδ => ?_)
      by_cases h : δ = α
      · exact Or.inl h
      · exact Or.inr (hgood.2 α hα δ hδ h)
  | suN =>
    exact Or.inl (exists_perfect_orbit_of_comp S hK Nat.prime_three hT i
      (Inputs256i.compCharElem_suN_three S hK Nat.prime_three le_rfl hp hT hap h1 i hkind))
  | twoD =>
    obtain ⟨P, hPA, hPperf, hP⟩ := Inputs256i.orbitCharElemPerfect_outer_any S hp hT hap h1 i (Or.inl hkind)
    rw [hK] at hP
    exact Or.inl ⟨P, hPperf, le_rationalComponent_of_perfect S i hPA hPperf, hP⟩
  | exc =>
    obtain ⟨P, hPA, hPperf, hP⟩ := Inputs256i.orbitCharElemPerfect_outer_any S hp hT hap h1 i (Or.inr hkind)
    rw [hK] at hP
    exact Or.inl ⟨P, hPperf, le_rationalComponent_of_perfect S i hPA hPperf, hP⟩

theorem exists_perfect_mul_coprime_three (hK : ringChar K = 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) {k : ModGL τ (AlgebraicClosure K)}
    (hk : k ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) {m : ℕ} (hkm : k ^ 3 ^ m = 1) :
    ∃ P W : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P, P⁆ = P ∧
      P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
      CFSG.Open.IsSubnormal W (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) ∧
      Nat.Coprime (Nat.card W) p ∧ ∃ g ∈ P, ∃ y ∈ W, g * y = k := by
  classical
  have hp3 : p ≠ 3 := by omega
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hform := S.frob.iform_eq
  have hΓ : S.Γ ≤ adjointGroup τ (AlgebraicClosure K) :=
    (Subgroup.commutator_le_self S.D.model).trans inf_le_left
  have hΓM : S.Γ ≤ S.D.model := Subgroup.commutator_le_self S.D.model
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ (AlgebraicClosure K) (rootCharHom a)).2.1
  haveI : Finite (Set.range (rationalRoots S.ρ (rootCharHom a))) := (Set.finite_range _).to_subtype
  haveI : Fintype (Set.range (rationalRoots S.ρ (rootCharHom a))) := Fintype.ofFinite _
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup (ModGL τ (AlgebraicClosure K)),
      U = rootSpan τ (AlgebraicClosure K) (kernelRoots (rootCharHom a)) := ⟨_, rfl⟩
  have hUd : U ≤ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [hUdef]
    exact CFSG.LieType.Chevalley.rootSpan_le_centralizer a fun γ hγ => hγ
  have hBU : ∀ O : Set.range (rationalRoots S.ρ (rootCharHom a)), orbitCharClosure S 3 O.1 ≤ U := by
    rintro ⟨_, i, rfl⟩
    rw [hUdef]
    exact (orbitCharClosure_le_rootSpan S 3 _).trans (rootSpan_mono (rationalRoots_subset_kernelRoots hker i))
  have hUnorm : ∀ O : Set.range (rationalRoots S.ρ (rootCharHom a)),
      U ≤ Subgroup.normalizer (rootSpan τ (AlgebraicClosure K) O.1 : Set (ModGL τ (AlgebraicClosure K))) := by
    rintro ⟨_, i, rfl⟩
    rw [hUdef]
    exact rootSpan_le_normalizer_of_closed (L := AlgebraicClosure K) (rationalRoots_subset_kernelRoots hker i)
      fun γ hγ δ hδ h => rationalRoots_closed hker hform i hγ hδ h
  have hex : ∀ O : Set.range (rationalRoots S.ρ (rootCharHom a)),
      ∃ P : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P, P⁆ = P ∧
        P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
        (¬ Nat.Coprime (Nat.card (orbitCharClosure S 3 O.1)) p → orbitCharClosure S 3 O.1 ≤ P) := by
    rintro ⟨_, i, rfl⟩
    rcases orbit_dichotomy_three S hK hp hp5 hT hap h1 i with ⟨P, hPp, hPR, hPm⟩ | hc
    · refine ⟨P, hPp, hPR.trans (langSubnormal_of_mem_torus S hT i).1, fun _ => ?_⟩
      exact (Subgroup.closure_le _).2 fun g hg => hPm g hg.1 hg.2.1 hg.2.2
    · exact ⟨⊥, Subgroup.commutator_bot_left _, bot_le, fun h => absurd hc h⟩
  choose Pf hPfperf hPfle hPfB using hex
  have hkB : k ∈ ⨆ O : Set.range (rationalRoots S.ρ (rootCharHom a)), orbitCharClosure S 3 O.1 :=
    mem_iSup_of_charElem_family S hK Nat.prime_three hp hp3 hT hap (fun O => orbitCharClosure S 3 O.1)
      (fun O g hg hgM hgn => mem_orbitCharClosure_of_charElem S 3 hg hgM hgn) hk hkm
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup (ModGL τ (AlgebraicClosure K)), P = ⨆ O, Pf O := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup (ModGL τ (AlgebraicClosure K)),
      Y = ⨆ O : {O : Set.range (rationalRoots S.ρ (rootCharHom a)) //
        Nat.Coprime (Nat.card (orbitCharClosure S 3 O.1)) p}, orbitCharClosure S 3 O.1.1 := ⟨_, rfl⟩
  have hPperf : ⁅P, P⁆ = P := by
    rw [hPdef]
    exact commutator_iSup_eq_charQ Pf hPfperf
  have hPle : P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [hPdef]
    exact iSup_le hPfle
  have hkPY : k ∈ P ⊔ Y := by
    have hle : (⨆ O : Set.range (rationalRoots S.ρ (rootCharHom a)), orbitCharClosure S 3 O.1) ≤ P ⊔ Y := by
      refine iSup_le fun O => ?_
      by_cases h : Nat.Coprime (Nat.card (orbitCharClosure S 3 O.1)) p
      · rw [hYdef]
        exact (le_iSup (fun O' : {O : Set.range (rationalRoots S.ρ (rootCharHom a)) //
          Nat.Coprime (Nat.card (orbitCharClosure S 3 O.1)) p} => orbitCharClosure S 3 O'.1.1)
          ⟨O, h⟩).trans le_sup_right
      · rw [hPdef]
        exact (hPfB O h).trans ((le_iSup Pf O).trans le_sup_left)
    exact hle hkB
  have hYnorm : ∀ u ∈ U, u ∈ S.D.model →
      u ∈ Subgroup.normalizer (Y : Set (ModGL τ (AlgebraicClosure K))) := by
    intro u hu huM
    rw [hYdef]
    exact mem_normalizer_iSup_of_conj_mem
      (fun O x hx => conj_mem_orbitCharClosure S 3 (hUnorm O.1 hu) huM hx)
      (fun O x hx => by
        simpa using conj_mem_orbitCharClosure S 3 (hUnorm O.1 (U.inv_mem hu)) (S.D.model.inv_mem huM) hx)
  have hPX : P ≤ toralCentralizer τ (AlgebraicClosure K) a := fun x hx =>
    Subgroup.mem_inf.2 ⟨hΓ (Subgroup.mem_inf.1 (hPle hx)).1, (Subgroup.mem_inf.1 (hPle hx)).2⟩
  have hPU : P ≤ U := by
    rw [hUdef]
    exact perfect_le_rootSpan_kernel hp a hap hPX hPperf
  have hPN : P ≤ Subgroup.normalizer (Y : Set (ModGL τ (AlgebraicClosure K))) := fun x hx =>
    hYnorm x (hPU hx) (hΓM (Subgroup.mem_inf.1 (hPle hx)).1)
  have hmul : k ∈ ((P ⊔ Y : Subgroup (ModGL τ (AlgebraicClosure K))) :
      Set (ModGL τ (AlgebraicClosure K))) := hkPY
  rw [Subgroup.coe_mul_of_left_le_normalizer_right P Y hPN] at hmul
  obtain ⟨g, hgP, y, hyY, hgy⟩ := Set.mem_mul.1 hmul
  have hYU : Y ≤ U := by
    rw [hYdef]
    exact iSup_le fun O => hBU O.1
  have hWU : Y ⊓ S.Γ ≤ U ⊓ S.Γ := fun x hx => ⟨hYU hx.1, hx.2⟩
  have hWn : ((Y ⊓ S.Γ).subgroupOf (U ⊓ S.Γ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hWU]
    intro w u hw hu
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hYnorm u hu.1 (hΓM hu.2)) w).1 hw.1,
      S.Γ.mul_mem (S.Γ.mul_mem hu.2 hw.2) (S.Γ.inv_mem hu.2)⟩
  have hUΓsub : CFSG.Open.IsSubnormal (U ⊓ S.Γ) (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
    have h0 := isSubnormal_kernelRootSpan (L := AlgebraicClosure K) a
    rw [← hUdef] at h0
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.isSubnormal_inf_subgroupOf h0 S.Γ
    have hTC : toralCentralizer τ (AlgebraicClosure K) a ⊓ S.Γ =
        S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
      ext x
      simp only [toralCentralizer, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hΓ h.1, h.2⟩, h.1⟩⟩
    rw [hTC] at h2
    have hle : U ⊓ S.Γ ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := fun x hx =>
      ⟨hx.2, hUd hx.1⟩
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 h2
  have hcommB : Pairwise fun (O O' : {O : Set.range (rationalRoots S.ρ (rootCharHom a)) //
      Nat.Coprime (Nat.card (orbitCharClosure S 3 O.1)) p}) =>
      ∀ x y : ModGL τ (AlgebraicClosure K), x ∈ orbitCharClosure S 3 O.1.1 →
        y ∈ orbitCharClosure S 3 O'.1.1 → Commute x y := by
    intro O O' hne x y hx hy
    obtain ⟨i, hi⟩ := O.1.2
    obtain ⟨j, hj⟩ := O'.1.2
    have hij : rationalRoots S.ρ (rootCharHom a) i ≠ rationalRoots S.ρ (rootCharHom a) j := by
      rw [hi, hj]
      exact fun h => hne (Subtype.ext (Subtype.ext h))
    have hx' := orbitCharClosure_le_rootSpan S 3 _ hx
    have hy' := orbitCharClosure_le_rootSpan S 3 _ hy
    rw [← hi] at hx'
    rw [← hj] at hy'
    exact commute_rootSpan_rationalRoots hker hform hij x hx' y hy'
  have hYcop : Nat.Coprime (Nat.card Y) p := by
    have hrangeY : (Subgroup.noncommPiCoprod hcommB).range = Y := by
      rw [hYdef]
      exact Subgroup.noncommPiCoprod_range
    have hdvd : Nat.card Y ∣ ∏ O : {O : Set.range (rationalRoots S.ρ (rootCharHom a)) //
        Nat.Coprime (Nat.card (orbitCharClosure S 3 O.1)) p}, Nat.card (orbitCharClosure S 3 O.1.1) := by
      rw [← hrangeY, ← Nat.card_pi]
      exact Subgroup.card_range_dvd _
    exact Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.prod_left fun O _ => O.2)
  refine ⟨P, Y ⊓ S.Γ, hPperf, hPle, CFSG.Open.IsSubnormal.step hWU hWn hUΓsub,
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hYcop, g, hgP, y, ⟨hyY, ?_⟩, hgy⟩
  have hy : y = g⁻¹ * k := by rw [← hgy]; group
  rw [hy]
  exact S.Γ.mul_mem (S.Γ.inv_mem (Subgroup.mem_inf.1 (hPle hgP)).1) (Subgroup.mem_inf.1 hk).1

theorem qGenCoprime_three_of_langSetup {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hres : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcRationalLieTypesP p)
    (hK : ringChar K = 3) {C : Type} [Group C] (ι : C →* ModGL τ (AlgebraicClosure K))
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    Inputs256i.QGenCoprime 3 p β := by
  classical
  intro s hs ⟨n, hn⟩
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β _ hβ, hrange]
  have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}).comap ι = fixSubgroup β := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hι _
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hx).1
  have hιs : ι s ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [← hfix]
    exact ⟨s, mem_fixSubgroup.2 hs, rfl⟩
  have hιn : ι s ^ 3 ^ n = 1 := by rw [← map_pow, hn, map_one]
  obtain ⟨P, W, hPperf, hPle, hWsub, hWcop, g, hgP, y, hyW, hgy⟩ :=
    exists_perfect_mul_coprime_three S hK hp hp5 hT hap h1 hιs hιn
  have hPR := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.perfect_le_iSup_rationalComponent_of_prime
    S hp hT hap h1 hTame P hPle hPperf
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ (AlgebraicClosure K) (rootCharHom a)).2.1
  let R : KernelComponent (rootCharHom a) → Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun i => rationalComponent S.ρ S.Γ (rootCharHom a) i
  let Q := {i : KernelComponent (rootCharHom a) // CFSG.IsQuasisimple (R i)}
  have hcompR : ∀ i : Q, IsComponentOf (R i.1) (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
    intro i
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i.1
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple i.2⟩
  have hRrange : ∀ i : Q, R i.1 ≤ ι.range := fun i => (hcompR i).1.trans hCdrange
  let Fq : Q → Subgroup C := fun i => (R i.1).comap ι
  have hmapF : (⨆ i, Fq i).map ι = ⨆ i : Q, R i.1 := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => Subgroup.map_comap_eq_self (hRrange i)
  have hLℓ : ringChar (AlgebraicClosure K) = 3 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, hK]
  have hFchev : ∀ i : Q, Inputs256e.IsChevSub 3 β (Fq i) := by
    intro i
    have hc := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isComponentOf_comap_of_injective ι hι
      (hRrange i) hCdrange (hcompR i)
    rw [hcomapfix] at hc
    obtain ⟨-, hsub, hq⟩ := hc
    let e : ↥(Fq i) ≃* ↥(R i.1) := (Subgroup.equivMapOfInjective (Fq i) ι hι).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (hRrange i)))
    have hdata := hres τ (AlgebraicClosure K) p₀ S a hT hap h1 i.1 i.2
    rw [hLℓ] at hdata
    exact ⟨hsub, hq, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hdata.chev⟩
  have hgF : g ∈ (⨆ i, Fq i).map ι := by
    rw [hmapF]
    exact hPR hgP
  obtain ⟨g', hg', hgg'⟩ := hgF
  have hWr : W ≤ ι.range := hWsub.le.trans hCdrange
  have hWsub' : CFSG.Open.IsSubnormal (W.comap ι) (fixSubgroup β) := by
    have h := isSubnormal_comap_of_injective ι hι hCdrange hWsub
    rwa [hcomapfix] at h
  have hWcop' : Nat.Coprime (Nat.card (W.comap ι)) p := by
    have e1 : Nat.card (W.comap ι) = Nat.card W := by
      rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hWr]
    rw [e1]
    exact hWcop
  obtain ⟨y', rfl⟩ : y ∈ ι.range := hWr hyW
  have hs' : g' * y' = s := hι (by rw [map_mul, hgg', hgy])
  rw [← hs']
  refine Subgroup.mul_mem _ ?_ ?_
  · exact (iSup_le fun i => le_iSup₂_of_le
      (f := fun (J : Subgroup C) (_ : Inputs256i.IsChevSubOrCoprime 3 p β J) => J) (Fq i)
      (Or.inl (hFchev i)) le_rfl) hg'
  · exact le_iSup₂_of_le (f := fun (J : Subgroup C) (_ : Inputs256i.IsChevSubOrCoprime 3 p β J) => J)
      (W.comap ι) (Or.inr ⟨hWsub', hWcop'⟩) le_rfl hyW

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256n

end
