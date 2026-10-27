module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCharFree
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BadAux
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSubB
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnWeyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.SeitzGeneration CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (d4_weyl_cube_of_pow_three d4_fieldActor_pow_three
  monoY weylY actY weylY_actY
  exists_zpow_eq_one_of_commute card_relWeylTwist_D4 eq_or_eq_inv_of_pow_three_eq_one
  ringEquiv_ne_one_of_pow inv_conj_mul_hom_inv conj_mul_hom_mul_conj fieldActor_mem_graphFixedTorus
  normSeq_three)
open CFSG.GH74.GLS.Stage2.OddAut (normSeq normSeq_eq_one_of_pow_eq_one)

theorem card_pow_three_eq_one_le_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] :
    Nat.card {x : G // x ^ 3 = 1} ≤ 3 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le (by norm_num)

theorem nine_le_card_inf_ker {H G : Type*} [Group H] [Group G] [Finite G] [IsCyclic G]
    (Θ : H →* G) (V : Subgroup H) (hVc : Nat.card V = 27) (hV3 : ∀ x ∈ V, x ^ 3 = 1) :
    9 ≤ Nat.card ↥(V ⊓ Θ.ker) := by
  classical
  set θ : V →* G := Θ.comp V.subtype with hθ
  have h1 := Subgroup.card_ker_mul_card_range θ
  have hrange : Nat.card θ.range ≤ 3 := by
    have hinj : Function.Injective (fun y : θ.range => (⟨(y : G), by
        obtain ⟨x, hx⟩ := y.2
        rw [← hx]
        change Θ x ^ 3 = 1
        rw [← map_pow, show (x : H) ^ 3 = 1 from hV3 x x.2, map_one]⟩ : {x : G // x ^ 3 = 1})) := by
      intro a b h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h
    exact (Nat.card_le_card_of_injective _ hinj).trans card_pow_three_eq_one_le_of_isCyclic
  have hker : Nat.card θ.ker = Nat.card ↥(V ⊓ Θ.ker) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : θ.ker => (⟨((x : V) : H),
      Subgroup.mem_inf.2 ⟨(x : V).2, x.2⟩⟩ : ↥(V ⊓ Θ.ker))) ⟨fun a b h => ?_, fun y => ?_⟩)
    · simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    · exact ⟨⟨⟨y, (Subgroup.mem_inf.1 y.2).1⟩, (Subgroup.mem_inf.1 y.2).2⟩, rfl⟩
  rw [hVc] at h1
  by_contra hlt
  push Not at hlt
  have : Nat.card θ.ker * Nat.card θ.range ≤ 8 * 3 :=
    Nat.mul_le_mul (by omega) hrange
  omega

@[expose] def unitsPowThreeEquiv (L : Type) [Field L] :
    {A : Lˣ // A ^ 3 = 1} ≃ rootsOfUnity 3 L where
  toFun A := ⟨A.1, (mem_rootsOfUnity 3 A.1).2 A.2⟩
  invFun A := ⟨A.1, (mem_rootsOfUnity 3 A.1).1 A.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_units_pow_three_eq_one (L : Type) [Field L] : Finite {A : Lˣ // A ^ 3 = 1} :=
  Finite.of_equiv _ (unitsPowThreeEquiv L).symm

theorem card_units_pow_three_eq_one_le (L : Type) [Field L] :
    Nat.card {A : Lˣ // A ^ 3 = 1} ≤ 3 := by
  rw [Nat.card_congr (unitsPowThreeEquiv L)]
  exact card_rootsOfUnity L 3

section Q1

variable {K : Type} [Field K] [Finite K]

theorem coreFreeAt_of_toral_q1 (hA2 : TrialityA2CoreFree) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hh : (h : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (h3 : (MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1) :
    CoreFreeAt 3 (MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ) := by
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hN := normSeq_eq_one_of_pow_eq_one hZ (d4_fieldActor_pow_three K hK σ hσ) h3
  obtain ⟨y, s, -, -, hconj, d, hd, hd3, hsd⟩ := d4_toral_conj_all hℓ hf K hK σ hσ h hh hN
  rw [← coreFreeAt_conj_iff _ (MulAut.conj y), hconj]
  by_cases hd1 : d = 1
  · have hs1 : s = 1 := by
      apply Subtype.ext
      have h1 : (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → Kˣ) =
          (1 : Fin TwistTag.D4.tag.rank → Kˣ) := funext fun i => by fin_cases i <;> rfl
      rw [hsd, hd1, h1, rootDiagUnit_one]
      rfl
    rw [hs1, map_one, one_mul]
    exact coreFreeAt_three_fieldActor_self hℓ hℓ3 hf hK σ hσ
  · exact hA2 ℓ f hℓ hℓ3 hf K hK σ hσ s (Or.inl ⟨hq, d, hd, hd3, hd1, hsd⟩)

theorem exists_toral_outer_q1 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hq : (ℓ ^ f) % 3 = 1) (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (V : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hV3 : ∀ x ∈ V, x ^ 3 = 1) (hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hV0 : ∀ x ∈ V, ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      (g : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
        x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ)
    (hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    (hinner : 3 < Nat.card ↥(V ⊓ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)) :
    ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      ∃ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        (h : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
        (φ = MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ ∨
          φ⁻¹ = MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  obtain ⟨⟨Θ, hΘ, hΘker⟩, hcyc, hcard⟩ := exists_fieldHom_D4 hℓ hf hK σ hσ
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hσ1 : σ ≠ 1 :=
    ringEquiv_ne_one_of_pow (Nat.one_lt_pow (by omega) hℓ.one_lt) hK σ hσ
  have hinn : ∀ x : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      x ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ↔ Θ x = 1 := fun x => by
    rw [← hΘker, MonoidHom.mem_ker]
  have hΘform : ∀ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      Θ (MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ) = δ := fun g δ => hΘ _ g δ rfl
  by_cases hc1 : ∃ x ∈ V, x ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        (g : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
        ∃ δ : K ≃+* K, x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ
  · obtain ⟨x, hxV, hxout, g, hgT, δ, hx⟩ := hc1
    have hΘx : Θ x = δ := by rw [hx]; exact hΘform g δ
    have hδ1 : δ ≠ 1 := fun h => hxout ((hinn x).2 (by rw [hΘx, h]))
    have hδ3 : δ ^ 3 = 1 := by rw [← hΘx, ← map_pow, hV3 x hxV, map_one]
    rcases eq_or_eq_inv_of_pow_three_eq_one hσ1 hσ3 hδ1 hδ3 with h | h
    · rw [h] at hx
      exact ⟨x, hxV, hxout, g, hgT, Or.inl hx⟩
    · rw [h] at hx
      refine ⟨x, hxV, hxout, fieldActor (t := TwistTag.D4) σ σ g⁻¹, ?_, Or.inr ?_⟩
      · exact fieldActor_mem_graphFixedTorus σ σ (x := g⁻¹) (inv_mem hgT)
      · rw [hx]
        exact inv_conj_mul_hom_inv (fieldActorHom (t := TwistTag.D4) σ) g σ
  exfalso
  push Not at hc1
  obtain ⟨e, heV, heout⟩ := hout
  obtain ⟨n, δ, hnM, hen⟩ := hV0 e heV
  have hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom :=
    fun h => hc1 e heV heout n h δ hen
  have hΘe : Θ e = δ := by rw [hen]; exact hΘform n δ
  have hδ1 : δ ≠ 1 := fun h => heout ((hinn e).2 (by rw [hΘe, h]))
  have hδ3 : δ ^ 3 = 1 := by rw [← hΘe, ← map_pow, hV3 e heV, map_one]
  have hδσ := eq_or_eq_inv_of_pow_three_eq_one hσ1 hσ3 hδ1 hδ3
  have he3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1 := by
    rw [← hen]
    exact hV3 e heV
  have hweyl1 : ∀ x : monoY σ, weylY σ x = 1 ↔
      ((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈
        graphFixedTorus TwistTag.D4 K σ.toRingHom := fun x => by
    change graphFixedWeylHom TwistTag.D4 K σ.toRingHom ⟨(x : _).1, x.2⟩ = 1 ↔ _
    rw [← MonoidHom.mem_ker, graphFixedWeylHom_ker, Subgroup.mem_subgroupOf]
  have hweylmem : ∀ x : monoY σ, weylY σ x ∈ relWeylTwist TwistTag.D4 := fun x =>
    graphFixedWeylHom_mem TwistTag.D4 K σ.toRingHom ⟨(x : _).1, x.2⟩
  have hfA3 : fieldActor (t := TwistTag.D4) σ δ ^ 3 = 1 := by
    have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) δ 3
    rw [hδ3, map_one] at h
    exact h.symm
  let nm : monoY σ := ⟨n, hnM⟩
  have hNs : normSeq (fieldActor (t := TwistTag.D4) σ δ) n 3 = 1 :=
    normSeq_eq_one_of_pow_eq_one hZ hfA3 he3
  have hN3 : nm * actY σ δ nm * actY σ δ (actY σ δ nm) = 1 := by
    refine Subtype.ext ?_
    have h : normSeq (fieldActor (t := TwistTag.D4) σ δ) n 3 = n * fieldActor σ δ n *
        fieldActor σ δ (fieldActor σ δ n) := normSeq_three _ n
    change n * fieldActor σ δ n * fieldActor σ δ (fieldActor σ δ n) = 1
    rw [← h]
    exact hNs
  have hwn3 : weylY σ nm ^ 3 = 1 := by
    have h := congrArg (weylY σ) hN3
    simp only [map_mul, weylY_actY, map_one] at h
    rw [pow_three']
    exact h
  have hfix : ∀ ι ∈ V ⊓ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range,
      ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ∃ v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        MulAut.conj v = ι ∧ (v : ModGL TwistTag.D4.tag K) =
          CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.D4.tag
            ![ω, ω, 1, ω] := by
    intro ι hι
    obtain ⟨hιV, v, hv⟩ := Subgroup.mem_inf.1 hι
    by_cases hv1 : v = 1
    · refine ⟨1, one_pow 3, v, hv, ?_⟩
      have h1 : (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → Kˣ) =
          (1 : Fin TwistTag.D4.tag.rank → Kˣ) := funext fun i => by fin_cases i <;> rfl
      rw [hv1, h1, rootDiagUnit_one]
      rfl
    have hv3 : v ^ 3 = 1 := by
      apply hinj
      rw [map_pow, hv, hV3 ι hιV, map_one]
    have hvM : (v : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom := by
      obtain ⟨g', δ', hg'M, hιg'⟩ := hV0 ι hιV
      have hΘι : Θ ι = 1 := (hinn ι).1 ⟨v, hv⟩
      have hδ' : δ' = 1 := (hΘ ι g' δ' hιg').symm.trans hΘι
      rw [hδ', fieldActor_one, mul_one] at hιg'
      have : v = g' := hinj (hv.trans hιg')
      rw [this]
      exact hg'M
    let vm : monoY σ := ⟨v, hvM⟩
    have hwv3 : weylY σ vm ^ 3 = 1 := by
      rw [← map_pow, show vm ^ 3 = 1 from Subtype.ext hv3, map_one]
    have hcomm : nm * actY σ δ vm = vm * nm := by
      have h := hVcomm e heV ι hιV
      rw [hen, ← hv] at h
      have h1 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) * MulAut.conj v =
          MulAut.conj (n * fieldActor σ δ v) * fieldActor σ δ :=
        conj_mul_hom_mul_conj (fieldActorHom (t := TwistTag.D4) σ) n v δ
      have h2 : MulAut.conj v * (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) =
          MulAut.conj (v * n) * fieldActor σ δ := by rw [← mul_assoc, ← map_mul]
      rw [h1, h2] at h
      exact Subtype.ext (hinj (mul_right_cancel h))
    have hwcomm : weylY σ nm * weylY σ vm = weylY σ vm * weylY σ nm := by
      have h := congrArg (weylY σ) hcomm
      rw [map_mul, map_mul, weylY_actY] at h
      exact h
    by_cases hwv1 : weylY σ vm = 1
    ·
      have hvT := (hweyl1 vm).1 hwv1
      have hev : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v := by
        rw [← hen]
        have h := hVcomm e heV ι hιV
        rw [← hv] at h
        have h1 : e * MulAut.conj v = MulAut.conj (e v) * e := mulAut_mul_conj e v
        rw [h] at h1
        exact (hinj (mul_right_cancel h1)).symm
      obtain ⟨ω, -, hω3, -, hω⟩ := d4_fixed_line_all hq K σ hσ v n δ hvT hv1 hv3 hnM
        hnT (d4_weyl_cube_of_pow_three K hK σ hσ n δ hδσ hnM he3) hδσ hev
      exact ⟨ω, hω3, v, hv, hω⟩
    ·
      exfalso
      obtain ⟨j, hj⟩ := exists_zpow_eq_one_of_commute (weylY σ) (relWeylTwist TwistTag.D4)
        card_relWeylTwist_D4 hweylmem nm vm hwn3 hwv3 hwcomm hwv1
      let g'' : monoY σ := nm * actY σ δ vm ^ j
      have hg''W : weylY σ g'' = 1 := by
        change weylY σ (nm * actY σ δ vm ^ j) = 1
        rw [map_mul, map_zpow, weylY_actY]
        exact hj
      have hg''T := (hweyl1 g'').1 hg''W
      have hcoe : (g'' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
          n * fieldActor σ δ (v ^ j) := by
        rw [map_zpow]
        rfl
      have hee : e * ι ^ j = MulAut.conj (g'' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) *
          fieldActor σ δ := by
        rw [hcoe, hen, ← hv, ← map_zpow]
        exact conj_mul_hom_mul_conj (fieldActorHom (t := TwistTag.D4) σ) n (v ^ j) δ
      have hΘ' : Θ (e * ι ^ j) = δ := by rw [hee]; exact hΘform _ δ
      exact hc1 (e * ι ^ j) (mul_mem heV (zpow_mem hιV j))
        (fun h => hδ1 (hΘ'.symm.trans ((hinn _).1 h))) _ hg''T δ hee
  choose ω hω3 v hv hvω using hfix
  have hinj' : Function.Injective (fun ι : ↥(V ⊓ (MulAut.conj :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) =>
      (⟨ω ι ι.2, hω3 ι ι.2⟩ : {x : Kˣ // x ^ 3 = 1})) := by
    intro a b hab
    have h1 : ω a a.2 = ω b b.2 := congrArg Subtype.val hab
    have h2 : v a a.2 = v b b.2 := Subtype.ext (by rw [hvω, hvω, h1])
    apply Subtype.ext
    rw [← hv a a.2, ← hv b b.2, h2]
  have h3 := (Nat.card_le_card_of_injective _ hinj').trans
    (card_pow_three_eq_one_le_of_isCyclic (G := Kˣ))
  omega

theorem exists_coreFree_of_elemAbelian_q1 (hA2 : TrialityA2CoreFree) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (D : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 3) :
    ∃ x ∈ D, x ≠ 1 ∧ CoreFreeAt 3 x := by
  classical
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨⟨Θ, -, hΘker⟩, hcyc, hcard'⟩ := exists_fieldHom_D4 hℓ hf hK σ hσ
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard']; omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDp : IsPGroup 3 D := IsPGroup.of_card hcard
  obtain ⟨β, hβ⟩ := d4_exists_conj_le_B0_all hℓ hf K hK σ hσ hq D hDp
  set V := D.map (MulAut.conj β⁻¹).toMonoidHom with hV
  have hmemV : ∀ x' ∈ V, ∃ x ∈ D, x' = β⁻¹ * x * β := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hD3 : ∀ x ∈ D, x ^ 3 = 1 := hD.2
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hV3 : ∀ x ∈ V, x ^ 3 = 1 := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := hmemV x' hx'
    rw [show β⁻¹ * x * β = MulAut.conj β⁻¹ x by rw [MulAut.conj_apply, inv_inv], ← map_pow,
      hD3 x hx, map_one]
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x' hx' y' hy'
    obtain ⟨x, hx, rfl⟩ := hmemV x' hx'
    obtain ⟨y, hy, rfl⟩ := hmemV y' hy'
    calc β⁻¹ * x * β * (β⁻¹ * y * β) = β⁻¹ * (x * y) * β := by group
      _ = β⁻¹ * (y * x) * β := by rw [hDcomm x hx y hy]
      _ = β⁻¹ * y * β * (β⁻¹ * x * β) := by group
  have hV0 : ∀ x ∈ V, ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      (g : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
        x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := hmemV x' hx'
    exact hβ x hx
  have hVc : Nat.card V = 27 := by
    rw [hV, Subgroup.card_map_of_injective (MulAut.conj β⁻¹).injective, hcard]
    norm_num
  have hinner : 3 < Nat.card ↥(V ⊓ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) := by
    have h9 := nine_le_card_inf_ker Θ V hVc hV3
    rw [hΘker] at h9
    omega
  have hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    by_contra h
    push Not at h
    have hr : RankLE2 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun F hF =>
      (card_le_nine_of_graphFixedRootGroup_ne_three hℓ hℓ3 hf hK (σ := σ.toRingHom) hσ F
        ⟨hF.1, hF.2⟩).trans (by norm_num)
    have hVe : IsElemAbelian 3 V := ⟨⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩, hV3⟩
    exact false_of_inner_cube_of_rankLE2 Nat.prime_three hinj hr hVe (by rw [hVc]; norm_num)
      fun x hx => h x hx
  obtain ⟨φ, hφV, hφout, h, hh, hφ⟩ :=
    exists_toral_outer_q1 hℓ hf hq hK σ hσ V hV3 hVcomm hV0 hout hinner
  obtain ⟨x, hxD, rfl⟩ := hmemV φ hφV
  refine ⟨x, hxD, ?_, ?_⟩
  · rintro rfl
    exact hφout ⟨1, by rw [map_one, mul_one, inv_mul_cancel]⟩
  · rw [← coreFreeAt_conj_iff x β⁻¹, inv_inv]
    have h3 : (MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
      rcases hφ with hφ | hφ
      · rw [← hφ]
        exact hV3 _ hφV
      · rw [← hφ, inv_pow, hV3 _ hφV, inv_one]
    have hcf := coreFreeAt_of_toral_q1 hA2 hℓ hℓ3 hf hq hK σ hσ h hh h3
    rcases hφ with hφ | hφ
    · rw [hφ]
      exact hcf
    · have h4 := hcf.inv
      rwa [← hφ, inv_inv] at h4

end Q1

section Q2

open CFSG.GH74.GLS.Stage2.Bender.Thm1 (D4MinusFrame D4MinusToral d4MinusPsi d4Minus_torus_h1
  d4MinusPsi_mem_range_iff d4MinusPsi_fieldActor d4MinusPsi_injective d4MinusPsi_apply
  d4Minus_exists_N' mnWeyl_exists_zpow_mul_mem mnWeyl_inv_mul_apply_mem conj_twist_eq)
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf twistedTorusOf_le_adjointGroup)
open CFSG.RankThree.PartOne.KGD (triEmb)
open CFSG.RankThree.Chevalley (trialityOpposition)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {K : Type} [Field K] [Finite K]

theorem coreFreeAt_of_toral_q2 (hA2 : TrialityA2CoreFree) {ℓ f : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame ℓ f L g₀)
    (t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (ht : d4MinusPsi σ L g₀ t ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)))
    (hcoc : t * fieldActor (t := TwistTag.D4) σ σ t *
      fieldActor (t := TwistTag.D4) σ σ (fieldActor (t := TwistTag.D4) σ σ t) = 1) :
    CoreFreeAt 3 (MulAut.conj t * fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := id hg₀
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  have hcoc' : d4MinusPsi σ L g₀ t *
      ((diagramMap TwistTag.D4 L)⁻¹ * d4MinusPsi σ L g₀ t * diagramMap TwistTag.D4 L) *
      ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * d4MinusPsi σ L g₀ t *
        diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) = 1 := by
    have := congrArg (d4MinusPsi σ L g₀) hcoc
    simpa only [map_mul, d4MinusPsi_fieldActor Fr hcomm hg₀P, map_one] using this
  obtain ⟨e, he, b, hb3, -, hrel⟩ :=
    d4Minus_torus_h1 (dvd_pow_self ℓ (by omega) : ℓ ∣ ℓ ^ f) Fr hFr ht hcoc'
  obtain ⟨y₁, hy₁⟩ := (d4MinusPsi_mem_range_iff hℓ hf hK hσ Fr hFr hg₀C hg₀F e).2
    ⟨twistedTorusOf_le_adjointGroup _ _ he, (mem_twistedTorusOf.1 he).2⟩
  set δ := fieldActor (t := TwistTag.D4) σ σ with hδ
  have hψs : d4MinusPsi σ L g₀ (y₁ * t * (δ y₁)⁻¹) =
      rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] := by
    rw [map_mul, map_mul, map_inv, hy₁, hδ, d4MinusPsi_fieldActor Fr hcomm hg₀P, hy₁]
    exact hrel
  rw [← coreFreeAt_conj_iff _ (MulAut.conj y₁), conj_twist_eq δ y₁ t]
  by_cases hb1 : b = 1
  · have hs1 : y₁ * t * (δ y₁)⁻¹ = 1 := by
      apply d4MinusPsi_injective g₀
      have h1 : (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ) = 1 := by
        rw [hb1]
        funext i
        fin_cases i <;> rfl
      rw [hψs, h1]
      exact (rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)).trans (map_one _).symm
    rw [hs1, map_one, one_mul]
    exact coreFreeAt_three_fieldActor_self hℓ hℓ3 hf hK σ hσ
  · have hs : D4MinusToral ℓ f hℓ K σ (y₁ * t * (δ y₁)⁻¹) := by
      have h := hψs
      rw [d4MinusPsi_apply] at h
      refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, g₀, b, hg₀, hb3,
        hb1, ?_⟩
      calc triEmb K σ L (y₁ * t * (δ y₁)⁻¹) =
          g₀ * (g₀⁻¹ * triEmb K σ L (y₁ * t * (δ y₁)⁻¹) * g₀) * g₀⁻¹ := by group
        _ = _ := by rw [h]
    exact hA2 ℓ f hℓ hℓ3 hf K hK σ hσ _ (Or.inr ⟨hq, hs⟩)

theorem exists_toral_outer_q2 {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame ℓ f L g₀)
    (T' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (m' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hT' : ∀ y, y ∈ T' ↔ d4MinusPsi σ L g₀ y ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)))
    (hm'T : m' ∉ T') (hm'3 : m' ^ 3 ∈ T') (hm'n : ∀ t ∈ T', m' * t * m'⁻¹ ∈ T')
    (hm'δ : fieldActor (t := TwistTag.D4) σ σ m' = m')
    (hTδ : ∀ t ∈ T', fieldActor (t := TwistTag.D4) σ σ t ∈ T')
    (hNmono : ∀ n ∈ T' ⊔ Subgroup.zpowers m',
      d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L ∧
        (d4MinusPsi σ L g₀ n ∈ torusGroup TwistTag.D4.tag L →
          d4MinusPsi σ L g₀ n ∈ twistedTorusOf (trialityOpposition L)
            (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))))
    (V : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hV3 : ∀ x ∈ V, x ^ 3 = 1) (hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hV0 : ∀ x ∈ V, ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      g ∈ T' ⊔ Subgroup.zpowers m' ∧ (δ = 1 ∨ δ = σ ∨ δ = σ⁻¹) ∧
        x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ)
    (hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    (hinner : 3 < Nat.card ↥(V ⊓ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)) :
    ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      ∃ t ∈ T', (φ = MulAut.conj t * fieldActor (t := TwistTag.D4) σ σ ∨
          φ⁻¹ = MulAut.conj t * fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  obtain ⟨⟨Θ, hΘ, hΘker⟩, hcyc, hcard⟩ := exists_fieldHom_D4 hℓ hf hK σ hσ
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hσ1 : σ ≠ 1 :=
    ringEquiv_ne_one_of_pow (Nat.one_lt_pow (by omega) hℓ.one_lt) hK σ hσ
  have hD3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := d4_fieldActor_pow_three K hK σ hσ
  have hDinv : fieldActor (t := TwistTag.D4) σ σ⁻¹ =
      fieldActor (t := TwistTag.D4) σ σ * fieldActor (t := TwistTag.D4) σ σ := by
    have h1 : fieldActor (t := TwistTag.D4) σ σ⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹ :=
      map_inv (fieldActorHom (t := TwistTag.D4) σ) σ
    rw [h1]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_three]
    exact hD3
  have hstab : ∀ δ : K ≃+* K, (δ = σ ∨ δ = σ⁻¹) →
      fieldActor (t := TwistTag.D4) σ δ m' = m' ∧
        ∀ t ∈ T', fieldActor (t := TwistTag.D4) σ δ t ∈ T' := by
    intro δ hδ
    rcases hδ with h | h
    · rw [h]
      exact ⟨hm'δ, hTδ⟩
    · rw [h, hDinv]
      exact ⟨by rw [MulAut.mul_apply, hm'δ, hm'δ], fun t ht => by
        rw [MulAut.mul_apply]
        exact hTδ _ (hTδ t ht)⟩
  have hinn : ∀ x : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      x ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ↔ Θ x = 1 := fun x => by
    rw [← hΘker, MonoidHom.mem_ker]
  have hΘform : ∀ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      Θ (MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ) = δ := fun g δ => hΘ _ g δ rfl
  by_cases hc1 : ∃ x ∈ V, x ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, g ∈ T' ∧
        ∃ δ : K ≃+* K, x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ
  · obtain ⟨x, hxV, hxout, g, hgT, δ, hx⟩ := hc1
    have hΘx : Θ x = δ := by rw [hx]; exact hΘform g δ
    have hδ1 : δ ≠ 1 := fun h => hxout ((hinn x).2 (by rw [hΘx, h]))
    have hδ3 : δ ^ 3 = 1 := by rw [← hΘx, ← map_pow, hV3 x hxV, map_one]
    rcases eq_or_eq_inv_of_pow_three_eq_one hσ1 hσ3 hδ1 hδ3 with h | h
    · rw [h] at hx
      exact ⟨x, hxV, hxout, g, hgT, Or.inl hx⟩
    · rw [h] at hx
      refine ⟨x, hxV, hxout, fieldActor (t := TwistTag.D4) σ σ g⁻¹, hTδ _ (inv_mem hgT),
        Or.inr ?_⟩
      rw [hx]
      exact inv_conj_mul_hom_inv (fieldActorHom (t := TwistTag.D4) σ) g σ
  exfalso
  push Not at hc1
  obtain ⟨e, heV, heout⟩ := hout
  obtain ⟨n, δ, hnN, hδ, hen⟩ := hV0 e heV
  have hnT : n ∉ T' := fun h => hc1 e heV heout n h δ hen
  have hΘe : Θ e = δ := by rw [hen]; exact hΘform n δ
  have hδ1 : δ ≠ 1 := fun h => heout ((hinn e).2 (by rw [hΘe, h]))
  have hδσ : δ = σ ∨ δ = σ⁻¹ := hδ.resolve_left hδ1
  have he3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1 := by
    rw [← hen]
    exact hV3 e heV
  have hfix : ∀ ι ∈ V ⊓ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range,
      ∃ A : Lˣ, A ^ 3 = 1 ∧ ∃ v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        MulAut.conj v = ι ∧ d4MinusPsi σ L g₀ v = rootDiagUnit TwistTag.D4.tag ![A, A, 1, A] := by
    intro ι hι
    obtain ⟨hιV, v, hv⟩ := Subgroup.mem_inf.1 hι
    by_cases hv1 : v = 1
    · refine ⟨1, one_pow 3, v, hv, ?_⟩
      have h1 : (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → Lˣ) = 1 := by
        funext i
        fin_cases i <;> rfl
      rw [hv1, map_one, h1]
      exact (rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)).symm
    have hv3 : v ^ 3 = 1 := by
      apply hinj
      rw [map_pow, hv, hV3 ι hιV, map_one]
    have hvN : v ∈ T' ⊔ Subgroup.zpowers m' := by
      obtain ⟨g', δ', hg'N, -, hιg'⟩ := hV0 ι hιV
      have hΘι : Θ ι = 1 := (hinn ι).1 ⟨v, hv⟩
      have hδ' : δ' = 1 := (hΘ ι g' δ' hιg').symm.trans hΘι
      rw [hδ', fieldActor_one, mul_one] at hιg'
      have : v = g' := hinj (hv.trans hιg')
      rw [this]
      exact hg'N
    by_cases hvT : v ∈ T'
    · have hev : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v := by
        rw [← hen]
        have h := hVcomm e heV ι hιV
        rw [← hv] at h
        have h1 : e * MulAut.conj v = MulAut.conj (e v) * e := mulAut_mul_conj e v
        rw [h] at h1
        exact (hinj (mul_right_cancel h1)).symm
      obtain ⟨A, hA3, -, hA⟩ := d4Minus_fixed_line_all hℓ hf hq K hK σ hσ L hg₀ v n δ
        ((hT' v).1 hvT) hv1 hv3 (hNmono n hnN).1
        (fun htor => hnT ((hT' n).2 ((hNmono n hnN).2 htor))) hδσ he3 hev
      exact ⟨A, hA3, v, hv, hA⟩
    · exfalso
      obtain ⟨j, hj⟩ := mnWeyl_exists_zpow_mul_mem hm'T hm'3 hm'n hnN hvN hvT
      obtain ⟨hDm, hDT⟩ := hstab δ hδσ
      have hg'' : n * fieldActor (t := TwistTag.D4) σ δ (v ^ j) ∈ T' := by
        have h1 := mnWeyl_inv_mul_apply_mem hm'3 hm'n (fieldActor (t := TwistTag.D4) σ δ) hDm
          hDT (zpow_mem hvN j)
        have e : n * fieldActor (t := TwistTag.D4) σ δ (v ^ j) =
            (n * v ^ j) * ((v ^ j)⁻¹ * fieldActor (t := TwistTag.D4) σ δ (v ^ j)) := by
          rw [mul_assoc, mul_inv_cancel_left]
        rw [e]
        exact mul_mem hj h1
      have hee : e * ι ^ j = MulAut.conj (n * fieldActor (t := TwistTag.D4) σ δ (v ^ j)) *
          fieldActor (t := TwistTag.D4) σ δ := by
        rw [hen, ← hv, ← map_zpow]
        exact conj_mul_hom_mul_conj (fieldActorHom (t := TwistTag.D4) σ) n (v ^ j) δ
      have hΘ' : Θ (e * ι ^ j) = δ := by rw [hee]; exact hΘform _ δ
      exact hc1 (e * ι ^ j) (mul_mem heV (zpow_mem hιV j))
        (fun h => hδ1 (hΘ'.symm.trans ((hinn _).1 h))) _ hg'' δ hee
  choose A hA3 v hv hvA using hfix
  have hinj' : Function.Injective (fun ι : ↥(V ⊓ (MulAut.conj :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) =>
      (⟨A ι ι.2, hA3 ι ι.2⟩ : {x : Lˣ // x ^ 3 = 1})) := by
    intro a b hab
    have h1 : A a a.2 = A b b.2 := congrArg Subtype.val hab
    have h2 : v a a.2 = v b b.2 := d4MinusPsi_injective g₀ (by rw [hvA, hvA, h1])
    apply Subtype.ext
    rw [← hv a a.2, ← hv b b.2, h2]
  have := finite_units_pow_three_eq_one L
  have h3 := (Nat.card_le_card_of_injective _ hinj').trans (card_units_pow_three_eq_one_le L)
  omega

theorem exists_coreFree_of_elemAbelian_q2 (hA2 : TrialityA2CoreFree) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (D : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 3) :
    ∃ x ∈ D, x ≠ 1 ∧ CoreFreeAt 3 x := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have : CharP K ℓ := by
    have : Fintype K := Fintype.ofFinite K
    have h : Fintype.card K = ℓ ^ (f * 3) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]
    exact charP_of_card_eq_prime_pow h
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨g₀, hg₀C, hg₀P, hg₀F⟩ := d4Minus_exists_frame_all (L := AlgebraicClosure K) ℓ hf
  have hg₀ : D4MinusFrame ℓ f (AlgebraicClosure K) g₀ := ⟨hg₀C, hg₀P, hg₀F⟩
  obtain ⟨T', m', hT', hm'T, hm'3, hm'n, hm'δ, hTδ, hidx, hNmono, -, -⟩ :=
    d4Minus_exists_N' (σ := σ) hf hq hK hσ hg₀
  have hNδ : ∀ x ∈ T' ⊔ Subgroup.zpowers m',
      fieldActor (t := TwistTag.D4) σ σ x ∈ T' ⊔ Subgroup.zpowers m' := by
    have hle : T' ⊔ Subgroup.zpowers m' ≤ (T' ⊔ Subgroup.zpowers m').comap
        ((fieldActor (t := TwistTag.D4) σ σ : MulAut _).toMonoidHom) := by
      refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_sup_left (hTδ t ht)
      · change fieldActor (t := TwistTag.D4) σ σ m' ∈ T' ⊔ Subgroup.zpowers m'
        rw [hm'δ]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers m')
    exact fun x hx => hle hx
  obtain ⟨⟨Θ, -, hΘker⟩, hcyc, hcard'⟩ := exists_fieldHom_D4 hℓ hf hK σ hσ
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard']; omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD3 : ∀ x ∈ D, x ^ 3 = 1 := hD.2
  obtain ⟨β, hβ⟩ := d4_exists_conj_le_Bδ_all hℓ hf K hK σ hσ _ hidx hNδ D hD3
  set V := D.map (MulAut.conj β⁻¹).toMonoidHom with hV
  have hmemV : ∀ x' ∈ V, ∃ x ∈ D, x' = β⁻¹ * x * β := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hV3 : ∀ x ∈ V, x ^ 3 = 1 := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := hmemV x' hx'
    rw [show β⁻¹ * x * β = MulAut.conj β⁻¹ x by rw [MulAut.conj_apply, inv_inv], ← map_pow,
      hD3 x hx, map_one]
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x' hx' y' hy'
    obtain ⟨x, hx, rfl⟩ := hmemV x' hx'
    obtain ⟨y, hy, rfl⟩ := hmemV y' hy'
    calc β⁻¹ * x * β * (β⁻¹ * y * β) = β⁻¹ * (x * y) * β := by group
      _ = β⁻¹ * (y * x) * β := by rw [hDcomm x hx y hy]
      _ = β⁻¹ * y * β * (β⁻¹ * x * β) := by group
  have hV0 : ∀ x ∈ V, ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      g ∈ T' ⊔ Subgroup.zpowers m' ∧ (δ = 1 ∨ δ = σ ∨ δ = σ⁻¹) ∧
        x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := hmemV x' hx'
    exact hβ x hx
  have hVc : Nat.card V = 27 := by
    rw [hV, Subgroup.card_map_of_injective (MulAut.conj β⁻¹).injective, hcard]
    norm_num
  have hinner : 3 < Nat.card ↥(V ⊓ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) := by
    have h9 := nine_le_card_inf_ker Θ V hVc hV3
    rw [hΘker] at h9
    omega
  have hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    by_contra h
    push Not at h
    have hr : RankLE2 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun F hF =>
      (card_le_nine_of_graphFixedRootGroup_ne_three hℓ hℓ3 hf hK (σ := σ.toRingHom) hσ F
        ⟨hF.1, hF.2⟩).trans (by norm_num)
    have hVe : IsElemAbelian 3 V := ⟨⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩, hV3⟩
    exact false_of_inner_cube_of_rankLE2 Nat.prime_three hinj hr hVe (by rw [hVc]; norm_num)
      fun x hx => h x hx
  obtain ⟨φ, hφV, hφout, t, ht, hφ⟩ := exists_toral_outer_q2 hℓ hf hq hK σ hσ
    (AlgebraicClosure K) hg₀ T' m' hT' hm'T hm'3 hm'n hm'δ hTδ hNmono V hV3 hVcomm hV0 hout
    hinner
  obtain ⟨x, hxD, rfl⟩ := hmemV φ hφV
  refine ⟨x, hxD, ?_, ?_⟩
  · rintro rfl
    exact hφout ⟨1, by rw [map_one, mul_one, inv_mul_cancel]⟩
  · rw [← coreFreeAt_conj_iff x β⁻¹, inv_inv]
    have h3 : (MulAut.conj t * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
      rcases hφ with hφ | hφ
      · rw [← hφ]
        exact hV3 _ hφV
      · rw [← hφ, inv_pow, hV3 _ hφV, inv_one]
    have hN := normSeq_eq_one_of_pow_eq_one hZ (d4_fieldActor_pow_three K hK σ hσ) h3
    rw [normSeq_three] at hN
    have hcf := coreFreeAt_of_toral_q2 hA2 hℓ hℓ3 hf hq hK σ hσ (AlgebraicClosure K) hg₀ t
      ((hT' t).1 ht) hN
    rcases hφ with hφ | hφ
    · rw [hφ]
      exact hcf
    · have h4 := hcf.inv
      rwa [← hφ, inv_inv] at h4

end Q2

section Assembly

variable {K : Type} [Field K] [Finite K]

theorem isLocallyBalancedAbs_three_of_a2CoreFree (hA2 : TrialityA2CoreFree) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    IsLocallyBalancedAbs 3 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  intro D hD hcard H hH _
  have hq : (ℓ ^ f) % 3 = 1 ∨ (ℓ ^ f) % 3 = 2 := by
    have hn : ¬ 3 ∣ ℓ ^ f := not_three_dvd_prime_pow hℓ hℓ3 f
    omega
  obtain ⟨x, hxD, hx1, hcf⟩ : ∃ x ∈ D, x ≠ 1 ∧ CoreFreeAt 3 x := by
    rcases hq with hq | hq
    · exact exists_coreFree_of_elemAbelian_q1 hA2 hℓ hℓ3 hf hq hK σ hσ D hD hcard
    · exact exists_coreFree_of_elemAbelian_q2 hA2 hℓ hℓ3 hf hq hK σ hσ D hD hcard
  exact localDeltaIn_eq_bot_of_coreFree Nat.prime_three hinj hH hxD hx1 hcf

theorem crossCharFamAt_trialityD4_three_of_a2CoreFree_all (hA2 : TrialityA2CoreFree) :
    CrossCharFamAt .trialityD4 fun _ p => p = 3 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ p - - hc rfl
  change d = _ at hd
  subst hd
  have hq3 : q.p ≠ 3 := fun h => hc (by simp [h])
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_three_of_a2CoreFree hA2 q.prime_p hq3 q.exponent_pos hK σ hσ)

end Assembly

end CFSG.HardMathSupport.Timmesfeld.CrossChar
