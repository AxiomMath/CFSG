module

public import CFSG.LieType.SeitzGeneration.CubeCoverE6All24

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverField

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.CubeCoverE6
  CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LocalAnalysis.GLTheoremB
  CFSG.RankThree.PartOne.CTP
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

theorem seitzHyperGamma_eq_top_of_cover_overgroups {K S : Type*} [Group K] [Group S] [Finite K]
    (hperf : commutator K = ⊤) (θ : K ⧸ Subgroup.center K ≃* S) {p : ℕ} (hp : p.Prime)
    {D : Subgroup (MulAut S)} {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (hED : ¬ coverImage θ E ≤ D) (hA : coverImage θ E ⊓ D ≠ ⊥)
    (hJ : ∀ x ∈ coverImage θ E, x ∉ D → ∃ J : Subgroup S, J ≤ fixedSubgroup x ∧
      J ≤ Subgroup.closure {k | k ∈ J ∧ (∃ m : ℕ, ¬ p ∣ m ∧ k ^ m = 1) ∧
        ∃ b ∈ coverImage θ E ⊓ D, b ≠ 1 ∧ b k = k} ∧
      (∀ a ∈ coverImage θ E ⊓ D, (∀ k ∈ J, a k = k) → a = 1) ∧
      ∀ H : Subgroup S, J ≤ H → H ≤ fixedSubgroup x ∨ H = ⊤) :
    seitzHyperGamma p E = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite S := Finite.of_surjective θ.toMonoidHom θ.surjective
  let π : K →* S := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  let ind : MulAut K →* MulAut S :=
    (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)
  have hcover : coverImage θ E = E.map ind := rfl
  have hind : Function.Injective ind :=
    (MulAut.congr θ).injective.comp (quotientCenterAut'_injective hperf)
  have hπker : π.ker = Subgroup.center K :=
    (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center K))
      θ.toMonoidHom θ.injective).trans (QuotientGroup.ker_mk' _)
  have hπsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hind_apply : ∀ (f : MulAut K) (g : K), π (f g) = ind f (π g) := by
    intro f g
    simp [π, ind, MulAut.congr, quotientCenterAut']
  have hEab : IsElemAbelian p (coverImage θ E) := isElemAbelian_coverImage θ hE
  have hcardE : Nat.card (coverImage θ E) = p ^ 3 := by
    rw [card_coverImage hperf θ E, hEc]
  have key : ∀ (x : MulAut S) (hxE : x ∈ coverImage θ E) (hxD : x ∉ D) (J : Subgroup S),
      J ≤ fixedSubgroup x →
      J ≤ Subgroup.closure {k | k ∈ J ∧ (∃ m : ℕ, ¬ p ∣ m ∧ k ^ m = 1) ∧
        ∃ b ∈ coverImage θ E ⊓ D, b ≠ 1 ∧ b k = k} →
      J ≤ (seitzHyperGamma p E).map π := by
    intro x hxE hxD J hJx hJg
    refine hJg.trans ((Subgroup.closure_le _).2 ?_)
    rintro k ⟨hkJ, ⟨m, hmp, hkm⟩, b, hb, hb1, hbk⟩
    have hxb : x ∉ Subgroup.zpowers b := fun h =>
      hxD (Subgroup.zpowers_le.2 hb.2 h)
    have hFE : Subgroup.closure ({b, x} : Set (MulAut S)) ≤ coverImage θ E :=
      (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hb.1, Set.singleton_subset_iff.2 hxE⟩)
    have hrel : (Subgroup.closure ({b, x} : Set (MulAut S))).relIndex
        (coverImage θ E) = p :=
      relIndex_closure_pair_of_not_mem hp hEab hcardE hb.1 hxE hb1 hxb
    let F : Subgroup (MulAut K) :=
      (Subgroup.closure ({b, x} : Set (MulAut S))).comap ind ⊓ E
    have hFmap : F.map ind = Subgroup.closure ({b, x} : Set (MulAut S)) := by
      apply le_antisymm
      · rintro _ ⟨f, hf, rfl⟩
        exact hf.1
      · intro y hy
        have hyE : y ∈ E.map ind := by rw [← hcover]; exact hFE hy
        obtain ⟨e, heE, heq⟩ := Subgroup.mem_map.1 hyE
        have hce : e ∈ Subgroup.comap ind (Subgroup.closure ({b, x} : Set (MulAut S))) := by
          rw [Subgroup.mem_comap, heq]
          exact hy
        exact Subgroup.mem_map.2 ⟨e, ⟨hce, heE⟩, heq⟩
    have hFrel : F.relIndex E = p := by
      have h1 := Subgroup.relIndex_map_map_of_injective F E hind
      rw [hFmap, ← hcover] at h1
      exact h1.symm.trans hrel
    have hFp : IsPGroup p ↥F :=
      (CFSG.Open.IsElemAbelian.isPGroup hE).of_injective
        (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
    obtain ⟨y, hy⟩ := hπsurj k
    have hst : Subgroup.closure ({b, x} : Set (MulAut S)) ≤
        MulAction.stabilizer (MulAut S) k := by
      rw [Subgroup.closure_le]
      refine Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩
      · exact MulAction.mem_stabilizer_iff.2 hbk
      · exact MulAction.mem_stabilizer_iff.2 (hJx hkJ)
    have hfixF : ∀ f ∈ F, y⁻¹ * f y ∈ Subgroup.center K := by
      intro f hf
      have hfk : ind f k = k :=
        MulAction.mem_stabilizer_iff.1 (hst hf.1)
      rw [← hπker]
      refine MonoidHom.mem_ker.2 ?_
      rw [map_mul, map_inv, hind_apply f y, hy, hfk, inv_mul_cancel]
    have hpow : ∃ m : ℕ, ¬ p ∣ m ∧ y ^ m ∈ Subgroup.center K := by
      refine ⟨m, hmp, ?_⟩
      rw [← hπker]
      refine MonoidHom.mem_ker.2 ?_
      rw [map_pow, hy, hkm]
    obtain ⟨y', hy'c, hy'fix⟩ := exists_fixed_mul_center hFp hfixF (Or.inr hpow)
    have hΓ : y' ∈ seitzHyperGamma p E :=
      (le_iSup₂_of_le (f := fun (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E = p) =>
        fixedPoints F) F ⟨inf_le_right, hFrel⟩ le_rfl) (mem_fixedPoints.2 hy'fix)
    have hπy' : π y' = k := by
      have h1 : π (y⁻¹ * y') = 1 := by
        rw [← MonoidHom.mem_ker, hπker]
        exact hy'c
      rw [map_mul, map_inv] at h1
      have h2 : π y = π y' := inv_mul_eq_one.mp h1
      exact h2.symm.trans hy
    exact Subgroup.mem_map.2 ⟨y', hΓ, hπy'⟩
  obtain ⟨x, hxE, hxD⟩ : ∃ x ∈ coverImage θ E, x ∉ D := by
    by_contra h
    push Not at h
    exact hED fun y hy => h y hy
  obtain ⟨a, haED, ha1⟩ : ∃ a ∈ coverImage θ E ⊓ D, a ≠ 1 := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
    exact ⟨a, ha, fun h => ha1 (Subtype.ext h)⟩
  have hxaE : x * a ∈ coverImage θ E := (coverImage θ E).mul_mem hxE haED.1
  have hxaD : x * a ∉ D := fun h => hxD (by simpa using D.mul_mem h (D.inv_mem haED.2))
  obtain ⟨J₁, hJ₁x, hJ₁g, -, hJ₁m⟩ := hJ x hxE hxD
  obtain ⟨J₂, hJ₂x, hJ₂g, hJ₂f, -⟩ := hJ (x * a) hxaE hxaD
  have hJ₁le : J₁ ≤ (seitzHyperGamma p E).map π := key x hxE hxD J₁ hJ₁x hJ₁g
  have hJ₂le : J₂ ≤ (seitzHyperGamma p E).map π := key (x * a) hxaE hxaD J₂ hJ₂x hJ₂g
  have hMtop : (seitzHyperGamma p E).map π = ⊤ := by
    by_contra hne
    rcases hJ₁m _ hJ₁le with hle | htop
    · refine absurd (hJ₂f a haED fun k hk => ?_) ha1
      have h1 : x k = k := hle (hJ₂le hk)
      have h2 : x (a k) = k := hJ₂x hk
      exact x.injective (h2.trans h1.symm)
    · exact hne htop
  have hsup : seitzHyperGamma p E ⊔ Subgroup.center K = ⊤ := by
    have h2 := congrArg (Subgroup.comap π) hMtop
    rw [Subgroup.comap_map_eq, hπker, Subgroup.comap_top] at h2
    exact h2
  exact eq_top_of_sup_center_eq_top hperf hsup

theorem exists_overgroupData_of_conj_coprime {S : Type*} [Group S] {D E : Subgroup (MulAut S)}
    [D.Normal] {x y ψ : MulAut S} (hψ : ψ * x * ψ⁻¹ = y) {J : Subgroup S}
    (hJy : J ≤ fixedSubgroup y) {p : ℕ}
    (hgen : J ≤ Subgroup.closure
      {k | k ∈ J ∧ (∃ m : ℕ, ¬ p ∣ m ∧ k ^ m = 1) ∧
        ∃ b ∈ (E ⊓ D).map (MulAut.conj ψ).toMonoidHom, b ≠ 1 ∧ b k = k})
    (hfaith : ∀ a ∈ D, (∀ k ∈ J, a k = k) → a = 1)
    (hmax : ∀ H : Subgroup S, J ≤ H → H ≤ fixedSubgroup y ∨ H = ⊤) :
    ∃ J' : Subgroup S, J' ≤ fixedSubgroup x ∧
      J' ≤ Subgroup.closure {k | k ∈ J' ∧ (∃ m : ℕ, ¬ p ∣ m ∧ k ^ m = 1) ∧
        ∃ b ∈ E ⊓ D, b ≠ 1 ∧ b k = k} ∧
      (∀ a ∈ E ⊓ D, (∀ k ∈ J', a k = k) → a = 1) ∧
      ∀ H : Subgroup S, J' ≤ H → H ≤ fixedSubgroup x ∨ H = ⊤ := by
  have hyψ : ∀ k, y (ψ k) = ψ (x k) := fun k => by
    rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hinvJ : ∀ k ∈ J, ψ⁻¹ k ∈ J.comap ψ.toMonoidHom := fun k hk => by
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.apply_inv_self]
    exact hk
  refine ⟨J.comap ψ.toMonoidHom, fun k hk => ?_, fun k hk => ?_, fun a ha hfix => ?_,
    fun H hJH => ?_⟩
  · refine mem_fixedSubgroup.2 (ψ.injective ?_)
    rw [← hyψ]
    exact mem_fixedSubgroup.1 (hJy (Subgroup.mem_comap.1 hk))
  · have h2 := Subgroup.mem_map_of_mem (ψ⁻¹ : MulAut S).toMonoidHom
      (hgen (Subgroup.mem_comap.1 hk))
    rw [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      MulAut.inv_apply_self] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨l, hmem, rfl⟩
    obtain ⟨hlJ, hpow, b, hb, hb1, hbl⟩ := hmem
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨m, hmp, hlm⟩ := hpow
    have hb0 : b₀ ≠ 1 := fun h => hb1 (by simp [h])
    refine ⟨hinvJ l hlJ, ?_, b₀, hb₀, hb0, ?_⟩
    · exact ⟨m, hmp, by rw [← map_pow, hlm, map_one]⟩
    · have h3 : ψ (b₀ (ψ⁻¹ l)) = l := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
          MulAut.mul_apply] at hbl
        exact hbl
      exact (MulAut.inv_apply_self S ψ _).symm.trans (congrArg (fun z => ψ⁻¹ z) h3)
  · have h1 : ψ * a * ψ⁻¹ ∈ D := (inferInstance : D.Normal).conj_mem a ha.2 ψ
    refine conj_eq_one_iff.1 (hfaith _ h1 fun k hk => ?_)
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix _ (hinvJ k hk), MulAut.apply_inv_self]
  · have hJ : J ≤ H.map ψ.toMonoidHom := fun k hk =>
      ⟨ψ⁻¹ k, hJH (hinvJ k hk), MulAut.apply_inv_self S ψ k⟩
    rcases hmax _ hJ with hle | htop
    · refine Or.inl fun h hh => mem_fixedSubgroup.2 (ψ.injective ?_)
      rw [← hyψ]
      exact mem_fixedSubgroup.1 (hle ⟨h, hh, rfl⟩)
    · refine Or.inr (eq_top_iff.2 fun k _ => ?_)
      have hk : ψ k ∈ H.map ψ.toMonoidHom := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨h, hh, hhk⟩ := hk
      rwa [ψ.injective hhk] at hh

theorem le_closure_uni_fixed_of_le {S T : Type*} [Group S] [Group T] {J : Subgroup S}
    (e : ↥J ≃* T) {p r : ℕ} {𝒟 : Subgroup (MulAut T)}
    (hgen : ∀ P : Subgroup (MulAut T), P ≤ 𝒟 → IsElemAbelian p P → Nat.card P = p ^ 2 →
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.UniPlaneGen r P)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hAJ : ∀ a ∈ A, ∀ k ∈ J, a k ∈ J)
    (hfaith : ∀ a ∈ A, (∀ k ∈ J, a k = k) → a = 1)
    (h𝒟 : ∀ a ∈ A, ∀ d : MulAut T,
      (∀ k (hk : k ∈ J), ((e.symm (d (e ⟨k, hk⟩)) : S)) = a k) → d ∈ 𝒟) :
    J ≤ Subgroup.closure {k | k ∈ J ∧ (∃ n : ℕ, k ^ (r ^ n) = 1) ∧
      ∃ b ∈ A, b ≠ 1 ∧ b k = k} := by
  classical
  let rJ : ↥A → MulAut ↥J := fun a =>
    { toFun := fun k => ⟨(a : MulAut S) k, hAJ a a.2 k k.2⟩
      invFun := fun k => ⟨((a : MulAut S)⁻¹) k, hAJ a⁻¹ (A.inv_mem a.2) k k.2⟩
      left_inv := fun k => Subtype.ext (MulAut.inv_apply_self S _ _)
      right_inv := fun k => Subtype.ext (MulAut.apply_inv_self S _ _)
      map_mul' := fun k l => Subtype.ext (map_mul (a : MulAut S) (k : S) (l : S)) }
  let ρ : ↥A →* MulAut T :=
    (MulAut.congr e).toMonoidHom.comp
      { toFun := rJ
        map_one' := MulEquiv.ext fun _ => rfl
        map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl }
  have hρ : ∀ (a : ↥A) (k : ↥J), ρ a (e k) = e (rJ a k) := fun a k => by
    show e (rJ a (e.symm (e k))) = e (rJ a k)
    rw [MulEquiv.symm_apply_apply]
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine Subtype.ext (hfaith a a.2 fun k hk => ?_)
    have h1 : e (rJ a ⟨k, hk⟩) = e ⟨k, hk⟩ := by rw [← hρ, ha, MulAut.one_apply]
    exact congrArg Subtype.val (e.injective h1)
  have hB : IsElemAbelian p ρ.range := by
    have h := (hA.subgroupOf A).map ρ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
  have hBc : Nat.card ρ.range = p ^ 2 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, hAc]
  have hρmem : ρ.range ≤ 𝒟 := by
    rintro _ ⟨a, rfl⟩
    refine h𝒟 a a.2 (ρ a) ?_
    intro k hk
    rw [hρ a ⟨k, hk⟩, MulEquiv.symm_apply_apply]
    rfl
  have htop : CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.uniPlaneClosure r
      ρ.range = ⊤ := hgen ρ.range hρmem hB hBc
  let Tset : Set T := {t | ∃ b ∈ ρ.range, b ≠ 1 ∧ b t = t ∧ ∃ n : ℕ, t ^ (r ^ n) = 1}
  let KsetJ : Set ↥J := {y | (∃ n : ℕ, ((y : S)) ^ (r ^ n) = 1) ∧
    ∃ b ∈ A, b ≠ 1 ∧ b (y : S) = (y : S)}
  have hgenJ : (⊤ : Subgroup ↥J) ≤ Subgroup.closure KsetJ := by
    intro y _
    have hy : e y ∈ Subgroup.closure Tset := by
      have hm : e y ∈ CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.uniPlaneClosure
          r ρ.range := by
        rw [htop]
        exact Subgroup.mem_top _
      simpa [Tset, CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.uniPlaneClosure]
        using hm
    have h2 : e.symm (e y) ∈ (Subgroup.closure Tset).map e.symm.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy
    rw [MonoidHom.map_closure] at h2
    have h3 : y ∈ Subgroup.closure (e.symm '' Tset) := by simpa using h2
    refine (Subgroup.closure_mono ?_) h3
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨b, hb, hb1, hbt, n, hn⟩ := ht
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hb
    have ha1 : a ≠ 1 := fun h => hb1 (by rw [h, map_one])
    have ha1' : (a : MulAut S) ≠ 1 := fun h => ha1 (Subtype.ext h)
    refine ⟨⟨n, ?_⟩, a, a.2, ha1', ?_⟩
    · have hpow : (e.symm t) ^ (r ^ n) = 1 := by
        apply e.injective
        rw [map_pow, MulEquiv.apply_symm_apply, hn, map_one]
      simpa using congrArg (fun z : ↥J => (z : S)) hpow
    · have hfix : rJ a (e.symm t) = e.symm t := by
        apply e.injective
        rw [← hρ a (e.symm t), MulEquiv.apply_symm_apply, hbt]
      simpa [rJ] using congrArg (fun z : ↥J => (z : S)) hfix
  intro k hk
  have h4 : (⟨k, hk⟩ : ↥J) ∈ Subgroup.closure KsetJ := hgenJ (Subgroup.mem_top _)
  have h5 : ((⟨k, hk⟩ : ↥J) : S) ∈ (Subgroup.closure KsetJ).map J.subtype :=
    Subgroup.mem_map_of_mem _ h4
  rw [MonoidHom.map_closure] at h5
  refine (Subgroup.closure_mono ?_) h5
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y.2, hy⟩

theorem le_closure_uni_fixed {S T : Type*} [Group S] [Group T] {J : Subgroup S}
    (e : ↥J ≃* T) {p r : ℕ}
    (hgen : ∀ P : Subgroup (MulAut T), IsElemAbelian p P → Nat.card P = p ^ 2 →
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.UniPlaneGen r P)
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hAJ : ∀ a ∈ A, ∀ k ∈ J, a k ∈ J)
    (hfaith : ∀ a ∈ A, (∀ k ∈ J, a k = k) → a = 1) :
    J ≤ Subgroup.closure {k | k ∈ J ∧ (∃ n : ℕ, k ^ (r ^ n) = 1) ∧
      ∃ b ∈ A, b ≠ 1 ∧ b k = k} :=
  le_closure_uni_fixed_of_le (𝒟 := ⊤) e (fun P _ => hgen P) hA hAc hAJ hfaith
    fun _ _ _ _ => Subgroup.mem_top _


theorem fixedFieldImage_le_closure_uni_of_plane {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (σ : K ≃+* K) (hσ : orderOf σ = 3)
    (h3 : 3 ∣ Nat.card (fixSubfield σ) - 1)
    {A : Subgroup (MulAut ↥(adjointGroup Tag.E6 K))}
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 2) (hAD : A ≤ e6Inndiag K)
    (hAσ : ∀ b ∈ A, Commute b (entrywiseAdjointAut Tag.E6 σ)) :
    (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) ≤ Subgroup.closure
      {k | k ∈ (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) ∧
        (∃ n : ℕ, k ^ (ringChar K ^ n) = 1) ∧ ∃ b ∈ A, b ≠ 1 ∧ b k = k} := by
  classical
  have hchar : ringChar (fixSubfield σ) = ringChar K := by
    have h1 : CharP (fixSubfield σ) (ringChar (fixSubfield σ)) := ringChar.charP _
    have h2 : CharP (fixSubfield σ) (ringChar K) :=
      (RingHom.charP_iff (fixSubfield σ).subtype (fixSubfield σ).subtype.injective
        (ringChar K)).mpr (ringChar.charP K)
    exact CharP.eq (fixSubfield σ) h1 h2
  have hk3 : ringChar (fixSubfield σ) ≠ 3 := by rw [hchar]; exact hK3
  have hk2 : 2 < Nat.card (fixSubfield σ) := by
    have hm1 : 1 < Nat.card (fixSubfield σ) := Finite.one_lt_card
    have hpos : 0 < Nat.card (fixSubfield σ) - 1 := by omega
    have h3le : 3 ≤ Nat.card (fixSubfield σ) - 1 := Nat.le_of_dvd hpos h3
    omega
  have hJC : fixedFieldImage Tag.E6 σ ≤ adjointGroup Tag.E6 K :=
    fixedFieldImage_le.trans inf_le_left
  let e : ↥((fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K)) ≃*
      adjointGroup Tag.E6 (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv (τ := Tag.E6) σ).symm
  refine le_closure_uni_fixed (p := 3) (r := ringChar K) e ?_ hA hAc ?_ ?_
  · intro P hP hPc
    rw [← hchar]
    exact uniPlaneGen_e6_adjoint (k := fixSubfield σ) hk3 h3 P hP hPc
  · intro a ha k hk
    exact map_fixedFieldImage_subgroupOf_le (Or.inr (Or.inr (Or.inl rfl))) σ (hAσ a ha)
      (Subgroup.mem_map_of_mem _ hk)
  · intro a ha hfix
    exact eq_one_of_mem_e6Inndiag_of_fix_subfield (fixSubfield σ) hk2 (hAD ha)
      fun x hx => hfix x (Subgroup.mem_subgroupOf.2 hx)

theorem seitzHyperGamma_eq_top_e6_field_cube {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3) (h3 : 3 ∣ Nat.card k - 1)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hED : ¬ coverImage θ E ≤ e6Inndiag k) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card k (ringChar k)
  have hK : Nat.card k = ringChar k ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  haveI : CharP k (ringChar k) := ringChar.charP k
  have hEab : IsElemAbelian 3 (coverImage θ E) := isElemAbelian_coverImage θ hE
  have hAc : Nat.card ↥(coverImage θ E ⊓ e6Inndiag k) = 3 ^ 2 :=
    card_inf_e6Inndiag (K := k) (E := coverImage θ E) hEab
      (by rw [card_coverImage hperf θ E, hcard]) hED
  have hA : coverImage θ E ⊓ e6Inndiag k ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAc
    norm_num at hAc
  have hDn : (e6Inndiag k).Normal := e6Inndiag_normal k
  refine seitzHyperGamma_eq_top_of_cover_overgroups hperf θ (p := 3) Nat.prime_three hE hcard
    hED hA ?_
  intro x hxE hxD
  have hx3 : x ^ 3 = 1 := hEab.2 x hxE
  obtain ⟨σ, hσ, -, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos k hK
    Nat.prime_three (by norm_num) hx3 hxD
  have hcardfix := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ
  rw [hσ] at hcardfix
  have h3fix : 3 ∣ Nat.card (fixSubfield σ) - 1 := by
    set m := Nat.card (fixSubfield σ) with hm
    have hm2 : 1 < m := Finite.one_lt_card
    have hdvd : 3 ∣ m ^ 3 - 1 := by
      rw [← hcardfix]
      exact h3
    have hcube : ∀ x : ZMod 3, x ^ 3 = x := by decide
    have hzero : ((m ^ 3 - 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).mpr hdvd
    have hsub : ((m ^ 3 - 1 : ℕ) : ZMod 3) = ((m : ZMod 3) ^ 3 - 1) := by
      rw [Nat.cast_sub (show 1 ≤ m ^ 3 from by
        have : 0 < m ^ 3 := pow_pos (by omega) 3
        omega), Nat.cast_pow, Nat.cast_one]
    rw [hsub, hcube] at hzero
    have hm1 : (m : ZMod 3) = 1 := sub_eq_zero.mp hzero
    have hmod : m ≡ 1 [MOD 3] := (ZMod.natCast_eq_natCast_iff m 1 3).mp (by
      rw [hm1]; norm_num)
    exact (Nat.modEq_iff_dvd' (le_of_lt hm2)).mp hmod.symm
  have hk2 : 2 < Nat.card (fixSubfield σ) := by
    have hpos : 0 < Nat.card (fixSubfield σ) - 1 := by
      have := Finite.one_lt_card (α := fixSubfield σ)
      omega
    have h3le : 3 ≤ Nat.card (fixSubfield σ) - 1 := Nat.le_of_dvd hpos h3fix
    have := Finite.one_lt_card (α := fixSubfield σ)
    omega
  have hA' : IsElemAbelian 3
      ((coverImage θ E ⊓ e6Inndiag k).map (MulAut.conj ψ).toMonoidHom) :=
    (hEab.mono (inf_le_left : coverImage θ E ⊓ e6Inndiag k ≤ coverImage θ E)).map _
  have hAc' : Nat.card
      ((coverImage θ E ⊓ e6Inndiag k).map (MulAut.conj ψ).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj ψ).injective, hAc]
  have hAD' : (coverImage θ E ⊓ e6Inndiag k).map (MulAut.conj ψ).toMonoidHom ≤
      e6Inndiag k := by
    rintro _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hDn.conj_mem b hb.2 ψ
  have hAσ' : ∀ b ∈ (coverImage θ E ⊓ e6Inndiag k).map (MulAut.conj ψ).toMonoidHom,
      Commute b (entrywiseAdjointAut Tag.E6 σ) := by
    rintro _ ⟨b, hb, rfl⟩
    have hbx : Commute b x :=
      congrArg Subtype.val (hEab.1.is_comm.comm ⟨b, hb.1⟩ ⟨x, hxE⟩)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hψ]
    exact hbx.conj ψ
  have hplane := fixedFieldImage_le_closure_uni_of_plane hk3 σ hσ h3fix hA' hAc' hAD' hAσ'
  have hr3 : ∀ j : ℕ, ¬ 3 ∣ ringChar k ^ j := fun j h =>
    hk3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hplane' : (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 k) ≤
      Subgroup.closure {s | s ∈ (fixedFieldImage Tag.E6 σ).subgroupOf
          (adjointGroup Tag.E6 k) ∧ (∃ m : ℕ, ¬ 3 ∣ m ∧ s ^ m = 1) ∧
        ∃ b ∈ (coverImage θ E ⊓ e6Inndiag k).map (MulAut.conj ψ).toMonoidHom,
          b ≠ 1 ∧ b s = s} := by
    refine hplane.trans (Subgroup.closure_mono ?_)
    rintro s ⟨hs, ⟨j, hj⟩, b, hb, hb1, hbs⟩
    exact ⟨hs, ⟨ringChar k ^ j, hr3 j, hj⟩, b, hb, hb1, hbs⟩
  obtain ⟨J', hJ'x, hJ'g, hJ'f, hJ'm⟩ :=
    exists_overgroupData_of_conj_coprime (p := 3) (D := e6Inndiag k)
      (E := coverImage θ E) hψ (fixedFieldImage_subgroupOf_le_subfieldGroup Tag.E6 σ)
      hplane'
      (fun a ha hfix => eq_one_of_mem_e6Inndiag_of_fix_subfield (fixSubfield σ) hk2 ha
        fun y hy => hfix y (Subgroup.mem_subgroupOf.2 hy))
      (fun H hJH => le_subfieldGroup_or_eq_top_of_fixedFieldImage_le (Or.inl rfl) σ
        Nat.prime_three (by norm_num) hσ (by omega) H hJH)
  exact ⟨J', hJ'x, hJ'g, hJ'f, hJ'm⟩

end CFSG.LieType.SeitzGeneration.CubeCoverField

end
