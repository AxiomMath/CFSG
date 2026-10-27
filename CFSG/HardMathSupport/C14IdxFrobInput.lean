module

public import CFSG.HardMathSupport.C14IdxTorusFixed
public import CFSG.HardMathSupport.C14IdxTorusOrbits
public import CFSG.HardMathSupport.C14IdxTorusDecomp
public import CFSG.HardMathSupport.C14IdxRetwist

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality

lemma not_dvd_index_of_pow_eq_one_mem
    {G : Type*} [Group G] {p : ℕ} {H T D : Subgroup G} [Finite H]
    (hp : p.Prime) (hDH : D ≤ H) [hN : (D.subgroupOf H).Normal]
    (hHT : ∀ h ∈ H, ∃ t ∈ T, t⁻¹ * h ∈ D)
    (hT : ∀ t ∈ T, ∀ n : ℕ, t ^ p ^ n = 1 → t ∈ D) :
    ¬ p ∣ (D.subgroupOf H).index := by
  classical
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have hdvd' : p ∣ Nat.card (H ⧸ D.subgroupOf H) := by
    simpa [Subgroup.index_eq_card] using hdvd
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := H ⧸ D.subgroupOf H) p hdvd'
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨t, htT, htd⟩ := hHT h.1 h.2
  have htH : t ∈ H := by
    have h1 : (t⁻¹ * h.1)⁻¹ ∈ H := H.inv_mem (hDH htd)
    have h2 : h.1 * (t⁻¹ * h.1)⁻¹ ∈ H := H.mul_mem h.2 h1
    simpa [mul_assoc] using h2
  let tH : H := ⟨t, htH⟩
  have hqeq : (QuotientGroup.mk tH : H ⧸ D.subgroupOf H) = QuotientGroup.mk h := by
    rw [QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    simpa [tH] using htd
  have hqm : orderOf (QuotientGroup.mk' (D.subgroupOf H) tH) = p := by
    rw [QuotientGroup.mk'_apply, hqeq]
    exact hq
  let m := orderOf tH
  have hm0 : m ≠ 0 := (orderOf_pos tH).ne'
  obtain ⟨a, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
  have hpow : (tH ^ m') ^ p ^ a = 1 := by
    rw [← pow_mul, Nat.mul_comm, ← hmeq, pow_orderOf_eq_one]
  have htpowD : t ^ m' ∈ D :=
    hT (t ^ m') (T.pow_mem htT m') a (by simpa [tH] using hpow)
  have hmem : tH ^ m' ∈ D.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    simpa [tH] using htpowD
  have hpowq : (QuotientGroup.mk' (D.subgroupOf H) tH) ^ m' = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  exact hm' (hqm ▸ orderOf_dvd_of_pow_eq_one hpowq)

theorem idxConclusion_of_pinned
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type} {p : ℕ}
    {a : ι → Fin τ.rank → Lˣ} {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)} {σ : adjointGroup τ L →* adjointGroup τ L}
    (hσ : ∀ g, (σ g : ModGL τ L) = frobTwistGL τ L 2 e Q g)
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    (hQX : ∀ α, IsRoot τ α → ∀ c : L, Q * pinnedX τ L α c * Q⁻¹ = pinnedX τ L (θ α) c)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hQ : (adjointGroup τ L).map (MulAut.conj Q).toMonoidHom = adjointGroup τ L)
    (hΨ : Set.BijOn θ (familyKernel a) (familyKernel a))
    (hΨp : Set.BijOn θ (posRoots (familyKernel a)) (posRoots (familyKernel a)))
    (hp : p.Prime) (hfin : Finite ↥(σ.eqLocus (MonoidHom.id _)))
    (hsat : CorootPSaturated p (familyKernel a)) :
    IdxConclusion p a σ := by
  classical
  have hK : kernelRoots (familyChar a) = familyKernel a := kernelRoots_familyChar a
  have hU : unionRoots (familyChar a) Set.univ = familyKernel a :=
    (unionRoots_univ_eq_kernelRoots _).trans hK
  have hΔ : Set.BijOn θ (simpleRoots (kernelRoots (familyChar a)) : Set (Fin τ.rank → ℤ))
      (simpleRoots (kernelRoots (familyChar a)) : Set (Fin τ.rank → ℤ)) := by
    rw [hK]
    exact bijOn_simpleRoots_of_bijOn_posRoots (fun α hα => hα.1) hΨ hΨp
  have hTp : ∀ t ∈ unionTorus L (familyChar a) Set.univ,
      frobTwistGL τ L 2 e Q t = t → ∀ n : ℕ, t ^ p ^ n = 1 →
      t ∈ Subgroup.closure {x : ModGL τ L |
        x ∈ unionRootSpan L (familyChar a) Set.univ ∧ frobTwistGL τ L 2 e Q x = x ∧
          ∃ k : ℕ, x ^ 2 ^ k = 1} := by
    intro t ht hσt n hn
    obtain ⟨c, rfl, hc⟩ := exists_coordTuple_of_frobTwist_fixed hθ hθΦ hQX hQT hΔ hp
      (hK.symm ▸ hsat) ht hσt hn
    exact rootDiagUnit_coordTuple_mem_closure_of_simpleRoots he hθ hθΦ hQX hQT
      (hK.symm ▸ hΨ) hΔ c hc
  have hI5 : ∀ s ∈ unionRootSpan L (familyChar a) Set.univ,
      frobTwistGL τ L 2 e Q s = s →
      ∃ t ∈ unionTorus L (familyChar a) Set.univ, frobTwistGL τ L 2 e Q t = t ∧
        t⁻¹ * s ∈ Subgroup.closure {x : ModGL τ L |
          x ∈ unionRootSpan L (familyChar a) Set.univ ∧ frobTwistGL τ L 2 e Q x = x ∧
            ∃ k : ℕ, x ^ 2 ^ k = 1} := fun s hs hσs =>
    exists_fixed_torus_mul_mem_closure hθ hQX hQT hQ (hU.symm ▸ hΨ) (hU.symm ▸ hΨp) hs hσs
  have hS : (famS a).map (adjointGroup τ L).subtype =
      unionRootSpan L (familyChar a) Set.univ := by
    rw [map_famS_subtype_eq_rootSpan, unionRootSpan, hU]
  let S' : Subgroup (ModGL τ L) := unionRootSpan L (familyChar a) Set.univ
  have hS' : S' = (famS a).map (adjointGroup τ L).subtype := hS.symm
  let σ' : ModGL τ L →* ModGL τ L := frobTwistGL τ L 2 e Q
  let H : Subgroup (adjointGroup τ L) := famS a ⊓ σ.eqLocus (MonoidHom.id _)
  let E : Set (adjointGroup τ L) := {x | x ∈ H ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
  let D : Subgroup (adjointGroup τ L) := Subgroup.closure E
  let D' : Subgroup (ModGL τ L) :=
    Subgroup.closure {x : ModGL τ L | x ∈ S' ∧ σ' x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
  let T : Subgroup (adjointGroup τ L) :=
    (unionTorus L (familyChar a) Set.univ ⊓ σ'.eqLocus (MonoidHom.id _)).comap
      (adjointGroup τ L).subtype
  have hι : Function.Injective (adjointGroup τ L).subtype :=
    Subgroup.subtype_injective _
  have hEimage : (adjointGroup τ L).subtype '' E =
      {x : ModGL τ L | x ∈ S' ∧ σ' x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hS']
        exact Subgroup.mem_map_of_mem _ hy.1.1
      · show σ' ((y : adjointGroup τ L) : ModGL τ L) =
          ((y : adjointGroup τ L) : ModGL τ L)
        rw [← hσ y]
        simpa using hy.1.2
      · obtain ⟨k, hk⟩ := hy.2
        exact ⟨k, by simpa using congrArg (adjointGroup τ L).subtype hk⟩
    · rintro ⟨hxS, hxσ, hxk⟩
      rw [hS'] at hxS
      rcases Subgroup.mem_map.mp hxS with ⟨y, hyS, hyx⟩
      have hyx' : ((y : adjointGroup τ L) : ModGL τ L) = x := hyx
      refine ⟨y, ?_, hyx⟩
      refine ⟨Subgroup.mem_inf.mpr ⟨hyS, ?_⟩, ?_⟩
      · apply (adjointGroup τ L).subtype_injective
        have h2 : ((σ y : adjointGroup τ L) : ModGL τ L) =
            ((y : adjointGroup τ L) : ModGL τ L) := by
          rw [hσ y]
          simpa only [σ', hyx'] using hxσ
        exact h2
      · obtain ⟨k, hk⟩ := hxk
        refine ⟨k, ?_⟩
        apply (adjointGroup τ L).subtype_injective
        have h2 : (adjointGroup τ L).subtype (y ^ 2 ^ k : adjointGroup τ L) =
            x ^ 2 ^ k := by
          rw [map_pow, hyx]
        rw [h2, hk]
        simp
  have hDmap : D.map (adjointGroup τ L).subtype = D' := by
    change (Subgroup.closure E).map (adjointGroup τ L).subtype =
      Subgroup.closure {x : ModGL τ L | x ∈ S' ∧ σ' x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
    rw [MonoidHom.map_closure, hEimage]
  have hHfin : Finite H := by
    have hEq : (σ.eqLocus (MonoidHom.id _) : Set (adjointGroup τ L)).Finite := Set.toFinite _
    exact (hEq.subset (fun x hx => hx.2)).to_subtype
  have hDH : D ≤ H := by
    change Subgroup.closure E ≤ H
    exact (Subgroup.closure_le H).2 (fun x hx => hx.1)
  have hnorm : (D.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDH]
    change H ≤ Subgroup.normalizer (Subgroup.closure E)
    rw [Subgroup.le_normalizer_closure_iff]
    intro h hh x hx
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (famS a).mul_mem ((famS a).mul_mem hh.1 hx.1.1) ((famS a).inv_mem hh.1)
      · show σ (h * x * h⁻¹) = h * x * h⁻¹
        have hh' : σ h = h := by simpa using hh.2
        have hx' : σ x = x := by simpa using hx.1.2
        rw [map_mul, map_mul, map_inv, hh', hx']
    · obtain ⟨k, hk⟩ := hx.2
      exact ⟨k, by rw [conj_pow, hk]; simp⟩
  have hHT : ∀ h ∈ H, ∃ t ∈ T, t⁻¹ * h ∈ D := by
    intro h hh
    have hhS : ((h : adjointGroup τ L) : ModGL τ L) ∈ S' := by
      rw [hS']
      exact Subgroup.mem_map_of_mem _ hh.1
    have hhσ : σ' ((h : adjointGroup τ L) : ModGL τ L) =
        ((h : adjointGroup τ L) : ModGL τ L) := by
      rw [← hσ (h : adjointGroup τ L), hh.2]
      simp
    obtain ⟨t, htT, htfix, htd⟩ := hI5 _ hhS hhσ
    have htS : t ∈ S' := unionTorus_le_unionRootSpan htT
    rw [hS'] at htS
    rcases Subgroup.mem_map.mp htS with ⟨tA, htAfamS, htAeq⟩
    refine ⟨tA, ?_, ?_⟩
    · rw [Subgroup.mem_comap]
      rw [htAeq]
      exact Subgroup.mem_inf.mpr ⟨htT, htfix⟩
    · have hmemD' : (adjointGroup τ L).subtype (tA⁻¹ * h) ∈ D' := by
        rw [map_mul, map_inv, htAeq]
        exact htd
      rw [← hDmap] at hmemD'
      exact (Subgroup.mem_map_iff_mem hι).mp hmemD'
  have hT : ∀ t ∈ T, ∀ n : ℕ, t ^ p ^ n = 1 → t ∈ D := by
    intro t ht n hn
    rw [Subgroup.mem_comap] at ht
    obtain ⟨htTorus, htfix⟩ := Subgroup.mem_inf.mp ht
    have hn' : ((adjointGroup τ L).subtype t) ^ p ^ n = 1 := by
      rw [← map_pow, hn, map_one]
    have hmemD' : (adjointGroup τ L).subtype t ∈ D' :=
      hTp _ htTorus htfix n hn'
    rw [← hDmap] at hmemD'
    exact (Subgroup.mem_map_iff_mem hι).mp hmemD'
  have hnotdvd : ¬ p ∣ (D.subgroupOf H).index :=
    not_dvd_index_of_pow_eq_one_mem hp hDH hHT hT
  simpa [IdxConclusion, H, D, E] using hnotdvd

theorem excIdxFrobInput_holds :
    ExcIdxFrobInput := by
  intro τ L _ _ _ ι p hp _ a e he Q' hQT hQ' F₀ hF₀ hM hfin hsat
  obtain ⟨m, hm, Q, θ, hσ, hθ, hθΦ, hQX, hQT', hQ, hΨ, hΨp⟩ :=
    exists_pinned_retwist he hQT hQ' hF₀ hM
  let σ : adjointGroup τ L →* adjointGroup τ L :=
    (MulAut.conj m⁻¹).toMonoidHom.comp (F₀.comp (MulAut.conj m).toMonoidHom)
  have hσg : ∀ g, σ g = m⁻¹ * F₀ (m * g * m⁻¹) * m := fun g => by
    simp [σ, MulAut.conj_apply]
  refine idxConclusion_of_conj hm hσg ?_
  have hfin' : Finite ↥(σ.eqLocus (MonoidHom.id _)) := by
    have hmem : ∀ x : σ.eqLocus (MonoidHom.id _),
        F₀ (m * (x : adjointGroup τ L) * m⁻¹) = m * (x : adjointGroup τ L) * m⁻¹ := by
      intro x
      have hx : σ (x : adjointGroup τ L) = (x : adjointGroup τ L) := x.2
      rw [hσg] at hx
      calc F₀ (m * (x : adjointGroup τ L) * m⁻¹)
          = m * (m⁻¹ * F₀ (m * (x : adjointGroup τ L) * m⁻¹) * m) * m⁻¹ := by group
        _ = m * (x : adjointGroup τ L) * m⁻¹ := by rw [hx]
    let f : σ.eqLocus (MonoidHom.id _) → F₀.eqLocus (MonoidHom.id _) :=
      fun x => ⟨m * (x : adjointGroup τ L) * m⁻¹, hmem x⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      calc (x : adjointGroup τ L)
          = m⁻¹ * (m * (x : adjointGroup τ L) * m⁻¹) * m := by group
        _ = m⁻¹ * (m * (y : adjointGroup τ L) * m⁻¹) * m := by
              simpa [f] using congrArg (fun z : F₀.eqLocus (MonoidHom.id _) =>
                m⁻¹ * (z : adjointGroup τ L) * m) hxy
        _ = (y : adjointGroup τ L) := by group
    exact Finite.of_injective f hf
  exact idxConclusion_of_pinned he (fun g => by rw [hσg]; exact hσ g) hθ hθΦ hQX hQT' hQ hΨ hΨp
    hp hfin' hsat

end CFSG.HardMathSupport.C14Idx
