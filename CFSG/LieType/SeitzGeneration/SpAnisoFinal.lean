module

public import CFSG.LieType.SeitzGeneration.SpAnisoPair
public import CFSG.LieType.SeitzGeneration.HyperExClassical
public import CFSG.LieType.SeitzGeneration.InnerSymplectic
public import CFSG.LieType.SeitzGeneration.SpHyperTwoThree

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.CTP CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {p r : ℕ} {K : Type} [Field K] {A : Subgroup (StatedSp r K)}

theorem SpAnisoSetup.hyperClosure_eq_top [Finite K] (S : SpAnisoSetup p r K A)
    (hq : ¬ (p = 3 ∧ Nat.card K = 2)) : hyperClosure p ⊤ A = ⊤ := by
  classical
  refine eq_top_of_transCenter (transCenter_of_pairs
    (Vs := fun F : {F : Subgroup A // F.index = p} => hyperFixed (spRep A) F.1)
    S.iSup_blk ?_ (fun F => S.blk_nondeg F.2) ?_ ?_)
  · intro i j hij u hu v hv
    exact S.blk_orth i.2 j.2 (fun h => hij (Subtype.ext h)) hu hv
  · intro F c hc t
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F.1.map A.subtype,
      Subgroup.map_subtype_le _, ?_, ?_⟩
    · have hsub : (F.1.map A.subtype).subgroupOf A = F.1 :=
        Subgroup.comap_map_eq_self_of_injective A.subtype_injective F.1
      rw [Subgroup.relIndex, hsub]
      exact F.2
    · rintro _ ⟨g, hg, rfl⟩
      exact (commute_spTransvection (mem_hyperFixed.1 hc g hg) t).symm
  · intro i j hij y hy y' hy' hy0 hy'0
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have h₁ : hyperFixed (spRep A) i.1 ≠ ⊥ := fun h => hy0 (by
      rw [h] at hy
      simpa using hy)
    have h₂ : hyperFixed (spRep A) j.1 ≠ ⊥ := fun h => hy'0 (by
      rw [h] at hy'
      simpa using hy')
    exact S.transCenter_of_mem_pair hq i.2 j.2 hne h₁ h₂ (Submodule.add_mem_sup hy hy')

theorem map_hyperClosure_le_of_lift {G Q : Type*} [Group G] [Group Q] {π : G →* Q} {A : Subgroup G}
    {E : Subgroup Q} (hAE : A.map π = E) (hdis : Disjoint A π.ker) :
    (hyperClosure p ⊤ A).map π ≤ hyperClosure p ⊤ E := by
  rw [hyperClosure, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨k, ⟨-, F₀, hF₀A, hF₀, hcomm⟩, rfl⟩
  refine ⟨Subgroup.mem_top _, F₀.map π, hAE ▸ Subgroup.map_mono hF₀A, ?_, ?_⟩
  · have h := relIndex_map_lift (p := p) hAE hdis (F' := F₀.subgroupOf A) hF₀
    have heq : (F₀.subgroupOf A).map (π.comp A.subtype) = F₀.map π := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hF₀A]
    rwa [heq] at h
  · rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul, hcomm f hf]

theorem hyperGen_top_of_aniso [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hr : 1 ≤ r) (hq : ¬ (p = 3 ∧ Nat.card K = 2)) {E : Subgroup (StatedProj (StatedSp r K))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (haniso : ∀ W : Submodule K (Fin r ⊕ Fin r → K), (∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) →
      (∀ g : StatedSp r K, proj r K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥) :
    HyperGen p (⊤ : Subgroup (StatedProj (StatedSp r K))) E := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hproj := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
    (r := r) (K := K)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hker : ¬ p ∣ Nat.card (proj r K).ker := fun hd =>
    hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (coprime_card_ker_proj hr hp hp2) hd (dvd_refl p))
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ :=
    exists_lift_elemAbelian (proj r K) hproj hker hcomm hE.2
  have S : SpAnisoSetup p r K A :=
    { prime := hp
      ne_two := hp2
      cast_ne_zero := hpK
      comm := hAcomm
      pow_eq_one := hAexp
      card_eq := hAcard.trans hcard
      aniso := fun W hW hstab => haniso W hW fun g hg w hw => by
        rw [← hAE] at hg
        obtain ⟨a, ha, hag⟩ := hg
        have hz : a⁻¹ * g ∈ (proj r K).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj] at hz
        have hzW := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_stabilizer
          W hz
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.mem_stabilizer] at hzW
        have hzw : spEnd (a⁻¹ * g) w ∈ W := by
          rw [← hzW]
          exact ⟨w, hw, rfl⟩
        have hgz : g = a * (a⁻¹ * g) := by group
        rw [hgz, spEnd_mul, Module.End.mul_apply]
        exact hstab a ha _ hzw }
  have htop := S.hyperClosure_eq_top hq
  intro k _
  obtain ⟨g, rfl⟩ := hproj k
  have hg : g ∈ hyperClosure p ⊤ A := by
    rw [htop]
    exact Subgroup.mem_top g
  exact map_hyperClosure_le_of_lift hAE hAdis ⟨g, hg, rfl⟩

@[expose] def SpAnisoNotTwoThree (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (E₀ : Subgroup (Cat d)) : Prop :=
  ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
    (e : Cat d ≃* StatedProj (StatedSp r K)), (p : K) ≠ 0 ∧ 1 ≤ r ∧
    ¬ (p = 3 ∧ Nat.card K = 2) ∧
    ∀ W : Submodule K (Fin r ⊕ Fin r → K), (∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) →
      (∀ g : StatedSp r K, proj r K g ∈ E₀.map e.toMonoidHom → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥

theorem seitzHyperLie_spAnisoNotTwoThree :
    SeitzHyperLie fun d p E₀ => SpAnisoNotTwoThree d p E₀ := by
  intro d p hp hp2 hpd hlist E₀ hE hcard hani
  obtain ⟨r, K, _, _, e, hpK, hr, hq, hW⟩ := hani
  have hE' : IsElemAbelian p (E₀.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card (E₀.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  exact hyperGen_top_of_mulEquiv e (hyperGen_top_of_aniso hp hp2 hpK hr hq hE' hcard' hW)

theorem not_two_three_of_card {d : TauCeti.ValidLieTypeIndex} {p : ℕ} (h32 : ¬ IsSpTwoThree d p)
    {r : ℕ} {q : TauCeti.PrimePower} (hd : d.1 = .B r q ∨ d.1 = .C r q) {K : Type}
    (hK : Nat.card K = q.p ^ q.exponent) : ¬ (p = 3 ∧ Nat.card K = 2) := by
  rintro ⟨hp3, h2⟩
  rw [hK] at h2
  obtain ⟨hq2, he1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp h2
  exact h32 ⟨hp3, r, q, hq2, he1, hd⟩

theorem exists_sp_model_notTwoThree {d : TauCeti.ValidLieTypeIndex} (hd : IsSymplecticIndex d.1)
    {p : ℕ} (hp : p.Prime) (hpd : p ≠ d.1.characteristic) (h32 : ¬ IsSpTwoThree d p) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
      Nonempty (Cat d ≃* StatedProj (StatedSp r K)) ∧ (p : K) ≠ 0 ∧ 1 ≤ r ∧
        ¬ (p = 3 ∧ Nat.card K = 2) := by
  obtain ⟨d, hv⟩ := d
  rcases hd with ⟨q, rfl⟩ | ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  · have hq : p ≠ q.p := by simpa using hpd
    have hK := CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv
    refine ⟨2, _, inferInstance, CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
      ⟨CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv⟩, ?_, by norm_num,
      not_two_three_of_card h32 (Or.inl rfl) hK⟩
    have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
      ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩
    refine CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp ?_
    rw [hK]
    exact fun h => hq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))
  · have hq : p ≠ q.p := by simpa using hpd
    have hK := CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv
    refine ⟨r, _, inferInstance, CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
      ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3⟩,
      ?_, by omega, not_two_three_of_card h32 (Or.inl rfl) hK⟩
    have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
      ⟨TauCeti.LieTypeIndex.B r q, hv⟩
    refine CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp ?_
    rw [hK]
    exact fun h => hq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))
  · have hq : p ≠ q.p := by simpa using hpd
    have hr3 : 3 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    have hK := card_fixedField_C r q hv
    refine ⟨r, _, inferInstance, CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
      ⟨CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv⟩, ?_, by omega,
      not_two_three_of_card h32 (Or.inr rfl) hK⟩
    have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
      ⟨TauCeti.LieTypeIndex.C r q, hv⟩
    refine CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp ?_
    rw [hK]
    exact fun h => hq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))

theorem spReducible_or_spAnisoNotTwoThree {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSymplecticIndex d.1) {p : ℕ} (hp : p.Prime) (hpd : p ≠ d.1.characteristic)
    (h32 : ¬ IsSpTwoThree d p) (E₀ : Subgroup (Cat d)) :
    SpReducible d p E₀ ∨ SpAnisoNotTwoThree d p E₀ := by
  obtain ⟨r, K, _, _, ⟨e⟩, hpK, hr, hq⟩ := exists_sp_model_notTwoThree hd hp hpd h32
  by_cases h : ∃ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) ∧
      ∀ g : StatedSp r K, proj r K g ∈ E₀.map e.toMonoidHom → ∀ w ∈ W, spEnd g w ∈ W
  · exact Or.inl ⟨r, K, inferInstance, inferInstance, e, hpK, hr, h⟩
  · refine Or.inr ⟨r, K, inferInstance, inferInstance, e, hpK, hr, hq, fun W hiso hstab => ?_⟩
    by_contra hne
    exact h ⟨W, hne, hiso, hstab⟩

theorem hyperExFor_symplectic : HyperExFor fun d => IsSymplecticIndex d.1 := by
  rintro d p hp hp2 hpd hlist ⟨E₀, hE, hcard, hsym⟩
  by_cases h32 : IsSpTwoThree d p
  · exact seitzHyperLieEx_symplectic_twoThree d p hp hp2 hpd hlist ⟨E₀, hE, hcard, hsym, h32⟩
  · refine ⟨E₀, hE, hcard, ?_⟩
    rcases spReducible_or_spAnisoNotTwoThree hsym hp hpd h32 E₀ with hred | hani
    · exact seitzHyperLie_symplecticReducible d p hp hp2 hpd hlist E₀ hE hcard hred
    · exact seitzHyperLie_spAnisoNotTwoThree d p hp hp2 hpd hlist E₀ hE hcard hani

theorem hyperExFor_classical' (hu : HyperExFor fun d => IsUnitaryIndex' d.1)
    (ho : HyperExFor fun d => IsOrthogonalIndex d.1) :
    HyperExFor fun d => IsClassicalIndex d.1 :=
  hyperExFor_classical_of_families hyperExFor_linear hu hyperExFor_symplectic ho

end CFSG.LieType.SeitzGeneration
