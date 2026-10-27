module

public import CFSG.Fischer.Aut.Complete
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagParabolic
public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagInndiagGen
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverDiag

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.RootWeight CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar

section Generic

variable {G : Type*} [Group G]

theorem le_iSup_hyper_of_map_conj_normalizer {p : ℕ} {C A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (C : Set G))
    (h : C ≤ ⨆ (B : Subgroup G) (_ : B ≤ A.map (MulAut.conj x).toMonoidHom)
      (_ : B.relIndex (A.map (MulAut.conj x).toMonoidHom) = p),
        C ⊓ Subgroup.centralizer (B : Set G)) :
    C ≤ ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
      C ⊓ Subgroup.centralizer (B : Set G) := by
  set f : G →* G := (MulAut.conj x⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj x⁻¹).injective
  have hxC : ∀ y, y ∈ C ↔ x * y * x⁻¹ ∈ C := Subgroup.mem_normalizer_iff.1 hx
  have hxC' : ∀ y, y ∈ C ↔ x⁻¹ * y * x ∈ C := Subgroup.mem_normalizer_iff''.1 hx
  have hAA : (A.map (MulAut.conj x).toMonoidHom).map f = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext y
    simp only [f, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have hle : (⨆ (B : Subgroup G) (_ : B ≤ A.map (MulAut.conj x).toMonoidHom)
      (_ : B.relIndex (A.map (MulAut.conj x).toMonoidHom) = p),
        C ⊓ Subgroup.centralizer (B : Set G)) ≤
      (⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
        C ⊓ Subgroup.centralizer (B : Set G)).comap f := by
    refine iSup₂_le fun B hB => iSup_le fun hBi => fun y hy => ?_
    obtain ⟨hyC, hyc⟩ := Subgroup.mem_inf.1 hy
    have hB₀ : B.map f ≤ A := hAA ▸ Subgroup.map_mono hB
    have hB₀i : (B.map f).relIndex A = p := by
      rw [← hAA, Subgroup.relIndex_map_map_of_injective _ _ hf, hBi]
    rw [Subgroup.mem_comap]
    refine Subgroup.mem_iSup_of_mem (B.map f) (Subgroup.mem_iSup_of_mem hB₀
      (Subgroup.mem_iSup_of_mem hB₀i (Subgroup.mem_inf.2 ⟨?_, ?_⟩)))
    · change x⁻¹ * y * x⁻¹⁻¹ ∈ C
      rw [inv_inv]
      exact (hxC' y).1 hyC
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hby := Subgroup.mem_centralizer_iff.1 hyc b hb
      change x⁻¹ * b * x⁻¹⁻¹ * (x⁻¹ * y * x⁻¹⁻¹) = x⁻¹ * y * x⁻¹⁻¹ * (x⁻¹ * b * x⁻¹⁻¹)
      simp only [inv_inv]
      calc x⁻¹ * b * x * (x⁻¹ * y * x) = x⁻¹ * (b * y) * x := by group
        _ = x⁻¹ * (y * b) * x := by rw [hby]
        _ = x⁻¹ * y * x * (x⁻¹ * b * x) := by group
  intro c hc
  have hmem := hle (h ((hxC c).1 hc))
  rw [Subgroup.mem_comap] at hmem
  have e : f (x * c * x⁻¹) = c := by
    change x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c
    group
  rwa [e] at hmem

theorem le_iSup_hyper_of_normalizes_radicals [Finite G] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hrp : r ≠ p) {C Q Q' A : Subgroup G} [IsElementaryAbelian p A] (hA1 : A ≠ ⊥) {x : G}
    (hx : x ∈ Subgroup.normalizer (C : Set G)) (hQC : Q ≤ C) (hQ'C : Q' ≤ C)
    (hCQ : C ≤ Q ⊔ Q') (hQp : IsPGroup r Q) (hQ'p : IsPGroup r Q')
    (hAQ : A.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (Q : Set G))
    (hAQ' : A.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (Q' : Set G)) :
    C ≤ ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
      C ⊓ Subgroup.centralizer (B : Set G) := by
  haveI : IsElementaryAbelian p (A.map (MulAut.conj x).toMonoidHom) := IsElementaryAbelian.map _
  haveI : Nontrivial (A.map (MulAut.conj x).toMonoidHom) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact fun h => hA1 ((Subgroup.map_eq_bot_iff_of_injective A (MulAut.conj x).injective).1 h)
  refine le_iSup_hyper_of_map_conj_normalizer hx (hCQ.trans (sup_le ?_ ?_))
  · exact le_iSup_hyper_of_coprime (not_dvd_card_of_isPGroup hrp hQp) hAQ hQC
  · exact le_iSup_hyper_of_coprime (not_dvd_card_of_isPGroup hrp hQ'p) hAQ' hQ'C

theorem le_iSup_hyper_of_normalizing [Finite G] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hrp : r ≠ p) {C Q Q' M T A : Subgroup G} [IsElementaryAbelian p A] (hA1 : A ≠ ⊥)
    (hQC : Q ≤ C) (hQ'C : Q' ≤ C) (hMC : M ≤ Subgroup.normalizer (C : Set G))
    (hTC : T ≤ Subgroup.normalizer (C : Set G)) (hCQ : C ≤ Q ⊔ Q')
    (hQp : IsPGroup r Q) (hQ'p : IsPGroup r Q')
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) (hMQ' : M ≤ Subgroup.normalizer (Q' : Set G))
    (hTQ : T ≤ Subgroup.normalizer (Q : Set G)) (hTQ' : T ≤ Subgroup.normalizer (Q' : Set G))
    {x : G} (hx : x ∈ Subgroup.normalizer (C : Set G))
    (hAx : A.map (MulAut.conj x).toMonoidHom ≤ Q ⊔ (M ⊔ T)) :
    C ≤ ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
      C ⊓ Subgroup.centralizer (B : Set G) := by
  have hM'Q : M ⊔ T ≤ Subgroup.normalizer (Q : Set G) := sup_le hMQ hTQ
  have hM'Q' : M ⊔ T ≤ Subgroup.normalizer (Q' : Set G) := sup_le hMQ' hTQ'
  have hM'C : M ⊔ T ≤ Subgroup.normalizer (C : Set G) := sup_le hMC hTC
  have hPQ : Q ⊔ (M ⊔ T) ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer hM'Q
  have hPC : Q ⊔ (M ⊔ T) ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (hQC.trans Subgroup.le_normalizer) hM'C
  have hpQ : ¬ p ∣ Nat.card Q := not_dvd_card_of_isPGroup hrp hQp
  have hindex : ¬ p ∣ ((M ⊔ T).subgroupOf (Q ⊔ (M ⊔ T))).index := fun h =>
    hpQ (h.trans (index_subgroupOf_dvd_card_of_sup le_sup_left le_sup_right hPQ (sup_comm _ _)))
  have hAxp : IsPGroup p (A.map (MulAut.conj x).toMonoidHom) :=
    (IsElementaryAbelian.isPGroup p A).map _
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hAx hAxp hindex
  have hmap : A.map (MulAut.conj (y * x)).toMonoidHom =
      (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  have hA'' : A.map (MulAut.conj (y * x)).toMonoidHom ≤ M ⊔ T := hmap ▸ hyA
  have hyxC : y * x ∈ Subgroup.normalizer (C : Set G) := Subgroup.mul_mem _ (hPC hy) hx
  exact le_iSup_hyper_of_normalizes_radicals hrp hA1 hyxC hQC hQ'C hCQ hQp hQ'p
    (hA''.trans hM'Q) (hA''.trans hM'Q')

end Generic

section Transport

variable {M : Type*} [Group M] {C D : Subgroup M}

theorem seitzHyperGamma_eq_top_of_matrix {p : ℕ} (ι : D →* MulAut C)
    (hι : ∀ (g : D) (s : C), ((ι g s : C) : M) = (g : M) * (s : M) * (g : M)⁻¹)
    (hinj : Function.Injective ι) (E : Subgroup (MulAut C)) (hE : E ≤ ι.range)
    (h : C ≤ ⨆ (B : Subgroup M) (_ : B ≤ (E.comap ι).map D.subtype)
      (_ : B.relIndex ((E.comap ι).map D.subtype) = p), C ⊓ Subgroup.centralizer (B : Set M)) :
    seitzHyperGamma p E = ⊤ := by
  have hEmap : (E.comap ι).map ι = E := Subgroup.map_comap_eq_self hE
  have key : ∀ B : Subgroup M, B ≤ (E.comap ι).map D.subtype →
      B.relIndex ((E.comap ι).map D.subtype) = p →
      C ⊓ Subgroup.centralizer (B : Set M) ≤ (seitzHyperGamma p E).map C.subtype := by
    intro B hBA hBi y hy
    obtain ⟨hyC, hyB⟩ := Subgroup.mem_inf.1 hy
    have hBD : B ≤ D := hBA.trans (by rintro _ ⟨g, -, rfl⟩; exact g.2)
    set B' : Subgroup D := B.comap D.subtype with hB'
    have hB'E : B' ≤ E.comap ι := fun g hg => by
      obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.1 (hBA (Subgroup.mem_comap.1 hg))
      have : g' = g := Subtype.ext hgg'
      exact this ▸ hg'
    have hBmap : B'.map D.subtype = B := by
      rw [hB', Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.2 hBD]
    have hFE : B'.map ι ≤ E := hEmap ▸ Subgroup.map_mono hB'E
    have hFi : (B'.map ι).relIndex E = p := by
      have h1 := Subgroup.relIndex_map_map_of_injective B' (E.comap ι) hinj
      have h2 := Subgroup.relIndex_map_map_of_injective B' (E.comap ι) D.subtype_injective
      rw [hEmap] at h1
      rw [hBmap] at h2
      rw [h1, ← h2, hBi]
    have hyF : (⟨y, hyC⟩ : C) ∈ fixedPoints (B'.map ι) := by
      rintro φ ⟨g, hg, rfl⟩
      apply Subtype.ext
      have hgB : (g : M) ∈ B := Subgroup.mem_comap.1 hg
      have hcomm := (Subgroup.mem_centralizer_iff.1 hyB) (g : M) hgB
      change ((ι g ⟨y, hyC⟩ : C) : M) = y
      rw [hι, hcomm, mul_inv_cancel_right]
    exact ⟨⟨y, hyC⟩, Subgroup.mem_iSup_of_mem (B'.map ι)
      (Subgroup.mem_iSup_of_mem ⟨hFE, hFi⟩ hyF), rfl⟩
  rw [eq_top_iff]
  intro s _
  obtain ⟨t, ht, hts⟩ := (h.trans (iSup₂_le fun B hB => iSup_le fun hBi => key B hB hBi)) s.2
  have : t = s := Subtype.ext hts
  rwa [← this]

theorem isElementaryAbelian_matrixPlane {p : ℕ} (ι : D →* MulAut C) (hinj : Function.Injective ι)
    {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) :
    IsElementaryAbelian p ((E.comap ι).map D.subtype) := by
  refine IsElementaryAbelian.of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
  · obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨h, hh, rfl⟩ := hb
    have : g * h = h * g := by
      apply hinj
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨ι g, hg⟩ ⟨ι h, hh⟩)
    exact congrArg Subtype.val this
  · obtain ⟨g, hg, rfl⟩ := ha
    have : g ^ p = 1 := hinj (by rw [map_pow, map_one]; exact hE.2 _ hg)
    simpa using congrArg Subtype.val this

theorem matrixPlane_ne_bot (ι : D →* MulAut C) {E : Subgroup (MulAut C)} (hE : E ≤ ι.range)
    (hE1 : E ≠ ⊥) : (E.comap ι).map D.subtype ≠ ⊥ := by
  intro h
  apply hE1
  have h1 : E.comap ι = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).1 h
  rw [← Subgroup.map_comap_eq_self hE, h1, Subgroup.map_bot]

theorem matrixPlane_le_normalizer (ι : D →* MulAut C)
    (hι : ∀ (g : D) (s : C), ((ι g s : C) : M) = (g : M) * (s : M) * (g : M)⁻¹)
    {E : Subgroup (MulAut C)} {R : Subgroup C} (hR : ∀ ε ∈ E, R.map ε.toMonoidHom = R) :
    (E.comap ι).map D.subtype ≤ Subgroup.normalizer ((R.map C.subtype : Subgroup M) : Set M) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hgR := hR (ι g) hg
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr' : ι g r ∈ R.map (ι g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hgR] at hr'
    exact ⟨_, hr', by simp [hι]⟩
  · rintro ⟨r', hr', hy⟩
    have hr'' : r' ∈ R.map (ι g).toMonoidHom := by rw [hgR]; exact hr'
    obtain ⟨r, hr, rfl⟩ := hr''
    refine ⟨r, hr, ?_⟩
    have h1 : (g : M) * (r : M) * (g : M)⁻¹ = (g : M) * y * (g : M)⁻¹ := by
      rw [← hι]
      exact hy
    exact mul_left_cancel (mul_right_cancel h1)

end Transport

section Ordinary


theorem ordinary_inndiag_prime_subgroup_hyperplane_generation (τ : Tag) (k : Type) [Field k]
    [Finite k] (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup τ k)] (A : Subgroup (ModGL τ k)) (hAC : A ≤ innDiagGL τ k)
    [IsElementaryAbelian p A] (hA1 : A ≠ ⊥) (R : Subgroup (ModGL τ k))
    (hRC : R ≤ adjointGroup τ k) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL τ k))) :
    (⨆ (B : Subgroup (ModGL τ k)) (_ : B ≤ A) (_ : B.relIndex A = p),
      adjointGroup τ k ⊓ Subgroup.centralizer (B : Set (ModGL τ k))) = adjointGroup τ k := by
  have := finite_modGL (τ := τ) (K := k)
  refine le_antisymm (iSup₂_le fun B _ => iSup_le fun _ => inf_le_left) ?_
  set T : Subgroup (ModGL τ k) := (rootDiagUnitHom τ k).range with hT
  have hTC : T ≤ Subgroup.normalizer (adjointGroup τ k : Set (ModGL τ k)) := by
    rintro _ ⟨b, rfl⟩
    exact (root_diagonal_conjugation τ k b).2.2
  have hTD : T ≤ diagonalGroup := by
    rintro _ ⟨b, rfl⟩
    exact CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_diagonalGroup b
  obtain ⟨g, hg, l, hl, hJ, hAg⟩ := exists_conj_mem_parabolic_sup_of_normalizes
    (RootWeightDatum.ordinary τ : RootWeightDatum k) r (T := T) hTC hTD hRC hRr hR hAC hAR
  set J : Set (Fin τ.rank) := (RootWeightDatum.ordinary τ : RootWeightDatum k).face l
  have hJ' : J ≠ Set.univ := hJ
  obtain ⟨w₀, δ, hδinj, hδ⟩ := exists_longest_simple_perm τ
  have hnC : canonicalRep (coxeterSystem τ) k w₀ ∈ adjointGroup τ k :=
    canonicalRep_mem_adjointGroup _ k w₀
  set n := canonicalRep (coxeterSystem τ) k w₀
  set Q' := (parabolicRadical τ k (δ '' J)).map (MulAut.conj n⁻¹).toMonoidHom
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin'⟩ :=
    parabolic_root_radical_Levi_factors τ k (δ '' J)
  have hQ'p : IsPGroup r Q' := (hfin' r).2.1.map _
  have hQ'C : Q' ≤ adjointGroup τ k := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem (inv_mem hnC) (rootSpan_le_adjointGroup k _ hq)) (inv_inv n ▸ hnC)
  have hMQ' : parabolicLevi τ k J ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) :=
    parabolicLevi_le_normalizer_opposite hδ J
  have hTQ' : T ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) := by
    rintro _ ⟨b, rfl⟩
    refine mem_normalizer_map_conj_inv ?_
    change n * rootDiagUnit τ b * n⁻¹ ∈ _
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_normalizer_parabolicRadical _ _
  have hCQ := adjointGroup_le_parabolicRadical_sup_opposite (τ := τ) (k := k) (r := r) hδinj hδ hJ'
  obtain ⟨-, -, -, hMP, -, hPQM, -, -, -, -, -, -, hfin⟩ :=
    parabolic_root_radical_Levi_factors τ k J
  have hQp : IsPGroup r (parabolicRadical τ k J) := (hfin r).2.1
  have hQC : parabolicRadical τ k J ≤ adjointGroup τ k := rootSpan_le_adjointGroup k _
  have hMC : parabolicLevi τ k J ≤ adjointGroup τ k :=
    hMP.trans (parabolicSubgroup_le_adjointGroup τ k J)
  have hMQ : parabolicLevi τ k J ≤ Subgroup.normalizer (parabolicRadical τ k J : Set (ModGL τ k)) :=
    hMP.trans (parabolicSubgroup_le_normalizer_parabolicRadical J)
  have hTQ : T ≤ Subgroup.normalizer (parabolicRadical τ k J : Set (ModGL τ k)) := by
    rintro _ ⟨b, rfl⟩
    exact rootDiagUnit_mem_normalizer_parabolicRadical b J
  have hAx : A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      parabolicRadical τ k J ⊔ (parabolicLevi τ k J ⊔ T) := by
    rintro _ ⟨a, ha, rfl⟩
    have h : g⁻¹ * a * g ∈ parabolicSubgroup τ k J ⊔ T := hAg a ha
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine (sup_le (hPQM ▸ sup_le le_sup_left (le_sup_left.trans le_sup_right))
      (le_sup_right.trans le_sup_right) : parabolicSubgroup τ k J ⊔ T ≤
        parabolicRadical τ k J ⊔ (parabolicLevi τ k J ⊔ T)) h
  exact le_iSup_hyper_of_normalizing hrp hA1 hQC hQ'C (hMC.trans Subgroup.le_normalizer) hTC hCQ
    hQp hQ'p hMQ hMQ' hTQ hTQ' (Subgroup.le_normalizer (inv_mem hg)) hAx

theorem seitzHyperGamma_eq_top_of_inndiag {τ : Tag} {k : Type} [Field k] [Finite k] {r p : ℕ}
    [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p) [IsSimpleGroup (adjointGroup τ k)]
    {D : Subgroup (ModGL τ k)} (hD : D ≤ innDiagGL τ k) (ι : D →* MulAut (adjointGroup τ k))
    (hι : ∀ (g : D) (s : adjointGroup τ k), ((ι g s : adjointGroup τ k) : ModGL τ k) =
      (g : ModGL τ k) * (s : ModGL τ k) * (g : ModGL τ k)⁻¹)
    (hinj : Function.Injective ι) {E : Subgroup (MulAut (adjointGroup τ k))} (hE : E ≤ ι.range)
    (hEab : IsElemAbelian p E) (hE1 : E ≠ ⊥)
    (hnorm : ∃ R : Subgroup (adjointGroup τ k), R ≠ ⊥ ∧ IsPGroup r R ∧
      ∀ ε ∈ E, R.map ε.toMonoidHom = R) :
    seitzHyperGamma p E = ⊤ := by
  obtain ⟨R, hR1, hRp, hRn⟩ := hnorm
  haveI := isElementaryAbelian_matrixPlane ι hinj hEab
  have hAD : (E.comap ι).map D.subtype ≤ D := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  refine seitzHyperGamma_eq_top_of_matrix ι hι hinj E hE ?_
  exact (ordinary_inndiag_prime_subgroup_hyperplane_generation τ k r p hrp _ (hAD.trans hD)
    (matrixPlane_ne_bot ι hE hE1) (R.map (adjointGroup τ k).subtype)
    (by rintro _ ⟨s, -, rfl⟩; exact s.2) (hRp.map _)
    (fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R
      (adjointGroup τ k).subtype_injective).1 h))
    (matrixPlane_le_normalizer ι hι hRn)).ge

end Ordinary

section Light


theorem e6Inndiag_eq_innerAut_of_lt_four (K : Type) [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (h : ¬ 4 ≤ Nat.card K) :
    e6Inndiag K = CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  push Not at h
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, -, hcard'⟩ := FiniteField.card K (ringChar K)
  have hcard : Nat.card K = ringChar K ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, hcard']
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have hp2 := hp.two_le
  have he1 : (e : ℕ) = 1 := by
    by_contra hne
    have he2 : 2 ≤ (e : ℕ) := by have := e.pos; omega
    have h4 : ringChar K ^ 2 ≤ ringChar K ^ (e : ℕ) := Nat.pow_le_pow_right (by omega) he2
    have h5 : 4 ≤ ringChar K ^ 2 := by nlinarith
    omega
  rw [he1, pow_one] at hcard
  have h23 : ringChar K = 2 := by
    have hle : ringChar K ≤ 3 := by omega
    rcases (show ringChar K = 2 ∨ ringChar K = 3 by omega) with h2 | h3
    · exact h2
    · exact absurd h3 hK3
  have hK2 : Nat.card K = 2 := by rw [hcard, h23]
  exact e6Inndiag_eq_innerAut_of_not_dvd K (by rw [hK2]; norm_num)

end Light

section E6


theorem e6DiagParCubes_holds : E6ThreeDefs.E6DiagParCubes := by
  intro K _ _ hK3 E hEab hcard hEd hnorm
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (adjointGroup Tag.E6 K) :=
    CFSG.SeitzReduction.E6Pilot.isSimpleGroup_adjointGroup_E6
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    simp at hcard
  by_cases hK4 : 4 ≤ Nat.card K
  · exact seitzHyperGamma_eq_top_of_inndiag hK3 (D := e6InndiagGL K) le_rfl (e6InndiagConj K)
      (fun g s => e6InndiagConj_apply g s) (e6InndiagConj_injective K hK4)
      (by rw [range_e6InndiagConj]; exact hEd) hEab hE1 hnorm
  · have hinn := e6Inndiag_eq_innerAut_of_lt_four K hK3 hK4
    exact seitzHyperGamma_eq_top_of_inndiag hK3 (D := adjointGroup Tag.E6 K) le_sup_left
      MulAut.conj (fun g s => rfl)
      (CFSG.Fischer.mulAutConj_injective center_adjointGroup_eq_bot)
      (hEd.trans hinn.le) hEab hE1 hnorm

end E6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
