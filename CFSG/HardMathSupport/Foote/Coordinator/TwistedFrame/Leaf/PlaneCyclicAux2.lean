module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCyclicAux1
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus
public import CFSG.RankThree.PartOne.KD4L.TrialityEquiv
public import CFSG.RankThree.PartOne.KE.SigmaTransport


public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCyclic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section E8Twelve

open Matrix CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KD4T CFSG.RankThree.Chevalley

theorem isCyclic_centralizer_of_injective_hom' {G H : Type*} [Group G] [Group H] (Λ : G →* H)
    (hΛ : Function.Injective Λ) {p : ℕ}
    (hH : ∀ x : H, orderOf x = p → IsCyclic ↥(Subgroup.centralizer ({x} : Set H))) {g : G}
    (hg : orderOf g = p) : IsCyclic ↥(Subgroup.centralizer ({g} : Set G)) := by
  have hc := hH (Λ g) (by rw [orderOf_injective Λ hΛ g, hg])
  let φ : ↥(Subgroup.centralizer ({g} : Set G)) →*
      ↥(Subgroup.centralizer ({Λ g} : Set H)) :=
    (Λ.comp (Subgroup.centralizer ({g} : Set G)).subtype).codRestrict _ (by
      rintro ⟨x, hx⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [← map_mul, ← map_mul, hx])
  refine isCyclic_of_injective φ ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply Subtype.ext
  exact hΛ (congrArg Subtype.val h)

theorem dvd_phi12_of_orderOf {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 12) : p ∣ q ^ 4 - q ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, orderOf_zero] at h
    omega
  set x : ZMod p := (q : ZMod p) with hx
  have h12 : x ^ 12 = 1 := by rw [← h]; exact pow_orderOf_eq_one x
  have h6 : x ^ 6 ≠ 1 := fun h6 => by
    have := orderOf_dvd_of_pow_eq_one h6
    rw [h] at this
    omega
  have h4 : x ^ 4 ≠ 1 := fun h4 => by
    have := orderOf_dvd_of_pow_eq_one h4
    rw [h] at this
    omega
  have hsq : (x ^ 6 - 1) * (x ^ 6 + 1) = 0 := by linear_combination h12
  have h61 : x ^ 6 + 1 = 0 := (mul_eq_zero.1 hsq).resolve_left (sub_ne_zero.2 h6)
  have hfac : (x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) = 0 := by linear_combination h61
  have h21 : x ^ 2 + 1 ≠ 0 := fun h21 => h4 (by linear_combination (x ^ 2 - 1) * h21)
  have h0 : x ^ 4 - x ^ 2 + 1 = 0 := (mul_eq_zero.1 hfac).resolve_left h21
  have hq2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq0) (by norm_num)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub hq2]
  exact h0

theorem d4_layer_equiv_E8_one {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) (n : ModGL Tag.E8 L) (hn : n ∈ monomialSubgroup Tag.E8 L)
    (hact : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        weylQuotientHom Tag.E8 L ⟨n, hn⟩ • α =
          u • permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α)
    (P : Subgroup (ModGL Tag.E8 L))
    (hP : P = rootSpan Tag.E8 L (parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (ℓ ^ f) ^ 3 ∧
      (∀ c, σ c = c ^ ℓ ^ f) ∧ Nonempty (P ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨-, hπ, hπ'⟩ := leafCycle_E8 1 2 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have h1 : ∀ k : Fin Tag.D4.rank, List.formPerm [(1 : Fin Tag.E8.rank), 2, 4] (d4Id k) =
      d4Id (rhoE 1 k) := by decide +kernel
  obtain ⟨K, hK, hKf, σ, hKc, hσ, hE⟩ := triality_layer_graph_equiv hf
    (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) 1 (Or.inl rfl) h1 (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) n hn hact P hP
  exact ⟨K, hK, hKf, σ, hKc, fun x => by simpa using hσ x, hE⟩


theorem d4_transported_equiv_E8_one {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) (v : WeylGroup Tag.E8) (n : ModGL Tag.E8 L)
    (hn : n ∈ monomialSubgroup Tag.E8 L)
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v) • α =
          u • permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α)
    (P : Subgroup (ModGL Tag.E8 L))
    (hP : P = rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (ℓ ^ f) ^ 3 ∧
      (∀ c, σ c = c ^ ℓ ^ f) ∧ Nonempty (P ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  set n' : ModGL Tag.E8 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVm) hn) hVm
  have hπV : weylQuotientHom Tag.E8 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E8 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hn⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E8 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hn⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  set P' : Subgroup (ModGL Tag.E8 L) :=
    rootSpan Tag.E8 L (parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓ twistedFixedPoints n' Φ
    with hP'
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨e'⟩⟩ := d4_layer_equiv_E8_one hf n' hn'm
    (by rw [hπn']; exact hcert) P' rfl
  have hroots : ∀ r ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8), IsRoot Tag.E8 r := fun r hr => hr.1
  set c₀ : ModGL Tag.E8 L →* ModGL Tag.E8 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hQ : (rootSpan Tag.E8 L (parabolicRoots Tag.E8 (d4Nodes Tag.E8))).map c₀ =
      rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) :=
    map_conj_rootSpan v hroots
  have hR : (twistedFixedPoints n' Φ).map c₀ = twistedFixedPoints n Φ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hcapp]
      exact (mem_twistedFixedPoints_conj hΦV).1 hx
    · intro hy
      refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
      · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        rw [e]
        exact hy
      · rw [hcapp]
        group
  have hPmap : P = P'.map c₀ := by
    rw [hP, hP', Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]
  refine ⟨K, hK, hKf, σ, hKc, hσ, ⟨?_⟩⟩
  exact ((MulEquiv.subgroupCongr hPmap).trans
    (P'.equivMapOfInjective c₀ (MulAut.conj V).injective).symm).trans e'

@[expose] def e8T12WordV : List (Fin Tag.E8.rank) :=
  [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2, 1,
    3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0]

@[expose] def e8T12Mw : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 0, 0, 0, 0, -1, 2, 0; 0, 0, 0, 0, 1, -2, 2, 0; 0, 1, 0, 0, 0, -2, 3, 0;
    0, 0, 0, 1, 0, -3, 4, 0; 0, 0, 1, 0, 0, -2, 3, 0; 1, 0, 0, 0, 0, -1, 2, 0;
    0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def e8T12Mv : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![-1, 0, 0, 0, 2, -2, 0, 0; -2, 1, 0, 0, 2, -2, 0, 0; -2, 1, 0, 0, 3, -4, 1, 0;
    -3, 2, 0, 0, 4, -5, 0, 1; -2, 2, 0, 0, 3, -4, 0, 0; -2, 2, 0, 0, 2, -3, 0, 0;
    -2, 1, 1, 0, 1, -2, 0, 0; -1, 0, 0, 1, 0, -1, 0, 0]

theorem wordMat_e8T12w : wordMat Tag.E8 TwClass.wordE8Twelve = e8T12Mw := by
  have h : ∀ ij : Fin Tag.E8.rank × Fin Tag.E8.rank,
      wordMat Tag.E8 TwClass.wordE8Twelve ij.1 ij.2 = e8T12Mw ij.1 ij.2 := by decide +kernel
  exact Matrix.ext fun i j => h (i, j)

theorem wordMat_e8T12v : wordMat Tag.E8 e8T12WordV = e8T12Mv := by
  have h : ∀ ij : Fin Tag.E8.rank × Fin Tag.E8.rank,
      wordMat Tag.E8 e8T12WordV ij.1 ij.2 = e8T12Mv ij.1 ij.2 := by decide +kernel
  exact Matrix.ext fun i j => h (i, j)

theorem e8T12_J₂_iff : ∀ i : Fin Tag.E8.rank,
    i.val ∉ TwClass.e8Twelve.J₂ ↔ ¬ (1 ≤ i.val ∧ i.val ≤ 4) := by decide

theorem e8T12_S₂_eq : (TwClass.e8Twelve.S₂ : Set (Fin Tag.E8.rank → ℤ)) =
    parabolicRoots Tag.E8 (d4Nodes Tag.E8) := by
  ext α
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  rw [e8T12_J₂_iff i]
  exact Iff.rfl

theorem e8T12_S₁_orth : ∀ m : Fin 240,
    (∀ m' : Fin 240,
      (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m' i = 0) →
        iform (τ := Tag.E8) (e8RootVec m) (e8RootVec m') = 0) →
      ∃ m' : Fin 240,
        (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m' i = 0) ∧
          e8RootVec m = e8T12Mv *ᵥ e8RootVec m' := by
  decide +kernel

theorem e8T12_S₁_roots : ∀ m' : Fin 240,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m' i = 0) →
      (∃ m : Fin 240, e8RootVec m = e8T12Mv *ᵥ e8RootVec m') ∧
        ∀ m'' : Fin 240,
          (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m'' i = 0) →
            iform (τ := Tag.E8) (e8T12Mv *ᵥ e8RootVec m') (e8RootVec m'') = 0 := by
  decide +kernel

theorem e8T12_cert₂ : ∀ m : Fin 240,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m i = 0) →
      e8T12Mw *ᵥ e8RootVec m =
        permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) (e8RootVec m) := by
  decide +kernel

theorem e8T12_cert₁ : ∀ m : Fin 240,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m i = 0) →
      e8T12Mw *ᵥ (e8T12Mv *ᵥ e8RootVec m) =
        e8T12Mv *ᵥ permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) (e8RootVec m) := by
  decide +kernel


@[expose] def e8T12W : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve

@[expose] def e8T12V : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd e8T12WordV

theorem e8T12_vs (x : Fin Tag.E8.rank → ℤ) : e8T12V • x = e8T12Mv *ᵥ x := by
  unfold e8T12V
  rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, wordMat_e8T12v]

theorem e8T12_ws (x : Fin Tag.E8.rank → ℤ) : e8T12W • x = e8T12Mw *ᵥ x := by
  unfold e8T12W
  rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, wordMat_e8T12w]

theorem e8T12_S₁_mem_of {β : Fin Tag.E8.rank → ℤ} (h1 : IsRoot Tag.E8 β)
    (h2 : ∀ m : Fin 240,
      (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m i = 0) →
        iform (τ := Tag.E8) β (e8RootVec m) = 0) :
    β ∈ (TwClass.e8Twelve.S₁ : Set (Fin Tag.E8.rank → ℤ)) := by
  refine ⟨h1, fun α' hα' => ?_⟩
  obtain ⟨hα'r, hα'z⟩ := hα'
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα'r
  exact h2 m (fun i hi => hα'z i hi)

theorem e8T12_S₁_eq : (TwClass.e8Twelve.S₁ : Set (Fin Tag.E8.rank → ℤ)) =
    (fun γ => e8T12V • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) := by
  ext β
  constructor
  · rintro ⟨hr, ho⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    obtain ⟨m', hm', h⟩ := e8T12_S₁_orth m fun m' hm' =>
      ho (e8RootVec m') ⟨isRoot_e8RootVec m', hm'⟩
    refine ⟨e8RootVec m', ⟨isRoot_e8RootVec m', fun i hi => hm' i ((e8T12_J₂_iff i).2 hi)⟩, ?_⟩
    show e8T12V • e8RootVec m' = e8RootVec m
    rw [e8T12_vs]
    exact h.symm
  · rintro ⟨α, ⟨hα, hz⟩, rfl⟩
    obtain ⟨m', rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα
    have hz' : ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m' i = 0 :=
      fun i hi => hz i ((e8T12_J₂_iff i).1 hi)
    obtain ⟨⟨m, hm⟩, ho⟩ := e8T12_S₁_roots m' hz'
    have hv : e8T12V • e8RootVec m' = e8T12Mv *ᵥ e8RootVec m' := e8T12_vs _
    refine e8T12_S₁_mem_of (β := e8T12V • e8RootVec m') ?_ ?_
    · rw [hv]
      exact isRoot_iff_exists_e8RootVec.2 ⟨m, hm⟩
    · rw [hv]
      exact ho

theorem e8T12_S₂_eq' : (TwClass.e8Twelve.S₂ : Set (Fin Tag.E8.rank → ℤ)) =
    (fun γ => (1 : WeylGroup Tag.E8) • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) := by
  rw [e8T12_S₂_eq]
  ext α
  simp only [one_smul, Set.image_id']

theorem e8T12_hcert₁ : ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
    (e8T12V⁻¹ * e8T12W * e8T12V) • α =
      permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by
  rintro α ⟨hα, hz⟩
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα
  have hz' : ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m i = 0 :=
    fun i hi => hz i ((e8T12_J₂_iff i).1 hi)
  have h := e8T12_cert₁ m hz'
  rw [mul_smul, mul_smul, e8T12_vs, e8T12_ws, h, ← e8T12_vs, inv_smul_smul]

theorem e8T12_hcert₂ : ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
    ((1 : WeylGroup Tag.E8)⁻¹ * e8T12W * (1 : WeylGroup Tag.E8)) • α =
      permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by
  rintro α ⟨hα, hz⟩
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα
  have hz' : ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → e8RootVec m i = 0 :=
    fun i hi => hz i ((e8T12_J₂_iff i).1 hi)
  rw [inv_one, one_mul, mul_one, e8T12_ws, e8T12_cert₂ m hz']

theorem cyclic_of_d4 {K : Type} [Field K] [Finite K] {w : WeylGroup Tag.E8}
    (D : LangLevi Tag.E8 K w) (v : WeylGroup Tag.E8) {S : Set (Fin Tag.E8.rank → ℤ)}
    (hS : S = (fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8))
    (hcert : ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      (v⁻¹ * w * v) • α = permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card K ^ 4 - Nat.card K ^ 2 + 1) :
    ∀ g : ↥(D.frame S), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(D.frame S))) := by
  classical
  intro g hg
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓp, hcard⟩ := FiniteField.card K ℓ
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  haveI : CharP D.L ℓ := charP_of_injective_algebraMap (algebraMap K D.L).injective ℓ
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hKcard : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hFr : D.Fr = iterateFrobenius D.L ℓ (f : ℕ) :=
    RingHom.ext fun c => by rw [D.hFr, hKcard, iterateFrobenius_def]
  set n : ModGL Tag.E8 D.L := canonicalRep (coxeterSystem Tag.E8) D.L w with hndef
  have hn : n ∈ monomialSubgroup Tag.E8 D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hπw : weylQuotientHom Tag.E8 D.L ⟨n, hn⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  set P : Subgroup (ModGL Tag.E8 D.L) :=
    rootSpan Tag.E8 D.L ((fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius D.L ℓ (f : ℕ)))) with hP
  obtain ⟨K', hK'F, hK'fin, σ, hK', hσ, ⟨e⟩⟩ := d4_transported_equiv_E8_one (L := D.L) (ℓ := ℓ)
    (f := (f : ℕ)) f.pos v n hn
    ⟨1, one_mem _, fun α hα => by rw [hπw, hcert α hα, one_smul]⟩ P rfl
  let ι : ↥(D.frame S) →* ↥P :=
    ((frameEmb D).comp (D.frame S).subtype).codRestrict P (fun x => by
      refine ⟨?_, ?_⟩
      · rw [← hS]
        exact ((mem_frame_iff' D S x).1 x.2).2
      · rw [← hFr]
        exact frameEmb_twistedFixed D x)
  have hι : Function.Injective ι := fun x y h => by
    apply Subtype.ext
    exact frameEmb_injective D (congrArg Subtype.val h)
  obtain ⟨T, -, -, hT⟩ := triality_cyclotomic_twelve_torus_and_prime_centralizers hℓp f.pos K' hK'
    σ hσ
  have hd' : p ∣ (ℓ ^ (f : ℕ)) ^ 4 - (ℓ ^ (f : ℕ)) ^ 2 + 1 := by rwa [hKcard] at hd
  refine isCyclic_centralizer_of_injective_hom' (e.toMonoidHom.comp ι) (e.injective.comp hι)
    (fun x hx => ?_) hg
  obtain ⟨-, -, hc⟩ := hT p hp (by omega) hd'
  obtain ⟨-, -, -, hcyc, -⟩ := hc x hx
  exact hcyc

theorem planeCyclic_e8Twelve (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.e8Twelve.e) :
    (∀ g : ↥(TwClass.e8Twelve.X₁ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e8Twelve.X₁ D)))) ∧
    (∀ g : ↥(TwClass.e8Twelve.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e8Twelve.X₂ D)))) := by
  have hd : p ∣ Nat.card K ^ 4 - Nat.card K ^ 2 + 1 := dvd_phi12_of_orderOf hp hord
  exact ⟨cyclic_of_d4 (w := e8T12W) D e8T12V e8T12_S₁_eq e8T12_hcert₁ hp hp5 hd,
    cyclic_of_d4 (w := e8T12W) D 1 e8T12_S₂_eq' e8T12_hcert₂ hp hp5 hd⟩

end E8Twelve

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCyclic
