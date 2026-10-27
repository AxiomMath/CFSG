module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnStr
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.Monster.B.E6.StdF4RadicalRoots
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartOne.KD4L.TrialityEquiv

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)


set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

@[expose] def d4t2outZeta : Fin Tag.E6.rank → ℤ := ![2, 3, 4, 6, 5, 4]

@[expose] def d4t2outPerms : List (Equiv.Perm (Fin Tag.E6.rank)) :=
  [1, List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4], List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2]]

@[expose] def d4t2outVec (π : Equiv.Perm (Fin Tag.E6.rank)) (b₀ b₅ : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → ℤ :=
  (2 : ℤ) • b₀ + (3 : ℤ) • Pi.single (π 1) 1 + (4 : ℤ) • Pi.single (π 2) 1 +
    (6 : ℤ) • Pi.single (π 3) 1 + (5 : ℤ) • Pi.single (π 4) 1 + (4 : ℤ) • b₅

@[expose] def d4t2outGram (π : Equiv.Perm (Fin Tag.E6.rank)) (b : Fin Tag.E6.rank → ℤ)
    (i : Fin Tag.E6.rank) : Bool :=
  ([1, 2, 3, 4] : List (Fin Tag.E6.rank)).all fun j =>
    iform b (Pi.single (π j) 1) == iform (Pi.single i 1) (Pi.single j 1)

@[expose] def d4t2outCong (b : Fin Tag.E6.rank → ℤ) : Bool := (b 0 + b 5 + 1) % 3 == 0

@[expose] def d4t2outPair (π : Equiv.Perm (Fin Tag.E6.rank)) (b₀ b₅ : Fin Tag.E6.rank → ℤ) :
    Bool :=
  d4t2outGram π b₅ 5 && d4t2outCong b₅ && iform b₀ b₅ == 0 &&
    (List.finRange Tag.E6.rank).all fun t => (d4t2outVec π b₀ b₅ t - d4t2outZeta t) % 3 == 0

@[expose] def d4t2outCheck : Bool :=
  d4t2outPerms.all fun π => (List.range e6Certificate.roots.length).all fun k =>
    !(d4t2outGram π (e6Certificate.root k) 0 && d4t2outCong (e6Certificate.root k)) ||
      (List.range e6Certificate.roots.length).all fun m =>
        !d4t2outPair π (e6Certificate.root k) (e6Certificate.root m)

theorem d4t2outCheck_eq : d4t2outCheck = true := by decide +kernel

theorem d4t2out_cartan_zeta : ∀ i : Fin Tag.E6.rank,
    (3 : ℤ) ∣ ∑ j, Tag.E6.cartan i j * d4t2outZeta j := by
  decide +kernel

theorem d4t2outZeta_eq : d4t2outZeta = (2 : ℤ) • Pi.single 0 1 + (3 : ℤ) • Pi.single 1 1 +
    (4 : ℤ) • Pi.single 2 1 + (6 : ℤ) • Pi.single 3 1 + (5 : ℤ) • Pi.single 4 1 +
      (4 : ℤ) • Pi.single 5 1 := by
  decide +kernel

theorem d4t2out_smul_zeta (w : WeylGroup Tag.E6) (t : Fin Tag.E6.rank) :
    (3 : ℤ) ∣ (w • d4t2outZeta - d4t2outZeta) t := by
  have key : ∀ x : Fin Tag.E6.rank → ℤ, (∀ i, (3 : ℤ) ∣ ∑ j, Tag.E6.cartan i j * x j) →
      (∀ i, (3 : ℤ) ∣ ∑ j, Tag.E6.cartan i j * (w • x) j) ∧
        ∀ t, (3 : ℤ) ∣ (w • x - x) t := by
    induction w using (coxeterSystem Tag.E6).simple_induction with
    | simple i =>
      intro x hx
      have hs : (coxeterSystem Tag.E6).simple i • x =
          x - (∑ j, Tag.E6.cartan i j * x j) • Pi.single i 1 := simple_smul i x
      rw [hs]
      refine ⟨fun k => ?_, fun t => ?_⟩
      · have e : ∑ j, Tag.E6.cartan k j * (x - (∑ j, Tag.E6.cartan i j * x j) •
            (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j =
            ∑ j, Tag.E6.cartan k j * x j - Tag.E6.cartan k i * ∑ j, Tag.E6.cartan i j * x j := by
          simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_comm]
        rw [e]
        exact dvd_sub (hx k) (dvd_mul_of_dvd_right (hx i) _)
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel_left, dvd_neg]
        exact dvd_mul_of_dvd_left (hx i) _
    | one =>
      intro x hx
      refine ⟨fun i => by rw [one_smul]; exact hx i, fun t => ?_⟩
      rw [one_smul, sub_self]
      exact dvd_zero 3
    | mul w w' hw hw' =>
      intro x hx
      obtain ⟨h1, h2⟩ := hw' x hx
      obtain ⟨h3, h4⟩ := hw _ h1
      refine ⟨fun i => by rw [mul_smul]; exact h3 i, fun t => ?_⟩
      have h5 := dvd_add (h4 t) (h2 t)
      rw [Pi.sub_apply, Pi.sub_apply, sub_add_sub_cancel] at h5
      rw [mul_smul, Pi.sub_apply]
      exact h5
  exact (key _ d4t2out_cartan_zeta).2 t

theorem d4t2out_rootChar_smul {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (v : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ℤ) :
    rootChar a (v • x) =
      ∏ k, rootChar a (v • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) ^ x k := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin Tag.E6.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, Finset.smul_sum]
  change rootCharHom a (Multiplicative.ofAdd
    (∑ k, v • (x k • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)))) = _
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [smul_comm v (x k), ofAdd_zsmul, map_zpow]
  rfl

section Search


theorem d4t2out_no_weyl {π : Equiv.Perm (Fin Tag.E6.rank)} (hπ : π ∈ d4t2outPerms)
    {w₀ : WeylGroup Tag.E6}
    (hw₀ : ∀ j ∈ d4Set Tag.E6, w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single (π j) 1)
    (h0 : (3 : ℤ) ∣ (w₀ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 +
      (w₀ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5 + 1)
    (h5 : (3 : ℤ) ∣ (w₀ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0 +
      (w₀ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 5 + 1) : False := by
  obtain ⟨k, hk, hkb⟩ := RootCertificate.exists_root_eq e6Certificate_check
    (IsRoot.smul (IsRoot.basis (0 : Fin Tag.E6.rank)) w₀)
  obtain ⟨m, hm, hmb⟩ := RootCertificate.exists_root_eq e6Certificate_check
    (IsRoot.smul (IsRoot.basis (5 : Fin Tag.E6.rank)) w₀)
  have hJ : ∀ j ∈ ([1, 2, 3, 4] : List (Fin Tag.E6.rank)), j ∈ d4Set Tag.E6 := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  have hgram : ∀ i : Fin Tag.E6.rank, d4t2outGram π (w₀ • Pi.single i 1) i = true := fun i =>
    List.all_eq_true.2 fun j hj => beq_iff_eq.2 (by rw [← hw₀ j (hJ j hj), iform_smul])
  have hcong : ∀ b : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ b 0 + b 5 + 1 → d4t2outCong b = true :=
    fun b hb => beq_iff_eq.2 (Int.emod_eq_zero_of_dvd hb)
  have hvec : w₀ • d4t2outZeta =
      d4t2outVec π (w₀ • Pi.single 0 1) (w₀ • Pi.single 5 1) := by
    rw [d4t2outZeta_eq]
    simp only [smul_add, smul_comm w₀ (_ : ℤ)]
    rw [hw₀ 1 ⟨by decide, by decide⟩, hw₀ 2 ⟨by decide, by decide⟩, hw₀ 3 ⟨by decide, by decide⟩,
      hw₀ 4 ⟨by decide, by decide⟩]
    rfl
  have hpair : d4t2outPair π (w₀ • Pi.single 0 1) (w₀ • Pi.single 5 1) = true := by
    simp only [d4t2outPair, Bool.and_eq_true]
    refine ⟨⟨⟨hgram 5, hcong _ h5⟩, beq_iff_eq.2 ?_⟩, List.all_eq_true.2 fun t _ => ?_⟩
    · rw [iform_smul]
      decide +kernel
    · refine beq_iff_eq.2 (Int.emod_eq_zero_of_dvd ?_)
      have := d4t2out_smul_zeta w₀ t
      rwa [hvec] at this
  have hc := d4t2outCheck_eq
  rw [d4t2outCheck, List.all_eq_true] at hc
  have hc1 := hc π hπ
  rw [List.all_eq_true] at hc1
  have hc2 := hc1 k (List.mem_range.2 hk)
  rw [hkb, hgram 0, hcong _ h0, Bool.and_self, Bool.not_true, Bool.false_or,
    List.all_eq_true] at hc2
  have hc3 := hc2 m (List.mem_range.2 hm)
  rw [hmb, hpair] at hc3
  exact Bool.false_ne_true hc3

theorem d4t2out_three_dvd {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (h3q : 3 ∣ S.D.q + 1) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hall : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i)
    {u w₀ : WeylGroup .E6} (hu : u ∈ parabolicWeylGroup .E6 (d4Set .E6))
    (hθ : ∀ γ, IsRoot .E6 γ → v⁻¹ • S.ρ (v • γ) = (u * w₀) • permLattice e6Graph γ) :
    (3 : ℤ) ∣ (w₀ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w₀ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) 5 + 1 ∧
      (3 : ℤ) ∣ (w₀ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w₀ • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) 5 + 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : ∀ γ, IsRoot .E6 γ → rootChar a (v • γ) = 1 →
      γ ∈ parabolicRoots .E6 (d4Nodes .E6) := by
    intro γ hγ h1
    have hmem : v • γ ∈ componentRoots (rootCharHom a) i :=
      hall ⟨(isRoot_smul_iff v).2 hγ, h1⟩
    rw [hΨ] at hmem
    obtain ⟨α, hα, hαe⟩ := hmem
    rwa [(smul_left_cancel_iff v).1 hαe] at hα
  have hJ : ∀ j ∈ d4Set .E6, rootChar a (v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 1 := by
    intro j hj
    have hmem : v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨_, single_mem_parabolicRoots hj, rfl⟩
    exact hmem.1.2
  have hout : ∀ γ, IsRoot .E6 γ → γ 0 ≠ 0 → rootChar a (v • γ) ≠ 1 := fun γ hγ h0 h1 =>
    h0 ((hker γ hγ h1).2 0 fun h => absurd h.1 (by decide))
  have hout5 : ∀ γ, IsRoot .E6 γ → γ 5 ≠ 0 → rootChar a (v • γ) ≠ 1 := fun γ hγ h0 h1 =>
    h0 ((hker γ hγ h1).2 5 fun h => absurd h.2 (by decide))
  have hcube : ∀ x, rootChar a x ^ 3 = 1 := fun x => by
    rw [rootChar, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap j, one_zpow]
  obtain ⟨z, hz⟩ : ∃ z, rootChar a (v • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) = z := ⟨_, rfl⟩
  have hz1 : z ≠ 1 := hz ▸ hout _ (IsRoot.basis 0) (by decide)
  have hz5 : rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) ≠ 1 :=
    hout5 _ (IsRoot.basis 5) (by decide)
  have hγ : IsRoot .E6 (Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 +
      Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := by
    have e : (Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 :
        Fin Tag.E6.rank → ℤ) =
        reflect .E6 0 (reflect .E6 2 (reflect .E6 3 (reflect .E6 4 (Pi.single 5 1)))) := by
      decide +kernel
    rw [e]
    exact .reflect _ (.reflect _ (.reflect _ (.reflect _ (.basis _))))
  have h05 : z * rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) ≠ 1 := by
    have h := hout _ hγ (by decide)
    simp only [smul_add, rootChar_add, hJ 2 ⟨by decide, by decide⟩, hJ 3 ⟨by decide, by decide⟩,
      hJ 4 ⟨by decide, by decide⟩, mul_one, hz] at h
    exact h
  have hq3 : ∀ y : Lˣ, y ^ 3 = 1 → y ≠ 1 → (y : L) ^ 2 + y + 1 = 0 := by
    intro y h3 h1
    have h3' : (y : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    have h1' : (y : L) ≠ 1 := fun h => h1 (Units.ext h)
    have : ((y : L) - 1) * ((y : L) ^ 2 + y + 1) = 0 := by linear_combination h3'
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1')
  have hz5' : rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) = z := by
    have e0 := hq3 z (hz ▸ hcube _) hz1
    have e5 := hq3 _ (hcube _) hz5
    set y := rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ))
    have : ((y : L) - z) * ((y : L) + z + 1) = 0 := by linear_combination e5 - e0
    rcases mul_eq_zero.1 this with h | h
    · exact Units.ext (sub_eq_zero.1 h)
    · refine absurd (Units.ext ?_) h05
      rw [Units.val_mul, Units.val_one]
      linear_combination (z : L) * h - e0
  have hcJ : ∀ c : Fin Tag.E6.rank, c ≠ 0 → c ≠ 5 → 1 ≤ c.val ∧ c.val ≤ 4 := by decide
  have hchi : ∀ x, rootChar a (v • x) = z ^ (x 0 + x 5) := by
    intro x
    rw [d4t2out_rootChar_smul a v x, Finset.prod_eq_mul (0 : Fin Tag.E6.rank) 5 (by decide)
      (fun c _ hc => by rw [hJ c (hcJ c hc.1 hc.2), one_zpow])
      (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h),
      hz, hz5', zpow_add]
  have key : ∀ s t : Fin Tag.E6.rank, permLattice e6Graph (Pi.single s 1) = Pi.single t 1 →
      (Pi.single s 1 : Fin Tag.E6.rank → ℤ) 0 + (Pi.single s 1 : Fin Tag.E6.rank → ℤ) 5 = 1 →
      (3 : ℤ) ∣ (w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) 5 + 1 := by
    intro s t hst hs1
    have hfr := S.frob.rootChar_eq a hT _ (IsRoot.smul (IsRoot.basis s) v)
    have hρs : S.ρ (v • (Pi.single s 1 : Fin Tag.E6.rank → ℤ)) =
        v • (u • (w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ))) := by
      have h := hθ _ (IsRoot.basis s)
      rw [hst, mul_smul] at h
      rw [← h, smul_inv_smul]
    rw [hρs, hchi, hchi, smul_apply_of_mem_parabolicWeylGroup hu _
      (fun h => absurd h.1 (by decide) : (0 : Fin Tag.E6.rank) ∉ d4Set .E6),
      smul_apply_of_mem_parabolicWeylGroup hu _
      (fun h => absurd h.2 (by decide) : (5 : Fin Tag.E6.rank) ∉ d4Set .E6), hs1,
      zpow_one] at hfr
    have h1 : z ^ ((w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) 0 +
        (w₀ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) 5 + 1) = 1 := by
      rw [zpow_add_one, hfr, ← pow_succ]
      obtain ⟨c, hc⟩ := h3q
      rw [hc, pow_mul, ← hz, hcube, one_pow]
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [orderOf_eq_prime (hz ▸ hcube _) hz1, Nat.cast_ofNat] at h2
  have h50 : permLattice e6Graph (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = Pi.single 0 1 := by
    rw [permLattice_single]
    rfl
  have h00 : permLattice e6Graph (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = Pi.single 5 1 := by
    rw [permLattice_single]
    rfl
  exact ⟨key 5 0 h50 (by decide), key 0 5 h00 (by decide)⟩

end Search

theorem d4t2out_center_eq_bot {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun y => by
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx) y']
  rw [h, Subgroup.mem_bot] at hex
  rw [Subgroup.mem_bot]
  exact e.injective (hex.trans (map_one e).symm)

section Rho


theorem d4t2out_rho_eq {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) :
    ∃ w : WeylGroup .E6, S.D.n = canonicalRep (coxeterSystem .E6) L w ∧
      ∀ γ, IsRoot .E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hq0 : 0 < S.D.q := S.hqpow.1.pos
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  refine ⟨w, hn, fun γ hγ => ?_⟩
  have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
      Fr := by
    ext1 g
    change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
      (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
    rw [hΦ', hn]
  have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
  have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
      rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
    rw [← S.frob.map_rootSubgroup γ hγ, hst]
    exact h2
  exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ)
    (IsRoot.smul (hγ.permLattice e6Graph_cartan) w) h3

end Rho

section Layer


open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
  (exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4)

theorem d4t2out_layer_equiv {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) {a b c : Fin TwistTag.E6.tag.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    Nonempty (↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) = ⊥ := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (List.formPerm [a, b, c] j) 1 : Fin TwistTag.E6.tag.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rw [permLattice_single (List.formPerm [a, b, c])] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  have key : ∀ e, StdTwist n₁ (List.formPerm [a, b, c]) e →
      Nonempty (↥(subsystemGroup TwistTag.E6.tag L (d4Set TwistTag.E6.tag) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(subsystemGroup TwistTag.E6.tag L (d4Set TwistTag.E6.tag) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) = ⊥ := by
    intro e hstd
    obtain ⟨K, _, _, σ, hKc, hσ, ⟨eP⟩⟩ := layer_graph_equiv_of_standard hf hstd hh hlang rfl
    have hqc : (⟨ℓ, f, Fact.out, hf⟩ : TauCeti.PrimePower).card = ℓ ^ f :=
      TauCeti.PrimePower.card_def _
    have hKc' : Nat.card K = (⟨ℓ, f, Fact.out, hf⟩ : TauCeti.PrimePower).card ^ 3 := by
      rw [hqc]
      exact hKc
    have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
      center_graphFixedRootGroup_eq_bot σ.surjective
    refine ⟨?_, d4t2out_center_eq_bot eP hZ⟩
    rcases hstd.he with rfl | rfl
    · obtain ⟨φ⟩ := catEquiv_trialityD4_of_field ⟨ℓ, f, Fact.out, hf⟩
        (TauCeti.LieTypeIndex.valid_trialityD4 _) K hKc' σ fun c => by rw [hσ, pow_one, hqc]
      exact ⟨eP.trans φ.symm⟩
    · have h₁ : ∀ c, σ.symm c = c ^ (ℓ ^ f) := fun c => by
        apply σ.injective
        rw [RingEquiv.apply_symm_apply, hσ, ← pow_mul]
        haveI : Fintype K := Fintype.ofFinite K
        have hcard : ℓ ^ f * (ℓ ^ f) ^ 2 = Fintype.card K := by
          rw [← Nat.card_eq_fintype_card, hKc]
          ring
        rw [hcard, FiniteField.pow_card]
      obtain ⟨ψ⟩ := exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4 K hKc σ σ.symm hσ h₁
      obtain ⟨φ⟩ := catEquiv_trialityD4_of_field ⟨ℓ, f, Fact.out, hf⟩
        (TauCeti.LieTypeIndex.valid_trialityD4 _) K hKc' σ.symm fun c => by rw [hqc]; exact h₁ c
      exact ⟨(eP.trans ψ).trans φ.symm⟩
  rcases hcyc with h1 | h2
  · exact key 1 ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
  · exact key 2 ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩

end Layer

section Main


theorem d4t2out_theta_cycle {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    (h3q : 3 ∣ S.D.q + 1) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hall : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) :
    ∃ (w u w₀ : WeylGroup .E6) (πJ : Equiv.Perm (Fin Tag.E6.rank)),
      S.D.n = canonicalRep (coxeterSystem .E6) L w ∧
      u ∈ parabolicWeylGroup .E6 (d4Set .E6) ∧ v⁻¹ * w * e6WeylTwist v = u * w₀ ∧
      (∀ α ∈ parabolicRoots .E6 (d4Nodes .E6), w₀ • permLattice e6Graph α = permLattice πJ α) ∧
      (πJ = List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∨
        πJ = List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2]) ∧
      ∀ α ∈ parabolicRoots .E6 (d4Nodes .E6), v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
  obtain ⟨w, hn, hρw⟩ := d4t2out_rho_eq S hS
  classical
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
  have hθall : ∀ γ, IsRoot Tag.E6 γ → v⁻¹ • S.ρ (v • γ) = w' • permLattice e6Graph γ := by
    intro γ hγ
    rw [hρw _ ((isRoot_smul_iff v).2 hγ), ← e6WeylTwist_smul v γ, hw', mul_smul, mul_smul]
  have hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α := fun α hα => hθall α hα.1
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have hmemΨ : v • α ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨α, hα, rfl⟩
    have h2 := hρ _ hmemΨ
    rw [hΨ] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    rw [← hβe, inv_smul_smul]
    exact hβ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) w' := by
    intro α hα
    have h1 := hθ (permLattice e6Graph α) (hσpar α hα)
    rw [hσσ] at h1
    rw [← h1]
    exact hθmem _ (hσpar α hα)
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, hπJ, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have hπ1 : πJ ≠ 1 := by
    intro h1
    apply hnin
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have h := hθ' α hα
    rw [h1] at h
    calc S.ρ (v • α) = v • (v⁻¹ • S.ρ (v • α)) := (smul_inv_smul v _).symm
      _ = v • (u • α) := by rw [h]; rfl
      _ = (v * u * v⁻¹) • v • α := by rw [mul_smul, mul_smul, inv_smul_smul]
  have hF := d4t2out_three_dvd S h3q hT hap i v hΨ hall hu
    fun γ hγ => by rw [hθall γ hγ, hw₀]
  have hcyc : πJ = List.formPerm [e6Idx 1, e6Idx 2, e6Idx 4] ∨
      πJ = List.formPerm [e6Idx 1, e6Idx 4, e6Idx 2] := by
    rcases hπ' with h | h | h | h | h | h
    · exact (d4t2out_no_weyl (by rw [h]; simp [d4t2outPerms]) hw₀π hF.1 hF.2).elim
    · left
      rw [hπJ, h]
      decide
    · right
      rw [hπJ, h]
      decide
    · exact (hπ1 (by rw [hπJ, h, Equiv.swap_mul_self])).elim
    · exact (d4t2out_no_weyl (by rw [h]; simp [d4t2outPerms]) hw₀π hF.1 hF.2).elim
    · exact (d4t2out_no_weyl (by rw [h]; simp [d4t2outPerms]) hw₀π hF.1 hF.2).elim
  exact ⟨w, u, w₀, πJ, hn, hu, hw₀, hlin, hcyc, hθ'⟩

theorem d4t2out_rootSpan_model_quasisimple {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) (hq : S.D.q = ℓ ^ f)
    (h3q : 3 ∣ ℓ ^ f + 1) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hall : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) :
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      Nonempty (↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) =
        ⊥ := by
  obtain ⟨w, u, w₀, πJ, hn, hu, hw₀, hlin, hcyc, -⟩ :=
    d4t2out_theta_cycle S hS (by rw [hq]; exact h3q) hT hap i v hΨ hall hρ hnin
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  classical
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v)
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hnδM := canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn'M : nv⁻¹ * nw * nδ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hπn' : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ =
      v⁻¹ * w * e6WeylTwist v := by
    have e : (⟨nv⁻¹ * nw * nδ, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nδ, hnδM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w),
      weylQuotientHom_eq (mapsRootLines_canonicalRep (e6WeylTwist v))]
  have hnPv : nv⁻¹ * (nw * e6Diagram L) * nv = (nv⁻¹ * nw * nδ) * e6Diagram L := by
    have h := e6Diagram_conj_canonicalRep Fr v
    calc nv⁻¹ * (nw * e6Diagram L) * nv =
        nv⁻¹ * nw * (e6Diagram L * nv * (e6Diagram L)⁻¹) * e6Diagram L := by group
      _ = (nv⁻¹ * nw * nδ) * e6Diagram L := by rw [h]
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ • permLattice e6Graph α =
        u • permLattice πJ α := by
    intro α hα
    rw [hπn', hw₀, mul_smul, hlin α hα]
  have hlayer : Nonempty (↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints ((nv⁻¹ * nw * nδ) * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints ((nv⁻¹ * nw * nδ) * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) = ⊥ ∧
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints ((nv⁻¹ * nw * nδ) * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
    rcases hcyc with h | h
    · rw [h] at hact
      obtain ⟨he, hz⟩ := d4t2out_layer_equiv hf h12 h24 h14 hv1 hv2 hv4 hn'M hu hact
      exact ⟨he, hz, (twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn'M hu hact).2⟩
    · rw [h] at hact
      obtain ⟨he, hz⟩ := d4t2out_layer_equiv hf h14 h24.symm h12 hv1 hv4 hv2 hn'M hu hact
      exact ⟨he, hz,
        (twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn'M hu hact).2⟩
  have hmodel : rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (nw * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hΨ]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ', hFr'] at hxF'
      change (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
        (nw * e6Diagram L)⁻¹ = x
      calc (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (nw * e6Diagram L)⁻¹ = nw * (e6Diagram L *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (e6Diagram L)⁻¹) * nw⁻¹ := by
            group
        _ = x := hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      have hxF' : (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
          (nw * e6Diagram L)⁻¹ = x := hxF
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ', hFr']
      calc nw * (e6Diagram L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (e6Diagram L)⁻¹) * nw⁻¹ = (nw * e6Diagram L) *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (nw * e6Diagram L)⁻¹ := by
            group
        _ = x := hxF'
  have hqs : CFSG.IsQuasisimple
        ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      Nonempty (↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) =
        ⊥ := by
    rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v (nw * e6Diagram L) hroots, ← hnv, hnPv]
    obtain ⟨⟨eQ⟩, hZQ, hqsQ⟩ := hlayer
    have e := (rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      twistedFixedPoints ((nv⁻¹ * nw * nδ) * e6Diagram L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).equivMapOfInjective
          (MulAut.conj nv).toMonoidHom (MulAut.conj nv).injective
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqsQ, ⟨e.symm.trans eQ⟩,
      d4t2out_center_eq_bot e.symm hZQ⟩
  exact hqs

theorem d4t2out_rationalComponent_equiv {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) (hq : S.D.q = ℓ ^ f)
    (h3q : 3 ∣ ℓ ^ f + 1) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hall : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) :
    Nonempty (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 ⟨ℓ, f, Fact.out, hf⟩,
          TauCeti.LieTypeIndex.valid_trialityD4 _⟩).Group) ∧
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ := by
  have hqs := d4t2out_rootSpan_model_quasisimple S hS hf hq h3q hT hap i v hΨ hall hρ hnin
  rw [rationalComponent_eq_of_layer S i hρ hqs.1]
  exact hqs.2

theorem twE6ComponentType_rational_of_outer_d4
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f) (hl3 : l ≠ 3)
    (h3 : ((3 : ℕ) : L) ≠ 0) (h3q : 3 ∣ l ^ f + 1)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) :
    TwE6ComponentType (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP L l := by
    rw [CharP.charP_iff_prime_eq_zero hl]
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff hf.ne').1 h
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
      (rootDiagUnitHom Tag.E6 L).map_pow a 3
    have h2 : a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, hap j, Pi.one_apply]
    rw [← h1, h2, CFSG.LieType.Chevalley.rootDiagUnit_one]
  obtain ⟨v, hv, -⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3 facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1
  have hle : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) := fun γ hγ => hγ.1
  have hsub : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i :=
    (Set.eq_of_subset_of_ncard_le hle (hall.trans hc.symm).le hfin).ge
  obtain ⟨⟨e⟩, hZ⟩ := d4t2out_rationalComponent_equiv S hS hf hq h3q hT hap i v hv hsub hρ hnin
  unfold TwE6ComponentType
  refine Or.inl ⟨?_, ⟨.trialityD4 ⟨l, f, hl, hf⟩, TauCeti.LieTypeIndex.valid_trialityD4 _⟩,
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e), ?_, ?_⟩
  · rw [hZ, Subgroup.card_bot]
    decide
  · simp only [TauCeti.LieTypeIndex.characteristic_trialityD4]
    exact fun h => hl3 h.symm
  · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]

end Main

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
