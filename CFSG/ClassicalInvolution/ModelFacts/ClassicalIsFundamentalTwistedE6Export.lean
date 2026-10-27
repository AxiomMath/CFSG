module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Chain

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

section Commutator

variable {G : Type*} [Group G] {ι : Type*}

theorem commutatorElement_mem_iSup_of_commute (H C : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hCH : ∀ i, C i ≤ H i) (hC : ∀ i, ⁅H i, H i⁆ ≤ C i)
    (hnorm : ∀ i, ∀ g ∈ H i, ∀ c ∈ C i, g * c * g⁻¹ ∈ C i) {x y : G} (hx : x ∈ ⨆ i, H i)
    (hy : y ∈ ⨆ i, H i) : ⁅x, y⁆ ∈ ⨆ i, C i := by
  set N : Subgroup G := ⨆ i, C i with hN
  have hHN : ∀ j, ∀ g ∈ H j, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro j g hg n hn
    induction hn using Subgroup.iSup_induction' with
    | hp i c hc =>
      by_cases hij : i = j
      · subst hij
        exact Subgroup.mem_iSup_of_mem i (hnorm i g hg c hc)
      · have h1 : g * c = c * g := (hcomm (Ne.symm hij) g c hg (hCH i hc)).eq
        have : g * c * g⁻¹ = c := by rw [h1]; group
        rw [this]
        exact Subgroup.mem_iSup_of_mem i hc
    | h1 => simp
    | hmul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
  have hTN : ∀ g ∈ ⨆ i, H i, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp j a ha => exact fun n hn => hHN j a ha n hn
    | h1 =>
      intro n hn
      simpa using hn
    | hmul a b _ _ ha hb =>
      intro n hn
      have e : a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact ha _ (hb n hn)
  have hgen : ∀ i j, ∀ a ∈ H i, ∀ b ∈ H j, ⁅a, b⁆ ∈ N := by
    intro i j a ha b hb
    by_cases hij : i = j
    · subst hij
      exact Subgroup.mem_iSup_of_mem i (hC i (Subgroup.commutator_mem_commutator ha hb))
    · have h1 : a * b = b * a := (hcomm hij a b ha hb).eq
      have : ⁅a, b⁆ = 1 := by
        rw [commutatorElement_def, h1]
        group
      rw [this]
      exact one_mem _
  have hstep : ∀ i, ∀ a ∈ H i, ∀ b ∈ ⨆ j, H j, ⁅a, b⁆ ∈ N := by
    intro i a ha b hb
    induction hb using Subgroup.iSup_induction' with
    | hp j c hc => exact hgen i j a ha c hc
    | h1 => simp
    | hmul c d hc hd hcn hdn =>
      have e : ⁅a, c * d⁆ = ⁅a, c⁆ * (c * ⁅a, d⁆ * c⁻¹) := by
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      rw [e]
      exact mul_mem hcn (hTN c hc _ hdn)
  induction hx using Subgroup.iSup_induction' with
  | hp i a ha => exact hstep i a ha y hy
  | h1 => simp
  | hmul a b ha hb han hbn =>
    have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hTN a ha _ hbn) han

end Commutator

section Perfect

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem le_kernelFixedGroup_of_isPerfect {P : Subgroup (adjointGroup τ k)}
    (hP : P ≤ D.totalFixedGroup) (hperf : Group.IsPerfect P) : P ≤ D.kernelFixedGroup := by
  have h : ⁅P, P⁆ ≤ D.kernelFixedGroup := Subgroup.commutator_le.2 fun x hx y hy =>
    D.commutatorElement_mem_kernelFixedGroup (hP hx) (hP hy)
  rwa [Subgroup.isPerfect_iff.1 hperf] at h

theorem le_orbitFixedJoin_of_isPerfect {P : Subgroup (adjointGroup τ k)}
    (hP : P ≤ D.totalFixedGroup) (hperf : Group.IsPerfect P) : P ≤ D.orbitFixedJoin := by
  have h1 := le_kernelFixedGroup_of_isPerfect D hP hperf
  have h : ⁅P, P⁆ ≤ D.orbitFixedJoin := Subgroup.commutator_le.2 fun x hx y hy =>
    D.commutatorElement_mem_orbitFixedJoin (h1 hx) (h1 hy)
  rwa [Subgroup.isPerfect_iff.1 hperf] at h

theorem le_iSup_orbitGroupC_of_isPerfect {P : Subgroup (adjointGroup τ k)}
    (hP : P ≤ D.totalFixedGroup) (hperf : Group.IsPerfect P) :
    P ≤ ⨆ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroupC := by
  have h1 := le_orbitFixedJoin_of_isPerfect D hP hperf
  have h : ⁅P, P⁆ ≤ ⨆ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroupC :=
    Subgroup.commutator_le.2 fun x hx y hy =>
      commutatorElement_mem_iSup_of_commute
        (fun J' : Set.range D.classOrbit => (D.withOrbit J').fixedGroup)
        (fun J' => (D.withOrbit J').orbitGroupC)
        (fun J₁ J₂ hne x y hx hy => Subtype.ext
          (D.commute_of_ne hne ((D.withOrbit J₁).mem_fixedGroup.1 hx).1
            ((D.withOrbit J₂).mem_fixedGroup.1 hy).1).eq)
        (fun J' => (D.withOrbit J').orbitGroupC_le_fixedGroup)
        (fun J' => (D.withOrbit J').commutator_fixedGroup_le)
        (fun J' g hg c hc => by
          have := (D.withOrbit J').orbitGroupC_normal.conj_mem
            ⟨c, (D.withOrbit J').orbitGroupC_le_fixedGroup hc⟩ (Subgroup.mem_subgroupOf.2 hc)
            ⟨g, hg⟩
          exact Subgroup.mem_subgroupOf.1 this) (h1 hx) (h1 hy)
  rwa [Subgroup.isPerfect_iff.1 hperf] at h

end Perfect

section Datum

variable (p : ℕ) [Fact p.Prime] (t : TwistTag) {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_datum_conj_centralizer (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    (reps : List (SignRep t.tag)) {r₀ : ℕ}
    (hB : ∀ i j, t.tag.symmetrizedCartan (t.perm i) (t.perm j) = t.tag.symmetrizedCartan i j)
    (hfix : ∀ r ∈ reps, permChar t.perm (signMaskChar t.tag r.mask) = signMaskChar t.tag r.mask)
    (hrep : ∀ χ, permChar t.perm χ ∈ charOrbit χ →
      ∃ r ∈ reps, χ ∈ charOrbit (signMaskChar t.tag r.mask))
    (hunt : ∀ r ∈ reps, UntwistAt (frobTwistGL t.tag k p e (diagramMap t k))
      (signCharTuple (signMaskChar t.tag r.mask)))
    (hθ : ∀ r ∈ reps, ThetaProperties t.perm r₀ (signMaskChar t.tag r.mask) (wordElt t.tag []))
    (hpin : ∀ r ∈ reps, IsTwistPinningNormalization t.tag k p e (signMaskChar t.tag r.mask)
      (thetaMap (wordElt t.tag []) t.perm) (wordWeylMatrix t.tag k [] * diagramMap t k))
    (hne : ∀ r ∈ reps, (kernelRoots (signMaskChar t.tag r.mask)).Nonempty)
    (hZ : ∀ r ∈ reps, ∀ y ∈ toralCentralizer t.tag k (signCharTuple (signMaskChar t.tag r.mask)),
      frobTwistGL t.tag k p e (diagramMap t k) y = y →
        y ∈ toralRootGroup t.tag k (signCharTuple (signMaskChar t.tag r.mask)))
    {x : ModGL t.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k)))
    (hx2 : x ^ 2 = 1) :
    ∃ r ∈ reps, ∃ (D : OrthogonalSemilinearFixedRootDatum t.tag p k) (w h : ModGL t.tag k),
      w ∈ adjointGroup t.tag k ∧ h ∈ torusGroup t.tag k ∧
      w * x * w⁻¹ = rootDiagUnit t.tag (signCharTuple (signMaskChar t.tag r.mask)) ∧
      D.χ = signMaskChar t.tag r.mask ∧ D.e = e ∧
      (∀ γ, D.θ (toReal γ) = toReal (thetaMap (wordElt t.tag []) t.perm γ)) ∧
      (∀ y : adjointGroup t.tag k, (D.F y : ModGL t.tag k) =
        frobTwistGL t.tag k p e (h * diagramMap t k) y) ∧
      (fixedPointsIn (adjointGroup t.tag k) (frobTwistGL t.tag k p e (diagramMap t k)) ⊓
        Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup t.tag k).subtype := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨r, hr, g₁, hg₁G, hFg₁, hg₁x, -⟩ :=
    exists_twisted_toral_reduction p t hp he reps hfix hrep hunt hx hx2
  set χ := signMaskChar t.tag r.mask with hχ
  set F := frobTwistGL t.tag k p e (diagramMap t k) with hF
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signCharTuple hk2 χ
  set M := torusGroup t.tag k ⊔ rootSpan t.tag k (kernelRoots χ) with hM_def
  have hMeq : toralRootGroup t.tag k a = M := by rw [toralRootGroup, hker]
  have hMG : M ≤ adjointGroup t.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hMZ : ∀ y ∈ M, rootDiagUnit t.tag a * y * (rootDiagUnit t.tag a)⁻¹ = y := fun y hy =>
    (mem_toralCentralizer.1 (toralRootGroup_le a (hMeq ▸ hy))).2
  have hD : (adjointGroup t.tag k).map (MulAut.conj (diagramMap t k)).toMonoidHom =
      adjointGroup t.tag k := map_conj_diagramMap t k (Or.inl rfl)
  have hτ : t.tag = .D4 ∨ t.tag = .E6 ∨ t.tag = .E7 := by cases t <;> simp [TwistTag.tag]
  obtain ⟨D, h, hhT, hDχ, hDe, hDθ, hDF, hX⟩ := exists_pinned_datum p hp hk he hτ (ρ := t.perm)
    t.cartan_perm hB (hθ r hr) (Q₀ := wordWeylMatrix t.tag k [] * diagramMap t k)
    (fun γ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX t [] hγ)
    (mul_mem (wordWeylMatrix_mem_normalizer []) (diagramMap_mem_normalizer t))
    (map_conj_wordWeylMatrix_mul [] hD) (hpin r hr) (hne r hr)
  have hQ₀ : wordWeylMatrix t.tag k [] * diagramMap t k = diagramMap t k := by
    rw [wordWeylMatrix_nil, one_mul]
  rw [hQ₀] at hDF hX
  obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  obtain ⟨s, hs⟩ := exists_rootDiagUnit_frob_eq p t he a₀⁻¹
  set u := rootDiagUnit t.tag s with hu_def
  have hFu : F u = h⁻¹ * u := by
    rw [hs, ← rootDiagUnit_inv, ← ha₀]
  have huM : u ∈ M := Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s)
  have hFh : ∀ y, frobTwistGL t.tag k p e (h * diagramMap t k) y = h * F y * h⁻¹ :=
    fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M F).map (MulAut.conj u).toMonoidHom =
      fixedPointsIn M (frobTwistGL t.tag k p e (h * diagramMap t k)) :=
    map_conj_fixedPointsIn_eq M F _ huM hFh hFu
  have hud : u * rootDiagUnit t.tag a * u⁻¹ = rootDiagUnit t.tag a := by
    have h1 := hMZ u huM
    calc u * rootDiagUnit t.tag a * u⁻¹ =
        (rootDiagUnit t.tag a * u * (rootDiagUnit t.tag a)⁻¹) * rootDiagUnit t.tag a * u⁻¹ := by
          rw [h1]
      _ = rootDiagUnit t.tag a := by group
  refine ⟨r, hr, D, u * g₁, h, mul_mem (hMG huM) hg₁G, hhT, ?_, hDχ, hDe, hDθ,
    fun y => hDF y, ?_⟩
  · calc u * g₁ * x * (u * g₁)⁻¹ = u * (g₁ * x * g₁⁻¹) * u⁻¹ := by group
      _ = rootDiagUnit t.tag a := by rw [hg₁x, hud]
  · ext y
    constructor
    · rintro ⟨z, ⟨hzR, hzx⟩, rfl⟩
      obtain ⟨hzG, hzF⟩ := mem_fixedPointsIn.1 hzR
      have hzx' : z * x = x * z :=
        Subgroup.mem_centralizer_singleton_iff.1 (hzx : z ∈ Subgroup.centralizer {x})
      have hy₁G : g₁ * z * g₁⁻¹ ∈ adjointGroup t.tag k := mul_mem (mul_mem hg₁G hzG) (inv_mem hg₁G)
      have hy₁F : F (g₁ * z * g₁⁻¹) = g₁ * z * g₁⁻¹ := by
        rw [map_mul, map_mul, map_inv, hFg₁, hzF]
      have hy₁d : rootDiagUnit t.tag a * (g₁ * z * g₁⁻¹) * (rootDiagUnit t.tag a)⁻¹ =
          g₁ * z * g₁⁻¹ := by
        rw [← hg₁x]
        calc g₁ * x * g₁⁻¹ * (g₁ * z * g₁⁻¹) * (g₁ * x * g₁⁻¹)⁻¹ =
            g₁ * (x * z * x⁻¹) * g₁⁻¹ := by group
          _ = g₁ * z * g₁⁻¹ := by rw [← hzx']; group
      have hy₁M : g₁ * z * g₁⁻¹ ∈ M := hMeq ▸ hZ r hr _ (mem_toralCentralizer.2 ⟨hy₁G, hy₁d⟩) hy₁F
      have hmem : u * (g₁ * z * g₁⁻¹) * u⁻¹ ∈
          fixedPointsIn M (frobTwistGL t.tag k p e (h * diagramMap t k)) := by
        rw [← hconj]
        exact ⟨_, mem_fixedPointsIn.2 ⟨hy₁M, hy₁F⟩, rfl⟩
      rw [← hX] at hmem
      have e : (MulAut.conj (u * g₁)).toMonoidHom z = u * (g₁ * z * g₁⁻¹) * u⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
        group
      rw [e]
      exact hmem
    · intro hy
      rw [hX] at hy
      rw [← hconj] at hy
      obtain ⟨y₁, hy₁, rfl⟩ := hy
      obtain ⟨hy₁M, hy₁F⟩ := mem_fixedPointsIn.1 hy₁
      have hy₁G := hMG hy₁M
      have hz : g₁⁻¹ * y₁ * g₁ ∈ fixedPointsIn (adjointGroup t.tag k) F ⊓
          Subgroup.centralizer {x} := by
        refine ⟨mem_fixedPointsIn.2 ⟨mul_mem (mul_mem (inv_mem hg₁G) hy₁G) hg₁G, ?_⟩, ?_⟩
        · rw [map_mul, map_mul, map_inv, hFg₁, hy₁F]
        · show g₁⁻¹ * y₁ * g₁ ∈ Subgroup.centralizer ({x} : Set (ModGL t.tag k))
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h1 := hMZ y₁ hy₁M
          have hx' : x = g₁⁻¹ * rootDiagUnit t.tag a * g₁ := by
            rw [← hg₁x]
            group
          symm
          calc x * (g₁⁻¹ * y₁ * g₁) = g₁⁻¹ * (rootDiagUnit t.tag a * y₁) * g₁ := by
                rw [hx']
                group
            _ = g₁⁻¹ * (y₁ * rootDiagUnit t.tag a) * g₁ := by
                have h2 : rootDiagUnit t.tag a * y₁ = y₁ * rootDiagUnit t.tag a := by
                  calc rootDiagUnit t.tag a * y₁ =
                      (rootDiagUnit t.tag a * y₁ * (rootDiagUnit t.tag a)⁻¹) *
                        rootDiagUnit t.tag a := by group
                    _ = y₁ * rootDiagUnit t.tag a := by rw [h1]
                rw [h2]
            _ = (g₁⁻¹ * y₁ * g₁) * x := by
                rw [hx']
                group
      refine ⟨_, hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
      group

end Datum

section E6

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem e6_kernelRoots_nonempty {r : SignRep .E6} (hr : r ∈ e6SignDiagramReps) :
    (kernelRoots (signMaskChar Tag.E6 r.mask)).Nonempty := by
  simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h : ∃ m, (m = 0 ∨ m = 20 ∨ m = 2) ∧ r.mask = m := by
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, Or.inl rfl, rfl⟩
    · exact ⟨20, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨2, Or.inr (Or.inr rfl), rfl⟩
  obtain ⟨m, hm, hrm⟩ := h
  rw [hrm]
  have h1 : (List.range e6Certificate.roots.length).any (inKernel e6Certificate m) = true := by
    rcases hm with rfl | rfl | rfl <;> decide +kernel
  simp only [List.any_eq_true, List.mem_range] at h1
  obtain ⟨j, hj, hker⟩ := h1
  exact ⟨_, (mem_kernelRoots_iff e6Certificate_check).2 ⟨j, hj, rfl, hker⟩⟩

theorem e6_toralRootGroup_eq {k : Type} [Field k] [IsAlgClosed k] (hk2 : ringChar k ≠ 2)
    {a : Fin TwistTag.E6.tag.rank → kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) :
    toralRootGroup TwistTag.E6.tag k a = toralCentralizer TwistTag.E6.tag k a :=
  (exceptional_toral_centralizer_identity_component TwistTag.E6.tag k hk2 a ha).2.2.2.2.1
    (Or.inr (Or.inr (Or.inl rfl)))

theorem e6_exists_datum_conj_centralizer (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)))
    (hx2 : x ^ 2 = 1) :
    ∃ r ∈ e6SignDiagramReps, ∃ (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)
      (w h : ModGL TwistTag.E6.tag k),
      w ∈ adjointGroup TwistTag.E6.tag k ∧ h ∈ torusGroup TwistTag.E6.tag k ∧
      w * x * w⁻¹ = rootDiagUnit TwistTag.E6.tag
        (signCharTuple (signMaskChar TwistTag.E6.tag r.mask)) ∧
      D.χ = signMaskChar TwistTag.E6.tag r.mask ∧ D.e = e ∧
      (∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ)) ∧
      (∀ y : adjointGroup TwistTag.E6.tag k, (D.F y : ModGL TwistTag.E6.tag k) =
        frobTwistGL TwistTag.E6.tag k p e (h * diagramMap TwistTag.E6 k) y) ∧
      (fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) ⊓
        Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype := by
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  obtain ⟨r, hr, D, w, h, hw, hh, hwx, hDχ, hDe, hDθ, hDF, hcent⟩ :=
    exists_datum_conj_centralizer p TwistTag.E6 hp hk he e6SignDiagramReps (r₀ := 2)
      symmetrizedCartan_perm_E6 h6.permChar_eq h6.exists_rep
      (fun r _ => untwistAt_of_eq _ _ (e6_toralRootGroup_eq hk2 (signCharTuple_sign _)))
      (fun r hr => h6.theta r hr [] (nil_mem_omegaWords_e6 hr))
      (fun r hr => n6 r hr [] (nil_mem_omegaWords_e6 hr))
      (fun r hr => e6_kernelRoots_nonempty hr)
      (fun r _ y hy _ => (e6_toralRootGroup_eq hk2 (signCharTuple_sign _)).symm ▸ hy) hx hx2
  refine ⟨r, hr, D, w, h, hw, hh, hwx, hDχ, hDe, fun γ => ?_, hDF, hcent⟩
  have := hDθ γ
  rwa [wordElt_nil, thetaMap_one] at this

end E6

end CFSG.ClassicalInvolution.ModelFacts
