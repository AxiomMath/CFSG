module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidPolyCubic
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidPinnedCubic
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobRoot

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

section Poly

@[expose] noncomputable def zmodIndexList (s : ℕ) [NeZero s] : List ℕ :=
  (Finset.univ : Finset (ZMod s)).toList.map ZMod.val

theorem zmodIndexList_nodup (s : ℕ) [NeZero s] : (zmodIndexList s).Nodup :=
  List.Nodup.map (ZMod.val_injective s) (Finset.nodup_toList _)

theorem zero_mem_zmodIndexList (s : ℕ) [NeZero s] : 0 ∈ zmodIndexList s :=
  List.mem_map.2 ⟨0, Finset.mem_toList.2 (Finset.mem_univ _), ZMod.val_zero⟩

theorem lt_of_mem_zmodIndexList {s : ℕ} [NeZero s] {k : ℕ} (hk : k ∈ zmodIndexList s) : k < s := by
  obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hk
  exact ZMod.val_lt κ

variable {L A : Type*} [Field L] [Ring A] [Algebra L A]

theorem twisted_norm_identity (ψ : L →+* L) (q : ℕ) {c : ℕ} (hψ : ∀ x : L, ψ x = x ^ c)
    (ks : List ℕ) (aN bN dN aN' bN' dN' : ℕ → A) (z' : Aˣ) (t : L)
    (h : (z' : A) * (ks.map fun k => 1 + ψ (t ^ q ^ k) • aN' k + ψ (t ^ q ^ k) ^ 2 • bN' k +
          ψ (t ^ q ^ k) ^ 3 • dN' k).prod * (↑z'⁻¹ : A) =
      (ks.map fun k => 1 + (t ^ q ^ k) • aN k + (t ^ q ^ k) ^ 2 • bN k +
          (t ^ q ^ k) ^ 3 • dN k).prod) :
    (z' : A) * evAt (t ^ c) (prodList3 q aN' bN' dN' ks) * (↑z'⁻¹ : A) =
      evAt t (prodList3 q aN bN dN ks) := by
  have e : ∀ k : ℕ, (t ^ c) ^ q ^ k = ψ (t ^ q ^ k) := fun k => by
    rw [hψ, pow_right_comm]
  rw [evAt_prodList3, evAt_prodList3]
  simp only [e]
  exact h

end Poly

section Cert


section Factor

variable {τ : Tag} {L : Type} [Field L]

theorem conj_map_pinnedX_expand3 (ψ : L →+* L) (g : ModGL τ L) {μ : L} (hμ : μ ≠ 0)
    (α : Fin τ.rank → ℤ) :
    ∃ a b d : Module.End L (RootModule τ L), a ≠ 0 ∧ ∀ c : L,
      ((Units.map (entrywiseHom ψ) (g * pinnedX τ L α (μ * c) * g⁻¹) : ModGL τ L) :
        Module.End L (RootModule τ L)) = 1 + (ψ c) • a + (ψ c) ^ 2 • b + (ψ c) ^ 3 • d := by
  obtain ⟨A, B, C, hA, hABC⟩ := pinnedX_expand_cubic (τ := τ) (L := L) α
  set g' : ModGL τ L := Units.map (entrywiseHom ψ) g with hg'
  have hψμ : ψ μ ≠ 0 := fun h => hμ ((map_eq_zero ψ).1 h)
  refine ⟨ψ μ • ((g' : Module.End L (RootModule τ L)) * A *
      ((g'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))),
    (ψ μ) ^ 2 • ((g' : Module.End L (RootModule τ L)) * B *
      ((g'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))),
    (ψ μ) ^ 3 • ((g' : Module.End L (RootModule τ L)) * C *
      ((g'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))), ?_, fun c => ?_⟩
  · intro h0
    rcases smul_eq_zero.1 h0 with h | h
    · exact hψμ h
    · apply hA
      have := congrArg (fun m => ((g'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) * m *
        (g' : Module.End L (RootModule τ L))) h
      simpa [mul_assoc] using this
  · rw [map_mul, map_mul, map_inv, entrywise_pinnedX_units, ← hg']
    rw [Units.val_mul, Units.val_mul, hABC, map_mul, unit_conj_cubic]
    module

end Factor

section Data

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem exists_factor_data3 (ψ : L →+* L) (zu : ModGL τ L) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (k : ℕ) :
    ∃ a b d a' b' d' : Module.End L (RootModule τ L), a ≠ 0 ∧ a' ≠ 0 ∧
      (∀ t : L, ((iterHom S.D.step k (zu * pinnedX τ L γ t * zu⁻¹) : ModGL τ L) :
        Module.End L (RootModule τ L)) = 1 + (t ^ (S.D.q ^ k)) • a +
          (t ^ (S.D.q ^ k)) ^ 2 • b + (t ^ (S.D.q ^ k)) ^ 3 • d) ∧
      (∀ t : L, ((Units.map (entrywiseHom ψ) (iterHom S.D.step k
        (zu * pinnedX τ L γ t * zu⁻¹)) : ModGL τ L) : Module.End L (RootModule τ L)) =
          1 + (ψ (t ^ (S.D.q ^ k))) • a' + (ψ (t ^ (S.D.q ^ k))) ^ 2 • b' +
            (ψ (t ^ (S.D.q ^ k))) ^ 3 • d') := by
  obtain ⟨μ, hμ, hμe⟩ := iter_step_pinnedX S k hγ
  have hit : ∀ t : L, iterHom S.D.step k (zu * pinnedX τ L γ t * zu⁻¹) =
      iterHom S.D.step k zu * pinnedX τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] γ)
        (μ * t ^ (S.D.q ^ k)) * (iterHom S.D.step k zu)⁻¹ := by
    intro t
    rw [map_mul, map_mul, map_inv, iterHom_eq_iterate, iterHom_eq_iterate, hμe]
  obtain ⟨a, b, d, ha, hab⟩ := conj_map_pinnedX_expand3 (RingHom.id L)
    (iterHom S.D.step k zu) hμ ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] γ)
  obtain ⟨a', b', d', ha', hab'⟩ := conj_map_pinnedX_expand3 ψ (iterHom S.D.step k zu) hμ
    ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] γ)
  refine ⟨a, b, d, a', b', d', ha, ha', fun t => ?_, fun t => ?_⟩
  · rw [hit]
    have h1 := hab (t ^ (S.D.q ^ k))
    have e : ∀ x : ModGL τ L, Units.map (entrywiseHom (RingHom.id L)) x = x :=
      fun x => Units.ext (entrywise_id _)
    rw [e] at h1
    simpa using h1
  · rw [hit, hab' (t ^ (S.D.q ^ k))]

end Data

section Norm

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem coe_map_norm_eq_prod {A : Type*} [Monoid A] {F : Aˣ →* Aˣ} {s : ℕ} [NeZero s]
    (P : CycFamily F s) (y : P.S 0) (φ : Aˣ →* Aˣ) (E : ℕ → A)
    (hE : ∀ k : ℕ, ((φ (iterHom F k (y : Aˣ)) : Aˣ) : A) = E k) :
    ((φ (P.norm y) : Aˣ) : A) = ((zmodIndexList s).map E).prod := by
  rw [norm_eq_list_prod P y, map_list_prod, List.map_map, units_coe_list_prod]
  unfold zmodIndexList
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  exact hE k.val

theorem outer_hmain {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {θ : Fin τ.rank → ℤ} {zu : ModGL τ L}
    (hy : ∀ t : L, zu * pinnedX τ L θ t * zu⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).S 0)
    (ψ : L →+* L) {q c : ℕ} (hψ : ∀ x : L, ψ x = x ^ c)
    (aN bN dN aN' bN' dN' : ℕ → Module.End L (RootModule τ L))
    (hE1 : ∀ (k : ℕ) (t : L), ((iterHom S.D.step k (zu * pinnedX τ L θ t * zu⁻¹) : ModGL τ L) :
      Module.End L (RootModule τ L)) = 1 + (t ^ q ^ k) • aN k + (t ^ q ^ k) ^ 2 • bN k +
        (t ^ q ^ k) ^ 3 • dN k)
    (hE2 : ∀ (k : ℕ) (t : L), ((Units.map (entrywiseHom ψ) (iterHom S.D.step k
      (zu * pinnedX τ L θ t * zu⁻¹)) : ModGL τ L) : Module.End L (RootModule τ L)) =
        1 + ψ (t ^ q ^ k) • aN' k + ψ (t ^ q ^ k) ^ 2 • bN' k + ψ (t ^ q ^ k) ^ 3 • dN' k)
    (z' : ModGL τ L) (t : L)
    (hf : z' * Units.map (entrywiseHom ψ) ((outerOrbitFamily S hT i hs hmin).norm ⟨_, hy t⟩) *
      z'⁻¹ = (outerOrbitFamily S hT i hs hmin).norm ⟨_, hy t⟩) :
    ((z' : ModGL τ L) : Module.End L (RootModule τ L)) *
        evAt (t ^ c) (prodList3 q aN' bN' dN' (zmodIndexList s)) *
        ((z'⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) =
      evAt t (prodList3 q aN bN dN (zmodIndexList s)) := by
  have hn1 := coe_map_norm_eq_prod (outerOrbitFamily S hT i hs hmin) ⟨_, hy t⟩ (MonoidHom.id _)
    (fun k => 1 + (t ^ q ^ k) • aN k + (t ^ q ^ k) ^ 2 • bN k + (t ^ q ^ k) ^ 3 • dN k)
    fun k => hE1 k t
  have hn2 := coe_map_norm_eq_prod (outerOrbitFamily S hT i hs hmin) ⟨_, hy t⟩
    (Units.map (entrywiseHom ψ))
    (fun k => 1 + ψ (t ^ q ^ k) • aN' k + ψ (t ^ q ^ k) ^ 2 • bN' k + ψ (t ^ q ^ k) ^ 3 • dN' k)
    fun k => hE2 k t
  have hfA := congrArg (fun m : ModGL τ L => (m : Module.End L (RootModule τ L))) hf
  simp only [Units.val_mul] at hfA
  rw [hn2] at hfA
  simp only [MonoidHom.id_apply] at hn1
  rw [hn1] at hfA
  exact twisted_norm_identity ψ q hψ (zmodIndexList s) aN bN dN aN' bN' dN' z' t hfA

theorem outer_false_of_norm_fixed_cubic {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {θ : Fin τ.rank → ℤ} (hθr : IsRoot τ θ) (zu : ModGL τ L)
    (hy : ∀ t : L, zu * pinnedX τ L θ t * zu⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).S 0)
    {r f j : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f) (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ (r ^ (f * s)))
    (hrt : ∀ t : L, σ t = t → (outerOrbitFamily S hT i hs hmin).norm ⟨_, hy t⟩ ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hq5 : 5 ≤ r ^ f) (hc3 : r ^ j ≠ 3) (hc2 : r ^ j = 2 → 7 ≤ r ^ f) (hj0 : 0 < j)
    (hjf : j < f) (z' : ModGL τ L)
    (hfix : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z'⁻¹ = x) : False := by
  classical
  have hs0 : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := (expChar_prime_iff L hr).1 inferInstance
  have hfs : 0 < f * s := Nat.mul_pos (by omega) hs0
  obtain ⟨hfinK, hKcard⟩ := outer_fixSubfield_card (L := L) hfs σ hσ
  let : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have hKcard' : Fintype.card (fixSubfield σ) = (r ^ f) ^ s := by
    rw [← Nat.card_eq_fintype_card, hKcard, pow_mul]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : L →+* L, ψ = iterateFrobenius L r j := ⟨_, rfl⟩
  rw [← hψ] at hfix
  have hψpow : ∀ x : L, ψ x = x ^ (r ^ j) := fun x => by rw [hψ, iterateFrobenius_def]
  choose aN bN dN aN' bN' dN' haN haN' hE1 hE2 using
    fun k : ℕ => exists_factor_data3 S ψ zu hθr k
  refine no_twisted_conj3 (fixSubfield σ).subtype hr hj0 hjf hs0 hKcard' hq5 hc3 hc2
    (zmodIndexList s) (zmodIndexList_nodup s) (zero_mem_zmodIndexList s)
    (fun k hk => lt_of_mem_zmodIndexList hk) aN bN dN aN' bN' dN' (haN 0) (haN' 0) z' fun t => ?_
  exact outer_hmain S hT i hs hmin hy ψ hψpow aN bN dN aN' bN' dN'
    (fun k t => by rw [← hq]; exact hE1 k t) (fun k t => by rw [← hq]; exact hE2 k t) z' (t : L)
    (hfix _ (hrt (t : L) t.2))

end Norm

section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_sl2_fix_perfect {r n : ℕ} [Fact r.Prime] [CharP L r] (hn : 0 < n)
    (hr4 : 4 ≤ r ^ n) (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ (r ^ n)) :
    Group.IsPerfect (SL2 (fixSubfield σ)) := by
  classical
  obtain ⟨hfinK, hKcard⟩ := outer_fixSubfield_card (L := L) hn σ hσ
  let : Fintype (fixSubfield σ) := Fintype.ofFinite _
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (Finset.univ : Finset (fixSubfield σ)).card by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hKcard]
      exact hr4)
  exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩

theorem outerOrbitFamily_S_zero {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i) :
    (outerOrbitFamily S hT i hs hmin).S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
  rw [outerOrbitFamily_S, ZMod.val_zero]
  simp only [Function.iterate_zero, id_eq, Set.image_id']

theorem outer_exists_theta0 {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {θ : Fin τ.rank → ℤ} (hθ : θ ∈ componentRoots (rootCharHom a) i) (σ : L ≃+* L)
    (zu : ModGL τ L)
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        zu * g * zu⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ A : SL2 L, iterHom S.D.step s (zu * rootSL2 τ L θ A * zu⁻¹) =
      zu * rootSL2 τ L θ (Matrix.SpecialLinearGroup.map σ.toRingHom A) * zu⁻¹) :
    ∃ θ₀ : SL2 (fixSubfield σ) →* (outerOrbitFamily S hT i hs hmin).S 0,
      (∀ A, ((θ₀ A : (outerOrbitFamily S hT i hs hmin).S 0) : ModGL τ L) =
        zu * rootSL2 τ L θ (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A) * zu⁻¹) ∧
      ∀ A, iterHom S.D.step s ((θ₀ A : (outerOrbitFamily S hT i hs hmin).S 0) : ModGL τ L) =
        θ₀ A := by
  have hθr : IsRoot τ θ := isRoot_of_mem_componentRoots hθ
  have hP0 := outerOrbitFamily_S_zero S hT i hs hmin
  have hneg : -θ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem θ hθ
  have hmemS : ∀ A : SL2 L,
      zu * rootSL2 τ L θ A * zu⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).S 0 := by
    intro A
    rw [hP0]
    refine (hnorm i _).1 ?_
    have h1 : rootSL2 τ L θ A ∈ rootRankOneGroup τ L θ := ⟨A, rfl⟩
    rw [(exceptional_Lang_root_rank_one_torus_transport τ L hθr).1] at h1
    exact sup_le (rootSubgroup_le_rootSpan hθ) (rootSubgroup_le_rootSpan hneg) h1
  have hσι : ∀ A : SL2 (fixSubfield σ), Matrix.SpecialLinearGroup.map σ.toRingHom
      (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A) =
        Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A := by
    intro A
    ext k l
    exact ((A : Matrix (Fin 2) (Fin 2) (fixSubfield σ)) k l).2
  refine ⟨((MulAut.conj zu).toMonoidHom.comp ((rootSL2 τ L θ).comp
      (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype))).codRestrict
      ((outerOrbitFamily S hT i hs hmin).S 0) fun A => hmemS _, fun A => rfl, fun A => ?_⟩
  show iterHom S.D.step s (zu * rootSL2 τ L θ (Matrix.SpecialLinearGroup.map
    (fixSubfield σ).subtype A) * zu⁻¹) = zu * rootSL2 τ L θ (Matrix.SpecialLinearGroup.map
    (fixSubfield σ).subtype A) * zu⁻¹
  rw [hz, hσι]

theorem outer_norm_mem_of_untwist {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {θ : Fin τ.rank → ℤ} (hθ : θ ∈ componentRoots (rootCharHom a) i) (σ : L ≃+* L)
    (zu : ModGL τ L)
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        zu * g * zu⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ A : SL2 L, iterHom S.D.step s (zu * rootSL2 τ L θ A * zu⁻¹) =
      zu * rootSL2 τ L θ (Matrix.SpecialLinearGroup.map σ.toRingHom A) * zu⁻¹)
    (hperf : Group.IsPerfect (SL2 (fixSubfield σ))) :
    ∃ hy : ∀ t : L, zu * pinnedX τ L θ t * zu⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).S 0,
      ∀ t : L, σ t = t → (outerOrbitFamily S hT i hs hmin).norm ⟨_, hy t⟩ ∈
        rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  obtain ⟨θ₀, hθ₀, hθfix⟩ := outer_exists_theta0 S hT i hs hmin hθ σ zu hnorm hz
  have hy : ∀ t : L, zu * pinnedX τ L θ t * zu⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).S 0 := by
    intro t
    rw [outerOrbitFamily_S_zero S hT i hs hmin]
    exact (hnorm i _).1 (pinnedX_mem_rootSpan hθ _)
  refine ⟨hy, fun t ht => ?_⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = (pinnedData τ θ).2.2 := ⟨_, rfl⟩
  have hε2 : ε • ε • t = t := by
    rcases pinnedSign_eq τ θ with h | h <;> rw [hε, h] <;> simp
  have hA : ((θ₀ (uSL (ε • (⟨t, ht⟩ : fixSubfield σ))) :
      (outerOrbitFamily S hT i hs hmin).S 0) : ModGL τ L) = zu * pinnedX τ L θ t * zu⁻¹ := by
    rw [hθ₀, map_uSL, rootSL2_uSL_eq, map_zsmul, ← hε]
    have e : ε • ε • (fixSubfield σ).subtype (⟨t, ht⟩ : fixSubfield σ) = t := hε2
    rw [e]
  have h1 := outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hθfix
    (uSL (ε • (⟨t, ht⟩ : fixSubfield σ)))
  rwa [show θ₀ (uSL (ε • (⟨t, ht⟩ : fixSubfield σ))) = ⟨_, hy t⟩ from Subtype.ext hA] at h1

theorem outer_false_of_component_skeleton {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {r f : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f) (hf2 : 2 ≤ f)
    (key : ∀ (s : ℕ) [NeZero s]
      (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i)
      (hmin : ∀ k, 0 < k → k < s →
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
          componentRoots (rootCharHom a) i)
      (θ : Fin τ.rank → ℤ) (_ : IsRoot τ θ) (zu : ModGL τ L)
      (hy : ∀ t : L, zu * pinnedX τ L θ t * zu⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).S 0)
      (σ : L ≃+* L), (∀ c, σ c = c ^ (r ^ (f * s))) →
      (∀ t : L, σ t = t → (outerOrbitFamily S hT i hs hmin).norm ⟨_, hy t⟩ ∈
        rationalComponent S.ρ S.Γ (rootCharHom a) i) → False) : False := by
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := (expChar_prime_iff L hr).1 inferInstance
  obtain ⟨⟨θ, hθk⟩, hθi⟩ := Quotient.exists_rep i
  have hθ : θ ∈ componentRoots (rootCharHom a) i := ⟨hθk, hθi⟩
  have hθs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] θ ∈ componentRoots (rootCharHom a) i := by
    rw [← hs]
    exact Set.mem_image_of_mem _ hθ
  obtain ⟨w, hw, hwθ⟩ := outer_exists_smul_eq (isRootComponent_componentRoots i) hθ hθs
    (outer_iterate_iform S s θ θ).symm
  obtain ⟨σ, zu, hσ, hnorm, hz⟩ := outer_exists_untwist_root S hT i hs0 hθ hw hwθ.symm
  have hσ' : ∀ c, σ c = c ^ (r ^ (f * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ4 : 4 ≤ r ^ (f * s) := by
    have hr2 := hr.two_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr2 2
      _ ≤ r ^ (f * s) :=
        Nat.pow_le_pow_right (by omega) (le_trans hf2 (Nat.le_mul_of_pos_right f hs0))
  have hperf := outer_sl2_fix_perfect (L := L) (r := r) (Nat.mul_pos (by omega) hs0) hQ4 σ hσ'
  obtain ⟨hy, hrt⟩ := outer_norm_mem_of_untwist S hT i hs hmin hθ σ zu hnorm hz hperf
  exact key s hs hmin θ (isRoot_of_mem_componentRoots hθ) zu hy σ hσ' hrt

theorem outer_false_of_component_fixed_by_twist_cubic {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {r f j : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f) (hq5 : 5 ≤ r ^ f)
    (hc3 : r ^ j ≠ 3) (hc2 : r ^ j = 2 → 7 ≤ r ^ f) (hj0 : 0 < j) (hjf : j < f)
    (z' : ModGL τ L)
    (hfix : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z'⁻¹ = x) : False :=
  outer_false_of_component_skeleton S hT i hr hq (by omega)
    fun _ _ hs hmin _ hθr zu hy σ hσ hrt =>
      outer_false_of_norm_fixed_cubic S hT i hs hmin hθr zu hy hr hq σ hσ hrt hq5 hc3 hc2 hj0 hjf
        z' hfix

end Main

section Root

variable {τ : Tag} {L : Type} [Field L]

theorem FrobRoot.not_conj_cubic [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ}
    (R : FrobRoot S.D p) {r j : ℕ} [ExpChar L r] (hr : r.Prime) (hq0 : R.q0 = r ^ j)
    (hj : 0 < j) (hp : 2 ≤ p) (hq5 : 5 ≤ r ^ (j * p)) (hc3 : r ^ j ≠ 3)
    (hc2 : r ^ j = 2 → 7 ≤ r ^ (j * p)) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (z : ModGL τ L)
    (hz : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, R.step0 x = z * x * z⁻¹) :
    False := by
  have hFr : R.Fr0 = iterateFrobenius L r j :=
    RingHom.ext fun c => by rw [R.Fr0_apply, hq0, iterateFrobenius_def]
  have hq : S.D.q = r ^ (j * p) := by rw [R.q_eq, hq0, ← pow_mul]
  have hjf : j < j * p := lt_mul_of_one_lt_right hj hp
  refine outer_false_of_component_fixed_by_twist_cubic S hT i hr hq hq5 hc3 hc2 hj hjf
    (z⁻¹ * R.z0) fun x hx => ?_
  have h := hz x hx
  rw [R.step0_apply, hFr] at h
  calc z⁻¹ * R.z0 * Units.map (entrywiseHom (iterateFrobenius L r j)) x * (z⁻¹ * R.z0)⁻¹
      = z⁻¹ * (R.z0 * Units.map (entrywiseHom (iterateFrobenius L r j)) x * R.z0⁻¹) * z := by
        group
    _ = x := by rw [h]; group

end Root

end Cert

end CFSG.HardMathSupport.Timmesfeld.LangTorus

end
