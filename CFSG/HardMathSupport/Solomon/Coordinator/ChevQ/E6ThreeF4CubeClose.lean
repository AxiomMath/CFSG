module

public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Torus
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZTorusClose

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section Generic

theorem mem_hyperClosure_of_conj_commute {Y : Type*} [Group Y] {p : ℕ} {E₀ F : Subgroup Y}
    (hFE : F ≤ E₀) (hFi : F.relIndex E₀ = p) {g s : Y} (hg : g ∈ hyperClosure p ⊤ E₀)
    (h : ∀ f ∈ F, Commute (g * f * g⁻¹) s) : s ∈ hyperClosure p ⊤ E₀ := by
  have hk : g⁻¹ * s * g ∈ hyperClosure p ⊤ E₀ := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F, hFE, hFi, fun f hf => ?_⟩
    have e := (h f hf).eq
    calc f * (g⁻¹ * s * g) = g⁻¹ * (g * f * g⁻¹ * s) * g := by group
      _ = g⁻¹ * (s * (g * f * g⁻¹)) * g := by rw [e]
      _ = g⁻¹ * s * g * f := by group
  have hm := (hyperClosure p ⊤ E₀).mul_mem ((hyperClosure p ⊤ E₀).mul_mem hg hk)
    ((hyperClosure p ⊤ E₀).inv_mem hg)
  have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
  rwa [e] at hm

theorem mem_of_conj_pair {G : Type*} [Group G] {K : Type*} [Field K] (H : Subgroup G)
    (X Y : K → G) (hX : ∀ a b, X (a + b) = X a * X b) {s : G} (hs : s ∈ H) {α β : K}
    (hαβ : α ≠ β) (hP : ∀ c, X c * Y c ∈ H)
    (hconj : ∀ c, s * (X c * Y c) * s⁻¹ = X (α * c) * Y (β * c)) (c : K) :
    X c ∈ H ∧ Y c ∈ H := by
  have hd : α - β ≠ 0 := sub_ne_zero.2 hαβ
  set e := c / (α - β) with he
  have hXc : X c = X (α * e) * (X (β * e))⁻¹ := by
    have h1 : α * e = c + β * e := by
      rw [he]
      field_simp
      ring
    rw [h1, hX, mul_inv_cancel_right]
  have hmem : X (α * e) * (X (β * e))⁻¹ ∈ H := by
    have h := H.mul_mem (H.mul_mem (H.mul_mem hs (hP e)) (H.inv_mem hs)) (H.inv_mem (hP (β * e)))
    rw [hconj e] at h
    have e2 : X (α * e) * Y (β * e) * (X (β * e) * Y (β * e))⁻¹ =
        X (α * e) * (X (β * e))⁻¹ := by group
    rwa [e2] at h
  have hXmem : X c ∈ H := hXc ▸ hmem
  refine ⟨hXmem, ?_⟩
  have h := H.mul_mem (H.inv_mem hXmem) (hP c)
  rwa [inv_mul_cancel_left] at h

theorem exists_unit_pow_succ_eq_one_of_five_le (K : Type) [Field K] [Finite K] (q : ℕ)
    (hK : Nat.card K = q ^ 2) (hq : 5 ≤ q) :
    ∃ t : Kˣ, (t : K) ^ (q + 1) = 1 ∧ (t : K) ^ 4 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [Nat.one_le_pow 2 q (by omega), (by omega : 1 ≤ q)]
    ring
  have hdvd : (q - 1) ∣ orderOf g := by
    rw [hord, hfac]
    exact dvd_mul_right _ _
  have hto : orderOf (g ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, hfac]
    exact Nat.mul_div_cancel_left _ (by omega)
  refine ⟨g ^ (q - 1), ?_, ?_⟩
  · have h1 := pow_orderOf_eq_one (g ^ (q - 1))
    rw [hto] at h1
    have h2 := congrArg Units.val h1
    simpa using h2
  · intro h4
    have h5 : (g ^ (q - 1)) ^ 4 = 1 := Units.ext (by simpa using h4)
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hto] at h6
    have h7 := Nat.le_of_dvd (by norm_num) h6
    omega

end Generic

section Anti


@[expose] def e6AntiA (K : Type) [Field K] (u : Kˣ) : adjointGroup .E6 K :=
  ⟨torusElt Tag.E6 K (e6Index 2) u * torusElt Tag.E6 K (e6Index 4) u⁻¹,
    mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _)⟩

@[expose] def e6AntiB (K : Type) [Field K] (u : Kˣ) : adjointGroup .E6 K :=
  ⟨torusElt Tag.E6 K (e6Index 0) u * torusElt Tag.E6 K (e6Index 5) u⁻¹,
    mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _)⟩

@[expose] def antiCharA {K : Type} [Field K] (u : Kˣ) : Fin Tag.E6.rank → Kˣ :=
  fun j => u ^ Tag.E6.cartan (e6Index 2) j * u⁻¹ ^ Tag.E6.cartan (e6Index 4) j

@[expose] def antiCharB {K : Type} [Field K] (u : Kˣ) : Fin Tag.E6.rank → Kˣ :=
  fun j => u ^ Tag.E6.cartan (e6Index 0) j * u⁻¹ ^ Tag.E6.cartan (e6Index 5) j

theorem coe_e6AntiA (K : Type) [Field K] (u : Kˣ) :
    (e6AntiA K u : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 (antiCharA u) := by
  change torusElt Tag.E6 K (e6Index 2) u * torusElt Tag.E6 K (e6Index 4) u⁻¹ = _
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  rfl

theorem coe_e6AntiB (K : Type) [Field K] (u : Kˣ) :
    (e6AntiB K u : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 (antiCharB u) := by
  change torusElt Tag.E6 K (e6Index 0) u * torusElt Tag.E6 K (e6Index 5) u⁻¹ = _
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  rfl

theorem antiCharA_zero {K : Type} [Field K] (u : Kˣ) : antiCharA u (e6Index 0) = u⁻¹ := by
  simp only [antiCharA]
  rw [show Tag.E6.cartan (e6Index 2) (e6Index 0) = -1 from by decide +kernel,
    show Tag.E6.cartan (e6Index 4) (e6Index 0) = 0 from by decide +kernel]
  simp

theorem antiCharA_five {K : Type} [Field K] (u : Kˣ) : antiCharA u (e6Index 5) = u := by
  simp only [antiCharA]
  rw [show Tag.E6.cartan (e6Index 2) (e6Index 5) = 0 from by decide +kernel,
    show Tag.E6.cartan (e6Index 4) (e6Index 5) = -1 from by decide +kernel]
  simp

theorem antiCharB_two {K : Type} [Field K] (u : Kˣ) : antiCharB u (e6Index 2) = u⁻¹ := by
  simp only [antiCharB]
  rw [show Tag.E6.cartan (e6Index 0) (e6Index 2) = -1 from by decide +kernel,
    show Tag.E6.cartan (e6Index 5) (e6Index 2) = 0 from by decide +kernel]
  simp

theorem antiCharB_four {K : Type} [Field K] (u : Kˣ) : antiCharB u (e6Index 4) = u := by
  simp only [antiCharB]
  rw [show Tag.E6.cartan (e6Index 0) (e6Index 4) = 0 from by decide +kernel,
    show Tag.E6.cartan (e6Index 5) (e6Index 4) = -1 from by decide +kernel]
  simp

theorem xE_param_add {K : Type} [Field K] (i : Fin Tag.E6.rank) (c d : K) :
    xE Tag.E6 K i (c + d) = xE Tag.E6 K i c * xE Tag.E6 K i d :=
  Subtype.ext (xUnit_add i c d)

theorem yE_param_add {K : Type} [Field K] (i : Fin Tag.E6.rank) (c d : K) :
    yE Tag.E6 K i (c + d) = yE Tag.E6 K i c * yE Tag.E6 K i d :=
  Subtype.ext (yUnit_add i c d)

theorem conj_xE_of_coe {K : Type} [Field K] {s : adjointGroup .E6 K}
    {a : Fin Tag.E6.rank → Kˣ} (hs : (s : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 a)
    (i : Fin Tag.E6.rank) (c : K) :
    s * xE Tag.E6 K i c * s⁻¹ = xE Tag.E6 K i ((a i : K) * c) := by
  apply Subtype.ext
  change (s : ModGL Tag.E6 K) * xUnit Tag.E6 K i c * (s : ModGL Tag.E6 K)⁻¹ =
    xUnit Tag.E6 K i ((a i : K) * c)
  rw [hs]
  exact (root_diagonal_conjugation Tag.E6 K a).1 i c

theorem conj_yE_of_coe {K : Type} [Field K] {s : adjointGroup .E6 K}
    {a : Fin Tag.E6.rank → Kˣ} (hs : (s : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 a)
    (i : Fin Tag.E6.rank) (c : K) :
    s * yE Tag.E6 K i c * s⁻¹ = yE Tag.E6 K i ((((a i)⁻¹ : Kˣ) : K) * c) := by
  apply Subtype.ext
  change (s : ModGL Tag.E6 K) * yUnit Tag.E6 K i c * (s : ModGL Tag.E6 K)⁻¹ =
    yUnit Tag.E6 K i ((((a i)⁻¹ : Kˣ) : K) * c)
  rw [hs]
  exact (root_diagonal_conjugation Tag.E6 K a).2.1 i c

theorem conj_mul_conj {G : Type*} [Group G] (s x y : G) :
    s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by
  group

theorem e6AntiA_conj_xE (K : Type) [Field K] (u : Kˣ) (c : K) :
    e6AntiA K u * (xE Tag.E6 K (e6Index 0) c * xE Tag.E6 K (e6Index 5) c) * (e6AntiA K u)⁻¹ =
      xE Tag.E6 K (e6Index 0) (((u⁻¹ : Kˣ) : K) * c) * xE Tag.E6 K (e6Index 5) ((u : K) * c) := by
  rw [conj_mul_conj, conj_xE_of_coe (coe_e6AntiA K u), conj_xE_of_coe (coe_e6AntiA K u),
    antiCharA_zero, antiCharA_five]

theorem e6AntiA_conj_yE (K : Type) [Field K] (u : Kˣ) (c : K) :
    e6AntiA K u * (yE Tag.E6 K (e6Index 0) c * yE Tag.E6 K (e6Index 5) c) * (e6AntiA K u)⁻¹ =
      yE Tag.E6 K (e6Index 0) ((u : K) * c) * yE Tag.E6 K (e6Index 5) (((u⁻¹ : Kˣ) : K) * c) := by
  rw [conj_mul_conj, conj_yE_of_coe (coe_e6AntiA K u), conj_yE_of_coe (coe_e6AntiA K u),
    antiCharA_zero, antiCharA_five, inv_inv]

theorem e6AntiB_conj_xE (K : Type) [Field K] (u : Kˣ) (c : K) :
    e6AntiB K u * (xE Tag.E6 K (e6Index 2) c * xE Tag.E6 K (e6Index 4) c) * (e6AntiB K u)⁻¹ =
      xE Tag.E6 K (e6Index 2) (((u⁻¹ : Kˣ) : K) * c) * xE Tag.E6 K (e6Index 4) ((u : K) * c) := by
  rw [conj_mul_conj, conj_xE_of_coe (coe_e6AntiB K u), conj_xE_of_coe (coe_e6AntiB K u),
    antiCharB_two, antiCharB_four]

theorem e6AntiB_conj_yE (K : Type) [Field K] (u : Kˣ) (c : K) :
    e6AntiB K u * (yE Tag.E6 K (e6Index 2) c * yE Tag.E6 K (e6Index 4) c) * (e6AntiB K u)⁻¹ =
      yE Tag.E6 K (e6Index 2) ((u : K) * c) * yE Tag.E6 K (e6Index 4) (((u⁻¹ : Kˣ) : K) * c) := by
  rw [conj_mul_conj, conj_yE_of_coe (coe_e6AntiB K u), conj_yE_of_coe (coe_e6AntiB K u),
    antiCharB_two, antiCharB_four, inv_inv]

end Anti

section Split


theorem orbitWord_f4_three : TwistTag.E6.orbitWord (f4FoldedIndex ⟨3, by decide⟩) =
    [e6Index 0, e6Index 5] := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨3, by decide⟩) =
      [(⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank), ⟨5, by decide⟩] := by decide +kernel
  exact h

theorem orbitWord_f4_two : TwistTag.E6.orbitWord (f4FoldedIndex ⟨2, by decide⟩) =
    [e6Index 2, e6Index 4] := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨2, by decide⟩) =
      [(⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank), ⟨4, by decide⟩] := by decide +kernel
  exact h

theorem xE_pair_mem_fixE6 (K : Type) [Field K] (j : Fin Tag.F4.rank) {i₁ i₂ : Fin Tag.E6.rank}
    (hj : TwistTag.E6.orbitWord (f4FoldedIndex j) = [i₁, i₂]) (c : K) :
    xE Tag.E6 K i₁ c * xE Tag.E6 K i₂ c ∈ fixE6 K ∧
      yE Tag.E6 K i₁ c * yE Tag.E6 K i₂ c ∈ fixE6 K := by
  have hx := f4OrbitXUnit_mem (K := K) j c
  have hy := f4OrbitYUnit_mem (K := K) j c
  simp only [f4OrbitXUnit, f4OrbitYUnit, hj, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hx hy
  exact ⟨Subgroup.mem_subgroupOf.mpr hx, Subgroup.mem_subgroupOf.mpr hy⟩

theorem xE_fixed_mem_fixE6 (K : Type) [Field K] (j : Fin Tag.F4.rank) {i : Fin Tag.E6.rank}
    (hj : TwistTag.E6.orbitWord (f4FoldedIndex j) = [i]) (c : K) :
    xE Tag.E6 K i c ∈ fixE6 K ∧ yE Tag.E6 K i c ∈ fixE6 K := by
  have h := xyUnit_mem_fixed_of_orbitWord_eq K j i hj c
  exact ⟨Subgroup.mem_subgroupOf.mpr h.1, Subgroup.mem_subgroupOf.mpr h.2⟩

theorem eq_top_of_fixE6_anti (K : Type) [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    (H : Subgroup (adjointGroup .E6 K)) (hF : fixE6 K ≤ H) (hA : ∀ u : Kˣ, e6AntiA K u ∈ H)
    (hB : ∀ u : Kˣ, e6AntiB K u ∈ H) : H = ⊤ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨u, hu⟩ := CFSG.LieType.Chevalley.exists_unit_sq_ne_one (F := K)
    ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK⟩
  have hne : ((u⁻¹ : Kˣ) : K) ≠ (u : K) := by
    intro h
    apply hu
    have h1 : (u : K) * ((u⁻¹ : Kˣ) : K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h] at h1
    rw [sq]
    exact h1
  have h05 : ∀ c : K, (xE Tag.E6 K (e6Index 0) c ∈ H ∧ xE Tag.E6 K (e6Index 5) c ∈ H) ∧
      (yE Tag.E6 K (e6Index 0) c ∈ H ∧ yE Tag.E6 K (e6Index 5) c ∈ H) := fun c =>
    ⟨mem_of_conj_pair H (xE Tag.E6 K (e6Index 0)) (xE Tag.E6 K (e6Index 5))
        (xE_param_add _) (hA u) hne
        (fun c => hF (xE_pair_mem_fixE6 K _ orbitWord_f4_three c).1)
        (e6AntiA_conj_xE K u) c,
      mem_of_conj_pair H (yE Tag.E6 K (e6Index 0)) (yE Tag.E6 K (e6Index 5))
        (yE_param_add _) (hA u) hne.symm
        (fun c => hF (xE_pair_mem_fixE6 K _ orbitWord_f4_three c).2)
        (e6AntiA_conj_yE K u) c⟩
  have h24 : ∀ c : K, (xE Tag.E6 K (e6Index 2) c ∈ H ∧ xE Tag.E6 K (e6Index 4) c ∈ H) ∧
      (yE Tag.E6 K (e6Index 2) c ∈ H ∧ yE Tag.E6 K (e6Index 4) c ∈ H) := fun c =>
    ⟨mem_of_conj_pair H (xE Tag.E6 K (e6Index 2)) (xE Tag.E6 K (e6Index 4))
        (xE_param_add _) (hB u) hne
        (fun c => hF (xE_pair_mem_fixE6 K _ orbitWord_f4_two c).1)
        (e6AntiB_conj_xE K u) c,
      mem_of_conj_pair H (yE Tag.E6 K (e6Index 2)) (yE Tag.E6 K (e6Index 4))
        (yE_param_add _) (hB u) hne.symm
        (fun c => hF (xE_pair_mem_fixE6 K _ orbitWord_f4_two c).2)
        (e6AntiB_conj_yE K u) c⟩
  apply eq_top_of_simpleRootOps_gen
  intro i c
  have h1 := xE_fixed_mem_fixE6 K ⟨0, by decide⟩ orbitWord_f4_zero c
  have h3 := xE_fixed_mem_fixE6 K ⟨1, by decide⟩ orbitWord_f4_one c
  fin_cases i
  · exact ⟨(h05 c).1.1, (h05 c).2.1⟩
  · exact ⟨hF h1.1, hF h1.2⟩
  · exact ⟨(h24 c).1.1, (h24 c).2.1⟩
  · exact ⟨hF h3.1, hF h3.2⟩
  · exact ⟨(h24 c).1.2, (h24 c).2.2⟩
  · exact ⟨(h05 c).1.2, (h05 c).2.2⟩

theorem e6_hyperGen_of_anti (K : Type) [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    (E₀ : Subgroup (adjointGroup .E6 K)) (hcl : fixE6 K ≤ hyperClosure 3 ⊤ E₀)
    (hF : ∃ F ≤ E₀, F.relIndex E₀ = 3 ∧ ∃ g ∈ fixE6 K, ∀ f ∈ F, ∀ u : Kˣ,
      Commute (g * f * g⁻¹) (e6AntiA K u) ∧ Commute (g * f * g⁻¹) (e6AntiB K u)) :
    HyperGen 3 ⊤ E₀ := by
  obtain ⟨F, hFE, hFi, g, hg, hcomm⟩ := hF
  refine hyperGen_iff_le.2 (top_le_iff.2 (eq_top_of_fixE6_anti K hK _ hcl (fun u => ?_)
    (fun u => ?_)))
  · exact mem_hyperClosure_of_conj_commute hFE hFi (hcl hg) fun f hf => (hcomm f hf u).1
  · exact mem_hyperClosure_of_conj_commute hFE hFi (hcl hg) fun f hf => (hcomm f hf u).2

end Split

section Twisted


theorem twE6_hyperGen_of_anti {k K : Type} [Field k] [Finite k] [Field K] [Finite K]
    [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = Nat.card k ^ 2) (hk : 5 ≤ Nat.card k)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hcl : (phiG σ hfix).range ≤ hyperClosure 3 ⊤ E₀)
    (hF : ∃ F ≤ E₀, F.relIndex E₀ = 3 ∧ ∃ g ∈ (phiG σ hfix).range, ∀ f ∈ F, ∀ t : Kˣ,
      (t : K) ^ (Nat.card k + 1) = 1 → Commute (g * f * g⁻¹) (torusWord σ hσ hK t)) :
    HyperGen 3 ⊤ E₀ := by
  obtain ⟨F, hFE, hFi, g, hg, hcomm⟩ := hF
  obtain ⟨t, ht, ht4⟩ := exists_unit_pow_succ_eq_one_of_five_le K (Nat.card k) hK hk
  exact hyperGen_iff_le.2 (top_le_iff.2 (closure_top_of_torusWord σ hσ hfix hK _ hcl t ht ht4
    (mem_hyperClosure_of_conj_commute hFE hFi (hcl hg) fun f hf => hcomm f hf t ht)))

end Twisted

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

end
