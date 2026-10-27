module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Plane
public import CFSG.HardMathSupport.Foote.Proving.PSL4FivePart
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups


theorem closure_centralizers_eq_top_of_frame {τ : Tag} {K : Type} [Field K] [Finite K] {n : ℕ}
    {S : Set (Fin τ.rank → ℤ)} {ψA ψB : SL(n, K) →* ModGL τ K} (hA : Function.Injective ψA)
    (hB : Function.Injective ψB) (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hrange : ψA.range ⊔ ψB.range = rootSpan τ K S) (hC : FrameClosing τ K S)
    (hN : FrameNormalizerSolvable τ K S) {p : ℕ} [hp : Fact p.Prime] (hpn : n < p)
    (hcyc : ∀ g : SL(n, K), orderOf g = p →
      IsCyclic (Subgroup.centralizer ({g} : Set SL(n, K))))
    (hcard : (Nat.card (adjointGroup τ K)).factorization p =
      2 * (Nat.card SL(n, K)).factorization p)
    (hthird : ∀ E : Subgroup (adjointGroup τ K), Nat.card E = p ^ 2 → (∀ x ∈ E, x ^ p = 1) →
      ∀ a b : adjointGroup τ K, a ∈ E → b ∈ E → a ≠ 1 → b ≠ 1 →
        ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
          ∃ P : Subgroup (adjointGroup τ K),
            P ≤ Subgroup.centralizer ({e} : Set (adjointGroup τ K)) ∧ ¬ Group.IsSolvable ↥P)
    (E : Subgroup (adjointGroup τ K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : adjointGroup τ K | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := inferInstance
  have hAG : ∀ x, ψA x ∈ adjointGroup τ K := fun x =>
    rootSpan_le_adjointGroup K S (hrange ▸ Subgroup.mem_sup_left ⟨x, rfl⟩)
  have hBG : ∀ x, ψB x ∈ adjointGroup τ K := fun x =>
    rootSpan_le_adjointGroup K S (hrange ▸ Subgroup.mem_sup_right ⟨x, rfl⟩)
  let ψA' : SL(n, K) →* adjointGroup τ K := ψA.codRestrict (adjointGroup τ K) hAG
  let ψB' : SL(n, K) →* adjointGroup τ K := ψB.codRestrict (adjointGroup τ K) hBG
  have hψA' : ∀ x, ((ψA' x : adjointGroup τ K) : ModGL τ K) = ψA x := fun _ => rfl
  have hψB' : ∀ x, ((ψB' x : adjointGroup τ K) : ModGL τ K) = ψB x := fun _ => rfl
  have hA' : Function.Injective ψA' := fun x y h => hA (congrArg Subtype.val h)
  have hB' : Function.Injective ψB' := fun x y h => hB (congrArg Subtype.val h)
  have hcomm' : ∀ x y, Commute (ψA' x) (ψB' y) := fun x y => Subtype.ext (hcomm x y).eq
  have hAB : ¬ p ∣ Nat.card ↥(ψA'.range ⊓ ψB'.range) := by
    intro hdvd
    have hle : ψA'.range ⊓ ψB'.range ≤ (Subgroup.center SL(n, K)).map ψA' := by
      rintro z ⟨⟨c, rfl⟩, hcB⟩
      exact ⟨c, Subgroup.mem_center_iff.2 fun x => (commute_of_frame_mem_range hA' hcomm' hcB x).eq,
        rfl⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective hA'] at h1
    have h2 := CFSG.HardMathSupport.Foote.Proving.natCard_center_SL_le (Fin n) K
    have h3 : p ≤ Nat.card ↥(ψA'.range ⊓ ψB'.range) := Nat.le_of_dvd Nat.card_pos hdvd
    simp only [Fintype.card_fin] at h2
    have := hp.out.two_le
    omega
  obtain ⟨g, a, hao, hEg⟩ :=
    exists_conj_plane_of_frame ψA' ψB' hA' hB' hcomm' hcyc hAB hcard E hEp hEc
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  set T : Subgroup (adjointGroup τ K) → Set (adjointGroup τ K) :=
    fun F => {k | ∃ x ∈ F, x ≠ 1 ∧ Commute k x} with hTdef
  have hTE : T E' = (MulAut.conj g).toMonoidHom '' T E := by
    ext k
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hx1, hkx⟩
      refine ⟨g⁻¹ * k * g, ⟨x, hx, fun h => hx1 (by simp [h]), ?_⟩, by simp [MulAut.conj_apply]; group⟩
      have h := hkx.eq
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at h
      show g⁻¹ * k * g * x = x * (g⁻¹ * k * g)
      calc g⁻¹ * k * g * x = g⁻¹ * (k * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * k) * g := by rw [h]
        _ = x * (g⁻¹ * k * g) := by group
    · rintro ⟨k₀, ⟨x, hx, hx1, hkx⟩, rfl⟩
      refine ⟨(MulAut.conj g).toMonoidHom x, ⟨x, hx, rfl⟩, fun h => hx1 ?_, ?_⟩
      · exact (map_eq_one_iff _ (MulAut.conj g).injective).1 h
      · exact hkx.map _
  suffices hE'top : Subgroup.closure (T E') = ⊤ by
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom y ∈ Subgroup.closure (T E') := by
      rw [hE'top]
      exact Subgroup.mem_top _
    rw [hTE, ← MonoidHom.map_closure] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := (MulAut.conj g).injective hzy
    rw [← this]
    exact hz
  set H := Subgroup.closure (T E') with hH
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hao
    exact hp.out.one_lt.ne hao
  have hA1 : ψA' a ≠ 1 := fun h => ha1 (hA' (h.trans (map_one ψA').symm))
  have hB1 : ψB' a ≠ 1 := fun h => ha1 (hB' (h.trans (map_one ψB').symm))
  have haE : ψA' a ∈ E' := by
    rw [hEg]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hbE : ψB' a ∈ E' := by
    rw [hEg]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hXH : ψA'.range ⊔ ψB'.range ≤ H := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact Subgroup.subset_closure ⟨ψB' a, hbE, hB1, hcomm' y a⟩
    · rintro _ ⟨y, rfl⟩
      exact Subgroup.subset_closure ⟨ψA' a, haE, hA1, (hcomm' a y).symm⟩
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]
  have hE'p : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hEp y hy, map_one]
  obtain ⟨e, heE, hea, heb, P, hPC, hPs⟩ :=
    hthird E' hE'c hE'p (ψA' a) (ψB' a) haE hbE hA1 hB1
  have he1 : e ≠ 1 := fun h => hea (h ▸ Subgroup.one_mem _)
  have hPH : P ≤ H := fun z hz =>
    Subgroup.subset_closure ⟨e, heE, he1,
      (commute_iff_eq _ _).2 (Subgroup.mem_centralizer_singleton_iff.1 (hPC hz))⟩
  have hzc : ∀ h ∈ Subgroup.zpowers (ψA' a), ∀ k ∈ Subgroup.zpowers (ψB' a), Commute h k := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((hcomm' a a).zpow_left i).zpow_right j
  have heE' := heE
  rw [hEg] at heE'
  obtain ⟨_, ⟨i, hi0⟩, _, ⟨j, hj0⟩, hce⟩ := exists_mul_of_mem_sup_of_commute hzc heE'
  simp only at hi0 hj0
  rw [← hi0, ← hj0] at hce
  have hi : orderOf (a ^ i) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hao,
        pow_orderOf_eq_one, one_zpow]
    · intro h
      apply heb
      have : ψA' a ^ i = 1 := by rw [← map_zpow, h, map_one]
      rw [hce, this, one_mul]
      exact Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩
  have hj : orderOf (a ^ j) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hao,
        pow_orderOf_eq_one, one_zpow]
    · intro h
      apply hea
      have : ψB' a ^ j = 1 := by rw [← map_zpow, h, map_one]
      rw [hce, this, mul_one]
      exact Subgroup.mem_zpowers_iff.2 ⟨i, rfl⟩
  have heq : e = ψA' (a ^ i) * ψB' (a ^ j) := by rw [hce, map_zpow, map_zpow]
  have hXS : rootSpan τ K S = (ψA'.range ⊔ ψB'.range).map (adjointGroup τ K).subtype := by
    rw [Subgroup.map_sup, ← hrange]
    congr 1
    · rw [← MonoidHom.range_comp]
      rfl
    · rw [← MonoidHom.range_comp]
      rfl
  have hnot : ¬ H.map (adjointGroup τ K).subtype ≤
      Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) := by
    intro hle
    have hPN : P.map (adjointGroup τ K).subtype ≤
        Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) :=
      (Subgroup.map_mono hPH).trans hle
    have hsol : Group.IsSolvable ↥(P.map (adjointGroup τ K).subtype ⊓ rootSpan τ K S) := by
      apply Group.isSolvable_of_comm
      rintro ⟨z, ⟨w, hwP, rfl⟩, hzX⟩ ⟨z', ⟨w', hw'P, rfl⟩, hz'X⟩
      apply Subtype.ext
      have hwX : w ∈ ψA'.range ⊔ ψB'.range := by
        rw [hXS] at hzX
        obtain ⟨w₀, hw₀, hw₀e⟩ := hzX
        have : w₀ = w := Subtype.ext hw₀e
        rw [← this]
        exact hw₀
      have hw'X : w' ∈ ψA'.range ⊔ ψB'.range := by
        rw [hXS] at hz'X
        obtain ⟨w₀, hw₀, hw₀e⟩ := hz'X
        have : w₀ = w' := Subtype.ext hw₀e
        rw [← this]
        exact hw₀
      have hwe : Commute w (ψA' (a ^ i) * ψB' (a ^ j)) := by
        rw [← heq]
        exact (commute_iff_eq _ _).2 (Subgroup.mem_centralizer_singleton_iff.1 (hPC hwP))
      have hw'e : Commute w' (ψA' (a ^ i) * ψB' (a ^ j)) := by
        rw [← heq]
        exact (commute_iff_eq _ _).2 (Subgroup.mem_centralizer_singleton_iff.1 (hPC hw'P))
      have hc := commute_of_mem_centralizer_frame ψA' ψB' hA' hB' hcomm' hcyc hAB hi hj hwX hw'X
        hwe hw'e
      show (w : ModGL τ K) * w' = w' * w
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hc.eq]
    have hPsol := hN _ (Subgroup.map_subtype_le _) hPN hsol
    apply hPs
    let e1 := Subgroup.equivMapOfInjective P (adjointGroup τ K).subtype
      (adjointGroup τ K).subtype_injective
    exact Group.isSolvable_of_surjective (f := e1.symm.toMonoidHom) e1.symm.surjective
  have hXmap : rootSpan τ K S ≤ H.map (adjointGroup τ K).subtype := by
    rw [hXS]
    exact Subgroup.map_mono hXH
  have htop := hC _ (Subgroup.map_subtype_le _) hXmap hnot
  rw [eq_top_iff]
  intro y _
  have hy : (y : ModGL τ K) ∈ H.map (adjointGroup τ K).subtype := by
    rw [htop]
    exact y.2
  obtain ⟨y₀, hy₀, hy₀e⟩ := hy
  have : y₀ = y := Subtype.ext hy₀e
  rw [← this]
  exact hy₀

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
