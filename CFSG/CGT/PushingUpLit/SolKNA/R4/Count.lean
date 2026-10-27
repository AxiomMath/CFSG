module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Std
public import CFSG.ClassicalInvolution.Q3.TL3S8BCount
public import CFSG.ClassicalInvolution.Q3.TL3C11R

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Gen

variable {G : Type*} [Group G]

theorem exists_closure_of_index_two {H H₀ : Subgroup G} (hle : H₀ ≤ H)
    (hidx : ∀ x ∈ H, ∀ y ∈ H, x ∉ H₀ → y ∉ H₀ → x⁻¹ * y ∈ H₀) {m : ℕ}
    (h₀ : ∃ s : Finset G, s.card ≤ m ∧ Subgroup.closure (s : Set G) = H₀) :
    ∃ s : Finset G, s.card ≤ m + 1 ∧ Subgroup.closure (s : Set G) = H := by
  classical
  obtain ⟨s, hs, hcl⟩ := h₀
  by_cases hH : H ≤ H₀
  · exact ⟨s, by omega, hcl.trans (le_antisymm hle hH)⟩
  · obtain ⟨x, hxH, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hH
    have hsH : (s : Set G) ⊆ H := fun y hy =>
      hle (by rw [← hcl]; exact Subgroup.subset_closure hy)
    have hxc : x ∈ Subgroup.closure ((insert x s : Finset G) : Set G) :=
      Subgroup.subset_closure (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
    have hsc : H₀ ≤ Subgroup.closure ((insert x s : Finset G) : Set G) := by
      rw [← hcl, Subgroup.closure_le]
      intro z hz
      exact Subgroup.subset_closure
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hz)))
    refine ⟨insert x s, (Finset.card_insert_le _ _).trans (by omega), le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      intro y hy
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hy
      · exact hxH
      · exact hsH hy
    · intro y hyH
      by_cases hy0 : y ∈ H₀
      · exact hsc hy0
      · have h1 := hsc (hidx x hxH y hyH hx hy0)
        have e : y = x * (x⁻¹ * y) := by group
        rw [e]
        exact Subgroup.mul_mem _ hxc h1

theorem exists_closure_of_ker_cyclic {H D C : Subgroup G} [IsCyclic C] (hDH : D ≤ H)
    {F : G → G} (hmul : ∀ g ∈ H, ∀ k ∈ H, F (g * k) = F g * F k) (hC : ∀ g ∈ H, F g ∈ C)
    (hker : ∀ g ∈ H, F g = 1 → g ∈ D) {m : ℕ}
    (hD : ∃ s : Finset G, s.card ≤ m ∧ Subgroup.closure (s : Set G) = D) :
    ∃ s : Finset G, s.card ≤ m + 1 ∧ Subgroup.closure (s : Set G) = H := by
  classical
  obtain ⟨s, hs, hcl⟩ := hD
  let φ : ↥H →* G := MonoidHom.mk' (fun g => F (g : G)) (fun g k => hmul g g.2 k k.2)
  have hrange : φ.range ≤ C := by
    rintro _ ⟨g, rfl⟩
    exact hC g g.2
  have : IsCyclic ↥φ.range := Subgroup.isCyclic_of_le hrange
  obtain ⟨⟨c₀, hc₀⟩, hgen⟩ := (inferInstance : IsCyclic ↥φ.range).exists_generator
  obtain ⟨g₀, hg₀⟩ := MonoidHom.mem_range.mp hc₀
  have hsH : (s : Set G) ⊆ H := fun y hy =>
    hDH (by rw [← hcl]; exact Subgroup.subset_closure hy)
  have hg₀c : (g₀ : G) ∈ Subgroup.closure ((insert (g₀ : G) s : Finset G) : Set G) :=
    Subgroup.subset_closure (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hDc : D ≤ Subgroup.closure ((insert (g₀ : G) s : Finset G) : Set G) := by
    rw [← hcl, Subgroup.closure_le]
    intro z hz
    exact Subgroup.subset_closure
      (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hz)))
  refine ⟨insert (g₀ : G) s, (Finset.card_insert_le _ _).trans (by omega), le_antisymm ?_ ?_⟩
  · rw [Subgroup.closure_le]
    intro y hy
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hy
    · exact g₀.2
    · exact hsH hy
  · intro g hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (hgen ⟨φ ⟨g, hg⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩)
    have hk' : c₀ ^ k = φ ⟨g, hg⟩ := by
      have := congrArg Subtype.val hk
      simpa using this
    have hφ : φ (⟨g, hg⟩ * g₀ ^ (-k)) = 1 := by
      rw [map_mul, map_zpow, hg₀, ← hk', zpow_neg, mul_inv_cancel]
    have hmem : g * (g₀ : G) ^ (-k) ∈ H := H.mul_mem hg (H.zpow_mem g₀.2 _)
    have hFk : F (g * (g₀ : G) ^ (-k)) = 1 := by
      have e : ((⟨g, hg⟩ * g₀ ^ (-k) : ↥H) : G) = g * (g₀ : G) ^ (-k) := by simp
      rw [← e]
      exact hφ
    have h1 := Subgroup.mul_mem _ (hDc (hker _ hmem hFk))
      (Subgroup.zpow_mem _ hg₀c k)
    rwa [show g * (g₀ : G) ^ (-k) * (g₀ : G) ^ k = g by group] at h1

theorem inv_mul_mem_of_relIndex_two {H K : Subgroup G} (hi : H.relIndex K = 2) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (ha' : a ∉ H) (hb' : b ∉ H) : a⁻¹ * b ∈ H := by
  obtain ⟨a₀, -, h⟩ := Subgroup.relIndex_eq_two_iff'.mp hi
  have h1 : a₀ * a ∈ H := by
    rcases h a ha with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 ha'
  have h2 : a₀ * b ∈ H := by
    rcases h b hb with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact h2
    · exact absurd h2 hb'
  have e : a⁻¹ * b = (a₀ * a)⁻¹ * (a₀ * b) := by group
  rw [e]
  exact H.mul_mem (H.inv_mem h1) h2

end Gen

section TwoGen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem e2Prime_two_generators_of_le {K : Subgroup G} {S : Sylow 2 G} (hE : TightE2Prime K S)
    {D : Subgroup G}
    (hDT : D ≤ (S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)) :
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = D := by
  classical
  obtain ⟨C, hCcyc, hCT, hidx⟩ := hE
  have hDC : IsCyclic ↥(D ⊓ C) := Subgroup.isCyclic_of_le (H' := C) inf_le_right
  obtain ⟨⟨c, hc⟩, hcgen⟩ := hDC.exists_generator
  have hCz : D ⊓ C = Subgroup.zpowers c := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcgen ⟨y, hy⟩)
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exact Subgroup.zpowers_le.mpr hc
  by_cases hDt : D ≤ C
  · refine ⟨{c}, by simp, ?_⟩
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure, ← hCz, inf_eq_left.mpr hDt]
  · obtain ⟨x, hxD, hxC⟩ := Set.not_subset.mp hDt
    refine ⟨{c, x}, Finset.card_le_two, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hc.1
      · exact hxD
    · intro y hyD
      have hcl : Subgroup.zpowers c ≤ Subgroup.closure (({c, x} : Finset G) : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      have hxcl : x ∈ Subgroup.closure (({c, x} : Finset G) : Set G) :=
        Subgroup.subset_closure (by simp)
      by_cases hyC : y ∈ C
      · exact hcl (hCz ▸ ⟨hyD, hyC⟩)
      · have hmem : x⁻¹ * y ∈ D ⊓ C :=
          ⟨D.mul_mem (D.inv_mem hxD) hyD, hidx x (hDT hxD) y (hDT hyD) hxC hyC⟩
        rw [show y = x * (x⁻¹ * y) by group]
        exact Subgroup.mul_mem _ hxcl (hcl (hCz ▸ hmem))

end TwoGen

@[expose] def TightThm6SylowBelowSRc (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)], IH (Nat.card G) →
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → TightClsR r G R S t →
      Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) → ∀ T : Subgroup G,
      IsSylow2Of T
        (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)) →
      IsSylow2Of T ⊤ → Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) →
        TwoSubgroupsFourGenerated (genFittingFStar G)

@[expose] def TightCountRc (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)], IH (Nat.card G) →
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G), StdR r R S t T →
      TightClsR r G R S t → ¬ AllTypeTwo (tightCore R) t → TightC19_11bSR r →
      TightE2Prime (tightCore R) T → TwoSubgroupsFourGenerated (genFittingFStar G)

@[expose] def TightPMR (r : ℕ) (IH : ℕ → Prop) : Prop :=
  4 ≤ r → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    IH (Nat.card G) → (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G), StdR r R S t T →
      TightClsR r G R S t → ¬ AllTypeTwo (tightCore R) t → TightC19_11bSR r →
      TightE2Prime (tightCore R) T →
      ∀ C : Subgroup G, C ≤ (S : Subgroup R).map R.subtype → IsCyclic ↥C →
        C.relIndex ((S : Subgroup R).map R.subtype) = 2 →
        ∀ g ∈ (T : Subgroup G), (∀ x ∈ C, g * x * g⁻¹ = x) ∨ (∀ x ∈ C, g * x * g⁻¹ = x⁻¹)

theorem tightThm6SylowBelowSRc_of_parts {r : ℕ} (hB3 : GoldschmidtB3Tmp) (hp : SylowPartsR r)
    (hcore : TightC19_11bSR r) {IH : ℕ → Prop} (hcount : TightCountRc r IH) :
    TightThm6SylowBelowSRc r IH := by
  intro G _ _ _ hIH hnab R S t hd hc hq T hT hTG he
  by_contra hn
  obtain ⟨T', -, h⟩ := hp.bundle hd hq he hn hT hTG
  obtain ⟨W, hW, -⟩ := hp.w69 h
  rcases hp.muZ2OrS3 h hW with hZ | hS3
  · exact hp.not_muIsoZ2 hnab hB3 h hW hZ
  · have hmu := hp.not_allTypeTwo h hW hS3
    exact hn (hcount G hIH hnab R S t T' h hc hmu hcore (hp.e2_of_core hcore hnab h hmu))

theorem tightCountRc_of_pm {r : ℕ} {IH : ℕ → Prop} (hr : 4 ≤ r) (hpm : TightPMR r IH) :
    TightCountRc r IH := by
  intro G _ _ _ hIH hnab R S t T h hc hmu hcore hE
  classical
  have hpm' := hpm hr G hIH hnab R S t T h hc hmu hcore hE
  obtain ⟨e⟩ := h.quat
  set S' : Subgroup G := (S : Subgroup R).map R.subtype with hS'
  have hS'T : (T : Subgroup G) ⊓ tightCore R = S' := h.inf_core_eq
  have hS'K : S' ≤ tightCore R := by rw [← hS'T]; exact inf_le_right
  have hS'T' : S' ≤ (T : Subgroup G) := by rw [← hS'T]; exact inf_le_left
  have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  set q₁ : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a 1) with hq₁
  set c : G := (((q₁ : R)) : G) with hc_def
  have hcS' : c ∈ S' := ⟨(q₁ : R), q₁.2, rfl⟩
  set C : Subgroup G := Subgroup.zpowers c with hCdef
  have hCS' : C ≤ S' := Subgroup.zpowers_le.mpr hcS'
  have hCcyc : IsCyclic ↥C := by rw [hCdef]; infer_instance
  have hcardS' : Nat.card ↥S' = 2 ^ r := by
    rw [hS', Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr e.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
    obtain ⟨k, hk⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_add]
    ring
  have hordc : orderOf c = 2 ^ (r - 1) := by
    have h1 : orderOf c = orderOf q₁ :=
      (Subgroup.orderOf_coe (H := R) (q₁ : R)).trans (Subgroup.orderOf_coe q₁)
    have h2 : orderOf (e.symm (QuaternionGroup.a 1)) =
        orderOf (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (r - 2))) :=
      orderOf_injective e.symm.toMonoidHom e.symm.injective _
    rw [h1, hq₁, h2, QuaternionGroup.orderOf_a_one]
    obtain ⟨k, hk⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [hk, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega, pow_succ]
    ring
  have hrel : C.relIndex S' = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := C) (K := S')
    rw [inf_eq_left.mpr hCS', hCdef, Nat.card_zpowers, hordc, hcardS'] at h1
    have hpos : 0 < 2 ^ (r - 1) := by positivity
    have h2 : 2 ^ r = 2 * 2 ^ (r - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]
      ring
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (by linarith)
  obtain ⟨y, hyS', hyC⟩ : ∃ y ∈ S', y ∉ C := by
    by_contra hcon
    push Not at hcon
    exact absurd (Subgroup.relIndex_eq_one.mpr (fun y hy => hcon y hy)) (by rw [hrel]; norm_num)
  refine twoSubgroupsFourGenerated_subgroup (genFittingFStar G) ?_
  refine fourGenerated_of_sylow T fun P hPT => ?_
  set P₀ : Subgroup G := P ⊓ Subgroup.centralizer (C : Set G) with hP₀
  set D : Subgroup G := P ⊓ Subgroup.centralizer (S' : Set G) with hD
  have hDP₀ : D ≤ P₀ := inf_le_inf_left P (Subgroup.centralizer_le hCS')
  have hinv : ∀ u ∈ P, u ∉ P₀ → ∀ z ∈ C, u * z * u⁻¹ = z⁻¹ := by
    intro u hu hu0
    rcases hpm' C hCS' hCcyc hrel u (hPT hu) with h1 | h2
    · refine absurd ⟨hu, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩ hu0
      calc z * u = (u * z * u⁻¹) * u := by rw [h1 z hz]
        _ = u * z := by group
    · exact h2
  have hA : ∀ x ∈ P, ∀ x' ∈ P, x ∉ P₀ → x' ∉ P₀ → x⁻¹ * x' ∈ P₀ := by
    intro x hx x' hx' hx0 hx0'
    refine ⟨P.mul_mem (P.inv_mem hx) hx', Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have e1 : x' * z * x'⁻¹ = z⁻¹ := hinv x' hx' hx0' z hz
    have e0 : x * z * x⁻¹ = z⁻¹ := hinv x hx hx0 z hz
    have e3 : x⁻¹ * z⁻¹ * x = z := by rw [← e0]; group
    have key : (x⁻¹ * x') * z * (x⁻¹ * x')⁻¹ = z := by
      calc (x⁻¹ * x') * z * (x⁻¹ * x')⁻¹ = x⁻¹ * (x' * z * x'⁻¹) * x := by group
        _ = x⁻¹ * z⁻¹ * x := by rw [e1]
        _ = z := e3
    calc z * (x⁻¹ * x') = ((x⁻¹ * x') * z * (x⁻¹ * x')⁻¹) * (x⁻¹ * x') := by rw [key]
      _ = (x⁻¹ * x') * z := by group
  have hgc : ∀ g ∈ P₀, ∀ z ∈ C, g * z * g⁻¹ = z := by
    intro g hg z hz
    have h1 : z * g = g * z := Subgroup.mem_centralizer_iff.mp hg.2 z hz
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [h1]
      _ = z := by group
  have hFmem : ∀ g ∈ P₀, g * y * g⁻¹ ∈ S' ∧ g * y * g⁻¹ ∉ C := by
    intro g hg
    have hgT : g ∈ (T : Subgroup G) := hPT hg.1
    have hgN : g ∈ Subgroup.normalizer (tightCore R : Set G) := h.hTN hgT
    have hyT : y ∈ (T : Subgroup G) := hS'T' hyS'
    have h1 : g * y * g⁻¹ ∈ (T : Subgroup G) ⊓ tightCore R :=
      ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hgT hyT) ((T : Subgroup G).inv_mem hgT),
        (Subgroup.mem_normalizer_iff.mp hgN y).mp (hS'K hyS')⟩
    refine ⟨hS'T ▸ h1, fun hcon => hyC ?_⟩
    have h2 : g * y * g⁻¹ * g = g * (g * y * g⁻¹) := by
      have := Subgroup.mem_centralizer_iff.mp hg.2 _ hcon
      exact this
    have h3 : y = g * y * g⁻¹ :=
      calc y = g⁻¹ * (g * y * g⁻¹ * g) := by group
        _ = g⁻¹ * (g * (g * y * g⁻¹)) := by rw [h2]
        _ = g * y * g⁻¹ := by group
    rw [h3]
    exact hcon
  set F : G → G := fun g => y⁻¹ * (g * y * g⁻¹) with hF
  have hFC : ∀ g ∈ P₀, F g ∈ C := fun g hg =>
    inv_mul_mem_of_relIndex_two hrel hyS' (hFmem g hg).1 hyC (hFmem g hg).2
  have hFmul : ∀ g ∈ P₀, ∀ k ∈ P₀, F (g * k) = F g * F k := by
    intro g hg k hk
    have hk' : k * y * k⁻¹ = y * F k := by simp only [hF]; group
    calc F (g * k) = y⁻¹ * (g * (k * y * k⁻¹) * g⁻¹) := by simp only [hF]; group
      _ = y⁻¹ * (g * (y * F k) * g⁻¹) := by rw [hk']
      _ = (y⁻¹ * (g * y * g⁻¹)) * (g * F k * g⁻¹) := by group
      _ = F g * F k := by rw [hgc g hg _ (hFC k hk)]
  have hker : ∀ g ∈ P₀, F g = 1 → g ∈ D := by
    intro g hg hFg
    refine ⟨hg.1, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hgy : g * y * g⁻¹ = y := by
      have h1 : y⁻¹ * (g * y * g⁻¹) = 1 := hFg
      calc g * y * g⁻¹ = y * (y⁻¹ * (g * y * g⁻¹)) := by group
        _ = y := by rw [h1, mul_one]
    by_cases hsC : s ∈ C
    · exact Subgroup.mem_centralizer_iff.mp hg.2 s hsC
    · have hs' : y⁻¹ * s ∈ C := inv_mul_mem_of_relIndex_two hrel hyS' hs hyC hsC
      have h1 : g * s * g⁻¹ = s :=
        calc g * s * g⁻¹ = (g * y * g⁻¹) * (g * (y⁻¹ * s) * g⁻¹) := by group
          _ = y * (y⁻¹ * s) := by rw [hgy, hgc g hg _ hs']
          _ = s := by group
      calc s * g = (g * s * g⁻¹) * g := by rw [h1]
        _ = g * s := by group
  have hDle : D ≤ (T : Subgroup G) ⊓
      Subgroup.centralizer (((T : Subgroup G) ⊓ tightCore R : Subgroup G) : Set G) := by
    intro g hg
    refine ⟨hPT hg.1, ?_⟩
    rw [hS'T]
    exact hg.2
  obtain ⟨s₁, hs₁, hcl₁⟩ := e2Prime_two_generators_of_le hE hDle
  obtain ⟨s₂, hs₂, hcl₂⟩ := exists_closure_of_ker_cyclic (H := P₀) (D := D) (C := C) hDP₀
    hFmul hFC hker ⟨s₁, hs₁, hcl₁⟩
  obtain ⟨s, hs, hcl⟩ := exists_closure_of_index_two (H := P) (H₀ := P₀) inf_le_left hA
    ⟨s₂, hs₂, hcl₂⟩
  exact ⟨s, by omega, hcl⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
