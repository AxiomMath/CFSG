module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.EnKLHeis

public section

namespace CFSG.SeitzReduction.EPilot.HeisIrr

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

section Shift

variable {τ : Tag} (K : Type) [Field K]

@[expose] def shiftRoot (γ : Fin τ.rank → ℤ) (f : (Fin τ.rank → ℤ) → K) :
    (Fin τ.rank → ℤ) → K :=
  fun ν => if ν ∈ rootFinset τ then f (ν - γ) else 0

variable {K}

@[expose] def SupportedDeg1 (g : (Fin τ.rank → ℤ) → K) : Prop :=
  ∀ ν, g ν ≠ 0 → ν ∈ rootFinset τ ∧ ν (iθ τ) = 1

theorem shiftRoot_single {γ μ : Fin τ.rank → ℤ} (h : μ + γ ∈ rootFinset τ) :
    shiftRoot K γ (Pi.single μ (1 : K)) = Pi.single (μ + γ) 1 := by
  funext ν
  simp only [shiftRoot, Pi.single_apply]
  by_cases hν : ν = μ + γ
  · subst hν
    simp [h]
  · have h' : ν - γ ≠ μ := fun e => hν (by rw [← e]; abel)
    simp [hν, h']

theorem pos_sum_of_deg_one (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ ν ∈ rootFinset τ, ν (iθ τ) = 1 → 0 < ∑ i, ν i := by
  rcases hτ with rfl | rfl | rfl <;> decide +kernel

open Classical in
noncomputable def hgt (g : (Fin τ.rank → ℤ) → K) : ℕ :=
  ((rootFinset τ).filter fun ν => g ν ≠ 0).sup fun ν => (∑ i, ν i).toNat

open Classical in
theorem le_hgt {g : (Fin τ.rank → ℤ) → K} {ν : Fin τ.rank → ℤ}
    (hν : ν ∈ rootFinset τ) (h : g ν ≠ 0) : (∑ i, ν i).toNat ≤ hgt g :=
  Finset.le_sup (f := fun ν => (∑ i, ν i).toNat) (Finset.mem_filter.2 ⟨hν, h⟩)

open Classical in
theorem hgt_lt_of_forall {g : (Fin τ.rank → ℤ) → K} {n : ℕ} (hn : 0 < n)
    (h : ∀ ν ∈ rootFinset τ, g ν ≠ 0 → (∑ i, ν i).toNat < n) : hgt g < n :=
  (Finset.sup_lt_iff hn).2 fun ν hν => h ν (Finset.mem_filter.1 hν).1 (Finset.mem_filter.1 hν).2

theorem supportedDeg1_shift_neg {j : Fin τ.rank} (hj : j ≠ iθ τ)
    {g : (Fin τ.rank → ℤ) → K} (hg : SupportedDeg1 g) :
    SupportedDeg1 (shiftRoot K (-Pi.single j 1) g) := by
  intro ν hν
  simp only [shiftRoot] at hν
  by_cases hΦ : ν ∈ rootFinset τ
  · rw [if_pos hΦ] at hν
    obtain ⟨-, h7⟩ := hg _ hν
    refine ⟨hΦ, ?_⟩
    simpa [Pi.single_apply, hj] using h7
  · rw [if_neg hΦ] at hν
    exact absurd rfl hν

private theorem eq_single_of_forall_shift_eq_zero (hK : Nat.card K = 2)
    (hroot : ∀ μ ∈ rootFinset τ, μ (iθ τ) = 1 → μ ≠ Pi.single (iθ τ) 1 →
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ μ - Pi.single j 1 ∈ rootFinset τ)
    {g : (Fin τ.rank → ℤ) → K} (hg0 : g ≠ 0) (hs : SupportedDeg1 g)
    (hall : ∀ j : Fin τ.rank, j ≠ iθ τ → shiftRoot K (-Pi.single j 1) g = 0) :
    g = Pi.single (Pi.single (iθ τ) 1 : Fin τ.rank → ℤ) (1 : K) := by
  classical
  have hK01 : ∀ c : K, c ≠ 0 → c = 1 := fun c hc =>
    ((Nat.card_eq_two_iff' (0 : K)).1 hK).unique hc one_ne_zero
  have hsupp : ∀ ν, g ν ≠ 0 → ν = Pi.single (iθ τ) 1 := by
    intro ν hν
    by_contra hne
    obtain ⟨hνΦ, hν7⟩ := hs ν hν
    obtain ⟨j, hj, hjΦ⟩ := hroot ν hνΦ hν7 hne
    have h0 := congrFun (hall j hj) (ν - Pi.single j 1)
    simp only [shiftRoot, if_pos hjΦ, Pi.zero_apply] at h0
    have : ν - Pi.single j 1 - -Pi.single j 1 = ν := by abel
    rw [this] at h0
    exact hν h0
  obtain ⟨ν₀, hν₀⟩ : ∃ ν, g ν ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg0 (funext hcon)
  have h0 := hsupp ν₀ hν₀
  subst h0
  have hone : g (Pi.single (iθ τ) 1) = 1 := hK01 _ hν₀
  funext ν
  by_cases hν : ν = Pi.single (iθ τ) 1
  · subst hν; simp [hone]
  · rw [Pi.single_apply, if_neg hν]
    by_contra hne
    exact hν (hsupp ν hne)

private theorem exists_shift_lt_hgt (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (W : AddSubgroup ((Fin τ.rank → ℤ) → K))
    (hlow : ∀ j : Fin τ.rank, j ≠ iθ τ → ∀ f ∈ W, shiftRoot K (-Pi.single j 1) f ∈ W)
    {g : (Fin τ.rank → ℤ) → K} (hg : g ∈ W) (hg0 : g ≠ 0) (hs : SupportedDeg1 g)
    (hall : ¬ ∀ j : Fin τ.rank, j ≠ iθ τ → shiftRoot K (-Pi.single j 1) g = 0) :
    ∃ g' ∈ W, g' ≠ 0 ∧ SupportedDeg1 g' ∧ hgt g' < hgt g := by
  classical
  push Not at hall
  obtain ⟨j, hj, hne⟩ := hall
  refine ⟨shiftRoot K (-Pi.single j 1) g, hlow j hj g hg, hne,
    supportedDeg1_shift_neg hj hs, ?_⟩
  obtain ⟨ν₀, hν₀⟩ : ∃ ν, g ν ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg0 (funext hcon)
  obtain ⟨hν₀Φ, hν₀7⟩ := hs ν₀ hν₀
  have hpos0 : 0 < hgt g :=
    lt_of_lt_of_le (by have := pos_sum_of_deg_one hτ ν₀ hν₀Φ hν₀7; omega) (le_hgt hν₀Φ hν₀)
  refine hgt_lt_of_forall hpos0 fun ν hν hSν => ?_
  have hSν' : g (ν + (Pi.single j 1 : Fin τ.rank → ℤ)) ≠ 0 := by
    simpa [shiftRoot, hν] using hSν
  obtain ⟨hμΦ, hμ7⟩ := hs _ hSν'
  have hν7 : ν (iθ τ) = 1 := by
    have : (ν + (Pi.single j 1 : Fin τ.rank → ℤ)) (iθ τ) = ν (iθ τ) := by
      simp [hj]
    omega
  have hp := pos_sum_of_deg_one hτ ν hν hν7
  have hle := le_hgt hμΦ hSν'
  have hsum : ∑ i, (ν + (Pi.single j 1 : Fin τ.rank → ℤ)) i = ∑ i, ν i + 1 := by
    simp [Finset.sum_add_distrib, Pi.single_apply]
  rw [hsum] at hle
  omega

theorem single_mem_of_lowering (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2)
    (hroot : ∀ μ ∈ rootFinset τ, μ (iθ τ) = 1 → μ ≠ Pi.single (iθ τ) 1 →
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ μ - Pi.single j 1 ∈ rootFinset τ)
    (W : AddSubgroup ((Fin τ.rank → ℤ) → K))
    (hlow : ∀ j : Fin τ.rank, j ≠ iθ τ → ∀ f ∈ W, shiftRoot K (-Pi.single j 1) f ∈ W)
    {f : (Fin τ.rank → ℤ) → K} (hf : f ∈ W) (hf0 : f ≠ 0) (hs : SupportedDeg1 f) :
    Pi.single (Pi.single (iθ τ) 1 : Fin τ.rank → ℤ) (1 : K) ∈ W := by
  classical
  suffices H : ∀ n : ℕ, ∀ g ∈ W, g ≠ 0 → SupportedDeg1 g → hgt g = n →
      Pi.single (Pi.single (iθ τ) 1 : Fin τ.rank → ℤ) (1 : K) ∈ W from
    H _ f hf hf0 hs rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hg hg0 hgs hn
    by_cases hall : ∀ j : Fin τ.rank, j ≠ iθ τ → shiftRoot K (-Pi.single j 1) g = 0
    · have hg_eq := eq_single_of_forall_shift_eq_zero hK hroot hg0 hgs hall
      rw [← hg_eq]
      exact hg
    · obtain ⟨g', hg', hg'0, hgs', hlt⟩ :=
        exists_shift_lt_hgt hτ W hlow hg hg0 hgs hall
      exact ih (hgt g') (by rwa [← hn]) g' hg' hg'0 hgs' rfl

theorem single_mem_of_raising (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hroot : ∀ μ ∈ rootFinset τ, μ (iθ τ) = 1 → μ ≠ Pi.single (iθ τ) 1 →
      ∃ j : Fin τ.rank, j ≠ iθ τ ∧ μ - Pi.single j 1 ∈ rootFinset τ)
    (W : AddSubgroup ((Fin τ.rank → ℤ) → K))
    (hhigh : ∀ j : Fin τ.rank, j ≠ iθ τ → ∀ f ∈ W, shiftRoot K (Pi.single j 1) f ∈ W)
    (hbot : Pi.single (Pi.single (iθ τ) 1 : Fin τ.rank → ℤ) (1 : K) ∈ W) :
    ∀ ν ∈ rootFinset τ, ν (iθ τ) = 1 → Pi.single ν (1 : K) ∈ W := by
  suffices H : ∀ n : ℕ, ∀ ν ∈ rootFinset τ, ν (iθ τ) = 1 → (∑ i, ν i).toNat = n →
      Pi.single ν (1 : K) ∈ W from fun ν hν h7 => H _ ν hν h7 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ν hν h7 hn
    by_cases hα : ν = Pi.single (iθ τ) 1
    · rw [hα]; exact hbot
    · obtain ⟨j, hj, hjΦ⟩ := hroot ν hν h7 hα
      have hμ7 : (ν - (Pi.single j 1 : Fin τ.rank → ℤ)) (iθ τ) = 1 := by
        simp [hj, h7]
      have hp := pos_sum_of_deg_one hτ ν hν h7
      have hsum : ∑ i, (ν - (Pi.single j 1 : Fin τ.rank → ℤ)) i = ∑ i, ν i - 1 := by
        simp [Finset.sum_sub_distrib, Pi.single_apply]
      have hlt : (∑ i, (ν - (Pi.single j 1 : Fin τ.rank → ℤ)) i).toNat < n := by
        rw [hsum, ← hn]
        omega
      have h1 := ih _ hlt (ν - (Pi.single j 1 : Fin τ.rank → ℤ)) hjΦ hμ7 rfl
      have h2 := hhigh j hj _ h1
      rw [shiftRoot_single (by simpa using hν), sub_add_cancel] at h2
      exact h2

end Shift

section Coord

variable {τ : Tag} {K : Type} [Field K]

theorem mem_Qθ_of_mem_highRadical (hnode : iθ τ = highNode τ)
    {x : adjointGroup τ K} (hx : x ∈ highRadical τ K) :
    (x : ModGL τ K) ∈ Qθ τ K := by
  have hx' : (x : ModGL τ K) ∈ parabolicRadical τ K (perpNodes τ) :=
    Subgroup.mem_subgroupOf.1 hx
  have hset : perpNodes τ = Jθ τ := by
    ext j
    simp [perpNodes, Jθ, hnode]
  simpa [Qθ, hset] using hx'

noncomputable def coordGroup (hnode : iθ τ = highNode τ)
    (V : Subgroup (adjointGroup τ K))
    (hV : V ≤ highRadical τ K) : AddSubgroup ((Fin τ.rank → ℤ) → K) where
  carrier := {f | ∃ v ∈ V, heisCoord τ K (v : ModGL τ K) = f}
  zero_mem' := ⟨1, one_mem V, heisCoord_one⟩
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v * w, mul_mem hv hw,
      (heisCoord_spec τ K).mul _ (mem_Qθ_of_mem_highRadical hnode (hV hv)) _
        (mem_Qθ_of_mem_highRadical hnode (hV hw))⟩
  neg_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v⁻¹, inv_mem hv,
      heisCoord_inv (mem_Qθ_of_mem_highRadical hnode (hV hv))⟩

theorem supportedDeg1_heisCoord {q : ModGL τ K} (hq : q ∈ Qθ τ K) :
    SupportedDeg1 (heisCoord τ K q) := by
  intro ν hν
  by_contra hcon
  refine hν ((heisCoord_spec τ K).support q hq ν ?_)
  intro hD
  exact hcon ⟨mem_rootFinset.2 hD.1, hD.2⟩

theorem shiftRoot_mem_coordGroup [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hnode : iθ τ = highNode τ) {V : Subgroup (adjointGroup τ K)}
    {hV : V ≤ highRadical τ K}
    (hN : perpLevi τ K ≤ Subgroup.normalizer (V : Set (adjointGroup τ K)))
    {γ : Fin τ.rank → ℤ} (hD : γ ∈ perpRoots τ)
    {f : (Fin τ.rank → ℤ) → K} (hf : f ∈ coordGroup hnode V hV) :
    shiftRoot K γ f ∈ coordGroup hnode V hV := by
  obtain ⟨v, hv, rfl⟩ := hf
  have hD0 : γ (iθ τ) = 0 := by rw [hnode]; exact hD.2
  have hd := hN (pinnedElt_mem_perpLevi hD 1)
  have hu : pinnedElt τ γ (1 : K) * v * (pinnedElt τ γ (1 : K))⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 hd v).1 hv
  have key := (heisCoord_conj_pinnedX_of_deg_zero hτ hD.1 hD0
    (1 : K) (mem_Qθ_of_mem_highRadical hnode (hV hv))).2
  have hshift : shiftRoot K γ (heisCoord τ K (v : ModGL τ K)) =
      heisCoord τ K ((pinnedElt τ γ (1 : K) * v *
        (pinnedElt τ γ (1 : K))⁻¹ : adjointGroup τ K) : ModGL τ K) -
        heisCoord τ K (v : ModGL τ K) := by
    funext ν
    rw [Pi.sub_apply, show ((pinnedElt τ γ (1 : K) * v *
        (pinnedElt τ γ (1 : K))⁻¹ : adjointGroup τ K) : ModGL τ K) =
        pinnedX τ K γ 1 * (v : ModGL τ K) * (pinnedX τ K γ 1)⁻¹ from rfl, key ν]
    simp [shiftRoot]
  rw [hshift]
  exact sub_mem ⟨_, hu, rfl⟩ ⟨v, hv, rfl⟩

theorem mem_zpowers_of_heisCoord_eq_zero (hnode : iθ τ = highNode τ)
    (hK : Nat.card K = 2) {q : adjointGroup τ K}
    (hq : q ∈ highRadical τ K) (h : heisCoord τ K (q : ModGL τ K) = 0) :
    q ∈ Subgroup.zpowers (pinnedElt τ (highRoot τ) (1 : K)) := by
  have hU : (q : ModGL τ K) ∈ Uθ τ K :=
    ((heisCoord_spec τ K).eq_zero_iff _ (mem_Qθ_of_mem_highRadical hnode hq)).1 h
  obtain ⟨c, hc⟩ := CFSG.Blueprint.Chevalley.mem_rootSubgroup.1 hU
  by_cases hc0 : c = 0
  · subst hc0
    rw [pinnedX_zero] at hc
    have hq1 : q = 1 := Subtype.ext hc.symm
    rw [hq1]
    exact one_mem _
  · have hc1 : c = 1 := ((Nat.card_eq_two_iff' (0 : K)).1 hK).unique hc0 one_ne_zero
    subst hc1
    have hqt : pinnedElt τ (highRoot τ) (1 : K) = q := Subtype.ext hc
    rw [← hqt]
    exact Subgroup.mem_zpowers _

private theorem mem_coordGroup_of_supported (hnode : iθ τ = highNode τ)
    (hK : Nat.card K = 2) {V : Subgroup (adjointGroup τ K)}
    {hV : V ≤ highRadical τ K} {c : (Fin τ.rank → ℤ) → K}
    (hcs : SupportedDeg1 c)
    (hall : ∀ ν ∈ rootFinset τ, ν (iθ τ) = 1 →
      Pi.single ν (1 : K) ∈ coordGroup hnode V hV) :
    c ∈ coordGroup hnode V hV := by
  classical
  have hK01 : ∀ a : K, a ≠ 0 → a = 1 := fun a ha =>
    ((Nat.card_eq_two_iff' (0 : K)).1 hK).unique ha one_ne_zero
  have hc : c = ∑ ν ∈ (rootFinset τ).filter (fun ν => c ν ≠ 0),
      (Pi.single ν (1 : K) : (Fin τ.rank → ℤ) → K) := by
    funext μ
    rw [Finset.sum_apply]
    simp only [Pi.single_apply]
    rw [Finset.sum_ite_eq]
    by_cases hμ : c μ = 0
    · have hnm : μ ∉ (rootFinset τ).filter (fun ν => c ν ≠ 0) := fun h =>
        (Finset.mem_filter.1 h).2 hμ
      rw [if_neg hnm, hμ]
    · rw [if_pos (Finset.mem_filter.2 ⟨(hcs μ hμ).1, hμ⟩), hK01 _ hμ]
  rw [hc]
  refine AddSubgroup.sum_mem _ fun ν hν => ?_
  obtain ⟨hνΦ, hμ⟩ := Finset.mem_filter.1 hν
  exact hall ν hνΦ (hcs ν hμ).2

private theorem highRadical_le_of_singles_mem (hnode : iθ τ = highNode τ)
    (hK : Nat.card K = 2) {V : Subgroup (adjointGroup τ K)}
    (h2 : V ≤ highRadical τ K)
    (h1 : Subgroup.zpowers (pinnedElt τ (highRoot τ) (1 : K)) ≤ V)
    (hall : ∀ ν ∈ rootFinset τ, ν (iθ τ) = 1 →
      Pi.single ν (1 : K) ∈ coordGroup hnode V h2) :
    highRadical τ K ≤ V := by
  intro q hq
  set c := heisCoord τ K (q : ModGL τ K) with hcdef
  have hcs : SupportedDeg1 c := supportedDeg1_heisCoord (mem_Qθ_of_mem_highRadical hnode hq)
  have hcW : c ∈ coordGroup hnode V h2 := mem_coordGroup_of_supported hnode hK hcs hall
  obtain ⟨v, hv, hvq⟩ := hcW
  have hqv : heisCoord τ K ((q * v⁻¹ : adjointGroup τ K) : ModGL τ K) = 0 := by
    have hmul := (heisCoord_spec τ K).mul _ (mem_Qθ_of_mem_highRadical hnode hq) _
      (inv_mem (mem_Qθ_of_mem_highRadical hnode (h2 hv)))
    rw [show ((q * v⁻¹ : adjointGroup τ K) : ModGL τ K) =
      (q : ModGL τ K) * (v : ModGL τ K)⁻¹ from rfl, hmul,
      heisCoord_inv (mem_Qθ_of_mem_highRadical hnode (h2 hv)), hvq, ← hcdef]
    exact add_neg_cancel _
  have hmem : q * v⁻¹ ∈ Subgroup.zpowers (pinnedElt τ (highRoot τ) (1 : K)) :=
    mem_zpowers_of_heisCoord_eq_zero hnode hK (mul_mem hq (inv_mem (h2 hv))) hqv
  have hqeq : q = (q * v⁻¹) * v := by group
  rw [hqeq]
  exact mul_mem (h1 hmem) hv

theorem eq_zpowers_or_eq_highRadical [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hnode : iθ τ = highNode τ) (hK : Nat.card K = 2)
    {V : Subgroup (adjointGroup τ K)}
    (h1 : Subgroup.zpowers (pinnedElt τ (highRoot τ) (1 : K)) ≤ V)
    (h2 : V ≤ highRadical τ K)
    (hN : perpLevi τ K ≤ Subgroup.normalizer (V : Set (adjointGroup τ K))) :
    V = Subgroup.zpowers (pinnedElt τ (highRoot τ) (1 : K)) ∨ V = highRadical τ K := by
  classical
  have hroot := exists_sub_single_mem_rootFinset_of_deg_one hτ
  by_cases hV : ∀ v ∈ V, heisCoord τ K (v : ModGL τ K) = 0
  · exact Or.inl (le_antisymm
      (fun v hv => mem_zpowers_of_heisCoord_eq_zero hnode hK (h2 hv) (hV v hv)) h1)
  · right
    push Not at hV
    obtain ⟨v₀, hv₀, hne⟩ := hV
    have hW₀ : heisCoord τ K (v₀ : ModGL τ K) ∈ coordGroup hnode V h2 := ⟨v₀, hv₀, rfl⟩
    have hlow : ∀ j : Fin τ.rank, j ≠ iθ τ → ∀ f ∈ coordGroup hnode V h2,
        shiftRoot K (-Pi.single j 1) f ∈ coordGroup hnode V h2 := fun j hj f hf =>
      shiftRoot_mem_coordGroup hτ hnode hN
        (neg_single_mem_perpRoots (fun h => hj (h.trans hnode.symm))) hf
    have hhigh : ∀ j : Fin τ.rank, j ≠ iθ τ → ∀ f ∈ coordGroup hnode V h2,
        shiftRoot K (Pi.single j 1) f ∈ coordGroup hnode V h2 := fun j hj f hf =>
      shiftRoot_mem_coordGroup hτ hnode hN
        (single_mem_perpRoots (fun h => hj (h.trans hnode.symm))) hf
    have hbot := single_mem_of_lowering hτ hK hroot (coordGroup hnode V h2) hlow hW₀ hne
      (supportedDeg1_heisCoord (mem_Qθ_of_mem_highRadical hnode (h2 hv₀)))
    have hall := single_mem_of_raising hτ hroot (coordGroup hnode V h2) hhigh hbot
    exact le_antisymm h2 (highRadical_le_of_singles_mem hnode hK h2 h1 hall)

end Coord

end CFSG.SeitzReduction.EPilot.HeisIrr
