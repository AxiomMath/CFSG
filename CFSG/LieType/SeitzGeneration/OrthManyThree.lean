module

public import CFSG.LieType.SeitzGeneration.OrthManyThreeRot
public import CFSG.LieType.SeitzGeneration.InnerThreeOrthogonal

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical
  CFSG.Open OrthNS OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Aniso

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)} {P : Submodule K V}

theorem IsPiece.anisotropic_of_orderOf_two_of_ne_two (hP : IsPiece Q E P)
    (hK : KernelLineData Q p E) (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) : ∀ s ∈ P, Q s = 0 → s = 0 := by
  classical
  obtain ⟨M, hM, hPM⟩ := hP.exists_lineSpace_le hK hp hpl
  obtain ⟨a, haM⟩ := exists_notMem_line hK hp hM
  obtain ⟨q, hmon, hirr, hne1, hdvd, ⟨τ, hq, hnoroot⟩, hker⟩ :=
    hP.exists_quadratic hK hp hpl hM hPM h2 haM
  have hτ : τ ≠ 0 := by
    subst hq
    exact manyTwo_tau_ne_zero hp hp2 hmon hirr hdvd hne1
  have hd : finrank K P = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ := hP.exists_line hK hp hp2 hpl
    exact h.trans h2
  set g : V ≃ₗ[K] V := ((a : orthDerived Q) : V ≃ₗ[K] V) with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_mem_orthogonalGroup
  have hrel : ∀ v ∈ P, g (g v) = τ • g v - v := fun v hv => by
    have := hker v hv
    rw [hq] at this
    exact manyTwo_apply_sq_of_aeval g.toLinearMap τ v this
  intro s hsP hsQ
  by_contra hs0
  have hli := manyTwo_linearIndependent_pair hs0 (hrel s hsP) hnoroot
  have hgsP : g s ∈ P := hP.eStable a a.2 s hsP
  have hspan := manyThree_span_pair_eq hd hsP hgsP hli
  have hpol : polar Q s (g s) = 0 := polar_self_apply_eq_zero hgO hτ (hrel s hsP) hsQ
  refine hs0 (hP.regular s hsP fun y hy => ?_)
  rw [← hspan] at hy
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_self_eq_zero hsQ, hpol]
  ring

end Aniso

section Small

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)} {P : Submodule K V}

theorem manyThree_exists_move_of_closure {x y : E} (hcl : Subgroup.closure ({x, y} : Set E) = ⊤)
    (hP : IsPiece Q E P) :
    (∃ u ∈ P, ((x : orthDerived Q) : V ≃ₗ[K] V) u ≠ u) ∨
      (∃ u ∈ P, ((y : orthDerived Q) : V ≃ₗ[K] V) u ≠ u) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hy⟩ := hcon
  let φ : E →* V ≃ₗ[K] V := (orthDerived Q).subtype.comp E.subtype
  have hle : Subgroup.closure ({x, y} : Set E) ≤ (stabPW P).comap φ := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [Subgroup.mem_comap.mpr (mem_stabPW.mpr hx), Subgroup.mem_comap.mpr (mem_stabPW.mpr hy)]
  have hall : ∀ z : E, ∀ u ∈ P, ((z : orthDerived Q) : V ≃ₗ[K] V) u = u := fun z u hu =>
    mem_stabPW.mp (Subgroup.mem_comap.mp (hle (hcl ▸ Subgroup.mem_top z))) u hu
  have hPle : P ≤ planeFixSpace E := fun u hu => by
    refine (CFSG.RankThree.Classical.mem_fixSpace).mpr fun g hg => ?_
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
    exact hall ⟨e, he⟩ u hu
  have hPP : Disjoint P P := hP.disjoint.mono_right hPle
  exact hP.ne_bot (disjoint_self.mp hPP)

theorem manyThree_tau_eq_neg_one {g : V ≃ₗ[K] V} (hg3 : g ^ 3 = 1) {τ : K} {u : V} (hu : u ≠ 0)
    (hrel : g (g u) = τ • g u - u) (hnoroot : ∀ r : K, r ^ 2 - τ * r + 1 ≠ 0) : τ = -1 := by
  have h3 : g (g (g u)) = u := by
    have := congrArg (fun h : V ≃ₗ[K] V => h u) hg3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  have h4 : g (g (g u)) = τ • (τ • g u - u) - g u := by
    rw [hrel, map_sub, map_smul, hrel]
  rw [h3] at h4
  have hli := manyTwo_linearIndependent_pair hu hrel hnoroot
  have key : (τ + 1) • u + (-((τ + 1) * (τ - 1))) • g u = 0 := by
    linear_combination (norm := module) h4
  have := (LinearIndependent.pair_iff.mp hli _ _ key).1
  linear_combination this

theorem manyThree_rel_of_order_three {g : V ≃ₗ[K] V} (hg3 : g ^ 3 = 1) {S : Submodule K V}
    (hst : ∀ u ∈ S, g u ∈ S) (hfix : ∀ u ∈ S, g u = u → u = 0) :
    ∀ u ∈ S, g (g u) = (-1 : K) • g u - u := by
  intro u hu
  have h3 : g (g (g u)) = u := by
    have := congrArg (fun h : V ≃ₗ[K] V => h u) hg3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  have hw : g (g u) + g u + u ∈ S := S.add_mem (S.add_mem (hst _ (hst u hu)) (hst u hu)) hu
  have h0 : g (g u) + g u + u = 0 :=
    hfix _ hw (by rw [map_add, map_add, h3]; abel)
  linear_combination (norm := module) h0

end Small

section Main

theorem closure_eq_top_of_noSingular_two_three {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (hpl : 3 ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2) (hNS : OrthNoInvariantSingular Q E)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod 3) = 2) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  obtain ⟨n, P, hP, hPP, hPV, hPsp⟩ :=
    exists_piece_decomposition hQ hp hp2 hpl E hcomm hexp hcard hNS
  choose M hMc hMP hMk hMf _ _ using fun i => (hP i).exists_line hK hp hp2 hpl
  obtain ⟨a, b, hab⟩ := exists_pieces_diff_lines hK hp hpl hP hPsp (M := M)
    fun i => ⟨hMc i, hMP i⟩
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hH : orthCentralizerSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthCentralizerSpan_le_orthogonalGroup E
  have hdimP : ∀ i, finrank K (P i) = 2 := fun i => (hMf i).trans h2
  have hV0reg : PolarNondegOn Q (planeFixSpace E) := polarNondegOn_planeFixSpace hK
  have haniso : ∀ i, ∀ t ∈ P i, Q t = 0 → t = 0 := fun i =>
    (hP i).anisotropic_of_orderOf_two_of_ne_two hK hp hp2 hpl h2
  have hV02 : finrank K (planeFixSpace E) ≤ 2 := finrank_planeFixSpace_le_two hNS
  have hcount : 7 ≤ finrank K (planeFixSpace E) + 2 * n := by
    have h1 : finrank K V ≤ finrank K ↥(planeFixSpace E ⊔ ⨆ i, P i) := by
      rw [← finrank_top K V]
      exact Submodule.finrank_mono hPsp
    have h3 := Submodule.finrank_add_le_finrank_add_finrank (planeFixSpace E) (⨆ i, P i)
    have h4 := manyTwo_finrank_iSup_fin_le P
    simp only [hdimP, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h4
    omega
  have hEichPair : ∀ i j : Fin n, i ≠ j → ∀ e ∈ P i ⊔ P j, ∀ w ∈ P i ⊔ P j,
      eichler Q e w ∈ orthCentralizerSpan Q E := by
    intro i j hij
    by_cases hM : M i = M j
    · have hle : P i ⊔ P j ≤ planeFixSpace E ⊔ lineSpace (M i) := by
        refine sup_le ((hMP i).trans le_sup_right) ?_
        rw [hM]
        exact (hMP j).trans le_sup_right
      exact fun e he w hw => eichler_mem_span_of_mem_sup hEΩ
        (ne_bot_of_card_prime hp (hMc i)) (hle he) (hle hw)
    · exact eichler_mem_of_pair_pieces hQ hp hK hEΩ hNS (hMc i) (hMc j) hM (hP i) (hP j)
        (hMP i) (hMP j) (hPP i j hij) h2
  obtain ⟨x₀, y₀, τ, hτ, hnoroot, hcl, hx₀, hy₀⟩ :=
    exists_two_mixing_elements_aux hK hp (hMc a) (hMc b) hab (hP a) (hP b) (hMP a) (hMP b) h2
  have hτ1 : τ = -1 := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hP a).ne_bot
    exact manyThree_tau_eq_neg_one (coe_pow_eq_one hK x₀) hu0
      (hx₀ u (Submodule.mem_sup_left hu)) hnoroot
  subst hτ1
  have hZ : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ z : E, z ≠ 1 ∧
      (∀ u ∈ P a ⊔ P b, ((z : orthDerived Q) : V ≃ₗ[K] V) (((z : orthDerived Q) : V ≃ₗ[K] V) u) =
        (-1 : K) • ((z : orthDerived Q) : V ≃ₗ[K] V) u - u) ∧
      ∀ u ∈ P k, ((z : orthDerived Q) : V ≃ₗ[K] V) (((z : orthDerived Q) : V ≃ₗ[K] V) u) =
        (-1 : K) • ((z : orthDerived Q) : V ≃ₗ[K] V) u - u := by
    intro k hka hkb
    have key : ∀ z : E, (∃ u ∈ P k, ((z : orthDerived Q) : V ≃ₗ[K] V) u ≠ u) →
        z ≠ 1 ∧ ∀ u ∈ P k, ((z : orthDerived Q) : V ≃ₗ[K] V)
          (((z : orthDerived Q) : V ≃ₗ[K] V) u) =
          (-1 : K) • ((z : orthDerived Q) : V ≃ₗ[K] V) u - u := fun z hz => by
      refine ⟨fun h1 => ?_, manyThree_rel_of_order_three (coe_pow_eq_one hK z)
        (fun u hu => (hP k).eStable z z.2 u hu) fun u hu hfix =>
          (hP k).eq_zero_of_fixed hK.comm hz hu hfix⟩
      obtain ⟨u, -, hu⟩ := hz
      exact hu (by rw [h1]; rfl)
    rcases manyThree_exists_move_of_closure hcl (hP k) with h | h
    · exact ⟨x₀, (key x₀ h).1, hx₀, (key x₀ h).2⟩
    · exact ⟨y₀, (key y₀ h).1, hy₀, (key y₀ h).2⟩
  have hY : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
      (planeFixSpace E ≠ ⊥ → planeFixSpace E ≤ Y) ∧ OrthSep Q Y (P a ⊔ P b) ∧
      PolarNondegOn Q Y ∧ (∀ e ∈ Y, ∀ w ∈ Y, eichler Q e w ∈ orthCentralizerSpan Q E) ∧
      3 ≤ finrank K Y ∧ (finrank K Y = 3 → (2 : K) ≠ 0) := by
    intro k hka hkb
    have hkab : OrthSep Q (P k) (P a ⊔ P b) :=
      manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb)
    by_cases hV0 : planeFixSpace E = ⊥
    ·
      have hn4 : 4 ≤ n := by
        have : finrank K (planeFixSpace E) = 0 := by rw [hV0]; exact finrank_bot K V
        omega
      obtain ⟨l, hl⟩ := manyTwo_exists_fin_notMem (S := {a, b, k}) (m := 3) (by omega)
        Finset.card_le_three
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      obtain ⟨hla, hlb, hlk⟩ := hl
      have hkl : OrthSep Q (P k) (P l) := hPP k l (Ne.symm hlk)
      have hlab : OrthSep Q (P l) (P a ⊔ P b) :=
        manyTwo_orthSep_sup_right (hPP l a hla) (hPP l b hlb)
      have hdisj := OrthSep.disjoint (hP k).regular hkl
      have hdimY : finrank K ↥(P k ⊔ P l) = 4 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq (P k) (P l)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k, hdimP l] at this
        omega
      exact ⟨P k ⊔ P l, le_sup_left, fun h => absurd hV0 h, manyTwo_orthSep_sup_left hkab hlab,
        polarNondegOn_sup (hP k).regular (hP l).regular hkl,
        hEichPair k l (Ne.symm hlk), by omega, fun h => absurd h (by omega)⟩
    ·
      have hd0 : 1 ≤ finrank K (planeFixSpace E) := Submodule.one_le_finrank_iff.mpr hV0
      have hdisj := (hP k).disjoint.symm
      have hdimY : finrank K ↥(planeFixSpace E ⊔ P k) = finrank K (planeFixSpace E) + 2 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq (planeFixSpace E) (P k)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k] at this
        omega
      have hle : planeFixSpace E ⊔ P k ≤ planeFixSpace E ⊔ lineSpace (M k) :=
        sup_le le_sup_left ((hMP k).trans le_sup_right)
      refine ⟨planeFixSpace E ⊔ P k, le_sup_right, fun _ => le_sup_left,
        manyTwo_orthSep_sup_left (manyTwo_orthSep_sup_right (hPV a) (hPV b)) hkab,
        polarNondegOn_sup hV0reg (hP k).regular (hPV k),
        fun e he w hw => eichler_mem_span_of_mem_sup hEΩ (ne_bot_of_card_prime hp (hMc k))
          (hle he) (hle hw), by omega, fun h3 => ?_⟩
      exact two_ne_zero_of_finrank_planeFixSpace hK (by omega)
  have hRoot : ∀ s ∈ P a ⊔ P b, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthCentralizerSpan Q E) s := by
    intro s hs hs0 hsQ
    have hrel : ∀ w ∈ P a ⊔ P b, polar Q s w = 0 → w ∈ rootSet Q (orthCentralizerSpan Q E) s :=
      fun w hw hsw => ⟨hsw, hEichPair a b hab' s hs w hw⟩
    have hYR : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
        (planeFixSpace E ≠ ⊥ → planeFixSpace E ≤ Y) ∧
        ∀ y ∈ Y, y ∈ rootSet Q (orthCentralizerSpan Q E) s := by
      intro k hka hkb
      obtain ⟨Y, hPY, hV0Y, hYP, hYreg, hYH, hY3, h2Y⟩ := hY k hka hkb
      have hsY : ∀ y ∈ Y, polar Q s y = 0 := fun y hy => by
        rw [polar_comm]
        exact hYP y hy s hs
      obtain ⟨z, hz1, hzab, hzk⟩ := hZ k hka hkb
      have hz1' : (z : orthDerived Q) ≠ 1 := fun h => hz1 (Subtype.ext h)
      have hmix := exists_mixed_vector_rot hH (g := ((z : orthDerived Q) : V ≃ₗ[K] V))
        orthDerived_mem_orthogonalGroup
        (fun A hA h1 h2' hmove => rot_mem_orthCentralizerSpan hQ hT z.2 hz1'
          (Nat.odd_iff.mpr rfl) (coe_pow_eq_one hK z) hA h1 h2' hmove)
        (neg_ne_zero.mpr one_ne_zero) hnoroot (P₁ := P a) (P₂ := P b) (P₃ := P k)
        (hP a).regular (hP k).regular (hPP a b hab') (hPP a k (Ne.symm hka))
        (hPP b k (Ne.symm hkb)) (hdimP a) (hdimP k) (haniso b)
        (fun u hu => (hP a).eStable z z.2 u hu) (fun u hu => (hP b).eStable z z.2 u hu)
        (fun u hu => (hP k).eStable z z.2 u hu)
        (fun u hu => hzab u (Submodule.mem_sup_left hu))
        (fun u hu => hzab u (Submodule.mem_sup_right hu)) hzk hPY hYP hs hs0 hsQ hrel
      exact ⟨Y, hPY, hV0Y, manyTwo_subset_rootSet_of_pivot hH hYreg hY3 h2Y hYH hsY hmix⟩
    refine ⟨hs0, hsQ, fun w hsw => ?_⟩
    have hspan : (⊤ : Submodule K V) ≤ (P a ⊔ P b) ⊔
        (planeFixSpace E ⊔ ⨆ k : {k : Fin n // k ≠ a ∧ k ≠ b}, P k.1) := by
      refine hPsp.trans (sup_le ?_ (iSup_le fun i => ?_))
      · exact le_sup_of_le_right le_sup_left
      · by_cases hia : i = a
        · rw [hia]
          exact le_sup_of_le_left le_sup_left
        by_cases hib : i = b
        · rw [hib]
          exact le_sup_of_le_left le_sup_right
        · exact le_sup_of_le_right (le_sup_of_le_right
            (le_iSup (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1) ⟨i, hia, hib⟩))
    obtain ⟨w₁, hw₁, z, hz, rfl⟩ := Submodule.mem_sup.mp (hspan (Submodule.mem_top (x := w)))
    have hzR : polar Q s z = 0 ∧ z ∈ rootSet Q (orthCentralizerSpan Q E) s := by
      obtain ⟨v₀, hv₀, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
      have hv₀perp : polar Q s v₀ = 0 := by
        rw [polar_comm]
        exact manyTwo_orthSep_sup_right (hPV a) (hPV b) v₀ hv₀ s hs
      have hz'R : polar Q s z' = 0 ∧ z' ∈ rootSet Q (orthCentralizerSpan Q E) s := by
        refine Submodule.iSup_induction (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1)
          (motive := fun x => polar Q s x = 0 ∧ x ∈ rootSet Q (orthCentralizerSpan Q E) s) hz'
          ?_ ⟨polar_zero_right Q s, AddSubgroup.zero_mem _⟩ ?_
        · rintro ⟨k, hka, hkb⟩ x hx
          obtain ⟨Y, hPY, -, hYR'⟩ := hYR k hka hkb
          refine ⟨?_, hYR' x (hPY hx)⟩
          rw [polar_comm]
          exact manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb) x hx s hs
        · rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
          exact ⟨by rw [polar_add_right, hx1, hy1, add_zero], AddSubgroup.add_mem _ hx2 hy2⟩
      have hv₀R : v₀ ∈ rootSet Q (orthCentralizerSpan Q E) s := by
        by_cases hV0 : planeFixSpace E = ⊥
        · rw [hV0] at hv₀
          rw [(Submodule.mem_bot K).mp hv₀]
          exact AddSubgroup.zero_mem _
        · have hn3 : 2 < n := by omega
          obtain ⟨k, hk⟩ := manyTwo_exists_fin_notMem (S := {a, b}) (m := 2) hn3
            Finset.card_le_two
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          obtain ⟨Y, -, hV0Y, hYR'⟩ := hYR k hk.1 hk.2
          exact hYR' v₀ (hV0Y hV0 hv₀)
      exact ⟨by rw [polar_add_right, hv₀perp, hz'R.1, add_zero],
        AddSubgroup.add_mem _ hv₀R hz'R.2⟩
    have hw₁perp : polar Q s w₁ = 0 := by
      rw [polar_add_right, hzR.1, add_zero] at hsw
      exact hsw
    exact (AddSubgroup.add_mem _ (hrel w₁ hw₁ hw₁perp) hzR.2).2
  have hXreg : PolarNondegOn Q (P a ⊔ P b) :=
    polarNondegOn_sup (hP a).regular (hP b).regular (hPP a b hab')
  have hX3 : 3 ≤ finrank K ↥(P a ⊔ P b) := by
    have hdisj := OrthSep.disjoint (hP a).regular (hPP a b hab')
    have := Submodule.finrank_sup_add_finrank_inf_eq (P a) (P b)
    rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP a, hdimP b] at this
    omega
  obtain ⟨u, huX, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) hX3
  obtain ⟨u', hu'X, hu'Q, huu'⟩ := exists_partner_of_polarNondegOn hXreg huX hu0 huQ
  have hu'0 : u' ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at huu'
    exact zero_ne_one huu'
  have hle : elementaryGroup Q ≤ orthCentralizerSpan Q E :=
    elementaryGroup_le_of_hypPair hQ hH ⟨u, u', huQ, hu'Q, huu'⟩ (hRoot u huX hu0 huQ)
      (hRoot u' hu'X hu'0 hu'Q)
  exact closure_centralizers_eq_top_of_le E
    ((orthDerived_eq_and_le_closure hQ hT).1.le.trans hle)

end Main

section Master

theorem manyThree_not_three_dvd_card {K : Type} [Field K] [Finite K] (hpl : 3 ≠ ringChar K) :
    ¬ 3 ∣ Nat.card K := by
  classical
  intro h3
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard] at h3
  exact hpl ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
    (Nat.prime_three.dvd_of_dvd_pow h3))

theorem orthMasterNoSingularThree {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (hpl : 3 ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2) (hNS : OrthNoInvariantSingular Q E) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  obtain ⟨he2, -⟩ := noSingular_ord hQ Nat.prime_three (by norm_num) hpl E hcomm hexp hcard hNS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ((Nat.card K : ℕ) : ZMod 3) ≠ 0 := fun h0 =>
    manyThree_not_three_dvd_card hpl ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  have hle : orderOf ((Nat.card K : ℕ) : ZMod 3) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hne))
  exact closure_eq_top_of_noSingular_two_three Q hQ hT hdim hpl E hcomm hexp hcard hNS
    (by omega)

theorem orthMasterThree : OrthMasterThree := by
  intro K V _ _ _ _ _ Q hQ hT hdim hpl E hcomm hexp hcard
  by_cases hNS : OrthNoInvariantSingular Q E
  · exact orthMasterNoSingularThree Q hQ hT hdim hpl E hcomm hexp hcard hNS
  · unfold OrthNoInvariantSingular at hNS
    push Not at hNS
    obtain ⟨W, hWst, hWsing, hW0⟩ := hNS
    exact orthPlaneGen_three_of_singular_stable Q hQ hT hpl E hcomm hexp hcard
      ⟨W, hW0, hWsing, hWst⟩

theorem seitzInnerThreeOrthogonal : SeitzInnerThreeOrthogonal :=
  seitzInnerThreeOrthogonal_of_master orthMasterThree

end Master

end CFSG.LieType.SeitzGeneration
