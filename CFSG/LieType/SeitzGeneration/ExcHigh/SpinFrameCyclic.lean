module

public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinFrameToral

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Models.OrthogonalPairs
  QuadraticMap Matrix CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.LieType.Universal.Spin
  CFSG.LieType.SeitzGeneration OrthBlk CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryMixing CFSG.RankThree.Classical
open CFSG.RankThree.Classical2 (orthDerived)
open scoped MatrixGroups

section Decomposition

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] in
theorem exists_goodPlanes_of_decomposition {S : Set (V ≃ₗ[K] V)} {n k : ℕ}
    {P : Fin n → Submodule K V} {V₀ : Submodule K V}
    (hPreg : ∀ i, PolarNondegOn Q (P i)) (hPdim : ∀ i, Module.finrank K ↥(P i) = 2)
    (hPan : ∀ i, ∀ s ∈ P i, Q s = 0 → s = 0)
    (hPP : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, polar Q x y = 0)
    (hV0reg : PolarNondegOn Q V₀) (hV0an : ∀ s ∈ V₀, Q s = 0 → s = 0)
    (hV0dim : Module.finrank K ↥V₀ ≤ 2)
    (hV0P : ∀ i, ∀ x ∈ V₀, ∀ y ∈ P i, polar Q x y = 0)
    (hPsp : ⊤ ≤ V₀ ⊔ ⨆ i, P i) (hk : Module.finrank K V = 4 * k)
    (hPst : ∀ g ∈ S, ∀ i, ∀ x ∈ P i, g x ∈ P i) (hV0st : ∀ g ∈ S, ∀ x ∈ V₀, g x ∈ V₀) :
    ∃ Pl : Fin (2 * k) → Submodule K V, GoodPlanes Q S Pl := by
  classical
  let Pl₀ : Fin (n + 1) → Submodule K V := Fin.snoc (α := fun _ => Submodule K V) P V₀
  have hPl₀reg : ∀ i, PolarNondegOn Q (Pl₀ i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Pl₀] using hV0reg
    · simpa [Pl₀] using hPreg j
  have hl : Pl₀ (Fin.last n) = V₀ := by simp [Pl₀]
  have hc : ∀ i : Fin n, Pl₀ i.castSucc = P i := fun i => by simp [Pl₀]
  have hPl₀orth : ∀ i j, i ≠ j → ∀ x ∈ Pl₀ i, ∀ y ∈ Pl₀ j, polar Q x y = 0 := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · intro x hx y hy
      rw [hc] at hx hy
      exact hPP i' j' (fun h => hij (by rw [h])) x hx y hy
    · intro x hx y hy
      rw [hc] at hx
      rw [hl] at hy
      rw [polar_comm]
      exact hV0P i' y hy x hx
    · intro x hx y hy
      rw [hl] at hx
      rw [hc] at hy
      exact hV0P j' x hx y hy
    · exact absurd rfl hij
  have hPl₀span : ⨆ i, Pl₀ i = ⊤ := by
    rw [eq_top_iff]
    refine hPsp.trans (sup_le ?_ (iSup_le fun i => ?_))
    · exact le_iSup_of_le (Fin.last n) (by simp [Pl₀])
    · exact le_iSup_of_le i.castSucc (by simp [Pl₀])
  obtain ⟨-, hsum⟩ := polarNondegOn_iSup_fin Pl₀ hPl₀reg hPl₀orth
  rw [hPl₀span, finrank_top, hk, Fin.sum_univ_castSucc] at hsum
  have hsum' : 4 * k = 2 * n + Module.finrank K ↥V₀ := by
    have hfin : ∀ i : Fin n, Module.finrank K ↥(Pl₀ i.castSucc) = 2 := fun i => by
      rw [hc]; exact hPdim i
    have hfinl : Module.finrank K ↥(Pl₀ (Fin.last n)) = Module.finrank K ↥V₀ := by
      rw [hl]
    rw [Finset.sum_congr rfl (fun i _ => hfin i), hfinl, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hsum
    omega
  rcases (show Module.finrank K ↥V₀ = 0 ∨ Module.finrank K ↥V₀ = 2 by omega) with h0 | h2
  ·
    have hbot : V₀ = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hPspan : ⨆ i, P i = ⊤ := by
      rw [eq_top_iff]
      refine hPsp.trans (sup_le ?_ le_rfl)
      rw [hbot]
      exact bot_le
    have hg : GoodPlanes Q S P :=
      ⟨hPreg, hPdim, hPan, fun i j hij => hPP i j hij, hPspan, hPst⟩
    exact ⟨_, hg.congr (show n = 2 * k by omega)⟩
  · have hg : GoodPlanes Q S Pl₀ := by
      refine ⟨hPl₀reg, ?_, ?_, hPl₀orth, hPl₀span, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [hl]; exact h2
        · rw [hc]; exact hPdim j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [hl]; exact hV0an
        · rw [hc]; exact hPan j
      · intro g hg i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [hl]; exact hV0st g hg
        · rw [hc]; exact hPst g hg j
    exact ⟨_, hg.congr (show n + 1 = 2 * k by omega)⟩

end Decomposition

section Cyclic

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {g : V ≃ₗ[K] V}

omit [Finite K] in
theorem exists_minimal_stable_cyc {U : Submodule K V} (hU : U ≠ ⊥) (hUg : ∀ x ∈ U, g x ∈ U) :
    ∃ S : Submodule K V, S ≤ U ∧ S ≠ ⊥ ∧ (∀ x ∈ S, g x ∈ S) ∧
      ∀ S' : Submodule K V, S' ≤ S → (∀ x ∈ S', g x ∈ S') → S' = ⊥ ∨ S' = S := by
  obtain ⟨S, ⟨hSU, hS0, hSst⟩, hSmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min
    {S | S ≤ U ∧ S ≠ ⊥ ∧ ∀ x ∈ S, g x ∈ S} ⟨U, le_rfl, hU, hUg⟩
  refine ⟨S, hSU, hS0, hSst, fun S' hS'S hS'st => ?_⟩
  by_cases hS'0 : S' = ⊥
  · exact Or.inl hS'0
  · right
    by_contra hne
    exact hSmin S' ⟨hS'S.trans hSU, hS'0, hS'st⟩ (lt_of_le_of_ne hS'S hne)

omit [Finite K] [FiniteDimensional K V] in
theorem perp_stable_cyc (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1)
    (hp : 0 < p) {S : Submodule K V} (hS : ∀ x ∈ S, g x ∈ S) :
    ∀ y ∈ perp Q S, g y ∈ perp Q S := by
  intro y hy
  rw [mem_perp] at hy ⊢
  intro s hs
  have hu : (g ^ (p - 1)) s ∈ S := OrthBlk.pow_apply_mem hS (p - 1) s hs
  have hgu : g ((g ^ (p - 1)) s) = s := by
    rw [← LinearEquiv.mul_apply, ← pow_succ', Nat.sub_add_cancel hp, hgp]
    rfl
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO ((g ^ (p - 1)) s) y
  rw [hgu] at h1
  rw [h1]
  exact hy _ hu

omit [Finite K] [FiniteDimensional K V] in
theorem polarNondegOn_of_minimal_cyc (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgp : g ^ p = 1) (hp : 0 < p)
    (hNS : ∀ T : Submodule K V, (∀ x ∈ T, g x ∈ T) → (∀ x ∈ T, Q x = 0) → T = ⊥)
    {S : Submodule K V} (hS0 : S ≠ ⊥) (hSfix : ∀ s ∈ S, g s = s → s = 0)
    (hst : ∀ x ∈ S, g x ∈ S)
    (hmin : ∀ S' : Submodule K V, S' ≤ S → (∀ x ∈ S', g x ∈ S') → S' = ⊥ ∨ S' = S) :
    PolarNondegOn Q S := by
  classical
  have hperp : ∀ y ∈ perp Q S, g y ∈ perp Q S := perp_stable_cyc hgO hgp hp hst
  have hR : ∀ x ∈ S ⊓ perp Q S, g x ∈ S ⊓ perp Q S := fun x hx => ⟨hst x hx.1, hperp x hx.2⟩
  rcases hmin _ inf_le_left hR with hR0 | hRS
  · intro x hxS hx
    have hxR : x ∈ S ⊓ perp Q S :=
      ⟨hxS, mem_perp.mpr fun s hs => by rw [polar_comm]; exact hx s hs⟩
    rw [hR0] at hxR
    exact (Submodule.mem_bot K).mp hxR
  · exfalso
    have hSS : ∀ s ∈ S, ∀ t ∈ S, polar Q s t = 0 := fun s hs t ht => by
      have ht' : t ∈ S ⊓ perp Q S := by rw [hRS]; exact ht
      exact mem_perp.mp ht'.2 s hs
    let S₀ : Submodule K V :=
      { carrier := {s | s ∈ S ∧ Q s = 0}
        add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, by
          rw [QuadraticMap.map_add Q a b, ha.2, hb.2, hSS a ha.1 b hb.1]; simp⟩
        zero_mem' := ⟨S.zero_mem, QuadraticMap.map_zero Q⟩
        smul_mem' := fun c a ha => ⟨S.smul_mem c ha.1, by
          rw [map_smul_eq_sq, ha.2, mul_zero]⟩ }
    have hS₀st : ∀ x ∈ S₀, g x ∈ S₀ := fun x hx =>
      ⟨hst x hx.1, by rw [map_of_mem hgO, hx.2]⟩
    rcases hmin S₀ (fun s hs => hs.1) hS₀st with h0 | hfull
    · obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
      have hgs : g s ≠ s := fun h => hs0 (hSfix s hsS h)
      have hQ2 : (2 : K) * Q s = 0 := by rw [← polar_self_eq_two_mul]; exact hSS s hsS s hsS
      have hd : g s - s ∈ S₀ := by
        refine ⟨S.sub_mem (hst s hsS) hsS, ?_⟩
        rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right,
          map_of_mem hgO, hSS _ (hst s hsS) s hsS]
        linear_combination hQ2
      rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
      exact hgs hd
    · refine hS0 (hNS S hst fun v hv => ?_)
      have hv' : v ∈ S₀ := by rw [hfull]; exact hv
      exact hv'.2

@[expose] def IsPieceCyc (Q : QuadraticForm K V) (g : V ≃ₗ[K] V) (P : Submodule K V) : Prop :=
  P ≠ ⊥ ∧ PolarNondegOn Q P ∧ (∀ x ∈ P, g x ∈ P) ∧
    ∀ S : Submodule K V, S ≤ P → (∀ x ∈ S, g x ∈ S) → S = ⊥ ∨ S = P

omit [Finite K] in
theorem exists_pieces_cyc (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1)
    (hp : 0 < p)
    (hNS : ∀ T : Submodule K V, (∀ x ∈ T, g x ∈ T) → (∀ x ∈ T, Q x = 0) → T = ⊥) :
    ∀ (n : ℕ) (W : Submodule K V), Module.finrank K W = n → (∀ x ∈ W, g x ∈ W) →
      PolarNondegOn Q W → (∀ w ∈ W, g w = w → w = 0) →
      ∃ (m : ℕ) (P : Fin m → Submodule K V), (∀ i, IsPieceCyc Q g (P i)) ∧
        (∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, polar Q x y = 0) ∧ (∀ i, P i ≤ W) ∧
          W ≤ ⨆ i, P i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hWst hWreg hWfix
  by_cases hW0 : W = ⊥
  · exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [hW0]⟩
  obtain ⟨S, hSW, hS0, hSst, hSmin⟩ := exists_minimal_stable_cyc hW0 hWst
  have hSfix : ∀ s ∈ S, g s = s → s = 0 := fun s hs h => hWfix s (hSW hs) h
  have hSreg : PolarNondegOn Q S :=
    polarNondegOn_of_minimal_cyc hgO hgp hp hNS hS0 hSfix hSst hSmin
  set W' : Submodule K V := W ⊓ perp Q S with hW'
  have hW'st : ∀ x ∈ W', g x ∈ W' := fun x hx =>
    ⟨hWst x hx.1, perp_stable_cyc hgO hgp hp hSst x hx.2⟩
  have hW'reg : PolarNondegOn Q W' := polarNondegOn_inf_perp hWreg hSreg hSW
  have hW'fix : ∀ w ∈ W', g w = w → w = 0 := fun w hw h => hWfix w hw.1 h
  have hlt : Module.finrank K W' < n := by
    rw [← hn]
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => ?_)
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    have : s ∈ W' := by rw [h]; exact hSW hsS
    exact hs0 (hSreg s hsS fun t ht => by rw [polar_comm]; exact mem_perp.mp this.2 t ht)
  obtain ⟨m, P', hP'piece, hP'orth, hP'le, hP'sp⟩ :=
    ih _ hlt W' rfl hW'st hW'reg hW'fix
  have hSpiece : IsPieceCyc Q g S := ⟨hS0, hSreg, hSst, hSmin⟩
  refine ⟨m + 1, Fin.cons S P', ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hSpiece
    · simpa using hP'piece j
  · intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · exact absurd rfl hij
    · intro s hs t ht
      simp only [Fin.cons_zero, Fin.cons_succ] at hs ht
      exact mem_perp.mp (hP'le j' ht).2 s hs
    · intro s hs t ht
      simp only [Fin.cons_zero, Fin.cons_succ] at hs ht
      rw [polar_comm]
      exact mem_perp.mp (hP'le i' hs).2 t ht
    · simp only [Fin.cons_succ]
      exact hP'orth i' j' fun h => hij (by rw [h])
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hSW
    · simpa using (hP'le j).trans inf_le_left
  · intro w hw
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_add_inf_perp hSreg hSW hw
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_iSup_of_mem (0 : Fin (m + 1)) (by simpa using ha)
    · have hr' : r ∈ ⨆ j, P' j := hP'sp hr
      refine (iSup_le fun j => ?_ : (⨆ j, P' j) ≤ ⨆ i, (Fin.cons S P' : Fin (m + 1) → _) i) hr'
      exact le_iSup_of_le j.succ (by simp)

open Polynomial in
theorem IsPieceCyc.finrank_eq_orderOf {P : Submodule K V} (hP : IsPieceCyc Q g P)
    (hp : p.Prime) (hpl : p ≠ ringChar K) (hgp : g ^ p = 1)
    (hfix : ∀ s ∈ P, g s = s → s = 0) :
    Module.finrank K P = orderOf ((Nat.card K : ℕ) : ZMod p) := by
  classical
  set T : Module.End K V := g.toLinearMap with hT
  have hTP : ∀ x ∈ P, T x ∈ P := hP.2.2.1
  haveI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hP.1
  have hTp : T ^ p = 1 := by
    rw [hT, ← toLinearMap_pow, hgp]
    rfl
  have hpow : T.restrict hTP ^ p = 1 := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    rw [coe_pow_of_intertwine (A := T.restrict hTP) (B := T) (fun u => rfl), hTp]
    rfl
  have hfix' : ∀ v : P, T.restrict hTP v = v → v = 0 := by
    intro v hv
    exact Subtype.ext (hfix v v.2 (congrArg Subtype.val hv))
  have hsimple : ∀ S : Submodule K P, (∀ s ∈ S, T.restrict hTP s ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hSa : ∀ s ∈ S.map P.subtype, g s ∈ S.map P.subtype := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨T.restrict hTP s, hS s hs, rfl⟩
    rcases hP.2.2.2 (S.map P.subtype) (Submodule.map_subtype_le P S) hSa with h0 | h1
    · left
      rw [eq_bot_iff]
      intro s hs
      have : (s : V) ∈ S.map P.subtype := ⟨s, hs, rfl⟩
      rw [h0] at this
      exact Subtype.ext ((Submodule.mem_bot K).mp this)
    · right
      rw [eq_top_iff]
      intro s _
      have : (s : V) ∈ S.map P.subtype := by rw [h1]; exact s.2
      obtain ⟨t, ht, hts⟩ := this
      have : t = s := Subtype.ext hts
      rwa [← this]
  obtain ⟨h, hmon, hirr, hdvd, hne1, hgh, hfin⟩ :=
    exists_irreducible_of_simple_endomorphism hp.pos (T.restrict hTP) hpow hfix' hsimple
  rw [hfin]
  exact natDegree_eq_orderOf_of_dvd hp hpl hmon hirr hdvd hne1

theorem IsPieceCyc.anisotropic {P : Submodule K V} (hP : IsPieceCyc Q g P)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgp : g ^ p = 1) (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (hdim : Module.finrank K P = 2) (hfix : ∀ s ∈ P, g s = s → s = 0) :
    ∀ s ∈ P, Q s = 0 → s = 0 := by
  classical
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega : p ≠ 2)
  have hfix2 : ∀ u ∈ P, (g ^ 2) u = u → u = 0 := by
    intro u hu h
    apply hfix u hu
    have h1 : g = (g ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      have h3 : 2 * (k + 1) = p + 1 := by omega
      rw [h3, pow_succ, hgp, one_mul]
    have h4 := OrthBlk.pow_apply_of_fixed h (k + 1)
    rw [← h1] at h4
    exact h4
  have hg2p : (g ^ 2) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hgp, one_pow]
  have hgg : ∀ u, (g ^ 2) u = g (g u) := fun u => by rw [pow_two]; rfl
  intro s hsP hsQ
  by_contra hs0
  by_cases h1 : ∃ c : K, g s = c • s
  · obtain ⟨c, hc⟩ := h1
    exact false_of_eigenvector hp h2 hgp hs0 hc (fun h => hs0 (hfix s hsP h))
  push Not at h1
  set t : V := g s with ht
  have htP : t ∈ P := hP.2.2.1 s hsP
  have hQt : Q t = 0 := by rw [ht, map_of_mem hgO, hsQ]
  have ht0 : t ≠ 0 := fun h => hs0 (by
    have : g s = 0 := h
    exact (map_eq_zero_iff _ g.injective).mp this)
  have hli : LinearIndependent K ![s, t] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    by_cases hβ : β = 0
    · rw [hβ, zero_smul, add_zero] at hαβ
      exact ⟨(smul_eq_zero.mp hαβ).resolve_right hs0, hβ⟩
    · exfalso
      apply h1 (-(α / β))
      have : β • t = -(α • s) := eq_neg_of_add_eq_zero_right hαβ
      calc t = β⁻¹ • (β • t) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
        _ = (-(α / β)) • s := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hspan : Submodule.span K {s, t} = P := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
    · rintro x (rfl | rfl)
      exacts [hsP, htP]
    · have hr : Set.range ![s, t] = {s, t} := by
        ext x
        simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
      have := finrank_span_eq_card hli
      rw [hr] at this
      rw [hdim, this]
      simp
  have hpst : polar Q s t ≠ 0 := by
    intro h0
    refine hs0 (hP.2.1 s hsP fun y hy => ?_)
    rw [← hspan] at hy
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_self_eq_zero hsQ, h0]
    ring
  have hgtP : g t ∈ P := hP.2.2.1 t htP
  rw [← hspan] at hgtP
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hgtP
  have hQgt : Q (g t) = 0 := by rw [map_of_mem hgO, hQt]
  rw [← hαβ, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hsQ, hQt,
    polar_smul_left_eq, polar_smul_right_eq] at hQgt
  have hαβ0 : α * β * polar Q s t = 0 := by linear_combination hQgt
  rcases mul_eq_zero.mp hαβ0 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · subst h4
      refine false_of_eigenvector hp h2 hgp ht0 (c := β) ?_ (fun h => ht0 (hfix t htP h))
      rw [← hαβ, zero_smul, zero_add]
    · subst h4
      refine false_of_eigenvector hp h2 hg2p hs0 (c := α) ?_ (fun h => hs0 (hfix2 s hsP h))
      rw [hgg, ← ht, ← hαβ, zero_smul, add_zero]
  · exact hpst h3

theorem exists_goodPlanes_cyclic (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1)
    (hNS : ∀ T : Submodule K V, (∀ x ∈ T, g x ∈ T) → (∀ x ∈ T, Q x = 0) → T = ⊥)
    {k : ℕ} (hk : Module.finrank K V = 4 * k) :
    ∃ Pl : Fin (2 * k) → Submodule K V, GoodPlanes Q {h | ∃ i : ℕ, h = g ^ i} Pl := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_ne_ringChar hp hpl
  have hTop : PolarNondegOn Q ⊤ := fun x _ hxy =>
    eq_zero_of_polar_eq_zero hQ fun v => hxy v Submodule.mem_top
  have hstTop : ∀ s ∈ (⊤ : Submodule K V), g s ∈ (⊤ : Submodule K V) := fun _ _ =>
    Submodule.mem_top
  set V₀ : Submodule K V := OrthBlk.fixIn g ⊤ with hV₀
  set W : Submodule K V := OrthBlk.normKer g p ⊤ with hW
  have hV₀reg : PolarNondegOn Q V₀ := OrthBlk.polarNondegOn_fixIn hgO hgp hpK hTop hstTop
  have hWreg : PolarNondegOn Q W := OrthBlk.polarNondegOn_normKer hgO hgp hpK hTop hstTop
  have hWst : ∀ x ∈ W, g x ∈ W := OrthBlk.normKer_stable (Commute.refl g) hstTop
  have hWfix : ∀ w ∈ W, g w = w → w = 0 := fun w hw h =>
    Submodule.disjoint_def.mp (OrthBlk.disjoint_fixIn_normKer hpK (g := g) ⊤) w
      (OrthBlk.mem_fixIn.mpr ⟨Submodule.mem_top, h⟩) hw
  obtain ⟨m, P, hP, hPP, hPle, hPsp⟩ :=
    exists_pieces_cyc hgO hgp hp.pos hNS _ W rfl hWst hWreg hWfix
  have hPfix : ∀ i, ∀ s ∈ P i, g s = s → s = 0 := fun i s hs h => hWfix s (hPle i hs) h
  have hPdim : ∀ i, Module.finrank K ↥(P i) = 2 := fun i =>
    ((hP i).finrank_eq_orderOf hp hpl hgp (hPfix i)).trans hord
  have hV0an : ∀ s ∈ V₀, Q s = 0 → s = 0 := fun s hs hsQ => by
    have hgs : g s = s := (OrthBlk.mem_fixIn.mp hs).2
    have := hNS (Submodule.span K {s}) (fun x hx => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hgs]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s))
      (fun x hx => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul_eq_sq, hsQ, mul_zero])
    simpa using Submodule.span_singleton_eq_bot.mp this
  refine exists_goodPlanes_of_decomposition (P := P) (V₀ := V₀)
    (S := {h | ∃ i : ℕ, h = g ^ i}) (fun i => (hP i).2.1) hPdim
    (fun i => (hP i).anisotropic hp hp5 hgO hgp hord (hPdim i) (hPfix i))
    hPP hV₀reg hV0an ?_ (fun i x hx y hy => OrthBlk.polar_fixIn_normKer hgO hpK
      (OrthBlk.mem_fixIn.mp hx).2 (OrthBlk.mem_normKer.mp (hPle i hy)).2) ?_ hk ?_ ?_
  · by_contra h
    push Not at h
    obtain ⟨x, hx, hx0, hxQ⟩ := exists_singular_of_three_le_any (Q := Q) (S := V₀) h
    exact hx0 (hV0an x hx hxQ)
  · rw [← OrthBlk.sup_fixIn_normKer hgp hpK hstTop]
    exact sup_le_sup_left hPsp _
  · rintro h ⟨i, rfl⟩ j x hx
    exact OrthBlk.pow_apply_mem (hP j).2.2.1 i x hx
  · rintro h ⟨i, rfl⟩ x hx
    rw [OrthBlk.pow_apply_of_fixed (OrthBlk.mem_fixIn.mp hx).2 i]
    exact hx

end Cyclic

section SpinCyc

variable {K : Type} [Field K] [Finite K]

theorem exists_spin_conj_frameGroup_cyclic (hodd : Odd (Nat.card K)) {n : ℕ} (hn : 3 ≤ n) {k : ℕ}
    (hnk : n = 2 * k) (ι : Fin k × Bool ≃ Fin n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : p ≠ ringChar K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (b : spinGroup (quadPlus n K)) (hb : b ^ p = 1)
    (hNS : ∀ T : Submodule K (Fin n ⊕ Fin n → K),
      (∀ v ∈ T, spinAction (quadPlus n K) b v ∈ T) →
      (∀ v ∈ T, quadPlus n K v = 0) → T = ⊥) :
    ∃ x : spinGroup (quadPlus n K), x * b * x⁻¹ ∈ spinFrameGroup n K hn ι := by
  classical
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  haveI : Invertible (2 : K) := invertibleOfNonzero h2
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hQnd : (polarBilin (quadPlus n K)).Nondegenerate := nondegenerate_polarBilin_quadPlus n K
  haveI : Finite (spinGroup (quadPlus n K)) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  set g := spinAction (quadPlus n K) b with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => map_spinAction _ b w
  have hgp : g ^ p = 1 := by rw [hg, ← map_pow, hb, map_one]
  have hk : Module.finrank K (Fin n ⊕ Fin n → K) = 4 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨Pl, hGP⟩ := exists_goodPlanes_cyclic hQnd hp hp5 hpl hord hgO hgp
    (fun T hTi hTs => hNS T hTi hTs) hk
  obtain ⟨x, hx⟩ := exists_spin_conj_of_goodPlanes hodd hn hnk ι hp (by omega)
    (Subgroup.zpowers b) (by
      intro y hy
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hb,
        _root_.one_zpow])
    (hGP.mono (by
      rintro h ⟨e, he, rfl⟩
      obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr he)
      exact ⟨i, by rw [← hi, map_pow]⟩))
  exact ⟨x, hx b (Subgroup.mem_zpowers b)⟩

end SpinCyc

end CFSG.LieType.SeitzGeneration.ExcHigh
