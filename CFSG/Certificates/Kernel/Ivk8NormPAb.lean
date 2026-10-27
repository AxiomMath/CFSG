module

public import CFSG.Certificates.Kernel.Ivk8NormPGlue
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12NormP

public section

namespace CFSG.KS.Ivk8NormP

open Subgroup

variable {M : Type*} [Group M]

theorem mem_normalizer_zpowers {s u : M} (hs : s * s = 1)
    (h : s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u⁻¹) : s ∈ normalizer (zpowers u : Set M) := by
  have hmap : (zpowers u).map (MulAut.conj s).toMonoidHom = zpowers u := by
    rw [MonoidHom.map_zpowers]
    change zpowers (s * u * s⁻¹) = zpowers u
    rcases h with h | h
    · rw [h]
    · rw [h, zpowers_inv]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have : s * z * s⁻¹ ∈ (zpowers u).map (MulAut.conj s).toMonoidHom := ⟨z, hz, rfl⟩
    rwa [hmap] at this
  · intro hz
    have : s * (s * z * s⁻¹) * s⁻¹ ∈ (zpowers u).map (MulAut.conj s).toMonoidHom :=
      ⟨_, hz, rfl⟩
    rw [hmap] at this
    have e : s * (s * z * s⁻¹) * s⁻¹ = z := by
      calc s * (s * z * s⁻¹) * s⁻¹ = (s * s) * z * (s⁻¹ * s⁻¹) := by group
        _ = z := by rw [hs, hsi, hs, one_mul, mul_one]
    rwa [e] at this

theorem exists_line_aux {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (xs : List M)
    (hinv : ∀ s ∈ xs, s * s = 1) (hcomm : ∀ s ∈ xs, ∀ t ∈ xs, s * t = t * s) :
    ∀ T : List M, (∀ t ∈ T, t ∈ xs) → ∀ E : Subgroup M, E ≠ ⊥ →
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) →
      (∀ s ∈ xs, ∀ x ∈ E, s * x * s⁻¹ ∈ E) →
      ∃ u ∈ E, u ≠ 1 ∧ ∀ t ∈ T, t * u * t⁻¹ = u ∨ t * u * t⁻¹ = u⁻¹
  | [], _, E, hE, _, _, _ => by
    obtain ⟨u, hu, hu1⟩ := E.bot_or_exists_ne_one.resolve_left hE
    exact ⟨u, hu, hu1, by simp⟩
  | s :: T, hT, E, hE, hEc, hEp, hEi => by
    have hs : s ∈ xs := hT s List.mem_cons_self
    have hss := hinv s hs
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    let Ep : Subgroup M :=
      { carrier := {x | x ∈ E ∧ s * x * s⁻¹ = x}
        one_mem' := ⟨E.one_mem, by group⟩
        mul_mem' := fun {x y} hx hy => ⟨E.mul_mem hx.1 hy.1, by
          calc s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
            _ = x * y := by rw [hx.2, hy.2]⟩
        inv_mem' := fun {x} hx => ⟨E.inv_mem hx.1, by
          calc s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
            _ = x⁻¹ := by rw [hx.2]⟩ }
    let Em : Subgroup M :=
      { carrier := {x | x ∈ E ∧ s * x * s⁻¹ = x⁻¹}
        one_mem' := ⟨E.one_mem, by group⟩
        mul_mem' := fun {x y} hx hy => ⟨E.mul_mem hx.1 hy.1, by
          calc s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
            _ = x⁻¹ * y⁻¹ := by rw [hx.2, hy.2]
            _ = (y * x)⁻¹ := by group
            _ = (x * y)⁻¹ := by rw [hEc y hy.1 x hx.1]⟩
        inv_mem' := fun {x} hx => ⟨E.inv_mem hx.1, by
          calc s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
            _ = x⁻¹⁻¹ := by rw [hx.2]⟩ }
    have hcs : ∀ s' ∈ xs, s * s' = s' * s := fun s' hs' => hcomm s hs s' hs'
    have hconj : ∀ s' ∈ xs, ∀ x : M, s * (s' * x * s'⁻¹) * s⁻¹ = s' * (s * x * s⁻¹) * s'⁻¹ := by
      intro s' hs' x
      have h1 : s * s' = s' * s := hcs s' hs'
      have h2 : s'⁻¹ * s⁻¹ = s⁻¹ * s'⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, h1]
      calc s * (s' * x * s'⁻¹) * s⁻¹ = (s * s') * x * (s'⁻¹ * s⁻¹) := by group
        _ = (s' * s) * x * (s⁻¹ * s'⁻¹) := by rw [h1, h2]
        _ = s' * (s * x * s⁻¹) * s'⁻¹ := by group
    have hEpi : ∀ s' ∈ xs, ∀ x ∈ Ep, s' * x * s'⁻¹ ∈ Ep := fun s' hs' x hx =>
      ⟨hEi s' hs' x hx.1, by rw [hconj s' hs' x, hx.2]⟩
    have hEmi : ∀ s' ∈ xs, ∀ x ∈ Em, s' * x * s'⁻¹ ∈ Em := fun s' hs' x hx =>
      ⟨hEi s' hs' x hx.1, by rw [hconj s' hs' x, hx.2]; group⟩
    obtain ⟨x, hx, hx1⟩ := E.bot_or_exists_ne_one.resolve_left hE
    set y := s * x * s⁻¹ with hy
    have hyE : y ∈ E := hEi s hs x hx
    have hsy : s * y * s⁻¹ = x := by
      rw [hy]
      calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
        _ = x := by rw [hss, hsi, hss, one_mul, mul_one]
    obtain ⟨m, hm⟩ : ∃ m, p + 1 = 2 * m := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      exact ⟨k + 1, by omega⟩
    have hxp : x * y ∈ Ep := by
      refine ⟨E.mul_mem hx hyE, ?_⟩
      calc s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
        _ = y * x := by rw [← hy, hsy]
        _ = x * y := hEc y hyE x hx
    have hxm : x * y⁻¹ ∈ Em := by
      refine ⟨E.mul_mem hx (E.inv_mem hyE), ?_⟩
      calc s * (x * y⁻¹) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹)⁻¹ := by group
        _ = y * x⁻¹ := by rw [← hy, hsy]
        _ = (x * y⁻¹)⁻¹ := by group
    have hprod : (x * y) ^ m * (x * y⁻¹) ^ m = x := by
      have hc : Commute (x * y) (x * y⁻¹) :=
        hEc _ (E.mul_mem hx hyE) _ (E.mul_mem hx (E.inv_mem hyE))
      rw [← hc.mul_pow]
      have h2 : x * y * (x * y⁻¹) = x ^ 2 := by
        calc x * y * (x * y⁻¹) = x * (y * x) * y⁻¹ := by group
          _ = x * (x * y) * y⁻¹ := by rw [hEc y hyE x hx]
          _ = x ^ 2 := by rw [← mul_assoc, mul_inv_cancel_right, sq]
      rw [h2, ← pow_mul, ← hm, pow_succ, hEp x hx, one_mul]
    have hF : ∃ F : Subgroup M, F ≠ ⊥ ∧ F ≤ E ∧ (∀ s' ∈ xs, ∀ z ∈ F, s' * z * s'⁻¹ ∈ F) ∧
        ∀ z ∈ F, s * z * s⁻¹ = z ∨ s * z * s⁻¹ = z⁻¹ := by
      by_cases h1 : (x * y) ^ m = 1
      · refine ⟨Em, ?_, fun z hz => hz.1, hEmi, fun z hz => Or.inr hz.2⟩
        intro hb
        have hmem : (x * y⁻¹) ^ m ∈ Em := Em.pow_mem hxm m
        rw [hb, Subgroup.mem_bot] at hmem
        rw [h1, hmem, one_mul] at hprod
        exact hx1 hprod.symm
      · refine ⟨Ep, ?_, fun z hz => hz.1, hEpi, fun z hz => Or.inl hz.2⟩
        intro hb
        have hmem : (x * y) ^ m ∈ Ep := Ep.pow_mem hxp m
        rw [hb, Subgroup.mem_bot] at hmem
        exact h1 hmem
    obtain ⟨F, hF1, hFE, hFi, hFs⟩ := hF
    obtain ⟨u, hu, hu1, hT'⟩ := exists_line_aux hp hp2 xs hinv hcomm T
      (fun t ht => hT t (List.mem_cons_of_mem _ ht)) F hF1
      (fun a ha b hb => hEc a (hFE ha) b (hFE hb)) (fun a ha => hEp a (hFE ha)) hFi
    refine ⟨u, hFE hu, hu1, ?_⟩
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact hFs u hu
    · exact hT' t ht

theorem exists_line [Finite M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Subgroup M}
    (hU : IsPGroup p U) (hU1 : U ≠ ⊥) (xs : List M) (hinv : ∀ s ∈ xs, s * s = 1)
    (hcomm : ∀ s ∈ xs, ∀ t ∈ xs, s * t = t * s)
    (hxsU : ∀ s ∈ xs, s ∈ normalizer (U : Set M)) :
    ∃ u ∈ U, orderOf u = p ∧ ∀ s ∈ xs, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  let E : Subgroup M :=
    { carrier := {x | x ∈ U ∧ (∀ w ∈ U, x * w = w * x) ∧ x ^ p = 1}
      one_mem' := ⟨U.one_mem, fun w _ => by group, one_pow p⟩
      mul_mem' := fun {x y} hx hy => ⟨U.mul_mem hx.1 hy.1, fun w hw => by
          rw [mul_assoc, hy.2.1 w hw, ← mul_assoc, hx.2.1 w hw, mul_assoc],
        by rw [Commute.mul_pow (a := x) (b := y) (hx.2.1 y hy.1) p, hx.2.2, hy.2.2, one_mul]⟩
      inv_mem' := fun {x} hx => ⟨U.inv_mem hx.1, fun w hw =>
          (Commute.inv_left (a := x) (b := w) (hx.2.1 w hw)).eq,
        by rw [inv_pow, hx.2.2, inv_one]⟩ }
  have hE : E ≠ ⊥ := by
    have hUn : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).2 hU1
    have hZ : Nontrivial (center U) := hU.center_nontrivial
    have hZp : IsPGroup p (center U) := hU.to_subgroup _
    obtain ⟨k, hk0, hk⟩ := hZp.nontrivial_iff_card.1 hZ
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center U) p
      (by rw [hk]; exact dvd_pow_self p (by omega))
    intro hb
    have hzE : ((z : U) : M) ∈ E := by
      refine ⟨(z : U).2, fun w hw => ?_, ?_⟩
      · have := (Subgroup.mem_center_iff.1 z.2) ⟨w, hw⟩
        exact (congrArg Subtype.val this).symm
      · have h1 : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
        have h2 := congrArg (fun a : center U => ((a : U) : M)) h1
        simpa using h2
    rw [hb, Subgroup.mem_bot] at hzE
    have hz1 : z = 1 := Subtype.ext (Subtype.ext hzE)
    rw [hz1, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hEi : ∀ s ∈ xs, ∀ x ∈ E, s * x * s⁻¹ ∈ E := by
    intro s hs x hx
    have hn := mem_normalizer_iff.1 (hxsU s hs)
    refine ⟨(hn x).1 hx.1, fun w hw => ?_, by rw [conj_pow, hx.2.2]; group⟩
    have hw' : s⁻¹ * w * s ∈ U := by
      have := (hn (s⁻¹ * w * s)).2
      apply this
      have e : s * (s⁻¹ * w * s) * s⁻¹ = w := by group
      rw [e]
      exact hw
    have hc := hx.2.1 _ hw'
    calc s * x * s⁻¹ * w = s * (x * (s⁻¹ * w * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * w * s) * x) * s⁻¹ := by rw [hc]
      _ = w * (s * x * s⁻¹) := by group
  obtain ⟨u, hu, hu1, hT⟩ := exists_line_aux hp hp2 xs hinv hcomm xs (fun t ht => ht) E hE
    (fun a ha b hb => ha.2.1 b hb.1) (fun a ha => ha.2.2) hEi
  exact ⟨u, hu.1, orderOf_eq_prime hu.2.2 hu1, hT⟩

theorem noP_of_cents_ab [Finite M] {G S₀ : Subgroup M} (hS₀G : S₀ ≤ G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {xs : List M} (hinv : ∀ s ∈ xs, s * s = 1)
    (hcomm : ∀ s ∈ xs, ∀ t ∈ xs, s * t = t * s) (hxsS : ∀ s ∈ xs, s ∈ S₀) {A B : M}
    (hAx : A ∈ xs) (hBx : B ∈ xs) (hA1 : A ≠ 1) (hB1 : B ≠ 1) (hAneB : A ≠ B)
    {ds : List (M × M × Subgroup M)}
    (hK : ∀ d ∈ ds, ∀ x ∈ G, x * d.2.1 = d.2.1 * x → x ∈ d.2.2) (hcs : ∀ d ∈ ds, d.1 ∈ G)
    (hcov : ∀ e ∈ [A, B, A * B], ∃ d ∈ ds, d.1 * d.2.1 * d.1⁻¹ = e)
    (hN : ∀ d ∈ ds, ∀ y ∈ d.2.2, orderOf y = p →
      ∃ h ∈ closure {x | x ∈ xs}, h ∉ normalizer (zpowers (d.1 * y * d.1⁻¹) : Set M))
    {k : ℕ} (hS₀ : ¬ 2 ^ (k + 1) ∣ Nat.card S₀) :
    ∀ P W : Subgroup M, P ≤ S₀ → W ≤ G → Nat.card P = 2 ^ k → IsPGroup p W →
      P ≤ normalizer (W : Set M) → W = ⊥ := by
  classical
  intro P W hPS hWG hPc hWp hPW
  by_contra hWne
  set S : Set M := {x | x ∈ xs} with hS
  have hinvS : ∀ x ∈ S, x * x = 1 := hinv
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := hcomm
  have hAH : A ∈ closure S := subset_closure hAx
  have hBH : B ∈ closure S := subset_closure hBx
  have hHc : ∀ h ∈ closure S, h * A = A * h ∧ h * B = B * h := fun h hh =>
    ⟨comm_of_mem_closure hcommS h hh _ hAH, comm_of_mem_closure hcommS h hh _ hBH⟩
  have hHS : closure S ≤ S₀ := (closure_le _).2 hxsS
  obtain ⟨e, he, U, hUG, hUe, hUp, hU1, hnormU⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.exists_cent_part
    hS₀G hp hp2 hAH hBH (hinv A hAx) (hinv B hBx) (hcomm A hAx B hBx) hA1 hB1 hAneB
    (isPGroup_two_closure hinvS hcommS) hHS hHc hS₀ hPS hWG hPc hWp hPW hWne
  obtain ⟨u, huU, huo, hu⟩ := exists_line hp hp2 hUp hU1 xs hinv hcomm
    (fun s hs => hnormU s (subset_closure hs))
  have hnorm : closure S ≤ normalizer (zpowers u : Set M) :=
    (closure_le _).2 fun s hs => mem_normalizer_zpowers (hinv s hs) (hu s hs)
  obtain ⟨⟨c, r, K⟩, hd, hcr⟩ := hcov e he
  have hcG := hcs _ hd
  have hy : c⁻¹ * u * c ∈ K := by
    refine hK _ hd _ (G.mul_mem (G.mul_mem (G.inv_mem hcG) (hUG huU)) hcG) ?_
    have h1 : u * (c * r * c⁻¹) = (c * r * c⁻¹) * u := by rw [hcr]; exact hUe u huU
    calc c⁻¹ * u * c * r = c⁻¹ * (u * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * r * c⁻¹) * u) * c := by rw [h1]
      _ = r * (c⁻¹ * u * c) := by group
  have hyo : orderOf (c⁻¹ * u * c) = p := by
    have : c⁻¹ * u * c = (MulAut.conj c⁻¹) u := by simp
    rw [this, MulEquiv.orderOf_eq, huo]
  have hcy : c * (c⁻¹ * u * c) * c⁻¹ = u := by group
  obtain ⟨h, hh, hnot⟩ := hN _ hd _ hy hyo
  rw [hcy] at hnot
  exact hnot (hnorm hh)

theorem noP_of_cent_free [Finite M] {G S₀ K : Subgroup M} (hS₀G : S₀ ≤ G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A B r : M} (hAS : A ∈ S₀) (hBS : B ∈ S₀) (hAA : A * A = 1)
    (hBB : B * B = 1) (hAB : A * B = B * A) (hA1 : A ≠ 1) (hB1 : B ≠ 1) (hAneB : A ≠ B)
    (hK : ∀ x ∈ G, x * r = r * x → x ∈ K) (hpK : ¬ p ∣ Nat.card K) {cs : List M}
    (hcs : ∀ c ∈ cs, c ∈ G) (hcov : ∀ e ∈ [A, B, A * B], ∃ c ∈ cs, c * r * c⁻¹ = e)
    {k : ℕ} (hS₀ : ¬ 2 ^ (k + 1) ∣ Nat.card S₀) :
    ∀ P W : Subgroup M, P ≤ S₀ → W ≤ G → Nat.card P = 2 ^ k → IsPGroup p W →
      P ≤ normalizer (W : Set M) → W = ⊥ := by
  refine noP_of_cents_ab hS₀G hp hp2 (xs := [A, B]) ?_ ?_ ?_ List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self) hA1 hB1 hAneB
    (ds := cs.map fun c => (c, r, K)) ?_ ?_ ?_ ?_ hS₀
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hAA
    · exact hBB
  · intro s hs t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact hAB
    · exact hAB.symm
    · rfl
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hAS
    · exact hBS
  · intro d hd
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hd
    exact hK
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    exact hcs c hc
  · intro e he
    obtain ⟨c, hc, h⟩ := hcov e he
    exact ⟨(c, r, K), List.mem_map_of_mem hc, h⟩
  · intro d hd y hy hyo
    exfalso
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hd
    apply hpK
    rw [← hyo, ← Subgroup.orderOf_mk y hy]
    exact orderOf_dvd_natCard _

end CFSG.KS.Ivk8NormP

end
