module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.LocalData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

theorem rep_words (ws : List (List (Fin 45))) :
    ∀ j < (ws.map wtab).length, Rep ((ws.map wperm).getD j 1) ((ws.map wtab).getD j []) := by
  intro j hj
  have hj' : j < ws.length := by simpa using hj
  rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getD_eq_getElem _ _ hj]
  simp only [List.getElem_map]
  exact rep_wperm _

theorem length_words (ws : List (List (Fin 45))) : (ws.map wperm).length = (ws.map wtab).length :=
  by simp

theorem tauPerm_mul_self (j : Fin 45) : tauPerm j * tauPerm j = 1 := by
  rw [← psi_s43', ← map_mul, s43_mul_self, map_one]

theorem wperm_reverse_mul : ∀ w : List (Fin 45), wperm w.reverse * wperm w = 1
  | [] => by simp [wperm]
  | i :: w => by
    rw [List.reverse_cons, wperm_append]
    have h1 : wperm [i] = tauPerm i := by simp [wperm]
    have h2 : wperm (i :: w) = tauPerm i * wperm w := by simp [wperm]
    rw [h1, h2]
    calc wperm w.reverse * tauPerm i * (tauPerm i * wperm w)
        = wperm w.reverse * (tauPerm i * tauPerm i) * wperm w := by group
      _ = 1 := by rw [tauPerm_mul_self, mul_one, wperm_reverse_mul w]

theorem wperm_inv (w : List (Fin 45)) : (wperm w)⁻¹ = wperm w.reverse :=
  (eq_inv_of_mul_eq_one_left (wperm_reverse_mul w)).symm

theorem getD_mem {l : List Tab} {i : ℕ} (hi : i < l.length) : l.getD i [] ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

theorem mem_gen_words {ws : List (List (Fin 45))} {elems : List Tab} {par : List (ℕ × ℕ)}
    {act : List (List ℕ)} (h : enumOK (ws.map wtab) elems par act = true)
    (g : Equiv.Perm (Fin 45)) :
    g ∈ gen (ws.map wperm) ↔ ∃ i < elems.length, Rep g (elems.getD i []) :=
  mem_gen_iff_of_enumOK (length_words ws) (rep_words ws) h g

theorem card_gen_words {ws : List (List (Fin 45))} {elems : List Tab} {par : List (ℕ × ℕ)}
    {act : List (List ℕ)} (h : enumOK (ws.map wtab) elems par act = true) :
    Nat.card (gen (ws.map wperm)) = elems.length :=
  card_gen_of_enumOK (length_words ws) (rep_words ws) h

theorem gen_words_le_P (ws : List (List (Fin 45))) : gen (ws.map wperm) ≤ P := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_setOf_eq, List.mem_map] at hg
  obtain ⟨w, -, rfl⟩ := hg
  exact wperm_mem w

theorem wperm_mem_gen {ws : List (List (Fin 45))} {w : List (Fin 45)} (hw : w ∈ ws) :
    wperm w ∈ gen (ws.map wperm) :=
  Subgroup.subset_closure (List.mem_map_of_mem hw)

theorem exists_mem_tab {ws : List (List (Fin 45))} {elems : List Tab} {par : List (ℕ × ℕ)}
    {act : List (List ℕ)} (h : enumOK (ws.map wtab) elems par act = true)
    {g : Equiv.Perm (Fin 45)} (hg : g ∈ gen (ws.map wperm)) : ∃ t ∈ elems, Rep g t := by
  obtain ⟨i, hi, hr⟩ := (mem_gen_words h g).1 hg
  exact ⟨_, getD_mem hi, hr⟩

theorem mem_gen_of_mem_tab {ws : List (List (Fin 45))} {elems : List Tab} {par : List (ℕ × ℕ)}
    {act : List (List ℕ)} (h : enumOK (ws.map wtab) elems par act = true)
    {g : Equiv.Perm (Fin 45)} {t : Tab} (ht : t ∈ elems) (hr : Rep g t) :
    g ∈ gen (ws.map wperm) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  refine (mem_gen_words h g).2 ⟨i, hi, ?_⟩
  rwa [List.getD_eq_getElem _ _ hi]

theorem mem_normalizer_of_conj_mem' {G : Type*} [Group G] (H : Subgroup G) [Finite H] (σ : G)
    (h : ∀ x ∈ H, σ * x * σ⁻¹ ∈ H) : σ ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : H → H := fun y => ⟨σ * y * σ⁻¹, h y y.2⟩
  have hinj : Function.Injective f := by
    intro y z hyz
    have := congrArg Subtype.val hyz
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨σ * x * σ⁻¹, hx⟩
  have := congrArg Subtype.val hy
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact y.2

@[expose] def fixesZero (l : List Tab) : Bool := l.all fun t => t.getD 0 0 == 0

@[expose] def normB (gs : List (List (Fin 45))) (elems : List Tab) : Bool :=
  gs.all fun w => elems.all fun t => elems.contains (tmul (tmul (wtab w) t) (wtab w.reverse))

@[expose] def meetB (A B : List Tab) : Bool := A.all fun t => t == tid || !B.contains t

@[expose] def centerB (gens elems zs : List Tab) : Bool :=
  elems.all fun t => !(gens.all fun g => tmul t g == tmul g t) || zs.contains t

@[expose] def meetConjB (w : List (Fin 45)) (S E : List Tab) : Bool :=
  S.all fun t => !(S.contains (tmul (tmul (wtab w.reverse) t) (wtab w))) || E.contains t

@[expose] def commB (a b : Tab) : Bool := tmul a b == tmul b a

@[expose] def witB (elems zs : List Tab) (wit : List (ℕ × ℕ)) : Bool :=
  (List.range elems.length).all fun i => zs.contains (elems.getD i []) ||
    (decide ((wit.getD i (0, 0)).1 < elems.length) &&
      decide ((wit.getD i (0, 0)).2 < elems.length) &&
      commB (elems.getD i []) (elems.getD (wit.getD i (0, 0)).1 []) &&
      commB (elems.getD i []) (elems.getD (wit.getD i (0, 0)).2 []) &&
      !commB (elems.getD (wit.getD i (0, 0)).1 []) (elems.getD (wit.getD i (0, 0)).2 []))

@[expose] def tau0Tab : Tab := tauTab.getD 0 []

theorem E_fix : fixesZero Eelems = true := by decide +kernel
theorem K_fix : fixesZero Kelems = true := by decide +kernel
theorem S0_fix : fixesZero S0elems = true := by decide +kernel
theorem K_norm_E : normB Kgens Eelems = true := by decide +kernel
theorem K_meet_E : meetB Kelems Eelems = true := by decide +kernel
theorem E_center : centerB (Egens.map wtab) Eelems [tid, tau0Tab] = true := by decide +kernel
theorem S0_center : centerB (S0gens.map wtab) S0elems [tid, tau0Tab] = true := by decide +kernel
theorem S0_meet : meetConjB [4, 3, 1, 0] S0elems Eelems = true := by decide +kernel
theorem E_wit : witB Eelems [tid, tau0Tab] Ewit = true := by decide +kernel

theorem factorization_two_576 : (576 : ℕ).factorization 2 = 6 := by
  rw [show (576 : ℕ) = 2 ^ 6 * 9 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem factorization_two_25920 : (25920 : ℕ).factorization 2 = 6 := by
  rw [show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem factorization_three_25920 : (25920 : ℕ).factorization 3 = 4 := by
  rw [show (25920 : ℕ) = 3 ^ 4 * 320 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

section SylowTools

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem card_subgroupOf_of_le {H S : Subgroup G} (h : S ≤ H) :
    Nat.card (S.subgroupOf H) = Nat.card S :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

theorem pCoreOf_le_of_card {H S : Subgroup G} (hSH : S ≤ H)
    (hS : Nat.card S = p ^ (Nat.card H).factorization p) : CFSG.Open.pCoreOf p H ≤ S := by
  let S' : Sylow p H := Sylow.ofCard (S.subgroupOf H) (by rw [card_subgroupOf_of_le hSH, hS])
  have h1 : CFSG.pCore p H ≤ S' := CFSG.pCore_isPGroup.le_sylow_of_normal S'
  rintro _ ⟨y, hy, rfl⟩
  exact h1 hy

theorem le_pCoreOf_of_normal {H N : Subgroup G} (hNH : N ≤ H) (hp : IsPGroup p N)
    (hn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) : N ≤ CFSG.Open.pCoreOf p H := by
  have hnor : (N.subgroupOf H).Normal := ⟨fun n hn' g => by
    rw [mem_subgroupOf] at hn' ⊢
    exact hn g g.2 n hn'⟩
  have hp' : IsPGroup p (N.subgroupOf H) := hp.of_equiv (subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ CFSG.pCore p H := le_sSup ⟨hnor, hp'⟩
  intro x hx
  exact ⟨⟨x, hNH hx⟩, hle (by rw [mem_subgroupOf]; exact hx), rfl⟩

end SylowTools

abbrev E : Subgroup (Equiv.Perm (Fin 45)) := gen (Egens.map wperm)

abbrev K : Subgroup (Equiv.Perm (Fin 45)) := gen (Kgens.map wperm)

abbrev S0 : Subgroup (Equiv.Perm (Fin 45)) := gen (S0gens.map wperm)

abbrev H0 : Subgroup (Equiv.Perm (Fin 45)) :=
  P ⊓ centralizer ({tauPerm 0} : Set (Equiv.Perm (Fin 45)))

theorem card_E : Nat.card E = 32 := (card_gen_words E_enumOK).trans (by decide)
theorem card_K : Nat.card K = 18 := (card_gen_words K_enumOK).trans (by decide)
theorem card_S0 : Nat.card S0 = 64 := (card_gen_words S0_enumOK).trans (by decide)
theorem card_H0 : Nat.card H0 = 576 := card_centralizer_tau_zero

theorem le_H0_of_fix {ws : List (List (Fin 45))} {elems : List Tab} {par : List (ℕ × ℕ)}
    {act : List (List ℕ)} (h : enumOK (ws.map wtab) elems par act = true)
    (hf : fixesZero elems = true) : gen (ws.map wperm) ≤ H0 := by
  intro g hg
  have hgP := gen_words_le_P ws hg
  refine ⟨hgP, (mem_centralizer_tauPerm_iff hgP 0).2 ?_⟩
  obtain ⟨t, ht, hr⟩ := exists_mem_tab h hg
  have h0 := List.all_eq_true.1 hf t ht
  apply Fin.ext
  exact (hr.2 0 (by norm_num)).trans (by simpa using h0)

theorem E_le_H0 : E ≤ H0 := le_H0_of_fix E_enumOK E_fix
theorem K_le_H0 : K ≤ H0 := le_H0_of_fix K_enumOK K_fix
theorem S0_le_H0 : S0 ≤ H0 := le_H0_of_fix S0_enumOK S0_fix

theorem conj_mem_E_of_normB {gs : List (List (Fin 45))} (hN : normB gs Eelems = true)
    {w : List (Fin 45)} (hw : w ∈ gs) {x : Equiv.Perm (Fin 45)} (hx : x ∈ E) :
    wperm w * x * (wperm w)⁻¹ ∈ E := by
  obtain ⟨t, ht, hr⟩ := exists_mem_tab E_enumOK hx
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 hN w hw) t ht
  rw [List.contains_iff_mem] at h1
  rw [wperm_inv]
  exact mem_gen_of_mem_tab E_enumOK h1 (rep_mul (rep_mul (rep_wperm w) hr) (rep_wperm w.reverse))

theorem gen_le_normalizer_E {gs : List (List (Fin 45))} (hN : normB gs Eelems = true) :
    gen (gs.map wperm) ≤ normalizer (E : Set (Equiv.Perm (Fin 45))) := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_setOf_eq, List.mem_map] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  exact mem_normalizer_of_conj_mem' E _ fun x hx => conj_mem_E_of_normB hN hw hx

theorem K_le_normalizer_E : K ≤ normalizer (E : Set (Equiv.Perm (Fin 45))) :=
  gen_le_normalizer_E K_norm_E

theorem eq_one_of_mem_E_of_mem_K {x : Equiv.Perm (Fin 45)} (hE : x ∈ E) (hK : x ∈ K) :
    x = 1 := by
  obtain ⟨t, ht, hr⟩ := exists_mem_tab K_enumOK hK
  obtain ⟨t', ht', hr'⟩ := exists_mem_tab E_enumOK hE
  have h1 := List.all_eq_true.1 K_meet_E t ht
  rw [rep_eq_tab hr hr'] at h1
  have h2 : Eelems.contains t' = true := List.contains_iff_mem.2 ht'
  simp only [h2, Bool.not_true, Bool.or_false, beq_iff_eq] at h1
  rw [h1] at hr'
  exact rep_unique hr' rep_one

theorem exists_mul_eq_of_mem_H0 {h : Equiv.Perm (Fin 45)} (hh : h ∈ H0) :
    ∃ e ∈ E, ∃ k ∈ K, e * k = h := by
  let f : E × K → H0 := fun q => ⟨q.1 * q.2, mul_mem (E_le_H0 q.1.2) (K_le_H0 q.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨e, k⟩ ⟨e', k'⟩ hq
    have h1 : (e : Equiv.Perm (Fin 45)) * k = e' * k' := congrArg Subtype.val hq
    have h2 : (e' : Equiv.Perm (Fin 45))⁻¹ * e = k' * (k : Equiv.Perm (Fin 45))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
    have h3 : (e' : Equiv.Perm (Fin 45))⁻¹ * e = 1 :=
      eq_one_of_mem_E_of_mem_K (mul_mem (inv_mem e'.2) e.2) (h2 ▸ mul_mem k'.2 (inv_mem k.2))
    have he : e = e' := Subtype.ext (inv_mul_eq_one.1 h3).symm
    subst he
    have hk : k = k' := Subtype.ext (mul_left_cancel h1)
    rw [hk]
  have hcard : Nat.card H0 ≤ Nat.card (E × K) := by
    rw [Nat.card_prod, card_E, card_K, card_H0]
  obtain ⟨⟨e, k⟩, hek⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨h, hh⟩
  exact ⟨e, e.2, k, k.2, congrArg Subtype.val hek⟩

theorem H0_le_normalizer_E : H0 ≤ normalizer (E : Set (Equiv.Perm (Fin 45))) := by
  intro h hh
  obtain ⟨e, he, k, hk, rfl⟩ := exists_mul_eq_of_mem_H0 hh
  exact mul_mem (le_normalizer he) (K_le_normalizer_E hk)

theorem isPGroup_E : IsPGroup 2 E := IsPGroup.of_card (n := 5) (by rw [card_E]; norm_num)

theorem card_S0_eq : Nat.card S0 = 2 ^ (Nat.card H0).factorization 2 := by
  rw [card_S0, card_H0, factorization_two_576]
  norm_num

theorem pCoreOf_H0_le_conj {k : Equiv.Perm (Fin 45)} (hk : k ∈ H0) :
    CFSG.Open.pCoreOf 2 H0 ≤ S0.map (MulAut.conj k).toMonoidHom := by
  have hle : S0.map (MulAut.conj k).toMonoidHom ≤ H0 := by
    rintro _ ⟨s, hs, rfl⟩
    exact mul_mem (mul_mem hk (S0_le_H0 hs)) (inv_mem hk)
  have hc : Nat.card (S0.map (MulAut.conj k).toMonoidHom) =
      2 ^ (Nat.card H0).factorization 2 := by
    rw [← card_S0_eq]
    exact Subgroup.card_map_of_injective (MulAut.conj k).injective
  exact pCoreOf_le_of_card hle hc

theorem mem_conj_S0 {k x : Equiv.Perm (Fin 45)} (hx : x ∈ S0.map (MulAut.conj k).toMonoidHom) :
    k⁻¹ * x * k ∈ S0 := by
  obtain ⟨s, hs, rfl⟩ := hx
  simpa [mul_assoc] using hs

theorem pCoreOf_H0 : CFSG.Open.pCoreOf 2 H0 = E := by
  apply le_antisymm
  · have hk : wperm [4, 3, 1, 0] ∈ H0 := K_le_H0 (wperm_mem_gen (by simp [Kgens]))
    intro x hx
    have hx1 := pCoreOf_le_of_card S0_le_H0 card_S0_eq hx
    have hx2 := mem_conj_S0 (pCoreOf_H0_le_conj hk hx)
    obtain ⟨t, ht, hr⟩ := exists_mem_tab S0_enumOK hx1
    have hm := List.all_eq_true.1 S0_meet t ht
    obtain ⟨t', ht', hr'⟩ := exists_mem_tab S0_enumOK hx2
    have hr2 : Rep ((wperm [4, 3, 1, 0])⁻¹ * x * wperm [4, 3, 1, 0])
        (tmul (tmul (wtab [4, 3, 1, 0].reverse) t) (wtab [4, 3, 1, 0])) := by
      rw [wperm_inv]
      exact rep_mul (rep_mul (rep_wperm _) hr) (rep_wperm _)
    rw [← rep_eq_tab hr' hr2] at hm
    have hc1 : S0elems.contains t' = true := List.contains_iff_mem.2 ht'
    simp only [hc1, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hm
    exact mem_gen_of_mem_tab E_enumOK hm hr
  · exact le_pCoreOf_of_normal E_le_H0 isPGroup_E fun h hh n hn =>
      (mem_normalizer_iff.1 (H0_le_normalizer_E hh) n).1 hn

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
