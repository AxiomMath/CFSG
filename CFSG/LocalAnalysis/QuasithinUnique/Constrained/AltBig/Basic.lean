module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.Defs

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement Pointwise

variable {α : Type} [Fintype α] [DecidableEq α]

theorem quasisimple_comm_eq {G : Type} [Group G] {E : Subgroup G}
    (h : CFSG.Open.IsQuasisimple ↥E) : ⁅E, E⁆ = E := by
  rw [← Subgroup.map_subtype_commutator, h.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem quasisimple_ne_bot {G : Type} [Group G] {E : Subgroup G}
    (h : CFSG.Open.IsQuasisimple ↥E) : E ≠ ⊥ := by
  have hq : Nontrivial (↥E ⧸ Subgroup.center ↥E) := h.2.toNontrivial
  have hsurj : Function.Surjective (QuotientGroup.mk : ↥E → ↥E ⧸ Subgroup.center ↥E) :=
    QuotientGroup.mk_surjective
  have hE : Nontrivial ↥E := hsurj.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot E).mp hE

theorem even_card_of_closed (p : FpfInv α) (S : Set α) (hS : ∀ x ∈ S, p.μ x ∈ S) :
    Even (Nat.card S) := by
  classical
  have hiff : ∀ x, p.μ x ∈ S ↔ x ∈ S := fun x =>
    ⟨fun hx => by simpa [p.inv] using hS _ hx, hS x⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : Perm S, ∀ x : S, ((σ x : S) : α) = p.μ x :=
    ⟨Equiv.Perm.subtypePerm (p := fun x => x ∈ S) p.μ hiff, fun x => rfl⟩
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hσ, p.inv]
  have hfix : ∀ x : S, σ x ≠ x := by
    intro x hx
    apply p.fpf x.1
    have h := congrArg Subtype.val hx
    rw [hσ] at h
    exact h
  have hsupp : σ.support = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    rw [Equiv.Perm.mem_support]
    exact hfix x
  have h2 := Equiv.Perm.two_dvd_card_support hσ2
  rw [hsupp, Finset.card_univ] at h2
  rw [Nat.card_eq_fintype_card]
  exact even_iff_two_dvd.mpr h2

theorem perfect_fix_small {E : Subgroup (Perm α)} (hE : ⁅E, E⁆ = E) {W : Set α}
    (hW : Nat.card W ≤ 4) (hinv : ∀ e ∈ E, ∀ x ∈ W, e x ∈ W) :
    ∀ e ∈ E, ∀ x ∈ W, e x = x := by
  classical
  have hmem : ∀ e ∈ E, ∀ x : α, e x ∈ W ↔ x ∈ W := by
    intro e he x
    refine ⟨fun hx => ?_, fun hx => hinv e he x hx⟩
    have h' := hinv e⁻¹ (E.inv_mem he) (e x) hx
    simpa using h'
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥E →* Perm W, ∀ (e : ↥E) (x : W), ((ρ e x : W) : α) = (e : Perm α) x :=
    ⟨{ toFun := fun e => Equiv.Perm.subtypePerm (p := fun x => x ∈ W) (e : Perm α) (hmem e e.2)
       map_one' := rfl
       map_mul' := fun _ _ => rfl }, fun _ _ => rfl⟩
  have hEp : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hE
  have hK : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    have h1 : (commutator ↥E).map ρ = ⁅ρ.range, ρ.range⁆ := map_commutator_eq ↥E ρ
    rw [hEp.commutator_eq_top, ← MonoidHom.range_eq_map] at h1
    exact h1.symm
  have hKperf : Group.IsPerfect ↥(ρ.range) := Subgroup.isPerfect_iff.mpr hK
  haveI : Group.IsSolvable (Perm W) := Equiv.Perm.isSolvable hW
  have hKbot : ρ.range = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(ρ.range) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact (Group.IsPerfect.not_isSolvable ↥(ρ.range)) inferInstance
  intro e he x hx
  have h1 : ρ ⟨e, he⟩ = 1 := by
    have hmemK : ρ ⟨e, he⟩ ∈ ρ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hKbot, Subgroup.mem_bot] at hmemK
    exact hmemK
  have h2 := hρ ⟨e, he⟩ ⟨x, hx⟩
  rw [h1] at h2
  simpa using h2.symm

theorem orbit_mu_mem (p : FpfInv α) (h4 : 4 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) (x : α) : p.μ x ∈ MulAction.orbit (↥Y) x := by
  have hcard : ({x, p.μ x} : Finset α).card < (Finset.univ : Finset α).card := by
    rw [Finset.card_univ]
    have h1 := Finset.card_insert_le x ({p.μ x} : Finset α)
    rw [Finset.card_singleton] at h1
    omega
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hyx : y ≠ x := fun hh => hy (by simp [hh])
  have hyμ : y ≠ p.μ x := fun hh => hy (by simp [hh])
  have hxμy : x ≠ p.μ y := fun hh => hyμ (by rw [hh, p.inv])
  have hB' : ∀ a b : α, b ≠ a → b ≠ p.μ a → swap a (p.μ a) * swap b (p.μ b) ∈ Y := hB
  have hg : swap x (p.μ x) * swap y (p.μ y) ∈ Y := hB' x y hyx hyμ
  have hgx : (swap x (p.μ x) * swap y (p.μ y)) x = p.μ x := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hyx.symm hxμy,
      Equiv.swap_apply_left]
  exact MulAction.mem_orbit_iff.mpr ⟨⟨_, hg⟩, hgx⟩

theorem perfect_fix_pairs (p : FpfInv α) {E : Subgroup (Perm α)} (hE : ⁅E, E⁆ = E) {W : Set α}
    (h : ∀ e ∈ E, ∀ x ∈ W, e x = x ∨ e x = p.μ x) (hW : ∀ x ∈ W, p.μ x ∈ W) :
    ∀ e ∈ E, ∀ x ∈ W, e x = x := by
  have hinv : ∀ (σ : Perm α) (z : α), σ (σ⁻¹ z) = z := fun σ z => by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have hA : ∀ e ∈ E, ∀ y ∈ W,
      (e y = y → e (p.μ y) = p.μ y) ∧ (e y = p.μ y → e (p.μ y) = y) := by
    intro e he y hy
    have h' := h e he (p.μ y) (hW y hy)
    rw [p.inv y] at h'
    constructor
    · intro hey
      rcases h' with h1 | h1
      · exact h1
      · exfalso
        apply p.fpf y
        apply e.injective
        rw [h1, hey]
    · intro hey
      rcases h' with h1 | h1
      · exfalso
        apply p.fpf y
        apply e.injective
        rw [h1, hey]
      · exact h1
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, ∀ y ∈ W, a (b y) = b (a y) := by
    intro a ha b hb y hy
    obtain ⟨hA1, hA2⟩ := hA a ha y hy
    obtain ⟨hB1, hB2⟩ := hA b hb y hy
    rcases h a ha y hy with ha1 | ha1 <;> rcases h b hb y hy with hb1 | hb1
    · rw [hb1, ha1, hb1]
    · rw [hb1, ha1, hA1 ha1, hb1]
    · rw [hb1, ha1, hB1 hb1]
    · rw [hb1, ha1, hA2 ha1, hB2 hb1]
  have hfix : ∀ g ∈ E, ∀ k ∈ E, ⁅g, k⁆ ∈ fixOn W := by
    intro g hg k hk
    rw [mem_fixOn]
    intro z hz
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    have h1 : g⁻¹ (k⁻¹ z) = k⁻¹ (g⁻¹ z) := hcomm g⁻¹ (E.inv_mem hg) k⁻¹ (E.inv_mem hk) z hz
    rw [h1, hinv k, hinv g]
  have hsub : ⁅E, E⁆ ≤ fixOn W :=
    Subgroup.commutator_le.mpr (fun g hg k hk => hfix g hg k hk)
  rw [hE] at hsub
  intro e he x hx
  exact mem_fixOn.mp (hsub he) x hx

theorem fix_pairs_of_commute (p : FpfInv α) {W : Set α} (hW : ∀ x ∈ W, p.μ x ∈ W)
    (h6 : 6 ≤ Nat.card W) {e : Perm α}
    (h : ∀ x ∈ W, ∀ y ∈ W, y ≠ x → y ≠ p.μ x →
      Commute e (swap x (p.μ x) * swap y (p.μ y))) :
    ∀ x ∈ W, e x = x ∨ e x = p.μ x := by
  intro x hx
  have hW6 : 6 ≤ W.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact h6
  have hcard2 : ({x, p.μ x} : Set α).ncard ≤ 2 := by
    have h1 := Set.ncard_insert_le x ({p.μ x} : Set α)
    rw [Set.ncard_singleton] at h1
    omega
  obtain ⟨y, hyW, hyS⟩ : ∃ y ∈ W, y ∉ ({x, p.μ x} : Set α) := by
    have h1 := Set.le_ncard_sdiff ({x, p.μ x} : Set α) W
    have h2 : (W \ {x, p.μ x}).ncard ≠ 0 := by omega
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero h2
    exact ⟨y, hy.1, hy.2⟩
  have hyx : y ≠ x := fun hh => hyS (by simp [hh])
  have hyμ : y ≠ p.μ x := fun hh => hyS (by simp [hh])
  have hmove : ∀ u ∈ W, u ≠ x → u ≠ p.μ x →
      e x = x ∨ e x = p.μ x ∨ e x = u ∨ e x = p.μ u := by
    intro u hu hux huμ
    have hc := h x hx u hu hux huμ
    have hxμu : x ≠ p.μ u := fun hh => huμ (by rw [hh, p.inv])
    have hσx : (swap x (p.μ x) * swap u (p.μ u)) x = p.μ x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hux.symm hxμu,
        Equiv.swap_apply_left]
    have hk : ∀ t, e ((swap x (p.μ x) * swap u (p.μ u)) t)
        = (swap x (p.μ x) * swap u (p.μ u)) (e t) := by
      intro t
      have := congrArg (fun π : Perm α => π t) hc.eq
      simpa only [Equiv.Perm.mul_apply] using this
    have hk' : e (p.μ x) = (swap x (p.μ x) * swap u (p.μ u)) (e x) := by
      have := hk x
      rwa [hσx] at this
    by_contra hcon
    have h1 : e x ≠ x := fun h => hcon (Or.inl h)
    have h2 : e x ≠ p.μ x := fun h => hcon (Or.inr (Or.inl h))
    have h3 : e x ≠ u := fun h => hcon (Or.inr (Or.inr (Or.inl h)))
    have h4 : e x ≠ p.μ u := fun h => hcon (Or.inr (Or.inr (Or.inr h)))
    have hfix : (swap x (p.μ x) * swap u (p.μ u)) (e x) = e x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h3 h4,
        Equiv.swap_apply_of_ne_of_ne h1 h2]
    have hee : e (p.μ x) = e x := by rw [hk', hfix]
    exact p.fpf x (e.injective hee)
  obtain ⟨z, hzW, hzS⟩ : ∃ z ∈ W, z ∉ ({x, p.μ x, y, p.μ y} : Set α) := by
    have h4 : ({x, p.μ x, y, p.μ y} : Set α).ncard ≤ 4 := by
      have a1 := Set.ncard_insert_le x ({p.μ x, y, p.μ y} : Set α)
      have a2 := Set.ncard_insert_le (p.μ x) ({y, p.μ y} : Set α)
      have a3 := Set.ncard_insert_le y ({p.μ y} : Set α)
      have a4 := Set.ncard_singleton (p.μ y)
      omega
    have h1 := Set.le_ncard_sdiff ({x, p.μ x, y, p.μ y} : Set α) W
    have h2 : (W \ {x, p.μ x, y, p.μ y}).ncard ≠ 0 := by omega
    obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero h2
    exact ⟨z, hz.1, hz.2⟩
  have hzx : z ≠ x := fun hh => hzS (by simp [hh])
  have hzμx : z ≠ p.μ x := fun hh => hzS (by simp [hh])
  have hzy : z ≠ y := fun hh => hzS (by simp [hh])
  have hzμy : z ≠ p.μ y := fun hh => hzS (by simp [hh])
  have hA := hmove y hyW hyx hyμ
  have hB := hmove z hzW hzx hzμx
  have hyz : y ≠ z := fun hh => hzy hh.symm
  have hyμz : y ≠ p.μ z := fun hh => hzμy (by rw [hh, p.inv])
  have hμyz : p.μ y ≠ z := fun hh => hzμy hh.symm
  have hμyμz : p.μ y ≠ p.μ z := fun hh => hzy (by
    have := congrArg p.μ hh
    rw [p.inv, p.inv] at this
    exact this.symm)
  rcases hA with hA | hA | hA | hA <;> rcases hB with hB | hB | hB | hB <;>
    first
    | exact Or.inl hA
    | exact Or.inr hA
    | exact Or.inl hB
    | exact Or.inr hB
    | exact absurd (hA.symm.trans hB) (by assumption)

theorem altBigBlockFact {Y : Subgroup (Perm α)} {B : Set α} (hBl : MulAction.IsBlock (↥Y) B)
    {σ : Perm α} (hσ : σ ∈ Y) {b : α} (hb : b ∈ B) (hσb : σ b ∈ B) :
    ∀ z ∈ B, σ z ∈ B := by
  intro z hz
  let g : ↥Y := ⟨σ, hσ⟩
  have hg : ∀ w : α, g • w = σ w := fun _ => rfl
  have hgB : g • B = B := by
    by_contra hne
    have hdis : Disjoint (g • B) ((1 : ↥Y) • B) :=
      hBl (by rw [one_smul]; exact hne)
    rw [one_smul] at hdis
    have h1 : σ b ∈ g • B := Set.mem_smul_set.mpr ⟨b, hb, hg b⟩
    exact Set.disjoint_left.mp hdis h1 hσb
  have hmem : σ z ∈ g • B := Set.mem_smul_set.mpr ⟨z, hz, hg z⟩
  rwa [hgB] at hmem

theorem block_closed_core (p : FpfInv α) (h6 : 6 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hC : ∀ a b : α, b ≠ a → b ≠ p.μ a → swap a (p.μ a) * swap b (p.μ b) ∈ Y)
    {B : Set α} (hBl : MulAction.IsBlock (↥Y) B)
    (h2 : ∃ a ∈ B, ∃ b ∈ B, a ≠ b) : ∀ x ∈ B, p.μ x ∈ B := by
  intro x hx
  by_contra hnot
  have hxpz : ∀ z ∈ B, x ≠ p.μ z := fun z hz h => hnot (by rw [h, p.inv]; exact hz)
  have hzpx : ∀ z ∈ B, z ≠ p.μ x := fun z hz h => hnot (by rw [← h]; exact hz)
  have step1 : ∀ z ∈ B, z ≠ x → p.μ z ∈ B := by
    intro z hz hzx
    have hcard : (({x, p.μ x, z, p.μ z} : Finset α)).card < (Finset.univ : Finset α).card := by
      rw [Finset.card_univ]
      exact lt_of_le_of_lt Finset.card_le_four (by omega)
    obtain ⟨w, -, hwS⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwS
    obtain ⟨hwx, hwpx, hwz, hwpz⟩ := hwS
    have hu : swap z (p.μ z) * swap w (p.μ w) ∈ Y := hC z w hwz hwpz
    have hxw : x ≠ w := Ne.symm hwx
    have hxpw : x ≠ p.μ w := fun h => hwpx (by rw [h, p.inv])
    have hux : (swap z (p.μ z) * swap w (p.μ w)) x = x := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxw hxpw,
        swap_apply_of_ne_of_ne (Ne.symm hzx) (hxpz z hz)]
    have hzw : z ≠ w := Ne.symm hwz
    have hzpw : z ≠ p.μ w := fun h => hwpz (by rw [h, p.inv])
    have hzu : (swap z (p.μ z) * swap w (p.μ w)) z = p.μ z := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzw hzpw, swap_apply_left]
    have hxB : (swap z (p.μ z) * swap w (p.μ w)) x ∈ B := by
      rw [hux]; exact hx
    have hzB := altBigBlockFact hBl hu hx hxB z hz
    rwa [hzu] at hzB
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ B, z ≠ x := by
    obtain ⟨a, ha, b, hb, hab⟩ := h2
    by_cases hax : a = x
    · exact ⟨b, hb, fun hbx => hab (hax.trans hbx.symm)⟩
    · exact ⟨a, ha, hax⟩
  have hpz : p.μ z ∈ B := step1 z hz hzx
  have hpzx : p.μ z ≠ x := fun h => hzpx z hz (by rw [← h, p.inv])
  have hpzpx : p.μ z ≠ p.μ x := fun h => hzx (Equiv.injective p.μ h)
  have hw'Y : swap x (p.μ x) * swap z (p.μ z) ∈ Y := hC x z hzx (hzpx z hz)
  have hw'z : (swap x (p.μ x) * swap z (p.μ z)) z = p.μ z := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hpzx hpzpx]
  have hw'zB : (swap x (p.μ x) * swap z (p.μ z)) z ∈ B := by
    rw [hw'z]; exact hpz
  have hw'x : (swap x (p.μ x) * swap z (p.μ z)) x = p.μ x := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hzx) (hxpz z hz), swap_apply_left]
  have hw'xB := altBigBlockFact hBl hw'Y hz hw'zB x hx
  rw [hw'x] at hw'xB
  exact hnot hw'xB

theorem block_closed (p : FpfInv α) (h6 : 6 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {B : Set α} (hBl : MulAction.IsBlock (↥Y) B)
    (h2 : ∃ a ∈ B, ∃ b ∈ B, a ≠ b) : ∀ x ∈ B, p.μ x ∈ B := by
  have hC : ∀ a b : α, b ≠ a → b ≠ p.μ a → swap a (p.μ a) * swap b (p.μ b) ∈ Y := hB
  exact block_closed_core p h6 hC hBl h2

open scoped Pointwise in
theorem exists_bad_pair (p : FpfInv α) (h3 : 3 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hprim : MulAction.IsPreprimitive (↥Y) α) :
    ∃ n ∈ Y, ∃ x, p.μ (n x) ≠ n (p.μ x) := by
  by_contra hcon
  have h : ∀ n ∈ Y, ∀ x, p.μ (n x) = n (p.μ x) := by
    intro n hn x
    by_contra hne
    exact hcon ⟨n, hn, x, hne⟩
  have hpos : 0 < Fintype.card α := by omega
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp hpos
  have pair_eq : ∀ y y' : α, (y' = y ∨ y' = p.μ y) →
      ({y, p.μ y} : Set α) = {y', p.μ y'} := by
    intro y y' hy'
    rcases hy' with e | e
    · rw [e]
    · rw [e, p.inv]
      exact Set.pair_comm _ _
  have aux : ∀ y y' z : α, (z = y ∨ z = p.μ y) → (z = y' ∨ z = p.μ y') →
      (y' = y ∨ y' = p.μ y) := by
    intro y y' z hz hz'
    rcases hz with h0 | h0 <;> rcases hz' with h1 | h1
    · exact Or.inl (h1.symm.trans h0)
    · have e : y = p.μ y' := h0.symm.trans h1
      refine Or.inr ?_
      rw [e, p.inv]
    · exact Or.inr (h1.symm.trans h0)
    · have e : p.μ y = p.μ y' := h0.symm.trans h1
      refine Or.inl ?_
      have e2 : p.μ (p.μ y) = p.μ (p.μ y') := by rw [e]
      rw [p.inv, p.inv] at e2
      exact e2.symm
  have pair_disj : ∀ y y' : α, ({y, p.μ y} : Set α) = {y', p.μ y'} ∨
      Disjoint ({y, p.μ y} : Set α) {y', p.μ y'} := by
    intro y y'
    by_cases hd : Disjoint ({y, p.μ y} : Set α) {y', p.μ y'}
    · exact Or.inr hd
    · left
      obtain ⟨z, hz, hz'⟩ := Set.not_disjoint_iff.mp hd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz hz'
      exact pair_eq y y' (aux y y' z hz hz')
  have key : ∀ g : ↥Y, g • ({x₀, p.μ x₀} : Set α) =
      ({(g : Perm α) x₀, p.μ ((g : Perm α) x₀)} : Set α) := by
    intro g
    have e1 : g • x₀ = (g : Perm α) x₀ := rfl
    have e2 : g • p.μ x₀ = (g : Perm α) (p.μ x₀) := rfl
    have e3 : p.μ ((g : Perm α) x₀) = (g : Perm α) (p.μ x₀) := h (g : Perm α) g.2 x₀
    rw [Set.smul_set_insert, Set.smul_set_singleton, e1, e2, e3]
  have hblock : MulAction.IsBlock (↥Y) ({x₀, p.μ x₀} : Set α) := by
    rw [MulAction.isBlock_iff_smul_eq_smul_or_disjoint]
    intro g₁ g₂
    rw [key g₁, key g₂]
    exact pair_disj _ _
  rcases MulAction.IsBlock.subsingleton_or_eq_univ hblock with hsub | huniv
  · have hx : x₀ ∈ ({x₀, p.μ x₀} : Set α) := Set.mem_insert _ _
    have hy : p.μ x₀ ∈ ({x₀, p.μ x₀} : Set α) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact p.fpf x₀ (hsub hx hy).symm
  · obtain ⟨a, b, c, hab, hac, hbc⟩ :=
      Fintype.two_lt_card_iff.mp (show 2 < Fintype.card α by omega)
    have ha : a ∈ ({x₀, p.μ x₀} : Set α) := by rw [huniv]; exact Set.mem_univ a
    have hb : b ∈ ({x₀, p.μ x₀} : Set α) := by rw [huniv]; exact Set.mem_univ b
    have hc : c ∈ ({x₀, p.μ x₀} : Set α) := by rw [huniv]; exact Set.mem_univ c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
    rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rcases hc with h4 | h4 <;>
      first
        | exact hab (h1.trans h2.symm)
        | exact hac (h1.trans h4.symm)
        | exact hbc (h2.trans h4.symm)

theorem th3_swap_commute {a b c d : α} (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c) (h4 : b ≠ d) :
    swap a b * swap c d = swap c d * swap a b := by
  ext z
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem th3_core {G : Type*} [Group G] {a1 a2 a3 a4 : G}
    (h23 : a2 * a3 = a3 * a2) (h21 : a2 * a1 = a1 * a2) (h41 : a4 * a1 = a1 * a4)
    (h43 : a4 * a3 = a3 * a4) (h24 : a2 * a4 = a4 * a2) (h22 : a2 * a2 = 1)
    (h44 : a4 * a4 = 1) :
    (a1 * a2 * (a3 * a4)) * (a1 * a2 * (a3 * a4)) = (a1 * a3) * (a1 * a3) := by
  have hX : a1 * a2 * (a3 * a4) = (a1 * a3) * (a2 * a4) := by
    calc a1 * a2 * (a3 * a4) = a1 * (a2 * a3) * a4 := by simp only [mul_assoc]
      _ = a1 * (a3 * a2) * a4 := by rw [h23]
      _ = a1 * a3 * (a2 * a4) := by simp only [mul_assoc]
  have hdc : (a2 * a4) * (a1 * a3) = (a1 * a3) * (a2 * a4) := by
    calc (a2 * a4) * (a1 * a3) = a2 * (a4 * a1) * a3 := by simp only [mul_assoc]
      _ = a2 * (a1 * a4) * a3 := by rw [h41]
      _ = (a2 * a1) * a4 * a3 := by simp only [mul_assoc]
      _ = (a1 * a2) * a4 * a3 := by rw [h21]
      _ = a1 * a2 * (a4 * a3) := by simp only [mul_assoc]
      _ = a1 * a2 * (a3 * a4) := by rw [h43]
      _ = a1 * (a2 * a3) * a4 := by simp only [mul_assoc]
      _ = a1 * (a3 * a2) * a4 := by rw [h23]
      _ = a1 * a3 * (a2 * a4) := by simp only [mul_assoc]
  have hd2 : (a2 * a4) * (a2 * a4) = 1 := by
    calc (a2 * a4) * (a2 * a4) = a2 * (a4 * a2) * a4 := by simp only [mul_assoc]
      _ = a2 * (a2 * a4) * a4 := by rw [← h24]
      _ = (a2 * a2) * (a4 * a4) := by simp only [mul_assoc]
      _ = 1 := by rw [h22, h44, one_mul]
  calc (a1 * a2 * (a3 * a4)) * (a1 * a2 * (a3 * a4))
      = (a1 * a3) * (a2 * a4) * ((a1 * a3) * (a2 * a4)) := by rw [hX]
    _ = (a1 * a3) * ((a2 * a4) * (a1 * a3)) * (a2 * a4) := by simp only [mul_assoc]
    _ = (a1 * a3) * ((a1 * a3) * (a2 * a4)) * (a2 * a4) := by rw [hdc]
    _ = (a1 * a3) * (a1 * a3) * ((a2 * a4) * (a2 * a4)) := by simp only [mul_assoc]
    _ = (a1 * a3) * (a1 * a3) := by rw [hd2, mul_one]

theorem th3_exists_not_mem {S : Finset α} (h : S.card < Fintype.card α) : ∃ z, z ∉ S := by
  have hlt : S.card < (Finset.univ : Finset α).card := by
    rw [Finset.card_univ]
    exact h
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨z, hz⟩

theorem th3_main (p : FpfInv α) (h10 : 10 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB2 : ∀ a b : α, b ≠ a → b ≠ p.μ a → swap a (p.μ a) * swap b (p.μ b) ∈ Y)
    {n : Perm α} (hn : n ∈ Y) {x : α} (hx : p.μ (n x) ≠ n (p.μ x)) :
    ∃ g ∈ Y, g.IsThreeCycle := by
  have hμμ : ∀ y, p.μ (p.μ y) = y := p.inv
  have hfpf : ∀ y, p.μ y ≠ y := p.fpf
  have hmu : ∀ a b, p.μ a = b → a = p.μ b := by
    intro a b h
    subst h
    exact (hμμ a).symm
  have hxμ : x ≠ p.μ x := fun h => hfpf x h.symm
  have hu12 : n x ≠ n (p.μ x) := fun h => hxμ (n.injective h)
  have hu11 : n x ≠ p.μ (n x) := fun h => hfpf (n x) h.symm
  have hR : ({n x, p.μ (n x), n (p.μ x), p.μ (n (p.μ x))} : Finset α).card < Fintype.card α := by
    have h4 : ({n x, p.μ (n x), n (p.μ x), p.μ (n (p.μ x))} : Finset α).card ≤ 4 :=
      Finset.card_le_four
    omega
  obtain ⟨r, hr⟩ := th3_exists_not_mem hR
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hr
  have hr'1 : p.μ r ≠ n x := fun h => hr2 (hmu r (n x) h)
  have hr'2 : p.μ r ≠ p.μ (n x) := fun h => hr1 (p.μ.injective h)
  have hr'3 : p.μ r ≠ n (p.μ x) := fun h => hr4 (hmu r (n (p.μ x)) h)
  have hδ₁ : swap (n x) (p.μ (n x)) * swap r (p.μ r) ∈ Y := hB2 (n x) r hr1 hr2
  obtain ⟨T, hT⟩ : ∃ T : Finset α, T = {p.μ (n x), r, p.μ r} := ⟨_, rfl⟩
  have hTmem : ∀ t, t ∈ T ↔ t = p.μ (n x) ∨ t = r ∨ t = p.μ r := by
    intro t
    rw [hT]
    simp
  have hTcard : T.card ≤ 3 := by
    rw [hT]
    exact Finset.card_le_three
  obtain ⟨B, hB'⟩ : ∃ B : Finset α,
      B = {x, p.μ x} ∪ T.image (fun t => n⁻¹ t) ∪ T.image (fun t => p.μ (n⁻¹ t)) := ⟨_, rfl⟩
  have hBcard : B.card < Fintype.card α := by
    rw [hB']
    have h1 := Finset.card_union_le ({x, p.μ x} ∪ T.image (fun t => n⁻¹ t))
      (T.image (fun t => p.μ (n⁻¹ t)))
    have h2 := Finset.card_union_le ({x, p.μ x} : Finset α) (T.image (fun t => n⁻¹ t))
    have h3 : (T.image (fun t => n⁻¹ t)).card ≤ T.card := Finset.card_image_le
    have h4 : (T.image (fun t => p.μ (n⁻¹ t))).card ≤ T.card := Finset.card_image_le
    have h5 : ({x, p.μ x} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨q, hq⟩ := th3_exists_not_mem hBcard
  have hqx : q ≠ x := fun h => hq (by rw [hB', h]; simp)
  have hqx' : q ≠ p.μ x := fun h => hq (by rw [hB', h]; simp)
  have hqT : ∀ t ∈ T, n q ≠ t := by
    intro t ht he
    apply hq
    rw [hB']
    refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, ?_⟩))
    subst he
    simp
  have hqT' : ∀ t ∈ T, n (p.μ q) ≠ t := by
    intro t ht he
    apply hq
    rw [hB']
    refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, ?_⟩)
    subst he
    simp [hμμ]
  have hnq1 : n q ≠ p.μ (n x) := hqT (p.μ (n x)) ((hTmem _).2 (Or.inl rfl))
  have hnq2 : n q ≠ r := hqT r ((hTmem _).2 (Or.inr (Or.inl rfl)))
  have hnq3 : n q ≠ p.μ r := hqT (p.μ r) ((hTmem _).2 (Or.inr (Or.inr rfl)))
  have hnq'1 : n (p.μ q) ≠ p.μ (n x) := hqT' (p.μ (n x)) ((hTmem _).2 (Or.inl rfl))
  have hnq'2 : n (p.μ q) ≠ r := hqT' r ((hTmem _).2 (Or.inr (Or.inl rfl)))
  have hnq'3 : n (p.μ q) ≠ p.μ r := hqT' (p.μ r) ((hTmem _).2 (Or.inr (Or.inr rfl)))
  have hnqx : n q ≠ n x := fun h => hqx (n.injective h)
  have hnqx2 : n q ≠ n (p.μ x) := fun h => hqx' (n.injective h)
  have hnq'x : n (p.μ q) ≠ n x := fun h => hqx' (hmu q x (n.injective h))
  have hnq'x2 : n (p.μ q) ≠ n (p.μ x) := fun h => hqx (p.μ.injective (n.injective h))
  have hδ₀ : swap x (p.μ x) * swap q (p.μ q) ∈ Y := hB2 x q hqx hqx'
  have hconj : n * (swap x (p.μ x) * swap q (p.μ q)) * n⁻¹
      = swap (n x) (n (p.μ x)) * swap (n q) (n (p.μ q)) := by
    rw [Equiv.swap_apply_apply n x (p.μ x), Equiv.swap_apply_apply n q (p.μ q)]
    simp only [mul_assoc, inv_mul_cancel_left]
  have hδ₂ : swap (n x) (n (p.μ x)) * swap (n q) (n (p.μ q)) ∈ Y := by
    rw [← hconj]
    exact Y.mul_mem (Y.mul_mem hn hδ₀) (Y.inv_mem hn)
  have c23 : swap r (p.μ r) * swap (n x) (n (p.μ x))
      = swap (n x) (n (p.μ x)) * swap r (p.μ r) :=
    th3_swap_commute hr1 hr3 hr'1 hr'3
  have c21 : swap r (p.μ r) * swap (n x) (p.μ (n x))
      = swap (n x) (p.μ (n x)) * swap r (p.μ r) :=
    th3_swap_commute hr1 hr2 hr'1 hr'2
  have c24 : swap r (p.μ r) * swap (n q) (n (p.μ q))
      = swap (n q) (n (p.μ q)) * swap r (p.μ r) :=
    th3_swap_commute hnq2.symm hnq'2.symm hnq3.symm hnq'3.symm
  have c41 : swap (n q) (n (p.μ q)) * swap (n x) (p.μ (n x))
      = swap (n x) (p.μ (n x)) * swap (n q) (n (p.μ q)) :=
    th3_swap_commute hnqx hnq1 hnq'x hnq'1
  have c43 : swap (n q) (n (p.μ q)) * swap (n x) (n (p.μ x))
      = swap (n x) (n (p.μ x)) * swap (n q) (n (p.μ q)) :=
    th3_swap_commute hnqx hnqx2 hnq'x hnq'x2
  have hgY : swap (n x) (p.μ (n x)) * swap r (p.μ r)
      * (swap (n x) (n (p.μ x)) * swap (n q) (n (p.μ q))) ∈ Y :=
    Y.mul_mem hδ₁ hδ₂
  refine ⟨_, Y.mul_mem hgY hgY, ?_⟩
  rw [th3_core c23 c21 c41 c43 c24 (Equiv.swap_mul_self r (p.μ r))
    (Equiv.swap_mul_self (n q) (n (p.μ q)))]
  exact Equiv.Perm.IsThreeCycle.isThreeCycle_sq
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same hu11 hu12 hx)

theorem three_cycle_of_bad (p : FpfInv α) (h10 : 10 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {n : Perm α} (hn : n ∈ Y) {x : α} (hx : p.μ (n x) ≠ n (p.μ x)) :
    ∃ g ∈ Y, g.IsThreeCycle := by
  have hB2 : ∀ a b : α, b ≠ a → b ≠ p.μ a → swap a (p.μ a) * swap b (p.μ b) ∈ Y := by
    dsimp only [FpfInv.Contained] at hB
    exact hB
  exact th3_main p h10 hB2 hn hx

theorem open_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have h3 : (commutator A).map e.toMonoidHom = commutator B := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [← h3, h1, Subgroup.map_top_of_surjective _ e.surjective]
  · have hc : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
      ext b
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact MulEquivClass.apply_mem_center e ha
      · intro hb
        refine ⟨e.symm b, MulEquivClass.apply_mem_center e.symm hb, by simp⟩
    exact (MulEquiv.isSimpleGroup_congr (QuotientGroup.congr (Subgroup.center A)
      (Subgroup.center B) e hc)).1 h2

theorem coe_swap_subtype {β : Type} [DecidableEq β] {S : Set β} (a b t : ↥S) :
    (((swap a b) t : ↥S) : β) = swap (a : β) (b : β) (t : β) := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all [Subtype.ext_iff]

end CFSG.QuasithinUnique.L246C127.AltBig
