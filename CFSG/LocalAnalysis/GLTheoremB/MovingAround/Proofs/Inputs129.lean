module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129k
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123a

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs129

open Equiv Equiv.Perm

section PermFacts

variable {α : Type*} [DecidableEq α]

@[expose] def c3 (a b c : α) : Perm α := swap a c * swap a b

theorem c3_apply_left {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) : c3 a b c a = b := by
  simp [c3, swap_apply_of_ne_of_ne hab.symm hbc]

theorem c3_apply_mid {a b c : α} : c3 a b c b = c := by
  simp [c3]

theorem c3_apply_right {a b c : α} (hac : a ≠ c) (hbc : b ≠ c) : c3 a b c c = a := by
  simp [c3, swap_apply_of_ne_of_ne hac.symm hbc.symm]

theorem c3_apply_of_ne {a b c x : α} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) : c3 a b c x = x := by
  simp [c3, swap_apply_of_ne_of_ne hxa hxb, swap_apply_of_ne_of_ne hxa hxc]

theorem comm_eq_c3 {σ τ : Perm α} {x₀ : α} (h : ∀ y, σ y ≠ y → τ y ≠ y → y = x₀)
    (hσ : σ x₀ ≠ x₀) (hτ : τ x₀ ≠ x₀) :
    σ * τ * σ⁻¹ * τ⁻¹ = c3 x₀ (σ x₀) (τ x₀) := by
  have hσσ : σ (σ x₀) ≠ σ x₀ := fun h' => hσ (σ.injective h')
  have hττ : τ (τ x₀) ≠ τ x₀ := fun h' => hτ (τ.injective h')
  have hτσ : τ (σ x₀) = σ x₀ := by
    by_contra hne
    exact hσ (h _ hσσ hne)
  have hστ : σ (τ x₀) = τ x₀ := by
    by_contra hne
    exact hτ (h _ hne hττ)
  have hst : σ x₀ ≠ τ x₀ := by
    intro he
    rw [← he] at hστ
    exact hσσ hστ
  have hinv : ∀ (f : Perm α) (x : α), f x = x → f⁻¹ x = x := fun f x hx => by
    rw [Perm.inv_eq_iff_eq]; exact hx.symm
  ext y
  simp only [Perm.mul_apply]
  by_cases hy0 : y = x₀
  · subst hy0
    rw [c3_apply_left (Ne.symm hσ) hst]
    set z := τ⁻¹ y with hz
    have hτz : τ z = y := by simp [hz]
    have hzy : z ≠ y := by
      intro h'
      rw [h'] at hτz
      exact hτ hτz
    have hσz : σ z = z := by
      by_contra hne
      exact hzy (h z hne (by rw [hτz]; exact Ne.symm hzy))
    rw [hinv σ z hσz, hτz]
  by_cases hy1 : y = σ x₀
  · subst hy1
    rw [c3_apply_mid, hinv τ _ hτσ]
    have h1 : σ⁻¹ (σ x₀) = x₀ := by simp
    rw [h1, hστ]
  by_cases hy2 : y = τ x₀
  · subst hy2
    rw [c3_apply_right (Ne.symm hτ) hst]
    have h1 : τ⁻¹ (τ x₀) = x₀ := by simp
    rw [h1]
    set z := σ⁻¹ x₀ with hz
    have hσz : σ z = x₀ := by simp [hz]
    have hzx : z ≠ x₀ := by
      intro h'
      rw [h'] at hσz
      exact hσ hσz
    have hτz : τ z = z := by
      by_contra hne
      exact hzx (h z (by rw [hσz]; exact Ne.symm hzx) hne)
    rw [hτz, hσz]
  rw [c3_apply_of_ne hy0 hy1 hy2]
  by_cases hτy : τ y = y
  · rw [hinv τ y hτy]
    by_cases hσy : σ y = y
    · rw [hinv σ y hσy, hτy, hσy]
    · set z := σ⁻¹ y with hz
      have hσz : σ z = y := by simp [hz]
      have hzy : z ≠ y := by
        intro h'
        rw [h'] at hσz
        exact hσy hσz
      have hzx : z ≠ x₀ := fun h' => hy1 (by rw [← hσz, h'])
      have hτz : τ z = z := by
        by_contra hne
        exact hzx (h z (by rw [hσz]; exact Ne.symm hzy) hne)
      rw [hτz, hσz]
  · have hσy : σ y = y := by
      by_contra hne
      exact hy0 (h y hne hτy)
    set z := τ⁻¹ y with hz
    have hτz : τ z = y := by simp [hz]
    have hzy : z ≠ y := by
      intro h'
      rw [h'] at hτz
      exact hτy hτz
    have hzx : z ≠ x₀ := fun h' => hy2 (by rw [← hτz, h'])
    have hσz : σ z = z := by
      by_contra hne
      exact hzx (h z hne (by rw [hτz]; exact Ne.symm hzy))
    rw [hinv σ z hσz, hτz, hσy]

theorem c3_eq_swap_mul_swap {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c3 a b c = swap a b * swap b c := by
  ext z
  simp only [c3, Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem c3_eq_mul {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    c3 a b c = c3 a d c * c3 a b d := by
  ext z
  simp only [c3, Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

variable [Fintype α]

theorem isThreeCycle_c3 {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (c3 a b c).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same hac hab hbc.symm

theorem sign_eq_one_of_pow {p : ℕ} (hp : Odd p) {σ : Perm α} (h : σ ^ p = 1) : sign σ = 1 := by
  have h1 : (sign σ) ^ p = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (sign σ) with h2 | h2
  · exact h2
  · rw [h2, hp.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem map_alt_le {β : Type*} [Fintype β] [DecidableEq β] (f : Perm α →* Perm β) :
    (alternatingGroup α).map f ≤ alternatingGroup β := by
  rw [← closure_three_cycles_eq_alternating (α := α), MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  have h3 : c ^ 3 = 1 := by
    have := hc.orderOf
    rw [← this]
    exact pow_orderOf_eq_one c
  refine mem_alternatingGroup.2 (sign_eq_one_of_pow (p := 3) (by decide) ?_)
  rw [← map_pow, h3, map_one]

end PermFacts

section Gens

@[expose] def hypGens (p : ℕ) (V : Type*) [Group V] [Fintype V] [DecidableEq V] : Set (Perm V) :=
  {g | g ∈ alternatingGroup V ∧ ∃ H : Subgroup V, H.index ≤ p ∧ ∀ h ∈ H, ∀ x, g (h * x) = h * g x}

variable {p : ℕ} {V : Type*} [CommGroup V] [Fintype V] [DecidableEq V]

theorem mulLeft_pow_apply (v : V) (n : ℕ) (x : V) : ((Equiv.mulLeft v) ^ n) x = v ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply, ih, Equiv.coe_mulLeft, pow_succ', mul_assoc]

theorem mulLeft_mem_closure (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1) (v : V) :
    Equiv.mulLeft v ∈ Subgroup.closure (hypGens p V) := by
  apply Subgroup.subset_closure
  refine ⟨mem_alternatingGroup.2 (sign_eq_one_of_pow (hp.odd_of_ne_two hp2) ?_), ⊤,
    by rw [Subgroup.index_top]; exact hp.one_lt.le, fun h _ x => ?_⟩
  · ext x
    rw [mulLeft_pow_apply, hexp v, one_mul, Perm.one_apply]
  · simp only [Equiv.coe_mulLeft]
    exact mul_left_comm v h x

theorem alt_le_of_card_le (hcard : Nat.card V ≤ p) :
    alternatingGroup V ≤ Subgroup.closure (hypGens p V) := fun g hg =>
  Subgroup.subset_closure ⟨hg, ⊥, by rw [Subgroup.index_bot]; exact hcard, fun h hh x => by
    rw [Subgroup.mem_bot] at hh
    rw [hh, one_mul, one_mul]⟩

omit [DecidableEq V] in
theorem zpowers_eq_of_mem (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1) {y z : V}
    (hz : z ∈ Subgroup.zpowers y) (hz1 : z ≠ 1) : Subgroup.zpowers z = Subgroup.zpowers y := by
  haveI := Fact.mk hp
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hz
    exact hz1 hz
  apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hz)
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hexp y) hy1,
    orderOf_eq_prime (hexp z) hz1]

omit [DecidableEq V] in
theorem inf_zpowers_eq_bot (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1) {u w : V}
    (hw : w ∉ Subgroup.zpowers u) {z : V} (hzu : z ∈ Subgroup.zpowers u)
    (hzw : z ∈ Subgroup.zpowers w) : z = 1 := by
  by_contra hz1
  have h1 := zpowers_eq_of_mem hp hexp hzw hz1
  have h2 := zpowers_eq_of_mem hp hexp hzu hz1
  apply hw
  rw [← h2, h1]
  exact Subgroup.mem_zpowers w

open Classical in
@[expose] noncomputable def ptr (u x : V) : Perm V :=
  ofSubtype ((Equiv.mulLeft u).subtypePerm (p := fun v => v * x⁻¹ ∈ Subgroup.zpowers u)
    (fun v => by
      simp only [Equiv.coe_mulLeft]
      rw [mul_assoc]
      exact Subgroup.mul_mem_cancel_left _ (Subgroup.mem_zpowers u)))

theorem ptr_apply_of_mem {u x v : V} (hv : v * x⁻¹ ∈ Subgroup.zpowers u) : ptr u x v = u * v := by
  unfold ptr
  rw [ofSubtype_apply_of_mem (a := v) _ hv]
  simp

theorem ptr_apply_of_not_mem {u x v : V} (hv : v * x⁻¹ ∉ Subgroup.zpowers u) : ptr u x v = v := by
  unfold ptr
  exact ofSubtype_apply_of_not_mem _ hv

theorem ptr_pow_apply (u x : V) (n : ℕ) (v : V) :
    ((ptr u x) ^ n) v = if v * x⁻¹ ∈ Subgroup.zpowers u then u ^ n * v else v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih]
    split_ifs with hv
    · have hv' : u ^ n * v * x⁻¹ ∈ Subgroup.zpowers u := by
        rw [mul_assoc]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) n) hv
      rw [ptr_apply_of_mem hv', ← mul_assoc, ← pow_succ']
    · exact ptr_apply_of_not_mem hv

theorem ptr_comm (u x : V) {h : V} (hh : h ∈ Subgroup.zpowers u) (v : V) :
    ptr u x (h * v) = h * ptr u x v := by
  by_cases hv : v * x⁻¹ ∈ Subgroup.zpowers u
  · have hv' : h * v * x⁻¹ ∈ Subgroup.zpowers u := by
      rw [mul_assoc]; exact Subgroup.mul_mem _ hh hv
    rw [ptr_apply_of_mem hv', ptr_apply_of_mem hv]
    exact mul_left_comm u h v
  · have hv' : h * v * x⁻¹ ∉ Subgroup.zpowers u := by
      rw [mul_assoc]; exact fun h' => hv ((Subgroup.mul_mem_cancel_left _ hh).1 h')
    rw [ptr_apply_of_not_mem hv', ptr_apply_of_not_mem hv]

theorem ptr_mem_hypGens (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    (hcard : Nat.card V ≤ p ^ 2) {u : V} (hu : u ≠ 1) (x : V) : ptr u x ∈ hypGens p V := by
  haveI := Fact.mk hp
  refine ⟨mem_alternatingGroup.2 (sign_eq_one_of_pow (hp.odd_of_ne_two hp2) ?_),
    Subgroup.zpowers u, ?_, fun h hh v => ptr_comm u x hh v⟩
  · ext v
    rw [ptr_pow_apply, hexp u, one_mul, Perm.one_apply]
    split_ifs <;> rfl
  · have h1 := (Subgroup.zpowers u).index_mul_card
    rw [Nat.card_zpowers, orderOf_eq_prime (hexp u) hu] at h1
    have h2 : (Subgroup.zpowers u).index * p ≤ p * p := by rw [h1, ← sq]; exact hcard
    exact Nat.le_of_mul_le_mul_right h2 hp.pos

theorem c3_mem_closure_base (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    (hcard : Nat.card V ≤ p ^ 2) {u w : V} (hu : u ≠ 1) (hw : w ∉ Subgroup.zpowers u) (x : V) :
    c3 x (u * x) (w * x) ∈ Subgroup.closure (hypGens p V) := by
  have hw1 : w ≠ 1 := fun h => hw (h ▸ Subgroup.one_mem _)
  have hx : x * x⁻¹ ∈ Subgroup.zpowers u := by rw [mul_inv_cancel]; exact Subgroup.one_mem _
  have hx' : x * x⁻¹ ∈ Subgroup.zpowers w := by rw [mul_inv_cancel]; exact Subgroup.one_mem _
  have ha : ptr u x x = u * x := ptr_apply_of_mem hx
  have hb : ptr w x x = w * x := ptr_apply_of_mem hx'
  have key := comm_eq_c3 (σ := ptr u x) (τ := ptr w x) (x₀ := x) (fun y hy1 hy2 => by
      have h1 : y * x⁻¹ ∈ Subgroup.zpowers u := by
        by_contra h'
        exact hy1 (ptr_apply_of_not_mem h')
      have h2 : y * x⁻¹ ∈ Subgroup.zpowers w := by
        by_contra h'
        exact hy2 (ptr_apply_of_not_mem h')
      have h3 := inf_zpowers_eq_bot hp hexp hw h1 h2
      exact mul_inv_eq_one.1 h3)
    (by rw [ha]; exact fun h => hu (mul_eq_right.1 h))
    (by rw [hb]; exact fun h => hw1 (mul_eq_right.1 h))
  rw [ha, hb] at key
  rw [← key]
  have hga := Subgroup.subset_closure (ptr_mem_hypGens hp hp2 hexp hcard hu x)
  have hgb := Subgroup.subset_closure (ptr_mem_hypGens hp hp2 hexp hcard hw1 x)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hga hgb)
    (Subgroup.inv_mem _ hga)) (Subgroup.inv_mem _ hgb)

theorem alt_le_base (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    (hcard1 : p < Nat.card V) (hcard : Nat.card V ≤ p ^ 2) :
    alternatingGroup V ≤ Subgroup.closure (hypGens p V) := by
  haveI := Fact.mk hp
  have hnc : ∀ a b c : V, b * a⁻¹ ≠ 1 → c * a⁻¹ ∉ Subgroup.zpowers (b * a⁻¹) →
      c3 a b c ∈ Subgroup.closure (hypGens p V) := by
    intro a b c hu hw
    have := c3_mem_closure_base hp hp2 hexp hcard hu hw a
    rwa [inv_mul_cancel_right, inv_mul_cancel_right] at this
  rw [← closure_three_cycles_eq_alternating (α := V), Subgroup.closure_le]
  intro g hg
  obtain ⟨a, ha⟩ := hg.isCycle.nonempty_support
  have hdec := (hg.eq_swap_mul_swap_iff_mem_support).2 ha
  have hnd := (hg.nodup_iff_mem_support (a := a)).2 ha
  obtain ⟨hA, hBC⟩ := List.nodup_cons.1 hnd
  obtain ⟨hB, -⟩ := List.nodup_cons.1 hBC
  have hab : a ≠ g a := fun h => hA (List.mem_cons.2 (Or.inl h))
  have hac : a ≠ g (g a) := fun h => hA (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl h))))
  have hbc : g a ≠ g (g a) := fun h => hB (List.mem_singleton.2 h)
  set b := g a with hb
  set c := g (g a) with hc
  have hg3 : g = c3 a b c := by rw [hdec, c3_eq_swap_mul_swap hab hac hbc]
  rw [SetLike.mem_coe, hg3]
  have hu : b * a⁻¹ ≠ 1 := fun h => hab (mul_inv_eq_one.1 h).symm
  by_cases hcol : c * a⁻¹ ∈ Subgroup.zpowers (b * a⁻¹)
  ·
    obtain ⟨v, hv⟩ : ∃ v : V, v ∉ Subgroup.zpowers (b * a⁻¹) := by
      by_contra hcon
      push Not at hcon
      have h1 : Subgroup.zpowers (b * a⁻¹) = ⊤ := eq_top_iff.2 fun v _ => hcon v
      have h2 := Nat.card_zpowers (b * a⁻¹)
      rw [h1, Subgroup.card_top, orderOf_eq_prime (hexp _) hu] at h2
      omega
    set d := v * a with hd
    have hda : d * a⁻¹ = v := by rw [hd, mul_inv_cancel_right]
    have had : a ≠ d := fun h => hv (by rw [← hda, ← h, mul_inv_cancel]; exact Subgroup.one_mem _)
    have hbd : b ≠ d := fun h => hv (by rw [← hda, ← h]; exact Subgroup.mem_zpowers _)
    have hcd : c ≠ d := fun h => hv (by rw [← hda, ← h]; exact hcol)
    rw [c3_eq_mul hab hac hbc had hbd hcd]
    have hv1 : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    have hca1 : c * a⁻¹ ≠ 1 := fun h => hac (mul_inv_eq_one.1 h).symm
    refine Subgroup.mul_mem _ (hnc a d c (by rw [hda]; exact hv1) ?_)
      (hnc a b d hu (by rw [hda]; exact hv))
    rw [hda]
    intro hcv
    have h1 := zpowers_eq_of_mem hp hexp hcv hca1
    have h2 := zpowers_eq_of_mem hp hexp hcol hca1
    apply hv
    rw [← h2, h1]
    exact Subgroup.mem_zpowers v
  · exact hnc a b c hu hcol

end Gens

section Transport

variable {p : ℕ} {V : Type*} [CommGroup V]

theorem pow_not_mem [Finite V] (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1) {H : Subgroup V} {u : V}
    (hu : u ∉ H) {d : ℕ} (hd0 : 0 < d) (hdp : d < p) : u ^ d ∉ H := by
  intro hd
  haveI := Fact.mk hp
  have hu1 : u ≠ 1 := fun h => hu (h ▸ H.one_mem)
  have hz1 : u ^ d ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [orderOf_eq_prime (hexp u) hu1] at this
    exact absurd (Nat.le_of_dvd hd0 this) (by omega)
  have h1 : Subgroup.zpowers (u ^ d) = Subgroup.zpowers u :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) d))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hexp u) hu1,
        orderOf_eq_prime (hexp _) hz1])
  apply hu
  have : u ∈ Subgroup.zpowers (u ^ d) := by rw [h1]; exact Subgroup.mem_zpowers u
  exact (Subgroup.zpowers_le.2 hd) this

theorem decomp_unique [Finite V] (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1) {H : Subgroup V} {u : V}
    (hu : u ∉ H) {j j' : ℕ} (hj : j < p) (hj' : j' < p) {h h' : V} (hh : h ∈ H) (hh' : h' ∈ H)
    (he : u ^ j * h = u ^ j' * h') : j = j' ∧ h = h' := by
  have key : ∀ {a b : ℕ}, a < p → b ≤ a → ∀ {x y : V}, x ∈ H → y ∈ H → u ^ a * x = u ^ b * y →
      a = b := by
    intro a b ha hba x y hx hy hxy
    by_contra hne
    have h1 : u ^ (a - b) = y * x⁻¹ := by
      rw [pow_sub u hba, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, hxy,
        mul_comm]
    exact pow_not_mem hp hexp hu (d := a - b) (by omega) (by omega)
      (h1 ▸ H.mul_mem hy (H.inv_mem hx))
  have hjj : j = j' := by
    rcases le_total j' j with h1 | h1
    · exact key hj h1 hh hh' he
    · exact (key hj' h1 hh' hh he.symm).symm
  subst hjj
  exact ⟨rfl, mul_left_cancel he⟩

@[expose] noncomputable def decompEquiv [Finite V] (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1)
    {H : Subgroup V} (hH : H.index = p) {u : V} (hu : u ∉ H) : ↥H × Fin p ≃ V :=
  Equiv.ofBijective (fun q => u ^ (q.2 : ℕ) * (q.1 : V)) (by
    refine Function.Injective.bijective_of_nat_card_le (fun q q' hq => ?_) ?_
    · obtain ⟨h1, h2⟩ := decomp_unique hp hexp hu q.2.2 q'.2.2 q.1.2 q'.1.2 hq
      exact Prod.ext (Subtype.ext h2) (Fin.ext h1)
    · rw [Nat.card_prod, Nat.card_fin, ← H.index_mul_card, hH, mul_comm])

theorem decompEquiv_apply [Finite V] (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1)
    {H : Subgroup V} (hH : H.index = p) {u : V} (hu : u ∉ H) (q : ↥H × Fin p) :
    decompEquiv hp hexp hH hu q = u ^ (q.2 : ℕ) * (q.1 : V) := rfl

theorem decomp_exists [Finite V] (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1)
    {H : Subgroup V} (hH : H.index = p) {u : V} (hu : u ∉ H) (x : V) :
    ∃ h : ↥H, ∃ j : Fin p, x = u ^ (j : ℕ) * (h : V) := by
  obtain ⟨q, hq⟩ := (decompEquiv hp hexp hH hu).surjective x
  exact ⟨q.1, q.2, hq.symm⟩

@[expose] def prodHom (α β : Type*) : Perm α →* Perm (α × β) where
  toFun σ := Equiv.prodCongr σ (Equiv.refl β)
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

variable [Fintype V] [DecidableEq V]

@[expose] noncomputable def iota (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1) {H : Subgroup V}
    (hH : H.index = p) {u : V} (hu : u ∉ H) : Perm ↥H →* Perm V :=
  (Equiv.permCongrHom (decompEquiv hp hexp hH hu)).toMonoidHom.comp (prodHom ↥H (Fin p))

theorem iota_apply (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1) {H : Subgroup V}
    (hH : H.index = p) {u : V} (hu : u ∉ H) (σ : Perm ↥H) (h : ↥H) (j : Fin p) :
    iota hp hexp hH hu σ (u ^ (j : ℕ) * (h : V)) = u ^ (j : ℕ) * ((σ h : ↥H) : V) := by
  have h1 : u ^ (j : ℕ) * (h : V) = decompEquiv hp hexp hH hu (h, j) := rfl
  rw [h1]
  simp only [iota, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  change (decompEquiv hp hexp hH hu).permCongr ((prodHom ↥H (Fin p)) σ)
    (decompEquiv hp hexp hH hu (h, j)) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem iota_apply_coe (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1) {H : Subgroup V}
    (hH : H.index = p) {u : V} (hu : u ∉ H) (σ : Perm ↥H) (h : ↥H) :
    iota hp hexp hH hu σ (h : V) = ((σ h : ↥H) : V) := by
  have := iota_apply hp hexp hH hu σ h ⟨0, hp.pos⟩
  simpa using this

@[expose] def commSub (f : Perm V) : Subgroup V where
  carrier := {v | ∀ x, f (v * x) = v * f x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    simp only [Set.mem_setOf_eq] at *
    rw [mul_assoc, ha, hb, mul_assoc]
  inv_mem' := by
    intro a ha x
    simp only [Set.mem_setOf_eq] at *
    have := ha (a⁻¹ * x)
    rw [mul_inv_cancel_left] at this
    rw [this, inv_mul_cancel_left]

theorem mem_commSub {f : Perm V} {v : V} : v ∈ commSub f ↔ ∀ x, f (v * x) = v * f x := Iff.rfl

theorem iota_mem_hypGens (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1) {H : Subgroup V}
    [DecidablePred (· ∈ H)] (hH : H.index = p) {u : V} (hu : u ∉ H) {g : Perm ↥H}
    (hg : g ∈ hypGens p ↥H) : iota hp hexp hH hu g ∈ hypGens p V := by
  obtain ⟨hgalt, Y, hYi, hYc⟩ := hg
  refine ⟨map_alt_le (iota hp hexp hH hu) ⟨g, hgalt, rfl⟩, Y.map H.subtype ⊔ Subgroup.zpowers u,
    ?_, ?_⟩
  ·
    set Y' := Y.map H.subtype ⊔ Subgroup.zpowers u with hY'
    have h1 := Y'.index_mul_card
    have h2 := H.index_mul_card
    have h3 := Y.index_mul_card
    have hYcard : Nat.card (Y.map H.subtype) = Nat.card Y :=
      Subgroup.card_map_of_injective H.subtype_injective
    have hinj : Function.Injective (fun q : ↥Y × Fin p =>
        (⟨u ^ (q.2 : ℕ) * ((q.1 : ↥H) : V), Y'.mul_mem
          (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _))
          (Subgroup.mem_sup_left ⟨q.1, q.1.2, rfl⟩)⟩ : ↥Y')) := by
      intro q q' hq
      have hq' := congrArg Subtype.val hq
      simp only at hq'
      obtain ⟨h1, h2⟩ := decomp_unique hp hexp hu q.2.2 q'.2.2 (q.1 : ↥H).2 (q'.1 : ↥H).2 hq'
      exact Prod.ext (Subtype.ext (Subtype.ext h2)) (Fin.ext h1)
    have h4 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_fin] at h4
    have hpos : 0 < Nat.card Y' := Nat.card_pos
    rw [hH] at h2
    have h5 : Y'.index * Nat.card Y' ≤ p * Nat.card Y' := by
      rw [h1, ← h2, ← h3]
      calc p * (Y.index * Nat.card Y) ≤ p * (p * Nat.card Y) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hYi)
        _ ≤ p * Nat.card Y' := Nat.mul_le_mul_left _ (by rw [mul_comm]; exact h4)
    exact Nat.le_of_mul_le_mul_right h5 hpos
  ·
    have hle : Y.map H.subtype ⊔ Subgroup.zpowers u ≤ commSub (iota hp hexp hH hu g) := by
      refine sup_le ?_ ((Subgroup.zpowers_le).2 ?_)
      · rintro _ ⟨y, hy, rfl⟩
        rw [mem_commSub]
        intro x
        obtain ⟨h, j, rfl⟩ := decomp_exists hp hexp hH hu x
        have e1 : (H.subtype y : V) * (u ^ (j : ℕ) * (h : V)) = u ^ (j : ℕ) * ((y * h : ↥H) : V) := by
          simp only [Subgroup.coe_subtype, Subgroup.coe_mul]
          exact mul_left_comm _ _ _
        rw [e1, iota_apply, iota_apply, hYc y hy h]
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul]
        exact mul_left_comm _ _ _
      · rw [mem_commSub]
        intro x
        obtain ⟨h, j, rfl⟩ := decomp_exists hp hexp hH hu x
        by_cases hj : (j : ℕ) + 1 < p
        · have e1 : u * (u ^ (j : ℕ) * (h : V)) = u ^ ((⟨(j : ℕ) + 1, hj⟩ : Fin p) : ℕ) * (h : V) := by
            simp only
            rw [pow_succ', mul_assoc]
          rw [e1, iota_apply, iota_apply]
          simp only
          rw [pow_succ', mul_assoc]
        · have hjp : (j : ℕ) + 1 = p := by have := j.2; omega
          have hup : u * u ^ (j : ℕ) = 1 := by rw [← pow_succ', hjp, hexp u]
          have e1 : u * (u ^ (j : ℕ) * (h : V)) = (h : V) := by rw [← mul_assoc, hup, one_mul]
          rw [e1, iota_apply_coe, iota_apply, ← mul_assoc, hup, one_mul]
    intro y hy x
    exact (mem_commSub.1 (hle hy)) x

end Transport

section Step

variable {p : ℕ} {V : Type*} [CommGroup V] [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem line_lemma {w y₁ y₂ : V} (hy₁ : y₁ ∉ Subgroup.zpowers w) (hy₂ : y₂ ∉ Subgroup.zpowers w)
    (hy₁₂ : y₂ * y₁⁻¹ ∉ Subgroup.zpowers w) {h h' : V}
    (hh : h = 1 ∨ h = y₁ ∨ h = w * y₁) (hh' : h' = 1 ∨ h' = y₂ ∨ h' = w * y₂)
    (he : h * h'⁻¹ ∈ Subgroup.zpowers w) : h = 1 ∧ h' = 1 := by
  have hw : w ∈ Subgroup.zpowers w := Subgroup.mem_zpowers w
  have key : ∀ c c' : V, h * c⁻¹ ∈ Subgroup.zpowers w → h' * c'⁻¹ ∈ Subgroup.zpowers w →
      c * c'⁻¹ ∈ Subgroup.zpowers w := by
    intro c c' h1 h2
    have e : c * c'⁻¹ = (h * c⁻¹)⁻¹ * (h * h'⁻¹) * (h' * c'⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) he) h2
  have hc : ∃ c : V, (c = 1 ∨ c = y₁) ∧ h * c⁻¹ ∈ Subgroup.zpowers w ∧ (c = 1 → h = 1) := by
    rcases hh with e | e | e
    · exact ⟨1, Or.inl rfl, by rw [e]; simp, fun _ => e⟩
    · exact ⟨y₁, Or.inr rfl, by rw [e, mul_inv_cancel]; exact Subgroup.one_mem _,
        fun h1 => absurd (h1 ▸ Subgroup.one_mem _) hy₁⟩
    · exact ⟨y₁, Or.inr rfl, by rw [e, mul_inv_cancel_right]; exact hw,
        fun h1 => absurd (h1 ▸ Subgroup.one_mem _) hy₁⟩
  have hc' : ∃ c' : V, (c' = 1 ∨ c' = y₂) ∧ h' * c'⁻¹ ∈ Subgroup.zpowers w ∧ (c' = 1 → h' = 1) := by
    rcases hh' with e | e | e
    · exact ⟨1, Or.inl rfl, by rw [e]; simp, fun _ => e⟩
    · exact ⟨y₂, Or.inr rfl, by rw [e, mul_inv_cancel]; exact Subgroup.one_mem _,
        fun h1 => absurd (h1 ▸ Subgroup.one_mem _) hy₂⟩
    · exact ⟨y₂, Or.inr rfl, by rw [e, mul_inv_cancel_right]; exact hw,
        fun h1 => absurd (h1 ▸ Subgroup.one_mem _) hy₂⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := hc
  obtain ⟨c', hc1', hc2', hc3'⟩ := hc'
  have hk := key c c' hc2 hc2'
  rcases hc1 with e1 | e1 <;> rcases hc1' with e2 | e2
  · exact ⟨hc3 e1, hc3' e2⟩
  · rw [e1, e2, one_mul] at hk
    exact absurd ((Subgroup.inv_mem_iff _).1 hk) hy₂
  · rw [e1, e2, inv_one, mul_one] at hk
    exact absurd hk hy₁
  · rw [e1, e2] at hk
    have := Subgroup.inv_mem _ hk
    rw [mul_inv_rev, inv_inv] at this
    exact absurd this hy₁₂

theorem le_of_supp_hyperplane (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    {H : Subgroup V} [DecidablePred (· ∈ H)] (hH : H.index = p) (hHcard : p ^ 2 ≤ Nat.card H)
    (hIH : alternatingGroup ↥H ≤ Subgroup.closure (hypGens p ↥H))
    {g : Perm V} (hg : g ∈ alternatingGroup V) (hgH : ∀ v, v ∉ H → g v = v) :
    g ∈ Subgroup.closure (hypGens p V) := by
  haveI := Fact.mk hp
  set T := Subgroup.closure (hypGens p V) with hT
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨u, hu⟩ : ∃ u : V, u ∉ H := by
    by_contra hcon
    push Not at hcon
    have h1 : H = ⊤ := eq_top_iff.2 fun v _ => hcon v
    rw [h1, Subgroup.index_top] at hH
    exact hp.one_lt.ne hH
  have hιT : ∀ {u' : V} (hu' : u' ∉ H), ∀ σ ∈ alternatingGroup ↥H, iota hp hexp hH hu' σ ∈ T := by
    intro u' hu' σ hσ
    have h1 : (Subgroup.closure (hypGens p ↥H)).map (iota hp hexp hH hu') ≤ T := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g', hg', rfl⟩
      exact Subgroup.subset_closure (iota_mem_hypGens hp hexp hH hu' hg')
    exact h1 ⟨σ, hIH hσ, rfl⟩
  obtain ⟨w, hwH, hw1⟩ : ∃ w ∈ H, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 hcon
    rw [h1, Subgroup.card_bot] at hHcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hwp : orderOf w = p := orderOf_eq_prime (hexp w) hw1
  have hcardw : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, hwp]
  obtain ⟨y₁, hy₁H, hy₁⟩ : ∃ y ∈ H, y ∉ Subgroup.zpowers w := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (H := H) (K := Subgroup.zpowers w) hcon
    rw [hcardw] at h1
    have : p < p ^ 2 := by nlinarith
    omega
  obtain ⟨y₂, hy₂H, hy₂, hy₁₂⟩ : ∃ y ∈ H, y ∉ Subgroup.zpowers w ∧ y * y₁⁻¹ ∉ Subgroup.zpowers w := by
    by_contra hcon
    push Not at hcon
    have hsub : (H : Set V) ⊆ (Subgroup.zpowers w : Set V) ∪
        (fun z => z * y₁) '' (Subgroup.zpowers w : Set V) := by
      intro y hy
      by_cases hyw : y ∈ Subgroup.zpowers w
      · exact Or.inl hyw
      · exact Or.inr ⟨y * y₁⁻¹, hcon y hy hyw, inv_mul_cancel_right y y₁⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (Subgroup.zpowers w : Set V)
      ((fun z => z * y₁) '' (Subgroup.zpowers w : Set V))
    rw [Set.ncard_image_of_injective _ (mul_left_injective y₁)] at h2
    have h3 : (Subgroup.zpowers w : Set V).ncard = p := by
      rw [← Nat.card_coe_set_eq]; exact hcardw
    have h4 : (H : Set V).ncard = Nat.card H := by rw [← Nat.card_coe_set_eq]; rfl
    have : 2 * p < p ^ 2 := by nlinarith
    omega
  have hy₁1 : y₁ ≠ 1 := fun h => hy₁ (h ▸ Subgroup.one_mem _)
  have hy₂1 : y₂ ≠ 1 := fun h => hy₂ (h ▸ Subgroup.one_mem _)
  have hwy₁ : w * y₁ ∈ H := H.mul_mem hwH hy₁H
  have hwy₂ : w * y₂ ∈ H := H.mul_mem hwH hy₂H
  have hwj : ∀ j : ℕ, 0 < j → j < p → w ^ j ≠ 1 := by
    intro j hj0 hjp h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hwp] at this
    exact absurd (Nat.le_of_dvd hj0 this) (by omega)
  set σ : Perm ↥H := c3 (1 : ↥H) ⟨y₁, hy₁H⟩ ⟨w * y₁, hwy₁⟩ with hσ
  set τ : Perm ↥H := c3 (1 : ↥H) ⟨y₂, hy₂H⟩ ⟨w * y₂, hwy₂⟩ with hτ
  have hd1 : (1 : ↥H) ≠ ⟨y₁, hy₁H⟩ := fun h => hy₁1 (congrArg Subtype.val h).symm
  have hd2 : (⟨y₁, hy₁H⟩ : ↥H) ≠ ⟨w * y₁, hwy₁⟩ := fun h => hw1 (by
    have := congrArg Subtype.val h
    simp only at this
    exact (mul_eq_right.1 this.symm))
  have hd1' : (1 : ↥H) ≠ ⟨y₂, hy₂H⟩ := fun h => hy₂1 (congrArg Subtype.val h).symm
  have hd2' : (⟨y₂, hy₂H⟩ : ↥H) ≠ ⟨w * y₂, hwy₂⟩ := fun h => hw1 (by
    have := congrArg Subtype.val h
    simp only at this
    exact (mul_eq_right.1 this.symm))
  have hσ1 : σ 1 = ⟨y₁, hy₁H⟩ := c3_apply_left hd1 hd2
  have hτ1 : τ 1 = ⟨y₂, hy₂H⟩ := c3_apply_left hd1' hd2'
  have hσmov : ∀ h : ↥H, σ h ≠ h → (h : V) = 1 ∨ (h : V) = y₁ ∨ (h : V) = w * y₁ := by
    intro h hne
    by_contra hcon
    push Not at hcon
    exact hne (c3_apply_of_ne (fun e => hcon.1 (by rw [e]; rfl))
      (fun e => hcon.2.1 (by rw [e])) (fun e => hcon.2.2 (by rw [e])))
  have hτmov : ∀ h : ↥H, τ h ≠ h → (h : V) = 1 ∨ (h : V) = y₂ ∨ (h : V) = w * y₂ := by
    intro h hne
    by_contra hcon
    push Not at hcon
    exact hne (c3_apply_of_ne (fun e => hcon.1 (by rw [e]; rfl))
      (fun e => hcon.2.1 (by rw [e])) (fun e => hcon.2.2 (by rw [e])))
  have huw : u * w ∉ H := fun h => hu (by
    have := H.mul_mem h (H.inv_mem hwH)
    rwa [mul_inv_cancel_right] at this)
  set a : Perm V := iota hp hexp hH hu σ with ha
  set b : Perm V := iota hp hexp hH huw τ with hb
  have ha1 : a 1 = y₁ := by
    have := iota_apply_coe hp hexp hH hu σ 1
    rw [hσ1] at this
    simpa using this
  have hb1 : b 1 = y₂ := by
    have := iota_apply_coe hp hexp hH huw τ 1
    rw [hτ1] at this
    simpa using this
  have hcomm := comm_eq_c3 (σ := a) (τ := b) (x₀ := 1) (fun v hav hbv => by
      obtain ⟨h, j, rfl⟩ := decomp_exists hp hexp hH hu v
      obtain ⟨h', j', hv'⟩ := decomp_exists hp hexp hH huw (u ^ (j : ℕ) * (h : V))
      have hσh : σ h ≠ h := by
        intro e
        apply hav
        rw [ha, iota_apply, e]
      have hτh' : τ h' ≠ h' := by
        intro e
        apply hbv
        rw [hv', hb, iota_apply, e]
      have e1 : (u * w) ^ (j' : ℕ) * (h' : V) = u ^ (j' : ℕ) * (w ^ (j' : ℕ) * (h' : V)) := by
        rw [mul_pow, mul_assoc]
      rw [e1] at hv'
      obtain ⟨hjj, hhh⟩ := decomp_unique hp hexp hu j.2 j'.2 h.2
        (H.mul_mem (H.pow_mem hwH _) h'.2) hv'
      have hl := line_lemma hy₁ hy₂ hy₁₂ (hσmov h hσh) (hτmov h' hτh') (by
        rw [hhh, mul_inv_cancel_right]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers w) _)
      have hj0 : (j' : ℕ) = 0 := by
        by_contra hj0
        apply hwj j' (Nat.pos_of_ne_zero hj0) j'.2
        have := hhh
        rw [hl.1, hl.2, mul_one] at this
        exact this.symm
      rw [hjj, hj0, pow_zero, one_mul, hl.1])
    (by rw [ha1]; exact hy₁1) (by rw [hb1]; exact hy₂1)
  rw [ha1, hb1] at hcomm
  have hd3 : ∀ {y : V} (hyH : w * y ∈ H), y ∉ Subgroup.zpowers w → (1 : ↥H) ≠ ⟨w * y, hyH⟩ := by
    intro y hyH hy h
    apply hy
    have h1 := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at h1
    have e : y = w⁻¹ := by rw [eq_inv_iff_mul_eq_one, mul_comm]; exact h1.symm
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers w)
  have hσalt : σ ∈ alternatingGroup ↥H :=
    (isThreeCycle_c3 hd1 (hd3 hwy₁ hy₁) hd2).mem_alternatingGroup
  have hτalt : τ ∈ alternatingGroup ↥H :=
    (isThreeCycle_c3 hd1' (hd3 hwy₂ hy₂) hd2').mem_alternatingGroup
  have hρT : c3 (1 : V) y₁ y₂ ∈ T := by
    rw [← hcomm]
    have h1 := hιT hu σ hσalt
    have h2 := hιT huw τ hτalt
    exact T.mul_mem (T.mul_mem (T.mul_mem h1 h2) (T.inv_mem h1)) (T.inv_mem h2)
  set T'' : Subgroup (Perm ↥H) := T.comap (ofSubtype : Perm ↥H →* Perm V) with hT''
  have hy₁₂ne : (⟨y₁, hy₁H⟩ : ↥H) ≠ ⟨y₂, hy₂H⟩ := fun h => hy₁₂ (by
    have := congrArg Subtype.val h
    simp only at this
    rw [← this, mul_inv_cancel]; exact Subgroup.one_mem _)
  set ρ₀ : Perm ↥H := c3 (1 : ↥H) ⟨y₁, hy₁H⟩ ⟨y₂, hy₂H⟩ with hρ₀
  have hρ₀3 : ρ₀.IsThreeCycle := isThreeCycle_c3 hd1 hd1' hy₁₂ne
  have hρ₀T : ρ₀ ∈ T'' := by
    show ofSubtype ρ₀ ∈ T
    have : ofSubtype ρ₀ = c3 (1 : V) y₁ y₂ := by
      rw [hρ₀, c3, map_mul, ofSubtype_swap_eq, ofSubtype_swap_eq]
      rfl
    rw [this]; exact hρT
  have hnot : ∀ (h : ↥H) (j : Fin p), (j : ℕ) ≠ 0 → u ^ (j : ℕ) * (h : V) ∉ H := by
    intro h j hj hmem
    have e : u ^ (j : ℕ) * (h : V) = u ^ (0 : ℕ) * (u ^ (j : ℕ) * (h : V)) := by simp
    exact hj (decomp_unique hp hexp hu j.2 hp.pos h.2 hmem e).1
  have hnorm : ∀ g' σ' : Perm ↥H, ofSubtype (g' * σ' * g'⁻¹) =
      iota hp hexp hH hu g' * ofSubtype σ' * (iota hp hexp hH hu g')⁻¹ := by
    intro g' σ'
    ext x
    obtain ⟨h, j, rfl⟩ := decomp_exists hp hexp hH hu x
    rw [Perm.mul_apply, Perm.mul_apply, ← map_inv, iota_apply]
    by_cases hj : (j : ℕ) = 0
    · have e : u ^ (j : ℕ) * (h : V) = (h : V) := by rw [hj, pow_zero, one_mul]
      rw [e, ofSubtype_apply_coe]
      have e2 : u ^ (j : ℕ) * ((g'⁻¹ h : ↥H) : V) = ((g'⁻¹ h : ↥H) : V) := by
        rw [hj, pow_zero, one_mul]
      rw [e2, ofSubtype_apply_coe, iota_apply_coe]
      rfl
    · rw [ofSubtype_apply_of_not_mem _ (hnot h j hj),
        ofSubtype_apply_of_not_mem _ (hnot (g'⁻¹ h) j hj), iota_apply]
      simp
  have h5 : 5 ≤ Nat.card ↥H := by nlinarith
  have hthree : ∀ c : Perm ↥H, c.IsThreeCycle → c ∈ T'' := by
    intro c hc
    have hconj := alternatingGroup.isThreeCycle_isConj h5
      (σ := ⟨ρ₀, hρ₀3.mem_alternatingGroup⟩) (τ := ⟨c, hc.mem_alternatingGroup⟩) hρ₀3 hc
    obtain ⟨g', hg'⟩ := isConj_iff.1 hconj
    have hc' : c = (g' : Perm ↥H) * ρ₀ * (g' : Perm ↥H)⁻¹ := by
      have := congrArg Subtype.val hg'
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at this
      exact this.symm
    show ofSubtype c ∈ T
    rw [hc', hnorm]
    have h1 := hιT hu (g' : Perm ↥H) g'.2
    exact T.mul_mem (T.mul_mem h1 hρ₀T) (T.inv_mem h1)
  have hAltT : alternatingGroup ↥H ≤ T'' := by
    rw [← closure_three_cycles_eq_alternating (α := ↥H), Subgroup.closure_le]
    exact hthree
  have hg₁ : ∀ x, g x ∈ H ↔ x ∈ H := by
    intro x
    constructor
    · intro hgx
      by_contra hx
      rw [hgH x hx] at hgx
      exact hx hgx
    · intro hx
      by_contra hgx
      have h1 := hgH (g x) hgx
      rw [g.injective h1] at hgx
      exact hgx hx
  have hg₂ : ∀ x, g x ≠ x → x ∈ H := fun x hx => by
    by_contra h
    exact hx (hgH x h)
  have hsub : g.subtypePerm hg₁ ∈ alternatingGroup ↥H := by
    rw [mem_alternatingGroup, sign_subtypePerm _ _ hg₂]
    exact mem_alternatingGroup.1 hg
  have := hAltT hsub
  rw [hT'', Subgroup.mem_comap, ofSubtype_subtypePerm _ hg₂] at this
  exact this

theorem le_of_supp_coset (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    {H : Subgroup V} [DecidablePred (· ∈ H)] (hH : H.index = p) (hHcard : p ^ 2 ≤ Nat.card H)
    (hIH : alternatingGroup ↥H ≤ Subgroup.closure (hypGens p ↥H)) (x : V)
    {g : Perm V} (hg : g ∈ alternatingGroup V) (hgH : ∀ v, v * x⁻¹ ∉ H → g v = v) :
    g ∈ Subgroup.closure (hypGens p V) := by
  set t : Perm V := Equiv.mulLeft x with ht
  have htT := mulLeft_mem_closure hp hp2 hexp x
  set g' : Perm V := t⁻¹ * g * t with hg'
  have hg'alt : g' ∈ alternatingGroup V := by
    rw [mem_alternatingGroup, hg', map_mul, map_mul, map_inv, mem_alternatingGroup.1 hg, mul_one,
      inv_mul_cancel]
  have hg'H : ∀ v, v ∉ H → g' v = v := by
    intro v hv
    have h1 : (x * v) * x⁻¹ ∉ H := by rwa [mul_comm x v, mul_inv_cancel_right]
    rw [hg', Perm.mul_apply, Perm.mul_apply, ht, Equiv.coe_mulLeft, hgH _ h1]
    simp
  have h1 := le_of_supp_hyperplane hp hp2 hexp hH hHcard hIH hg'alt hg'H
  have e : g = t * g' * t⁻¹ := by rw [hg']; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htT h1) (Subgroup.inv_mem _ htT)

end Step

section Core

variable {p : ℕ}

theorem coset_inter {V : Type*} [CommGroup V] [Finite V] (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1)
    {H₀ H₁ : Subgroup V} (hH₀ : H₀.index = p) {u : V} (hu₀ : u ∉ H₀) (hu₁ : u ∈ H₁) (x y : V) :
    ∃ z, z * x⁻¹ ∈ H₀ ∧ z * y⁻¹ ∈ H₁ := by
  obtain ⟨h, j, hj⟩ := decomp_exists hp hexp hH₀ hu₀ (y * x⁻¹)
  refine ⟨(u ^ (j : ℕ))⁻¹ * y, ?_, ?_⟩
  · rw [mul_assoc, hj, inv_mul_cancel_left]
    exact h.2
  · rw [mul_inv_cancel_right]
    exact H₁.inv_mem (H₁.pow_mem hu₁ _)

theorem ncard_coset {V : Type*} [Group V] [Finite V] (K : Subgroup V) (x : V) :
    {v | v * x⁻¹ ∈ K}.ncard = Nat.card K := by
  have e : {v | v * x⁻¹ ∈ K} = (fun h => h * x) '' (K : Set V) := by
    ext v
    constructor
    · intro hv
      exact ⟨v * x⁻¹, hv, inv_mul_cancel_right v x⟩
    · rintro ⟨h, hh, rfl⟩
      show h * x * x⁻¹ ∈ K
      rw [mul_inv_cancel_right]
      exact hh
  rw [e, Set.ncard_image_of_injective _ (mul_left_injective x), ← Nat.card_coe_set_eq]
  rfl

theorem alt_le_step {V : Type*} [CommGroup V] [Fintype V] [DecidableEq V] (hp : p.Prime)
    (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1) {t : ℕ} (hcard : Nat.card V = p ^ t) (ht : 3 ≤ t)
    (hIH : ∀ (H : Subgroup V) [DecidablePred (· ∈ H)], H.index = p →
      alternatingGroup ↥H ≤ Subgroup.closure (hypGens p ↥H)) :
    alternatingGroup V ≤ Subgroup.closure (hypGens p V) := by
  classical
  haveI := Fact.mk hp
  have hdvd : p ^ (t - 1) ∣ Nat.card V := by
    rw [hcard]; exact pow_dvd_pow p (Nat.sub_le t 1)
  have hidx : ∀ K : Subgroup V, Nat.card K = p ^ (t - 1) → K.index = p := by
    intro K hK
    have h1 := K.index_mul_card
    rw [hK, hcard] at h1
    have h2 : p ^ t = p * p ^ (t - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h1
  obtain ⟨H₀, hH₀c, -⟩ := Sylow.exists_subgroup_card_pow_prime_le p hdvd ⊥
    (by rw [Subgroup.card_bot, pow_zero]) (Nat.zero_le _)
  have hH₀ := hidx H₀ hH₀c
  obtain ⟨u, hu₀⟩ : ∃ u : V, u ∉ H₀ := by
    by_contra hcon
    push Not at hcon
    have h1 : H₀ = ⊤ := eq_top_iff.2 fun v _ => hcon v
    rw [h1, Subgroup.index_top] at hH₀
    exact hp.one_lt.ne hH₀
  have hu1 : u ≠ 1 := fun h => hu₀ (h ▸ H₀.one_mem)
  obtain ⟨H₁, hH₁c, hH₁u⟩ := Sylow.exists_subgroup_card_pow_prime_le p hdvd (Subgroup.zpowers u)
    (by rw [Nat.card_zpowers, orderOf_eq_prime (hexp u) hu1, pow_one]) (by omega : 1 ≤ t - 1)
  have hH₁ := hidx H₁ hH₁c
  have hu₁ : u ∈ H₁ := hH₁u (Subgroup.mem_zpowers u)
  have hp2le : p ^ 2 ≤ p ^ (t - 1) := Nat.pow_le_pow_right hp.pos (by omega)
  set Hb : Bool → Subgroup V := fun b => cond b H₁ H₀ with hHb
  have hHbi : ∀ b, (Hb b).index = p := fun b => by cases b <;> assumption
  have hHbc : ∀ b, Nat.card (Hb b) = p ^ (t - 1) := fun b => by cases b <;> assumption
  set S : Bool × V → Set V := fun i => {v | v * i.2⁻¹ ∈ Hb i.1} with hS
  have hS3 : ∀ i, 3 ≤ (S i).ncard := by
    intro i
    rw [hS]
    simp only
    rw [ncard_coset, hHbc]
    have : 3 ≤ p := by have := hp.two_le; omega
    nlinarith
  have hcover : (⋃ i, S i) = Set.univ := by
    refine Set.eq_univ_of_forall fun v => Set.mem_iUnion.2 ⟨(false, v), ?_⟩
    show v * v⁻¹ ∈ H₀
    rw [mul_inv_cancel]
    exact H₀.one_mem
  have hcross : ∀ (x y : V) (b : Bool), (S (b, x) ∩ S (!b, y)).Nonempty := by
    intro x y b
    cases b
    · obtain ⟨z, hz0, hz1⟩ := coset_inter hp hexp hH₀ hu₀ hu₁ x y
      exact ⟨z, hz0, hz1⟩
    · obtain ⟨z, hz0, hz1⟩ := coset_inter hp hexp hH₀ hu₀ hu₁ y x
      exact ⟨z, hz1, hz0⟩
  have hconn : ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j := by
    rintro ⟨b, x⟩ ⟨b', y⟩
    cases b <;> cases b'
    · exact Relation.ReflTransGen.head (hcross x x false) (Relation.ReflTransGen.single (hcross x y true))
    · exact Relation.ReflTransGen.single (hcross x y false)
    · exact Relation.ReflTransGen.single (hcross x y true)
    · exact Relation.ReflTransGen.head (hcross x x true) (Relation.ReflTransGen.single (hcross x y false))
  have hgen := GL83.iSup_altOn_eq_alternatingGroup hS3 hcover hconn
  rw [← hgen]
  refine iSup_le fun i => ?_
  intro g hg
  rw [GL83.mem_altOn] at hg
  exact le_of_supp_coset hp hp2 hexp (H := Hb i.1) (hHbi i.1) (by rw [hHbc]; exact hp2le)
    (hIH (Hb i.1) (hHbi i.1)) i.2 hg.1 (fun v hv => hg.2 v hv)

theorem core_alt_le (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ (n : ℕ) (V : Type) [CommGroup V] [Fintype V] [DecidableEq V], Nat.card V = n →
      (∀ v : V, v ^ p = 1) → alternatingGroup V ≤ Subgroup.closure (hypGens p V) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn hexp
    haveI := Fact.mk hp
    have hpg : IsPGroup p V := fun v => ⟨1, by rw [pow_one]; exact hexp v⟩
    obtain ⟨t, ht⟩ := IsPGroup.iff_card.1 hpg
    rcases Nat.lt_or_ge t 2 with ht2 | ht2
    · apply alt_le_of_card_le
      rw [ht]
      calc p ^ t ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    · rcases Nat.lt_or_ge t 3 with ht3 | ht3
      · have ht2' : t = 2 := by omega
        rw [ht2'] at ht
        exact alt_le_base hp hp2 hexp (by rw [ht]; nlinarith [hp.two_le]) (by rw [ht])
      · refine alt_le_step hp hp2 hexp ht ht3 ?_
        intro H _ hH
        have hlt : Nat.card H < n := by
          have h1 := H.index_mul_card
          rw [hH] at h1
          have h2 : 0 < Nat.card H := Nat.card_pos
          rw [← hn, ← h1]
          nlinarith [hp.two_le]
        exact ih (Nat.card H) hlt ↥H rfl (fun v => Subtype.ext (by simp [hexp]))

end Core

section Orbit

variable {p : ℕ} {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem orbit_alt_mem (hp : p.Prime) (hp2 : p ≠ 2) (B : Subgroup (Perm Ω))
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBe : ∀ b ∈ B, b ^ p = 1) (i : Ω)
    {g : Perm Ω} (hg : g ∈ alternatingGroup Ω) (hgs : ∀ j, (∀ b ∈ B, b i ≠ j) → g j = j)
    (T : Subgroup (Perm Ω))
    (hT : ∀ f : Perm Ω, f ∈ alternatingGroup Ω → ∀ X : Subgroup (Perm Ω), X ≤ B →
      (X.subgroupOf B).index ≤ p → (∀ x ∈ X, f * x = x * f) → f ∈ T) :
    g ∈ T := by
  classical
  haveI := Fact.mk hp
  set St : Subgroup ↥B := MulAction.stabilizer ↥B i with hSt
  have hcommB : ∀ a b : ↥B, a * b = b * a := fun a b => Subtype.ext (hBc a a.2 b b.2)
  haveI hnorm : St.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by rw [hcommB g n, mul_inv_cancel_right]
    rw [this]; exact hn⟩
  set V := ↥B ⧸ St with hV
  letI : CommGroup V := { (inferInstance : Group V) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcommB a b] }
  letI : Fintype V := Fintype.ofFinite V
  have hexpV : ∀ v : V, v ^ p = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_pow]
    have : b ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hBe b b.2)
    rw [this, QuotientGroup.mk_one]
  set ψ : V ≃ ↥(MulAction.orbit ↥B i) := (MulAction.orbitEquivQuotientStabilizer ↥B i).symm with hψ
  have hψmk : ∀ b : ↥B, ((ψ (b : V)) : Ω) = (b : Perm Ω) i := fun b => by
    rw [hψ, MulAction.orbitEquivQuotientStabilizer_symm_apply]
    rfl
  have hψmul : ∀ (b : ↥B) (w : V), ((ψ ((b : V) * w)) : Ω) = (b : Perm Ω) (ψ w) := by
    intro b w
    induction w using QuotientGroup.induction_on with | H c => ?_
    rw [← QuotientGroup.mk_mul, hψmk, hψmk, Subgroup.coe_mul, Perm.mul_apply]
  have hmem_orbit : ∀ j : Ω, j ∈ MulAction.orbit ↥B i ↔ ∃ b ∈ B, b i = j := by
    intro j
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hinv : ∀ (b : ↥B) (j : Ω), j ∉ MulAction.orbit ↥B i → (b : Perm Ω) j ∉ MulAction.orbit ↥B i := by
    intro b j hj hbj
    apply hj
    rw [hmem_orbit] at hbj ⊢
    obtain ⟨c, hc, hcj⟩ := hbj
    refine ⟨(b : Perm Ω)⁻¹ * c, B.mul_mem (B.inv_mem b.2) hc, ?_⟩
    rw [Perm.mul_apply, hcj]
    simp
  set Ψ : Perm V →* Perm Ω :=
    (ofSubtype : Perm ↥(MulAction.orbit ↥B i) →* Perm Ω).comp (Equiv.permCongrHom ψ).toMonoidHom
    with hΨ
  have hΨmem : ∀ (g' : Perm V) (w : V), Ψ g' (ψ w) = ψ (g' w) := by
    intro g' w
    rw [hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ofSubtype_apply_coe]
    change ((ψ.permCongr g') (ψ w) : Ω) = _
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  have hΨout : ∀ (g' : Perm V) (j : Ω), j ∉ MulAction.orbit ↥B i → Ψ g' j = j := by
    intro g' j hj
    rw [hΨ, MonoidHom.comp_apply]
    exact ofSubtype_apply_of_not_mem _ hj
  have hΨalt : ∀ g' : Perm V, g' ∈ alternatingGroup V → Ψ g' ∈ alternatingGroup Ω := by
    intro g' hg'
    rw [mem_alternatingGroup, hΨ, MonoidHom.comp_apply, sign_ofSubtype, MulEquiv.coe_toMonoidHom]
    change sign (ψ.permCongr g') = 1
    rw [sign_permCongr]
    exact mem_alternatingGroup.1 hg'
  have hgens : ∀ g' ∈ hypGens p V, Ψ g' ∈ T := by
    rintro g' ⟨hg'alt, Y, hYi, hYc⟩
    set Y₀ : Subgroup ↥B := Y.comap (QuotientGroup.mk' St) with hY₀
    refine hT _ (hΨalt g' hg'alt) (Y₀.map B.subtype) (Subgroup.map_subtype_le _) ?_ ?_
    · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective B.subtype_injective, hY₀,
        Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective St)]
      exact hYi
    · rintro _ ⟨b, hb, rfl⟩
      ext j
      simp only [Subgroup.coe_subtype, Perm.mul_apply]
      by_cases hj : j ∈ MulAction.orbit ↥B i
      · obtain ⟨w, hw⟩ := ψ.surjective ⟨j, hj⟩
        have hjw : j = (ψ w : Ω) := by rw [hw]
        rw [hjw, ← hψmul, hΨmem, hΨmem, hYc (b : V) hb w, hψmul]
      · rw [hΨout g' _ (hinv b j hj), hΨout g' j hj]
  have hcl : (Subgroup.closure (hypGens p V)).map Ψ ≤ T := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g', hg', rfl⟩
    exact hgens g' hg'
  have hcore := core_alt_le hp hp2 (Nat.card V) V rfl hexpV
  have hgO : ∀ j, j ∉ MulAction.orbit ↥B i → g j = j := by
    intro j hj
    apply hgs j
    intro b hb hbj
    exact hj ((hmem_orbit j).2 ⟨b, hb, hbj⟩)
  have hg₁ : ∀ x, g x ∈ MulAction.orbit ↥B i ↔ x ∈ MulAction.orbit ↥B i := by
    intro x
    constructor
    · intro hgx
      by_contra hx
      rw [hgO x hx] at hgx
      exact hx hgx
    · intro hx
      by_contra hgx
      have h1 := hgO (g x) hgx
      rw [g.injective h1] at hgx
      exact hgx hx
  have hg₂ : ∀ x, g x ≠ x → x ∈ MulAction.orbit ↥B i := fun x hx => by
    by_contra h
    exact hx (hgO x h)
  set g'' : Perm V := (Equiv.permCongrHom ψ).symm (g.subtypePerm hg₁) with hg''
  have hg''alt : g'' ∈ alternatingGroup V := by
    rw [mem_alternatingGroup, hg'', Equiv.permCongrHom_symm]
    change sign (ψ.symm.permCongr _) = 1
    rw [sign_permCongr, sign_subtypePerm _ _ hg₂]
    exact mem_alternatingGroup.1 hg
  have hΨg : Ψ g'' = g := by
    rw [hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hg'', MulEquiv.apply_symm_apply,
      ofSubtype_subtypePerm _ hg₂]
  rw [← hΨg]
  exact hcl ⟨g'', hcore hg''alt, rfl⟩

end Orbit

theorem input23_9_holds : Lemma129k.Input23_9 := by
  intro p k n hp hp2 B hB hk i _ g hg
  classical
  haveI := Fact.mk hp
  set B' : Subgroup (Perm (Fin n)) := B.map (alternatingGroup (Fin n)).subtype with hB'
  have hmem : (g : Perm (Fin n)) ∈ (CFSG.Open.GLBCore p (k - 1) B).map (alternatingGroup (Fin n)).subtype := by
    refine orbit_alt_mem hp hp2 B' ?_ ?_ i g.2 ?_ _ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (CFSG.Open.IsElemAbelian.comm hB ha hb)
    · rintro _ ⟨b, hb, rfl⟩
      have := congrArg Subtype.val (hB.2 b hb)
      simpa using this
    · intro j hj
      apply hg j
      intro b hb
      exact hj _ ⟨b, hb, rfl⟩
    · intro f hf X hXB hXi hXc
      set X' : Subgroup ↥(alternatingGroup (Fin n)) := X.comap (alternatingGroup (Fin n)).subtype with hX'
      have hX'B : X' ≤ B := by
        intro x hx
        obtain ⟨b, hb, hbx⟩ := hXB hx
        have : b = x := Subtype.ext hbx
        rw [← this]
        exact hb
      have hXmap : X'.map (alternatingGroup (Fin n)).subtype = X := by
        apply le_antisymm (Subgroup.map_comap_le _ _)
        intro y hy
        obtain ⟨b, -, rfl⟩ := hXB hy
        exact ⟨b, hy, rfl⟩
      have hX'el : CFSG.Open.IsElemAbelian p X' := hB.mono hX'B
      have hcardB : Nat.card B = p ^ CFSG.Open.pRank p B := Lemma129.card_eq_pow_pRank hp hB
      have hcardX : Nat.card X' = p ^ CFSG.Open.pRank p X' := Lemma129.card_eq_pow_pRank hp hX'el
      have hB'c : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective
      have hXc' : Nat.card X = Nat.card X' := by
        rw [← hXmap]
        exact Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective
      have h1 := (X.subgroupOf B').index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXB).toEquiv] at h1
      have h2 : p ^ CFSG.Open.pRank p B ≤ p ^ (CFSG.Open.pRank p X' + 1) := by
        rw [← hcardB, ← hB'c, ← h1, hXc', hcardX, pow_succ, mul_comm]
        exact Nat.mul_le_mul_left _ hXi
      have h3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
      have hrank : k - 1 ≤ CFSG.Open.pRank p X' := by omega
      have hle : Subgroup.normalizer (X' : Set ↥(alternatingGroup (Fin n))) ≤
          CFSG.Open.GLBCore p (k - 1) B := le_sSup ⟨X', hX'B, hrank, rfl⟩
      refine ⟨⟨f, hf⟩, hle ?_, rfl⟩
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      apply Subtype.ext
      exact (hXc (x : Perm (Fin n)) hx).symm
  obtain ⟨a, ha, hag⟩ := hmem
  have : a = g := Subtype.ext hag
  rw [← this]
  exact ha

section Five

variable {p : ℕ} {Ω : Type} [Fintype Ω] [DecidableEq Ω]

@[expose] def fixOut (S : Set Ω) : Subgroup (Perm Ω) where
  carrier := {f | ∀ x, x ∉ S → f x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x hx
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Perm.mul_apply, hb x hx, ha x hx]
  inv_mem' := by
    intro a ha x hx
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Perm.inv_eq_iff_eq]
    exact (ha x hx).symm

theorem mem_fixOut {S : Set Ω} {f : Perm Ω} : f ∈ fixOut S ↔ ∀ x, x ∉ S → f x = x := Iff.rfl

theorem fixOut_mono {S S' : Set Ω} (h : S ⊆ S') : fixOut S ≤ fixOut S' :=
  fun _ hf x hx => hf x (fun h' => hx (h h'))

@[expose] def setStab (T : Set Ω) : Subgroup (Perm Ω) where
  carrier := {f | ∀ z, z ∈ T ↔ f z ∈ T}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro a b ha hb z
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Perm.mul_apply, hb z, ha (b z)]
  inv_mem' := by
    intro a ha z
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h := ha (a⁻¹ z)
    simp only [Perm.coe_inv, Equiv.apply_symm_apply] at h ⊢
    exact h.symm

theorem mem_setStab {T : Set Ω} {f : Perm Ω} : f ∈ setStab T ↔ ∀ z, z ∈ T ↔ f z ∈ T := Iff.rfl

theorem fixOut_le_setStab {S T : Set Ω} (h : ∀ z ∈ T, z ∉ S) : fixOut S ≤ setStab T := by
  intro f hf z
  constructor
  · intro hz
    rw [hf z (h z hz)]
    exact hz
  · intro hz
    have h1 : f (f z) = f z := hf _ (h _ hz)
    rw [f.injective h1] at hz
    exact hz

theorem fixOut_le_setStab_self (S : Set Ω) : fixOut S ≤ setStab S := by
  intro f hf z
  constructor
  · intro hz
    by_contra hfz
    have h1 := hf (f z) hfz
    rw [f.injective h1] at hfz
    exact hfz hz
  · intro hfz
    by_contra hz
    rw [hf z hz] at hfz
    exact hz hfz

theorem setStab_sdiff {A B : Set Ω} {f : Perm Ω} (hA : f ∈ setStab A) (hB : f ∈ setStab B) :
    f ∈ setStab (A \ B) := fun z => by
  simp only [Set.mem_diff]
  rw [hA z, hB z]

theorem card_mul_le_card_sup {G : Type*} [Group G] [Finite G] (H K : Subgroup G)
    (hd : ∀ a ∈ H, a ∈ K → a = 1) : Nat.card H * Nat.card K ≤ Nat.card ↥(H ⊔ K) := by
  have hinj : Function.Injective (fun q : ↥H × ↥K =>
      (⟨(q.1 : G) * (q.2 : G), Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2)
        (Subgroup.mem_sup_right q.2.2)⟩ : ↥(H ⊔ K))) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a = 1 :=
      hd _ (H.mul_mem (H.inv_mem a'.2) a.2) (h2 ▸ K.mul_mem b'.2 (K.inv_mem b.2))
    have h4 : (a : G) = a' := by rw [inv_mul_eq_one] at h3; exact h3.symm
    have h5 : (b : G) = b' := by rw [h4] at h1; exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at this

theorem arith_block {k j : ℕ} (hp : 3 ≤ p) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    k * p ^ j ≤ p ^ k * j := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  have h1 : 2 * d + 1 ≤ p ^ d :=
    (Lemma129e.three_pow_ge d).trans (Nat.pow_le_pow_left hp d)
  have h2 : j + d ≤ p ^ d * j := by nlinarith
  rw [pow_add]
  calc (j + d) * p ^ j ≤ (p ^ d * j) * p ^ j := Nat.mul_le_mul_right _ h2
    _ = p ^ j * p ^ d * j := by ring

theorem sup_step (hp : p.Prime) {R : Subgroup (Perm Ω)} {S O : Finset Ω} {k j e' : ℕ}
    (hOk : O.card ≤ p ^ k) {E' G : Subgroup (Perm Ω)} (hE'alt : E' ≤ alternatingGroup Ω)
    (hE'el : CFSG.Open.IsElemAbelian p E') (hE'c : E' ≤ Subgroup.centralizer (R : Set (Perm Ω)))
    (hE'fix : E' ≤ fixOut ((S \ O : Finset Ω) : Set Ω))
    (hE'T : ∀ y, ∃ T : Finset Ω, y ∈ T ∧ T.card ≤ p ^ k ∧ E' ≤ setStab (T : Set Ω))
    (hE'card : Nat.card E' = p ^ e') (hOS : O ⊆ S)
    (hGalt : G ≤ alternatingGroup Ω) (hGel : CFSG.Open.IsElemAbelian p G)
    (hGc : G ≤ Subgroup.centralizer (R : Set (Perm Ω))) (hGfix : G ≤ fixOut (O : Set Ω))
    (hGcard : p ^ j ≤ Nat.card G) :
    ∃ E : Subgroup (Perm Ω), E ≤ alternatingGroup Ω ∧ CFSG.Open.IsElemAbelian p E ∧
      E ≤ Subgroup.centralizer (R : Set (Perm Ω)) ∧ E ≤ fixOut (S : Set Ω) ∧
      (∀ y, ∃ T : Finset Ω, y ∈ T ∧ T.card ≤ p ^ k ∧ E ≤ setStab (T : Set Ω)) ∧
      ∃ e : ℕ, Nat.card E = p ^ e ∧ e' + j ≤ e := by
  haveI := Fact.mk hp
  have hdisj : ∀ z ∈ (O : Set Ω), z ∉ ((S \ O : Finset Ω) : Set Ω) := by
    intro z hz hz'
    rw [Finset.coe_sdiff, Set.mem_diff] at hz'
    exact hz'.2 hz
  have hE'O : E' ≤ setStab (O : Set Ω) := hE'fix.trans (fixOut_le_setStab hdisj)
  have hGO : G ≤ setStab (O : Set Ω) := hGfix.trans (fixOut_le_setStab_self _)
  have hcomm : ∀ a ∈ E', ∀ b ∈ G, a * b = b * a := by
    intro a ha b hb
    ext y
    simp only [Perm.mul_apply]
    by_cases hy : y ∈ (O : Set Ω)
    · have hby : b y ∈ (O : Set Ω) := (hGO hb y).1 hy
      rw [hE'fix ha _ (hdisj _ hby), hE'fix ha _ (hdisj _ hy)]
    · have hay : a y ∉ (O : Set Ω) := fun h => hy ((hE'O ha y).2 h)
      rw [hGfix hb _ hy, hGfix hb _ hay]
  have hd : ∀ a ∈ E', a ∈ G → a = 1 := by
    intro a ha haG
    ext y
    by_cases hy : y ∈ (O : Set Ω)
    · exact hE'fix ha _ (hdisj _ hy)
    · exact hGfix haG _ hy
  refine ⟨E' ⊔ G, sup_le hE'alt hGalt, hE'el.sup_of_commute hGel hcomm, sup_le hE'c hGc,
    sup_le (hE'fix.trans (fixOut_mono ?_)) (hGfix.trans (fixOut_mono ?_)), ?_, ?_⟩
  · intro z hz
    rw [Finset.coe_sdiff, Set.mem_diff] at hz
    exact hz.1
  · intro z hz
    exact hOS hz
  · intro y
    by_cases hy : y ∈ O
    · exact ⟨O, hy, hOk, sup_le hE'O hGO⟩
    · obtain ⟨T', hyT', hT'k, hE'T'⟩ := hE'T y
      refine ⟨T' \ O, Finset.mem_sdiff.2 ⟨hyT', hy⟩,
        (Finset.card_le_card Finset.sdiff_subset).trans hT'k, sup_le ?_ ?_⟩
      · intro a ha
        rw [Finset.coe_sdiff]
        exact setStab_sdiff (hE'T' ha) (hE'O ha)
      · intro b hb
        rw [Finset.coe_sdiff]
        intro z
        by_cases hz : z ∈ (O : Set Ω)
        · have hbz : b z ∈ (O : Set Ω) := (hGO hb z).1 hz
          simp only [Set.mem_diff]
          exact ⟨fun h => absurd hz h.2, fun h => absurd hbz h.2⟩
        · rw [hGfix hb z hz]
  · have hpg : IsPGroup p ↥(E' ⊔ G) := (hE'el.sup_of_commute hGel hcomm).isPGroup
    obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hpg
    refine ⟨e, he, ?_⟩
    have h1 := card_mul_le_card_sup E' G hd
    rw [hE'card, he] at h1
    have h2 : p ^ (e' + j) ≤ p ^ e := by
      rw [pow_add]
      exact (Nat.mul_le_mul_left _ hGcard).trans h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h2

@[expose] def resO (O : Finset Ω) (f : Perm Ω) (hf : ∀ y, f y ∈ O ↔ y ∈ O) : Perm Ω :=
  ofSubtype (f.subtypePerm (p := (· ∈ O)) hf)

theorem resO_apply_mem {O : Finset Ω} {f : Perm Ω} (hf : ∀ y, f y ∈ O ↔ y ∈ O) {y : Ω}
    (hy : y ∈ O) : resO O f hf y = f y := by
  unfold resO
  rw [ofSubtype_apply_of_mem (a := y) _ hy]
  simp

theorem resO_apply_not_mem {O : Finset Ω} {f : Perm Ω} (hf : ∀ y, f y ∈ O ↔ y ∈ O) {y : Ω}
    (hy : y ∉ O) : resO O f hf y = y := by
  unfold resO
  exact ofSubtype_apply_of_not_mem _ hy

@[expose] def resHom (O : Finset Ω) (R : Subgroup (Perm Ω)) (hR : ∀ r ∈ R, ∀ y, r y ∈ O ↔ y ∈ O) :
    ↥R →* Perm Ω where
  toFun r := resO O r (hR r r.2)
  map_one' := by
    ext y
    by_cases hy : y ∈ O
    · rw [resO_apply_mem _ hy]; rfl
    · rw [resO_apply_not_mem _ hy]; rfl
  map_mul' r s := by
    ext y
    by_cases hy : y ∈ O
    · have hsy : (s : Perm Ω) y ∈ O := (hR s s.2 y).2 hy
      rw [Perm.mul_apply, resO_apply_mem _ hy, resO_apply_mem _ hy, resO_apply_mem _ hsy]
      rfl
    · have hsy : (s : Perm Ω) y ∉ O := fun h => hy ((hR s s.2 y).1 h)
      rw [Perm.mul_apply, resO_apply_not_mem _ hy, resO_apply_not_mem _ hy,
        resO_apply_not_mem _ hy]

theorem addRight_pow_apply (a : ZMod p) (n : ℕ) (z : ZMod p) :
    ((Equiv.addRight a) ^ n) z = z + n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, Equiv.coe_addRight]
    push_cast
    ring

theorem exists_E (hp : p.Prime) (hp2 : p ≠ 2) (R : Subgroup (Perm Ω))
    (hR : CFSG.Open.IsElemAbelian p R) {k : ℕ} (hk : 1 ≤ k)
    (horb : ∀ x : Ω, {y | ∃ r ∈ R, r x = y}.ncard ≤ p ^ k) :
    ∀ (m : ℕ) (S : Finset Ω), S.card = m → (∀ r ∈ R, ∀ x, x ∈ S ↔ r x ∈ S) →
      ∃ E : Subgroup (Perm Ω), E ≤ alternatingGroup Ω ∧ CFSG.Open.IsElemAbelian p E ∧
        E ≤ Subgroup.centralizer (R : Set (Perm Ω)) ∧ E ≤ fixOut (S : Set Ω) ∧
        (∀ y, ∃ T : Finset Ω, y ∈ T ∧ T.card ≤ p ^ k ∧ E ≤ setStab (T : Set Ω)) ∧
        ∃ e : ℕ, Nat.card E = p ^ e ∧ k * (m - m % p) ≤ p ^ k * e := by
  classical
  haveI := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro S hS hSinv
  by_cases hmov : ∃ x ∈ S, ∃ r ∈ R, r x ≠ x
  · obtain ⟨x, hxS, r₀, hr₀, hr₀x⟩ := hmov
    set O : Finset Ω := Finset.univ.filter (fun y => ∃ r ∈ R, r x = y) with hO
    have hmemO : ∀ y, y ∈ O ↔ ∃ r ∈ R, r x = y := fun y => by simp [hO]
    have hOinv : ∀ r ∈ R, ∀ y, r y ∈ O ↔ y ∈ O := by
      intro r hr y
      rw [hmemO, hmemO]
      constructor
      · rintro ⟨s, hs, hsy⟩
        refine ⟨r⁻¹ * s, R.mul_mem (R.inv_mem hr) hs, ?_⟩
        rw [Perm.mul_apply, hsy]
        simp
      · rintro ⟨s, hs, rfl⟩
        exact ⟨r * s, R.mul_mem hr hs, rfl⟩
    have hOS : O ⊆ S := by
      intro y hy
      obtain ⟨s, hs, rfl⟩ := (hmemO y).1 hy
      exact (hSinv s hs x).1 hxS
    have hxO : x ∈ O := (hmemO x).2 ⟨1, R.one_mem, rfl⟩
    have hr₀O : r₀ x ∈ O := (hmemO _).2 ⟨r₀, hr₀, rfl⟩
    have hOset : {y | ∃ r ∈ R, r x = y} = (O : Set Ω) := by
      ext y
      rw [Finset.mem_coe, hmemO]
      rfl
    have hOorb : (O : Set Ω) = MulAction.orbit ↥R x := by
      ext y
      rw [Finset.mem_coe, hmemO, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨⟨r, hr⟩, rfl⟩
      · rintro ⟨r, rfl⟩
        exact ⟨r, r.2, rfl⟩
    have hOcard : O.card = (MulAction.orbit ↥R x).ncard := by
      rw [← hOorb, Set.ncard_coe_finset]
    obtain ⟨j, hj⟩ : ∃ j, O.card = p ^ j := by
      obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 hR.isPGroup
      have h1 : (MulAction.orbit ↥R x).ncard ∣ p ^ r := by
        rw [← hr, ← MulAction.index_stabilizer ↥R x]
        exact Subgroup.index_dvd_card _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h1
      exact ⟨j, hOcard.trans hj⟩
    have hOk : O.card ≤ p ^ k := by
      have := horb x
      rwa [hOset, Set.ncard_coe_finset] at this
    have hj1 : 1 ≤ j := by
      by_contra hj0
      have h1 : O.card = 1 := by rw [hj, show j = 0 by omega, pow_zero]
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
      rw [ha, Finset.mem_singleton] at hxO hr₀O
      exact hr₀x (hr₀O.trans hxO.symm)
    have hjk : j ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hj ▸ hOk)
    have hS'inv : ∀ r ∈ R, ∀ y, y ∈ S \ O ↔ r y ∈ S \ O := by
      intro r hr y
      rw [Finset.mem_sdiff, Finset.mem_sdiff, ← hSinv r hr y, hOinv r hr y]
    have hpj : p ^ j ≤ m := by rw [← hj, ← hS]; exact Finset.card_le_card hOS
    have hS'card : (S \ O).card = m - p ^ j := by rw [Finset.card_sdiff_of_subset hOS, hS, hj]
    have hlt : m - p ^ j < m := by have := Nat.one_le_pow j p hp.pos; omega
    obtain ⟨E', hE'alt, hE'el, hE'c, hE'fix, hE'T, e', hE'card, hE'ineq⟩ :=
      ih (m - p ^ j) hlt (S \ O) hS'card hS'inv
    set ρ := resHom O R hOinv with hρ
    set G := ρ.range with hG
    have hGexp : ∀ g ∈ G, g ^ p = 1 := by
      rintro _ ⟨r, rfl⟩
      rw [← map_pow]
      have : r ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hR.2 r r.2)
      rw [this, map_one]
    have hGel : CFSG.Open.IsElemAbelian p G := by
      have h1 : CFSG.Open.IsElemAbelian p (⊤ : Subgroup ↥R) := by
        have := hR.subgroupOf R
        rwa [Subgroup.subgroupOf_self] at this
      rw [hG, MonoidHom.range_eq_map]
      exact h1.map ρ
    have hGalt : G ≤ alternatingGroup Ω := fun g hg =>
      mem_alternatingGroup.2 (sign_eq_one_of_pow hodd (hGexp g hg))
    have hGfix : G ≤ fixOut (O : Set Ω) := by
      rintro _ ⟨r, rfl⟩ y hy
      exact resO_apply_not_mem _ hy
    have hGc : G ≤ Subgroup.centralizer (R : Set (Perm Ω)) := by
      rintro _ ⟨r, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      ext y
      simp only [Perm.mul_apply]
      change s (resO O r (hOinv r r.2) y) = resO O r (hOinv r r.2) (s y)
      by_cases hy : y ∈ O
      · have hsy : s y ∈ O := (hOinv s hs y).2 hy
        rw [resO_apply_mem _ hy, resO_apply_mem _ hsy]
        have := hR.comm hs r.2
        exact congrArg (fun f : Perm Ω => f y) this
      · have hsy : s y ∉ O := fun h => hy ((hOinv s hs y).1 h)
        rw [resO_apply_not_mem _ hy, resO_apply_not_mem _ hsy]
    have hGcard : p ^ j ≤ Nat.card G := by
      have hGx : ∀ g : ↥G, (g : Perm Ω) x ∈ O := fun g =>
        (hGfix.trans (fixOut_le_setStab_self _)) g.2 x |>.1 hxO
      have hsurj : Function.Surjective (fun g : ↥G => (⟨(g : Perm Ω) x, hGx g⟩ : ↥O)) := by
        rintro ⟨y, hy⟩
        obtain ⟨s, hs, rfl⟩ := (hmemO y).1 hy
        refine ⟨⟨ρ ⟨s, hs⟩, ⟨s, hs⟩, rfl⟩, ?_⟩
        apply Subtype.ext
        change resO O s (hOinv s hs) x = s x
        exact resO_apply_mem _ hxO
      have h1 := Nat.card_le_card_of_surjective _ hsurj
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hj] at h1
      exact h1
    obtain ⟨E, hEalt, hEel, hEc, hEfix, hET, e, hEcard, he⟩ :=
      sup_step hp hOk hE'alt hE'el hE'c hE'fix hE'T hE'card hOS hGalt hGel hGc hGfix hGcard
    refine ⟨E, hEalt, hEel, hEc, hEfix, hET, e, hEcard, ?_⟩
    have hmod : m % p = (m - p ^ j) % p := by
      have h1 : m - p ^ j + p * p ^ (j - 1) = m := by
        rw [← pow_succ', Nat.sub_add_cancel hj1]; omega
      have h2 := Nat.add_mul_mod_self_left (m - p ^ j) p (p ^ (j - 1))
      rw [h1] at h2
      exact h2
    have hle := Nat.mod_le (m - p ^ j) p
    have hab := arith_block hp3 hj1 hjk
    have h2 : m - m % p = (m - p ^ j - (m - p ^ j) % p) + p ^ j := by rw [hmod]; omega
    rw [h2, mul_add]
    calc k * (m - p ^ j - (m - p ^ j) % p) + k * p ^ j ≤ p ^ k * e' + p ^ k * j :=
          Nat.add_le_add hE'ineq hab
      _ = p ^ k * (e' + j) := by ring
      _ ≤ p ^ k * e := Nat.mul_le_mul_left _ he
  · push Not at hmov
    by_cases hmp : m < p
    · refine ⟨⊥, bot_le, CFSG.Open.isElemAbelian_bot p, bot_le, bot_le,
        fun y => ⟨{y}, Finset.mem_singleton_self y, ?_, bot_le⟩, 0,
        by rw [Subgroup.card_bot, pow_zero], ?_⟩
      · rw [Finset.card_singleton]
        exact Nat.one_le_pow _ _ hp.pos
      · rw [Nat.mod_eq_of_lt hmp, Nat.sub_self, mul_zero]
        exact Nat.zero_le _
    · push Not at hmp
      obtain ⟨T₀, hT₀S, hT₀card⟩ := Finset.exists_subset_card_eq (show p ≤ S.card by rw [hS]; exact hmp)
      have hcardZ : Fintype.card (ZMod p) = Fintype.card ↥T₀ := by
        rw [ZMod.card, Fintype.card_coe, hT₀card]
      set f₀ : ZMod p ≃ ↥T₀ := Fintype.equivOfCardEq hcardZ with hf₀
      set c : Perm Ω := (Equiv.addRight (1 : ZMod p)).extendDomain f₀ with hc
      have hcp : c ^ p = 1 := by
        have h1 : (Equiv.addRight (1 : ZMod p)) ^ p = 1 := by
          ext z
          rw [addRight_pow_apply, ZMod.natCast_self, zero_mul, add_zero, Perm.one_apply]
        have h2 : c = Perm.extendDomainHom f₀ (Equiv.addRight (1 : ZMod p)) := rfl
        rw [h2, ← map_pow, h1, map_one]
      have hc1 : c ≠ 1 := by
        intro h
        have h1 : c (f₀ 0) = f₀ (0 + 1) := Perm.extendDomain_apply_image _ _ _
        rw [h, Perm.one_apply, zero_add] at h1
        have h2 := f₀.injective (Subtype.ext h1)
        exact zero_ne_one h2
      have hcout : ∀ y, y ∉ T₀ → c y = y := fun y hy => Perm.extendDomain_apply_not_subtype _ _ hy
      have hcin : ∀ y, y ∈ T₀ → c y ∈ T₀ := by
        intro y hy
        have : y = (f₀ (f₀.symm ⟨y, hy⟩) : Ω) := by simp
        rw [this, Perm.extendDomain_apply_image]
        exact (f₀ _).2
      have hRT : ∀ r ∈ R, ∀ y, y ∈ T₀ ↔ r y ∈ T₀ := by
        intro r hr y
        constructor
        · intro hy
          rw [hmov y (hT₀S hy) r hr]
          exact hy
        · intro hy
          have h1 := hmov (r y) (hT₀S hy) r hr
          rw [r.injective h1] at hy
          exact hy
      set G := Subgroup.zpowers c with hG
      have hcfix : c ∈ fixOut (T₀ : Set Ω) := fun y hy => hcout y hy
      have hGfix : G ≤ fixOut (T₀ : Set Ω) := (Subgroup.zpowers_le).2 hcfix
      have hGalt : G ≤ alternatingGroup Ω :=
        (Subgroup.zpowers_le).2 (mem_alternatingGroup.2 (sign_eq_one_of_pow hodd hcp))
      have hGel : CFSG.Open.IsElemAbelian p G := by
        rw [hG, Subgroup.zpowers_eq_closure]
        refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
        · intro a ha b hb
          rw [Set.mem_singleton_iff] at ha hb
          rw [ha, hb]
        · intro a ha
          rw [Set.mem_singleton_iff] at ha
          rw [ha, hcp]
      have hGc : G ≤ Subgroup.centralizer (R : Set (Perm Ω)) := by
        refine (Subgroup.zpowers_le).2 ?_
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        ext y
        simp only [Perm.mul_apply]
        by_cases hy : y ∈ T₀
        · rw [hmov y (hT₀S hy) r hr, hmov (c y) (hT₀S (hcin y hy)) r hr]
        · have hry : r y ∉ T₀ := fun h => hy ((hRT r hr y).2 h)
          rw [hcout y hy, hcout (r y) hry]
      have hGcard : p ^ 1 ≤ Nat.card G := by
        rw [hG, Nat.card_zpowers, orderOf_eq_prime hcp hc1, pow_one]
      have hS'inv : ∀ r ∈ R, ∀ y, y ∈ S \ T₀ ↔ r y ∈ S \ T₀ := by
        intro r hr y
        rw [Finset.mem_sdiff, Finset.mem_sdiff, ← hSinv r hr y, ← hRT r hr y]
      have hS'card : (S \ T₀).card = m - p := by
        rw [Finset.card_sdiff_of_subset hT₀S, hS, hT₀card]
      obtain ⟨E', hE'alt, hE'el, hE'c, hE'fix, hE'T, e', hE'card, hE'ineq⟩ :=
        ih (m - p) (by have := hp.pos; omega) (S \ T₀) hS'card hS'inv
      have hT₀k : T₀.card ≤ p ^ k := by
        rw [hT₀card]
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
      obtain ⟨E, hEalt, hEel, hEc, hEfix, hET, e, hEcard, he⟩ :=
        sup_step hp hT₀k hE'alt hE'el hE'c hE'fix hE'T hE'card hT₀S hGalt hGel hGc hGfix hGcard
      refine ⟨E, hEalt, hEel, hEc, hEfix, hET, e, hEcard, ?_⟩
      have hmod : m % p = (m - p) % p := by
        have h1 : m - p + p * 1 = m := by omega
        have h2 := Nat.add_mul_mod_self_left (m - p) p 1
        rw [h1] at h2
        exact h2
      have hle := Nat.mod_le (m - p) p
      have hab := arith_block (j := 1) (k := k) hp3 le_rfl hk
      rw [pow_one, mul_one] at hab
      have h2 : m - m % p = (m - p - (m - p) % p) + p := by rw [hmod]; omega
      rw [h2, mul_add]
      calc k * (m - p - (m - p) % p) + k * p ≤ p ^ k * e' + p ^ k * 1 := by
            rw [mul_one]; exact Nat.add_le_add hE'ineq hab
        _ = p ^ k * (e' + 1) := by ring
        _ ≤ p ^ k * e := Nat.mul_le_mul_left _ he

end Five

section FiveGen

open MulAction GL83 GL83.PiGen

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {p : ℕ} [Fact p.Prime]

theorem perm_gen_le (hp3 : 3 ≤ p) {R : Subgroup (Perm Ω)} (hR : IsPGroup p R)
    (hnp : ¬ p ∣ Fintype.card Ω) (h3 : 3 ≤ Fintype.card Ω) {m : ℕ} (hm : 1 ≤ m)
    (horb : ∀ ω : Ω, Nat.card (orbit R ω) ≤ m) :
    alternatingGroup Ω ≤ ⨆ (E : {E : Subgroup (Perm Ω) // E ≤ R ∧ Nat.card R ≤ m * Nat.card E}),
      altOn (fixSet E.1) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hmod : ∀ E : Subgroup (Perm Ω), E ≤ R →
      Fintype.card Ω ≡ Nat.card (fixSet E) [MOD p] := by
    intro E hE
    have := card_fixSet_modEq (p := p) (hR.to_le hE)
    rwa [Nat.card_eq_fintype_card] at this
  have hω₀ : ∃ ω₀, ω₀ ∈ fixSet R := by
    by_contra h
    have h' : ∀ ω, ω ∉ fixSet R := fun ω hω => h ⟨ω, hω⟩
    have hempty : fixSet R = ∅ := Set.eq_empty_of_forall_notMem h'
    have hm' := hmod R le_rfl
    have h0 : Nat.card (fixSet R) = 0 := by rw [hempty]; simp
    rw [h0] at hm'
    exact hnp ((Nat.modEq_zero_iff_dvd).1 hm')
  let P : Subgroup (Perm Ω) → Prop := fun E =>
    E ≤ R ∧ Nat.card R ≤ m * Nat.card E ∧ 3 ≤ Nat.card (fixSet E)
  have hgood : ∀ ω : Ω, ω ∉ fixSet R → P (stabIn R ω) ∧ ω ∈ fixSet (stabIn R ω) := by
    intro ω hω
    refine ⟨⟨stabIn_le R ω, ?_, ?_⟩, mem_fixSet_stabIn R ω⟩
    · rw [card_mul_card_stabIn R ω]
      exact Nat.mul_le_mul_right _ (horb ω)
    · have hsub : fixSet R ⊆ fixSet (stabIn R ω) := fixSet_anti (stabIn_le R ω)
      have hss : fixSet R ⊂ fixSet (stabIn R ω) :=
        ⟨hsub, fun h => hω (h (mem_fixSet_stabIn R ω))⟩
      have hlt : Nat.card (fixSet R) < Nat.card (fixSet (stabIn R ω)) := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        exact Set.ncard_lt_ncard hss
      have h1 := hmod R le_rfl
      have h2 := hmod (stabIn R ω) (stabIn_le R ω)
      have h3' : Nat.card (fixSet R) ≡ Nat.card (fixSet (stabIn R ω)) [MOD p] := h1.symm.trans h2
      have h4 := (Nat.modEq_iff_dvd' hlt.le).1 h3'
      have h5' : p ≤ Nat.card (fixSet (stabIn R ω)) - Nat.card (fixSet R) :=
        Nat.le_of_dvd (by omega) h4
      omega
  have hcover : ∀ ω : Ω, ∃ E, P E ∧ ω ∈ fixSet E := by
    intro ω
    by_cases hnt : ∃ ω', ω' ∉ fixSet R
    · by_cases hω : ω ∈ fixSet R
      · obtain ⟨ω', hω'⟩ := hnt
        exact ⟨stabIn R ω', (hgood ω' hω').1, fixSet_anti (stabIn_le R ω') hω⟩
      · exact ⟨stabIn R ω, (hgood ω hω).1, (hgood ω hω).2⟩
    · have hall : ∀ ω', ω' ∈ fixSet R := fun ω' => by_contra fun h => hnt ⟨ω', h⟩
      have hfix : fixSet R = Set.univ := Set.eq_univ_of_forall hall
      refine ⟨R, ⟨le_rfl, ?_, ?_⟩, hall ω⟩
      · nlinarith [Nat.card_pos (α := R)]
      · rw [hfix, Nat.card_univ, Nat.card_eq_fintype_card]
        exact h3
  obtain ⟨ω₀, hω₀R⟩ := hω₀
  have : Nonempty Ω := ⟨ω₀⟩
  let ι : Type _ := {E : Subgroup (Perm Ω) // P E}
  have hS3 : ∀ E : ι, 3 ≤ (fixSet E.1).ncard := fun E => by
    have := E.2.2.2
    rwa [Nat.card_coe_set_eq] at this
  have hcov : (⋃ E : ι, fixSet E.1) = Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ?_
    obtain ⟨E, hE, hωE⟩ := hcover ω
    exact Set.mem_iUnion.2 ⟨⟨E, hE⟩, hωE⟩
  have hconn : ∀ i j : ι,
      Relation.ReflTransGen (fun a b : ι => (fixSet a.1 ∩ fixSet b.1).Nonempty) i j :=
    fun i j => Relation.ReflTransGen.single
      ⟨ω₀, fixSet_anti i.2.1 hω₀R, fixSet_anti j.2.1 hω₀R⟩
  have hgen := iSup_altOn_eq_alternatingGroup (S := fun E : ι => fixSet E.1) hS3 hcov hconn
  rw [← hgen]
  exact iSup_le fun E => le_iSup_of_le ⟨E.1, E.2.1, E.2.2.1⟩ le_rfl

end FiveGen

open GL83 GL83.PiGen in
theorem input23_5_holds : Lemma129e.Input23_5 := by
  intro p n k hp hp2 hpn hk1 hkn K _ _ φ B _ hBel horb1 _
  classical
  haveI := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set R : Subgroup (Perm (Fin n)) := (B.map φ.toMonoidHom).map (alternatingGroup (Fin n)).subtype
    with hR
  have hRel : CFSG.Open.IsElemAbelian p R := (hBel.map _).map _
  have horb : ∀ x : Fin n, {y | ∃ r ∈ R, r x = y}.ncard ≤ p ^ k := by
    intro x
    have h1 := horb1 x
    unfold Lemma129e.orbitLen at h1
    have h2 : {y | ∃ r ∈ R, r x = y} =
        {j : Fin n | ∃ b ∈ B, ((φ b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) x = j} := by
      ext y
      constructor
      · rintro ⟨r, ⟨a, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
        exact ⟨b, hb, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨_, ⟨φ b, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
    rw [h2]
    exact h1
  obtain ⟨E, hEalt, hEel, hEc, -, hET, e, hEcard, hEineq⟩ :=
    exists_E hp hp2 R hRel hk1 horb n Finset.univ (by simp) (by simp)
  have hnp : n % p ≤ n := Nat.mod_le n p
  have hdiv1 : p ^ k * (n / p ^ k) ≤ p * (n / p) := by
    have h1 : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h1, mul_assoc]
    apply Nat.mul_le_mul_left
    rw [Nat.le_div_iff_mul_le hp.pos]
    calc p ^ (k - 1) * (n / (p * p ^ (k - 1))) * p = p * p ^ (k - 1) * (n / (p * p ^ (k - 1))) := by
          ring
      _ ≤ n := Nat.mul_div_le n _
  have hdiv2 : p * (n / p) = n - n % p := by
    have := Nat.div_add_mod n p
    omega
  have hrank : k * (n / p ^ k) ≤ e := by
    have h1 : p ^ k * (k * (n / p ^ k)) ≤ p ^ k * e := by
      calc p ^ k * (k * (n / p ^ k)) = k * (p ^ k * (n / p ^ k)) := by ring
        _ ≤ k * (n - n % p) := Nat.mul_le_mul_left _ (hdiv2 ▸ hdiv1)
        _ ≤ p ^ k * e := hEineq
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos k)
  have hnpk : p ≤ n / p ^ k := by
    rw [Nat.le_div_iff_mul_le (pow_pos hp.pos k), ← pow_succ']
    exact hkn.le
  have he2 : k + 2 ≤ e := by nlinarith
  set EA : Subgroup ↥(alternatingGroup (Fin n)) := E.subgroupOf (alternatingGroup (Fin n)) with hEA
  have hEAel : CFSG.Open.IsElemAbelian p EA := hEel.subgroupOf _
  have hEAcard : Nat.card EA = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEalt).toEquiv
  have hEArank : CFSG.Open.pRank p EA = e := by
    have h1 := Lemma129.card_eq_pow_pRank hp hEAel
    rw [hEAcard, hEcard] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  have hcore : CFSG.Open.GLBCore p 2 EA = ⊤ := by
    have horbE : ∀ ω : Fin n, Nat.card (MulAction.orbit E ω) ≤ p ^ k := by
      intro ω
      obtain ⟨T, hωT, hTk, hET'⟩ := hET ω
      have hsub : MulAction.orbit E ω ⊆ (T : Set (Fin n)) := by
        rintro _ ⟨g, rfl⟩
        exact (hET' g.2 ω).1 hωT
      rw [Nat.card_coe_set_eq]
      calc (MulAction.orbit E ω).ncard ≤ (T : Set (Fin n)).ncard := Set.ncard_le_ncard hsub
        _ = T.card := Set.ncard_coe_finset T
        _ ≤ p ^ k := hTk
    have hgen := perm_gen_le hp3 hEel.isPGroup (by rwa [Fintype.card_fin])
      (by rw [Fintype.card_fin]; have : p ^ (k + 1) ≥ 3 := by
            calc 3 ≤ p := hp3
              _ = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp.pos (by omega)
          omega)
      (Nat.one_le_pow _ _ hp.pos) horbE
    have hle : alternatingGroup (Fin n) ≤
        (CFSG.Open.GLBCore p 2 EA).map (alternatingGroup (Fin n)).subtype := by
      refine hgen.trans (iSup_le fun F => ?_)
      intro g hg
      rw [mem_altOn] at hg
      obtain ⟨hgalt, hgfix⟩ := hg
      obtain ⟨F, hFE, hFi⟩ := F
      set FA : Subgroup ↥(alternatingGroup (Fin n)) := F.subgroupOf (alternatingGroup (Fin n))
        with hFA
      have hFAEA : FA ≤ EA := fun x hx => hFE hx
      have hFAel : CFSG.Open.IsElemAbelian p FA := hEAel.mono hFAEA
      have hFAcard : Nat.card FA = Nat.card F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hFE.trans hEalt)).toEquiv
      have hFArank : 2 ≤ CFSG.Open.pRank p FA := by
        have h1 := Lemma129.card_eq_pow_pRank hp hFAel
        rw [hFAcard] at h1
        rw [hEcard, h1, ← pow_add] at hFi
        have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hFi
        omega
      have hstab : ∀ x, g x ∈ fixSet F ↔ x ∈ fixSet F := by
        intro x
        constructor
        · intro hgx
          by_contra hx
          rw [hgfix x hx] at hgx
          exact hx hgx
        · intro hx
          by_contra hgx
          have h1 := hgfix (g x) hgx
          rw [g.injective h1] at hgx
          exact hgx hx
      have hcomm : ∀ f ∈ F, f * g = g * f := by
        intro f hf
        ext x
        simp only [Perm.mul_apply]
        by_cases hx : x ∈ fixSet F
        · rw [hx f hf, (hstab x).2 hx f hf]
        · have hfx : f x ∉ fixSet F := by
            intro h
            have h1 : f (f x) = f x := h f hf
            rw [f.injective h1] at h
            exact hx h
          rw [hgfix x hx, hgfix (f x) hfx]
      have hN : Subgroup.normalizer (FA : Set ↥(alternatingGroup (Fin n))) ≤
          CFSG.Open.GLBCore p 2 EA := le_sSup ⟨FA, hFAEA, hFArank, rfl⟩
      refine ⟨⟨g, hgalt⟩, hN (Subgroup.centralizer_le_normalizer _ ?_), rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      apply Subtype.ext
      exact hcomm (f : Perm (Fin n)) hf
    rw [eq_top_iff]
    intro a _
    obtain ⟨b, hb, hba⟩ := hle a.2
    have : b = a := Subtype.ext hba
    rw [← this]
    exact hb
  refine ⟨EA.map φ.symm.toMonoidHom, hEAel.map _, ?_, ?_, ?_⟩
  · rintro x hx _ ⟨a, ha, rfl⟩
    have h1 : ((φ x : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ R := ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
    have h2 := Subgroup.mem_centralizer_iff.1 (hEc (Subgroup.mem_subgroupOf.1 ha)) _ h1
    have h3 : φ x * a = a * φ x := Subtype.ext h2
    have h4 := congrArg φ.symm h3
    simp only [map_mul, MulEquiv.symm_apply_apply] at h4
    simpa using h4
  · rw [pRank_map_eq_of_injective hp.one_lt _ φ.symm.injective, hEArank]
    exact hrank
  · have h1 := Lemma129k.glbCore_le_comap (k := 2) hp.one_lt φ.symm.toMonoidHom φ.symm.injective EA
    rw [hcore] at h1
    rw [eq_top_iff]
    intro y _
    have h2 : φ y ∈ (⊤ : Subgroup ↥(alternatingGroup (Fin n))) := Subgroup.mem_top _
    have h3 := h1 h2
    rw [Subgroup.mem_comap] at h3
    simpa using h3

section I191

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_deltaTwo {p : ℕ} {X D : Subgroup G} (hDX : D ≤ X) (hD : IsElemAbelian p D) :
    D ≤ Subgroup.normalizer ((Lemma129.deltaTwo X D : Subgroup G) : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hkey : ∀ e ∈ D, ∀ z, z ∈ pCoreOf 2 (X ⊓ Subgroup.centralizer ({e} : Set G)) ↔
      d * z * d⁻¹ ∈ pCoreOf 2 (X ⊓ Subgroup.centralizer ({e} : Set G)) := by
    intro e he z
    have hdC : d ∈ X ⊓ Subgroup.centralizer ({e} : Set G) :=
      ⟨hDX hd, Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hD hd he)⟩
    exact Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hdC) z
  simp only [Lemma129.deltaTwo, Subgroup.mem_iInf]
  exact ⟨fun h e he he1 => (hkey e he y).1 (h e he he1),
    fun h e he he1 => (hkey e he y).2 (h e he he1)⟩

theorem inDelta_deltaTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X D : Subgroup G} (hDX : D ≤ X)
    (hD : IsElemAbelian p D) (hD1 : D ≠ ⊥) : InDelta p X D (Lemma129.deltaTwo X D) := by
  have hle : ∀ e ∈ D, e ≠ 1 →
      Lemma129.deltaTwo X D ≤ pCoreOf 2 (X ⊓ Subgroup.centralizer ({e} : Set G)) :=
    fun e he he1 => (iInf_le _ e).trans ((iInf_le _ he).trans (iInf_le _ he1))
  obtain ⟨e₀, he₀, he₀1⟩ : ∃ e ∈ D, e ≠ 1 := by
    by_contra h
    push Not at h
    exact hD1 ((Subgroup.eq_bot_iff_forall D).2 h)
  refine ⟨hDX, hD, hD1, ?_, fun e he he1 =>
    (hle e he he1).trans (Inputs123a.pCoreOf_two_le_glaPPrimeCoreOf hp hp2 _)⟩
  exact (hle e₀ he₀ he₀1).trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)

theorem input19_1_two_holds : Lemma129.Input19_1_two := by
  intro G _ _ _ p hp hp2 X _ k D hk hEk
  obtain ⟨hDX, hDel, hDcard⟩ := hEk
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hΔ := inDelta_deltaTwo hp hp2 hDX hDel hD1
  refine ⟨⟨fun K hK => barX_le_normalizer (hΔ.main h1Stmt_zero hp hK).1, ?_⟩, fun K hK hnc => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have hy : (y : G) ∈ oPrimePOf p X := ⟨y, hz, rfl⟩
    have hsΔ : (s : G) ∈ Lemma129.deltaTwo X D := Subgroup.mem_subgroupOf.1 hs
    have hc := hΔ.commutator_oPrimePOf_le h1Stmt_zero hp (Subgroup.commutator_mem_commutator hy hsΔ)
    rw [commutatorElement_def, commutator_mem_core_iff y.2 s.2] at hc
    exact hc
  · have hn : ¬ ⁅K, Lemma129.deltaTwo X D⁆ ≤ GLAPPrimeCoreOf p X := fun h => hnc (by
      rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.1 hx
      have hsΔ : (s : G) ∈ Lemma129.deltaTwo X D := Subgroup.mem_subgroupOf.1 hs
      have hc := h (Subgroup.commutator_mem_commutator hxK hsΔ)
      rw [commutatorElement_def, commutator_mem_core_iff x.2 s.2] at hc
      exact hc)
    have hDN : D ≤ Subgroup.normalizer ((Lemma129.deltaTwo X D : Subgroup G) : Set G) :=
      le_normalizer_deltaTwo hDX hDel
    obtain ⟨hDK, hker, hne, -, -⟩ := hΔ.conclusions h1Stmt_zero hp hK hDcard hDN hn
    have himg_eq : autBar p (Lemma129.deltaTwo X D) K = Lemma123.DeltaImage p X D K := by
      unfold autBar Lemma123.DeltaImage
      rw [Subgroup.inf_subgroupOf_right]
      rfl
    have himg : autBar p (Lemma129.deltaTwo X D) K ≤
        localDeltaTwoIn (innerAut (barOf p K) ⊔ autBar p (Lemma129.deltaTwo X D) K) (autBar p D K) := by
      rw [himg_eq]
      exact Inputs123a.deltaImage_le hp hp2 hK.1 hDel
    refine ⟨hDK, ?_, ?_, himg⟩
    · rw [Subgroup.eq_bot_iff_forall]
      rintro x ⟨hxD, ⟨y, hy, rfl⟩, -⟩
      have h1 : (y : G) ∈ centralizerQuot K (GLAPPrimeCoreOf p K) :=
        (mem_centralizerQuot_iff_barAut_eq_one p y).2 hy
      have h2 : (y : G) ∈ kerB p D K := ⟨hxD, h1⟩
      rw [hker] at h2
      exact h2
    · intro hbal
      have hD'eq : autBar p D K = (D.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K) := by
        unfold autBar
        rw [inf_eq_left.2 hDK]
      have hEk' : IsEkIn p k (autBar p D K) (autBar p D K) := by
        refine ⟨le_rfl, ?_, ?_⟩
        · rw [hD'eq]
          exact (hDel.subgroupOf _).map _
        · rw [hD'eq, card_map_barAut hDK hker, hDcard]
      have hWne : autBar p (Lemma129.deltaTwo X D) K ≠ ⊥ := by
        unfold autBar
        rw [Subgroup.inf_subgroupOf_right]
        exact hne
      have hnormW : autBar p D K ≤ Subgroup.normalizer
          ((autBar p (Lemma129.deltaTwo X D) K : Subgroup (MulAut (barOf p K))) :
            Set (MulAut (barOf p K))) := by
        unfold autBar
        refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map (barAut p K))
        intro d hd
        rw [Subgroup.mem_normalizer_iff]
        intro w
        have hd' : (d : G) ∈ D := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hd)).1
        have h1 := Subgroup.mem_normalizer_iff.1 (hDN hd') (w : G)
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_mul,
          InvMemClass.coe_inv]
        constructor
        · rintro ⟨hw, hwN⟩
          exact ⟨h1.1 hw, Subgroup.mul_mem _ (Subgroup.mul_mem _ d.2 hwN) (Subgroup.inv_mem _ d.2)⟩
        · rintro ⟨hw, -⟩
          exact ⟨h1.2 hw, w.2⟩
      have hnorm : autBar p D K ≤ Subgroup.normalizer
          ((innerAut (barOf p K) ⊔ autBar p (Lemma129.deltaTwo X D) K : Subgroup (MulAut (barOf p K))) :
            Set (MulAut (barOf p K))) := by
        intro δ hδ
        have hI : ∀ ε : MulAut (barOf p K), ε ∈ Subgroup.normalizer
            ((innerAut (barOf p K) : Subgroup (MulAut (barOf p K))) : Set (MulAut (barOf p K))) := by
          intro ε
          rw [(Subgroup.normalizer_eq_top_iff).2 (Lemma123.innerAut_normal _)]
          exact Subgroup.mem_top _
        rw [Subgroup.mem_normalizer_iff]
        intro t
        constructor
        · intro ht
          exact conj_mem_sup_of_mem_normalizer (hI δ) (hnormW hδ) ht
        · intro ht
          have h1 := conj_mem_sup_of_mem_normalizer (hI δ⁻¹) (hnormW (Subgroup.inv_mem _ hδ)) ht
          simpa [mul_assoc] using h1
      have h0 := hbal (autBar p D K) hEk' (innerAut (barOf p K) ⊔ autBar p (Lemma129.deltaTwo X D) K)
        le_sup_left hnorm
      rw [h0] at himg
      exact hWne (le_bot_iff.1 himg)

end I191

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs129

end
