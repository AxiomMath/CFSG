module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviModules
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.InvariantsAut
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviCentralizers

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement

theorem map_rangeSubgroup_le_D4 {X : Type*} [Group X] {A : Type*} [AddGroup A] {x : A → X}
    (hx : ∀ a b, x (a + b) = x a * x b) (α : MulAut X) (c : A → A) (hc : ∀ a, α (x a) = x (c a)) :
    (rangeSubgroup hx).map α.toMonoidHom ≤ rangeSubgroup hx := by
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨c a, (hc a).symm⟩

theorem conj_mem_commutator_of_mem_normalizer_D4 {G : Type*} [Group G] {A B : Subgroup G}
    {g : G} (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) {x : G}
    (hx : x ∈ ⁅A, B⁆) : g * x * g⁻¹ ∈ ⁅A, B⁆ := by
  have h : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement, MulAut.conj_apply,
      MulAut.conj_apply]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hA a).1 ha)
      ((mem_normalizer_iff.1 hB b).1 hb)
  simpa using h hx

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem φ_pow_mem_D (k : ℕ) {y : X} (hy : y ∈ d.D) : (d.φ ^ k) y ∈ d.D := by
  have h2 := map_rangeSubgroup_le_D4 d.x₂_add (d.φ ^ k) _ (d.φ_pow_x₂ k)
  have h3 := map_rangeSubgroup_le_D4 d.x₃_add (d.φ ^ k) _ (d.φ_pow_x₃ k)
  have h4 := map_rangeSubgroup_le_D4 d.x₄_add (d.φ ^ k) _ (d.φ_pow_x₄ k)
  have h5 := map_rangeSubgroup_le_D4 d.x₅_add (d.φ ^ k) _ (d.φ_pow_x₅ k)
  have h6 := map_rangeSubgroup_le_D4 d.x₆_add (d.φ ^ k) _ (d.φ_pow_x₆ k)
  have hD : d.D.map (d.φ ^ k).toMonoidHom ≤ d.D := by
    simp only [D, F, W, Y, V, Subgroup.map_sup, U₂, U₃, U₄, U₅, U₆]
    exact sup_le_sup h2 (sup_le_sup h3 (sup_le_sup h4 (sup_le_sup h5 h6)))
  exact hD ⟨y, hy, rfl⟩

theorem φ_pow_u (k : ℕ) : (d.φ ^ k) d.u = d.u := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_u]

theorem φ_pow_v (k : ℕ) : (d.φ ^ k) d.v = d.v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_v]

theorem φ_pow_mem_leviShort (k : ℕ) {y : X} (hy : y ∈ d.leviShort) :
    (d.φ ^ k) y ∈ d.leviShort := by
  have h : d.leviShort.map (d.φ ^ k).toMonoidHom ≤ d.leviShort := by
    rw [leviShort, MonoidHom.map_closure, closure_le]
    rintro _ ⟨z, hz | hz, rfl⟩
    · obtain ⟨a, rfl⟩ := hz
      change (d.φ ^ k) (d.x₁ a) ∈ d.leviShort
      rw [d.φ_pow_x₁]
      exact d.x₁_mem_leviShort _
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      change (d.φ ^ k) d.u ∈ d.leviShort
      rw [d.φ_pow_u]
      exact d.u_mem_leviShort
  exact h ⟨y, hy, rfl⟩

theorem φ_pow_torus (k : ℕ) (h : (d.Γ₀)ˣ × d.Γˣ) :
    (d.φ ^ k) (d.torus h) = d.torus (h ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_torus, ← pow_mul, ← pow_succ]

theorem φ_pow_eq_one_of_forall {k : ℕ} (hk : ∀ c : d.Γ, c ^ 2 ^ k = c) : d.φ ^ k = 1 := by
  have hk₀ : ∀ c : d.Γ₀, c ^ 2 ^ k = c := fun c => Subtype.ext (by
    rw [SubmonoidClass.coe_pow]
    exact hk c)
  set E := (d.φ ^ k).toMonoidHom.eqLocus (MonoidHom.id X) with hE
  have hS : d.S ≤ E := by
    rw [S, sixClosure, closure_le]
    rintro _ (((((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩)
    · change (d.φ ^ k) (d.x₁ a) = d.x₁ a
      rw [d.φ_pow_x₁, hk]
    · change (d.φ ^ k) (d.x₂ a) = d.x₂ a
      rw [d.φ_pow_x₂, hk₀]
    · change (d.φ ^ k) (d.x₃ a) = d.x₃ a
      rw [d.φ_pow_x₃, hk]
    · change (d.φ ^ k) (d.x₄ a) = d.x₄ a
      rw [d.φ_pow_x₄, hk]
    · change (d.φ ^ k) (d.x₅ a) = d.x₅ a
      rw [d.φ_pow_x₅, hk₀]
    · change (d.φ ^ k) (d.x₆ a) = d.x₆ a
      rw [d.φ_pow_x₆, hk₀]
  have hW : closure ({d.u, d.v} : Set X) ≤ E := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact d.φ_pow_u k
    · exact d.φ_pow_v k
  have htop : (⊤ : Subgroup X) ≤ E := by
    rw [← d.sup_closure_eq_top]
    exact sup_le hS hW
  ext g
  exact htop (mem_top g)

theorem leviShort_le_normalizer_D : d.leviShort ≤ normalizer (d.D : Set X) := by
  rw [← d.normalizer_V_eq_normalizer_D]
  exact d.leviShort_le_normalizer_V

theorem J₁_le_normalizer_D : d.J₁ ≤ normalizer (d.D : Set X) :=
  inf_le_left.trans d.J_le_normalizer_D

theorem exists_mul_of_mem_normalizer_V {g : X} (hg : g ∈ normalizer (d.V : Set X)) :
    ∃ n ∈ d.D, ∃ s ∈ d.leviShort, ∃ j ∈ d.J₁, g = n * s * j := by
  obtain ⟨-, h2, -, hJ, -⟩ := d.yamada_three_eight_four
  rw [h2] at hg
  have h1 : d.leviShort ⊔ d.J₁ ≤ normalizer (d.D : Set X) :=
    sup_le d.leviShort_le_normalizer_D d.J₁_le_normalizer_D
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ h1, Set.mem_mul] at hg
  obtain ⟨n, hn, b, hb, rfl⟩ := hg
  have h3 : d.J₁ ≤ normalizer (d.leviShort : Set X) :=
    hJ.trans (centralizer_le_normalizer _)
  rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ h3,
    Set.mem_mul] at hb
  obtain ⟨s, hs, j, hj, rfl⟩ := hb
  exact ⟨n, hn, s, hs, j, hj, by rw [mul_assoc]⟩

theorem D_inf_leviShort : d.D ⊓ d.leviShort = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_left _ le_sup_left).trans d.yamada_three_eight_four.2.2.2.2.le)

theorem exists_mul_of_mem_D_sup_leviShort {g : X} (hg : g ∈ d.D ⊔ d.leviShort) :
    ∃ n ∈ d.D, ∃ s ∈ d.leviShort, g = n * s := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ d.leviShort_le_normalizer_D,
    Set.mem_mul] at hg
  obtain ⟨n, hn, s, hs, rfl⟩ := hg
  exact ⟨n, hn, s, hs, rfl⟩

theorem torus_conj_x₆_of_snd_eq_one (l : (d.Γ₀)ˣ) (a : d.Γ₀) :
    d.torus (l, 1) * d.x₆ a * (d.torus (l, 1))⁻¹ = d.x₆ ((l : d.Γ₀) * (l : d.Γ₀) * a) := by
  rw [d.torus_x₆]
  congr 1
  simp only [Units.val_one]
  have h1 : d.nm 1 = 1 := d.nm_one
  change (l : d.Γ₀) * (l : d.Γ₀) * d.nm 1 * a = _
  rw [h1, mul_one]

theorem eq_one_of_mem_J₁_of_mem_centralizer_V {j : X} (hj : j ∈ d.J₁)
    (hjV : j ∈ centralizer (d.V : Set X)) : j = 1 := by
  have h6 : j ∈ d.J₆ ⊓ d.J₁ := ⟨⟨hj.1, hjV⟩, hj⟩
  rw [d.J₆_inf_J₁, mem_bot] at h6
  exact h6

theorem centralizer_V_eq : centralizer (d.V : Set X) = d.D ⊔ d.leviShort := by
  apply le_antisymm
  · intro g hg
    obtain ⟨n, hn, s, hs, j, hj, rfl⟩ :=
      d.exists_mul_of_mem_normalizer_V (centralizer_le_normalizer _ hg)
    have hnV : n ∈ centralizer (d.V : Set X) := d.S_le_centralizer_V (d.D_le_S hn)
    have hsV : s ∈ centralizer (d.V : Set X) := d.leviShort_le_centralizer_V hs
    have hjV : j ∈ centralizer (d.V : Set X) := by
      have := mul_mem (inv_mem (mul_mem hnV hsV)) hg
      rwa [show (n * s)⁻¹ * (n * s * j) = j by group] at this
    rw [d.eq_one_of_mem_J₁_of_mem_centralizer_V hj hjV, mul_one]
    exact mul_mem (mem_sup_left hn) (mem_sup_right hs)
  · exact sup_le (d.D_le_S.trans d.S_le_centralizer_V) d.leviShort_le_centralizer_V

theorem leviShort_le_of_U₁_le {N : Subgroup X} (hU : d.U₁ ≤ N)
    (hN : d.leviShort ≤ normalizer (N : Set X)) : d.leviShort ≤ N := by
  have hg : d.u * d.x₁ 1 * d.u ∈ N := by
    have := (mem_normalizer_iff.1 (hN d.u_mem_leviShort) (d.x₁ 1)).1 (hU (d.x₁_mem_U₁ 1))
    rwa [d.u_inv] at this
  have hgL : d.u * d.x₁ 1 * d.u ∈ d.leviShort :=
    mul_mem (mul_mem d.u_mem_leviShort (d.x₁_mem_leviShort 1)) d.u_mem_leviShort
  rcases d.mem_leviShort_iff.1 hgL with ⟨x, hx, h, hh, he⟩ | ⟨x, hx, h, hh, y, hy, he⟩
  · exact absurd (he ▸ mul_mem (d.S_le_B (d.U₁_le_S hx)) (d.J_le_B hh.1))
      (d.u_x₁_u_not_mem_B one_ne_zero)
  have hhu : h * d.u ∈ N := by
    have e : x⁻¹ * (d.u * d.x₁ 1 * d.u) * y⁻¹ = h * d.u := by rw [he]; group
    rw [← e]
    exact mul_mem (mul_mem (inv_mem (hU hx)) hg) (inv_mem (hU hy))
  have hJ : d.J₆ ≤ N := by
    intro s hs
    obtain ⟨r, hr, rfl⟩ := d.exists_mul_self_eq_of_mem_J₆ hs
    have hr' := (mem_normalizer_iff.1 (hN (d.J₆_le_leviShort hr)) (h * d.u)).1 hhu
    have hur : d.u * r⁻¹ = r * d.u := by
      have := d.u_conj_eq_inv_of_mem_J₆ (inv_mem hr)
      rw [inv_inv] at this
      calc d.u * r⁻¹ = d.u * r⁻¹ * d.u * d.u := by rw [mul_assoc _ d.u d.u, d.u_mul_self,
            mul_one]
        _ = r * d.u := by rw [this]
    have hrh : r * h = h * r := d.J_commute hr.1 hh.1
    have e : r * (h * d.u) * r⁻¹ * (h * d.u)⁻¹ = r * r := by
      calc r * (h * d.u) * r⁻¹ * (h * d.u)⁻¹ = r * h * (d.u * r⁻¹) * d.u⁻¹ * h⁻¹ := by group
        _ = h * r * (r * d.u) * d.u⁻¹ * h⁻¹ := by rw [hrh, hur]
        _ = h * (r * r) * h⁻¹ := by group
        _ = r * r := by
          rw [show h * (r * r) * h⁻¹ = (h * r) * r * h⁻¹ by group, ← hrh,
            show r * h * r * h⁻¹ = r * (h * r) * h⁻¹ by group, ← hrh]
          group
    rw [← e]
    exact mul_mem hr' (inv_mem hhu)
  have hu : d.u ∈ N := by
    have := mul_mem (inv_mem (hJ hh)) hhu
    rwa [inv_mul_cancel_left] at this
  rw [leviShort, closure_le]
  rintro g (hg | hg)
  · exact hU hg
  · rw [Set.mem_singleton_iff.1 hg]
    exact hu

theorem U₁_le_commutator_leviShort : d.U₁ ≤ ⁅d.leviShort, d.leviShort⁆ := by
  obtain ⟨β, hβ⟩ := d.exists_units_ne_one
  have hβ2 : (β : d.Γ) ^ 2 + 1 ≠ 0 := by
    intro h0
    apply hβ
    have h1 : (β : d.Γ) ^ 2 = 1 := by
      have := congrArg (· + 1) h0
      simpa [add_assoc, CharTwo.add_self_eq_zero] using this
    exact d.units_eq_one_of_sq (Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one]))
  rintro _ ⟨a, rfl⟩
  have hJ : d.hBCD β ∈ d.leviShort :=
    d.J₆_le_leviShort (by rw [d.J₆_eq_range_hBCD]; exact ⟨β, rfl⟩)
  have h1 : d.hBCD β * d.x₁ (a / ((β : d.Γ) ^ 2 + 1)) * (d.hBCD β)⁻¹ =
      d.x₁ ((β : d.Γ) ^ 2 * (a / ((β : d.Γ) ^ 2 + 1))) := by
    rw [d.hBCD_apply, d.torus_x₁, Units.val_pow_eq_pow_val]
  have h2 : ⁅d.hBCD β, d.x₁ (a / ((β : d.Γ) ^ 2 + 1))⁆ = d.x₁ a := by
    rw [commutatorElement_def, h1, d.x₁_inv, ← d.x₁_add]
    congr 1
    field_simp
  rw [← h2]
  exact commutator_mem_commutator hJ (d.x₁_mem_leviShort _)

theorem commutator_self_le_D4 {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem commutator_leviShort : ⁅d.leviShort, d.leviShort⁆ = d.leviShort := by
  have := d.finite
  refine le_antisymm (commutator_self_le_D4 _) (d.leviShort_le_of_U₁_le
    d.U₁_le_commutator_leviShort fun s hs => mem_normalizer_fintype fun x hx => ?_)
  exact conj_mem_commutator (le_normalizer hs) hx

theorem D_le_commutator_sup_V : d.D ≤ ⁅d.D, d.leviShort⁆ ⊔ d.V := by
  have := d.finite
  have hVD : d.V ≤ d.D := d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D))
  have hTD : ⁅d.D, d.leviShort⁆ ⊔ d.V ≤ d.D := by
    refine sup_le ?_ hVD
    rw [commutator_le]
    intro n hn s hs
    rw [commutatorElement_def, show n * s * n⁻¹ * s⁻¹ = n * (s * n⁻¹ * s⁻¹) by group]
    exact mul_mem hn ((mem_normalizer_iff.1 (d.leviShort_le_normalizer_D hs) _).1 (inv_mem hn))
  have hN : d.leviShort ≤ normalizer ((⁅d.D, d.leviShort⁆ ⊔ d.V : Subgroup X) : Set X) :=
    fun s hs => mem_normalizer_sup (mem_normalizer_fintype fun x hx =>
      conj_mem_commutator_of_mem_normalizer_D4 (d.leviShort_le_normalizer_D hs)
        (le_normalizer hs) hx) (d.leviShort_le_normalizer_V hs)
  rcases d.leviShort_irreducible_D_mod_V le_sup_right hTD hN with hT | hT
  · exfalso
    obtain ⟨b, hb⟩ := d.exists_tr_eq 1
    have h1 : d.x₅ 1 ∈ ⁅d.D, d.leviShort⁆ := by
      rw [commutator_comm]
      have := commutator_mem_commutator (d.x₁_mem_leviShort 1) (d.F_le_D (d.x₄_mem_F b))
      rw [d.comm₁₄, one_mul] at this
      change d.x₅ (d.tr b) ∈ _ at this
      rwa [hb] at this
    have h2 : d.x₅ 1 ∈ d.V := hT ▸ mem_sup_left h1
    exact one_ne_zero (d.x₅_mem_V_iff.1 h2)
  · exact hT.ge

theorem commutator_D_sup_leviShort :
    ⁅d.D ⊔ d.leviShort, d.D ⊔ d.leviShort⁆ = d.D ⊔ d.leviShort := by
  refine le_antisymm (commutator_self_le_D4 _) (sup_le ?_ ?_)
  · refine d.D_le_commutator_sup_V.trans (sup_le (commutator_mono le_sup_left le_sup_right) ?_)
    rw [← d.commutator_D_eq]
    exact commutator_mono le_sup_left le_sup_left
  · calc d.leviShort = ⁅d.leviShort, d.leviShort⁆ := d.commutator_leviShort.symm
      _ ≤ _ := commutator_mono le_sup_right le_sup_right

theorem mem_D_of_mem_S_of_conj_u_mem_S {g : X} (hg : g ∈ d.S) (hu : d.u * g * d.u ∈ d.S) :
    g ∈ d.D := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hg
  have hun : d.u * n * d.u ∈ d.D := by
    have := (mem_normalizer_iff.1 d.u_mem_normalizer_D n).1 hn
    rwa [d.u_inv] at this
  have h1 : d.u * d.x₁ a * d.u ∈ d.S := by
    have e : d.u * (d.x₁ a * n) * d.u * (d.u * n * d.u)⁻¹ = d.u * d.x₁ a * d.u⁻¹ := by group
    rw [d.u_inv] at e
    rw [← e]
    exact mul_mem hu (inv_mem (d.D_le_S hun))
  have ha : a = 0 := by
    by_contra ha
    exact d.u_x₁_u_not_mem_B ha (d.S_le_B h1)
  rw [ha, d.x₁_zero, one_mul]
  exact hn

theorem le_D_of_isPGroup {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hS : d.S ≤ normalizer (Q : Set X)) (hu : d.u ∈ normalizer (Q : Set X)) : Q ≤ d.D := by
  have := d.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  have hQS : Q ≤ d.S := by
    have h1 : IsPGroup 2 (Q ⊔ (P : Subgroup X) : Subgroup X) :=
      hQ.to_sup_of_normal_left' P.isPGroup' (hP ▸ hS)
    have h2 := P.is_maximal' h1 le_sup_right
    rw [← hP, ← h2]
    exact le_sup_left
  intro x hx
  have hux : d.u * x * d.u ∈ d.S := by
    have := (mem_normalizer_iff.1 hu x).1 hx
    rw [d.u_inv] at this
    exact hQS this
  exact d.mem_D_of_mem_S_of_conj_u_mem_S (hQS hx) hux

theorem pow_two_pow_injective (k : ℕ) {a b : d.Γ} (h : a ^ 2 ^ k = b ^ 2 ^ k) : a = b := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, pow_mul, pow_mul] at h
    exact ih (d.sq_injective h)

theorem pow_two_pow_surjective_Γ₀ (k : ℕ) (a : d.Γ₀) : ∃ c : d.Γ₀, c ^ 2 ^ k = a := by
  have hinj : Function.Injective (fun c : d.Γ₀ => c ^ 2 ^ k) := fun b c h => Subtype.ext
    (d.pow_two_pow_injective k (by
      have := congrArg (fun z : d.Γ₀ => (z : d.Γ)) h
      simpa using this))
  exact Finite.surjective_of_injective hinj a

theorem mem_normalizer_V_of_conj_mul_φ_pow {g : X} {k : ℕ}
    (hV : ∀ y ∈ d.V, (MulAut.conj g * d.φ ^ k) y ∈ d.V) : g ∈ normalizer (d.V : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype fun y hy => ?_
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := d.pow_two_pow_surjective_Γ₀ k a
  have h := hV (d.x₆ c) (d.x₆_mem_V c)
  rwa [MulAut.mul_apply, d.φ_pow_x₆, MulAut.conj_apply] at h

theorem eq_conj_of_trivial_mod_D {α : MulAut X} (hV : ∀ y ∈ d.V, α y ∈ d.V)
    (hα : ∀ y ∈ d.leviShort, α y * y⁻¹ ∈ d.D) :
    ∃ n ∈ d.D, ∃ j ∈ d.J₁, α = MulAut.conj (n * j) := by
  obtain ⟨g, k, rfl⟩ := d.aut_eq α
  obtain ⟨n, hn, s, hs, j, hj, rfl⟩ :=
    d.exists_mul_of_mem_normalizer_V (d.mem_normalizer_V_of_conj_mul_φ_pow hV)
  have hjc : ∀ z ∈ d.leviShort, j * z * j⁻¹ = z := fun z hz => by
    rw [← mem_centralizer_iff.1 (d.yamada_three_eight_four.2.2.2.1 hj) z hz, mul_inv_cancel_right]
  have hfix : ∀ y ∈ d.leviShort, s * (d.φ ^ k) y * s⁻¹ = y := by
    intro y hy
    have hφy := d.φ_pow_mem_leviShort k hy
    have hz : s * (d.φ ^ k) y * s⁻¹ ∈ d.leviShort := mul_mem (mul_mem hs hφy) (inv_mem hs)
    have h1 := hα y hy
    rw [MulAut.mul_apply, MulAut.conj_apply,
      show n * s * j * (d.φ ^ k) y * (n * s * j)⁻¹ =
        n * (s * (j * (d.φ ^ k) y * j⁻¹) * s⁻¹) * n⁻¹ by group, hjc _ hφy] at h1
    set z := s * (d.φ ^ k) y * s⁻¹
    have hzn : z * n⁻¹ * z⁻¹ ∈ d.D :=
      (mem_normalizer_iff.1 (d.leviShort_le_normalizer_D hz) _).1 (inv_mem hn)
    have h2 : z * y⁻¹ ∈ d.D := by
      have e : z * y⁻¹ = (z * n⁻¹ * z⁻¹)⁻¹ * n⁻¹ * (n * z * n⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hzn) (inv_mem hn)) h1
    have h3 : z * y⁻¹ ∈ d.D ⊓ d.leviShort := Subgroup.mem_inf.2 ⟨h2, mul_mem hz (inv_mem hy)⟩
    rw [d.D_inf_leviShort, mem_bot, mul_inv_eq_one] at h3
    exact h3
  have h1 := hfix (d.x₁ 1) (d.x₁_mem_leviShort 1)
  rw [d.φ_pow_x₁, one_pow] at h1
  have hU₁c : ∀ a b : d.Γ, d.x₁ a * d.x₁ b = d.x₁ b * d.x₁ a := fun a b =>
    commute_of_add d.x₁_add a b
  obtain ⟨x, hx, h, hh, rfl⟩ : ∃ x ∈ d.U₁, ∃ h ∈ d.J₆, s = x * h := by
    rcases d.mem_leviShort_iff.1 hs with hB | ⟨x, hx, h, hh, y, hy, rfl⟩
    · exact hB
    exfalso
    obtain ⟨b, rfl⟩ := hy
    have e : d.u * d.x₁ 1 * d.u = (x * h)⁻¹ * d.x₁ 1 * (x * h) := by
      have e1 : x * h * d.u * d.x₁ b * d.x₁ 1 * (x * h * d.u * d.x₁ b)⁻¹ =
          x * h * (d.u * d.x₁ 1 * d.u⁻¹) * (x * h)⁻¹ := by
        rw [show x * h * d.u * d.x₁ b * d.x₁ 1 * (x * h * d.u * d.x₁ b)⁻¹ =
          x * h * d.u * (d.x₁ b * d.x₁ 1 * (d.x₁ b)⁻¹) * d.u⁻¹ * (x * h)⁻¹ by group,
          hU₁c b 1, mul_inv_cancel_right]
        group
      rw [e1, d.u_inv] at h1
      calc d.u * d.x₁ 1 * d.u = (x * h)⁻¹ * (x * h * (d.u * d.x₁ 1 * d.u) * (x * h)⁻¹) *
            (x * h) := by group
        _ = (x * h)⁻¹ * d.x₁ 1 * (x * h) := by rw [h1]
    have hxh : x * h ∈ d.B := mul_mem (d.S_le_B (d.U₁_le_S hx)) (d.J_le_B hh.1)
    refine d.u_x₁_u_not_mem_B one_ne_zero ?_
    rw [e]
    exact mul_mem (mul_mem (inv_mem hxh) (d.S_le_B (d.U₁_le_S (d.x₁_mem_U₁ 1)))) hxh
  obtain ⟨⟨l, m⟩, rfl, -⟩ := d.mem_J₆.1 hh
  obtain ⟨b, rfl⟩ := hx
  have hcoord : ∀ a : d.Γ, (m : d.Γ) * a ^ 2 ^ k = a := by
    intro a
    have h2 := hfix (d.x₁ a) (d.x₁_mem_leviShort a)
    rw [d.φ_pow_x₁, show d.x₁ b * d.torus (l, m) * d.x₁ (a ^ 2 ^ k) *
        (d.x₁ b * d.torus (l, m))⁻¹ =
        d.x₁ b * (d.torus (l, m) * d.x₁ (a ^ 2 ^ k) * (d.torus (l, m))⁻¹) * (d.x₁ b)⁻¹ by group,
      d.torus_x₁, hU₁c b, mul_inv_cancel_right] at h2
    exact d.x₁_injective h2
  have hm : m = 1 := Units.ext (by simpa using hcoord 1)
  have hk : ∀ c : d.Γ, c ^ 2 ^ k = c := fun c => by simpa [hm] using hcoord c
  have hφ := d.φ_pow_eq_one_of_forall hk
  have hl : d.torus (l, m) = 1 := by
    have h6 : d.torus (l, m) ∈ d.J₆ ⊓ d.J₁ := ⟨hh, (d.torus_mem_J₁_iff _).2 hm⟩
    rwa [d.J₆_inf_J₁, mem_bot] at h6
  rw [hl, mul_one] at hfix ⊢
  have hb : b = 0 := by
    by_contra hb
    have h2 := hfix d.u d.u_mem_leviShort
    rw [hφ, MulAut.one_apply] at h2
    refine d.u_x₁_u_not_mem_B hb ?_
    have e : d.u * d.x₁ b * d.u = d.x₁ b := by
      calc d.u * d.x₁ b * d.u = d.u * (d.x₁ b * d.u * (d.x₁ b)⁻¹) * d.x₁ b := by group
        _ = d.x₁ b := by rw [h2, d.u_mul_self, one_mul]
    rw [e]
    exact d.S_le_B (d.U₁_le_S (d.x₁_mem_U₁ b))
  rw [hb, d.x₁_zero, mul_one, hφ, mul_one]
  exact ⟨n, hn, j, hj, rfl⟩

theorem exists_of_centralizes_V {g : X} {k : ℕ}
    (hV : ∀ y ∈ d.V, (MulAut.conj g * d.φ ^ k) y = y) :
    g ∈ d.D ⊔ d.leviShort ∧ ∀ c : d.Γ₀, c ^ 2 ^ k = c := by
  obtain ⟨n, hn, s, hs, j, hj, rfl⟩ := d.exists_mul_of_mem_normalizer_V
    (d.mem_normalizer_V_of_conj_mul_φ_pow fun y hy => (hV y hy).symm ▸ hy)
  obtain ⟨⟨l, m⟩, rfl, hm⟩ := d.mem_J₁.1 hj
  dsimp only at hm
  subst hm
  have hnsV : n * s ∈ centralizer (d.V : Set X) :=
    mul_mem (d.S_le_centralizer_V (d.D_le_S hn)) (d.leviShort_le_centralizer_V hs)
  have hcoord : ∀ c : d.Γ₀, (l : d.Γ₀) * (l : d.Γ₀) * c ^ 2 ^ k = c := by
    intro c
    have h1 := hV (d.x₆ c) (d.x₆_mem_V c)
    rw [MulAut.mul_apply, d.φ_pow_x₆, MulAut.conj_apply,
      show n * s * d.torus (l, 1) * d.x₆ (c ^ 2 ^ k) * (n * s * d.torus (l, 1))⁻¹ =
        n * s * (d.torus (l, 1) * d.x₆ (c ^ 2 ^ k) * (d.torus (l, 1))⁻¹) * (n * s)⁻¹ by group,
      d.torus_conj_x₆_of_snd_eq_one,
      ← mem_centralizer_iff.1 hnsV _ (d.x₆_mem_V _), mul_inv_cancel_right] at h1
    exact d.x₆_injective h1
  have hl : l = 1 := d.units₀_eq_one_of_sq (Units.ext (by simpa [sq] using hcoord 1))
  subst hl
  refine ⟨?_, fun c => by simpa using hcoord c⟩
  rw [show d.torus (1, 1) = 1 from map_one d.torus, mul_one]
  exact mul_mem (mem_sup_left hn) (mem_sup_right hs)

theorem φ_pow_apply_of_mem_J₁ {k : ℕ} (hk : ∀ c : d.Γ₀, c ^ 2 ^ k = c) {j : X}
    (hj : j ∈ d.J₁) : (d.φ ^ k) j = j := by
  obtain ⟨⟨l, m⟩, rfl, hm⟩ := d.mem_J₁.1 hj
  dsimp only at hm
  subst hm
  rw [d.φ_pow_torus]
  congr 1
  refine Prod.ext (Units.ext ?_) (by simp)
  simpa using hk l

theorem eq_one_of_mul_pow_eq_one {n j : X} (hn : n ∈ d.D) (hj : j ∈ d.J₁) {m : ℕ}
    (h : (n * j) ^ 2 ^ m = 1) : j = 1 := by
  have hpow : ∀ e : ℕ, ∃ n' ∈ d.D, (n * j) ^ e = n' * j ^ e := by
    intro e
    induction e with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ e ih =>
      obtain ⟨n', hn', he⟩ := ih
      have hjD : j ^ e ∈ normalizer (d.D : Set X) := pow_mem (d.J₁_le_normalizer_D hj) e
      refine ⟨n' * (j ^ e * n * (j ^ e)⁻¹), mul_mem hn' ((mem_normalizer_iff.1 hjD n).1 hn), ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨n', hn', he⟩ := hpow (2 ^ m)
  rw [h] at he
  have hDJ : d.D ⊓ d.J₁ = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left _ le_sup_right).trans d.yamada_three_eight_four.2.2.2.2.le)
  have hjD : j ^ 2 ^ m ∈ d.D ⊓ d.J₁ := by
    refine Subgroup.mem_inf.2 ⟨?_, pow_mem hj _⟩
    rw [eq_inv_of_mul_eq_one_right he.symm]
    exact inv_mem hn'
  rw [hDJ, mem_bot] at hjD
  obtain ⟨⟨l, m'⟩, rfl, hm⟩ := d.mem_J₁.1 hj
  dsimp only at hm
  subst hm
  rw [← map_pow] at hjD
  have h1 := d.torus_injective (hjD.trans (map_one d.torus).symm)
  have hl : ((l : d.Γ₀) : d.Γ) ^ 2 ^ m = 1 ^ 2 ^ m := by
    have := congrArg (fun p => (((p.1 : (d.Γ₀)ˣ) : d.Γ₀) : d.Γ)) h1
    simpa using this
  have hl' : l = 1 := Units.ext (Subtype.ext (d.pow_two_pow_injective m hl))
  rw [hl']
  exact map_one d.torus

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
