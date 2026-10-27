module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open SimpleGraph

section Dist

variable {X V : Type*} [Group X] [MulAction X V] {Δ : SimpleGraph V}

private theorem edist_map_le {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    (a b : V) : H.edist (f a) (f b) ≤ G.edist a b := by
  by_cases hr : G.Reachable a b
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    rw [← hp, ← SimpleGraph.Walk.length_map f p]
    exact SimpleGraph.edist_le _
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

private theorem edist_iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (a b : V) : H.edist (f a) (f b) = G.edist a b := by
  refine le_antisymm (edist_map_le f.toHom a b) ?_
  simpa using edist_map_le f.symm.toHom (f a) (f b)

private theorem dist_iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (a b : V) : H.dist (f a) (f b) = G.dist a b := by
  rw [SimpleGraph.dist, SimpleGraph.dist, edist_iso]

@[expose] def smulIso (hΔ : ∀ (g : X) (x y : V), Δ.Adj (g • x) (g • y) ↔ Δ.Adj x y) (g : X) :
    Δ ≃g Δ where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := hΔ g _ _

variable (hΔ : ∀ (g : X) (x y : V), Δ.Adj (g • x) (g • y) ↔ Δ.Adj x y)
include hΔ

theorem smulIso_apply (g : X) (x : V) : smulIso hΔ g x = g • x := rfl

theorem reachable_smul_iff (g : X) {x y : V} :
    Δ.Reachable (g • x) (g • y) ↔ Δ.Reachable x y :=
  (smulIso hΔ g).reachable_iff

theorem edist_smul (g : X) (x y : V) : Δ.edist (g • x) (g • y) = Δ.edist x y :=
  edist_iso (smulIso hΔ g) x y

theorem dist_smul (g : X) (x y : V) : Δ.dist (g • x) (g • y) = Δ.dist x y :=
  dist_iso (smulIso hΔ g) x y

theorem dist_smul_left (g : X) (x y : V) : Δ.dist (g • x) y = Δ.dist x (g⁻¹ • y) := by
  simpa using (dist_smul hΔ g⁻¹ (g • x) y).symm

theorem dist_smul_right (g : X) (x y : V) : Δ.dist x (g • y) = Δ.dist (g⁻¹ • x) y := by
  simpa using (dist_smul hΔ g⁻¹ x (g • y)).symm

theorem adj_smul_left_iff (g : X) (x y : V) : Δ.Adj (g • x) y ↔ Δ.Adj x (g⁻¹ • y) := by
  simpa using (hΔ g⁻¹ (g • x) y).symm

theorem dist_smul_of_smul_eq {a : V} {k : X} (hk : k • a = a) (v : V) :
    Δ.dist a (k • v) = Δ.dist a v := by
  simpa [hk] using dist_smul hΔ k a v

theorem dist_le_of_base [MulAction.IsPretransitive X V] (a₀ : V) {d : ℕ}
    (h : ∀ v, Δ.dist a₀ v ≤ d) (x y : V) : Δ.dist x y ≤ d := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X a₀ x
  rw [dist_smul_left hΔ]
  exact h _

omit hΔ in
theorem ronanSet_smul (hΔ : ∀ (g : X) (x y : V), Δ.Adj (g • x) (g • y) ↔ Δ.Adj x y) (g : X)
    (a b : V) (n : ℕ) :
    {c | Δ.Adj (g • a) c ∧ Δ.dist c (g • b) = n} =
      (g • ·) '' {c | Δ.Adj a c ∧ Δ.dist c b = n} := by
  ext c
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨g⁻¹ • c, ⟨?_, ?_⟩, smul_inv_smul g c⟩
    · rw [← hΔ g, smul_inv_smul]
      exact h1
    · rw [← dist_smul hΔ g, smul_inv_smul]
      exact h2
  · rintro ⟨c', ⟨h1, h2⟩, rfl⟩
    exact ⟨(hΔ g _ _).2 h1, by rw [dist_smul hΔ]; exact h2⟩

omit hΔ in
theorem preconnected_induce_image (hΔ : ∀ (g : X) (x y : V), Δ.Adj (g • x) (g • y) ↔ Δ.Adj x y)
    (g : X) {S : Set V} (h : (Δ.induce S).Preconnected) :
    (Δ.induce ((g • ·) '' S)).Preconnected := by
  let f : Δ.induce S →g Δ.induce ((g • ·) '' S) :=
    { toFun := fun x => ⟨g • x.1, x.1, x.2, rfl⟩
      map_rel' := fun h => (hΔ g _ _).2 h }
  rintro ⟨_, u, hu, rfl⟩ ⟨_, w, hw, rfl⟩
  exact (h ⟨u, hu⟩ ⟨w, hw⟩).map f

end Dist

section Level

variable {V : Type*} {Δ : SimpleGraph V}

theorem reachable_and_dist_le_of_level {a : V} {f : V → ℕ} (h0 : f a = 0)
    (huniq : ∀ b, f b = 0 → b = a) (hdown : ∀ c k, f c = k + 1 → ∃ n, Δ.Adj c n ∧ f n = k) :
    ∀ c, Δ.Reachable a c ∧ Δ.dist a c ≤ f c := by
  have key : ∀ m : ℕ, ∀ c, f c = m → Δ.Reachable a c ∧ Δ.dist a c ≤ m := by
    intro m
    induction m with
    | zero =>
      intro c hc
      obtain rfl := huniq c hc
      exact ⟨Reachable.refl _, by simp⟩
    | succ k ih =>
      intro c hc
      obtain ⟨n, hcn, hn⟩ := hdown c k hc
      obtain ⟨hr, hd⟩ := ih n hn
      refine ⟨hr.trans hcn.symm.reachable, ?_⟩
      obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
      calc Δ.dist a c ≤ (p.concat hcn.symm).length := dist_le _
        _ = Δ.dist a n + 1 := by rw [Walk.length_concat, hp]
        _ ≤ k + 1 := by omega
  exact fun c => key _ c rfl

theorem level_le_of_walk {f : V → ℕ} (hlip : ∀ u v, Δ.Adj u v → f v ≤ f u + 1) {u v : V}
    (p : Δ.Walk u v) : f v ≤ f u + p.length := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have := hlip x y h
    rw [Walk.length_cons]
    omega

theorem dist_eq_of_level {a : V} {f : V → ℕ} (h0 : f a = 0) (huniq : ∀ b, f b = 0 → b = a)
    (hdown : ∀ c k, f c = k + 1 → ∃ n, Δ.Adj c n ∧ f n = k)
    (hlip : ∀ u v, Δ.Adj u v → f v ≤ f u + 1) :
    (∀ c, Δ.Reachable a c) ∧ ∀ c, Δ.dist a c = f c := by
  have hb := reachable_and_dist_le_of_level h0 huniq hdown
  refine ⟨fun c => (hb c).1, fun c => le_antisymm (hb c).2 ?_⟩
  obtain ⟨p, hp⟩ := (hb c).1.exists_walk_length_eq_dist
  have := level_le_of_walk hlip p
  omega

theorem connected_of_level {a : V} {f : V → ℕ} (h0 : f a = 0) (huniq : ∀ b, f b = 0 → b = a)
    (hdown : ∀ c k, f c = k + 1 → ∃ n, Δ.Adj c n ∧ f n = k)
    (hlip : ∀ u v, Δ.Adj u v → f v ≤ f u + 1) : Δ.Connected := by
  have h := (dist_eq_of_level h0 huniq hdown hlip).1
  haveI : Nonempty V := ⟨a⟩
  exact ⟨fun u w => (h u).symm.trans (h w)⟩

theorem edist_eq_of_level {a : V} {f : V → ℕ} (h0 : f a = 0) (huniq : ∀ b, f b = 0 → b = a)
    (hdown : ∀ c k, f c = k + 1 → ∃ n, Δ.Adj c n ∧ f n = k)
    (hlip : ∀ u v, Δ.Adj u v → f v ≤ f u + 1) (c : V) : Δ.edist a c = f c := by
  obtain ⟨hr, hd⟩ := dist_eq_of_level h0 huniq hdown hlip
  rw [← (hr c).coe_dist_eq_edist, hd c]

end Level

section Tree

variable {V : Type*} {Δ : SimpleGraph V}

theorem preconnected_induce_of_descent {S : Set V} {r : V} (hr : r ∈ S) (μ : V → ℕ)
    (h : ∀ v ∈ S, v = r ∨ ∃ p ∈ S, Δ.Adj v p ∧ μ p < μ v) :
    (Δ.induce S).Preconnected := by
  have key : ∀ n : ℕ, ∀ (v : V) (hv : v ∈ S), μ v = n →
      (Δ.induce S).Reachable ⟨v, hv⟩ ⟨r, hr⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv hμ
      rcases h v hv with rfl | ⟨p, hp, hvp, hlt⟩
      · exact Reachable.refl _
      · have h1 : (Δ.induce S).Adj ⟨v, hv⟩ ⟨p, hp⟩ := hvp
        exact h1.reachable.trans (ih (μ p) (hμ ▸ hlt) p hp rfl)
  intro u w
  exact (key _ u.1 u.2 rfl).trans (key _ w.1 w.2 rfl).symm

theorem preconnected_induce_of_parent {S : Set V} {r : V} (hr : r ∈ S) (par : V → V)
    (dep : V → ℕ)
    (h : ∀ v ∈ S, v ≠ r → par v ∈ S ∧ Δ.Adj v (par v) ∧ dep (par v) < dep v) :
    (Δ.induce S).Preconnected :=
  preconnected_induce_of_descent hr dep fun v hv => by
    by_cases e : v = r
    · exact Or.inl e
    · exact Or.inr ⟨par v, (h v hv e).1, (h v hv e).2.1, (h v hv e).2.2⟩

theorem preconnected_induce_of_nodes {S : Set V} (ns : List V) (ps : ℕ → ℕ)
    (hns : ∀ v ∈ ns, v ∈ S) (hS : ∀ v ∈ S, v ∈ ns)
    (hps : ∀ t u, 0 < t → ns[t]? = some u → ps t < t ∧ ∃ p, ns[ps t]? = some p ∧ Δ.Adj u p) :
    (Δ.induce S).Preconnected := by
  rcases ns with _ | ⟨r, ns'⟩
  · intro u
    exact absurd (hS u.1 u.2) (by simp)
  · have hr : r ∈ S := hns r (by simp)
    have key : ∀ t : ℕ, ∀ (u : V) (hu : u ∈ S), (r :: ns')[t]? = some u →
        (Δ.induce S).Reachable ⟨u, hu⟩ ⟨r, hr⟩ := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        intro u hu hnt
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hnt
          subst hnt
          exact Reachable.refl _
        · obtain ⟨hlt, p, hp, hadj⟩ := hps t u ht hnt
          have hpS : p ∈ S := hns p (List.mem_of_getElem? hp)
          have h1 : (Δ.induce S).Adj ⟨u, hu⟩ ⟨p, hpS⟩ := hadj
          exact h1.reachable.trans (ih (ps t) hlt p hpS hp)
    intro u w
    obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 (hS u.1 u.2)
    obtain ⟨t', ht'⟩ := List.mem_iff_getElem?.1 (hS w.1 w.2)
    exact (key t u.1 u.2 ht).trans (key t' w.1 w.2 ht').symm

end Tree

section Forest

theorem exists_mem_smul_eq_of_forest {X V : Type*} [Group X] [MulAction X V] {S : Set X}
    {ι : Type*} [Membership V ι] {R : ι} (par : V → V) (dep : V → ℕ)
    (h : ∀ v, v ∈ R ∨ (dep (par v) < dep v ∧ ∃ s ∈ S, s • par v = v)) :
    ∀ v, ∃ r ∈ R, ∃ k ∈ Subgroup.closure S, k • r = v := by
  have key : ∀ n, ∀ v, dep v = n → ∃ r ∈ R, ∃ k ∈ Subgroup.closure S, k • r = v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      rcases h v with hvR | ⟨hlt, s, hs, hsv⟩
      · exact ⟨v, hvR, 1, Subgroup.one_mem _, one_smul _ v⟩
      · have hlt' : dep (par v) < n := hv ▸ hlt
        obtain ⟨r, hrR, k', hk', hk'r⟩ := ih (dep (par v)) hlt' (par v) rfl
        exact ⟨r, hrR, s * k', Subgroup.mul_mem _ (Subgroup.subset_closure hs) hk',
          by rw [mul_smul, hk'r, hsv]⟩
  intro v
  exact key (dep v) v rfl

theorem smul_eq_of_mem_closure {X V : Type*} [Group X] [MulAction X V] {S : Set X} {a : V}
    (h : ∀ s ∈ S, s • a = a) : ∀ k ∈ Subgroup.closure S, k • a = a := by
  intro k hk
  exact Subgroup.closure_induction (fun x hx => h x hx) (one_smul _ _)
    (fun x y hx hy ihx ihy => by rw [mul_smul, ihy, ihx])
    (fun x hx ih => by rw [inv_smul_eq_iff, ih]) hk

theorem smul_apply_eq_of_mem_closure {X V β : Type*} [Group X] [MulAction X V] {S : Set X}
    {F : V → β} (h : ∀ s ∈ S, ∀ v, F (s • v) = F v) :
    ∀ k ∈ Subgroup.closure S, ∀ v, F (k • v) = F v := by
  intro k hk
  exact Subgroup.closure_induction (fun x hx => h x hx) (fun v => by rw [one_smul])
    (fun x y hx hy ihx ihy v => by rw [mul_smul, ihx, ihy])
    (fun x hx ih v => by rw [← ih (x⁻¹ • v), smul_inv_smul]) hk

end Forest

section Reps

variable {X V : Type*} [Group X] [MulAction X V]

theorem forall_imp_of_forall_rep [MulAction.IsPretransitive X V] {W : Type*} [MulAction X W]
    {a₀ : V} (K : Subgroup X) (hK : ∀ k ∈ K, k • a₀ = a₀) {H C : V → W → Prop}
    (hH : ∀ (g : X) (a : V) (w : W), H (g • a) (g • w) ↔ H a w)
    (hC : ∀ (g : X) (a : V) (w : W), C a w → C (g • a) (g • w)) {ι : Type*} [Membership W ι]
    {R : ι} (hR : ∀ w, H a₀ w → ∃ r ∈ R, ∃ k ∈ K, k • r = w)
    (h : ∀ r ∈ R, H a₀ r → C a₀ r) : ∀ (a : V) (w : W), H a w → C a w := by
  intro a w hw
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq X a₀ a
  have h1 : H a₀ (x⁻¹ • w) := by
    have := (hH x⁻¹ (x • a₀) w).2 hw
    rwa [inv_smul_smul] at this
  obtain ⟨r, hr, k, hk, hkr⟩ := hR _ h1
  have h2 : H a₀ r := (hH k a₀ r).1 (by rw [hK k hk, hkr]; exact h1)
  have h3 : C a₀ (x⁻¹ • w) := by
    have := hC k a₀ r (h r hr h2)
    rwa [hK k hk, hkr] at this
  have h4 := hC x a₀ _ h3
  rwa [smul_inv_smul] at h4

variable {Δ : SimpleGraph V} (hΔ : ∀ (g : X) (x y : V), Δ.Adj (g • x) (g • y) ↔ Δ.Adj x y)
include hΔ

theorem dist_eq_of_level_of_reps {a : V} {f : V → ℕ} (K : Subgroup X)
    (hK : ∀ k ∈ K, k • a = a) (hfK : ∀ k ∈ K, ∀ v, f (k • v) = f v) {ι : Type*}
    [Membership V ι] {R : ι} (hR : ∀ v, ∃ r ∈ R, ∃ k ∈ K, k • r = v) (h0 : f a = 0)
    (huniq : ∀ r ∈ R, f r = 0 → r = a)
    (hdown : ∀ r ∈ R, ∀ k, f r = k + 1 → ∃ n, Δ.Adj r n ∧ f n = k)
    (hlip : ∀ r ∈ R, ∀ v, Δ.Adj r v → f v ≤ f r + 1) :
    (∀ c, Δ.Reachable a c) ∧ ∀ c, Δ.dist a c = f c := by
  refine dist_eq_of_level h0 ?_ ?_ ?_
  · intro b hb
    obtain ⟨r, hr, k, hk, rfl⟩ := hR b
    rw [hfK k hk] at hb
    rw [huniq r hr hb]
    exact hK k hk
  · intro c m hc
    obtain ⟨r, hr, k, hk, rfl⟩ := hR c
    rw [hfK k hk] at hc
    obtain ⟨n, hn, hfn⟩ := hdown r hr m hc
    exact ⟨k • n, (hΔ k _ _).2 hn, by rw [hfK k hk, hfn]⟩
  · intro u v huv
    obtain ⟨r, hr, k, hk, rfl⟩ := hR u
    have h1 : Δ.Adj r (k⁻¹ • v) := by
      have := (hΔ k⁻¹ _ _).2 huv
      rwa [inv_smul_smul] at this
    have h2 := hlip r hr _ h1
    have h3 : f v = f (k⁻¹ • v) := by
      have := hfK k hk (k⁻¹ • v)
      rwa [smul_inv_smul] at this
    rw [hfK k hk]
    omega

theorem connected_of_level_of_reps {a : V} {f : V → ℕ} (K : Subgroup X)
    (hK : ∀ k ∈ K, k • a = a) (hfK : ∀ k ∈ K, ∀ v, f (k • v) = f v) {ι : Type*}
    [Membership V ι] {R : ι} (hR : ∀ v, ∃ r ∈ R, ∃ k ∈ K, k • r = v) (h0 : f a = 0)
    (huniq : ∀ r ∈ R, f r = 0 → r = a)
    (hdown : ∀ r ∈ R, ∀ k, f r = k + 1 → ∃ n, Δ.Adj r n ∧ f n = k)
    (hlip : ∀ r ∈ R, ∀ v, Δ.Adj r v → f v ≤ f r + 1) : Δ.Connected := by
  have h := (dist_eq_of_level_of_reps hΔ K hK hfK hR h0 huniq hdown hlip).1
  haveI : Nonempty V := ⟨a⟩
  exact ⟨fun u w => (h u).symm.trans (h w)⟩

private theorem preconnected_ronanSet_smul (x : X) (i : ℕ) (a b : V)
    (h : (Δ.induce {c | Δ.Adj a c ∧ Δ.dist c b = i - 1}).Preconnected) :
    (Δ.induce {c | Δ.Adj (x • a) c ∧ Δ.dist c (x • b) = i - 1}).Preconnected := by
  rw [ronanSet_smul hΔ]
  exact preconnected_induce_image hΔ x h

private theorem exists_ronanII_smul (x : X) (i : ℕ) (a b g : V)
    (h : ∃ c c', Δ.Adj a c ∧ Δ.dist c b = i - 1 ∧ Δ.Adj a c' ∧ Δ.dist c' g = i - 1 ∧
      (c = c' ∨ Δ.Adj c c')) :
    ∃ c c', Δ.Adj (x • a) c ∧ Δ.dist c (x • b) = i - 1 ∧ Δ.Adj (x • a) c' ∧
      Δ.dist c' (x • g) = i - 1 ∧ (c = c' ∨ Δ.Adj c c') := by
  obtain ⟨c, c', h1, h2, h3, h4, h5⟩ := h
  exact ⟨x • c, x • c', (hΔ x _ _).2 h1, by rw [dist_smul hΔ]; exact h2, (hΔ x _ _).2 h3,
    by rw [dist_smul hΔ]; exact h4, h5.imp (congrArg (x • ·)) ((hΔ x _ _).2)⟩

variable [MulAction.IsPretransitive X V] {a₀ : V} (K : Subgroup X) (hK : ∀ k ∈ K, k • a₀ = a₀)
  {i : ℕ}

include hK

theorem ronan_i_iff_reps {ι : Type*} [Membership V ι] {R : ι}
    (hR : ∀ b, Δ.dist a₀ b = i → ∃ r ∈ R, ∃ k ∈ K, k • r = b) :
    (∀ a b, Δ.dist a b = i →
        (Δ.induce {c | Δ.Adj a c ∧ Δ.dist c b = i - 1}).Preconnected) ↔
      ∀ r ∈ R, Δ.dist a₀ r = i →
        (Δ.induce {c | Δ.Adj a₀ c ∧ Δ.dist c r = i - 1}).Preconnected := by
  refine ⟨fun h r _ => h a₀ r, fun h => ?_⟩
  exact forall_imp_of_forall_rep (W := V) K hK
    (H := fun a b => Δ.dist a b = i)
    (C := fun a b => (Δ.induce {c | Δ.Adj a c ∧ Δ.dist c b = i - 1}).Preconnected)
    (fun g a b => by rw [dist_smul hΔ])
    (fun g a b hab => preconnected_ronanSet_smul hΔ g i a b hab) hR h

theorem ronan_ii_iff_reps {ι : Type*} [Membership V ι] {R : ι}
    (hR : ∀ b, Δ.dist a₀ b = i → ∃ r ∈ R, ∃ k ∈ K, k • r = b) :
    (∀ a b g, Δ.dist a b = i → Δ.dist a g = i → Δ.Adj b g →
        ∃ c c', Δ.Adj a c ∧ Δ.dist c b = i - 1 ∧ Δ.Adj a c' ∧ Δ.dist c' g = i - 1 ∧
          (c = c' ∨ Δ.Adj c c')) ↔
      ∀ r ∈ R, Δ.dist a₀ r = i → ∀ g, Δ.dist a₀ g = i → Δ.Adj r g →
        ∃ c c', Δ.Adj a₀ c ∧ Δ.dist c r = i - 1 ∧ Δ.Adj a₀ c' ∧ Δ.dist c' g = i - 1 ∧
          (c = c' ∨ Δ.Adj c c') := by
  refine ⟨fun h r _ hr g hg hrg => h a₀ r g hr hg hrg, fun h => ?_⟩
  have key := forall_imp_of_forall_rep (W := V) K hK
    (H := fun a b => Δ.dist a b = i)
    (C := fun a b => ∀ g, Δ.dist a g = i → Δ.Adj b g →
      ∃ c c', Δ.Adj a c ∧ Δ.dist c b = i - 1 ∧ Δ.Adj a c' ∧ Δ.dist c' g = i - 1 ∧
        (c = c' ∨ Δ.Adj c c'))
    (fun g a b => by rw [dist_smul hΔ])
    (fun x a b hab g hg hbg => by
      have h1 : Δ.dist a (x⁻¹ • g) = i := by rw [← dist_smul_left hΔ]; exact hg
      have h2 : Δ.Adj b (x⁻¹ • g) := (adj_smul_left_iff hΔ x b g).1 hbg
      have := exists_ronanII_smul hΔ x i a b _ (hab _ h1 h2)
      rwa [smul_inv_smul] at this)
    hR (fun r hr hdr => h r hr hdr)
  exact fun a b g hab hag hbg => key a b hab g hag hbg

theorem ronan_ii_iff_pair_reps {ι : Type*} [Membership (V × V) ι] {R : ι}
    (hR : ∀ b g, Δ.dist a₀ b = i → Δ.dist a₀ g = i → Δ.Adj b g →
      ∃ r ∈ R, ∃ k ∈ K, k • r.1 = b ∧ k • r.2 = g) :
    (∀ a b g, Δ.dist a b = i → Δ.dist a g = i → Δ.Adj b g →
        ∃ c c', Δ.Adj a c ∧ Δ.dist c b = i - 1 ∧ Δ.Adj a c' ∧ Δ.dist c' g = i - 1 ∧
          (c = c' ∨ Δ.Adj c c')) ↔
      ∀ r ∈ R, Δ.dist a₀ r.1 = i → Δ.dist a₀ r.2 = i → Δ.Adj r.1 r.2 →
        ∃ c c', Δ.Adj a₀ c ∧ Δ.dist c r.1 = i - 1 ∧ Δ.Adj a₀ c' ∧ Δ.dist c' r.2 = i - 1 ∧
          (c = c' ∨ Δ.Adj c c') := by
  refine ⟨fun h r _ h1 h2 h3 => h a₀ r.1 r.2 h1 h2 h3, fun h => ?_⟩
  have key := forall_imp_of_forall_rep (W := V × V) K hK
    (H := fun a w => Δ.dist a w.1 = i ∧ Δ.dist a w.2 = i ∧ Δ.Adj w.1 w.2)
    (C := fun a w => ∃ c c', Δ.Adj a c ∧ Δ.dist c w.1 = i - 1 ∧ Δ.Adj a c' ∧
      Δ.dist c' w.2 = i - 1 ∧ (c = c' ∨ Δ.Adj c c'))
    (fun g a w => by simp only [Prod.smul_fst, Prod.smul_snd, dist_smul hΔ, hΔ])
    (fun x a w hw => exists_ronanII_smul hΔ x i a w.1 w.2 hw)
    (fun w hw => by
      obtain ⟨r, hr, k, hk, h1, h2⟩ := hR w.1 w.2 hw.1 hw.2.1 hw.2.2
      exact ⟨r, hr, k, hk, Prod.ext h1 h2⟩)
    (fun r hr hrH => h r hr hrH.1 hrH.2.1 hrH.2.2)
  exact fun a b g hab hag hbg => key a (b, g) ⟨hab, hag, hbg⟩

theorem ronan_ii_of_two_level_reps {ι₁ ι₂ : Type*} [Membership V ι₁] [Membership V ι₂]
    {R : ι₁} {Rg : V → ι₂} {Kr : V → Subgroup X}
    (hR : ∀ b, Δ.dist a₀ b = i → ∃ r ∈ R, ∃ k ∈ K, k • r = b)
    (hKr : ∀ r ∈ R, ∀ k ∈ Kr r, k • a₀ = a₀ ∧ k • r = r)
    (hRg : ∀ r ∈ R, ∀ g, Δ.dist a₀ r = i → Δ.dist a₀ g = i → Δ.Adj r g →
      ∃ s ∈ Rg r, ∃ k ∈ Kr r, k • s = g)
    (h : ∀ r ∈ R, ∀ s ∈ Rg r, Δ.dist a₀ r = i → Δ.dist a₀ s = i → Δ.Adj r s →
      ∃ c c', Δ.Adj a₀ c ∧ Δ.dist c r = i - 1 ∧ Δ.Adj a₀ c' ∧ Δ.dist c' s = i - 1 ∧
        (c = c' ∨ Δ.Adj c c')) :
    ∀ a b g, Δ.dist a b = i → Δ.dist a g = i → Δ.Adj b g →
      ∃ c c', Δ.Adj a c ∧ Δ.dist c b = i - 1 ∧ Δ.Adj a c' ∧ Δ.dist c' g = i - 1 ∧
        (c = c' ∨ Δ.Adj c c') := by
  refine (ronan_ii_iff_pair_reps hΔ (MulAction.stabilizer X a₀) (fun k hk => hk)
    (R := {p | p.1 ∈ R ∧ p.2 ∈ Rg p.1}) ?_).2 ?_
  · intro b g hb hg hbg
    obtain ⟨r, hr, k, hk, rfl⟩ := hR b hb
    have hg' : Δ.dist a₀ (k⁻¹ • g) = i :=
      (dist_smul_of_smul_eq hΔ (inv_smul_eq_iff.2 (hK k hk).symm) g).trans hg
    have hrg : Δ.Adj r (k⁻¹ • g) := (adj_smul_left_iff hΔ k r g).1 hbg
    have hdr : Δ.dist a₀ r = i := (dist_smul_of_smul_eq hΔ (hK k hk) r).symm.trans hb
    obtain ⟨s, hs, k₂, hk₂, hk₂s⟩ := hRg r hr _ hdr hg' hrg
    obtain ⟨hk₂a, hk₂r⟩ := hKr r hr k₂ hk₂
    refine ⟨(r, s), ⟨hr, hs⟩, k * k₂, ?_, ?_, ?_⟩
    · show (k * k₂) • a₀ = a₀
      rw [mul_smul, hk₂a, hK k hk]
    · show (k * k₂) • r = k • r
      rw [mul_smul, hk₂r]
    · show (k * k₂) • s = g
      rw [mul_smul, hk₂s, smul_inv_smul]
  · rintro ⟨r, s⟩ ⟨hr, hs⟩ hdr hds hrs
    exact h r hr s hs hdr hds hrs

end Reps

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
