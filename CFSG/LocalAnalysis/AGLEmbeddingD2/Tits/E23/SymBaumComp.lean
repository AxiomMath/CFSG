module

public import CFSG.CGT.PushingUpLit.BHS5.SymPow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.SymBaumPerm

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Tits.E23

open Equiv CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5

variable {V : Type} [CommGroup V] [Finite V]

structure SymComp (P M E : Subgroup (MulAut V)) (m : ℕ) (θ : ↥E ≃* Perm (Fin m))
    (β : ↥(commV E) →* coreMod m) (i₀ : Fin m) : Prop where
  odd : Odd m
  three : 3 ≤ m
  inv : ∀ x ∈ E, ∀ p ∈ commV E, x p ∈ commV E
  surj : Function.Surjective β
  ker : β.ker = ⊥
  equiv : ∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
    β ⟨(x : MulAut V) p, hp⟩ = coreAct m (θ x) (β p)
  top : commV E ⊔ fixV E = ⊤
  dsw : ∀ B ∈ dInter (Hyp51.offSet P) E, ∃ i j : Fin m, i ≠ j ∧
    ∀ b : ↥E, (b : MulAut V) ∈ B → θ b = 1 ∨ θ b = swap i j
  stab : ∀ x : ↥E, (x : MulAut V) ∈ genD P ⊓ M ↔ θ x i₀ = i₀

theorem SymComp.exists_of_symType {P M E : Subgroup (MulAut V)}
    (h : SymType (genD P ⊓ M) (Hyp51.offSet P) E) :
    ∃ (m : ℕ) (θ : ↥E ≃* Perm (Fin m)) (β : ↥(commV E) →* coreMod m) (i₀ : Fin m),
      SymComp P M E m θ β i₀ := by
  obtain ⟨m, θ, β, hodd, h3, hinv, hsurj, hker, hequiv, htop, hdsw, i₀, hstab⟩ := h
  exact ⟨m, θ, β, i₀, ⟨hodd, h3, hinv, hsurj, hker, hequiv, htop, hdsw, hstab⟩⟩

@[expose] def Induces {E : Subgroup (MulAut V)} {m : ℕ} (θ : ↥E ≃* Perm (Fin m)) (n : MulAut V)
    (π : Perm (Fin m)) : Prop :=
  ∀ e e' : ↥E, (e' : MulAut V) = n * e * n⁻¹ → θ e' = π * θ e * π⁻¹

section Induces

variable {E : Subgroup (MulAut V)} {m : ℕ} {θ : ↥E ≃* Perm (Fin m)}

omit [Finite V] in
theorem induces_one : Induces θ 1 1 := by
  intro e e' he'
  have : e' = e := Subtype.ext (by simpa using he')
  rw [this]
  group

omit [Finite V] in
theorem induces_mul {n₁ n₂ : MulAut V} {π₁ π₂ : Perm (Fin m)}
    (hn₂ : n₂ ∈ Subgroup.normalizer (E : Set (MulAut V))) (h₁ : Induces θ n₁ π₁)
    (h₂ : Induces θ n₂ π₂) : Induces θ (n₁ * n₂) (π₁ * π₂) := by
  intro e e' he'
  set e₂ : ↥E := ⟨n₂ * e * n₂⁻¹, (Subgroup.mem_normalizer_iff.1 hn₂ e).1 e.2⟩ with he₂
  have h2 : θ e₂ = π₂ * θ e * π₂⁻¹ := h₂ e e₂ rfl
  have h1 : θ e' = π₁ * θ e₂ * π₁⁻¹ := by
    refine h₁ e₂ e' ?_
    show (e' : MulAut V) = n₁ * (n₂ * e * n₂⁻¹) * n₁⁻¹
    rw [he']
    group
  rw [h1, h2]
  group

omit [Finite V] in
theorem induces_inv {n : MulAut V} {π : Perm (Fin m)} (h : Induces θ n π) :
    Induces θ n⁻¹ π⁻¹ := by
  intro e e' he'
  have h1 : θ e = π * θ e' * π⁻¹ := by
    refine h e' e ?_
    rw [he']
    group
  rw [h1]
  group

end Induces

theorem mem_commV_of_mem_normalizer {E : Subgroup (MulAut V)} {n : MulAut V}
    (hn : n ∈ Subgroup.normalizer (E : Set (MulAut V))) {w : V} (hw : w ∈ commV E) :
    n w ∈ commV E :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hn hw

section Component

variable {P T M : Subgroup (MulAut V)} {ℰ : Set (Subgroup (MulAut V))}
  {E : Subgroup (MulAut V)} {m : ℕ} {θ : ↥E ≃* Perm (Fin m)} {β : ↥(commV E) →* coreMod m}
  {i₀ : Fin m}

theorem SymComp.fix_of_mem_T (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M)
    (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) {x : ↥E} (hx : (x : MulAut V) ∈ T) : θ x i₀ = i₀ :=
  (hc.stab x).1 ⟨hF.le_genD hE x.2, h.minpar.le_M hx⟩

theorem SymComp.stab_M (hc : SymComp P M E m θ β i₀) (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ)
    (x : ↥E) : (x : MulAut V) ∈ M ↔ θ x i₀ = i₀ := by
  rw [← hc.stab]
  exact ⟨fun hx => ⟨hF.le_genD hE x.2, hx⟩, fun hx => hx.2⟩

theorem SymComp.exists_induces (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M)
    (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) {n : MulAut V} (hnT : n ∈ T)
    (hnN : n ∈ Subgroup.normalizer (E : Set (MulAut V))) :
    ∃ π : Perm (Fin m), π i₀ = i₀ ∧ Induces θ n π := by
  obtain ⟨R, -, hRfix, hR⟩ := exists_stab_pGroup h.minpar.syl.2.1 h.minpar.le_M hc.three θ i₀
    (hc.stab_M hF hE)
  obtain ⟨π, hπR, hπ⟩ := hR n hnT hnN
  exact ⟨π, hRfix π hπR, hπ⟩

theorem SymComp.exists_induces_move (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M)
    (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) (hV : ∀ v : V, v ^ 2 = 1) {a b : Fin m}
    (ha : a ≠ i₀) (hb : b ≠ i₀) :
    ∃ n ∈ T, n ∈ Subgroup.normalizer (E : Set (MulAut V)) ∧
      ∃ π : Perm (Fin m), π i₀ = i₀ ∧ π a = b ∧ Induces θ n π := by
  classical
  let R' : Subgroup (Perm (Fin m)) :=
    { carrier := {π | π i₀ = i₀ ∧ ∃ n ∈ T, n ∈ Subgroup.normalizer (E : Set (MulAut V)) ∧
        Induces θ n π}
      one_mem' := ⟨rfl, 1, T.one_mem, Subgroup.one_mem _, induces_one⟩
      mul_mem' := by
        rintro π₁ π₂ ⟨hπ₁, n₁, hn₁T, hn₁N, hn₁⟩ ⟨hπ₂, n₂, hn₂T, hn₂N, hn₂⟩
        refine ⟨by simp [Equiv.Perm.mul_apply, hπ₂, hπ₁], n₁ * n₂, T.mul_mem hn₁T hn₂T,
          Subgroup.mul_mem _ hn₁N hn₂N, induces_mul hn₂N hn₁ hn₂⟩
      inv_mem' := by
        rintro π ⟨hπ, n, hnT, hnN, hn⟩
        exact ⟨Equiv.Perm.inv_eq_iff_eq.2 hπ.symm, n⁻¹, T.inv_mem hnT, Subgroup.inv_mem _ hnN,
          induces_inv hn⟩ }
  have hOstab : ∀ π ∈ R', π ∈ BHSSym.setStab (MulAction.orbit R' a) := by
    intro π hπ x
    set g : R' := ⟨π, hπ⟩
    have hgx : g • x = π x := rfl
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hgx] at hx
      have := MulAction.mem_orbit_of_mem_orbit g⁻¹ hx
      rwa [inv_smul_smul] at this
    · rw [← hgx]
      exact MulAction.mem_orbit_of_mem_orbit g hx
  have hi₀O : i₀ ∉ MulAction.orbit R' a := by
    rintro ⟨g, hg⟩
    apply ha
    have h1 : (g : Perm (Fin m)) a = i₀ := hg
    have h2 : (g : Perm (Fin m)) i₀ = i₀ := g.2.1
    exact (g : Perm (Fin m)).injective (h1.trans h2.symm)
  have hcov := orbit_eq_of_sym h.minpar (fun E' hE' => hF.le_P h hV hE') hF.conj_mem hF.comm hE
    (hF.indep E hE) θ i₀ (hc.stab_M hF hE) hi₀O (MulAction.mem_orbit_self a)
    fun n hnT hnN => by
      obtain ⟨π, hπ0, hπ⟩ := hc.exists_induces h hF hE hnT hnN
      exact ⟨π, hOstab π ⟨hπ0, n, hnT, hnN, hπ⟩, hπ⟩
  obtain ⟨g, hg⟩ := hcov b hb
  obtain ⟨hg0, n, hnT, hnN, hn⟩ := g.2
  exact ⟨n, hnT, hnN, g, hg0, hg, hn⟩

theorem eq_of_swap_of_mem_T (h : Hyp51 P T M) {c d₁ d₂ : Fin m} (e₁ e₂ : ↥E)
    (h₁ : (e₁ : MulAut V) ∈ T) (h₂ : (e₂ : MulAut V) ∈ T) (hc₁ : c ≠ d₁) (hc₂ : c ≠ d₂)
    (he₁ : θ e₁ = swap c d₁) (he₂ : θ e₂ = swap c d₂) : d₁ = d₂ := by
  set Q : Subgroup (Perm (Fin m)) := (T.subgroupOf E).map θ.toMonoidHom with hQ
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨g, hg⟩
    obtain ⟨e, he, rfl⟩ := hg
    obtain ⟨k, hk⟩ := h.minpar.syl.2.1 ⟨(e : MulAut V), Subgroup.mem_subgroupOf.1 he⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : (e : MulAut V) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hek : e ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    simp [← map_pow, hek]
  exact eq_of_swap_mem_of_isPGroup hQ2 hc₁ hc₂ (he₁ ▸ ⟨e₁, Subgroup.mem_subgroupOf.2 h₁, rfl⟩)
    (he₂ ▸ ⟨e₂, Subgroup.mem_subgroupOf.2 h₂, rfl⟩)

variable {X : Subgroup (MulAut V)}

theorem SymComp.exists_swap_mem_X (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M)
    (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ)
    (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X) :
    ∃ (e : ↥E) (a b : Fin m), (e : MulAut V) ∈ X ∧ a ≠ b ∧ θ e = swap a b := by
  obtain ⟨B₀, hB₀, hB₀X⟩ := hX₀
  obtain ⟨E₀, hE₀, hB₀E₀⟩ := hF.cover B₀ hB₀
  obtain ⟨t, htT, htE⟩ := hF.trans E₀ hE₀ E hE
  have hB₁D : conjSub t B₀ ∈ Hyp51.offSet P := hB₀.conj (h.minpar.T_le htT)
  have hB₁E : conjSub t B₀ ≤ E := htE ▸ conjSub_mono t hB₀E₀
  have hB₁X : conjSub t B₀ ≤ X := by
    intro z hz
    rw [mem_conjSub_iff] at hz
    have h2 := (Subgroup.mem_normalizer_iff.1 (hTX htT) (t⁻¹ * z * t)).1 (hB₀X hz)
    simpa [mul_assoc] using h2
  obtain ⟨i, j, hij, hB⟩ := hc.dsw (conjSub t B₀) ⟨hB₁D, hB₁E⟩
  have hne : conjSub t B₀ ≠ ⊥ := (h.hyp43 hV).ne_bot _ hB₁D
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  set e : ↥E := ⟨(b : MulAut V), hB₁E b.2⟩ with he
  refine ⟨e, i, j, hB₁X b.2, hij, ?_⟩
  rcases hB e b.2 with h1 | h1
  · exfalso
    apply hb1
    have : e = 1 := θ.injective (h1.trans (map_one θ).symm)
    exact Subtype.ext (by have := congrArg Subtype.val this; simpa [he] using this)
  · exact h1

theorem SymComp.swap_mem_X (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M)
    (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) (hXT : X ≤ T)
    (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X) {x : ↥E} (hxT : (x : MulAut V) ∈ T) {c d : Fin m}
    (hcd : c ≠ d) (hx : θ x = swap c d) : (x : MulAut V) ∈ X := by
  obtain ⟨e, a, b, heX, hab, he⟩ := hc.exists_swap_mem_X h hV hF hE hTX hX₀
  have hai : a ≠ i₀ := by
    intro h0
    have := hc.fix_of_mem_T h hF hE (hXT heX)
    rw [he, h0, swap_apply_left] at this
    exact hab (h0.trans this.symm)
  have hci : c ≠ i₀ := by
    intro h0
    have := hc.fix_of_mem_T h hF hE hxT
    rw [hx, h0, swap_apply_left] at this
    exact hcd (h0.trans this.symm)
  obtain ⟨n, hnT, hnN, π, hπ0, hπa, hπ⟩ := hc.exists_induces_move h hF hE hV hai hci
  set e' : ↥E := ⟨n * e * n⁻¹, (Subgroup.mem_normalizer_iff.1 hnN e).1 e.2⟩ with he'
  have he'X : (e' : MulAut V) ∈ X := (Subgroup.mem_normalizer_iff.1 (hTX hnT) e).1 heX
  have hθe' : θ e' = swap c (π b) := by
    rw [hπ e e' rfl, he, ← swap_apply_apply, hπa]
  have hπb : c ≠ π b := by
    intro h2
    exact hab (π.injective (hπa.trans h2))
  have hbd : π b = d := eq_of_swap_of_mem_T h e' x (hXT he'X) hxT hπb hcd hθe' hx
  have : e' = x := θ.injective (by rw [hθe', hbd, hx])
  rw [← this]
  exact he'X

theorem SymComp.exists_swap_at (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M)
    (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) (hXT : X ≤ T)
    (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X) {c : Fin m} (hc0 : c ≠ i₀) :
    ∃ d, d ≠ c ∧ ∃ y : ↥E, (y : MulAut V) ∈ X ∧ θ y = swap c d := by
  obtain ⟨e, a, b, heX, hab, he⟩ := hc.exists_swap_mem_X h hV hF hE hTX hX₀
  have hai : a ≠ i₀ := by
    intro h0
    have := hc.fix_of_mem_T h hF hE (hXT heX)
    rw [he, h0, swap_apply_left] at this
    exact hab (h0.trans this.symm)
  obtain ⟨n, hnT, hnN, π, hπ0, hπa, hπ⟩ := hc.exists_induces_move h hF hE hV hai hc0
  set e' : ↥E := ⟨n * e * n⁻¹, (Subgroup.mem_normalizer_iff.1 hnN e).1 e.2⟩ with he'
  have he'X : (e' : MulAut V) ∈ X := (Subgroup.mem_normalizer_iff.1 (hTX hnT) e).1 heX
  have hθe' : θ e' = swap c (π b) := by
    rw [hπ e e' rfl, he, ← swap_apply_apply, hπa]
  refine ⟨π b, fun h2 => hab (π.injective (hπa.trans h2.symm)), e', he'X, hθe'⟩

@[expose] def swapSub (X E : Subgroup (MulAut V)) {m : ℕ} (θ : ↥E ≃* Perm (Fin m)) :
    Subgroup (Perm (Fin m)) :=
  (X.subgroupOf E).map θ.toMonoidHom

theorem mem_swapSub {X E : Subgroup (MulAut V)} {m : ℕ} {θ : ↥E ≃* Perm (Fin m)}
    {g : Perm (Fin m)} :
    g ∈ swapSub X E θ ↔ ∃ y : ↥E, (y : MulAut V) ∈ X ∧ θ y = g := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.1 hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.2 hy, rfl⟩

theorem swapSub_match (h : Hyp51 P T M) (hXT : X ≤ T) :
    ∀ a b c : Fin m, a ≠ b → a ≠ c → swap a b ∈ swapSub X E θ → swap a c ∈ swapSub X E θ →
      b = c := by
  intro a b c hab hac h1 h2
  obtain ⟨y₁, hy₁, hy₁'⟩ := mem_swapSub.1 h1
  obtain ⟨y₂, hy₂, hy₂'⟩ := mem_swapSub.1 h2
  exact eq_of_swap_of_mem_T h y₁ y₂ (hXT hy₁) (hXT hy₂) hab hac hy₁' hy₂'

theorem SymComp.swapSub_fix (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M)
    (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) (hXT : X ≤ T) :
    ∀ z ∈ swapSub X E θ, z i₀ = i₀ := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_swapSub.1 hz
  exact hc.fix_of_mem_T h hF hE (hXT hy)

theorem fix_of_closure {E : Subgroup (MulAut V)} {m : ℕ} (θ : ↥E ≃* Perm (Fin m))
    (u : ↥(coreMod m)) (S : Set ↥E) (hS : ∀ e ∈ S, coreAct m (θ e) u = u) {g : ↥E}
    (hg : g ∈ Subgroup.closure S) : coreAct m (θ g) u = u := by
  let Stab : Subgroup ↥E :=
    { carrier := {g | coreAct m (θ g) u = u}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        show coreAct m (θ (a * b)) u = u
        rw [map_mul, map_mul, MulAut.mul_apply]
        have ha' : coreAct m (θ a) u = u := ha
        have hb' : coreAct m (θ b) u = u := hb
        rw [hb', ha']
      inv_mem' := by
        intro a ha
        show coreAct m (θ a⁻¹) u = u
        have ha' : coreAct m (θ a) u = u := ha
        calc coreAct m (θ a⁻¹) u = coreAct m (θ a⁻¹) (coreAct m (θ a) u) := by rw [ha']
          _ = u := by rw [← MulAut.mul_apply, ← map_mul, ← map_mul]; simp }
  exact (Subgroup.closure_le Stab).2 hS hg

theorem SymComp.exists_vec_of_swap (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M)
    (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) (hXT : X ≤ T)
    (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X)
    (hcl : ∀ g : ↥E, (g : MulAut V) ∈ X →
      g ∈ Subgroup.closure {e : ↥E | (e : MulAut V) ∈ T ∧ (θ e).IsSwap})
    {c d : Fin m} (hcd : c ≠ d) (hsw : swap c d ∈ swapSub X E θ) :
    ∃ w : ↥(commV E), β w = uvec hc.odd c * uvec hc.odd d ∧
      ∀ g : ↥E, (g : MulAut V) ∈ X → (g : MulAut V) w.1 = w.1 := by
  obtain ⟨w, hw⟩ := hc.surj (uvec hc.odd c * uvec hc.odd d)
  refine ⟨w, hw, fun g hgX => ?_⟩
  have hS : ∀ e ∈ {e : ↥E | (e : MulAut V) ∈ T ∧ (θ e).IsSwap},
      coreAct m (θ e) (uvec hc.odd c * uvec hc.odd d) = uvec hc.odd c * uvec hc.odd d := by
    rintro e ⟨heT, c', d', hcd', hθ⟩
    have heX : (e : MulAut V) ∈ X := hc.swap_mem_X h hV hF hE hXT hTX hX₀ heT hcd' hθ
    have hsw' : swap c' d' ∈ swapSub X E θ := mem_swapSub.2 ⟨e, heX, hθ⟩
    have hmatch := swapSub_match (E := E) (θ := θ) h hXT
    rw [hθ]
    exact coreAct_swap_fix_pair hc.odd hcd (swap_eq_or_disjoint hmatch hcd hcd' hsw hsw')
  have hgS := fix_of_closure θ _ _ hS (hcl g hgX)
  have hw' : β ⟨(g : MulAut V) w.1, hc.inv g g.2 w.1 w.2⟩ = β w := by
    rw [hc.equiv g w, hw, hgS]
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hc.ker
  exact congrArg Subtype.val (hinj hw')

theorem SymComp.commV_inf_fixV (hc : SymComp P M E m θ β i₀) {w : ↥(commV E)}
    (hw : ∀ g : ↥E, (g : MulAut V) w.1 = w.1) : w = 1 := by
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hc.ker
  have h1 : β w = 1 := by
    refine eq_one_of_fix_all hc.odd _ fun σ => ?_
    have hmem : (θ.symm σ : MulAut V) w.1 ∈ commV E := hc.inv _ (θ.symm σ).2 w.1 w.2
    have := hc.equiv (θ.symm σ) w hmem
    rw [θ.apply_symm_apply] at this
    rw [← this]
    congr 1
    exact Subtype.ext (hw (θ.symm σ))
  exact hinj (h1.trans (map_one β).symm)

theorem SymComp.local_step (hc : SymComp P M E m θ β i₀) (h : Hyp51 P T M)
    (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ) (hE : E ∈ ℰ) (hXT : X ≤ T)
    (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X)
    (hcl : ∀ g : ↥E, (g : MulAut V) ∈ X →
      g ∈ Subgroup.closure {e : ↥E | (e : MulAut V) ∈ T ∧ (θ e).IsSwap})
    {x : MulAut V} (hxT : x ∈ T) (hxN : x ∈ Subgroup.normalizer (E : Set (MulAut V)))
    (hxfix : ∀ w ∈ commV E, (∀ g : ↥E, (g : MulAut V) ∈ X → (g : MulAut V) w = w) → x w = w) :
    ∃ ε : ↥E, (ε : MulAut V) ∈ X ∧ ∀ w ∈ commV E, (ε : MulAut V) w = x w := by
  classical
  obtain ⟨π, hπ0, hπ⟩ := hc.exists_induces h hF hE hxT hxN
  set ε₀ : ↥E := θ.symm π with hε₀
  have hθε₀ : θ ε₀ = π := θ.apply_symm_apply π
  have hconj : ∀ e : ↥E, x * (e : MulAut V) * x⁻¹ = (ε₀ : MulAut V) * (e : MulAut V) * (ε₀ : MulAut V)⁻¹ := by
    intro e
    have hmem : x * (e : MulAut V) * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hxN e).1 e.2
    have h1 := hπ e ⟨_, hmem⟩ rfl
    have h2 : (⟨_, hmem⟩ : ↥E) = ε₀ * e * ε₀⁻¹ :=
      θ.injective (by rw [h1, map_mul, map_mul, hθε₀, map_inv, hθε₀])
    exact congrArg Subtype.val h2
  set z : MulAut V := (ε₀ : MulAut V)⁻¹ * x with hz
  have hzc : ∀ e : ↥E, z * (e : MulAut V) = (e : MulAut V) * z := by
    intro e
    have h1 := hconj e
    calc z * (e : MulAut V) = (ε₀ : MulAut V)⁻¹ * (x * (e : MulAut V) * x⁻¹) * x := by
          rw [hz]; group
      _ = (ε₀ : MulAut V)⁻¹ * ((ε₀ : MulAut V) * (e : MulAut V) * (ε₀ : MulAut V)⁻¹) * x := by
          rw [h1]
      _ = (e : MulAut V) * z := by rw [hz]; group
  have hzmem : ∀ w ∈ commV E, z w ∈ commV E := by
    intro w hw
    exact hc.inv _ (E.inv_mem ε₀.2) _ (mem_commV_of_mem_normalizer hxN hw)
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hc.ker
  let βe : ↥(commV E) ≃* ↥(coreMod m) := MulEquiv.ofBijective β ⟨hinj, hc.surj⟩
  let zhom : ↥(commV E) →* ↥(commV E) :=
    { toFun := fun w => ⟨z w.1, hzmem w.1 w.2⟩
      map_one' := Subtype.ext (map_one z)
      map_mul' := fun a b => Subtype.ext (map_mul z a.1 b.1) }
  have hzhom_inj : Function.Injective zhom := fun a b hab =>
    Subtype.ext (z.injective (congrArg Subtype.val hab))
  let ζ : ↥(coreMod m) →* ↥(coreMod m) := β.comp (zhom.comp βe.symm.toMonoidHom)
  have hζinj : Function.Injective ζ := hinj.comp (hzhom_inj.comp βe.symm.injective)
  have hζβ : ∀ p : ↥(commV E), ζ (β p) = β (zhom p) := by
    intro p
    show β (zhom (βe.symm (β p))) = _
    rw [show β p = βe p from rfl, βe.symm_apply_apply]
  have hζcomm : ∀ (σ : Perm (Fin m)) (d : ↥(coreMod m)),
      ζ (coreAct m σ d) = coreAct m σ (ζ d) := by
    intro σ d
    obtain ⟨p, rfl⟩ := hc.surj d
    set e : ↥E := θ.symm σ with he
    have hθe : θ e = σ := θ.apply_symm_apply σ
    have hep : (e : MulAut V) p.1 ∈ commV E := hc.inv e e.2 p.1 p.2
    have h1 : β ⟨(e : MulAut V) p.1, hep⟩ = coreAct m σ (β p) := by
      rw [hc.equiv e p hep, hθe]
    rw [← h1, hζβ, hζβ]
    have h2 : z ((e : MulAut V) p.1) = (e : MulAut V) (z p.1) := by
      have := congrArg (fun f : MulAut V => f p.1) (hzc e)
      simpa using this
    have hzp : (e : MulAut V) (z p.1) ∈ commV E := hc.inv e e.2 _ (hzmem p.1 p.2)
    have h3 : β ⟨(e : MulAut V) (z p.1), hzp⟩ = coreAct m σ (β (zhom p)) := by
      have := hc.equiv e (zhom p) hzp
      rw [hθe] at this
      exact this
    rw [← h3]
    congr 1
    exact Subtype.ext h2
  have hztriv : ∀ w ∈ commV E, z w = w := by
    intro w hw
    have h1 := eq_self_of_commute hc.odd hc.three ζ hζinj hζcomm (β ⟨w, hw⟩)
    rw [hζβ] at h1
    have h2 := hinj h1
    exact congrArg Subtype.val h2
  have hxε : ∀ w ∈ commV E, (ε₀ : MulAut V) w = x w := by
    intro w hw
    have hxz : x = (ε₀ : MulAut V) * z := by rw [hz]; group
    conv_rhs => rw [hxz]
    show (ε₀ : MulAut V) w = (ε₀ : MulAut V) (z w)
    rw [hztriv w hw]
  have hmem : π ∈ swapSub X E θ := by
    refine mem_of_commute_swaps (swapSub X E θ) i₀ (hc.swapSub_fix h hF hE hXT) ?_
      (swapSub_match (E := E) (θ := θ) h hXT) π ?_
    · intro c hc0
      obtain ⟨d, hdc, y, hyX, hy⟩ := hc.exists_swap_at h hV hF hE hXT hTX hX₀ hc0
      exact ⟨d, hdc, mem_swapSub.2 ⟨y, hyX, hy⟩⟩
    · intro c d hcd hsw
      obtain ⟨w, hw, hwfix⟩ := hc.exists_vec_of_swap h hV hF hE hXT hTX hX₀ hcl hcd hsw
      have hxw : x w.1 = w.1 := hxfix w.1 w.2 hwfix
      have hεw : (ε₀ : MulAut V) w.1 = w.1 := (hxε w.1 w.2).trans hxw
      have hεmem : (ε₀ : MulAut V) w.1 ∈ commV E := hc.inv ε₀ ε₀.2 w.1 w.2
      have h1 : β ⟨(ε₀ : MulAut V) w.1, hεmem⟩ = coreAct m π (β w) := by
        rw [hc.equiv ε₀ w hεmem, hθε₀]
      have h2 : (⟨(ε₀ : MulAut V) w.1, hεmem⟩ : ↥(commV E)) = w := Subtype.ext hεw
      rw [h2, hw] at h1
      exact pair_of_fix_uvec hc.odd hcd h1.symm
  obtain ⟨y, hyX, hy⟩ := mem_swapSub.1 hmem
  have hyε : y = ε₀ := θ.injective (by rw [hy, hθε₀])
  refine ⟨ε₀, hyε ▸ hyX, hxε⟩

end Component

end CFSG.AGLEmbeddingD2.Tits.E23
