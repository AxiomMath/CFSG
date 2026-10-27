module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.QuasithinUnique.Setup.X1

section Aut

variable {G : Type*} [Group G]

theorem autInner_of_card_pairs [Finite G] (hc : Subgroup.center G = ⊥) {a b : G}
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (P : G → G → Prop)
    (hP : ∀ φ : G ≃* G, P (φ a) (φ b))
    (hcard : Nat.card {p : G × G // P p.1 p.2} ≤ Nat.card G) :
    ∀ φ : G ≃* G, ∃ s : G, ∀ x, φ x = s * x * s⁻¹ := by
  have hinj : Function.Injective
      (fun φ : G ≃* G => (⟨(φ a, φ b), hP φ⟩ : {p : G × G // P p.1 p.2})) := by
    intro φ ψ h
    have h1 : φ a = ψ a := congrArg (fun q : {p : G × G // P p.1 p.2} => q.1.1) h
    have h2 : φ b = ψ b := congrArg (fun q : {p : G × G // P p.1 p.2} => q.1.2) h
    have hfun : Set.EqOn (φ : G →* G) (ψ : G →* G) ({a, b} : Set G) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact h1
      · rw [hx]; exact h2
    ext x
    have := MonoidHom.eqOn_closure hfun (hgen ▸ Subgroup.mem_top x)
    exact this
  have hcard1 : Nat.card (G ≃* G) ≤ Nat.card G :=
    (Nat.card_le_card_of_injective _ hinj).trans hcard
  have hconj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hcentral : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hconj := congrArg (fun f : MulAut G => f y) (MonoidHom.mem_ker.1 hx)
      change x * y * x⁻¹ = y at hconj
      have heq := congrArg (fun z : G => z * x) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
    rwa [hc] at hcentral
  have hcard2 : Nat.card G ≤ Nat.card (G ≃* G) := Nat.card_le_card_of_injective _ hconj
  have hbij : Function.Bijective (MulAut.conj : G →* MulAut G) :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨hconj, le_antisymm hcard2 hcard1⟩
  intro φ
  obtain ⟨s, hs⟩ := hbij.2 φ
  exact ⟨s, fun x => by rw [← hs]; rfl⟩

end Aut

section Conj

variable {S : Type*} [Group S]

theorem exists_generating_conjugates_of_conj {t₀ t h : S} (cs₀ : List S)
    (h₀ : Subgroup.closure {x : S | ∃ c ∈ cs₀, x = c * t₀ * c⁻¹} = ⊤) (hth : h * t₀ * h⁻¹ = t) :
    ∃ cs : List S, cs.length = cs₀.length ∧
      Subgroup.closure {x : S | ∃ c ∈ cs, x = c * t * c⁻¹} = ⊤ := by
  refine ⟨cs₀.map fun c => h * c * h⁻¹, by simp, ?_⟩
  have hφ : ∀ x : S, (MulAut.conj h).toMonoidHom x = h * x * h⁻¹ := fun x => rfl
  have himg : {x : S | ∃ c ∈ cs₀.map fun c => h * c * h⁻¹, x = c * t * c⁻¹} =
      (MulAut.conj h).toMonoidHom '' {x : S | ∃ c ∈ cs₀, x = c * t₀ * c⁻¹} := by
    ext x
    simp only [List.mem_map, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨c * t₀ * c⁻¹, ⟨c, hc, rfl⟩, ?_⟩
      rw [hφ, ← hth]
      group
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨_, ⟨c, hc, rfl⟩, ?_⟩
      rw [hφ, ← hth]
      group
  rw [himg, ← MonoidHom.map_closure, h₀, Subgroup.map_top, MonoidHom.range_eq_top]
  intro y
  exact ⟨h⁻¹ * y * h, by rw [hφ]; group⟩

end Conj

section Indep

variable {S : Type*} [Group S]

@[expose] def subprods : List S → List S
  | [] => [1]
  | y :: l => subprods l ++ (subprods l).map (y * ·)

inductive IndepList : List S → Prop
  | nil : IndepList []
  | cons (x : S) (l : List S) : x * x = 1 → x ≠ 1 → (∀ y ∈ l, x * y = y * x) →
      x ∉ subprods l → IndepList l → IndepList (x :: l)

theorem one_mem_subprods (l : List S) : (1 : S) ∈ subprods l := by
  induction l with
  | nil => simp [subprods]
  | cons y l ih => simp only [subprods, List.mem_append]; exact Or.inl ih

theorem length_subprods (l : List S) : (subprods l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons y l ih => simp [subprods, ih, pow_succ]; ring

theorem subprods_subset {B : Subgroup S} {l : List S} (h : ∀ y ∈ l, y ∈ B) :
    ∀ z ∈ subprods l, z ∈ B := by
  induction l with
  | nil => intro z hz; simp only [subprods, List.mem_singleton] at hz; rw [hz]; exact B.one_mem
  | cons y l ih =>
    intro z hz
    simp only [subprods, List.mem_append, List.mem_map] at hz
    have hl : ∀ w ∈ l, w ∈ B := fun w hw => h w (List.mem_cons_of_mem y hw)
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact ih hl z hz
    · exact B.mul_mem (h y List.mem_cons_self) (ih hl w hw)

theorem card_le_two_pow_of_no_indep [Finite S] (n : ℕ)
    (h : ¬ ∃ l : List S, IndepList l ∧ l.length = n + 1) :
    ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ n := by
  intro B hcomm hsq
  by_contra hgt
  push Not at hgt
  have key : ∀ m, m ≤ n + 1 → ∃ l : List S, IndepList l ∧ l.length = m ∧ ∀ y ∈ l, y ∈ B := by
    intro m
    induction m with
    | zero => intro _; exact ⟨[], IndepList.nil, rfl, by simp⟩
    | succ m ih =>
      intro hm
      obtain ⟨l, hl, hlen, hlB⟩ := ih (by omega)
      classical
      have hsub : ∃ x ∈ B, x ∉ subprods l := by
        by_contra hno
        push Not at hno
        have : Nat.card B ≤ (subprods l).toFinset.card := by
          have hle : (B : Set S) ⊆ ((subprods l).toFinset : Set S) := fun x hx => by
            simpa using hno x hx
          calc Nat.card B = (B : Set S).ncard := Nat.card_coe_set_eq _
            _ ≤ ((subprods l).toFinset : Set S).ncard := Set.ncard_le_ncard hle
            _ = (subprods l).toFinset.card := Set.ncard_coe_finset _
        have h2 : (subprods l).toFinset.card ≤ 2 ^ m := by
          calc (subprods l).toFinset.card ≤ (subprods l).length := List.toFinset_card_le _
            _ = 2 ^ l.length := length_subprods l
            _ = 2 ^ m := by rw [hlen]
        have h3 : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨x, hxB, hx⟩ := hsub
      refine ⟨x :: l, IndepList.cons x l (hsq x hxB) ?_ (fun y hy => hcomm x hxB y (hlB y hy)) hx hl,
        by simp [hlen], ?_⟩
      · intro h1
        exact hx (h1 ▸ one_mem_subprods l)
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hxB
        · exact hlB y hy
  obtain ⟨l, hl, hlen, -⟩ := key (n + 1) le_rfl
  exact h ⟨l, hl, hlen⟩

theorem indepList_three {x y z : S} (h : IndepList [x, y, z]) :
    x * x = 1 ∧ y * y = 1 ∧ z * z = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ x * y = y * x ∧
      x * z = z * x ∧ y * z = z * y ∧ x ≠ y ∧ x ≠ z ∧ x ≠ y * z ∧ y ≠ z := by
  have e1 : subprods [z] = [1, z] := by simp [subprods]
  have e2 : subprods [y, z] = [1, z, y, y * z] := by simp [subprods]
  cases h with
  | cons _ _ hx2 hx1 hxc hxs hl =>
    cases hl with
    | cons _ _ hy2 hy1 hyc hys hl' =>
      cases hl' with
      | cons _ _ hz2 hz1 hzc hzs hl'' =>
        rw [e2] at hxs
        rw [e1] at hys
        refine ⟨hx2, hy2, hz2, hx1, hy1, hz1, hxc y (by simp), hxc z (by simp),
          hyc z (by simp), ?_, ?_, ?_, ?_⟩
        · intro h
          exact hxs (by simp [h])
        · intro h
          exact hxs (by simp [h])
        · intro h
          exact hxs (by simp [h])
        · intro h
          exact hys (by simp [h])

end Indep

end CFSG.QuasithinUnique.Setup.X1
