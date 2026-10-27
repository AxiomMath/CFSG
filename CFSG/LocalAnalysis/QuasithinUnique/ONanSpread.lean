module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanBasic

public section

namespace CFSG.QuasithinUnique.ONan

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem sup_eq_top_of_inf_eq_bot {r : ℕ} (hV : finrank (ZMod 2) V = 2 * r)
    {D E : Submodule (ZMod 2) V} (hD : finrank (ZMod 2) D = r) (hE : finrank (ZMod 2) E = r)
    (hDE : D ⊓ E = ⊥) : D ⊔ E = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h := Submodule.finrank_sup_add_finrank_inf_eq D E
  rw [hDE, finrank_bot, hD, hE] at h
  omega

structure IsPartialSpread (r : ℕ) {ι : Type*} (D : ι → Submodule (ZMod 2) V) : Prop where
  finrank_space : finrank (ZMod 2) V = 2 * r
  finrank_eq : ∀ i, finrank (ZMod 2) (D i) = r
  inf_eq_bot : ∀ i j, i ≠ j → D i ⊓ D j = ⊥

variable {r : ℕ} {ι : Type*} {D : ι → Submodule (ZMod 2) V}

theorem IsPartialSpread.exists_unique_part (h : IsPartialSpread r D) {i j : ι} (hij : j ≠ i)
    (v : V) : ∃! e : V, e ∈ D j ∧ e + v ∈ D i := by
  have htop : D j ⊔ D i = ⊤ :=
    sup_eq_top_of_inf_eq_bot h.finrank_space (h.finrank_eq j) (h.finrank_eq i)
      (h.inf_eq_bot j i hij)
  have hv : v ∈ D j ⊔ D i := htop ▸ Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  refine ⟨u, ⟨hu, ?_⟩, ?_⟩
  · rw [add_self_add]; exact hw
  · rintro e ⟨he, he'⟩
    have h1 : e + u ∈ D j := (D j).add_mem he hu
    have h2 : e + u ∈ D i := by
      have := (D i).add_mem he' hw
      rwa [← add_assoc, add_add_self] at this
    have h3 : e + u ∈ D j ⊓ D i := ⟨h1, h2⟩
    rw [h.inf_eq_bot j i hij, Submodule.mem_bot] at h3
    exact (add_eq_zero_iff_eq e u).mp h3

omit [Finite V] in
theorem IsPartialSpread.part_injective (h : IsPartialSpread r D) {i : ι} {v : V} (hv : v ∉ D i)
    {f : {j : ι // j ≠ i} → V} (hf : ∀ j : {j : ι // j ≠ i}, f j ∈ D j ∧ f j + v ∈ D i) :
    Function.Injective f := by
  intro j j' hjj'
  by_contra hne
  have hne' : (j : ι) ≠ j' := fun h => hne (Subtype.ext h)
  have h1 : f j ∈ D j ⊓ D j' := ⟨(hf j).1, hjj' ▸ (hf j').1⟩
  rw [h.inf_eq_bot _ _ hne', Submodule.mem_bot] at h1
  apply hv
  have := (hf j).2
  rwa [h1, zero_add] at this

theorem ncard_coset {D : Submodule (ZMod 2) V} (hD : finrank (ZMod 2) D = r) (v : V) :
    {x : V | x + v ∈ D}.ncard = 2 ^ r := by
  have : {x : V | x + v ∈ D} = (fun x => x + v) ⁻¹' (D : Set V) := rfl
  rw [this, Set.ncard_preimage_of_injective_subset_range (add_left_injective v),
    ncard_submodule, hD]
  intro x hx
  exact ⟨x + v, add_add_self x v⟩

theorem natCard_ne [Finite ι] (i : ι) : Nat.card {j : ι // j ≠ i} = Nat.card ι - 1 := by
  have h : Nat.card {j : ι // j ≠ i} = (({i} : Set ι)ᶜ).ncard := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [h, Set.ncard_compl, Set.ncard_singleton]

theorem IsPartialSpread.natCard_le [Finite ι] (h : IsPartialSpread r D) (hr : 1 ≤ r) :
    Nat.card ι ≤ 2 ^ r + 1 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hne'
  · simp
  · have h2 : 0 < Nat.card ι := Nat.card_pos
    obtain ⟨i⟩ := hne'
    have hne : D i ≠ ⊤ := by
      intro htop
      have := h.finrank_eq i
      rw [htop, finrank_top, h.finrank_space] at this
      omega
    obtain ⟨v, hv⟩ : ∃ v, v ∉ D i := by
      by_contra hcon
      apply hne
      rw [eq_top_iff]
      intro x _
      by_contra hx
      exact hcon ⟨x, hx⟩
    choose f hf using fun j : {j : ι // j ≠ i} => (h.exists_unique_part j.2 v).exists
    have hfinj := h.part_injective hv hf
    have hrange : Set.range f ⊆ {x : V | x + v ∈ D i} := by
      rintro _ ⟨j, rfl⟩
      exact (hf j).2
    have h1 := Set.ncard_le_ncard hrange
    rw [Set.ncard_range_of_injective hfinj, natCard_ne, ncard_coset (h.finrank_eq i)] at h1
    omega

theorem IsPartialSpread.completion [Finite ι] (hS : IsPartialSpread r D)
    (hι : Nat.card ι = 2 ^ r) :
    ∃ Z : Submodule (ZMod 2) V, finrank (ZMod 2) Z = r ∧
      ∀ v : V, v ∈ Z ↔ (v = 0 ∨ ∀ i, v ∉ D i) := by
  classical
  have : Nonempty ι := by
    have : 0 < Nat.card ι := by rw [hι]; positivity
    exact (Nat.card_pos_iff.mp this).1
  let Zs : Set V := {z | z = 0 ∨ ∀ i, z ∉ D i}
  have key : ∀ (i : ι) (v : V), v ∉ D i → ∃! z : V, z ∈ Zs ∧ z + v ∈ D i := by
    intro i v hv
    choose f hf using fun j : {j : ι // j ≠ i} => (hS.exists_unique_part j.2 v).exists
    have hfinj := hS.part_injective hv hf
    have hrange : Set.range f ⊆ {x : V | x + v ∈ D i} := by
      rintro _ ⟨j, rfl⟩
      exact (hf j).2
    have hcoset : {x : V | x + v ∈ D i}.ncard = 2 ^ r := ncard_coset (hS.finrank_eq i) v
    have hcardR : (Set.range f).ncard = 2 ^ r - 1 := by
      rw [Set.ncard_range_of_injective hfinj, natCard_ne, hι]
    have hdiff : ({x : V | x + v ∈ D i} \ Set.range f).ncard = 1 := by
      rw [Set.ncard_sdiff hrange, hcoset, hcardR]
      have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      omega
    obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hdiff
    have hzmem : z ∈ ({x : V | x + v ∈ D i} \ Set.range f) := by rw [hz]; exact rfl
    obtain ⟨hz1, hz2⟩ := hzmem
    have hz1' : z + v ∈ D i := hz1
    refine ⟨z, ⟨Or.inr ?_, hz1'⟩, ?_⟩
    · intro j hzj
      by_cases hji : j = i
      · subst hji
        have := (D j).add_mem hzj hz1'
        rw [add_self_add] at this
        exact hv this
      · exact hz2 ⟨⟨j, hji⟩, (hS.exists_unique_part hji v).unique (hf ⟨j, hji⟩) ⟨hzj, hz1'⟩⟩
    · rintro z' ⟨hz'Z, hz'v⟩
      have hz'notin : z' ∉ Set.range f := by
        rintro ⟨j, rfl⟩
        rcases hz'Z with h0 | hall
        · apply hv
          have := (hf j).2
          rwa [h0, zero_add] at this
        · exact hall j (hf j).1
      have : z' ∈ ({x : V | x + v ∈ D i} \ Set.range f) := ⟨hz'v, hz'notin⟩
      rw [hz] at this
      exact this
  have hadd : ∀ x ∈ Zs, ∀ y ∈ Zs, x + y ∈ Zs := by
    intro x hx y hy
    by_contra hxy
    have hxy' : ¬ (x + y = 0 ∨ ∀ i, x + y ∉ D i) := hxy
    simp only [not_or, not_forall, not_not] at hxy'
    obtain ⟨hne, i, hi⟩ := hxy'
    have hxi : x ∉ D i := by
      intro hxi
      have hx0 : x = 0 := hx.resolve_right (fun H => H i hxi)
      have hyi : y ∈ D i := by
        have := (D i).add_mem hxi hi
        rwa [add_self_add] at this
      have hy0 : y = 0 := hy.resolve_right (fun H => H i hyi)
      exact hne (by rw [hx0, hy0, add_zero])
    obtain ⟨z, _, huniq⟩ := key i x hxi
    have h1 : x = z := huniq x ⟨hx, by rw [ZModModule.add_self]; exact (D i).zero_mem⟩
    have h2 : y = z := huniq y ⟨hy, by rwa [add_comm]⟩
    exact hne (by rw [h1, h2, ZModModule.add_self])
  let Z : Submodule (ZMod 2) V := submoduleOfAdd Zs (Or.inl rfl) hadd
  have hZmem : ∀ v, v ∈ Z ↔ v ∈ Zs := fun v => mem_submoduleOfAdd Zs (Or.inl rfl) hadd v
  refine ⟨Z, ?_, fun v => hZmem v⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hZi : Z ⊓ D i = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxZ, hxD⟩
    rcases (hZmem x).mp hxZ with h0 | hall
    · rw [h0]; exact Submodule.zero_mem _
    · exact absurd hxD (hall i)
  have hZtop : Z ⊔ D i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    by_cases hv : v ∈ D i
    · exact Submodule.mem_sup_right hv
    · obtain ⟨z, ⟨hz, hzv⟩, _⟩ := key i v hv
      have : v = z + (z + v) := (add_self_add z v).symm
      rw [this]
      exact Submodule.add_mem_sup ((hZmem z).mpr hz) hzv
  have h := Submodule.finrank_sup_add_finrank_inf_eq Z (D i)
  rw [hZtop, hZi, finrank_top, finrank_bot, hS.finrank_space, hS.finrank_eq i] at h
  omega

theorem spread_completion_fin (r : ℕ) (hV : finrank (ZMod 2) V = 2 * r)
    (D : Fin (2 ^ r) → Submodule (ZMod 2) V) (hD : ∀ i, finrank (ZMod 2) (D i) = r)
    (hDD : ∀ i j, i ≠ j → D i ⊓ D j = ⊥) :
    ∃ Z : Submodule (ZMod 2) V, finrank (ZMod 2) Z = r ∧
      ∀ v : V, v ∈ Z ↔ (v = 0 ∨ ∀ i, v ∉ D i) :=
  IsPartialSpread.completion ⟨hV, hD, hDD⟩ (by simp)

end CFSG.QuasithinUnique.ONan
