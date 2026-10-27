module

public import CFSG.GH74.GLS.Bg.TwoGroups.Statements

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

@[expose] def fixSub {T : Type} [Group T] (t : MulAut T) : Subgroup T where
  carrier := {g | t g = g}
  mul_mem' := by
    intro a b ha hb
    show t (a * b) = a * b
    rw [map_mul]
    exact congrArg₂ (· * ·) ha hb
  one_mem' := map_one t
  inv_mem' := by
    intro a ha
    show t a⁻¹ = a⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) ha

theorem exists_coset_fixed {T : Type} [Group T] [Finite T] (hp : IsPGroup 2 T) (t : MulAut T)
    (ht : t * t = 1) (U : Subgroup T) (hU : ∀ u ∈ U, t u ∈ U) (hne : U ≠ ⊤) :
    ∃ x : T, x ∉ U ∧ x⁻¹ * t x ∈ U := by
  classical
  have : Fintype (T ⧸ U) := Fintype.ofFinite _
  let f : T ⧸ U → T ⧸ U := Quotient.map' (fun x => t x) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ U := QuotientGroup.leftRel_apply.mp hab
    refine QuotientGroup.leftRel_apply.mpr ?_
    have := hU _ hab'
    rwa [map_mul, map_inv] at this)
  have hf : ∀ x : T, f (QuotientGroup.mk x) = QuotientGroup.mk (t x) := fun x => rfl
  let F : Function.End (T ⧸ U) := f
  have hF2 : F ^ 2 ^ 1 = 1 := by
    funext q
    induction q using QuotientGroup.induction_on with
    | _ x =>
      show f (f (QuotientGroup.mk x)) = QuotientGroup.mk x
      rw [hf, hf]
      have : t (t x) = x := by
        have := congrArg (fun s : MulAut T => s x) ht
        simpa using this
      rw [this]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := F) (p := 2) (n := 1) hF2
  have hidx : Even (Fintype.card (T ⧸ U)) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    obtain ⟨n, hn⟩ := hp.index U
    rw [hn]
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.index_eq_one.mp (by simpa using hn))
    exact (Nat.even_pow.mpr ⟨even_two, hn0⟩)
  have hbase : (QuotientGroup.mk (1 : T) : T ⧸ U) ∈ F.fixedPoints := by
    show f (QuotientGroup.mk 1) = QuotientGroup.mk 1
    rw [hf, map_one]
  have hfpeven : Even (Fintype.card F.fixedPoints) := by
    have h1 : Fintype.card (T ⧸ U) % 2 = Fintype.card F.fixedPoints % 2 := hmod
    rw [Nat.even_iff] at hidx ⊢
    omega
  have hpos : 0 < Fintype.card F.fixedPoints := Fintype.card_pos_iff.mpr ⟨⟨_, hbase⟩⟩
  have hgt : 1 < Fintype.card F.fixedPoints := by
    obtain ⟨k, hk⟩ := hfpeven
    omega
  obtain ⟨⟨q, hq⟩, hqne⟩ := Fintype.exists_ne_of_one_lt_card hgt ⟨_, hbase⟩
  induction q using QuotientGroup.induction_on with
  | _ x =>
    have hq' : f (QuotientGroup.mk x) = QuotientGroup.mk x := hq
    rw [hf] at hq'
    refine ⟨x, ?_, QuotientGroup.eq.mp hq'.symm⟩
    intro hx
    apply hqne
    apply Subtype.ext
    exact QuotientGroup.eq.mpr (by simpa using U.inv_mem hx)

theorem exists_fixed_coset3 {T : Type} [Group T] [Finite T] (hp : IsPGroup 2 T) (α : MulAut T)
    (m : ℕ) (hα : α ^ (3 ^ m) = 1) (A : Subgroup T) (hA : ∀ a ∈ A, α a ∈ A) (g : T)
    (hg : g⁻¹ * α g ∈ A) : ∃ s : T, g⁻¹ * s ∈ A ∧ α s = s := by
  classical
  have hmem : ∀ s : T, g⁻¹ * s ∈ A → g⁻¹ * α s ∈ A := by
    intro s hs
    have h1 : g⁻¹ * α s = (g⁻¹ * α g) * α (g⁻¹ * s) := by
      rw [map_mul, map_inv]; group
    rw [h1]; exact mul_mem hg (hA _ hs)
  let β : Type := {s : T // g⁻¹ * s ∈ A}
  have : Fintype β := Fintype.ofFinite β
  let f : Function.End β := fun s => ⟨α s.1, hmem s.1 s.2⟩
  have hf : ∀ k : ℕ, ∀ s : β, ((f ^ k) s : T) = (α ^ k) s.1 := by
    intro k
    induction k with
    | zero => intro s; rfl
    | succ k ih =>
      intro s
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f s) : T) = (α ^ k) (α s.1)
      rw [ih]
  have hfp : f ^ 3 ^ m = 1 := by
    funext s
    apply Subtype.ext
    rw [hf, hα]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := m) hfp
  have hβ : Fintype.card β = Nat.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun s => ⟨g⁻¹ * s.1, s.2⟩
        invFun := fun a => ⟨g * a.1, by simp⟩
        left_inv := fun s => by apply Subtype.ext; simp
        right_inv := fun a => by apply Subtype.ext; simp }
  have hA3 : Nat.card A % 3 ≠ 0 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hp.to_subgroup A)
    rw [hk]
    intro h
    have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hne : Fintype.card f.fixedPoints ≠ 0 := by
    intro h0
    have : Fintype.card β % 3 = Fintype.card f.fixedPoints % 3 := hmod
    rw [h0, hβ] at this
    exact hA3 (by omega)
  obtain ⟨⟨s, hs⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hne)
  refine ⟨s.1, s.2, ?_⟩
  have : f s = s := hs
  exact congrArg Subtype.val this

theorem axb {T : Type} [Group T] [Finite T] (hp : IsPGroup 2 T) (α t : MulAut T) (m : ℕ)
    (hα : α ^ (3 ^ m) = 1) (ht : t * t = 1) (hc : α * t = t * α)
    (hfix : ∀ g : T, t g = g → α g = g) : α = 1 := by
  by_contra hne
  set U : Subgroup T := fixSub α with hUdef
  have hUt : ∀ u ∈ U, t u ∈ U := by
    intro u hu
    have hu' : α u = u := hu
    show α (t u) = t u
    have : α (t u) = t (α u) := by
      have := congrArg (fun s : MulAut T => s u) hc
      simpa using this
    rw [this, hu']
  have hUtop : U ≠ ⊤ := by
    intro htop
    apply hne
    refine MulEquiv.ext fun g => ?_
    have : g ∈ U := htop ▸ Subgroup.mem_top g
    exact this
  obtain ⟨x', hx'U, hx'⟩ := exists_coset_fixed hp t ht U hUt hUtop
  set x : T := x'⁻¹ with hx
  have hxU : x ∉ U := fun h => hx'U (by simpa [hx] using U.inv_mem h)
  have hu : t x * x⁻¹ ∈ U := by
    have := U.inv_mem hx'
    have e : (x'⁻¹ * t x')⁻¹ = t x * x⁻¹ := by
      simp [hx, map_inv]
    rwa [e] at this
  set u : T := t x * x⁻¹ with hudef
  have hux : t x = u * x := by simp [hudef]
  have hαu : α u = u := hu
  set d : T := x⁻¹ * α x with hddef
  have htd : t d = d := by
    have h1 : t d = (t x)⁻¹ * α (t x) := by
      rw [hddef, map_mul, map_inv]
      congr 1
      have := congrArg (fun s : MulAut T => s x) hc
      simpa using this.symm
    rw [h1, hux, map_mul, hαu, mul_inv_rev, hddef]
    group
  have hαd : α d = d := hfix d htd
  have hαdk : ∀ k : ℕ, (α ^ k) d = d := by
    intro k
    induction k with
    | zero => rfl
    | succ j ihj => rw [pow_succ, MulAut.mul_apply, hαd, ihj]
  have hpow : ∀ k : ℕ, (α ^ k) x = x * d ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply]
      have hax : α x = x * d := by rw [hddef]; group
      rw [hax, map_mul, ih, hαdk, pow_succ]
      group
  have hd1 : d ^ 3 ^ m = 1 := by
    have h1 := hpow (3 ^ m)
    rw [hα] at h1
    have : x = x * d ^ 3 ^ m := by simpa using h1
    simpa using this.symm
  have hd2 : d = 1 := by
    obtain ⟨n, hn⟩ := hp d
    have h1 : orderOf d ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hd1
    have h2 : orderOf d ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have h3 : orderOf d ∣ Nat.gcd (3 ^ m) (2 ^ n) := Nat.dvd_gcd h1 h2
    have : Nat.gcd (3 ^ m) (2 ^ n) = 1 :=
      Nat.Coprime.pow m n (by norm_num : Nat.Coprime 3 2)
    rw [this] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  apply hxU
  have : α x = x := by
    have : α x = x * d := by rw [hddef]; group
    rw [this, hd2, mul_one]
  exact this

theorem card_fix_modEq {T : Type} [Group T] [Finite T] (p : ℕ) [Fact p.Prime] (α : MulAut T)
    (m : ℕ) (hα : α ^ (p ^ m) = 1) (V : Subgroup T) (hV : ∀ v ∈ V, α v ∈ V) :
    Nat.card V ≡ Nat.card {v : V // α v = v} [MOD p] := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let f : Function.End V := fun d => ⟨α d, hV d d.2⟩
  have hf : ∀ k : ℕ, ∀ d : V, ((f ^ k) d : T) = (α ^ k) d := by
    intro k
    induction k with
    | zero => intro d; rfl
    | succ k ih =>
      intro d
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f d) : T) = (α ^ k) (α d)
      rw [ih]
  have hfp : f ^ p ^ m = 1 := by
    funext d
    apply Subtype.ext
    rw [hf, hα]
    rfl
  have := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := m) hfp
  rw [Nat.card_eq_fintype_card]
  have h2 : Nat.card {d : V // α d = d} = Fintype.card f.fixedPoints := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun d => by
      show α d = d ↔ f d = d
      constructor
      · intro h; exact Subtype.ext h
      · intro h; exact congrArg Subtype.val h)
  rw [h2]
  exact this

theorem card_fix_modEq3 {T : Type} [Group T] [Finite T] (α : MulAut T) (m : ℕ)
    (hα : α ^ (3 ^ m) = 1) (V : Subgroup T) (hV : ∀ v ∈ V, α v ∈ V) :
    Nat.card V ≡ Nat.card {v : V // α v = v} [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact card_fix_modEq 3 α m hα V hV

theorem exists_fixed_nontrivial {T : Type} [Group T] [Finite T] (hp : IsPGroup 2 T) (t : MulAut T)
    (ht : t * t = 1) (V : Subgroup T) (hV : ∀ v ∈ V, t v ∈ V) (hne : V ≠ ⊥) :
    ∃ v ∈ V, v ≠ 1 ∧ t v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_fix_modEq 2 t 1 (by rw [pow_one, pow_two]; exact ht) V hV
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hp.to_subgroup V)
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hne
    apply Subgroup.eq_bot_of_card_eq
    simpa using hn
  have hev : Nat.card V % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  have hF : Nat.card {v : V // t v = v} % 2 = 0 := by
    have h1 : Nat.card V % 2 = Nat.card {v : V // t v = v} % 2 := hmod
    omega
  have hpos : 0 < Nat.card {v : V // t v = v} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, V.one_mem⟩, map_one t⟩, inferInstance⟩
  have hgt : 1 < Nat.card {v : V // t v = v} := by omega
  have : Nontrivial {v : V // t v = v} := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨x, hx⟩ := exists_ne (⟨⟨1, V.one_mem⟩, map_one t⟩ : {v : V // t v = v})
  refine ⟨x.1.1, x.1.2, ?_, x.2⟩
  intro h
  apply hx
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem commAut_invariant {T : Type} [Group T] (α : MulAut T) :
    ∀ k ∈ commAut α, α k ∈ commAut α := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    apply Subgroup.subset_closure
    exact ⟨α g, by rw [map_mul, map_inv]⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem commAut_eq_top {T : Type} [Group T] [Finite T] (hp : IsPGroup 2 T) (α : MulAut T)
    (m : ℕ) (hα : α ^ (3 ^ m) = 1) (hfix : ∀ g : T, α g = g → g = 1) : commAut α = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : g⁻¹ * α g ∈ commAut α := Subgroup.subset_closure ⟨g, rfl⟩
  obtain ⟨s, hs, hαs⟩ := exists_fixed_coset3 hp α m hα (commAut α) (commAut_invariant α) g hg
  have : s = 1 := hfix s hαs
  rw [this, mul_one] at hs
  simpa using inv_mem hs

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
