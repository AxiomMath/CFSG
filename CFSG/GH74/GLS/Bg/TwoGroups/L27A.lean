module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23T
public import CFSG.GH74.GLS.Bg.TwoGroups.L26Cop

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L27

open L26

theorem perm_pow_three {α : Type} [Fintype α] [DecidableEq α] (hα : Fintype.card α ≤ 8)
    (σ : Equiv.Perm α) (k : ℕ) (h : σ ^ (3 ^ k) = 1) : σ ^ 3 = 1 := by
  have hord : orderOf σ ∣ 3 := by
    rw [← Equiv.Perm.lcm_cycleType]
    refine Multiset.lcm_dvd.mpr ?_
    intro n hn
    have h1 : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : n ∣ 3 ^ k := h1.trans (orderOf_dvd_of_pow_eq_one h)
    have hle : n ≤ 8 := by
      have h3 : n ≤ σ.cycleType.sum := Multiset.le_sum_of_mem hn
      rw [Equiv.Perm.sum_cycleType] at h3
      exact h3.trans ((Finset.card_le_univ _).trans hα)
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    have hi : i ≤ 1 := by
      by_contra hcon
      have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 3 ^ i ∣ 3 ^ 1 := pow_dvd_pow 3 hi
      _ = 3 := pow_one 3
  exact orderOf_dvd_iff_pow_eq_one.mp hord

theorem aut_pow_three {C : Type} [Group C] [Finite C] (hC : Nat.card C ≤ 8) (β : MulAut C)
    (k : ℕ) (h : β ^ (3 ^ k) = 1) : β ^ 3 = 1 := by
  classical
  have : Fintype C := Fintype.ofFinite C
  have h1 : (MulAut.toPerm C β) ^ (3 ^ k) = 1 := by
    rw [← map_pow, h, map_one]
  have h2 := perm_pow_three (by rw [← Nat.card_eq_fintype_card]; exact hC) _ k h1
  have h3 : MulAut.toPerm C (β ^ 3) = 1 := by rw [map_pow]; exact h2
  refine MulEquiv.ext fun c => ?_
  exact congrArg (fun σ : Equiv.Perm C => σ c) h3

variable {T : Type} [Group T] [Finite T]

omit [Finite T] in
theorem mem_cent {t g : T} : g ∈ Subgroup.centralizer ({t} : Set T) ↔ t * g = g * t := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

omit [Finite T] in
theorem conj_comm_of_fix (t : T) (α : MulAut T) (hαt : α t = t) :
    α * MulAut.conj t = MulAut.conj t * α := by
  refine MulEquiv.ext fun g => ?_
  show α (t * g * t⁻¹) = t * α g * t⁻¹
  rw [map_mul, map_mul, map_inv, hαt]

omit [Finite T] in
theorem cent_inv (t : T) (α : MulAut T) (hαt : α t = t) :
    ∀ c ∈ Subgroup.centralizer ({t} : Set T), α c ∈ Subgroup.centralizer ({t} : Set T) := by
  intro c hc
  rw [mem_cent] at hc ⊢
  have := congrArg α hc
  rw [map_mul, map_mul, hαt] at this
  exact this

theorem alpha_cube (hp : IsPGroup 2 T) (t : T) (ht2 : t * t = 1)
    (hC : Nat.card (Subgroup.centralizer ({t} : Set T)) ≤ 8)
    (α : MulAut T) (n : ℕ) (hα : α ^ (3 ^ n) = 1) (hαt : α t = t) : α ^ 3 = 1 := by
  set C := Subgroup.centralizer ({t} : Set T) with hCdef
  have hinv : ∀ c ∈ C, α c ∈ C := cent_inv t α hαt
  have h1 : (L23.xRes α C hinv) ^ (3 ^ n) = 1 := by
    refine MulEquiv.ext fun c => ?_
    apply Subtype.ext
    rw [L23.xRes_pow, hα]
    rfl
  have h2 := aut_pow_three hC _ n h1
  have h3 : ∀ g : T, MulAut.conj t g = g → (α ^ 3) g = g := by
    intro g hg
    have hgC : g ∈ C := by
      rw [hCdef, mem_cent]
      rw [MulAut.conj_apply] at hg
      calc t * g = (t * g * t⁻¹) * t := by group
        _ = g * t := by rw [hg]
    have h4 := L23.xRes_pow α C hinv 3 ⟨g, hgC⟩
    rw [h2] at h4
    exact h4.symm
  have hct : MulAut.conj t * MulAut.conj t = 1 := by
    rw [← map_mul, ht2, map_one]
  have hc : α ^ 3 * MulAut.conj t = MulAut.conj t * α ^ 3 :=
    (Commute.pow_left (show Commute α (MulAut.conj t) from conj_comm_of_fix t α hαt) 3).eq
  exact axb hp (α ^ 3) (MulAut.conj t) n (by rw [← pow_mul, mul_comm, pow_mul, hα, one_pow]) hct
    hc h3

structure Hyp7 (T : Type) [Group T] (t : T) (α : MulAut T) : Prop where
  p2 : IsPGroup 2 T
  t2 : t * t = 1
  t1 : t ≠ 1
  Cab : ∀ a b : T, t * a = a * t → t * b = b * t → a * b = b * a
  C2 : ∀ c : T, t * c = c * t → c * c = 1
  Ccard : Nat.card (Subgroup.centralizer ({t} : Set T)) = 8
  a3 : α ^ 3 = 1
  a1 : α ≠ 1
  αt : α t = t

structure Cfg7 (T : Type) [Group T] (t : T) (α : MulAut T) (E : Subgroup T) : Prop
    extends Hyp7 T t α where
  EC : ∀ e ∈ E, t * e = e * t
  Ecard : Nat.card E = 4
  Einv : ∀ e ∈ E, α e ∈ E
  Efpf : ∀ e ∈ E, α e = e → e = 1
  tE : t ∉ E
  CE : ∀ c : T, t * c = c * t → c ∈ E ∨ ∃ e ∈ E, c = t * e

variable {t : T} {α : MulAut T}

theorem exists_E (h : Hyp7 T t α) : ∃ E : Subgroup T, Cfg7 T t α E := by
  classical
  have hp := h.p2
  set C := Subgroup.centralizer ({t} : Set T) with hCdef
  have htC : t ∈ C := mem_cent.mpr rfl
  have hinv : ∀ c ∈ C, α c ∈ C := cent_inv t α h.αt
  have hcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    h.Cab a b (mem_cent.mp ha) (mem_cent.mp hb)
  let _ : CommGroup ↥C :=
    { (inferInstance : Group ↥C) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let β : MulAut ↥C := L23.xRes α C hinv
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun c => ?_
    apply Subtype.ext
    rw [L23.xRes_pow, h.a3]
    rfl
  have hβ333 : ∀ c : ↥C, β (β (β c)) = c := by
    intro c
    have h1 := congrArg (fun s : MulAut ↥C => s c) hβ3
    rw [pow_three] at h1
    exact h1
  have hsq : ∀ c : ↥C, c * c = 1 := fun c => Subtype.ext (h.C2 c (mem_cent.mp c.2))
  let ν : ↥C →* ↥C :=
    { toFun := fun c => c * β c * β (β c)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [map_mul]
        ac_rfl }
  have hν : ∀ c, ν c = c * β c * β (β c) := fun c => rfl
  have hνβ : ∀ c, ν (β c) = ν c := by
    intro c
    rw [hν, hν, hβ333]
    ac_rfl
  have hβν : ∀ c, β (ν c) = ν c := by
    intro c
    rw [hν]
    simp only [map_mul, hβ333]
    ac_rfl
  have hrange : ν.range = fixSub β := by
    ext w
    constructor
    · rintro ⟨c, rfl⟩
      exact hβν c
    · intro hw
      have hw' : β w = w := hw
      refine ⟨w, ?_⟩
      rw [hν, hw', hw', hsq w, one_mul]
  have hCcard : Nat.card ↥C = 8 := h.Ccard
  have hfixcard : Nat.card (fixSub β) = Nat.card {v : ↥C // α v = v} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    show β v = v ↔ α v = v
    constructor
    · intro hv
      exact congrArg Subtype.val hv
    · intro hv
      exact Subtype.ext hv
  have hmod := card_fix_modEq3 α 1 (by rw [pow_one]; exact h.a3) C hinv
  have hdvd : Nat.card (fixSub β) ∣ 8 := hCcard ▸ Subgroup.card_subgroup_dvd_card (fixSub β)
  have hf3 : Nat.card (fixSub β) % 3 = 2 := by
    rw [hfixcard]
    have h1 : 8 % 3 = Nat.card {v : ↥C // α v = v} % 3 := by rw [← hCcard]; exact hmod
    omega
  have hnotall : Nat.card (fixSub β) ≠ 8 := by
    intro h8
    have htop : fixSub β = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [h8, hCcard]
    apply h.a1
    refine axb hp α (MulAut.conj t) 1 (by rw [pow_one]; exact h.a3) ?_ ?_ ?_
    · rw [← map_mul, h.t2, map_one]
    · exact conj_comm_of_fix t α h.αt
    · intro g hg
      have hgC : g ∈ C := by
        rw [hCdef, mem_cent]
        rw [MulAut.conj_apply] at hg
        calc t * g = (t * g * t⁻¹) * t := by group
          _ = g * t := by rw [hg]
      have : (⟨g, hgC⟩ : ↥C) ∈ fixSub β := by rw [htop]; exact Subgroup.mem_top _
      exact congrArg Subtype.val (this : β ⟨g, hgC⟩ = ⟨g, hgC⟩)
  have hf2 : Nat.card (fixSub β) = 2 := by
    obtain ⟨i, hi, hi'⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card (fixSub β) ∣ 2 ^ 3 from hdvd)
    interval_cases i
    · rw [pow_zero] at hi'
      omega
    · rw [hi']
      norm_num
    · rw [hi'] at hf3
      norm_num at hf3
    · exact absurd (by rw [hi']; norm_num) hnotall
  have hker4 : Nat.card ν.ker = 4 := by
    have h1 := Subgroup.card_ker_mul_card_range ν
    rw [hrange, hf2, hCcard] at h1
    omega
  refine ⟨ν.ker.map C.subtype, ?_⟩
  have hmemE : ∀ e : T, e ∈ ν.ker.map C.subtype ↔ ∃ c : ↥C, ν c = 1 ∧ (c : T) = e := by
    intro e
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
  let tC : ↥C := ⟨t, htC⟩
  have hνt : ν tC = tC := by
    show tC * β tC * β (β tC) = tC
    have e1 : β tC = tC := Subtype.ext h.αt
    rw [e1, e1, hsq tC, one_mul]
  have htC_fix : tC ∈ fixSub β := Subtype.ext h.αt
  have htC1 : tC ≠ 1 := fun h' => h.t1 (congrArg Subtype.val h')
  refine
    { toHyp7 := h
      EC := ?_
      Ecard := ?_
      Einv := ?_
      Efpf := ?_
      tE := ?_
      CE := ?_ }
  · intro e he
    obtain ⟨c, -, rfl⟩ := (hmemE e).mp he
    exact mem_cent.mp c.2
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hker4
  · intro e he
    obtain ⟨c, hc, rfl⟩ := (hmemE e).mp he
    exact (hmemE _).mpr ⟨β c, by rw [hνβ]; exact hc, rfl⟩
  · intro e he hfix
    obtain ⟨c, hc, rfl⟩ := (hmemE e).mp he
    have hβc : β c = c := Subtype.ext hfix
    have h1 : ν c = c := by rw [hν, hβc, hβc, hsq c, one_mul]
    have h2 : c = 1 := by rw [← h1]; exact hc
    rw [h2]
    rfl
  · intro htE
    obtain ⟨c, hc, hct⟩ := (hmemE t).mp htE
    have hc' : c = tC := Subtype.ext hct
    rw [hc', hνt] at hc
    exact htC1 hc
  · intro c hc
    have hcC : c ∈ C := mem_cent.mpr hc
    let c' : ↥C := ⟨c, hcC⟩
    have hν_mem : ν c' ∈ fixSub β := by rw [← hrange]; exact ⟨c', rfl⟩
    have hcases : ∀ w ∈ fixSub β, w = 1 ∨ w = tC := by
      intro w hw
      obtain ⟨y0, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fixSub β))).mp hf2
      by_cases hw1 : w = 1
      · exact Or.inl hw1
      · right
        have e1 : (⟨w, hw⟩ : ↥(fixSub β)) = y0 :=
          huniq _ (fun h' => hw1 (congrArg Subtype.val h'))
        have e2 : (⟨tC, htC_fix⟩ : ↥(fixSub β)) = y0 :=
          huniq _ (fun h' => htC1 (congrArg Subtype.val h'))
        exact congrArg Subtype.val (e1.trans e2.symm)
    rcases hcases _ hν_mem with h1 | h1
    · exact Or.inl ((hmemE c).mpr ⟨c', h1, rfl⟩)
    · right
      have hν2 : ν (c' * tC) = 1 := by rw [map_mul, h1, hνt, hsq tC]
      refine ⟨c * t, (hmemE _).mpr ⟨c' * tC, hν2, rfl⟩, ?_⟩
      calc c = c * (t * t) := by rw [h.t2, mul_one]
        _ = (c * t) * t := by rw [mul_assoc]
        _ = (t * c) * t := by rw [hc]
        _ = t * (c * t) := by rw [mul_assoc]

end L27

end CFSG.GH74.GLS.Bg.TwoGroups
