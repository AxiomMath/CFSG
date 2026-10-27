module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldDef
public import Mathlib.RingTheory.IntegralDomain

public section

namespace CFSG.GH74.GLS.SP

theorem card_pow_eq_of_isCyclic {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) (hG : Nat.card G = d * s) {g : G} (hg : g ^ s = 1) :
    Nat.card {x : G // x ^ d = g} = d := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have key : ∀ n : ℕ, 0 < n → Nat.card (powMonoidHom (α := G) n).ker ≤ n := by
    intro n hn
    have h := IsCyclic.card_pow_eq_one_le (α := G) hn
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card (powMonoidHom (α := G) n).ker
        = Fintype.card {x : G // x ^ n = 1} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquivRight fun x => by simp [MonoidHom.mem_ker]
      _ = (Finset.univ.filter fun a : G => a ^ n = 1).card := Fintype.card_subtype _
      _ ≤ n := h
  set φ : G →* G := powMonoidHom (α := G) d with hφ
  have h1 : Nat.card φ.ker * Nat.card φ.range = d * s := by
    rw [← hG, ← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  have h2 : Nat.card φ.ker ≤ d := key d hd
  have hle : φ.range ≤ (powMonoidHom (α := G) s).ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply, hφ]
    rw [← pow_mul, ← hG]
    exact pow_card_eq_one'
  have h3 : Nat.card φ.range ≤ s := le_trans (Subgroup.card_le_of_le hle) (key s hs)
  have h4 : Nat.card φ.ker = d := by
    by_contra hne
    have : Nat.card φ.ker < d := lt_of_le_of_ne h2 hne
    nlinarith
  have h5 : Nat.card φ.range = s := by
    rw [h4] at h1
    exact Nat.eq_of_mul_eq_mul_left hd h1
  have hrange : φ.range = (powMonoidHom (α := G) s).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h5]; exact key s hs)
  have hgr : g ∈ φ.range := by
    rw [hrange, MonoidHom.mem_ker]; simpa using hg
  obtain ⟨y, hy⟩ := hgr
  have hy' : y ^ d = g := hy
  refine Eq.trans (Nat.card_congr ?_) h4
  refine ⟨fun x => ⟨x.1 * y⁻¹, ?_⟩, fun z => ⟨z.1 * y, ?_⟩, ?_, ?_⟩
  · rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply, hφ]
    rw [mul_pow, inv_pow, x.2, hy', mul_inv_cancel]
  · have := z.2
    rw [MonoidHom.mem_ker] at this
    simp only [powMonoidHom_apply, hφ] at this
    show (z.1 * y) ^ d = g
    rw [mul_pow, this, one_mul, hy']
  · intro x; ext; simp
  · intro z; ext; simp

theorem exists_fixed_mul_mem_of_coprime {U : Type*} [Group U] [Finite U] (θ : U ≃* U) {r e : ℕ}
    [Fact r.Prime] (hθ : θ ^ (r ^ e) = 1) (V : Subgroup U) (hV : ∀ v ∈ V, θ v ∈ V)
    (hcop : ¬ r ∣ Nat.card V) {x : U} (hx : x⁻¹ * θ x ∈ V) :
    ∃ v ∈ V, θ (x * v) = x * v := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hmem : ∀ y : U, x⁻¹ * y ∈ V → x⁻¹ * θ y ∈ V := by
    intro y hy
    have h : x⁻¹ * θ y = (x⁻¹ * θ x) * θ (x⁻¹ * y) := by
      rw [map_mul, map_inv]; group
    rw [h]
    exact V.mul_mem hx (hV _ hy)
  have hθiter : ∀ (n : ℕ) (y : U), (θ ^ n) y = θ^[n] y := by
    intro n y
    induction n generalizing y with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]
  let g : Function.End {y : U // x⁻¹ * y ∈ V} := fun y => ⟨θ y.1, hmem y.1 y.2⟩
  have hgiter : ∀ (n : ℕ) (y : {y : U // x⁻¹ * y ∈ V}), ((g ^ n) y).1 = θ^[n] y.1 := by
    intro n y
    induction n generalizing y with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih _
  have hg : g ^ (r ^ e) = 1 := by
    funext y
    apply Subtype.ext
    rw [hgiter, ← hθiter, hθ]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := r) (n := e) hg
  have hC : Nat.card {y : U // x⁻¹ * y ∈ V} = Nat.card V :=
    Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun v => ⟨x * v.1, by simp⟩
        left_inv := fun y => by ext; simp
        right_inv := fun v => by ext; simp }
  simp only [← Nat.card_eq_fintype_card, hC] at hmod
  have hne : Nat.card (Function.fixedPoints g) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hcop ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨y, hyfix⟩⟩ := Finite.card_pos_iff.1 (Nat.pos_of_ne_zero hne)
  refine ⟨x⁻¹ * y.1, y.2, ?_⟩
  rw [mul_inv_cancel_left]
  exact congrArg Subtype.val hyfix

theorem card_fixed_frob_twist {k : Type*} [Field k] [Finite k] {p f m : ℕ} [Fact p.Prime]
    [CharP k p] (hm : 0 < m) (hf : 0 < f) (hk : Nat.card k = (p ^ f) ^ m) (ν : kˣ)
    (hν : ν ^ (∑ i ∈ Finset.range m, (p ^ f) ^ i) = 1) :
    Nat.card {a : k // (ν : k) * a ^ (p ^ f) = a} = p ^ f := by
  classical
  have hr2 : 2 ≤ p ^ f :=
    le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow hf.ne' p)
  generalize p ^ f = r at hr2 hk hν ⊢
  obtain ⟨d, rfl⟩ : ∃ d, r = d + 1 := ⟨r - 1, by omega⟩
  have hd : 0 < d := by omega
  have hgeom : ∀ n : ℕ, d * (∑ i ∈ Finset.range n, (d + 1) ^ i) + 1 = (d + 1) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ (d + 1) n, mul_add, add_right_comm, ih]
      ring
  have hs : 0 < ∑ i ∈ Finset.range m, (d + 1) ^ i :=
    Finset.sum_pos (fun i _ => pow_pos (by omega) i) (Finset.nonempty_range_iff.2 hm.ne')
  have hG : Nat.card kˣ = d * ∑ i ∈ Finset.range m, (d + 1) ^ i := by
    rw [Nat.card_units, hk]
    have := hgeom m
    omega
  have hg : ν⁻¹ ^ (∑ i ∈ Finset.range m, (d + 1) ^ i) = 1 := by
    rw [inv_pow, hν, inv_one]
  have hA := card_pow_eq_of_isCyclic (G := kˣ) hd hs hG hg
  have h0 : (ν : k) * (0 : k) ^ (d + 1) = 0 := by simp
  have hx : ∀ x : kˣ, x ^ d = ν⁻¹ → (ν : k) * (x : k) ^ (d + 1) = x := by
    intro x hx
    have h : (ν * x ^ (d + 1) : kˣ) = x := by
      calc ν * x ^ (d + 1) = ν * (x ^ d * x) := by rw [pow_succ]
        _ = ν * (ν⁻¹ * x) := by rw [hx]
        _ = x := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    simpa using congrArg Units.val h
  have e : Option {x : kˣ // x ^ d = ν⁻¹} ≃ {a : k // (ν : k) * a ^ (d + 1) = a} := by
    refine Equiv.ofBijective
      (fun o => match o with
        | none => ⟨0, h0⟩
        | some x => ⟨(x.1 : k), hx x.1 x.2⟩) ⟨?_, ?_⟩
    · rintro (_ | ⟨x, hx⟩) (_ | ⟨y, hy⟩) h
      · rfl
      · exact absurd (congrArg Subtype.val h).symm y.ne_zero
      · exact absurd (congrArg Subtype.val h) x.ne_zero
      · have := Units.ext (congrArg Subtype.val h)
        subst this
        rfl
    · rintro ⟨a, ha⟩
      by_cases ha0 : a = 0
      · subst ha0
        exact ⟨none, rfl⟩
      · set u : kˣ := Units.mk0 a ha0 with hu
        have h2 : (ν * u ^ d) * u = 1 * u := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_pow_eq_pow_val, one_mul, hu, Units.val_mk0]
          calc (ν : k) * a ^ d * a = ν * (a ^ d * a) := mul_assoc _ _ _
            _ = ν * a ^ (d + 1) := by rw [pow_succ]
            _ = a := ha
        have h1 : ν * u ^ d = 1 := mul_right_cancel h2
        exact ⟨some ⟨u, eq_inv_of_mul_eq_one_right h1⟩, rfl⟩
  rw [← Nat.card_congr e, Finite.card_option, hA]

theorem card_fixed_eq_mul {U : Type*} [Group U] [Finite U] (θ : U ≃* U) {r e : ℕ} [Fact r.Prime]
    (hθ : θ ^ (r ^ e) = 1) (V : Subgroup U) [V.Normal] (hV : ∀ v ∈ V, θ v ∈ V)
    (hcop : ¬ r ∣ Nat.card V) :
    Nat.card ↥(foldFix θ) = Nat.card ↥(V ⊓ foldFix θ) *
      Nat.card {x : U ⧸ V // QuotientGroup.map V V θ.toMonoidHom (fun v hv => hV v hv) x = x} := by
  classical
  have hmap : ∀ x : U, QuotientGroup.map V V θ.toMonoidHom (fun v hv => hV v hv)
      (x : U ⧸ V) = ((θ x : U) : U ⧸ V) :=
    fun x => QuotientGroup.map_mk V V θ.toMonoidHom (fun v hv => hV v hv) x
  let π : foldFix θ →* U ⧸ V := (QuotientGroup.mk' V).comp (foldFix θ).subtype
  have hrange : ∀ q : U ⧸ V, q ∈ π.range ↔
      QuotientGroup.map V V θ.toMonoidHom (fun v hv => hV v hv) q = q := by
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    constructor
    · rintro ⟨y, hy⟩
      have hy' : ((y : U) : U ⧸ V) = (x : U ⧸ V) := hy
      rw [← hy', hmap, mem_foldFix.1 y.2]
    · intro h
      rw [hmap] at h
      obtain ⟨v, hv, hfix⟩ :=
        exists_fixed_mul_mem_of_coprime θ hθ V hV hcop (QuotientGroup.eq.1 h.symm)
      refine ⟨⟨x * v, hfix⟩, ?_⟩
      show (((x * v : U)) : U ⧸ V) = (x : U ⧸ V)
      exact (QuotientGroup.eq.2 (by rwa [inv_mul_cancel_left])).symm
  have hker : ∀ y : foldFix θ, y ∈ π.ker ↔ (y : U) ∈ V := by
    intro y
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff (y : U)
  have hcard : Nat.card π.ker = Nat.card ↥(V ⊓ foldFix θ) :=
    Nat.card_congr
      { toFun := fun y => ⟨y.1.1, Subgroup.mem_inf.2 ⟨(hker y.1).1 y.2, y.1.2⟩⟩
        invFun := fun u => ⟨⟨u.1, (Subgroup.mem_inf.1 u.2).2⟩,
          (hker ⟨u.1, (Subgroup.mem_inf.1 u.2).2⟩).2 (Subgroup.mem_inf.1 u.2).1⟩
        left_inv := fun y => rfl
        right_inv := fun u => rfl }
  have hmul : Nat.card ↥(foldFix θ) = Nat.card π.ker * Nat.card π.range := by
    rw [← Subgroup.index_ker π]
    exact (Subgroup.card_mul_index π.ker).symm
  rw [hmul, hcard]
  exact congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight hrange))

end CFSG.GH74.GLS.SP
