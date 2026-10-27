module

public import CFSG.GH74.GLS.Bg.TwoGroups.L26Cop
public import CFSG.GH74.GLS.Bg.TwoGroups.L26Quot
public import CFSG.GH74.GLS.Bg.TwoGroups.L26Abel
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

structure Cfg (T : Type) [Group T] (α t : MulAut T) (E : Subgroup T) : Prop where
  p2 : IsPGroup 2 T
  a3 : α ^ 3 = 1
  t2 : t * t = 1
  comm : α * t = t * α
  hE : ∀ g, g ∈ E ↔ t g = g
  E2 : ∀ e ∈ E, e * e = 1
  Ec : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  Ecard : Nat.card E = 4
  Efpf : ∀ e ∈ E, α e = e → e = 1

variable {T : Type} [Group T] {α t : MulAut T} {E : Subgroup T}

theorem Cfg.Einv (cfg : Cfg T α t E) : ∀ e ∈ E, α e ∈ E := by
  intro e he
  rw [cfg.hE] at he ⊢
  have := congrArg (fun s : MulAut T => s e) cfg.comm
  simp only [MulAut.mul_apply] at this
  rw [← this, he]

theorem Cfg.tt (cfg : Cfg T α t E) (g : T) : t (t g) = g := by
  have := congrArg (fun s : MulAut T => s g) cfg.t2
  simpa using this

theorem Cfg.alpha_inv (cfg : Cfg T α t E) (g : T) : α⁻¹ g = α (α g) := by
  have h : α * α * α = 1 := by rw [← pow_three']; exact cfg.a3
  have h2 : α⁻¹ = α * α := by
    calc α⁻¹ = α⁻¹ * (α * α * α) := by rw [h, mul_one]
      _ = α * α := by group
  rw [h2]; rfl

theorem center_invariant (f : MulAut T) : ∀ z ∈ Subgroup.center T, f z ∈ Subgroup.center T := by
  intro z hz
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := f.surjective g
  rw [← map_mul, ← map_mul, hz g']

variable [Finite T]

theorem Cfg.hfix (cfg : Cfg T α t E) : ∀ g : T, α g = g → g = 1 := by
  intro g hg
  by_contra hg1
  have hC : ∀ v ∈ fixSub α, t v ∈ fixSub α := by
    intro v hv
    show α (t v) = t v
    have := congrArg (fun s : MulAut T => s v) cfg.comm
    simp only [MulAut.mul_apply] at this
    rw [this]
    exact congrArg t (hv : α v = v)
  have hne : fixSub α ≠ ⊥ := by
    intro h
    apply hg1
    have : g ∈ fixSub α := hg
    rw [h] at this
    simpa using this
  obtain ⟨v, hv, hv1, htv⟩ := exists_fixed_nontrivial cfg.p2 t cfg.t2 (fixSub α) hC hne
  exact hv1 (cfg.Efpf v ((cfg.hE v).mpr htv) hv)

omit [Finite T] in
theorem klein_orbit (cfg : Cfg T α t E) (z : T) (hz : z ∈ E) (hz1 : z ≠ 1) :
    ∀ w ∈ E, w = 1 ∨ w = z ∨ w = α z ∨ w = z * α z := by
  have hαz : α z ∈ E := cfg.Einv z hz
  have hαz1 : α z ≠ 1 := fun h => hz1 (by simpa using h)
  have hne : α z ≠ z := fun h => hz1 (cfg.Efpf z hz h)
  have hprod1 : z * α z ≠ 1 := by
    intro h
    apply hne
    have : α z = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (eq_inv_of_mul_eq_one_left (cfg.E2 z hz)).symm
  exact L23.subgroup_card_four E cfg.Ecard z (α z) (z * α z) hz hαz (mul_mem hz hαz)
    (Ne.symm hz1) (Ne.symm hαz1) (Ne.symm hprod1) (Ne.symm hne)
    (fun h => hαz1 (mul_eq_left.mp h.symm)) (fun h => hz1 (mul_eq_right.mp h.symm))

theorem Cfg.Ecen (cfg : Cfg T α t E) : ∀ e ∈ E, ∀ g : T, e * g = g * e := by
  have hEn : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [cfg.Ecard]; norm_num)
  obtain ⟨e₀, he₀⟩ := exists_ne (1 : E)
  have hTn : Nontrivial T := ⟨⟨e₀, 1, fun h => he₀ (Subtype.ext h)⟩⟩
  have hcn : Nontrivial (Subgroup.center T) := IsPGroup.center_nontrivial cfg.p2
  have hne : Subgroup.center T ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hcn
  obtain ⟨z, hzc, hz1, htz⟩ := exists_fixed_nontrivial cfg.p2 t cfg.t2 (Subgroup.center T)
    (center_invariant t) hne
  have hzE : z ∈ E := (cfg.hE z).mpr htz
  have hαzc : α z ∈ Subgroup.center T := center_invariant α z hzc
  intro e he g
  rcases klein_orbit cfg z hzE hz1 e he with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact ((Subgroup.mem_center_iff.mp hzc) g).symm
  · rw [h]; exact ((Subgroup.mem_center_iff.mp hαzc) g).symm
  · rw [h]; exact ((Subgroup.mem_center_iff.mp (mul_mem hzc hαzc)) g).symm

@[expose] def tHom (t : MulAut T) (V : Subgroup T) (hVt : ∀ v ∈ V, t v ∈ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) : V →* V where
  toFun v := ⟨v * t v, mul_mem v.2 (hVt v v.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    show (a : T) * b * t (a * b) = (a * t a) * (b * t b)
    rw [map_mul]
    have h := hVc b b.2 (t a) (hVt a a.2)
    calc (a : T) * b * (t a * t b) = a * (b * t a) * t b := by simp only [mul_assoc]
      _ = a * (t a * b) * t b := by rw [h]
      _ = (a * t a) * (b * t b) := by simp only [mul_assoc]

theorem Cfg.noV (cfg : Cfg T α t E) (V : Subgroup T) (hVt : ∀ v ∈ V, t v ∈ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a * a = 1)
    (hV16 : Nat.card V = 16) : V = ⊤ := by
  by_contra hne
  obtain ⟨x', hx'V, hx'⟩ := exists_coset_fixed cfg.p2 t cfg.t2 V hVt hne
  let θ : V →* V := tHom t V hVt hVc
  have hθ : ∀ v : V, (θ v : T) = v * t v := fun v => rfl
  have hker : ∀ v : V, θ v = 1 → t v = v := by
    intro v hv
    have h1 : (v : T) * t v = 1 := by rw [← hθ]; exact congrArg Subtype.val hv
    have h2 : t v = (v : T)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact (eq_inv_of_mul_eq_one_left (hV2 v v.2)).symm
  have hrange : ∀ v : V, t (θ v : T) = θ v := by
    intro v
    rw [hθ, map_mul, cfg.tt]
    exact hVc _ (hVt v v.2) _ v.2
  have hcard := Subgroup.card_ker_mul_card_range θ
  rw [hV16] at hcard
  have hkE : ∀ v : θ.ker, (v.1.1 : T) ∈ E := fun v => (cfg.hE _).mpr (hker v.1 v.2)
  have hrE : ∀ w : θ.range, (w.1.1 : T) ∈ E := by
    rintro ⟨w, v, rfl⟩
    exact (cfg.hE _).mpr (hrange v)
  let fk : θ.ker → E := fun v => ⟨v.1.1, hkE v⟩
  let fr : θ.range → E := fun w => ⟨w.1.1, hrE w⟩
  have hfk : Function.Injective fk := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun e : E => (e : T)) h))
  have hfr : Function.Injective fr := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun e : E => (e : T)) h))
  have hk4 : Nat.card θ.ker ≤ 4 := by
    have := Nat.card_le_card_of_injective fk hfk
    rwa [cfg.Ecard] at this
  have hr4 : Nat.card θ.range ≤ 4 := by
    have := Nat.card_le_card_of_injective fr hfr
    rwa [cfg.Ecard] at this
  have hk : Nat.card θ.ker = 4 ∧ Nat.card θ.range = 4 := by
    generalize Nat.card θ.ker = k at *
    generalize Nat.card θ.range = r at *
    interval_cases k <;> interval_cases r <;> omega
  have hbk : Function.Bijective fk :=
    hfk.bijective_of_nat_card_le (by rw [cfg.Ecard, hk.1])
  have hbr : Function.Bijective fr :=
    hfr.bijective_of_nat_card_le (by rw [cfg.Ecard, hk.2])
  have hEV : E ≤ V := by
    intro e he
    obtain ⟨v, hv⟩ := hbk.2 ⟨e, he⟩
    have : (v.1.1 : T) = e := congrArg (fun e : E => (e : T)) hv
    rw [← this]
    exact v.1.2
  set v₀ : T := x'⁻¹ * t x' with hv₀
  have hv₀E : v₀ ∈ E := by
    rw [cfg.hE]
    have h1 : t v₀ = (t x')⁻¹ * x' := by
      rw [hv₀, map_mul, map_inv, cfg.tt]
    rw [h1]
    have h2 : v₀ * v₀ = 1 := hV2 v₀ hx'
    have h3 : v₀⁻¹ = v₀ := (eq_inv_of_mul_eq_one_left h2).symm
    rw [← h3, hv₀]
    group
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := hbr.2 ⟨v₀, hv₀E⟩
  have hav : ((θ a : V) : T) = v₀ := congrArg (fun e : E => (e : T)) ha
  rw [hθ] at hav
  have hy : t (x' * a) = x' * a := by
    have h1 : t x' = x' * v₀ := by rw [hv₀]; group
    rw [map_mul, h1, ← hav]
    have h2 : t (a : T) * t a = 1 := hV2 _ (hVt a a.2)
    calc x' * (a * t a) * t a = x' * a * (t a * t a) := by simp only [mul_assoc]
      _ = x' * a := by rw [h2, mul_one]
  have hyV : x' * a ∈ V := hEV ((cfg.hE _).mpr hy)
  exact hx'V (by simpa using mul_mem hyV (inv_mem a.2))

@[expose] def IsA (α t : MulAut T) (A : Subgroup T) : Prop :=
  A.Normal ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, t a ∈ A ∧ α a ∈ A)

theorem Cfg.exists_maxA (cfg : Cfg T α t E) :
    ∃ A : Subgroup T, IsA α t A ∧ E ≤ A ∧ ∀ B : Subgroup T, IsA α t B → A ≤ B → B = A := by
  classical
  have hE : IsA α t E := by
    refine ⟨⟨fun n hn g => ?_⟩, cfg.Ec, fun a ha => ⟨?_, cfg.Einv a ha⟩⟩
    · have := cfg.Ecen n hn g
      have h : g * n * g⁻¹ = n := by rw [← this]; group
      rw [h]; exact hn
    · have := (cfg.hE a).mp ha
      rw [this]; exact ha
  let S := {A : Subgroup T // IsA α t A ∧ E ≤ A}
  have : Nonempty S := ⟨⟨E, hE, le_rfl⟩⟩
  obtain ⟨⟨A, hA, hEA⟩, hmax⟩ := Finite.exists_max (fun A : S => Nat.card A.1)
  refine ⟨A, hA, hEA, fun B hB hAB => ?_⟩
  have hBS : IsA α t B ∧ E ≤ B := ⟨hB, hEA.trans hAB⟩
  have := hmax ⟨B, hBS⟩
  exact (Subgroup.eq_of_le_of_card_ge hAB this).symm

theorem Cfg.quot_fpf (cfg : Cfg T α t E) (N : Subgroup T) [N.Normal] (hN : ∀ n ∈ N, α n ∈ N)
    (y : T ⧸ N) (hy : quotAut N α hN y = y) : y = 1 := by
  induction y using QuotientGroup.induction_on with
  | _ g =>
    rw [quotAut_mk] at hy
    have h1 : g⁻¹ * α g ∈ N := QuotientGroup.eq.mp hy.symm
    obtain ⟨s, hs, hαs⟩ := exists_fixed_coset3 cfg.p2 α 1 (by rw [pow_one]; exact cfg.a3) N hN g h1
    have : s = 1 := cfg.hfix s hαs
    rw [this, mul_one] at hs
    have : g ∈ N := by simpa using N.inv_mem hs
    exact (QuotientGroup.eq_one_iff g).mpr this

theorem Cfg.exists_x (cfg : Cfg T α t E) (A : Subgroup T) [hAn : A.Normal]
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAi : ∀ a ∈ A, t a ∈ A ∧ α a ∈ A) (c : T) (hcC : c ∈ Subgroup.centralizer (A : Set T))
    (hcA : c ∉ A) :
    ∃ x : T, x ∈ Subgroup.centralizer (A : Set T) ∧ x ∉ A ∧ (∀ g : T, g * x * g⁻¹ * x⁻¹ ∈ A) ∧
      x⁻¹ * t x ∈ A ∧ x * α x * α (α x) ∈ A := by
  set C := Subgroup.centralizer (A : Set T) with hCdef
  have hAt : ∀ n ∈ A, t n ∈ A := fun n hn => (hAi n hn).1
  have hAα : ∀ n ∈ A, α n ∈ A := fun n hn => (hAi n hn).2
  have hCn : C.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hCdef, Subgroup.mem_centralizer_iff] at hn ⊢
    intro a ha
    have h1 := hn (g⁻¹ * a * g) (by simpa [mul_assoc] using hAn.conj_mem a ha g⁻¹)
    calc a * (g * n * g⁻¹) = g * ((g⁻¹ * a * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = g * n * g⁻¹ * a := by group
  have hCt : ∀ n ∈ C, t n ∈ C := by
    intro n hn
    rw [hCdef, Subgroup.mem_centralizer_iff] at hn ⊢
    intro a ha
    have h1 := hn (t a) (hAt a ha)
    calc a * t n = t (t a) * t n := by rw [cfg.tt]
      _ = t (t a * n) := by rw [map_mul]
      _ = t (n * t a) := by rw [h1]
      _ = t n * a := by rw [map_mul, cfg.tt]
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => hAc b hb a ha)
  let tb := quotAut A t hAt
  let ab := quotAut A α hAα
  have hp2 : IsPGroup 2 (T ⧸ A) := cfg.p2.to_quotient A
  have htb2 : tb * tb = 1 := by
    have := quotAut_pow_eq_one A t hAt 2 (by rw [pow_two]; exact cfg.t2)
    rwa [pow_two] at this
  have hab3 : ab ^ 3 = 1 := quotAut_pow_eq_one A α hAα 3 cfg.a3
  let N : Subgroup (T ⧸ A) := C.map (QuotientGroup.mk' A)
  have hNn : N.Normal := hCn.map (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
  have hNbot : N ≠ ⊥ := by
    intro h
    have hmem : (QuotientGroup.mk c : T ⧸ A) ∈ N := ⟨c, hcC, rfl⟩
    rw [h] at hmem
    exact hcA ((QuotientGroup.eq_one_iff c).mp (by simpa using hmem))
  have : Group.IsNilpotent (T ⧸ A) := hp2.isNilpotent
  have hV := Group.IsNilpotent.inf_center_ne_bot_of_normal hNbot
  have hVt : ∀ v ∈ N ⊓ Subgroup.center (T ⧸ A), tb v ∈ N ⊓ Subgroup.center (T ⧸ A) := by
    rintro v ⟨⟨c', hc', rfl⟩, hvc⟩
    refine ⟨⟨t c', hCt c' hc', ?_⟩, center_invariant tb _ hvc⟩
    show QuotientGroup.mk (t c') = tb (QuotientGroup.mk c')
    rw [quotAut_mk]
  obtain ⟨m, ⟨⟨c', hc', hcm⟩, hmc⟩, hm1, htm⟩ :=
    exists_fixed_nontrivial hp2 tb htb2 _ hVt hV
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective m
  have hc'' : QuotientGroup.mk c' = (QuotientGroup.mk x : T ⧸ A) := hcm
  have hxC : x ∈ C := by
    have h1 : c'⁻¹ * x ∈ A := QuotientGroup.eq.mp hc''
    have : x = c' * (c'⁻¹ * x) := by group
    rw [this]
    exact mul_mem hc' (hAC h1)
  have hmcen := Subgroup.mem_center_iff.mp hmc
  refine ⟨x, hxC, ?_, ?_, ?_, ?_⟩
  · intro hxA
    exact hm1 ((QuotientGroup.eq_one_iff x).mpr hxA)
  · intro g
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h := hmcen (QuotientGroup.mk g)
    rw [h]
    group
  · have h1 : quotAut A t hAt (QuotientGroup.mk x) = QuotientGroup.mk (t x) :=
      quotAut_mk A t hAt x
    have h2 : (QuotientGroup.mk x : T ⧸ A) = QuotientGroup.mk (t x) := by
      rw [← h1]; exact htm.symm
    exact QuotientGroup.eq.mp h2
  · set m₀ : T ⧸ A := QuotientGroup.mk x with hm₀
    set m₁ : T ⧸ A := ab m₀ with hm₁
    set m₂ : T ⧸ A := ab m₁ with hm₂
    have hc1 : m₁ ∈ Subgroup.center (T ⧸ A) := center_invariant ab _ hmc
    have hc2 : m₂ ∈ Subgroup.center (T ⧸ A) := center_invariant ab _ hc1
    have h3 : ab m₂ = m₀ := by
      have := congrArg (fun s : MulAut (T ⧸ A) => s m₀) hab3
      simpa [pow_succ, MulAut.mul_apply, hm₂, hm₁] using this
    have hw : ab (m₀ * m₁ * m₂) = m₀ * m₁ * m₂ := by
      rw [map_mul, map_mul, h3]
      have e1 := hmcen (m₁ * m₂)
      calc ab m₀ * ab m₁ * m₀ = m₁ * m₂ * m₀ := rfl
        _ = m₀ * (m₁ * m₂) := e1
        _ = m₀ * m₁ * m₂ := by rw [mul_assoc]
    have hw1 := cfg.quot_fpf A hAα _ hw
    have hmk : (QuotientGroup.mk (x * α x * α (α x)) : T ⧸ A) = m₀ * m₁ * m₂ := by
      have e1 : (QuotientGroup.mk (α x) : T ⧸ A) = m₁ := (quotAut_mk A α hAα x).symm
      have e2 : (QuotientGroup.mk (α (α x)) : T ⧸ A) = m₂ := by
        rw [hm₂, ← e1]; exact (quotAut_mk A α hAα (α x)).symm
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, e1, e2]
    rw [← QuotientGroup.eq_one_iff, hmk]
    exact hw1

omit [Finite T] in
theorem Cfg.centralizer_inv (cfg : Cfg T α t E) (A : Subgroup T)
    (hAi : ∀ a ∈ A, t a ∈ A ∧ α a ∈ A) :
    ∀ n ∈ Subgroup.centralizer (A : Set T), t n ∈ Subgroup.centralizer (A : Set T) ∧
      α n ∈ Subgroup.centralizer (A : Set T) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  refine ⟨?_, ?_⟩
  · intro a ha
    have h1 := hn (t a) (hAi a ha).1
    calc a * t n = t (t a) * t n := by rw [cfg.tt]
      _ = t (t a * n) := by rw [map_mul]
      _ = t (n * t a) := by rw [h1]
      _ = t n * a := by rw [map_mul, cfg.tt]
  · intro a ha
    have hinv : α⁻¹ a ∈ A := by rw [cfg.alpha_inv]; exact (hAi _ (hAi a ha).2).2
    have h1 := hn (α⁻¹ a) hinv
    have hαa : α (α⁻¹ a) = a := by simp
    calc a * α n = α (α⁻¹ a) * α n := by rw [hαa]
      _ = α (α⁻¹ a * n) := by rw [map_mul]
      _ = α (n * α⁻¹ a) := by rw [h1]
      _ = α n * a := by rw [map_mul, hαa]

theorem Cfg.centralizer_le (cfg : Cfg T α t E) (A : Subgroup T) (hA : IsA α t A)
    (hmax : ∀ B : Subgroup T, IsA α t B → A ≤ B → B = A) :
    Subgroup.centralizer (A : Set T) ≤ A := by
  obtain ⟨hAn, hAc, hAi⟩ := hA
  have hAα : ∀ n ∈ A, α n ∈ A := fun n hn => (hAi n hn).2
  have hAt : ∀ n ∈ A, t n ∈ A := fun n hn => (hAi n hn).1
  by_contra hne
  have hex : ∃ c ∈ Subgroup.centralizer (A : Set T), c ∉ A := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hne (fun c hc => h c hc)
  obtain ⟨c, hcC, hcA⟩ := hex
  obtain ⟨x, hxC, hxA, hx2, hx3, hx4⟩ := cfg.exists_x A hAc hAi c hcC hcA
  set C := Subgroup.centralizer (A : Set T) with hCdef
  set y : T := α x with hy
  set z : T := α y with hz
  have hyC : y ∈ C := (cfg.centralizer_inv A hAi x hxC).2
  have hzC : z ∈ C := (cfg.centralizer_inv A hAi y hyC).2
  set u : T := x * y * z with hu
  have huA : u ∈ A := hx4
  have hxy : x * y = y * x := by
    set c₀ : T := x⁻¹ * y⁻¹ * x * y with hc₀
    have hd : y⁻¹ * x * y * x⁻¹ ∈ A := by
      have := hx2 y⁻¹
      simpa using this
    have hc₀A : c₀ ∈ A := by
      have := hAn.conj_mem _ hd x⁻¹
      have e : x⁻¹ * (y⁻¹ * x * y * x⁻¹) * x⁻¹⁻¹ = c₀ := by rw [hc₀]; group
      rwa [e] at this
    have hcx : c₀ * x = x * c₀ := (Subgroup.mem_centralizer_iff.mp hxC) c₀ hc₀A
    have hw : x * y * x⁻¹ ∈ C := mul_mem (mul_mem hxC hyC) (inv_mem hxC)
    have huw : u * (x * y * x⁻¹) = (x * y * x⁻¹) * u :=
      (Subgroup.mem_centralizer_iff.mp hw) u huA
    have hzu : z = y⁻¹ * x⁻¹ * u := by rw [hu]; group
    have h2 : z⁻¹ * y * z = x * y * x⁻¹ := by
      calc z⁻¹ * y * z = u⁻¹ * (x * y * x⁻¹) * u := by rw [hzu]; group
        _ = x * y * x⁻¹ := by rw [mul_assoc, ← huw, inv_mul_cancel_left]
    have h1 : α c₀ = y⁻¹ * (z⁻¹ * y * z) := by
      rw [hc₀]
      simp only [map_mul, map_inv]
      rw [← hy, ← hz]
      group
    have hαc : α c₀ = c₀ := by
      rw [h1, h2]
      calc y⁻¹ * (x * y * x⁻¹) = x * c₀ * x⁻¹ := by rw [hc₀]; group
        _ = c₀ := by rw [← hcx]; group
    have hc1 : c₀ = 1 := cfg.hfix c₀ hαc
    calc x * y = y * (y⁻¹ * x * y) := by group
      _ = y * x := by
        have : y⁻¹ * x * y = x := by
          calc y⁻¹ * x * y = x * (x⁻¹ * y⁻¹ * x * y) := by group
            _ = x := by rw [← hc₀, hc1, mul_one]
        rw [this]
  let H : Subgroup T := Subgroup.closure ((A : Set T) ∪ {x, y})
  have hsub : ∀ s ∈ (A : Set T) ∪ {x, y}, ∀ s' ∈ (A : Set T) ∪ {x, y}, s * s' = s' * s := by
    have hAx : ∀ a ∈ A, a * x = x * a := fun a ha => (Subgroup.mem_centralizer_iff.mp hxC) a ha
    have hAy : ∀ a ∈ A, a * y = y * a := fun a ha => (Subgroup.mem_centralizer_iff.mp hyC) a ha
    intro s hs s' hs'
    rcases hs with hs | hs <;> rcases hs' with hs' | hs'
    · exact hAc s hs s' hs'
    · rcases hs' with h | h
      · rw [h]; exact hAx s hs
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact hAy s hs
    · rcases hs with h | h
      · rw [h]; exact (hAx s' hs').symm
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact (hAy s' hs').symm
    · rcases hs with h | h <;> rcases hs' with h' | h'
      · rw [h, h']
      · rw [Set.mem_singleton_iff] at h'; rw [h, h']; exact hxy
      · rw [Set.mem_singleton_iff] at h; rw [h, h']; exact hxy.symm
      · rw [Set.mem_singleton_iff] at h h'; rw [h, h']
  have hHcomm : ∀ h ∈ H, ∀ h' ∈ H, h * h' = h' * h := by
    have hpair : Set.Pairwise ((A : Set T) ∪ {x, y}) Commute :=
      fun s hs s' hs' _ => hsub s hs s' hs'
    have hc : IsMulCommutative H := Subgroup.isMulCommutative_closure hpair
    intro h hh h' hh'
    exact congrArg Subtype.val (hc.is_comm.comm (⟨h, hh⟩ : H) ⟨h', hh'⟩)
  have hAH : A ≤ H := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hxH : x ∈ H := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hyH : y ∈ H := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hx2y : ∀ g : T, g * y * g⁻¹ * y⁻¹ ∈ A := by
    intro g
    have h1 := hx2 (α⁻¹ g)
    have h2 := hAα _ h1
    have e : α (α⁻¹ g * x * (α⁻¹ g)⁻¹ * x⁻¹) = g * y * g⁻¹ * y⁻¹ := by
      simp only [map_mul, map_inv]
      simp [hy]
    rwa [e] at h2
  have hHn : H.Normal := by
    refine ⟨fun h hh g => ?_⟩
    induction hh using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with hs | hs
      · exact hAH (hAn.conj_mem s hs g)
      · rcases hs with h | h
        · rw [h]
          have : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
          rw [this]; exact mul_mem (hAH (hx2 g)) hxH
        · rw [Set.mem_singleton_iff] at h
          rw [h]
          have : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
          rw [this]; exact mul_mem (hAH (hx2y g)) hyH
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]; exact mul_mem ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem ha
  have hHt : ∀ h ∈ H, t h ∈ H := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with hs | hs
      · exact hAH (hAt s hs)
      · rcases hs with h | h
        · rw [h]
          have : t x = x * (x⁻¹ * t x) := by group
          rw [this]; exact mul_mem hxH (hAH hx3)
        · rw [Set.mem_singleton_iff] at h
          rw [h]
          have h1 : t y = α (t x) := by
            have := congrArg (fun f : MulAut T => f x) cfg.comm
            simp only [MulAut.mul_apply] at this
            rw [hy, ← this]
          have : t x = x * (x⁻¹ * t x) := by group
          rw [h1, this, map_mul, ← hy]
          exact mul_mem hyH (hAH (hAα _ hx3))
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  have hHα : ∀ h ∈ H, α h ∈ H := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with hs | hs
      · exact hAH (hAα s hs)
      · rcases hs with h | h
        · rw [h]; exact hyH
        · rw [Set.mem_singleton_iff] at h
          rw [h]
          have : α y = y⁻¹ * x⁻¹ * u := by
            have : z = y⁻¹ * x⁻¹ * u := by rw [hu]; group
            exact this
          rw [this]
          exact mul_mem (mul_mem (inv_mem hyH) (inv_mem hxH)) (hAH huA)
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  have hHA : IsA α t H := ⟨hHn, hHcomm, fun h hh => ⟨hHt h hh, hHα h hh⟩⟩
  have := hmax H hHA hAH
  exact hxA (by rw [← this]; exact hxH)

theorem Cfg.card_V_le (cfg : Cfg T α t E) (V : Subgroup T) (hVt : ∀ v ∈ V, t v ∈ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a * a = 1) :
    Nat.card V ≤ 16 := by
  let θ : V →* V := tHom t V hVt hVc
  have hθ : ∀ v : V, (θ v : T) = v * t v := fun v => rfl
  have hker : ∀ v : V, θ v = 1 → t v = v := by
    intro v hv
    have h1 : (v : T) * t v = 1 := by rw [← hθ]; exact congrArg Subtype.val hv
    have h2 : t v = (v : T)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact (eq_inv_of_mul_eq_one_left (hV2 v v.2)).symm
  have hrange : ∀ v : V, t (θ v : T) = θ v := by
    intro v
    rw [hθ, map_mul, cfg.tt]
    exact hVc _ (hVt v v.2) _ v.2
  have hcard := Subgroup.card_ker_mul_card_range θ
  have hkE : ∀ v : θ.ker, (v.1.1 : T) ∈ E := fun v => (cfg.hE _).mpr (hker v.1 v.2)
  have hrE : ∀ w : θ.range, (w.1.1 : T) ∈ E := by
    rintro ⟨w, v, rfl⟩
    exact (cfg.hE _).mpr (hrange v)
  let fk : θ.ker → E := fun v => ⟨v.1.1, hkE v⟩
  let fr : θ.range → E := fun w => ⟨w.1.1, hrE w⟩
  have hfk : Function.Injective fk := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun e : E => (e : T)) h))
  have hfr : Function.Injective fr := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun e : E => (e : T)) h))
  have hk4 : Nat.card θ.ker ≤ 4 := by
    have := Nat.card_le_card_of_injective fk hfk
    rwa [cfg.Ecard] at this
  have hr4 : Nat.card θ.range ≤ 4 := by
    have := Nat.card_le_card_of_injective fr hfr
    rwa [cfg.Ecard] at this
  rw [← hcard]
  exact (Nat.mul_le_mul hk4 hr4)

theorem Cfg.omega1 (cfg : Cfg T α t E) (A : Subgroup T) (hA : IsA α t A)
    (hEA : E ≤ A)
    (hno : ∀ V : Subgroup T, (∀ v ∈ V, t v ∈ V) → (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) →
      (∀ a ∈ V, a * a = 1) → Nat.card V = 16 → False) :
    ∀ a ∈ A, a * a = 1 → a ∈ E := by
  obtain ⟨hAn, hAc, hAi⟩ := hA
  let V : Subgroup T :=
    { carrier := {a | a ∈ A ∧ a * a = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
          _ = a * (a * b) * b := by rw [hAc b hb a ha]
          _ = (a * a) * (b * b) := by simp only [mul_assoc]
          _ = 1 := by rw [ha2, hb2, one_mul]
      one_mem' := ⟨one_mem A, mul_one 1⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨inv_mem ha, ?_⟩
        have : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha2).symm
        rw [this]; exact ha2 }
  have hVmem : ∀ a, a ∈ V ↔ a ∈ A ∧ a * a = 1 := fun a => Iff.rfl
  have hVt : ∀ v ∈ V, t v ∈ V := by
    intro v hv
    rw [hVmem] at hv ⊢
    refine ⟨(hAi v hv.1).1, ?_⟩
    rw [← map_mul, hv.2, map_one]
  have hVα : ∀ v ∈ V, α v ∈ V := by
    intro v hv
    rw [hVmem] at hv ⊢
    refine ⟨(hAi v hv.1).2, ?_⟩
    rw [← map_mul, hv.2, map_one]
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hAc a ha.1 b hb.1
  have hV2 : ∀ a ∈ V, a * a = 1 := fun a ha => ha.2
  have hEV : E ≤ V := fun e he => ⟨hEA he, cfg.E2 e he⟩
  have hle := cfg.card_V_le V hVt hVc hV2
  have hge : 4 ≤ Nat.card V := by
    have := Subgroup.card_le_of_le hEV
    rwa [cfg.Ecard] at this
  have hmod := card_fix_modEq3 α 1 (by rw [pow_one]; exact cfg.a3) V hVα
  have hfixcard : Nat.card {v : V // α v = v} = 1 := by
    have : Unique {v : V // α v = v} :=
      { default := ⟨1, map_one α⟩
        uniq := fun v => Subtype.ext (Subtype.ext (cfg.hfix v.1.1 v.2)) }
    exact Nat.card_unique
  rw [hfixcard] at hmod
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (cfg.p2.to_subgroup V)
  have hmod1 : Nat.card V % 3 = 1 := hmod
  rw [hn] at hle hge hmod1
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hVE : Nat.card V = 4 := by
    interval_cases n
    · omega
    · omega
    · rw [hn]; norm_num
    · omega
    · exfalso
      exact hno V hVt hVc hV2 (by rw [hn]; norm_num)
  intro a ha ha2
  have : V = E := (Subgroup.eq_of_le_of_card_ge hEV (by rw [hVE, cfg.Ecard])).symm
  rw [← this]
  exact ⟨ha, ha2⟩

theorem Cfg.quot (cfg : Cfg T α t E) [hEn : E.Normal] (hEtop : E ≠ ⊤) :
    ∃ E' : Subgroup (T ⧸ E), Cfg (T ⧸ E) (quotAut E α cfg.Einv)
      (quotAut E t (fun n hn => by rw [(cfg.hE n).mp hn]; exact hn)) E' ∧
      Nat.card (T ⧸ E) < Nat.card T := by
  classical
  have hEt : ∀ n ∈ E, t n ∈ E := fun n hn => by rw [(cfg.hE n).mp hn]; exact hn
  let ab := quotAut E α cfg.Einv
  let tb := quotAut E t hEt
  have hp2 : IsPGroup 2 (T ⧸ E) := cfg.p2.to_quotient E
  have hab3 : ab ^ 3 = 1 := quotAut_pow_eq_one E α cfg.Einv 3 cfg.a3
  have htb2 : tb * tb = 1 := by
    have := quotAut_pow_eq_one E t hEt 2 (by rw [pow_two]; exact cfg.t2)
    rwa [pow_two] at this
  have hcomm : ab * tb = tb * ab := quotAut_comm E α t cfg.Einv hEt cfg.comm
  have hfpf : ∀ y : T ⧸ E, ab y = y → y = 1 := fun y hy => cfg.quot_fpf E cfg.Einv y hy
  set Fb : Subgroup (T ⧸ E) := fixSub tb with hFb
  have hFbmem : ∀ y, y ∈ Fb ↔ tb y = y := fun y => Iff.rfl
  have hFbinv : ∀ y ∈ Fb, ab y ∈ Fb := by
    intro y hy
    rw [hFbmem] at hy ⊢
    have := congrArg (fun s : MulAut (T ⧸ E) => s y) hcomm
    simp only [MulAut.mul_apply] at this
    rw [← this, hy]
  have hnt : (⊤ : Subgroup (T ⧸ E)) ≠ ⊥ := by
    intro h
    apply hEtop
    rw [eq_top_iff]
    intro g _
    have : (QuotientGroup.mk g : T ⧸ E) ∈ (⊤ : Subgroup (T ⧸ E)) := Subgroup.mem_top _
    rw [h] at this
    exact (QuotientGroup.eq_one_iff g).mp (by simpa using this)
  obtain ⟨f, -, hf1, hf⟩ := exists_fixed_nontrivial hp2 tb htb2 ⊤ (fun _ _ => Subgroup.mem_top _) hnt
  let g : T ⧸ E → T := fun y => (QuotientGroup.mk_surjective y).choose
  have hg : ∀ y, (QuotientGroup.mk (g y) : T ⧸ E) = y := fun y =>
    (QuotientGroup.mk_surjective y).choose_spec
  have hFE : ∀ y : Fb, (g y)⁻¹ * t (g y) ∈ E := by
    intro y
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (QuotientGroup.mk (g y) : T ⧸ E) = y := hg y
    have h2 : tb (QuotientGroup.mk (g y)) = QuotientGroup.mk (t (g y)) := quotAut_mk E t hEt _
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h2, h1]
    have : tb (y : T ⧸ E) = y := y.2
    rw [this]; simp
  let F : Fb → E := fun y => ⟨(g y)⁻¹ * t (g y), hFE y⟩
  have hFinj : Function.Injective F := by
    intro y₁ y₂ h
    have h' : (g y₁)⁻¹ * t (g y₁) = (g y₂)⁻¹ * t (g y₂) := congrArg Subtype.val h
    have h1 : t (g y₂) = g y₂ * ((g y₁)⁻¹ * t (g y₁)) := by
      rw [h']; group
    have h2 : t (g y₂ * (g y₁)⁻¹) = g y₂ * (g y₁)⁻¹ := by
      rw [map_mul, map_inv, h1]; group
    have h3 : g y₂ * (g y₁)⁻¹ ∈ E := (cfg.hE _).mpr h2
    have h4 : (QuotientGroup.mk (g y₂) : T ⧸ E) = QuotientGroup.mk (g y₁) := by
      have : g y₂ = (g y₂ * (g y₁)⁻¹) * g y₁ := by group
      rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr h3, one_mul]
    apply Subtype.ext
    rw [← hg y₁, ← hg y₂, h4]
  have hle4 : Nat.card Fb ≤ 4 := by
    have := Nat.card_le_card_of_injective F hFinj
    rwa [cfg.Ecard] at this
  have hFbne : Fb ≠ ⊥ := by
    intro h
    have : f ∈ Fb := (hFbmem f).mpr hf
    rw [h] at this
    exact hf1 (by simpa using this)
  have hge2 : 2 ≤ Nat.card Fb := by
    have : Nontrivial Fb := (Subgroup.nontrivial_iff_ne_bot Fb).mpr hFbne
    exact Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.mpr this)
  have hmod := card_fix_modEq3 ab 1 (by rw [pow_one]; exact hab3) Fb hFbinv
  have hfixcard : Nat.card {v : Fb // ab v = v} = 1 := by
    have : Unique {v : Fb // ab v = v} :=
      { default := ⟨1, map_one ab⟩
        uniq := fun v => Subtype.ext (Subtype.ext (hfpf v.1.1 v.2)) }
    exact Nat.card_unique
  rw [hfixcard] at hmod
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hp2.to_subgroup Fb)
  have hmod1 : Nat.card Fb % 3 = 1 := hmod
  rw [hn] at hle4 hge2 hmod1
  have hFb4 : Nat.card Fb = 4 := by
    have hn4 : n ≤ 2 := by
      by_contra h
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n
    · omega
    · omega
    · rw [hn]; norm_num
  obtain ⟨hE2', hEc'⟩ := elem_of_fpf ab hab3 Fb hFb4 hFbinv (fun e _ he => hfpf e he)
  refine ⟨Fb, ⟨hp2, hab3, htb2, hcomm, fun y => Iff.rfl, hE2', hEc', hFb4,
    fun e _ he => hfpf e he⟩, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup E
  rw [cfg.Ecard] at h1
  have : 0 < Nat.card (T ⧸ E) := Nat.card_pos
  omega

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
