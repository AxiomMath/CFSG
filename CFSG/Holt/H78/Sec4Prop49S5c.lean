module

public import CFSG.Holt.H78.Sec4Prop49S5b
import CFSG.Holt.H78.Sec4KnownKV
import CFSG.Holt.TwoGroupsFocal

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

section Torus

variable {Δ : Type} [Fintype Δ] {M : Subgroup (Equiv.Perm Δ)}

theorem IsNaturalSE.exists_generator (hM : IsNaturalSE M) {a b : Δ} (hab : a ≠ b) :
    ∃ d ∈ M, d a = a ∧ d b = b ∧ Odd (orderOf d) ∧
      ∀ m ∈ M, m a = a → m b = b → m ∈ Subgroup.zpowers d := by
  obtain ⟨n, k, e, hA⟩ := hM.exists_isBenderAction
  have := hA.isCyclic_stabilizer_inf hab
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(stabilizer (↥M) a ⊓ stabilizer (↥M) b))
  have hgodd : Odd (orderOf g) :=
    Odd.of_dvd_nat (hA.odd_card_stabilizer_inf hab) (orderOf_dvd_natCard g)
  refine ⟨((g : M) : Equiv.Perm Δ), (g : M).2, (Subgroup.mem_inf.mp g.2).1,
    (Subgroup.mem_inf.mp g.2).2, ?_, fun m hm hma hmb => ?_⟩
  · rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
      (hg ⟨⟨m, hm⟩, Subgroup.mem_inf.mpr ⟨hma, hmb⟩⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by
      have := congrArg (fun x : ↥(stabilizer (↥M) a ⊓ stabilizer (↥M) b) =>
        ((x : M) : Equiv.Perm Δ)) hj
      simpa using this⟩

theorem IsNaturalSE.eq_one_of_conj_eq (hM : IsNaturalSE M) {a b : Δ} (hab : a ≠ b)
    {d : Equiv.Perm Δ}
    (hgen : ∀ m ∈ M, m a = a → m b = b → m ∈ Subgroup.zpowers d) {z : Equiv.Perm Δ}
    (hz : z ∈ CFSG.GH74.Uniqueness.Bender.rootCenter (seRadical M a)) (hdz : d * z * d⁻¹ = z) :
    z = 1 := by
  by_contra hz1
  obtain ⟨n, k, e, hA⟩ := hM.exists_isBenderAction
  have hcomm : Commute d z := by
    rw [Commute, SemiconjBy]
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [hdz]
  have hall : ∀ z' ∈ CFSG.GH74.Uniqueness.Bender.rootCenter (seRadical M a), z' ≠ 1 → z' = z := by
    intro z' hz' hz'1
    obtain ⟨d', hd'M, hd'a, hd'b, hd'z⟩ := hM.exists_conj_eq hab hz hz1 hz' hz'1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen d' hd'M hd'a hd'b)
    rw [← hd'z, (hcomm.zpow_left j).eq, mul_inv_cancel_right]
  have hcard := hA.card_rootCenter_seRadical a
  have hsub : ((CFSG.GH74.Uniqueness.Bender.rootCenter (seRadical M a) : Subgroup _) :
      Set (Equiv.Perm Δ)) ⊆ {1, z} := fun z' hz' => by
    by_cases h1 : z' = 1
    · exact Or.inl h1
    · exact Or.inr (hall z' hz' h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_insert_le (1 : Equiv.Perm Δ) {z}
  rw [Set.ncard_singleton] at h2
  rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard] at h1
  have := hA.four_le_q
  omega

end Torus

namespace P49Config

section LineHom

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α : Ω} {v : G}
  (C : P49Config G Ω α v)

noncomputable def lineEquiv : C.D.Ψc C.i ≃ C.line :=
  Equiv.ofInjective (fun ψ => (C.lpt ψ : Ω)) C.lpt_coe_injective

noncomputable def lineHom : stabilizer G C.line →* Equiv.Perm (C.D.Ψc C.i) :=
  C.lineEquiv.permCongrHom.symm.toMonoidHom.comp
    (inducedHom (stabilizer G C.line) C.line le_rfl)

theorem lineActs_lineHom (g : stabilizer G C.line) : C.LineActs g (C.lineHom g) := fun ψ => by
  have e : (C.lineEquiv ((C.lineHom g) ψ) : Ω) = (g : G) • (C.lineEquiv ψ : Ω) := by
    simp [lineHom, Equiv.permCongrHom, Equiv.permCongr]
  exact e.symm

variable {C} in
theorem LineActs.pow {g : G} {m : Equiv.Perm (C.D.Ψc C.i)} (h : C.LineActs g m) (k : ℕ) :
    C.LineActs (g ^ k) (m ^ k) := by
  induction k with
  | zero => simpa using C.lineActs_one
  | succ k ih => simpa [pow_succ] using ih.mul h

theorem lineHom_eq {g : stabilizer G C.line} {m : Equiv.Perm (C.D.Ψc C.i)}
    (h : C.LineActs g m) : C.lineHom g = m :=
  (C.lineActs_lineHom g).unique h

end LineHom

section EOnLine

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable (P : C.P95Data)

@[expose] def W : Subgroup G := P.E ⊓ fixingSubgroup G C.line

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_W {e : G} : e ∈ P.W ↔ e ∈ P.E ∧ ∀ y ∈ C.line, e • y = y := by
  rw [W, Subgroup.mem_inf, mem_fixingSubgroup_iff]

theorem E_le_stabilizer_line (h : C.P95) : P.E ≤ stabilizer G C.line := fun _ he =>
  mem_stabilizer_iff.mpr (h.smul_line_of_mem_K (P.E_le_K he))

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem lineActs_of_eqOn {x y : G} (hx : x ∈ stabilizer G α) (hy : y ∈ stabilizer G α)
    (hxy : ∀ γ ∈ C.Γ, x • γ = y • γ) {m : Equiv.Perm (C.D.Ψc C.i)} (hym : C.LineActs y m) :
    C.LineActs x m := fun ψ => by
  rw [← hym ψ]
  rcases eq_or_ne (C.lpt ψ : Ω) α with hψ | hψ
  · rw [hψ, mem_stabilizer_iff.mp hx, mem_stabilizer_iff.mp hy]
  · exact hxy _ (mem_Γ_of_mem_line C (C.lpt_mem_line ψ) hψ)

theorem exists_mem_E_lineActs (h : C.P95) {z : Equiv.Perm (C.D.Ψc C.i)} (hz : z ∈ C.rootZ) :
    ∃ e ∈ P.E, C.LineActs e z := by
  have hαa : (C.lpt (C.D.coord C.a C.i) : Ω) = α := by rw [C.lpt_coord_a, C.coe_a]
  have hz' : z ∈ Subgroup.closure
      {x | x ∈ seRadical (C.D.M C.i) (C.D.coord C.a C.i) ∧ x * x = 1} := by
    rw [(C.isNaturalSE C.i).closure_seRadical_involutions]
    exact hz
  clear hz
  induction hz' using Subgroup.closure_induction with
  | mem x hx =>
    rcases eq_or_ne x 1 with rfl | hx1
    · exact ⟨1, one_mem _, C.lineActs_one⟩
    have hxM := seRadical_le hx.1
    have hxJ := (C.isNaturalSE C.i).mem_longInv_perm hxM
      (orderOf_eq_prime (by rw [sq]; exact hx.2) hx1)
    obtain ⟨s, hs, -, hsx⟩ := C.exists_lineActs_longInvAt h.setting hxM
      ⟨hxJ, apply_eq_of_mem_seRadical hx.1⟩
    rw [hαa] at hs
    obtain ⟨e, he, heq⟩ := P.exists_mem_E_eqOn h (Subgroup.subset_closure hs)
    exact ⟨e, he, lineActs_of_eqOn (P.E_le_stabilizer he)
      (K_le_stabilizer C (Subgroup.subset_closure hs)) heq hsx⟩
  | one => exact ⟨1, one_mem _, C.lineActs_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, he, hex⟩ := hx
    obtain ⟨e', he', hey⟩ := hy
    exact ⟨e * e', mul_mem he he', hex.mul hey⟩
  | inv x _ hx =>
    obtain ⟨e, he, hex⟩ := hx
    exact ⟨e⁻¹, inv_mem he, hex.inv⟩

theorem lineHom_mem_rootZ (h : C.P95) {e : G} (he : e ∈ P.E) :
    C.lineHom ⟨e, P.E_le_stabilizer_line h he⟩ ∈ C.rootZ := by
  obtain ⟨z, hz, hez⟩ := h.exists_lineActs_rootZ (P.E_le_K he)
  rw [C.lineHom_eq (g := ⟨e, P.E_le_stabilizer_line h he⟩) hez]
  exact hz

theorem mem_W_iff_lineHom (h : C.P95) {e : G} (he : e ∈ P.E) :
    e ∈ P.W ↔ C.lineHom ⟨e, P.E_le_stabilizer_line h he⟩ = 1 := by
  rw [mem_W]
  constructor
  · rintro ⟨-, hfix⟩
    exact C.lineHom_eq fun ψ => by
      rw [hfix _ (C.lpt_mem_line ψ), Equiv.Perm.one_apply]
  · intro h1
    refine ⟨he, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    have := C.lineActs_lineHom ⟨e, P.E_le_stabilizer_line h he⟩ ψ
    rw [h1, Equiv.Perm.one_apply] at this
    exact this

theorem lineHom_mul (h : C.P95) {e e' : G} (he : e ∈ P.E) (he' : e' ∈ P.E) :
    C.lineHom ⟨e * e', P.E_le_stabilizer_line h (mul_mem he he')⟩ =
      C.lineHom ⟨e, P.E_le_stabilizer_line h he⟩ *
        C.lineHom ⟨e', P.E_le_stabilizer_line h he'⟩ := by
  rw [← map_mul]
  rfl

theorem lineHom_inv (h : C.P95) {e : G} (he : e ∈ P.E) :
    C.lineHom ⟨e⁻¹, P.E_le_stabilizer_line h (inv_mem he)⟩ =
      (C.lineHom ⟨e, P.E_le_stabilizer_line h he⟩)⁻¹ := by
  rw [← map_inv]
  rfl

theorem card_E (h : C.P95) : Nat.card P.E = Nat.card P.W * Nat.card C.rootZ := by
  set f : P.E → Equiv.Perm (C.D.Ψc C.i) := fun e => C.lineHom ⟨e, P.E_le_stabilizer_line h e.2⟩
  have huniv : f ⁻¹' (C.rootZ : Set (Equiv.Perm (C.D.Ψc C.i))) = Set.univ :=
    Set.eq_univ_of_forall fun e => P.lineHom_mem_rootZ h e.2
  have hl : ∀ z ∈ (C.rootZ : Set (Equiv.Perm (C.D.Ψc C.i))),
      Nat.card {e // f e = z} = Nat.card P.W := by
    intro z hz
    obtain ⟨e₀, he₀, he₀z⟩ := P.exists_mem_E_lineActs h hz
    have hf₀ : C.lineHom ⟨e₀, P.E_le_stabilizer_line h he₀⟩ = z := C.lineHom_eq he₀z
    have hW : ∀ e : P.E, f e = z → e₀⁻¹ * (e : G) ∈ P.W := fun e hez => by
      have hmem : e₀⁻¹ * (e : G) ∈ P.E := mul_mem (inv_mem he₀) e.2
      refine (P.mem_W_iff_lineHom h hmem).mpr ?_
      rw [P.lineHom_mul h (inv_mem he₀) e.2, P.lineHom_inv h he₀, hf₀,
        show C.lineHom ⟨(e : G), P.E_le_stabilizer_line h e.2⟩ = z from hez,
        inv_mul_cancel]
    refine Nat.card_congr
      { toFun := fun e => ⟨e₀⁻¹ * e.1, hW e.1 e.2⟩
        invFun := fun w => ⟨⟨e₀ * w.1, mul_mem he₀ ((P.mem_W.mp w.2).1)⟩, ?_⟩
        left_inv := fun e => Subtype.ext (Subtype.ext (by simp))
        right_inv := fun w => Subtype.ext (by simp) }
    show C.lineHom ⟨e₀ * w.1, _⟩ = z
    rw [P.lineHom_mul h he₀ (P.mem_W.mp w.2).1, hf₀,
      (P.mem_W_iff_lineHom h (P.mem_W.mp w.2).1).mp w.2, mul_one]
  have := card_preimage_eq_mul f hl
  rw [huniv, Nat.card_univ, SetLike.coe_sort_coe] at this
  exact this

theorem exists_torus (h : C.P95) :
    ∃ n ∈ stabilizer G α, n • C.β = C.β ∧ n ∈ Subgroup.normalizer (P.E : Set G) ∧
      Odd (orderOf n) ∧ (∀ w ∈ P.W, n * w = w * n) ∧
      ∃ d ∈ C.D.M C.i, C.LineActs n d ∧ ∀ m ∈ C.D.M C.i,
        m (C.D.coord C.a C.i) = C.D.coord C.a C.i → m (C.D.coord C.b C.i) = C.D.coord C.b C.i →
          m ∈ Subgroup.zpowers d := by
  have hαa : (C.lpt (C.D.coord C.a C.i) : Ω) = α := by rw [C.lpt_coord_a, C.coe_a]
  obtain ⟨d₀, hd₀M, hd₀a, hd₀b, hd₀odd, hd₀gen⟩ :=
    (C.isNaturalSE C.i).exists_generator C.coord_ne
  have hWp : IsPGroup 2 P.W := P.isPGroup_E.to_le inf_le_left
  obtain ⟨g, hg, hgd⟩ := C.exists_lineActs_closure h.setting h.transitive hWp inf_le_right hd₀M
  have hgW : g ∈ Subgroup.centralizer (P.W : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_ hg
    rintro c ⟨-, hc, -⟩
    exact hc
  have hgα : g ∈ stabilizer G α := by
    rw [mem_stabilizer_iff, hgd.smul_α, hd₀a, hαa]
  have hgβ : g • C.β = C.β := by rw [hgd.smul_β, hd₀b, C.lpt_coord_b]
  obtain ⟨n₁, hn₁α, hn₁N, hn₁Γ, hn₁C⟩ := P.exists_mem_normalizer_eqOn h hgα
  have hn₁d : C.LineActs n₁ d₀ := lineActs_of_eqOn hn₁α hgα hn₁Γ hgd
  have hn₁W : ∀ w ∈ P.W, n₁ * w = w * n₁ := fun w hw =>
    hn₁C w (P.mem_W.mp hw).1 (Subgroup.mem_centralizer_iff.mp hgW w hw).symm
  obtain ⟨a, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n₁).ne'
  have hcop : Nat.Coprime (orderOf d₀) (2 ^ a) :=
    Nat.Coprime.pow_right _ (Odd.coprime_two_right hd₀odd)
  have hzp : Subgroup.zpowers (d₀ ^ 2 ^ a) = Subgroup.zpowers d₀ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow, Nat.Coprime.gcd_eq_one hcop,
      Nat.div_one]
  refine ⟨n₁ ^ 2 ^ a, Subgroup.pow_mem _ hn₁α _, ?_, Subgroup.pow_mem _ hn₁N _, ?_, ?_,
    d₀ ^ 2 ^ a, Subgroup.pow_mem _ hd₀M _, hn₁d.pow _, fun m hm hma hmb => ?_⟩
  · have hβ : n₁ ∈ stabilizer G C.β := by
      rw [mem_stabilizer_iff, hn₁Γ _ C.β_mem_Γ, hgβ]
    exact mem_stabilizer_iff.mp (Subgroup.pow_mem _ hβ _)
  · rw [orderOf_pow_of_dvd (by positivity) ⟨r, hord⟩, hord, Nat.mul_div_cancel_left _
      (by positivity)]
    exact hr
  · intro w hw
    exact ((Commute.pow_left (hn₁W w hw) _)).eq
  · rw [hzp]
    exact hd₀gen m hm hma hmb

end P95Data

end EOnLine

section Torus

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable (P : C.P95Data)

structure Torus where
  n : G
  d : Equiv.Perm (C.D.Ψc C.i)
  mem_stabilizer : n ∈ stabilizer G α
  smul_β : n • C.β = C.β
  mem_normalizer : n ∈ Subgroup.normalizer (P.E : Set G)
  odd : Odd (orderOf n)
  comm : ∀ w ∈ P.W, n * w = w * n
  d_mem : d ∈ C.D.M C.i
  lineActs : C.LineActs n d
  gen : ∀ m ∈ C.D.M C.i, m (C.D.coord C.a C.i) = C.D.coord C.a C.i →
    m (C.D.coord C.b C.i) = C.D.coord C.b C.i → m ∈ Subgroup.zpowers d

theorem nonempty_torus (h : C.P95) : Nonempty P.Torus := by
  obtain ⟨n, h1, h2, h3, h4, h5, d, h6, h7, h8⟩ := P.exists_torus h
  exact ⟨⟨n, d, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

namespace Torus

variable {P} (T : P.Torus)

@[expose] def V : Subgroup G := Subgroup.closure {x | ∃ e ∈ P.E, T.n * e * T.n⁻¹ * e⁻¹ = x}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_E {e : G} (he : e ∈ P.E) : T.n * e * T.n⁻¹ ∈ P.E :=
  (Subgroup.mem_normalizer_iff.mp T.mem_normalizer e).mp he

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem d_apply_a : T.d (C.D.coord C.a C.i) = C.D.coord C.a C.i := by
  have e := T.lineActs.smul_α
  rw [mem_stabilizer_iff.mp T.mem_stabilizer] at e
  have e2 : ((C.lpt (C.D.coord C.a C.i)) : Ω) = α := by rw [C.lpt_coord_a, C.coe_a]
  exact C.lpt_injective (Subtype.ext (e.symm.trans e2.symm))

theorem mem_V (h : C.P95) {x : G} : x ∈ T.V ↔ ∃ e ∈ P.E, T.n * e * T.n⁻¹ * e⁻¹ = x := by
  refine ⟨fun hx => ?_, fun hx => Subgroup.subset_closure hx⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, one_mem _, by group⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨e', he', rfl⟩ := hy
    refine ⟨e * e', mul_mem he he', ?_⟩
    have h1 := P.commute_E h (inv_mem he) (mul_mem (T.conj_mem_E he') (inv_mem he'))
    calc T.n * (e * e') * T.n⁻¹ * (e * e')⁻¹
        = T.n * e * T.n⁻¹ * ((T.n * e' * T.n⁻¹ * e'⁻¹) * e⁻¹) := by group
      _ = T.n * e * T.n⁻¹ * (e⁻¹ * (T.n * e' * T.n⁻¹ * e'⁻¹)) := by rw [h1]
      _ = T.n * e * T.n⁻¹ * e⁻¹ * (T.n * e' * T.n⁻¹ * e'⁻¹) := by group
  | inv x _ hx =>
    obtain ⟨e, he, rfl⟩ := hx
    refine ⟨e⁻¹, inv_mem he, ?_⟩
    have h1 := P.commute_E h he (T.conj_mem_E (inv_mem he))
    calc T.n * e⁻¹ * T.n⁻¹ * e⁻¹⁻¹ = e * (T.n * e⁻¹ * T.n⁻¹) := by rw [inv_inv, ← h1]
      _ = (T.n * e * T.n⁻¹ * e⁻¹)⁻¹ := by group

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem V_le_E : T.V ≤ P.E := by
  rw [V, Subgroup.closure_le]
  rintro _ ⟨e, he, rfl⟩
  exact mul_mem (T.conj_mem_E he) (inv_mem he)

theorem eq_one_of_mem_W (h : C.P95) {x : G} (hx : x ∈ T.V) (hxW : x ∈ P.W) : x = 1 := by
  obtain ⟨e, he, rfl⟩ := (T.mem_V h).mp hx
  have hc : ∀ k : ℕ, T.n ^ k * (T.n * e * T.n⁻¹ * e⁻¹) = (T.n * e * T.n⁻¹ * e⁻¹) * T.n ^ k :=
    fun k => ((Commute.pow_left (T.comm _ hxW) k)).eq
  have key : ∀ k : ℕ, (T.n * e * T.n⁻¹ * e⁻¹) ^ k = T.n ^ k * e * (T.n ^ k)⁻¹ * e⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (T.n * e * T.n⁻¹ * e⁻¹) ^ (k + 1)
          = (T.n ^ k * (T.n * e * T.n⁻¹ * e⁻¹) * (T.n ^ k)⁻¹) *
              (T.n * e * T.n⁻¹ * e⁻¹) ^ k := by
            rw [hc k, mul_inv_cancel_right, pow_succ']
        _ = T.n ^ (k + 1) * e * (T.n ^ (k + 1))⁻¹ * e⁻¹ := by
            rw [ih, pow_succ]; group
  have h1 := key (orderOf T.n)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, mul_inv_cancel] at h1
  obtain ⟨r, hr⟩ := T.odd
  have hx2 := P.mul_self_E h (T.V_le_E hx)
  rw [hr, pow_succ, pow_mul, sq, hx2, one_pow, one_mul] at h1
  exact h1

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_rootZ {z : Equiv.Perm (C.D.Ψc C.i)} (hz : z ∈ C.rootZ) :
    T.d * z * T.d⁻¹ ∈ C.rootZ :=
  conj_mem_rootCenter_seRadical (Subgroup.le_normalizer T.d_mem) T.d_apply_a hz

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_pow_eq {m : Equiv.Perm (C.D.Ψc C.i)} (hm : m ∈ C.D.M C.i)
    (hma : m (C.D.coord C.a C.i) = C.D.coord C.a C.i)
    (hmb : m (C.D.coord C.b C.i) = C.D.coord C.b C.i) : ∃ k : ℕ, T.d ^ k = m := by
  have h1 := T.gen m hm hma hmb
  rw [← SetLike.mem_coe, ← (isOfFinOrder_of_finite T.d).powers_eq_zpowers] at h1
  exact Submonoid.mem_powers_iff _ _ |>.mp h1

theorem exists_mem_V_lineActs (h : C.P95) {z : Equiv.Perm (C.D.Ψc C.i)} (hz : z ∈ C.rootZ) :
    ∃ x ∈ T.V, C.LineActs x z := by
  set f : C.rootZ → C.rootZ := fun y => ⟨T.d * (y : Equiv.Perm (C.D.Ψc C.i)) * T.d⁻¹ *
    (y : Equiv.Perm (C.D.Ψc C.i))⁻¹, mul_mem (T.conj_mem_rootZ y.2) (inv_mem y.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨Y, hY⟩ ⟨Y', hY'⟩ hyy
    have e := congrArg Subtype.val hyy
    simp only [f] at e
    have hy0 : Y'⁻¹ * Y ∈ C.rootZ := mul_mem (inv_mem hY') hY
    have hfix : T.d * (Y'⁻¹ * Y) * T.d⁻¹ = Y'⁻¹ * Y := by
      have e' : T.d * Y * T.d⁻¹ = T.d * Y' * T.d⁻¹ * Y'⁻¹ * Y := by
        rw [← e]; group
      calc T.d * (Y'⁻¹ * Y) * T.d⁻¹ = (T.d * Y' * T.d⁻¹)⁻¹ * (T.d * Y * T.d⁻¹) := by group
        _ = Y'⁻¹ * Y := by rw [e']; group
    have h1 := (C.isNaturalSE C.i).eq_one_of_conj_eq C.coord_ne T.gen hy0 hfix
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨z, hz⟩
  obtain ⟨e, he, hey⟩ := P.exists_mem_E_lineActs h y.2
  refine ⟨T.n * e * T.n⁻¹ * e⁻¹, Subgroup.subset_closure ⟨e, he, rfl⟩, ?_⟩
  have := ((T.lineActs.mul hey).mul T.lineActs.inv).mul hey.inv
  have e2 : T.d * (y : Equiv.Perm (C.D.Ψc C.i)) * T.d⁻¹ * (y : Equiv.Perm (C.D.Ψc C.i))⁻¹ = z :=
    congrArg Subtype.val hy
  rwa [e2] at this

theorem V_le (h : C.P95) {E' : Subgroup G} (hE' : E' ≤ P.E)
    (hinv : ∀ e ∈ E', T.n * e * T.n⁻¹ ∈ E')
    (hsurj : ∀ z ∈ C.rootZ, ∃ e ∈ E', C.LineActs e z) : T.V ≤ E' := by
  rw [V, Subgroup.closure_le]
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨z, hz, hez⟩ := h.exists_lineActs_rootZ (P.E_le_K he)
  obtain ⟨e', he', he'z⟩ := hsurj z hz
  have hw : e'⁻¹ * e ∈ P.W := (P.mem_W).mpr ⟨mul_mem (inv_mem (hE' he')) he, by
    rintro _ ⟨ψ, rfl⟩
    have := (he'z.inv.mul hez) ψ
    rwa [inv_mul_cancel, Equiv.Perm.one_apply] at this⟩
  have hc := T.comm _ hw
  have e1 : T.n * e * T.n⁻¹ * e⁻¹ = T.n * e' * T.n⁻¹ * e'⁻¹ := by
    calc T.n * e * T.n⁻¹ * e⁻¹
        = T.n * e' * T.n⁻¹ * (T.n * (e'⁻¹ * e) * T.n⁻¹) * (e'⁻¹ * e)⁻¹ * e'⁻¹ := by group
      _ = T.n * e' * T.n⁻¹ * e'⁻¹ := by rw [hc, mul_inv_cancel_right]; group
  rw [SetLike.mem_coe, e1]
  exact mul_mem (hinv e' he') (inv_mem he')

theorem trivial_or_surj (h : C.P95) {E' : Subgroup G} (hE' : E' ≤ P.E)
    (hinv : ∀ e ∈ E', T.n * e * T.n⁻¹ ∈ E') :
    (∀ e ∈ E', ∀ y ∈ C.line, e • y = y) ∨ ∀ z ∈ C.rootZ, ∃ e ∈ E', C.LineActs e z := by
  set I : Subgroup (Equiv.Perm (C.D.Ψc C.i)) :=
    (E'.subgroupOf (stabilizer G C.line)).map C.lineHom
  have hmemI : ∀ {z}, z ∈ I ↔ ∃ e ∈ E', C.LineActs e z := fun {z} => by
    constructor
    · rintro ⟨⟨e, he⟩, he', rfl⟩
      exact ⟨e, he', C.lineActs_lineHom ⟨e, he⟩⟩
    · rintro ⟨e, he, hez⟩
      exact ⟨⟨e, P.E_le_stabilizer_line h (hE' he)⟩, he, C.lineHom_eq hez⟩
  have hIZ : I ≤ C.rootZ := fun z hz => by
    obtain ⟨e, he, hez⟩ := hmemI.mp hz
    rw [← C.lineHom_eq (g := ⟨e, P.E_le_stabilizer_line h (hE' he)⟩) hez]
    exact P.lineHom_mem_rootZ h (hE' he)
  have hpow : ∀ k : ℕ, ∀ e ∈ E', T.n ^ k * e * (T.n ^ k)⁻¹ ∈ E' := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro e he
      have := hinv _ (ih e he)
      rwa [show T.n * (T.n ^ k * e * (T.n ^ k)⁻¹) * T.n⁻¹ = T.n ^ (k + 1) * e * (T.n ^ (k + 1))⁻¹
        by group] at this
  have hI : ∀ d' ∈ C.D.M C.i, d' (C.D.coord C.a C.i) = C.D.coord C.a C.i →
      d' (C.D.coord C.b C.i) = C.D.coord C.b C.i → ∀ w ∈ I, d' * w * d'⁻¹ ∈ I := by
    intro d' hd' hd'a hd'b w hw
    obtain ⟨k, rfl⟩ := T.exists_pow_eq hd' hd'a hd'b
    obtain ⟨e, he, hew⟩ := hmemI.mp hw
    exact hmemI.mpr ⟨_, hpow k e he, ((T.lineActs.pow k).mul hew).mul (T.lineActs.pow k).inv⟩
  rcases (C.isNaturalSE C.i).eq_bot_or_eq_rootCenter C.coord_ne hIZ hI with hbot | htop
  · left
    intro e he
    rintro _ ⟨ψ, rfl⟩
    have h1 : C.lineHom ⟨e, P.E_le_stabilizer_line h (hE' he)⟩ ∈ I := ⟨⟨e, _⟩, he, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have := C.lineActs_lineHom ⟨e, P.E_le_stabilizer_line h (hE' he)⟩ ψ
    rw [h1, Equiv.Perm.one_apply] at this
    exact this
  · right
    intro z hz
    exact hmemI.mp (htop ▸ hz)

theorem card_V (h : C.P95) : Nat.card T.V = Nat.card C.rootZ := by
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨C.lineHom
    ⟨x, P.E_le_stabilizer_line h (T.V_le_E x.2)⟩,
      P.lineHom_mem_rootZ h (T.V_le_E x.2)⟩) ⟨fun x y hxy => ?_, fun z => ?_⟩)
  · have e := congrArg Subtype.val hxy
    simp only at e
    have hxy' : (x : G)⁻¹ * y ∈ P.W := by
      refine (P.mem_W_iff_lineHom h (mul_mem (inv_mem (T.V_le_E x.2)) (T.V_le_E y.2))).mpr ?_
      rw [P.lineHom_mul h (inv_mem (T.V_le_E x.2)) (T.V_le_E y.2), P.lineHom_inv h (T.V_le_E x.2),
        e, inv_mul_cancel]
    have := T.eq_one_of_mem_W h (mul_mem (inv_mem x.2) y.2) hxy'
    exact Subtype.ext (inv_mul_eq_one.mp this)
  · obtain ⟨x, hx, hxz⟩ := T.exists_mem_V_lineActs h z.2
    exact ⟨⟨x, hx⟩, Subtype.ext (C.lineHom_eq hxz)⟩

theorem conj_mem_V (h : C.P95) {x : G} (hx : x ∈ T.V) : T.n * x * T.n⁻¹ ∈ T.V := by
  obtain ⟨e, he, rfl⟩ := (T.mem_V h).mp hx
  exact (T.mem_V h).mpr ⟨T.n * e * T.n⁻¹, T.conj_mem_E he, by group⟩

theorem exists_pow_conj_eq (h : C.P95) {x y : G} (hx : x ∈ T.V) (hy : y ∈ T.V) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : ∃ k : ℕ, T.n ^ k * x * (T.n ^ k)⁻¹ = y := by
  have hxE := T.V_le_E hx
  have hyE := T.V_le_E hy
  set zx := C.lineHom ⟨x, P.E_le_stabilizer_line h hxE⟩
  set zy := C.lineHom ⟨y, P.E_le_stabilizer_line h hyE⟩
  have hzx1 : zx ≠ 1 := fun h1 => hx1 (T.eq_one_of_mem_W h hx ((P.mem_W_iff_lineHom h hxE).mpr h1))
  have hzy1 : zy ≠ 1 := fun h1 => hy1 (T.eq_one_of_mem_W h hy ((P.mem_W_iff_lineHom h hyE).mpr h1))
  obtain ⟨d', hd'M, hd'a, hd'b, hd'z⟩ := (C.isNaturalSE C.i).exists_conj_eq C.coord_ne
    (P.lineHom_mem_rootZ h hxE) hzx1 (P.lineHom_mem_rootZ h hyE) hzy1
  obtain ⟨k, rfl⟩ := T.exists_pow_eq hd'M hd'a hd'b
  refine ⟨k, ?_⟩
  have hpowV : ∀ j : ℕ, T.n ^ j * x * (T.n ^ j)⁻¹ ∈ T.V := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      have := T.conj_mem_V h ih
      rwa [show T.n * (T.n ^ j * x * (T.n ^ j)⁻¹) * T.n⁻¹ = T.n ^ (j + 1) * x * (T.n ^ (j + 1))⁻¹
        by group] at this
  have hact : C.LineActs (T.n ^ k * x * (T.n ^ k)⁻¹) zy := by
    have e1 : zy = T.d ^ k * zx * (T.d ^ k)⁻¹ := hd'z.symm
    rw [e1]
    exact ((T.lineActs.pow k).mul (C.lineActs_lineHom ⟨x, P.E_le_stabilizer_line h hxE⟩)).mul
      (T.lineActs.pow k).inv
  have hw : (T.n ^ k * x * (T.n ^ k)⁻¹)⁻¹ * y ∈ P.W := (P.mem_W).mpr
    ⟨mul_mem (inv_mem (T.V_le_E (hpowV k))) hyE, by
      rintro _ ⟨ψ, rfl⟩
      have := (hact.inv.mul (C.lineActs_lineHom ⟨y, P.E_le_stabilizer_line h hyE⟩)) ψ
      rwa [inv_mul_cancel, Equiv.Perm.one_apply] at this⟩
  exact inv_mul_eq_one.mp (T.eq_one_of_mem_W h (mul_mem (inv_mem (hpowV k)) hy) hw)

end Torus

end P95Data

end Torus

section ThreeLines

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem exists_notMem_line (C : P49Config G Ω α v) : ∃ ω, ω ∉ C.line := by
  by_contra hne
  have hall : ∀ ω, ω ∈ C.line := fun ω => by_contra fun hω => hne ⟨ω, hω⟩
  have hv : v = 1 := FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun ω => by
    rw [one_smul]
    exact mem_fixSet_zpowers_iff.mp (C.line_subset_fixSet (hall ω))
  have h2 := C.isTypeL.orderOf_eq_two
  rw [hv, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem P95.exists_mem_linesThrough_ne (h : C.P95) :
    ∃ ℓ ∈ linesThrough G C.line α, ℓ ≠ C.line := by
  by_contra hne
  have hall : ∀ ℓ ∈ linesThrough G C.line α, ℓ = C.line := fun ℓ hℓ =>
    by_contra fun h1 => hne ⟨ℓ, hℓ, h1⟩
  have hS := h.setting
  have := hS.star.isPretransitive
  have : Nontrivial Ω := by
    have h3 := hS.star.three_le_card
    exact Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hpre := hS.preprimitive
  have hle : stabilizer G α ≤ stabilizer G C.line := fun g hg => by
    have h1 : g • C.line ∈ linesThrough G C.line α := by
      refine ⟨⟨g, rfl⟩, ?_⟩
      have := Set.smul_mem_smul_set (a := g) C.α_mem_line
      rwa [mem_stabilizer_iff.mp hg] at this
    exact mem_stabilizer_iff.mpr (hall _ h1)
  obtain ⟨P⟩ := nonempty_p95Data C
  obtain ⟨g, hg⟩ := exists_smul_eq G α C.β
  have hs := conj_mem_longInvAt P.t_mem g
  rw [hg] at hs
  have hsL : g * P.t * g⁻¹ ∈ stabilizer G C.line :=
    mem_stabilizer_iff.mpr (C.isJClosed_line hS h.transitive _ C.β_mem_line _ hs)
  have hsα : g * P.t * g⁻¹ ∉ stabilizer G α := fun hα =>
    C.ne (hs.1.2.unique (mem_stabilizer_iff.mp hα) hs.2)
  have htop : stabilizer G C.line = ⊤ :=
    (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) α).lt_iff.mp
      (lt_of_le_of_ne hle fun heq => hsα (heq ▸ hsL))
  obtain ⟨ω, hω⟩ := exists_notMem_line C
  obtain ⟨g', hg'⟩ := exists_smul_eq G α ω
  have h1 := mem_stabilizer_iff.mp (htop ▸ Subgroup.mem_top g' : g' ∈ stabilizer G C.line)
  refine hω ?_
  rw [← hg', ← h1]
  exact Set.smul_mem_smul_set C.α_mem_line

omit [FaithfulSMul G Ω] in
theorem _root_.CFSG.Holt.H78.Sec4Setting.false_of_index_two (hS : Sec4Setting G Ω) {α : Ω}
    {H : Subgroup G} (hcomm : ∀ g ∈ stabilizer G α, ∀ g' ∈ stabilizer G α, g * g' * g⁻¹ * g'⁻¹ ∈ H)
    (hsq : ∀ g ∈ stabilizer G α, g * g ∈ H) (hJ : longInvAt G Ω α ⊆ H) {y : G}
    (hy : y ∈ stabilizer G α) (hyH : y ∉ H) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS.star.isPretransitive
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hpowH : ∀ k : ℕ, y ^ (2 * k) ∈ H := fun k => by
    rw [pow_mul, sq]
    exact Subgroup.pow_mem _ (hsq y hy) k
  have hy'H : y ^ m ∉ H := by
    obtain ⟨k, rfl⟩ := hm
    intro h1
    refine hyH ?_
    have := mul_mem (inv_mem (hpowH k)) h1
    rwa [show (y ^ (2 * k))⁻¹ * y ^ (2 * k + 1) = y by group] at this
  have hy'p : IsPGroup 2 (Subgroup.zpowers (y ^ m)) := by
    refine IsPGroup.of_card (n := a) ?_
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by obtain ⟨k, rfl⟩ := hm; omega) ⟨2 ^ a, by
      rw [hord, mul_comm]⟩, hord, Nat.mul_div_cancel _ (by obtain ⟨k, rfl⟩ := hm; omega)]
  obtain ⟨S, hyS, hSyl⟩ := exists_fusionIsSylowIn_ge hy'p
    (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hy _))
  have hcardG : Nat.card G = Nat.card Ω * Nat.card (stabilizer G α) := by
    rw [← (stabilizer G α).index_mul_card, MulAction.index_stabilizer, orbit_eq_univ,
      Set.ncard_univ]
  have : Nonempty Ω := ⟨α⟩
  have hfac : (Nat.card G).factorization 2 = (Nat.card (stabilizer G α)).factorization 2 := by
    rw [hcardG, Nat.factorization_mul (Nat.card_pos (α := Ω)).ne' Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hS.star.odd_card.not_two_dvd_nat,
      zero_add]
  set P : Sylow 2 G := Sylow.ofCard S (by rw [card_eq_of_fusionIsSylowIn hSyl, hfac])
  have hPS : (P : Subgroup G) = S := Sylow.coe_ofCard _ _
  have hfoc : ∀ x ∈ (P : Subgroup G), ∀ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) →
      x⁻¹ * (g * x * g⁻¹) ∈ S ⊓ H := by
    intro x hx g hgx
    rw [hPS] at hx hgx
    have hxα := hSyl.1 hx
    have hgxα := hSyl.1 hgx
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hx) hgx, ?_⟩
    obtain ⟨g', hg', hg'x⟩ : ∃ g' ∈ stabilizer G α, g' * x * g'⁻¹ = g * x * g⁻¹ := by
      by_cases hgα : g⁻¹ • α = α
      · exact ⟨g, mem_stabilizer_iff.mpr (inv_smul_eq_iff.mp hgα).symm, rfl⟩
      have hxg : x • (g⁻¹ • α) = g⁻¹ • α := by
        rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group, mul_smul, mul_smul, smul_inv_smul,
          mem_stabilizer_iff.mp hgxα]
      have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
        hSyl.2.1.to_le (show Subgroup.zpowers x ≤ S from Subgroup.zpowers_le.mpr hx)
      have hαF : α ∈ fixSet Ω (Subgroup.zpowers x) := mem_fixSet_zpowers_iff.mpr hxα
      have hβF : g⁻¹ • α ∈ fixSet Ω (Subgroup.zpowers x) := mem_fixSet_zpowers_iff.mpr hxg
      have h3 : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers x)) := by
        rw [three_le_card_fixSet_iff hS.star.odd_card hxp]
        exact (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨α, g⁻¹ • α, hαF, hβF, Ne.symm hgα⟩
          |>.trans_eq (Nat.card_coe_set_eq _).symm
      have := (hS.star_centralizerImage hxp h3).isPretransitive
      obtain ⟨π, hπ⟩ := exists_smul_eq (centralizerImage Ω (Subgroup.zpowers x))
        (⟨α, hαF⟩ : fixSet Ω (Subgroup.zpowers x)) ⟨g⁻¹ • α, hβF⟩
      obtain ⟨c, hc, hcπ⟩ := mem_centralizerImage.mp π.2
      have hcα : c • α = g⁻¹ • α := by
        rw [← hcπ ⟨α, hαF⟩]
        exact congrArg Subtype.val hπ
      refine ⟨g * c, by rw [mem_stabilizer_iff, mul_smul, hcα, smul_inv_smul], ?_⟩
      have hcx : c * x = x * c := (mem_centralizer_zpowers_iff.mp hc)
      calc g * c * x * (g * c)⁻¹ = g * (c * x) * c⁻¹ * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hcx]; group
    rw [← hg'x]
    have := hcomm _ (inv_mem hxα) _ hg'
    rwa [inv_inv, show x⁻¹ * g' * x * g'⁻¹ = x⁻¹ * (g' * x * g'⁻¹) by group] at this
  obtain ⟨N, hN, -, -, hNS⟩ := exists_normal_inf_eq_of_focal P (hPS ▸ inf_le_left) hfoc
  rw [hPS] at hNS
  have hJN : longInv G Ω ⊆ N := by
    intro s hs
    obtain ⟨ω, hω⟩ := exists_mem_longInvAt hs
    obtain ⟨g, hg⟩ := exists_smul_eq G ω α
    have hs' := conj_mem_longInvAt hω g
    rw [hg] at hs'
    have hs'p : IsPGroup 2 (Subgroup.zpowers (g * s * g⁻¹)) :=
      isPGroup_zpowers_of_orderOf_eq_two hs'.1.1
    obtain ⟨S', hS'1, hS'⟩ := exists_fusionIsSylowIn_ge hs'p
      (Subgroup.zpowers_le.mpr (mem_stabilizer_iff.mpr hs'.2))
    obtain ⟨c, hc, hcS⟩ := exists_mem_conj_of_fusionIsSylowIn hSyl hS'
    have h1 : c⁻¹ * (g * s * g⁻¹) * c ∈ S ⊓ H := by
      refine Subgroup.mem_inf.mpr ⟨(hcS _).mp (hS'1 (Subgroup.mem_zpowers _)), ?_⟩
      have := mul_mem (hcomm _ (inv_mem hc) _ hs'.2) (hJ hs')
      rwa [show c⁻¹ * (g * s * g⁻¹) * c⁻¹⁻¹ * (g * s * g⁻¹)⁻¹ * (g * s * g⁻¹) =
        c⁻¹ * (g * s * g⁻¹) * c by group] at this
    rw [← hNS] at h1
    have h2 := hN.conj_mem _ h1.1 c
    rw [show c * (c⁻¹ * (g * s * g⁻¹) * c) * c⁻¹ = g * s * g⁻¹ by group] at h2
    have h3 := hN.conj_mem _ h2 g⁻¹
    rwa [show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s by group] at h3
  have hNtop : N = ⊤ := by
    rw [eq_top_iff, ← hS.jHull_eq_top, jHull, Subgroup.closure_le]
    exact hJN
  have : y ^ m ∈ S ⊓ H := by
    rw [← hNS, hNtop]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, hyS (Subgroup.mem_zpowers _)⟩
  exact hy'H this.2

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem line_mem_linesThrough (C : P49Config G Ω α v) : C.line ∈ linesThrough G C.line α :=
  ⟨⟨1, one_smul G _⟩, C.α_mem_line⟩

theorem P95.exists_three_lines (h : C.P95) :
    ∃ ℓ₂ ∈ linesThrough G C.line α, ∃ ℓ₃ ∈ linesThrough G C.line α,
      ℓ₂ ≠ C.line ∧ ℓ₃ ≠ C.line ∧ ℓ₂ ≠ ℓ₃ := by
  obtain ⟨ℓ₂, hℓ₂, hℓ₂L⟩ := h.exists_mem_linesThrough_ne
  by_contra hne
  have hall : ∀ ℓ ∈ linesThrough G C.line α, ℓ = C.line ∨ ℓ = ℓ₂ := fun ℓ hℓ => by
    by_cases h1 : ℓ = C.line
    · exact Or.inl h1
    · by_cases h2 : ℓ = ℓ₂
      · exact Or.inr h2
      · exact absurd ⟨ℓ₂, hℓ₂, ℓ, hℓ, hℓ₂L, h1, fun h3 => h2 h3.symm⟩ hne
  have hL := line_mem_linesThrough C
  have hmem : ∀ {g : G}, g ∈ stabilizer G α → ∀ {ℓ}, ℓ ∈ linesThrough G C.line α →
      g • ℓ ∈ linesThrough G C.line α := fun {g} hg {ℓ} hℓ => by
    have := smul_mem_linesThrough hℓ g
    rwa [mem_stabilizer_iff.mp hg] at this
  have K2 : ∀ g ∈ stabilizer G α, g • C.line = C.line → g • ℓ₂ = ℓ₂ := fun g hg h1 => by
    rcases hall _ (hmem hg hℓ₂) with h2 | h2
    · exact absurd (smul_left_cancel g (h2.trans h1.symm)) hℓ₂L
    · exact h2
  have K3 : ∀ g ∈ stabilizer G α, g • C.line = ℓ₂ → g • ℓ₂ = C.line := fun g hg h1 => by
    rcases hall _ (hmem hg hℓ₂) with h2 | h2
    · exact h2
    · exact absurd (smul_left_cancel g (h2.trans h1.symm)) (fun h3 => hℓ₂L h3)
  have hε : ∀ g ∈ stabilizer G α, ∀ g' ∈ stabilizer G α,
      ((g * g') • C.line = C.line ↔ (g • C.line = C.line ↔ g' • C.line = C.line)) := by
    intro g hg g' hg'
    rw [mul_smul]
    rcases hall _ (hmem hg' hL) with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      rcases hall _ (hmem hg hL) with h2 | h2
      · rw [K2 g hg h2]
        simp [h2, hℓ₂L]
      · rw [K3 g hg h2, h2]
        simp
  set H : Subgroup G := stabilizer G α ⊓ stabilizer G C.line
  have hH : ∀ {g}, g ∈ stabilizer G α → (g ∈ H ↔ g • C.line = C.line) := fun {g} hg => by
    rw [Subgroup.mem_inf, mem_stabilizer_iff (a := C.line)]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨hg, h1⟩⟩
  have hinv : ∀ g ∈ stabilizer G α, (g⁻¹ • C.line = C.line ↔ g • C.line = C.line) := by
    intro g hg
    have := hε g hg g⁻¹ (inv_mem hg)
    rw [mul_inv_cancel, one_smul] at this
    tauto
  have hcomm : ∀ g ∈ stabilizer G α, ∀ g' ∈ stabilizer G α, g * g' * g⁻¹ * g'⁻¹ ∈ H := by
    intro g hg g' hg'
    rw [hH (mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')),
      show g * g' * g⁻¹ * g'⁻¹ = (g * g') * (g⁻¹ * g'⁻¹) by group,
      hε _ (mul_mem hg hg') _ (mul_mem (inv_mem hg) (inv_mem hg')), hε g hg g' hg',
      hε _ (inv_mem hg) _ (inv_mem hg'), hinv g hg, hinv g' hg']
  have hsq : ∀ g ∈ stabilizer G α, g * g ∈ H := fun g hg => by
    rw [hH (mul_mem hg hg), hε g hg g hg]
  have hJ : longInvAt G Ω α ⊆ H := fun s hs =>
    (hH hs.2).mpr (h.smul_eq_of_mem_K (Subgroup.subset_closure hs) hL)
  obtain ⟨P⟩ := nonempty_p95Data C
  obtain ⟨n, hnα, -, hn⟩ := P.exists_mem_normalizer_smul_line h hℓ₂
  exact h.setting.false_of_index_two hcomm hsq hJ hnα fun hnH => hℓ₂L
    (hn.symm.trans ((hH hnα).mp hnH))

end ThreeLines

end P49Config

end CFSG.Holt.H78
