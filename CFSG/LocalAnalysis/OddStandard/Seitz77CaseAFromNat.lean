module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools Matrix MatrixGroups

section SylowMap

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem isSylowOf_map_of_injective {f : G →* H} (hf : Function.Injective f) {p : ℕ}
    [Fact p.Prime] {P K : Subgroup G} : IsSylowOf p (P.map f) (K.map f) ↔ IsSylowOf p P K := by
  rw [isSylowOf_iff, isSylowOf_iff, Subgroup.map_le_map_iff_of_injective hf,
    Subgroup.relIndex_map_map_of_injective P K hf]
  constructor
  · rintro ⟨hle, hP, hdvd⟩
    exact ⟨hle, hP.of_equiv (Subgroup.equivMapOfInjective P f hf).symm, hdvd⟩
  · rintro ⟨hle, hP, hdvd⟩
    exact ⟨hle, hP.map f, hdvd⟩

omit [Finite H] in
theorem IsSylowOf.map_hom {p : ℕ} [Fact p.Prime] (f : G →* H) {Y P : Subgroup G}
    (h : IsSylowOf p P Y) : IsSylowOf p (P.map f) (Y.map f) := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow_eq_subgroupOf
  have hsurj : Function.Surjective (f.subgroupMap Y) := f.subgroupMap_surjective Y
  let Q' : Sylow p ↥(Y.map f) := Q.mapSurjective hsurj
  refine ⟨Q', ?_⟩
  have h1 : (Q' : Subgroup ↥(Y.map f)) = Q.map (f.subgroupMap Y) := rfl
  have hcomp : (Y.map f).subtype.comp (f.subgroupMap Y) = f.comp Y.subtype := by
    ext x
    rfl
  rw [h1, hQ, Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr h.le]

end SylowMap

theorem exists_mem_normalizer_of_sylow_comap {N Z : Type*} [Group N] [Finite N] [Group Z]
    (f : N →* Z) {S : Subgroup N} (hS : IsSylowOf 2 S ((S.map f).comap f)) {m : N}
    (hm : ∀ z ∈ S.map f, f m * z * (f m)⁻¹ ∈ S.map f) :
    ∃ k ∈ (S.map f).comap f, k⁻¹ * m ∈ normalizer (S : Set N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ y : N, y ∈ S.map (MulAut.conj m).toMonoidHom ↔ m⁻¹ * y * m ∈ S := by
    intro y
    constructor
    · rintro ⟨s, hs, rfl⟩
      have : m⁻¹ * (MulAut.conj m).toMonoidHom s * m = s := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this]
      exact hs
    · intro hy
      refine ⟨m⁻¹ * y * m, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hle : S.map (MulAut.conj m).toMonoidHom ≤ (S.map f).comap f := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hy
    show f ((MulAut.conj m) s) ∈ S.map f
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    exact hm _ ⟨s, hs, rfl⟩
  have hcard : Nat.card (S.map (MulAut.conj m).toMonoidHom) =
      2 ^ (Nat.card ((S.map f).comap f)).factorization 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]
    exact hS.card_eq
  have hS' : IsSylowOf 2 (S.map (MulAut.conj m).toMonoidHom) ((S.map f).comap f) :=
    isSylowOf_of_card hle hcard
  obtain ⟨k, hk, hconj⟩ := hS.exists_mem_conj hS'
  refine ⟨k, hk, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 : y ∈ S ↔ m * y * m⁻¹ ∈ S.map (MulAut.conj m).toMonoidHom := by
    rw [hmem]
    have : m⁻¹ * (m * y * m⁻¹) * m = y := by group
    rw [this]
  have h2 : (k⁻¹ * m) * y * (k⁻¹ * m)⁻¹ = k⁻¹ * (m * y * m⁻¹) * k := by group
  rw [h2, h1, hconj]

section Frob

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

variable (F) in
@[expose] noncomputable def frobPow (j : ℕ) : RingAut F := iterateFrobeniusEquiv F 2 j

theorem frobPow_apply (j : ℕ) (a : F) : frobPow F j a = a ^ 2 ^ j := by
  simp [frobPow, iterateFrobeniusEquiv_apply, iterateFrobenius_def]

theorem frobPow_add (i j : ℕ) : frobPow F (i + j) = frobPow F i * frobPow F j := by
  ext a
  show frobPow F (i + j) a = frobPow F i (frobPow F j a)
  rw [frobPow_apply, frobPow_apply, frobPow_apply, ← pow_mul, ← pow_add, add_comm]

theorem frobPow_zero : frobPow F 0 = 1 := by
  ext a
  rw [frobPow_apply]
  simp

theorem frobPow_four (hF : Nat.card F = 16) : frobPow F 4 = 1 := by
  ext a
  rw [frobPow_apply]
  exact Nat16.pow_two_pow_four hF a

theorem frobPow_two_mul_self (hF : Nat.card F = 16) : frobPow F 2 * frobPow F 2 = 1 := by
  rw [← frobPow_add]
  exact frobPow_four hF

theorem frobPow_two_ne_one (hF : Nat.card F = 16) : frobPow F 2 ≠ 1 := by
  obtain ⟨z, hz⟩ := Weights16.exists_pow_four_eq hF
  intro h
  have h1 := congrArg (fun τ : RingAut F => τ z) h
  simp only [frobPow_apply] at h1
  have h2 : z ^ 4 = z := by simpa using h1
  rw [hz] at h2
  simp at h2

end Frob

section SemiLin

variable {F : Type*} [Field F]

@[expose] def SemiLin (φs : F →+* Module.End (ZMod 2) (Fin 8 → ZMod 2))
    (n : GL (Fin 8) (ZMod 2)) (τ : RingAut F) : Prop :=
  ∀ (a : F) (v : Fin 8 → ZMod 2), (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (φs a v) =
    φs (τ a) ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)

variable {φs : F →+* Module.End (ZMod 2) (Fin 8 → ZMod 2)} {n n' : GL (Fin 8) (ZMod 2)}
  {τ τ' : RingAut F}

theorem SemiLin.one : SemiLin φs 1 (1 : RingAut F) := by
  intro a v
  simp

theorem SemiLin.mul (h : SemiLin φs n τ) (h' : SemiLin φs n' τ') :
    SemiLin φs (n * n') (τ * τ') := by
  intro a v
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h' a v, h, Matrix.mulVec_mulVec, ← Units.val_mul]
  rfl

theorem SemiLin.unique (h : SemiLin φs n τ) (h' : SemiLin φs n τ') : τ = τ' := by
  refine RingEquiv.ext fun a => φs.injective (LinearMap.ext fun w => ?_)
  have hw : (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      (((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w) = w := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have e1 := h a (((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w)
  have e2 := h' a (((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w)
  rw [hw] at e1 e2
  exact e1.symm.trans e2

open Classical in
@[expose] noncomputable def semiAut (φs : F →+* Module.End (ZMod 2) (Fin 8 → ZMod 2))
    (n : GL (Fin 8) (ZMod 2)) : RingAut F :=
  if h : ∃ τ, SemiLin φs n τ then Classical.choose h else 1

theorem semiLin_semiAut (h : ∃ τ, SemiLin φs n τ) : SemiLin φs n (semiAut φs n) := by
  unfold semiAut
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

theorem semiAut_eq (h : SemiLin φs n τ) : semiAut φs n = τ :=
  (semiLin_semiAut ⟨τ, h⟩).unique h

theorem semiAut_mul (h : SemiLin φs n τ) (h' : SemiLin φs n' τ') :
    semiAut φs (n * n') = semiAut φs n * semiAut φs n' := by
  rw [semiAut_eq h, semiAut_eq h', semiAut_eq (h.mul h')]

theorem SemiLin.isSemilinear [Finite F] [CharP F 2] {Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)}
    (hΦ : ∀ (a : F) (v : Fin 8 → ZMod 2), Φ (φs a v) = a • Φ v) {j : ℕ}
    (h : SemiLin φs n (frobPow F j)) :
    Nat16.IsSemilinear j (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      (Φ.symm w))) := by
  intro a w
  have h1 : Φ.symm (a • w) = φs a (Φ.symm w) := by
    apply Φ.injective
    rw [hΦ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  show Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Φ.symm (a • w))) =
    a ^ 2 ^ j • Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Φ.symm w))
  rw [h1, h a, hΦ, frobPow_apply]

end SemiLin

section UPlus

variable {F : Type*} [Field F]

@[expose] def uPlus (F : Type*) [Field F] : Subgroup SL(2, F) where
  carrier := Set.range (Nat16.uE (F := F))
  one_mem' := ⟨0, Nat16.uE_zero⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c', Nat16.uE_add c c'⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [eq_inv_iff_mul_eq_one, ← Nat16.uE_add, neg_add_cancel, Nat16.uE_zero]

theorem uE_mem_uPlus (c : F) : Nat16.uE c ∈ uPlus F := ⟨c, rfl⟩

theorem card_uPlus (hF : Nat.card F = 16) : Nat.card (uPlus F) = 16 := by
  have h : Nat.card (Set.range (Nat16.uE (F := F))) = Nat.card F :=
    Nat.card_range_of_injective Nat16.uE_injective
  exact h.trans hF

theorem isSylowOf_uPlus [Finite F] (hF : Nat.card F = 16) : IsSylowOf 2 (uPlus F) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨le_top, IsPGroup.of_card (n := 4) (by rw [card_uPlus hF]; norm_num), ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h1 := Subgroup.card_mul_index (uPlus F)
  rw [card_uPlus hF, Nat16.card_SL2 hF] at h1
  have h2 : (uPlus F).index = 255 := by omega
  rw [h2]
  omega

theorem exists_rhohat_adapted [Finite F] (hF : Nat.card F = 16)
    {Hgl Q : Subgroup (GL (Fin 8) (ZMod 2))} (e : SL(2, F) ≃* ↥Hgl) (hQ : IsSylowOf 2 Q Hgl) :
    ∃ rhat : SL(2, F) →* GL (Fin 8) (ZMod 2), Function.Injective rhat ∧ rhat.range = Hgl ∧
      (uPlus F).map rhat = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFin : Finite SL(2, F) := inferInstance
  have hQle : Q ≤ Hgl := hQ.le
  have hQ₀ : IsSylowOf 2 (Q.subgroupOf Hgl) ⊤ := by
    rw [← isSylowOf_map_subtype_iff Hgl, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQle,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hQ
  have hQ₁ : IsSylowOf 2 ((Q.subgroupOf Hgl).map e.symm.toMonoidHom) ⊤ := by
    have := (isSylowOf_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective
      (p := 2) (P := Q.subgroupOf Hgl) (K := ⊤)).2 hQ₀
    rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at this
  obtain ⟨g, -, hg⟩ := (isSylowOf_uPlus hF).exists_mem_conj hQ₁
  let rhat : SL(2, F) →* GL (Fin 8) (ZMod 2) :=
    Hgl.subtype.comp (e.toMonoidHom.comp (MulAut.conj g).toMonoidHom)
  have hrhat : ∀ x, rhat x = ((e (g * x * g⁻¹) : ↥Hgl) : GL (Fin 8) (ZMod 2)) := fun x => rfl
  refine ⟨rhat, ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : e (g * x * g⁻¹) = e (g * y * g⁻¹) := Subtype.ext (by rwa [hrhat, hrhat] at hxy)
    have h2 := e.injective h1
    simpa using h2
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [hrhat]
      exact (e (g * x * g⁻¹)).2
    · intro hy
      refine ⟨g⁻¹ * e.symm ⟨y, hy⟩ * g, ?_⟩
      have h1 : g * (g⁻¹ * e.symm ⟨y, hy⟩ * g) * g⁻¹ = e.symm ⟨y, hy⟩ := by group
      rw [hrhat, h1, MulEquiv.apply_symm_apply]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hz : g * x * g⁻¹ ∈ (Q.subgroupOf Hgl).map e.symm.toMonoidHom := by
        rw [hg]
        have h1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [h1]
        exact hx
      obtain ⟨q, hq, hqz⟩ := hz
      rw [hrhat]
      have : e (g * x * g⁻¹) = q := by
        rw [← hqz]
        exact e.apply_symm_apply q
      rw [this]
      exact mem_subgroupOf.mp hq
    · intro hy
      have hz : e.symm ⟨y, hQle hy⟩ ∈ (Q.subgroupOf Hgl).map e.symm.toMonoidHom :=
        ⟨⟨y, hQle hy⟩, mem_subgroupOf.mpr hy, rfl⟩
      rw [hg] at hz
      refine ⟨g⁻¹ * e.symm ⟨y, hQle hy⟩ * g, hz, ?_⟩
      have h1 : g * (g⁻¹ * e.symm ⟨y, hQle hy⟩ * g) * g⁻¹ = e.symm ⟨y, hQle hy⟩ := by group
      rw [hrhat, h1, MulEquiv.apply_symm_apply]

end UPlus

section NatStrSection

variable {F : Type*} [Field F]

structure NatStr (rhat : SL(2, F) →* GL (Fin 8) (ZMod 2))
    (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (φs : F →+* Module.End (ZMod 2) (Fin 8 → ZMod 2)) :
    Prop where
  smul : ∀ (a : F) (v : Fin 8 → ZMod 2), Φ (φs a v) = a • Φ v
  comm : ∀ (g : SL(2, F)) (a : F) (v : Fin 8 → ZMod 2),
    (rhat g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (φs a v) =
      φs a ((rhat g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)
  nat : ∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
    Φ ((rhat g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) =
      (g : Matrix (Fin 2) (Fin 2) F).mulVec (Φ v)
  uE : ∀ (c : F) (v : Fin 8 → ZMod 2),
    Φ ((rhat (Nat16.uE c) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) =
      ![Φ v 0 + c * Φ v 1, Φ v 1]
  two_elt : ∀ n : GL (Fin 8) (ZMod 2),
    (∀ (a : F) (v : Fin 8 → ZMod 2), (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (φs a v) =
      φs a ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)) →
    (∃ m : ℕ, n ^ 2 ^ m = 1) → ∃ g : SL(2, F), rhat g = n
  norm : ∀ n : GL (Fin 8) (ZMod 2), (∀ g : SL(2, F), ∃ g' : SL(2, F), n * rhat g * n⁻¹ = rhat g') →
    ∃ j : ZMod 4, ∀ (a : F) (v : Fin 8 → ZMod 2),
      (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (φs a v) =
        φs (a ^ 2 ^ j.val) ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)

theorem exists_natStr (hF : Nat.card F = 16) (rhat : SL(2, F) →* GL (Fin 8) (ZMod 2))
    (hinj : Function.Injective rhat) {x₃ : SL(2, F)} (hx₃ : orderOf x₃ = 3)
    (hfpf : ∀ v : Fin 8 → ZMod 2,
      (rhat x₃ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v → v = 0) :
    ∃ (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F))
      (φs : F →+* Module.End (ZMod 2) (Fin 8 → ZMod 2)), NatStr rhat Φ φs := by
  obtain ⟨Φ, φs, h1, h2, h3, h4, -, h6, h7⟩ := Nat16.exists_F16_structure hF rhat hinj hx₃ hfpf
  exact ⟨Φ, φs, ⟨h1, h2, h3, h4, h6, h7⟩⟩

variable {rhat : SL(2, F) →* GL (Fin 8) (ZMod 2)} {Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)}
  {φs : F →+* Module.End (ZMod 2) (Fin 8 → ZMod 2)}

theorem NatStr.exists_semiLin [Finite F] [CharP F 2] (N : NatStr rhat Φ φs)
    {n : GL (Fin 8) (ZMod 2)} (hn : ∀ g : SL(2, F), ∃ g' : SL(2, F), n * rhat g * n⁻¹ = rhat g') :
    ∃ j : ℕ, j < 4 ∧ SemiLin φs n (frobPow F j) := by
  obtain ⟨j, hj⟩ := N.norm n hn
  refine ⟨j.val, ZMod.val_lt j, fun a v => ?_⟩
  rw [hj a v, frobPow_apply]

end NatStrSection

end CFSG.OddStandard.Seitz77
