module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBCommon
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBFrameData

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open
open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.LieType.Chevalley (SL2 uSL vSL HSL WSL)
open scoped commutatorElement

section Involution

variable {G : Type} [Group G] {t : G}

theorem mem_map_conj_iff (ht : t * t = 1) {H : Subgroup G} {x : G} :
    x ∈ H.map (MulAut.conj t).toMonoidHom ↔ t * x * t ∈ H := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, htinv,
      show t * (t * y * t) * t = (t * t) * y * (t * t) by group, ht, one_mul, mul_one]
    exact hy
  · intro hx
    refine ⟨t * x * t, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, htinv,
      show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ht, one_mul, mul_one]

theorem conj_mem_map_conj (ht : t * t = 1) {H : Subgroup G} {x : G} (hx : x ∈ H) :
    t * x * t ∈ H.map (MulAut.conj t).toMonoidHom := by
  rw [mem_map_conj_iff ht, show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ht, one_mul,
    mul_one]
  exact hx

theorem map_conj_map_conj (ht : t * t = 1) (H : Subgroup G) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  ext x
  rw [mem_map_conj_iff ht, mem_map_conj_iff ht,
    show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ht, one_mul, mul_one]

@[expose] def diagHom (ht : t * t = 1) {M : Subgroup G}
    (hM : ∀ x ∈ M, ∀ y ∈ M.map (MulAut.conj t).toMonoidHom, x * y = y * x) : M →* G where
  toFun x := x * (t * x * t)
  map_one' := by simp [ht]
  map_mul' x y := by
    have hc : (y : G) * (t * x * t) = (t * x * t) * y :=
      hM y y.2 _ (conj_mem_map_conj ht x.2)
    simp only [Subgroup.coe_mul]
    have e : t * ((x : G) * y) * t = (t * x * t) * (t * y * t) := by
      rw [show (t * x * t) * (t * y * t) = t * x * (t * t) * y * t by group, ht, mul_one]
      group
    calc (x : G) * y * (t * (x * y) * t) = x * (y * (t * x * t)) * (t * y * t) := by
          rw [e]
          group
      _ = x * ((t * x * t) * y) * (t * y * t) := by rw [hc]
      _ = x * (t * x * t) * (y * (t * y * t)) := by group

theorem diagHom_apply (ht : t * t = 1) {M : Subgroup G}
    (hM : ∀ x ∈ M, ∀ y ∈ M.map (MulAut.conj t).toMonoidHom, x * y = y * x) (x : M) :
    diagHom ht hM x = x * (t * x * t) := rfl

theorem diagHom_injective (ht : t * t = 1) {M : Subgroup G}
    (hM : ∀ x ∈ M, ∀ y ∈ M.map (MulAut.conj t).toMonoidHom, x * y = y * x)
    (hinf : M ⊓ M.map (MulAut.conj t).toMonoidHom = ⊥) : Function.Injective (diagHom ht hM) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [diagHom_apply] at hx
  have hx' : (x : G) = t * (x : G)⁻¹ * t := by
    calc (x : G) = (t * x * t)⁻¹ := eq_inv_of_mul_eq_one_left hx
      _ = t⁻¹ * (x : G)⁻¹ * t⁻¹ := by group
      _ = t * (x : G)⁻¹ * t := by rw [inv_eq_of_mul_eq_one_right ht]
  have hmem : (x : G) ∈ M ⊓ M.map (MulAut.conj t).toMonoidHom :=
    ⟨x.2, by rw [hx']; exact conj_mem_map_conj ht (inv_mem x.2)⟩
  rw [hinf, mem_bot] at hmem
  exact Subtype.ext hmem

theorem conj_mul_conj_eq {g : G} (hg : g * t = t * g) (x : G) :
    g * x * g⁻¹ * (t * (g * x * g⁻¹) * t) = g * (x * (t * x * t)) * g⁻¹ := by
  have hg' : g⁻¹ * t = t * g⁻¹ := by
    calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hg]
      _ = t * g⁻¹ := by group
  calc g * x * g⁻¹ * (t * (g * x * g⁻¹) * t) = g * x * g⁻¹ * ((t * g) * x * (g⁻¹ * t)) := by
        group
    _ = g * x * g⁻¹ * ((g * t) * x * (t * g⁻¹)) := by rw [hg, hg']
    _ = g * (x * (t * x * t)) * g⁻¹ := by group

end Involution

section Products

variable {G : Type*} [Group G]

theorem card_sup_of_commute {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    (hinf : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hc' : ∀ (m : ↥H) (n : ↥K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hc m.1 m.2 n.1 n.2
  let φ := MonoidHom.noncommCoprod H.subtype K.subtype hc'
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hinf
  have hrange : φ.range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {g : G}
    (hg : g ∈ H ⊔ K) : ∃ x ∈ H, ∃ y ∈ K, g = x * y := by
  have hle : H ≤ normalizer (K : Set G) := fun x hx =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => (hc x hx y hy).symm)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H K hle, Set.mem_mul] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  exact ⟨x, hx, y, hy, rfl⟩

theorem eq_and_eq_of_mul_eq {H K : Subgroup G} (hinf : H ⊓ K = ⊥) {x x' y y' : G} (hx : x ∈ H)
    (hx' : x' ∈ H) (hy : y ∈ K) (hy' : y' ∈ K) (h : x * y = x' * y') : x = x' ∧ y = y' := by
  have h1 : x'⁻¹ * x = y' * y⁻¹ := by
    calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
      _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h]
      _ = y' * y⁻¹ := by group
  have h2 : x'⁻¹ * x ∈ H ⊓ K :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx') hx, h1 ▸ mul_mem hy' (inv_mem hy)⟩
  rw [hinf, mem_bot] at h2
  have hxx : x = x' := by rw [← mul_inv_cancel_left x' x, h2, mul_one]
  subst hxx
  exact ⟨rfl, mul_left_cancel h⟩

theorem commutatorElement_mul_mul {x y z z' : G} (h1 : z * y = y * z) (h2 : z * z' = z' * z)
    (h3 : z' * x = x * z') : ⁅x * z, y * z'⁆ = ⁅x, y⁆ := by
  have e1 : z * (y * z') * z⁻¹ = y * z' := by
    calc z * (y * z') * z⁻¹ = (z * y) * z' * z⁻¹ := by group
      _ = y * (z * z') * z⁻¹ := by rw [h1]; group
      _ = y * z' := by rw [h2]; group
  have e2 : z' * x⁻¹ * z'⁻¹ = x⁻¹ := by
    have h3' : z' * x⁻¹ = x⁻¹ * z' := by
      calc z' * x⁻¹ = x⁻¹ * (x * z') * x⁻¹ := by group
        _ = x⁻¹ * (z' * x) * x⁻¹ := by rw [h3]
        _ = x⁻¹ * z' := by group
    rw [h3', mul_inv_cancel_right]
  calc ⁅x * z, y * z'⁆ = x * (z * (y * z') * z⁻¹) * x⁻¹ * z'⁻¹ * y⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * y * (z' * x⁻¹ * z'⁻¹) * y⁻¹ := by rw [e1]; group
    _ = ⁅x, y⁆ := by rw [e2, commutatorElement_def]

end Products

section Factors

variable {H : Type*} [Group H]

theorem center_eq_bot_of_isSimpleGroup {P : Type*} [Group P] [IsSimpleGroup P] {a b : P}
    (hab : a * b ≠ b * a) : center P = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center P) with h | h
  · exact h
  · exact absurd ((mem_center_iff.1 (h ▸ mem_top b)) a) hab

theorem map_conj_mul_self (g : H) (X : Subgroup H) :
    X.map (MulAut.conj (g * g)).toMonoidHom =
      (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp, Function.comp_apply]
  group

variable [Finite H]

theorem map_conj_eq_or_eq {P Q : Subgroup H} [IsSimpleGroup P] (hPZ : center P = ⊥)
    (hcard : Nat.card P = Nat.card Q) (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) {g : H}
    (hg : ∀ x ∈ P ⊔ Q, g * x * g⁻¹ ∈ P ⊔ Q) :
    P.map (MulAut.conj g).toMonoidHom = P ∨ P.map (MulAut.conj g).toMonoidHom = Q := by
  set N := P.map (MulAut.conj g).toMonoidHom with hN
  have hcardN : Nat.card N = Nat.card P := card_map_of_injective (MulAut.conj g).injective
  have hPE : ∀ e ∈ P ⊔ Q, ∀ x ∈ P, e * x * e⁻¹ ∈ P := by
    have hle : P ⊔ Q ≤ normalizer (P : Set H) := sup_le le_normalizer fun y hy =>
      centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => hc x hx y hy)
    intro e he x hx
    exact (mem_normalizer_iff.1 (hle he) x).1 hx
  have hgn : g ∈ normalizer ((P ⊔ Q : Subgroup H) : Set H) := mem_normalizer_fintype hg
  have hNE : N ≤ P ⊔ Q := fun _ ⟨x, hx, hxg⟩ => hxg ▸ hg x (mem_sup_left hx)
  have hNn : ∀ e ∈ P ⊔ Q, ∀ n ∈ N, e * n * e⁻¹ ∈ N := by
    rintro e he _ ⟨x, hx, rfl⟩
    have he' : g⁻¹ * e * g ∈ P ⊔ Q := by
      have := (mem_normalizer_iff.1 (inv_mem hgn) e).1 he
      rwa [inv_inv] at this
    refine ⟨(g⁻¹ * e * g) * x * (g⁻¹ * e * g)⁻¹, hPE _ he' x hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hNP : ((N ⊓ P).subgroupOf P).Normal := ⟨fun n hn x => by
    rw [mem_subgroupOf] at hn ⊢
    exact Subgroup.mem_inf.2 ⟨hNn x (mem_sup_left x.2) n (mem_inf.1 hn).1,
      mul_mem (mul_mem x.2 (mem_inf.1 hn).2) (inv_mem x.2)⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ P).subgroupOf P) with h | h
  · right
    have hinf : ∀ x ∈ N, x ∈ P → x = 1 := fun x hxN hxP => by
      have : (⟨x, hxP⟩ : P) ∈ (N ⊓ P).subgroupOf P := mem_subgroupOf.2 (mem_inf.2 ⟨hxN, hxP⟩)
      rw [h, mem_bot] at this
      exact congrArg Subtype.val this
    have hcomm : ∀ n ∈ N, ∀ x ∈ P, n * x = x * n := by
      intro n hn x hx
      have h1 : n * x * n⁻¹ * x⁻¹ = 1 := hinf _
        (by
          rw [show n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) by group]
          exact mul_mem hn (hNn x (mem_sup_left hx) _ (inv_mem hn)))
        (mul_mem (hPE n (hNE hn) x hx) (inv_mem hx))
      calc n * x = n * x * n⁻¹ * x⁻¹ * (x * n) := by group
        _ = x * n := by rw [h1, one_mul]
    have hNQ : N ≤ Q := by
      intro n hn
      obtain ⟨p, hp, y, hy, rfl⟩ := exists_mul_of_mem_sup hc (hNE hn)
      have hpZ : (⟨p, hp⟩ : P) ∈ center P := mem_center_iff.2 fun z => Subtype.ext (by
        have h1 := hcomm _ hn z z.2
        have h2 := hc z z.2 y hy
        have h3 : p * z * y = z * p * y := by
          calc p * z * y = p * y * z := by rw [mul_assoc, h2, ← mul_assoc]
            _ = z * (p * y) := h1
            _ = z * p * y := by rw [mul_assoc]
        exact (mul_right_cancel h3).symm)
      rw [hPZ, mem_bot] at hpZ
      have hp1 : p = 1 := congrArg Subtype.val hpZ
      rw [hp1, one_mul]
      exact hy
    exact eq_of_le_of_card_ge hNQ (by rw [hcardN, hcard])
  · left
    have hPN : P ≤ N := fun x hx => by
      have : (⟨x, hx⟩ : P) ∈ (N ⊓ P).subgroupOf P := by rw [h]; exact mem_top _
      exact (mem_inf.1 (mem_subgroupOf.1 this)).1
    exact (eq_of_le_of_card_ge hPN hcardN.le).symm

theorem map_conj_mul_self_eq {P Q : Subgroup H} [IsSimpleGroup P] [IsSimpleGroup Q]
    (hPZ : center P = ⊥) (hQZ : center Q = ⊥) (hcard : Nat.card P = Nat.card Q)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) (hinf : P ⊓ Q = ⊥) {g : H}
    (hg : ∀ x ∈ P ⊔ Q, g * x * g⁻¹ ∈ P ⊔ Q) :
    P.map (MulAut.conj (g * g)).toMonoidHom = P := by
  have hc' : ∀ x ∈ Q, ∀ y ∈ P, x * y = y * x := fun x hx y hy => (hc y hy x hx).symm
  have hg' : ∀ x ∈ Q ⊔ P, g * x * g⁻¹ ∈ Q ⊔ P := by rw [sup_comm]; exact hg
  rw [map_conj_mul_self]
  rcases map_conj_eq_or_eq hPZ hcard hc hg with h | h
  · rw [h, h]
  · rcases map_conj_eq_or_eq hQZ hcard.symm hc' hg' with h' | h'
    · exfalso
      have hPQ : P = Q := Subgroup.map_injective (MulAut.conj g).injective (h.trans h'.symm)
      have hbot : P = ⊥ := by rw [← hinf, ← hPQ, inf_idem]
      exact (Subgroup.nontrivial_iff_ne_bot P).1 inferInstance hbot
    · rw [h, h']

end Factors

namespace CaseBNotation

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}
  {K : Type} [Field K] {w : WData d Vi q} {D : LeviData A Vi K}

@[expose] noncomputable def δ (N : CaseBNotation w D) : N.M₁ →* G :=
  diagHom d.t_mul_self N.M₁_comm

theorem δ_apply (N : CaseBNotation w D) (x : N.M₁) : N.δ x = x * (d.t * x * d.t) := rfl

theorem δ_injective (N : CaseBNotation w D) : Function.Injective N.δ :=
  diagHom_injective d.t_mul_self N.M₁_comm N.M₁_inf

theorem W₁_le_M₁ (N : CaseBNotation w D) : N.W₁ ≤ N.M₁ := N.M₁_eq ▸ le_sup_left

theorem ℓ_range_le_M₁ (N : CaseBNotation w D) : N.ℓ.range ≤ N.M₁ := N.M₁_eq ▸ le_sup_right

theorem δ_ℓ (N : CaseBNotation w D) (B : SL2 K) : N.δ ⟨N.ℓ B, N.ℓ_mem B⟩ = D.lev B := N.diag B

theorem conj_t_mem_W (w : WData d Vi q) {x : G} (hx : x ∈ w.W) : d.t * x * d.t ∈ w.W := by
  have := (mem_normalizer_iff.mp w.t_norm x).mp hx
  rwa [inv_eq_of_mul_eq_one_right d.t_mul_self] at this

theorem inv_eq_self_of_mem_W (w : WData d Vi q) {x : G} (hx : x ∈ w.W) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact w.elem.2 x hx)

theorem δ_W₁ (N : CaseBNotation w D) {x : G} (hx : x ∈ N.W₁) :
    N.δ ⟨x, N.W₁_le_M₁ hx⟩ = d.t * x * d.t * x⁻¹ := by
  have hxW : x ∈ w.W := N.W₁_le hx
  rw [δ_apply, inv_eq_self_of_mem_W w hxW]
  exact comm_of_isElemAbelian w.elem hxW (conj_t_mem_W w hxW)

theorem exists_δ_W₁ (N : CaseBNotation w D) {v : G} (hv : v ∈ Vi) :
    ∃ x : N.M₁, (x : G) ∈ N.W₁ ∧ N.δ x = v := by
  obtain ⟨x, ⟨hx, hxv⟩, -⟩ := N.bij v hv
  exact ⟨⟨x, N.W₁_le_M₁ hx⟩, hx, by rw [N.δ_W₁ hx, hxv]⟩

@[expose] noncomputable def δpre (N : CaseBNotation w D) (X : Subgroup G) : Subgroup G :=
  (X.comap N.δ).map N.M₁.subtype

theorem mem_δpre (N : CaseBNotation w D) {X : Subgroup G} {x : G} :
    x ∈ N.δpre X ↔ ∃ h : x ∈ N.M₁, N.δ ⟨x, h⟩ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem δpre_le (N : CaseBNotation w D) (X : Subgroup G) : N.δpre X ≤ N.M₁ := fun _ hx =>
  (N.mem_δpre.1 hx).1

theorem card_δpre (N : CaseBNotation w D) {X : Subgroup G} (hX : X ≤ N.δ.range) :
    Nat.card (N.δpre X) = Nat.card X := by
  rw [δpre, Subgroup.card_map_of_injective N.M₁.subtype_injective,
    ← Subgroup.card_map_of_injective N.δ_injective, Subgroup.map_comap_eq, inf_eq_right.2 hX]

end CaseBNotation

theorem uSL_mul_vSL_ne {K : Type} [Field K] : (uSL 1 * vSL 1 : SL2 K) ≠ vSL 1 * uSL 1 := by
  intro h
  have := congrArg (fun B : SL2 K => (B : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [CFSG.LieType.Chevalley.coe_uSL, CFSG.LieType.Chevalley.coe_vSL, Matrix.mul_apply,
    Fin.sum_univ_two] at this

theorem HSL_mul_HSL {K : Type} [Field K] (a b : Kˣ) : (HSL a * HSL b : SL2 K) = HSL (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Chevalley.coe_HSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem pow_eq_one_of_mem_inf_sup {G : Type*} [Group G] {X Y S : Subgroup G}
    (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hinf : X ⊓ Y = ⊥)
    (hSY : S ≤ normalizer (Y : Set G)) {n : ℕ} (hS : ∀ s ∈ S, s ^ n = 1) {x : G}
    (hx : x ∈ X ⊓ (S ⊔ Y)) : x ^ n = 1 := by
  obtain ⟨hxX, hxSY⟩ := mem_inf.1 hx
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right S Y hSY, Set.mem_mul] at hxSY
  obtain ⟨s, hs, y, hy, rfl⟩ := hxSY
  have hcomm : Commute (s * y) y⁻¹ := hc _ hxX _ (inv_mem hy)
  have h1 : s ^ n = (s * y) ^ n * y⁻¹ ^ n := by
    rw [← hcomm.mul_pow, mul_inv_cancel_right]
  rw [hS s hs, inv_pow] at h1
  have h2 : (s * y) ^ n = y ^ n := (eq_of_mul_inv_eq_one h1.symm)
  have h3 : (s * y) ^ n ∈ X ⊓ Y := mem_inf.2 ⟨pow_mem hxX n, h2 ▸ pow_mem hy n⟩
  rw [hinf, mem_bot] at h3
  exact h3

theorem perfect_Ebar {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
    {q : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 3 ≤ Nat.card K)
    (w : WData d Vi q) (D : LeviData A Vi K) :
    ⁅w.Ebar D.lev.range, w.Ebar D.lev.range⁆ = w.Ebar D.lev.range := by
  have hLperf : ⁅w.Lbar D.lev.range, w.Lbar D.lev.range⁆ = w.Lbar D.lev.range := by
    obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) hK
    have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ :=
      Matrix.SL2.commutator_eq_top μ.ne_zero (sq_ne_one_of_charTwo hμ)
    rw [← w.range_levBar D, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hperf]
  refine le_antisymm (commutator_le_left _ _) (normalClosure_le_normal ?_)
  intro x hx
  have hx' : x ∈ ⁅w.Lbar D.lev.range, w.Lbar D.lev.range⁆ := by rw [hLperf]; exact hx
  exact commutator_mono le_normalClosure le_normalClosure hx'

namespace CaseBNotation

section Factors

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}
  {K : Type} [Field K] {w : WData d Vi q} {D : LeviData A Vi K}

@[expose] def Pbar (N : CaseBNotation w D) : Subgroup w.Nbar := N.σ.range

@[expose] def Qbar (N : CaseBNotation w D) : Subgroup w.Nbar :=
  N.Pbar.map (MulAut.conj w.tbar).toMonoidHom

theorem mem_Qbar (N : CaseBNotation w D) {x : w.Nbar} :
    x ∈ N.Qbar ↔ w.tbar * x * w.tbar ∈ N.Pbar :=
  mem_map_conj_iff (CaseBModule.tbar_mul_self w)

theorem conj_tbar_tbar (w : WData d Vi q) (x : w.Nbar) :
    w.tbar * (w.tbar * x * w.tbar) * w.tbar = x := by
  rw [show w.tbar * (w.tbar * x * w.tbar) * w.tbar = (w.tbar * w.tbar) * x * (w.tbar * w.tbar) by
    group, CaseBModule.tbar_mul_self w, one_mul, mul_one]

theorem tbar_σ_mem_Qbar (N : CaseBNotation w D) (B : SL2 K) :
    w.tbar * N.σ B * w.tbar ∈ N.Qbar :=
  N.mem_Qbar.2 (by rw [conj_tbar_tbar]; exact ⟨B, rfl⟩)

theorem Pbar_Qbar_comm (N : CaseBNotation w D) : ∀ x ∈ N.Pbar, ∀ y ∈ N.Qbar, x * y = y * x := by
  rintro _ ⟨B, rfl⟩ y hy
  obtain ⟨B', hB'⟩ := N.mem_Qbar.1 hy
  have hy' : y = w.tbar * N.σ B' * w.tbar := by rw [hB', conj_tbar_tbar]
  rw [hy']
  exact N.σ_comm B B'

theorem Pbar_inf_Qbar (N : CaseBNotation w D) : N.Pbar ⊓ N.Qbar = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨B, rfl⟩, hx⟩
  obtain ⟨B', hB'⟩ := N.mem_Qbar.1 hx
  have h : N.σ B = w.tbar * N.σ B' * w.tbar := by rw [hB', conj_tbar_tbar]
  rw [N.σ_disj B B' h, map_one]
  exact one_mem _

theorem Pbar_sup_le_Ebar (N : CaseBNotation w D) : N.Pbar ⊔ N.Qbar ≤ w.Ebar D.lev.range := by
  have hn : (w.Ebar D.lev.range).Normal := normalClosure_normal
  refine sup_le ?_ fun y hy => ?_
  · rintro _ ⟨B, rfl⟩
    exact N.σ_mem B
  · obtain ⟨B, hB⟩ := N.mem_Qbar.1 hy
    have hy' : y = w.tbar * N.σ B * w.tbar⁻¹ := by
      rw [hB, CaseBModule.tbar_inv w, conj_tbar_tbar]
    rw [hy']
    exact hn.conj_mem _ (N.σ_mem B) _

theorem Ebar_eq [Finite K] [CharP K 2] (N : CaseBNotation w D) (hK : 3 ≤ Nat.card K) :
    w.Ebar D.lev.range = N.Pbar ⊔ N.Qbar := by
  refine le_antisymm ?_ N.Pbar_sup_le_Ebar
  have hO : standardComponentOddCore w.Nbar ≤ centralizer (w.Ebar D.lev.range : Set w.Nbar) :=
    commutator_eq_bot_iff_le_centralizer.mp N.oddCore_comm
  have hdec : ∀ x ∈ w.Ebar D.lev.range, ∃ p ∈ N.Pbar ⊔ N.Qbar,
      ∃ z ∈ standardComponentOddCore w.Nbar, x = p * z := by
    intro x hx
    obtain ⟨B, B', hBB⟩ := N.σ_onto x hx
    refine ⟨N.σ B * (w.tbar * N.σ B' * w.tbar),
      mul_mem (mem_sup_left ⟨B, rfl⟩) (mem_sup_right (N.tbar_σ_mem_Qbar B')), _, ?_,
      (mul_inv_cancel_left _ _).symm⟩
    exact QuotientGroup.eq.1 hBB.symm
  rw [← perfect_Ebar hK w D]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  obtain ⟨p, hp, z, hz, rfl⟩ := hdec a ha
  obtain ⟨p', hp', z', hz', rfl⟩ := hdec b hb
  have hpE := N.Pbar_sup_le_Ebar hp
  have hp'E := N.Pbar_sup_le_Ebar hp'
  have hzE : z ∈ w.Ebar D.lev.range := by
    have := mul_mem (inv_mem hpE) ha
    rwa [inv_mul_cancel_left] at this
  have hz'E : z' ∈ w.Ebar D.lev.range := by
    have := mul_mem (inv_mem hp'E) hb
    rwa [inv_mul_cancel_left] at this
  rw [commutatorElement_mul_mul (mem_centralizer_iff.1 (hO hz) p' hp'E).symm
    (mem_centralizer_iff.1 (hO hz) z' hz'E).symm (mem_centralizer_iff.1 (hO hz') p hpE).symm,
    commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hp hp') (inv_mem hp)) (inv_mem hp')

theorem isSimpleGroup_Pbar [Finite K] (N : CaseBNotation w D) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) : IsSimpleGroup N.Pbar := by
  have : Fintype K := Fintype.ofFinite K
  exact isSimpleGroup_of_mulEquiv_SL2 hf (by rw [Fintype.card_eq_nat_card, hKc])
    (MonoidHom.ofInjective N.σ_injective).symm

theorem isSimpleGroup_Qbar [Finite K] (N : CaseBNotation w D) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) : IsSimpleGroup N.Qbar := by
  have : Fintype K := Fintype.ofFinite K
  exact isSimpleGroup_of_mulEquiv_SL2 hf (by rw [Fintype.card_eq_nat_card, hKc])
    ((MulEquiv.subgroupMap (MulAut.conj w.tbar) N.Pbar).symm.trans
      (MonoidHom.ofInjective N.σ_injective).symm)

theorem center_Pbar [Finite K] (N : CaseBNotation w D) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) : center N.Pbar = ⊥ := by
  have := N.isSimpleGroup_Pbar hf hKc
  refine center_eq_bot_of_isSimpleGroup (a := ⟨N.σ (uSL 1), uSL 1, rfl⟩)
    (b := ⟨N.σ (vSL 1), vSL 1, rfl⟩) fun h => uSL_mul_vSL_ne (K := K) (N.σ_injective ?_)
  have := congrArg Subtype.val h
  simpa only [Subgroup.coe_mul, map_mul] using this

theorem center_Qbar [Finite K] (N : CaseBNotation w D) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) : center N.Qbar = ⊥ := by
  have := N.isSimpleGroup_Qbar hf hKc
  set e := MulEquiv.subgroupMap (MulAut.conj w.tbar) N.Pbar
  refine center_eq_bot_of_isSimpleGroup (a := e ⟨N.σ (uSL 1), uSL 1, rfl⟩)
    (b := e ⟨N.σ (vSL 1), vSL 1, rfl⟩) fun h => uSL_mul_vSL_ne (K := K) (N.σ_injective ?_)
  have h' : e (⟨N.σ (uSL 1), uSL 1, rfl⟩ * ⟨N.σ (vSL 1), vSL 1, rfl⟩) =
      e (⟨N.σ (vSL 1), vSL 1, rfl⟩ * ⟨N.σ (uSL 1), uSL 1, rfl⟩) := by
    rw [map_mul, map_mul]
    exact h
  have := congrArg Subtype.val (e.injective h')
  simpa only [Subgroup.coe_mul, map_mul] using this

theorem card_Qbar (N : CaseBNotation w D) : Nat.card N.Qbar = Nat.card N.Pbar :=
  card_map_of_injective (MulAut.conj w.tbar).injective

theorem map_conj_mul_self_Pbar [Finite G] [Finite K] [CharP K 2] (N : CaseBNotation w D)
    {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (g : w.Nbar) :
    N.Pbar.map (MulAut.conj (g * g)).toMonoidHom = N.Pbar ∧
      N.Qbar.map (MulAut.conj (g * g)).toMonoidHom = N.Qbar := by
  have hK : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := N.isSimpleGroup_Pbar hf hKc
  have := N.isSimpleGroup_Qbar hf hKc
  have hn : (w.Ebar D.lev.range).Normal := normalClosure_normal
  have hg : ∀ x ∈ N.Pbar ⊔ N.Qbar, g * x * g⁻¹ ∈ N.Pbar ⊔ N.Qbar := by
    rw [← N.Ebar_eq hK]
    exact fun x hx => hn.conj_mem x hx g
  have hg' : ∀ x ∈ N.Qbar ⊔ N.Pbar, g * x * g⁻¹ ∈ N.Qbar ⊔ N.Pbar := by
    rw [sup_comm]; exact hg
  refine ⟨map_conj_mul_self_eq (N.center_Pbar hf hKc) (N.center_Qbar hf hKc) N.card_Qbar.symm
    N.Pbar_Qbar_comm N.Pbar_inf_Qbar hg, map_conj_mul_self_eq (N.center_Qbar hf hKc)
    (N.center_Pbar hf hKc) N.card_Qbar (fun x hx y hy => (N.Pbar_Qbar_comm y hy x hx).symm)
    (by rw [inf_comm]; exact N.Pbar_inf_Qbar) hg'⟩

end Factors

section Preimages

open CaseBModule (preim mem_preim)

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}
  {K : Type} [Field K] {w : WData d Vi q} {D : LeviData A Vi K}

theorem comm_t_mul (w : WData d Vi q) {x y : G} (hx : x ∈ w.W) (hy : y ∈ w.W) :
    d.t * (x * y) * d.t * (x * y)⁻¹ = (d.t * x * d.t * x⁻¹) * (d.t * y * d.t * y⁻¹) := by
  have c1 : x⁻¹ * (d.t * y * d.t) = (d.t * y * d.t) * x⁻¹ :=
    comm_of_isElemAbelian w.elem (inv_mem hx) (conj_t_mem_W w hy)
  have c2 : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := comm_of_isElemAbelian w.elem (inv_mem hx) (inv_mem hy)
  have e : d.t * (x * y) * d.t = (d.t * x * d.t) * (d.t * y * d.t) := by
    rw [show (d.t * x * d.t) * (d.t * y * d.t) = d.t * x * (d.t * d.t) * y * d.t by group,
      d.t_mul_self, mul_one]
    group
  calc d.t * (x * y) * d.t * (x * y)⁻¹ = (d.t * x * d.t) * (d.t * y * d.t) * (x⁻¹ * y⁻¹) := by
        rw [e, mul_inv_rev, ← c2]
    _ = (d.t * x * d.t) * ((d.t * y * d.t) * x⁻¹) * y⁻¹ := by group
    _ = (d.t * x * d.t) * (x⁻¹ * (d.t * y * d.t)) * y⁻¹ := by rw [← c1]
    _ = (d.t * x * d.t * x⁻¹) * (d.t * y * d.t * y⁻¹) := by group

theorem W₁t_le_W (N : CaseBNotation w D) : N.W₁.map (MulAut.conj d.t).toMonoidHom ≤ w.W := by
  rw [← N.W₁_sup]
  exact le_sup_right

theorem W₁_le_commutator [CharP K 2] (N : CaseBNotation w D) {l : Kˣ} (hl : (l : K) ≠ 1) :
    N.W₁ ≤ ⁅N.M₁, N.M₁⁆ := by
  intro x hx
  have hxW := N.W₁_le hx
  have hxV : d.t * x * d.t * x⁻¹ ∈ D.ι.range := by rw [D.range_ι]; exact w.comm_mem x hxW
  obtain ⟨v, hv⟩ := hxV
  have hl1 : (l : K) + 1 ≠ 0 := by rw [← CharTwo.sub_eq_add]; exact sub_ne_zero.2 hl
  have hl2 : ((l⁻¹ : Kˣ) : K) + 1 ≠ 0 := by
    rw [← CharTwo.sub_eq_add]
    refine sub_ne_zero.2 fun h => hl ?_
    rwa [Units.val_inv_eq_inv_val, inv_eq_one] at h
  set v' : Multiplicative (Fin 2 → K) := Multiplicative.ofAdd
    ![Multiplicative.toAdd v 0 / ((l : K) + 1), Multiplicative.toAdd v 1 / (((l⁻¹ : Kˣ) : K) + 1)]
    with hv'
  have hv'V : D.ι v' ∈ Vi := by
    have h : D.ι v' ∈ D.ι.range := ⟨v', rfl⟩
    rwa [D.range_ι] at h
  obtain ⟨y, ⟨hy, hyv⟩, -⟩ := N.bij _ hv'V
  have hyW := N.W₁_le hy
  obtain ⟨hzW, hzt⟩ := N.nat (HSL l) y hy
  have hty : d.t * y⁻¹ * d.t * y⁻¹⁻¹ = D.ι v' := by
    have h := hyv
    rw [inv_eq_self_of_mem_W w hyW] at h
    rw [inv_inv, inv_eq_self_of_mem_W w hyW]
    exact h
  have hz_comm : d.t * (N.ℓ (HSL l) * y * (N.ℓ (HSL l))⁻¹ * y⁻¹) * d.t *
      (N.ℓ (HSL l) * y * (N.ℓ (HSL l))⁻¹ * y⁻¹)⁻¹ = d.t * x * d.t * x⁻¹ := by
    rw [comm_t_mul w (N.W₁_le hzW) (inv_mem hyW), hzt, hyv, hty, D.lev_conj, ← hv, ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, hv', toAdd_ofAdd]
    funext i
    have hl3 : 1 + (l : K) ≠ 0 := by rwa [add_comm]
    fin_cases i
    · simp [CFSG.LieType.Chevalley.coe_HSL]
      field_simp
    · simp [CFSG.LieType.Chevalley.coe_HSL]
      field_simp
  have hzx := (N.bij _ (w.comm_mem x hxW)).unique ⟨mul_mem hzW (inv_mem hy), hz_comm⟩ ⟨hx, rfl⟩
  rw [← hzx, ← commutatorElement_def]
  exact commutator_mem_commutator (N.ℓ_mem _) (N.W₁_le_M₁ hy)

theorem commutator_M₁ [Finite K] [CharP K 2] (N : CaseBNotation w D) (hK : 3 ≤ Nat.card K) :
    ⁅N.M₁, N.M₁⁆ = N.M₁ := by
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) hK
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · have hperf : commutator (SL2 K) = ⊤ :=
      Matrix.SL2.commutator_eq_top μ.ne_zero (sq_ne_one_of_charTwo hμ)
    have hL : ⁅N.ℓ.range, N.ℓ.range⁆ = N.ℓ.range := by
      rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hperf]
    calc N.M₁ = N.W₁ ⊔ N.ℓ.range := N.M₁_eq.symm
      _ ≤ ⁅N.M₁, N.M₁⁆ := sup_le (N.W₁_le_commutator fun h => hμ (Units.ext h))
          (hL ▸ commutator_mono N.ℓ_range_le_M₁ N.ℓ_range_le_M₁)

theorem M₁_le_preim (N : CaseBNotation w D) : N.M₁ ≤ preim w N.Pbar := by
  rw [← N.M₁_eq]
  refine sup_le (N.W₁_le.trans (CaseBModule.W_le_preim w _)) ?_
  rintro _ ⟨B, rfl⟩
  obtain ⟨h, hB⟩ := N.ℓ_bar B
  exact (mem_preim w _).2 ⟨h, hB ▸ ⟨B, rfl⟩⟩

theorem preim_le (N : CaseBNotation w D) :
    preim w N.Pbar ≤ N.M₁ ⊔ N.W₁.map (MulAut.conj d.t).toMonoidHom := by
  intro y hy
  obtain ⟨hyN, B, hB⟩ := (mem_preim w _).1 hy
  obtain ⟨h, hℓ⟩ := N.ℓ_bar B
  have h1 : (N.ℓ B)⁻¹ * y ∈ w.W := (w.projBar_eq_iff ⟨N.ℓ B, h⟩ ⟨y, hyN⟩).1 (hℓ.trans hB)
  rw [← N.W₁_sup] at h1
  have e : y = N.ℓ B * ((N.ℓ B)⁻¹ * y) := by group
  rw [e]
  exact mul_mem (mem_sup_left (N.ℓ_mem B)) (sup_le_sup_right N.W₁_le_M₁ _ h1)

theorem commutator_sup_le (N : CaseBNotation w D) :
    ⁅N.M₁ ⊔ N.W₁.map (MulAut.conj d.t).toMonoidHom,
      N.M₁ ⊔ N.W₁.map (MulAut.conj d.t).toMonoidHom⁆ ≤ N.M₁ := by
  have hc : ∀ x ∈ N.M₁, ∀ y ∈ N.W₁.map (MulAut.conj d.t).toMonoidHom, x * y = y * x :=
    fun x hx y hy => N.M₁_comm x hx y (map_mono N.W₁_le_M₁ hy)
  have hW : ∀ y ∈ N.W₁.map (MulAut.conj d.t).toMonoidHom,
      ∀ y' ∈ N.W₁.map (MulAut.conj d.t).toMonoidHom, y * y' = y' * y :=
    fun y hy y' hy' => comm_of_isElemAbelian w.elem (N.W₁t_le_W hy) (N.W₁t_le_W hy')
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hc ha
  obtain ⟨x', hx', y', hy', rfl⟩ := exists_mul_of_mem_sup hc hb
  rw [commutatorElement_mul_mul (hc x' hx' y hy).symm (hW y hy y' hy') (hc x hx y' hy').symm,
    commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hx') (inv_mem hx)) (inv_mem hx')

theorem M₁_eq_commutator [Finite K] [CharP K 2] (N : CaseBNotation w D) (hK : 3 ≤ Nat.card K) :
    N.M₁ = ⁅preim w N.Pbar, preim w N.Pbar⁆ :=
  le_antisymm ((N.commutator_M₁ hK).symm.le.trans (commutator_mono N.M₁_le_preim N.M₁_le_preim))
    ((commutator_mono N.preim_le N.preim_le).trans N.commutator_sup_le)

theorem conj_mem_M₁ [Finite K] [CharP K 2] (N : CaseBNotation w D) (hK : 3 ≤ Nat.card K)
    {g : G} (hg : ∀ y ∈ preim w N.Pbar, g * y * g⁻¹ ∈ preim w N.Pbar) {x : G} (hx : x ∈ N.M₁) :
    g * x * g⁻¹ ∈ N.M₁ := by
  have hle := CaseBModule.map_conj_le_of_forall hg
  rw [N.M₁_eq_commutator hK] at hx ⊢
  have h : g * x * g⁻¹ ∈ (⁅preim w N.Pbar, preim w N.Pbar⁆).map (MulAut.conj g).toMonoidHom :=
    ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  rw [map_commutator] at h
  exact commutator_mono hle hle h

theorem mem_preim_Qbar (N : CaseBNotation w D) {y : G} :
    y ∈ preim w N.Qbar ↔ d.t * y * d.t ∈ preim w N.Pbar := by
  have htN : d.t ∈ w.N := w.t_norm
  have key : ∀ (z : G) (hz : z ∈ w.N), w.projBar ⟨d.t * z * d.t, mul_mem (mul_mem htN hz) htN⟩ =
      w.tbar * w.projBar ⟨z, hz⟩ * w.tbar := fun z hz => by
    rw [← map_mul, ← map_mul]
    rfl
  rw [mem_preim, mem_preim]
  constructor
  · rintro ⟨hy, hyQ⟩
    exact ⟨mul_mem (mul_mem htN hy) htN, by rw [key y hy]; exact N.mem_Qbar.1 hyQ⟩
  · rintro ⟨hy, hyP⟩
    have hy' : y ∈ w.N := by
      have := mul_mem (mul_mem htN hy) htN
      rwa [show d.t * (d.t * y * d.t) * d.t = (d.t * d.t) * y * (d.t * d.t) by group,
        d.t_mul_self, one_mul, mul_one] at this
    refine ⟨hy', N.mem_Qbar.2 ?_⟩
    rw [← key y hy']
    exact hyP

theorem conj_mem_M₁t [Finite K] [CharP K 2] (N : CaseBNotation w D) (hK : 3 ≤ Nat.card K)
    {g : G} (hg : ∀ y ∈ preim w N.Qbar, g * y * g⁻¹ ∈ preim w N.Qbar) {x : G}
    (hx : x ∈ N.M₁.map (MulAut.conj d.t).toMonoidHom) :
    g * x * g⁻¹ ∈ N.M₁.map (MulAut.conj d.t).toMonoidHom := by
  have tt : ∀ z : G, d.t * (d.t * z) = z := fun z => by rw [← mul_assoc, d.t_mul_self, one_mul]
  have hg' : ∀ y ∈ preim w N.Pbar, (d.t * g * d.t) * y * (d.t * g * d.t)⁻¹ ∈ preim w N.Pbar := by
    intro y hy
    have h1 : d.t * y * d.t ∈ preim w N.Qbar := by
      rw [N.mem_preim_Qbar]
      simpa only [mul_assoc, tt, d.t_mul_self, mul_one] using hy
    have h2 := N.mem_preim_Qbar.1 (hg _ h1)
    have e : (d.t * g * d.t) * y * (d.t * g * d.t)⁻¹ = d.t * (g * (d.t * y * d.t) * g⁻¹) * d.t := by
      rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right d.t_mul_self]
      group
    rw [e]
    exact h2
  rw [mem_map_conj_iff d.t_mul_self] at hx ⊢
  have h := N.conj_mem_M₁ hK hg' hx
  have e : (d.t * g * d.t) * (d.t * x * d.t) * (d.t * g * d.t)⁻¹ = d.t * (g * x * g⁻¹) * d.t := by
    rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right d.t_mul_self]
    simp only [mul_assoc, tt]
  rwa [e] at h

theorem card_M₁ [Finite K] (N : CaseBNotation w D) (hKq : Nat.card K = q) :
    Nat.card N.M₁ = q ^ 3 * (q ^ 2 - 1) := by
  let ρ : N.M₁ →* w.Nbar := w.projBar.comp (Subgroup.inclusion N.M₁_le)
  have hker : ρ.ker = N.W₁.subgroupOf N.M₁ := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change w.projBar _ = 1 ↔ _
    rw [w.projBar_eq_one_iff]
    constructor
    · intro hx
      rw [← N.M₁_inf_W]
      exact ⟨x.2, hx⟩
    · intro hx
      exact N.W₁_le hx
  have hrange : ρ.range = N.σ.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨h, hx⟩ := (mem_preim w _).1 (N.M₁_le_preim x.2)
      exact hx
    · rintro ⟨B, rfl⟩
      obtain ⟨h, hB⟩ := N.ℓ_bar B
      exact ⟨⟨N.ℓ B, N.ℓ_mem B⟩, hB⟩
  have h1 := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe N.W₁_le_M₁).toEquiv, N.card_W₁,
    ← Nat.card_congr (MonoidHom.ofInjective N.σ_injective).toEquiv,
    CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hKq] at h1
  rw [← h1]
  ring

end Preimages

end CaseBNotation

namespace CaseBNotation

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : FrameData A d.V K} {q : ℕ}

omit [Finite K] [CharP K 2] in
theorem δ_conj {Vi : Subgroup G} {w : WData d Vi q} {D : LeviData A Vi K}
    (N : CaseBNotation w D) (g x : N.M₁) : N.δ (g * x * g⁻¹) = N.δ g * N.δ x * (N.δ g)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

omit [Finite K] [CharP K 2] in
theorem exists_δ_eq {i : Fin 2} {w : WData d (F.rad i) q}
    (N : CaseBNotation w (F.leviData i)) {v : G} (hv : v ∈ d.V) : ∃ x : N.M₁, N.δ x = v := by
  obtain ⟨x₀, hx₀, s, rfl⟩ := F.exists_mul_lev i hv
  obtain ⟨y, -, hy⟩ := N.exists_δ_W₁ hx₀
  exact ⟨y * ⟨N.ℓ (uSL s), N.ℓ_mem _⟩, by rw [map_mul, hy, N.δ_ℓ]⟩

omit [Finite K] [CharP K 2] in
theorem le_range_δ {i : Fin 2} {w : WData d (F.rad i) q}
    (N : CaseBNotation w (F.leviData i)) : d.V ≤ N.δ.range := fun _ hv => N.exists_δ_eq hv

variable {w₀ : WData d (F.rad 0) q} {w₁ : WData d (F.rad 1) q}

theorem R_comm (N : CaseBNotation w₀ (F.leviData 0)) {x y : G}
    (hx : x ∈ N.δpre (F.rad 1)) (hy : y ∈ N.δpre (F.rad 1)) :
    x * y = y * x := by
  obtain ⟨hx, hδx⟩ := N.mem_δpre.1 hx
  obtain ⟨hy, hδy⟩ := N.mem_δpre.1 hy
  have h : (⟨x, hx⟩ : N.M₁) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := N.δ_injective (by
    rw [map_mul, map_mul]
    exact comm_of_isElemAbelian F.radicals.elem₂ hδx hδy)
  exact congrArg Subtype.val h

theorem R_mul_self (N : CaseBNotation w₀ (F.leviData 0)) {x : G}
    (hx : x ∈ N.δpre (F.rad 1)) : x * x = 1 := by
  obtain ⟨hx, hδx⟩ := N.mem_δpre.1 hx
  have h : (⟨x, hx⟩ : N.M₁) * ⟨x, hx⟩ = 1 := N.δ_injective (by
    rw [map_mul, map_one, ← sq]
    exact F.radicals.elem₂.2 _ hδx)
  exact congrArg Subtype.val h

theorem exists_R (N : CaseBNotation w₀ (F.leviData 0)) {v : G}
    (hv : v ∈ F.rad 1) :
    ∃ r ∈ N.δpre (F.rad 1), r * (d.t * r * d.t) = v := by
  obtain ⟨r, hr⟩ := N.exists_δ_eq (F.radicals.le₂ hv)
  exact ⟨r, N.mem_δpre.2 ⟨r.2, by rw [hr]; exact hv⟩, hr⟩

theorem R_sup_le_centralizer (N : CaseBNotation w₀ (F.leviData 0)) :
    N.δpre (F.rad 1) ⊔
        (N.δpre (F.rad 1)).map (MulAut.conj d.t).toMonoidHom ≤
      centralizer ((F.rad 1 : Subgroup G) : Set G) := by
  set R := N.δpre (F.rad 1) with hR
  have hRM : R ≤ N.M₁ := N.δpre_le _
  refine sup_le (fun x hx => mem_centralizer_iff.2 fun v hv => ?_)
    fun x hx => mem_centralizer_iff.2 fun v hv => ?_
  · obtain ⟨r, hr, rfl⟩ := N.exists_R hv
    have h1 := N.R_comm hx hr
    have h2 := N.M₁_comm x (hRM hx) _ (conj_mem_map_conj d.t_mul_self (hRM hr))
    calc r * (d.t * r * d.t) * x = r * x * (d.t * r * d.t) := by rw [mul_assoc, ← h2, ← mul_assoc]
      _ = x * (r * (d.t * r * d.t)) := by rw [← h1, mul_assoc]
  · obtain ⟨r, hr, rfl⟩ := N.exists_R hv
    have tt : ∀ y : G, d.t * (d.t * y) = y := fun y => by rw [← mul_assoc, d.t_mul_self, one_mul]
    have h1 := N.R_comm ((mem_map_conj_iff d.t_mul_self).1 hx) hr
    have hrx : r * x = x * r := N.M₁_comm r (hRM hr) x (map_mono hRM hx)
    have hxr : x * (d.t * r * d.t) = (d.t * r * d.t) * x := by
      have h2 := congrArg (fun z => d.t * (z * d.t)) h1
      simp only [mul_assoc, tt, d.t_mul_self, mul_one] at h2
      simpa only [mul_assoc] using h2
    calc r * (d.t * r * d.t) * x = r * (x * (d.t * r * d.t)) := by rw [mul_assoc, ← hxr]
      _ = x * (r * (d.t * r * d.t)) := by rw [← mul_assoc, hrx, mul_assoc]

variable [Finite G]

theorem R_sup_le_normalizer (N : CaseBNotation w₀ (F.leviData 0)) :
    N.δpre (F.rad 1) ⊔
        (N.δpre (F.rad 1)).map (MulAut.conj d.t).toMonoidHom ≤
      normalizer ((F.rad 1 ⊔ zpowers d.t : Subgroup G) : Set G) := by
  set R := N.δpre (F.rad 1) with hR
  set E := F.rad 1 ⊔ zpowers d.t with hE
  have htE : d.t ∈ normalizer (E : Set G) := le_normalizer (mem_sup_right (mem_zpowers d.t))
  have hRE : R ≤ normalizer (E : Set G) := by
    intro r hr
    refine CaseBModule.mem_normalizer_of_map_le ?_
    rw [hE, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le (fun _ ⟨v, hv, hvr⟩ => ?_) (zpowers_le.2 ?_)
    · rw [← hvr, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        ← (mem_centralizer_iff.1 (N.R_sup_le_centralizer (mem_sup_left hr)) v hv),
        mul_inv_cancel_right]
      exact mem_sup_left hv
    · obtain ⟨hrM, hδr⟩ := N.mem_δpre.1 hr
      have hrr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (N.R_mul_self hr)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hrr,
        show r * d.t * r = r * (d.t * r * d.t) * d.t by
          simp only [mul_assoc, d.t_mul_self, mul_one]]
      exact mul_mem (mem_sup_left hδr) (mem_sup_right (mem_zpowers d.t))
  refine sup_le hRE fun x hx => ?_
  have hx' : x = d.t * (d.t * x * d.t) * d.t := by
    rw [show d.t * (d.t * x * d.t) * d.t = (d.t * d.t) * x * (d.t * d.t) by group, d.t_mul_self,
      one_mul, mul_one]
  rw [hx']
  exact mul_mem (mul_mem htE (hRE ((mem_map_conj_iff d.t_mul_self).1 hx))) htE

omit [Finite G] in
theorem card_R (N : CaseBNotation w₀ (F.leviData 0)) :
    Nat.card (N.δpre (F.rad 1)) = Nat.card K ^ 2 := by
  rw [N.card_δpre ((F.radicals.le₂).trans N.le_range_δ), F.radicals.card₂]

theorem W_eq (N : CaseBNotation w₀ (F.leviData 0)) (hKq : Nat.card K = q) :
    w₁.W = N.δpre (F.rad 1) ⊔
      (N.δpre (F.rad 1)).map (MulAut.conj d.t).toMonoidHom := by
  set R := N.δpre (F.rad 1) with hR
  have hRM : R ≤ N.M₁ := N.δpre_le _
  have hRtM : R.map (MulAut.conj d.t).toMonoidHom ≤ N.M₁.map (MulAut.conj d.t).toMonoidHom :=
    map_mono hRM
  have hc : ∀ x ∈ R, ∀ y ∈ R.map (MulAut.conj d.t).toMonoidHom, x * y = y * x :=
    fun x hx y hy => N.M₁_comm x (hRM hx) y (hRtM hy)
  have h1 : R ≤ centralizer (R : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => N.R_comm hy hx
  have h2 : R.map (MulAut.conj d.t).toMonoidHom ≤
      centralizer ((R.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) := by
    intro x hx
    refine mem_centralizer_iff.2 fun y hy => ?_
    have := N.R_comm ((mem_map_conj_iff d.t_mul_self).1 hy) ((mem_map_conj_iff d.t_mul_self).1 hx)
    have tt : ∀ z : G, d.t * (d.t * z) = z := fun z => by
      rw [← mul_assoc, d.t_mul_self, one_mul]
    have h3 := congrArg (fun z => d.t * (z * d.t)) this
    simp only [mul_assoc, tt, d.t_mul_self, mul_one] at h3
    simpa only [mul_assoc] using h3
  have h3 : R ≤ centralizer ((R.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) :=
    fun x hx => mem_centralizer_iff.2 fun y hy => (hc x hx y hy).symm
  have h4 : R.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (R : Set G) :=
    fun y hy => mem_centralizer_iff.2 fun x hx => hc x hx y hy
  have hinf : R ⊓ R.map (MulAut.conj d.t).toMonoidHom = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hRM hRtM).trans N.M₁_inf.le)
  refine (w₁.unique _ ?_ ?_ ?_).symm
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hX2 : IsPGroup 2 (F.rad 1) := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]; exact F.radicals.elem₂.2 x x.2)⟩
    have hR2 : IsPGroup 2 R := (hX2.comap_of_injective N.δ N.δ_injective).map N.M₁.subtype
    refine w₁.le_sup_of_isPGroup _ (IsPGroup.to_sup_of_normal_left' hR2 (hR2.map _)
      fun y hy => Subgroup.mem_normalizer_fintype fun x hx => ?_)
      (le_inf N.R_sup_le_normalizer N.R_sup_le_centralizer)
    rw [← hc x hx y hy, mul_inv_cancel_right]
    exact hx
  · have hle : R ⊔ R.map (MulAut.conj d.t).toMonoidHom ≤
        centralizer ((R ⊔ R.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) := by
      refine sup_le ?_ ?_
      · rw [le_centralizer_iff]
        exact sup_le h1 h4
      · rw [le_centralizer_iff]
        exact sup_le h3 h2
    exact fun a ha b hb => (mem_centralizer_iff.1 (hle hb) a ha)
  · rw [card_sup_of_commute hc hinf, Subgroup.card_map_of_injective (MulAut.conj d.t).injective,
      card_R, hKq]
    ring

theorem ℓ_HSL_mem_N (N : CaseBNotation w₀ (F.leviData 0)) (hKq : Nat.card K = q) (m : Kˣ) :
    N.ℓ (HSL m) ∈ w₁.N := by
  set R := N.δpre (F.rad 1) with hR
  set g := N.ℓ (HSL m) with hg
  have hRM : R ≤ N.M₁ := N.δpre_le _
  refine CaseBModule.mem_normalizer_of_map_le ?_
  rw [N.W_eq hKq, Subgroup.map_sup]
  refine sup_le_sup (fun _ ⟨r, hr, hrg⟩ => ?_) fun _ ⟨x, hx, hxg⟩ => ?_
  · obtain ⟨hrM, hδr⟩ := N.mem_δpre.1 hr
    rw [← hrg, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h := N.δ_conj ⟨g, N.ℓ_mem _⟩ ⟨r, hrM⟩
    rw [N.δ_ℓ] at h
    refine N.mem_δpre.2 ⟨(⟨g, N.ℓ_mem _⟩ * ⟨r, hrM⟩ * (⟨g, N.ℓ_mem _⟩ : N.M₁)⁻¹ : N.M₁).2, ?_⟩
    have e : (⟨g * r * g⁻¹, (⟨g, N.ℓ_mem _⟩ * ⟨r, hrM⟩ * (⟨g, N.ℓ_mem _⟩ : N.M₁)⁻¹ : N.M₁).2⟩ :
        N.M₁) = ⟨g, N.ℓ_mem _⟩ * ⟨r, hrM⟩ * (⟨g, N.ℓ_mem _⟩ : N.M₁)⁻¹ := rfl
    rw [e, h]
    exact F.lev_zero_HSL_conj_mem_V₁ m hδr
  · rw [← hxg, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      N.M₁_comm g (N.ℓ_mem _) x (map_mono hRM hx), mul_inv_cancel_right]
    exact hx

omit [Finite G] [Finite K] in
theorem eq_one_of_ℓ_HSL_conj (N : CaseBNotation w₀ (F.leviData 0)) {m : Kˣ} (hm : (m : K) ≠ 1)
    {b : G} (hb : b ∈ N.δpre d.V) (hfix : N.ℓ (HSL m) * b * (N.ℓ (HSL m))⁻¹ = b) : b = 1 := by
  obtain ⟨hbM, hδb⟩ := N.mem_δpre.1 hb
  have h := N.δ_conj ⟨N.ℓ (HSL m), N.ℓ_mem _⟩ ⟨b, hbM⟩
  rw [N.δ_ℓ] at h
  have e : (⟨N.ℓ (HSL m), N.ℓ_mem _⟩ * ⟨b, hbM⟩ * (⟨N.ℓ (HSL m), N.ℓ_mem _⟩ : N.M₁)⁻¹ : N.M₁) =
      ⟨b, hbM⟩ := Subtype.ext hfix
  rw [e] at h
  have h1 := F.eq_one_of_lev_zero_HSL_conj hm hδb h.symm
  have h2 : (⟨b, hbM⟩ : N.M₁) = 1 := N.δ_injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

open CaseBModule (preim mem_preim) in
theorem ℓ_sq_conj_mem (N₀ : CaseBNotation w₀ (F.leviData 0))
    (N₁ : CaseBNotation w₁ (F.leviData 1)) (hKq : Nat.card K = q) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) (μ : Kˣ) :
    (∀ x ∈ N₁.M₁, N₀.ℓ (HSL μ * HSL μ) * x * (N₀.ℓ (HSL μ * HSL μ))⁻¹ ∈ N₁.M₁) ∧
      ∀ x ∈ N₁.M₁.map (MulAut.conj d.t).toMonoidHom,
        N₀.ℓ (HSL μ * HSL μ) * x * (N₀.ℓ (HSL μ * HSL μ))⁻¹ ∈
          N₁.M₁.map (MulAut.conj d.t).toMonoidHom := by
  have hK : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set g₀ : w₁.N := ⟨N₀.ℓ (HSL μ), N₀.ℓ_HSL_mem_N hKq μ⟩ with hg₀
  have hh : N₀.ℓ (HSL μ * HSL μ) = ((g₀ * g₀ : w₁.N) : G) := by rw [map_mul]; rfl
  obtain ⟨hP, hQ⟩ := N₁.map_conj_mul_self_Pbar hf hKc (w₁.projBar g₀)
  have key : ∀ X : Subgroup w₁.Nbar,
      X.map (MulAut.conj (w₁.projBar g₀ * w₁.projBar g₀)).toMonoidHom = X →
      ∀ y ∈ preim w₁ X, N₀.ℓ (HSL μ * HSL μ) * y * (N₀.ℓ (HSL μ * HSL μ))⁻¹ ∈ preim w₁ X := by
    intro X hX y hy
    obtain ⟨hyN, hyX⟩ := (mem_preim w₁ X).1 hy
    rw [hh]
    refine (mem_preim w₁ X).2 ⟨mul_mem (mul_mem (g₀ * g₀).2 hyN) (inv_mem (g₀ * g₀).2), ?_⟩
    rw [← hX]
    refine ⟨w₁.projBar ⟨y, hyN⟩, hyX, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
    rfl
  exact ⟨fun x hx => N₁.conj_mem_M₁ hK (key _ hP) hx,
    fun x hx => N₁.conj_mem_M₁t hK (key _ hQ) hx⟩

omit [Finite G] [Finite K] [CharP K 2] in
theorem V_le_sup (N₁ : CaseBNotation w₁ (F.leviData 1)) :
    d.V ≤ N₁.M₁ ⊔ N₁.M₁.map (MulAut.conj d.t).toMonoidHom := by
  intro v hv
  obtain ⟨x, hx, s, rfl⟩ := F.exists_mul_lev 1 hv
  refine mul_mem ?_ ?_
  · have hxW : x ∈ w₁.W := w₁.lt.le hx
    rw [← N₁.W₁_sup] at hxW
    exact sup_le_sup N₁.W₁_le_M₁ (map_mono N₁.W₁_le_M₁) hxW
  · rw [← N₁.diag]
    exact mul_mem (mem_sup_left (N₁.ℓ_mem _))
      (mem_sup_right (conj_mem_map_conj d.t_mul_self (N₁.ℓ_mem _)))

open CFSG.OddStandard.Seitz77 (uelt exists_uelt uelt_inv uelt_mul uelt_inj mem_radTwo coordA_uelt)
  in
theorem A_le_sup (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1))
    (hKq : Nat.card K = q) {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) :
    N₀.δpre d.V ≤ N₁.M₁ ⊔ N₁.M₁.map (MulAut.conj d.t).toMonoidHom := by
  set M := N₁.M₁ ⊔ N₁.M₁.map (MulAut.conj d.t).toMonoidHom with hM
  have hK : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) hK
  have hl : ((μ * μ : Kˣ) : K) ≠ 1 := by
    rw [Units.val_mul, ← sq]
    exact sq_ne_one_of_charTwo hμ
  have hlinv : (((μ * μ)⁻¹ : Kˣ) : K) - 1 ≠ 0 := by
    refine sub_ne_zero.2 fun h => hl ?_
    rwa [Units.val_inv_eq_inv_val, inv_eq_one] at h
  set h := N₀.ℓ (HSL μ * HSL μ) with hh
  have hhM : h ∈ N₀.M₁ := N₀.ℓ_mem _
  have hδh : N₀.δ ⟨h, hhM⟩ = (F.leviData 0).lev (HSL (μ * μ)) := by
    rw [N₀.δ_ℓ, HSL_mul_HSL]
  obtain ⟨hM1, hM2⟩ := N₀.ℓ_sq_conj_mem N₁ hKq hf hKc μ
  have hMh : ∀ x ∈ M, h * x * h⁻¹ ∈ M := by
    intro x hx
    have hle : M.map (MulAut.conj h).toMonoidHom ≤ M := by
      rw [hM, Subgroup.map_sup]
      exact sup_le_sup (CaseBModule.map_conj_le_of_forall hM1)
        (CaseBModule.map_conj_le_of_forall hM2)
    exact hle ⟨x, hx, rfl⟩
  have hWM : w₁.W ≤ M := by
    rw [← N₁.W₁_sup]
    exact sup_le_sup N₁.W₁_le_M₁ (map_mono N₁.W₁_le_M₁)
  have hRW : N₀.δpre (F.rad 1) ≤ w₁.W := by
    rw [N₀.W_eq hKq]
    exact le_sup_left
  have hRM := hRW.trans hWM
  have hkey : ∀ y ∈ N₀.δpre d.V, y⁻¹ * (h * y * h⁻¹) ∈ M := by
    intro y hy
    obtain ⟨hyM, hδy⟩ := N₀.mem_δpre.1 hy
    have hδyM : y * (d.t * y * d.t) ∈ M := V_le_sup N₁ hδy
    have hyt : d.t * y * d.t ∈ N₀.M₁.map (MulAut.conj d.t).toMonoidHom :=
      conj_mem_map_conj d.t_mul_self hyM
    have c1 : h * (d.t * y * d.t) * h⁻¹ = d.t * y * d.t := by
      rw [N₀.M₁_comm h hhM _ hyt, mul_inv_cancel_right]
    have hzM : y⁻¹ * (h * y * h⁻¹) ∈ N₀.M₁ :=
      mul_mem (inv_mem hyM) (mul_mem (mul_mem hhM hyM) (inv_mem hhM))
    have c2 := N₀.M₁_comm _ hzM _ hyt
    have e : y⁻¹ * (h * y * h⁻¹) =
        (y * (d.t * y * d.t))⁻¹ * (h * (y * (d.t * y * d.t)) * h⁻¹) := by
      calc y⁻¹ * (h * y * h⁻¹) = (d.t * y * d.t)⁻¹ * ((y⁻¹ * (h * y * h⁻¹)) * (d.t * y * d.t)) := by
            rw [c2]; group
        _ = (d.t * y * d.t)⁻¹ * (y⁻¹ * (h * y * h⁻¹) * (h * (d.t * y * d.t) * h⁻¹)) := by
            rw [c1]
        _ = _ := by group
    rw [e]
    exact mul_mem (inv_mem hδyM) (hMh _ hδyM)
  intro x hx
  obtain ⟨hxM, hδx⟩ := N₀.mem_δpre.1 hx
  obtain ⟨u, hu⟩ := F.mem_V_iff.1 hδx
  obtain ⟨a, b, c, rfl⟩ := exists_uelt u
  obtain ⟨y, hy⟩ := N₀.exists_δ_eq (F.ψ_mem_V (uelt (a * ((((μ * μ)⁻¹ : Kˣ) : K) - 1)⁻¹) 0 0))
  have hyA : (y : G) ∈ N₀.δpre d.V := N₀.mem_δpre.2 ⟨y.2, by rw [hy]; exact F.ψ_mem_V _⟩
  set z : N₀.M₁ := y⁻¹ * (⟨h, hhM⟩ * y * (⟨h, hhM⟩ : N₀.M₁)⁻¹) with hz
  have hzM : (z : G) ∈ M := hkey _ hyA
  have hδz : N₀.δ z = F.ψ (uelt a 0 0) := by
    rw [hz, map_mul, map_inv, N₀.δ_conj, hδh, hy, F.lev_zero_HSL_conj, ← map_inv, ← map_mul,
      uelt_inv, uelt_mul]
    congr 1
    rw [uelt_inj]
    refine ⟨?_, by ring, by ring⟩
    field_simp
    ring
  have hr : ((z⁻¹ * ⟨x, hxM⟩ : N₀.M₁) : G) ∈ N₀.δpre (F.rad 1) := by
    refine N₀.mem_δpre.2 ⟨(z⁻¹ * ⟨x, hxM⟩ : N₀.M₁).2, ?_⟩
    have e : (⟨((z⁻¹ * ⟨x, hxM⟩ : N₀.M₁) : G), (z⁻¹ * ⟨x, hxM⟩ : N₀.M₁).2⟩ : N₀.M₁) =
        z⁻¹ * ⟨x, hxM⟩ := rfl
    rw [e, map_mul, map_inv, hδz, ← hu, ← map_inv, ← map_mul, uelt_inv, uelt_mul,
      ← F.map_radTwo_ψ]
    exact ⟨_, (mem_radTwo _).2 (by rw [coordA_uelt]; ring), rfl⟩
  have e : x = (z : G) * ((z⁻¹ * ⟨x, hxM⟩ : N₀.M₁) : G) :=
    (congrArg Subtype.val (mul_inv_cancel_left z ⟨x, hxM⟩)).symm
  rw [e]
  exact mul_mem hzM (hRM hr)

theorem A_le_sup_inf (N₀ : CaseBNotation w₀ (F.leviData 0))
    (N₁ : CaseBNotation w₁ (F.leviData 1)) (hKq : Nat.card K = q) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) :
    N₀.δpre d.V ≤ (N₀.δpre d.V ⊓ N₁.M₁) ⊔
      (N₀.δpre d.V ⊓ N₁.M₁.map (MulAut.conj d.t).toMonoidHom) := by
  set A₀ := N₀.δpre d.V with hA₀
  set M₁ := N₁.M₁ with hM₁
  set M₂ := N₁.M₁.map (MulAut.conj d.t).toMonoidHom with hM₂
  set S₀ := A₀ ⊔ A₀.map (MulAut.conj d.t).toMonoidHom with hS₀
  have hK : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq : q = 2 ^ f := hKq.symm.trans hKc
  have hcM : ∀ x ∈ M₁, ∀ y ∈ M₂, x * y = y * x := N₁.M₁_comm
  have hcM' : ∀ x ∈ M₂, ∀ y ∈ M₁, x * y = y * x := fun x hx y hy => (hcM y hy x hx).symm
  have hinfM : M₁ ⊓ M₂ = ⊥ := N₁.M₁_inf
  have hinfM' : M₂ ⊓ M₁ = ⊥ := by rw [inf_comm]; exact hinfM
  have hA₀M : A₀ ≤ M₁ ⊔ M₂ := N₀.A_le_sup N₁ hKq hf hKc
  have hMt : (M₁ ⊔ M₂).map (MulAut.conj d.t).toMonoidHom = M₁ ⊔ M₂ := by
    rw [Subgroup.map_sup, hM₂, map_conj_map_conj d.t_mul_self, sup_comm]
  have hS₀M : S₀ ≤ M₁ ⊔ M₂ := sup_le hA₀M (hMt ▸ map_mono hA₀M)
  have hnorm : ∀ {X Y : Subgroup G}, (∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) →
      X ⊔ Y ≤ normalizer (Y : Set G) := fun hc => sup_le (fun x hx =>
        centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => (hc x hx y hy).symm))
      le_normalizer
  have hA₀M₀ : A₀ ≤ N₀.M₁ := N₀.δpre_le _
  have hcA : ∀ x ∈ A₀, ∀ y ∈ A₀.map (MulAut.conj d.t).toMonoidHom, x * y = y * x :=
    fun x hx y hy => N₀.M₁_comm x (hA₀M₀ hx) y (map_mono hA₀M₀ hy)
  have hinfA : A₀ ⊓ A₀.map (MulAut.conj d.t).toMonoidHom = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hA₀M₀ (map_mono hA₀M₀)).trans N₀.M₁_inf.le)
  have hcardA : Nat.card A₀ = q ^ 3 := by
    rw [hA₀, N₀.card_δpre N₀.le_range_δ, F.radicals.card, hKq]
  have hcardS : Nat.card S₀ = q ^ 6 := by
    rw [hS₀, card_sup_of_commute hcA hinfA, card_map_of_injective (MulAut.conj d.t).injective,
      hcardA]
    ring
  have hSpow : ∀ s ∈ S₀, s ^ (q ^ 6) = 1 := fun s hs => by
    have h := pow_card_eq_one' (G := S₀) (x := ⟨s, hs⟩)
    rw [hcardS] at h
    exact congrArg Subtype.val h
  have hXcard : ∀ {X Y : Subgroup G}, (∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) → X ⊓ Y = ⊥ →
      S₀ ≤ X ⊔ Y → Nat.card X = q ^ 3 * (q ^ 2 - 1) → Nat.card ↥(X ⊓ (S₀ ⊔ Y)) ≤ q ^ 3 := by
    intro X Y hc hinf hSXY hcardX
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hSY : S₀ ≤ normalizer (Y : Set G) := hSXY.trans (hnorm hc)
    have h2 : IsPGroup 2 ↥(X ⊓ (S₀ ⊔ Y)) := by
      rw [IsPGroup.iff_orderOf]
      intro x
      have hx1 : (x : G) ^ (q ^ 6) = 1 := pow_eq_one_of_mem_inf_sup hc hinf hSY hSpow x.2
      have hdvd : orderOf x ∣ 2 ^ (f * 6) := by
        rw [pow_mul, ← hq]
        exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow]; exact hx1))
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h2
    have hdvd : Nat.card ↥(X ⊓ (S₀ ⊔ Y)) ∣ Nat.card X := card_dvd_of_le inf_le_left
    rw [hk, hcardX] at hdvd
    have hodd : Nat.Coprime (2 ^ k) (q ^ 2 - 1) := by
      refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_)
      have h4 : 2 ∣ q ^ 2 := by
        rw [hq, ← pow_mul]
        exact dvd_pow_self 2 (by omega)
      have h5 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by rw [hq]; positivity)
      omega
    rw [hk]
    exact Nat.le_of_dvd (by rw [hq]; positivity) (hodd.dvd_of_dvd_mul_right hdvd)
  set X₁ := M₁ ⊓ (S₀ ⊔ M₂) with hX₁
  set X₂ := M₂ ⊓ (S₀ ⊔ M₁) with hX₂
  have hmemX₁ : ∀ {x y : G}, x ∈ M₁ → y ∈ M₂ → x * y ∈ S₀ → x ∈ X₁ := by
    intro x y hx hy hs
    refine mem_inf.2 ⟨hx, ?_⟩
    have e : x = (x * y) * y⁻¹ := (mul_inv_cancel_right x y).symm
    rw [e]
    exact mul_mem (mem_sup_left hs) (mem_sup_right (inv_mem hy))
  have hS₀X : S₀ ≤ X₁ ⊔ X₂ := by
    intro s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hcM (hS₀M hs)
    have hyX : y ∈ X₂ := mem_inf.2 ⟨hy, by
      rw [show y = x⁻¹ * (x * y) by group]
      exact mul_mem (mem_sup_right (inv_mem hx)) (mem_sup_left hs)⟩
    exact mul_mem (mem_sup_left (hmemX₁ hx hy hs)) (mem_sup_right hyX)
  have hcX : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x := fun x hx y hy =>
    hcM x (mem_inf.1 hx).1 y (mem_inf.1 hy).1
  have hinfX : X₁ ⊓ X₂ = ⊥ := eq_bot_iff.2 ((inf_le_inf inf_le_left inf_le_left).trans hinfM.le)
  have hcardM₁ : Nat.card M₁ = q ^ 3 * (q ^ 2 - 1) := N₁.card_M₁ hKq
  have hcardM₂ : Nat.card M₂ = q ^ 3 * (q ^ 2 - 1) := by
    rw [hM₂, card_map_of_injective (MulAut.conj d.t).injective]
    exact hcardM₁
  have hS₀eq : S₀ = X₁ ⊔ X₂ := eq_of_le_of_card_ge hS₀X (by
    rw [card_sup_of_commute hcX hinfX, hcardS]
    calc Nat.card X₁ * Nat.card X₂ ≤ q ^ 3 * q ^ 3 := Nat.mul_le_mul
          (hXcard hcM hinfM hS₀M hcardM₁) (hXcard hcM' hinfM' (sup_comm M₁ M₂ ▸ hS₀M) hcardM₂)
      _ = q ^ 6 := by ring)
  have hX₁S : X₁ ≤ S₀ := hS₀eq ▸ le_sup_left
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) hK
  have hl : ((μ * μ : Kˣ) : K) ≠ 1 := by
    rw [Units.val_mul, ← sq]
    exact sq_ne_one_of_charTwo hμ
  obtain ⟨hM1, hM2⟩ := N₀.ℓ_sq_conj_mem N₁ hKq hf hKc μ
  set h := N₀.ℓ (HSL μ * HSL μ) with hh
  have hhM : h ∈ N₀.M₁ := N₀.ℓ_mem _
  have tt : ∀ z : G, d.t * (d.t * z) = z := fun z => by rw [← mul_assoc, d.t_mul_self, one_mul]
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right d.t_mul_self
  have hht : ∀ z : G, (d.t * h * d.t) * z * (d.t * h * d.t)⁻¹ =
      d.t * (h * (d.t * z * d.t) * h⁻¹) * d.t :=
    fun z => by
      rw [mul_inv_rev, mul_inv_rev, htinv]
      simp only [mul_assoc]
  have hhtM₁ : ∀ z ∈ M₁, (d.t * h * d.t) * z * (d.t * h * d.t)⁻¹ ∈ M₁ := fun z hz => by
    rw [hht]
    exact (mem_map_conj_iff d.t_mul_self).1 (hM2 _ (conj_mem_map_conj d.t_mul_self hz))
  have hhtM₂ : ∀ z ∈ M₂, (d.t * h * d.t) * z * (d.t * h * d.t)⁻¹ ∈ M₂ := fun z hz => by
    rw [hht]
    exact conj_mem_map_conj d.t_mul_self (hM1 _ ((mem_map_conj_iff d.t_mul_self).1 hz))
  have hhtA : ∀ a ∈ A₀, (d.t * h * d.t) * a * (d.t * h * d.t)⁻¹ = a := fun a ha => by
    rw [← N₀.M₁_comm a (hA₀M₀ ha) _ (conj_mem_map_conj d.t_mul_self hhM), mul_inv_cancel_right]
  have hfix : ∀ b ∈ A₀.map (MulAut.conj d.t).toMonoidHom,
      (d.t * h * d.t) * b * (d.t * h * d.t)⁻¹ = b → b = 1 := by
    intro b hb hbfix
    have hb' : d.t * b * d.t ∈ A₀ := (mem_map_conj_iff d.t_mul_self).1 hb
    have h1 : N₀.ℓ (HSL (μ * μ)) * (d.t * b * d.t) * (N₀.ℓ (HSL (μ * μ)))⁻¹ = d.t * b * d.t := by
      rw [← HSL_mul_HSL, ← hh]
      have := congrArg (fun z => d.t * z * d.t) hbfix
      rw [hht] at this
      simpa only [mul_assoc, tt, d.t_mul_self, mul_one] using this
    have h2 := N₀.eq_one_of_ℓ_HSL_conj hl hb' h1
    calc b = d.t * (d.t * b * d.t) * d.t := by simp only [mul_assoc, tt, d.t_mul_self, mul_one]
      _ = 1 := by rw [h2, mul_one, d.t_mul_self]
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hcM (hA₀M ha)
  have hxS : x ∈ S₀ := hX₁S (hmemX₁ hx hy (mem_sup_left ha))
  have hxfix : (d.t * h * d.t) * x * (d.t * h * d.t)⁻¹ = x := by
    have e := hhtA _ ha
    rw [show (d.t * h * d.t) * (x * y) * (d.t * h * d.t)⁻¹ =
        ((d.t * h * d.t) * x * (d.t * h * d.t)⁻¹) * ((d.t * h * d.t) * y * (d.t * h * d.t)⁻¹) by
      group] at e
    exact (eq_and_eq_of_mul_eq hinfM (hhtM₁ x hx) hx (hhtM₂ y hy) hy e).1
  obtain ⟨a', ha', b, hb, rfl⟩ := exists_mul_of_mem_sup hcA hxS
  have hb1 : b = 1 := by
    refine hfix b hb ?_
    rw [show (d.t * h * d.t) * (a' * b) * (d.t * h * d.t)⁻¹ =
        ((d.t * h * d.t) * a' * (d.t * h * d.t)⁻¹) * ((d.t * h * d.t) * b * (d.t * h * d.t)⁻¹) by
      group, hhtA a' ha'] at hxfix
    exact mul_left_cancel hxfix
  subst hb1
  rw [mul_one] at hx ha ⊢
  have hyA : y ∈ A₀ := by
    rw [show y = a'⁻¹ * (a' * y) by group]
    exact mul_mem (inv_mem ha') ha
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨ha', hx⟩)) (mem_sup_right (mem_inf.2 ⟨hyA, hy⟩))

theorem A_le_or (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1))
    (hKq : Nat.card K = q) {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) :
    N₀.δpre d.V ≤ N₁.M₁ ∨ N₀.δpre d.V ≤ N₁.M₁.map (MulAut.conj d.t).toMonoidHom := by
  set A₀ := N₀.δpre d.V with hA₀
  set P := A₀ ⊓ N₁.M₁ with hP
  set Q := A₀ ⊓ N₁.M₁.map (MulAut.conj d.t).toMonoidHom with hQ
  have hdec : A₀ ≤ P ⊔ Q := N₀.A_le_sup_inf N₁ hKq hf hKc
  have hcPQ : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    N₁.M₁_comm x (mem_inf.1 hx).2 y (mem_inf.1 hy).2
  have hA₀M₀ : A₀ ≤ N₀.M₁ := N₀.δpre_le _
  set P' := (P.subgroupOf N₀.M₁).map N₀.δ with hP'
  set Q' := (Q.subgroupOf N₀.M₁).map N₀.δ with hQ'
  have hc' : ∀ u ∈ P', ∀ v ∈ Q', u * v = v * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg N₀.δ (Subtype.ext (hcPQ _ (mem_subgroupOf.1 hx) _ (mem_subgroupOf.1 hy)))
  have hinf' : P' ⊓ Q' = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have hyx := N₀.δ_injective hxy
    subst hyx
    have h1 : (y : G) ∈ N₁.M₁ ⊓ N₁.M₁.map (MulAut.conj d.t).toMonoidHom :=
      mem_inf.2 ⟨(mem_inf.1 (mem_subgroupOf.1 hx)).2, (mem_inf.1 (mem_subgroupOf.1 hy)).2⟩
    rw [N₁.M₁_inf, mem_bot] at h1
    rw [show y = 1 from Subtype.ext h1, map_one]
    exact one_mem _
  have hsup' : P' ⊔ Q' = d.V := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact (N₀.mem_δpre.1 (mem_inf.1 (mem_subgroupOf.1 hx)).1).2
      · rintro _ ⟨x, hx, rfl⟩
        exact (N₀.mem_δpre.1 (mem_inf.1 (mem_subgroupOf.1 hx)).1).2
    · intro v hv
      obtain ⟨a, ha⟩ := N₀.exists_δ_eq hv
      have haA : (a : G) ∈ A₀ := N₀.mem_δpre.2 ⟨a.2, by rw [ha]; exact hv⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup hcPQ (hdec haA)
      have hxM := hA₀M₀ (mem_inf.1 hx).1
      have hyM := hA₀M₀ (mem_inf.1 hy).1
      have e : a = ⟨x, hxM⟩ * ⟨y, hyM⟩ := Subtype.ext hxy
      rw [← ha, e, map_mul]
      exact mul_mem (mem_sup_left ⟨⟨x, hxM⟩, mem_subgroupOf.2 hx, rfl⟩)
        (mem_sup_right ⟨⟨y, hyM⟩, mem_subgroupOf.2 hy, rfl⟩)
  have hbot : ∀ {X : Subgroup G}, X ≤ A₀ → (X.subgroupOf N₀.M₁).map N₀.δ = ⊥ → ∀ x ∈ X, x = 1 := by
      intro X hXA hX x hx
      have h1 : N₀.δ ⟨x, hA₀M₀ (hXA hx)⟩ ∈ (X.subgroupOf N₀.M₁).map N₀.δ :=
        ⟨_, mem_subgroupOf.2 hx, rfl⟩
      rw [hX, mem_bot] at h1
      exact congrArg Subtype.val (N₀.δ_injective (h1.trans (map_one _).symm))
  rcases F.eq_bot_or_eq_bot hc' hinf' hsup' with h | h
  · right
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hcPQ (hdec ha)
    rw [hbot inf_le_left h x hx, one_mul]
    exact (mem_inf.1 hy).2
  · left
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hcPQ (hdec ha)
    rw [hbot inf_le_left h y hy, mul_one]
    exact (mem_inf.1 hx).2

end CaseBNotation

end CFSG.LocalAnalysis.EvenBN.LinearThree
