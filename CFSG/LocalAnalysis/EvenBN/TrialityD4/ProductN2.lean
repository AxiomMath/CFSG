module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductLayer
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Module

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

section Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def kTwo (d : TrialityD4Data L q) (t : G) (K : Subgroup G) : Subgroup G :=
  kThree d t K ⊔ yamadaM₆ d t

@[expose] noncomputable def kFour (d : TrialityD4Data L q) (t : G) (K : Subgroup G) : Subgroup G :=
  ⁅kTwo d t K, kTwo d t K⁆ ⊔ kThree d t K

@[expose] noncomputable def kFive (d : TrialityD4Data L q) (t : G) (K : Subgroup G) : Subgroup G :=
  ⁅kFour d t K, kFour d t K⁆ ⊔ kThree d t K ⊔ yamadaY₂ d t

@[expose] noncomputable def zKTwo (d : TrialityD4Data L q) (t : G) (K : Subgroup G) :
    Subgroup G :=
  centerMod (yamadaW₃ d t) (kTwo d t K)

@[expose] noncomputable def zKTwoT (d : TrialityD4Data L q) (t : G) (K : Subgroup G) :
    Subgroup G :=
  centerMod (yamadaW₃ d t) ((kTwo d t K)ᵍ[t])

end Defs

namespace ProductN2Aux

open scoped commutatorElement

section AbsCore

section Copies

variable {Q : Type*} [Group Q]

theorem map_inf_centralizer_aux (e : MulAut Q) (X H : Subgroup Q) :
    (X ⊓ centralizer (H : Set Q)).map e.toMonoidHom =
      X.map e.toMonoidHom ⊓ centralizer ((H.map e.toMonoidHom : Subgroup Q) : Set Q) := by
  ext y
  rw [mem_map_equiv, mem_inf, mem_inf, mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro ⟨hX, hC⟩
    refine ⟨hX, fun h hh => ?_⟩
    rw [SetLike.mem_coe, mem_map_equiv] at hh
    have := congrArg e (hC _ hh)
    simpa using this
  · rintro ⟨hX, hC⟩
    refine ⟨hX, fun h hh => ?_⟩
    have hh' : e h ∈ ((H.map e.toMonoidHom : Subgroup Q) : Set Q) := by
      rw [SetLike.mem_coe, mem_map_equiv]
      simpa using hh
    have := congrArg e.symm (hC _ hh')
    simpa using this

theorem mem_normalizer_bot_aux (g : Q) : g ∈ normalizer ((⊥ : Subgroup Q) : Set Q) := by
  rw [normalizer_eq_top (⊥ : Subgroup Q)]
  exact mem_top g

theorem centralizer_sup_aux (A B : Subgroup Q) :
    centralizer ((A ⊔ B : Subgroup Q) : Set Q) =
      centralizer (A : Set Q) ⊓ centralizer (B : Set Q) := by
  refine le_antisymm (le_inf (centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
    (centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))) fun x hx => ?_
  have h1 : zpowers x ≤ centralizer (A : Set Q) := (zpowers_le).2 (mem_inf.1 hx).1
  have h2 : zpowers x ≤ centralizer (B : Set Q) := (zpowers_le).2 (mem_inf.1 hx).2
  rw [le_centralizer_iff] at h1 h2
  have h3 : A ⊔ B ≤ centralizer ((zpowers x : Subgroup Q) : Set Q) := sup_le h1 h2
  rw [le_centralizer_iff] at h3
  exact h3 (mem_zpowers x)

end Copies

variable {Q : Type*} [Group Q] [Finite Q]

abbrev zOf (M A : Subgroup Q) : Subgroup Q := M ⊓ centralizer (A : Set Q)

abbrev hOf (t : Q) (A M : Subgroup Q) : Subgroup Q := A ⊔ zOf M (Aᵍ[t])

section Generic

variable {G : Type*} [Group G]

theorem conj_eq_self_of_commute {A A' : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a)
    {a y : G} (ha : a ∈ A) (hy : y ∈ A') : a * y * a⁻¹ = y := by
  rw [hcomm a ha y hy]
  group

theorem conj_eq_self_of_commute' {A A' : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a)
    {a y : G} (ha : a ∈ A) (hy : y ∈ A') : y * a * y⁻¹ = a := by
  rw [← hcomm a ha y hy]
  group

theorem conj_conj_comm {v t : G} (h : v * t = t * v) (x : G) :
    v * (t⁻¹ * x * t) * v⁻¹ = t⁻¹ * (v * x * v⁻¹) * t := by
  have h1 : v * t⁻¹ = t⁻¹ * v := by
    calc v * t⁻¹ = t⁻¹ * (t * v) * t⁻¹ := by group
      _ = t⁻¹ * (v * t) * t⁻¹ := by rw [h]
      _ = t⁻¹ * v := by group
  have h2 : t * v⁻¹ = v⁻¹ * t := by
    calc t * v⁻¹ = v⁻¹ * (v * t) * v⁻¹ := by group
      _ = v⁻¹ * (t * v) * v⁻¹ := by rw [h]
      _ = v⁻¹ * t := by group
  calc v * (t⁻¹ * x * t) * v⁻¹ = (v * t⁻¹) * x * (t * v⁻¹) := by group
    _ = (t⁻¹ * v) * x * (v⁻¹ * t) := by rw [h1, h2]
    _ = t⁻¹ * (v * x * v⁻¹) * t := by group

theorem le_normalizer_of_commute {A A' H H' : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hH : H ≤ A) (hH' : H' ≤ A') :
    H ≤ normalizer (H' : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [conj_eq_self_of_commute hcomm (hH hh) (hH' hx)]
    exact hx
  · intro hx
    have h1 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = h * x * h⁻¹ :=
      conj_eq_self_of_commute hcomm (inv_mem (hH hh)) (hH' hx)
    have h2 : x = h * x * h⁻¹ := by
      calc x = h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ := by group
        _ = h * x * h⁻¹ := h1
    rw [h2]
    exact hx

theorem eq_of_sup_eq_of_commute {A A' H H' : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hinf : A ⊓ A' = ⊥) (hH : H ≤ A)
    (hH' : H' ≤ A') (hsup : H ⊔ H' = A ⊔ A') : H = A := by
  refine le_antisymm hH fun a ha => ?_
  have ha' : a ∈ H ⊔ H' := hsup ▸ mem_sup_left ha
  have hnorm : H ≤ normalizer (H' : Set G) := le_normalizer_of_commute hcomm hH hH'
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H H' hnorm] at ha'
  obtain ⟨h, hh, h', hh', rfl⟩ := ha'
  have hmem : h' ∈ A ⊓ A' := ⟨by
    have := mul_mem (inv_mem (hH hh)) ha
    simpa using this, hH' hh'⟩
  rw [hinf, mem_bot] at hmem
  show h * h' ∈ H
  rw [hmem, mul_one]
  exact hh

theorem card_sup_eq_mul_of_commute {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hnorm : A ≤ normalizer (B : Set G) := le_normalizer_of_commute hcomm le_rfl le_rfl
  have hmem : ∀ p : A × B, (p.1 : G) * p.2 ∈ A ⊔ B := fun p =>
    mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)
  have hbij : Function.Bijective
      (fun p : A × B => (⟨(p.1 : G) * p.2, hmem p⟩ : ↥(A ⊔ B))) := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      have h' : a * b = a' * b' := congrArg Subtype.val h
      have hm : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
          _ = b' * b⁻¹ := by group
      have hmemi : a'⁻¹ * a ∈ A ⊓ B :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha') ha, hm ▸ mul_mem hb' (inv_mem hb)⟩
      rw [hinf, mem_bot] at hmemi
      have haa : a = a' := by
        have := congrArg (a' * ·) hmemi
        simpa using this
      subst haa
      have hbb : b = b' := mul_left_cancel h'
      subst hbb
      rfl
    · intro y
      obtain ⟨x, hx⟩ := y
      have hx' := hx
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A B hnorm] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

theorem comm_mul_of_central {h h' z z' : G} (hzh' : z * h' = h' * z) (hzz' : z * z' = z' * z)
    (hz'h : z' * h = h * z') :
    ⁅h * z, h' * z'⁆ = ⁅h, h'⁆ := by
  have hzc : z * (h' * z') * z⁻¹ = h' * z' := by
    calc z * (h' * z') * z⁻¹ = (z * h') * z' * z⁻¹ := by group
      _ = (h' * z) * z' * z⁻¹ := by rw [hzh']
      _ = h' * (z * z') * z⁻¹ := by group
      _ = h' * (z' * z) * z⁻¹ := by rw [hzz']
      _ = h' * z' := by group
  have hz'hinv : z' * h⁻¹ * z'⁻¹ = h⁻¹ := by
    calc z' * h⁻¹ * z'⁻¹ = (z' * h * z'⁻¹)⁻¹ := by group
      _ = (h * z' * z'⁻¹)⁻¹ := by rw [hz'h]
      _ = h⁻¹ := by group
  calc ⁅h * z, h' * z'⁆ = h * (z * (h' * z') * z⁻¹) * h⁻¹ * z'⁻¹ * h'⁻¹ := by
        rw [commutatorElement_def]; group
    _ = h * (h' * z') * h⁻¹ * z'⁻¹ * h'⁻¹ := by rw [hzc]
    _ = h * h' * (z' * h⁻¹ * z'⁻¹) * h'⁻¹ := by group
    _ = ⁅h, h'⁆ := by rw [hz'hinv, commutatorElement_def]

theorem comm_le_self (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem conj_twice {t : G} (ht : t * t = 1) (x : G) : t⁻¹ * (t⁻¹ * x * t) * t = x := by
  rw [inv_eq_of_mul_eq_one_right ht]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [ht]; simp

theorem mem_normalizer_centralizer_singleton [Finite G] {g t : G} (hg : g * t = t * g) :
    g ∈ normalizer (centralizer ({t} : Set G) : Set G) :=
  mem_normalizer_fintype fun n hn => by
    rw [SetLike.mem_coe, mem_centralizer_iff] at hn ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 := hn h (Set.mem_singleton h)
    have h2 : h * g⁻¹ = g⁻¹ * h := by
      calc h * g⁻¹ = g⁻¹ * (g * h) * g⁻¹ := by group
        _ = g⁻¹ * (h * g) * g⁻¹ := by rw [hg]
        _ = g⁻¹ * h := by group
    calc h * (g * n * g⁻¹) = (h * g) * n * g⁻¹ := by group
      _ = (g * h) * n * g⁻¹ := by rw [← hg]
      _ = g * (h * n) * g⁻¹ := by group
      _ = g * (n * h) * g⁻¹ := by rw [h1]
      _ = g * n * (h * g⁻¹) := by group
      _ = g * n * (g⁻¹ * h) := by rw [h2]
      _ = g * n * g⁻¹ * h := by group

end Generic

theorem center_sup_of {A A' M : Subgroup Q} (hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hc1 : ∀ x ∈ (A ⊔ A') ⊔ M, (∀ m ∈ M, x * m = m * x) → x ∈ M) :
    (A ⊔ M) ⊓ centralizer ((A ⊔ M : Subgroup Q) : Set Q) = M ⊓ centralizer (A : Set Q) := by
  have hMc' : ∀ x ∈ M, x ∈ centralizer (M : Set Q) := fun x hx =>
    mem_centralizer_iff.2 fun m hm => hMc m hm x hx
  apply le_antisymm
  · intro x hx
    obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxM : x ∈ M := by
      apply hc1 x (sup_le_sup_right le_sup_left M hxK)
      intro m hm
      exact (mem_centralizer_iff.1 hxC m (mem_sup_right hm)).symm
    exact Subgroup.mem_inf.2 ⟨hxM, centralizer_le (SetLike.coe_subset_coe.2
      (le_sup_left : A ≤ A ⊔ M)) hxC⟩
  · intro x hx
    obtain ⟨hxM, hxA⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨mem_sup_right hxM, ?_⟩
    rw [centralizer_sup_aux]
    exact Subgroup.mem_inf.2 ⟨hxA, hMc' x hxM⟩

structure HatData (t v : Q) (A M Qs F Lv L0 : Subgroup Q) : Prop where
  t_sq : t * t = 1
  v_sq : v * v = 1
  vt : v * t = t * v
  M_comm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x
  M_two : IsPGroup 2 M
  M_ne : M ≠ ⊥
  M_t : Mᵍ[t] = M
  v_M : v ∈ normalizer (M : Set Q)
  A_M : A ≤ normalizer (M : Set Q)
  A_comm : ∀ a ∈ A, ∀ b ∈ Aᵍ[t], a * b = b * a
  A_inf : A ⊓ Aᵍ[t] = ⊥
  A_inf_M : (A ⊔ Aᵍ[t]) ⊓ M = ⊥
  c1 : ∀ x ∈ (A ⊔ Aᵍ[t]) ⊔ M, (∀ m ∈ M, x * m = m * x) → x ∈ M
  Qs_A : Qs ≤ A
  Qs_two : IsPGroup 2 Qs
  v_dec : ∃ v₁ ∈ A, v = v₁ * (t⁻¹ * v₁ * t)
  gen : A ⊔ Aᵍ[t] = (Qs ⊔ Qsᵍ[t]) ⊔ (Qs ⊔ Qsᵍ[t]).map (MulAut.conj v).toMonoidHom
  F_ctr : ∀ x, x ∈ F ↔ x ∈ (M ⊔ (Qs ⊔ Qsᵍ[t]) : Subgroup Q) ∧
    x ∈ centralizer ((M ⊔ (Qs ⊔ Qsᵍ[t]) : Subgroup Q) : Set Q)
  F_t : Fᵍ[t] = F
  F_inf : F ⊓ F.map (MulAut.conj v).toMonoidHom = ⊥
  M_F : M ≤ F ⊔ F.map (MulAut.conj v).toMonoidHom
  free : Nat.card M = Nat.card ↥(M ⊓ centralizer ({t} : Set Q)) ^ 2
  L0_M : L0 ≤ normalizer (M : Set Q)
  L0_t : L0 ≤ centralizer ({t} : Set Q)
  L0_Z : L0 ≤ normalizer ((zOf M A ⊔ zOf M (Aᵍ[t]) : Subgroup Q) : Set Q)
  irr : ∀ S : Subgroup Q, S ≤ M ⊓ centralizer ({t} : Set Q) → L0 ≤ normalizer (S : Set Q) →
    S = ⊥ ∨ S = M ⊓ centralizer ({t} : Set Q)
  Lv_N : Lv ≤ (A ⊔ Aᵍ[t]) ⊔ M
  Lv_t : Lv ≤ centralizer ({t} : Set Q)
  Lv_v : v ∈ Lv
  Lv_Qs : ∀ q ∈ Qs, q * (t⁻¹ * q * t) ∈ Lv
  Lv_M : M ⊓ centralizer ({t} : Set Q) ≤ Lv
  Lv_perf : Lv ≤ ⁅Lv, Lv⁆
  core : ∀ R : Subgroup Q, R ≤ A ⊔ M → IsPGroup 2 R → A ≤ normalizer (R : Set Q) → R ≤ M

namespace HatData

variable {t v : Q} {A M Qs F Lv L0 : Subgroup Q} (D : HatData t v A M Qs F Lv L0)
include D

theorem v_mem : v ∈ (A ⊔ Aᵍ[t]) ⊔ M := by
  obtain ⟨v₁, hv₁, hv⟩ := D.v_dec
  rw [hv]
  exact mem_sup_left (mul_mem (mem_sup_left hv₁) (mem_sup_right (conj_mem_map_conj_inv t hv₁)))

theorem A'_M : Aᵍ[t] ≤ normalizer (M : Set Q) := by
  rintro _ ⟨a, ha, rfl⟩
  have h1 : t⁻¹ ∈ normalizer (M : Set Q) := by
    rw [mem_normalizer_iff_map_conj_eq]
    exact D.M_t
  exact mul_mem (mul_mem h1 (D.A_M ha)) (inv_mem h1)

theorem Qs_v_le : Qs.map (MulAut.conj v).toMonoidHom ≤ A := by
  obtain ⟨v₁, hv₁, hv⟩ := D.v_dec
  rintro _ ⟨q, hq, rfl⟩
  have hq' : q ∈ A := D.Qs_A hq
  have hv₁' : t⁻¹ * v₁ * t ∈ Aᵍ[t] := conj_mem_map_conj_inv t hv₁
  have e : (MulAut.conj v).toMonoidHom q = v₁ * ((t⁻¹ * v₁ * t) * q * (t⁻¹ * v₁ * t)⁻¹) * v₁⁻¹ := by
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, hv]
    group
  rw [e, conj_eq_self_of_commute' D.A_comm hq' hv₁']
  exact mul_mem (mul_mem hv₁ hq') (inv_mem hv₁)

theorem Qs'_v_le : (Qsᵍ[t]).map (MulAut.conj v).toMonoidHom ≤ Aᵍ[t] := by
  obtain ⟨v₁, hv₁, hv⟩ := D.v_dec
  rintro _ ⟨q, hq, rfl⟩
  have hq' : q ∈ Aᵍ[t] := Subgroup.map_mono D.Qs_A hq
  have hv₁' : t⁻¹ * v₁ * t ∈ Aᵍ[t] := conj_mem_map_conj_inv t hv₁
  have hy : (t⁻¹ * v₁ * t) * q * (t⁻¹ * v₁ * t)⁻¹ ∈ Aᵍ[t] :=
    mul_mem (mul_mem hv₁' hq') (inv_mem hv₁')
  have e : (MulAut.conj v).toMonoidHom q =
      v₁ * ((t⁻¹ * v₁ * t) * q * (t⁻¹ * v₁ * t)⁻¹) * v₁⁻¹ := by
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, hv]
    group
  rw [e, conj_eq_self_of_commute D.A_comm hv₁ hy]
  exact hy

theorem A_eq : A = Qs ⊔ Qs.map (MulAut.conj v).toMonoidHom := by
  have hgen := D.gen
  rw [Subgroup.map_sup] at hgen
  refine (eq_of_sup_eq_of_commute D.A_comm D.A_inf
    (H := Qs ⊔ Qs.map (MulAut.conj v).toMonoidHom)
    (H' := Qsᵍ[t] ⊔ (Qsᵍ[t]).map (MulAut.conj v).toMonoidHom)
    (sup_le D.Qs_A D.Qs_v_le) (sup_le (Subgroup.map_mono D.Qs_A) D.Qs'_v_le) ?_).symm
  rw [hgen]
  exact sup_sup_sup_comm _ _ _ _

theorem Z₂_eq : zOf M (Aᵍ[t]) = (zOf M A)ᵍ[t] := by
  have h := map_inf_centralizer_aux (MulAut.conj t⁻¹) M A
  rw [D.M_t] at h
  exact h.symm

theorem Z_inf : zOf M A ⊓ zOf M (Aᵍ[t]) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨⟨hzM, hzA⟩, ⟨-, hzA'⟩⟩ := (⟨mem_inf.1 (mem_inf.1 hz).1, mem_inf.1 (mem_inf.1 hz).2⟩ :
    (z ∈ M ∧ z ∈ centralizer (A : Set Q)) ∧
      (z ∈ M ∧ z ∈ centralizer ((Aᵍ[t] : Subgroup Q) : Set Q)))
  have hzM' : z ∈ centralizer (M : Set Q) := mem_centralizer_iff.2 fun m hm => D.M_comm m hm z hzM
  have hzN : z ∈ centralizer ((((A ⊔ Aᵍ[t]) ⊔ M : Subgroup Q)) : Set Q) := by
    rw [centralizer_sup_aux, centralizer_sup_aux]
    exact ⟨⟨hzA, hzA'⟩, hzM'⟩
  have hPN : (M ⊔ (Qs ⊔ Qsᵍ[t]) : Subgroup Q) ≤ (A ⊔ Aᵍ[t]) ⊔ M :=
    sup_le le_sup_right (sup_le (D.Qs_A.trans (le_sup_left.trans le_sup_left))
      ((Subgroup.map_mono D.Qs_A).trans (le_sup_right.trans le_sup_left)))
  have hzP : z ∈ (M ⊔ (Qs ⊔ Qsᵍ[t]) : Subgroup Q) := mem_sup_left hzM
  have hzF : z ∈ F := (D.F_ctr z).2 ⟨hzP, centralizer_le (SetLike.coe_subset_coe.2 hPN) hzN⟩
  have hvz : v * z * v⁻¹ = z := by
    have hc : v * z = z * v := mem_centralizer_iff.1 hzN v D.v_mem
    rw [hc]
    group
  have hzF' : z ∈ F.map (MulAut.conj v).toMonoidHom := ⟨z, hzF, by
    simpa using hvz⟩
  have : z ∈ F ⊓ F.map (MulAut.conj v).toMonoidHom := ⟨hzF, hzF'⟩
  rw [D.F_inf] at this
  exact this

theorem Z_ne_bot : zOf M A ≠ ⊥ := by
  intro hZ1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set cv : MulAut Q := MulAut.conj v with hcv
  set ct : MulAut Q := MulAut.conj t⁻¹ with hct
  set Qs' : Subgroup Q := Qsᵍ[t] with hQs'
  have hMv : M.map cv.toMonoidHom = M := mem_normalizer_iff_map_conj_eq.1 D.v_M
  have hMt : M.map ct.toMonoidHom = M := D.M_t
  have hFt : F.map ct.toMonoidHom = F := D.F_t
  have hvt' : ∀ x, cv (ct x) = ct (cv x) := by
    intro x
    simp only [hcv, hct, MulAut.conj_apply, inv_inv]
    exact conj_conj_comm D.vt x
  have hmapcomm : ∀ X : Subgroup Q, (X.map cv.toMonoidHom).map ct.toMonoidHom =
      (X.map ct.toMonoidHom).map cv.toMonoidHom := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (hvt' x).symm
  have hMc : ∀ x ∈ M, x ∈ centralizer (M : Set Q) := fun x hx =>
    mem_centralizer_iff.2 fun m hm => D.M_comm m hm x hx
  have hQsN : Qs ≤ (A ⊔ Aᵍ[t]) ⊔ M := D.Qs_A.trans (le_sup_left.trans le_sup_left)
  have hQs'N : Qs' ≤ (A ⊔ Aᵍ[t]) ⊔ M :=
    (Subgroup.map_mono D.Qs_A).trans (le_sup_right.trans le_sup_left)
  have hPN : (M ⊔ (Qs ⊔ Qs') : Subgroup Q) ≤ (A ⊔ Aᵍ[t]) ⊔ M :=
    sup_le le_sup_right (sup_le hQsN hQs'N)
  have hF : F = (M ⊓ centralizer (Qs : Set Q)) ⊓ (M ⊓ centralizer (Qs' : Set Q)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxP, hxC⟩ := (D.F_ctr x).1 hx
      have hxM : x ∈ M := by
        apply D.c1 x (hPN hxP)
        intro m hm
        exact (mem_centralizer_iff.1 hxC m (mem_sup_left hm)).symm
      exact ⟨⟨hxM, centralizer_le (SetLike.coe_subset_coe.2
          (le_sup_left.trans le_sup_right : Qs ≤ M ⊔ (Qs ⊔ Qs'))) hxC⟩,
        ⟨hxM, centralizer_le (SetLike.coe_subset_coe.2
          (le_sup_right.trans le_sup_right : Qs' ≤ M ⊔ (Qs ⊔ Qs'))) hxC⟩⟩
    · rintro ⟨⟨hxM, hxQ⟩, ⟨-, hxQ'⟩⟩
      refine (D.F_ctr x).2 ⟨mem_sup_left hxM, ?_⟩
      rw [centralizer_sup_aux, centralizer_sup_aux]
      exact ⟨hMc x hxM, hxQ, hxQ'⟩
  have hFZT : F ≤ M ⊓ centralizer (Qs : Set Q) := by
    rw [hF]
    exact inf_le_left
  have hZTv : (M ⊓ centralizer (Qs : Set Q)).map cv.toMonoidHom =
      M ⊓ centralizer ((Qs.map cv.toMonoidHom : Subgroup Q) : Set Q) := by
    rw [map_inf_centralizer_aux, hMv]
  have hZTvt : ((M ⊓ centralizer (Qs : Set Q)).map cv.toMonoidHom).map ct.toMonoidHom =
      M ⊓ centralizer (((Qs.map cv.toMonoidHom).map ct.toMonoidHom : Subgroup Q) : Set Q) := by
    rw [hZTv, map_inf_centralizer_aux, hMt]
  set Qs'' : Subgroup Q := (Qs.map cv.toMonoidHom).map ct.toMonoidHom with hQs''
  have hQs''A' : Qs'' ≤ Aᵍ[t] := Subgroup.map_mono D.Qs_v_le
  have hQs''2 : IsPGroup 2 Qs'' := (D.Qs_two.map cv.toMonoidHom).map ct.toMonoidHom
  have hnormQ : Qs ≤ normalizer (Qs'' : Set Q) :=
    le_normalizer_of_commute D.A_comm D.Qs_A hQs''A'
  have hR2 : IsPGroup 2 (Qs ⊔ Qs'' : Subgroup Q) :=
    D.Qs_two.to_sup_of_normal_right' hQs''2 hnormQ
  have hRM : (Qs ⊔ Qs'' : Subgroup Q) ≤ normalizer (M : Set Q) :=
    sup_le (D.Qs_A.trans D.A_M) (hQs''A'.trans D.A'_M)
  obtain ⟨x, hxM, hxne, hxfix⟩ := exists_mem_forall_conj_mem_of_isPGroup (p := 2)
    (R := Qs ⊔ Qs'') (H := M) (N := ⊥) hR2 D.M_two bot_le
    (fun hle => D.M_ne (le_bot_iff.1 hle)) hRM
    (fun r _ => mem_normalizer_bot_aux r)
    (fun r _ => mem_normalizer_bot_aux r)
  have hxC : ∀ r ∈ (Qs ⊔ Qs'' : Subgroup Q), r * x = x * r := by
    intro r hr
    have h1 := hxfix r hr
    rw [Subgroup.mem_bot] at h1
    have h2 : r * x * r⁻¹ = x := by
      have := congrArg (x * ·) h1
      simpa using this
    calc r * x = (r * x * r⁻¹) * r := by group
      _ = x * r := by rw [h2]
  have hxZT : x ∈ M ⊓ centralizer (Qs : Set Q) :=
    ⟨hxM, mem_centralizer_iff.2 fun r hr => hxC r (mem_sup_left hr)⟩
  have hxZT'' : x ∈ M ⊓ centralizer (Qs'' : Set Q) :=
    ⟨hxM, mem_centralizer_iff.2 fun r hr => hxC r (mem_sup_right hr)⟩
  have hx1 : x ≠ 1 := fun h => hxne (by rw [h]; exact one_mem _)
  have hA₀ : ∀ y ∈ (M ⊓ centralizer (Qs : Set Q)) ⊓ F.map cv.toMonoidHom, y = 1 := by
    intro y hy
    obtain ⟨⟨hyM, hyQ⟩, hyF⟩ := hy
    have hyQv : y ∈ centralizer ((Qs.map cv.toMonoidHom : Subgroup Q) : Set Q) := by
      have : y ∈ (M ⊓ centralizer (Qs : Set Q)).map cv.toMonoidHom :=
        Subgroup.map_mono hFZT hyF
      rw [hZTv] at this
      exact this.2
    have hyA : y ∈ zOf M A := by
      refine ⟨hyM, ?_⟩
      rw [D.A_eq, centralizer_sup_aux]
      exact ⟨hyQ, hyQv⟩
    rw [hZ1] at hyA
    exact (Subgroup.mem_bot.1 hyA)
  have hFM : F ≤ M := hFZT.trans inf_le_left
  have hFvM : F.map cv.toMonoidHom ≤ M := (Subgroup.map_mono hFM).trans hMv.le
  have hZTF : M ⊓ centralizer (Qs : Set Q) ≤ F := by
    intro y hy
    have hsplit : y ∈ F ⊔ F.map cv.toMonoidHom := D.M_F hy.1
    have hnormF : F ≤ normalizer ((F.map cv.toMonoidHom : Subgroup Q) : Set Q) :=
      le_normalizer_of_commute D.M_comm hFM hFvM
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right F (F.map cv.toMonoidHom) hnormF]
      at hsplit
    obtain ⟨f, hf, f', hf', hyf⟩ := hsplit
    have hyf' : f * f' = y := hyf
    have hf'ZT : f' ∈ (M ⊓ centralizer (Qs : Set Q)) ⊓ F.map cv.toMonoidHom := by
      refine ⟨?_, hf'⟩
      have : f⁻¹ * y ∈ M ⊓ centralizer (Qs : Set Q) := mul_mem (inv_mem (hFZT hf)) hy
      rwa [← hyf', inv_mul_cancel_left] at this
    have h1 : f' = 1 := hA₀ f' hf'ZT
    rw [← hyf', h1, mul_one]
    exact hf
  have hZT''le : M ⊓ centralizer (Qs'' : Set Q) ≤ F.map cv.toMonoidHom := by
    rw [← hZTvt]
    calc _ ≤ (F.map cv.toMonoidHom).map ct.toMonoidHom :=
          Subgroup.map_mono (Subgroup.map_mono hZTF)
      _ = (F.map ct.toMonoidHom).map cv.toMonoidHom := hmapcomm F
      _ = F.map cv.toMonoidHom := by rw [hFt]
  have hxF : x ∈ F := hZTF hxZT
  have hxFv : x ∈ F.map cv.toMonoidHom := hZT''le hxZT''
  have hx0 : x ∈ F ⊓ F.map cv.toMonoidHom := ⟨hxF, hxFv⟩
  rw [D.F_inf] at hx0
  exact hx1 (Subgroup.mem_bot.1 hx0)

theorem M_eq_sup : M = zOf M A ⊔ zOf M (Aᵍ[t]) ∧
    Nat.card ↥(zOf M A) = Nat.card ↥(M ⊓ centralizer ({t} : Set Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z₁ := zOf M A with hZ₁
  set Z₂ := zOf M (Aᵍ[t]) with hZ₂
  have hZ₁M : Z₁ ≤ M := inf_le_left
  have hZ₂M : Z₂ ≤ M := inf_le_left
  have hinf : Z₁ ⊓ Z₂ = ⊥ := D.Z_inf
  have hZ₂eq : Z₂ = Z₁ᵍ[t] := D.Z₂_eq
  have hZ₁eq : Z₂ᵍ[t] = Z₁ := by rw [hZ₂eq, map_conj_inv_map_conj_inv D.t_sq]
  have hcommZ : ∀ a ∈ Z₁, ∀ b ∈ Z₂, a * b = b * a := fun a ha b hb =>
    D.M_comm a (hZ₁M ha) b (hZ₂M hb)
  have hmemf : ∀ z ∈ Z₁, z * (t⁻¹ * z * t) ∈ (Z₁ ⊔ Z₂) ⊓ centralizer ({t} : Set Q) := by
    intro z hz
    have hz' : t⁻¹ * z * t ∈ Z₂ := by
      rw [hZ₂eq]
      exact conj_mem_map_conj_inv t hz
    refine Subgroup.mem_inf.2 ⟨mul_mem (mem_sup_left hz) (mem_sup_right hz'), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hy : t⁻¹ * (z * (t⁻¹ * z * t)) * t = z * (t⁻¹ * z * t) := by
      calc t⁻¹ * (z * (t⁻¹ * z * t)) * t = (t⁻¹ * z * t) * (t⁻¹ * (t⁻¹ * z * t) * t) := by group
        _ = (t⁻¹ * z * t) * z := by rw [conj_twice D.t_sq]
        _ = z * (t⁻¹ * z * t) := (D.M_comm _ (hZ₂M hz') _ (hZ₁M hz))
    calc z * (t⁻¹ * z * t) * t = t * (t⁻¹ * (z * (t⁻¹ * z * t)) * t) := by group
      _ = t * (z * (t⁻¹ * z * t)) := by rw [hy]
  let f : ↥Z₁ → ↥((Z₁ ⊔ Z₂) ⊓ centralizer ({t} : Set Q)) := fun z =>
    ⟨z * (t⁻¹ * z * t), hmemf z z.2⟩
  have hfbij : Function.Bijective f := by
    constructor
    · intro z w h
      have h' : (z : Q) * (t⁻¹ * z * t) = w * (t⁻¹ * w * t) := congrArg Subtype.val h
      have hw' : t⁻¹ * (w : Q) * t ∈ Z₂ := by
        rw [hZ₂eq]
        exact conj_mem_map_conj_inv t w.2
      have hz' : t⁻¹ * (z : Q) * t ∈ Z₂ := by
        rw [hZ₂eq]
        exact conj_mem_map_conj_inv t z.2
      have hm : (w : Q)⁻¹ * z = (t⁻¹ * w * t) * (t⁻¹ * z * t)⁻¹ := by
        calc (w : Q)⁻¹ * z = (w : Q)⁻¹ * (z * (t⁻¹ * z * t)) * (t⁻¹ * z * t)⁻¹ := by group
          _ = (w : Q)⁻¹ * (w * (t⁻¹ * w * t)) * (t⁻¹ * z * t)⁻¹ := by rw [h']
          _ = (t⁻¹ * w * t) * (t⁻¹ * z * t)⁻¹ := by group
      have hmem : (w : Q)⁻¹ * z ∈ Z₁ ⊓ Z₂ :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem w.2) z.2, by rw [hm]; exact mul_mem hw' (inv_mem hz')⟩
      rw [hinf, mem_bot] at hmem
      apply Subtype.ext
      have := congrArg (fun x => (w : Q) * x) hmem
      simpa using this
    · intro y
      obtain ⟨y, hy⟩ := y
      obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.1 hy
      have hnorm : Z₁ ≤ normalizer (Z₂ : Set Q) := le_normalizer_of_commute hcommZ le_rfl le_rfl
      have hyS' := hyS
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Z₁ Z₂ hnorm] at hyS'
      obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hyS'
      have hc : t * (z₁ * z₂) = (z₁ * z₂) * t := (mem_centralizer_singleton_iff.1 hyC).symm
      have hfix : t⁻¹ * (z₁ * z₂) * t = z₁ * z₂ := by
        calc t⁻¹ * (z₁ * z₂) * t = t⁻¹ * ((z₁ * z₂) * t) := by group
          _ = t⁻¹ * (t * (z₁ * z₂)) := by rw [hc]
          _ = z₁ * z₂ := by group
      have ha : t⁻¹ * z₁ * t ∈ Z₂ := by
        rw [hZ₂eq]
        exact conj_mem_map_conj_inv t hz₁
      have hb : t⁻¹ * z₂ * t ∈ Z₁ := by
        rw [← hZ₁eq]
        exact conj_mem_map_conj_inv t hz₂
      have hab : (t⁻¹ * z₂ * t) * (t⁻¹ * z₁ * t) = z₁ * z₂ := by
        calc (t⁻¹ * z₂ * t) * (t⁻¹ * z₁ * t) = (t⁻¹ * z₁ * t) * (t⁻¹ * z₂ * t) :=
              (hcommZ _ hb _ ha)
          _ = t⁻¹ * (z₁ * z₂) * t := by group
          _ = z₁ * z₂ := hfix
      have hm : z₁⁻¹ * (t⁻¹ * z₂ * t) = z₂ * (t⁻¹ * z₁ * t)⁻¹ := by
        calc z₁⁻¹ * (t⁻¹ * z₂ * t) = z₁⁻¹ * ((t⁻¹ * z₂ * t) * (t⁻¹ * z₁ * t)) *
              (t⁻¹ * z₁ * t)⁻¹ := by group
          _ = z₁⁻¹ * (z₁ * z₂) * (t⁻¹ * z₁ * t)⁻¹ := by rw [hab]
          _ = z₂ * (t⁻¹ * z₁ * t)⁻¹ := by group
      have hmem : z₁⁻¹ * (t⁻¹ * z₂ * t) ∈ Z₁ ⊓ Z₂ :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hz₁) hb, by rw [hm]; exact mul_mem hz₂ (inv_mem ha)⟩
      rw [hinf, mem_bot] at hmem
      have hb' : t⁻¹ * z₂ * t = z₁ := by
        have := congrArg (fun x => z₁ * x) hmem
        simpa using this
      have hz₂' : z₂ = t⁻¹ * z₁ * t := by
        have e1 : z₂ = t * (t⁻¹ * z₂ * t) * t⁻¹ := by group
        rw [e1, hb', inv_eq_of_mul_eq_one_right D.t_sq]
      refine ⟨⟨z₁, hz₁⟩, Subtype.ext ?_⟩
      show z₁ * (t⁻¹ * z₁ * t) = z₁ * z₂
      rw [hz₂']
  have hcard1 : Nat.card ↥((Z₁ ⊔ Z₂) ⊓ centralizer ({t} : Set Q)) = Nat.card ↥Z₁ :=
    (Nat.card_congr (Equiv.ofBijective f hfbij)).symm
  have hcard2 : Nat.card ↥(Z₁ ⊔ Z₂) = Nat.card ↥Z₁ * Nat.card ↥Z₁ := by
    rw [card_sup_eq_mul_of_commute hcommZ hinf, hZ₂eq,
      Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective]
  have hÎM : Z₁ ⊔ Z₂ ≤ M := sup_le hZ₁M hZ₂M
  set S : Subgroup Q := (Z₁ ⊔ Z₂) ⊓ centralizer ({t} : Set Q) with hS
  have hSM : S ≤ M ⊓ centralizer ({t} : Set Q) := inf_le_inf_right _ hÎM
  have hL0S : L0 ≤ normalizer (S : Set Q) := by
    intro g hg
    have h1 : g ∈ normalizer ((Z₁ ⊔ Z₂ : Subgroup Q) : Set Q) := D.L0_Z hg
    have h2 : g ∈ normalizer (centralizer ({t} : Set Q) : Set Q) :=
      mem_normalizer_centralizer_singleton
        (mem_centralizer_singleton_iff.1 (D.L0_t hg))
    exact mem_normalizer_inf_D4 h1 h2
  have hSne : S ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥S = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hcard1] at h1
    exact D.Z_ne_bot (Subgroup.card_eq_one.1 h1)
  rcases D.irr S hSM hL0S with h | h
  · exact absurd h hSne
  · have hcZ : Nat.card ↥Z₁ = Nat.card ↥(M ⊓ centralizer ({t} : Set Q)) := by
      rw [← hcard1, ← h]
    refine ⟨?_, hcZ⟩
    symm
    refine Subgroup.eq_of_le_of_card_ge hÎM ?_
    rw [hcard2, hcZ, ← sq]
    exact D.free.le

theorem diag_fix {z : Q} (hz : z ∈ M) (hz' : t⁻¹ * z * t ∈ M) :
    z * (t⁻¹ * z * t) ∈ M ⊓ centralizer ({t} : Set Q) := by
  refine Subgroup.mem_inf.2 ⟨mul_mem hz hz', ?_⟩
  rw [mem_centralizer_singleton_iff]
  have hy : t⁻¹ * (z * (t⁻¹ * z * t)) * t = z * (t⁻¹ * z * t) := by
    calc t⁻¹ * (z * (t⁻¹ * z * t)) * t = (t⁻¹ * z * t) * (t⁻¹ * (t⁻¹ * z * t) * t) := by group
      _ = (t⁻¹ * z * t) * z := by rw [conj_twice D.t_sq]
      _ = z * (t⁻¹ * z * t) := D.M_comm _ hz' _ hz
  calc z * (t⁻¹ * z * t) * t = t * (t⁻¹ * (z * (t⁻¹ * z * t)) * t) := by group
    _ = t * (z * (t⁻¹ * z * t)) := by rw [hy]

theorem Z₂_t : (zOf M (Aᵍ[t]))ᵍ[t] = zOf M A := by
  rw [D.Z₂_eq, map_conj_inv_map_conj_inv D.t_sq]

theorem A_norm_Z₂ : A ≤ normalizer ((zOf M (Aᵍ[t]) : Subgroup Q) : Set Q) := fun a ha =>
  mem_normalizer_inf_D4 (D.A_M ha)
    (mem_normalizer_centralizer_D4 (le_normalizer_of_commute D.A_comm le_rfl le_rfl ha))

theorem A'_norm_Z₁ : Aᵍ[t] ≤ normalizer ((zOf M A : Subgroup Q) : Set Q) := fun a ha =>
  mem_normalizer_inf_D4 (D.A'_M ha)
    (mem_normalizer_centralizer_D4
      (le_normalizer_of_commute (fun a ha b hb => (D.A_comm b hb a ha).symm)
        (le_rfl : Aᵍ[t] ≤ Aᵍ[t]) (le_rfl : A ≤ A) ha))

theorem H₂_eq : (hOf t A M)ᵍ[t] = Aᵍ[t] ⊔ zOf M A := by
  rw [Subgroup.map_sup]
  congr 1
  exact D.Z₂_t

theorem H_comm : ∀ a ∈ hOf t A M, ∀ b ∈ (hOf t A M)ᵍ[t], a * b = b * a := by
  intro a ha b hb
  rw [D.H₂_eq] at hb
  have hle : hOf t A M ≤ centralizer (((Aᵍ[t] ⊔ zOf M A : Subgroup Q)) : Set Q) := by
    rw [centralizer_sup_aux]
    refine le_inf (sup_le ?_ ?_) (sup_le ?_ ?_)
    · intro x hx
      exact mem_centralizer_iff.2 fun h hh => (D.A_comm x hx h hh).symm
    · exact inf_le_right
    · intro x hx
      exact mem_centralizer_iff.2 fun h hh => (mem_centralizer_iff.1 hh.2 x hx).symm
    · intro x hx
      exact mem_centralizer_iff.2 fun h hh => D.M_comm h hh.1 x hx.1
  exact (mem_centralizer_iff.1 (hle ha) b hb).symm

theorem prod_decomp :
    (A ⊔ Aᵍ[t]) ⊔ M = hOf t A M ⊔ (hOf t A M)ᵍ[t] ∧
    hOf t A M ⊓ (hOf t A M)ᵍ[t] = ⊥ ∧ ⁅hOf t A M, (hOf t A M)ᵍ[t]⁆ = ⊥ := by
  have hM := D.M_eq_sup.1
  have hcomm : ∀ a ∈ hOf t A M, ∀ b ∈ (hOf t A M)ᵍ[t], a * b = b * a := D.H_comm
  refine ⟨?_, ?_, ?_⟩
  · rw [D.H₂_eq]
    calc (A ⊔ Aᵍ[t]) ⊔ M = (A ⊔ Aᵍ[t]) ⊔ (zOf M A ⊔ zOf M (Aᵍ[t])) := by rw [← hM]
      _ = (A ⊔ zOf M (Aᵍ[t])) ⊔ (Aᵍ[t] ⊔ zOf M A) := by
        rw [sup_comm (zOf M A)]
        exact sup_sup_sup_comm _ _ _ _
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    rw [D.H₂_eq] at hx2
    have hn1 : A ≤ normalizer ((zOf M (Aᵍ[t]) : Subgroup Q) : Set Q) := D.A_norm_Z₂
    have hn2 : Aᵍ[t] ≤ normalizer ((zOf M A : Subgroup Q) : Set Q) := D.A'_norm_Z₁
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A _ hn1] at hx1
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (Aᵍ[t]) _ hn2] at hx2
    obtain ⟨a, ha, z₂, hz₂, rfl⟩ := hx1
    obtain ⟨a', ha', z₁, hz₁, hxx⟩ := hx2
    have hxx' : a' * z₁ = a * z₂ := hxx
    have hm : a'⁻¹ * a = z₁ * z₂⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * z₂) * z₂⁻¹ := by group
        _ = a'⁻¹ * (a' * z₁) * z₂⁻¹ := by rw [hxx']
        _ = z₁ * z₂⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ (A ⊔ Aᵍ[t]) ⊓ M := Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem (mem_sup_right ha')) (mem_sup_left ha), by
        rw [hm]
        exact mul_mem (hz₁.1) (inv_mem hz₂.1)⟩
    rw [D.A_inf_M, Subgroup.mem_bot] at hmem
    have haa : a = a' := by
      have := congrArg (a' * ·) hmem
      simpa using this
    have ha1 : a = 1 := by
      have : a ∈ A ⊓ Aᵍ[t] := Subgroup.mem_inf.2 ⟨ha, haa ▸ ha'⟩
      rw [D.A_inf, Subgroup.mem_bot] at this
      exact this
    have hz : a * z₂ ∈ zOf M A ⊓ zOf M (Aᵍ[t]) := by
      rw [ha1, one_mul]
      refine Subgroup.mem_inf.2 ⟨?_, hz₂⟩
      have : z₁ = z₂ := by
        rw [ha1, one_mul] at hxx'
        rw [haa] at ha1
        rw [ha1, one_mul] at hxx'
        exact hxx'
      exact this ▸ hz₁
    rw [D.Z_inf, Subgroup.mem_bot] at hz
    show a * z₂ = 1
    exact hz
  · rw [commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact mem_centralizer_iff.2 fun b hb => (D.H_comm a ha b hb).symm

theorem fixed_eq :
    ((A ⊔ Aᵍ[t]) ⊔ M) ⊓ centralizer ({t} : Set Q) = Lv ∧
    ∃ e : ↥(hOf t A M) ≃* ↥Lv, ∀ h, ((e h : ↥Lv) : Q) = (h : Q) * (t⁻¹ * (h : Q) * t) := by
  obtain ⟨hN, hinf, hcomm⟩ := D.prod_decomp
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right D.t_sq
  set H₁ := hOf t A M with hH₁
  let δ : ↥H₁ →* Q := diagonalHom H₁ t hcomm
  have hδ : ∀ h : ↥H₁, δ h = (h : Q) * (t⁻¹ * (h : Q) * t) := fun h => rfl
  have hfixN : ∀ x ∈ ((A ⊔ Aᵍ[t]) ⊔ M) ⊓ centralizer ({t} : Set Q), ∃ h : ↥H₁, δ h = x := by
    intro x hx
    obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.1 hx
    rw [hN] at hxN
    have hnorm : H₁ ≤ normalizer ((H₁ᵍ[t] : Subgroup Q) : Set Q) :=
      le_normalizer_of_commute D.H_comm le_rfl le_rfl
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H₁ _ hnorm] at hxN
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hxN
    have hc : (h₁ * h₂) * t = t * (h₁ * h₂) := mem_centralizer_singleton_iff.1 hxC
    have hfix : t⁻¹ * (h₁ * h₂) * t = h₁ * h₂ := by
      calc t⁻¹ * (h₁ * h₂) * t = t⁻¹ * ((h₁ * h₂) * t) := by group
        _ = t⁻¹ * (t * (h₁ * h₂)) := by rw [hc]
        _ = h₁ * h₂ := by group
    have ha : t⁻¹ * h₁ * t ∈ H₁ᵍ[t] := conj_mem_map_conj_inv t hh₁
    have hb : t⁻¹ * h₂ * t ∈ H₁ := by
      have := mem_map_conj_inv_iff.1 hh₂
      rwa [ht'] at this ⊢
    have hab : (t⁻¹ * h₂ * t) * (t⁻¹ * h₁ * t) = h₁ * h₂ := by
      calc (t⁻¹ * h₂ * t) * (t⁻¹ * h₁ * t) = (t⁻¹ * h₁ * t) * (t⁻¹ * h₂ * t) :=
            D.H_comm _ hb _ ha
        _ = t⁻¹ * (h₁ * h₂) * t := by group
        _ = h₁ * h₂ := hfix
    have hm : h₁⁻¹ * (t⁻¹ * h₂ * t) = h₂ * (t⁻¹ * h₁ * t)⁻¹ := by
      calc h₁⁻¹ * (t⁻¹ * h₂ * t) = h₁⁻¹ * ((t⁻¹ * h₂ * t) * (t⁻¹ * h₁ * t)) *
            (t⁻¹ * h₁ * t)⁻¹ := by group
        _ = h₁⁻¹ * (h₁ * h₂) * (t⁻¹ * h₁ * t)⁻¹ := by rw [hab]
        _ = h₂ * (t⁻¹ * h₁ * t)⁻¹ := by group
    have hmem : h₁⁻¹ * (t⁻¹ * h₂ * t) ∈ H₁ ⊓ H₁ᵍ[t] :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hh₁) hb, by rw [hm]; exact mul_mem hh₂ (inv_mem ha)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hb' : t⁻¹ * h₂ * t = h₁ := by
      have := congrArg (fun x => h₁ * x) hmem
      simpa using this
    have hh₂' : h₂ = t⁻¹ * h₁ * t := by
      have e1 : h₂ = t * (t⁻¹ * h₂ * t) * t⁻¹ := by group
      rw [e1, hb', ht']
    refine ⟨⟨h₁, hh₁⟩, ?_⟩
    rw [hδ]
    show h₁ * (t⁻¹ * h₁ * t) = h₁ * h₂
    rw [hh₂']
  set T : Subgroup Q := (Lv.comap δ).map H₁.subtype with hTdef
  have hT : ∀ x, x ∈ T ↔ ∃ hx : x ∈ H₁, δ ⟨x, hx⟩ ∈ Lv := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hδx⟩
      exact ⟨⟨x, hx⟩, hδx, rfl⟩
  have hAH : A ≤ H₁ := le_sup_left
  have hQsT : Qs ≤ T := fun q hq => (hT q).2 ⟨hAH (D.Qs_A hq), D.Lv_Qs q hq⟩
  obtain ⟨v₁, hv₁, hv⟩ := D.v_dec
  have hδv₁ : δ ⟨v₁, hAH hv₁⟩ = v := by rw [hδ]; exact hv.symm
  have hQsvT : Qs.map (MulAut.conj v).toMonoidHom ≤ T := by
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ A := D.Qs_A hq
    have hv₁' : t⁻¹ * v₁ * t ∈ Aᵍ[t] := conj_mem_map_conj_inv t hv₁
    have e : (MulAut.conj v).toMonoidHom q = v₁ * q * v₁⁻¹ := by
      have e0 : (MulAut.conj v).toMonoidHom q =
          v₁ * ((t⁻¹ * v₁ * t) * q * (t⁻¹ * v₁ * t)⁻¹) * v₁⁻¹ := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, hv]
        group
      rw [e0, conj_eq_self_of_commute' D.A_comm hq' hv₁']
    rw [e]
    have hy : v₁ * q * v₁⁻¹ ∈ H₁ := hAH (mul_mem (mul_mem hv₁ hq') (inv_mem hv₁))
    refine (hT _).2 ⟨hy, ?_⟩
    have : δ ⟨v₁ * q * v₁⁻¹, hy⟩ = δ ⟨v₁, hAH hv₁⟩ * δ ⟨q, hAH hq'⟩ * (δ ⟨v₁, hAH hv₁⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this, hδv₁]
    exact mul_mem (mul_mem D.Lv_v (D.Lv_Qs q hq)) (inv_mem D.Lv_v)
  have hAT : A ≤ T := D.A_eq.le.trans (sup_le hQsT hQsvT)
  have hZ₂T : zOf M (Aᵍ[t]) ≤ T := by
    intro z hz
    have hzH : z ∈ H₁ := mem_sup_right hz
    refine (hT z).2 ⟨hzH, ?_⟩
    have hz' : t⁻¹ * z * t ∈ zOf M A := by
      rw [← D.Z₂_t]
      exact conj_mem_map_conj_inv t hz
    exact D.Lv_M (D.diag_fix hz.1 hz'.1)
  have hH₁T : H₁ ≤ T := sup_le hAT hZ₂T
  have hδLv : ∀ h : ↥H₁, δ h ∈ Lv := fun h => by
    obtain ⟨hx, hδx⟩ := (hT h).1 (hH₁T h.2)
    exact hδx
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro h h1
    have h2 := (diagonalHom_eq_one_iff hcomm h).1 h1
    have h3 : (h : Q)⁻¹ ∈ H₁ ⊓ H₁ᵍ[t] := Subgroup.mem_inf.2 ⟨inv_mem h.2, by
      rw [← h2]; exact conj_mem_map_conj_inv t h.2⟩
    rw [hinf, Subgroup.mem_bot, inv_eq_one] at h3
    exact Subtype.ext h3
  have hfix : ((A ⊔ Aᵍ[t]) ⊔ M) ⊓ centralizer ({t} : Set Q) = Lv := by
    apply le_antisymm
    · intro x hx
      obtain ⟨h, rfl⟩ := hfixN x hx
      exact hδLv h
    · intro y hy
      exact Subgroup.mem_inf.2 ⟨D.Lv_N hy, D.Lv_t hy⟩
  refine ⟨hfix, ?_⟩
  refine ⟨MulEquiv.ofBijective (δ.codRestrict Lv hδLv) ⟨?_, ?_⟩, fun h => rfl⟩
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  · rintro ⟨y, hy⟩
    obtain ⟨h, hh⟩ := hfixN y (hfix ▸ hy)
    exact ⟨h, Subtype.ext hh⟩

theorem K₄_eq : ⁅A ⊔ M, A ⊔ M⁆ ⊔ A = hOf t A M ∧ hOf t A M ≤ ⁅hOf t A M, hOf t A M⁆ := by
  obtain ⟨hfix, e, he⟩ := D.fixed_eq
  have hM := D.M_eq_sup.1
  set H₁ := hOf t A M with hH₁
  set Z₁ := zOf M A with hZ₁
  set Z₂ := zOf M (Aᵍ[t]) with hZ₂
  have hZ₁M : Z₁ ≤ M := inf_le_left
  have hZ₂M : Z₂ ≤ M := inf_le_left
  have hH₁K : H₁ ≤ A ⊔ M := sup_le le_sup_left (hZ₂M.trans le_sup_right)
  have hperf : H₁ ≤ ⁅H₁, H₁⁆ := by
    have hLvp : Group.IsPerfect ↥Lv :=
      Subgroup.isPerfect_iff.2 (le_antisymm (comm_le_self Lv) D.Lv_perf)
    have : Group.IsPerfect ↥H₁ :=
      Group.IsPerfect.ofSurjective (G := ↥Lv) (G' := ↥H₁) (f := e.symm.toMonoidHom)
        e.symm.surjective
    exact (Subgroup.isPerfect_iff.1 this).ge
  refine ⟨?_, hperf⟩
  apply le_antisymm
  · refine sup_le ?_ le_sup_left
    have hKH : A ⊔ M = H₁ ⊔ Z₁ := by
      apply le_antisymm
      · refine sup_le (le_sup_left.trans le_sup_left) ?_
        refine hM.le.trans (sup_le le_sup_right ?_)
        exact (le_sup_right : Z₂ ≤ H₁).trans le_sup_left
      · refine sup_le (sup_le le_sup_left (hZ₂M.trans le_sup_right)) (hZ₁M.trans le_sup_right)
    have hZ₁c : ∀ z ∈ Z₁, ∀ h ∈ H₁, z * h = h * z := by
      intro z hz h hh
      have hle : H₁ ≤ centralizer (Z₁ : Set Q) := by
        refine sup_le ?_ ?_
        · intro a ha
          exact mem_centralizer_iff.2 fun z hz => (mem_centralizer_iff.1 hz.2 a ha).symm
        · intro a ha
          exact mem_centralizer_iff.2 fun z hz => D.M_comm z hz.1 a ha.1
      exact mem_centralizer_iff.1 (hle hh) z hz
    have hnorm : H₁ ≤ normalizer (Z₁ : Set Q) :=
      le_normalizer_of_commute (A := H₁) (A' := Z₁) (fun h hh z hz => (hZ₁c z hz h hh).symm)
        le_rfl le_rfl
    rw [hKH, commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H₁ Z₁ hnorm] at hg₁ hg₂
    obtain ⟨h, hh, z, hz, rfl⟩ := hg₁
    obtain ⟨h', hh', z', hz', rfl⟩ := hg₂
    have e1 : ⁅h * z, h' * z'⁆ = ⁅h, h'⁆ :=
      comm_mul_of_central (hZ₁c z hz h' hh') (D.M_comm z (hZ₁M hz) z' (hZ₁M hz'))
        (hZ₁c z' hz' h hh)
    show ⁅h * z, h' * z'⁆ ∈ H₁
    rw [e1]
    exact comm_le_self H₁ (Subgroup.commutator_mem_commutator hh hh')
  · exact hperf.trans ((commutator_mono hH₁K hH₁K).trans le_sup_left)

theorem pcore_eq :
    zOf M (Aᵍ[t]) ≤ hOf t A M ∧ IsPGroup 2 (zOf M (Aᵍ[t])) ∧
    hOf t A M ≤ normalizer ((zOf M (Aᵍ[t]) : Subgroup Q) : Set Q) ∧
    ∀ R : Subgroup Q, R ≤ hOf t A M → hOf t A M ≤ normalizer (R : Set Q) → IsPGroup 2 R →
      R ≤ zOf M (Aᵍ[t]) := by
  refine ⟨le_sup_right, D.M_two.to_le inf_le_left, sup_le D.A_norm_Z₂ le_normalizer, ?_⟩
  intro R hRH hHN hR2
  have hAN : A ≤ normalizer (R : Set Q) := (le_sup_left : A ≤ hOf t A M).trans hHN
  have hRK : R ≤ A ⊔ M := hRH.trans (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  have hRM : R ≤ M := D.core R hRK hR2 hAN
  intro r hr
  have hrH := hRH hr
  have hn : A ≤ normalizer ((zOf M (Aᵍ[t]) : Subgroup Q) : Set Q) := D.A_norm_Z₂
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A _ hn] at hrH
  obtain ⟨a, ha, z, hz, rfl⟩ := hrH
  have haM : a ∈ M := by
    have := mul_mem (hRM hr) (inv_mem hz.1)
    simpa using this
  have h1 : a ∈ (A ⊔ Aᵍ[t]) ⊓ M := Subgroup.mem_inf.2 ⟨mem_sup_left ha, haM⟩
  rw [D.A_inf_M, Subgroup.mem_bot] at h1
  show a * z ∈ zOf M (Aᵍ[t])
  rw [h1, one_mul]
  exact hz

end HatData

end AbsCore

section Hat

open NormalizerQuotient

variable {G : Type*} [Group G] {W : Subgroup G}

theorem mem_bar_iff_exists {X : Subgroup G} {y : Bar W} :
    y ∈ bar W X ↔ ∃ x : normalizer (W : Set G), (x : G) ∈ X ∧ proj W x = y := by
  unfold bar
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.2 hx, rfl⟩

theorem bar_sup {X Y : Subgroup G} (hX : X ≤ normalizer (W : Set G))
    (hY : Y ≤ normalizer (W : Set G)) : bar W (X ⊔ Y) = bar W X ⊔ bar W Y := by
  unfold bar
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem bar_inf {X Y : Subgroup G} (hWX : W ≤ X) : bar W (X ⊓ Y) = bar W X ⊓ bar W Y := by
  apply le_antisymm (le_inf (bar_mono inf_le_left) (bar_mono inf_le_right))
  intro y hy
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨x₀, rfl⟩ := proj_surjective y
  have hx₀X : (x₀ : G) ∈ X := (mem_bar_iff hWX x₀).1 hy1
  obtain ⟨y', hy'Y, e⟩ := mem_bar_iff_exists.1 hy2
  have hw : (y' : G)⁻¹ * x₀ ∈ W := proj_eq_proj_iff.1 e
  have hy'X : (y' : G) ∈ X := by
    have : (y' : G) = x₀ * ((y' : G)⁻¹ * x₀)⁻¹ := by group
    rw [this]
    exact mul_mem hx₀X (inv_mem (hWX hw))
  rw [← e]
  exact mem_bar_iff_exists.2 ⟨y', Subgroup.mem_inf.2 ⟨hy'X, hy'Y⟩, rfl⟩

theorem bar_map_conj {g : G} (hg : g ∈ normalizer (W : Set G)) {X : Subgroup G}
    (hX : X ≤ normalizer (W : Set G)) :
    bar W (X.map (MulAut.conj g).toMonoidHom) =
      (bar W X).map (MulAut.conj (proj W ⟨g, hg⟩)).toMonoidHom := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_bar_iff_exists.1 hy
    obtain ⟨x, hx, hxz⟩ := hz
    have hxN : x ∈ normalizer (W : Set G) := hX hx
    refine ⟨proj W ⟨x, hxN⟩, mem_bar_iff_exists.2 ⟨⟨x, hxN⟩, hx, rfl⟩, ?_⟩
    have e : (⟨z, z.2⟩ : normalizer (W : Set G)) = ⟨g, hg⟩ * ⟨x, hxN⟩ * ⟨g, hg⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hxz]
      simp [MulAut.conj_apply]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul, ← e]
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy'
    have hxN : (x : G) ∈ normalizer (W : Set G) := x.2
    have hzN : g * (x : G) * g⁻¹ ∈ normalizer (W : Set G) :=
      mul_mem (mul_mem hg hxN) (inv_mem hg)
    refine mem_bar_iff_exists.2 ⟨⟨g * x * g⁻¹, hzN⟩, ⟨x, hx, ?_⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl

theorem bar_commutator {X Y : Subgroup G} (hX : X ≤ normalizer (W : Set G))
    (hY : Y ≤ normalizer (W : Set G)) : bar W ⁅X, Y⁆ = ⁅bar W X, bar W Y⁆ := by
  have hXY : ⁅X, Y⁆ ≤ normalizer (W : Set G) :=
    (commutator_mono hX hY).trans (Subgroup.commutator_le_self _)
  have hsub : ⁅X, Y⁆.subgroupOf (normalizer (W : Set G)) =
      ⁅X.subgroupOf (normalizer (W : Set G)), Y.subgroupOf (normalizer (W : Set G))⁆ := by
    apply Subgroup.map_injective (normalizer (W : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hXY, inf_of_le_left hX, inf_of_le_left hY]
  unfold bar
  rw [hsub, Subgroup.map_commutator]

theorem proj_mem_normalizer_bar [Finite G] {Y : Subgroup G} (hWY : W ≤ Y) {g : G}
    (hgW : g ∈ normalizer (W : Set G)) (hgY : g ∈ normalizer (Y : Set G)) :
    proj W ⟨g, hgW⟩ ∈ normalizer ((bar W Y : Subgroup (Bar W)) : Set (Bar W)) :=
  bar_le_normalizer_bar hWY (Subgroup.zpowers_le.2 hgY) (proj_mem_bar (mem_zpowers g))

theorem lift_sup {Y₁ Y₂ : Subgroup (Bar W)} : lift (Y₁ ⊔ Y₂) = lift Y₁ ⊔ lift Y₂ := by
  have h1 : lift Y₁ ≤ normalizer (W : Set G) := lift_le_normalizer Y₁
  have h2 : lift Y₂ ≤ normalizer (W : Set G) := lift_le_normalizer Y₂
  have h3 : bar W (lift Y₁ ⊔ lift Y₂) = Y₁ ⊔ Y₂ := by
    rw [bar_sup h1 h2, bar_lift, bar_lift]
  have h4 := lift_bar (A := W) (X := lift Y₁ ⊔ lift Y₂) (le_sup_of_le_left (le_lift Y₁))
    (sup_le h1 h2)
  rw [h3] at h4
  exact h4

theorem lift_inf {Y₁ Y₂ : Subgroup (Bar W)} : lift (Y₁ ⊓ Y₂) = lift Y₁ ⊓ lift Y₂ := by
  ext g
  rw [Subgroup.mem_inf, mem_lift_iff, mem_lift_iff, mem_lift_iff]
  constructor
  · rintro ⟨hg, hy⟩
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hy
    exact ⟨⟨hg, h1⟩, ⟨hg, h2⟩⟩
  · rintro ⟨⟨hg, h1⟩, ⟨hg', h2⟩⟩
    exact ⟨hg, Subgroup.mem_inf.2 ⟨h1, h2⟩⟩

theorem map_subtype_center {Γ : Type*} [Group Γ] (H : Subgroup Γ) :
    (Subgroup.center ↥H).map H.subtype = H ⊓ centralizer (H : Set Γ) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.2 ⟨z.2, mem_centralizer_iff.2 fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
    exact congrArg Subtype.val this
  · intro hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 hx
    refine ⟨⟨x, hxH⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.1 hxC y y.2)

theorem bar_centerMod (A : Subgroup G) :
    bar W (centerMod W A) = bar W A ⊓ centralizer ((bar W A : Subgroup (Bar W)) : Set (Bar W)) := by
  unfold centerMod upperCenterMod
  rw [bar_lift, Subgroup.upperCentralSeries_one, map_subtype_center]

theorem isPGroup_lift_of [Finite G] {Y : Subgroup (Bar W)} (hW : IsPGroup 2 W)
    (hY : IsPGroup 2 Y) : IsPGroup 2 (lift Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isPGroup_lift hW hY

theorem relIndex_eq_card_bar [Finite G] {X : Subgroup G} (hWX : W ≤ X)
    (hXN : X ≤ normalizer (W : Set G)) : W.relIndex X = Nat.card (bar W X) := by
  have h1 := Subgroup.relIndex_mul_card W X
  rw [inf_of_le_left hWX] at h1
  have h2 := card_bar_mul hWX hXN
  have hpos : 0 < Nat.card W := Nat.card_pos
  have : W.relIndex X * Nat.card W = Nat.card (bar W X) * Nat.card W := by
    rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem bar_zpowers {t : G} (htW : t ∈ normalizer (W : Set G)) :
    bar W (zpowers t) = zpowers (proj W ⟨t, htW⟩) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hn)
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine mem_bar_iff_exists.2 ⟨⟨t, htW⟩ ^ n, ?_, by rw [map_zpow]⟩
    simpa using Subgroup.zpow_mem_zpowers t n

theorem centralizer_zpowers_eq {Γ : Type*} [Group Γ] (a : Γ) :
    centralizer ((zpowers a : Subgroup Γ) : Set Γ) = centralizer ({a} : Set Γ) := by
  ext x
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx a (Subgroup.mem_zpowers a)
  · intro hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute a x := hx a rfl
    exact (hc.zpow_left n).eq

theorem centralizerMod_zpowers {t : G} (htW : t ∈ normalizer (W : Set G)) :
    centralizerMod W (zpowers t) = lift (centralizer ({proj W ⟨t, htW⟩} : Set (Bar W))) := by
  unfold centralizerMod
  rw [bar_zpowers htW, centralizer_zpowers_eq]

theorem bar_self (W : Subgroup G) : bar W W = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy
  rw [Subgroup.mem_bot, proj_eq_one_iff]
  exact hx

theorem eq_of_bar_eq {X Y : Subgroup G} (hWX : W ≤ X) (hXN : X ≤ normalizer (W : Set G))
    (hWY : W ≤ Y) (hYN : Y ≤ normalizer (W : Set G)) (h : bar W X = bar W Y) : X = Y := by
  rw [← lift_bar hWX hXN, ← lift_bar hWY hYN, h]

theorem le_of_bar_eq_bot {X : Subgroup G} (hXN : X ≤ normalizer (W : Set G))
    (h : bar W X = ⊥) : X ≤ W := by
  intro z hz
  have h1 : proj W ⟨z, hXN hz⟩ ∈ bar W X := proj_mem_bar hz
  rw [h, Subgroup.mem_bot, proj_eq_one_iff] at h1
  exact h1

theorem le_sup_of_bar_le {X Y : Subgroup G} (hXN : X ≤ normalizer (W : Set G))
    (h : bar W X ≤ bar W Y) : X ≤ Y ⊔ W := by
  intro z hz
  have h1 : proj W ⟨z, hXN hz⟩ ∈ bar W X := proj_mem_bar hz
  obtain ⟨y, hy, hyz⟩ := mem_bar_iff_exists.1 (h h1)
  have hw : (y : G)⁻¹ * z ∈ W := proj_eq_proj_iff.1 hyz
  have e : z = (y : G) * ((y : G)⁻¹ * z) := by group
  rw [e]
  exact mul_mem (mem_sup_left hy) (mem_sup_right hw)

theorem lift_bot : lift (⊥ : Subgroup (Bar W)) = W := by
  have h1 := lift_bar (A := W) (X := W) le_rfl le_normalizer
  rwa [bar_self] at h1

theorem lift_bar_eq_sup {X : Subgroup G} (hXN : X ≤ normalizer (W : Set G)) :
    lift (bar W X) = X ⊔ W := by
  have h1 := lift_bar (A := W) (X := X ⊔ W) le_sup_right (sup_le hXN le_normalizer)
  rwa [bar_sup hXN le_normalizer, bar_self, sup_bot_eq] at h1

theorem isQuotientIso_bar_of_inf {B X : Subgroup G} (hXN : X ≤ normalizer (W : Set G))
    (hinf : X ⊓ W = B) : IsQuotientIso X B ↥(bar W X) := by
  let φ : ↥X →* ↥(bar W X) :=
    ((proj W).comp (Subgroup.inclusion hXN)).codRestrict (bar W X) (fun x => proj_mem_bar x.2)
  refine ⟨φ, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  · ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hinf]
    constructor
    · intro h1
      have h2 : proj W ⟨x, hXN x.2⟩ = 1 := congrArg Subtype.val h1
      exact Subgroup.mem_inf.2 ⟨x.2, proj_eq_one_iff.1 h2⟩
    · intro h1
      exact Subtype.ext (proj_eq_one_iff.2 (Subgroup.mem_inf.1 h1).2)

theorem isQuotientIso_congr {X B : Subgroup G} {T T' : Type*} [Group T] [Group T']
    (h : IsQuotientIso X B T) (e : T ≃* T') : IsQuotientIso X B T' := by
  obtain ⟨φ, hφs, hφk⟩ := h
  refine ⟨e.toMonoidHom.comp φ, e.surjective.comp hφs, ?_⟩
  rw [← hφk]
  ext x
  simp

theorem centerMod_eq_lift (A : Subgroup G) :
    centerMod W A =
      lift (bar W A ⊓ centralizer ((bar W A : Subgroup (Bar W)) : Set (Bar W))) := by
  unfold centerMod upperCenterMod
  rw [Subgroup.upperCentralSeries_one, map_subtype_center]

end Hat

section GenericG

variable {G : Type*} [Group G]

theorem mem_of_mul_mem_prod {A A' E E' : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hinf : A ⊓ A' = ⊥) (hE : E ≤ A) (hE' : E' ≤ A')
    {k k' : G} (hk : k ∈ A) (hk' : k' ∈ A') (hw : k'⁻¹ * k ∈ E ⊔ E') : k ∈ E := by
  have hnorm : E ≤ normalizer (E' : Set G) := le_normalizer_of_commute hcomm hE hE'
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right E E' hnorm] at hw
  obtain ⟨e, he, e', he', hee⟩ := hw
  have hee' : e * e' = k'⁻¹ * k := hee
  have hek' : e * k' = k' * e := hcomm e (hE he) k' hk'
  have hk_eq : k = e * (k' * e') := by
    calc k = k' * (k'⁻¹ * k) := by group
      _ = k' * (e * e') := by rw [hee']
      _ = (k' * e) * e' := by group
      _ = (e * k') * e' := by rw [hek']
      _ = e * (k' * e') := by group
  have hmem : e⁻¹ * k ∈ A ⊓ A' := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hE he)) hk, ?_⟩
    have : e⁻¹ * k = k' * e' := by rw [hk_eq]; group
    rw [this]
    exact mul_mem hk' (hE' he')
  rw [hinf, Subgroup.mem_bot] at hmem
  have : k = e := by
    have := congrArg (e * ·) hmem
    simpa using this
  rw [this]
  exact he

theorem commutator_sup_le_of_comm {A A' M : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hA : A ≤ normalizer (M : Set G))
    (hA' : A' ≤ normalizer (M : Set G)) : ⁅A ⊔ M, A' ⊔ M⁆ ≤ M := by
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A M hA] at hg₁
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A' M hA'] at hg₂
  obtain ⟨k, hk, m, hm, rfl⟩ := hg₁
  obtain ⟨k', hk', m', hm', rfl⟩ := hg₂
  have hkk' : k * k' = k' * k := hcomm k hk k' hk'
  have hk'inv : k'⁻¹ ∈ normalizer (M : Set G) := inv_mem (hA' hk')
  have hkinv : k⁻¹ ∈ normalizer (M : Set G) := inv_mem (hA hk)
  have hmk' : k'⁻¹ * m * k' ∈ M := by
    have := (mem_normalizer_iff.1 hk'inv m).1 hm
    simpa [mul_assoc] using this
  have hmk : k⁻¹ * m' * k ∈ M := by
    have := (mem_normalizer_iff.1 hkinv m').1 hm'
    simpa [mul_assoc] using this
  have hP : k * k' ∈ normalizer (M : Set G) := mul_mem (hA hk) (hA' hk')
  have e1 : k * m * (k' * m') = (k * k') * ((k'⁻¹ * m * k') * m') := by group
  have e2 : k' * m' * (k * m) = (k * k') * ((k⁻¹ * m' * k) * m) := by
    calc k' * m' * (k * m) = (k' * k) * ((k⁻¹ * m' * k) * m) := by group
      _ = (k * k') * ((k⁻¹ * m' * k) * m) := by rw [hkk']
  have e3 : ⁅k * m, k' * m'⁆ = (k * k') * (((k'⁻¹ * m * k') * m') *
      ((k⁻¹ * m' * k) * m)⁻¹) * (k * k')⁻¹ := by
    calc ⁅k * m, k' * m'⁆ = (k * m * (k' * m')) * (k' * m' * (k * m))⁻¹ := by
          rw [commutatorElement_def]; group
      _ = ((k * k') * ((k'⁻¹ * m * k') * m')) * ((k * k') * ((k⁻¹ * m' * k) * m))⁻¹ := by
          rw [e1, e2]
      _ = _ := by group
  rw [e3]
  have hin : ((k'⁻¹ * m * k') * m') * ((k⁻¹ * m' * k) * m)⁻¹ ∈ M :=
    mul_mem (mul_mem hmk' hm') (inv_mem (mul_mem hmk hm))
  exact (mem_normalizer_iff.1 hP _).1 hin

theorem isQuotientIso_sup {A B : Subgroup G} {T : Type*} [Group T]
    (hAB : A ≤ normalizer (B : Set G)) (hiso : IsQuotientIso A (A ⊓ B) T) :
    IsQuotientIso (A ⊔ B) B T := by
  obtain ⟨φ, hφs, hφk⟩ := hiso
  have hKn : (A ⊔ B) ≤ normalizer (B : Set G) := sup_le hAB le_normalizer
  haveI hnB : (B.subgroupOf (A ⊔ B)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).2 hKn
  set ψ : ↥A →* ↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' (B.subgroupOf (A ⊔ B))).comp (Subgroup.inclusion le_sup_left) with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf (A ⊔ B)) y
    have hx' := hx
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A B hAB] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [hψ, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa using hb
  have hkerψ : ψ.ker = (A ⊓ B).subgroupOf A := by
    ext x
    simp only [hψ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf,
      Subgroup.coe_inclusion, Subgroup.mem_inf]
    exact ⟨fun hb => ⟨x.2, hb⟩, fun hb => hb.2⟩
  have hker : φ.ker = ψ.ker := by rw [hφk, hkerψ]
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  let e : T ≃* ↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B) :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
  · exact e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]

theorem sectionIso_of_isQuotientIso {A B A' B' : Subgroup G} {T : Type*} [Group T]
    (h : IsQuotientIso A B T) (h' : IsQuotientIso A' B' T) : SectionIso A B A' B' := by
  obtain ⟨φ, hφs, hφk⟩ := h
  obtain ⟨φ', hφ's, hφ'k⟩ := h'
  have n1 : (B.subgroupOf A).Normal := hφk ▸ MonoidHom.normal_ker φ
  have n2 : (B'.subgroupOf A').Normal := hφ'k ▸ MonoidHom.normal_ker φ'
  refine ⟨n1, n2, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)).trans
    (((QuotientGroup.quotientMulEquivOfEq hφ'k.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's)).symm)

theorem eq_or_eq_of_quotient_simple {X B C : Subgroup G} {T : Type*} [Group T] [IsSimpleGroup T]
    (hiso : IsQuotientIso X B T) (hBC : B ≤ C) (hCX : C ≤ X)
    (hCn : X ≤ normalizer (C : Set G)) : C = B ∨ C = X := by
  obtain ⟨φ, hφs, hφk⟩ := hiso
  haveI hC' : (C.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hCX).2 hCn
  haveI hmapN : ((C.subgroupOf X).map φ).Normal := hC'.map φ hφs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C.subgroupOf X).map φ) with hb | ht
  · left
    refine le_antisymm ?_ hBC
    intro c hc
    have hcX : c ∈ X := hCX hc
    have h1 : φ ⟨c, hcX⟩ ∈ (C.subgroupOf X).map φ := ⟨⟨c, hcX⟩, mem_subgroupOf.2 hc, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    have h2 : (⟨c, hcX⟩ : X) ∈ φ.ker := h1
    rw [hφk, mem_subgroupOf] at h2
    exact h2
  · right
    refine le_antisymm hCX ?_
    intro x hx
    have h1 : φ ⟨x, hx⟩ ∈ (C.subgroupOf X).map φ := by rw [ht]; exact mem_top _
    obtain ⟨c, hc, hcx⟩ := h1
    have h2 : c⁻¹ * ⟨x, hx⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
    rw [hφk, mem_subgroupOf] at h2
    have h3 : (c : G) ∈ C := mem_subgroupOf.1 hc
    have h4 : (c : G) * ((c : G)⁻¹ * x) = x := by group
    rw [← h4]
    exact mul_mem h3 (hBC h2)

theorem le_oTwoPrimeRes_of_isPGroup {S X : Subgroup G} (hSX : S ≤ X) (hS : IsPGroup 2 S) :
    S ≤ oTwoPrimeRes X := by
  intro s hs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hk' : s ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact Subgroup.subset_closure ⟨hSX hs, k, hk'⟩

theorem oTwoPrimeRes_le (X : Subgroup G) : oTwoPrimeRes X ≤ X :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem conjT_eq_self_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : Xᵍ[g] = X :=
  mem_normalizer_iff_map_conj_eq.1 (inv_mem hg)

theorem conjT_eq_of_le {X : Subgroup G} {t : G} (ht : t * t = 1) (hle : Xᵍ[t] ≤ X) :
    Xᵍ[t] = X := by
  refine le_antisymm hle ?_
  have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hle
  rwa [map_conj_inv_map_conj_inv ht] at this

theorem map_conj_le_normalizer {W X : Subgroup G} {g : G} (hg : g ∈ normalizer (W : Set G))
    (hX : X ≤ normalizer (W : Set G)) :
    X.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hg (hX hx)) (inv_mem hg)

theorem h1Zero_of_sec_bot {Γ : Type*} [Group Γ] {τ : Γ} {N : Subgroup Γ} (h : H1ZeroSec τ N ⊥) :
    H1Zero τ N := by
  intro n hn hcoc
  obtain ⟨m, hm, hmn⟩ := h n hn (by rw [hcoc]; exact one_mem _)
  refine ⟨m, hm, ?_⟩
  rw [Subgroup.mem_bot] at hmn
  have : n = m⁻¹ * (τ * m * τ⁻¹) := by
    have := congrArg (fun x => m⁻¹ * x * (τ * m * τ⁻¹)) hmn
    simpa [mul_assoc] using this
  exact this

theorem isElemSection_le_normalizer {Γ : Type*} [Group Γ] [Finite Γ] {A B : Subgroup Γ}
    (h : IsElemSection A B) : A ≤ normalizer (B : Set Γ) := fun x hx =>
  mem_normalizer_fintype fun n hn => by
    have := mul_mem (h.commutator_mem x hx n (h.le hn)) hn
    simpa [mul_assoc] using this

theorem mem_normalizer_oTwoPrimeRes {X : Subgroup G} [Finite G] {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer ((oTwoPrimeRes X : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun n hn => ?_
  have hle : oTwoPrimeRes X ≤ (oTwoPrimeRes X).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    obtain ⟨hsX, k, hk⟩ := hs
    refine Subgroup.subset_closure ⟨?_, k, ?_⟩
    · exact (mem_normalizer_iff.1 hg s).1 hsX
    · show (g * s * g⁻¹) ^ (2 ^ k) = 1
      rw [conj_pow, hk]
      group
  exact hle hn

theorem mem_normalizer_normalizer [Finite G] {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((normalizer (X : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_fintype fun n hn => mul_mem (mul_mem hg hn) (inv_mem hg)

theorem map_conj_map_conj_comm {g t : G} (hgt : g * t = t * g) (X : Subgroup G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom =
      (X.map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact (conj_conj_comm hgt x).symm

theorem mem_normalizer_sup_center [Finite G] {K K' : Subgroup G} {x : G}
    (hx : (K.map (MulAut.conj x).toMonoidHom = K ∧ K'.map (MulAut.conj x).toMonoidHom = K') ∨
      (K.map (MulAut.conj x).toMonoidHom = K' ∧ K'.map (MulAut.conj x).toMonoidHom = K)) :
    x ∈ normalizer ((((K ⊓ centralizer (K : Set G)) ⊔ (K' ⊓ centralizer (K' : Set G)) :
      Subgroup G)) : Set G) := by
  refine mem_normalizer_iff_map_conj_eq.2 ?_
  show Subgroup.map (MulAut.conj x).toMonoidHom _ = _
  rw [Subgroup.map_sup, map_inf_centralizer_aux, map_inf_centralizer_aux]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

end GenericG

section Context

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem isPGroup_of_isSylowOf {P K : Subgroup G} (h : IsSylowOf 2 P K) : IsPGroup 2 P := by
  obtain ⟨Q, hQ⟩ := h
  have := Q.isPGroup'.map K.subtype
  rwa [hQ] at this

theorem t_mem_normalizer_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ normalizer (yamadaM₆ d t : Set G) := by
  have htL₆ : t ∈ yamadaL₆ d t := by
    rw [(h.yamada_5_29_1_of_layerHyp d hlay).1]
    exact mem_sup_right (mem_zpowers t)
  exact mem_normalizer_inf_D4 (le_normalizer htL₆)
    (Setup.mem_normalizer_centralizer_C8 (h.t_mem_normalizer_yamadaY₂ d))

theorem isPGroup_M₆ (d : TrialityD4Data L (2 ^ f)) : IsPGroup 2 (yamadaM₆ d t) :=
  (isPGroup_yamadaL₆ d t).to_le inf_le_left

theorem not_P_le_centralizer_Y₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : ¬ yamadaP d t ≤ centralizer (yamadaY₂ d t : Set G) := by
  intro hle
  have hx₂ : L.subtype (d.x₂ 1) ∈ yamadaP d t :=
    h.S_map_le_yamadaP d hlay ⟨d.x₂ 1, d.U₂_le_S (d.x₂_mem_U₂ 1), rfl⟩
  have hx₅ : L.subtype (d.x₅ 1) ∈ yamadaY₂ d t :=
    h.Y_map_le_yamadaY₂ d hlay ⟨d.x₅ 1, d.x₅_mem_Y 1, rfl⟩
  have hc := mem_centralizer_iff.1 (hle hx₂) _ hx₅
  have hcL : d.x₅ 1 * d.x₂ 1 = d.x₂ 1 * d.x₅ 1 := Subtype.ext hc
  have h1 : ⁅d.x₂ 1, d.x₅ 1⁆ = 1 := by
    rw [commutatorElement_def, ← hcL]
    group
  rw [d.comm₂₅] at h1
  have h2 : d.x₆ (1 * 1) = d.x₆ 0 := by rw [h1, d.x₆_zero]
  have h3 := d.x₆_injective h2
  have h4 : (1 : d.Γ₀) = 0 := by simpa using h3
  exact one_ne_zero h4

theorem normalizer_P_le_normalizer_of_series {P X : Subgroup G} {n : ℕ}
    (hX : (Subgroup.upperCentralSeries ↥P n).map P.subtype = X) :
    normalizer (P : Set G) ≤ normalizer (X : Set G) := by
  rw [← hX]
  exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem t_mem_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ normalizer (yamadaW₃ d t : Set G) :=
  normalizer_P_le_normalizer_of_series (S5_upperCentralSeries_P h d hlay).2.2.1
    (h.t_mem_normalizer_yamadaP d hlay)

theorem W₃_le_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaW₃ d t ≤ yamadaM₆ d t :=
  (h.yamadaW₃_le_yamadaF₄_R5 d hlay).trans (h.yamadaF₄_le_yamadaM₆_PA d hlay)

theorem prodX_le_P (d : TrialityD4Data L (2 ^ f)) : prodX d t ≤ yamadaP d t :=
  inf_le_left.trans (yamadaD₅_le_yamadaP d t)

theorem nThree_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nThree d t ≤ normalizer (yamadaW₃ d t : Set G) := by
  obtain ⟨-, ⟨hNX, -⟩, -⟩ := A3_structure h d hp hK
  have hv : vG d ∈ normalizer (yamadaW₃ d t : Set G) := h.v_mem_normalizer_yamadaW₃ d
  have hXW : prodX d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (prodX_le_P d).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)
  rw [hNX]
  refine sup_le hXW ?_
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hv (hXW hx)) (inv_mem hv)

theorem nTwo_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nTwo d t ≤ normalizer (yamadaW₃ d t : Set G) :=
  sup_le (nThree_le_normalizer_W₃ h d hp hK)
    ((yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer))

theorem nTwo_le_normalizer_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nTwo d t ≤ normalizer (yamadaM₆ d t : Set G) := by
  obtain ⟨-, ⟨-, -, hN3M, -⟩, -⟩ := A3_structure h d hp hK
  exact sup_le hN3M le_normalizer

theorem P_le_nTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaP d t ≤ nTwo d t := by
  obtain ⟨-, ⟨hNX, -⟩, ⟨-, -, hPeq, -⟩⟩ := A3_structure h d hp hK
  have hXN : prodX d t ≤ nThree d t := by rw [hNX]; exact le_sup_left
  rw [hPeq]
  exact sup_le le_sup_right (hXN.trans le_sup_left)

theorem nThree_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (nThree d t)ᵍ[t] = nThree d t := by
  obtain ⟨⟨-, -, -, -, hN3, -⟩, -⟩ := A3_structure h d hp hK
  rw [hN3, Subgroup.map_sup, map_conj_inv_map_conj_inv h.t_mul_t, sup_comm]

theorem nTwo_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (nTwo d t)ᵍ[t] = nTwo d t := by
  show (nThree d t ⊔ yamadaM₆ d t)ᵍ[t] = _
  rw [Subgroup.map_sup, nThree_conj_eq h d hp hK,
    conjT_eq_self_of_mem_normalizer (t_mem_normalizer_M₆ h d hp.layer)]
  rfl

theorem not_P_le_centralizerMod (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) :
    ¬ yamadaP d t ≤ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) := by
  intro hPc
  have hlay := hp.layer
  obtain ⟨hS1, hS2, hS3, hS4⟩ := S5_upperCentralSeries_P h d hlay
  obtain ⟨-, -, -, -, -, -, -, hD, hM, hP, -⟩ := T4_series_free h d hp
  have hmemZ3 : ∀ x : ↥(yamadaP d t), (x : G) ∈ yamadaW₃ d t →
      x ∈ Subgroup.upperCentralSeries ↥(yamadaP d t) 3 := by
    intro x hx
    rw [← hS3] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := Subtype.ext hzx
    rwa [this] at hz
  have hMF : yamadaM₆ d t ≤ yamadaF₄ d t := by
    intro m hm
    rw [← hS4]
    have hmP : m ∈ yamadaP d t := yamadaM₆_le_yamadaP d t hm
    refine ⟨⟨m, hmP⟩, ?_, rfl⟩
    change (⟨m, hmP⟩ : ↥(yamadaP d t)) ∈ Subgroup.upperCentralSeries ↥(yamadaP d t) (3 + 1)
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    have hmN : m ∈ normalizer (yamadaW₃ d t : Set G) :=
      h.yamadaP_le_normalizer_yamadaW₃_PA d hlay hmP
    have h3 : (y : G) * m * (y : G)⁻¹ * m⁻¹ ∈ yamadaW₃ d t :=
      (mem_centralizerMod_iff.1 (hPc y.2)).2 m hm hmN
    apply hmemZ3
    have e : m * (y : G) * m⁻¹ * (y : G)⁻¹ = ((y : G) * m * (y : G)⁻¹ * m⁻¹)⁻¹ := by group
    show m * (y : G) * m⁻¹ * (y : G)⁻¹ ∈ yamadaW₃ d t
    rw [e]
    exact inv_mem h3
  have hPD : yamadaP d t = yamadaD₅ d t :=
    sup_eq_left.2 (hMF.trans (Setup.yamadaF₄_le_yamadaD₅_PA (t := t) d))
  have hcard : (2 ^ f) ^ 24 = (2 ^ f) ^ 18 := by
    rw [← hP, ← hD, hPD]
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by have := hp.two_le; omega)
  have := Nat.pow_right_injective h2f hcard
  omega

end Context

section Fields

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}

theorem four_le_card_Γ₀ (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) : 4 ≤ Nat.card d.Γ₀ := by
  rw [d.card_Γ₀]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem isSimpleGroup_SL (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) :
    IsSimpleGroup SL(2, d.Γ₀) :=
  sl2_isSimpleGroup_of_charTwo (four_le_card_Γ₀ d hf)

end Fields

section B1Abs

variable {G : Type*} [Group G] [Finite G]

theorem inf_centralizer_eq_or {A E₁ : Subgroup G} {T : Type*} [Group T] [IsSimpleGroup T]
    (hq : IsQuotientIso A E₁ T) (hEA : E₁ ≤ A) (hAN : A ≤ normalizer (E₁ : Set G))
    (hcomm : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x) :
    A ⊓ centralizer (E₁ : Set G) = E₁ ∨ A ≤ centralizer (E₁ : Set G) := by
  have hE₁C : E₁ ≤ A ⊓ centralizer (E₁ : Set G) :=
    le_inf hEA (fun x hx => mem_centralizer_iff.2 fun y hy => hcomm y hy x hx)
  have hnorm : A ≤ normalizer ((A ⊓ centralizer (E₁ : Set G) : Subgroup G) : Set G) := by
    intro a ha
    refine mem_normalizer_fintype fun c hc => ?_
    obtain ⟨hcA, hcC⟩ := Subgroup.mem_inf.1 hc
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ha hcA) (inv_mem ha), mem_centralizer_iff.2 ?_⟩
    intro e he
    have haN : a ∈ normalizer (E₁ : Set G) := hAN ha
    have he' : a⁻¹ * e * a ∈ E₁ := by
      have := (mem_normalizer_iff.1 (inv_mem haN) e).1 he
      simpa using this
    have h1 := mem_centralizer_iff.1 hcC _ he'
    calc e * (a * c * a⁻¹) = a * ((a⁻¹ * e * a) * c) * a⁻¹ := by group
      _ = a * (c * (a⁻¹ * e * a)) * a⁻¹ := by rw [h1]
      _ = a * c * a⁻¹ * e := by group
  rcases eq_or_eq_of_quotient_simple hq hE₁C inf_le_left hnorm with h | h
  · exact Or.inl h
  · exact Or.inr (h ▸ inf_le_right)

theorem sup_le_centralizer_of_le {A E₁ : Subgroup G} {t : G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ Aᵍ[t], a * b = b * a) (hEA : E₁ ≤ A)
    (hAC : A ≤ centralizer (E₁ : Set G)) :
    A ⊔ Aᵍ[t] ≤ centralizer ((E₁ ⊔ E₁ᵍ[t] : Subgroup G) : Set G) := by
  have hA'C : Aᵍ[t] ≤ centralizer ((E₁ᵍ[t] : Subgroup G) : Set G) := by
    have := map_inf_centralizer_aux (MulAut.conj t⁻¹) A E₁
    have hAeq : A ⊓ centralizer (E₁ : Set G) = A := inf_eq_left.2 hAC
    rw [hAeq] at this
    have h2 : Aᵍ[t] ≤ Aᵍ[t] ⊓ centralizer ((E₁ᵍ[t] : Subgroup G) : Set G) := by
      rw [← this]
    exact h2.trans inf_le_right
  have hA'C₁ : Aᵍ[t] ≤ centralizer (E₁ : Set G) := fun b hb =>
    mem_centralizer_iff.2 fun e he => (hcomm e (hEA he) b hb)
  have hAC' : A ≤ centralizer ((E₁ᵍ[t] : Subgroup G) : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun e he => (hcomm a ha e (Subgroup.map_mono hEA he)).symm
  rw [centralizer_sup_aux]
  exact sup_le (le_inf hAC hAC') (le_inf hA'C₁ hA'C)

theorem inf_centralizer_le {K A E₁ Q₃ : Subgroup G} {t : G}
    (hKc : ∀ a ∈ K, ∀ b ∈ Kᵍ[t], a * b = b * a) (hQc : ∀ a ∈ Q₃, ∀ b ∈ Q₃ᵍ[t], a * b = b * a)
    (hE₁K : E₁ ≤ K) (hEQ : E₁ ≤ Q₃) (hQ₃K : Q₃ ≤ K) (hQ₃A : Q₃ ≤ A)
    (hcen : A ⊓ centralizer (E₁ : Set G) = E₁)
    {a b : G} (ha : a ∈ Q₃) (hb : b ∈ Q₃ᵍ[t])
    (hab : a * b ∈ centralizer ((E₁ ⊔ E₁ᵍ[t] : Subgroup G) : Set G)) :
    a * b ∈ E₁ ⊔ E₁ᵍ[t] := by
  have hbK : b ∈ Kᵍ[t] := Subgroup.map_mono hQ₃K hb
  have haE : a ∈ E₁ := by
    have hC : a ∈ centralizer (E₁ : Set G) := by
      refine mem_centralizer_iff.2 fun e he => ?_
      have h1 : (a * b) * e = e * (a * b) :=
        (mem_centralizer_iff.1 hab e (mem_sup_left he)).symm
      have h2 : b * e = e * b := (hKc e (hE₁K he) b hbK).symm
      have h3 : e * a = a * e := by
        have : (e * a) * b = (a * e) * b := by
          calc (e * a) * b = e * (a * b) := by group
            _ = (a * b) * e := h1.symm
            _ = a * (b * e) := by group
            _ = a * (e * b) := by rw [h2]
            _ = (a * e) * b := by group
        exact mul_right_cancel this
      exact h3
    rw [← hcen]
    exact Subgroup.mem_inf.2 ⟨hQ₃A ha, hC⟩
  have hbE : b ∈ E₁ᵍ[t] := by
    obtain ⟨a', ha', rfl⟩ := hb
    have hC : a' ∈ centralizer (E₁ : Set G) := by
      refine mem_centralizer_iff.2 fun e he => ?_
      have hyK : t⁻¹ * e * t ∈ Kᵍ[t] := conj_mem_map_conj_inv t (hE₁K he)
      have h1 : (a * (MulAut.conj t⁻¹) a') * (t⁻¹ * e * t) =
          (t⁻¹ * e * t) * (a * (MulAut.conj t⁻¹) a') :=
        (mem_centralizer_iff.1 hab _ (mem_sup_right (conj_mem_map_conj_inv t he))).symm
      have h2 : a * (t⁻¹ * e * t) = (t⁻¹ * e * t) * a := hKc a (hQ₃K ha) _ hyK
      have h3 : (MulAut.conj t⁻¹) a' * (t⁻¹ * e * t) = (t⁻¹ * e * t) * (MulAut.conj t⁻¹) a' := by
        have : a * ((MulAut.conj t⁻¹) a' * (t⁻¹ * e * t)) =
            a * ((t⁻¹ * e * t) * (MulAut.conj t⁻¹) a') := by
          calc a * ((MulAut.conj t⁻¹) a' * (t⁻¹ * e * t))
              = (a * (MulAut.conj t⁻¹) a') * (t⁻¹ * e * t) := by group
            _ = (t⁻¹ * e * t) * (a * (MulAut.conj t⁻¹) a') := h1
            _ = ((t⁻¹ * e * t) * a) * (MulAut.conj t⁻¹) a' := by group
            _ = (a * (t⁻¹ * e * t)) * (MulAut.conj t⁻¹) a' := by rw [h2]
            _ = a * ((t⁻¹ * e * t) * (MulAut.conj t⁻¹) a') := by group
        exact mul_left_cancel this
      simp only [MulAut.conj_apply, inv_inv] at h3
      have h4 : (t⁻¹ * a' * t) * (t⁻¹ * e * t) = (t⁻¹ * e * t) * (t⁻¹ * a' * t) := by
        simpa [mul_assoc] using h3
      have h5 : t * ((t⁻¹ * a' * t) * (t⁻¹ * e * t)) * t⁻¹ =
          t * ((t⁻¹ * e * t) * (t⁻¹ * a' * t)) * t⁻¹ := by rw [h4]
      have h6 : a' * e = e * a' := by
        calc a' * e = t * ((t⁻¹ * a' * t) * (t⁻¹ * e * t)) * t⁻¹ := by group
          _ = t * ((t⁻¹ * e * t) * (t⁻¹ * a' * t)) * t⁻¹ := h5
          _ = e * a' := by group
      exact h6.symm
    have ha'E : a' ∈ E₁ := by
      rw [← hcen]
      exact Subgroup.mem_inf.2 ⟨hQ₃A ha', hC⟩
    exact ⟨a', ha'E, rfl⟩
  exact mul_mem (mem_sup_left haE) (mem_sup_right hbE)

theorem B1_abstract {T : Type*} [Group T] [IsSimpleGroup T] {t : G}
    {K A E₁ Y₂ M P X N₃ Q₃ : Subgroup G}
    (hMt : t ∈ normalizer (M : Set G))
    (hKc : ∀ a ∈ K, ∀ b ∈ Kᵍ[t], a * b = b * a)
    (hA : A = oTwoPrimeRes (K ⊓ normalizer (E₁ : Set G)))
    (hq3 : IsQuotientIso A E₁ T) (hAinf : A ⊓ Aᵍ[t] = ⊥) (hAcomm : ⁅A, Aᵍ[t]⁆ = ⊥)
    (hN3 : N₃ = A ⊔ Aᵍ[t]) (hEK : E₁ ≤ A) (hE₁K : E₁ ≤ K)
    (hE₁abel : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x) (hYE : Y₂ = E₁ ⊔ E₁ᵍ[t])
    (hEQ : E₁ ≤ Q₃) (hEn : Q₃ ≤ normalizer (E₁ : Set G)) (hQ₃K : Q₃ ≤ K) (hQ2 : IsPGroup 2 Q₃)
    (hXQ : X = Q₃ ⊔ Q₃ᵍ[t]) (hQcomm : ⁅Q₃, Q₃ᵍ[t]⁆ = ⊥) (hNX : X ≤ N₃)
    (hN3M : N₃ ≤ normalizer (M : Set G)) (hN3M6 : N₃ ⊓ M = Y₂) (hPeq : P = M ⊔ X)
    (hMC : M ≤ centralizer (Y₂ : Set G)) (hXM : X ≤ normalizer (M : Set G))
    (hS : ¬ P ≤ centralizer (Y₂ : Set G)) :
    (N₃ ⊔ M = (A ⊔ M) ⊔ (A ⊔ M)ᵍ[t] ∧ (A ⊔ M) ⊓ (A ⊔ M)ᵍ[t] = M ∧
      ⁅A ⊔ M, (A ⊔ M)ᵍ[t]⁆ ≤ M ∧ IsQuotientIso (A ⊔ M) M T ∧
      SectionIso (A ⊔ M) M A E₁) ∧ P ⊓ centralizer (Y₂ : Set G) = M := by
  have hMt' : Mᵍ[t] = M := conjT_eq_self_of_mem_normalizer hMt
  have hAN₃ : A ≤ N₃ := hN3 ▸ le_sup_left
  have hA'N₃ : Aᵍ[t] ≤ N₃ := hN3 ▸ le_sup_right
  have hAM : A ≤ normalizer (M : Set G) := hAN₃.trans hN3M
  have hA'M : Aᵍ[t] ≤ normalizer (M : Set G) := hA'N₃.trans hN3M
  have hAcomm' : ∀ a ∈ A, ∀ b ∈ Aᵍ[t], a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hAcomm ha) b hb).symm
  have hQc : ∀ a ∈ Q₃, ∀ b ∈ Q₃ᵍ[t], a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hQcomm ha) b hb).symm
  have hY₂M : Y₂ ≤ M := hN3M6 ▸ inf_le_right
  have hE₁Y : E₁ ≤ Y₂ := by rw [hYE]; exact le_sup_left
  have hE₁A' : E₁ᵍ[t] ≤ Aᵍ[t] := Subgroup.map_mono hEK
  have hAKN : A ≤ K ⊓ normalizer (E₁ : Set G) := by rw [hA]; exact oTwoPrimeRes_le _
  have hAY : ∀ x ∈ A, x ∈ Y₂ → x ∈ E₁ := by
    intro x hx hxY
    refine mem_of_mul_mem_prod hAcomm' hAinf hEK hE₁A' hx (one_mem _) ?_
    rw [inv_one, one_mul, ← hYE]
    exact hxY
  have hAM_eq : A ⊓ M = E₁ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxA, hxM⟩ := Subgroup.mem_inf.1 hx
      refine hAY x hxA ?_
      rw [← hN3M6]
      exact Subgroup.mem_inf.2 ⟨hAN₃ hxA, hxM⟩
    · exact le_inf hEK (hE₁Y.trans hY₂M)
  have hK₂t : (A ⊔ M)ᵍ[t] = Aᵍ[t] ⊔ M := by
    rw [Subgroup.map_sup, hMt']
  have hq3' : IsQuotientIso A (A ⊓ M) T := by rw [hAM_eq]; exact hq3
  have hiso : IsQuotientIso (A ⊔ M) M T := isQuotientIso_sup hAM hq3'
  have part1 : N₃ ⊔ M = (A ⊔ M) ⊔ (A ⊔ M)ᵍ[t] ∧ (A ⊔ M) ⊓ (A ⊔ M)ᵍ[t] = M ∧
      ⁅A ⊔ M, (A ⊔ M)ᵍ[t]⁆ ≤ M ∧ IsQuotientIso (A ⊔ M) M T ∧ SectionIso (A ⊔ M) M A E₁ := by
    refine ⟨?_, ?_, ?_, hiso, sectionIso_of_isQuotientIso hiso hq3⟩
    · rw [hK₂t, hN3, sup_sup_sup_comm, sup_idem]
    · apply le_antisymm
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
        rw [hK₂t] at hx2
        rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A M hAM] at hx1
        rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (Aᵍ[t]) M hA'M] at hx2
        obtain ⟨k, hk, m, hm, rfl⟩ := hx1
        obtain ⟨k', hk', m', hm', hxx⟩ := hx2
        have hxx' : k' * m' = k * m := hxx
        have hkk' : k'⁻¹ * k = m' * m⁻¹ := by
          calc k'⁻¹ * k = k'⁻¹ * (k * m) * m⁻¹ := by group
            _ = k'⁻¹ * (k' * m') * m⁻¹ := by rw [hxx']
            _ = m' * m⁻¹ := by group
        have hwY : k'⁻¹ * k ∈ Y₂ := by
          rw [← hN3M6]
          refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hA'N₃ hk')) (hAN₃ hk), ?_⟩
          rw [hkk']
          exact mul_mem hm' (inv_mem hm)
        have hw : k'⁻¹ * k ∈ E₁ ⊔ E₁ᵍ[t] := by rw [← hYE]; exact hwY
        have hkE : k ∈ E₁ := mem_of_mul_mem_prod hAcomm' hAinf hEK hE₁A' hk hk' hw
        show k * m ∈ M
        exact mul_mem (hY₂M (hE₁Y hkE)) hm
      · exact le_inf le_sup_right (hK₂t ▸ le_sup_right)
    · rw [hK₂t]
      exact commutator_sup_le_of_comm hAcomm' hAM hA'M
  refine ⟨part1, ?_⟩
  have hQ₃A : Q₃ ≤ A := by
    rw [hA]
    exact le_oTwoPrimeRes_of_isPGroup (le_inf hQ₃K hEn) hQ2
  have hcen : A ⊓ centralizer (E₁ : Set G) = E₁ := by
    rcases inf_centralizer_eq_or hq3 hEK (hAKN.trans inf_le_right) hE₁abel with hh | hh
    · exact hh
    · exfalso
      have hN₃C : N₃ ≤ centralizer ((Y₂ : Subgroup G) : Set G) := by
        rw [hYE, hN3]
        exact sup_le_centralizer_of_le hAcomm' hEK hh
      have hPC : P ≤ centralizer ((Y₂ : Subgroup G) : Set G) := by
        rw [hPeq]
        exact sup_le hMC (hNX.trans hN₃C)
      exact hS hPC
  have hXC : ∀ x ∈ X, x ∈ centralizer ((Y₂ : Subgroup G) : Set G) → x ∈ Y₂ := by
    intro x hx hxC
    have hnormQ : Q₃ ≤ normalizer ((Q₃ᵍ[t] : Subgroup G) : Set G) :=
      le_normalizer_of_commute hQc le_rfl le_rfl
    rw [hXQ, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Q₃ _ hnormQ] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [hYE] at hxC ⊢
    exact inf_centralizer_le hKc hQc hE₁K hEQ hQ₃K hQ₃A hcen ha hb hxC
  apply le_antisymm
  · intro z hz
    obtain ⟨hzP, hzC⟩ := Subgroup.mem_inf.1 hz
    have hXP : X ≤ P := hPeq ▸ le_sup_right
    rw [hPeq, sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right X M hXM] at hzP
    obtain ⟨x, hx, m, hm, rfl⟩ := hzP
    have hxC : x ∈ centralizer ((Y₂ : Subgroup G) : Set G) := by
      have h1 : x = (x * m) * m⁻¹ := by group
      rw [h1]
      exact mul_mem hzC (inv_mem (hMC hm))
    exact mul_mem (hY₂M (hXC x hx hxC)) hm
  · exact le_inf (hPeq ▸ le_sup_left) hMC

theorem characteristic_subgroupOf_of_inf_centralizer {P Y M : Subgroup G} {Z : Subgroup ↥P}
    [Z.Characteristic] (hZ : Z.map P.subtype = Y) (hM : P ⊓ centralizer (Y : Set G) = M) :
    (M.subgroupOf P).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_le]
  intro φ x hx
  have hφx : ((φ x : ↥P) : G) ∈ M := hx
  rw [← hM] at hφx
  obtain ⟨-, hφC⟩ := Subgroup.mem_inf.1 hφx
  show (x : G) ∈ M
  rw [← hM]
  refine Subgroup.mem_inf.2 ⟨x.2, mem_centralizer_iff.2 fun y hy => ?_⟩
  rw [← hZ] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hφz : φ z ∈ Z := by
    have := Subgroup.characteristic_iff_map_eq.1 ‹Z.Characteristic› φ
    rw [← this]
    exact ⟨z, hz, rfl⟩
  have hφzY : ((φ z : ↥P) : G) ∈ Y := by
    rw [← hZ]
    exact ⟨φ z, hφz, rfl⟩
  have h1 := mem_centralizer_iff.1 hφC ((φ z : ↥P) : G) hφzY
  have h2 : φ z * φ x = φ x * φ z := Subtype.ext h1
  have h3 : z * x = x * z := φ.injective (by rw [map_mul, map_mul]; exact h2)
  exact congrArg Subtype.val h3

theorem center_SL_trivial {k : Type*} [Field k] [CharP k 2]
    (x : SL(2, k)) (hx : ∀ y : SL(2, k), x * y = y * x) : x = 1 := by
  have hA : x ∈ Subgroup.center SL(2, k) := Subgroup.mem_center_iff.2 fun y => (hx y).symm
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

theorem mem_of_commutator_mem_of_quotient {X M : Subgroup G} {T : Type*} [Group T]
    (hiso : IsQuotientIso X M T) (hcen : ∀ x : T, (∀ y, x * y = y * x) → x = 1) {k : G}
    (hk : k ∈ X) (h : ∀ a ∈ X, k * a * k⁻¹ * a⁻¹ ∈ M) : k ∈ M := by
  obtain ⟨φ, hφs, hφk⟩ := hiso
  have h1 : φ ⟨k, hk⟩ = 1 := by
    apply hcen
    intro y
    obtain ⟨a, rfl⟩ := hφs y
    have h2 : (⟨k * a * k⁻¹ * a⁻¹, mul_mem (mul_mem (mul_mem hk a.2) (inv_mem hk)) (inv_mem a.2)⟩ :
        X) ∈ φ.ker := by
      rw [hφk, mem_subgroupOf]
      exact h a a.2
    rw [MonoidHom.mem_ker] at h2
    have h3 : φ ⟨k, hk⟩ * φ a * (φ ⟨k, hk⟩)⁻¹ * (φ a)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h2
    calc φ ⟨k, hk⟩ * φ a = (φ ⟨k, hk⟩ * φ a * (φ ⟨k, hk⟩)⁻¹ * (φ a)⁻¹) * (φ a * φ ⟨k, hk⟩) := by
          group
      _ = φ a * φ ⟨k, hk⟩ := by rw [h3, one_mul]
  have h2 : (⟨k, hk⟩ : X) ∈ φ.ker := h1
  rw [hφk, mem_subgroupOf] at h2
  exact h2

theorem conj_mem_centralizerMod {W B : Subgroup G} {g x : G}
    (hgW : g ∈ normalizer (W : Set G)) (hgB : g ∈ normalizer (B : Set G))
    (hx : x ∈ centralizerMod W B) : g * x * g⁻¹ ∈ centralizerMod W B := by
  rw [mem_centralizerMod_iff] at hx ⊢
  obtain ⟨hxW, hxc⟩ := hx
  refine ⟨mul_mem (mul_mem hgW hxW) (inv_mem hgW), fun b hb hbW => ?_⟩
  have hb' : g⁻¹ * b * g ∈ B := by
    have := (mem_normalizer_iff.1 (inv_mem hgB) b).1 hb
    simpa using this
  have hb'W : g⁻¹ * b * g ∈ normalizer (W : Set G) :=
    mul_mem (mul_mem (inv_mem hgW) hbW) hgW
  have h1 := hxc _ hb' hb'W
  have h2 := (mem_normalizer_iff.1 hgW _).1 h1
  have e : g * (x * (g⁻¹ * b * g) * x⁻¹ * (g⁻¹ * b * g)⁻¹) * g⁻¹ =
      g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹ * b⁻¹ := by group
  rw [e] at h2
  simpa [mul_assoc] using h2

theorem prod_facts {t : G} {K₂ M N : Subgroup G} (hMK : M ≤ K₂) (hN : N = K₂ ⊔ K₂ᵍ[t])
    (hcomm : ⁅K₂, K₂ᵍ[t]⁆ ≤ M) (hMt : Mᵍ[t] = M) :
    (∀ k ∈ K₂, ∀ y ∈ K₂ᵍ[t], k * y * k⁻¹ * y⁻¹ ∈ M) ∧
      (∀ k ∈ K₂, ∀ y ∈ K₂ᵍ[t], y * k * y⁻¹ * k⁻¹ ∈ M) ∧ N ≤ normalizer (K₂ : Set G) ∧
      K₂ ≤ normalizer (K₂ᵍ[t] : Set G) ∧ M ≤ K₂ᵍ[t] := by
  have hMK' : M ≤ K₂ᵍ[t] := by
    rw [← hMt]
    exact Subgroup.map_mono hMK
  have hc1 : ∀ k ∈ K₂, ∀ y ∈ K₂ᵍ[t], k * y * k⁻¹ * y⁻¹ ∈ M := fun k hk y hy =>
    hcomm (Subgroup.commutator_mem_commutator hk hy)
  have hc2 : ∀ k ∈ K₂, ∀ y ∈ K₂ᵍ[t], y * k * y⁻¹ * k⁻¹ ∈ M := by
    intro k hk y hy
    have := inv_mem (hc1 k hk y hy)
    have e : (k * y * k⁻¹ * y⁻¹)⁻¹ = y * k * y⁻¹ * k⁻¹ := by group
    rwa [e] at this
  refine ⟨hc1, hc2, ?_, ?_, hMK'⟩
  · rw [hN]
    refine sup_le le_normalizer fun y hy => mem_normalizer_fintype fun k hk => ?_
    have e : y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k := by group
    rw [e]
    exact mul_mem (hMK (hc2 k hk y hy)) hk
  · intro k hk
    refine mem_normalizer_fintype fun y hy => ?_
    have e : k * y * k⁻¹ = (k * y * k⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact mul_mem (hMK' (hc1 k hk y hy)) hy

theorem le_of_inf_eq_M {T : Type*} [Group T]
    (hcenT : ∀ x : T, (∀ y, x * y = y * x) → x = 1) {t : G} {K₂ M N R : Subgroup G}
    (hiso : IsQuotientIso K₂ M T) (hMK : M ≤ K₂) (hN : N = K₂ ⊔ K₂ᵍ[t])
    (hcomm : ⁅K₂, K₂ᵍ[t]⁆ ≤ M) (hMt : Mᵍ[t] = M) (hRN : R ≤ N)
    (hRn : N ≤ normalizer (R : Set G)) (h1 : R ⊓ K₂ = M) (h2 : R ⊓ K₂ᵍ[t] = M) : R ≤ M := by
  obtain ⟨hc1, hc2, hK₂n, hK₂'n, hMK'⟩ := prod_facts hMK hN hcomm hMt
  have hMn : K₂ ≤ normalizer (M : Set G) := by
    obtain ⟨φ, -, hφk⟩ := hiso
    have : (M.subgroupOf K₂).Normal := hφk ▸ MonoidHom.normal_ker φ
    exact (normal_subgroupOf_iff_le_normalizer hMK).1 this
  have hK₂N : K₂ ≤ N := hN ▸ le_sup_left
  intro z hz
  have hzN₀ : z ∈ N := hRN hz
  have hzN := hzN₀
  rw [hN, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right K₂ _ hK₂'n] at hzN
  obtain ⟨k, hk, k', hk', rfl⟩ := hzN
  have hcomm_k : ∀ a ∈ K₂, k * a * k⁻¹ * a⁻¹ ∈ M := by
    intro a ha
    have hzaN : a ∈ normalizer (R : Set G) := hRn (hK₂N ha)
    have h3 : (k * k') * a * (k * k')⁻¹ * a⁻¹ ∈ R ⊓ K₂ := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have e : (k * k') * a * (k * k')⁻¹ * a⁻¹ = (k * k') * (a * (k * k')⁻¹ * a⁻¹) := by
          group
        rw [e]
        exact mul_mem hz ((mem_normalizer_iff.1 hzaN _).1 (inv_mem hz))
      · exact mul_mem ((mem_normalizer_iff.1 (hK₂n hzN₀) a).1 ha) (inv_mem ha)
    rw [h1] at h3
    have hc : k' * a * k'⁻¹ * a⁻¹ ∈ M := hc2 a ha k' hk'
    have e : k * a * k⁻¹ * a⁻¹ = (k * (k' * a * k'⁻¹ * a⁻¹) * k⁻¹)⁻¹ *
        ((k * k') * a * (k * k')⁻¹ * a⁻¹) := by group
    rw [e]
    exact mul_mem (inv_mem ((mem_normalizer_iff.1 (hMn hk) _).1 hc)) h3
  have hkM : k ∈ M := mem_of_commutator_mem_of_quotient hiso hcenT hk hcomm_k
  have hzK' : k * k' ∈ K₂ᵍ[t] := mul_mem (hMK' hkM) hk'
  rw [← h2]
  exact Subgroup.mem_inf.2 ⟨hz, hzK'⟩

theorem C1_abstract {T : Type*} [Group T] [IsSimpleGroup T]
    (hcenT : ∀ x : T, (∀ y, x * y = y * x) → x = 1) {t : G} {K₂ M N Z : Subgroup G}
    (hiso : IsQuotientIso K₂ M T) (hMK : M ≤ K₂) (hN : N = K₂ ⊔ K₂ᵍ[t])
    (hcomm : ⁅K₂, K₂ᵍ[t]⁆ ≤ M) (hMt : Mᵍ[t] = M) (hMZ : M ≤ Z) (hZN : Z ≤ N)
    (hZt : Zᵍ[t] = Z) (hZn : N ≤ normalizer (Z : Set G)) : Z ≤ M ∨ N ≤ Z := by
  have hK₂N : K₂ ≤ N := hN ▸ le_sup_left
  have hK₂'N : K₂ᵍ[t] ≤ N := hN ▸ le_sup_right
  have hMC : M ≤ Z ⊓ K₂ := le_inf hMZ hMK
  have hCn : K₂ ≤ normalizer ((Z ⊓ K₂ : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_inf_D4 (hZn (hK₂N hk)) (le_normalizer hk)
  rcases eq_or_eq_of_quotient_simple hiso hMC inf_le_right hCn with hC | hC
  · left
    have hC' : Z ⊓ K₂ᵍ[t] = M := by
      have h1 : (Z ⊓ K₂)ᵍ[t] = Mᵍ[t] := by rw [hC]
      rw [Subgroup.map_inf _ _ _ (MulAut.conj t⁻¹).injective, hZt, hMt] at h1
      exact h1
    exact le_of_inf_eq_M hcenT hiso hMK hN hcomm hMt hZN hZn hC hC'
  · right
    have hK₂Z : K₂ ≤ Z := hC ▸ inf_le_left
    have hK₂'Z : K₂ᵍ[t] ≤ Z := by
      rw [← hZt]
      exact Subgroup.map_mono hK₂Z
    rw [hN]
    exact sup_le hK₂Z hK₂'Z

theorem isQuotientIso_map_conj {X B : Subgroup G} {T : Type*} [Group T] (g : G)
    (h : IsQuotientIso X B T) :
    IsQuotientIso (X.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom) T := by
  obtain ⟨φ, hφs, hφk⟩ := h
  set c : G →* G := (MulAut.conj g).toMonoidHom with hc
  have hinj : Function.Injective c := (MulAut.conj g).injective
  let e : X ≃* X.map c := Subgroup.equivMapOfInjective X c hinj
  refine ⟨φ.comp e.symm.toMonoidHom, hφs.comp e.symm.surjective, ?_⟩
  ext y
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
  have hy : (e.symm y : X) ∈ φ.ker ↔ φ (e.symm y) = 1 := MonoidHom.mem_ker
  rw [← hy, hφk, mem_subgroupOf]
  have hey : c (e.symm y : G) = (y : G) := by
    have h1 := Subgroup.coe_equivMapOfInjective_apply X c hinj (e.symm y)
    have h2 : (e (e.symm y) : G) = (y : G) := by rw [MulEquiv.apply_symm_apply]
    exact h1.symm.trans h2
  constructor
  · intro hmem
    rw [← hey]
    exact ⟨_, hmem, rfl⟩
  · rintro ⟨b, hb, hby⟩
    have : (e.symm y : G) = b := hinj (hey.trans hby.symm)
    rw [this]
    exact hb

theorem perm_abstract {T : Type*} [Group T] [IsSimpleGroup T]
    (hcenT : ∀ x : T, (∀ y, x * y = y * x) → x = 1) {t g : G} {K₂ M N : Subgroup G}
    (hiso : IsQuotientIso K₂ M T) (hMK : M ≤ K₂) (hN : N = K₂ ⊔ K₂ᵍ[t])
    (hcomm : ⁅K₂, K₂ᵍ[t]⁆ ≤ M) (hMt : Mᵍ[t] = M)
    (hgN : g ∈ normalizer (N : Set G)) (hgM : g ∈ normalizer (M : Set G)) :
    K₂.map (MulAut.conj g).toMonoidHom = K₂ ∨ K₂.map (MulAut.conj g).toMonoidHom = K₂ᵍ[t] := by
  obtain ⟨hc1, hc2, hK₂n, hK₂'n, hMK'⟩ := prod_facts hMK hN hcomm hMt
  have hK₂N : K₂ ≤ N := hN ▸ le_sup_left
  have hK₂'N : K₂ᵍ[t] ≤ N := hN ▸ le_sup_right
  have hne : K₂ ≠ M := by
    intro hK
    obtain ⟨φ, hφs, hφk⟩ := hiso
    have hall : ∀ x : K₂, φ x = 1 := by
      intro x
      have : x ∈ φ.ker := by
        rw [hφk, mem_subgroupOf, ← hK]
        exact x.2
      exact this
    have : Subsingleton T := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hφs a
      obtain ⟨y, rfl⟩ := hφs b
      rw [hall x, hall y]⟩
    exact not_subsingleton T ‹_›
  set R := K₂.map (MulAut.conj g).toMonoidHom with hR
  have hRcard : Nat.card R = Nat.card K₂ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hMR : M ≤ R := by
    have h1 : M.map (MulAut.conj g).toMonoidHom = M := mem_normalizer_iff_map_conj_eq.1 hgM
    rw [← h1]
    exact Subgroup.map_mono hMK
  have hRN : R ≤ N := by
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_normalizer_iff.1 hgN k).1 (hK₂N hk)
  have hRn : N ≤ normalizer (R : Set G) := by
    intro n hn
    refine mem_normalizer_fintype fun r hr => ?_
    obtain ⟨k, hk, rfl⟩ := hr
    have hn' : g⁻¹ * n * g ∈ N := by
      have := (mem_normalizer_iff.1 (inv_mem hgN) n).1 hn
      simpa using this
    have hk' : (g⁻¹ * n * g) * k * (g⁻¹ * n * g)⁻¹ ∈ K₂ :=
      (mem_normalizer_iff.1 (hK₂n hn') k).1 hk
    refine ⟨_, hk', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hiso' : IsQuotientIso (K₂ᵍ[t]) M T := by
    have := isQuotientIso_map_conj (MulAut.conj t⁻¹ |> fun _ => t⁻¹) hiso
    rw [hMt] at this
    exact this
  have hMC₁ : M ≤ R ⊓ K₂ := le_inf hMR hMK
  have hMC₂ : M ≤ R ⊓ K₂ᵍ[t] := le_inf hMR hMK'
  have hCn₁ : K₂ ≤ normalizer ((R ⊓ K₂ : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_inf_D4 (hRn (hK₂N hk)) (le_normalizer hk)
  have hCn₂ : K₂ᵍ[t] ≤ normalizer ((R ⊓ K₂ᵍ[t] : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_inf_D4 (hRn (hK₂'N hk)) (le_normalizer hk)
  have hcard' : Nat.card (K₂ᵍ[t]) = Nat.card K₂ :=
    Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective
  rcases eq_or_eq_of_quotient_simple hiso hMC₁ inf_le_right hCn₁ with h1 | h1
  swap
  · left
    have hle : K₂ ≤ R := h1 ▸ inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hle hRcard.le).symm
  rcases eq_or_eq_of_quotient_simple hiso' hMC₂ inf_le_right hCn₂ with h2 | h2
  · exfalso
    have hRM : R ≤ M := le_of_inf_eq_M hcenT hiso hMK hN hcomm hMt hRN hRn h1 h2
    have hcard := Subgroup.card_le_of_le hRM
    rw [hRcard] at hcard
    exact hne (Subgroup.eq_of_le_of_card_ge hMK hcard).symm
  · right
    have hle : K₂ᵍ[t] ≤ R := h2 ▸ inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard', hRcard])).symm

end B1Abs

section B1Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem B1_proof (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (nTwo d t = kTwo d t K ⊔ (kTwo d t K)ᵍ[t] ∧ kTwo d t K ⊓ (kTwo d t K)ᵍ[t] = yamadaM₆ d t ∧
      ⁅kTwo d t K, (kTwo d t K)ᵍ[t]⁆ ≤ yamadaM₆ d t ∧
      IsQuotientIso (kTwo d t K) (yamadaM₆ d t) (SL(2, d.Γ₀)) ∧
      SectionIso (kTwo d t K) (yamadaM₆ d t) (kThree d t K) (eOne d t K)) ∧
    (yamadaP d t ⊓ centralizer ((yamadaY₂ d t : Subgroup G) : Set G) = yamadaM₆ d t ∧
      ((yamadaM₆ d t).subgroupOf (yamadaP d t)).Characteristic ∧
      normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
        normalizer ((yamadaM₆ d t : Subgroup G) : Set G)) := by
  have hlay := hp.layer
  obtain ⟨⟨hXY, hXsyl, hXcard⟩, ⟨hXQ, hQinf, hQcomm, hQsyl, hQcard⟩,
    ⟨hYE, hEinf, hEelem, hEcard, hEQ, hEnorm, hEcoat⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hEK, hpc, hq3, hzc, hN3, hAinf, hAcomm, hq33⟩, ⟨hNX, hLv, hN3M, v₁, hv₁, hdec, hv₁n⟩,
    ⟨hN3M6, hpN2, hPeq, hPsyl, hCM⟩⟩ := A3_structure h d hp hK
  haveI hSL : IsSimpleGroup SL(2, d.Γ₀) := isSimpleGroup_SL d hp.two_le
  have hS5 := S5_upperCentralSeries_P h d hlay
  have hKc : ∀ a ∈ K, ∀ b ∈ Kᵍ[t], a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hK.comm ha) b hb).symm
  have hE₁abel : ∀ x ∈ eOne d t K, ∀ y ∈ eOne d t K, x * y = y * x := by
    haveI := hEelem.1
    exact fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : eOne d t K) ⟨y, hy⟩)
  have hEn : qThree d t K ≤ normalizer ((eOne d t K : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hEQ).1 hEnorm
  have hXM : prodX d t ≤ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) :=
    ((hPeq ▸ le_sup_right : prodX d t ≤ yamadaP d t)).trans
      (h.yamadaP_le_normalizer_yamadaM₆ d hlay)
  obtain ⟨part1, hMeq⟩ := B1_abstract (T := SL(2, d.Γ₀)) (t := t) (K := K)
    (A := kThree d t K) (E₁ := eOne d t K) (Y₂ := yamadaY₂ d t) (M := yamadaM₆ d t)
    (P := yamadaP d t) (X := prodX d t) (N₃ := nThree d t) (Q₃ := qThree d t K)
    (t_mem_normalizer_M₆ h d hlay) hKc rfl hq3 hAinf hAcomm hN3 hEK inf_le_right hE₁abel hYE hEQ
    hEn inf_le_right (isPGroup_of_isSylowOf hQsyl) hXQ hQcomm
    (hNX ▸ le_sup_left) hN3M hN3M6 hPeq inf_le_right hXM (not_P_le_centralizer_Y₂ h d hlay)
  have hZ : (Subgroup.upperCentralSeries ↥(yamadaP d t) 2).map (yamadaP d t).subtype =
      yamadaY₂ d t := hS5.2.1
  haveI hchar : ((yamadaM₆ d t).subgroupOf (yamadaP d t)).Characteristic :=
    characteristic_subgroupOf_of_inf_centralizer hZ hMeq
  refine ⟨part1, hMeq, hchar, ?_⟩
  have hMP : yamadaM₆ d t ≤ yamadaP d t := yamadaM₆_le_yamadaP d t
  have := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := yamadaP d t) ((yamadaM₆ d t).subgroupOf (yamadaP d t))
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hMP] at this

end B1Main

section C1Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem C1_proof (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nTwo d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) = yamadaM₆ d t := by
  have hlay := hp.layer
  obtain ⟨⟨hN2eq, hK₂inf, hcomm, hiso, -⟩, -⟩ := B1_proof h d hp hK
  haveI hSL : IsSimpleGroup SL(2, d.Γ₀) := isSimpleGroup_SL d hp.two_le
  have hMW : yamadaW₃ d t ≤ yamadaM₆ d t := W₃_le_M₆ h d hlay
  have hN₂W := nTwo_le_normalizer_W₃ h d hp hK
  have hN₂M := nTwo_le_normalizer_M₆ h d hp hK
  have htW := t_mem_normalizer_W₃ h d hlay
  have htM := t_mem_normalizer_M₆ h d hlay
  have hMt : (yamadaM₆ d t)ᵍ[t] = yamadaM₆ d t := conjT_eq_self_of_mem_normalizer htM
  have hMc : yamadaM₆ d t ≤ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) := by
    intro g hg
    rw [mem_centralizerMod_iff]
    refine ⟨(h.yamadaP_le_normalizer_yamadaW₃_PA d hlay) (yamadaM₆_le_yamadaP d t hg), ?_⟩
    intro b hb hbN
    exact h.commutator_mem_yamadaW₃_of_mem_yamadaM₆ d hlay hg hb
  have hMZ : yamadaM₆ d t ≤ nTwo d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) :=
    le_inf le_sup_right hMc
  have hZn : nTwo d t ≤ normalizer
      ((nTwo d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) : Subgroup G) : Set G) := by
    intro n hn
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨hzN, hzC⟩ := Subgroup.mem_inf.1 hz
    exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hn hzN) (inv_mem hn),
      conj_mem_centralizerMod (hN₂W hn) (hN₂M hn) hzC⟩
  have hcM : (centralizerMod (yamadaW₃ d t) (yamadaM₆ d t))ᵍ[t] ≤
      centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_centralizerMod (inv_mem htW) (inv_mem htM) hx
  have hcMt := conjT_eq_of_le h.t_mul_t hcM
  have hZt : (nTwo d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t))ᵍ[t] =
      nTwo d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t⁻¹).injective, nTwo_conj_eq h d hp hK, hcMt]
  rcases C1_abstract (T := SL(2, d.Γ₀)) (fun x hx => center_SL_trivial x hx) hiso
    (le_sup_right : yamadaM₆ d t ≤ kTwo d t K) hN2eq hcomm hMt hMZ inf_le_left hZt hZn
    with hle | hle
  · exact le_antisymm hle hMZ
  · exfalso
    refine not_P_le_centralizerMod h d hp ?_
    exact (P_le_nTwo h d hp hK).trans (hle.trans inf_le_right)

end C1Main

section HatFields

open NormalizerQuotient

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

noncomputable def hatT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    Bar (yamadaW₃ d t) :=
  proj (yamadaW₃ d t) ⟨t, t_mem_normalizer_W₃ h d hp.layer⟩

noncomputable def hatV (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    Bar (yamadaW₃ d t) :=
  proj (yamadaW₃ d t) ⟨vG d, h.v_mem_normalizer_yamadaW₃ d⟩

theorem proj_inv_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    proj (yamadaW₃ d t) ⟨t⁻¹, inv_mem (t_mem_normalizer_W₃ h d hp.layer)⟩ = (hatT h d hp)⁻¹ := by
  unfold hatT
  rw [← map_inv]
  rfl

theorem bar_conjT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {X : Subgroup G} (hX : X ≤ normalizer (yamadaW₃ d t : Set G)) :
    bar (yamadaW₃ d t) (Xᵍ[t]) = (bar (yamadaW₃ d t) X)ᵍ[hatT h d hp] := by
  have := bar_map_conj (W := yamadaW₃ d t) (inv_mem (t_mem_normalizer_W₃ h d hp.layer)) hX
  rw [proj_inv_t h d hp] at this
  exact this

theorem bar_conjV (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {X : Subgroup G} (hX : X ≤ normalizer (yamadaW₃ d t : Set G)) :
    bar (yamadaW₃ d t) (X.map (MulAut.conj (vG d)).toMonoidHom) =
      (bar (yamadaW₃ d t) X).map (MulAut.conj (hatV h d)).toMonoidHom :=
  bar_map_conj (W := yamadaW₃ d t) (h.v_mem_normalizer_yamadaW₃ d) hX

theorem hat_t_sq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    hatT h d hp * hatT h d hp = 1 := by
  unfold hatT
  rw [← map_mul, proj_eq_one_iff]
  show t * t ∈ yamadaW₃ d t
  rw [h.t_mul_t]
  exact one_mem _

theorem hat_v_sq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    hatV h d * hatV h d = 1 := by
  unfold hatV
  rw [← map_mul, proj_eq_one_iff]
  show vG d * vG d ∈ yamadaW₃ d t
  rw [Setup.coe_v_mul_self d]
  exact one_mem _

theorem hat_vt (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    hatV h d * hatT h d hp = hatT h d hp * hatV h d := by
  unfold hatV hatT
  rw [← map_mul, ← map_mul, proj_eq_proj_iff]
  have hvt : vG d * t = t * vG d := mem_centralizer_iff.1 h.htL _ (d.v : L).2
  show (vG d * t)⁻¹ * (t * vG d) ∈ yamadaW₃ d t
  rw [hvt, inv_mul_cancel]
  exact one_mem _

theorem hat_M_comm (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    ∀ x ∈ bar (yamadaW₃ d t) (yamadaM₆ d t), ∀ y ∈ bar (yamadaW₃ d t) (yamadaM₆ d t),
      x * y = y * x := by
  intro x hx y hy
  obtain ⟨x₀, hx₀, rfl⟩ := mem_bar_iff_exists.1 hx
  obtain ⟨y₀, hy₀, rfl⟩ := mem_bar_iff_exists.1 hy
  exact ((commutator_mem_iff_proj x₀.2 y₀.2).2
    (h.commutator_mem_yamadaW₃_of_mem_yamadaM₆ d hp.layer hx₀ hy₀)).symm

theorem hat_M_two (d : TrialityD4Data L (2 ^ f)) :
    IsPGroup 2 (bar (yamadaW₃ d t) (yamadaM₆ d t)) :=
  isPGroup_bar (isPGroup_M₆ d)

theorem not_M₆_le_D₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    ¬ yamadaM₆ d t ≤ yamadaD₅ d t := by
  intro hMD
  obtain ⟨-, -, -, -, -, -, -, hD, hM, hP, -⟩ := T4_series_free h d hp
  have hPD : yamadaP d t = yamadaD₅ d t := sup_eq_left.2 hMD
  have hcard : (2 ^ f) ^ 24 = (2 ^ f) ^ 18 := by rw [← hP, ← hD, hPD]
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by have := hp.two_le; omega)
  have := Nat.pow_right_injective h2f hcard
  omega

theorem hat_M_ne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    bar (yamadaW₃ d t) (yamadaM₆ d t) ≠ ⊥ := by
  intro hbot
  apply not_M₆_le_D₅ h d hp
  intro m hm
  have h1 : proj (yamadaW₃ d t) ⟨m, (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)
      (yamadaM₆_le_yamadaP d t hm)⟩ ∈ bar (yamadaW₃ d t) (yamadaM₆ d t) := proj_mem_bar hm
  rw [hbot, Subgroup.mem_bot, proj_eq_one_iff] at h1
  exact (Setup.yamadaF₄_le_yamadaD₅_PA (t := t) d)
    ((h.yamadaW₃_le_yamadaF₄_R5 d hp.layer) h1)

theorem hat_M_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    (bar (yamadaW₃ d t) (yamadaM₆ d t))ᵍ[hatT h d hp] = bar (yamadaW₃ d t) (yamadaM₆ d t) := by
  have hMN : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)
  rw [← bar_conjT h d hp hMN, conjT_eq_self_of_mem_normalizer (t_mem_normalizer_M₆ h d hp.layer)]

theorem hat_v_M (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    hatV h d ∈ normalizer ((bar (yamadaW₃ d t) (yamadaM₆ d t) : Subgroup _) : Set _) :=
  proj_mem_normalizer_bar (W₃_le_M₆ h d hp.layer) (h.v_mem_normalizer_yamadaW₃ d)
    (h.v_mem_normalizer_yamadaM₆_PA d hp.layer)

theorem kThree_le_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kThree d t K ≤ nThree d t := by
  obtain ⟨⟨-, -, -, -, hN3, -⟩, -⟩ := A3_structure h d hp hK
  rw [hN3]; exact le_sup_left

theorem kThree'_le_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (kThree d t K)ᵍ[t] ≤ nThree d t := by
  obtain ⟨⟨-, -, -, -, hN3, -⟩, -⟩ := A3_structure h d hp hK
  rw [hN3]; exact le_sup_right

theorem kThree_commute (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ a ∈ kThree d t K, ∀ b ∈ (kThree d t K)ᵍ[t], a * b = b * a := by
  obtain ⟨⟨-, -, -, -, -, -, hAcomm, -⟩, -⟩ := A3_structure h d hp hK
  exact fun a ha b hb =>
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hAcomm ha) b hb).symm

theorem Y₂_le_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaY₂ d t ≤ yamadaW₃ d t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hW3Y2, -⟩ := T4_series_free h d hp
  exact hW3Y2.1.le

theorem qThree_le_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    qThree d t K ≤ kThree d t K := by
  obtain ⟨-, ⟨-, -, -, hQsyl, -⟩, ⟨-, -, -, -, hEQ, hEnorm, -⟩⟩ := A2_sylow h d hp hK
  have hEn : qThree d t K ≤ normalizer ((eOne d t K : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hEQ).1 hEnorm
  exact le_oTwoPrimeRes_of_isPGroup (le_inf inf_le_right hEn) (isPGroup_of_isSylowOf hQsyl)

theorem hat_A_M (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (kThree d t K) ≤
      normalizer ((bar (yamadaW₃ d t) (yamadaM₆ d t) : Subgroup _) : Set _) := by
  obtain ⟨-, ⟨-, -, hN3M, -⟩, -⟩ := A3_structure h d hp hK
  exact bar_le_normalizer_bar (W₃_le_M₆ h d hp.layer) ((kThree_le_nThree h d hp hK).trans hN3M)

theorem hat_A_comm (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ a ∈ bar (yamadaW₃ d t) (kThree d t K),
      ∀ b ∈ (bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp], a * b = b * a := by
  intro a ha b hb
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  rw [← bar_conjT h d hp hKW] at hb
  obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 ha
  obtain ⟨y, hy, rfl⟩ := mem_bar_iff_exists.1 hb
  have hc := kThree_commute h d hp hK x hx y hy
  refine ((commutator_mem_iff_proj x.2 y.2).2 ?_).symm
  rw [hc]
  simp

theorem hat_A_inf (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (kThree d t K) ⊓ (bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp] = ⊥ := by
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  obtain ⟨⟨hEK, -, -, -, hN3, hAinf, -⟩, -, ⟨hN3M6, -⟩⟩ := A3_structure h d hp hK
  obtain ⟨-, -, ⟨hYE, -⟩⟩ := A2_sylow h d hp hK
  rw [← bar_conjT h d hp hKW, eq_bot_iff]
  intro z hz
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hz1
  obtain ⟨y, hy, hxy⟩ := mem_bar_iff_exists.1 hz2
  have hw : (y : G)⁻¹ * x ∈ yamadaW₃ d t := proj_eq_proj_iff.1 hxy
  have hwY : (y : G)⁻¹ * x ∈ yamadaY₂ d t := by
    rw [← hN3M6]
    exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ((kThree'_le_nThree h d hp hK) hy))
      ((kThree_le_nThree h d hp hK) hx), W₃_le_M₆ h d hp.layer hw⟩
  have hw' : (y : G)⁻¹ * x ∈ eOne d t K ⊔ (eOne d t K)ᵍ[t] := by rw [← hYE]; exact hwY
  have hxE : (x : G) ∈ eOne d t K :=
    mem_of_mul_mem_prod (kThree_commute h d hp hK) hAinf hEK (Subgroup.map_mono hEK) hx hy hw'
  have hxW : (x : G) ∈ yamadaW₃ d t :=
    Y₂_le_W₃ h d hp (by rw [hYE]; exact mem_sup_left hxE)
  rw [Subgroup.mem_bot, proj_eq_one_iff]
  exact hxW

theorem hat_A_inf_M (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (bar (yamadaW₃ d t) (kThree d t K) ⊔ (bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp]) ⊓
      bar (yamadaW₃ d t) (yamadaM₆ d t) = ⊥ := by
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hK'W : (kThree d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree'_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  obtain ⟨⟨-, -, -, -, hN3, -⟩, -, ⟨hN3M6, -⟩⟩ := A3_structure h d hp hK
  rw [← bar_conjT h d hp hKW, ← bar_sup hKW hK'W, eq_bot_iff]
  intro z hz
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hz1
  obtain ⟨m, hm, hmx⟩ := mem_bar_iff_exists.1 hz2
  have hw : (m : G)⁻¹ * x ∈ yamadaW₃ d t := proj_eq_proj_iff.1 hmx
  have hxM : (x : G) ∈ yamadaM₆ d t := by
    have e : (x : G) = m * ((m : G)⁻¹ * x) := by group
    rw [e]
    exact mul_mem hm (W₃_le_M₆ h d hp.layer hw)
  have hxN : (x : G) ∈ nThree d t := by rw [hN3]; exact hx
  have hxY : (x : G) ∈ yamadaY₂ d t := by
    rw [← hN3M6]
    exact Subgroup.mem_inf.2 ⟨hxN, hxM⟩
  rw [Subgroup.mem_bot, proj_eq_one_iff]
  exact Y₂_le_W₃ h d hp hxY

theorem hat_c1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ x ∈ (bar (yamadaW₃ d t) (kThree d t K) ⊔
        (bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp]) ⊔
        bar (yamadaW₃ d t) (yamadaM₆ d t),
      (∀ m ∈ bar (yamadaW₃ d t) (yamadaM₆ d t), x * m = m * x) →
        x ∈ bar (yamadaW₃ d t) (yamadaM₆ d t) := by
  intro x hx hcomm
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hK'W : (kThree d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree'_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hMW : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)
  obtain ⟨⟨-, -, -, -, hN3, -⟩, -⟩ := A3_structure h d hp hK
  rw [← bar_conjT h d hp hKW, ← bar_sup hKW hK'W, ← bar_sup (sup_le hKW hK'W) hMW] at hx
  obtain ⟨x₀, hx₀, rfl⟩ := mem_bar_iff_exists.1 hx
  have hx₀N : (x₀ : G) ∈ nTwo d t := by
    show (x₀ : G) ∈ nThree d t ⊔ yamadaM₆ d t
    rw [hN3]
    exact hx₀
  have hcen : (x₀ : G) ∈ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) := by
    rw [mem_centralizerMod_iff]
    refine ⟨x₀.2, fun b hb hbN => ?_⟩
    have hc := hcomm (proj (yamadaW₃ d t) ⟨b, hbN⟩) (proj_mem_bar hb)
    exact (commutator_mem_iff_proj x₀.2 hbN).1 hc.symm
  have hmem : (x₀ : G) ∈ yamadaM₆ d t := by
    rw [← C1_proof h d hp hK]
    exact Subgroup.mem_inf.2 ⟨hx₀N, hcen⟩
  exact proj_mem_bar hmem

theorem hat_Qs_A (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (qThree d t K) ≤ bar (yamadaW₃ d t) (kThree d t K) :=
  bar_mono (qThree_le_kThree h d hp hK)

theorem hat_Qs_two (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    IsPGroup 2 (bar (yamadaW₃ d t) (qThree d t K)) := by
  obtain ⟨-, ⟨-, -, -, hQsyl, -⟩, -⟩ := A2_sylow h d hp hK
  exact isPGroup_bar (isPGroup_of_isSylowOf hQsyl)

theorem hat_v_dec (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∃ v₁ ∈ bar (yamadaW₃ d t) (kThree d t K),
      hatV h d = v₁ * ((hatT h d hp)⁻¹ * v₁ * hatT h d hp) := by
  obtain ⟨-, ⟨-, -, -, v₁, hv₁, hdec, -⟩, -⟩ := A3_structure h d hp hK
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hvW := h.v_mem_normalizer_yamadaW₃ d
  have htW := t_mem_normalizer_W₃ h d hp.layer
  have e : (⟨vG d, hvW⟩ : normalizer (yamadaW₃ d t : Set G)) =
      ⟨v₁, hKW hv₁⟩ * (⟨t, htW⟩⁻¹ * ⟨v₁, hKW hv₁⟩ * ⟨t, htW⟩) := by
    apply Subtype.ext
    simpa using hdec
  refine ⟨proj (yamadaW₃ d t) ⟨v₁, hKW hv₁⟩, proj_mem_bar hv₁, ?_⟩
  unfold hatV hatT
  rw [e, map_mul, map_mul, map_mul, map_inv]

theorem F₄_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : yamadaF₄ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
  ((Setup.yamadaF₄_le_yamadaD₅_PA (t := t) d).trans (yamadaD₅_le_yamadaP d t)).trans
    (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)

theorem mem_F₄_iff (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {g : G} : g ∈ yamadaF₄ d t ↔ g ∈ yamadaP d t ∧
      ∀ y ∈ yamadaP d t, g * y * g⁻¹ * y⁻¹ ∈ yamadaW₃ d t := by
  obtain ⟨hS1, hS2, hS3, hS4⟩ := S5_upperCentralSeries_P h d hp.layer
  have hmemZ3 : ∀ x : ↥(yamadaP d t), (x : G) ∈ yamadaW₃ d t →
      x ∈ Subgroup.upperCentralSeries ↥(yamadaP d t) 3 := by
    intro x hx
    rw [← hS3] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := Subtype.ext hzx
    rwa [this] at hz
  constructor
  · intro hg
    rw [← hS4] at hg
    obtain ⟨z, hz, rfl⟩ := hg
    refine ⟨z.2, fun y hy => ?_⟩
    have hz4 : z ∈ Subgroup.upperCentralSeries ↥(yamadaP d t) (3 + 1) := hz
    rw [Subgroup.mem_upperCentralSeries_succ_iff] at hz4
    have h3 := hz4 ⟨y, hy⟩
    have h4 : (((z * ⟨y, hy⟩ * z⁻¹ * ⟨y, hy⟩⁻¹ : ↥(yamadaP d t))) : G) ∈
        (Subgroup.upperCentralSeries ↥(yamadaP d t) 3).map (yamadaP d t).subtype := ⟨_, h3, rfl⟩
    rw [hS3] at h4
    simpa using h4
  · rintro ⟨hgP, hg⟩
    rw [← hS4]
    refine ⟨⟨g, hgP⟩, ?_, rfl⟩
    change (⟨g, hgP⟩ : ↥(yamadaP d t)) ∈ Subgroup.upperCentralSeries ↥(yamadaP d t) (3 + 1)
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    exact hmemZ3 _ (hg y y.2)

theorem prodX_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : prodX d t ≤ normalizer (yamadaW₃ d t : Set G) :=
  (prodX_le_P d).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)

theorem hat_gen (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (kThree d t K) ⊔ (bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp] =
      (bar (yamadaW₃ d t) (qThree d t K) ⊔ (bar (yamadaW₃ d t) (qThree d t K))ᵍ[hatT h d hp]) ⊔
        (bar (yamadaW₃ d t) (qThree d t K) ⊔
          (bar (yamadaW₃ d t) (qThree d t K))ᵍ[hatT h d hp]).map
            (MulAut.conj (hatV h d)).toMonoidHom := by
  obtain ⟨-, ⟨hXQ, -⟩, -⟩ := A2_sylow h d hp hK
  obtain ⟨⟨-, -, -, -, hN3, -⟩, ⟨hNX, -⟩, -⟩ := A3_structure h d hp hK
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hK'W : (kThree d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree'_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hXW := prodX_le_normalizer_W₃ h d hp
  have hQW : qThree d t K ≤ normalizer (yamadaW₃ d t : Set G) := by
    refine le_trans ?_ hXW
    rw [hXQ]; exact le_sup_left
  have hQ'W : (qThree d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) := by
    refine le_trans ?_ hXW
    rw [hXQ]; exact le_sup_right
  have hXvW := map_conj_le_normalizer (h.v_mem_normalizer_yamadaW₃ d) hXW
  rw [← bar_conjT h d hp hKW, ← bar_sup hKW hK'W, ← bar_conjT h d hp hQW,
    ← bar_sup hQW hQ'W, ← hXQ, ← bar_conjV h d hXW, ← bar_sup hXW hXvW, ← hNX, hN3]

theorem hat_F_ctr (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ x, x ∈ bar (yamadaW₃ d t) (yamadaF₄ d t) ↔
      x ∈ (bar (yamadaW₃ d t) (yamadaM₆ d t) ⊔ (bar (yamadaW₃ d t) (qThree d t K) ⊔
        (bar (yamadaW₃ d t) (qThree d t K))ᵍ[hatT h d hp]) : Subgroup _) ∧
      x ∈ centralizer ((bar (yamadaW₃ d t) (yamadaM₆ d t) ⊔
        (bar (yamadaW₃ d t) (qThree d t K) ⊔
          (bar (yamadaW₃ d t) (qThree d t K))ᵍ[hatT h d hp]) : Subgroup _) : Set _) := by
  obtain ⟨-, ⟨hXQ, -⟩, -⟩ := A2_sylow h d hp hK
  obtain ⟨-, -, ⟨-, -, hPeq, -⟩⟩ := A3_structure h d hp hK
  have hXW := prodX_le_normalizer_W₃ h d hp
  have hQW : qThree d t K ≤ normalizer (yamadaW₃ d t : Set G) := by
    refine le_trans ?_ hXW
    rw [hXQ]; exact le_sup_left
  have hQ'W : (qThree d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) := by
    refine le_trans ?_ hXW
    rw [hXQ]; exact le_sup_right
  have hMW : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)
  have hPW : yamadaP d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer
  have hbarP : bar (yamadaW₃ d t) (yamadaM₆ d t) ⊔ (bar (yamadaW₃ d t) (qThree d t K) ⊔
      (bar (yamadaW₃ d t) (qThree d t K))ᵍ[hatT h d hp]) = bar (yamadaW₃ d t) (yamadaP d t) := by
    rw [← bar_conjT h d hp hQW, ← bar_sup hQW hQ'W, ← hXQ, ← bar_sup hMW hXW, ← hPeq]
  rw [hbarP]
  intro x
  constructor
  · intro hx
    obtain ⟨f₀, hf₀, rfl⟩ := mem_bar_iff_exists.1 hx
    obtain ⟨hfP, hfc⟩ := (mem_F₄_iff h d hp).1 hf₀
    refine ⟨proj_mem_bar hfP, mem_centralizer_iff.2 fun z hz => ?_⟩
    obtain ⟨y₀, hy₀, rfl⟩ := mem_bar_iff_exists.1 hz
    exact (commutator_mem_iff_proj f₀.2 y₀.2).2 (hfc y₀ hy₀)
  · rintro ⟨hxP, hxC⟩
    obtain ⟨p₀, hp₀, rfl⟩ := mem_bar_iff_exists.1 hxP
    refine proj_mem_bar ((mem_F₄_iff h d hp).2 ⟨hp₀, fun y hy => ?_⟩)
    have hyN : y ∈ normalizer (yamadaW₃ d t : Set G) := hPW hy
    have := mem_centralizer_iff.1 hxC (proj (yamadaW₃ d t) ⟨y, hyN⟩) (proj_mem_bar hy)
    exact (commutator_mem_iff_proj p₀.2 hyN).1 this

theorem hat_F_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    (bar (yamadaW₃ d t) (yamadaF₄ d t))ᵍ[hatT h d hp] = bar (yamadaW₃ d t) (yamadaF₄ d t) := by
  rw [← bar_conjT h d hp (F₄_le_normalizer_W₃ h d hp),
    conjT_eq_self_of_mem_normalizer (h.t_mem_normalizer_yamadaF₄ d hp.layer)]

theorem hat_F_inf (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    bar (yamadaW₃ d t) (yamadaF₄ d t) ⊓
      (bar (yamadaW₃ d t) (yamadaF₄ d t)).map (MulAut.conj (hatV h d)).toMonoidHom = ⊥ := by
  have hF := F₄_le_normalizer_W₃ h d hp
  rw [← bar_conjV h d hF, ← bar_inf (h.yamadaW₃_le_yamadaF₄_R5 d hp.layer), eq_bot_iff,
    ← bar_self (yamadaW₃ d t)]
  exact bar_mono (h.yamadaF₄_inf_map_conj_le_yamadaW₃_PA d hp.layer)

theorem hat_M_F (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    bar (yamadaW₃ d t) (yamadaM₆ d t) ≤ bar (yamadaW₃ d t) (yamadaF₄ d t) ⊔
      (bar (yamadaW₃ d t) (yamadaF₄ d t)).map (MulAut.conj (hatV h d)).toMonoidHom := by
  have hF := F₄_le_normalizer_W₃ h d hp
  have hFv := map_conj_le_normalizer (h.v_mem_normalizer_yamadaW₃ d) hF
  rw [← bar_conjV h d hF, ← bar_sup hF hFv]
  exact bar_mono (h.yamadaM₆_le_sup_map_conj_yamadaF₄_PA d hp.layer)

theorem hat_free (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    Nat.card ↥(bar (yamadaW₃ d t) (yamadaM₆ d t)) =
      Nat.card ↥(bar (yamadaW₃ d t) (yamadaM₆ d t) ⊓
        centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t)))) ^ 2 := by
  have hlay := hp.layer
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hFW, -, -, hMF, -⟩ := T4_series_free h d hp
  have htW := t_mem_normalizer_W₃ h d hlay
  have hWF := h.yamadaW₃_le_yamadaF₄_R5 d hlay
  have hFM := h.yamadaF₄_le_yamadaM₆_PA d hlay
  have hMN : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hlay)
  have hMsec : IsElemSection (yamadaM₆ d t) (yamadaW₃ d t) :=
    ⟨hWF.trans hFM, fun x hx => h.mul_self_mem_yamadaW₃_of_mem_yamadaM₆ d hlay hx,
      fun x hx y hy => h.commutator_mem_yamadaW₃_of_mem_yamadaM₆ d hlay hx hy⟩
  have hfree : IsFreeSection t (yamadaM₆ d t) (yamadaW₃ d t) :=
    T1_extension hMsec hWF hFM h.t_mul_t (t_mem_normalizer_M₆ h d hlay)
      (h.t_mem_normalizer_yamadaF₄ d hlay) htW hFW.2.1 hMF.2.1
  unfold IsFreeSection at hfree
  have hWM : yamadaW₃ d t ≤ yamadaM₆ d t := hWF.trans hFM
  rw [centralizerMod_zpowers htW] at hfree
  have hC : yamadaM₆ d t ⊓ lift (centralizer ({proj (yamadaW₃ d t) ⟨t, htW⟩} :
      Set (Bar (yamadaW₃ d t)))) ≤ normalizer (yamadaW₃ d t : Set G) := inf_le_left.trans hMN
  have hWC : yamadaW₃ d t ≤ yamadaM₆ d t ⊓ lift (centralizer ({proj (yamadaW₃ d t) ⟨t, htW⟩} :
      Set (Bar (yamadaW₃ d t)))) := le_inf hWM (le_lift _)
  rw [relIndex_eq_card_bar hWM hMN, relIndex_eq_card_bar hWC hC,
    bar_inf hWM, bar_lift] at hfree
  exact hfree

theorem h1Zero_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    H1Zero t (yamadaW₃ d t) := by
  have hlay := hp.layer
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hV, hY, hW, -⟩ := T4_series_free h d hp
  have htV := normalizer_P_le_normalizer_of_series (S5_upperCentralSeries_P h d hlay).1
    (h.t_mem_normalizer_yamadaP d hlay)
  have htY := normalizer_P_le_normalizer_of_series (S5_upperCentralSeries_P h d hlay).2.1
    (h.t_mem_normalizer_yamadaP d hlay)
  have htW := t_mem_normalizer_W₃ h d hlay
  have hbot : t ∈ normalizer ((⊥ : Subgroup G) : Set G) :=
    mem_normalizer_bot_aux t
  have hV1 : H1Zero t (yamadaV₁ d t) :=
    h1Zero_of_sec_bot (T1_h1_zero hV.1 h.t_mul_t htV hbot hV.2.1)
  have hY1 : H1Zero t (yamadaY₂ d t) :=
    T2_h1_zero h.t_mul_t hY.1.le (isElemSection_le_normalizer hY.1) htY htV hV1
      (T1_h1_zero hY.1 h.t_mul_t htY htV hY.2.1)
  exact T2_h1_zero h.t_mul_t hW.1.le (isElemSection_le_normalizer hW.1) htW htY hY1
    (T1_h1_zero hW.1 h.t_mul_t htW htY hW.2.1)

theorem J_comm {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q) :
    ∀ a ∈ d.J, ∀ b ∈ d.J, a * b = b * a := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem L_le_centralizer_t (h : Setup G L f t) : L ≤ centralizer ({t} : Set G) := fun x hx =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h.htL x hx)

theorem J_map_le_centralizer_J₀ {q : ℕ} (d : TrialityD4Data L q) :
    d.J.map L.subtype ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (J_comm d b (d.J₀_le_J hb) a ha)

theorem J_map_le_ncs (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.J.map L.subtype ≤ ncs d t :=
  le_inf ((map_subtype_le _).trans (L_le_centralizer_t h))
    (Setup.map_le_normalizer_map d.J_le_normalizer_S)

theorem J_map_le_normalizer_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.J.map L.subtype ≤ normalizer (yamadaP d t : Set G) :=
  (J_map_le_ncs h d).trans (ncs_le_normalizer_yamadaP h d hlay)

theorem J_map_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.J.map L.subtype ≤ normalizer (yamadaW₃ d t : Set G) :=
  (J_map_le_normalizer_P h d hlay).trans
    (normalizer_P_le_normalizer_of_series (S5_upperCentralSeries_P h d hlay).2.2.1)

theorem J_map_le_normalizer_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    d.J.map L.subtype ≤ normalizer (yamadaM₆ d t : Set G) :=
  (J_map_le_normalizer_P h d hp.layer).trans (B1_proof h d hp hK).2.2.2

theorem J_map_le_normalizer_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.J.map L.subtype ≤ normalizer (nThree d t : Set G) := by
  intro x hx
  have hY : x ∈ normalizer (yamadaY₂ d t : Set G) :=
    normalizer_P_le_normalizer_of_series (S5_upperCentralSeries_P h d hlay).2.1
      (J_map_le_normalizer_P h d hlay hx)
  have hE : x ∈ normalizer (jZeroLayer d : Set G) :=
    Setup.le_normalizer_jZeroLayer d (J_map_le_centralizer_J₀ d hx)
  exact mem_normalizer_oTwoPrimeRes (mem_normalizer_inf_D4 hE (mem_normalizer_normalizer hY))

theorem J_map_le_normalizer_nTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    d.J.map L.subtype ≤ normalizer (nTwo d t : Set G) := fun x hx =>
  mem_normalizer_sup (J_map_le_normalizer_nThree h d hp.layer hx)
    (J_map_le_normalizer_M₆ h d hp hK hx)

theorem kTwo_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kTwo d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
  sup_le ((kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK))
    ((yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer))

theorem hat_bar_K₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (kTwo d t K) =
      bar (yamadaW₃ d t) (kThree d t K) ⊔ bar (yamadaW₃ d t) (yamadaM₆ d t) :=
  bar_sup ((kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK))
    ((yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer))

theorem hat_bar_K₂' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) ((kTwo d t K)ᵍ[t]) =
      (bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp] ⊔ bar (yamadaW₃ d t) (yamadaM₆ d t) := by
  rw [bar_conjT h d hp (kTwo_le_normalizer_W₃ h d hp hK), hat_bar_K₂ h d hp hK,
    Subgroup.map_sup, hat_M_t h d hp]

theorem hat_center_K₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (kTwo d t K) ⊓ centralizer ((bar (yamadaW₃ d t) (kTwo d t K) :
      Subgroup _) : Set _) = zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
        (bar (yamadaW₃ d t) (kThree d t K)) := by
  rw [hat_bar_K₂ h d hp hK]
  exact center_sup_of (hat_M_comm h d hp) (hat_c1 h d hp hK)

theorem hat_center_K₂' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) ((kTwo d t K)ᵍ[t]) ⊓ centralizer ((bar (yamadaW₃ d t) ((kTwo d t K)ᵍ[t]) :
      Subgroup _) : Set _) = zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
        ((bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp]) := by
  rw [hat_bar_K₂' h d hp hK]
  exact center_sup_of (A := (bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp])
    (A' := bar (yamadaW₃ d t) (kThree d t K)) (hat_M_comm h d hp)
    (by rw [sup_comm ((bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp])]; exact hat_c1 h d hp hK)

theorem M₆_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) :
    yamadaM₆ d t ⊓ centralizer ({t} : Set G) = d.M.map L.subtype := by
  obtain ⟨-, -, -, -, -, hM6, -⟩ := T4_series_free h d hp
  exact hM6

theorem W_map_le_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    d.W.map L.subtype ≤ yamadaW₃ d t := Setup.W_map_le_yamadaW₃_S4C h d hlay

theorem hat_Mfix (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    bar (yamadaW₃ d t) (yamadaM₆ d t) ⊓ centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t))) =
      bar (yamadaW₃ d t) (d.M.map L.subtype) := by
  have hlay := hp.layer
  have hM₀ := M₆_inf_centralizer h d hp
  have hM₀M : d.M.map L.subtype ≤ yamadaM₆ d t := hM₀ ▸ inf_le_left
  have hM₀C : d.M.map L.subtype ≤ centralizer ({t} : Set G) := hM₀ ▸ inf_le_right
  have hMN : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hlay)
  have htW := t_mem_normalizer_W₃ h d hlay
  apply le_antisymm
  · intro y hy
    obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨m, hm, rfl⟩ := mem_bar_iff_exists.1 hyM
    have hc := (commutator_mem_iff_proj (N := yamadaW₃ d t) htW m.2).1
      (mem_centralizer_singleton_iff.1 hyC)
    have hcomm : (m : G)⁻¹ * (t * m * t⁻¹) ∈ yamadaW₃ d t := by
      have hmem := (mem_normalizer_iff.1 (inv_mem m.2) _).1 hc
      have e : (m : G)⁻¹ * (t * m * t⁻¹ * (m : G)⁻¹) * (m : G)⁻¹⁻¹ = (m : G)⁻¹ * (t * m * t⁻¹) := by
        group
      rw [← e]
      simpa using hmem
    have hmem := T2_lift h.t_mul_t (W₃_le_M₆ h d hlay) hMN (t_mem_normalizer_M₆ h d hlay) htW
      (h1Zero_W₃ h d hp) m hm hcomm
    rw [hM₀] at hmem
    have hM₀N : d.M.map L.subtype ≤ normalizer (yamadaW₃ d t : Set G) := hM₀M.trans hMN
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hM₀N] at hmem
    obtain ⟨x, hx, w, hw, hxw⟩ := hmem
    have hxN : x ∈ normalizer (yamadaW₃ d t : Set G) := hM₀N hx
    have e : (⟨(m : G), m.2⟩ : normalizer (yamadaW₃ d t : Set G)) =
        ⟨x, hxN⟩ * ⟨w, le_normalizer hw⟩ := Subtype.ext hxw.symm
    have hproj : proj (yamadaW₃ d t) m = proj (yamadaW₃ d t) ⟨x, hxN⟩ := by
      have : m = ⟨x, hxN⟩ * ⟨w, le_normalizer hw⟩ := e
      rw [this, map_mul, (proj_eq_one_iff.2 hw : proj (yamadaW₃ d t) ⟨w, le_normalizer hw⟩ = 1),
        mul_one]
    rw [hproj]
    exact proj_mem_bar hx
  · refine le_inf (bar_mono hM₀M) fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy
    rw [mem_centralizer_singleton_iff]
    refine (commutator_mem_iff_proj (N := yamadaW₃ d t) htW x.2).2 ?_
    have hxt : (x : G) * t = t * x := mem_centralizer_singleton_iff.1 (hM₀C hx)
    have e : t * (x : G) * t⁻¹ * (x : G)⁻¹ = 1 := by
      rw [← hxt]; group
    rw [e]
    exact one_mem _

theorem leviLong_map_le_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    d.leviLong.map L.subtype ≤ nThree d t := by
  obtain ⟨-, ⟨-, hLv, -⟩, -⟩ := A3_structure h d hp hK
  exact hLv

theorem proj_mem_centralizer_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {x : normalizer (yamadaW₃ d t : Set G)} (hx : (x : G) * t = t * x) :
    proj (yamadaW₃ d t) x ∈ centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t))) := by
  rw [mem_centralizer_singleton_iff]
  refine (commutator_mem_iff_proj (N := yamadaW₃ d t) (t_mem_normalizer_W₃ h d hp.layer) x.2).2 ?_
  have e : t * (x : G) * t⁻¹ * (x : G)⁻¹ = 1 := by
    rw [← hx]; group
  rw [e]
  exact one_mem _

theorem hat_L0_M (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (d.leviLong.map L.subtype ⊔ d.J.map L.subtype) ≤
      normalizer ((bar (yamadaW₃ d t) (yamadaM₆ d t) : Subgroup _) : Set _) := by
  obtain ⟨-, ⟨-, -, hN3M, -⟩, -⟩ := A3_structure h d hp hK
  exact bar_le_normalizer_bar (W₃_le_M₆ h d hp.layer)
    (sup_le ((leviLong_map_le_nThree h d hp hK).trans hN3M)
      (J_map_le_normalizer_M₆ h d hp hK))

theorem hat_L0_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    bar (yamadaW₃ d t) (d.leviLong.map L.subtype ⊔ d.J.map L.subtype) ≤
      centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t))) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy
  have hxL : (x : G) ∈ L := (sup_le (map_subtype_le _) (map_subtype_le _) : _ ≤ L) hx
  exact proj_mem_centralizer_t h d hp (mem_centralizer_singleton_iff.1 (L_le_centralizer_t h hxL))

theorem hat_L0_Z (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (d.leviLong.map L.subtype ⊔ d.J.map L.subtype) ≤
      normalizer ((zOf (bar (yamadaW₃ d t) (yamadaM₆ d t)) (bar (yamadaW₃ d t) (kThree d t K)) ⊔
        zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
          ((bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp]) : Subgroup _) : Set _) := by
  haveI hSL : IsSimpleGroup SL(2, d.Γ₀) := isSimpleGroup_SL d hp.two_le
  have hlay := hp.layer
  have htW := t_mem_normalizer_W₃ h d hlay
  have hK₂W := kTwo_le_normalizer_W₃ h d hp hK
  have hK₂'W : (kTwo d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) :=
    map_conj_le_normalizer (inv_mem htW) hK₂W
  obtain ⟨hN2eq, -, hcomm, hiso, -⟩ := (B1_proof h d hp hK).1
  have hMK : yamadaM₆ d t ≤ kTwo d t K := le_sup_right
  have hMt : (yamadaM₆ d t)ᵍ[t] = yamadaM₆ d t :=
    conjT_eq_self_of_mem_normalizer (t_mem_normalizer_M₆ h d hlay)
  have hcenT : ∀ x : SL(2, d.Γ₀), (∀ y, x * y = y * x) → x = 1 := fun x hx =>
    center_SL_trivial x hx
  obtain ⟨-, -, hK₂n, -, -⟩ := prod_facts hMK hN2eq hcomm hMt
  have key : ∀ g : G, ∀ hgW : g ∈ normalizer (yamadaW₃ d t : Set G), g * t = t * g →
      ((kTwo d t K).map (MulAut.conj g).toMonoidHom = kTwo d t K ∨
        (kTwo d t K).map (MulAut.conj g).toMonoidHom = (kTwo d t K)ᵍ[t]) →
      proj (yamadaW₃ d t) ⟨g, hgW⟩ ∈ normalizer ((zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
        (bar (yamadaW₃ d t) (kThree d t K)) ⊔ zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
          ((bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp]) : Subgroup _) : Set _) := by
    intro g hgW hgt hcase
    have hcomm' : ((kTwo d t K)ᵍ[t]).map (MulAut.conj g).toMonoidHom =
        ((kTwo d t K).map (MulAut.conj g).toMonoidHom)ᵍ[t] :=
      (map_conj_map_conj_comm hgt (kTwo d t K)).symm
    have h1 := bar_map_conj hgW hK₂W
    have h2 := bar_map_conj hgW hK₂'W
    have hhat : ((bar (yamadaW₃ d t) (kTwo d t K)).map
          (MulAut.conj (proj (yamadaW₃ d t) ⟨g, hgW⟩)).toMonoidHom =
            bar (yamadaW₃ d t) (kTwo d t K) ∧
        (bar (yamadaW₃ d t) ((kTwo d t K)ᵍ[t])).map
          (MulAut.conj (proj (yamadaW₃ d t) ⟨g, hgW⟩)).toMonoidHom =
            bar (yamadaW₃ d t) ((kTwo d t K)ᵍ[t])) ∨
        ((bar (yamadaW₃ d t) (kTwo d t K)).map
          (MulAut.conj (proj (yamadaW₃ d t) ⟨g, hgW⟩)).toMonoidHom =
            bar (yamadaW₃ d t) ((kTwo d t K)ᵍ[t]) ∧
        (bar (yamadaW₃ d t) ((kTwo d t K)ᵍ[t])).map
          (MulAut.conj (proj (yamadaW₃ d t) ⟨g, hgW⟩)).toMonoidHom =
            bar (yamadaW₃ d t) (kTwo d t K)) := by
      rcases hcase with hc | hc
      · left
        refine ⟨by rw [← h1, hc], by rw [← h2, hcomm', hc]⟩
      · right
        refine ⟨by rw [← h1, hc], ?_⟩
        rw [← h2, hcomm', hc, map_conj_inv_map_conj_inv h.t_mul_t]
    have := mem_normalizer_sup_center hhat
    rwa [hat_center_K₂ h d hp hK, hat_center_K₂' h d hp hK] at this
  have hLN : d.leviLong.map L.subtype ≤ normalizer (yamadaW₃ d t : Set G) :=
    (leviLong_map_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hJN : d.J.map L.subtype ≤ normalizer (yamadaW₃ d t : Set G) :=
    J_map_le_normalizer_W₃ h d hlay
  rw [bar_sup hLN hJN]
  refine sup_le ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy
    have hxL : (x : G) ∈ L := (map_subtype_le _ : d.leviLong.map L.subtype ≤ L) hx
    have hxN₂ : (x : G) ∈ nTwo d t :=
      ((leviLong_map_le_nThree h d hp hK).trans le_sup_left) hx
    exact key x x.2 (mem_centralizer_singleton_iff.1 (L_le_centralizer_t h hxL))
      (Or.inl (mem_normalizer_iff_map_conj_eq.1 (hK₂n hxN₂)))
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy
    have hxL : (x : G) ∈ L := (map_subtype_le _ : d.J.map L.subtype ≤ L) hx
    exact key x x.2 (mem_centralizer_singleton_iff.1 (L_le_centralizer_t h hxL))
      (perm_abstract hcenT hiso hMK hN2eq hcomm hMt
        (J_map_le_normalizer_nTwo h d hp hK hx) (J_map_le_normalizer_M₆ h d hp hK hx))

theorem hat_irr (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ S : Subgroup (Bar (yamadaW₃ d t)),
      S ≤ bar (yamadaW₃ d t) (yamadaM₆ d t) ⊓
        centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t))) →
      bar (yamadaW₃ d t) (d.leviLong.map L.subtype ⊔ d.J.map L.subtype) ≤
        normalizer (S : Set (Bar (yamadaW₃ d t))) →
      S = ⊥ ∨ S = bar (yamadaW₃ d t) (yamadaM₆ d t) ⊓
        centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t))) := by
  intro S hS hL0
  have hlay := hp.layer
  have hMfix := hat_Mfix h d hp
  have hM₀ : d.M.map L.subtype ≤ yamadaM₆ d t := (M₆_inf_centralizer h d hp) ▸ inf_le_left
  have hMN : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hlay)
  have hM₀N : d.M.map L.subtype ≤ normalizer (yamadaW₃ d t : Set G) := hM₀.trans hMN
  let θ : ↥(d.M.map L.subtype) →* Bar (yamadaW₃ d t) :=
    (proj (yamadaW₃ d t)).comp (Subgroup.inclusion hM₀N)
  let T : Subgroup L := ((S.comap θ).map (d.M.map L.subtype).subtype).comap L.subtype
  have hmemT : ∀ x : L, x ∈ T ↔ ∃ hx : (x : G) ∈ d.M.map L.subtype, θ ⟨x, hx⟩ ∈ S := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hxM : (x : G) ∈ d.M.map L.subtype := by
        have h2 : (x : G) = (y : G) := hyx.symm
        rw [h2]
        exact y.2
      refine ⟨hxM, ?_⟩
      have : (⟨(x : G), hxM⟩ : ↥(d.M.map L.subtype)) = y := Subtype.ext hyx.symm
      rw [this]
      exact hy
    · rintro ⟨hx, hθ⟩
      exact ⟨⟨x, hx⟩, hθ, rfl⟩
  have hTM : T ≤ d.M := by
    intro x hx
    obtain ⟨hxM, -⟩ := (hmemT x).1 hx
    obtain ⟨x', hx', hxx⟩ := hxM
    have : x' = x := Subtype.ext hxx
    rwa [← this]
  have hWT : d.W ≤ T := by
    intro x hx
    have hxM : (x : G) ∈ d.M.map L.subtype := ⟨x, d.F_le_M (d.W_le_F hx), rfl⟩
    refine (hmemT x).2 ⟨hxM, ?_⟩
    have hxW : (x : G) ∈ yamadaW₃ d t := W_map_le_W₃ h d hlay ⟨x, hx, rfl⟩
    have : θ ⟨x, hxM⟩ = 1 := proj_eq_one_iff.2 hxW
    rw [this]
    exact one_mem _
  have hLJ : d.leviLong.map L.subtype ⊔ d.J.map L.subtype ≤ normalizer (yamadaW₃ d t : Set G) :=
    sup_le ((leviLong_map_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK))
      (J_map_le_normalizer_W₃ h d hlay)
  have hconj : ∀ g : L, (g : G) ∈ d.leviLong.map L.subtype ⊔ d.J.map L.subtype →
      g ∈ normalizer (d.M : Set L) → ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g hgL0 hgM x hx
    obtain ⟨hxM₀, hθx⟩ := (hmemT x).1 hx
    have hxM : x ∈ d.M := hTM hx
    have hgxg : g * x * g⁻¹ ∈ d.M := (mem_normalizer_iff.1 hgM x).1 hxM
    have hmem : ((g * x * g⁻¹ : L) : G) ∈ d.M.map L.subtype := ⟨_, hgxg, rfl⟩
    refine (hmemT _).2 ⟨hmem, ?_⟩
    have hgN : (g : G) ∈ normalizer (yamadaW₃ d t : Set G) := hLJ hgL0
    have hĝ : proj (yamadaW₃ d t) ⟨(g : G), hgN⟩ ∈ normalizer (S : Set _) :=
      hL0 (proj_mem_bar hgL0)
    have e : (⟨((g * x * g⁻¹ : L) : G), hM₀N hmem⟩ : normalizer (yamadaW₃ d t : Set G)) =
        ⟨(g : G), hgN⟩ * ⟨(x : G), hM₀N hxM₀⟩ * ⟨(g : G), hgN⟩⁻¹ := by
      apply Subtype.ext
      simp
    have e2 : θ ⟨((g * x * g⁻¹ : L) : G), hmem⟩ = proj (yamadaW₃ d t) ⟨(g : G), hgN⟩ *
        θ ⟨x, hxM₀⟩ * (proj (yamadaW₃ d t) ⟨(g : G), hgN⟩)⁻¹ := by
      show proj (yamadaW₃ d t) ⟨((g * x * g⁻¹ : L) : G), hM₀N hmem⟩ = _
      rw [e, map_mul, map_mul, map_inv]
      rfl
    rw [e2]
    exact (mem_normalizer_iff.1 hĝ _).1 hθx
  have hKT : d.leviLong ≤ normalizer (T : Set L) := fun g hg =>
    mem_normalizer_fintype fun x hx =>
      hconj g (mem_sup_left ⟨g, hg, rfl⟩) (d.leviLong_le_normalizer_M hg) x hx
  have hJT : d.J ≤ normalizer (T : Set L) := fun g hg =>
    mem_normalizer_fintype fun x hx =>
      hconj g (mem_sup_right ⟨g, hg, rfl⟩) (d.J_le_normalizer_M hg) x hx
  rcases d.leviLong_J_irreducible_M_mod_W hWT hTM hKT hJT with hT | hT
  · left
    rw [eq_bot_iff]
    intro s hs
    have hs' : s ∈ bar (yamadaW₃ d t) (d.M.map L.subtype) := hMfix ▸ hS hs
    obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hs'
    obtain ⟨x', hx', hxx⟩ := hx
    have hxM : (x' : G) ∈ d.M.map L.subtype := ⟨x', hx', rfl⟩
    have hx'T : x' ∈ T := by
      refine (hmemT x').2 ⟨hxM, ?_⟩
      have : θ ⟨x', hxM⟩ = proj (yamadaW₃ d t) x := by
        show proj (yamadaW₃ d t) ⟨(x' : G), _⟩ = _
        congr 1
        exact Subtype.ext hxx
      rw [this]
      exact hs
    rw [hT] at hx'T
    rw [Subgroup.mem_bot, proj_eq_one_iff]
    rw [← hxx]
    exact W_map_le_W₃ h d hlay ⟨x', hx'T, rfl⟩
  · right
    apply le_antisymm hS
    rw [hMfix]
    intro s hs
    obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hs
    obtain ⟨x', hx', hxx⟩ := hx
    have hx'T : x' ∈ T := hT ▸ hx'
    obtain ⟨hxM, hθ⟩ := (hmemT x').1 hx'T
    have : θ ⟨x', hxM⟩ = proj (yamadaW₃ d t) x := by
      show proj (yamadaW₃ d t) ⟨(x' : G), _⟩ = _
      congr 1
      exact Subtype.ext hxx
    rw [← this]
    exact hθ

end HatFields

section LSide

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem leviLong_le_commutator (hq : 4 ≤ Nat.card d.Γ₀) :
    d.leviLong ≤ ⁅d.leviLong, d.leviLong⁆ := by
  have hperf : Group.IsPerfect SL(2, d.Γ₀) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four hq)
  haveI : Group.IsPerfect ↥d.leviLong :=
    Group.IsPerfect.ofSurjective (f := d.leviLongEquiv.symm.toMonoidHom)
      d.leviLongEquiv.symm.surjective
  exact (Subgroup.isPerfect_iff.1 this).ge

theorem leviLong_sup_M_le_commutator (hq : 4 ≤ Nat.card d.Γ₀) :
    d.leviLong ⊔ d.M ≤ ⁅d.leviLong ⊔ d.M, d.leviLong ⊔ d.M⁆ ⊔ d.W := by
  set A := d.leviLong ⊔ d.M with hA
  set C := ⁅A, A⁆ ⊔ d.W with hC
  have hWC : d.W ≤ C := le_sup_right
  have hAA : ⁅A, A⁆ ≤ C := le_sup_left
  have hL : d.leviLong ≤ C :=
    (leviLong_le_commutator d hq).trans ((commutator_mono le_sup_left le_sup_left).trans hAA)
  have hvW : d.v ∈ normalizer (d.W : Set X) :=
    d.leviLong_le_normalizer_W d.v_mem_leviLong
  have hx₃ : ∀ c : d.Γ, ∃ w₀ ∈ d.W, d.x₃ c = ⁅d.x₁ c, d.x₂ 1⁆ * w₀⁻¹ := by
    intro c
    have hc := d.comm₁₂ c 1
    have h1 : c * ((1 : d.Γ₀) : d.Γ) = c := by simp
    rw [h1] at hc
    refine ⟨_, mul_mem (d.x₄_mem_W (d.σ c * d.σ (d.σ c) * ((1 : d.Γ₀) : d.Γ)))
      (d.x₅_mem_W (fixedNorm d.σ_cube c * 1)), ?_⟩
    rw [hc]
    simp only [mul_one]
    group
  have hx₃C : ∀ c : d.Γ, d.x₃ c ∈ C := by
    intro c
    obtain ⟨w₀, hw₀, e⟩ := hx₃ c
    rw [e]
    refine mul_mem (hAA ?_) (inv_mem (hWC hw₀))
    exact Subgroup.commutator_mem_commutator ((le_sup_right : d.M ≤ A) (d.x₁_mem_M c))
      ((le_sup_left : d.leviLong ≤ A) (d.x₂_mem_leviLong 1))
  have hx₁C : ∀ c : d.Γ, d.x₁ c ∈ C := by
    intro c
    obtain ⟨w₀, hw₀, e⟩ := hx₃ c
    have e1 : d.x₁ c = d.v * d.x₃ c * d.v⁻¹ := by rw [d.v_conj_x₃]
    have e2 : d.v * d.x₃ c * d.v⁻¹ = ⁅d.v * d.x₁ c * d.v⁻¹, d.v * d.x₂ 1 * d.v⁻¹⁆ *
        (d.v * w₀ * d.v⁻¹)⁻¹ := by
      rw [e]
      simp only [commutatorElement_def]
      group
    rw [e1, e2, d.v_conj_x₁]
    refine mul_mem (hAA ?_) (inv_mem (hWC ((mem_normalizer_iff.1 hvW w₀).1 hw₀)))
    refine Subgroup.commutator_mem_commutator
      ((le_sup_right : d.M ≤ A) (d.F_le_M (d.x₃_mem_F c))) ?_
    exact (le_sup_left : d.leviLong ≤ A) (mul_mem (mul_mem d.v_mem_leviLong
      (d.x₂_mem_leviLong 1)) (inv_mem d.v_mem_leviLong))
  have hFC : d.F ≤ C := sup_le (by rintro _ ⟨c, rfl⟩; exact hx₃C c) hWC
  have hMC : d.M ≤ C := sup_le (by rintro _ ⟨c, rfl⟩; exact hx₁C c) hFC
  exact sup_le hL hMC

end LSide

section Core

open NormalizerQuotient

theorem mem_normalizer_lift {G : Type*} [Group G] [Finite G] {W : Subgroup G}
    {Y : Subgroup (Bar W)} {g : G} (hg : g ∈ normalizer (W : Set G))
    (hgY : proj W ⟨g, hg⟩ ∈ normalizer (Y : Set (Bar W))) :
    g ∈ normalizer ((lift Y : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun n hn => ?_
  obtain ⟨hnN, hnY⟩ := mem_lift_iff.1 hn
  have hgnN : g * n * g⁻¹ ∈ normalizer (W : Set G) := mul_mem (mul_mem hg hnN) (inv_mem hg)
  refine mem_lift_iff.2 ⟨hgnN, ?_⟩
  have e : (⟨g * n * g⁻¹, hgnN⟩ : normalizer (W : Set G)) =
      ⟨g, hg⟩ * ⟨n, hnN⟩ * ⟨g, hg⟩⁻¹ := Subtype.ext (by simp)
  rw [e, map_mul, map_mul, map_inv]
  exact (mem_normalizer_iff.1 hgY _).1 hnY

theorem core_abstract {G : Type*} [Group G] [Finite G] {K M R : Subgroup G} {T : Type*} [Group T]
    [IsSimpleGroup T] (hT : ¬ IsPGroup 2 T) (hiso : IsQuotientIso (K ⊔ M) M T)
    (hKM : K ≤ normalizer (M : Set G)) (hR : R ≤ K ⊔ M) (hR2 : IsPGroup 2 R)
    (hRK : K ≤ normalizer (R : Set G)) : R ≤ M := by
  have hXM : K ⊔ M ≤ normalizer (M : Set G) := sup_le hKM le_normalizer
  have hCX : R ⊔ M ≤ K ⊔ M := sup_le hR le_sup_right
  have hCn : K ⊔ M ≤ normalizer ((R ⊔ M : Subgroup G) : Set G) := by
    refine sup_le (fun k hk => mem_normalizer_sup (hRK hk) (hKM hk)) ?_
    exact fun m hm => le_normalizer (mem_sup_right hm)
  rcases eq_or_eq_of_quotient_simple hiso le_sup_right hCX hCn with hC | hC
  · exact le_sup_left.trans hC.le
  · exfalso
    apply hT
    obtain ⟨φ, hφs, hφk⟩ := hiso
    have hsurj : Function.Surjective (φ.comp (Subgroup.inclusion hR)) := by
      intro y
      obtain ⟨x, rfl⟩ := hφs y
      have hx : (x : G) ∈ R ⊔ M := by rw [hC]; exact x.2
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right R M (hR.trans hXM)] at hx
      obtain ⟨r, hr, m, hm, hrm⟩ := hx
      refine ⟨⟨r, hr⟩, ?_⟩
      have hker : (⟨r, hR hr⟩ : ↥(K ⊔ M))⁻¹ * x ∈ φ.ker := by
        rw [hφk, mem_subgroupOf]
        show r⁻¹ * (x : G) ∈ M
        have : (x : G) = r * m := hrm.symm
        rw [this, inv_mul_cancel_left]
        exact hm
      have := MonoidHom.mem_ker.1 hker
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this
    exact hR2.of_surjective _ hsurj

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem not_isPGroup_SL (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) :
    ¬ IsPGroup 2 SL(2, d.Γ₀) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hSL : IsSimpleGroup SL(2, d.Γ₀) := isSimpleGroup_SL d hf
  haveI : Finite SL(2, d.Γ₀) := inferInstance
  haveI : Group.IsPerfect SL(2, d.Γ₀) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect
      (exists_finset_card_four (four_le_card_Γ₀ d hf))
  exact Group.IsPerfect.not_isNilpotent SL(2, d.Γ₀) h.isNilpotent

end Core

section LvFields

open NormalizerQuotient

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem M_map_le_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    d.M.map L.subtype ≤ yamadaM₆ d t := (M₆_inf_centralizer h d hp) ▸ inf_le_left

theorem lvM_le_nTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : lvM d ≤ nTwo d t := by
  show (d.leviLong ⊔ d.M).map L.subtype ≤ nThree d t ⊔ yamadaM₆ d t
  rw [Subgroup.map_sup]
  exact sup_le_sup (leviLong_map_le_nThree h d hp hK) (M_map_le_M₆ h d hp)

theorem lvM_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    lvM d ≤ normalizer (yamadaW₃ d t : Set G) :=
  (lvM_le_nTwo h d hp hK).trans (nTwo_le_normalizer_W₃ h d hp hK)

theorem D_map_le_lvM (d : TrialityD4Data L (2 ^ f)) : d.D.map L.subtype ≤ lvM d := by
  refine Subgroup.map_mono (sup_le (le_trans ?_ le_sup_left) (d.F_le_M.trans le_sup_right))
  rintro _ ⟨a, rfl⟩
  exact d.x₂_mem_leviLong a

theorem mul_conj_commute {Γ : Type*} [Group Γ] {t x : Γ} (ht : t * t = 1)
    (hc : x * (t⁻¹ * x * t) = (t⁻¹ * x * t) * x) :
    (x * (t⁻¹ * x * t)) * t = t * (x * (t⁻¹ * x * t)) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [hti] at hc ⊢
  calc x * (t * x * t) * t = x * t * x * (t * t) := by group
    _ = x * t * x := by rw [ht, mul_one]
    _ = (t * t) * x * t * x := by rw [ht, one_mul]
    _ = t * ((t * x * t) * x) := by group
    _ = t * (x * (t * x * t)) := by rw [hc]

theorem hat_Lv_N (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (lvM d) ≤ (bar (yamadaW₃ d t) (kThree d t K) ⊔
      (bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp]) ⊔ bar (yamadaW₃ d t) (yamadaM₆ d t) := by
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hK'W : (kThree d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree'_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hMW : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)
  obtain ⟨⟨-, -, -, -, hN3, -⟩, -⟩ := A3_structure h d hp hK
  rw [← bar_conjT h d hp hKW, ← bar_sup hKW hK'W, ← bar_sup (sup_le hKW hK'W) hMW]
  refine bar_mono ?_
  have e : nTwo d t = (kThree d t K ⊔ (kThree d t K)ᵍ[t]) ⊔ yamadaM₆ d t := by
    show nThree d t ⊔ yamadaM₆ d t = _
    rw [hN3]
  rw [← e]
  exact lvM_le_nTwo h d hp hK

theorem hat_Lv_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    bar (yamadaW₃ d t) (lvM d) ≤ centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t))) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy
  have hxL : (x : G) ∈ L := (Subgroup.map_subtype_le _ : lvM d ≤ L) hx
  exact proj_mem_centralizer_t h d hp (mem_centralizer_singleton_iff.1 (L_le_centralizer_t h hxL))

theorem hat_Lv_v (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    hatV h d ∈ bar (yamadaW₃ d t) (lvM d) :=
  proj_mem_bar (x := ⟨vG d, h.v_mem_normalizer_yamadaW₃ d⟩)
    ⟨d.v, mem_sup_left d.v_mem_leviLong, rfl⟩

theorem hat_Lv_Qs (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ q ∈ bar (yamadaW₃ d t) (qThree d t K),
      q * ((hatT h d hp)⁻¹ * q * hatT h d hp) ∈ bar (yamadaW₃ d t) (lvM d) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 hy
  obtain ⟨-, ⟨hXQ, -, hQcomm, -⟩, -⟩ := A2_sylow h d hp hK
  have htW := t_mem_normalizer_W₃ h d hp.layer
  have hxt : t⁻¹ * (x : G) * t ∈ prodX d t := by
    rw [hXQ]; exact mem_sup_right (conj_mem_map_conj_inv t hx)
  have hxX : (x : G) ∈ prodX d t := by rw [hXQ]; exact mem_sup_left hx
  have hc : (x : G) * (t⁻¹ * x * t) = (t⁻¹ * x * t) * x :=
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hQcomm hx) _
      (conj_mem_map_conj_inv t hx)).symm
  have hD : (x : G) * (t⁻¹ * x * t) ∈ yamadaD₅ d t ⊓ centralizer ({t} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem ((inf_le_left : prodX d t ≤ yamadaD₅ d t) hxX)
      ((inf_le_left : prodX d t ≤ yamadaD₅ d t) hxt), ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact mul_conj_commute h.t_mul_t hc
  obtain ⟨-, -, -, -, hDfix, -⟩ := T4_series_free h d hp
  rw [hDfix] at hD
  have hmem : (x : G) * (t⁻¹ * x * t) ∈ lvM d := D_map_le_lvM d hD
  have hN : (x : G) * (t⁻¹ * (x : G) * t) ∈ normalizer (yamadaW₃ d t : Set G) :=
    mul_mem x.2 (mul_mem (mul_mem (inv_mem htW) x.2) htW)
  have e : proj (yamadaW₃ d t) x * ((hatT h d hp)⁻¹ * proj (yamadaW₃ d t) x * hatT h d hp) =
      proj (yamadaW₃ d t) ⟨(x : G) * (t⁻¹ * x * t), hN⟩ := by
    rw [← proj_inv_t h d hp]
    unfold hatT
    rw [← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact proj_mem_bar hmem

theorem hat_Lv_M (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    bar (yamadaW₃ d t) (yamadaM₆ d t) ⊓
        centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t))) ≤
      bar (yamadaW₃ d t) (lvM d) := by
  rw [hat_Mfix h d hp]
  exact bar_mono (Subgroup.map_mono le_sup_right)

theorem hat_Lv_perf (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (lvM d) ≤ ⁅bar (yamadaW₃ d t) (lvM d), bar (yamadaW₃ d t) (lvM d)⁆ := by
  have hLN := lvM_le_normalizer_W₃ h d hp hK
  rw [← bar_commutator hLN hLN]
  have h1 := leviLong_sup_M_le_commutator d (four_le_card_Γ₀ d hp.two_le)
  have h2 : lvM d ≤ ⁅lvM d, lvM d⁆ ⊔ yamadaW₃ d t := by
    refine (Subgroup.map_mono h1).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_commutator]
    exact sup_le_sup_left (W_map_le_W₃ h d hp.layer) _
  have hCN : ⁅lvM d, lvM d⁆ ≤ normalizer (yamadaW₃ d t : Set G) :=
    (commutator_mono hLN hLN).trans (Subgroup.commutator_le_self _)
  have h4 := bar_mono (A := yamadaW₃ d t) h2
  rwa [bar_sup hCN le_normalizer, bar_self, sup_bot_eq] at h4

theorem hat_core (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ R : Subgroup (Bar (yamadaW₃ d t)),
      R ≤ bar (yamadaW₃ d t) (kThree d t K) ⊔ bar (yamadaW₃ d t) (yamadaM₆ d t) →
      IsPGroup 2 R → bar (yamadaW₃ d t) (kThree d t K) ≤ normalizer (R : Set (Bar (yamadaW₃ d t))) →
      R ≤ bar (yamadaW₃ d t) (yamadaM₆ d t) := by
  intro R hR hR2 hRn
  haveI hSL : IsSimpleGroup SL(2, d.Γ₀) := isSimpleGroup_SL d hp.two_le
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hK₂W := kTwo_le_normalizer_W₃ h d hp hK
  obtain ⟨-, ⟨-, -, hN3M, -⟩, -⟩ := A3_structure h d hp hK
  have hiso : IsQuotientIso (kThree d t K ⊔ yamadaM₆ d t) (yamadaM₆ d t) SL(2, d.Γ₀) :=
    (B1_proof h d hp hK).1.2.2.2.1
  have hKM : kThree d t K ≤ normalizer (yamadaM₆ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans hN3M
  have hW₃K : yamadaW₃ d t ≤ kTwo d t K := (W₃_le_M₆ h d hp.layer).trans le_sup_right
  have hRK2 : lift R ≤ kThree d t K ⊔ yamadaM₆ d t := by
    have h1 : lift R ≤ lift (bar (yamadaW₃ d t) (kTwo d t K)) :=
      lift_mono (by rwa [hat_bar_K₂ h d hp hK])
    rwa [lift_bar hW₃K hK₂W] at h1
  have hlift2 : IsPGroup 2 (lift R) :=
    isPGroup_lift_of ((isPGroup_M₆ d).to_le (W₃_le_M₆ h d hp.layer)) hR2
  have hkn : kThree d t K ≤ normalizer ((lift R : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_lift (hKW hk) (hRn (proj_mem_bar (x := ⟨k, hKW hk⟩) hk))
  have hle := core_abstract (not_isPGroup_SL d hp.two_le) hiso hKM hRK2 hlift2 hkn
  calc R = bar (yamadaW₃ d t) (lift R) := (bar_lift R).symm
    _ ≤ bar (yamadaW₃ d t) (yamadaM₆ d t) := bar_mono hle

theorem hatData_of (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    HatData (hatT h d hp) (hatV h d) (bar (yamadaW₃ d t) (kThree d t K))
      (bar (yamadaW₃ d t) (yamadaM₆ d t)) (bar (yamadaW₃ d t) (qThree d t K))
      (bar (yamadaW₃ d t) (yamadaF₄ d t)) (bar (yamadaW₃ d t) (lvM d))
      (bar (yamadaW₃ d t) (d.leviLong.map L.subtype ⊔ d.J.map L.subtype)) where
  t_sq := hat_t_sq h d hp
  v_sq := hat_v_sq h d
  vt := hat_vt h d hp
  M_comm := hat_M_comm h d hp
  M_two := hat_M_two d
  M_ne := hat_M_ne h d hp
  M_t := hat_M_t h d hp
  v_M := hat_v_M h d hp
  A_M := hat_A_M h d hp hK
  A_comm := hat_A_comm h d hp hK
  A_inf := hat_A_inf h d hp hK
  A_inf_M := hat_A_inf_M h d hp hK
  c1 := hat_c1 h d hp hK
  Qs_A := hat_Qs_A h d hp hK
  Qs_two := hat_Qs_two h d hp hK
  v_dec := hat_v_dec h d hp hK
  gen := hat_gen h d hp hK
  F_ctr := hat_F_ctr h d hp hK
  F_t := hat_F_t h d hp
  F_inf := hat_F_inf h d hp
  M_F := hat_M_F h d hp
  free := hat_free h d hp
  L0_M := hat_L0_M h d hp hK
  L0_t := hat_L0_t h d hp
  L0_Z := hat_L0_Z h d hp hK
  irr := hat_irr h d hp hK
  Lv_N := hat_Lv_N h d hp hK
  Lv_t := hat_Lv_t h d hp
  Lv_v := hat_Lv_v h d
  Lv_Qs := hat_Lv_Qs h d hp hK
  Lv_M := hat_Lv_M h d hp
  Lv_perf := hat_Lv_perf h d hp hK
  core := hat_core h d hp hK

end LvFields

section Assembly

open NormalizerQuotient

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem kFour_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kFour d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
  sup_le ((comm_le_self _).trans (kTwo_le_normalizer_W₃ h d hp hK))
    ((kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK))

theorem W₃_le_kFour (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    (K : Subgroup G) : yamadaW₃ d t ≤ kFour d t K := by
  calc yamadaW₃ d t = ⁅yamadaM₆ d t, yamadaM₆ d t⁆ := (S5_commutator_M₆ h d hp.layer).symm
    _ ≤ ⁅kTwo d t K, kTwo d t K⁆ := commutator_mono le_sup_right le_sup_right
    _ ≤ kFour d t K := le_sup_left

theorem W₃_le_kFour' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    (K : Subgroup G) : yamadaW₃ d t ≤ (kFour d t K)ᵍ[t] := by
  have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) (W₃_le_kFour h d hp K)
  rwa [conjT_eq_self_of_mem_normalizer (t_mem_normalizer_W₃ h d hp.layer)] at this

theorem W₃_le_nTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaW₃ d t ≤ nTwo d t := (W₃_le_M₆ h d hp.layer).trans le_sup_right

theorem hat_bar_nTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (nTwo d t) = (bar (yamadaW₃ d t) (kThree d t K) ⊔
      (bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp]) ⊔ bar (yamadaW₃ d t) (yamadaM₆ d t) := by
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hK'W : (kThree d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree'_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hMW : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)
  obtain ⟨⟨-, -, -, -, hN3, -⟩, -⟩ := A3_structure h d hp hK
  have e : nTwo d t = (kThree d t K ⊔ (kThree d t K)ᵍ[t]) ⊔ yamadaM₆ d t := by
    show nThree d t ⊔ yamadaM₆ d t = _
    rw [hN3]
  rw [e, bar_sup (sup_le hKW hK'W) hMW, bar_sup hKW hK'W, bar_conjT h d hp hKW]

theorem hat_bar_kFour (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    bar (yamadaW₃ d t) (kFour d t K) = hOf (hatT h d hp) (bar (yamadaW₃ d t) (kThree d t K))
      (bar (yamadaW₃ d t) (yamadaM₆ d t)) := by
  have hK₂W := kTwo_le_normalizer_W₃ h d hp hK
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hCN : ⁅kTwo d t K, kTwo d t K⁆ ≤ normalizer (yamadaW₃ d t : Set G) :=
    (comm_le_self _).trans hK₂W
  show bar (yamadaW₃ d t) (⁅kTwo d t K, kTwo d t K⁆ ⊔ kThree d t K) = _
  rw [bar_sup hCN hKW, bar_commutator hK₂W hK₂W, hat_bar_K₂ h d hp hK]
  exact (hatData_of h d hp hK).K₄_eq.1

theorem zKTwo_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    zKTwo d t K = lift (zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
      (bar (yamadaW₃ d t) (kThree d t K))) := by
  unfold zKTwo
  rw [centerMod_eq_lift, hat_center_K₂ h d hp hK]

theorem zKTwoT_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    zKTwoT d t K = lift (zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
      ((bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp])) := by
  unfold zKTwoT
  rw [centerMod_eq_lift, hat_center_K₂' h d hp hK]

theorem card_hat_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    Nat.card ↥(bar (yamadaW₃ d t) (yamadaM₆ d t)) = (2 ^ f) ^ 12 := by
  have hMN : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)
  have h1 := card_bar_mul (W₃_le_M₆ h d hp.layer) hMN
  obtain ⟨-, -, -, -, -, -, -, -, hM, -⟩ := T4_series_free h d hp
  rw [h.card_yamadaW₃ d hp.layer, hM] at h1
  have hpos : 0 < (2 ^ f) ^ 10 := by positivity
  have : Nat.card ↥(bar (yamadaW₃ d t) (yamadaM₆ d t)) * (2 ^ f) ^ 10 =
      (2 ^ f) ^ 12 * (2 ^ f) ^ 10 := by
    rw [h1, ← pow_add]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem card_Z₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    Nat.card ↥(zOf (bar (yamadaW₃ d t) (yamadaM₆ d t)) (bar (yamadaW₃ d t) (kThree d t K))) =
      (2 ^ f) ^ 6 := by
  have hD := hatData_of h d hp hK
  have hc := hD.M_eq_sup.2
  have hfree := hat_free h d hp
  rw [card_hat_M₆ h d hp] at hfree
  have h2 : ((2 ^ f) ^ 6) ^ 2 = Nat.card ↥(bar (yamadaW₃ d t) (yamadaM₆ d t) ⊓
      centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t)))) ^ 2 := by
    rw [← pow_mul]
    exact hfree
  rw [hc]
  exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2).symm

theorem C2_one_a (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaM₆ d t = zKTwo d t K ⊔ zKTwoT d t K := by
  have hD := hatData_of h d hp hK
  have hMN : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) :=
    (yamadaM₆_le_yamadaP d t).trans (h.yamadaP_le_normalizer_yamadaW₃_PA d hp.layer)
  rw [zKTwo_eq h d hp hK, zKTwoT_eq h d hp hK, ← lift_sup, ← hD.M_eq_sup.1,
    lift_bar (W₃_le_M₆ h d hp.layer) hMN]

theorem C2_one_b (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    zKTwo d t K ⊓ zKTwoT d t K = yamadaW₃ d t := by
  rw [zKTwo_eq h d hp hK, zKTwoT_eq h d hp hK, ← lift_inf, (hatData_of h d hp hK).Z_inf,
    lift_bot]

theorem relIndex_zKTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (yamadaW₃ d t).relIndex (zKTwo d t K) = (2 ^ f) ^ 6 := by
  rw [zKTwo_eq h d hp hK, relIndex_eq_card_bar (le_lift _) (lift_le_normalizer _), bar_lift]
  exact card_Z₁ h d hp hK

theorem relIndex_zKTwoT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (yamadaW₃ d t).relIndex (zKTwoT d t K) = (2 ^ f) ^ 6 := by
  rw [zKTwoT_eq h d hp hK, relIndex_eq_card_bar (le_lift _) (lift_le_normalizer _), bar_lift,
    (hatData_of h d hp hK).Z₂_eq,
    Subgroup.card_map_of_injective (fun a b hab => (MulAut.conj (hatT h d hp)⁻¹).injective hab)]
  exact card_Z₁ h d hp hK

theorem C2_two_a (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nTwo d t = kFour d t K ⊔ (kFour d t K)ᵍ[t] := by
  have htW := t_mem_normalizer_W₃ h d hp.layer
  have hkN := kFour_le_normalizer_W₃ h d hp hK
  have hkN' : (kFour d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) :=
    map_conj_le_normalizer (inv_mem htW) hkN
  refine eq_of_bar_eq (W₃_le_nTwo h d hp) (nTwo_le_normalizer_W₃ h d hp hK)
    ((W₃_le_kFour h d hp K).trans le_sup_left) (sup_le hkN hkN') ?_
  rw [bar_sup hkN hkN', bar_conjT h d hp hkN, hat_bar_nTwo h d hp hK, hat_bar_kFour h d hp hK]
  exact (hatData_of h d hp hK).prod_decomp.1

theorem C2_two_b (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kFour d t K ⊓ (kFour d t K)ᵍ[t] = yamadaW₃ d t := by
  have hkN := kFour_le_normalizer_W₃ h d hp hK
  refine eq_of_bar_eq (le_inf (W₃_le_kFour h d hp K) (W₃_le_kFour' h d hp K))
    (inf_le_left.trans hkN) le_rfl le_normalizer ?_
  rw [bar_inf (W₃_le_kFour h d hp K), bar_conjT h d hp hkN, hat_bar_kFour h d hp hK, bar_self]
  exact (hatData_of h d hp hK).prod_decomp.2.1

theorem C2_two_c (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ⁅kFour d t K, (kFour d t K)ᵍ[t]⁆ ≤ yamadaW₃ d t := by
  have htW := t_mem_normalizer_W₃ h d hp.layer
  have hkN := kFour_le_normalizer_W₃ h d hp hK
  have hkN' : (kFour d t K)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) :=
    map_conj_le_normalizer (inv_mem htW) hkN
  refine le_of_bar_eq_bot ((commutator_mono hkN hkN').trans (comm_le_self _)) ?_
  rw [bar_commutator hkN hkN', bar_conjT h d hp hkN, hat_bar_kFour h d hp hK]
  exact (hatData_of h d hp hK).prod_decomp.2.2

theorem C2_two_d (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kFour d t K = kThree d t K ⊔ zKTwoT d t K := by
  have hkN := kFour_le_normalizer_W₃ h d hp hK
  have hKW : kThree d t K ≤ normalizer (yamadaW₃ d t : Set G) :=
    (kThree_le_nThree h d hp hK).trans (nThree_le_normalizer_W₃ h d hp hK)
  have hZ : zKTwoT d t K ≤ normalizer (yamadaW₃ d t : Set G) := by
    rw [zKTwoT_eq h d hp hK]; exact lift_le_normalizer _
  have hWZ : yamadaW₃ d t ≤ zKTwoT d t K := by
    rw [zKTwoT_eq h d hp hK]; exact le_lift _
  refine eq_of_bar_eq (W₃_le_kFour h d hp K) hkN (hWZ.trans le_sup_right) (sup_le hKW hZ) ?_
  rw [bar_sup hKW hZ, hat_bar_kFour h d hp hK, zKTwoT_eq h d hp hK, bar_lift]

theorem lvM_inf_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    lvM d ⊓ yamadaW₃ d t = d.W.map L.subtype := by
  obtain ⟨-, -, hW3, -⟩ := T4_series_free h d hp
  apply le_antisymm
  · intro z hz
    obtain ⟨hzl, hzW⟩ := Subgroup.mem_inf.1 hz
    have hzL : z ∈ L := (Subgroup.map_subtype_le _ : lvM d ≤ L) hzl
    rw [← hW3]
    exact Subgroup.mem_inf.2 ⟨hzW, mem_centralizer_singleton_iff.2
      (mem_centralizer_singleton_iff.1 (L_le_centralizer_t h hzL))⟩
  · intro z hz
    refine Subgroup.mem_inf.2 ⟨?_, W_map_le_W₃ h d hp.layer hz⟩
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, mem_sup_right (d.F_le_M (d.W_le_F hw)), rfl⟩

theorem W_map_le_lvM (d : TrialityD4Data L (2 ^ f)) : d.W.map L.subtype ≤ lvM d :=
  Subgroup.map_mono (d.W_le_F.trans (d.F_le_M.trans le_sup_right))

theorem C2_sectionIso (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    SectionIso (kFour d t K) (yamadaW₃ d t) (lvM d) (d.W.map L.subtype) := by
  have hD := hatData_of h d hp hK
  obtain ⟨-, e, -⟩ := hD.fixed_eq
  have hkN := kFour_le_normalizer_W₃ h d hp hK
  have h1 : IsQuotientIso (kFour d t K) (yamadaW₃ d t) ↥(bar (yamadaW₃ d t) (lvM d)) := by
    refine isQuotientIso_congr (isQuotientIso_bar_of_inf hkN
      (inf_of_le_right (W₃_le_kFour h d hp K))) ?_
    exact (MulEquiv.subgroupCongr (hat_bar_kFour h d hp hK)).trans e
  have h2 : IsQuotientIso (lvM d) (d.W.map L.subtype) ↥(bar (yamadaW₃ d t) (lvM d)) :=
    isQuotientIso_bar_of_inf (lvM_le_normalizer_W₃ h d hp hK) (lvM_inf_W₃ h d hp)
  exact sectionIso_of_isQuotientIso h1 h2

theorem C2_fixed (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nTwo d t ⊓ centralizer ({t} : Set G) = lvM d := by
  have hD := hatData_of h d hp hK
  have hfix := hD.fixed_eq.1
  rw [← hat_bar_nTwo h d hp hK] at hfix
  apply le_antisymm
  · intro x hx
    obtain ⟨hxN2, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxN : x ∈ normalizer (yamadaW₃ d t : Set G) := nTwo_le_normalizer_W₃ h d hp hK hxN2
    have h1 : proj (yamadaW₃ d t) ⟨x, hxN⟩ ∈ bar (yamadaW₃ d t) (nTwo d t) ⊓
        centralizer ({hatT h d hp} : Set (Bar (yamadaW₃ d t))) :=
      Subgroup.mem_inf.2 ⟨proj_mem_bar hxN2, proj_mem_centralizer_t h d hp
        (mem_centralizer_singleton_iff.1 hxC)⟩
    rw [hfix] at h1
    obtain ⟨ℓ, hℓ, hℓx⟩ := mem_bar_iff_exists.1 h1
    have hw : (ℓ : G)⁻¹ * x ∈ yamadaW₃ d t := proj_eq_proj_iff.1 hℓx
    have hℓL : (ℓ : G) ∈ L := (Subgroup.map_subtype_le _ : lvM d ≤ L) hℓ
    have hwC : (ℓ : G)⁻¹ * x ∈ centralizer ({t} : Set G) :=
      mul_mem (inv_mem (L_le_centralizer_t h hℓL)) hxC
    have hwW : (ℓ : G)⁻¹ * x ∈ lvM d := by
      have : (ℓ : G)⁻¹ * x ∈ d.W.map L.subtype := by
        obtain ⟨-, -, hW3, -⟩ := T4_series_free h d hp
        rw [← hW3]
        exact Subgroup.mem_inf.2 ⟨hw, hwC⟩
      exact W_map_le_lvM d this
    have e : x = (ℓ : G) * ((ℓ : G)⁻¹ * x) := by group
    rw [e]
    exact mul_mem hℓ hwW
  · exact le_inf (lvM_le_nTwo h d hp hK) (fun x hx =>
      L_le_centralizer_t h ((Subgroup.map_subtype_le _ : lvM d ≤ L) hx))

theorem C2_fixedMod (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nTwo d t ⊓ centralizerMod (yamadaW₃ d t) (zpowers t) = lvM d ⊔ yamadaW₃ d t := by
  have hD := hatData_of h d hp hK
  have hfix := hD.fixed_eq.1
  rw [← hat_bar_nTwo h d hp hK] at hfix
  have htW := t_mem_normalizer_W₃ h d hp.layer
  have hfix' : bar (yamadaW₃ d t) (nTwo d t) ⊓
      centralizer ({proj (yamadaW₃ d t) ⟨t, htW⟩} : Set (Bar (yamadaW₃ d t))) =
      bar (yamadaW₃ d t) (lvM d) := hfix
  rw [centralizerMod_zpowers htW]
  conv_lhs => rw [← lift_bar (W₃_le_nTwo h d hp) (nTwo_le_normalizer_W₃ h d hp hK)]
  rw [← lift_inf, hfix', lift_bar_eq_sup (lvM_le_normalizer_W₃ h d hp hK)]

theorem C2_two_h (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kFour d t K ≤ ⁅kFour d t K, kFour d t K⁆ ⊔ yamadaW₃ d t := by
  have hkN := kFour_le_normalizer_W₃ h d hp hK
  refine le_sup_of_bar_le hkN ?_
  rw [bar_commutator hkN hkN, hat_bar_kFour h d hp hK]
  exact (hatData_of h d hp hK).K₄_eq.2

theorem map_conj_lift (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    (Y : Subgroup (Bar (yamadaW₃ d t))) :
    (lift Y : Subgroup G)ᵍ[t] = lift (Yᵍ[hatT h d hp]) := by
  have htW := t_mem_normalizer_W₃ h d hp.layer
  have hN : (lift Y : Subgroup G) ≤ normalizer (yamadaW₃ d t : Set G) := lift_le_normalizer Y
  have h1 : bar (yamadaW₃ d t) ((lift Y : Subgroup G)ᵍ[t]) = Yᵍ[hatT h d hp] := by
    rw [bar_conjT h d hp hN, bar_lift]
  have hW1 : yamadaW₃ d t ≤ (lift Y : Subgroup G)ᵍ[t] := by
    have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) (le_lift (A := yamadaW₃ d t) Y)
    rwa [conjT_eq_self_of_mem_normalizer htW] at this
  have hN1 : (lift Y : Subgroup G)ᵍ[t] ≤ normalizer (yamadaW₃ d t : Set G) :=
    map_conj_le_normalizer (inv_mem htW) hN
  rw [← h1, lift_bar hW1 hN1]

theorem C2_pCore (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    pCoreOf 2 (kFour d t K) = zKTwoT d t K := by
  have hD := hatData_of h d hp hK
  obtain ⟨hZH, hZ2, hHn, hmax⟩ := hD.pcore_eq
  have hkN := kFour_le_normalizer_W₃ h d hp hK
  have hW2 : IsPGroup 2 (yamadaW₃ d t) := (isPGroup_M₆ d).to_le (W₃_le_M₆ h d hp.layer)
  have hWk := W₃_le_kFour h d hp K
  have hHbar := hat_bar_kFour h d hp hK
  rw [zKTwoT_eq h d hp hK]
  apply le_antisymm
  · have hRk : pCoreOf 2 (kFour d t K) ≤ kFour d t K := LieType.BorelTits.pCoreOf_le 2 _
    have hR2 : IsPGroup 2 (pCoreOf 2 (kFour d t K)) := LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hRn : kFour d t K ≤ normalizer ((pCoreOf 2 (kFour d t K) : Subgroup G) : Set G) :=
      LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hWR : yamadaW₃ d t ≤ pCoreOf 2 (kFour d t K) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWk hkN hW2
    have hRN : pCoreOf 2 (kFour d t K) ≤ normalizer (yamadaW₃ d t : Set G) := hRk.trans hkN
    have h1 : bar (yamadaW₃ d t) (pCoreOf 2 (kFour d t K)) ≤
        zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
          ((bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp]) := by
      refine hmax _ ?_ ?_ (isPGroup_bar hR2)
      · rw [← hHbar]; exact bar_mono hRk
      · rw [← hHbar]; exact bar_le_normalizer_bar hWR hRn
    calc pCoreOf 2 (kFour d t K) = lift (bar (yamadaW₃ d t) (pCoreOf 2 (kFour d t K))) :=
          (lift_bar hWR hRN).symm
      _ ≤ _ := lift_mono h1
  · have hl : lift (zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
        ((bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp])) ≤ kFour d t K := by
      have := lift_mono (A := yamadaW₃ d t) hZH
      rwa [← hHbar, lift_bar hWk hkN] at this
    have hn : kFour d t K ≤ normalizer ((lift (zOf (bar (yamadaW₃ d t) (yamadaM₆ d t))
        ((bar (yamadaW₃ d t) (kThree d t K))ᵍ[hatT h d hp])) : Subgroup G) : Set G) := by
      intro k hk
      have hkH : proj (yamadaW₃ d t) ⟨k, hkN hk⟩ ∈ hOf (hatT h d hp)
          (bar (yamadaW₃ d t) (kThree d t K)) (bar (yamadaW₃ d t) (yamadaM₆ d t)) := by
        rw [← hHbar]; exact proj_mem_bar hk
      exact mem_normalizer_lift (hkN hk) (hHn hkH)
    exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hl hn (isPGroup_lift_of hW2 hZ2)

theorem C2_kFour_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kFour d t K = kThree d t K ⊔ pCoreOf 2 (kFour d t K) := by
  rw [C2_pCore h d hp hK]
  exact C2_two_d h d hp hK

theorem C2_M₆_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaM₆ d t = pCoreOf 2 (kFour d t K) ⊔ pCoreOf 2 ((kFour d t K)ᵍ[t]) := by
  have e1 : pCoreOf 2 ((kFour d t K)ᵍ[t]) = (pCoreOf 2 (kFour d t K))ᵍ[t] :=
    LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj t⁻¹) (kFour d t K)
  have e2 : (zKTwoT d t K)ᵍ[t] = zKTwo d t K := by
    rw [zKTwoT_eq h d hp hK, map_conj_lift h d hp, (hatData_of h d hp hK).Z₂_t,
      ← zKTwo_eq h d hp hK]
  rw [e1, C2_pCore h d hp hK, e2, sup_comm]
  exact C2_one_a h d hp hK

theorem C2_proof (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (yamadaM₆ d t = zKTwo d t K ⊔ zKTwoT d t K ∧ zKTwo d t K ⊓ zKTwoT d t K = yamadaW₃ d t ∧
      (yamadaW₃ d t).relIndex (zKTwo d t K) = (2 ^ f) ^ 6 ∧
      (yamadaW₃ d t).relIndex (zKTwoT d t K) = (2 ^ f) ^ 6) ∧
    (nTwo d t = kFour d t K ⊔ (kFour d t K)ᵍ[t] ∧
      kFour d t K ⊓ (kFour d t K)ᵍ[t] = yamadaW₃ d t ∧
      ⁅kFour d t K, (kFour d t K)ᵍ[t]⁆ ≤ yamadaW₃ d t ∧
      kFour d t K = kThree d t K ⊔ zKTwoT d t K ∧
      SectionIso (kFour d t K) (yamadaW₃ d t) (lvM d) (d.W.map L.subtype) ∧
      nTwo d t ⊓ centralizer ({t} : Set G) = lvM d ∧
      nTwo d t ⊓ centralizerMod (yamadaW₃ d t) (zpowers t) = lvM d ⊔ yamadaW₃ d t ∧
      kFour d t K ≤ ⁅kFour d t K, kFour d t K⁆ ⊔ yamadaW₃ d t) ∧
    (yamadaW₃ d t ≤ kFour d t K ∧ kFour d t K = kThree d t K ⊔ pCoreOf 2 (kFour d t K) ∧
      yamadaM₆ d t = pCoreOf 2 (kFour d t K) ⊔ pCoreOf 2 ((kFour d t K)ᵍ[t]) ∧
      pCoreOf 2 (kFour d t K) = zKTwoT d t K) :=
  ⟨⟨C2_one_a h d hp hK, C2_one_b h d hp hK, relIndex_zKTwo h d hp hK, relIndex_zKTwoT h d hp hK⟩,
    ⟨C2_two_a h d hp hK, C2_two_b h d hp hK, C2_two_c h d hp hK, C2_two_d h d hp hK,
      C2_sectionIso h d hp hK, C2_fixed h d hp hK, C2_fixedMod h d hp hK, C2_two_h h d hp hK⟩,
    ⟨W₃_le_kFour h d hp K, C2_kFour_eq h d hp hK, C2_M₆_eq h d hp hK, C2_pCore h d hp hK⟩⟩

end Assembly

end ProductN2Aux

section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem B1_decomposition (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (nTwo d t = kTwo d t K ⊔ (kTwo d t K)ᵍ[t] ∧ kTwo d t K ⊓ (kTwo d t K)ᵍ[t] = yamadaM₆ d t ∧
      ⁅kTwo d t K, (kTwo d t K)ᵍ[t]⁆ ≤ yamadaM₆ d t ∧
      IsQuotientIso (kTwo d t K) (yamadaM₆ d t) (SL(2, d.Γ₀)) ∧
      SectionIso (kTwo d t K) (yamadaM₆ d t) (kThree d t K) (eOne d t K)) ∧
    (yamadaP d t ⊓ centralizer ((yamadaY₂ d t : Subgroup G) : Set G) = yamadaM₆ d t ∧
      ((yamadaM₆ d t).subgroupOf (yamadaP d t)).Characteristic ∧
      normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
        normalizer ((yamadaM₆ d t : Subgroup G) : Set G)) :=
  ProductN2Aux.B1_proof h d hp hK

theorem C2_decomposition (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (yamadaM₆ d t = zKTwo d t K ⊔ zKTwoT d t K ∧ zKTwo d t K ⊓ zKTwoT d t K = yamadaW₃ d t ∧
      (yamadaW₃ d t).relIndex (zKTwo d t K) = (2 ^ f) ^ 6 ∧
      (yamadaW₃ d t).relIndex (zKTwoT d t K) = (2 ^ f) ^ 6) ∧
    (nTwo d t = kFour d t K ⊔ (kFour d t K)ᵍ[t] ∧
      kFour d t K ⊓ (kFour d t K)ᵍ[t] = yamadaW₃ d t ∧
      ⁅kFour d t K, (kFour d t K)ᵍ[t]⁆ ≤ yamadaW₃ d t ∧
      kFour d t K = kThree d t K ⊔ zKTwoT d t K ∧
      SectionIso (kFour d t K) (yamadaW₃ d t) (lvM d) (d.W.map L.subtype) ∧
      nTwo d t ⊓ centralizer ({t} : Set G) = lvM d ∧
      nTwo d t ⊓ centralizerMod (yamadaW₃ d t) (zpowers t) = lvM d ⊔ yamadaW₃ d t ∧
      kFour d t K ≤ ⁅kFour d t K, kFour d t K⁆ ⊔ yamadaW₃ d t) ∧
    (yamadaW₃ d t ≤ kFour d t K ∧ kFour d t K = kThree d t K ⊔ pCoreOf 2 (kFour d t K) ∧
      yamadaM₆ d t = pCoreOf 2 (kFour d t K) ⊔ pCoreOf 2 ((kFour d t K)ᵍ[t]) ∧
      pCoreOf 2 (kFour d t K) = zKTwoT d t K) :=
  ProductN2Aux.C2_proof h d hp hK

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
