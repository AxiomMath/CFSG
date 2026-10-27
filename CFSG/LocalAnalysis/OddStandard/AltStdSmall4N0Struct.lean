module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructHomo

public section

namespace CFSG.OddStandard.AltStdSmall4.N0

open Subgroup Equiv AltStdCycTwo

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} (hn : 8 ≤ n) (c : Config G L Q n θ z)
  (hF : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * w θ hn)
  {P O : Subgroup G} {s : G} (hS : SetupData θ hn z P O s) {T : Subgroup G}
  (hT : TData θ hn z P T s)

include c hF hS hT

private theorem exists_eq_mul_z {u : G} (hu : u ∈ P) (huT : u ∉ T) : ∃ t ∈ T, u = t * z := by
  obtain ⟨j, hj⟩ := (mem_E_iff θ hn _).1 (bz_mem_E hn c (P_le_N0 hn c hS hu))
  obtain ⟨t₁, ht₁, hb⟩ := hT.trans j
  have hy : t₁⁻¹ * u ∈ B0 θ hn z :=
    P_inv_mul_mem_B0 hn c hS (hT.le_P ht₁) hu (by rw [hb, hj])
  obtain ⟨i, h | h⟩ := (mem_B0_iff' hn c _).1 hy
  · exfalso
    apply huT
    have : u = t₁ * eps θ hn i := by rw [← h]; group
    rw [this]
    exact mul_mem ht₁ (hT.E_le (eps_mem_E θ hn i))
  · refine ⟨t₁ * eps θ hn i, mul_mem ht₁ (hT.E_le (eps_mem_E θ hn i)), ?_⟩
    have : u = t₁ * (z * eps θ hn i) := by rw [← h]; group
    rw [this, ← eps_comm_z hn c i, mul_assoc]

theorem TData.eq_of_abelian {U : Subgroup G} (hUP : U ≤ P)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU : Nat.card U = 64) : U = T := by
  classical
  by_cases hle : U ≤ T
  · apply Subgroup.eq_of_le_of_card_ge hle
    rw [hU, hT.card_eq hn c hF hS]
  exfalso
  obtain ⟨u, huU, huT⟩ := Set.not_subset.1 hle
  obtain ⟨t, ht, rfl⟩ := exists_eq_mul_z hn c hF hS hT (hUP huU) huT
  have hUT : ∀ x ∈ U, x ∈ T → x ∈ E θ hn := by
    intro x hxU hxT
    apply hT.cent x hxT
    have h1 := hUab x hxU _ huU
    have h2 : x * t = t * x := hT.comm hn c hF hS hxT ht
    calc x * z = t⁻¹ * (t * x) * z := by group
      _ = t⁻¹ * (x * t) * z := by rw [h2]
      _ = t⁻¹ * (x * (t * z)) := by group
      _ = t⁻¹ * (t * z * x) := by rw [h1]
      _ = z * x := by group
  let f : U → E θ hn × Bool := fun y =>
    if hy : (y : G) ∈ T then (⟨y, hUT y y.2 hy⟩, false)
    else (⟨y * (t * z)⁻¹, by
      obtain ⟨t', ht', hy'⟩ := exists_eq_mul_z hn c hF hS hT (hUP y.2) hy
      apply hUT _ (mul_mem y.2 (inv_mem huU))
      rw [hy']
      have : t' * z * (t * z)⁻¹ = t' * t⁻¹ := by group
      rw [this]
      exact mul_mem ht' (inv_mem ht)⟩, true)
  have hf : Function.Injective f := by
    intro y y' h
    by_cases hy : (y : G) ∈ T <;> by_cases hy' : (y' : G) ∈ T <;>
      simp only [f, hy, hy', dif_pos, dif_neg, not_false_eq_true, Prod.mk.injEq,
        Bool.false_eq_true, Bool.true_eq_false, and_false, and_true] at h
    · simpa using congrArg (fun e : E θ hn => (e : G)) h
    · simpa using congrArg (fun e : E θ hn => (e : G)) h
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, card_E, hU, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  omega

theorem TData.normal {g : G} (hg : g ∈ N0 θ hn z) {x : G} (hx : x ∈ T) :
    g * x * g⁻¹ ∈ T ⊔ AltStdSec.oddCoreOf (N0 θ hn z) := by
  obtain ⟨d, hd, hdN⟩ := hS.frattini g hg
  set h := d⁻¹ * g with hh
  have hdN0 : d ∈ N0 θ hn z := (Subgroup.mem_inf.1 hd).1
  have hT' : T.map (MulAut.conj h).toMonoidHom = T := by
    apply hT.eq_of_abelian hn c hF hS
    · rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hdN y).1 (hT.le_P hy)
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show h * y * h⁻¹ * (h * y' * h⁻¹) = h * (y * y') * h⁻¹ by group,
        hT.comm hn c hF hS hy hy']
      group
    · rw [card_map_of_injective (MulAut.conj h).injective, hT.card_eq hn c hF hS]
  have hhx : h * x * h⁻¹ ∈ T := by
    rw [← hT']
    exact ⟨x, hx, rfl⟩
  obtain ⟨p, hp, o, ho, rfl⟩ := hS.decomp d hd
  have hOle : O ≤ AltStdSec.oddCoreOf (N0 θ hn z) :=
    le_oddCoreOf (fun _ ho => C0_le_N0 hn c (hS.O_le ho)) hS.O_norm hS.O_odd
  set t := h * x * h⁻¹ with htdef
  have htN : t ∈ N0 θ hn z := P_le_N0 hn c hS (hT.le_P hhx)
  have hpN : p ∈ N0 θ hn z := P_le_N0 hn c hS hp
  have ho' : o * (t * o⁻¹ * t⁻¹) ∈ O := mul_mem ho (hS.O_norm t htN _ (inv_mem ho))
  have h1 : g * x * g⁻¹ = (p * (o * (t * o⁻¹ * t⁻¹)) * p⁻¹) * (p * t * p⁻¹) := by
    rw [htdef, hh]; group
  rw [h1]
  exact mul_mem (mem_sup_right (hOle (hS.O_norm p hpN _ ho'))) (mem_sup_left (hT.conj_P p hp t hhx))

theorem TData.gen {g : G} (hg : g ∈ N0 θ hn z) :
    g ∈ T ⊔ AltStdSec.oddCoreOf (N0 θ hn z) ⊔ centralizer ({z} : Set G) := by
  obtain ⟨j, hj⟩ := conj_z_eq hn c hg
  obtain ⟨t, ht, htj⟩ := hT.trans j
  have htz : t * z * t⁻¹ = z * eps θ hn j := by
    rw [← eps_comm_z hn c j, ← htj, bz]
    group
  have hc : t⁻¹ * g ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc t⁻¹ * g * z = t⁻¹ * (g * z * g⁻¹) * g := by group
      _ = t⁻¹ * (t * z * t⁻¹) * g := by rw [hj, htz]
      _ = z * (t⁻¹ * g) := by group
  have : g = t * (t⁻¹ * g) := by group
  rw [this]
  exact mul_mem (mem_sup_left (mem_sup_left ht)) (mem_sup_right hc)

theorem TData.n0Data : N0Data θ hn z T where
  le := fun _ hx => P_le_N0 hn c hS (hT.le_P hx)
  homo := hT.homo hn c hF hS
  E_le := hT.E_le
  cent := hT.inf_cent hn c hF hS
  norm := by
    apply mem_normalizer_fintype
    intro x hx
    exact hT.conj_P z (hS.B0_le (z_mem_B0 hn c)) x hx
  normal := fun _ hg _ hx => hT.normal hn c hF hS hg hx
  gen := fun _ hg => hT.gen hn c hF hS hg

end CFSG.OddStandard.AltStdSmall4.N0

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup N0

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} (hn : 8 ≤ n) (c : Config G L Q n θ z)
  (hF : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * w θ hn)

include c hF in
theorem exists_n0Data : ∃ T : Subgroup G, N0Data θ hn z T := by
  obtain ⟨P, O, s, hS⟩ := exists_setup hn c hF
  obtain ⟨T, hT⟩ := exists_T hn c hF hS
  exact ⟨T, hT.n0Data hn c hF hS⟩

theorem sec4N0Struct_holds : Sec4N0Struct := by
  intro G _ _ L Q n θ z c hF
  exact exists_n0Data c.hn8 c hF

end CFSG.OddStandard.AltStdSmall4
