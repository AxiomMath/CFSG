module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aVec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Pow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Inv
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Hyp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem z4o_swap_add : ∀ a b : Fin 5, a ≠ b → ∀ u : Fin 5 → ZMod 2,
    permVec (Equiv.swap a b) u + u = 0 ∨
      permVec (Equiv.swap a b) u + u = fun i => if i = a ∨ i = b then 1 else 0 := by
  unfold permVec
  decide +kernel

theorem z4o_count_false [Finite G] {V B : Subgroup G} (hV : IsZ4Pow4 V) (hBV : B ≤ V)
    (hB16 : Nat.card B = 2 ^ 4) (hB2 : ∀ b ∈ B, b * b = 1) {c e : G}
    (hcV : c ∈ normalizer (V : Set G)) (hinv : ∀ v ∈ V, (c * c) * v * (c * c)⁻¹ = v⁻¹)
    (he : ∀ b ∈ B, c * b * c⁻¹ * b⁻¹ = 1 ∨ c * b * c⁻¹ * b⁻¹ = e) : False := by
  have hc := sec124_z4_comm hV
  have hsq := sec124_z4_sq_mem hV hBV hB16 hB2
  have hmemB := sec124_z4_mem_of_sq hV hBV hB16 hB2
  have hroot := sec124_z4_root hV hBV hB2
  have hα : ∀ v ∈ V, c * v * c⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hcV v).mp hv
  have hα' : ∀ v ∈ V, c⁻¹ * v * c ∈ V := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcV) v).mp hv
    simpa using this
  obtain ⟨δ, hδ⟩ : ∃ δ : G → G, ∀ v, δ v = c * v * c⁻¹ * v⁻¹ := ⟨_, fun _ => rfl⟩
  have hδV : ∀ v ∈ V, δ v ∈ V := fun v hv => by rw [hδ]; exact mul_mem (hα v hv) (inv_mem hv)
  have hδmul : ∀ v ∈ V, ∀ w ∈ V, δ (v * w) = δ v * δ w := by
    intro v hv w hw
    rw [hδ, hδ, hδ]
    have h1 : c * w * c⁻¹ * w⁻¹ * v⁻¹ = v⁻¹ * (c * w * c⁻¹ * w⁻¹) :=
      hc _ (mul_mem (hα w hw) (inv_mem hw)) _ (inv_mem hv)
    calc c * (v * w) * c⁻¹ * (v * w)⁻¹
        = c * v * c⁻¹ * (c * w * c⁻¹ * w⁻¹ * v⁻¹) := by group
      _ = c * v * c⁻¹ * (v⁻¹ * (c * w * c⁻¹ * w⁻¹)) := by rw [h1]
      _ = c * v * c⁻¹ * v⁻¹ * (c * w * c⁻¹ * w⁻¹) := by group
  have hδδ : ∀ v ∈ V, δ (δ v) = (c * v * c⁻¹)⁻¹ * (c * v * c⁻¹)⁻¹ := by
    intro v hv
    rw [hδ v, hδ]
    have h2 : c * (c * v * c⁻¹ * v⁻¹) * c⁻¹ =
        ((c * c) * v * (c * c)⁻¹) * (c * v * c⁻¹)⁻¹ := by group
    rw [h2, hinv v hv]
    have h3 : (c * v * c⁻¹)⁻¹ * v = v * (c * v * c⁻¹)⁻¹ := hc _ (inv_mem (hα v hv)) _ hv
    calc v⁻¹ * (c * v * c⁻¹)⁻¹ * (c * v * c⁻¹ * v⁻¹)⁻¹
        = v⁻¹ * ((c * v * c⁻¹)⁻¹ * v) * (c * v * c⁻¹)⁻¹ := by group
      _ = v⁻¹ * (v * (c * v * c⁻¹)⁻¹) * (c * v * c⁻¹)⁻¹ := by rw [h3]
      _ = (c * v * c⁻¹)⁻¹ * (c * v * c⁻¹)⁻¹ := by group
  have hBδ : ∀ b ∈ B, ∃ v ∈ V, δ (δ v) = b := by
    intro b hb
    obtain ⟨a, haV, haa⟩ := hroot b hb
    refine ⟨c⁻¹ * a * c, hα' a haV, ?_⟩
    rw [hδδ _ (hα' a haV), show c * (c⁻¹ * a * c) * c⁻¹ = a by group]
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = b := by rw [haa]; exact inv_eq_of_mul_eq_one_right (hB2 b hb)
  have hδsq : ∀ v ∈ V, δ v * δ v = 1 ∨ δ v * δ v = e := by
    intro v hv
    rw [← hδmul v hv v hv, hδ]
    exact he _ (hsq v hv)
  have hδB : ∀ w ∈ B, δ w = 1 ∨ δ w = e := fun w hw => by rw [hδ]; exact he w hw
  obtain ⟨d, hd⟩ : ∃ d : G, ∀ w ∈ V, (w * w = 1 ∨ w * w = e) →
      δ w = 1 ∨ δ w = e ∨ δ w = d ∨ δ w = d * e := by
    by_cases hu : ∃ u ∈ V, u * u = e ∧ u ∉ B
    · obtain ⟨u, huV, hue, -⟩ := hu
      refine ⟨δ u, fun w hw hww => ?_⟩
      by_cases hwB : w ∈ B
      · rcases hδB w hwB with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · have hwe : w * w = e := hww.resolve_left fun h => hwB (hmemB w hw h)
        have huwV : u⁻¹ * w ∈ V := mul_mem (inv_mem huV) hw
        have huw : u⁻¹ * w ∈ B := by
          refine hmemB _ huwV ?_
          have hcomm : u⁻¹ * w = w * u⁻¹ := hc _ (inv_mem huV) _ hw
          calc u⁻¹ * w * (u⁻¹ * w) = u⁻¹ * (w * u⁻¹) * w := by group
            _ = u⁻¹ * (u⁻¹ * w) * w := by rw [hcomm]
            _ = (u * u)⁻¹ * (w * w) := by group
            _ = 1 := by rw [hue, hwe, inv_mul_cancel]
        have hδw : δ w = δ u * δ (u⁻¹ * w) := by
          rw [← hδmul u huV _ huwV, mul_inv_cancel_left]
        rcases hδB _ huw with h | h
        · exact Or.inr (Or.inr (Or.inl (by rw [hδw, h, mul_one])))
        · exact Or.inr (Or.inr (Or.inr (by rw [hδw, h])))
    · refine ⟨1, fun w hw hww => ?_⟩
      by_cases hwB : w ∈ B
      · rcases hδB w hwB with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exfalso
        rcases hww with h | h
        · exact hwB (hmemB w hw h)
        · exact hu ⟨w, hw, h, hwB⟩
  have hsub : (B : Set G) ⊆ ({1, e, d, d * e} : Set G) := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := hBδ b hb
    rcases hd (δ v) (hδV v hv) (hδsq v hv) with h | h | h | h <;> simp [h]
  have h4 : ({1, e, d, d * e} : Set G).ncard ≤ 4 := by
    have h1 := Set.ncard_insert_le (1 : G) ({e, d, d * e} : Set G)
    have h2 := Set.ncard_insert_le e ({d, d * e} : Set G)
    have h3 := Set.ncard_insert_le d ({d * e} : Set G)
    have h5 := Set.ncard_singleton (d * e)
    omega
  have hle : Nat.card B ≤ 4 :=
    calc Nat.card B = (B : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, e, d, d * e} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 4 := h4
  rw [hB16] at hle
  norm_num at hle

theorem z4o_not_sq_mul_t [Finite G] {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 E : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E) (F : Sec12Frame t L S)
    (hZ : IsZ4Pow4 (secV t S L E)) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : SecNatCoord φ (secB S L)) {c : G} (hc : c ∈ (secM t S L ⊓ L) ⊔ S) {a b : Fin 5}
    (hab : a ≠ b) (hcσ : SecActs φ c (Equiv.swap a b)) {b' : G} (hb' : b' ∈ secB S L)
    (hcc : c * c = b' * t) : False := by
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  have hE : IsSylow2Of E (secCMB t S L) := hctx.sylowE
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hE
  have hB2 : ∀ b ∈ secB S L, b * b = 1 := fun b hb => sec12E_B_sq F hb
  have hVc := sec124_z4_comm hZ
  have htinv := sec124_t_inv F hE hZ
  have hcV : c ∈ normalizer (secV t S L E : Set G) :=
    sec122_Yc_le_normalizer_V F hS.1 hctx.S_norm hctx.ML_norm hc
  refine z4o_count_false hZ hBV F.bdata.2.1 hB2
    (e := φ fun i => if i = a ∨ i = b then 1 else 0) hcV ?_ ?_
  · intro v hv
    rw [hcc]
    have hvb : b' * v⁻¹ = v⁻¹ * b' := hVc _ (hBV hb') _ (inv_mem hv)
    calc b' * t * v * (b' * t)⁻¹ = b' * (t * v * t⁻¹) * b'⁻¹ := by group
      _ = b' * v⁻¹ * b'⁻¹ := by rw [htinv v hv]
      _ = v⁻¹ * b' * b'⁻¹ := by rw [hvb]
      _ = v⁻¹ := by group
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := hφ.onto x hx
    have hinv : (φ u)⁻¹ = φ u :=
      inv_eq_of_mul_eq_one_right (hφ.mul_self_eq_one (hφ.mem u hu))
    rw [hcσ u hu, hinv, ← hφ.mul _ _ (isEvenVec_permVec _ hu) hu]
    rcases z4o_swap_add a b hab u with h | h
    · left
      rw [h, hφ.map_zero]
    · right
      rw [h]

end CFSG.OddStandard.SmallF3.Omega
