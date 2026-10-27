module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G4Hd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t : G} {T1 T2 : Subgroup G}

theorem sec8t84g4_comm_of_le (W : Sec8T84Wr G t T1 T2) {A B : Subgroup G} (hA : A ≤ T1)
    (hB : B ≤ T2) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a :=
  fun a ha b hb => W.comm a (hA ha) b (hB hb)

theorem sec8t84g4_inf_of_le (W : Sec8T84Wr G t T1 T2) {A B : Subgroup G} (hA : A ≤ T1)
    (hB : B ≤ T2) : A ⊓ B = ⊥ := by
  have h : A ⊓ B ≤ T1 ⊓ T2 := inf_le_inf hA hB
  rw [W.inf] at h
  exact le_bot_iff.mp h

theorem sec8t84g4_sup_decomp (W : Sec8T84Wr G t T1 T2) {A B : Subgroup G} (hA : A ≤ T1)
    (hB : B ≤ T2) {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hc := sec8t84g4_comm_of_le W hA hB
  have hd := sec8t84g4_inf_of_le W hA hB
  have hcoe : x = ((sec124SupEquiv hc hd) ⟨x, hx⟩).1 * ((sec124SupEquiv hc hd) ⟨x, hx⟩).2 := by
    rw [← sec124SupEquiv_symm_coe hc hd ((sec124SupEquiv hc hd) ⟨x, hx⟩),
      MulEquiv.symm_apply_apply]
  exact ⟨_, ((sec124SupEquiv hc hd) ⟨x, hx⟩).1.2, _, ((sec124SupEquiv hc hd) ⟨x, hx⟩).2.2, hcoe⟩

theorem sec8t84g4_sup_cent (W : Sec8T84Wr G t T1 T2) {A A2 : Subgroup G} (hA : A ≤ T1)
    (hA2 : A2 ≤ T2) (hs1 : ∀ a ∈ A, t * a * t⁻¹ ∈ A2) :
    (A ⊔ A2) ⊓ centralizer ({t} : Set G) = sec8t84g4_diagSub W A := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxA, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := sec8t84g4_sup_decomp W hA hA2 hxA
    have hxT : a * b ∈ (T1 ⊔ T2) ⊓ centralizer ({t} : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left (hA ha))
        (Subgroup.mem_sup_right (hA2 hb)), hxc⟩
    obtain ⟨a', ha', hx'⟩ := (sec8t84_wr_mem_cent W).mp hxT
    obtain ⟨hae, hbe⟩ := sec8t84_wr_unique W (hA ha) ha' (hA2 hb) (W.swap1 a' ha') hx'
    refine (sec8t84g4_mem_diagSub W).mpr ⟨a, Subgroup.mem_inf.mpr ⟨ha, hA ha⟩, ?_⟩
    rw [hbe, ← hae]
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (sec8t84g4_mem_diagSub W).mp hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left ha.1)
      (Subgroup.mem_sup_right (hs1 a ha.1)), (sec8t84g4_diagSub_le W A hx).2⟩

theorem sec8t84g4_conj_cent {γ : G} (hγt : γ * t = t * γ) {a : G}
    (ha : a ∈ centralizer ({γ} : Set G)) : t * a * t⁻¹ ∈ centralizer ({γ} : Set G) := by
  have hca : Commute a γ := Subgroup.mem_centralizer_singleton_iff.mp ha
  have hct : Commute γ t := hγt
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    ((hct.symm.mul_left hca).mul_left hct.symm.inv_left)

theorem sec8t84g4_mem_normalizer_of_involution {U : Subgroup G} (ht : t * t = 1)
    (h : ∀ x ∈ U, t * x * t⁻¹ ∈ U) : t ∈ normalizer (U : Set G) := by
  have hti : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h2 := h _ hx
  have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
      _ = x := by rw [ht, hti]; group
  rwa [e] at h2

theorem sec8t84g4_card_swap (ht : t * t = 1) {H K : Subgroup G}
    (h1 : ∀ a ∈ H, t * a * t⁻¹ ∈ K) (h2 : ∀ b ∈ K, t * b * t⁻¹ ∈ H) :
    Nat.card ↥K = Nat.card ↥H := by
  have hti : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
  refine Nat.card_congr
    { toFun := fun b => ⟨t * b * t⁻¹, h2 b b.2⟩
      invFun := fun a => ⟨t * a * t⁻¹, h1 a a.2⟩
      left_inv := fun b => Subtype.ext ?_
      right_inv := fun a => Subtype.ext ?_ }
  · show t * (t * (b : G) * t⁻¹) * t⁻¹ = b
    calc t * (t * (b : G) * t⁻¹) * t⁻¹ = (t * t) * (b : G) * (t⁻¹ * t⁻¹) := by group
      _ = b := by rw [ht, hti]; group
  · show t * (t * (a : G) * t⁻¹) * t⁻¹ = a
    calc t * (t * (a : G) * t⁻¹) * t⁻¹ = (t * t) * (a : G) * (t⁻¹ * t⁻¹) := by group
      _ = a := by rw [ht, hti]; group

theorem sec8t84g4_swap_cent_pair {U1 U2 : Subgroup G} (hs1 : ∀ a ∈ U1, t * a * t⁻¹ ∈ U2)
    (hs2 : ∀ b ∈ U2, t * b * t⁻¹ ∈ U1) {γ : G} (hγt : γ * t = t * γ) :
    (∀ a ∈ U1 ⊓ centralizer ({γ} : Set G), t * a * t⁻¹ ∈ U2 ⊓ centralizer ({γ} : Set G)) ∧
      ∀ b ∈ U2 ⊓ centralizer ({γ} : Set G), t * b * t⁻¹ ∈ U1 ⊓ centralizer ({γ} : Set G) :=
  ⟨fun a ha => Subgroup.mem_inf.mpr ⟨hs1 a ha.1, sec8t84g4_conj_cent hγt ha.2⟩,
    fun b hb => Subgroup.mem_inf.mpr ⟨hs2 b hb.1, sec8t84g4_conj_cent hγt hb.2⟩⟩

theorem sec8t84g4_elemAb2_swap (ht : t * t = 1) {C1 C2 : Subgroup G} {k : ℕ}
    (hc1 : ∀ a ∈ C1, t * a * t⁻¹ ∈ C2) (hc2 : ∀ b ∈ C2, t * b * t⁻¹ ∈ C1)
    (h : IsElemAb2 C1 k) : IsElemAb2 C2 k := by
  have hti : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
  have hC2eq : C2 = C1.map (MulAut.conj t).toMonoidHom := by
    ext b
    constructor
    · intro hb
      refine Subgroup.mem_map.mpr ⟨t * b * t⁻¹, hc2 b hb, ?_⟩
      show t * (t * b * t⁻¹) * t⁻¹ = b
      calc t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t⁻¹ * t⁻¹) := by group
        _ = b := by rw [ht, hti]; group
    · rintro hb
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      exact hc1 a ha
  refine ⟨?_, ?_⟩
  · rw [hC2eq]; exact h.1.map _
  · rw [sec8t84g4_card_swap ht hc1 hc2]; exact h.2

end CFSG.OddStandard.SmallF3.Omega
