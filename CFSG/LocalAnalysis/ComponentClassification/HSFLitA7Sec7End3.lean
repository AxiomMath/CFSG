module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7End2
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2i

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem fixY_mul {x x' : X} (hx : x ∈ C.S₂) (hx' : x' ∈ C.S₂) :
    (x * x') * C.F.yF * (x * x')⁻¹ = C.F.yF ↔
      (x * C.F.yF * x⁻¹ = C.F.yF ↔ x' * C.F.yF * x'⁻¹ = C.F.yF) := by
  have hzy : S.z * C.F.yF ≠ C.F.yF := fun h => S.z_ne_one (by simpa using h)
  have e : (x * x') * C.F.yF * (x * x')⁻¹ = x * (x' * C.F.yF * x'⁻¹) * x⁻¹ := by group
  rw [e]
  rcases C.S₂_y hx' with h' | h' <;> rw [h']
  · simp
  · rw [conj_mul_eq, C.S₂_z hx]
    rcases C.S₂_y hx with h | h <;> rw [h]
    · simp [hzy]
    · rw [← mul_assoc, zz S, one_mul]
      simp [hzy]

theorem fixV_mul {x x' : X} (hx : x ∈ C.S₂) (hx' : x' ∈ C.S₂) :
    (x * x') * C.v' * (x * x')⁻¹ = C.v' ↔
      (x * C.v' * x⁻¹ = C.v' ↔ x' * C.v' * x'⁻¹ = C.v') := by
  have hkv : C.F.kF * C.v' ≠ C.v' := fun h => C.ne_one_k (by simpa using h)
  have e : (x * x') * C.v' * (x * x')⁻¹ = x * (x' * C.v' * x'⁻¹) * x⁻¹ := by group
  rw [e]
  rcases C.S₂_v' hx' with h' | h' <;> rw [h']
  · simp
  · rw [conj_mul_eq, C.S₂_k hx]
    rcases C.S₂_v' hx with h | h <;> rw [h]
    · simp [hkv]
    · rw [← mul_assoc, C.kk, one_mul]
      simp [hkv]

theorem fixY_inv {x : X} : x⁻¹ * C.F.yF * x⁻¹⁻¹ = C.F.yF ↔ x * C.F.yF * x⁻¹ = C.F.yF := by
  constructor <;> intro h
  · calc x * C.F.yF * x⁻¹ = x * (x⁻¹ * C.F.yF * x⁻¹⁻¹) * x⁻¹ := by rw [h]
      _ = C.F.yF := by group
  · calc x⁻¹ * C.F.yF * x⁻¹⁻¹ = x⁻¹ * (x * C.F.yF * x⁻¹) * x⁻¹⁻¹ := by rw [h]
      _ = C.F.yF := by group

theorem fixV_inv {x : X} : x⁻¹ * C.v' * x⁻¹⁻¹ = C.v' ↔ x * C.v' * x⁻¹ = C.v' := by
  constructor <;> intro h
  · calc x * C.v' * x⁻¹ = x * (x⁻¹ * C.v' * x⁻¹⁻¹) * x⁻¹ := by rw [h]
      _ = C.v' := by group
  · calc x⁻¹ * C.v' * x⁻¹⁻¹ = x⁻¹ * (x * C.v' * x⁻¹) * x⁻¹⁻¹ := by rw [h]
      _ = C.v' := by group

theorem swap_fixY {g : X} (hg : g ∈ normalizer (C.S₂ : Set X))
    (hz : g * S.z * g⁻¹ = C.F.kF) {x : X} (hx : x ∈ C.S₂) :
    (g * x * g⁻¹) * C.F.yF * (g * x * g⁻¹)⁻¹ = C.F.yF ↔ x * C.v' * x⁻¹ = C.v' := by
  have hgx : g * x * g⁻¹ ∈ C.S₂ := (mem_normalizer_iff.mp hg x).mp hx
  constructor
  · intro h
    have h1 := C.comm_conj_zpowers (inv_mem hg) ((C.fixY_iff hgx).mp h)
    rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group,
      show g⁻¹ * C.F.kF * g⁻¹⁻¹ = S.z by rw [← hz]; group] at h1
    exact (C.fixV_iff hx).mpr h1
  · intro h
    have h1 := C.comm_conj_zpowers hg ((C.fixV_iff hx).mp h)
    rw [hz] at h1
    exact (C.fixY_iff hgx).mpr h1

theorem swap_fixV {g : X} (hg : g ∈ normalizer (C.S₂ : Set X))
    (hk : g * C.F.kF * g⁻¹ = S.z) {x : X} (hx : x ∈ C.S₂) :
    (g * x * g⁻¹) * C.v' * (g * x * g⁻¹)⁻¹ = C.v' ↔ x * C.F.yF * x⁻¹ = C.F.yF := by
  have hgx : g * x * g⁻¹ ∈ C.S₂ := (mem_normalizer_iff.mp hg x).mp hx
  constructor
  · intro h
    have h1 := C.comm_conj_zpowers (inv_mem hg) ((C.fixV_iff hgx).mp h)
    rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group,
      show g⁻¹ * S.z * g⁻¹⁻¹ = C.F.kF by rw [← hk]; group] at h1
    exact (C.fixY_iff hx).mpr h1
  · intro h
    have h1 := C.comm_conj_zpowers hg ((C.fixY_iff hx).mp h)
    rw [hk] at h1
    exact (C.fixV_iff hgx).mpr h1

def V : Subgroup X where
  carrier := {x | x ∈ C.S₂ ∧ (x * C.F.yF * x⁻¹ = C.F.yF ↔ x * C.v' * x⁻¹ = C.v')}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨mul_mem ha hb, by rw [C.fixY_mul ha hb, C.fixV_mul ha hb, ha', hb']⟩
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨inv_mem ha, by rw [C.fixY_inv, C.fixV_inv]; exact ha'⟩

theorem mem_V {x : X} : x ∈ C.V ↔
    x ∈ C.S₂ ∧ (x * C.F.yF * x⁻¹ = C.F.yF ↔ x * C.v' * x⁻¹ = C.v') := by
  unfold V; rfl

theorem tau_not_fixY : ¬ C.tau * C.F.yF * C.tau⁻¹ = C.F.yF := fun h => S.z_ne_one (by
  rw [C.tau_y] at h; simpa using h)

theorem tau_not_fixV : ¬ C.tau * C.v' * C.tau⁻¹ = C.v' := fun h => C.ne_one_k (by
  rw [C.tau_v'] at h; simpa using h)

theorem V_eq : C.V = C.Q₂₀ ⊔ zpowers C.tau := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxS, hxe⟩ := C.mem_V.mp hx
    by_cases hy : x * C.F.yF * x⁻¹ = C.F.yF
    · exact mem_sup_left (C.mem_Q₂₀_of hxS hy (hxe.mp hy))
    · have hv : ¬ x * C.v' * x⁻¹ = C.v' := fun h => hy (hxe.mpr h)
      have hxt : x * C.tau⁻¹ ∈ C.S₂ := mul_mem hxS (inv_mem C.tau_mem)
      have hy' : (x * C.tau⁻¹) * C.F.yF * (x * C.tau⁻¹)⁻¹ = C.F.yF := by
        rw [C.fixY_mul hxS (inv_mem C.tau_mem), C.fixY_inv]
        exact iff_of_false hy C.tau_not_fixY
      have hv' : (x * C.tau⁻¹) * C.v' * (x * C.tau⁻¹)⁻¹ = C.v' := by
        rw [C.fixV_mul hxS (inv_mem C.tau_mem), C.fixV_inv]
        exact iff_of_false hv C.tau_not_fixV
      rw [show x = x * C.tau⁻¹ * C.tau by group]
      exact mul_mem (mem_sup_left (C.mem_Q₂₀_of hxt hy' hv')) (mem_sup_right (mem_zpowers _))
  · refine sup_le (fun x hx => C.mem_V.mpr ⟨hx.1, ?_⟩) (zpowers_le.mpr ?_)
    · exact iff_of_true (C.Q₂₀_F hx (mem_sup_left C.y_mem_E0))
        (C.Q₂₀_F hx (mem_sup_right (mem_zpowers _)))
    · exact C.mem_V.mpr ⟨C.tau_mem, iff_of_false C.tau_not_fixY C.tau_not_fixV⟩

theorem tau_not_mem_Q₂₀ : C.tau ∉ C.Q₂₀ := fun h =>
  C.tau_not_fixY (C.Q₂₀_F h (mem_sup_left C.y_mem_E0))

theorem card_V : Nat.card C.V = 512 := by
  rw [C.V_eq, card_sup_zpowers_eq (C.S₂_le_normalizer_Q₂₀ C.tau_mem)
    (by rw [pow_two, C.tau_tau]; exact one_mem _) C.tau_not_mem_Q₂₀, C.card_Q₂₀]

theorem V_le_S₂ : C.V ≤ C.S₂ := fun _ hx => (C.mem_V.mp hx).1

theorem not_conjTo_of_mem_V {x : X} (hx : x ∈ C.V) : ¬ ConjTo S.t x := by
  rw [C.V_eq] at hx
  rcases mem_or_of_mem_sup_zpowers (C.S₂_le_normalizer_Q₂₀ C.tau_mem)
    (by rw [pow_two, C.tau_tau]; exact one_mem _) hx with h | h
  · exact C.not_conjTo_of_mem_Q₂₀ h
  · rw [show x = x * C.tau⁻¹ * C.tau by group]
    exact C.not_conjTo_Q₂₀_tau h

theorem card_S₂' : Nat.card C.S₂ = 1024 := by rw [C.card_S₂, C.card_S₁]

section Transfer

variable (P : Sylow 2 X) (hSP : C.S₂ ≤ P)
include hSP

theorem exists_g' : ∃ g ∈ (P : Subgroup X), g ∉ C.S₂ ∧ g ∈ normalizer (C.S₂ : Set X) ∧
    g ^ 2 ∈ C.V ∧ ¬ g ^ 2 * C.F.yF * (g ^ 2)⁻¹ = C.F.yF := by
  have hP2 := P.isPGroup'
  obtain ⟨g, hgP, hgS, hgN⟩ := C.exists_g P hSP
  obtain ⟨hk, hz⟩ := C.swap_of_not_mem hP2 hSP hgP hgN hgS
  have hg2 : g ^ 2 ∈ C.S₂ := by
    have := C.mem_S₂_of_two hP2 hSP (inv_mem hgP) (inv_mem hgN)
      (fun h => hgS (by simpa using inv_mem h)) hgP hgN hgS
    rwa [inv_inv, ← pow_two] at this
  have hsw : g ^ 2 * C.F.yF * (g ^ 2)⁻¹ = C.F.yF ↔ g ^ 2 * C.v' * (g ^ 2)⁻¹ = C.v' := by
    have h := C.swap_fixY hgN hz hg2
    rwa [show g * g ^ 2 * g⁻¹ = g ^ 2 by group] at h
  by_cases hy : g ^ 2 * C.F.yF * (g ^ 2)⁻¹ = C.F.yF
  ·
    have hgtS : g * S.t ∉ C.S₂ := fun h => hgS (by
      simpa using mul_mem h (inv_mem C.t_mem_S₂))
    have hgtN : g * S.t ∈ normalizer (C.S₂ : Set X) := mul_mem hgN (le_normalizer C.t_mem_S₂)
    have hgt : g * S.t * g⁻¹ ∈ C.S₂ := (mem_normalizer_iff.mp hgN _).mp C.t_mem_S₂
    have e : (g * S.t) ^ 2 = (g * S.t * g⁻¹) * (g ^ 2 * S.t) := by
      rw [pow_two, pow_two]; group
    have hS : (g * S.t) ^ 2 ∈ C.S₂ := by rw [e]; exact mul_mem hgt (mul_mem hg2 C.t_mem_S₂)
    have hty : ¬ S.t * C.v' * S.t⁻¹ = C.v' := fun h => C.ne_one_k (by
      rw [C.t_v'] at h; simpa using h)
    have hy' : ¬ (g * S.t) ^ 2 * C.F.yF * ((g * S.t) ^ 2)⁻¹ = C.F.yF := by
      rw [e, C.fixY_mul hgt (mul_mem hg2 C.t_mem_S₂), C.fixY_mul hg2 C.t_mem_S₂,
        C.swap_fixY hgN hz C.t_mem_S₂]
      simp only [hy, C.t_y, iff_true]
      exact hty
    have hv' : ¬ (g * S.t) ^ 2 * C.v' * ((g * S.t) ^ 2)⁻¹ = C.v' := by
      rw [e, C.fixV_mul hgt (mul_mem hg2 C.t_mem_S₂), C.fixV_mul hg2 C.t_mem_S₂,
        C.swap_fixV hgN hk C.t_mem_S₂]
      simp only [C.t_y, hsw.mp hy, true_iff]
      exact hty
    exact ⟨g * S.t, mul_mem hgP (hSP C.t_mem_S₂), hgtS, hgtN,
      C.mem_V.mpr ⟨hS, iff_of_false hy' hv'⟩, hy'⟩
  · exact ⟨g, hgP, hgS, hgN, C.mem_V.mpr ⟨hg2, hsw⟩, hy⟩

end Transfer

include C in
theorem false_of_exc [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) : False := by
  obtain ⟨P, hSP⟩ := IsPGroup.exists_le_sylow C.isPGroup_S₂
  have hP2 := P.isPGroup'
  obtain ⟨g, hgP, hgS, hgN, hg2V, hg2y⟩ := C.exists_g' P hSP
  obtain ⟨hk, hz⟩ := C.swap_of_not_mem hP2 hSP hgP hgN hgS
  have hPN := C.P_le_normalizer P hSP
  have hgV : g ∈ normalizer (C.V : Set X) := mem_normalizer_of_map_le (by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hvS, hve⟩ := C.mem_V.mp hv
    show g * v * g⁻¹ ∈ C.V
    refine C.mem_V.mpr ⟨(mem_normalizer_iff.mp hgN v).mp hvS, ?_⟩
    rw [C.swap_fixY hgN hz hvS, C.swap_fixV hgN hk hvS]
    exact hve.symm)
  have hgnV : g ∉ C.V := fun h => hgS (C.V_le_S₂ h)
  have hcardM : Nat.card (C.V ⊔ zpowers g : Subgroup X) = 1024 := by
    rw [card_sup_zpowers_eq hgV hg2V hgnV, C.card_V]
  have hMP : C.V ⊔ zpowers g ≤ P := sup_le (C.V_le_S₂.trans hSP) (zpowers_le.mpr hgP)
  have hg2S : g ^ 2 ∈ C.S₂ := C.V_le_S₂ hg2V
  have hPeq : (P : Subgroup X) = C.S₂ ⊔ zpowers g := by
    apply le_antisymm
    · intro p hp
      by_cases hpS : p ∈ C.S₂
      · exact mem_sup_left hpS
      · have := C.mem_S₂_of_two hP2 hSP hgP hgN hgS hp (hPN hp) hpS
        rw [show p = g * (g⁻¹ * p) by group]
        exact mul_mem (mem_sup_right (mem_zpowers g)) (mem_sup_left this)
    · exact sup_le hSP (zpowers_le.mpr hgP)
  have hcardP : Nat.card (P : Subgroup X) = 2048 := by
    rw [hPeq, card_sup_zpowers_eq hgN hg2S hgS, C.card_S₂']
  have hidx : (C.V ⊔ zpowers g).relIndex P = 2 := by
    have h := Subgroup.relIndex_mul_card (C.V ⊔ zpowers g) (P : Subgroup X)
    rw [inf_eq_left.mpr hMP, hcardM, hcardP] at h
    omega
  have hMt : ∀ x : X, x⁻¹ * S.t * x ∉ C.V ⊔ zpowers g := by
    intro x hx
    have hc : ConjTo S.t (x⁻¹ * S.t * x) := ⟨x⁻¹, by group⟩
    rcases mem_or_of_mem_sup_zpowers hgV hg2V hx with h | h
    · exact C.not_conjTo_of_mem_V h hc
    · obtain ⟨v, hv, hcv⟩ : ∃ v ∈ C.V, x⁻¹ * S.t * x = v * g := ⟨_, h, by group⟩
      obtain ⟨hvS, hve⟩ := C.mem_V.mp hv
      have hgv : g * v * g⁻¹ ∈ C.S₂ := (mem_normalizer_iff.mp hgN v).mp hvS
      have e : (x⁻¹ * S.t * x) ^ 2 = v * ((g * v * g⁻¹) * g ^ 2) := by
        rw [hcv, pow_two, pow_two]; group
      have hy : ¬ (x⁻¹ * S.t * x) ^ 2 * C.F.yF * ((x⁻¹ * S.t * x) ^ 2)⁻¹ = C.F.yF := by
        rw [e, C.fixY_mul hvS (mul_mem hgv hg2S), C.fixY_mul hgv hg2S, C.swap_fixY hgN hz hvS]
        intro h'
        apply hg2y
        tauto
      exact hy (by rw [sq_of_conjTo hc]; group)
  obtain ⟨N, hN, hsq, htN⟩ :=
    CFSG.Quasithin.thompson_transfer_exists_normal P hMP hidx S.data.orderOf_t hMt
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · obtain ⟨a, b, hab⟩ := hnab
    have h1 : ∀ x : X, x * x = 1 := fun x => by
      have := hsq x
      rw [hbot, Subgroup.mem_bot] at this
      rw [← pow_two]; exact this
    apply hab
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (h1 (a * b))).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (h1 a), inv_eq_of_mul_eq_one_right (h1 b)]
  · exact htN (htop ▸ mem_top S.t)

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
