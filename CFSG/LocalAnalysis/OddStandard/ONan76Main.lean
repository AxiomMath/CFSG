module

public import CFSG.LocalAnalysis.OddStandard.ONan76Star
public import CFSG.Open.FusionDefs

public section

namespace CFSG.OddStandard.ONan76

open Subgroup CFSG.ABGLocalTools

theorem pow_pred_eq {G : Type*} [Group G] {n : ℕ} (hn : 3 ≤ n) (x : G) :
    x ^ 2 ^ (n - 1) = (x ^ 4) ^ 2 ^ (n - 3) ∧ x ^ 2 ^ (n - 1) = (x * x) ^ 2 ^ (n - 2) ∧
      x ^ 2 ^ (n - 2) = (x * x) ^ 2 ^ (n - 3) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← pow_mul, show 4 = 2 ^ 2 from rfl, ← pow_add]
    congr 2
    omega
  · rw [← pow_two, ← pow_mul, ← pow_succ']
    congr 2
    omega
  · rw [← pow_two, ← pow_mul, ← pow_succ']
    congr 2
    omega

namespace AlperinFrame

variable {G : Type*} [Group G] [Finite G] {n : ℕ} {v₁ v₂ v₃ s t : G}
  (hF : AlperinFrame n v₁ v₂ v₃ s t)

include hF

theorem false_of_cent (hn : 3 ≤ n) (hPs : IsSylowOf 2 hF.P ⊤) {a j k : G} (ha : a ∈ hF.V)
    (hao : a ^ 2 ^ (n - 1) ≠ 1) (hjP : j ∈ hF.P) (hja : j * a = a * j) (hjV : j ∉ hF.V)
    (hj2 : j * j = 1) (hka : k * a = a * k) (hkj : k * j * k⁻¹ ∈ hF.V) : False := by
  obtain ⟨x, hxV, hext, hxC⟩ := hF.exists_extremal hn hPs ha
  have hxV' := conj_inv_mem_of_conj_mem hxV
  have hjx := hxC j (mem_inf.2 ⟨hjP, mem_centralizer_singleton_iff.2 hja⟩)
  refine hF.false_of_extremal hn (hxV a ha) ?_ hext hjx ?_ ?_ (k := x * k * x⁻¹) ?_ ?_
  · rw [conj_pow]
    intro h
    apply hao
    calc a ^ 2 ^ (n - 1) = x⁻¹ * (x * a ^ 2 ^ (n - 1) * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hjV
    have := hxV' _ h
    rwa [show x⁻¹ * (x * j * x⁻¹) * x = j by group] at this
  · rw [show x * j * x⁻¹ * (x * j * x⁻¹) = x * (j * j) * x⁻¹ by group, hj2]
    group
  · rw [mem_centralizer_singleton_iff]
    calc x * k * x⁻¹ * (x * a * x⁻¹) = x * (k * a) * x⁻¹ := by group
      _ = x * (a * k) * x⁻¹ := by rw [hka]
      _ = x * a * x⁻¹ * (x * k * x⁻¹) := by group
  · rw [show x * k * x⁻¹ * (x * j * x⁻¹) * (x * k * x⁻¹)⁻¹ = x * (k * j * k⁻¹) * x⁻¹ by group]
    exact hxV _ hkj

theorem conj_mem_W (hn : 3 ≤ n) (hPs : IsSylowOf 2 hF.P ⊤) {w g : G}
    (hw : w ∈ hF.W (by omega)) (hgw : g⁻¹ * w * g ∈ hF.P) : g⁻¹ * w * g ∈ hF.W (by omega) := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hwV, hw2⟩ := (hF.mem_W_iff hn1).1 hw
  set j := g⁻¹ * w * g with hj
  have hj2 : j * j = 1 := by
    rw [hj, show g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g by group, hw2]
    group
  by_cases hjV : j ∈ hF.V
  · exact (hF.mem_W_iff hn1).2 ⟨hjV, hj2⟩
  exfalso
  have hgj : g * j * g⁻¹ ∈ hF.V := by
    rw [hj, show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
    exact hwV
  obtain ⟨g', hg'j, hg'U⟩ := hF.exists_conj_P hn hPs hgj
  obtain ⟨u₁, hu₁, u₂, hu₂W, hju₁, hju₂, hu₁o, hu₂1, hu₁₂, hH, -⟩ :=
    hF.inv_data hn2 hgw hjV hj2
  have hu₂V := ((hF.mem_W_iff hn1).1 hu₂W).1
  have hu₂2 := ((hF.mem_W_iff hn1).1 hu₂W).2
  have hB : ∀ u ∈ hF.V, u * j = j * u → g' * u * g'⁻¹ ∈ hF.V → u ^ 2 ^ (n - 1) = 1 := by
    intro u hu huj hgu
    by_contra huo
    obtain ⟨m, hmV, hmu⟩ := hF.exists_normalizer_conj hn hPs hu hgu
    have hmV' := conj_inv_mem_of_conj_mem hmV
    refine hF.false_of_cent hn hPs hu huo hgw huj.symm hjV hj2 (k := m⁻¹ * g') ?_ ?_
    · calc m⁻¹ * g' * u = m⁻¹ * (g' * u * g'⁻¹) * g' := by group
        _ = m⁻¹ * (m * u * m⁻¹) * g' := by rw [hmu]
        _ = u * (m⁻¹ * g') := by group
    · rw [show m⁻¹ * g' * j * (m⁻¹ * g')⁻¹ = m⁻¹ * (g' * j * g'⁻¹) * m by group]
      exact hmV' _ hg'j
  set x₁ := g' * u₁ * g'⁻¹ with hx₁
  set x₂ := g' * u₂ * g'⁻¹ with hx₂
  set w' := g' * j * g'⁻¹ with hw'
  have hconj : ∀ a b : G, a * b = b * a → g' * a * g'⁻¹ * (g' * b * g'⁻¹) =
      g' * b * g'⁻¹ * (g' * a * g'⁻¹) := fun a b h => by
    rw [show g' * a * g'⁻¹ * (g' * b * g'⁻¹) = g' * (a * b) * g'⁻¹ by group, h]
    group
  have hconj_pow : ∀ (a : G) (m : ℕ), (g' * a * g'⁻¹) ^ m = g' * a ^ m * g'⁻¹ := fun a m =>
    conj_pow
  have hx₁P : x₁ ∈ hF.P := hg'U u₁ hu₁ hju₁.symm
  have hx₂P : x₂ ∈ hF.P := hg'U u₂ hu₂V hju₂.symm
  have hx₁V : x₁ ∉ hF.V := fun h => hu₁o (hB u₁ hu₁ hju₁.symm h)
  have hu₂e : u₂ ^ 2 ^ (n - 1) = 1 := by
    rw [show 2 ^ (n - 1) = 2 * 2 ^ (n - 2) by rw [← pow_succ']; congr 1; omega, pow_mul,
      pow_two, hu₂2, one_pow]
  have hx₁₂V : x₁ * x₂ ∉ hF.V := by
    intro h
    apply hu₁o
    have h12 := hB (u₁ * u₂) (mul_mem hu₁ hu₂V)
      (by rw [mul_assoc, ← hju₂, ← mul_assoc, ← hju₁, mul_assoc])
      (by rwa [show g' * (u₁ * u₂) * g'⁻¹ = x₁ * x₂ by rw [hx₁, hx₂]; group])
    rwa [(Commute.mul_pow (show Commute u₁ u₂ from hF.V_comm hn1 hu₁ hu₂V) _), hu₂e,
      mul_one] at h12
  have hw'V : w' ∈ hF.V := hg'j
  have hw'2 : w' * w' = 1 := by
    rw [hw', show g' * j * g'⁻¹ * (g' * j * g'⁻¹) = g' * (j * j) * g'⁻¹ by group, hj2]
    group
  have hw'W : w' ∈ hF.W hn1 := (hF.mem_W_iff hn1).2 ⟨hw'V, hw'2⟩
  have hw'1 : w' ≠ 1 := fun h => hjV (by
    have : j = 1 := by
      calc j = g'⁻¹ * w' * g' := by rw [hw']; group
        _ = 1 := by rw [h]; group
    rw [this]
    exact one_mem _)
  have hx₁w : x₁ * w' = w' * x₁ := hconj u₁ j hju₁.symm
  have hx₂w : x₂ * w' = w' * x₂ := hconj u₂ j hju₂.symm
  have hx₁x₂ : x₁ * x₂ = x₂ * x₁ := hconj u₁ u₂ (hF.V_comm hn1 hu₁ hu₂V)
  have hne : g' * u₁ ^ 2 ^ (n - 1) * g'⁻¹ ≠ w' := by
    intro h
    apply hjV
    have : j = u₁ ^ 2 ^ (n - 1) := by
      calc j = g'⁻¹ * w' * g' := by rw [hw']; group
        _ = u₁ ^ 2 ^ (n - 1) := by rw [← h]; group
    rw [this]
    exact pow_mem hu₁ _
  have hx₁ε : x₁ ^ 2 ^ (n - 1) = g' * u₁ ^ 2 ^ (n - 1) * g'⁻¹ := hconj_pow u₁ _
  have hx₁ε1 : x₁ ^ 2 ^ (n - 1) ≠ 1 := by
    rw [hx₁ε]
    intro h
    apply hu₁o
    calc u₁ ^ 2 ^ (n - 1) = g'⁻¹ * (g' * u₁ ^ 2 ^ (n - 1) * g'⁻¹) * g' := by group
      _ = 1 := by rw [h]; group
  have hx₁εε : x₁ ^ 2 ^ (n - 1) * x₁ ^ 2 ^ (n - 1) = 1 := by
    rw [hx₁ε, show g' * u₁ ^ 2 ^ (n - 1) * g'⁻¹ * (g' * u₁ ^ 2 ^ (n - 1) * g'⁻¹) =
      g' * (u₁ ^ 2 ^ (n - 1) * u₁ ^ 2 ^ (n - 1)) * g'⁻¹ by group, hF.mul_self_pow_pred hn1 hu₁]
    group
  obtain ⟨hp4, hp2, hp3⟩ := pow_pred_eq hn x₁
  by_cases hx₁2 : x₁ * x₁ ∈ hF.V
  · by_cases hx₂V : x₂ ∈ hF.V
    ·
      set H := hF.W hn1 ⊓ centralizer ({j} : Set G) with hHdef
      have hH4 : Nat.card H = 4 := by
        refine card_eq_four (a := u₁ ^ 2 ^ (n - 1)) (b := u₂) ?_ ?_ hu₁o hu₂1 hu₁₂.symm
          (hF.mul_self_pow_pred hn1 hu₁) fun x hx => ?_
        · refine mem_inf.2 ⟨(hF.mem_W_iff hn1).2 ⟨pow_mem hu₁ _,
            hF.mul_self_pow_pred hn1 hu₁⟩, mem_centralizer_singleton_iff.2 ?_⟩
          exact ((Commute.pow_right (show Commute j u₁ from hju₁) _).eq).symm
        · exact mem_inf.2 ⟨hu₂W, mem_centralizer_singleton_iff.2 hju₂.symm⟩
        · exact hH x (mem_inf.1 hx).1 (mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2).symm
      have hx₁εV : x₁ ^ 2 ^ (n - 1) ∈ hF.V := by rw [hp2]; exact pow_mem hx₁2 _
      set Y := hF.W hn1 ⊓ centralizer ({x₁} : Set G) with hYdef
      have hH'Y : H.map (MulAut.conj g').toMonoidHom ≤ Y := by
        rintro _ ⟨h, hh, rfl⟩
        obtain ⟨hhW, hhc⟩ := mem_inf.1 hh
        obtain ⟨hhV, hh2⟩ := (hF.mem_W_iff hn1).1 hhW
        show g' * h * g'⁻¹ ∈ Y
        have hV : g' * h * g'⁻¹ ∈ hF.V := by
          rcases hH h hhW (mem_centralizer_singleton_iff.1 hhc).symm with rfl | rfl | rfl | rfl
          · rw [mul_one, mul_inv_cancel]
            exact one_mem _
          · rw [← hx₁ε]
            exact hx₁εV
          · exact hx₂V
          · rw [show g' * (u₁ ^ 2 ^ (n - 1) * u₂) * g'⁻¹ =
              g' * u₁ ^ 2 ^ (n - 1) * g'⁻¹ * (g' * u₂ * g'⁻¹) by group, ← hx₁ε]
            exact mul_mem hx₁εV hx₂V
        refine mem_inf.2 ⟨(hF.mem_W_iff hn1).2 ⟨hV, ?_⟩, mem_centralizer_singleton_iff.2 ?_⟩
        · rw [show g' * h * g'⁻¹ * (g' * h * g'⁻¹) = g' * (h * h) * g'⁻¹ by group, hh2]
          group
        · exact hconj h u₁ (hF.V_comm hn1 hhV hu₁)
      have hw'Y : w' ∈ Y := mem_inf.2 ⟨hw'W, mem_centralizer_singleton_iff.2 hx₁w.symm⟩
      have hw'H : w' ∉ H.map (MulAut.conj g').toMonoidHom := by
        intro h
        rw [mem_map_conj, hw', show g'⁻¹ * (g' * j * g'⁻¹) * g' = j by group] at h
        exact hjV ((hF.mem_W_iff hn1).1 (mem_inf.1 h).1).1
      have hH'4 : Nat.card (H.map (MulAut.conj g').toMonoidHom) = 4 := by
        rw [card_map_of_injective (MulAut.conj g').injective, hH4]
      have hY8 : Nat.card Y ∣ 8 := hF.card_W hn1 ▸ card_dvd_of_le inf_le_left
      have hY4 : 4 ∣ Nat.card Y := hH'4 ▸ card_dvd_of_le hH'Y
      have hYW : Y = hF.W hn1 := by
        refine eq_of_le_of_card_ge inf_le_left ?_
        rw [hF.card_W hn1]
        obtain ⟨k, hk⟩ := hY4
        have hk0 : k ≠ 0 := fun h => by
          rw [h, mul_zero] at hk
          exact (Nat.card_pos (α := Y)).ne' hk
        have : Nat.card Y ≤ 8 := Nat.le_of_dvd (by norm_num) hY8
        by_contra hlt
        have hk1 : k = 1 := by omega
        apply hw'H
        have heq : H.map (MulAut.conj g').toMonoidHom = Y :=
          eq_of_le_of_card_ge hH'Y (by rw [hH'4, hk, hk1])
        rw [heq]
        exact hw'Y
      have hεW : vec v₁ v₂ v₃ ((2 ^ (n - 1), 0, 0) : Vec n) ∈ hF.W hn1 :=
        (hF.vec_mem_W_iff hn1).2 (by
          simp only [Prod.mk_add_mk, add_zero, Prod.mk_eq_zero, and_true]
          exact two_pow_pred_add_self hn1)
      have hεW' : vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n) ∈ hF.W hn1 :=
        (hF.vec_mem_W_iff hn1).2 (by
          simp only [Prod.mk_add_mk, add_zero, Prod.mk_eq_zero, true_and, and_true]
          exact two_pow_pred_add_self hn1)
      refine hx₁V (hF.mem_V_of_comm hn2 hx₁P ?_ ?_)
      · exact (mem_centralizer_singleton_iff.1 (mem_inf.1 (hYW ▸ hεW : _ ∈ Y)).2).symm
      · exact (mem_centralizer_singleton_iff.1 (mem_inf.1 (hYW ▸ hεW' : _ ∈ Y)).2).symm
    ·
      have hdV : x₁ ^ 2 ^ (n - 2) ∈ hF.V := by rw [hp3]; exact pow_mem hx₁2 _
      have hdd : x₁ ^ 2 ^ (n - 2) * x₁ ^ 2 ^ (n - 2) = x₁ ^ 2 ^ (n - 1) := by
        rw [← pow_add, ← two_mul, ← pow_succ']
        congr 2
        omega
      have hx₂2 : x₂ * x₂ ∈ hF.V := by
        rw [hx₂, show g' * u₂ * g'⁻¹ * (g' * u₂ * g'⁻¹) = g' * (u₂ * u₂) * g'⁻¹ by group, hu₂2,
          mul_one, mul_inv_cancel]
        exact one_mem _
      have hx₂inv : x₂⁻¹ = x₂ := inv_eq_of_mul_eq_one_right (by
        rw [hx₂, show g' * u₂ * g'⁻¹ * (g' * u₂ * g'⁻¹) = g' * (u₂ * u₂) * g'⁻¹ by group, hu₂2,
          mul_one, mul_inv_cancel])
      have h := hF.eq_sq_of_pair hn2 hx₁P hx₂P hx₁V hx₂V hx₁2 hx₂2 (by rwa [hx₂inv]) hdV
        (by rw [hdd]; exact hx₁ε1) ((Commute.pow_right (Commute.refl x₁) _).eq)
        ((Commute.pow_left (show Commute x₁ x₂ from hx₁x₂) _).eq.symm) hw'W hw'1 hx₁w hx₂w
      rw [hdd, hx₁ε] at h
      exact hne h.symm
  ·
    have hd₀V : x₁ ^ 2 ^ (n - 1) ∈ hF.V := by rw [hp4]; exact pow_mem (hF.pow_four_mem_V hn1 hx₁P) _
    have hd₀W : x₁ ^ 2 ^ (n - 1) ∈ hF.W hn1 := (hF.mem_W_iff hn1).2 ⟨hd₀V, hx₁εε⟩
    have h := hF.eq_of_sq_not_mem hn2 hx₁P hx₁2 hd₀W hw'W hx₁ε1 hw'1
      ((Commute.pow_right (Commute.refl x₁) _).eq) hx₁w
    rw [hx₁ε] at h
    exact hne h

end AlperinFrame

theorem stronglyClosed_of_alperinFrame {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    {n : ℕ} (hn : 3 ≤ n) {v₁ v₂ v₃ s t : G} (hF : AlperinFrame n v₁ v₂ v₃ s t)
    (hP : Subgroup.closure ({v₁, v₂, v₃, s, t} : Set G) = P) :
    CFSG.Open.fusionStronglyClosed
      {w | w ∈ Subgroup.closure ({v₁, v₂, v₃} : Set G) ∧ w * w = 1} (P : Subgroup G) := by
  have hPs : IsSylowOf 2 hF.P ⊤ := by
    rw [AlperinFrame.P, hP]
    exact isSylowOf_top P
  have hn1 : 1 ≤ n := by omega
  intro a ha g hga
  rw [← hP] at hga
  exact (hF.mem_W_iff hn1).1 (hF.conj_mem_W hn hPs (w := a) ((hF.mem_W_iff hn1).2 ha) hga)

end CFSG.OddStandard.ONan76
