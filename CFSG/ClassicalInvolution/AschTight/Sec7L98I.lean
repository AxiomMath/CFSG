module

public import CFSG.ClassicalInvolution.AschTight.Sec7L98H
public import CFSG.ClassicalInvolution.AschTight.Sec7L98G

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_of_transposition_z {z j g b : G} (hgz : g * z * g⁻¹ = z) (hgj : g * j * g⁻¹ = z * j)
    (hgzj : g * (z * j) * g⁻¹ = j) (hbz : b * z * b⁻¹ = j) (hbj : b * j * b⁻¹ = z * j)
    (hbzj : b * (z * j) * b⁻¹ = z) :
    (g * b * g⁻¹ * b) * z = z * (g * b * g⁻¹ * b) ∧
      (g * b * g⁻¹ * b) * j = j * (g * b * g⁻¹ * b) := by
  have hgi : ∀ x y : G, g * x * g⁻¹ = y → g⁻¹ * y * g = x := fun x y h => by rw [← h]; group
  have h1 : (g * b * g⁻¹ * b) * z * (g * b * g⁻¹ * b)⁻¹ = z := by
    calc (g * b * g⁻¹ * b) * z * (g * b * g⁻¹ * b)⁻¹
        = g * (b * (g⁻¹ * (b * z * b⁻¹) * g) * b⁻¹) * g⁻¹ := by group
      _ = z := by rw [hbz, hgi _ _ hgzj, hbzj, hgz]
  have h2 : (g * b * g⁻¹ * b) * j * (g * b * g⁻¹ * b)⁻¹ = j := by
    calc (g * b * g⁻¹ * b) * j * (g * b * g⁻¹ * b)⁻¹
        = g * (b * (g⁻¹ * (b * j * b⁻¹) * g) * b⁻¹) * g⁻¹ := by group
      _ = j := by rw [hbj, hgi _ _ hgj, hbj, hgzj]
  exact ⟨Tor98.comm_of_conj_eq h1, Tor98.comm_of_conj_eq h2⟩

theorem comm_of_transposition_j {z j g b : G} (hgz : g * z * g⁻¹ = z * j) (hgj : g * j * g⁻¹ = j)
    (hgzj : g * (z * j) * g⁻¹ = z) (hbz : b * z * b⁻¹ = j) (hbj : b * j * b⁻¹ = z * j) :
    (g * b * g⁻¹ * b) * z = z * (g * b * g⁻¹ * b) ∧
      (g * b * g⁻¹ * b) * j = j * (g * b * g⁻¹ * b) := by
  have hgi : ∀ x y : G, g * x * g⁻¹ = y → g⁻¹ * y * g = x := fun x y h => by rw [← h]; group
  have h1 : (g * b * g⁻¹ * b) * z * (g * b * g⁻¹ * b)⁻¹ = z := by
    calc (g * b * g⁻¹ * b) * z * (g * b * g⁻¹ * b)⁻¹
        = g * (b * (g⁻¹ * (b * z * b⁻¹) * g) * b⁻¹) * g⁻¹ := by group
      _ = z := by rw [hbz, hgi _ _ hgj, hbj, hgzj]
  have h2 : (g * b * g⁻¹ * b) * j * (g * b * g⁻¹ * b)⁻¹ = j := by
    calc (g * b * g⁻¹ * b) * j * (g * b * g⁻¹ * b)⁻¹
        = g * (b * (g⁻¹ * (b * j * b⁻¹) * g) * b⁻¹) * g⁻¹ := by group
      _ = j := by rw [hbj, hgi _ _ hgz, hbz, hgj]
  exact ⟨Tor98.comm_of_conj_eq h1, Tor98.comm_of_conj_eq h2⟩

namespace Cfg98

variable {Ω : Set (Subgroup G)} {K J K' X P : Subgroup G} {z j : G} {S : Sylow 2 G}
  {W : Subgroup G} (c : Cfg98 Ω K J K' X P z j S W)
include c

theorem c1_mem_C [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W) {g b₂ : G}
    (hgL : g ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j)
    (hb₂L : b₂ ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j)
    (hb₂o : Odd (orderOf b₂))
    (hcz : (g * b₂ * g⁻¹ * b₂) * z = z * (g * b₂ * g⁻¹ * b₂))
    (hcj : (g * b₂ * g⁻¹ * b₂) * j = j * (g * b₂ * g⁻¹ * b₂)) :
    g * b₂ * g⁻¹ * b₂ ∈ Subgroup.centralizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  have hcL : g * b₂ * g⁻¹ * b₂ ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL hb₂L)
      (Subgroup.inv_mem _ hgL)) hb₂L
  have hb₂N := L98_le_normalizer Ω _ z j hb₂L
  rcases t.sign (c.L_le_Y t hu hv hcL) (t.mem_C_Z_of_comm hcz hcj)
      (L98_le_normalizer Ω _ z j hcL) with h | h
  · exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
      have := h w hw
      calc w * (g * b₂ * g⁻¹ * b₂) = (g * b₂ * g⁻¹ * b₂) * w * (g * b₂ * g⁻¹ * b₂)⁻¹ *
            (g * b₂ * g⁻¹ * b₂) := by rw [this]
        _ = (g * b₂ * g⁻¹ * b₂) * w := by group
  · exfalso
    have h1 := eq_inv_of_conj_inv hb₂N hb₂o h u (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
    apply t.u_sq_ne
    calc u * u = u * u⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel u

theorem part3_setup [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W)
    (hXU : ∀ x ∈ X, ∀ w ∈ W ⊓ K, x * w = w * x) :
    ∃ A : Subgroup G, ∃ b₂ : G, A ≤ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ⊔ X ∧
      (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ⊔ X =
        (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ⊔ A ∧
      (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ⊓ A = ⊥ ∧
      b₂ ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j ∧ Odd (orderOf b₂) ∧
      b₂ * z * b₂⁻¹ = j ∧ b₂ * j * b₂⁻¹ = z * j ∧ b₂ * (z * j) * b₂⁻¹ = z ∧
      (∀ a ∈ A, a * b₂ * a⁻¹ = b₂) := by
  set UV := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hUV
  set L := L98 Ω UV z j with hL
  set O₁ := oddCoreOf (L ⊓ Subgroup.centralizer (UV : Set G)) with hO₁
  have hXC := c.part2 t hu hv hXU
  have hXN : X ≤ Subgroup.normalizer (UV : Set G) := c.X_le_N_UV t hv
  have hN₀C : UV ⊔ X ≤ Subgroup.centralizer (UV : Set G) := by
    refine sup_le (fun w hw => Subgroup.mem_centralizer_iff.mpr fun y hy => t.UV_comm y hy w hw)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    have := hXC x hx y hy
    calc y * x = x * y * x⁻¹ * x := by rw [this]
      _ = x * y := by group
  have hN₀L : UV ⊔ X ≤ Subgroup.normalizer (L : Set G) :=
    sup_le ((c.UV_le_L t).trans Subgroup.le_normalizer) (c.X_le_N_L t hv)
  have hN₀O : UV ⊔ X ≤ Subgroup.normalizer (O₁ : Set G) := fun g hg =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_inf (hN₀L hg)
      (normalizer_le_normalizer_centralizer UV
        (Subgroup.centralizer_le_normalizer (UV : Set G) (hN₀C hg))))
  have hO₁C : O₁ ≤ Subgroup.centralizer (UV : Set G) := (oddCoreOf_le_self _).trans inf_le_right
  have hO₁L : O₁ ≤ L := (oddCoreOf_le_self _).trans inf_le_left
  obtain ⟨r, hrR, hru⟩ := t.exists_r
  obtain ⟨t₀, ht₀T, ht₀v⟩ := t.exists_t
  obtain ⟨hbo, hbz, hbj, hbzj⟩ := t.exists_b hrR hru ht₀T ht₀v
  set b := (r * t₀) ^ 4 ^ orderOf (r * t₀) with hb
  have hρL : r * t₀ ∈ L := Subgroup.mul_mem _ (c.R_le_L t hrR) (c.T_le_L t ht₀T)
  have hbL : b ∈ L := Subgroup.pow_mem _ hρL _
  have hbN := L98_le_normalizer Ω UV z j hbL
  have hbO : b ∈ Subgroup.normalizer (O₁ : Set G) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_inf (L.le_normalizer hbL)
      (normalizer_le_normalizer_centralizer UV hbN))
  have hbfp := t.fpf hbz hbj hbzj
  have hO1UV : O₁ ⊓ UV = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup (oddCoreOf_odd_natCard _) t.UV_isPGroup
  have hOW : ∀ o ∈ O₁, ∀ w ∈ UV, o * w = w * o := fun o ho w hw =>
    (Subgroup.mem_centralizer_iff.mp (hO₁C ho) w hw).symm
  obtain ⟨A, hA⟩ := exists_coset_stab hN₀O b
  have hAN₀ : A ≤ UV ⊔ X := fun g hg => ((hA g).mp hg).1
  have hN₀eq : UV ⊔ X = UV ⊔ A := by
    refine le_antisymm (fun g hg => ?_) (sup_le le_sup_left hAN₀)
    have hgL := hN₀L hg
    have hdL : g * b * g⁻¹ * b⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hgL b).mp hbL) (L.inv_mem hbL)
    have hdC : g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (UV : Set G) := by
      have hgC := Subgroup.mem_centralizer_iff.mp (hN₀C hg)
      have hgcomm : ∀ y ∈ UV, g * y * g⁻¹ = y := fun y hy => by
        have := hgC y hy
        rw [← this]; group
      have hginv : ∀ y ∈ UV, g⁻¹ * y * g = y := fun y hy => by
        have := hgcomm y hy
        calc g⁻¹ * y * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [this]
          _ = y := by group
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : b⁻¹ * w * b ∈ UV := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) w).mp hw
        rwa [inv_inv] at this
      have h1 : (g * b * g⁻¹ * b⁻¹) * w * (g * b * g⁻¹ * b⁻¹)⁻¹ = w := by
        calc (g * b * g⁻¹ * b⁻¹) * w * (g * b * g⁻¹ * b⁻¹)⁻¹
            = g * (b * (g⁻¹ * (b⁻¹ * w * b) * g) * b⁻¹) * g⁻¹ := by group
          _ = g * (b * (b⁻¹ * w * b) * b⁻¹) * g⁻¹ := by rw [hginv _ hw']
          _ = g * w * g⁻¹ := by group
          _ = w := hgcomm w hw
      exact (Tor98.comm_of_conj_eq h1).symm
    obtain ⟨o, ho, w, hw, hd⟩ := c.CL_decomp t hu hv hdL hdC
    obtain ⟨w', hw', hw'e⟩ := exists_mul_conj_inv_eq t.UV_comm
      (fun a ha => (Subgroup.mem_normalizer_iff.mp hbN a).mp ha) hbfp w⁻¹ (UV.inv_mem hw)
    have hg' : w' * g ∈ A := by
      rw [hA]
      refine ⟨(UV ⊔ X).mul_mem (Subgroup.mem_sup_left hw') hg, ?_⟩
      have hgb : g * b * g⁻¹ = o * w * b := by rw [← hd]; group
      have e : (w' * g) * b * (w' * g)⁻¹ = o * (w * (w' * (b * w' * b⁻¹)⁻¹)) * b := by
        calc (w' * g) * b * (w' * g)⁻¹ = w' * (g * b * g⁻¹) * w'⁻¹ := by group
          _ = w' * (o * w * b) * w'⁻¹ := by rw [hgb]
          _ = (w' * o) * w * b * w'⁻¹ := by group
          _ = (o * w') * w * b * w'⁻¹ := by rw [hOW o ho w' hw']
          _ = o * (w' * w) * b * w'⁻¹ := by group
          _ = o * (w * w') * b * w'⁻¹ := by rw [t.UV_comm w' hw' w hw]
          _ = o * (w * (w' * (b * w' * b⁻¹)⁻¹)) * b := by group
      rw [e, hw'e, show o * (w * w⁻¹) * b = o * b by group]
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbO) o).mp ho
      rw [inv_inv] at this
      rw [show b⁻¹ * (o * b) = b⁻¹ * o * b by group]
      exact this
    rw [show g = w'⁻¹ * (w' * g) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (UV.inv_mem hw')) (Subgroup.mem_sup_right hg')
  have hinf : UV ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro w ⟨hw, hwA⟩
    rw [Subgroup.mem_bot]
    have h1 := ((hA w).mp hwA).2
    have hbw : b⁻¹ * w * b ∈ UV := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) w).mp hw
      rwa [inv_inv] at this
    have h2 : b⁻¹ * (w * b * w⁻¹) ∈ O₁ ⊓ UV := ⟨h1, by
      rw [show b⁻¹ * (w * b * w⁻¹) = (b⁻¹ * w * b) * w⁻¹ by group]
      exact UV.mul_mem hbw (UV.inv_mem hw)⟩
    rw [hO1UV, Subgroup.mem_bot] at h2
    have h3 : b⁻¹ * w * b = w := by
      calc b⁻¹ * w * b = b⁻¹ * (w * b * w⁻¹) * w := by group
        _ = w := by rw [h2, one_mul]
    exact hbfp w hw (by
      calc b * w * b⁻¹ = b * (b⁻¹ * w * b) * b⁻¹ := by rw [h3]
        _ = w := by group)
  have hA2 : IsPGroup 2 A :=
    (IsPGroup.to_sup_of_normal_left' t.UV_isPGroup c.hX2 hXN).to_le hAN₀
  obtain ⟨o₀, ho₀, hfix⟩ := exists_fixed_mul_of_odd hA2 (oddCoreOf_odd_natCard _)
    (hAN₀.trans hN₀O) (fun h hh => ((hA h).mp hh).2)
  have ho₀C := Subgroup.mem_centralizer_iff.mp (hO₁C ho₀)
  have hconj : ∀ y ∈ UV, (b * o₀) * y * (b * o₀)⁻¹ = b * y * b⁻¹ := by
    intro y hy
    have := ho₀C y hy
    calc (b * o₀) * y * (b * o₀)⁻¹ = b * (o₀ * y * o₀⁻¹) * b⁻¹ := by group
      _ = b * y * b⁻¹ := by rw [show o₀ * y * o₀⁻¹ = y by rw [← this]; group]
  have hzUV : z ∈ UV := Subgroup.mem_sup_left t.z_mem_U
  have hjUV : j ∈ UV := Subgroup.mem_sup_right t.j_mem_V
  have hzjUV : z * j ∈ UV := UV.mul_mem hzUV hjUV
  have hb₂o : Odd (orderOf (b * o₀)) := by
    have hzb : Subgroup.zpowers b ≤ Subgroup.normalizer (O₁ : Set G) :=
      Subgroup.zpowers_le.mpr hbO
    have e1 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hzb
    have hmem : b * o₀ ∈ Subgroup.zpowers b ⊔ O₁ :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
        (Subgroup.mem_sup_right ho₀)
    have h1 : orderOf (b * o₀) ∣ Nat.card ↥(Subgroup.zpowers b ⊔ O₁) := by
      rw [← Subgroup.orderOf_mk _ hmem]
      exact orderOf_dvd_natCard _
    have h2 : Nat.card ↥(Subgroup.zpowers b ⊔ O₁) ∣ Nat.card (Subgroup.zpowers b) * Nat.card O₁ :=
      ⟨_, e1.symm⟩
    refine Odd.of_dvd_nat ?_ (h1.trans h2)
    rw [Nat.card_zpowers]
    exact hbo.mul (oddCoreOf_odd_natCard _)
  refine ⟨A, b * o₀, hAN₀, hN₀eq, hinf, L.mul_mem hbL (hO₁L ho₀), hb₂o, ?_, ?_, ?_,
    fun a ha => hfix a ha⟩
  · rw [hconj z hzUV]; exact hbz
  · rw [hconj j hjUV]; exact hbj
  · rw [hconj _ hzjUV]; exact hbzj

theorem mem_centralizerModOdd_sup [Finite G] {a : G} (haK : conjSub a K = K)
    (haK' : conjSub a K' = K') (hK3 : ∀ k ∈ K, ⁅a, k⁆ ∈ oddCoreOf K)
    (hK'3 : ∀ k ∈ K', ⁅a, k⁆ ∈ oddCoreOf K') : a ∈ centralizerModOdd ⊤ (K ⊔ K') := by
  have hOK : oddCoreOf K ≤ oddCoreOf (K ⊔ K') := by
    refine Sec6Gen.le_oddCoreOf_of_normal ((oddCoreOf_le_self _).trans le_sup_left) ?_
      (oddCoreOf_odd_natCard _)
    exact sup_le (fun k hk => mem_normalizer_oddCoreOf_of_mem_normalizer
      (Subgroup.le_normalizer hk)) (fun k hk => mem_normalizer_oddCoreOf_of_mem_normalizer
      (c.K'_le hk))
  have hOK' : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') := by
    refine Sec6Gen.le_oddCoreOf_of_normal ((oddCoreOf_le_self _).trans le_sup_right) ?_
      (oddCoreOf_odd_natCard _)
    exact sup_le (fun k hk => mem_normalizer_oddCoreOf_of_mem_normalizer (c.K_le hk))
      (fun k hk => mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hk))
  have haN : a ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
    mem_normalizer_sup_of (mem_normalizer_iff_conjSub_eq.mpr haK)
      (mem_normalizer_iff_conjSub_eq.mpr haK')
  refine ⟨Subgroup.mem_top a, haN, mem_normalizer_oddCoreOf_of_mem_normalizer haN,
    fun l hl => ?_⟩
  rw [Subgroup.sup_eq_closure] at hl
  have hON : ∀ x ∈ Subgroup.closure ((K : Set G) ∪ K'), x ∈ Subgroup.normalizer
      ((oddCoreOf (K ⊔ K') : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer
      (by rw [Subgroup.sup_eq_closure]; exact hx))
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hOK (hK3 x hx)
    · exact hOK' (hK'3 x hx)
  | one => simp
  | mul x y hx hy ihx ihy =>
    have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ ihx ((Subgroup.mem_normalizer_iff.mp (hON x hx) _).mp ihy)
  | inv x hx ihx =>
    have e : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hON x hx)) _).mp
      (Subgroup.inv_mem _ ihx)

end Cfg98

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
