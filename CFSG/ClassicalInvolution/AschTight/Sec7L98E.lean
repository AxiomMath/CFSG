module

public import Mathlib
public import CFSG.ClassicalInvolution.AschTight.Sec7L98D

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem eq_one_of_odd_of_pow_two_pow {o : G} (ho : Odd (orderOf o)) {N : ℕ} (hN : o ^ 2 ^ N = 1) :
    o = 1 := by
  have h1 : orderOf o ∣ 2 ^ N := orderOf_dvd_of_pow_eq_one hN
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · rw [hk, pow_succ] at ho
    exact absurd ho (Nat.not_odd_iff_even.mpr ⟨2 ^ k, by ring⟩)

namespace Cfg98

variable {Ω : Set (Subgroup G)} {K J K' X P : Subgroup G} {z j : G} {S : Sylow 2 G}
  {W : Subgroup G} (c : Cfg98 Ω K J K' X P z j S W)
include c

theorem P_eq [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hv : Subgroup.zpowers v = J ⊓ W) :
    P = ((K ⊓ (S : Subgroup G)) ⊔ (K' ⊓ (S : Subgroup G))) ⊔ Subgroup.zpowers v := by
  have hRR' : IsSylow2In ((K ⊓ (S : Subgroup G)) ⊔ (K' ⊓ (S : Subgroup G))) (K ⊔ K') :=
    isSylow2In_sup_of_sylow c.K'_le c.sylow_R c.sylow_R'
      (fun g hg => mem_normalizer_inf (c.K'_le hg.1) (Subgroup.le_normalizer hg.2))
      (fun g hg => ⟨hg.2, hg.1.2⟩)
  have hSN : (S : Subgroup G) ⊓ (K ⊔ K') = (K ⊓ (S : Subgroup G)) ⊔ (K' ⊓ (S : Subgroup G)) :=
    hRR'.eq_of_le (S.isPGroup'.to_le inf_le_left) inf_le_right
      (le_inf (sup_le inf_le_right inf_le_right)
        (sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)))
  have hvS : Subgroup.zpowers v ≤ (S : Subgroup G) := by rw [hv]; exact inf_le_right.trans c.hWS
  have hvNK : Subgroup.zpowers v ≤ Subgroup.normalizer (K : Set G) := by
    rw [hv]; exact c.V_le_N_K
  have hvNK' : Subgroup.zpowers v ≤ Subgroup.normalizer (K' : Set G) := by
    rw [hv]; exact c.V_le_N_K'
  have hP2 := isSylow2In_sup_of_sylow (N := K ⊔ K') (C := J ⊓ Subgroup.centralizer ({z} : Set G))
    (inf_le_right.trans c.cent_le_normalizer_sup) hRR' t.he3
    (fun g hg => mem_normalizer_sup_of
      (mem_normalizer_inf (hvNK hg) (Subgroup.le_normalizer (hvS hg)))
      (mem_normalizer_inf (hvNK' hg) (Subgroup.le_normalizer (hvS hg))))
    (by rw [← hSN]; exact inf_le_inf_right _ hvS)
  exact hP2.eq_of_le c.hP.2.1 c.hP.1 (c.le_P hP2.1
    (sup_le (sup_le inf_le_right inf_le_right) hvS))

theorem P_le_Y [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hv : Subgroup.zpowers v = J ⊓ W) : P ≤ pairNormalizers K J z j := by
  rw [c.P_eq t hv]
  exact sup_le (sup_le t.R_le_Y t.R'_le_Y) (t.hvT.trans t.hTY)

theorem P_le_N_UV [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hv : Subgroup.zpowers v = J ⊓ W) :
    P ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  rw [c.P_eq t hv]
  exact sup_le (sup_le t.hRN t.hR'N) ((le_sup_right : Subgroup.zpowers v ≤ _).trans
    Subgroup.le_normalizer)

theorem D_dichotomy [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hv : Subgroup.zpowers v = J ⊓ W) :
    ∀ d ∈ P ⊓ Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G),
      d ∉ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
      ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, d * w * d⁻¹ = w⁻¹ := by
  intro d hd hdUV
  rcases t.sign (c.P_le_Y t hv hd.1) hd.2 (c.P_le_N_UV t hv hd.1) with h | h
  · exfalso
    apply hdUV
    have hdC : d ∈ Subgroup.centralizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun w hw => by
        have := h w hw
        calc w * d = d * w * d⁻¹ * d := by rw [this]
          _ = d * w := by group
    have hdX := t.hf ⟨c.P_le_Y t hv hd.1, hdC⟩
    have hON : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤
        Subgroup.normalizer ((oddCoreOf ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔
          (K ⊓ Subgroup.normalizer (J : Set G))) : Subgroup G) : Set G) := fun w hw =>
      mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (t.UV_le_X hw))
    have hd' := t.hXeq ▸ hdX
    obtain ⟨o, ho, w', hw', hdo⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hON hd'
    have hoodd : Odd (orderOf o) := by
      have h1 : orderOf o ∣ Nat.card ↥(oddCoreOf ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔
          (K ⊓ Subgroup.normalizer (J : Set G)))) := by
        rw [← Subgroup.orderOf_mk o ho]
        exact orderOf_dvd_natCard _
      exact Odd.of_dvd_nat (oddCoreOf_odd_natCard _) h1
    have hdw : d * w' = w' * d := (Subgroup.mem_centralizer_iff.mp hdC w' hw').symm
    obtain ⟨a, ha⟩ := (S.isPGroup'.to_le (le_sup_left.trans c.hPS) : IsPGroup 2 P) ⟨d, hd.1⟩
    obtain ⟨b, hb⟩ := t.UV_isPGroup ⟨w', hw'⟩
    have hda : d ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hwb : w' ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hoe : o = d * w'⁻¹ := by rw [hdo]; group
    have hcomm : Commute d w'⁻¹ := (Commute.inv_right (hdw : Commute d w'))
    have ho1 : o ^ 2 ^ (a + b) = 1 := by
      rw [hoe, hcomm.mul_pow, pow_add, pow_mul, hda, one_pow, one_mul, mul_comm (2 ^ a) (2 ^ b),
        pow_mul, inv_pow, hwb, inv_one, one_pow]
    have ho' := eq_one_of_odd_of_pow_two_pow hoodd ho1
    rw [hdo, ho', one_mul]
    exact hw'
  · exact h

theorem X_le_N_UV [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hv : Subgroup.zpowers v = J ⊓ W) :
    X ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  have hDA := c.D_dichotomy t hv
  have huP : u ∈ P := c.P_eq t hv ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (t.huR (Subgroup.mem_zpowers u)))
  have hvP : v ∈ P := c.P_eq t hv ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have hZC : ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v,
      w ∈ Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :=
    fun w hw => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      t.UV_comm y (t.Z_le_UV hy) w hw
  have hxD : ∀ x ∈ X, ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, w ∈ P →
      x * w * x⁻¹ ∈ P ⊓ Subgroup.centralizer
        ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
    intro x hx w hw hwP
    have hxZ := t.mem_C_Z_of_comm
      (Subgroup.mem_centralizer_iff.mp (c.hXc hx) z (by simp)).symm
      (Subgroup.mem_centralizer_iff.mp (c.hXc hx) j (by simp)).symm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := conj_mem_conjSub (n := x) hwP
      rwa [c.hXP x hx] at this
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := Subgroup.mem_centralizer_iff.mp hxZ y hy
      have h2 := Subgroup.mem_centralizer_iff.mp (hZC w hw) y hy
      calc y * (x * w * x⁻¹) = x * (x⁻¹ * y * x) * w * x⁻¹ := by group
        _ = x * y * w * x⁻¹ := by
            rw [show x⁻¹ * y * x = y by rw [mul_assoc, h1]; group]
        _ = x * (w * y) * x⁻¹ := by rw [mul_assoc x y w, h2]
        _ = (x * w * x⁻¹) * (x * y * x⁻¹) := by group
        _ = (x * w * x⁻¹) * y := by rw [show x * y * x⁻¹ = y by rw [← h1]; group]
  have huv : u * v = v * u := t.hcomm u (Subgroup.mem_zpowers u) v (Subgroup.mem_zpowers v)
  have huvsq : (u * v) * (u * v) ≠ 1 := by
    intro h
    have h1 : u * u = (v * v)⁻¹ := by
      have : u * u * (v * v) = 1 := by
        calc u * u * (v * v) = u * (u * v) * v := by group
          _ = u * (v * u) * v := by rw [huv]
          _ = (u * v) * (u * v) := by group
          _ = 1 := h
      exact eq_inv_of_mul_eq_one_left this
    have h2 : u * u ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v :=
      ⟨Subgroup.mul_mem _ (Subgroup.mem_zpowers u) (Subgroup.mem_zpowers u),
        h1 ▸ Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers v)
          (Subgroup.mem_zpowers v))⟩
    rw [t.U_inf_V, Subgroup.mem_bot] at h2
    exact t.u_sq_ne h2
  refine le_normalizer_of_conjSub_le fun x hx => ?_
  have hxu := hxD x hx u (Subgroup.mem_sup_left (Subgroup.mem_zpowers u)) huP
  have hxv := hxD x hx v (Subgroup.mem_sup_right (Subgroup.mem_zpowers v)) hvP
  have hc : (x * u * x⁻¹) * (x * v * x⁻¹) = (x * v * x⁻¹) * (x * u * x⁻¹) := by
    calc (x * u * x⁻¹) * (x * v * x⁻¹) = x * (u * v) * x⁻¹ := by group
      _ = x * (v * u) * x⁻¹ := by rw [huv]
      _ = (x * v * x⁻¹) * (x * u * x⁻¹) := by group
  have hsq : ∀ y : G, y * y ≠ 1 → (x * y * x⁻¹) * (x * y * x⁻¹) ≠ 1 := by
    intro y hy h
    apply hy
    calc y * y = x⁻¹ * ((x * y * x⁻¹) * (x * y * x⁻¹)) * x := by group
      _ = 1 := by rw [h]; group
  have hw₀ : u ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have h1 := mem_of_dihedral hDA hw₀ t.u_sq_ne hxu hxv hc (hsq v t.v_sq_ne)
    (by
      have := hsq (u * v) huvsq
      rwa [show x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) by group] at this)
  have h2 := mem_of_dihedral hDA hw₀ t.u_sq_ne hxv hxu hc.symm (hsq u t.u_sq_ne)
    (by
      have := hsq (v * u) (by rw [← huv]; exact huvsq)
      rwa [show x * (v * u) * x⁻¹ = (x * v * x⁻¹) * (x * u * x⁻¹) by group] at this)
  rw [conjSub_sup_eq, AscL62.conjSub_zpowers_eq, AscL62.conjSub_zpowers_eq]
  exact sup_le (Subgroup.zpowers_le.mpr h1) (Subgroup.zpowers_le.mpr h2)

end Cfg98

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
