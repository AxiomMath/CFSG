module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2T

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace Z2E

section Dihedral

variable {G : Type} [Group G]

theorem exists_conj_of_odd {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y))) : ∃ k : ℕ, (x * y) ^ k * x * ((x * y) ^ k)⁻¹ = y := by
  obtain ⟨i, hi⟩ := hodd
  refine ⟨i, ?_⟩
  obtain ⟨r, hr⟩ : ∃ r : G, r = x * y := ⟨_, rfl⟩
  rw [← hr] at hi ⊢
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxr : x * r * x⁻¹ = r⁻¹ := by
    rw [hr, hxi, mul_inv_rev, hxi, hyi, ← mul_assoc, hx, one_mul]
  have hk : x * r ^ i * x⁻¹ = (r ^ i)⁻¹ := by rw [← conj_pow, hxr, inv_pow]
  have hk' : r ^ i * x = x * (r ^ i)⁻¹ := by
    calc r ^ i * x = (x * r ^ i * x⁻¹)⁻¹ * x := by rw [hk, inv_inv]
      _ = x * (r ^ i)⁻¹ := by group
  have hm : r ^ i * r ^ i * r = 1 := by
    rw [← pow_add, ← pow_succ, ← two_mul, ← hi, pow_orderOf_eq_one]
  have hri : (r ^ i)⁻¹ * (r ^ i)⁻¹ = r := by
    calc (r ^ i)⁻¹ * (r ^ i)⁻¹ = (r ^ i)⁻¹ * (r ^ i)⁻¹ * (r ^ i * r ^ i * r) := by
          rw [hm, mul_one]
      _ = r := by group
  calc r ^ i * x * (r ^ i)⁻¹ = x * ((r ^ i)⁻¹ * (r ^ i)⁻¹) := by rw [hk', mul_assoc]
    _ = y := by rw [hri, hr, ← mul_assoc, hx, one_mul]

theorem exists_conj_comm_of_odd {u v : G} (hu : u * u = 1) (hv : v * v = 1)
    (hodd : Odd (orderOf (u * v * (u * v)))) :
    ∃ k : ℕ, (u * v) ^ k * v * ((u * v) ^ k)⁻¹ * u = u * ((u * v) ^ k * v * ((u * v) ^ k)⁻¹) := by
  obtain ⟨i, hi⟩ := hodd
  refine ⟨i + 1, ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : G, w = u * v := ⟨_, rfl⟩
  rw [← hw] at hi ⊢
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have huw : u * w * u⁻¹ = w⁻¹ := by
    rw [hw, hui, mul_inv_rev, hui, hvi, ← mul_assoc, hu, one_mul]
  have hk : u * w ^ (i + 1) * u⁻¹ = (w ^ (i + 1))⁻¹ := by rw [← conj_pow, huw, inv_pow]
  have hk2 : (w ^ (i + 1))⁻¹ * u = u * w ^ (i + 1) := by
    calc (w ^ (i + 1))⁻¹ * u = u * w ^ (i + 1) * u⁻¹ * u := by rw [hk]
      _ = u * w ^ (i + 1) := by group
  have hvu : v * u = w⁻¹ := by rw [hw, mul_inv_rev, hui, hvi]
  have hX : w ^ (i + 1) * w⁻¹ * w ^ (i + 1) * (w ^ (i + 1) * w⁻¹ * w ^ (i + 1)) = 1 := by
    have e1 : w ^ (i + 1) * w⁻¹ = w ^ i := by rw [pow_succ, mul_inv_cancel_right]
    rw [e1, ← pow_add, ← pow_add]
    have e2 : i + (i + 1) + (i + (i + 1)) = 2 * (2 * i + 1) := by omega
    rw [e2, pow_mul, sq, ← hi, pow_orderOf_eq_one]
  calc w ^ (i + 1) * v * (w ^ (i + 1))⁻¹ * u = w ^ (i + 1) * v * ((w ^ (i + 1))⁻¹ * u) := by
        rw [mul_assoc]
    _ = w ^ (i + 1) * (v * u) * w ^ (i + 1) := by rw [hk2, mul_assoc, mul_assoc, mul_assoc]
    _ = w ^ (i + 1) * w⁻¹ * w ^ (i + 1) := by rw [hvu]
    _ = (w ^ (i + 1) * w⁻¹ * w ^ (i + 1))⁻¹ := (inv_eq_of_mul_eq_one_right hX).symm
    _ = (w ^ (i + 1))⁻¹ * w * (w ^ (i + 1))⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
    _ = (w ^ (i + 1))⁻¹ * u * v * (w ^ (i + 1))⁻¹ := by rw [hw, mul_assoc _ u v]
    _ = u * (w ^ (i + 1) * v * (w ^ (i + 1))⁻¹) := by rw [hk2]; group

end Dihedral

section Simple

variable {X : Type} [Group X] [Finite X]

theorem exists_comm_conj_of_simple (hs : IsSimpleGroup X) (hZ : Subgroup.center X = ⊥) {a : X}
    (ha : a * a = 1) (ha1 : a ≠ 1) :
    ∃ g : X, (g * a * g⁻¹) * a = a * (g * a * g⁻¹) ∧ g * a * g⁻¹ ≠ a := by
  by_contra hcon
  push Not at hcon
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨N, hN, hNodd, hNa⟩ := CFSG.ZStar.glauberman_zStar X a ha1 ha hcon
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · apply ha1
    have hc : a ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hNa g
      rw [h, Subgroup.mem_bot] at h1
      have h2 : g * a * g⁻¹ = a := mul_inv_eq_one.mp h1
      calc g * a = g * a * g⁻¹ * g := by group
        _ = a * g := by rw [h2]
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  · rw [h, Subgroup.card_top] at hNodd
    have h2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
    have hd := orderOf_dvd_natCard a
    rw [h2] at hd
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hd)

end Simple

end Z2E

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_z2FrameAt (hL : TightLargeHypR 3 n Y R S t)
    (hsimp : IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)))
    (hnab : ∃ a b : ↥(genFittingFStar ↥(linkGrp R t)), a * b ≠ b * a)
    (hinv : ∀ a : ↥(linkGrp R t), a * a = 1 → a ∈ genFittingFStar ↥(linkGrp R t))
    (hconj : ∀ a a' : ↥(genFittingFStar ↥(linkGrp R t)), a * a = 1 → a ≠ 1 → a' * a' = 1 →
      a' ≠ 1 → ∃ g : ↥(genFittingFStar ↥(linkGrp R t)), g * a * g⁻¹ = a')
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {u : Y} (hu : IsUniqueInvolution J u) :
    ∃ (J₂ J₃ : Subgroup Y) (v : Y), Z2FrameAt R t J J₂ J₃ u v := by
  have ht := hL.datum.isUniqueInvolution_core
  have hΩ := hL.datum.hypOmegaGen
  have hπs := linkLayerHom'_surjective hL
  have hker := ker_linkLayerHom hL
  have hoddker : ∀ x : ↥(linkLayer R t), linkLayerHom' hL x = 1 → Odd (orderOf x) := by
    intro x hx
    have hxk : x ∈ classicalInvolutionOddCore ↥(linkLayer R t) := by
      rw [← hker]
      exact hx
    have hdvd := orderOf_dvd_natCard (⟨x, hxk⟩ : ↥(classicalInvolutionOddCore ↥(linkLayer R t)))
    rw [Subgroup.orderOf_mk] at hdvd
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥(linkLayer R t)).of_dvd_nat hdvd
  have hZF := Z2T.center_eq_bot_of_simple hsimp hnab
  have hZX : Subgroup.center ↥(linkGrp R t) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzF : z ∈ genFittingFStar ↥(linkGrp R t) :=
      centralizer_genFittingFStar_le (Subgroup.mem_centralizer_iff.mpr fun f _ =>
        Subgroup.mem_center_iff.mp hz f)
    have hzZ : (⟨z, hzF⟩ : ↥(genFittingFStar ↥(linkGrp R t))) ∈
        Subgroup.center ↥(genFittingFStar ↥(linkGrp R t)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hz g)
    rw [hZF, Subgroup.mem_bot] at hzZ
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hzZ)
  have hCt : ∀ x : ↥(linkLayer R t), (x : Y) ∈ Subgroup.centralizer ({t} : Set Y) :=
    fun x => linkLayerAt_le_centralizer x.2
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have huΛ : u ∈ linkLayer R t :=
    coreAt_le_linkLayerAt hJ (mem_coreAt_of_sq_sq hu.mem (by rw [hu.sq, one_mul]) ctu.symm)
  obtain ⟨uL, huL⟩ : ∃ uL : ↥(linkLayer R t), (uL : Y) = u := ⟨⟨u, huΛ⟩, rfl⟩
  have hu2 : uL * uL = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, huL, hu.sq]
    rfl)
  have hu1 : linkLayerHom' hL uL ≠ 1 := fun h => by
    have h1 := hoddker uL h
    rw [orderOf_eq_prime (by rw [sq]; exact hu2) (fun h' => hu.ne_one (by
      rw [← huL, h']
      rfl))] at h1
    exact absurd h1 (by decide)
  obtain ⟨ub, hub⟩ : ∃ ub, ub = linkLayerHom' hL uL := ⟨_, rfl⟩
  rw [← hub] at hu1
  have hū2 : ub * ub = 1 := by rw [hub, ← map_mul, hu2, map_one]
  have hubF := hinv ub hū2
  have hubF2 : (⟨ub, hubF⟩ : ↥(genFittingFStar ↥(linkGrp R t))) * ⟨ub, hubF⟩ = 1 :=
    Subtype.ext hū2
  have hubF1 : (⟨ub, hubF⟩ : ↥(genFittingFStar ↥(linkGrp R t))) ≠ 1 :=
    fun h => hu1 (congrArg Subtype.val h)
  obtain ⟨gF, hcF, hneF⟩ := Z2E.exists_comm_conj_of_simple hsimp hZF hubF2 hubF1
  obtain ⟨gb, hgb⟩ : ∃ gb : ↥(linkGrp R t), gb = (gF : ↥(linkGrp R t)) := ⟨_, rfl⟩
  have hcb : (gb * ub * gb⁻¹) * ub = ub * (gb * ub * gb⁻¹) := by
    rw [hgb]
    exact congrArg Subtype.val hcF
  have hneb : gb * ub * gb⁻¹ ≠ ub := fun h => hneF (Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgb]
    exact h))
  have hgbF : gb ∈ genFittingFStar ↥(linkGrp R t) := by rw [hgb]; exact gF.2
  obtain ⟨vb, hvb⟩ : ∃ vb, vb = gb * ub * gb⁻¹ := ⟨_, rfl⟩
  rw [← hvb] at hcb hneb
  have hvbF : vb ∈ genFittingFStar ↥(linkGrp R t) := by
    rw [hvb]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgbF hubF) (Subgroup.inv_mem _ hgbF)
  have hvb2 : vb * vb = 1 := by
    rw [hvb]
    calc gb * ub * gb⁻¹ * (gb * ub * gb⁻¹) = gb * (ub * ub) * gb⁻¹ := by group
      _ = 1 := by rw [hū2]; group
  obtain ⟨g₁, hg₁⟩ := hπs gb
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : ↥(linkLayer R t), v₀ = g₁ * uL * g₁⁻¹ := ⟨_, rfl⟩
  have hπv₀ : linkLayerHom' hL v₀ = vb := by
    rw [hv₀, map_mul, map_mul, map_inv, hg₁, ← hub, hvb]
  have hv₀2 : v₀ * v₀ = 1 := by
    rw [hv₀]
    calc g₁ * uL * g₁⁻¹ * (g₁ * uL * g₁⁻¹) = g₁ * (uL * uL) * g₁⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hubvb : ub * vb * (ub * vb) = 1 := by
    calc ub * vb * (ub * vb) = ub * (vb * ub) * vb := by group
      _ = ub * ub * (vb * vb) := by rw [hcb]; group
      _ = 1 := by rw [hū2, hvb2, one_mul]
  have hw2 : linkLayerHom' hL (uL * v₀ * (uL * v₀)) = 1 := by
    rw [map_mul, map_mul, hπv₀, ← hub, hubvb]
  obtain ⟨k, hk⟩ := Z2E.exists_conj_comm_of_odd hu2 hv₀2 (hoddker _ hw2)
  obtain ⟨w, hw⟩ : ∃ w : ↥(linkLayer R t), w = uL * v₀ := ⟨_, rfl⟩
  rw [← hw] at hk
  obtain ⟨pL, hpL⟩ : ∃ pL : ↥(linkLayer R t), pL = w ^ k * v₀ * (w ^ k)⁻¹ := ⟨_, rfl⟩
  rw [← hpL] at hk
  have hpL2 : pL * pL = 1 := by
    rw [hpL]
    calc w ^ k * v₀ * (w ^ k)⁻¹ * (w ^ k * v₀ * (w ^ k)⁻¹) = w ^ k * (v₀ * v₀) * (w ^ k)⁻¹ := by
          group
      _ = 1 := by rw [hv₀2]; group
  have hπw : linkLayerHom' hL w = ub * vb := by rw [hw, map_mul, hπv₀, ← hub]
  have hπp : linkLayerHom' hL pL = vb := by
    have hc : Commute (ub * vb) vb := by
      show ub * vb * vb = vb * (ub * vb)
      rw [← mul_assoc, hcb]
    rw [hpL, map_mul, map_mul, map_inv, map_pow, hπw, hπv₀, (hc.pow_left k).eq,
      mul_inv_cancel_right]
  have hg₂p : (w ^ k * g₁) * uL * (w ^ k * g₁)⁻¹ = pL := by rw [hpL, hv₀]; group
  have hJ₂ := conjSub_mem_omegaNbr_core hL hJ (hCt (w ^ k * g₁))
  have hp₂ : IsUniqueInvolution (conjSub ((w ^ k * g₁ : ↥(linkLayer R t)) : Y) J) (pL : Y) := by
    have h1 := hu.conj ((w ^ k * g₁ : ↥(linkLayer R t)) : Y)
    have e : ((w ^ k * g₁ : ↥(linkLayer R t)) : Y) * u * ((w ^ k * g₁ : ↥(linkLayer R t)) : Y)⁻¹ =
        (pL : Y) := by
      rw [← huL]
      exact congrArg Subtype.val hg₂p
    rwa [e] at h1
  have hup : u * (pL : Y) = (pL : Y) * u := by
    rw [← huL]
    exact (congrArg Subtype.val hk).symm
  have hpu : (pL : Y) ≠ u := by
    intro e
    have h1 : pL = uL := Subtype.ext (e.trans huL.symm)
    apply hneb
    rw [← hπp, h1, ← hub]
  have hptu : (pL : Y) ≠ t * u := by
    intro e
    have htLv : ((pL * uL : ↥(linkLayer R t)) : Y) = t := by
      rw [Subgroup.coe_mul, e, huL, mul_assoc, hu.sq, mul_one]
    have hcen : linkLayerHom' hL (pL * uL) ∈ Subgroup.center ↥(linkGrp R t) := by
      rw [Subgroup.mem_center_iff]
      intro xb
      obtain ⟨x, rfl⟩ := hπs xb
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (x : Y) * ((pL * uL : ↥(linkLayer R t)) : Y) = ((pL * uL : ↥(linkLayer R t)) : Y) * x
      rw [htLv]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hCt x)
    rw [hZX, Subgroup.mem_bot, map_mul, hπp, ← hub] at hcen
    apply hneb
    rw [eq_inv_of_mul_eq_one_left hcen, inv_eq_of_mul_eq_one_right hū2]
  have hcb1 : ub * vb ≠ 1 := fun h => hneb (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hū2])
  have hcbF : ub * vb ∈ genFittingFStar ↥(linkGrp R t) := Subgroup.mul_mem _ hubF hvbF
  obtain ⟨gF₃, hgF₃⟩ := hconj ⟨ub, hubF⟩ ⟨ub * vb, hcbF⟩ hubF2 hubF1 (Subtype.ext hubvb)
    (fun h => hcb1 (congrArg Subtype.val h))
  have hgb₃ : (gF₃ : ↥(linkGrp R t)) * ub * (gF₃ : ↥(linkGrp R t))⁻¹ = ub * vb :=
    congrArg Subtype.val hgF₃
  obtain ⟨g₃, hg₃⟩ := hπs (gF₃ : ↥(linkGrp R t))
  obtain ⟨qL, hqL⟩ : ∃ qL : ↥(linkLayer R t), qL = g₃ * uL * g₃⁻¹ := ⟨_, rfl⟩
  obtain ⟨yL, hyL⟩ : ∃ yL : ↥(linkLayer R t), yL = uL * pL := ⟨_, rfl⟩
  have hq2 : qL * qL = 1 := by
    rw [hqL]
    calc g₃ * uL * g₃⁻¹ * (g₃ * uL * g₃⁻¹) = g₃ * (uL * uL) * g₃⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hy2 : yL * yL = 1 := by
    rw [hyL]
    calc uL * pL * (uL * pL) = uL * (pL * uL) * pL := by group
      _ = uL * uL * (pL * pL) := by rw [hk]; group
      _ = 1 := by rw [hu2, hpL2, one_mul]
  have hπq : linkLayerHom' hL qL = ub * vb := by
    rw [hqL, map_mul, map_mul, map_inv, hg₃, ← hub, hgb₃]
  have hπy : linkLayerHom' hL yL = ub * vb := by rw [hyL, map_mul, hπp, ← hub]
  have hqy : linkLayerHom' hL (qL * yL) = 1 := by rw [map_mul, hπq, hπy, hubvb]
  obtain ⟨k₃, hk₃⟩ := Z2E.exists_conj_of_odd hq2 hy2 (hoddker _ hqy)
  obtain ⟨r, hr⟩ : ∃ r : ↥(linkLayer R t), r = qL * yL := ⟨_, rfl⟩
  rw [← hr] at hk₃
  have hg₄y : (r ^ k₃ * g₃) * uL * (r ^ k₃ * g₃)⁻¹ = yL := by
    calc (r ^ k₃ * g₃) * uL * (r ^ k₃ * g₃)⁻¹ = r ^ k₃ * (g₃ * uL * g₃⁻¹) * (r ^ k₃)⁻¹ := by
          group
      _ = r ^ k₃ * qL * (r ^ k₃)⁻¹ := by rw [hqL]
      _ = yL := hk₃
  have hJ₃ := conjSub_mem_omegaNbr_core hL hJ (hCt (r ^ k₃ * g₃))
  have hp₃ : IsUniqueInvolution (conjSub ((r ^ k₃ * g₃ : ↥(linkLayer R t)) : Y) J)
      (u * (pL : Y)) := by
    have h1 := hu.conj ((r ^ k₃ * g₃ : ↥(linkLayer R t)) : Y)
    have e : ((r ^ k₃ * g₃ : ↥(linkLayer R t)) : Y) * u *
        ((r ^ k₃ * g₃ : ↥(linkLayer R t)) : Y)⁻¹ = u * (pL : Y) := by
      have h2 := congrArg Subtype.val hg₄y
      rw [hyL] at h2
      rw [← huL]
      exact h2
    rwa [e] at h1
  exact ⟨_, _, _, hJ, hJ₂, hJ₃, hu, hp₂, hp₃, hup, hpu, hptu⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
