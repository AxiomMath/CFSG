module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDCommCard

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup Equiv CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

include ctx

private lemma commute_of_ψ_comm {a b : X} (haT : a ∈ ctx.A.T) (haL : a ∈ L)
    (hbT : b ∈ ctx.A.T)
    (hψ : ctx.A.ψ ⟨a, haT⟩ * ctx.A.ψ ⟨b, hbT⟩ =
      ctx.A.ψ ⟨b, hbT⟩ * ctx.A.ψ ⟨a, haT⟩) : a * b = b * a := by
  have hbC : b ∈ centralizer ({t} : Set X) := ctx.A.T_le_centralizer hbT
  have hcT : a * b * a⁻¹ * b⁻¹ ∈ ctx.A.T :=
    mul_mem (mul_mem (mul_mem haT hbT) (inv_mem haT)) (inv_mem hbT)
  have hcL : a * b * a⁻¹ * b⁻¹ ∈ L := by
    have h1 : b * a⁻¹ * b⁻¹ ∈ L := SD.conj_mem_L (A := ctx.A) hbC (L.inv_mem haL)
    simpa [mul_assoc] using mul_mem haL h1
  have hψc : ctx.A.ψ ⟨a * b * a⁻¹ * b⁻¹, hcT⟩ = 1 := by
    have hprod : (⟨a * b * a⁻¹ * b⁻¹, hcT⟩ : ctx.A.T) =
        (⟨a, haT⟩ : ctx.A.T) * ⟨b, hbT⟩ * (⟨a, haT⟩ : ctx.A.T)⁻¹ *
          (⟨b, hbT⟩ : ctx.A.T)⁻¹ := Subtype.ext rfl
    rw [hprod]
    simp only [map_mul, map_inv]
    rw [hψ]
    group
  have hcK : a * b * a⁻¹ * b⁻¹ ∈ ctx.A.K := (ctx.A.mem_K_iff hcT).mpr hψc
  have hbot : a * b * a⁻¹ * b⁻¹ ∈ ctx.A.K ⊓ L := ⟨hcK, hcL⟩
  rw [ctx.A.K_inf_L, mem_bot] at hbot
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = 1 * (b * a) := by rw [hbot]
    _ = b * a := one_mul _

private lemma R_comm_k {r : X} (hr : r ∈ ctx.A.R) : r * ctx.C.k = ctx.C.k * r := by
  refine commute_of_ψ_comm ctx hr.1 (ctx.A.R_le_L hr) ctx.C.k_mem ?_
  rw [ctx.C.ψ_k]
  exact (SD.k8_comm_of_mem_R8 (ctx.A.ψ_mem_R8' hr)).symm

private lemma R_comm_z {r : X} (hr : r ∈ ctx.A.R) : r * ctx.S.z = ctx.S.z * r :=
  (ctx.S.z_comm_R hr).symm

private lemma k_comm_z : ctx.C.k * ctx.S.z = ctx.S.z * ctx.C.k := by
  refine (commute_of_ψ_comm ctx (a := ctx.S.z) (b := ctx.C.k) ctx.S.z_mem.1
    (ctx.A.R_le_L ctx.S.z_mem) ctx.C.k_mem ?_).symm
  rw [← SD.ψX_of_mem ctx.S.z_mem.1, ctx.S.ψ_z, ctx.C.ψ_k]
  exact (SD.z8_comm_aff8' u5 0).symm

private lemma R_comm_k' {k' : X} (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k)
    {r : X} (hr : r ∈ ctx.A.R) : r * k' = k' * r := by
  rcases hk' with rfl | rfl
  · exact R_comm_k ctx hr
  · calc r * (ctx.S.z * ctx.C.k) = (r * ctx.S.z) * ctx.C.k := by group
      _ = (ctx.S.z * r) * ctx.C.k := by rw [R_comm_z ctx hr]
      _ = ctx.S.z * (r * ctx.C.k) := by group
      _ = ctx.S.z * (ctx.C.k * r) := by rw [R_comm_k ctx hr]
      _ = (ctx.S.z * ctx.C.k) * r := by group

private lemma k_comm_k' {k' : X} (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k) :
    ctx.C.k * k' = k' * ctx.C.k := by
  rcases hk' with rfl | rfl
  · rfl
  · calc ctx.C.k * (ctx.S.z * ctx.C.k) = (ctx.C.k * ctx.S.z) * ctx.C.k := by group
      _ = (ctx.S.z * ctx.C.k) * ctx.C.k := by rw [k_comm_z]

private lemma comm_of_eq_one_or_t {k' c : X} (hk'T : k' ∈ ctx.A.T)
    (hc : c = 1 ∨ c = t) : c * k' = k' * c := by
  rcases hc with rfl | rfl
  · rw [one_mul, mul_one]
  · exact (ctx.A.commute_t hk'T).symm

private lemma comm_of_mul {k' w c g : X} (hg : g = w * c) (hw : w * k' = k' * w)
    (hc : c * k' = k' * c) : g * k' = k' * g := by
  calc g * k' = w * c * k' := by rw [hg]
    _ = w * (c * k') := by rw [mul_assoc]
    _ = w * (k' * c) := by rw [hc]
    _ = w * k' * c := by rw [← mul_assoc]
    _ = k' * w * c := by rw [hw]
    _ = k' * (w * c) := by rw [mul_assoc]
    _ = k' * g := by rw [hg]

private lemma comm_of_mul_ker {k' g r e : X} (hk'T : k' ∈ ctx.A.T) (hgT : g ∈ ctx.A.T)
    (hr : r ∈ ctx.A.R) (heT : e ∈ ctx.A.T)
    (hψ : ctx.A.ψ ⟨r * e, mul_mem hr.1 heT⟩ = ctx.A.ψ ⟨g, hgT⟩)
    (hr_comm : r * k' = k' * r) (he_comm : e * k' = k' * e) : g * k' = k' * g := by
  have hwT : r * e ∈ ctx.A.T := mul_mem hr.1 heT
  have hcT : (r * e)⁻¹ * g ∈ ctx.A.T := mul_mem (inv_mem hwT) hgT
  have hψc : ctx.A.ψ ⟨(r * e)⁻¹ * g, hcT⟩ = 1 := by
    have hsplit : (⟨(r * e)⁻¹ * g, hcT⟩ : ctx.A.T) =
        (⟨r * e, hwT⟩ : ctx.A.T)⁻¹ * ⟨g, hgT⟩ := Subtype.ext rfl
    rw [hsplit, map_mul, map_inv, hψ, inv_mul_cancel]
  have hcK : (r * e)⁻¹ * g ∈ ctx.A.K := (ctx.A.mem_K_iff hcT).mpr hψc
  have hc2 : ((r * e)⁻¹ * g) ^ 2 = 1 := by
    have h2 : (⟨(r * e)⁻¹ * g, hcK⟩ : ctx.A.K) ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := ctx.A.K) (x := ⟨(r * e)⁻¹ * g, hcK⟩)
      rwa [ctx.C.card_K] at h
    exact congrArg Subtype.val h2
  have hc1 : (r * e)⁻¹ * g = 1 ∨ (r * e)⁻¹ * g = t := by
    by_cases h : (r * e)⁻¹ * g = 1
    · exact Or.inl h
    · exact Or.inr (ctx.A.eq_t_of_mem_K hcK hc2 h)
  have hc_comm : ((r * e)⁻¹ * g) * k' = k' * ((r * e)⁻¹ * g) :=
    comm_of_eq_one_or_t ctx hk'T hc1
  have hw_comm : (r * e) * k' = k' * (r * e) := by
    calc (r * e) * k' = r * (e * k') := by group
      _ = r * (k' * e) := by rw [he_comm]
      _ = (r * k') * e := by group
      _ = (k' * r) * e := by rw [hr_comm]
      _ = k' * (r * e) := by group
  exact comm_of_mul ctx (by group) hw_comm hc_comm

private lemma commutator_eq_one_or_t {k' x : X} (hk'T : k' ∈ ctx.A.T)
    (hx : x ∈ centralizer ({t} : Set X))
    (hxH : ctx.actX x * ctx.actX k' = ctx.actX k' * ctx.actX x) :
    x * k' * x⁻¹ * k'⁻¹ = 1 ∨ x * k' * x⁻¹ * k'⁻¹ = t := by
  have hk'C : k' ∈ centralizer ({t} : Set X) := ctx.A.T_le_centralizer hk'T
  have hcC : x * k' * x⁻¹ * k'⁻¹ ∈ centralizer ({t} : Set X) :=
    mul_mem (mul_mem (mul_mem hx hk'C) (inv_mem hx)) (inv_mem hk'C)
  have hact : ctx.actX (x * k' * x⁻¹ * k'⁻¹) = 1 := by
    rw [ctx.actX_mul (mul_mem (mul_mem hx hk'C) (inv_mem hx)) (inv_mem hk'C),
        ctx.actX_mul (mul_mem hx hk'C) (inv_mem hx),
        ctx.actX_mul hx hk'C, ctx.actX_inv hx, ctx.actX_inv hk'C, hxH]
    group
  exact (ctx.actX_eq_one_iff hcC).mp hact

theorem comm_of_mem_T_inf_chat {k' : X} (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k) {g : X}
    (hgT : g ∈ ctx.A.T) (hg : ctx.actX g * ctx.actX k' = ctx.actX k' * ctx.actX g) :
    g * k' = k' * g := by
  have hk'T : k' ∈ ctx.A.T := by
    rcases hk' with rfl | rfl
    · exact ctx.C.k_mem
    · exact mul_mem ctx.S.z_mem.1 ctx.C.k_mem
  have hψcomm : ctx.A.ψ ⟨g, hgT⟩ * ctx.A.ψ ⟨k', hk'T⟩ =
      ctx.A.ψ ⟨k', hk'T⟩ * ctx.A.ψ ⟨g, hgT⟩ := by
    let Φ : ↥(SDAutP.P ctx.M.F) →* Perm (ZMod 8) :=
      H8.subtype.comp (SDAutP.phi ctx.M.F).toMonoidHom
    have h1 : ctx.A.ψ ⟨g, hgT⟩ = Φ ⟨ctx.actX g, ctx.actX_mem_P hgT⟩ := by
      rw [ctx.ψ_eq hgT]; rfl
    have h2 : ctx.A.ψ ⟨k', hk'T⟩ = Φ ⟨ctx.actX k', ctx.actX_mem_P hk'T⟩ := by
      rw [ctx.ψ_eq hk'T]; rfl
    rw [h1, h2, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hg
  have hψXk' : SD.ψX ctx.A k' = k8 ∨ SD.ψX ctx.A k' = z8 * k8 := by
    rcases hk' with rfl | rfl
    · left
      rw [SD.ψX_of_mem ctx.C.k_mem, ctx.C.ψ_k]
    · right
      rw [SD.ψX_mul ctx.S.z_mem.1 ctx.C.k_mem, ctx.S.ψ_z, SD.ψX_of_mem ctx.C.k_mem, ctx.C.ψ_k]
  have hψg_k8 : ctx.A.ψ ⟨g, hgT⟩ * k8 = k8 * ctx.A.ψ ⟨g, hgT⟩ := by
    have hψk'eq : ctx.A.ψ ⟨k', hk'T⟩ = SD.ψX ctx.A k' := (SD.ψX_of_mem hk'T).symm
    rw [hψk'eq] at hψcomm
    rcases hψXk' with h | h
    · rw [h] at hψcomm; exact hψcomm
    · rw [h] at hψcomm
      exact (SD.commute_z8_mul_k8_iff (ctx.A.ψ_mem_H8 ⟨g, hgT⟩)).mp hψcomm
  have hmemR := SD.mem_R8_or_mul_k8_mem_R8 (ctx.A.ψ_mem_H8 ⟨g, hgT⟩) hψg_k8
  rcases hmemR with hR | hR
  · obtain ⟨r, hr, hrψ⟩ := ctx.A.exists_mem_R_ψ_eq hR
    have heT : (1 : X) ∈ ctx.A.T := one_mem _
    have hψ : ctx.A.ψ ⟨r * 1, mul_mem hr.1 heT⟩ = ctx.A.ψ ⟨g, hgT⟩ := by
      rw [show (⟨r * 1, mul_mem hr.1 heT⟩ : ctx.A.T) = ⟨r, hr.1⟩ from
        Subtype.ext (mul_one r)]
      exact hrψ
    have he_comm : (1 : X) * k' = k' * 1 := by rw [one_mul, mul_one]
    exact comm_of_mul_ker ctx hk'T hgT hr heT hψ (R_comm_k' ctx hk' hr) he_comm
  · obtain ⟨r, hr, hrψ⟩ := ctx.A.exists_mem_R_ψ_eq hR
    have heT : ctx.C.k ∈ ctx.A.T := ctx.C.k_mem
    have hψ : ctx.A.ψ ⟨r * ctx.C.k, mul_mem hr.1 heT⟩ = ctx.A.ψ ⟨g, hgT⟩ := by
      have hsplit : (⟨r * ctx.C.k, mul_mem hr.1 heT⟩ : ctx.A.T) =
          (⟨r, hr.1⟩ : ctx.A.T) * ⟨ctx.C.k, ctx.C.k_mem⟩ := Subtype.ext rfl
      rw [hsplit, map_mul, hrψ, ctx.C.ψ_k, mul_assoc, ← pow_two, SD.k8_sq, mul_one]
    exact comm_of_mul_ker ctx hk'T hgT hr heT hψ (R_comm_k' ctx hk' hr) (k_comm_k' ctx hk')

theorem comm_outer {k' : X} (hk' : k' = ctx.C.k ∨ k' = ctx.S.z * ctx.C.k) {g : X}
    (hg : g ∈ centralizer ({t} : Set X))
    (hcomm : ctx.actX g * ctx.actX k' = ctx.actX k' * ctx.actX g) : g * k' = k' * g := by
  have hk'T : k' ∈ ctx.A.T := by
    rcases hk' with rfl | rfl
    · exact ctx.C.k_mem
    · exact mul_mem ctx.S.z_mem.1 ctx.C.k_mem
  let Q := ↥(centralizer ({t} : Set X))
  let H : Subgroup Q := ctx.chat k'
  let kQ : Q := ⟨k', ctx.A.T_le_centralizer hk'T⟩
  let N : Subgroup Q := H ⊓ Subgroup.centralizer ({kQ} : Set Q)
  let U : Subgroup Q := (ctx.A.syl : Subgroup Q) ⊓ H
  have hH_comm : ∀ x : Q, x ∈ H → ctx.actX (x : X) * ctx.actX k' =
      ctx.actX k' * ctx.actX (x : X) := by
    intro x hx
    have hx' : ctx.act x ∈ Subgroup.centralizer ({ctx.actX k'} : Set (MulAut ↥L)) :=
      (Subgroup.mem_comap).mp hx
    rw [ctx.actX_of_mem x.2]
    exact mem_centralizer_singleton_iff.mp hx'
  have hU_le_N : U ≤ N := by
    intro x hx
    have hxH : x ∈ H := hx.2
    have hxT : (x : X) ∈ ctx.A.T := ⟨x, hx.1, rfl⟩
    have hxcomm : x * kQ = kQ * x :=
      Subtype.ext (comm_of_mem_T_inf_chat ctx hk' hxT (hH_comm x hxH))
    exact ⟨hxH, mem_centralizer_singleton_iff.mpr hxcomm⟩
  have hcomm1 : ∀ x : Q, (x : X) * k' * (x : X)⁻¹ * k'⁻¹ = 1 → x * kQ = kQ * x := by
    intro x hx1
    have h1 : x * kQ * x⁻¹ = kQ := by
      apply Subtype.ext
      show (x : X) * k' * (x : X)⁻¹ = k'
      have h := congrArg (fun y : X => y * k') hx1
      simpa [mul_assoc] using h
    calc x * kQ = (x * kQ * x⁻¹) * x := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = kQ * x := by rw [h1]
  have hrel : N.relIndex H ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases hHN : H ≤ N
    · exact ⟨1, H.one_mem, fun b hb => Or.inr (hHN hb)⟩
    · rw [SetLike.le_def] at hHN
      push Not at hHN
      obtain ⟨g₀, hg₀H, hg₀N⟩ := hHN
      refine ⟨g₀, hg₀H, fun b hb => ?_⟩
      by_cases hbN : b ∈ N
      · exact Or.inr hbN
      · left
        have hb_not_comm : b * kQ ≠ kQ * b := fun h =>
          hbN ⟨hb, mem_centralizer_singleton_iff.mpr h⟩
        have hg₀_not_comm : g₀ * kQ ≠ kQ * g₀ := fun h =>
          hg₀N ⟨hg₀H, mem_centralizer_singleton_iff.mpr h⟩
        have hbt : (b : X) * k' * (b : X)⁻¹ * k'⁻¹ = t := by
          rcases commutator_eq_one_or_t ctx hk'T b.2 (hH_comm b hb) with h | h
          · exact absurd (hcomm1 b h) hb_not_comm
          · exact h
        have hg₀t : (g₀ : X) * k' * (g₀ : X)⁻¹ * k'⁻¹ = t := by
          rcases commutator_eq_one_or_t ctx hk'T g₀.2 (hH_comm g₀ hg₀H) with h | h
          · exact absurd (hcomm1 g₀ h) hg₀_not_comm
          · exact h
        have hbk' : (b : X) * k' * (b : X)⁻¹ = t * k' := by
          have h := congrArg (fun y : X => y * k') hbt
          simpa [mul_assoc] using h
        have hg₀k' : (g₀ : X) * k' * (g₀ : X)⁻¹ = t * k' := by
          have h := congrArg (fun y : X => y * k') hg₀t
          simpa [mul_assoc] using h
        have hbt' : (b : X) * t * (b : X)⁻¹ = t := by
          have h := mem_centralizer_singleton_iff.mp b.2
          calc (b : X) * t * (b : X)⁻¹ = t * (b : X) * (b : X)⁻¹ := by rw [h]
            _ = t := by group
        have hbgX : (b : X) * (g₀ : X) * k' * ((b : X) * (g₀ : X))⁻¹ = k' := by
          have htt : t * t = 1 := by rw [← pow_two, SD.t_sq (A := ctx.A)]
          calc (b : X) * (g₀ : X) * k' * ((b : X) * (g₀ : X))⁻¹
              = (b : X) * ((g₀ : X) * k' * (g₀ : X)⁻¹) * (b : X)⁻¹ := by group
            _ = (b : X) * (t * k') * (b : X)⁻¹ := by rw [hg₀k']
            _ = ((b : X) * t * (b : X)⁻¹) * ((b : X) * k' * (b : X)⁻¹) := by group
            _ = t * (t * k') := by rw [hbt', hbk']
            _ = k' := by rw [← mul_assoc, htt, one_mul]
        have hbg_comm : (b * g₀) * kQ = kQ * (b * g₀) := by
          have h1 : (b * g₀) * kQ * (b * g₀)⁻¹ = kQ := by
            apply Subtype.ext
            exact hbgX
          have h2 : ((b * g₀) * kQ * (b * g₀)⁻¹) * (b * g₀) = (b * g₀) * kQ := by
            rw [mul_assoc, inv_mul_cancel, mul_one]
          calc (b * g₀) * kQ = ((b * g₀) * kQ * (b * g₀)⁻¹) * (b * g₀) := h2.symm
            _ = kQ * (b * g₀) := by rw [h1]
        exact ⟨mul_mem hb hg₀H, mem_centralizer_singleton_iff.mpr hbg_comm⟩
  have hH_card : Nat.card ↥H = 96 := ctx.card_chat hk'
  have hU_card : Nat.card ↥U = 32 := ctx.card_T_inf_chat hk'
  have hNH : N ≤ H := inf_le_left
  have hcard_rel : N.relIndex H * Nat.card ↥N = 96 := by
    have h := Subgroup.relIndex_mul_card (H := N) (K := H)
    rwa [inf_of_le_left hNH, hH_card] at h
  have hcardN : Nat.card ↥N = 96 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hrel with h | h
    · rw [h, one_mul] at hcard_rel; exact hcard_rel
    · exfalso
      rw [h] at hcard_rel
      have h48 : Nat.card ↥N = 48 := by omega
      have h32 : 32 ∣ Nat.card ↥N := by
        rw [← hU_card]
        exact Subgroup.card_dvd_of_le hU_le_N
      rw [h48] at h32
      exact absurd h32 (by norm_num)
  have hN_eq_H : N = H :=
    Subgroup.eq_of_le_of_card_ge hNH (by rw [hH_card, hcardN])
  have hgH : (⟨g, hg⟩ : Q) ∈ H := by
    have h : (⟨g, hg⟩ : Q) ∈ ctx.chat k' :=
      Subgroup.mem_comap.mpr (by
        rw [mem_centralizer_singleton_iff, ← ctx.actX_of_mem hg]
        exact hcomm)
    exact h
  have hgN : (⟨g, hg⟩ : Q) ∈ N := by
    rw [← hN_eq_H] at hgH
    exact hgH
  have hgcomm : (⟨g, hg⟩ : Q) * kQ = kQ * ⟨g, hg⟩ :=
    mem_centralizer_singleton_iff.mp hgN.2
  exact Subtype.ext_iff.mp hgcomm

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx
