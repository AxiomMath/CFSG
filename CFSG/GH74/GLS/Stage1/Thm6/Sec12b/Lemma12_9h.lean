module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9g

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

section

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G} {a : G}
  {V P₁ F' : Subgroup G}

namespace Ph1

theorem final_contra (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') {w b u p' : G} (hwF : w ∈ F') (hww : w * w = x)
    (hbS : b ∈ S) (hbT : b ∉ T) (hb2 : b * b = 1) (hp'P : p' ∈ P₁) (huu : u * u = x * z)
    (hu : u = w⁻¹ * p') (hbp : b * p' * b⁻¹ = u * w) : False := by
  have hwT : w ∈ T := B.F_le hwF
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right H.base.x_sq
  have hww' : w⁻¹ * w⁻¹ = x := by
    calc w⁻¹ * w⁻¹ = (w * w)⁻¹ := by group
      _ = x⁻¹ := by rw [hww]
      _ = x := hxinv
  obtain ⟨ρ, s, j, hD, hz⟩ := B.dih_data H
  have hbD : ∀ d, d ∈ P₁ ↔ b * d * b⁻¹ ∈ P₁ := B.P1_conj_iff H A hbS
  have hxzc : x * z = z * x := (H.hz.z_central x H.base.x_mem_T).symm
  have hzw : w⁻¹ * z = z * w⁻¹ := (H.hz.z_central w⁻¹ (T.inv_mem hwT)).symm
  rcases B.comm_w_P1 H A hwF hww hp'P with hδ | hδ
  ·
    have hwp : w * p' * w⁻¹ = p' := mul_inv_eq_one.1 hδ
    have hcomm : w⁻¹ * p' = p' * w⁻¹ := by
      calc w⁻¹ * p' = w⁻¹ * (w * p' * w⁻¹) := by rw [hwp]
        _ = p' * w⁻¹ := by group
    have hpp : p' * p' = z := by
      have h1 : u * u = (w⁻¹ * w⁻¹) * (p' * p') := by
        rw [hu]
        calc w⁻¹ * p' * (w⁻¹ * p') = w⁻¹ * (p' * w⁻¹) * p' := by group
          _ = w⁻¹ * (w⁻¹ * p') * p' := by rw [hcomm]
          _ = (w⁻¹ * w⁻¹) * (p' * p') := by group
      rw [hww', huu] at h1
      exact (mul_left_cancel h1).symm
    have hbp' : b * p' * b⁻¹ = p' := by
      rw [hbp, hu]
      calc w⁻¹ * p' * w = (p' * w⁻¹) * w := by rw [hcomm]
        _ = p' := by group
    obtain ⟨c, hcP, hc2, hc1, hcz, hyc⟩ := hD.exists_normalized_four_of_order_four hb2 hbD hp'P
      (by rw [← hz]; exact hpp) hbp'
    rw [← hz] at hcz hyc
    obtain ⟨k1, k2⟩ := B.K1pp H A hcP hc2 hc1 hcz b hbS hbT
    rcases hyc with e | e
    · exact k1 e
    · exact k2 e
  ·
    have hwp : w * p' * w⁻¹ = z * p' := mul_inv_eq_iff_eq_mul.1 hδ
    have hpz : z * p' = p' * z := H.hz.z_central p' (B.P1_le_T H hp'P)
    have hpw : p' * w⁻¹ = z * (w⁻¹ * p') := by
      calc p' * w⁻¹ = w⁻¹ * (w * p' * w⁻¹) := by group
        _ = w⁻¹ * (z * p') := by rw [hwp]
        _ = (w⁻¹ * z) * p' := by group
        _ = (z * w⁻¹) * p' := by rw [hzw]
        _ = z * (w⁻¹ * p') := by group
    have hpp : p' * p' = 1 := by
      have h1 : u * u = z * ((w⁻¹ * w⁻¹) * (p' * p')) := by
        rw [hu]
        calc w⁻¹ * p' * (w⁻¹ * p') = w⁻¹ * (p' * w⁻¹) * p' := by group
          _ = w⁻¹ * (z * (w⁻¹ * p')) * p' := by rw [hpw]
          _ = (w⁻¹ * z) * (w⁻¹ * p') * p' := by group
          _ = (z * w⁻¹) * (w⁻¹ * p') * p' := by rw [hzw]
          _ = z * ((w⁻¹ * w⁻¹) * (p' * p')) := by group
      rw [hww', huu] at h1
      have h2 : z * x = z * (x * (p' * p')) := by rw [← hxzc]; exact h1
      have h3 : x = x * (p' * p') := mul_left_cancel h2
      have h4 : x * 1 = x * (p' * p') := by rw [mul_one]; exact h3
      exact (mul_left_cancel h4).symm
    have hbp' : b * p' * b⁻¹ = z * p' := by
      rw [hbp, hu]
      have h1 : p' = z * (w⁻¹ * p' * w) := by
        calc p' = w⁻¹ * (w * p' * w⁻¹) * w := by group
          _ = w⁻¹ * (z * p') * w := by rw [hwp]
          _ = (w⁻¹ * z) * p' * w := by group
          _ = (z * w⁻¹) * p' * w := by rw [hzw]
          _ = z * (w⁻¹ * p' * w) := by group
      have h2 : z * p' = z * (z * (w⁻¹ * p' * w)) := by rw [← h1]
      calc w⁻¹ * p' * w = z * (z * (w⁻¹ * p' * w)) := by
            rw [← mul_assoc, H.hz.z_sq, one_mul]
        _ = z * p' := by rw [← h1]
    have hp1 : p' ≠ 1 := by
      intro h1
      apply H.hz.z_ne_one
      rw [h1] at hbp'
      simpa using hbp'.symm
    have hpz' : p' ≠ z := by
      intro h1
      apply H.hz.z_ne_one
      rw [h1, Ph0.sz H A b hbS] at hbp'
      have : z = z * z := hbp'
      rw [H.hz.z_sq] at this
      exact this
    refine (B.K1pp H A hp'P hpp hp1 hpz' b hbS hbT).2 ?_
    rw [hbp', hpz]

theorem case3b (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') (hF : F' ≠ Subgroup.zpowers x) : False := by
  obtain ⟨w, hwF, hww⟩ := B.exists_w H hF
  have hwT : w ∈ T := B.F_le hwF
  have hwS : w ∈ S := H.base.T_le_S hwT
  have hwRd : w ∉ Rd := by
    intro hw
    have h1 : w ∈ F' ⊓ Rd := ⟨hwF, hw⟩
    rw [B.F_inf] at h1
    rcases zpowers_sq_cases H.base.x_sq h1 with h | h
    · exact H.base.x_ne_one (by
        calc x = w * w := hww.symm
          _ = 1 := by rw [h, one_mul])
    · exact H.base.x_ne_one (by
        calc x = w * w := hww.symm
          _ = 1 := by rw [h]; exact H.base.x_sq)
  have := B.F_cyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥F')
  obtain ⟨f, hfF, hgen⟩ : ∃ f ∈ F', ∀ y ∈ F', ∃ k : ℤ, f ^ k = y := by
    refine ⟨(g : G), g.2, fun y hy => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hfT : f ∈ T := B.F_le hfF
  have hfS : f ∈ S := H.base.T_le_S hfT
  have hF'eq : F' = Subgroup.zpowers f := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := hgen y hy
      exact Subgroup.mem_zpowers_iff.2 ⟨k, hk⟩
    · exact (Subgroup.zpowers_le).2 hfF
  have hTgen : ∀ t ∈ T, ∃ k : ℤ, ∃ r ∈ Rd, t = f ^ k * r := by
    intro t ht
    have ht' : t ∈ Rd ⊔ Subgroup.zpowers f := by rw [← hF'eq, B.T_eq]; exact ht
    obtain ⟨a', ha', r, hr, hd⟩ := mem_sup_zpowers_of_normalIn H.base.Rd_normal hfT ht'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
    exact ⟨k, r, hr, hd⟩
  obtain ⟨j, r, hr, haj⟩ := hTgen _ A.a_sq
  obtain ⟨N₀, g₀, Nd₀⟩ : ∃ (N : Subgroup G) (g₀ : G), NData S T Rd N g₀ w := by
    obtain ⟨l, hl | hl⟩ := Int.even_or_odd' j
    · rw [hl] at haj
      have hfl : f ^ (-l) ∈ S := S.zpow_mem hfS _
      have hb₀S : a * f ^ (-l) ∈ S := S.mul_mem A.a_mem hfl
      have hb₀T : a * f ^ (-l) ∉ T := by
        intro h
        apply A.a_not
        have : a = (a * f ^ (-l)) * (f ^ (-l))⁻¹ := by group
        rw [this]
        exact T.mul_mem h (T.inv_mem (T.zpow_mem hfT _))
      have hc := B.S_comm_Rd H A hF (f ^ (-l)) hfl a A.a_mem
      have hca : a * (f ^ (-l) * a * (f ^ (-l))⁻¹ * a⁻¹) * a⁻¹ ∈ Rd :=
        B.Rd_normalS H A a A.a_mem _ hc
      have hfr : f ^ (2 * l) * r * (f ^ (2 * l))⁻¹ ∈ Rd :=
        B.Rd_normalS H A (f ^ (2 * l)) (S.zpow_mem hfS _) r hr
      have haa : a⁻¹ * a⁻¹ = r⁻¹ * (f ^ (2 * l))⁻¹ := by
        have : (a * a)⁻¹ = (f ^ (2 * l) * r)⁻¹ := by rw [haj]
        simpa [mul_inv_rev] using this
      have hb₀2 : (a * f ^ (-l)) * (a * f ^ (-l)) ∈ Rd := by
        have e : (a * f ^ (-l)) * (a * f ^ (-l)) =
            (a * (f ^ (-l) * a * (f ^ (-l))⁻¹ * a⁻¹) * a⁻¹) *
              (f ^ (2 * l) * r * (f ^ (2 * l))⁻¹) := by
          calc (a * f ^ (-l)) * (a * f ^ (-l))
              = a * f ^ (-l) * a * f ^ l * (a⁻¹ * a⁻¹) * (f ^ (2 * l) * r * (f ^ (2 * l))⁻¹) := by
                rw [haa]; group
            _ = _ := by group
        rw [e]; exact Rd.mul_mem hca hfr
      exact ⟨_, _, B.NData_of_b₀ H A hF hfF hTgen hb₀S hb₀T hb₀2 hwRd hwT⟩
    · exact ⟨Rd, a, B.NData_of_odd H A hfF hTgen hr haj ⟨l, hl⟩ hwRd⟩
  obtain ⟨b, hbS, hbT, hb2, -⟩ := B.inv_coset H A hwF hww Nd₀
  have Nd₁ : NData S T Rd (Rd ⊔ Subgroup.zpowers b) f w :=
    B.NData_of_b₀ H A hF hfF hTgen hbS hbT (by rw [hb2]; exact Rd.one_mem) hwRd hwT
  obtain ⟨b', hb'S, hb'T, hb'2, hb'N⟩ := B.inv_coset H A hwF hww Nd₁
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hb'inv : b'⁻¹ = b' := inv_eq_of_mul_eq_one_right hb'2
  have hbb' : b * b' ∈ T := by
    have := H.coset_eq (S.inv_mem hbS) hb'S (fun h => hbT (by simpa using T.inv_mem h)) hb'T
    simpa using this
  have hbN₁ : b ∈ Rd ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hm : w⁻¹ * (b * b') ∈ Rd := by
    have hmN : w⁻¹ * (b * b') ∈ Rd ⊔ Subgroup.zpowers b := by
      have e : w⁻¹ * (b * b') = (w⁻¹ * b * w⁻¹⁻¹) * (w⁻¹ * b') := by group
      rw [e]
      exact Subgroup.mul_mem _ (Nd₁.normal w⁻¹ (S.inv_mem hwS) b hbN₁) hb'N
    exact Nd₁.inter _ hmN (T.mul_mem (T.inv_mem hwT) hbb')
  obtain ⟨β, hβdef⟩ : ∃ β : G, β = w⁻¹ * (b * b') := ⟨_, rfl⟩
  rw [← hβdef] at hm
  have hββ : b * b' = w * β := by rw [hβdef]; group
  have hrel : b * (w * β) * b⁻¹ = (w * β)⁻¹ := by
    rw [← hββ]
    calc b * (b * b') * b⁻¹ = (b * b) * b' * b⁻¹ := by group
      _ = b' * b⁻¹ := by rw [hb2, one_mul]
      _ = b'⁻¹ * b⁻¹ := by rw [hb'inv]
      _ = (b * b')⁻¹ := by group
  have hxy := Ph0.sx H A hbS hbT
  obtain ⟨u, hudef⟩ : ∃ u : G, u = b * w * b⁻¹ := ⟨_, rfl⟩
  obtain ⟨p', hp'def⟩ : ∃ p' : G, p' = w * u := ⟨_, rfl⟩
  have hu : u = (w * β)⁻¹ * (b * β * b⁻¹)⁻¹ := by
    have h1 : u * (b * β * b⁻¹) = (w * β)⁻¹ := by
      rw [hudef, ← hrel]; group
    exact eq_mul_inv_of_mul_eq h1
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right H.base.x_sq
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right H.hz.z_sq
  have hxzc : x * z = z * x := (H.hz.z_central x H.base.x_mem_T).symm
  have hp'P : p' ∈ P₁ := by
    have hβRd : β ∈ Rd := hm
    rw [← B.sup_x] at hβRd
    obtain ⟨q, hq, c, hc, hβq⟩ := mem_sup_of_commute
      (comm_zpowers (fun u hu => H.base.x_central u (B.P1_le_T H hu))) hβRd
    have hq₂ : w * q⁻¹ * w⁻¹ ∈ P₁ := B.P1_normalS H A w hwS q⁻¹ (P₁.inv_mem hq)
    have hq₃ : (b * q * b⁻¹)⁻¹ ∈ P₁ := P₁.inv_mem (B.P1_normalS H A b hbS q hq)
    have e0 : p' = (w * β⁻¹ * w⁻¹) * (b * β * b⁻¹)⁻¹ := by
      rw [hp'def, hu]; group
    rw [e0]
    rcases zpowers_sq_cases H.base.x_sq hc with h1 | h1
    · rw [h1, mul_one] at hβq
      rw [hβq]
      exact P₁.mul_mem hq₂ hq₃
    · rw [h1] at hβq
      rw [hβq]
      have hwx : w * x⁻¹ * w⁻¹ = x⁻¹ := by
        have h2 := H.base.x_central w hwT
        calc w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
          _ = x⁻¹ := by
            have : w * x * w⁻¹ = x := by
              calc w * x * w⁻¹ = (x * w) * w⁻¹ := by rw [h2]
                _ = x := by group
            rw [this]
      have hbq : b * (q * x) * b⁻¹ = (b * q * b⁻¹) * (x * z) := by
        calc b * (q * x) * b⁻¹ = (b * q * b⁻¹) * (b * x * b⁻¹) := by group
          _ = (b * q * b⁻¹) * (x * z) := by rw [hxy]
      have e1 : (w * (q * x)⁻¹ * w⁻¹) * (b * (q * x) * b⁻¹)⁻¹ =
          x⁻¹ * (w * q⁻¹ * w⁻¹) * (x * z)⁻¹ * (b * q * b⁻¹)⁻¹ := by
        rw [hbq]
        calc (w * (q * x)⁻¹ * w⁻¹) * ((b * q * b⁻¹) * (x * z))⁻¹
            = (w * x⁻¹ * w⁻¹) * (w * q⁻¹ * w⁻¹) * (x * z)⁻¹ * (b * q * b⁻¹)⁻¹ := by group
          _ = x⁻¹ * (w * q⁻¹ * w⁻¹) * (x * z)⁻¹ * (b * q * b⁻¹)⁻¹ := by rw [hwx]
      have hxq₂ : x * (w * q⁻¹ * w⁻¹) = (w * q⁻¹ * w⁻¹) * x :=
        H.base.x_central _ (B.P1_le_T H hq₂)
      have e2 : x⁻¹ * (w * q⁻¹ * w⁻¹) * (x * z)⁻¹ * (b * q * b⁻¹)⁻¹ =
          (w * q⁻¹ * w⁻¹) * z * (b * q * b⁻¹)⁻¹ := by
        rw [mul_inv_rev, hxinv, hzinv]
        calc x * (w * q⁻¹ * w⁻¹) * (z * x) * (b * q * b⁻¹)⁻¹
            = ((x * (w * q⁻¹ * w⁻¹)) * (z * x)) * (b * q * b⁻¹)⁻¹ := rfl
          _ = (((w * q⁻¹ * w⁻¹) * x) * (z * x)) * (b * q * b⁻¹)⁻¹ := by rw [hxq₂]
          _ = ((w * q⁻¹ * w⁻¹) * (x * z) * x) * (b * q * b⁻¹)⁻¹ := by group
          _ = ((w * q⁻¹ * w⁻¹) * (z * x) * x) * (b * q * b⁻¹)⁻¹ := by rw [hxzc]
          _ = ((w * q⁻¹ * w⁻¹) * z * (x * x)) * (b * q * b⁻¹)⁻¹ := by group
          _ = (w * q⁻¹ * w⁻¹) * z * (b * q * b⁻¹)⁻¹ := by rw [H.base.x_sq, mul_one]
      rw [e1, e2]
      exact P₁.mul_mem (P₁.mul_mem hq₂ (B.z_mem_P1 H)) hq₃
  have huu : u * u = x * z := by
    calc u * u = b * (w * w) * b⁻¹ := by rw [hudef]; group
      _ = x * z := by rw [hww]; exact hxy
  have hu' : u = w⁻¹ * p' := by rw [hp'def]; group
  have hbu : b * u * b⁻¹ = w := by
    calc b * u * b⁻¹ = (b * b) * w * (b * b)⁻¹ := by rw [hudef]; group
      _ = w := by rw [hb2]; group
  have hbp : b * p' * b⁻¹ = u * w := by
    calc b * p' * b⁻¹ = (b * w * b⁻¹) * (b * u * b⁻¹) := by rw [hp'def]; group
      _ = u * w := by rw [hbu, ← hudef]
  exact B.final_contra H A hwF hww hbS hbT hb2 hp'P huu hu' hbp

end Ph1

end

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
