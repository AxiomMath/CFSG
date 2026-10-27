module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2C1b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "T₀" => (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem c1_exists_c (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hc : L2Ctx hs W) (hVS : IsSylowOf 2 V ⊤) (hSV : S.relIndex V = 2) {m : ℕ} (hm : 3 ≤ m)
    (e : ↥(S ⊓ L) ≃* DihedralGroup (2 ^ m))
    (hzy : ((e.symm (DihedralGroup.r 1) : ↥(S ⊓ L)) : X) ^ (2 ^ (m - 1)) = z)
    (hxz : ((e.symm (DihedralGroup.sr 0) : ↥(S ⊓ L)) : X) ≠ z) :
    ∃ c ∈ V, c ∉ S ∧ c * ((e.symm (DihedralGroup.sr 0) : ↥(S ⊓ L)) : X) * c⁻¹ =
      ((e.symm (DihedralGroup.sr 0) : ↥(S ⊓ L)) : X) := by
  set x : X := ((e.symm (DihedralGroup.sr 0) : ↥(S ⊓ L)) : X) with hx
  have hxD : x ∈ S ⊓ L := (e.symm (DihedralGroup.sr 0)).2
  have hx2 : x * x = 1 := by
    rw [hx, ← Subgroup.coe_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one,
      Subgroup.coe_one]
  have hx1 : x ≠ 1 := fun h => by
    have := congrArg e (Subtype.ext (h.trans (Subgroup.coe_one _).symm) :
      e.symm (DihedralGroup.sr 0) = 1)
    rw [MulEquiv.apply_symm_apply, map_one, DihedralGroup.one_def] at this
    cases this
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  have hxnz : x ∉ zpowers z := fun h => by
    rcases L415.mem_zpowers_two hz2 h with h1 | h1
    · exact hx1 h1
    · exact hxz h1
  obtain ⟨v₁, hv₁, hv₁t⟩ := hc.qc_exists_v hKF hSV
  have hv₁S : v₁ ∉ S := fun h => hs.setup.z_ne_one (by
    have h1 : v₁ * t * v₁⁻¹ = t := by
      rw [mem_centralizer_singleton_iff.mp (hs.sylow.le h)]
      group
    rw [h1] at hv₁t
    calc z = t⁻¹ * (t * z) := by group
      _ = 1 := by rw [← hv₁t]; group)
  have hST := hc.qc_S_ne hKF hSV
  obtain ⟨f', hfS, hfT⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hs.setup.T_le hST.symm)
  have hx₂D : f'⁻¹ * x * f' ∈ S ⊓ L := by
    have := hs.setup.conj_mem_D (inv_mem hfS) hxD
    rwa [inv_inv] at this
  have hfz : f'⁻¹ * z * f' = z := by
    rw [hs.setup.z_comm (inv_mem hfS)]
    group
  obtain ⟨b, hb⟩ := EndB.dih_eq_sr (by omega) e hx₂D
    (by calc f'⁻¹ * x * f' * (f'⁻¹ * x * f') = f'⁻¹ * (x * x) * f' := by group
          _ = 1 := by rw [hx2]; group)
    (fun h => hx1 (by
      calc x = f' * (f'⁻¹ * x * f') * f'⁻¹ := by group
        _ = 1 := by rw [h]; group))
    (by
      rw [hzy]
      intro h
      apply hxz
      calc x = f' * (f'⁻¹ * x * f') * f'⁻¹ := by group
        _ = f' * (f'⁻¹ * z * f') * f'⁻¹ := by rw [h, hfz]
        _ = z := by group)
  have hne : ∀ d ∈ S ⊓ L, ((e.symm (DihedralGroup.sr b) : ↥(S ⊓ L)) : X) ≠ d * x * d⁻¹ := by
    intro d hd h
    rw [← hb] at h
    apply hs.setup.conj_ne_of_not_mem_T hfS hfT hxD (by rw [sq, hx2]) hxnz (inv_mem hd)
    rw [h, inv_inv]
  have hx'D : v₁⁻¹ * x * v₁ ∈ S ⊓ L := by
    have := hc.c1_normal_D hKF hKC hVS hSV (inv_mem hv₁) hxD
    rwa [inv_inv] at this
  have hv₁z : v₁⁻¹ * z * v₁ = z := by
    rw [(mem_centralizer_iff.mp hs.z_mem_center_V.2 _ (inv_mem hv₁))]
    group
  obtain ⟨k, hk⟩ := EndB.dih_eq_sr (by omega) e hx'D
    (by calc v₁⁻¹ * x * v₁ * (v₁⁻¹ * x * v₁) = v₁⁻¹ * (x * x) * v₁ := by group
          _ = 1 := by rw [hx2]; group)
    (fun h => hx1 (by
      calc x = v₁ * (v₁⁻¹ * x * v₁) * v₁⁻¹ := by group
        _ = 1 := by rw [h]; group))
    (by
      rw [hzy]
      intro h
      apply hxz
      calc x = v₁ * (v₁⁻¹ * x * v₁) * v₁⁻¹ := by group
        _ = v₁ * (v₁⁻¹ * z * v₁) * v₁⁻¹ := by rw [h, hv₁z]
        _ = z := by group)
  obtain ⟨d, hd, hcases⟩ := EndB.dih_two_classes e hne k
  have hdV : d ∈ V := hs.le_V hd.1
  rcases hcases with h | h
  · rw [← hk] at h
    refine ⟨v₁ * d, mul_mem hv₁ hdV, fun hc' => hv₁S ?_, ?_⟩
    · have := mul_mem hc' (inv_mem hd.1)
      rwa [mul_inv_cancel_right] at this
    · calc v₁ * d * x * (v₁ * d)⁻¹ = v₁ * (d * x * d⁻¹) * v₁⁻¹ := by group
        _ = v₁ * (v₁⁻¹ * x * v₁) * v₁⁻¹ := by rw [h]
        _ = x := by group
  · rw [← hk, ← hb] at h
    refine ⟨v₁ * d * f'⁻¹, mul_mem (mul_mem hv₁ hdV) (inv_mem (hs.le_V hfS)),
      fun hc' => hv₁S ?_, ?_⟩
    · have := mul_mem hc' (mul_mem hfS (inv_mem hd.1))
      rwa [show v₁ * d * f'⁻¹ * (f' * d⁻¹) = v₁ by group] at this
    · calc v₁ * d * f'⁻¹ * x * (v₁ * d * f'⁻¹)⁻¹ =
            v₁ * (d * (f'⁻¹ * x * f') * d⁻¹) * v₁⁻¹ := by group
        _ = v₁ * (v₁⁻¹ * x * v₁) * v₁⁻¹ := by rw [h]
        _ = x := by group

theorem false_of_isSylowOf_two (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hc : L2Ctx hs W) (hVS : IsSylowOf 2 V ⊤) (hSV : S.relIndex V = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ g u : X, (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ := fun g u => rfl
  obtain ⟨m, hm, ⟨e⟩⟩ := hs.setup.dihedral
  set y : X := ((e.symm (DihedralGroup.r 1) : ↥(S ⊓ L)) : X) with hy
  have hyD : y ∈ S ⊓ L := (e.symm (DihedralGroup.r 1)).2
  have hzy : y ^ (2 ^ (m - 1)) = z := L415.symm_r_pow_half (by omega) e hs.setup.z_mem
    (fun d hd => (hs.setup.z_comm_D hd).symm) hs.setup.z_ne_one
  have hyord : orderOf y = 2 ^ m := by
    have h1 : orderOf (e.symm (DihedralGroup.r 1)) =
        orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) :=
      orderOf_injective e.symm.toMonoidHom e.symm.injective _
    rw [hy, Subgroup.orderOf_coe, h1, DihedralGroup.orderOf_r_one]
  have hyy : y⁻¹ ≠ y := fun h => by
    have h2 : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by
      rw [sq]
      nth_rewrite 1 [← h]
      exact inv_mul_cancel y)
    rw [hyord] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    have h4 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  set x : X := ((e.symm (DihedralGroup.sr 0) : ↥(S ⊓ L)) : X) with hx
  have hxD : x ∈ S ⊓ L := (e.symm (DihedralGroup.sr 0)).2
  have hxy : x * y * x⁻¹ = y⁻¹ := EndB.dih_sr_conj e 0
  have hxz : x ≠ z := fun h => hyy (by
    rw [← hxy, h]
    have h1 := hs.setup.z_comm_D hyD
    rw [← h1]
    group)
  have hx1 : x ≠ 1 := fun h => hyy (by rw [← hxy, h]; group)
  obtain ⟨g₀, -, hg₀⟩ := hs.setup.exists_conj_eq_z hKF hxD (by
    rw [sq, hx, ← Subgroup.coe_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one,
      Subgroup.coe_one]) hx1
  obtain ⟨c, hcV, hcS, hcx⟩ := hc.c1_exists_c hKF hKC hVS hSV hm e hzy hxz
  have hSC : V ⊓ centralizer ({t} : Set X) = S :=
    hs.sylow.eq_of_le (le_inf hs.le_V hs.sylow.le) inf_le_right
      (hs.sylow_V.isPGroup.to_le inf_le_left)
  have hST := hc.qc_S_ne hKF hSV
  have hct : c * t * c⁻¹ = t * z := by
    rcases hs.conj_t_of_qc hSV hST hcV with h | h
    · exfalso
      apply hcS
      rw [← hSC]
      exact Subgroup.mem_inf.mpr ⟨hcV, mem_centralizer_singleton_iff.mpr (by
        calc c * t = c * t * c⁻¹ * c := by group
          _ = t * c := by rw [h])⟩
    · exact h
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzc : t * c * t⁻¹ * c⁻¹ = z := by
    calc t * c * t⁻¹ * c⁻¹ = t * (c * t * c⁻¹)⁻¹ := by group
      _ = t * (t * z)⁻¹ := by rw [hct]
      _ = t * z⁻¹ * t⁻¹ := by group
      _ = t * z * t⁻¹ := by rw [hzi]
      _ = z * t * t⁻¹ := by rw [hs.comm_tbz.2.1]
      _ = z := by group
  have hVz : V ≤ centralizer ({z} : Set X) := fun v hv =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hs.z_mem_center_V.2 v hv)
  have hVzS : IsSylowOf 2 V (centralizer ({z} : Set X)) := by
    rw [isSylowOf_iff] at hVS ⊢
    refine ⟨hVz, hVS.2.1, fun h2 => hVS.2.2 ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact h2.trans (Subgroup.relIndex_dvd_index_of_le hVz)
  have hP₁z : (V ⊓ centralizer ({x} : Set X)).map (MulAut.conj g₀).toMonoidHom ≤
      centralizer ({z} : Set X) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hconj, mem_centralizer_singleton_iff, ← hg₀]
    have h1 : u * x = x * u := mem_centralizer_singleton_iff.mp hu.2
    calc g₀ * u * g₀⁻¹ * (g₀ * x * g₀⁻¹) = g₀ * (u * x) * g₀⁻¹ := by group
      _ = g₀ * (x * u) * g₀⁻¹ := by rw [h1]
      _ = g₀ * x * g₀⁻¹ * (g₀ * u * g₀⁻¹) := by group
  have hP₁2 : IsPGroup 2 ↥((V ⊓ centralizer ({x} : Set X)).map
      (MulAut.conj g₀).toMonoidHom) := (hs.sylow_V.isPGroup.to_le inf_le_left).map _
  obtain ⟨k₀, hk₀z, hk₀⟩ := GH74.GLS.C3.Layer2.exists_mem_conj_le_of_isSylowOf hVzS hP₁z hP₁2
  have htV : t ∈ V := hs.le_V (hs.setup.T_le (mem_sup_left (mem_sup_left (mem_zpowers t))))
  have htx : t ∈ V ⊓ centralizer ({x} : Set X) := Subgroup.mem_inf.mpr ⟨htV,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (hs.sylow.le hxD.1)).symm⟩
  have hcxC : c ∈ V ⊓ centralizer ({x} : Set X) := Subgroup.mem_inf.mpr ⟨hcV,
    mem_centralizer_singleton_iff.mpr (by
      calc c * x = c * x * c⁻¹ * c := by group
        _ = x * c := by rw [hcx])⟩
  have hmemV : ∀ u ∈ V ⊓ centralizer ({x} : Set X), (k₀⁻¹ * g₀) * u * (k₀⁻¹ * g₀)⁻¹ ∈ V := by
    intro u hu
    have := hk₀ _ ⟨u, hu, rfl⟩
    rw [hconj] at this
    rwa [show k₀⁻¹ * (g₀ * u * g₀⁻¹) * k₀ = (k₀⁻¹ * g₀) * u * (k₀⁻¹ * g₀)⁻¹ by group]
      at this
  have hgx : (k₀⁻¹ * g₀) * x * (k₀⁻¹ * g₀)⁻¹ = z := by
    have hk : k₀ * z = z * k₀ := (mem_centralizer_singleton_iff.mp hk₀z)
    calc (k₀⁻¹ * g₀) * x * (k₀⁻¹ * g₀)⁻¹ = k₀⁻¹ * (g₀ * x * g₀⁻¹) * k₀ := by group
      _ = k₀⁻¹ * (z * k₀) := by rw [hg₀]; group
      _ = z := by rw [← hk]; group
  set g := k₀⁻¹ * g₀ with hgdef
  have haV := hmemV t htx
  have hbV := hmemV c hcxC
  have hζ : (g * t * g⁻¹) * (g * c * g⁻¹) * (g * t * g⁻¹)⁻¹ * (g * c * g⁻¹)⁻¹ = g * z * g⁻¹ := by
    rw [← hzc]
    group
  have hTS2 : (T₀).relIndex S = 2 := by
    have h1 := Subgroup.relIndex_mul_card T₀ S
    rw [inf_of_le_left hs.setup.T_le] at h1
    obtain ⟨-, -, -, hST2⟩ := hc.qc_structure hKF hSV
    have hpos : 0 < Nat.card T₀ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans hST2)
  have hsq : ∀ v ∈ V, v ^ 2 ∈ T₀ := fun v hv =>
    hs.setup.sq_mem_T_of_relIndex hKF hKC hs.sylow_V hs.le_V hTS2 hSV hv
  have hTn : ∀ v ∈ V, ∀ u ∈ T₀, v * u * v⁻¹ ∈ T₀ := fun v hv u hu =>
    (mem_normalizer_iff.mp (hs.sylow_V.le hv) u).mp hu
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b * a⁻¹ * b⁻¹ ∈ T₀ := by
    intro a ha b hb
    have e1 : a * b * a⁻¹ * b⁻¹ = (a * b) ^ 2 * (b⁻¹ * (a ^ 2)⁻¹ * b⁻¹⁻¹) * (b ^ 2)⁻¹ := by
      simp only [sq, mul_inv_rev, inv_inv]
      group
    rw [e1]
    exact mul_mem (mul_mem (hsq _ (mul_mem ha hb)) (hTn _ (inv_mem hb) _ (inv_mem (hsq a ha))))
      (inv_mem (hsq b hb))
  have hζT := hζ ▸ hcomm _ haV _ hbV
  have hζD := hc.c1_mem_D hKF hKC hVS hSV hζT
  have hζz : g * z * g⁻¹ ≠ z := fun h => hxz (by
    have h1 : g * x * g⁻¹ = g * z * g⁻¹ := by rw [hgx, h]
    simpa [mul_assoc] using congrArg (fun u => g⁻¹ * u * g) h1)
  have hζ1 : g * z * g⁻¹ ≠ 1 := fun h => hs.setup.z_ne_one (by
    simpa [mul_assoc] using congrArg (fun u => g⁻¹ * u * g) h)
  have hζ2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  obtain ⟨k', hk'⟩ := EndB.dih_eq_sr (by omega) e hζD hζ2 hζ1 (by rw [hzy]; exact hζz)
  have hinv : (g * z * g⁻¹) * y * (g * z * g⁻¹)⁻¹ = y⁻¹ := by
    rw [hk']
    exact EndB.dih_sr_conj e k'
  have hnorm : ∀ v ∈ V, v * y * v⁻¹ ∈ zpowers y := fun v hv =>
    EndB.dih_conj_r_mem (by omega) e fun d hd => hc.c1_normal_D hKF hKC hVS hSV hv hd
  have hnorm' : ∀ v ∈ V, v⁻¹ * y * v ∈ zpowers y := fun v hv => by
    have := hnorm _ (inv_mem hv)
    rwa [inv_inv] at this
  have hfix := EndB.comm_conj_eq (hnorm _ haV) (hnorm' _ haV) (hnorm _ hbV) (hnorm' _ hbV)
  rw [hζ, hinv] at hfix
  exact hyy hfix

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
