module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

private theorem commutator_commutatorElement_eq_one {G : Type*} [Group G] {t' : G}
    (hcent : ∀ g : G, ⁅g, t'⁆ ∈ Subgroup.center G) (a b : G) : ⁅⁅a, b⁆, t'⁆ = 1 := by
  let ψ : G →* Subgroup.center G :=
    { toFun := fun g => ⟨⁅g, t'⁆, hcent g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show ⁅a * b, t'⁆ = ⁅a, t'⁆ * ⁅b, t'⁆
        have hconj : a * ⁅b, t'⁆ * a⁻¹ = ⁅b, t'⁆ := by
          rw [Subgroup.mem_center_iff.mp (hcent b) a]; group
        rw [commutatorElement_mul_left_eq_conj_mul, hconj]
        exact (Subgroup.mem_center_iff.mp (hcent b) ⁅a, t'⁆).symm) }
  have hmem : ⁅a, b⁆ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have h1 : ψ ⁅a, b⁆ = 1 := MonoidHom.mem_ker.mp hmem
  exact congrArg Subtype.val h1

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

private theorem V_le_Y' : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left

private theorem V'_le_Y' : V' ≤ Y := by rw [h.Y_eq]; exact le_sup_right

private theorem V_le_Q' : V ≤ Q := fun x hx => h.Y_le_Q (h.V_le_Y' hx)

private theorem comm_tau_mem_Q (a : H) : a * τ * a⁻¹ * τ⁻¹ ∈ Q := by
  haveI hQn : Q.Normal := ⟨fun x hx g => h.normal_Q g x hx⟩
  have hgE : a * τ * a⁻¹ ∈ centralizer (Y : Set H) := h.E_normal h.tau_mem_E
  have hgEE : a * τ * a⁻¹ ∈ Q ⊔ zpowers τ := by rw [← h.E_eq]; exact hgE
  obtain ⟨q, hq, zz, hzz, hxz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Q) (t := zpowers τ)).mp hgEE
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hzz
  have htau2 : τ ^ (2 : ℕ) = 1 := by rw [pow_two]; exact h.tau_sq
  have hmod : τ ^ n = τ ^ (n % (2 : ℤ)) := zpow_eq_zpow_emod' n htau2
  rw [← hn, hmod] at hxz
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · exfalso
    rw [h0, zpow_zero, mul_one] at hxz
    have hτQ : τ ∈ Q := by
      have heq : τ = a⁻¹ * q * a := by
        calc τ = a⁻¹ * (a * τ * a⁻¹) * a := by group
          _ = a⁻¹ * q * a := by rw [← hxz]
      rw [heq]
      simpa using h.normal_Q a⁻¹ q hq
    exact h.tau_not_mem_Q hτQ
  · rw [h1, zpow_one] at hxz
    have hgoal : a * τ * a⁻¹ * τ⁻¹ = q := by rw [← hxz]; group
    rw [hgoal]; exact hq

theorem E_cent_mod_Q {a e : H} (he : e ∈ centralizer (Y : Set H)) : a * e * a⁻¹ * e⁻¹ ∈ Q := by
  haveI hQn : Q.Normal := ⟨fun x hx g => h.normal_Q g x hx⟩
  let φ : H →* H ⧸ Q := QuotientGroup.mk' Q
  let K : Subgroup H := (Subgroup.centralizer ({φ a} : Set (H ⧸ Q))).comap φ
  have hφ1 : ∀ x : H, φ x = 1 ↔ x ∈ Q := by
    intro x
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' (N := Q)]
  have hQK : Q ≤ K := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    rw [(hφ1 x).mpr hx, one_mul, mul_one]
  have hτK : τ ∈ K := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have hcomm : ⁅φ a, φ τ⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (hφ1 ⁅a, τ⁆).mpr (by simpa [commutatorElement_def] using h.comm_tau_mem_Q a)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  have hEK : centralizer (Y : Set H) ≤ K := by
    rw [h.E_eq]
    exact sup_le hQK (Subgroup.zpowers_le.mpr hτK)
  have heK := hEK he
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at heK
  have hmem : φ (a * e * a⁻¹ * e⁻¹) = 1 := by
    rw [show φ (a * e * a⁻¹ * e⁻¹) = ⁅φ a, φ e⁆ by
          rw [← map_commutatorElement, commutatorElement_def]]
    exact commutatorElement_eq_one_iff_mul_comm.mpr heK.symm
  exact (hφ1 _).mp hmem

private theorem mk_center_of_mem_E [hQn : Q.Normal] {a : H}
    (ha : a ∈ centralizer (Y : Set H)) :
    (QuotientGroup.mk' Q a : H ⧸ Q) ∈ Subgroup.center (H ⧸ Q) := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (N := Q) x
  have h2 : ⁅(QuotientGroup.mk' Q b : H ⧸ Q), QuotientGroup.mk' Q a⁆ = 1 := by
    rw [← map_commutatorElement]
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' (N := Q)]
    simpa [commutatorElement_def] using h.E_cent_mod_Q (a := b) ha
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

theorem Mh_comm_t {m : H} (hm : m ∈ Mh) : m * t * m⁻¹ * t⁻¹ ∈ Q := by
  haveI hQn : Q.Normal := ⟨fun x hx g => h.normal_Q g x hx⟩
  let φ : H →* H ⧸ Q := QuotientGroup.mk' Q
  let K : Subgroup H := (Subgroup.centralizer ({φ t} : Set (H ⧸ Q))).comap φ
  have hφ1 : ∀ x : H, φ x = 1 ↔ x ∈ Q := by
    intro x
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' (N := Q)]
  have hcent : ∀ g : H ⧸ Q, ⁅g, φ t⁆ ∈ Subgroup.center (H ⧸ Q) := by
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (N := Q) g
    rw [← map_commutatorElement]
    exact h.mk_center_of_mem_E (by simpa [commutatorElement_def] using h.comm_t_mem_E c)
  have hcomm : ∀ a b : H, ⁅a, b⁆ ∈ K := by
    intro a b
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have hh := commutator_commutatorElement_eq_one hcent (φ a) (φ b)
    rw [show ⁅φ a, φ b⁆ = φ ⁅a, b⁆ from (map_commutatorElement φ a b).symm] at hh
    exact commutatorElement_eq_one_iff_mul_comm.mp hh
  have hKsup : ⁅Mh, zpowers ρ⁆ ⊔ zpowers τ ≤ K := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro x _ y _
      exact hcomm x y
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, h.t_tau]
  have hmK : m ∈ K := hKsup (h.Mh_le_comm_sup hMh hm)
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hmK
  have hmem : φ (m * t * m⁻¹ * t⁻¹) = 1 := by
    rw [show φ (m * t * m⁻¹ * t⁻¹) = ⁅φ m, φ t⁆ by
          rw [← map_commutatorElement, commutatorElement_def]]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hmK
  exact (hφ1 _).mp hmem

theorem Mh_comm_Q {m q : H} (hm : m ∈ Mh) (hq : q ∈ Q) : m * q * m⁻¹ * q⁻¹ ∈ V := by
  haveI hVn : V.Normal := ⟨fun x hx g => h.normal_V g x hx⟩
  let φ : H →* H ⧸ V := QuotientGroup.mk' V
  let K : Subgroup H := (Subgroup.centralizer ({φ m} : Set (H ⧸ V))).comap φ
  have hφ1 : ∀ x : H, φ x = 1 ↔ x ∈ V := by
    intro x
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' (N := V)]
  have hV'K : V' ≤ K := by
    intro u hu
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have huY : u ∈ Y := h.V'_le_Y' hu
    have hmuV : m * u * m⁻¹ * u⁻¹ ∈ V := h.Mh_comm_Y hMh hm huY
    have h2 : ⁅φ m, φ u⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (hφ1 ⁅m, u⁆).mpr (by simpa [commutatorElement_def] using hmuV)
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  have hBK : B ≤ K := by
    intro b hb
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have hbQ : b ∈ Q := h.B_le_Q hb
    set mbm : H := m * b * m⁻¹ with hmbmdef
    have hmbmQ : mbm ∈ Q := by rw [hmbmdef]; exact h.normal_Q m b hbQ
    set x' : H := m⁻¹ * t * m * t⁻¹ with hx'def
    have hx'Q : x' ∈ Q := by
      rw [hx'def]
      simpa using h.Mh_comm_t hMh (Mh.inv_mem hm)
    have htm : t * m = m * x' * t := by rw [hx'def]; group
    have hx'b : x' * b = b * x' := h.Q_comm x' hx'Q b hbQ
    have hconj_x'b : x' * b * x'⁻¹ = b := by rw [hx'b]; group
    have htb : t * mbm * t⁻¹ = mbm := by
      calc t * mbm * t⁻¹ = (t * m) * b * (t * m)⁻¹ := by rw [hmbmdef]; group
        _ = (m * x' * t) * b * (m * x' * t)⁻¹ := by rw [htm]
        _ = m * x' * (t * b * t⁻¹) * x'⁻¹ * m⁻¹ := by group
        _ = m * x' * b * x'⁻¹ * m⁻¹ := by rw [h.B_cent_t b hb]; group
        _ = m * b * m⁻¹ := by
              calc m * x' * b * x'⁻¹ * m⁻¹ = m * (x' * b * x'⁻¹) * m⁻¹ := by group
                _ = m * b * m⁻¹ := by rw [hconj_x'b]
        _ = mbm := by rw [← hmbmdef]
    have hcomm : t * mbm = mbm * t := by
      have hh := congrArg (fun x => x * t) htb
      simpa using hh
    have hmbmB : mbm ∈ B := h.cent_t_Q mbm hmbmQ hcomm
    have hcB : mbm * b⁻¹ ∈ B := B.mul_mem hmbmB (B.inv_mem hb)
    have htc : t * (mbm * b⁻¹) = (mbm * b⁻¹) * t := h.B_cent_t _ hcB
    have hmbm_sq : mbm * mbm = b * b := by
      have hb2V : b * b ∈ V := by simpa [pow_two] using h.sq_mem_V b hbQ
      calc mbm * mbm = m * (b * b) * m⁻¹ := by rw [hmbmdef]; group
        _ = b * b := h.Mh_cent_V hMh hm hb2V
    have hcQ : mbm * b⁻¹ ∈ Q := Q.mul_mem hmbmQ (Q.inv_mem hbQ)
    have hc_sq : (mbm * b⁻¹) * (mbm * b⁻¹) = 1 := by
      calc (mbm * b⁻¹) * (mbm * b⁻¹) = mbm * (b⁻¹ * mbm) * b⁻¹ := by group
        _ = mbm * (mbm * b⁻¹) * b⁻¹ := by
              rw [← h.Q_comm mbm hmbmQ b⁻¹ (Q.inv_mem hbQ)]
        _ = (mbm * mbm) * (b⁻¹ * b⁻¹) := by group
        _ = (b * b) * (b⁻¹ * b⁻¹) := by rw [hmbm_sq]
        _ = 1 := by group
    have hcY : mbm * b⁻¹ ∈ Y := h.Y_mem _ hcQ hc_sq
    have hcV : mbm * b⁻¹ ∈ V := h.Y_cent_t _ hcY htc
    have h2 : ⁅φ m, φ b⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (hφ1 ⁅m, b⁆).mpr (by simpa [commutatorElement_def, hmbmdef] using hcV)
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  have hQK : Q ≤ K := by rw [h.Q_eq]; exact sup_le hBK hV'K
  have hqK := hQK hq
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hqK
  have hmem : φ (m * q * m⁻¹ * q⁻¹) = 1 := by
    rw [show φ (m * q * m⁻¹ * q⁻¹) = ⁅φ m, φ q⁆ by
          rw [← map_commutatorElement, commutatorElement_def]]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hqK.symm
  exact (hφ1 _).mp hmem

theorem Mh_sq_mem_Q {m : H} (hm : m ∈ Mh) : m * m ∈ Q := by
  refine h.cent_Q (m * m) fun q hq => ?_
  set w : H := m * q * m⁻¹ * q⁻¹ with hwdef
  have hwV : w ∈ V := by rw [hwdef]; exact h.Mh_comm_Q hMh hm hq
  have hwY : w ∈ Y := h.V_le_Y' hwV
  have hww : w * w = 1 := h.Y_sq _ hwY
  have hcent : m * w * m⁻¹ = w := h.Mh_cent_V hMh hm hwV
  have hwq : m * q * m⁻¹ = w * q := by rw [hwdef]; group
  have hkey : (m * m) * q * (m * m)⁻¹ = q := by
    calc (m * m) * q * (m * m)⁻¹ = m * (m * q * m⁻¹) * m⁻¹ := by group
      _ = m * (w * q) * m⁻¹ := by rw [hwq]
      _ = (m * w * m⁻¹) * (m * q * m⁻¹) := by group
      _ = w * (m * q * m⁻¹) := by rw [hcent]
      _ = w * (w * q) := by rw [hwq]
      _ = (w * w) * q := by group
      _ = q := by rw [hww, one_mul]
  calc (m * m) * q = ((m * m) * q * (m * m)⁻¹) * (m * m) := by group
    _ = q * (m * m) := by rw [hkey]

theorem Mh_comm_mem_Q {a b : H} (ha : a ∈ Mh) (hb : b ∈ Mh) : a * b * a⁻¹ * b⁻¹ ∈ Q := by
  refine h.cent_Q (a * b * a⁻¹ * b⁻¹) fun q hq => ?_
  have hsame : ∀ r ∈ Q,
      (a * b) * r * (a * b)⁻¹ = (b * a) * r * (b * a)⁻¹ := by
    intro r hr
    set wa : H := a * r * a⁻¹ * r⁻¹ with hwa
    set wb : H := b * r * b⁻¹ * r⁻¹ with hwb
    have hwaV : wa ∈ V := by rw [hwa]; exact h.Mh_comm_Q hMh ha hr
    have hwbV : wb ∈ V := by rw [hwb]; exact h.Mh_comm_Q hMh hb hr
    have hwaq : a * r * a⁻¹ = wa * r := by rw [hwa]; group
    have hwbq : b * r * b⁻¹ = wb * r := by rw [hwb]; group
    have hcent_wb : a * wb * a⁻¹ = wb := h.Mh_cent_V hMh ha hwbV
    have hcent_wa : b * wa * b⁻¹ = wa := h.Mh_cent_V hMh hb hwaV
    have hcomm_w : wa * wb = wb * wa :=
      h.Q_comm wa (h.V_le_Q' hwaV) wb (h.V_le_Q' hwbV)
    have h1 : (a * b) * r * (a * b)⁻¹ = (wb * wa) * r := by
      calc (a * b) * r * (a * b)⁻¹ = a * (b * r * b⁻¹) * a⁻¹ := by group
        _ = a * (wb * r) * a⁻¹ := by rw [hwbq]
        _ = (a * wb * a⁻¹) * (a * r * a⁻¹) := by group
        _ = wb * (wa * r) := by rw [hcent_wb, hwaq]
        _ = (wb * wa) * r := by group
    have h2 : (b * a) * r * (b * a)⁻¹ = (wb * wa) * r := by
      calc (b * a) * r * (b * a)⁻¹ = b * (a * r * a⁻¹) * b⁻¹ := by group
        _ = b * (wa * r) * b⁻¹ := by rw [hwaq]
        _ = (b * wa * b⁻¹) * (b * r * b⁻¹) := by group
        _ = wa * (wb * r) := by rw [hcent_wa, hwbq]
        _ = (wa * wb) * r := by group
        _ = (wb * wa) * r := by rw [hcomm_w]
    exact h1.trans h2.symm
  set x : H := a * b * a⁻¹ * b⁻¹ with hxdef
  have hx_eq : x = (a * b) * (b * a)⁻¹ := by rw [hxdef]; group
  have hxq : x * q * x⁻¹ = q := by
    set q' : H := (b * a)⁻¹ * q * (b * a) with hq'def
    have hq'Q : q' ∈ Q := by
      rw [hq'def]
      simpa using h.normal_Q (b * a)⁻¹ q hq
    have hstep : (a * b) * q' * (a * b)⁻¹ = (b * a) * q' * (b * a)⁻¹ :=
      hsame q' hq'Q
    have hR : (b * a) * q' * (b * a)⁻¹ = q := by rw [hq'def]; group
    have hL : (a * b) * q' * (a * b)⁻¹ = x * q * x⁻¹ := by
      rw [hx_eq, hq'def]; group
    rw [← hL, hstep, hR]
  calc x * q = (x * q * x⁻¹) * x := by group
    _ = q * x := by rw [hxq]

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
