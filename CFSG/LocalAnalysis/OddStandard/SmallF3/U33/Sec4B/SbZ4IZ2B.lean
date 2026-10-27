module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ1A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem z4i_exists_mem_normalizer_not_mem_of_lt {P S₀ : Subgroup H}
    (hP : IsPGroup 2 P) (hlt : S₀ < P) :
    ∃ x ∈ P, x ∉ S₀ ∧ x ∈ normalizer (S₀ : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt' : S₀.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hlt.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ S₀.subgroupOf P := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt')
  refine ⟨y, y.2, fun h => hyP (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (S₀ : Set H)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hlt.le]
    exact hyN
  exact mem_subgroupOf.mp hy

namespace ZEData

variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}

theorem conj_t_form (h : ZEData Q Y V V' B K ρ t τ l) {g : H}
    (hg : ∀ x ∈ z4iVc K t τ l, g * x * g⁻¹ ∈ z4iVc K t τ l) :
    ∃ k ∈ K, ∃ b : Fin 2, g * t * g⁻¹ = k * t * τ ^ (b : ℕ) := by
  set x : H := g * t * g⁻¹ with hxdef
  have hxVc : x ∈ z4iVc K t τ l := by
    rw [hxdef]
    exact hg t (T3_le_Vc K t τ l (t_mem_T3 t τ l))
  have hxcentV : x ∈ centralizer (V : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hgv : g⁻¹ * v * g ∈ V := by simpa using h.normal_V g⁻¹ v hv
    have htv : t * (g⁻¹ * v * g) = (g⁻¹ * v * g) * t := h.V_cent_t _ hgv
    have hxv : x * v * x⁻¹ = v := by
      rw [hxdef]
      calc (g * t * g⁻¹) * v * (g * t * g⁻¹)⁻¹
          = g * (t * (g⁻¹ * v * g) * t⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * v * g) * g⁻¹ := by
              rw [show t * (g⁻¹ * v * g) * t⁻¹ = g⁻¹ * v * g by rw [htv]; group]
        _ = v := by group
    have hgoal : x * v = v * x := by
      calc x * v = (x * v * x⁻¹) * x := by group
        _ = v * x := by rw [hxv]
    exact hgoal.symm
  have hxF : x ∈ z4iF K t τ := by
    rw [← h.Vc_inf_cent_V]
    exact ⟨hxVc, hxcentV⟩
  obtain ⟨k, hk, a, b, hxeq⟩ := (h.mem_F_iff).mp hxF
  have hxnotY : x ∉ centralizer (Y : Set H) := by
    intro hxc
    obtain ⟨y0, hy0, hy0ne⟩ := h.t_not_cent_Y
    have hyY : g * y0 * g⁻¹ ∈ Y := h.normal_Y g y0 hy0
    have hcomm := (Subgroup.mem_centralizer_iff.mp hxc) (g * y0 * g⁻¹) hyY
    apply hy0ne
    rw [hxdef] at hcomm
    rw [show (g * y0 * g⁻¹) * (g * t * g⁻¹) = g * (y0 * t) * g⁻¹ by group,
        show (g * t * g⁻¹) * (g * y0 * g⁻¹) = g * (t * y0) * g⁻¹ by group] at hcomm
    exact (mul_left_cancel (mul_right_cancel hcomm)).symm
  fin_cases a
  · exfalso
    have hxK1 : x ∈ z4iK1 K τ := by
      refine (h.mem_K1_iff).mpr ⟨k, hk, b, ?_⟩
      rw [hxeq]; simp
    have hK1cent : z4iK1 K τ ≤ centralizer (Y : Set H) := by
      rw [← h.F_inf_cent_Y]; exact inf_le_right
    exact hxnotY (hK1cent hxK1)
  · refine ⟨k, hk, b, ?_⟩
    rw [hxeq]; simp

theorem card_Vc_cent_t (h : ZEData Q Y V V' B K ρ t τ l) :
    128 ≤ Nat.card ↥(z4iVc K t τ l ⊓ centralizer ({t} : Set H)) := by
  have hinf : B ⊓ z4iT3 t τ l = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    exact Subgroup.mem_bot.mpr (h.T3_inf_K x hx.2 (h.Q_le_K (h.B_le_Q hx.1)))
  have hcardB : Nat.card ↥(B ⊔ z4iT3 t τ l) = 128 := by
    have hc := card_sup_eq_mul (H := B) (K := z4iT3 t τ l) h.T3_norm_B hinf
    rw [h.card_B, h.card_T3] at hc
    exact hc
  have hR0le : B ⊔ z4iT3 t τ l ≤ z4iVc K t τ l ⊓ centralizer ({t} : Set H) := by
    refine le_inf (sup_le ?_ (T3_le_Vc K t τ l)) (sup_le ?_ h.T3_cent_t)
    · exact h.B_le_Q.trans (h.Q_le_K.trans (K_le_Vc K t τ l))
    · intro b hb
      exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
        rw [Set.mem_singleton_iff] at hy; rw [hy]; exact h.B_cent_t b hb)
  calc (128 : ℕ) = Nat.card ↥(B ⊔ z4iT3 t τ l) := hcardB.symm
    _ ≤ Nat.card ↥(z4iVc K t τ l ⊓ centralizer ({t} : Set H)) := Subgroup.card_le_of_le hR0le

theorem mem_Vc_of_cent_t (h : ZEData Q Y V V' B K ρ t τ l) {P : Subgroup H} (hP : IsPGroup 2 P)
    (hVP : z4iVc K t τ l ≤ P) {g : H} (hgP : g ∈ P) (hgt : g * t = t * g) :
    g ∈ z4iVc K t τ l := by
  have hR0leP : z4iVc K t τ l ⊓ centralizer ({t} : Set H) ≤ P :=
    inf_le_left.trans hVP
  have hR'leP : (z4iVc K t τ l ⊓ centralizer ({t} : Set H)) ⊔ zpowers g ≤ P :=
    sup_le hR0leP (Subgroup.zpowers_le.mpr hgP)
  have hgcent : g ∈ centralizer ({t} : Set H) :=
    Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hgt.symm)
  have hR'cent : (z4iVc K t τ l ⊓ centralizer ({t} : Set H)) ⊔ zpowers g ≤
      centralizer ({t} : Set H) :=
    sup_le inf_le_right (Subgroup.zpowers_le.mpr hgcent)
  have hleb : Nat.card ↥((z4iVc K t τ l ⊓ centralizer ({t} : Set H)) ⊔ zpowers g) ≤
      Nat.card ↥(z4iVc K t τ l ⊓ centralizer ({t} : Set H)) :=
    (h.bound _ (hP.to_le hR'leP) hR'cent).trans (card_Vc_cent_t h)
  have hEq : z4iVc K t τ l ⊓ centralizer ({t} : Set H) =
      (z4iVc K t τ l ⊓ centralizer ({t} : Set H)) ⊔ zpowers g :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hleb
  have hgR0 : g ∈ z4iVc K t τ l ⊓ centralizer ({t} : Set H) := by
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  exact (Subgroup.mem_inf.mp hgR0).1

theorem card_Q_sup_tau (h : ZEData Q Y V V' B K ρ t τ l) :
    Nat.card ↥(Q ⊔ zpowers τ) = 128 := by
  have hτ2z : τ ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    simpa [pow_two] using h.tau_sq
  have hinf : Q ⊓ zpowers τ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxQ, hxzp⟩ := hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxzp
    have hxQ' : τ ^ n ∈ Q := by rwa [hn]
    rw [← hn]
    rcases Int.even_or_odd' n with ⟨m, hm | hm⟩
    · rw [hm, zpow_mul, hτ2z, one_zpow]
    · exfalso
      rw [hm, zpow_add, zpow_mul, hτ2z, one_zpow, one_mul, zpow_one] at hxQ'
      exact h.tau_not_mem_Q hxQ'
  have hcardτ : Nat.card (zpowers τ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact h.tau_sq)
      (fun hτ1 => h.tau_not_mem_Q (by rw [hτ1]; exact Q.one_mem))
  have hcard := card_sup_eq_mul (H := Q) (K := zpowers τ) (fun s _ q hq => h.normal_Q s q hq)
    hinf
  rw [h.card_Q, hcardτ] at hcard
  rw [hcard]

private theorem z4i_conj_mem_Qsup (h : ZEData Q Y V V' B K ρ t τ l)
    (htriv : ∀ x ∈ K, ⁅t * τ, x⁆ ∈ Y) {g k : H}
    (hg : g ∈ normalizer ((z4iVc K t τ l : Subgroup H) : Set H))
    (hk : k ∈ K) (hgt : g * t * g⁻¹ = k * t * τ) :
    ∀ z ∈ K, g⁻¹ * z * g ∈ Q ⊔ zpowers τ := by
  have hgnorm := (Subgroup.mem_set_normalizer_iff''
    (S := ((z4iVc K t τ l : Subgroup H) : Set H))).mp hg
  have huK : ∀ z ∈ K, (t * τ) * z * (t * τ)⁻¹ ∈ K := by
    intro z hz
    rw [show (t * τ) * z * (t * τ)⁻¹ = t * (τ * z * τ⁻¹) * t⁻¹ by group]
    exact h.t_norm_K _ (h.tau_norm_K z hz)
  intro z hz
  set z' : H := g⁻¹ * z * g with hz'def
  have hz'Vc : z' ∈ z4iVc K t τ l := by
    rw [hz'def]
    exact (hgnorm z).mp (K_le_Vc K t τ l hz)
  have hz'centY : z' ∈ centralizer (Y : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcomm := h.K_cent_Y z hz (g * y * g⁻¹) (h.normal_Y g y hy)
    have hmain : z' * y = y * z' := by
      calc z' * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [hz'def]; group
        _ = g⁻¹ * ((g * y * g⁻¹) * z) * g := by rw [hcomm]
        _ = y * z' := by rw [hz'def]; group
    exact hmain.symm
  have hz'Y : ⁅t, z'⁆ ∈ Y := by
    have hwK : (t * τ) * z * (t * τ)⁻¹ ∈ K := huK z hz
    have hjz : ⁅g * t * g⁻¹, z⁆ = ⁅k, (t * τ) * z * (t * τ)⁻¹⁆ * ⁅t * τ, z⁆ := by
      rw [hgt]
      simp only [commutatorElement_def]
      group
    have hjzY : ⁅g * t * g⁻¹, z⁆ ∈ Y := by
      rw [hjz]
      exact Y.mul_mem (h.V_le_Y (h.comm_mem_V k hk _ hwK)) (htriv z hz)
    have hconj : ⁅t, z'⁆ = g⁻¹ * ⁅g * t * g⁻¹, z⁆ * g := by
      rw [hz'def]
      simp only [commutatorElement_def]
      group
    rw [hconj]
    simpa using h.normal_Y g⁻¹ _ hjzY
  have hz'K1 : z' ∈ z4iK1 K τ := by
    have hz'V : z' ∈ centralizer (V : Set H) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        Subgroup.mem_centralizer_iff.mp hz'centY v (h.V_le_Y hv)
    have hz'F : z' ∈ z4iF K t τ := by
      rw [← h.Vc_inf_cent_V]
      exact ⟨hz'Vc, hz'V⟩
    rw [← h.F_inf_cent_Y]
    exact ⟨hz'F, hz'centY⟩
  obtain ⟨k', hk'K, b', hz'eq⟩ := (h.mem_K1_iff).mp hz'K1
  have hk'Q : k' ∈ Q := by
    have hcommτ : Commute t (τ ^ (b' : ℕ)) :=
      (show Commute t τ from h.t_tau).pow_right (b' : ℕ)
    have hck : ⁅t, k' * τ ^ (b' : ℕ)⁆ = ⁅t, k'⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr hcommτ.eq]
      group
    have h1 : ⁅t, z'⁆ = ⁅t, k'⁆ := by rw [hz'eq, hck]
    exact (h.comm_t_mem_Y_iff hk'K).mp (by rw [← h1]; exact hz'Y)
  have hz'_Qsup : z' ∈ Q ⊔ zpowers τ := by
    rw [hz'eq]
    exact Subgroup.mul_mem_sup hk'Q (Subgroup.npow_mem_zpowers τ (b' : ℕ))
  simpa only [hz'def] using hz'_Qsup

theorem not_ttau_trivial (h : ZEData Q Y V V' B K ρ t τ l)
    (htriv : ∀ x ∈ K, ⁅t * τ, x⁆ ∈ Y) {g k : H}
    (hg : g ∈ normalizer ((z4iVc K t τ l : Subgroup H) : Set H)) (hk : k ∈ K)
    (hgt : g * t * g⁻¹ = k * t * τ) : False := by
  let f : K → ↥(Q ⊔ zpowers τ) := fun z =>
    ⟨g⁻¹ * (z : H) * g, z4i_conj_mem_Qsup h htriv hg hk hgt (z : H) z.2⟩
  have hf : Function.Injective f := by
    intro z z' hzz
    apply Subtype.ext
    have h1 := congrArg Subtype.val hzz
    simp only [f] at h1
    calc (z : H) = g * (g⁻¹ * (z : H) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * (z' : H) * g) * g⁻¹ := by rw [h1]
      _ = (z' : H) := by group
  have hle := Nat.card_le_card_of_injective f hf
  rw [h.card_K, card_Q_sup_tau h] at hle
  omega

theorem Vc_maximal (h : ZEData Q Y V V' B K ρ t τ l) {P : Subgroup H} (hP : IsPGroup 2 P)
    (hVP : z4iVc K t τ l ≤ P) : P = z4iVc K t τ l := by
  by_contra hne
  have hlt : z4iVc K t τ l < P := lt_of_le_of_ne hVP (Ne.symm hne)
  obtain ⟨g, hgP, hgVc, hgnorm⟩ := z4i_exists_mem_normalizer_not_mem_of_lt hP hlt
  have hgconj : ∀ x ∈ z4iVc K t τ l, g * x * g⁻¹ ∈ z4iVc K t τ l :=
    fun x hx => ((Subgroup.mem_set_normalizer_iff.mp hgnorm) x).mp hx
  obtain ⟨k, hk, b, hb⟩ := conj_t_form h hgconj
  have hjj : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    rw [show (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, h.t_sq]
    group
  fin_cases b
  · have hb0 : g * t * g⁻¹ = k * t := by simpa using hb
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
    have hjK : t * k * t⁻¹ ∈ K := h.t_norm_K k hk
    have hjform : g * t * g⁻¹ = t * (t * k * t⁻¹) := by
      rw [hb0]
      rw [show t * (t * k * t⁻¹) = (t * t) * k * t⁻¹ by group, h.t_sq, htinv]
      group
    obtain ⟨w, hwK, hwj⟩ := h.invol_tK (g * t * g⁻¹) ⟨t * k * t⁻¹, hjK, hjform⟩ hjj
    have hgt' : (w⁻¹ * g) * t = t * (w⁻¹ * g) := by
      have h2 : (w⁻¹ * g) * t * (w⁻¹ * g)⁻¹ = t := by
        calc (w⁻¹ * g) * t * (w⁻¹ * g)⁻¹ = w⁻¹ * (g * t * g⁻¹) * w := by group
          _ = w⁻¹ * (w * t * w⁻¹) * w := by rw [hwj]
          _ = t := by group
      calc (w⁻¹ * g) * t = ((w⁻¹ * g) * t * (w⁻¹ * g)⁻¹) * (w⁻¹ * g) := by group
        _ = t * (w⁻¹ * g) := by rw [h2]
    have hg'P : w⁻¹ * g ∈ P :=
      P.mul_mem (hVP (K_le_Vc K t τ l (K.inv_mem hwK))) hgP
    have hg'Vc : w⁻¹ * g ∈ z4iVc K t τ l := mem_Vc_of_cent_t h hP hVP hg'P hgt'
    have hgVc' : g ∈ z4iVc K t τ l := by
      have hmem : w * (w⁻¹ * g) ∈ z4iVc K t τ l :=
        (z4iVc K t τ l).mul_mem (K_le_Vc K t τ l hwK) hg'Vc
      rwa [show w * (w⁻¹ * g) = g by group] at hmem
    exact hgVc hgVc'
  · have hb1 : g * t * g⁻¹ = k * t * τ := by simpa using hb
    rcases h.ttau_dich with htriv | hreg
    · exact not_ttau_trivial h htriv hgnorm hk hb1
    · have hu_sq : (t * τ) * (t * τ) = 1 := by
        calc (t * τ) * (t * τ) = t * (τ * t) * τ := by group
          _ = t * (t * τ) * τ := by rw [← h.t_tau]
          _ = (t * t) * (τ * τ) := by group
          _ = 1 := by rw [h.t_sq, h.tau_sq, one_mul]
      have hu_inv : (t * τ)⁻¹ = t * τ := inv_eq_of_mul_eq_one_right hu_sq
      have hs : (t * τ) * k * (t * τ)⁻¹ ∈ K := by
        rw [show (t * τ) * k * (t * τ)⁻¹ = t * (τ * k * τ⁻¹) * t⁻¹ by group]
        exact h.t_norm_K _ (h.tau_norm_K k hk)
      have hjs : g * t * g⁻¹ = (t * τ) * ((t * τ) * k * (t * τ)⁻¹) := by
        rw [hb1]
        rw [show (t * τ) * ((t * τ) * k * (t * τ)⁻¹) =
          ((t * τ) * (t * τ)) * k * (t * τ)⁻¹ by group, hu_sq, hu_inv]
        group
      obtain ⟨w, hwK, hwj⟩ := h.invol_ttauK hreg (g * t * g⁻¹)
        ⟨(t * τ) * k * (t * τ)⁻¹, hs, hjs⟩ hjj
      refine h.not_conj (w⁻¹ * g) ?_
      calc (w⁻¹ * g) * t * (w⁻¹ * g)⁻¹ = w⁻¹ * (g * t * g⁻¹) * w := by group
        _ = w⁻¹ * (w * (t * τ) * w⁻¹) * w := by rw [hwj]
        _ = t * τ := by group

end ZEData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
