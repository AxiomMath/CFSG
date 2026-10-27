module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5HSyl

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Sec8
open scoped Pointwise

namespace Sec5H

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace Setup

variable {D : S.Sec5 F T₁} (C : Setup D)

include C in
theorem card_Q : Nat.card D.Q = 64 := by
  rw [← C.map_Q, card_map_of_injective C.inj, RH.card_Q]

include C in
theorem comm_y_of_mem_Q {x : X} (hx : x ∈ D.Q) : x * F.yF = F.yF * x := by
  rw [← C.map_Q, Subgroup.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [← C.ι_y, ← map_mul, ← map_mul, RH.Q_comm_y c ((RH.mem_Q c).mp hc)]

include C in
theorem Q_le_R : D.Q ≤ D.R := by
  rw [← C.map_Q, ← C.range_eq]; exact map_le_range _ _

theorem E0_eq_inf : C.E0 = C.Fs 0 ⊓ C.Fs 2 :=
  le_antisymm (le_inf (C.E0_le_Fs (Or.inl rfl)) (C.E0_le_Fs (Or.inr (Or.inl rfl)))) C.inf_le_E0

theorem comm_E0_of_mem_Q {x : X} (hx : x ∈ D.Q) {e : X} (he : e ∈ C.E0) : x * e = e * x := by
  rw [C.E0_eq] at he
  have hle : closure ({S.z, F.yF, F.kF} : Set X) ≤ centralizer ({x} : Set X) := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl | rfl
    · exact (C.comm_z_k (C.Q_le_R hx)).1.symm
    · exact (C.comm_y_of_mem_Q hx).symm
    · exact (C.comm_z_k (C.Q_le_R hx)).2.symm
  exact (mem_centralizer_singleton_iff.mp (hle he)).symm

omit [Finite X] in
theorem conjSub_closure_le {g : X} {s : Set X} {K : Subgroup X}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ K) : conjSub g (closure s) ≤ K := by
  rw [conjSub, MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

theorem Fs_eq_closure (i : Fin 8) :
    C.Fs i = closure {x | x ∈ (RH.Ggens i).map C.ι} := by
  rw [Fs, RH.G, map_span]

include C in
theorem w_eq : D.w = D.w₁ * S.t := by rw [w₁_eq_H D C.hH, mul_assoc, t_mul_t, mul_one]

theorem conjSub_d_two : conjSub D.d (C.Fs 2) = C.Fs 6 := by
  have hdt : D.d * S.t * D.d⁻¹ = S.t := by
    have h := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp D.d_mem).2
    rw [h, mul_inv_cancel_right]
  refine conjSub_eq_of_le ?_ (by rw [C.card_Fs, C.card_Fs])
  rw [C.Fs_eq_closure 2]
  refine conjSub_closure_le fun x hx => ?_
  simp only [RH.Ggens, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_ofPred_eq] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [C.ι_z, D.d_z, ← C.ι_y]; exact C.ι_mem_Fs.mpr (by decide +kernel)
  · rw [C.ι_k, D.d_k, ← C.ι_k]; exact C.ι_mem_Fs.mpr (by decide +kernel)
  · rw [C.ι_w, C.w_eq]
    have e : D.d * (D.w₁ * S.t) * D.d⁻¹ = (D.d * D.w₁ * D.d⁻¹) * (D.d * S.t * D.d⁻¹) := by
      group
    rw [e, D.d_w₁, hdt, ← C.ι_w₂, ← C.ι_t, ← map_mul]
    exact C.ι_mem_Fs.mpr (by decide +kernel)
  · rw [C.ι_y, D.d_y, ← C.ι_z, ← C.ι_y, ← map_mul]
    exact C.ι_mem_Fs.mpr RH.d_images.1

theorem conjSub_d_six : conjSub D.d (C.Fs 6) = C.Fs 7 := by
  have hdt : D.d * S.t * D.d⁻¹ = S.t := by
    have h := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp D.d_mem).2
    rw [h, mul_inv_cancel_right]
  refine conjSub_eq_of_le ?_ (by rw [C.card_Fs, C.card_Fs])
  rw [C.Fs_eq_closure 6]
  refine conjSub_closure_le fun x hx => ?_
  simp only [RH.Ggens, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_ofPred_eq] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [C.ι_z, D.d_z, ← C.ι_y]; exact C.ι_mem_Fs.mpr (by decide +kernel)
  · rw [C.ι_k, D.d_k, ← C.ι_k]; exact C.ι_mem_Fs.mpr (by decide +kernel)
  · rw [C.ι_y, D.d_y, ← C.ι_z, ← C.ι_y, ← map_mul]
    exact C.ι_mem_Fs.mpr RH.d_images.2.1
  · rw [map_mul, C.ι_w₂, C.ι_t]
    have e : D.d * (D.w₂ * S.t) * D.d⁻¹ = (D.d * D.w₂ * D.d⁻¹) * (D.d * S.t * D.d⁻¹) := by
      group
    rw [e, D.d_w₂, hdt, ← C.ι_w₂, ← C.ι_w₁, ← C.ι_t, ← map_mul, ← map_inv, ← map_mul]
    exact C.ι_mem_Fs.mpr RH.d_images.2.2

theorem conj_E₁_cases {n : X} (hn : n ∈ normalizer (D.Q : Set X)) :
    conjSub n (C.Fs 0) = C.Fs 0 ∨ conjSub n (C.Fs 0) = C.Fs 2 ∨ conjSub n (C.Fs 0) = C.Fs 6 ∨
      conjSub n (C.Fs 0) = C.Fs 7 := by
  have hle : conjSub n (C.Fs 0) ≤ D.Q := by
    rw [← conjSub_eq_self_iff.mpr hn]
    exact conjSub_mono _ (C.Fs_le_Q (Or.inl rfl))
  obtain ⟨i, hi⟩ := C.eq_Fs_of_elem _ (hle.trans C.Q_le_R) (fun a ha => by
      have hb := C.sq_of_mem_Fs (mem_conjSub.mp ha)
      calc a * a = n * ((n⁻¹ * a * n) * (n⁻¹ * a * n)) * n⁻¹ := by group
        _ = 1 := by rw [hb, mul_one, mul_inv_cancel])
    (by rw [card_conjSub, C.card_Fs])
  have hiQ : C.Fs i ≤ D.Q := hi ▸ hle
  have : i = 0 ∨ i = 2 ∨ i = 6 ∨ i = 7 := by
    by_contra hne
    push Not at hne
    have h1 : C.Fs i ⊓ D.Q = C.Fs i := inf_eq_left.mpr hiQ
    have h2 := C.card_Fs_inf_Q (i := i) (by
      obtain ⟨h0, h2, h6, h7⟩ := hne
      fin_cases i <;> simp_all)
    rw [h1, C.card_Fs] at h2
    omega
  rcases this with rfl | rfl | rfl | rfl
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (Or.inl hi))
  · exact Or.inr (Or.inr (Or.inr hi))

include C in
theorem R_le_normalizer_Q : D.R ≤ normalizer (D.Q : Set X) := by
  intro r hr
  rw [← conjSub_eq_self_iff]
  refine conjSub_eq_of_relIndex_two C.Q_le_R ?_ hr
  have h := Subgroup.relIndex_mul_card (H := D.Q) (K := D.R)
  rw [inf_eq_left.mpr C.Q_le_R, C.card_Q, D.card_R] at h
  omega

theorem pow_nine_dvd {q : X} (hqQ : q ∈ normalizer (D.Q : Set X))
    (hq : conjSub q (C.Fs 0) = C.Fs 2) : 2 ^ 9 ∣ Nat.card X := by
  set N := normalizer (D.Q : Set X) with hN
  let φ : N →* MulAut X := MulAut.conj.comp N.subtype
  let _ : MulAction N (Subgroup X) := MulAction.compHom _ φ
  have hsmul : ∀ (n : N) (H : Subgroup X), n • H = conjSub (n : X) H := fun _ _ => rfl
  have hd : D.d ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp D.d_mem).1).2
  have hdq : D.d * q ∈ N := mul_mem hd hqQ
  have hddq : D.d * (D.d * q) ∈ N := mul_mem hd hdq
  have horbit : MulAction.orbit N (C.Fs 0) = {C.Fs 0, C.Fs 2, C.Fs 6, C.Fs 7} := by
    ext H
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, rfl⟩
      rw [hsmul]
      exact C.conj_E₁_cases n.2
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨1, by rw [hsmul]; exact conjSub_one _⟩
      · exact ⟨⟨q, hqQ⟩, by rw [hsmul]; exact hq⟩
      · refine ⟨⟨D.d * q, hdq⟩, ?_⟩
        rw [hsmul]
        show conjSub (D.d * q) (C.Fs 0) = C.Fs 6
        rw [conjSub_mul, hq, C.conjSub_d_two]
      · refine ⟨⟨D.d * (D.d * q), hddq⟩, ?_⟩
        rw [hsmul]
        show conjSub (D.d * (D.d * q)) (C.Fs 0) = C.Fs 7
        rw [conjSub_mul, conjSub_mul, hq, C.conjSub_d_two, C.conjSub_d_six]
  have hcard_orbit : (MulAction.orbit N (C.Fs 0)).ncard = 4 := by
    rw [horbit]
    have h02 := C.Fs_ne (i := 0) (j := 2) (by decide)
    have h06 := C.Fs_ne (i := 0) (j := 6) (by decide)
    have h07 := C.Fs_ne (i := 0) (j := 7) (by decide)
    have h26 := C.Fs_ne (i := 2) (j := 6) (by decide)
    have h27 := C.Fs_ne (i := 2) (j := 7) (by decide)
    have h67 := C.Fs_ne (i := 6) (j := 7) (by decide)
    rw [Set.ncard_insert_of_notMem (by simp [h02, h06, h07]),
      Set.ncard_insert_of_notMem (by simp [h26, h27]), Set.ncard_pair h67]
  have hidx := MulAction.index_stabilizer N (C.Fs 0)
  rw [hcard_orbit] at hidx
  have hR : D.R.subgroupOf N ≤ MulAction.stabilizer N (C.Fs 0) := by
    intro r hr
    rw [MulAction.mem_stabilizer_iff, hsmul, C.Fs_zero]
    exact conjSub_eq_self_iff.mpr (D.R_le hr)
  have hRcard : Nat.card (D.R.subgroupOf N) = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.R_le_normalizer_Q).toEquiv, D.card_R]
  have h128 : 128 ∣ Nat.card (MulAction.stabilizer N (C.Fs 0)) := by
    rw [← hRcard]; exact Subgroup.card_dvd_of_le hR
  have hN512 : 2 ^ 9 ∣ Nat.card N := by
    rw [← Subgroup.card_mul_index (MulAction.stabilizer N (C.Fs 0)), hidx]
    obtain ⟨c, hc⟩ := h128
    rw [hc]
    exact ⟨c, by ring⟩
  exact hN512.trans (Subgroup.card_subgroup_dvd_card N)

end Setup

theorem false_of_setup {D : S.Sec5 F T₁} (C : Setup D) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hRP, hPL, hPL₀⟩ := C.exists_P
  obtain ⟨q, hqP, hqL₀⟩ := IsConcreteLE.not_le_iff_exists.mp hPL₀
  have hqR : q ∉ D.R := fun h => hqL₀ (Setup.R_le_L₀ h)
  have hq := C.cases_out hP hRP hPL hqP hqR
  obtain ⟨-, hq0, hq2⟩ := C.out_perm hq
  have hqL₀' : conjSub q (L₀ D) = L₀ D :=
    conjSub_eq_of_relIndex_two Setup.L₀_le_L C.relIndex_L₀ (hPL hqP)
  have hqR' : ∀ r ∈ D.R, q * r * q⁻¹ ∈ D.R := by
    intro r hr
    refine C.mem_R_of_mem_L₀ hP hRP (mul_mem (mul_mem hqP (hRP hr)) (inv_mem hqP)) ?_
    rw [← hqL₀']; exact conj_mem_conjSub (Setup.R_le_L₀ hr)
  have hqE0 : conjSub q C.E0 = C.E0 := by
    rw [C.E0_eq_inf, conjSub_inf, hq0, hq2, inf_comm]
  have hqE0' : ∀ e ∈ C.E0, q⁻¹ * e * q ∈ C.E0 := by
    intro e he
    rw [← mem_conjSub, hqE0]; exact he
  have hqQ : q ∈ normalizer (D.Q : Set X) := by
    rw [← conjSub_eq_self_iff]
    refine conjSub_eq_of_le (conjSub_le_iff.mpr fun x hx => ?_) le_rfl
    refine C.mem_Q_of_comm_y (hqR' x (C.Q_le_R hx)) ?_
    have hyE : F.yF ∈ C.E0 := by
      rw [C.E0_eq]; exact subset_closure (by simp)
    have hcomm := C.comm_E0_of_mem_Q hx (hqE0' _ hyE)
    calc q * x * q⁻¹ * F.yF = q * (x * (q⁻¹ * F.yF * q)) * q⁻¹ := by group
      _ = q * ((q⁻¹ * F.yF * q) * x) * q⁻¹ := by rw [hcomm]
      _ = F.yF * (q * x * q⁻¹) := by group
  have h512 := C.pow_nine_dvd hqQ hq0
  obtain ⟨Syl, hSyl⟩ := C.isSylow_P hP hRP hPL hqP hqL₀
  have hdvd : 2 ^ 9 ∣ Nat.card P := by
    rw [← hSyl]; exact Syl.pow_dvd_card_of_pow_dvd_card h512
  have hrel : D.R.relIndex P ∣ 2 := by
    refine Subgroup.relIndex_dvd_two_iff'.mpr ⟨q⁻¹, inv_mem hqP, fun b hb => ?_⟩
    by_cases hbR : b ∈ D.R
    · exact Or.inr hbR
    · left
      have hb' := C.cases_out hP hRP hPL hb hbR
      refine C.mem_R_of_mem_L₀ hP hRP (mul_mem (inv_mem hqP) hb) ?_
      have e : q⁻¹ * b = ((hEl D)⁻¹ * q)⁻¹ * ((hEl D)⁻¹ * b) := by group
      rw [e]
      refine mul_mem (inv_mem ?_) ?_
      · rcases hq with h | h
        · exact Setup.M_le_L₀ h
        · have := mul_mem Setup.w₂_mem_L₀ (Setup.M_le_L₀ h)
          rwa [mul_inv_cancel_left] at this
      · rcases hb' with h | h
        · exact Setup.M_le_L₀ h
        · have := mul_mem Setup.w₂_mem_L₀ (Setup.M_le_L₀ h)
          rwa [mul_inv_cancel_left] at this
  have hmc := Subgroup.relIndex_mul_card (H := D.R) (K := P)
  rw [inf_eq_left.mpr hRP, D.card_R] at hmc
  have hle := Nat.le_of_dvd (by norm_num) hrel
  have hpos : 0 < Nat.card P := Nat.card_pos
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by rintro rfl; omega
  omega

end Sec5H

theorem fritzA7Section5H : FritzA7Section5H := by
  intro _ X _ _ _ _ _ S F T₁ h4 hF D hH
  obtain ⟨C⟩ := Sec5H.exists_setup D hH h4 hF
  exact Sec5H.false_of_setup C

end CFSG.ComponentClassification.HSFLit
