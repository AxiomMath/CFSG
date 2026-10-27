module

public import CFSG.GH74.GLS.IVK.L2.TStruct
public import CFSG.GH74.GLS.IVK.L2.DihedralAux
public import CFSG.GH74.GLS.IVK.L2.Lemma12fg

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter
open scoped commutatorElement

section Key

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] {e : K ≃* L2 F}

theorem three_le_of_involution_mem_R (h : L2Field F) (N : L2Notation e) {f : MulAut K}
    (hf : f ∈ N.R) (hf2 : orderOf f = 2) (n : ℕ) (hn : Nat.card N.P = 2 ^ n) : 3 ≤ n := by
  have hR := (ivk_1_2f F h K e N).2 n hn
  have h2 : orderOf f ∣ Nat.card N.R := Subgroup.orderOf_dvd_natCard N.R hf
  rw [hf2] at h2
  have h3 : 2 ≤ Nat.card N.R := Nat.le_of_dvd Nat.card_pos h2
  by_contra hlt
  have : n - 2 = 0 := by omega
  rw [this] at hR
  simp at hR
  omega

theorem P_central_unique (h : L2Field F) (N : L2Notation e) (n : ℕ) (hn : Nat.card N.P = 2 ^ n)
    (hn3 : 3 ≤ n) {a b : MulAut K} (ha : a ∈ N.P) (hb : b ∈ N.P) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hac : ∀ x ∈ N.P, a * x = x * a) (hbc : ∀ x ∈ N.P, b * x = x * b) : a = b := by
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := P_dihedral_model h N n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hk' : k = 4 * 2 ^ m := by
    have : 2 ^ (m + 3) = 2 * (4 * 2 ^ m) := by ring
    omega
  have hkE : Even k := ⟨2 * 2 ^ m, by omega⟩
  have hkne : k ≠ 2 := by
    have : 0 < 2 ^ m := by positivity
    omega
  have := DihedralAux.central_involution_unique φ hkE hkne (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (fun x => Subtype.ext (hac x x.2)) (fun x => Subtype.ext (hbc x x.2))
    (fun h' => ha1 (congrArg Subtype.val h')) (fun h' => hb1 (congrArg Subtype.val h'))
  exact congrArg Subtype.val this

omit [Finite K] in
theorem conj_mem_P (N : L2Notation e) {τ : MulAut K} (hτ : τ ∈ (N.T : Subgroup (MulAut K)))
    {x : MulAut K} (hx : x ∈ N.P) : τ * x * τ⁻¹ ∈ N.P :=
  ⟨(N.T : Subgroup (MulAut K)).mul_mem ((N.T : Subgroup (MulAut K)).mul_mem hτ hx.1)
      ((N.T : Subgroup (MulAut K)).inv_mem hτ),
    (innAut_normal (K := K)).conj_mem x hx.2 τ⟩

theorem f_conj_t (h : L2Field F) (N : L2Notation e) (n : ℕ) (hn : Nat.card N.P = 2 ^ n)
    {f : MulAut K} (hf : f ∈ N.R) (hf2 : orderOf f = 2)
    (hF1 : ¬ ∀ d ∈ N.Pt, d * f = f * d) {z : MulAut K} (hz : z ∈ N.P) (hz1 : z ≠ 1)
    (hzc : ∀ x ∈ N.P, z * x = x * z) : f * N.t * f⁻¹ = N.t * z := by
  have hn3 := three_le_of_involution_mem_R h N hf hf2 n hn
  have hfT : f ∈ (N.T : Subgroup (MulAut K)) := hf.1
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, pow_two] at this
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hfP : ∀ x ∈ N.P, f * x = x * f := fun x hx => (N.R_cent f hf hf2 x hx).symm
  have hfPc : ∀ x ∈ N.P, f * x * f⁻¹ = x := by
    intro x hx
    calc f * x * f⁻¹ = (x * f) * f⁻¹ := by rw [hfP x hx]
      _ = x := by group
  set t := N.t with htdef
  set s := f * t * f⁻¹ with hsdef
  have hsT : s ∈ (N.T : Subgroup (MulAut K)) :=
    (N.T : Subgroup (MulAut K)).mul_mem ((N.T : Subgroup (MulAut K)).mul_mem hfT N.t_mem)
      ((N.T : Subgroup (MulAut K)).inv_mem hfT)
  have hsD : s ∈ innDiagSub e := (innDiagSub_normal e).conj_mem t N.t_mem_diag f
  have hsI : s ∉ innAut K := by
    intro hs
    apply N.t_not_mem_inn
    have := (innAut_normal (K := K)).conj_mem s hs f⁻¹
    have h2 : f⁻¹ * s * f⁻¹⁻¹ = t := by rw [hsdef]; group
    rwa [h2] at this
  set c := t⁻¹ * s with hcdef
  have hidx := innAut_relIndex_two e h
  unfold Subgroup.relIndex at hidx
  have hcP : c ∈ N.P := by
    refine ⟨(N.T : Subgroup (MulAut K)).mul_mem ((N.T : Subgroup (MulAut K)).inv_mem N.t_mem) hsT, ?_⟩
    have hq := Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨t⁻¹, (innDiagSub e).inv_mem N.t_mem_diag⟩ : ↥(innDiagSub e)))
      (b := ⟨s, hsD⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hq
    apply hq.mpr
    constructor
    · intro hh; exact absurd ((innAut K).inv_mem_iff.mp hh) N.t_not_mem_inn
    · intro hh; exact absurd hh hsI
  have hsc : s = t * c := by rw [hcdef]; group
  have hcc : ∀ x ∈ N.P, c * x = x * c := by
    intro x hx
    have hx' : t * x * t⁻¹ ∈ N.P := conj_mem_P N N.t_mem hx
    have h1 : s * x * s⁻¹ = t * x * t⁻¹ := by
      have e1 : f * (t * x * t⁻¹) * f⁻¹ = t * x * t⁻¹ := hfPc _ hx'
      have e2 : s * x * s⁻¹ = f * (t * x * t⁻¹) * f⁻¹ := by
        calc s * x * s⁻¹ = f * t * (f⁻¹ * x * f) * t⁻¹ * f⁻¹ := by rw [hsdef]; group
          _ = f * t * x * t⁻¹ * f⁻¹ := by
            have : f⁻¹ * x * f = x := by
              have := hfPc x hx
              rw [hfinv] at this ⊢
              exact this
            rw [this]
          _ = f * (t * x * t⁻¹) * f⁻¹ := by group
      rw [e2, e1]
    have h2 : t * (c * x * c⁻¹) * t⁻¹ = t * x * t⁻¹ := by
      rw [← h1, hsc]; group
    have h3 : c * x * c⁻¹ = x := by
      calc c * x * c⁻¹ = t⁻¹ * (t * (c * x * c⁻¹) * t⁻¹) * t := by group
        _ = t⁻¹ * (t * x * t⁻¹) * t := by rw [h2]
        _ = x := by group
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [h3]
  have hc2 : c * c = 1 := by
    have e1 : f * s * f⁻¹ = t := by
      rw [hsdef]
      calc f * (f * t * f⁻¹) * f⁻¹ = (f * f) * t * (f⁻¹ * f⁻¹) := by group
        _ = t := by rw [hff, hfinv, hff]; group
    have e2 : f * s * f⁻¹ = s * c := by
      calc f * s * f⁻¹ = f * (t * c) * f⁻¹ := by rw [← hsc]
        _ = (f * t * f⁻¹) * (f * c * f⁻¹) := by group
        _ = s * c := by rw [hfPc c hcP]
    have h5 : t = s * c := e1.symm.trans e2
    rw [hsc] at h5
    have h6 : t * (c * c) = t * 1 := by
      calc t * (c * c) = t * c * c := by group
        _ = t := h5.symm
        _ = t * 1 := by group
    exact mul_left_cancel h6
  have hc1 : c ≠ 1 := by
    intro hc1
    apply hF1
    have hst : s = t := by rw [hsc, hc1, mul_one]
    have hft : f * t = t * f := by
      calc f * t = (f * t * f⁻¹) * f := by group
        _ = t * f := by rw [← hsdef, hst]
    have hle : N.P ⊔ zpowers t ≤ centralizer ({f} : Set (MulAut K)) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]; exact hfP x hx
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]; exact hft
    intro d hd
    rw [← P_sup_zpowers_eq_Pt e h N] at hd
    have := hle hd
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this f (Set.mem_singleton f)).symm
  have hcz : c = z := P_central_unique h N n hn hn3 hcP hz hc1 hz1 hcc hzc
  rw [hcz] at hsc
  exact hsc

theorem R_unique_involution (N : L2Notation e) {a b : MulAut K} (ha : a ∈ N.R) (hb : b ∈ N.R)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha2 : a * a = 1) (hb2 : b * b = 1) : a = b := by
  have := R_isCyclic N
  have h1 := DihedralAux.cyclic_unique_involution (G := ↥N.R) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (Subtype.ext ha2) (Subtype.ext hb2)
  exact congrArg Subtype.val h1

theorem t_comm_z (h : L2Field F) (N : L2Notation e) (n : ℕ) (hn : Nat.card N.P = 2 ^ n)
    (hn3 : 3 ≤ n) {z : MulAut K} (hz : z ∈ N.P) (hz1 : z ≠ 1)
    (hzc : ∀ x ∈ N.P, z * x = x * z) : N.t * z * N.t⁻¹ = z := by
  have hzP' : N.t * z * N.t⁻¹ ∈ N.P := conj_mem_P N N.t_mem hz
  have h1 : N.t * z * N.t⁻¹ ≠ 1 := by
    intro h'
    apply hz1
    have := congrArg (fun y => N.t⁻¹ * y * N.t) h'
    simpa [mul_assoc] using this
  have hc : ∀ x ∈ N.P, (N.t * z * N.t⁻¹) * x = x * (N.t * z * N.t⁻¹) := by
    intro x hx
    have hx' : N.t⁻¹ * x * N.t⁻¹⁻¹ ∈ N.P :=
      conj_mem_P N ((N.T : Subgroup (MulAut K)).inv_mem N.t_mem) hx
    have h2 := hzc _ hx'
    calc N.t * z * N.t⁻¹ * x = N.t * (z * (N.t⁻¹ * x * N.t⁻¹⁻¹)) * N.t⁻¹ := by group
      _ = N.t * ((N.t⁻¹ * x * N.t⁻¹⁻¹) * z) * N.t⁻¹ := by rw [h2]
      _ = x * (N.t * z * N.t⁻¹) := by group
  exact P_central_unique h N n hn hn3 hzP' hz h1 hz1 hc hzc

@[expose] def FInvNotCentPt : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ f ∈ N.R, orderOf f = 2 → ¬ ∀ d ∈ N.Pt, d * f = f * d

theorem ivk_1_2i_a_of (hF1 : FInvNotCentPt) : IVK_1_2i_a := by
  intro F _ _ hF K _ _ e N f hf hf2 z hz hz2 hzc
  obtain ⟨n, hn⟩ : ∃ n, Nat.card N.P = 2 ^ n := ⟨_, card_P_eq e N⟩
  have hn3 := three_le_of_involution_mem_R hF N hf hf2 n hn
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h'
    rw [h', orderOf_one] at hz2
    omega
  have hzc' : ∀ x ∈ N.P, z * x = x * z := fun x hx => (hzc x hx).symm
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have key := f_conj_t hF N n hn hf hf2 (hF1 F hF K e N f hf hf2) hz hz1 hzc'
  have htz := t_comm_z hF N n hn hn3 hz hz1 hzc'
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, pow_two] at this
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have h1 : N.t * f * N.t⁻¹ * f⁻¹ = N.t * (f * N.t * f⁻¹)⁻¹ := by group
  rw [commutatorElement_def, h1, key]
  calc N.t * (N.t * z)⁻¹ = N.t * z⁻¹ * N.t⁻¹ := by group
    _ = z := by rw [hzinv, htz]

theorem f_conj_d (h : L2Field F) (N : L2Notation e) (n : ℕ) (hn : Nat.card N.P = 2 ^ n)
    {f : MulAut K} (hf : f ∈ N.R) (hf2 : orderOf f = 2)
    (hF1 : ¬ ∀ d ∈ N.Pt, d * f = f * d) {z : MulAut K} (hz : z ∈ N.P) (hz1 : z ≠ 1)
    (hzc : ∀ x ∈ N.P, z * x = x * z) {d : MulAut K} (hd : d ∈ N.Pt) (hdP : d ∉ N.P) :
    f * d * f⁻¹ = d * z := by
  have hkey := f_conj_t h N n hn hf hf2 hF1 hz hz1 hzc
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, pow_two] at this
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hfP : ∀ x ∈ N.P, f * x = x * f := fun x hx => (N.R_cent f hf hf2 x hx).symm
  have hidx := innAut_relIndex_two e h
  unfold Subgroup.relIndex at hidx
  have hdD : d ∈ innDiagSub e := Pt_le_innDiagSub N hd
  have hpP : d * N.t⁻¹ ∈ N.P := by
    refine ⟨(N.T : Subgroup (MulAut K)).mul_mem hd.1
      ((N.T : Subgroup (MulAut K)).inv_mem N.t_mem), ?_⟩
    have hq := Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨d, hdD⟩ : ↥(innDiagSub e)))
      (b := ⟨N.t⁻¹, (innDiagSub e).inv_mem N.t_mem_diag⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hq
    apply hq.mpr
    constructor
    · intro hh; exact absurd hh (fun hh' => hdP ⟨hd.1, hh'⟩)
    · intro hh; exact absurd ((innAut K).inv_mem_iff.mp hh) N.t_not_mem_inn
  set p := d * N.t⁻¹ with hpdef
  have hd' : d = p * N.t := by rw [hpdef]; group
  have hfp : f * p * f⁻¹ = p := by
    rw [hfinv, hfP p hpP, mul_assoc, hff, mul_one]
  calc f * d * f⁻¹ = (f * p * f⁻¹) * (f * N.t * f⁻¹) := by rw [hd']; group
    _ = p * (N.t * z) := by rw [hfp, hkey]
    _ = d * z := by rw [hd']; group

theorem P_exists_central_involution (h : L2Field F) (N : L2Notation e) (n : ℕ)
    (hn : Nat.card N.P = 2 ^ n) (hn3 : 3 ≤ n) :
    ∃ z ∈ N.P, z ≠ 1 ∧ z * z = 1 ∧ ∀ x ∈ N.P, z * x = x * z := by
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := P_dihedral_model h N n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hk' : k = 4 * 2 ^ m := by
    have : 2 ^ (m + 3) = 2 * (4 * 2 ^ m) := by ring
    omega
  have hpos : 0 < 2 ^ m := by positivity
  have hkE : Even k := ⟨2 * 2 ^ m, by omega⟩
  have hkne : k ≠ 2 := by omega
  obtain ⟨c, hcc, hc1, hc2⟩ := DihedralAux.exists_central_involution hkE hkne (by omega)
  refine ⟨(φ.symm c : MulAut K), (φ.symm c).2, ?_, ?_, ?_⟩
  · intro h'
    apply hc1
    have : φ.symm c = 1 := Subtype.ext h'
    simpa using congrArg φ this
  · have : φ.symm c * φ.symm c = 1 := by rw [← map_mul, hc2, map_one]
    exact congrArg Subtype.val this
  · intro x hx
    have := Subgroup.mem_center_iff.mp hcc (φ ⟨x, hx⟩)
    have h2 := congrArg (fun y => (φ.symm y : MulAut K)) this
    simp only [map_mul, MulEquiv.symm_apply_apply] at h2
    exact h2.symm

theorem ivk_1_2i_c_of (hF1 : FInvNotCentPt) : IVK_1_2i_c := by
  intro F _ _ hF K _ _ e N f hf hf2 x hxT hx2
  by_cases hxD : x ∈ N.Pt
  · by_cases hxP : x ∈ N.P
    · exact Or.inl hxP
    · exact Or.inr (Or.inl ⟨hxD, hxP⟩)
  · right; right
    obtain ⟨n, hn⟩ : ∃ n, Nat.card N.P = 2 ^ n := ⟨_, card_P_eq e N⟩
    have hn3 := three_le_of_involution_mem_R hF N hf hf2 n hn
    have hff : f * f = 1 := by
      have := pow_orderOf_eq_one f
      rwa [hf2, pow_two] at this
    have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
    have hf1 : f ≠ 1 := by
      intro h'
      rw [h', orderOf_one] at hf2
      omega
    have hx2' : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx2, pow_two] at this
    obtain ⟨d, hd, r, hr, hxdr⟩ := T_decomp N x hxT
    have hrT : r ∈ (N.T : Subgroup (MulAut K)) := hr.1
    have hdT : d ∈ (N.T : Subgroup (MulAut K)) := hd.1
    have hr1 : r ≠ 1 := by
      rintro rfl
      apply hxD
      rw [hxdr, mul_one]
      exact hd
    have hrr : r * r = 1 := by
      have hrd : r * d * r⁻¹ ∈ N.Pt :=
        ⟨(N.T : Subgroup (MulAut K)).mul_mem
          ((N.T : Subgroup (MulAut K)).mul_mem hrT hdT) ((N.T : Subgroup (MulAut K)).inv_mem hrT),
          (innDiagSub_normal e).conj_mem d (Pt_le_innDiagSub N hd) r⟩
      have h1 : (d * (r * d * r⁻¹)) * (r * r) = 1 := by
        calc (d * (r * d * r⁻¹)) * (r * r) = (d * r) * (d * r) := by group
          _ = x * x := by rw [hxdr]
          _ = 1 := hx2'
      have h2 : r * r = (d * (r * d * r⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : r * r ∈ N.Pt := by
        rw [h2]; exact N.Pt.inv_mem (N.Pt.mul_mem hd hrd)
      have h4 : r * r ∈ N.Pt ⊓ N.R := ⟨h3, N.R.mul_mem hr hr⟩
      rw [(ivk_1_2f F hF K e N).1] at h4
      simpa using h4
    have hrf : r = f := R_unique_involution N hr hf hr1 hf1 hrr hff
    have hxdf : x = d * f := by rw [hxdr, hrf]
    refine ⟨d, ?_, hxdf⟩
    by_contra hdP
    obtain ⟨z, hz, hz1, hzz, hzc⟩ := P_exists_central_involution hF N n hn hn3
    have hF1f := hF1 F hF K e N f hf hf2
    have hfd := f_conj_d hF N n hn hf hf2 hF1f hz hz1 hzc hd hdP
    have hdd : d * d = z := by
      have h1 : (d * f) * (d * f) = d * (f * d * f⁻¹) * (f * f) := by group
      rw [← hxdf, hx2', hfd, hff] at h1
      have h2 : d * (d * z) = 1 := by simpa using h1.symm
      have h3 : d * d * z = 1 := by rw [← mul_assoc] at h2; exact h2
      have h4 : d * d = z⁻¹ := eq_inv_of_mul_eq_one_left h3
      rw [h4]
      exact inv_eq_of_mul_eq_one_right hzz
    have hzPt : ∀ y ∈ N.Pt, z * y = y * z := by
      have hle : N.P ⊔ zpowers N.t ≤ centralizer ({z} : Set (MulAut K)) := by
        refine sup_le ?_ ?_
        · intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          rw [Set.mem_singleton_iff] at hg
          rw [hg]; exact hzc y hy
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro g hg
          rw [Set.mem_singleton_iff] at hg
          have htz := t_comm_z hF N n hn hn3 hz hz1 hzc
          rw [hg]
          calc z * N.t = (N.t * z * N.t⁻¹) * N.t := by rw [htz]
            _ = N.t * z := by group
      intro y hy
      rw [← P_sup_zpowers_eq_Pt e hF N] at hy
      have := hle hy
      rw [Subgroup.mem_centralizer_iff] at this
      exact this z (Set.mem_singleton z)
    obtain ⟨φ⟩ := Pt_dihedral_model hF N n hn
    have hdv : 8 ∣ 2 ^ n := by
      have : (2 : ℕ) ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 hn3
      simpa using this
    obtain ⟨y, hy⟩ := DihedralAux.sq_eq_central_is_sq_of_dvd hdv (by positivity) φ
      (z := ⟨z, P_le_Pt N hz⟩)
      (fun y' => Subtype.ext (hzPt y' y'.2)) (fun h' => hz1 (congrArg Subtype.val h'))
      (d := ⟨d, hd⟩) (Subtype.ext hdd)
    apply hdP
    have hyD : (y : MulAut K) ∈ innDiagSub e := Pt_le_innDiagSub N y.2
    have hidx := innAut_relIndex_two e hF
    unfold Subgroup.relIndex at hidx
    have hsq := Subgroup.mul_self_mem_of_index_two hidx (⟨y, hyD⟩ : ↥(innDiagSub e))
    rw [Subgroup.mem_subgroupOf] at hsq
    refine ⟨hdT, ?_⟩
    have : d = (y : MulAut K) * y := congrArg Subtype.val hy
    rw [this]
    exact hsq

theorem ivk_1_2h_a : IVK_1_2h_a := by
  intro F _ _ hF K _ _ e N f hf hf2
  refine ⟨?_, fun x hx => N.R_cent f hf hf2 x hx⟩
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ innDiagSub e ⊓ fieldAutSub e :=
    ⟨innAut_le_innDiagSub e hx.1.2, (Subgroup.zpowers_le).2 hf.2 hx.2⟩
  rw [innDiagSub_inf_fieldAutSub e] at h1
  exact h1

end Key



end CFSG.GH74.GLS.IVK
