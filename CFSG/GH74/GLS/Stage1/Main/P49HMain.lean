module

public import CFSG.GH74.GLS.Stage1.Main.P49HD
public import CFSG.GH74.GLS.Stage1.Main.P49T
public import CFSG.GH74.GLS.Stage1.Main.P49HBase

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.LocalAnalysis.SteinbergBK CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H

section Aux

variable {Y : Type} [Group Y]

theorem card_of_quat {Q : Subgroup Y} {n : ℕ} (hQ : IVK.IsQuaternionTwoGroup ↥Q n) :
    Nat.card ↥Q = 2 ^ n := by
  obtain ⟨hn, ⟨e⟩⟩ := hQ
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  calc 4 * 2 ^ (n - 2) = 2 ^ 2 * 2 ^ (n - 2) := by norm_num
    _ = 2 ^ n := by rw [← pow_add]; congr 1; omega

theorem unique_invol_of_quat {Q : Subgroup Y} {n : ℕ} (hQ : IVK.IsQuaternionTwoGroup ↥Q n) {x y : Y}
    (hx : x ∈ Q) (hy : y ∈ Q) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) : x = y := by
  obtain ⟨hn, ⟨e⟩⟩ := hQ
  have h1 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution (2 ^ (n - 2))
    (by positivity) (e ⟨x, hx⟩)).mp (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hx2)
  have h2 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution (2 ^ (n - 2))
    (by positivity) (e ⟨y, hy⟩)).mp (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hy2)
  exact congrArg Subtype.val (e.injective (h1.trans h2.symm))

theorem map_center_eq_inf_centralizer (Kb : Subgroup Y) :
    (center ↥Kb).map Kb.subtype = Kb ⊓ centralizer (Kb : Set Y) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.1 hz ⟨h, hh⟩
    exact congrArg Subtype.val this
  · rintro ⟨hx, hxc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 hxc) g g.2

end Aux

section FourGroups

variable {Y : Type} [Group Y]

theorem trivial_of_fixed {U : Subgroup Y} (hU : IVK.IsFourSubgroup U) {c : Y}
    (hc : ∀ x ∈ U, c * x * c⁻¹ ∈ U) {a : ℕ} (hca : c ^ (3 ^ a) = 1) {w : Y} (hw : w ∈ U)
    (hw1 : w ≠ 1) (hcw : c * w * c⁻¹ = w) : ∀ x ∈ U, c * x * c⁻¹ = x := by
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => P49T.sq_of_four hU hx
  intro x hx
  by_cases hx1 : x = 1
  · subst hx1; simp
  by_cases hxw : x = w
  · subst hxw; exact hcw
  have hmem := fun y => CFSG.QuasithinUnique.Unc25Small.mem_klein_iff hU.2 hsq hw hx hw1 hx1
    (Ne.symm hxw) y
  have hcx : c * x * c⁻¹ ∈ U := hc x hx
  have hcx1 : c * x * c⁻¹ ≠ 1 := by
    intro h; apply hx1
    have := congrArg (fun y => c⁻¹ * y * c) h
    simpa [mul_assoc] using this
  have hcxw : c * x * c⁻¹ ≠ w := by
    intro h; apply hxw
    have h' : c * x * c⁻¹ = c * w * c⁻¹ := h.trans hcw.symm
    have := mul_right_cancel h'
    exact mul_left_cancel this
  rcases (hmem _).1 hcx with h | h | h | h
  · exact absurd h hcx1
  · exact absurd h hcxw
  · exact h
  · exfalso
    set f : MulAut Y := MulAut.conj c with hf
    have hfx : f x = w * x := h
    have hfw : f w = w := hcw
    have hff : (f ^ 2) x = x := by
      rw [pow_two, MulAut.mul_apply, hfx, map_mul, hfw, hfx, ← mul_assoc, hsq w hw, one_mul]
    have hpow : ∀ j : ℕ, ((f ^ 2) ^ j) x = x := by
      intro j; induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, MulAut.mul_apply, hff, ih]
    obtain ⟨m, hm⟩ : Odd (3 ^ a) := Odd.pow (by decide)
    have h1 : (f ^ (3 ^ a)) x = x := by
      have : f ^ (3 ^ a) = 1 := by rw [hf, ← map_pow, hca, map_one]
      rw [this]; rfl
    have h2 : (f ^ (3 ^ a)) x = f x := by
      rw [hm, pow_succ', MulAut.mul_apply, pow_mul, hpow m]
    have : f x = x := h2.symm.trans h1
    rw [hfx] at this
    apply hw1
    have : w * x = 1 * x := by rw [one_mul]; exact this
    exact mul_right_cancel this

theorem not_le_of_isFour [Finite Y] {Kb : Subgroup Y} (hKn : Kb.Normal) {T : Subgroup Y}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {n : ℕ} (hP : IVK.IsQuaternionTwoGroup ↥(T ⊓ Kb) n)
    {V : Subgroup Y} (hV : IVK.IsFourSubgroup V) (hVK : V ≤ Kb) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 ↥V := by
    have := hV.1
    exact IsElementaryAbelian.isPGroup 2 ↥V
  obtain ⟨P0, hP0⟩ := exists_sylow_eq_of_isSylowOf_top hT
  obtain ⟨P', hP'⟩ := hV2.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y P' P0
  have hconj : ∀ x ∈ V, y * x * y⁻¹ ∈ T := by
    intro x hx
    rw [← hP0, ← hy, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hP' hx, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  obtain ⟨a, haV, b, hbV, ha2, hb2, hab⟩ := CFSG.GH74.GLS.Stage2.Local.exists_two_involutions_of_isFour hV
  have hord : ∀ x : Y, orderOf x = 2 → orderOf (y * x * y⁻¹) = 2 := by
    intro x hx
    have h := MulEquiv.orderOf_eq (MulAut.conj y) x
    rw [MulAut.conj_apply, hx] at h
    exact h
  have h1 := unique_invol_of_quat hP (x := y * a * y⁻¹) (y := y * b * y⁻¹)
    ⟨hconj a haV, hKn.conj_mem a (hVK haV) y⟩ ⟨hconj b hbV, hKn.conj_mem b (hVK hbV) y⟩
    (hord a ha2) (hord b hb2)
  apply hab
  have h2 := mul_right_cancel h1
  exact mul_left_cancel h2

theorem not_mem_of_four [Finite Y] {Kb : Subgroup Y} (hKn : Kb.Normal) {T : Subgroup Y}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {n : ℕ} (hP : IVK.IsQuaternionTwoGroup ↥(T ⊓ Kb) n)
    {V : Subgroup Y} (hV : IVK.IsFourSubgroup V) {c : Y} (hcV : ∀ v ∈ V, c * v * c⁻¹ ∈ V) {a : ℕ}
    (hca : c ^ (3 ^ a) = 1) (hcn : ∃ v ∈ V, c * v * c⁻¹ ≠ v) : c ∉ Kb := by
  intro hc
  obtain ⟨v, hvV, hv⟩ := hcn
  set w := (c * v * c⁻¹) * v⁻¹ with hw
  have hwV : w ∈ V := V.mul_mem (hcV v hvV) (V.inv_mem hvV)
  have hwK : w ∈ Kb := by
    have : w = c * (v * c⁻¹ * v⁻¹) := by rw [hw]; group
    rw [this]
    exact Kb.mul_mem hc (hKn.conj_mem c⁻¹ (Kb.inv_mem hc) v)
  have hw1 : w ≠ 1 := fun h => hv (mul_inv_eq_one.1 h)
  have hcw : c * w * c⁻¹ = w := by
    by_contra hne
    set u := c * w * c⁻¹ with hu
    have huV : u ∈ V := hcV w hwV
    have huK : u ∈ Kb := hKn.conj_mem w hwK c
    have hu1 : u ≠ 1 := by
      intro h; apply hw1
      have := congrArg (fun y => c⁻¹ * y * c) h
      simpa [hu, mul_assoc] using this
    have hsq : ∀ x ∈ V, x * x = 1 := fun x hx => P49T.sq_of_four hV hx
    have hmem := fun y => CFSG.QuasithinUnique.Unc25Small.mem_klein_iff hV.2 hsq hwV huV hw1 hu1
      (Ne.symm hne) y
    refine not_le_of_isFour hKn hT hP hV (fun x hx => ?_)
    rcases (hmem x).1 hx with h | h | h | h
    · rw [h]; exact Kb.one_mem
    · rw [h]; exact hwK
    · rw [h]; exact huK
    · rw [h]; exact Kb.mul_mem hwK huK
  exact hv (trivial_of_fixed hV hcV hca hwV hw1 hcw v hvV)

end FourGroups

section Main

variable {Y : Type} [Group Y] [Finite Y]

theorem kd_main (Kb : Subgroup Y) (hKn : Kb.Normal) (hKq : IsQuasisimple ↥Kb)
    (hZ : Nat.card ↥(center ↥Kb) = 2)
    (hout : ∀ α β : MulAut ↥Kb, ∃ k : ↥Kb, α * β * α⁻¹ * β⁻¹ = MulAut.conj k)
    (hO : pPrimeCore 2 Y = ⊥) (hcomp : ∀ L : Subgroup Y, IsComponent L → L ≤ Kb)
    (T : Subgroup Y) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {n : ℕ} (hn : 3 ≤ n)
    (hP : IVK.IsQuaternionTwoGroup ↥(T ⊓ Kb) n)
    (hQ : IVK.IsQuaternionTwoGroup ↥(T ⊓ centralizer (Kb : Set Y)) n)
    (hTcard : Nat.card ↥T = 2 ^ (2 * n))
    (hrot : ∃ s ∈ T, ∀ m : ℕ, s ^ m ∈ Kb → 2 ^ (n - 1) ∣ m)
    (V : Subgroup Y) (c : Y) (hV : IVK.IsFourSubgroup V)
    (hcX : c ∈ oPrimeResidual 2 Y) (hc3 : IsPGroup 3 ↥(zpowers c)) (hcV : ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hcn : ∃ v ∈ V, c * v * c⁻¹ ≠ v) :
    n = 3 ∧ ∃ Hb : Subgroup Y, Nonempty (↥Hb ≃* StatedSL 2 (ZMod 3)) ∧
      (∀ a ∈ Kb, ∀ b ∈ Hb, a * b = b * a) ∧ Nat.card ↥(Kb ⊓ Hb) = 2 ∧
      Kb ⊔ Hb ≤ oPrimeResidual 2 Y ∧ ((Kb ⊔ Hb).subgroupOf (oPrimeResidual 2 Y)).index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hKn
  set D : Subgroup Y := centralizer (Kb : Set Y) with hD
  have hDn : D.Normal := inferInstance
  set X := oPrimeResidual 2 Y with hX
  have hPc : Nat.card ↥(T ⊓ Kb) = 2 ^ n := card_of_quat hP
  have hQc : Nat.card ↥(T ⊓ D) = 2 ^ n := card_of_quat hQ
  have hZ' : Nat.card ↥(Kb ⊓ D) = 2 := by
    rw [← map_center_eq_inf_centralizer, Subgroup.card_map_of_injective Kb.subtype_injective]
    exact hZ
  have hKX : Kb ≤ X := le_oPrimeResidual_of_quasisimple hKq
  have hT2 : IsPGroup 2 ↥T := hT.isPGroup
  obtain ⟨a, ha⟩ := hc3 ⟨c, mem_zpowers c⟩
  have hca : c ^ (3 ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have hres := oPrimeResidual_le_sup hKn hout hT
  have hcN : c ∈ Kb ⊔ D := mem_of_pow_three hres hT2 hcX hca
  obtain ⟨k, hk, d, hd, hkd⟩ := Subgroup.mem_sup_of_normal_left.1 hcN
  have hcKb : c ∉ Kb := not_mem_of_four hKn hT hP hV hcV hca hcn
  have hdkc : d = k⁻¹ * c := by rw [← hkd]; group
  have hdX : d ∈ X := by rw [hdkc]; exact X.mul_mem (X.inv_mem (hKX hk)) hcX
  have hcomm_kd : k * d = d * k := (Subgroup.mem_centralizer_iff.1 hd) k hk
  have hcpow : k ^ (3 ^ a) * d ^ (3 ^ a) = 1 := by
    rw [← Commute.mul_pow (show Commute k d from hcomm_kd), hkd, hca]
  have hdpow : d ^ (3 ^ a) ∈ Kb := by
    have : d ^ (3 ^ a) = (k ^ (3 ^ a))⁻¹ := eq_inv_of_mul_eq_one_right hcpow
    rw [this]
    exact Kb.inv_mem (Kb.pow_mem hk _)
  have hsqz : ∀ z ∈ Kb ⊓ D, z ^ 2 = 1 := by
    intro z hz
    have := pow_card_eq_one' (G := ↥(Kb ⊓ D)) (x := ⟨z, hz⟩)
    rw [hZ'] at this
    simpa using congrArg Subtype.val this
  have hd3sq : (d ^ (3 ^ a)) ^ 2 = 1 := hsqz _ ⟨hdpow, D.pow_mem hd _⟩
  have hd2pow : (d ^ 2) ^ (3 ^ a) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hd3sq]
  obtain ⟨m, hm⟩ : Odd (3 ^ a) := Odd.pow (by decide)
  have hd2ne : d ^ 2 ≠ 1 := by
    intro h2
    have h3 : d ^ (3 ^ a) = d := by rw [hm, pow_succ, pow_mul, h2, one_pow, one_mul]
    apply hcKb
    rw [← hkd]
    exact Kb.mul_mem hk (h3 ▸ hdpow)
  have hnot : ¬ IsPGroup 2 ↥D := by
    intro h2g
    obtain ⟨j, hj⟩ := h2g ⟨d ^ 2, D.pow_mem hd 2⟩
    have hj' : (d ^ 2) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime (3 ^ a) (2 ^ j) := Nat.Coprime.pow a j (by norm_num)
    have h4 : (d ^ 2) ^ (Nat.gcd (3 ^ a) (2 ^ j)) = 1 := pow_gcd_eq_one.2 ⟨hd2pow, hj'⟩
    rw [hcop, pow_one] at h4
    exact hd2ne h4
  obtain ⟨t, e8, ht2, huniq, hC, hker, hcard, hSL⟩ :=
    centralizer_structure hKn hO hcomp hT hn hQ hnot
  have htK : ((t : ↥D) : Y) ∈ Kb := by
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥Kb)) 2 (by rw [hZ])
    have hζK : ((ζ : ↥Kb) : Y) ∈ Kb ⊓ D := by
      have : ((ζ : ↥Kb) : Y) ∈ (center ↥Kb).map Kb.subtype := Subgroup.mem_map.2 ⟨(ζ : ↥Kb), ζ.2, rfl⟩
      rwa [map_center_eq_inf_centralizer] at this
    have hζ2 : orderOf (⟨((ζ : ↥Kb) : Y), hζK.2⟩ : ↥D) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hζ]
    have := huniq _ hζ2
    rw [← this]
    exact hζK.1
  have hn3 : n = 3 := by
    obtain ⟨s, hsT, hs⟩ := hrot
    have hs2 : s ^ 2 ∈ Kb ⊔ D := sq_mem_sup_centralizer hKn hT hPc hQc hZ' hTcard (by omega) hsT
    obtain ⟨k₂, hk₂, d₂, hd₂, hkd₂⟩ := Subgroup.mem_sup_of_normal_left.1 hs2
    set P : Subgroup ↥D := pCore 2 ↥D with hPdef
    have hP'n : (P.map D.subtype).Normal :=
      map_normal_of_characteristic D.subtype D.subtype_injective
        (by rw [Subgroup.range_subtype]; infer_instance)
    let e' : ↥(P.map D.subtype) ≃* QuaternionGroup 2 :=
      (P.equivMapOfInjective D.subtype D.subtype_injective).symm.trans e8
    obtain ⟨f, hf⟩ : ∃ f : ℕ, s ^ (2 ^ f) = 1 := by
      obtain ⟨f, hf⟩ := hT2 ⟨s, hsT⟩
      exact ⟨f, by simpa using congrArg Subtype.val hf⟩
    have hα2 := axisAction_sq_eq_one e' hf
    have hαs2 : axisAction (P.map D.subtype) (s ^ 2) = 1 := by rw [map_pow]; exact hα2
    have hαk : axisAction (P.map D.subtype) k₂ = 1 := by
      refine axisAction_eq_one_of_comm fun x hx => ?_
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
      exact (Subgroup.mem_centralizer_iff.1 u.2) k₂ hk₂
    have hαd : axisAction (P.map D.subtype) d₂ = 1 := by
      have h1 : axisAction (P.map D.subtype) (s ^ 2) =
          axisAction (P.map D.subtype) k₂ * axisAction (P.map D.subtype) d₂ := by
        rw [← hkd₂, map_mul]
      rw [hαs2, hαk, one_mul] at h1
      exact h1.symm
    have hdP : (⟨d₂, hd₂⟩ : ↥D) ∈ P := by
      have h1 : axisAction P ⟨d₂, hd₂⟩ = 1 := axisAction_eq_one_of_map (d := ⟨d₂, hd₂⟩) hαd
      have := MonoidHom.mem_ker.2 h1
      rwa [hker] at this
    have hd4 : (⟨d₂, hd₂⟩ : ↥D) ^ 4 = 1 := pow_four_of_mulEquiv_quaternionEight e8 hdP
    have hd22 : d₂ ^ 2 ∈ Kb := by
      by_cases hu2 : (⟨d₂, hd₂⟩ : ↥D) ^ 2 = 1
      · have : d₂ ^ 2 = 1 := by simpa using congrArg Subtype.val hu2
        rw [this]; exact Kb.one_mem
      · have hord : orderOf ((⟨d₂, hd₂⟩ : ↥D) ^ 2) = 2 :=
          orderOf_eq_prime (by rw [← pow_mul]; exact hd4) hu2
        have h' := huniq _ hord
        have h'' : d₂ ^ 2 = ((t : ↥D) : Y) := by
          have := congrArg Subtype.val h'
          simpa using this
        rw [h'']; exact htK
    have hs4 : s ^ 4 ∈ Kb := by
      have hcomm : k₂ * d₂ = d₂ * k₂ := (Subgroup.mem_centralizer_iff.1 hd₂) k₂ hk₂
      have h1 : s ^ 4 = k₂ ^ 2 * d₂ ^ 2 := by
        calc s ^ 4 = (s ^ 2) ^ 2 := by rw [← pow_mul]
          _ = (k₂ * d₂) ^ 2 := by rw [hkd₂]
          _ = k₂ ^ 2 * d₂ ^ 2 := Commute.mul_pow (show Commute k₂ d₂ from hcomm) 2
      rw [h1]
      exact Kb.mul_mem (Kb.pow_mem hk₂ 2) hd22
    have hdvd := hs 4 hs4
    by_contra hne
    have h8 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  subst hn3
  have hSD : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ D) D :=
    hT.inf_of_le_normalizer le_top Subgroup.le_normalizer_of_normal
  have hcard24 : Nat.card ↥D = 24 := by
    rcases hcard with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, hnd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).1 hSD
      have h1 := Subgroup.relIndex_mul_card (T ⊓ D) D
      rw [inf_eq_left.2 (inf_le_right : T ⊓ D ≤ D), hQc, h] at h1
      have h6 : (T ⊓ D).relIndex D = 6 := by norm_num at h1; omega
      exact hnd ⟨3, by omega⟩
  obtain ⟨iso⟩ := hSL hcard24
  have hPcard : Nat.card ↥(pCore 2 ↥D) = 8 := by
    rw [Nat.card_congr e8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hDX : D ≤ X := by
    set P : Subgroup ↥D := pCore 2 ↥D with hPdef
    set M : Subgroup ↥D := (X ⊓ D).subgroupOf D with hM
    have hPM : P ≤ M := by
      intro u hu
      obtain ⟨j, hj⟩ := (pCore_isPGroup (p := 2) (G := ↥D)) ⟨u, hu⟩
      refine Subgroup.mem_subgroupOf.2 ⟨Subgroup.subset_closure ⟨j, ?_⟩, u.2⟩
      simpa using congrArg (fun z : ↥P => (((z : ↥D)) : Y)) hj
    have hd3M : (⟨d ^ 2, D.pow_mem hd 2⟩ : ↥D) ∈ M :=
      Subgroup.mem_subgroupOf.2 ⟨X.pow_mem hdX 2, D.pow_mem hd 2⟩
    have hd3P : (⟨d ^ 2, D.pow_mem hd 2⟩ : ↥D) ∉ P := by
      intro hP
      obtain ⟨j, hj⟩ := (pCore_isPGroup (p := 2) (G := ↥D)) ⟨_, hP⟩
      have hj' : (d ^ 2) ^ (2 ^ j) = 1 := by
        simpa using congrArg (fun z : ↥P => (((z : ↥D)) : Y)) hj
      have hcop : Nat.Coprime (3 ^ a) (2 ^ j) := Nat.Coprime.pow a j (by norm_num)
      have h4 : (d ^ 2) ^ (Nat.gcd (3 ^ a) (2 ^ j)) = 1 := pow_gcd_eq_one.2 ⟨hd2pow, hj'⟩
      rw [hcop, pow_one] at h4
      exact hd2ne h4
    have hMcard : Nat.card ↥M = 24 := by
      obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hPM
      have hdvd : Nat.card ↥M ∣ 24 := hcard24 ▸ Subgroup.card_subgroup_dvd_card M
      rw [hPcard] at hr
      have hr3 : r = 1 ∨ r = 3 := by
        have h1 : 8 * r ∣ 24 := hr ▸ hdvd
        have h2 : r ∣ 3 := by
          have : 8 * r ∣ 8 * 3 := by simpa using h1
          exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
        rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h <;> simp [h]
      rcases hr3 with h | h
      · exfalso
        have hMP : P = M := Subgroup.eq_of_le_of_card_ge hPM (by rw [hr, h, hPcard])
        exact hd3P (hMP ▸ hd3M)
      · rw [hr, h]
    have hMtop : M = ⊤ := Subgroup.eq_top_of_card_eq M (by rw [hMcard, hcard24])
    intro x hx
    have : (⟨x, hx⟩ : ↥D) ∈ M := hMtop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 this).1
  have hKDX : Kb ⊔ D ≤ X := sup_le hKX hDX
  have hTX : T ≤ X := isPGroup_le_oPrimeResidual hT2
  have hXeq : X = (Kb ⊔ D) ⊔ T := le_antisymm hres (sup_le hKDX hTX)
  refine ⟨rfl, D, ⟨iso.trans (specialLinearGroupEquivStatedSL 2 (ZMod 3))⟩,
    fun a ha b hb => (Subgroup.mem_centralizer_iff.1 hb) a ha, hZ', hKDX, ?_⟩
  have hidx := relIndex_sup_centralizer_eq_two hKn hT hPc hQc hZ' hTcard (by norm_num : 1 ≤ 3)
  change (Kb ⊔ D).relIndex X = 2
  have : (Kb ⊔ D).Normal := inferInstance
  rw [hXeq, Subgroup.relIndex_sup_left]
  exact hidx

end Main

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem kd_structure {Y : Type} [Group Y] [Finite Y]
    (Kb : Subgroup Y) (hKn : Kb.Normal) (hKq : IsQuasisimple ↥Kb) (hZ : Nat.card ↥(center ↥Kb) = 2)
    (hout : ∀ α β : MulAut ↥Kb, ∃ k : ↥Kb, α * β * α⁻¹ * β⁻¹ = MulAut.conj k)
    (hO : pPrimeCore 2 Y = ⊥) (hcomp : ∀ L : Subgroup Y, IsComponent L → L ≤ Kb)
    (T : Subgroup Y) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {n : ℕ} (hn : 3 ≤ n)
    (hP : IVK.IsQuaternionTwoGroup ↥(T ⊓ Kb) n)
    (hQ : IVK.IsQuaternionTwoGroup ↥(T ⊓ centralizer (Kb : Set Y)) n)
    (hTcard : Nat.card ↥T = 2 ^ (2 * n))
    (hrot : ∃ s ∈ T, ∀ m : ℕ, s ^ m ∈ Kb → 2 ^ (n - 1) ∣ m)
    (V : Subgroup Y) (c : Y) (hV : IVK.IsFourSubgroup V) (_hVX : V ≤ oPrimeResidual 2 Y)
    (hcX : c ∈ oPrimeResidual 2 Y) (hc3 : IsPGroup 3 ↥(zpowers c)) (hcV : ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hcn : ∃ v ∈ V, c * v * c⁻¹ ≠ v) :
    n = 3 ∧ ∃ Hb : Subgroup Y, Nonempty (↥Hb ≃* StatedSL 2 (ZMod 3)) ∧
      (∀ a ∈ Kb, ∀ b ∈ Hb, a * b = b * a) ∧ Nat.card ↥(Kb ⊓ Hb) = 2 ∧
      Kb ⊔ Hb ≤ oPrimeResidual 2 Y ∧ ((Kb ⊔ Hb).subgroupOf (oPrimeResidual 2 Y)).index = 2 :=
  P49H.kd_main Kb hKn hKq hZ hout hO hcomp T hT hn hP hQ hTcard hrot V c hV hcX hc3 hcV hcn

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
