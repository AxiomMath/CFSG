module

public import CFSG.GH74.GLS.Stage4.T2P56bRed
public import CFSG.GH74.GLS.Stage4.T2FourBuild
public import CFSG.GH74.GLS.Stage4.T2FourQ
public import CFSG.GH74.GLS.Stage4.T2CentS
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour
public import CFSG.GH74.GLS.Stage4.T2FourWey

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.Assembly.LowTwoRank CFSG.Open

theorem t2P56_sylow_shape {X : Type*} [Group X] [Finite X] (U : Subgroup X)
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUexp : ∀ a ∈ U, a ^ 2 = 1) (hUcard : Nat.card ↥U = 4)
    (hcent : ∀ g : X, (∀ a ∈ U, g * a = a * g) → (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ U)
    (S : Sylow 2 X) (hUS : U ≤ (S : Subgroup X)) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥(S : Subgroup X) ≃* DihedralGroup (2 ^ (n - 1)))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥(S : Subgroup X) ≃* SemidihedralGroup n)) := by
  have hP : IsPGroup 2 ↥(S : Subgroup X) := S.isPGroup'
  let V : Subgroup ↥(S : Subgroup X) := U.subgroupOf (S : Subgroup X)
  have hVab : ∀ a b : ↥(S : Subgroup X), a ∈ V → b ∈ V → a * b = b * a := by
    intro a b ha hb
    apply Subtype.ext
    exact hUab a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb)
  have hVcomm : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hVab a b a.2 b.2)⟩⟩
  refine CFSG.RankTwoShapes.selfCentralizing_four_shapes hP V hVcomm ?_ ?_ ?_
  · intro v hv
    apply Subtype.ext
    exact hUexp v (Subgroup.mem_subgroupOf.mp hv)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv]
    exact hUcard
  · apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg
      have hcomm : ∀ a ∈ U, (g : X) * a = a * (g : X) := by
        intro a ha
        have := hg ⟨a, hUS ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
        exact (congrArg Subtype.val this).symm
      obtain ⟨k, hk⟩ := hP g
      exact Subgroup.mem_subgroupOf.mpr (hcent g hcomm ⟨k, by exact congrArg Subtype.val hk⟩)
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hVab h v hh hv


theorem t2P56_two_ne_zero {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  refine Ring.two_ne_zero fun h => ?_
  have := Fintype.ofFinite F
  have h1 : Fintype.card F % 2 = 0 := FiniteField.even_card_of_char_two h
  rw [← Nat.card_eq_fintype_card] at h1
  have := Nat.odd_iff.mp hodd
  omega

theorem t2P56_eight_dvd_card_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    8 ∣ Nat.card (SL2 F) := by
  rw [t2C_card_sl2]
  obtain ⟨a, ha⟩ := hodd
  rw [ha]
  have h1 : (2 * a + 1) ^ 2 - 1 = 4 * (a * (a + 1)) := by
    have : (2 * a + 1) ^ 2 = 4 * (a * (a + 1)) + 1 := by ring
    omega
  rw [h1]
  have h2 : 2 ∣ a * (a + 1) := (Nat.even_mul_succ_self a).two_dvd
  obtain ⟨c, hc⟩ := h2
  exact ⟨(2 * a + 1) * c, by rw [hc]; ring⟩

theorem t2P56_not_dihedral {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (K : Subgroup X) (e : ↥K ≃* SL2 F) (S : Sylow 2 X) {m : ℕ}
    (hS : Nonempty (↥(S : Subgroup X) ≃* DihedralGroup (2 ^ m))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := t2P56_two_ne_zero hodd
  obtain ⟨φ⟩ := hS
  set z : X := (e.symm (negOne F) : X) with hz
  have hzK : z ∈ K := (e.symm (negOne F)).2
  have hze : e ⟨z, hzK⟩ = negOne F := by simp [hz]
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  set Q : Subgroup X := (Q₀ : Subgroup ↥K).map K.subtype with hQ
  have hQK : Q ≤ K := Subgroup.map_subtype_le _
  have hQp : IsPGroup 2 ↥Q := Q₀.isPGroup'.map K.subtype
  have hQcard : Nat.card ↥Q = 2 ^ (Nat.card ↥K).factorization 2 := by
    rw [hQ, Subgroup.card_map_of_injective K.subtype_injective]
    exact Q₀.card_eq_multiplicity
  have hQ8 : 8 ≤ Nat.card ↥Q := by
    have h8 : 8 ∣ Nat.card ↥K := by
      rw [Nat.card_congr e.toEquiv]; exact t2P56_eight_dvd_card_sl2 hodd
    have : 3 ≤ (Nat.card ↥K).factorization 2 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
        (show 2 ^ 3 ∣ Nat.card ↥K by simpa using h8)
      exact this
    rw [hQcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (Nat.card ↥K).factorization 2 := Nat.pow_le_pow_right (by norm_num) this
  have hzz : z * z = 1 := by
    have : e ⟨z, hzK⟩ * e ⟨z, hzK⟩ = 1 := by rw [hze]; exact negOne_mul_self
    have h1 : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := e.injective (by rw [map_mul, this, map_one])
    simpa using congrArg Subtype.val h1
  have hQnc : ¬ ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro hab
    have hidx : ¬ 2 ∣ Q.relIndex K := by
      have h1 : Q.relIndex K = (Q₀ : Subgroup ↥K).index := by
        have hKtop : (⊤ : Subgroup ↥K).map K.subtype = K := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        have := Subgroup.relIndex_map_map_of_injective (f := K.subtype) (Q₀ : Subgroup ↥K) ⊤
          K.subtype_injective
        rw [hKtop, Subgroup.relIndex_top_right] at this
        exact this
      rw [h1]
      exact Q₀.not_dvd_index
    have hle : Q ≤ Subgroup.zpowers z := by
      intro x hx
      exact t2C_cent_sylow_K hodd e hQp hidx hzK hze x (hQK hx) (fun p hp => hab x hx p hp)
    have hz2 : Nat.card ↥(Subgroup.zpowers z) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hzz)
    have := Subgroup.card_le_of_le hle
    omega
  have hQinv : ∀ a ∈ Q, ∀ b ∈ Q, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a = b := by
    have key : ∀ a ∈ Q, a * a = 1 → a ≠ 1 → a = z := by
      intro a ha ha2 ha1
      have haK : a ∈ K := hQK ha
      have h3 : e ⟨a, haK⟩ = negOne F := by
        apply eq_negOne_of_involution h2
        · have : (⟨a, haK⟩ : ↥K) * ⟨a, haK⟩ = 1 := Subtype.ext (by simpa using ha2)
          rw [← map_mul, this, map_one]
        · intro h1
          apply ha1
          have : (⟨a, haK⟩ : ↥K) = 1 := e.injective (by rw [h1, map_one])
          simpa using congrArg Subtype.val this
      have : (⟨a, haK⟩ : ↥K) = ⟨z, hzK⟩ := e.injective (by rw [h3, hze])
      simpa using congrArg Subtype.val this
    intro a ha b hb ha2 hb2 ha1 hb1
    rw [key a ha ha2 ha1, key b hb hb2 hb1]
  obtain ⟨S', hS'⟩ := hQp.exists_le_sylow
  let ψ : ↥(S' : Subgroup X) ≃* DihedralGroup (2 ^ m) := (Sylow.equiv S' S).trans φ
  have hm : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    subst hm0'
    have h1 : Nat.card ↥(S' : Subgroup X) = 2 := by
      rw [Nat.card_congr ψ.toEquiv]
      simp [Nat.card_eq_fintype_card, DihedralGroup.card]
    have := Subgroup.card_le_of_le hS'
    omega
  let W : Subgroup (DihedralGroup (2 ^ m)) := (Q.subgroupOf (S' : Subgroup X)).map ψ.toMonoidHom
  let f : ↥W ≃* ↥Q :=
    (ψ.subgroupMap (Q.subgroupOf (S' : Subgroup X))).symm.trans (Subgroup.subgroupOfEquivOfLe hS')
  rcases CFSG.GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral hm W with
    hcyc | ⟨k, hk, ⟨eW⟩⟩
  · apply hQnc
    have : IsCyclic ↥Q := isCyclic_of_surjective f.toMonoidHom f.surjective
    intro a ha b hb
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := ↥Q)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  ·
    have hn : Nontrivial (ZMod (2 ^ k)) := by
      have : Fact (1 < 2 ^ k) := ⟨Nat.one_lt_two_pow (by omega)⟩
      exact ZMod.nontrivial _
    let s₀ : ↥Q := f (eW.symm (DihedralGroup.sr 0))
    let s₁ : ↥Q := f (eW.symm (DihedralGroup.sr 1))
    have hsq : ∀ i : ZMod (2 ^ k), f (eW.symm (DihedralGroup.sr i)) * f (eW.symm (DihedralGroup.sr i)) = 1 := by
      intro i
      rw [← map_mul, ← map_mul]
      simp
    have hne1 : ∀ i : ZMod (2 ^ k), f (eW.symm (DihedralGroup.sr i)) ≠ 1 := by
      intro i h1
      have := eW.symm.injective (f.injective (h1.trans (map_one f).symm) |>.trans (map_one eW.symm).symm)
      exact absurd this (by simp)
    have hne : s₀ ≠ s₁ := by
      intro h1
      have := eW.symm.injective (f.injective h1)
      simp at this
    exact hne (Subtype.ext (hQinv _ s₀.2 _ s₁.2 (congrArg Subtype.val (hsq 0)) (congrArg Subtype.val (hsq 1))
      (fun h => hne1 0 (Subtype.ext h)) (fun h => hne1 1 (Subtype.ext h))))


section Prep

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G} {K₁ K₂ : Subgroup G}
  {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2P56_prep {n : ℕ}
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hC₁ : centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)))
    (h5 : 5 ≤ 3 ^ n) :
    ∃ (H : Subgroup G) (w₁ w₂ : G), T2Four z t K₁ K₂ H w₁ w₂ ∧
      (∀ x ∈ H, ∀ k : ℕ, x ^ (2 ^ k) = 1 → x ∈ t2U z t) ∧
      (∀ x ∈ K₁, x * t = t * x → x ∈ H) ∧ (∀ x ∈ K₂, x * t = t * x → x ∈ H) := by
  obtain ⟨H, w₁, w₂, hT, ε₁, ε₂, hε₁, hε₂, hq₁, hq₂, hcyc₁, hcyc₂, hcard₁, hcard₂, hform⟩ :=
    t2Four_of_rem hSet hRem hC₁ h5
  have hεeq : ε₂ = ε₁ := by
    have h12 : ε₁ ≡ ε₂ [ZMOD 4] := hq₁.symm.trans hq₂
    unfold Int.ModEq at h12
    rcases hε₁ with h | h <;> rcases hε₂ with h' | h' <;> rw [h, h'] at h12 ⊢ <;> first | rfl | omega
  have hm₁ : Nat.card ↥(H ⊓ K₁) % 4 = 2 := by
    have h1 := hcard₁
    have h2 := hq₁
    unfold Int.ModEq at h2
    rcases hε₁ with h | h <;> rw [h] at h1 h2 <;> omega
  set k : ℕ := Nat.card ↥(H ⊓ K₁) / 2 with hkdef
  have hk2 : 2 * k = Nat.card ↥(H ⊓ K₁) := by omega
  have hkodd : Odd k := Nat.odd_iff.2 (by omega)
  have hc₁ : Nat.card ↥(H ⊓ K₁) = 2 * k := hk2.symm
  have hc₂ : Nat.card ↥(H ⊓ K₂) = 2 * k := by
    have h1 := hcard₂
    rw [hεeq] at h1
    have h2 := hcard₁
    omega
  obtain ⟨Q₁, Q₂, hQ₁H, hQ₂H, hQ₁c, hQ₂c, hQ₁e, hQ₂e, hQ₁₂, hdec⟩ :=
    hT.odd_part hSet.z_mem₁ hSet.z_mem₂ k hkodd hcyc₁ hcyc₂ hc₁ hc₂ hform
  have hcommQ : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy =>
    hT.K_comm x (hQ₁H hx).2 y (hQ₂H hy).2
  have hQe := t2Q_exp hcommQ hQ₁e hQ₂e
  refine ⟨H, w₁, w₂, hT, ?_, ?_, ?_⟩
  · intro x hx s hxs
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    have hUH : t2U z t ≤ H :=
      t2U_le_of_mem hT.zz hT.uu hT.zu_comm hT.z_mem_H hT.u_mem_H
    have haH : a ∈ H := hUH ha
    have hQH : Q₁ ⊔ Q₂ ≤ H := sup_le (fun x hx => (hQ₁H hx).1) (fun x hx => (hQ₂H hx).1)
    have hbH : b ∈ H := hQH hb
    have hab : Commute a b := hT.H_comm a haH b hbH
    have ha2 : a * a = 1 :=
      t2S_closure_sq hT.zz hT.uu hT.zu_comm.symm a ha
    have hb2 : b * b = 1 := by
      have e1 : (a * b) ^ 2 = b ^ 2 := by
        rw [hab.mul_pow, pow_two a, ha2, one_mul]
      have h1 : (b ^ 2) ^ (2 ^ s) = 1 := by
        rw [← e1, ← pow_mul, mul_comm, pow_mul, hxs, one_pow]
      have h2 : (b ^ 2) ^ k = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hQe b hb, one_pow]
      have hcop : Nat.Coprime (2 ^ s) k := Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr hkodd)
      have hd1 : orderOf (b ^ 2) ∣ 2 ^ s := orderOf_dvd_of_pow_eq_one h1
      have hd2 : orderOf (b ^ 2) ∣ k := orderOf_dvd_of_pow_eq_one h2
      have hcop' : Nat.Coprime (orderOf (b ^ 2)) k := Nat.Coprime.coprime_dvd_left hd1 hcop
      have hd : orderOf (b ^ 2) = 1 := Nat.Coprime.eq_one_of_dvd hcop' hd2
      have := orderOf_eq_one_iff.mp hd
      rw [pow_two] at this
      exact this
    have hb1 : b = 1 := t2_pow_odd_trivial hkodd (hQe b hb) hb2
    rw [hb1, mul_one]
    exact ha
  · intro x hx hxt
    exact (hT.H₁_iff x hx).2 hxt
  · intro x hx hxt
    exact (hT.H₂_iff x hx).2 hxt

end Prep


section Main

theorem ch6P56bSylow : Ch6P56bSylow := by
  intro G _ _ hStd hr Gs _ n hn hAt z t K₁ K₂ F₁ F₂ _ _ hSet hRem H w₁ w₂ hT y hyH hyK hyz hyp hyodd
  have := hSet.finite₁
  have := hSet.finite₂
  have hC₁ : centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    have hKR := hSet.le_residual
    have hRC : oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤ centralizer ({z} : Set G) :=
      Subgroup.map_subtype_le _
    have h := Subgroup.relIndex_mul_relIndex (K₁ ⊔ K₂)
      (oPrimeResidualOf 2 (centralizer ({z} : Set G))) (centralizer ({z} : Set G)) hKR hRC
    rw [hT.C_idx, hSet.index_two] at h
    have h1 : (oPrimeResidualOf 2 (centralizer ({z} : Set G))).relIndex
        (centralizer ({z} : Set G)) = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1
  have h5 : 5 ≤ 3 ^ n := by
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨H₀, w₁₀, w₂₀, hT₀, h2part, hH₁, hH₂⟩ := t2P56_prep hSet hRem hC₁ h5
  have hyt : y * t = t * y := hT.H_comm y hyH t hT.u_mem_H
  have hyz' : y * z = z * y := hT.H_comm y hyH z hT.z_mem_H
  have hyH₀ : y ∈ H₀ := hyK.elim (fun h => hH₁ y h hyt) (fun h => hH₂ y h hyt)
  set X : Subgroup G := centralizer ({y} : Set G) with hXdef
  have hzX : z ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hyz'.symm
  have htX : t ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hyt.symm
  have hUX : t2U z t ≤ X := by
    unfold t2U
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzX
    · simpa using htX
  have hzU : z ∈ t2U z t := Subgroup.subset_closure (by simp)
  have htU : t ∈ t2U z t := Subgroup.subset_closure (by simp)
  have hUH : t2U z t ≤ H₀ :=
    t2U_le_of_mem hT₀.zz hT₀.uu hT₀.zu_comm hT₀.z_mem_H hT₀.u_mem_H
  let U' : Subgroup ↥X := (t2U z t).subgroupOf X
  have hUab : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact hT₀.H_comm (a : G) (hUH (Subgroup.mem_subgroupOf.mp ha)) (b : G)
      (hUH (Subgroup.mem_subgroupOf.mp hb))
  have hUexp : ∀ a ∈ U', a ^ 2 = 1 := by
    intro a ha
    apply Subtype.ext
    have h := t2S_closure_sq hT.zz hT.uu hT.zu_comm.symm (a : G) (Subgroup.mem_subgroupOf.mp ha)
    simpa [pow_two] using h
  have hUcard : Nat.card ↥U' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv]
    exact t2U_card hT.zz hT.uu hT.zu_comm hT.z_ne hT.u_ne hT.zu_ne
  have hcent : ∀ g : ↥X, (∀ a ∈ U', g * a = a * g) → (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ U' := by
    intro g hg hk2
    obtain ⟨k, hk⟩ := hk2
    have hgz : (g : G) * z = z * (g : G) :=
      congrArg Subtype.val (hg ⟨z, hzX⟩ (Subgroup.mem_subgroupOf.mpr hzU))
    have hgt : (g : G) * t = t * (g : G) :=
      congrArg Subtype.val (hg ⟨t, htX⟩ (Subgroup.mem_subgroupOf.mpr htU))
    have hgy : (g : G) * y = y * (g : G) := Subgroup.mem_centralizer_singleton_iff.mp g.2
    have hgC : (g : G) ∈ centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgz
    rcases hT₀.Y1 (g : G) hgC hgt with hgH | ⟨x, hxH, hgx⟩
    · refine Subgroup.mem_subgroupOf.mpr (h2part _ hgH k ?_)
      simpa using congrArg Subtype.val hk
    · exfalso
      have hw : (w₁₀ * w₂₀) * y * (w₁₀ * w₂₀)⁻¹ = y⁻¹ := hT₀.w₀_inv y hyH₀
      have hxc : x * y⁻¹ = y⁻¹ * x := hT₀.H_comm x hxH y⁻¹ (H₀.inv_mem hyH₀)
      have h1 : (g : G) * y * (g : G)⁻¹ = y⁻¹ := by
        rw [hgx]
        calc x * (w₁₀ * w₂₀) * y * (x * (w₁₀ * w₂₀))⁻¹
            = x * ((w₁₀ * w₂₀) * y * (w₁₀ * w₂₀)⁻¹) * x⁻¹ := by group
          _ = x * y⁻¹ * x⁻¹ := by rw [hw]
          _ = y⁻¹ := by rw [hxc]; group
      have h2 : (g : G) * y * (g : G)⁻¹ = y := by
        rw [hgy]; group
      have h3 : y = y⁻¹ := h2.symm.trans h1
      have h4 : y ^ 2 = 1 := by
        have : y * y = y * y⁻¹ := by rw [← h3]
        rw [pow_two, this, mul_inv_cancel]
      have h5' : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h4
      have h6 : orderOf y = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h5' with h | h
        · exact absurd h hyp.one_lt.ne'
        · exact h
      rw [h6] at hyodd
      exact absurd hyodd (by decide)
  have hU'p : IsPGroup 2 ↥U' := IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
  obtain ⟨S, hUS⟩ := hU'p.exists_le_sylow
  rcases t2P56_sylow_shape U' hUab hUexp hUcard hcent S hUS with ⟨m, hm, ⟨φ⟩⟩ | ⟨m, hm, ⟨φ⟩⟩
  · exfalso
    obtain ⟨Kj, F, _, _, hKjX, hFodd, ⟨eK⟩⟩ : ∃ (Kj : Subgroup G) (F : Type) (_ : Field F)
        (_ : Finite F), Kj ≤ X ∧ Odd (Nat.card F) ∧ Nonempty (↥Kj ≃* SL2 F) := by
      rcases hyK with h | h
      · obtain ⟨e⟩ := hSet.iso₂
        refine ⟨K₂, F₂, inferInstance, hSet.finite₂, ?_, ?_, ⟨e⟩⟩
        · intro x hx
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hSet.comm y h x hx).symm
        · rw [hSet.card₂]; exact hSet.odd₂
      · obtain ⟨e⟩ := hSet.iso₁
        refine ⟨K₁, F₁, inferInstance, hSet.finite₁, ?_, ?_, ⟨e⟩⟩
        · intro x hx
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hSet.comm x hx y h)
        · rw [hSet.card₁]; exact hSet.odd₁
    exact t2P56_not_dihedral hFodd (Kj.subgroupOf X) ((Subgroup.subgroupOfEquivOfLe hKjX).trans eK) S
      ⟨φ⟩
  · exact ⟨S, Or.inl ⟨m, hm, ⟨φ⟩⟩⟩

end Main

end CFSG.GH74.GLS.Stage4.Rest
