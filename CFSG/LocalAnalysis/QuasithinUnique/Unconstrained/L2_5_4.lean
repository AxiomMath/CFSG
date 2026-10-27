module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.NotationAPI
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace Unc25G2

theorem eq_one_of_pow_eq_one_of_two_pow {G : Type*} [Group G] {x : G} {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hx : x ^ p = 1) (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h4 : Nat.gcd p (2 ^ k) = 1 := hcop
  have h3 := Nat.dvd_gcd h1 h2
  rw [h4] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem conj_comm_aux {G : Type*} [Group G] {z s k : G} (h : s * z = z * s) :
    z⁻¹ * (s⁻¹ * k * s) * z = s⁻¹ * (z⁻¹ * k * z) * s := by
  have h1 : z⁻¹ * s⁻¹ = s⁻¹ * z⁻¹ := by
    rw [← mul_inv_rev, h, mul_inv_rev]
  calc z⁻¹ * (s⁻¹ * k * s) * z = (z⁻¹ * s⁻¹) * k * (s * z) := by group
    _ = (s⁻¹ * z⁻¹) * k * (z * s) := by rw [h1, h]
    _ = s⁻¹ * (z⁻¹ * k * z) * s := by group

end Unc25G2

namespace Tuple25

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem z_inverts_oddCoreIn (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z) :
    ∀ y ∈ oddCoreIn H, z⁻¹ * y * z = y⁻¹ :=
  (IsGamma0.centralizer_le_and_inverts_oddCoreIn hs.setting ht.gamma0 ht.sylow_inf
    hs.setting.isSylowTwoOf_M ht.lt.le ht.z_mem ht.z_ne_one ht.z_sq).2

theorem centreTwo (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z) {L : Subgroup G}
    (hL : IsComponentIn L H) (hin : Ch1.InducesInner z L) : Unc25G2.CentreTwo L := by
  intro y hyL hyc
  apply Unc25G2.exists_pow_two_pow_eq_one_of_odd_trivial
  intro j hj
  have hyjL : y ^ j ∈ L := L.pow_mem hyL j
  have hyjc : ∀ w ∈ L, w * y ^ j = y ^ j * w := fun w hw =>
    ((show Commute w y from hyc w hw).pow_right j).eq
  have hmem : y ^ j ∈ oddCoreIn H := Unc25G2.mem_oddCoreIn_of_central_odd hL hyjL hyjc hj
  have h1 := ht.z_inverts_oddCoreIn hs _ hmem
  obtain ⟨l, hl, hlact⟩ := hin
  have h2 := hlact _ hyjL
  have h3 : l⁻¹ * y ^ j * l = y ^ j := by
    have := hyjc l hl
    calc l⁻¹ * y ^ j * l = l⁻¹ * (y ^ j * l) := by group
      _ = l⁻¹ * (l * y ^ j) := by rw [this]
      _ = y ^ j := by group
  have h4 : (y ^ j)⁻¹ = y ^ j := by rw [← h1, h2, h3]
  have h5 : (y ^ j) ^ 2 = 1 := by
    rw [sq]
    calc y ^ j * y ^ j = y ^ j * (y ^ j)⁻¹ := by rw [h4]
      _ = 1 := mul_inv_cancel _
  have h6 : orderOf (y ^ j) ∣ 2 := orderOf_dvd_of_pow_eq_one h5
  rcases (Nat.dvd_prime Nat.prime_two).mp h6 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hj
    exact absurd hj (by decide)

end Tuple25

namespace Notation25

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

theorem comm_z_of_mem_S {s : G} (hs' : s ∈ N.S) : s * N.z = N.z * s :=
  Subgroup.mem_centralizer_iff.mp N.tuple.z_mem.2 s (N.S_le_T hs')

theorem z_mem_S : N.z ∈ N.S := N.tuple.center_le N.tuple.z_mem

theorem z_inverts_oddCoreIn : ∀ y ∈ oddCoreIn N.H, N.z⁻¹ * y * N.z = y⁻¹ :=
  N.tuple.z_inverts_oddCoreIn hs

theorem centreTwo_K (hin : Ch1.InducesInner N.z N.K) : Unc25G2.CentreTwo N.K :=
  N.tuple.centreTwo hs N.isComp hin

theorem inducesInner_conjugate (hin : Ch1.InducesInner N.z N.K) {s : G} (hsS : s ∈ N.S) :
    Ch1.InducesInner N.z (CFSG.conjugate N.K s) := by
  obtain ⟨l, hl, hlact⟩ := hin
  have hsz := N.comm_z_of_mem_S hsS
  refine ⟨s⁻¹ * l * s, ?_, fun x hx => ?_⟩
  · rw [BenderBranch.mem_conjugate_iff]
    have e : s * (s⁻¹ * l * s) * s⁻¹ = l := by group
    rw [e]
    exact hl
  · have hxK : s * x * s⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hx
    have := hlact _ hxK
    calc N.z⁻¹ * x * N.z = N.z⁻¹ * (s⁻¹ * (s * x * s⁻¹) * s) * N.z := by group
      _ = s⁻¹ * (N.z⁻¹ * (s * x * s⁻¹) * N.z) * s := Unc25G2.conj_comm_aux hsz
      _ = s⁻¹ * (l⁻¹ * (s * x * s⁻¹) * l) * s := by rw [this]
      _ = (s⁻¹ * l * s)⁻¹ * x * (s⁻¹ * l * s) := by group

theorem shape (hin : Ch1.InducesInner N.z N.K) :
    N.K0 = N.K ∨ ∃ s ∈ N.S, CFSG.conjugate N.K s ≠ N.K ∧
      N.K0 = N.K ⊔ CFSG.conjugate N.K s ∧ ⁅N.K, CFSG.conjugate N.K s⁆ = ⊥ := by
  have hcen := N.centreTwo_K hin
  by_cases hall : ∀ s ∈ N.S, CFSG.conjugate N.K s = N.K
  · left
    refine le_antisymm (iSup_le fun s => ?_) N.K_le_K0
    have := hall (s : G)⁻¹ (N.S.inv_mem s.2)
    simp only [CFSG.conjugate, inv_inv] at this
    exact this.le
  · right
    have hall' : ∃ s ∈ N.S, CFSG.conjugate N.K s ≠ N.K := by
      by_contra hcon
      exact hall fun s hs' => by_contra fun hne => hcon ⟨s, hs', hne⟩
    obtain ⟨s₀, hs₀S, hs₀⟩ := hall'
    have hK₂ : IsComponentIn (CFSG.conjugate N.K s₀) N.H :=
      Unc25G2.isComponentIn_conjugate N.isComp (N.S_le_H hs₀S)
    have hdich : ∀ t ∈ N.S, CFSG.conjugate N.K t = N.K ∨
        CFSG.conjugate N.K t = CFSG.conjugate N.K s₀ := by
      intro t ht
      by_contra hcon
      obtain ⟨ht1, ht2⟩ := not_or.mp hcon
      have hK₃ : IsComponentIn (CFSG.conjugate N.K t) N.H :=
        Unc25G2.isComponentIn_conjugate N.isComp (N.S_le_H ht)
      have h₁₂ : ⁅N.K, CFSG.conjugate N.K s₀⁆ = ⊥ :=
        (BenderBranch.eq_or_commute_of_isComponentIn N.isComp hK₂).resolve_left
          fun h => hs₀ h.symm
      have h₁₃ : ⁅N.K, CFSG.conjugate N.K t⁆ = ⊥ :=
        (BenderBranch.eq_or_commute_of_isComponentIn N.isComp hK₃).resolve_left
          fun h => ht1 h.symm
      have h₂₃ : ⁅CFSG.conjugate N.K s₀, CFSG.conjugate N.K t⁆ = ⊥ :=
        (BenderBranch.eq_or_commute_of_isComponentIn hK₂ hK₃).resolve_left
          fun h => ht2 h.symm
      obtain ⟨p, hp, hp2, hpd⟩ := Unc25G2.exists_odd_prime_dvd_card N.isComp
      have hd₂ : p ∣ Nat.card (CFSG.conjugate N.K s₀) := by
        rwa [BenderBranch.card_conjugate]
      have hd₃ : p ∣ Nat.card (CFSG.conjugate N.K t) := by
        rwa [BenderBranch.card_conjugate]
      have hZ₁ : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x ^ p = 1 → x = 1 := by
        intro x hx hxc hxp
        obtain ⟨k, hk⟩ := hcen x hx hxc
        exact Unc25G2.eq_one_of_pow_eq_one_of_two_pow hp hp2 hxp hk
      have hZ₂ : ∀ x ∈ CFSG.conjugate N.K s₀,
          (∀ y ∈ CFSG.conjugate N.K s₀, y * x = x * y) → x ^ p = 1 → x = 1 := by
        intro x hx hxc hxp
        obtain ⟨k, hk⟩ := (hcen.conjugate s₀) x hx hxc
        exact Unc25G2.eq_one_of_pow_eq_one_of_two_pow hp hp2 hxp hk
      obtain ⟨E, hEle, hE, hEcard⟩ := Unc25G2.exists_elemAbelian_card_cube_of_commuting hp
        h₁₂ h₁₃ h₂₃ hZ₁ hZ₂ hpd hd₂ hd₃
      have hEH : E ≤ N.H := hEle.trans (sup_le (sup_le N.K_le_H hK₂.1) hK₃.1)
      exact Unc25G2.false_of_isElemAbelian_card_cube hs.setting.qtke.2.2
        N.tuple.gamma0.isGamma.1 hEH hp hp2 hE hEcard
    refine ⟨s₀, hs₀S, hs₀, ?_, ?_⟩
    · refine le_antisymm (iSup_le fun s => ?_) (sup_le N.K_le_K0 ?_)
      · have := hdich (s : G)⁻¹ (N.S.inv_mem s.2)
        simp only [CFSG.conjugate, inv_inv] at this
        rcases this with h | h
        · exact h.le.trans le_sup_left
        · exact h.le.trans le_sup_right
      · exact le_iSup (fun s : N.S => N.K.map (MulAut.conj (s : G)).toMonoidHom)
          ⟨s₀⁻¹, N.S.inv_mem hs₀S⟩
    · exact (BenderBranch.eq_or_commute_of_isComponentIn N.isComp hK₂).resolve_left
        fun h => hs₀ h.symm

theorem K0_centre_two (hin : Ch1.InducesInner N.z N.K) :
    ∀ u ∈ N.K0, (∀ v ∈ N.K0, v * u = u * v) → ∃ k : ℕ, u ^ 2 ^ k = 1 := by
  intro u hu huc
  have hcen := N.centreTwo_K hin
  rcases N.shape hin with h | ⟨s₀, hs₀S, hne, hK0, hcomm⟩
  · rw [h] at hu huc
    exact hcen u hu huc
  · rw [hK0] at hu huc
    have hc : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K s₀, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp hu
    have haK : ∀ w ∈ N.K, w * a = a * w := by
      intro w hw
      have h1 := huc w (Subgroup.mem_sup_left hw)
      have hbw : b * w = w * b := (hc w hw b hb).symm
      have : w * a * b = a * w * b := by
        calc w * a * b = w * (a * b) := by rw [mul_assoc]
          _ = (a * b) * w := h1
          _ = a * (b * w) := by rw [mul_assoc]
          _ = a * (w * b) := by rw [hbw]
          _ = a * w * b := by rw [mul_assoc]
      exact mul_right_cancel this
    have hbK' : ∀ w ∈ CFSG.conjugate N.K s₀, w * b = b * w := by
      intro w hw
      have h1 := huc w (Subgroup.mem_sup_right hw)
      have haw : a * w = w * a := hc a ha w hw
      have : a * (w * b) = a * (b * w) := by
        calc a * (w * b) = (a * w) * b := by rw [mul_assoc]
          _ = (w * a) * b := by rw [haw]
          _ = w * (a * b) := by rw [mul_assoc]
          _ = (a * b) * w := h1
          _ = a * (b * w) := by rw [mul_assoc]
      exact mul_left_cancel this
    obtain ⟨i, hi⟩ := hcen a ha haK
    obtain ⟨j, hj⟩ := (hcen.conjugate s₀) b hb hbK'
    exact Unc25G2.exists_pow_two_pow_eq_one_mul (hc a ha b hb) hi hj

theorem exists_inner_K0 (hin : Ch1.InducesInner N.z N.K) :
    ∃ c ∈ N.K0, ∀ x ∈ N.K0, N.z⁻¹ * x * N.z = c⁻¹ * x * c := by
  rcases N.shape hin with h | ⟨s₀, hs₀S, hne, hK0, hcomm⟩
  · obtain ⟨l, hl, hlact⟩ := hin
    exact ⟨l, h ▸ hl, fun x hx => hlact x (h ▸ hx)⟩
  · have hin' := N.inducesInner_conjugate hin hs₀S
    obtain ⟨l, hl, hlact⟩ := hin
    obtain ⟨l', hl', hlact'⟩ := hin'
    have hc : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K s₀, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    refine ⟨l * l', ?_, ?_⟩
    · rw [hK0]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hl')
    · intro x hx
      rw [hK0] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp hx
      have hA : N.z⁻¹ * a * N.z = (l * l')⁻¹ * a * (l * l') := by
        rw [hlact a ha]
        have h1 : l' * (l⁻¹ * a * l) = (l⁻¹ * a * l) * l' :=
          (hc _ (N.K.mul_mem (N.K.mul_mem (N.K.inv_mem hl) ha) hl) _ hl').symm
        calc l⁻¹ * a * l = l'⁻¹ * (l' * (l⁻¹ * a * l)) := by group
          _ = l'⁻¹ * ((l⁻¹ * a * l) * l') := by rw [h1]
          _ = (l * l')⁻¹ * a * (l * l') := by group
      have hB : N.z⁻¹ * b * N.z = (l * l')⁻¹ * b * (l * l') := by
        rw [hlact' b hb]
        have h1 : l * b = b * l := hc l hl b hb
        have h2 : l⁻¹ * b * l = b := by
          calc l⁻¹ * b * l = l⁻¹ * (b * l) := by group
            _ = l⁻¹ * (l * b) := by rw [← h1]
            _ = b := by group
        calc l'⁻¹ * b * l' = l'⁻¹ * (l⁻¹ * b * l) * l' := by rw [h2]
          _ = (l * l')⁻¹ * b * (l * l') := by group
      calc N.z⁻¹ * (a * b) * N.z = (N.z⁻¹ * a * N.z) * (N.z⁻¹ * b * N.z) := by group
        _ = ((l * l')⁻¹ * a * (l * l')) * ((l * l')⁻¹ * b * (l * l')) := by rw [hA, hB]
        _ = (l * l')⁻¹ * (a * b) * (l * l') := by group

theorem K0_le_centralizer_pCoreOf :
    N.K0 ≤ Subgroup.centralizer (pCoreOf 2 N.H : Set G) := by
  refine iSup_le fun s => ?_
  have hL : IsComponentIn (CFSG.conjugate N.K (s : G)⁻¹) N.H :=
    Unc25G2.isComponentIn_conjugate N.isComp (N.H.inv_mem (N.S_le_H s.2))
  have hcomm := Unc25G2.commutator_pCoreOf_eq_bot hL
  have h : N.K.map (MulAut.conj (s : G)).toMonoidHom = CFSG.conjugate N.K (s : G)⁻¹ := by
    simp only [CFSG.conjugate, inv_inv]
  rw [h]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem SC_eq : N.SC = pCoreOf 2 N.H := by
  apply le_antisymm
  · have h2 : IsPGroup 2 N.SC := N.tuple.sylow.isPGroup.to_le N.SC_le_S
    have hK0 : N.K0 ≤ Subgroup.centralizer (N.SC : Set G) := fun k hk =>
      Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer ha) k hk).symm
    have hHN : N.H ≤ Subgroup.normalizer (N.SC : Set G) :=
      N.H_le_normalizer_of hK0 N.S_le_normalizer_SC
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 N.SC N.H
      (N.SC_le_S.trans N.S_le_H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (N.SC_le_S.trans N.S_le_H)).mpr hHN) h2
  · show pCoreOf 2 N.H ≤ N.S ⊓ Subgroup.centralizer (N.K0 : Set G)
    refine le_inf ?_ ?_
    · exact N.tuple.sylow.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N.H)
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N.H)
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N.H)
    · intro q hq
      exact Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (Subgroup.mem_centralizer_iff.mp (N.K0_le_centralizer_pCoreOf hk) q hq).symm

theorem SC_sylow : IsSylowTwoOf N.SC (N.H ⊓ Subgroup.centralizer (N.K0 : Set G)) := by
  have hn : N.H ≤ Subgroup.normalizer
      ((N.H ⊓ Subgroup.centralizer (N.K0 : Set G) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf N.H N.H _
      Subgroup.le_normalizer
      (N.H_le_normalizer_K0.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer _))
  have hsub : ((N.H ⊓ Subgroup.centralizer (N.K0 : Set G)).subgroupOf N.H).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hn).isSubnormal
  have h := RankOneRecog.isSylowTwoOf_inf_of_subnormal N.tuple.sylow inf_le_left hsub
  have e : N.S ⊓ (N.H ⊓ Subgroup.centralizer (N.K0 : Set G)) = N.SC :=
    le_antisymm (fun x hx => ⟨hx.1, hx.2.2⟩) (fun x hx => ⟨hx.1, N.S_le_H hx.1, hx.2⟩)
  rwa [e] at h

theorem SK_sylow : IsSylowTwoOf N.SK N.K :=
  RankOneRecog.isSylowTwoOf_inf_of_subnormal N.tuple.sylow N.K_le_H N.isComp.2.2

theorem SK0_sylow : IsSylowTwoOf N.SK0 N.K0 := by
  have hn : (N.K0.subgroupOf N.H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer N.K0_le_H).mpr N.H_le_normalizer_K0
  exact RankOneRecog.isSylowTwoOf_inf_of_subnormal N.tuple.sylow N.K0_le_H hn.isSubnormal

theorem SC_ne_bot : N.SC ≠ ⊥ := by
  rw [N.SC_eq]
  exact N.tuple.gamma0.isGamma.1

theorem exists_decomp (hin : Ch1.InducesInner N.z N.K) :
    ∃ w ∈ N.SC, ∃ c ∈ N.K0, N.z = w * c := by
  obtain ⟨c, hcK, hcact⟩ := N.exists_inner_K0 hin
  obtain ⟨w, hw⟩ : ∃ w : G, w = N.z * c⁻¹ := ⟨_, rfl⟩
  have hzS : N.z ∈ N.S := N.z_mem_S
  have hzH : N.z ∈ N.H := N.S_le_H hzS
  have hcH : c ∈ N.H := N.K0_le_H hcK
  have hwH : w ∈ N.H := by
    rw [hw]
    exact N.H.mul_mem hzH (N.H.inv_mem hcH)
  have hwC : w ∈ Subgroup.centralizer (N.K0 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxz : x * N.z = N.z * (c⁻¹ * x * c) := by
      rw [← hcact x hx]
      group
    calc x * w = (x * N.z) * c⁻¹ := by rw [hw]; group
      _ = (N.z * (c⁻¹ * x * c)) * c⁻¹ := by rw [hxz]
      _ = w * x := by rw [hw]; group
  have hz2 : N.z * N.z = 1 := by
    have := N.tuple.z_sq
    rwa [sq] at this
  have hzN : N.z ∈ Subgroup.normalizer (N.K0 : Set G) := N.S_le_normalizer_K0 hzS
  have hw2mem : w * w ∈ N.K0 := by
    have e : w * w = (N.z * c⁻¹ * N.z⁻¹) * c⁻¹ := by
      rw [hw]
      calc N.z * c⁻¹ * (N.z * c⁻¹) = (N.z * c⁻¹ * N.z⁻¹) * (N.z * N.z) * c⁻¹ := by group
        _ = (N.z * c⁻¹ * N.z⁻¹) * c⁻¹ := by rw [hz2, mul_one]
    rw [e]
    exact N.K0.mul_mem ((Subgroup.mem_normalizer_iff.mp hzN c⁻¹).mp (N.K0.inv_mem hcK))
      (N.K0.inv_mem hcK)
  have hw2c : ∀ v ∈ N.K0, v * (w * w) = (w * w) * v := by
    intro v hv
    have h1 : v * w = w * v := Subgroup.mem_centralizer_iff.mp hwC v hv
    calc v * (w * w) = (v * w) * w := by rw [mul_assoc]
      _ = (w * v) * w := by rw [h1]
      _ = w * (v * w) := by rw [mul_assoc]
      _ = w * (w * v) := by rw [h1]
      _ = (w * w) * v := by rw [mul_assoc]
  obtain ⟨k, hk⟩ := N.K0_centre_two hin (w * w) hw2mem hw2c
  have hw2 : ∃ k : ℕ, w ^ 2 ^ k = 1 := by
    refine ⟨k + 1, ?_⟩
    rw [← sq] at hk
    rw [← pow_mul, ← pow_succ'] at hk
    exact hk
  have hn : N.H ⊓ Subgroup.centralizer (N.K0 : Set G) ≤ Subgroup.normalizer (N.SC : Set G) := by
    have hK0 : N.K0 ≤ Subgroup.centralizer (N.SC : Set G) := fun k hk =>
      Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer ha) k hk).symm
    exact inf_le_left.trans (N.H_le_normalizer_of hK0 N.S_le_normalizer_SC)
  have hwSC : w ∈ N.SC :=
    Unc25G2.mem_of_isSylowTwoOf_of_normalizes N.SC_sylow hn ⟨hwH, hwC⟩ hw2
  refine ⟨w, hwSC, c, hcK, ?_⟩
  rw [hw]
  group

theorem z_mem_K0_sup_SC (hin : Ch1.InducesInner N.z N.K) : N.z ∈ N.K0 ⊔ N.SC := by
  obtain ⟨w, hwSC, c, hcK, hzwc⟩ := N.exists_decomp hin
  rw [hzwc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hwSC) (Subgroup.mem_sup_left hcK)

theorem z_not_mem_SC (hL : ComponentList M N.S N.z N.K) : N.z ∉ N.SC := by
  intro hz
  have hzc : N.z ∈ Subgroup.centralizer (N.K0 : Set G) := N.SC_le_centralizer hz
  have hKc : N.K ≤ Subgroup.centralizer (Subgroup.zpowers N.z : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hzc k (N.K_le_K0 hk))
  have hbot : ⁅N.K, Subgroup.zpowers N.z⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKc
  rw [hL.2.2.1] at hbot
  exact Unc25G2.isComponentIn_ne_bot N.isComp hbot

end Notation25

theorem notation254 : Notation254 := by
  intro G _ _ T M hs N hL
  have hin : Ch1.InducesInner N.z N.K := hL.2.1
  exact
    { shape := N.shape hin
      SC_eq := N.SC_eq
      SC_sylow := N.SC_sylow
      SC_ne_bot := N.SC_ne_bot
      z_mem := N.z_mem_K0_sup_SC hin
      z_not_mem := N.z_not_mem_SC hL }

end CFSG.QuasithinUnique
