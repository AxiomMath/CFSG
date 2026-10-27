module

public import CFSG.Quasithin.H13.L32AC47k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk3

public section

namespace CFSG.Quasithin.H13.L32A.C

open scoped Pointwise
open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem T_le_normalizer_l1_F4 (h1332 : Stmt13_3_2_F4) (S : Setting147 G T L V H) :
    T ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := S.hyp.normalizes_F4 (stmt13_3_2_two_of_F4 h1332)
  have h := A5.le_normalizer_oTwoRes_of_le_normalizer (F7.le_normalizer_inf hTL
    ((U3.T_le_normalizer_fsuV1 T V).trans Subgroup.le_normalizer))
  rwa [oTwoRes_eq_oTwoUpper] at h

theorem lemma14_7_47_l32_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h29 : Thm14_7_29_F4) (h32 : Lemma14_7_32_F4)
    (hMod : Lemma14_7_47_L32Mod_F4) : Lemma14_7_47_L32_F4 := by
  intro G _ _ T L V H S K hK hH hP
  by_contra hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK := h32 G T L V H S K hK
  have hKn := le_normalizer_of_setting h37 h38 S hK hTK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hL3 := relIndex_l1_F4 h1222 h1332 h1334 S.hyp
  have hTl1 := T_le_normalizer_l1_F4 h1332 S

  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  set π₀ : ↥K →* A6.SL3.S := φ.toMonoidHom.comp (QuotientGroup.mk' _) with hπ₀def
  have hπ₀ : Function.Surjective π₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ k : ↥K, π₀ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

  have hTsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTsylH hKH hKn
  have hS2 : IsPGroup 2 (T.subgroupOf K) :=
    hTsylH.2.1.comap_of_injective K.subtype K.subtype_injective
  have hSi : ¬ 2 ∣ (T.subgroupOf K).index := Subgroup.inf_subgroupOf_right T K ▸ hTsyl.2.2
  obtain ⟨h, hhD⟩ := exists_conj_map_eq_of_sylow π₀ hπ₀ hS2 hSi A6.SL3.P0_sylow.1
    A6.SL3.P0_sylow.2
  set π : ↥K →* A6.SL3.S := (MulAut.conj h⁻¹).toMonoidHom.comp π₀ with hπdef
  have hπ : Function.Surjective π := (MulAut.conj h⁻¹).surjective.comp hπ₀
  have hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker₀]
  have hD : (T.subgroupOf K).map π = A6.SL3.P0 := by
    rw [← hhD, Subgroup.map_map]

  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  set β := indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    indHom_apply π hπ hker hKn hHN

  have hgen : ∀ y (hy : y ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ∧ Odd (orderOf y)),
      β ⟨y, hl1H (Subgroup.subset_closure hy)⟩ = 1 := by
    intro y hy
    have hyl1 : y ∈ l1 T L V := Subgroup.subset_closure hy
    have hyH : y ∈ H := hl1H hyl1
    have hodd : Odd (orderOf (β ⟨y, hyH⟩)) :=
      Odd.of_dvd_nat (by rw [Subgroup.orderOf_mk]; exact hy.2) (orderOf_map_dvd β _)
    obtain ⟨g, hg⟩ := mem_inner_of_odd_orderOf sl3_outer hodd
    by_contra hne
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hne (by rw [← hg, map_one])
    have hog : orderOf g = orderOf (β ⟨y, hyH⟩) := by
      rw [← hg, orderOf_injective _ sl3_conj_injective]
    obtain ⟨s, hs, hw⟩ := sl3_comm_fact g hg1 (sl3_pow_21_of_odd (hog ▸ hodd))
    have hsP : s ∈ (T.subgroupOf K).map π := hD ▸ A6.SL3.P0list_mem le_rfl s hs
    obtain ⟨s', hs'T, rfl⟩ := hsP
    have hs'T' : (s' : G) ∈ T := hs'T
    set yH : ↥H := ⟨y, hyH⟩ with hyHdef
    set s₀ : G := (s' : G) with hs₀
    have huK : y⁻¹ * (s₀ * y * s₀⁻¹) ∈ K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hKn (H.inv_mem hyH)) s₀).mp s'.2
      have e : y⁻¹ * (s₀ * y * s₀⁻¹) = (y⁻¹ * s₀ * y⁻¹⁻¹) * s₀⁻¹ := by group
      rw [e]
      exact K.mul_mem h1 (K.inv_mem s'.2)
    have hul1 : y⁻¹ * (s₀ * y * s₀⁻¹) ∈ l1 T L V :=
      (l1 T L V).mul_mem ((l1 T L V).inv_mem hyl1)
        ((Subgroup.mem_normalizer_iff.mp (hTl1 hs'T') y).mp hyl1)
    have hπu : π ⟨_, huK⟩ = g⁻¹ * π s' * g * (π s')⁻¹ := by
      have e1 : (⟨y⁻¹ * (s₀ * y * s₀⁻¹), huK⟩ : ↥K) = conjK (hKn yH⁻¹.2) s' * s'⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply, hyHdef, hs₀]
        group
      rw [e1, map_mul, map_inv, ← hβ, map_inv, ← hg]
      simp [mul_assoc]
    have hu2 : y⁻¹ * (s₀ * y * s₀⁻¹) ∉ pCoreOf 2 (l1 T L V) := by
      intro hmem
      obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l1 T L V)) ⟨_, hmem⟩
      have hun : (⟨_, huK⟩ : ↥K) ^ 2 ^ n = 1 := Subtype.ext (by
        have := congrArg Subtype.val hn
        simpa using this)
      have hπn : (π ⟨_, huK⟩) ^ 2 ^ n = 1 := by rw [← map_pow, hun, map_one]
      exact hw (hπu ▸ sl3_pow_four_of_two_pow hπn)
    exact hnot (oTwoUpper_le_of_mem hL3 hl1H hKH hKn hul1 huK hu2)

  have hL1β : ∀ x (hx : x ∈ l1 T L V), β ⟨x, hl1H hx⟩ = 1 := by
    have hle : l1 T L V ≤ β.ker.map H.subtype :=
      (Subgroup.closure_le _).2 fun y hy =>
        ⟨⟨y, hl1H (Subgroup.subset_closure hy)⟩, hgen y hy, rfl⟩
    intro x hx
    obtain ⟨x', hx'k, hx'⟩ := hle hx
    have e : (⟨x, hl1H hx⟩ : ↥H) = x' := Subtype.ext hx'.symm
    rw [e]
    exact hx'k

  have hcomm : ∀ x ∈ l1 T L V, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    intro x hx k hk
    have h1 := hβ ⟨x, hl1H hx⟩ ⟨k, hk⟩
    rw [hL1β x hx, MulAut.one_apply] at h1
    have h2 : π (conjK (hKn (hl1H hx)) ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) ((hker _).mp h2)

  by_cases hout : ∃ t ∈ T, ∀ k ∈ K, ∃ x ∈ K,
      t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∉ pCoreOf 2 K
  · obtain ⟨t, ht, hto⟩ := hout
    exact hMod G T L V H S K hK hH hP hnot hcomm t ht hto
  push Not at hout

  have hTin : ∀ t (ht : t ∈ T), β ⟨t, hTH ht⟩ ∈ inner A6.SL3.S := by
    intro t ht
    obtain ⟨k, hk, hkx⟩ := hout t ht
    refine ⟨π ⟨k, hk⟩, ?_⟩
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    have h1 := hkx (k * x * k⁻¹) (K.mul_mem (K.mul_mem hk x.2) (K.inv_mem hk))
    have e : t * k⁻¹ * (k * x * k⁻¹) * (t * k⁻¹)⁻¹ * (k * x * k⁻¹)⁻¹ =
        (t * x * t⁻¹) * (k * x * k⁻¹)⁻¹ := by group
    rw [e] at h1
    have h2 : π (conjK (hKn (hTH ht)) x * (⟨k, hk⟩ * x * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹) = 1 := by
      refine (hker _).mpr ?_
      have e3 : ((conjK (hKn (hTH ht)) x * (⟨k, hk⟩ * x * (⟨k, hk⟩ : ↥K)⁻¹)⁻¹ : ↥K) : G) =
          (t * x * t⁻¹) * (k * x * k⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply]
      rw [e3]
      exact h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2.symm
  have hKin : ∀ k (hk : k ∈ K), β ⟨k, hKH hk⟩ = MulAut.conj (π ⟨k, hk⟩) := by
    intro k hk
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hInn : ∀ y : ↥H, β y ∈ inner A6.SL3.S := by
    have hle : K ⊔ (l1 T L V ⊔ T) ≤ ((inner A6.SL3.S).comap β).map H.subtype := by
      refine sup_le (fun k hk => ⟨⟨k, hKH hk⟩, ⟨π ⟨k, hk⟩, (hKin k hk).symm⟩, rfl⟩)
        (sup_le (fun x hx => ⟨⟨x, hl1H hx⟩, ?_, rfl⟩) (fun t ht => ⟨⟨t, hTH ht⟩, hTin t ht, rfl⟩))
      show β ⟨x, hl1H hx⟩ ∈ inner A6.SL3.S
      rw [hL1β x hx]
      exact (inner A6.SL3.S).one_mem
    rw [← hH] at hle
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have e : y = y' := Subtype.ext hyy'.symm
    rw [e]
    exact hy'

  let e := MonoidHom.ofInjective sl3_conj_injective
  set ψ : ↥H →* A6.SL3.S := e.symm.toMonoidHom.comp (β.codRestrict _ hInn) with hψdef
  have hψ : ∀ y : ↥H, MulAut.conj (ψ y) = β y := by
    intro y
    have := congrArg Subtype.val (e.apply_symm_apply (β.codRestrict _ hInn y))
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = π ⟨k, hk⟩ := fun k hk =>
    sl3_conj_injective (by rw [hψ, hKin])
  have hψs : Function.Surjective ψ := fun g => by
    obtain ⟨k, rfl⟩ := hπ g
    exact ⟨⟨k, hKH k.2⟩, hψK k k.2⟩
  have hψl1 : ∀ x (hx : x ∈ l1 T L V), ψ ⟨x, hl1H hx⟩ = 1 := fun x hx =>
    sl3_conj_injective (by rw [hψ, hL1β x hx, map_one])
  have hψT : ∀ t (ht : t ∈ T), ψ ⟨t, hTH ht⟩ ∈ A6.SL3.P0 := by
    intro t ht
    refine sl3_normalizer_P0 _ fun p hp => ?_
    have hpP : p ∈ (T.subgroupOf K).map π := hD ▸ A6.SL3.P0list_mem le_rfl p hp
    obtain ⟨s, hsT, rfl⟩ := hpP
    have e1 : ψ ⟨t, hTH ht⟩ * π s * (ψ ⟨t, hTH ht⟩)⁻¹ = π (conjK (hKn (hTH ht)) s) := by
      rw [← MulAut.conj_apply, hψ, hβ]
    rw [e1]
    have hmem : π (conjK (hKn (hTH ht)) s) ∈ A6.SL3.P0 := by
      rw [← hD]
      refine ⟨_, ?_, rfl⟩
      show ((conjK (hKn (hTH ht)) s : ↥K) : G) ∈ T
      rw [conjK_apply]
      exact T.mul_mem (T.mul_mem ht hsT) (T.inv_mem ht)
    exact hmem

  obtain ⟨c, hc⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).exists_card_eq
  have hcK : Nat.card K = 168 * 2 ^ c := by
    have hle : pCoreOf 2 K ≤ K := Subgroup.map_subtype_le _
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((pCoreOf 2 K).subgroupOf K),
      Nat.card_congr φ.toEquiv, A6.SL3.card_S,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hc]
  have hJK : l1 T L V ⊔ T ≤ Subgroup.normalizer (K : Set G) := (sup_le hl1H hTH).trans hKn
  have hidx : IsTwoThree (K.relIndex H) := by
    have h1 : K.relIndex H = K.relIndex (l1 T L V ⊔ T) := by
      rw [hH, sup_comm, relIndex_sup_eq hJK]
    rw [h1]
    have h2 := isTwoThree_card_sup hL3 hTsylH.2.1 hTl1
    rw [sup_comm] at h2
    exact h2.of_dvd (Subgroup.index_dvd_card _)
  have hcH : Nat.card H = K.relIndex H * (168 * 2 ^ c) := by
    have := Subgroup.relIndex_mul_card (H := K) (K := H)
    rw [inf_eq_left.mpr hKH, hcK] at this
    exact this.symm

  have hparab : ∀ X : Subgroup A6.SL3.S, Nat.card X = 24 → A6.SL3.P0 ≤ X →
      (X.comap ψ).map H.subtype ≤ Subgroup.normalizer (L : Set G) := by
    intro X hX24 hPX
    have hXidx : X.index = 7 := by
      have := X.card_mul_index
      rw [hX24, A6.SL3.card_S] at this
      omega
    have hcP : Nat.card ((X.comap ψ).map H.subtype) = K.relIndex H * (24 * 2 ^ c) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      have h1 := (X.comap ψ).card_mul_index
      rw [Subgroup.index_comap_of_surjective X hψs, hXidx, hcH] at h1
      have h2 : Nat.card (X.comap ψ) * 7 = K.relIndex H * (24 * 2 ^ c) * 7 := by
        rw [h1]
        ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
    have hsolv : Group.IsSolvable ↥((X.comap ψ).map H.subtype) := by
      refine isSolvable_of_isTwoThree ?_
      rw [hcP]
      exact hidx.mul (⟨3 + c, 1, by ring⟩ : IsTwoThree (24 * 2 ^ c))
    refine h29 G T L V S.hyp _ (sup_le ?_ ?_) ((Subgroup.map_subtype_le _).trans S.hz.2.1)
      hsolv
    · intro x hx
      refine ⟨⟨x, hl1H hx⟩, ?_, rfl⟩
      show ψ ⟨x, hl1H hx⟩ ∈ X
      rw [hψl1 x hx]
      exact X.one_mem
    · intro t ht
      exact ⟨⟨t, hTH ht⟩, hPX (hψT t ht), rfl⟩
  have hM1 := hparab A6.SL3.X1 A6.SL3.card_X1 inf_le_left
  have hM2 := hparab A6.SL3.X2 A6.SL3.card_X2 inf_le_right

  apply S.hz.2.2
  have htop : (⊤ : Subgroup ↥H) = A6.SL3.X1.comap ψ ⊔ A6.SL3.X2.comap ψ := by
    rw [Subgroup.comap_sup_eq ψ _ _ hψs, sl3_sup_X, Subgroup.comap_top]
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥H) ∈ A6.SL3.X1.comap ψ ⊔ A6.SL3.X2.comap ψ :=
    htop ▸ Subgroup.mem_top _
  have := Subgroup.mem_map_of_mem H.subtype hy'
  rw [Subgroup.map_sup] at this
  exact sup_le hM1 hM2 this

end Setting

end CFSG.Quasithin.H13.L32A.C
