module

public import CFSG.LargeExtraspecial.AS62F431b
public import Certificates.Data.A5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Quasithin

namespace AS62

theorem exists_comm_pow_ne : ∀ σ : Equiv.Perm (Fin 5), σ ≠ 1 →
    ∃ a : Equiv.Perm (Fin 5), Equiv.Perm.sign a = 1 ∧ (a * σ * a⁻¹ * σ⁻¹) ^ 8 ≠ 1 := by
  decide +kernel

theorem pow_eight_eq_one_of_pow_two_pow {c : Equiv.Perm (Fin 5)} {k : ℕ} (hc : c ^ 2 ^ k = 1) :
    c ^ 8 = 1 := by
  have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf c ∣ 120 := by
    have := orderOf_dvd_card (G := Equiv.Perm (Fin 5)) (x := c)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  have hj3 : j ≤ 3 := by
    rw [hjc] at h2
    by_contra hj3
    have h16 : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans h2
    norm_num at h16
  have h8 : orderOf c ∣ 8 := by
    rw [hjc]
    exact (Nat.pow_dvd_pow 2 hj3).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp h8

variable {G : Type} [Group G] [Finite G] {S : Setting G} {H : Subgroup G}

namespace ConfHyp

theorem le_normalizer_V (hc : ConfHyp S H) :
    H ≤ normalizer ((closure (S.zConj H) : Subgroup G) : Set G) := by
  obtain ⟨g⟩ := hc.exists_gens
  rw [← g.isFrameOf.V_eq]
  intro h hh
  rw [mem_normalizer_iff]
  intro v
  have hhF : h ∈ g.F.H := by rw [g.isFrameOf.H_eq]; exact hh
  refine ⟨fun hv => g.F.conj_mem_V hhF hv, fun hv => ?_⟩
  have h1 := g.F.conj_mem_V (g.F.H.inv_mem hhF) hv
  rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h1

theorem conj_mem_zConj_of_mem_normalizer (hc : ConfHyp S H) {n : G}
    (hn : n ∈ normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) {ω : G}
    (hω : ω ∈ S.zConj H) : n * ω * n⁻¹ ∈ S.zConj H := by
  obtain ⟨g⟩ := hc.exists_gens
  have h1 : n * ω * n⁻¹ ∈ closure (S.zConj H) :=
    (mem_normalizer_iff.mp hn ω).mp (subset_closure hω)
  rw [← g.isFrameOf.V_eq] at h1
  refine g.mem_zConj_of_mem_V hc h1 ?_
  obtain ⟨k, -, rfl⟩ := hω
  exact isConj_iff.mpr ⟨n * k, by group⟩

theorem orbit_normalizer_V (hc : ConfHyp S H) :
    {x | ∃ n ∈ normalizer ((closure (S.zConj H) : Subgroup G) : Set G), n * S.z * n⁻¹ = x} =
      S.zConj H := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact hc.conj_mem_zConj_of_mem_normalizer hn (Asc77.self_mem_conjIn _ _)
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hc.le_normalizer_V hk, rfl⟩

theorem card_normalizer_V (hc : ConfHyp S H) :
    Nat.card (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) =
      5 * Nat.card ↥(normalizer ((closure (S.zConj H) : Subgroup G) : Set G) ⊓ S.M) := by
  have h1 := Setting.card_eq_relIndex_mul
    (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) S.M
  rw [Setting.relIndex_centralizer_eq_ncard, hc.orbit_normalizer_V, hc.ncard_zConj] at h1
  exact h1

@[expose] def normPerm (hc : ConfHyp S H) :
    normalizer ((closure (S.zConj H) : Subgroup G) : Set G) →* Equiv.Perm (S.zConj H) where
  toFun n :=
    { toFun := fun ω => ⟨(n : G) * ω * (n : G)⁻¹, hc.conj_mem_zConj_of_mem_normalizer n.2 ω.2⟩
      invFun := fun ω => ⟨(n : G)⁻¹ * ω * n, by
        have h := hc.conj_mem_zConj_of_mem_normalizer (inv_mem n.2) ω.2
        rwa [inv_inv] at h⟩
      left_inv := fun ω => Subtype.ext (by
        change (n : G)⁻¹ * ((n : G) * ω * (n : G)⁻¹) * n = ω
        group)
      right_inv := fun ω => Subtype.ext (by
        change (n : G) * ((n : G)⁻¹ * ω * n) * (n : G)⁻¹ = ω
        group) }
  map_one' := Equiv.ext fun ω => Subtype.ext (by
    change ((1 : normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) : G) * ω *
      ((1 : normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) : G)⁻¹ = ω
    simp)
  map_mul' a b := Equiv.ext fun ω => Subtype.ext (by
    change ((a * b : normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) : G) * ω *
      ((a * b : normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) : G)⁻¹ =
        (a : G) * ((b : G) * ω * (b : G)⁻¹) * (a : G)⁻¹
    rw [coe_mul]
    group)

theorem coe_normPerm_apply (hc : ConfHyp S H)
    (n : normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) (ω : S.zConj H) :
    ((hc.normPerm n ω : S.zConj H) : G) = (n : G) * ω * (n : G)⁻¹ := rfl

theorem pCoreOf_normalizer_V (hc : ConfHyp S H) :
    pCoreOf 2 (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) =
      closure (S.zConj H) := by
  set N := normalizer ((closure (S.zConj H) : Subgroup G) : Set G) with hNdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, hp, hpz⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
  obtain ⟨L, -⟩ := hc.exists_label hp hpz
  have hHN := hc.le_normalizer_V
  have hVN : closure (S.zConj H) ≤ N := (hc.V_le).trans hHN
  let π : N →* Equiv.Perm (Fin 5) :=
    (L.ι.symm.permCongrHom : Equiv.Perm (S.zConj H) ≃* Equiv.Perm (Fin 5)).toMonoidHom.comp
      hc.normPerm
  have hπH : ∀ h : H, π ⟨h, hHN h.2⟩ = L.σ h := by
    intro h
    ext i
    rfl
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hπx : π x = 1 := by
      by_contra hne
      obtain ⟨a, ha, hpow⟩ := exists_comm_pow_ne (π x) hne
      obtain ⟨h, hh⟩ := L.exists_σ_eq hc.isAFive ha
      set c : N := ⟨h, hHN h.2⟩ * x * ⟨h, hHN h.2⟩⁻¹ * x⁻¹ with hc'
      have hcP : c ∈ CFSG.pCore 2 N :=
        mul_mem (CFSG.pCore_normal.conj_mem x hx _) (inv_mem hx)
      have hcπ : π c = a * π x * a⁻¹ * (π x)⁻¹ := by
        rw [hc', map_mul, map_mul, map_mul, map_inv, map_inv, hπH, hh]
      have hP : IsPGroup 2 (CFSG.pCore 2 N) := CFSG.pCore_isPGroup
      obtain ⟨k, hk⟩ := hP ⟨c, hcP⟩
      have hck : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
      apply hpow
      rw [← hcπ]
      exact pow_eight_eq_one_of_pow_two_pow (by rw [← map_pow, hck, map_one])
    refine hc.mem_V_of_commute (fun ω hω => ?_) hp hpz
    obtain ⟨i, rfl⟩ := L.exists_zz_eq hω
    have e1 : π x i = i := by rw [hπx, Equiv.Perm.one_apply]
    have e2 : ((hc.normPerm x (L.ι i) : S.zConj H) : G) = L.zz i := by
      have : hc.normPerm x (L.ι i) = L.ι i := by
        have h3 : L.ι.symm (hc.normPerm x (L.ι i)) = i := e1
        exact L.ι.symm.injective (h3.trans (L.ι.symm_apply_apply i).symm)
      rw [this]
      rfl
    rw [coe_normPerm_apply] at e2
    have e3 : (x : G) * L.zz i * (x : G)⁻¹ = L.zz i := e2
    calc (x : G) * L.zz i = (x : G) * L.zz i * (x : G)⁻¹ * x := by group
      _ = L.zz i * x := by rw [e3]
  · intro v hv
    refine ⟨⟨v, hVN hv⟩, ?_, rfl⟩
    have hN : ((closure (S.zConj H)).subgroupOf N).Normal := by
      refine ⟨fun n hn k => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      have h1 := (mem_normalizer_iff.mp k.2 n).mp hn
      simpa using h1
    have hcard : Nat.card ((closure (S.zConj H)).subgroupOf N) = 2 ^ 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv, hc.card_V]
      norm_num
    have hP : IsPGroup 2 ((closure (S.zConj H)).subgroupOf N) := IsPGroup.of_card hcard
    exact (le_sSup (show _ ∈ {K : Subgroup N | K.Normal ∧ IsPGroup 2 K} from ⟨hN, hP⟩) :
      _ ≤ CFSG.pCore 2 N) (mem_subgroupOf.mpr hv)

theorem normalizer_centerOf_pCoreOf_normalizer_V (hc : ConfHyp S H) :
    normalizer (centerOf (pCoreOf 2 (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)))
      : Set G) = normalizer ((closure (S.zConj H) : Subgroup G) : Set G) := by
  rw [hc.pCoreOf_normalizer_V, hc.centerOf_V]

theorem pCoreOf_sup_eq_bot_of_le (hc : ConfHyp S H) {K : Subgroup G} (hHK : H ≤ K) :
    pCoreOf 2 (S.M ⊔ K) = ⊥ := by
  obtain ⟨g⟩ := hc.exists_gens
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 (S.M ⊔ K) with hOdef
  have hOp : IsPGroup 2 O := isPGroup_pCoreOf 2 _
  have hOn : ∀ k ∈ S.M ⊔ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho => conj_mem_pCoreOf 2 hk ho
  have hOM : O ⊓ S.M ≤ S.QG := S.le_QG_of_normalizes' inf_le_right
    (fun c hcM o ho => ⟨hOn c (mem_sup_left hcM) o ho.1,
      S.M.mul_mem (S.M.mul_mem hcM ho.2) (S.M.inv_mem hcM)⟩) (hOp.to_le inf_le_left)
  have hzO : S.z ∉ O := by
    intro hz
    have htO := hOn g.s (mem_sup_right (hHK (g.mem_H g.rep_s))) S.z hz
    rw [g.isFrameOf.conj_z_of_rep_sD g.rep_s, ← g.t_eq] at htO
    exact hc.not_mem_QG g.t_mem_zConj g.t_ne_z (hOM ⟨htO, g.t_mem_M hc⟩)
  by_contra hne
  obtain ⟨o, hoO, ho1, hoc⟩ := exists_ne_one_commute_of_normalizes (P := S.QG)
    (S.extraspecial.1.map _) hOp hne fun q hq o ho => hOn q (mem_sup_left (S.QG_le_M hq)) o ho
  have hoM : o ∈ S.M := S.mem_M_iff.mpr (hoc S.z S.z_mem_QG).symm
  rcases S.eq_one_or_z_of_commute (hOM ⟨hoO, hoM⟩) (fun y hy => (hoc y hy).symm) with h | h
  · exact ho1 h
  · exact hzO (h ▸ hoO)

omit [Finite G] in
theorem z_mem_centerOf_inf_of_le (hc : ConfHyp S H) {K : Subgroup G} (hHK : H ≤ K) :
    S.z ∈ centerOf (S.M ⊓ K) :=
  ⟨⟨S.z_mem_M, hHK hc.z_mem⟩, mem_centralizer_iff.mpr fun _ hh => S.z_comm hh.1⟩

theorem f431Side (hc : ConfHyp S H) :
    pCoreOf 2 (S.M ⊔ normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) = ⊥ ∧
      S.z ∈ centerOf (S.M ⊓ normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) ∧
      normalizer (centerOf (pCoreOf 2 (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)))
        : Set G) = normalizer ((closure (S.zConj H) : Subgroup G) : Set G) :=
  ⟨hc.pCoreOf_sup_eq_bot_of_le hc.le_normalizer_V, hc.z_mem_centerOf_inf_of_le hc.le_normalizer_V,
    hc.normalizer_centerOf_pCoreOf_normalizer_V⟩

end ConfHyp

end AS62

end CFSG.LargeExtraspecial
