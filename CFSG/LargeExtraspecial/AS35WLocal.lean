module

public import CFSG.LargeExtraspecial.AS35WDefs
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LargeExtraspecial.AS35DQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem card_M_dvd_of_width_two (hw : S.width = 2) : Nat.card S.M ∣ 2 ^ 8 * 3 ^ 2 * 5 := by
  have hM : Nat.card S.M = Nat.card S.Q * Nat.card S.Mbar := by
    rw [← Nat.card_congr S.quotientEquivMbar.toEquiv, mul_comm]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup S.Q)
  have hQ : Nat.card S.Q = 2 ^ 5 := by rw [S.card_Q_eq, hw]
  have hdim : Module.finrank (ZMod 2) S.Qt = 2 * (1 + 1) := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have h2 : (Nat.card (ZMod 2) : ℤ) = 2 := by rw [Nat.card_zmod]; rfl
  have hO : Nat.card S.O ∣ 360 := by
    by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType S.q
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type S.q_nondegenerate hdim
        (ε := 1) (Or.inl ⟨rfl, hp⟩)
      rw [h2] at h
      have : Nat.card S.O = 72 := by
        have h' : (Nat.card S.O : ℤ) = 72 := by rw [h]; decide
        exact_mod_cast h'
      rw [this]; norm_num
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type S.q_nondegenerate hdim
        (ε := -1) (Or.inr ⟨rfl, hp⟩)
      rw [h2] at h
      have : Nat.card S.O = 120 := by
        have h' : (Nat.card S.O : ℤ) = 120 := by rw [h]; decide
        exact_mod_cast h'
      rw [this]; norm_num
  have hMbar : Nat.card S.Mbar ∣ 360 := (Subgroup.card_subgroup_dvd_card S.Mbar).trans hO
  rw [hM, hQ]
  have : 2 ^ 8 * 3 ^ 2 * 5 = 2 ^ 5 * 360 := by norm_num
  rw [this]
  exact Nat.mul_dvd_mul_left _ hMbar

omit [Finite G] in
theorem le_QG_of_normalizes' {P : Subgroup G} (hPM : P ≤ S.M)
    (hn : ∀ c ∈ S.M, ∀ x ∈ P, c * x * c⁻¹ ∈ P) (h2 : IsPGroup 2 P) : P ≤ S.QG := by
  have hnor : (P.subgroupOf S.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hPM]
    exact fun x k hx hk => hn k hk x hx
  have hP := S.le_of_normal _ hnor (h2.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm)
  exact fun x hx => ⟨⟨x, hPM hx⟩, hP hx, rfl⟩

variable {L : Subgroup G} [hLn : L.Normal] (hzL : S.z ∈ L)
include hzL

omit [Finite G] in
theorem map_oTwoCent_le_QG : (oTwoCent (⟨S.z, hzL⟩ : L)).map L.subtype ≤ S.QG := by
  refine S.le_QG_of_normalizes' ?_ ?_ ((isPGroup_oTwoCent _).map _)
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := mem_centralizer_singleton_iff.mp (oTwoCent_le_centralizer _ hy)
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h1
  · rintro c hc _ ⟨y, hy, rfl⟩
    have hfix : MulAut.conjNormal c (⟨S.z, hzL⟩ : L) = ⟨S.z, hzL⟩ := Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change c * S.z * c⁻¹ = S.z
      rw [S.mem_M_iff.mp hc, mul_inv_cancel_right])
    have h2 := AS35W.map_oTwoCent_le (MulAut.conjNormal c) (⟨S.z, hzL⟩ : L) ⟨y, hy, rfl⟩
    rw [hfix] at h2
    exact ⟨_, h2, by rw [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conjNormal_apply]⟩

omit [Finite G] hLn in
theorem mem_oTwoCent_of_mem_QG {x : L} (hx : (x : G) ∈ S.QG) :
    x ∈ oTwoCent (⟨S.z, hzL⟩ : L) := by
  refine le_oTwoCent (P := S.QG.comap L.subtype) ?_ ?_ ?_ hx
  · intro y hy
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (S.mem_M_iff.mp (S.QG_le_M hy)).symm.symm
  · intro c hc y hy
    have hcM : (c : G) ∈ S.M := by
      rw [S.mem_M_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
    show (c : G) * y * (c : G)⁻¹ ∈ S.QG
    obtain ⟨y', hy', hyy'⟩ := hy
    have hyy : (y : G) = y' := hyy'.symm
    rw [hyy]
    exact ⟨⟨c, hcM⟩ * y' * ⟨c, hcM⟩⁻¹, S.normal.conj_mem _ hy' _, rfl⟩
  · exact S.isPGroup_QG.comap_of_injective L.subtype L.subtype_injective

omit [Finite G] in
theorem eq_one_of_odd {y : L} (hyz : y ∈ centralizer ({(⟨S.z, hzL⟩ : L)} : Set L))
    (hyR : ∀ r ∈ oTwoCent (⟨S.z, hzL⟩ : L), y * r = r * y) (hodd : Odd (orderOf y)) :
    y = 1 := by
  have hyM : (y : G) ∈ S.M := by
    rw [S.mem_M_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hyz)
  have hcomm : ∀ q ∈ S.QG, (y : G) * q = q * y := by
    intro q hq
    set d : G := (y : G) * q * (y : G)⁻¹ * q⁻¹ with hd
    have hdQ : d ∈ S.QG := by
      obtain ⟨q', hq', rfl⟩ := hq
      refine ⟨⟨y, hyM⟩ * q' * ⟨y, hyM⟩⁻¹ * q'⁻¹, S.Q.mul_mem (S.normal.conj_mem _ hq' _)
        (S.Q.inv_mem hq'), rfl⟩
    have hdL : d ∈ L := by
      have h1 : q * (y : G)⁻¹ * q⁻¹ ∈ L := hLn.conj_mem _ (L.inv_mem y.2) q
      have : d = (y : G) * (q * (y : G)⁻¹ * q⁻¹) := by rw [hd]; group
      rw [this]
      exact L.mul_mem y.2 h1
    have hdR : (⟨d, hdL⟩ : L) ∈ oTwoCent (⟨S.z, hzL⟩ : L) := S.mem_oTwoCent_of_mem_QG hzL hdQ
    have hyd : (y : G) * d = d * y := congrArg Subtype.val (hyR _ hdR)
    have hyq : (y : G) * q * (y : G)⁻¹ = d * q := by rw [hd]; group
    have hpow : ∀ k : ℕ, (y : G) ^ k * q * ((y : G) ^ k)⁻¹ = d ^ k * q := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hydk : (y : G) * d ^ k = d ^ k * y := (Commute.pow_right hyd k).eq
        calc (y : G) ^ (k + 1) * q * ((y : G) ^ (k + 1))⁻¹
            = (y : G) * ((y : G) ^ k * q * ((y : G) ^ k)⁻¹) * (y : G)⁻¹ := by group
          _ = (y : G) * (d ^ k * q) * (y : G)⁻¹ := by rw [ih]
          _ = ((y : G) * d ^ k) * (q * (y : G)⁻¹) := by group
          _ = (d ^ k * y) * (q * (y : G)⁻¹) := by rw [hydk]
          _ = d ^ k * ((y : G) * q * (y : G)⁻¹) := by group
          _ = d ^ k * (d * q) := by rw [hyq]
          _ = d ^ (k + 1) * q := by group
    have hdn : d ^ orderOf y = 1 := by
      have h1 := hpow (orderOf y)
      have hy1 : (y : G) ^ orderOf y = 1 := by
        rw [← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [hy1, one_mul, inv_one, mul_one] at h1
      exact (mul_eq_right.mp h1.symm)
    have hd1 : d = 1 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup_QG) ⟨d, hdQ⟩
      rw [Subgroup.orderOf_mk] at hb
      have hdvd : orderOf d ∣ orderOf y := orderOf_dvd_of_pow_eq_one hdn
      have hcop : Nat.Coprime (2 ^ b) (orderOf y) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
      rw [hb] at hdvd
      have h1 : 2 ^ b = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
      rw [← orderOf_eq_one_iff, hb, h1]
    have : (y : G) * q * (y : G)⁻¹ * q⁻¹ = 1 := hd ▸ hd1
    calc (y : G) * q = (y : G) * q * (y : G)⁻¹ * q⁻¹ * (q * y) := by group
      _ = q * y := by rw [this, one_mul]
  have hyC : (y : G) ∈ centralizer (S.QG : Set G) := by
    rw [mem_centralizer_iff]
    exact fun q hq => (hcomm q hq).symm
  rw [S.centralizer_QG_eq] at hyC
  have hzz : S.z ^ 2 = 1 := by rw [← S.orderOf_z, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyC
  have hcases : (y : G) = 1 ∨ (y : G) = S.z := by
    rw [← hk, ← zpow_mod_orderOf, S.orderOf_z]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  rcases hcases with h | h
  · exact Subtype.ext h
  · exfalso
    have : orderOf y = 2 := by rw [← Subgroup.orderOf_coe, h, S.orderOf_z]
    rw [this] at hodd
    exact absurd hodd (by decide)

omit [Finite G] in
theorem selfCentralizing_of_normal [Finite L] {c : L}
    (hc : c ∈ centralizer ({(⟨S.z, hzL⟩ : L)} : Set L))
    (hcr : ∀ r ∈ oTwoCent (⟨S.z, hzL⟩ : L), c * r = r * c) :
    c ∈ oTwoCent (⟨S.z, hzL⟩ : L) := by
  set R := oTwoCent (⟨S.z, hzL⟩ : L)
  set Cc : Subgroup L := centralizer (R : Set L) ⊓ centralizer ({(⟨S.z, hzL⟩ : L)} : Set L)
  have hmem : ∀ x : L, x ∈ Cc ↔ (∀ r ∈ R, x * r = r * x) ∧
      x ∈ centralizer ({(⟨S.z, hzL⟩ : L)} : Set L) := by
    intro x
    rw [Subgroup.mem_inf, mem_centralizer_iff]
    exact ⟨fun h => ⟨fun r hr => (h.1 r hr).symm, h.2⟩, fun h => ⟨fun r hr => (h.1 r hr).symm,
      h.2⟩⟩
  refine le_oTwoCent (P := Cc) (fun x hx => ((hmem x).1 hx).2) ?_ ?_ ((hmem c).2 ⟨hcr, hc⟩)
  · intro d hd x hx
    obtain ⟨hxR, hxz⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨fun r hr => ?_, ?_⟩
    · have hr' : d⁻¹ * r * d⁻¹⁻¹ ∈ R := conj_mem_oTwoCent (Subgroup.inv_mem _ hd) hr
      have := hxR _ hr'
      calc d * x * d⁻¹ * r = d * (x * (d⁻¹ * r * d⁻¹⁻¹)) * d⁻¹ := by group
        _ = d * ((d⁻¹ * r * d⁻¹⁻¹) * x) * d⁻¹ := by rw [this]
        _ = r * (d * x * d⁻¹) := by group
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hd hxz) (Subgroup.inv_mem _ hd)
  · intro ⟨x, hx⟩
    obtain ⟨hxR, hxz⟩ := (hmem x).1 hx
    have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd hpos
    refine ⟨a, Subtype.ext ?_⟩
    have hdvd : 2 ^ a ∣ orderOf x := ⟨m, hxm⟩
    have hord : orderOf (x ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hxm,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    have hyz : x ^ 2 ^ a ∈ centralizer ({(⟨S.z, hzL⟩ : L)} : Set L) := Subgroup.pow_mem _ hxz _
    have hyR : ∀ r ∈ R, x ^ 2 ^ a * r = r * x ^ 2 ^ a := fun r hr =>
      (Commute.pow_left (hxR r hr) _).eq
    have := S.eq_one_of_odd hzL hyz hyR (hord ▸ hm)
    simpa using this

omit [Finite G] hzL in
theorem conjNormal_injective (hC : centralizer (L : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal : G →* MulAut L) := by
  intro g g' hgg
  have hcen : g'⁻¹ * g ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : G)) hgg
    simp only [MulAut.conjNormal_apply] at this
    calc l * (g'⁻¹ * g) = g'⁻¹ * (g' * l * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * l * g⁻¹) * g := by rw [this]
      _ = g'⁻¹ * g * l := by group
  rw [hC, Subgroup.mem_bot] at hcen
  calc g = g' * (g'⁻¹ * g) := by group
    _ = g' := by rw [hcen, mul_one]

theorem w2Data_of_normal (hw : S.width = 2)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t) (hC : centralizer (L : Set G) = ⊥) :
    AS35W.W2Data L ⟨S.z, hzL⟩ where
  orderOf_eq := by rw [Subgroup.orderOf_mk]; exact S.orderOf_z
  sylow_le := by
    obtain ⟨PG, -, hPM⟩ := S.exists_sylow_le_M
    obtain ⟨PL⟩ : Nonempty (Sylow 2 L) := inferInstance
    have hPL2 : IsPGroup 2 ((PL : Subgroup L).map L.subtype) := PL.isPGroup'.map _
    obtain ⟨P', hP'⟩ := hPL2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PG P'
    refine ⟨(MulAut.conjNormal g⁻¹ : MulAut L) • PL, fun x hx => ?_⟩
    rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have hx' : g * (x : G) * g⁻¹ ∈ ((g • PG : Sylow 2 G) : Subgroup G) := by
      rw [hg]
      refine hP' ⟨_, hx, ?_⟩
      rw [← map_inv, MulAut.smul_def, Subgroup.coe_subtype, MulAut.conjNormal_apply]
      group
    rw [Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    have hxP : (x : G) ∈ (PG : Subgroup G) := by
      convert hx' using 1
      simp only [MulAut.inv_def, MulAut.smul_def, MulAut.conj_symm_apply]
      group
    have hxz := S.mem_M_iff.mp (hPM hxP)
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext hxz
  card_dvd := by
    set K := centralizer ({(⟨S.z, hzL⟩ : L)} : Set L)
    have hKM : K.map L.subtype ≤ S.M := by
      rintro _ ⟨y, hy, rfl⟩
      rw [S.mem_M_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
    rw [← Subgroup.card_map_of_injective L.subtype_injective]
    exact (Subgroup.card_dvd_of_le hKM).trans (S.card_M_dvd_of_width_two hw)
  weaklyClosed := by
    intro x hx hcx
    have hxQ : (x : G) ∈ S.QG := S.map_oTwoCent_le_QG hzL ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hcx
    have hc' : (c : G) * S.z * (c : G)⁻¹ = x := congrArg Subtype.val hc
    have := hW c (hc' ▸ hxQ)
    exact Subtype.ext (hc'.symm.trans this)
  mem_oTwoCent := by
    intro t ht ht2
    have htQ : (t : G) ∈ S.QG := S.map_oTwoCent_le_QG hzL ⟨t, ht, rfl⟩
    have hzt : S.z ∈ oTwoCent (t : G) := hO _ htQ (by rw [Subgroup.orderOf_coe]; exact ht2)
    refine le_oTwoCent (P := (oTwoCent (t : G)).comap L.subtype) ?_ ?_ ?_ hzt
    · intro y hy
      have := mem_centralizer_singleton_iff.mp (oTwoCent_le_centralizer _ hy)
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext this
    · intro c hc y hy
      have hc' : (c : G) ∈ centralizer ({(t : G)} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
      exact conj_mem_oTwoCent hc' hy
    · exact (isPGroup_oTwoCent _).comap_of_injective L.subtype L.subtype_injective
  selfCentralizing := fun c hc hcr => S.selfCentralizing_of_normal hzL hc hcr
  sq_eq := by
    intro r hr
    have hrQ : (r : G) ∈ S.QG := S.map_oTwoCent_le_QG hzL ⟨r, hr, rfl⟩
    rcases S.sq_eq_one_or_z hrQ with h | h
    · exact Or.inl (Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one]))
    · exact Or.inr (Subtype.ext (by rw [Subgroup.coe_pow, h]))
  aut := by
    refine ⟨S.QG.map (MulAut.conjNormal : G →* MulAut L), ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (conjNormal_injective hC), S.card_QG_eq_card_Q,
        S.card_Q_eq, hw]
      norm_num
    · rintro _ ⟨q, hq, rfl⟩
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      change q * S.z * q⁻¹ = S.z
      rw [S.mem_M_iff.mp (S.QG_le_M hq), mul_inv_cancel_right]
    · rintro x ⟨q, hq, hqx⟩
      have hqx' : q = (x : G) := by
        apply conjNormal_injective hC
        rw [hqx]
        ext l
        simp [MulAut.conjNormal_apply, MulAut.conj_apply]
      exact S.mem_oTwoCent_of_mem_QG hzL (hqx' ▸ hq)

end Setting

end CFSG.LargeExtraspecial
