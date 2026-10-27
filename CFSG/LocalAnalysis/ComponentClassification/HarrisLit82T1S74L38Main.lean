module

public import CFSG.GH74.Orders.LieType
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreBalance

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74.L38

open CFSG Subgroup CFSG.OddStandard.Solomon75 CFSG.OddStandard.Solomon75.CoreAux

theorem card_of_isCoverOf {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hY : IsCoverOf .POmegaOdd 3 p f 2 Y) :
    Nat.card Y = (p ^ f) ^ 9 * (((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 4 - 1) * ((p ^ f) ^ 6 - 1))) := by
  obtain ⟨-, hZ, hm⟩ := hY
  have hsc := CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hm
  have hc := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hsc).2.2.2.1 rfl
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hev : 2 ∣ (p ^ f) ^ (3 * 3) * ∏ i ∈ Finset.Icc 1 3, ((p ^ f) ^ (2 * i) - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    rw [show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.prod_insert (by decide)]
    refine Dvd.dvd.mul_right ?_ _
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Y), hc, hZ, Open.ordBC,
    ClassicalInvolution.gcd_two_sub_one_of_odd hodd, Nat.div_mul_cancel hev,
    show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]

theorem mem_of_two_pow_of_odd_index {Cb : Type*} [Group Cb] {Lb : Subgroup Cb} [Lb.Normal]
    (hLi : ¬ 2 ∣ Lb.index) {s : Cb} {k : ℕ} (hs : orderOf s = 2 ^ k) : s ∈ Lb := by
  have h1 : orderOf (QuotientGroup.mk s : Cb ⧸ Lb) ∣ 2 ^ k :=
    hs ▸ orderOf_map_dvd (QuotientGroup.mk' Lb) s
  have h2 : orderOf (QuotientGroup.mk s : Cb ⧸ Lb) ∣ Lb.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) Lb.index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hLi)
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_le_cen {z : G} (hz : orderOf z = 2)
    (hcl : ∀ x : G, orderOf x = 2 → ∃ g : G, g * z * g⁻¹ = x) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ cen z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 2 G))
  have h2G : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
  have hS₀ : Nontrivial ↥(S₀ : Subgroup G) := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [S₀.card_eq_multiplicity]
    have h1 : 1 ≤ (Nat.card G).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2G
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (Nat.card G).factorization 2 := Nat.pow_le_pow_right (by norm_num) h1
  have hZ := S₀.isPGroup'.center_nontrivial
  obtain ⟨k, hk⟩ := (S₀.isPGroup'.to_subgroup (center ↥(S₀ : Subgroup G))).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥(S₀ : Subgroup G))) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  set z' : G := ((c : ↥(S₀ : Subgroup G)) : G) with hz'
  have hz'2 : orderOf z' = 2 := by
    rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have hz'c : ∀ s ∈ (S₀ : Subgroup G), s * z' = z' * s := by
    intro s hs
    have h := mem_center_iff.mp c.2 ⟨s, hs⟩
    exact congrArg Subtype.val h
  obtain ⟨g, hg⟩ := hcl z' hz'2
  refine ⟨g⁻¹ • S₀, fun x hx => ?_⟩
  rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  rw [mem_centralizer_singleton_iff, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  have h := hz'c s hs
  rw [← hg] at h
  calc g⁻¹ * s * g * z = g⁻¹ * (s * (g * z * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * z * g⁻¹ * s) * g := by rw [h]
    _ = z * (g⁻¹ * s * g) := by group

theorem exists_sylow_mulEquiv {z : G} {Lb : Subgroup (CentQuot z)} (hLn : Lb.Normal)
    (hLi : ¬ 2 ∣ Lb.index) {X : Type} [Group X] [Finite X] (e : ↥Lb ≃* X) (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≤ cen z) :
    ∃ P : Sylow 2 X, Nonempty (↥(S : Subgroup G) ≃* ↥(P : Subgroup X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥(cen z) →* CentQuot z := QuotientGroup.mk' (pPrimeCore 2 ↥(cen z)) with hπ
  set S' : Subgroup ↥(cen z) := (S : Subgroup G).subgroupOf (cen z) with hS'
  have hS'p : IsPGroup 2 S' := S.isPGroup'.comap_of_injective _ (cen z).subtype_injective
  set ψ : ↥S' →* CentQuot z := π.comp S'.subtype with hψ
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS'p) s
    have h1 := eq_one_of_mem_pPrimeCore_of_two_pow hs ⟨k, by
      change orderOf (s : ↥(cen z)) = 2 ^ k
      rw [Subgroup.orderOf_coe, hk]⟩
    exact mem_bot.mpr (Subtype.ext h1)
  have := hLn
  have hrange : ψ.range ≤ Lb := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS'p) s
    exact mem_of_two_pow_of_odd_index hLi (k := k) (by rw [orderOf_injective ψ hψi s, hk])
  set Q : Subgroup X := (ψ.range.subgroupOf Lb).map e.toMonoidHom with hQ
  let eQ : ↥(S : Subgroup G) ≃* ↥Q := (subgroupOfEquivOfLe hS).symm.trans
    ((MonoidHom.ofInjective hψi).trans ((subgroupOfEquivOfLe hrange).symm.trans
      ((ψ.range.subgroupOf Lb).equivMapOfInjective e.toMonoidHom e.injective)))
  have hQp : IsPGroup 2 Q := S.isPGroup'.of_equiv eQ
  obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
  have hXG : Nat.card X ∣ Nat.card G := by
    rw [← Nat.card_congr e.toEquiv]
    exact (card_subgroup_dvd_card Lb).trans ((card_quotient_dvd_card _).trans
      (card_subgroup_dvd_card (cen z)))
  have hfac : (Nat.card X).factorization 2 ≤ (Nat.card G).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hXG 2
  have hcard : Nat.card (P : Subgroup X) ≤ Nat.card Q := by
    rw [P.card_eq_multiplicity, ← Nat.card_congr eQ.toEquiv, S.card_eq_multiplicity]
    exact Nat.pow_le_pow_right (by norm_num) hfac
  have hQeq : Q = P := eq_of_le_of_card_ge hQP hcard
  exact ⟨P, ⟨eQ.trans (MulEquiv.subgroupCongr hQeq)⟩⟩

theorem not_isSolvable_cen {z : G} {p f : ℕ} {Lb : Subgroup (CentQuot z)}
    (hL : IsCoverOf .POmegaOdd 3 p f 2 ↥Lb) : ¬ Group.IsSolvable ↥(cen z) := by
  intro hsolv
  have : Group.IsSolvable (CentQuot z) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(cen z)))
  have : Group.IsSolvable ↥Lb := Group.isSolvable_of_isSolvable_injective Lb.subtype_injective
  have hnt : Nontrivial ↥Lb := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    have h1 := hL.2.1
    have h2 : Nat.card (center ↥Lb) ≤ Nat.card ↥Lb := card_le_card_group _
    omega
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Lb).ne hL.1.1.commutator_eq_top

end CFSG.ComponentClassification.HarrisLit.T1.S74.L38
