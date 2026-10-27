module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.GroupTheory.ABGLocalTools.Basic

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

theorem isSylowOf_map {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ} [Fact p.Prime]
    (φ : G →* G') {P K : Subgroup G} (h : IsSylowOf p P K) :
    IsSylowOf p (P.map φ) (K.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  let ψ : K →* K.map φ :=
    (φ.comp K.subtype).codRestrict (K.map φ) (fun x => ⟨x, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨Q.mapSurjective hψ, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSylowOf_map_range {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ}
    [Fact p.Prime] (φ : G →* G') (Q : Sylow p G) : IsSylowOf p ((Q : Subgroup G).map φ) φ.range :=
  ⟨Q.mapSurjective φ.rangeRestrict_surjective, by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]⟩

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

structure Standing (t : X) (L : Subgroup X) (p f : ℕ) : Prop where
  config : Config t L p f
  dihedral : DihedralStructure t L
  sixteen : 16 ∣ p ^ f - 1
  sect : ¬ SectionalRankLeFour X

namespace Standing

theorem centralizer_le_normalizer (h : Standing t L p f) :
    centralizer ({t} : Set X) ≤ normalizer (L : Set X) := by
  rw [h.dihedral.normalizer_eq]
  exact le_sup_right

@[expose] def rho (h : Standing t L p f) : ↥(centralizer ({t} : Set X)) →* MulAut (Bar L) :=
  (barAction L).comp (Subgroup.inclusion h.centralizer_le_normalizer)

theorem rho_apply (h : Standing t L p f) (x : ↥(centralizer ({t} : Set X))) :
    h.rho x = barAction L ⟨x, h.centralizer_le_normalizer x.2⟩ :=
  rfl

theorem mem_ker_rho (h : Standing t L p f) (x : ↥(centralizer ({t} : Set X))) :
    x ∈ h.rho.ker ↔ (x : X) ∈ coreActionKernel L := by
  rw [MonoidHom.mem_ker, rho_apply, ← MonoidHom.mem_ker, mem_ker_barAction]

theorem rho_of_mem (h : Standing t L p f) (l : L) :
    h.rho ⟨l, h.config.le_centralizer l.2⟩ = MulAut.conj (QuotientGroup.mk l : Bar L) := by
  rw [rho_apply]
  exact barAction_of_mem L l _

theorem innAut_le_range (h : Standing t L p f) : innAut (Bar L) ≤ h.rho.range := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨l, h.config.le_centralizer l.2⟩, h.rho_of_mem l⟩

theorem mem_zpowers_of_mem_ker [Finite X] (h : Standing t L p f) {s : X}
    (hsH : s ∈ centralizer ({t} : Set X)) (hsC : s ∈ coreActionKernel L) {k : ℕ}
    (hk : s ^ 2 ^ k = 1) : s ∈ zpowers t := by
  have hmem : s ∈ centralizer ({t} : Set X) ⊓ coreActionKernel L := ⟨hsH, hsC⟩
  rw [h.dihedral.kernel_eq] at hmem
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  have hOn : (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype
      ≤ normalizer (zpowers t : Set X) := by
    rintro _ ⟨o, -, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute (o : X) t := mem_centralizer_singleton_iff.mp o.2
    exact (hc.zpow_right j).eq.symm
  have hmem' : s ∈ ((pPrimeCore 2 ↥(centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype : Set X) * (zpowers t : Set X) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hOn]
    exact hmem
  obtain ⟨_, ⟨o, ho, rfl⟩, y, hy, rfl⟩ := hmem'
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
  have hc : Commute (o : X) (t ^ j) :=
    (Commute.zpow_right (mem_centralizer_singleton_iff.mp o.2) j)
  have hpow : (o : X) ^ 2 ^ (k + 1) = 1 := by
    have h1 : ((o : X) * t ^ j) ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ, pow_mul, show ((o : X) * t ^ j) ^ 2 ^ k = 1 from hk, one_pow]
    rw [hc.mul_pow] at h1
    have h2 : (t ^ j) ^ 2 ^ (k + 1) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        show t ^ 2 ^ (k + 1) = 1 by rw [pow_succ, pow_mul', ht2, one_pow], one_zpow]
    rwa [h2, mul_one] at h1
  have hord : orderOf o = 1 := by
    have hdvd1 : orderOf o ∣ 2 ^ (k + 1) := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      rw [Subgroup.coe_pow, hpow, Subgroup.coe_one]
    have hdvd2 : orderOf (⟨o, ho⟩ : pPrimeCore 2 ↥(centralizer ({t} : Set X))) ∣
        Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set X))) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd2
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set X)))) :=
      pPrimeCore_coprime_card
    have hcop' : Nat.Coprime (2 ^ (k + 1)) (Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set X)))) :=
      Nat.Coprime.pow_left _ hcop
    exact Nat.eq_one_of_dvd_coprimes hcop' hdvd1 hdvd2
  rw [orderOf_eq_one_iff] at hord
  subst hord
  simp only [map_one, one_mul]
  exact zpow_mem (mem_zpowers t) j


theorem mem_zpowers_of_rho_eq_one [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) {s : X} (hs : s ∈ S)
    (h1 : h.rho ⟨s, hS.le hs⟩ = 1) : s ∈ zpowers t := by
  have hC := (h.mem_ker_rho ⟨s, hS.le hs⟩).mp h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS.isPGroup) ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := by
    have := pow_orderOf_eq_one (⟨s, hs⟩ : S)
    rw [hk] at this
    exact congrArg Subtype.val this
  exact h.mem_zpowers_of_mem_ker (hS.le hs) hC hk'

theorem eq_one_of_mem_zpowers_of_mem [Finite X] (h : Standing t L p f) {x : X}
    (hxt : x ∈ zpowers t) (hxL : x ∈ L) : x = 1 := by
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hxt
  rcases Int.even_or_odd' j with ⟨m, rfl | rfl⟩
  · rw [zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow]
  · exfalso
    rw [zpow_add, zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow, one_mul,
      zpow_one] at hxL
    exact h.config.not_mem hxL

theorem commute_of_rho_commute [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) {a b : X} (ha : a ∈ S) (hb : b ∈ S)
    (haL : a ∈ L)
    (hab : h.rho ⟨a, hS.le ha⟩ * h.rho ⟨b, hS.le hb⟩ = h.rho ⟨b, hS.le hb⟩ * h.rho ⟨a, hS.le ha⟩) :
    a * b = b * a := by
  have hcS : a⁻¹ * b⁻¹ * a * b ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem (S.inv_mem ha) (S.inv_mem hb)) ha) hb
  have hcL : a⁻¹ * b⁻¹ * a * b ∈ L := by
    have hbN := h.centralizer_le_normalizer (hS.le hb)
    have h1 : b⁻¹ * a * b ∈ L := by
      have := (mem_normalizer_iff.mp (inv_mem hbN) a).mp haL
      rwa [inv_inv] at this
    have : a⁻¹ * b⁻¹ * a * b = a⁻¹ * (b⁻¹ * a * b) := by group
    rw [this]
    exact L.mul_mem (L.inv_mem haL) h1
  have h1 : h.rho ⟨a⁻¹ * b⁻¹ * a * b, hS.le hcS⟩ = 1 := by
    have : (⟨a⁻¹ * b⁻¹ * a * b, hS.le hcS⟩ : ↥(centralizer ({t} : Set X))) =
        (⟨a, hS.le ha⟩)⁻¹ * (⟨b, hS.le hb⟩)⁻¹ * ⟨a, hS.le ha⟩ * ⟨b, hS.le hb⟩ := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ _ (h.rho ⟨b, _⟩), hab]
    group
  have h2 := h.eq_one_of_mem_zpowers_of_mem (h.mem_zpowers_of_rho_eq_one hS hcS h1) hcL
  rw [show a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) by group, inv_mul_eq_one] at h2
  exact h2.symm


theorem isSylowOf_rho [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    IsSylowOf 2 ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho) h.rho.range := by
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  rw [← hQ]
  exact isSylowOf_map_range h.rho Q

theorem map_rho_eq_innAut (h : Standing t L p f) :
    (L.subgroupOf (centralizer ({t} : Set X))).map h.rho = innAut (Bar L) := by
  ext φ
  constructor
  · rintro ⟨⟨x, hx⟩, hxL, rfl⟩
    exact ⟨QuotientGroup.mk ⟨x, hxL⟩, (h.rho_of_mem ⟨x, hxL⟩).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨l, h.config.le_centralizer l.2⟩, l.2, h.rho_of_mem l⟩

theorem isSylowOf_inf [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : IsSylowOf 2 (S ⊓ L) L :=
  hS.inf_of_le_normalizer h.config.le_centralizer h.centralizer_le_normalizer

theorem isSylowOf_rho_inf [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    IsSylowOf 2 (((S ⊓ L).subgroupOf (centralizer ({t} : Set X))).map h.rho)
      (innAut (Bar L)) := by
  have hD : IsSylowOf 2 ((S ⊓ L).subgroupOf (centralizer ({t} : Set X)))
      (L.subgroupOf (centralizer ({t} : Set X))) := by
    rw [← isSylowOf_map_subtype_iff (centralizer ({t} : Set X)), subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_of_le_left (inf_le_right.trans h.config.le_centralizer),
      inf_of_le_left h.config.le_centralizer]
    exact h.isSylowOf_inf hS
  rw [← h.map_rho_eq_innAut]
  exact isSylowOf_map h.rho hD

theorem map_rho_inf_innAut [Finite X] (h : Standing t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) :
    (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) =
      ((S ⊓ L).subgroupOf (centralizer ({t} : Set X))).map h.rho := by
  refine (h.isSylowOf_rho_inf hS).eq_of_le (le_inf ?_ ?_) inf_le_right
    ((h.isSylowOf_rho hS).isPGroup.to_inf_left)
  · exact map_mono fun x hx => hx.1
  · rw [← h.map_rho_eq_innAut]
    exact map_mono fun x hx => hx.2


theorem rho_t (h : Standing t L p f) :
    h.rho ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ = 1 := by
  rw [← MonoidHom.mem_ker, mem_ker_rho, mem_coreActionKernel]
  refine ⟨h.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr rfl), fun j hj => ?_⟩
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.mp (h.config.le_centralizer hj)
  rw [show j⁻¹ * t⁻¹ * j * t = 1 by
    rw [show j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) by group, hjt]; group]
  exact one_mem _

theorem card_eq_two_mul [Finite X] (h : Standing t L p f) {S A : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (hAS : A ≤ S) (htA : t ∈ A) :
    Nat.card A = 2 * Nat.card ((A.subgroupOf (centralizer ({t} : Set X))).map h.rho) := by
  have hAH : A ≤ centralizer ({t} : Set X) := hAS.trans hS.le
  let φ : ↥(A.subgroupOf (centralizer ({t} : Set X))) →* MulAut (Bar L) :=
    h.rho.comp (A.subgroupOf (centralizer ({t} : Set X))).subtype
  have hrange : φ.range = (A.subgroupOf (centralizer ({t} : Set X))).map h.rho := by
    rw [MonoidHom.range_comp, range_subtype]
  let ι : ↥(A.subgroupOf (centralizer ({t} : Set X))) →* X :=
    (centralizer ({t} : Set X)).subtype.comp (A.subgroupOf (centralizer ({t} : Set X))).subtype
  have hι : Function.Injective ι :=
    (centralizer ({t} : Set X)).subtype_injective.comp Subtype.val_injective
  have hmap : φ.ker.map ι = zpowers t := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact h.mem_zpowers_of_rho_eq_one hS (hAS y.2) hy
    · intro hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
      have htH : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
      refine ⟨(⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr htA⟩ :
        ↥(A.subgroupOf (centralizer ({t} : Set X)))) ^ j, ?_, ?_⟩
      · show _ ∈ φ.ker
        rw [MonoidHom.mem_ker, map_zpow]
        change (h.rho ⟨t, htH⟩) ^ j = 1
        rw [h.rho_t, one_zpow]
      · rw [map_zpow]
        rfl
  have hker : Nat.card φ.ker = 2 := by
    rw [← card_map_of_injective hι, hmap, Nat.card_zpowers, h.config.orderOf_eq]
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange] at h1
  rw [h1]
  exact Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv.symm

end Standing

end CFSG.ComponentClassification.HarrisLit
