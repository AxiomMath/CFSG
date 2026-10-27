module

public import CFSG.LargeExtraspecial.AS35MQuot
public import CFSG.LargeExtraspecial.AS35HQuotSet
public import CFSG.LargeExtraspecial.AS35HCoprime

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuotE

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

omit S in
@[expose] def IsOddCentralE (E : Set G) (n : G) : Prop :=
  n ∈ centralizer E ∧ (∀ y ∈ centralizer E, n * y = y * n) ∧ Odd (orderOf n)

@[expose] def QuotCentHypE (E : Set G) : Prop :=
  ∀ c ∈ S.M, c ∈ centralizer E → (∀ q ∈ S.QG, q ∈ centralizer E → c * q = q * c) →
    ∃ n : G, IsOddCentralE E n ∧ c * n ∈ S.QG

@[expose] def QuotOTwoHypE (E : Set G) : Prop :=
  ∀ P : Subgroup G, P ≤ S.M → P ≤ centralizer E →
    (∀ n : G, IsOddCentralE E n → n ∈ P) →
    (∀ c ∈ S.M, c ∈ centralizer E → ∀ p ∈ P, c * p * c⁻¹ ∈ P) →
    (∀ p ∈ P, ∃ k : ℕ, ∃ n : G, IsOddCentralE E n ∧ p ^ (2 ^ k) = n) →
      ∀ p ∈ P, ∃ n : G, IsOddCentralE E n ∧ p * n ∈ S.QG

structure DescentSet (E : Set G) (x : G) : Prop where
  le_M : ∀ e ∈ E, e ∈ S.M
  mem : x ∈ E
  comm : ∀ e ∈ E, e * x = x * e
  cent : ∀ e ∈ E, ∀ q ∈ S.QG ⊓ centralizer ({x} : Set G), e * q = q * e

section Quot

variable {S} {E : Set G} {x : G}

theorem DescentSet.z_mem (hE : S.DescentSet E x) : S.z ∈ Cx E :=
  mem_centralizer_iff.mpr fun e he => S.z_comm (hE.le_M e he)

theorem DescentSet.x_mem (hE : S.DescentSet E x) : x ∈ Cx E :=
  mem_centralizer_iff.mpr hE.comm

theorem DescentSet.x_mem_M (hE : S.DescentSet E x) : x ∈ S.M := hE.le_M x hE.mem

theorem DescentSet.QG_inf (hE : S.DescentSet E x) :
    S.QG ⊓ centralizer E = S.QG ⊓ centralizer ({x} : Set G) := by
  ext q
  simp only [mem_inf]
  constructor
  · rintro ⟨hq, hqE⟩
    exact ⟨hq, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hqE x hE.mem).symm⟩
  · rintro ⟨hq, hqx⟩
    exact ⟨hq, mem_centralizer_iff.mpr fun e he => hE.cent e he q (mem_inf.mpr ⟨hq, hqx⟩)⟩

variable (S)

@[expose] def zCxE (hE : S.DescentSet E x) : Cx E := ⟨S.z, hE.z_mem⟩

@[expose] def zQuotE (hE : S.DescentSet E x) : GQ E := mkQ E (S.zCxE hE)

theorem zCxE_sq (hE : S.DescentSet E x) : S.zCxE hE ^ 2 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact S.z_mul_z)

@[expose] noncomputable def QQE (E : Set G) : Subgroup (GQ E) :=
  (S.QG.comap (Cx E).subtype).map (mkQ E)

theorem mem_QQE {y : GQ E} : y ∈ S.QQE E ↔ ∃ c : Cx E, (c : G) ∈ S.QG ∧ mkQ E c = y := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem mkQ_mem_QQE {c : Cx E} (hc : (c : G) ∈ S.QG) : mkQ E c ∈ S.QQE E :=
  (S.mem_QQE).mpr ⟨c, hc, rfl⟩

omit S in
theorem mem_Nx_of_isOddCentralE {n : G} (hn : IsOddCentralE E n) :
    (⟨n, hn.1⟩ : Cx E) ∈ Nx E := by
  refine ⟨mem_center_iff.mpr fun c => Subtype.ext ?_, by
    rw [Subgroup.orderOf_mk]; exact hn.2.2⟩
  exact (hn.2.1 c c.2).symm

omit S in
theorem isOddCentralE_of_mem_Nx {n : Cx E} (hn : n ∈ Nx E) : IsOddCentralE E n := by
  refine ⟨n.2, fun y hy => ?_, by rw [Subgroup.orderOf_coe]; exact hn.2⟩
  have h1 := mem_center_iff.mp hn.1 ⟨y, hy⟩
  exact (congrArg Subtype.val h1).symm

theorem orderOf_zQuotE (hE : S.DescentSet E x) : orderOf (S.zQuotE hE) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [zQuotE, ← map_pow, S.zCxE_sq, map_one]
  · intro h
    rw [zQuotE, ← map_one (mkQ E)] at h
    have h1 := eq_of_mkQ_eq (m := 1)
      (by rw [pow_one]; exact S.zCxE_sq hE) (by rw [one_pow]) h
    exact S.z_ne_one (congrArg Subtype.val h1)

theorem mkQ_mem_MQE_of_mem_M (hE : S.DescentSet E x) {c : Cx E} (hc : (c : G) ∈ S.M) :
    mkQ E c ∈ centralizer ({S.zQuotE hE} : Set (GQ E)) := by
  rw [mem_centralizer_singleton_iff, zQuotE, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (S.mem_M_iff.mp hc)

theorem mkQ_mem_MQE_iff (hE : S.DescentSet E x) (c : Cx E) :
    mkQ E c ∈ centralizer ({S.zQuotE hE} : Set (GQ E)) ↔ (c : G) ∈ S.M := by
  refine ⟨fun h => ?_, S.mkQ_mem_MQE_of_mem_M hE⟩
  rw [mem_centralizer_singleton_iff, zQuotE] at h
  have h1 := commute_of_mkQ_commute (m := 1)
    (by rw [pow_one]; exact S.zCxE_sq hE) h
  rw [S.mem_M_iff]
  exact congrArg Subtype.val h1

theorem QQE_le_MQE (hE : S.DescentSet E x) :
    S.QQE E ≤ centralizer ({S.zQuotE hE} : Set (GQ E)) := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := (S.mem_QQE).mp hy
  exact S.mkQ_mem_MQE_of_mem_M hE (S.QG_le_M hc)

@[expose] noncomputable def QQME (hE : S.DescentSet E x) :
    Subgroup ↥(centralizer ({S.zQuotE hE} : Set (GQ E))) :=
  (S.QQE E).subgroupOf (centralizer ({S.zQuotE hE} : Set (GQ E)))

theorem mem_QQME {hE : S.DescentSet E x}
    {m : ↥(centralizer ({S.zQuotE hE} : Set (GQ E)))} :
    m ∈ S.QQME hE ↔ (m : GQ E) ∈ S.QQE E := mem_subgroupOf

@[expose] noncomputable def cqxToQQME (hE : S.DescentSet E x) :
    ↥(S.QG ⊓ centralizer E) →* ↥(S.QQME hE) :=
  (((mkQ E).comp (Subgroup.inclusion (inf_le_right :
      S.QG ⊓ centralizer E ≤ Cx E))).codRestrict
    (centralizer ({S.zQuotE hE} : Set (GQ E)))
    (fun y => S.mkQ_mem_MQE_of_mem_M hE (S.QG_le_M (mem_inf.mp y.2).1))).codRestrict
    (S.QQME hE) (fun y => (S.mem_QQME).mpr (S.mkQ_mem_QQE (mem_inf.mp y.2).1))

theorem coe_cqxToQQME (hE : S.DescentSet E x) (y : ↥(S.QG ⊓ centralizer E)) :
    (((S.cqxToQQME hE y : ↥(centralizer ({S.zQuotE hE} : Set (GQ E)))) : GQ E)) =
      mkQ E ⟨y, (mem_inf.mp y.2).2⟩ := rfl

variable [Finite G]

theorem pow_four_of_coe_mem_QG_E {c : Cx E} (hc : (c : G) ∈ S.QG) : c ^ (2 ^ 2) = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow]; exact S.pow_four_of_mem_QG hc)

theorem cqxToQQME_injective (hE : S.DescentSet E x) :
    Function.Injective (S.cqxToQQME hE) := by
  intro a b h
  have h1 := congrArg (fun w : ↥(S.QQME hE) =>
    ((w : ↥(centralizer ({S.zQuotE hE} : Set (GQ E)))) : GQ E)) h
  simp only [coe_cqxToQQME] at h1
  have h2 := eq_of_mkQ_eq (S.pow_four_of_coe_mem_QG_E (c := ⟨a, (mem_inf.mp a.2).2⟩)
    (mem_inf.mp a.2).1) (S.pow_four_of_coe_mem_QG_E (c := ⟨b, (mem_inf.mp b.2).2⟩)
    (mem_inf.mp b.2).1) h1
  exact Subtype.ext (congrArg (fun w : Cx E => (w : G)) h2)

omit [Finite G] in
theorem cqxToQQME_surjective (hE : S.DescentSet E x) :
    Function.Surjective (S.cqxToQQME hE) := by
  rintro ⟨⟨w, hwM⟩, hw⟩
  have hw' : w ∈ S.QQE E := (S.mem_QQME).mp hw
  obtain ⟨c, hcQ, rfl⟩ := (S.mem_QQE).mp hw'
  exact ⟨⟨c, mem_inf.mpr ⟨hcQ, c.2⟩⟩, rfl⟩

@[expose] noncomputable def cqxEquivQQME (hE : S.DescentSet E x) :
    ↥(S.QG ⊓ centralizer E) ≃* ↥(S.QQME hE) :=
  MulEquiv.ofBijective (S.cqxToQQME hE) ⟨S.cqxToQQME_injective hE, S.cqxToQQME_surjective hE⟩

theorem isExtraspecialPGroup_cqxE (hE : S.DescentSet E x) (hx3 : orderOf x = 3)
    (hfix : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥) :
    IsExtraspecialPGroup 2 ↥(S.QG ⊓ centralizer E) := by
  rw [hE.QG_inf]
  exact S.isExtraspecialPGroup_cqx hE.x_mem_M (pow_three_of_orderOf hx3) hfix

@[expose] noncomputable def quotE (hE : S.DescentSet E x) (hx3 : orderOf x = 3)
    (hfix : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥) (hcent : S.QuotCentHypE E)
    (hO2 : S.QuotOTwoHypE E) : Setting (GQ E) where
  z := S.zQuotE hE
  orderOf_z := S.orderOf_zQuotE hE
  Q := S.QQME hE
  normal := ⟨fun q hq m => by
    rw [mem_QQME] at hq ⊢
    obtain ⟨d, hdQ, hd⟩ := (S.mem_QQE).mp hq
    obtain ⟨c, hc⟩ := mkQ_surjective E (m : GQ E)
    have hcM : (c : G) ∈ S.M := (S.mkQ_mem_MQE_iff hE c).mp (hc ▸ m.2)
    refine (S.mem_QQE).mpr ⟨c * d * c⁻¹, ?_, ?_⟩
    · rw [coe_mul, coe_mul, coe_inv]
      exact S.conj_mem_QG hcM hdQ
    · rw [map_mul, map_mul, map_inv, hc, hd]
      rfl⟩
  extraspecial := isExtraspecialPGroup_of_mulEquiv (S.cqxEquivQQME hE)
    (S.isExtraspecialPGroup_cqxE hE hx3 hfix)
  centralizer_le := by
    intro m hm
    rw [mem_QQME]
    obtain ⟨c, hc⟩ := mkQ_surjective E (m : GQ E)
    have hcM : (c : G) ∈ S.M := (S.mkQ_mem_MQE_iff hE c).mp (hc ▸ m.2)
    obtain ⟨n, hn, hcn⟩ := hcent c hcM c.2 (fun q hqQ hqE => by
      have hqC : q ∈ S.QG ⊓ centralizer E := mem_inf.mpr ⟨hqQ, hqE⟩
      have h1 := mem_centralizer_iff.mp hm (S.cqxToQQME hE ⟨q, hqC⟩)
        (S.cqxToQQME hE ⟨q, hqC⟩).2
      have h2 := congrArg (fun w : ↥(centralizer ({S.zQuotE hE} : Set (GQ E))) =>
        (w : GQ E)) h1
      simp only [coe_mul, coe_cqxToQQME, ← hc] at h2
      have h3 := commute_of_mkQ_commute (S.pow_four_of_coe_mem_QG_E (c := ⟨q, hqE⟩) hqQ)
        h2.symm
      exact congrArg (fun w : Cx E => (w : G)) h3)
    refine (S.mem_QQE).mpr ⟨c * ⟨n, hn.1⟩, hcn, ?_⟩
    rw [mkQ_mul_of_mem _ (mem_Nx_of_isOddCentralE hn), hc]
  le_of_normal := by
    intro P hPn hP2
    set P' : Subgroup G := ((P.map (centralizer ({S.zQuotE hE} : Set (GQ E))).subtype).comap
      (mkQ E)).map (Cx E).subtype with hP'
    have hmem : ∀ c : Cx E, (c : G) ∈ P' ↔
        mkQ E c ∈ P.map (centralizer ({S.zQuotE hE} : Set (GQ E))).subtype := fun c =>
      Subgroup.mem_map_iff_mem (Cx E).subtype_injective
    have key := hO2 P'
      (by
        rintro _ ⟨c, ⟨a, -, hac⟩, rfl⟩
        exact (S.mkQ_mem_MQE_iff hE c).mp (hac ▸ a.2))
      (by
        rintro _ ⟨c, -, rfl⟩
        exact c.2)
      (fun n hn => (hmem ⟨n, hn.1⟩).mpr ⟨1, P.one_mem, by
        rw [mkQ_eq_one_of_mem (mem_Nx_of_isOddCentralE hn)]
        rfl⟩)
      (by
        intro c hcM hcE p hp
        obtain ⟨c', hc', rfl⟩ := hp
        obtain ⟨a, ha, hac⟩ := hc'
        set cc : Cx E := ⟨c, hcE⟩ with hcc
        have hccM : mkQ E cc ∈ centralizer ({S.zQuotE hE} : Set (GQ E)) :=
          S.mkQ_mem_MQE_of_mem_M hE hcM
        refine (hmem (cc * c' * cc⁻¹)).mpr ⟨⟨mkQ E cc, hccM⟩ * a * ⟨mkQ E cc, hccM⟩⁻¹,
          hPn.conj_mem a ha _, ?_⟩
        change mkQ E cc * (a : GQ E) * (mkQ E cc)⁻¹ = mkQ E (cc * c' * cc⁻¹)
        rw [map_mul, map_mul, map_inv]
        congr 2)
      (by
        intro p hp
        obtain ⟨c', ⟨a, ha, hac⟩, rfl⟩ := hp
        obtain ⟨k, hk⟩ := hP2 ⟨a, ha⟩
        have hk' : a ^ (2 ^ k) = 1 := congrArg Subtype.val hk
        have h1 : mkQ E (c' ^ (2 ^ k)) = 1 := by
          rw [map_pow, ← hac]
          change ((a : GQ E)) ^ (2 ^ k) = 1
          rw [← coe_pow, hk', coe_one]
        have h2 := (QuotientGroup.eq_one_iff _).mp h1
        exact ⟨k, _, isOddCentralE_of_mem_Nx h2, by rw [coe_pow]; rfl⟩)
    intro w hw
    rw [mem_QQME]
    obtain ⟨c, hc⟩ := mkQ_surjective E (w : GQ E)
    have hcP : (c : G) ∈ P' := (hmem c).mpr ⟨w, hw, hc.symm⟩
    obtain ⟨n, hn, hcn⟩ := key c hcP
    refine (S.mem_QQE).mpr ⟨c * ⟨n, hn.1⟩, hcn, ?_⟩
    rw [mkQ_mul_of_mem _ (mem_Nx_of_isOddCentralE hn), hc]

section QuotAPI

variable (hE : S.DescentSet E x) (hx3 : orderOf x = 3)
  (hfix : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥) (hcent : S.QuotCentHypE E)
  (hO2 : S.QuotOTwoHypE E)

theorem quotE_z : (S.quotE hE hx3 hfix hcent hO2).z = S.zQuotE hE := rfl

theorem quotE_QG : (S.quotE hE hx3 hfix hcent hO2).QG = S.QQE E := by
  change (S.QQME hE).map (centralizer ({S.zQuotE hE} : Set (GQ E))).subtype = S.QQE E
  rw [QQME, Subgroup.subgroupOf_map_subtype]
  exact inf_of_le_left (S.QQE_le_MQE hE)

theorem card_quotE_Q :
    Nat.card (S.quotE hE hx3 hfix hcent hO2).Q =
      Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
  rw [← hE.QG_inf]
  exact (Nat.card_congr (S.cqxEquivQQME hE).toEquiv).symm

theorem two_mul_quotE_width :
    2 * (S.quotE hE hx3 hfix hcent hO2).width =
      finrank (ZMod 2) (fixSpace (S.rhoL hE.x_mem_M)) := by
  have h1 := (S.quotE hE hx3 hfix hcent hO2).card_Q_eq
  rw [S.card_quotE_Q, S.card_cqx_of_pow_three hE.x_mem_M (pow_three_of_orderOf hx3),
    ← pow_succ', add_comm] at h1
  have := Nat.pow_right_injective le_rfl h1
  omega

end QuotAPI

end Quot

end Setting

end CFSG.LargeExtraspecial
