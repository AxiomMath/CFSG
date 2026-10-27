module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ISetup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def sec4IRho (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) :
    ↥L →* ProjOrth Sec4IQ :=
  Sec4IOmega.subtype.comp (sec4ICover e)

theorem sec4IRho_apply (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (l : ↥L) :
    sec4IRho e l = ((e (QuotientGroup.mk l) : Sec4IOmega) : ProjOrth Sec4IQ) :=
  rfl

theorem sec4IRho_mem (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (l : ↥L) :
    sec4IRho e l ∈ Sec4IOmega :=
  (sec4ICover e l).2

theorem sec4IRho_eq_one_iff (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (l : ↥L) :
    sec4IRho e l = 1 ↔ l ∈ Subgroup.center ↥L := by
  rw [sec4IRho_apply]
  constructor
  · intro h
    have h1 : e (QuotientGroup.mk l) = 1 := Subtype.ext (by simpa using h)
    exact (QuotientGroup.eq_one_iff l).mp (e.map_eq_one_iff.mp h1)
  · intro h
    rw [(QuotientGroup.eq_one_iff l).mpr h, map_one]
    rfl

theorem exists_sec4IRho_eq (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {y : ProjOrth Sec4IQ}
    (hy : y ∈ Sec4IOmega) : ∃ l : ↥L, sec4IRho e l = y := by
  obtain ⟨q, hq⟩ := e.surjective ⟨y, hy⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, by rw [sec4IRho_apply, hq]⟩

theorem sec4IRho_injOn [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {S : Subgroup ↥L} (hS : IsPGroup 2 ↥S) :
    Set.InjOn (sec4IRho e) (S : Set ↥L) := by
  intro x hx y hy hxy
  have hcov := sec4ICover_odd hL e
  have hxyeq : sec4ICover e x = sec4ICover e y := by
    apply Sec4IOmega.subtype_injective
    exact hxy
  have hker : x⁻¹ * y ∈ (sec4ICover e).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxyeq, inv_mul_cancel]
  have hSmem : x⁻¹ * y ∈ S := S.mul_mem (S.inv_mem hx) hy
  obtain ⟨k, hk⟩ := hS ⟨x⁻¹ * y, hSmem⟩
  have hk' : (x⁻¹ * y) ^ (2 ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  have h2 : orderOf (x⁻¹ * y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hkdiv : orderOf (x⁻¹ * y) ∣ Nat.card (sec4ICover e).ker :=
    Subgroup.orderOf_dvd_natCard _ hker
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (sec4ICover e).ker) :=
    hcov.odd_card_ker.coprime_two_left.pow_left k
  have hz : x⁻¹ * y = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 hkdiv)
  rwa [inv_mul_eq_one] at hz

theorem natCard_map_sec4IRho [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {S : Subgroup ↥L} (hS : IsPGroup 2 ↥S) :
    Nat.card (S.map (sec4IRho e)) = Nat.card S := by
  have hinj := sec4IRho_injOn hL e hS
  let φ : ↥S → ↥(S.map (sec4IRho e)) := fun x =>
    ⟨sec4IRho e x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      have hab' : sec4IRho e (a : ↥L) = sec4IRho e (b : ↥L) :=
        congrArg (fun x : ↥(S.map (sec4IRho e)) => (x : ProjOrth Sec4IQ)) hab
      exact Subtype.ext (hinj a.2 b.2 hab')
    · intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact (Nat.card_congr (Equiv.ofBijective φ hφ)).symm

theorem sec4IRho_isSylow2Of [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {P : Subgroup G} (hP : IsSylow2Of P L) :
    IsSylow2Of ((P.subgroupOf L).map (sec4IRho e)) Sec4IOmega := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hP.exists_sylow
  have hTsub : (T : Subgroup ↥L) = P.subgroupOf L := by
    have h := congrArg (Subgroup.comap L.subtype) hT
    rwa [Subgroup.comap_map_eq_self_of_injective L.subtype_injective] at h
  have h := isSylow2Of_map_sylow (T.mapSurjective (sec4ICover_odd hL e).surjective)
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, hTsub] at h
  have hrho : sec4IRho e = Sec4IOmega.subtype.comp (sec4ICover e) := rfl
  rw [hrho]
  exact h

theorem sec4IRho_isElemAbelian_map (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {S : Subgroup ↥L} (hS : CFSG.Open.IsElemAbelian 2 S) :
    CFSG.Open.IsElemAbelian 2 (S.map (sec4IRho e)) := by
  obtain ⟨hcomm, hexp⟩ := hS
  haveI : IsMulCommutative ↥S := hcomm
  refine ⟨inferInstance, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  rw [← map_pow, hexp x hx, map_one]

theorem sec4IRho_isElemAbelian_of_map [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {S : Subgroup ↥L} (hS : IsPGroup 2 ↥S)
    (h : CFSG.Open.IsElemAbelian 2 (S.map (sec4IRho e))) : CFSG.Open.IsElemAbelian 2 S := by
  obtain ⟨hcomm, hexp⟩ := h
  haveI : IsMulCommutative ↥(S.map (sec4IRho e)) := hcomm
  have hinj := sec4IRho_injOn hL e hS
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff_of_setLike]
    intro x hx y hy
    apply hinj (S.mul_mem hx hy) (S.mul_mem hy hx)
    rw [map_mul, map_mul]
    exact setLike_mul_comm (s := S.map (sec4IRho e))
      (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  · intro x hx
    rw [pow_two]
    apply hinj (S.mul_mem hx hx) S.one_mem
    rw [map_mul, map_one]
    simpa [pow_two] using
      hexp (sec4IRho e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

end CFSG.OddStandard.SmallF3.Omega
