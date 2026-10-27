module

public import CFSG.ClassicalInvolution.Asc77.AscFusionDiag
public import CFSG.ClassicalInvolution.Asc77.AscFusionReduce
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K₀ : Subgroup G} {z₀ : G}

theorem twins_of_mem_conjClass (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀)
    (hp2 : p ≠ 2) {X Y : Subgroup G} {r : G} (hX : X ∈ CoreAssembly.conjClass K₀)
    (hY : Y ∈ CoreAssembly.conjClass K₀) (hXr : IsUniqueInvolution X r)
    (hYr : IsUniqueInvolution Y r) (hne : X ≠ Y) :
    Y ≤ Subgroup.normalizer (X : Set G) ∧ X ≤ Subgroup.normalizer (Y : Set G) ∧
      ⁅X, Y⁆ ≤ oddCoreOf X ⊓ oddCoreOf Y := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K₀ X hX
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K₀ Y hY
  have hUa := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj a)
  have hUb := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj b)
  exact twins_of_conjSub hq h₀ ((hUa.eq hXr).trans (hUb.eq hYr).symm) hne

theorem primeResidual_two_eq_top_of_isPerfect (W : Type*) [Group W] [Finite W]
    [Group.IsPerfect W] : primeResidual 2 W = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar := primeResidual_characteristic 2 W
  have hnorm : (primeResidual 2 W).Normal := inferInstance
  have hodd : Odd (primeResidual 2 W).index :=
    Nat.odd_iff.mpr (by
      have h := primeResidual_coprime_index 2 W
      have : ¬ 2 ∣ (primeResidual 2 W).index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h
      omega)
  exact eq_top_of_perfect_of_odd_index hodd

omit [Finite G] in
theorem conjSub_mem_conjClass {X : Subgroup G} (hX : X ∈ CoreAssembly.conjClass K₀) (c : G) :
    conjSub c X ∈ CoreAssembly.conjClass K₀ := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K₀ X hX
  exact ⟨c * g, conjSub_mul c g K₀⟩

theorem bstar (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀)
    {P Q : Subgroup G} (hP : P ∈ CoreAssembly.conjClass K₀) (hQ : Q ∈ CoreAssembly.conjClass K₀)
    {u r : G} (hPu : IsUniqueInvolution P u) (hQr : IsUniqueInvolution Q r)
    {a : G} (haP : a ∈ P) (ha4 : orderOf a = 4) (har : a * r = r * a) :
    u ∈ Subgroup.normalizer (Q : Set G) := by
  classical
  by_contra hu
  have hPmem : IsClassicalMember p f P u := isClassicalMember_of_mem_conjClass hp2 hq h₀ hP hPu
  have hQmem : IsClassicalMember p f Q r := isClassicalMember_of_mem_conjClass hp2 hq h₀ hQ hQr
  have ha4' : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
  have ha2 : a * a = u := by
    have hsq : (a * a) * (a * a) = 1 := by
      calc (a * a) * (a * a) = a ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := ha4'
    have hne1 : a * a ≠ 1 := by
      intro h
      have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [ha4] at h2
      omega
    rcases hPu.unique (a * a) (P.mul_mem haP haP) hsq with h | h
    · exact absurd h hne1
    · exact h
  have hu2 : u * u = 1 := hPu.sq
  have hua : u * a = a * u := by rw [← ha2]; group
  have hur : u * r = r * u := by
    rw [← ha2, mul_assoc, har, ← mul_assoc, har, mul_assoc]
  have hne : Q ≠ conjSub u Q := fun h => hu (AscHypOmega.mem_normalizer_of_conjSub_eq h.symm)
  obtain ⟨hQ'mem, hQ'r, hQ'N, hQN', -⟩ := twin_facts_conj hp2 hq h₀ hQ hQr hur hne
  obtain ⟨L, hLM, hLfix, hLperf, hLqs, hLsub, hLnc⟩ :=
    exists_twin_diagonal hp2 hq h₀ hQ hQr hu2 hur hne
  have hQ'mem' : IsClassicalMember p f (conjSub u Q) r :=
    isClassicalMember_of_mem_conjClass hp2 hq h₀ hQ'mem hQ'r
  set Q' : Subgroup G := conjSub u Q with hQ'def
  set M : Subgroup G := Q ⊔ Q' with hMdef
  have hQHr : Q ≤ Subgroup.centralizer ({r} : Set G) := isSubnormal_le hQmem.subnormal
  have hQ'Hr : Q' ≤ Subgroup.centralizer ({r} : Set G) := isSubnormal_le hQ'mem'.subnormal
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hQ'N
  set Cu : Subgroup G := Subgroup.centralizer ({u} : Set G) with hCu
  set R : Subgroup G := Subgroup.centralizer ({r} : Set G) ⊓ Cu with hRdef
  have hLR : L ≤ R := by
    intro x hx
    refine ⟨sup_le hQHr hQ'Hr (hLM hx), ?_⟩
    show x ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hLfix x hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hLcomp : IsPComponent 2 (L.subgroupOf R) := by
    refine (pComponent_subgroupOf_iff 2 L R hLR).mpr ⟨hLsub, ?_, hLqs⟩
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    exact primeResidual_two_eq_top_of_isPerfect ↥L
  have hPsn : (P.subgroupOf Cu).IsSubnormal := subnormal_subgroupOf_member hPmem
  have hPsnR : (P.subgroupOf R).IsSubnormal := by
    have h1 := hPsn.comap (Subgroup.inclusion (inf_le_right : R ≤ Cu))
    have h2 : (P.subgroupOf Cu).comap (Subgroup.inclusion (inf_le_right : R ≤ Cu)) =
        P.subgroupOf R := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [h2] at h1
  have haR : a ∈ R := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr har, ?_⟩
    show a ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hua.symm
  have haPR : (⟨a, haR⟩ : ↥R) ∈ P.subgroupOf R := haP
  rcases contains_or_normalizes_core 2 (L.subgroupOf R) (P.subgroupOf R) hLcomp hPsnR with
    hle | ⟨hnorm, -⟩
  ·
    have hLP : ∀ x ∈ L, x ∈ P := fun x hx => hle (show (⟨x, hLR hx⟩ : ↥R) ∈ L.subgroupOf R from hx)
    obtain ⟨q, hq', ℓ, hℓ, hqℓ⟩ : ∃ q ∈ Q, ∃ ℓ ∈ L, ⁅q, ℓ⁆ ∉ oddCoreOf Q := by
      by_contra h
      push Not at h
      exact hLnc h
    have hℓ1 : ℓ ≠ 1 := by
      rintro rfl
      exact hqℓ (by rw [commutatorElement_one_right]; exact Subgroup.one_mem _)
    have hLperf' : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    have : Nontrivial ↥L := ⟨⟨⟨ℓ, hℓ⟩, 1, fun h => hℓ1 (congrArg Subtype.val h)⟩⟩
    have hevenL : 2 ∣ Nat.card ↥L := by
      by_contra h2
      have hodd : Odd (Nat.card ↥L) := Nat.odd_iff.mpr (by omega)
      exact Group.IsPerfect.not_isSolvable ↥L (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
    obtain ⟨ℓ₂, hℓ₂⟩ := exists_prime_orderOf_dvd_card' 2 hevenL
    have hℓ₂sq : (ℓ₂ : G) * ℓ₂ = 1 := by
      have : (ℓ₂ : G) ^ 2 = 1 := by
        rw [← Subgroup.orderOf_coe] at hℓ₂
        rw [← hℓ₂]
        exact pow_orderOf_eq_one _
      rwa [pow_two] at this
    have hℓ₂1 : (ℓ₂ : G) ≠ 1 := by
      intro h
      have : ℓ₂ = 1 := Subtype.ext h
      rw [this, orderOf_one] at hℓ₂
      omega
    have hℓ₂u : (ℓ₂ : G) = u :=
      (hPu.unique ℓ₂ (hLP _ ℓ₂.2) hℓ₂sq).resolve_left hℓ₂1
    exact hu (hMQ (hLM (hℓ₂u ▸ ℓ₂.2)))
  ·
    have hnormA : (⟨a, haR⟩ : ↥R) ∈ Subgroup.normalizer ((L.subgroupOf R : Subgroup ↥R) : Set ↥R) :=
      hnorm haPR
    have hnormAinv : (⟨a, haR⟩ : ↥R)⁻¹ ∈
        Subgroup.normalizer ((L.subgroupOf R : Subgroup ↥R) : Set ↥R) :=
      (Subgroup.normalizer _).inv_mem hnormA
    have hLconj : L ≤ conjSub a M := by
      intro x hx
      rw [mem_conjSub_iff]
      have hxR : (⟨x, hLR hx⟩ : ↥R) ∈ L.subgroupOf R := hx
      have h1 := ((Subgroup.mem_normalizer_iff.mp hnormAinv) _).mp hxR
      have h2 : a⁻¹ * x * a⁻¹⁻¹ ∈ L := h1
      rw [inv_inv] at h2
      exact hLM h2
    have hMconj : conjSub a M = conjSub a Q ⊔ conjSub a Q' := by
      rw [hMdef, conjSub, Subgroup.map_sup]
      rfl
    have haru : a * r * a⁻¹ = r := by rw [har, mul_assoc, mul_inv_cancel, mul_one]
    have hQa_mem : conjSub a Q ∈ CoreAssembly.conjClass K₀ := conjSub_mem_conjClass hQ a
    have hQa_r : IsUniqueInvolution (conjSub a Q) r := by
      have := hQr.conj a
      rwa [haru] at this
    have hQ'a_mem : conjSub a Q' ∈ CoreAssembly.conjClass K₀ := conjSub_mem_conjClass hQ'mem a
    have hQ'a_r : IsUniqueInvolution (conjSub a Q') r := by
      have := hQ'r.conj a
      rwa [haru] at this
    have hQaQ : Q ≠ conjSub a Q := by
      intro h
      apply hu
      have hanorm : a ∈ Subgroup.normalizer (Q : Set G) :=
        AscHypOmega.mem_normalizer_of_conjSub_eq h.symm
      have := Subgroup.mul_mem _ hanorm hanorm
      rwa [ha2] at this
    have hQ'aQ : Q ≠ conjSub a Q' := by
      intro h
      apply hu
      have h1 : conjSub (a * u) Q = Q := by
        rw [conjSub_mul]
        exact h.symm
      have hau : a * u ∈ Subgroup.normalizer (Q : Set G) :=
        AscHypOmega.mem_normalizer_of_conjSub_eq h1
      have hinv : a⁻¹ = a * u :=
        inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ha2, hu2])
      rw [← hinv] at hau
      have hanorm : a ∈ Subgroup.normalizer (Q : Set G) := by
        simpa using (Subgroup.normalizer (Q : Set G)).inv_mem hau
      have := Subgroup.mul_mem _ hanorm hanorm
      rwa [ha2] at this
    obtain ⟨hQaN, -, hQQa⟩ := twins_of_mem_conjClass hq h₀ hp2 hQ hQa_mem hQr hQa_r hQaQ
    obtain ⟨hQ'aN, -, hQQ'a⟩ := twins_of_mem_conjClass hq h₀ hp2 hQ hQ'a_mem hQr hQ'a_r hQ'aQ
    have hcommQ : ⁅conjSub a Q ⊔ conjSub a Q', Q⁆ ≤ oddCoreOf Q :=
      CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize _ _ _ _
        (by rw [Subgroup.commutator_comm]; exact hQQa.trans inf_le_left)
        (by rw [Subgroup.commutator_comm]; exact hQQ'a.trans inf_le_left)
        (fun g hg => mem_normalizer_oddCoreOf' (hQaN hg))
        (fun g hg => mem_normalizer_oddCoreOf' (hQ'aN hg))
    apply hLnc
    intro q hq' ℓ hℓ
    have hℓM : ℓ ∈ conjSub a Q ⊔ conjSub a Q' := hMconj ▸ hLconj hℓ
    have h1 : ⁅ℓ, q⁆ ∈ ⁅conjSub a Q ⊔ conjSub a Q', Q⁆ :=
      Subgroup.commutator_mem_commutator hℓM hq'
    have h2 := hcommQ h1
    rw [← commutatorElement_inv]
    exact (oddCoreOf Q).inv_mem h2

theorem bStarStmt (p f : ℕ) [Fact p.Prime] : BStarStmt p f := by
  intro G _ _ K₀ z₀ h₀ hp2 hq P hP Q hQ u r hPu hQr a haP ha4 har
  exact bstar hp2 hq h₀ hP hQ hPu hQr haP ha4 har

theorem classicalFusionStmt_of_fusionCore (hC : FusionCoreStmt p f) : ClassicalFusionStmt p f :=
  classicalFusionStmt_of_core (bStarStmt p f) hC

end CFSG.ClassicalInvolution.Asc77.AscFusion
