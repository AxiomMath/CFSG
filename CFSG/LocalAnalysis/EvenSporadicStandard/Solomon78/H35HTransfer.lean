module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

private theorem exists_normal_odd_complement {D : Type*} [Group D] [Finite D] {u : D}
    (hu : orderOf u = 2) (hcomm : ∀ d : D, d * u = u * d)
    (hP : ∀ P : Subgroup D, IsPGroup 2 P → Nat.card P ≤ 2) :
    ∃ D0 : Subgroup D, D0.Normal ∧ (∀ d : D, d ∈ D0 ↔ Odd (orderOf d)) ∧
      ∀ d : D, d ∈ D0 ∨ d * u ∈ D0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardU : Nat.card (zpowers u) = 2 := by rw [Nat.card_zpowers, hu]
  have hfact : (Nat.card D).factorization 2 = 1 := by
    have h2 : 2 ∣ Nat.card D := hu ▸ orderOf_dvd_natCard u
    have hge : 1 ≤ (Nat.card D).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2
    obtain ⟨S⟩ : Nonempty (Sylow 2 D) := inferInstance
    have hS := hP S S.isPGroup'
    rw [Sylow.card_eq_multiplicity] at hS
    have hlt : 2 ^ (Nat.card D).factorization 2 ≤ 2 ^ 1 := by simpa using hS
    exact le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).1 hlt) hge
  let P : Sylow 2 D := Sylow.ofCard (zpowers u) (by rw [hcardU, hfact]; norm_num)
  have hPeq : (P : Subgroup D) = zpowers u := rfl
  have hNC : normalizer P ≤ centralizer (P : Set D) := by
    intro g _
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 (hPeq ▸ hh : h ∈ zpowers u)
    exact ((Commute.zpow_right (hcomm g : Commute g u) k).symm).eq
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hodd : Odd (Nat.card (MonoidHom.transferSylow P hNC).ker) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hNC))
  have hidx : (MonoidHom.transferSylow P hNC).ker.index = 2 := by
    rw [hcompl.symm.index_eq_card]
    exact hcardU
  have hker : ∀ d ∈ (MonoidHom.transferSylow P hNC).ker, Odd (orderOf d) := fun d hd => by
    have := orderOf_dvd_natCard (⟨d, hd⟩ : (MonoidHom.transferSylow P hNC).ker)
    rw [Subgroup.orderOf_mk] at this
    exact hodd.of_dvd_nat this
  have huker : u ∉ (MonoidHom.transferSylow P hNC).ker := fun h => by
    have h1 := hker u h
    rw [hu] at h1
    exact absurd h1 (by decide)
  refine ⟨(MonoidHom.transferSylow P hNC).ker, inferInstance, fun d => ⟨hker d, fun hd => ?_⟩, ?_⟩
  · by_contra hnd
    have hdu : d * u ∈ (MonoidHom.transferSylow P hNC).ker := by
      rw [mul_mem_iff_of_index_two hidx]
      exact ⟨fun h => absurd h hnd, fun h => absurd h huker⟩
    have hc : Commute d u := hcomm d
    have h3 : orderOf (d * u) = orderOf d * orderOf u :=
      hc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hu]; exact Nat.coprime_two_right.2 hd)
    have h4 := hker _ hdu
    rw [h3, hu] at h4
    exact absurd h4 (by simp)
  · intro d
    by_cases hd : d ∈ (MonoidHom.transferSylow P hNC).ker
    · exact Or.inl hd
    · refine Or.inr ?_
      rw [mul_mem_iff_of_index_two hidx]
      exact ⟨fun h => absurd h hd, fun h => absurd h huker⟩

private theorem isMulCommutative_of_card_le_four {A : Type*} [Group A] [Finite A]
    (h : Nat.card A ≤ 4) : IsMulCommutative A := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  obtain h1 | h2 | h3 | h4 : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨ Nat.card A = 4 :=
    by omega
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 h1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isCyclic_of_prime_card h2
    infer_instance
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := isCyclic_of_prime_card h3
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)

theorem not_mem_commutator_of_transfer {G : Type} [Group G] [Finite G] {u : G}
    (hu : orderOf u = 2) {M : Subgroup G} (hMH : M ≤ centralizer ({u} : Set G))
    (hMn : (M.subgroupOf (centralizer ({u} : Set G))).Normal)
    (hMz : Odd (Nat.card (center M)))
    (hSyl : ∀ S : Sylow 2 (centralizer (M : Set G)), Nat.card S = 2)
    (hidx : (M ⊔ (centralizer (M : Set G) ⊓ centralizer ({u} : Set G))).relIndex
      (centralizer ({u} : Set G)) ≤ 2) :
    u ∉ ⁅centralizer ({u} : Set G), centralizer ({u} : Set G)⁆ := by
  set H : Subgroup G := centralizer ({u} : Set G)
  set D : Subgroup G := centralizer (M : Set G) ⊓ H
  have hHu : ∀ h ∈ H, h * u = u * h := fun h hh => mem_centralizer_singleton_iff.1 hh
  have huH : u ∈ H := mem_centralizer_singleton_iff.2 rfl
  have hMu : ∀ m ∈ M, m * u = u * m := fun m hm => hHu m (hMH hm)
  have huC : u ∈ centralizer (M : Set G) := mem_centralizer_iff.2 fun m hm => hMu m hm
  have huD : u ∈ D := ⟨huC, huH⟩
  have hDH : D ≤ H := inf_le_right
  have hDC : D ≤ centralizer (M : Set G) := inf_le_left
  have hDM : ∀ d ∈ D, ∀ m ∈ M, m * d = d * m :=
    fun d hd m hm => mem_centralizer_iff.1 (hDC hd) m hm
  have hMconj : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M := fun h hh m hm =>
    mem_subgroupOf.1 (hMn.conj_mem ⟨m, hMH hm⟩ (mem_subgroupOf.2 hm) ⟨h, hh⟩)
  have hDconj : ∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D := by
    intro h hh d hd
    have hmem : h * d * h⁻¹ ∈ H := mul_mem (mul_mem hh (hDH hd)) (inv_mem hh)
    refine ⟨mem_centralizer_iff.2 fun m hm => ?_, hmem⟩
    have hm' : h⁻¹ * m * h ∈ M := by simpa using hMconj h⁻¹ (inv_mem hh) m hm
    have h1 := hDM d hd _ hm'
    calc m * (h * d * h⁻¹) = h * ((h⁻¹ * m * h) * d) * h⁻¹ := by group
      _ = h * (d * (h⁻¹ * m * h)) * h⁻¹ := by rw [h1]
      _ = (h * d * h⁻¹) * m := by group
  have hP' : ∀ P : Subgroup D, IsPGroup 2 P → Nat.card P ≤ 2 := by
    intro P hP
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let ι : D →* centralizer (M : Set G) := Subgroup.inclusion hDC
    have hι : Function.Injective ι := Subgroup.inclusion_injective hDC
    obtain ⟨S, hS⟩ := (hP.map ι).exists_le_sylow
    calc Nat.card P = Nat.card (P.map ι) := (Subgroup.card_map_of_injective hι).symm
      _ ≤ Nat.card S := Subgroup.card_le_of_le hS
      _ = 2 := hSyl S
  obtain ⟨D0, -, hD0, hcov⟩ := exists_normal_odd_complement (D := ↥D) (u := ⟨u, huD⟩)
    (by rw [Subgroup.orderOf_mk]; exact hu) (fun d => Subtype.ext (hHu d (hDH d.2))) hP'
  set D0G : Subgroup G := D0.map D.subtype
  have hD0Gmem : ∀ x : G, x ∈ D0G ↔ x ∈ D ∧ Odd (orderOf x) := by
    intro x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d.2, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact (hD0 d).1 hd⟩
    · rintro ⟨hx, hodd⟩
      exact ⟨⟨x, hx⟩, (hD0 _).2 (by rwa [Subgroup.orderOf_mk]), rfl⟩
  have hD0GD : D0G ≤ D := fun x hx => ((hD0Gmem x).1 hx).1
  have hD0Gconj : ∀ h ∈ H, ∀ x ∈ D0G, h * x * h⁻¹ ∈ D0G := by
    intro h hh x hx
    obtain ⟨hxD, hxodd⟩ := (hD0Gmem x).1 hx
    refine (hD0Gmem _).2 ⟨hDconj h hh x hxD, ?_⟩
    have := (MulAut.conj h).orderOf_eq x
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hxodd
  have hMD0G : M ≤ normalizer (D0G : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    intro m hm
    exact mem_centralizer_iff.2 fun d hd => (hDM d (hD0GD hd) m hm).symm
  have hMD : M ≤ normalizer (D : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    intro m hm
    exact mem_centralizer_iff.2 fun d hd => (hDM d hd m hm).symm
  set Q : Subgroup G := M ⊔ D0G
  set N : Subgroup G := M ⊔ D
  have hQmem : ∀ x ∈ Q, ∃ m ∈ M, ∃ d ∈ D0G, m * d = x := by
    intro x hx
    have h1 := Subgroup.coe_mul_of_left_le_normalizer_right M D0G hMD0G
    rw [← SetLike.mem_coe, h1] at hx
    exact Set.mem_mul.1 hx
  have hNmem : ∀ x ∈ N, ∃ m ∈ M, ∃ d ∈ D, m * d = x := by
    intro x hx
    have h1 := Subgroup.coe_mul_of_left_le_normalizer_right M D hMD
    rw [← SetLike.mem_coe, h1] at hx
    exact Set.mem_mul.1 hx
  have hNH : N ≤ H := sup_le hMH hDH
  have hQN : Q ≤ N := sup_le_sup_left hD0GD M
  have hQn : (Q.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨m, hm, d, hd, hmd⟩ := hQmem _ hx
    have h1 : (g : G) * x * (g : G)⁻¹ = ((g : G) * m * (g : G)⁻¹) * ((g : G) * d * (g : G)⁻¹) := by
      rw [← hmd]; group
    show (g : G) * x * (g : G)⁻¹ ∈ Q
    rw [h1]
    exact Subgroup.mul_mem_sup (hMconj g g.2 m hm) (hD0Gconj g g.2 d hd)
  have huQ : u ∉ Q := by
    intro huQ
    obtain ⟨m, hm, d, hd, hmd⟩ := hQmem u huQ
    obtain ⟨hdD, hdodd⟩ := (hD0Gmem d).1 hd
    have hmC : ∀ m' ∈ M, m' * m = m * m' := by
      intro m' hm'
      have h1 : m = u * d⁻¹ := by rw [← hmd]; group
      have h2 : m' * d⁻¹ = d⁻¹ * m' := by
        have h3 := hDM d hdD m' hm'
        calc m' * d⁻¹ = d⁻¹ * (d * m') * d⁻¹ := by group
          _ = d⁻¹ * (m' * d) * d⁻¹ := by rw [h3]
          _ = d⁻¹ * m' := by group
      rw [h1]
      calc m' * (u * d⁻¹) = (m' * u) * d⁻¹ := by group
        _ = (u * m') * d⁻¹ := by rw [hMu m' hm']
        _ = u * (m' * d⁻¹) := by group
        _ = u * (d⁻¹ * m') := by rw [h2]
        _ = (u * d⁻¹) * m' := by group
    have hz : (⟨m, hm⟩ : M) ∈ center M :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hmC g g.2)
    have hmodd : Odd (orderOf m) := by
      have h := orderOf_dvd_natCard (⟨⟨m, hm⟩, hz⟩ : center M)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h
      exact hMz.of_dvd_nat h
    have hcm : Commute m d := hDM d hdD m hm
    have hodd2 : Odd (orderOf (m * d)) :=
      (hmodd.mul hdodd).of_dvd_nat hcm.orderOf_mul_dvd_mul_orderOf
    rw [hmd, hu] at hodd2
    exact absurd hodd2 (by decide)
  have hQN2 : Q.relIndex N = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨u, le_sup_right (a := M) huD, huQ, ?_⟩
    intro b hb
    obtain ⟨m, hm, d, hd, rfl⟩ := hNmem b hb
    rcases hcov ⟨d, hd⟩ with h | h
    · exact Or.inr (Subgroup.mul_mem_sup hm (⟨⟨d, hd⟩, h, rfl⟩ : d ∈ D0G))
    · refine Or.inl ?_
      have h1 : d * u ∈ D0G := ⟨⟨d, hd⟩ * ⟨u, huD⟩, h, rfl⟩
      rw [mul_assoc]
      exact Subgroup.mul_mem_sup hm h1
  have hQH2 : Q.relIndex H ≤ 4 := by
    rw [← Subgroup.relIndex_mul_relIndex Q N H hQN hNH, hQN2]
    exact (Nat.mul_le_mul_left 2 hidx).trans (by norm_num)
  have : (Q.subgroupOf H).Normal := hQn
  have hcard : Nat.card (↥H ⧸ Q.subgroupOf H) ≤ 4 := by
    rw [← Subgroup.index_eq_card]
    exact hQH2
  have hcomm := isMulCommutative_of_card_le_four hcard
  have hcommle : ⁅H, H⁆ ≤ Q := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    let X : ↥H := ⟨x, hx⟩
    let Y : ↥H := ⟨y, hy⟩
    have h1 : (QuotientGroup.mk (X * Y * X⁻¹ * Y⁻¹) : ↥H ⧸ Q.subgroupOf H) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      rw [hcomm.is_comm.comm (QuotientGroup.mk X) (QuotientGroup.mk Y)]
      group
    exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  exact fun h => huQ (hcommle h)

end CFSG.EvenSporadicStandard.Solomon78
