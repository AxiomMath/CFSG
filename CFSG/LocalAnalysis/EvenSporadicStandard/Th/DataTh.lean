module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Data
public import CFSG.Sporadic.ThSchreier.NodeCentralCentralizer
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import CFSG.Sporadic.ThSchreier.NodeInnerInvolution

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier

theorem exists_sylow_center_elementary {J : Type*} [Group J] [Finite J] {Mc Q : Subgroup J}
    {a : J} (hQM : Q ≤ Mc) (hp : CFSG.pCore 2 ↥Mc = Q.subgroupOf Mc)
    (hc : centralizer (Q : Set J) ⊓ Mc = zpowers a) (ha : a ^ 2 = 1) (hidx : ¬ 2 ∣ Mc.index) :
    ∃ S : Subgroup J, IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧
      ∀ x ∈ S, (∀ y ∈ S, x * y = y * x) → x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 (Q.subgroupOf Mc) := hp ▸ CFSG.pCore_isPGroup
  obtain ⟨S₀, hS₀⟩ := hQp.exists_le_sylow
  refine ⟨(S₀ : Subgroup Mc).map Mc.subtype, S₀.isPGroup'.map _, ?_, ?_⟩
  · have h1 : ((S₀ : Subgroup Mc).map Mc.subtype).relIndex Mc = (S₀ : Subgroup Mc).index := by
      rw [Subgroup.relIndex,
        show ((S₀ : Subgroup Mc).map Mc.subtype).subgroupOf Mc = (S₀ : Subgroup Mc) from
          Subgroup.comap_map_eq_self_of_injective Mc.subtype_injective _]
    have h2 := Subgroup.relIndex_mul_index (Subgroup.map_subtype_le (S₀ : Subgroup Mc))
    rw [h1] at h2
    rw [← h2]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
    · exact S₀.not_dvd_index h
    · exact hidx h
  · rintro _ ⟨x, hx, rfl⟩ hcomm
    have hxc : (x : J) ∈ centralizer (Q : Set J) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hqS : q ∈ (S₀ : Subgroup Mc).map Mc.subtype :=
        ⟨⟨q, hQM hq⟩, hS₀ (by rw [mem_subgroupOf]; exact hq), rfl⟩
      exact (hcomm q hqS).symm
    have hxa : (x : J) ∈ zpowers a := hc ▸ ⟨hxc, x.2⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxa
    show (x : J) ^ 2 = 1
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [ha]

theorem ThData.of_facts {F : Type} [Group F] [Finite F] (hs : IsSimpleGroup F)
    (hn : ∃ x y : F, x * y ≠ y * x) (hinner : ∀ α : MulAut F, ∃ f : F, α = MulAut.conj f)
    {a : F} (ha2 : orderOf a = 2) (hconj : ∀ u : F, orderOf u = 2 → IsConj a u)
    (hperf : ⁅centralizer ({a} : Set F), centralizer ({a} : Set F)⁆ = centralizer ({a} : Set F))
    (hsyl : ∃ S : Subgroup F, IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧
      ∀ x ∈ S, (∀ y ∈ S, x * y = y * x) → x ^ 2 = 1) : ThData F := by
  refine ⟨hs, hn, hinner, fun u v hu hv => (hconj u hu).symm.trans (hconj v hv), ⟨a, ha2⟩,
    fun u hu => ?_, hsyl⟩
  obtain ⟨c, hc⟩ := isConj_iff.1 (hconj u hu)
  have h1 := map_centralizer_singleton (MulAut.conj c : F ≃* F) a
  have h2 : (MulAut.conj c : F ≃* F) a = u := (MulAut.conj_apply c a).trans hc
  rw [h2] at h1
  rw [← h1, map_commutator_self, hperf]

theorem exists_noncommuting_of_orders {Y : Type*} [Group Y] {x y : Y} (hx : orderOf x = 2)
    (hy : orderOf y = 3) (hxy : orderOf (x * y) = 19) : ∃ u v : Y, u * v ≠ v * u := by
  refine ⟨x, y, fun h => ?_⟩
  have hd := (show Commute x y from h).orderOf_mul_dvd_lcm
  rw [hxy, hx, hy] at hd
  exact absurd hd (by norm_num)

section Certified


instance finite_J_inst : Finite J := finite_J

instance finite_carrier_Th : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Th) := finite_Th

theorem thData_J : ThData J := by
  obtain ⟨hcent, hcard, hpC, hCQ⟩ := ctuc_Th_full_central_involution_centralizer
  have ha2 : orderOf a = 2 := Kernel.orderOf_a th_kernel_facts
  have hcard_J : Nat.card J = 90745943887872000 := natCard_J
  have hMperf : ⁅centralizer ({a} : Set J), centralizer ({a} : Set J)⁆ =
      centralizer ({a} : Set J) := by
    rw [hcent]
    have := isPerfect_M
    exact Subgroup.commutator_eq_self
  have hidx : ¬ 2 ∣ (centralizer ({a} : Set J)).index := by
    have h := (centralizer ({a} : Set J)).card_mul_index
    rw [hcard, hcard_J] at h
    have : (centralizer ({a} : Set J)).index = 976841775 := by omega
    rw [this]
    norm_num
  refine ThData.of_facts (Kernel.isSimpleGroup_J th_kernel_facts)
    (exists_noncommuting_of_orders ha2 (Kernel.orderOf_b th_kernel_facts)
      (Kernel.orderOf_ab th_kernel_facts)) ?_ ha2
    (fun u hu => all_involutions_conjugate u hu) hMperf ?_
  · intro α
    have hmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner J :=
      inner_J ▸ Subgroup.mem_top α
    obtain ⟨f, hf⟩ := hmem
    exact ⟨f, hf.symm⟩
  · exact exists_sylow_center_elementary (Q := Q) (a := a) (hcent ▸ Q_le_M) hpC hCQ
      (by have := pow_orderOf_eq_one a; rwa [ha2] at this) hidx

theorem thData_th : ThData (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
  ThData.of_mulEquiv (F := CFSG.Blueprint.NativeSporadic.Carrier .Th) (F' := J) thEquivJ thData_J

end Certified

end CFSG.EvenSporadicStandard.ThStd
