module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.GH74.GLS.IVK.Lifted.FAutBasic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.DisconnectedInvolutionGraph CFSG.DisconnectedInvolutionGraph.Helpers
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

theorem lift_fixed_point (K : Subgroup G) {a : G} (haN : a ∈ normalizer (K : Set G))
    (haa : a * a = 1) (q : Hat K) (hq : phi K a haN q = q) :
    ∃ k : ↥K, hatMk K k = q ∧ a * (k : G) * a⁻¹ = (k : G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k₀, hk₀⟩ := hatMk_surjective K q
  let T := {k : ↥K // hatMk K k = q}
  have : Fintype T := Fintype.ofFinite T
  let σ : MulAut ↥K := K.normalizerMonoidHom ⟨a, haN⟩
  have hσ : ∀ k : ↥K, ((σ k : ↥K) : G) = a * k * a⁻¹ := fun k => rfl
  have hσ2 : ∀ k : ↥K, σ (σ k) = k := by
    intro k
    apply Subtype.ext
    rw [hσ, hσ]
    calc a * (a * (k : G) * a⁻¹) * a⁻¹ = (a * a) * (k : G) * (a⁻¹ * a⁻¹) := by group
      _ = (k : G) := by
        rw [haa, show a⁻¹ * a⁻¹ = (a * a)⁻¹ by group, haa]
        simp
  have hmap : ∀ t : T, hatMk K (σ t.1) = q := by
    intro t
    have h1 : hatMk K (σ t.1) = phi K a haN (hatMk K t.1) := by
      rw [phi_mk]
      rfl
    rw [h1, t.2, hq]
  let τ : Equiv.Perm T :=
    { toFun := fun t => ⟨σ t.1, hmap t⟩
      invFun := fun t => ⟨σ t.1, hmap t⟩
      left_inv := fun t => Subtype.ext (hσ2 t.1)
      right_inv := fun t => Subtype.ext (hσ2 t.1) }
  have hτ : τ ^ 2 ^ 1 = 1 := by
    ext t
    exact congrArg (fun k : ↥K => (k : G)) (hσ2 t.1)
  let e : T ≃ ↥(hatMk K).ker :=
    { toFun := fun t => ⟨k₀⁻¹ * t.1, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hk₀, t.2, inv_mul_cancel]⟩
      invFun := fun n => ⟨k₀ * n.1, by
        rw [map_mul, hk₀, MonoidHom.mem_ker.1 n.2, mul_one]⟩
      left_inv := fun t => Subtype.ext (by simp)
      right_inv := fun n => Subtype.ext (by simp) }
  have hodd : Odd (Fintype.card T) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
    exact odd_card_ker_hatMk K
  have hnd : ¬ 2 ∣ Fintype.card T := by
    intro hd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd)
  obtain ⟨t, ht⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hτ
  refine ⟨t.1, t.2, ?_⟩
  have h2 := congrArg (fun u : T => ((u.1 : ↥K) : G)) ht
  exact h2

omit [Finite G] in
theorem lam_mem_fixed (K : Subgroup G) {a : G} (haN : a ∈ normalizer (K : Set G))
    (x : ↥(K ⊓ centralizer ({a} : Set G))) :
    hatMk K ⟨(x : G), x.2.1⟩ ∈ fixedSubgroup (Hat K) (phi K a haN) := by
  show phi K a haN (hatMk K ⟨(x : G), x.2.1⟩) = hatMk K ⟨(x : G), x.2.1⟩
  rw [phi_mk]
  congr 1
  apply Subtype.ext
  have := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
  show a * (x : G) * a⁻¹ = (x : G)
  rw [← this]
  group

end Lift

section FixedSylow

theorem fixedCond_noncyclic_sylow {Q : Type} [Group Q] [Finite Q] (φ : MulAut Q) (hf : FixedCond Q φ)
    (P : Sylow 2 ↥(fixedSubgroup Q φ)) : ¬ IsCyclic ↥(P : Subgroup ↥(fixedSubgroup Q φ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcyc
  obtain ⟨-, -, -, ⟨-, -, hidx, -⟩, -⟩ := cyclic_sylow_normal_odd_complement P hcyc
  have hX2 : IsPGroup 2 (↥(fixedSubgroup Q φ) ⧸ pPrimeCore 2 ↥(fixedSubgroup Q φ)) := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := k)
    show (pPrimeCore 2 ↥(fixedSubgroup Q φ)).index = 2 ^ k
    rw [hidx]
    exact hk
  rcases hf with ⟨L, hL⟩ | hS
  · obtain ⟨Kc, ⟨hqs, -⟩, -, -, -⟩ := hL
    have hKc2 : IsPGroup 2 ↥Kc := hX2.to_subgroup Kc
    obtain ⟨hperf, -, a, b, hab⟩ := hqs
    have hnt : Nontrivial ↥Kc := by
      refine ⟨⟨(QuotientGroup.mk_surjective (s := Subgroup.center ↥Kc) a).choose,
        (QuotientGroup.mk_surjective (s := Subgroup.center ↥Kc) b).choose, ?_⟩⟩
      intro h
      apply hab
      have h1 := (QuotientGroup.mk_surjective (s := Subgroup.center ↥Kc) a).choose_spec
      have h2 := (QuotientGroup.mk_surjective (s := Subgroup.center ↥Kc) b).choose_spec
      rw [← h1, ← h2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
    have : Group.IsNilpotent ↥Kc := hKc2.isNilpotent
    have : Group.IsPerfect ↥Kc := hperf
    exact Group.IsPerfect.not_isSolvable ↥Kc inferInstance
  · obtain ⟨W, -, F, hF, hFin, hcard, ⟨iso⟩⟩ := hS
    have hW2 : IsPGroup 2 ↥W := hX2.to_subgroup W
    obtain ⟨n, hn⟩ := hW2.exists_card_eq
    have h24 : Nat.card ↥W = 24 := by
      rw [Nat.card_congr iso.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard]
      norm_num
    rw [h24] at hn
    have h3 : 3 ∣ 2 ^ n := by
      rw [← hn]
      norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

end FixedSylow

section Main14a

theorem ivk_1_4a_quat : CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_1_4a_quat := by
  intro G _ _ z S h K hK a ha ha2 haF hSyl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨haN, hF⟩ := haF
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, sq] at this
  set X : Subgroup G := K ⊓ centralizer ({a} : Set G) with hX
  set Pa : Subgroup G := S ⊓ K ⊓ centralizer ({a} : Set G) with hPa
  obtain ⟨Qa, hQa⟩ := hSyl
  have hPaS : Pa ≤ S := fun x hx => hx.1.1
  have hPaK : Pa ≤ K := fun x hx => hx.1.2
  have hPa2 : IsPGroup 2 ↥Pa := h.sylow.isPGroup.to_le hPaS
  have hXK : X ≤ K := inf_le_left
  let lam : ↥X →* ↥(fixedSubgroup (Hat K) (phi K a haN)) :=
    ((hatMk K).comp (Subgroup.inclusion hXK)).codRestrict _ (fun x => lam_mem_fixed K haN x)
  have hlam : Function.Surjective lam := by
    rintro ⟨q, hq⟩
    obtain ⟨k, hkq, hk⟩ := lift_fixed_point K haN haa q hq
    refine ⟨⟨(k : G), k.2, ?_⟩, Subtype.ext hkq⟩
    show (k : G) ∈ centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (k : G) * a = (a * (k : G) * a⁻¹) * a := by rw [hk]
      _ = a * (k : G) := by group
  have hnc : ¬ IsCyclic ↥Pa := by
    intro hcyc
    have hQacyc : IsCyclic ↥(Qa : Subgroup ↥X) := by
      have e := Subgroup.equivMapOfInjective (Qa : Subgroup ↥X) X.subtype X.subtype_injective
      rw [hQa] at e
      exact e.isCyclic.2 hcyc
    let R : Sylow 2 ↥(fixedSubgroup (Hat K) (phi K a haN)) := Qa.mapSurjective hlam
    have hRcyc : IsCyclic ↥(R : Subgroup ↥(fixedSubgroup (Hat K) (phi K a haN))) := by
      have : (R : Subgroup ↥(fixedSubgroup (Hat K) (phi K a haN))) = (Qa : Subgroup ↥X).map lam :=
        Sylow.coe_mapSurjective hlam Qa
      rw [this]
      exact isCyclic_of_surjective (lam.subgroupMap (Qa : Subgroup ↥X))
        (lam.subgroupMap_surjective (Qa : Subgroup ↥X))
    exact fixedCond_noncyclic_sylow _ hF.2.2.2.2 R hRcyc
  have hrank : NoCommutingDistinctInvolutions ↥Pa := by
    intro u v huv
    have hu := u.2
    have hv := v.2
    apply Subtype.ext
    apply Subtype.ext
    refine eq_of_pRank_one hK.2 (hPaK (u.1).2) (hPaK (v.1).2) ?_ ?_ ?_
    · rw [← Subgroup.orderOf_coe] at hu; exact hu
    · rw [← Subgroup.orderOf_coe] at hv; exact hv
    · exact congrArg Subtype.val huv
  rcases rank_one_two_cyclic_or_quaternion hPa2 hrank with hc | ⟨e, he1, ⟨φ⟩⟩
  · exact absurd hc hnc
  · refine ⟨e + 2, by omega, ⟨?_⟩⟩
    have : e + 2 - 2 = e := by omega
    rw [this]
    exact φ.symm

end Main14a


end CFSG.GH74.GLS.IVK.Lifted
