module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallMod
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

namespace KDRank3SmallAbs

@[expose] def SmallF1 (S : Type) [Group S] (E : Subgroup (MulAut S)) : Prop :=
  ∀ b ∈ E, b ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S → ∀ W : Subgroup (MulAut S), IsPGroup 2 W → W ≠ ⊥ → W ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S →
    W ≤ Subgroup.centralizer ({b} : Set (MulAut S)) →
      E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S ≤ Subgroup.normalizer (W : Set (MulAut S)) → False

@[expose] def SmallF2 (S : Type) [Group S] (E : Subgroup (MulAut S)) : Prop :=
  ∀ W : Subgroup (MulAut S), IsPGroup 2 W → W ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S →
    E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S ≤ Subgroup.centralizer (W : Set (MulAut S)) → W = ⊥

@[expose] def SmallF3 (S : Type) [Group S] : Prop :=
  ∀ P : Subgroup (Outer S), IsPGroup 2 P → IsCyclic P

section Integers

theorem zmod_cube_one (m : ℕ) (hm : 0 < m) (u : ZMod (2 ^ m)) (hu : u ^ 3 = 1) : u = 1 := by
  have hu2 : u * u ^ 2 = 1 := by rw [← pow_succ']; exact hu
  have hu2' : u ^ 2 * u = 1 := by rw [← pow_succ]; exact hu
  let v : (ZMod (2 ^ m))ˣ := ⟨u, u ^ 2, hu2, hu2'⟩
  have hv3 : v ^ 3 = 1 := Units.ext (by simpa using hu)
  have htot : Nat.totient (2 ^ m) = 2 ^ (m - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two hm]
    simp
  have hvt : v ^ (2 ^ (m - 1)) = 1 := by
    have h := ZMod.pow_totient v
    rwa [htot] at h
  have hcop : Nat.Coprime 3 (2 ^ (m - 1)) := Nat.Coprime.pow_right _ (by norm_num)
  have h1 : v ^ Nat.gcd 3 (2 ^ (m - 1)) = 1 := pow_gcd_eq_one.2 ⟨hv3, hvt⟩
  rw [hcop.gcd_eq_one, pow_one] at h1
  exact congrArg Units.val h1

theorem int_cube_sub_one_dvd {m : ℕ} {k : ℤ} (h : (2 : ℤ) ^ m ∣ k ^ 3 - 1) :
    (2 : ℤ) ^ m ∣ k - 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h' : ((2 ^ m : ℕ) : ℤ) ∣ 1 - k ^ 3 := by
    push_cast
    exact (dvd_sub_comm).1 h
  have hc : (k : ZMod (2 ^ m)) ^ 3 = 1 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (k ^ 3) 1 (2 ^ m)).2 h'
    push_cast at this
    exact this
  have hk1 : (k : ZMod (2 ^ m)) = 1 := zmod_cube_one m hm _ hc
  have h2 : ((2 ^ m : ℕ) : ℤ) ∣ k - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 k (2 ^ m)).1 (by push_cast; exact hk1.symm)
  push_cast at h2
  exact h2

end Integers

section Cyclic

theorem centralizes_of_isCyclic_two {G : Type} [Group G] [Finite G] {T E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hT : IsPGroup 2 T) (hcyc : IsCyclic T)
    (hN : E ≤ Subgroup.normalizer (T : Set G)) : E ≤ Subgroup.centralizer (T : Set G) := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨m, hm⟩ := hT.exists_card_eq
  set γ : G := (g : G) with hγ
  have hγT : γ ∈ T := g.2
  have hord : orderOf γ = 2 ^ m := by
    rw [hγ, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hm]
  intro e he
  have hcon : e * γ * e⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hN he) γ).1 hγT
  obtain ⟨k, hk⟩ : ∃ k : ℤ, γ ^ k = e * γ * e⁻¹ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨e * γ * e⁻¹, hcon⟩)
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hconj : ∀ (x : G) (j : ℤ), e * x ^ j * e⁻¹ = (e * x * e⁻¹) ^ j := fun x j => by
    have := map_zpow (MulAut.conj e) x j
    simpa [MulAut.conj_apply] using this
  have hE3 : e * e * e = 1 := by
    rw [← pow_three']
    exact hE.2 e he
  have h3 : e * (e * (e * γ * e⁻¹) * e⁻¹) * e⁻¹ = γ := by
    have : e * (e * (e * γ * e⁻¹) * e⁻¹) * e⁻¹ = (e * e * e) * γ * (e * e * e)⁻¹ := by group
    rw [this, hE3]
    group
  have s1 : e * γ * e⁻¹ = γ ^ k := hk.symm
  have s2 : e * (e * γ * e⁻¹) * e⁻¹ = (γ ^ k) ^ k := by
    rw [s1, hconj γ k, s1]
  have s3 : e * (e * (e * γ * e⁻¹) * e⁻¹) * e⁻¹ = ((γ ^ k) ^ k) ^ k := by
    rw [s2, hconj (γ ^ k) k, hconj γ k, s1]
  have hk3 : ((γ ^ k) ^ k) ^ k = γ ^ (k ^ 3) := by
    rw [← zpow_mul, ← zpow_mul]
    congr 1
    ring
  have hcube : γ ^ (k ^ 3) = γ := by
    rw [← hk3]
    exact s3.symm.trans h3
  have hdvd3 : (orderOf γ : ℤ) ∣ k ^ 3 - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, hcube, zpow_one, mul_inv_cancel]
  rw [hord] at hdvd3
  have hdvd1 : (orderOf γ : ℤ) ∣ k - 1 := by
    rw [hord]
    exact int_cube_sub_one_dvd hdvd3
  have hγk : γ ^ k = γ := by
    have : γ ^ (k - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one]
      exact hdvd1
    rw [zpow_sub, zpow_one] at this
    calc γ ^ k = γ ^ k * γ⁻¹ * γ := by group
      _ = γ := by rw [this, one_mul]
  have hcomm : Commute e γ := by
    show e * γ = γ * e
    have h := hk
    rw [hγk] at h
    calc e * γ = (e * γ * e⁻¹) * e := by group
      _ = γ * e := by rw [← h]
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨t, ht⟩)
  have hjt : γ ^ j = t := by
    have := congrArg Subtype.val hj
    simpa using this
  rw [← hjt]
  exact (hcomm.zpow_right j).symm.eq

end Cyclic

section Minimal

def centralInvol {G : Type} [Group G] (T₀ : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ T₀ ∧ (∀ t ∈ T₀, t * x = x * t) ∧ x ^ 2 = 1}
  mul_mem' := by
    rintro x y ⟨hx, hxc, hx2⟩ ⟨hy, hyc, hy2⟩
    refine ⟨T₀.mul_mem hx hy, fun t ht => ?_, ?_⟩
    · rw [← mul_assoc, hxc t ht, mul_assoc, hyc t ht, ← mul_assoc]
    · have hc : Commute x y := hyc x hx
      rw [(hc.mul_pow 2), hx2, hy2, one_mul]
  one_mem' := ⟨T₀.one_mem, fun t _ => by simp, by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hxc, hx2⟩
    refine ⟨T₀.inv_mem hx, fun t ht => ?_, by rw [inv_pow, hx2, inv_one]⟩
    have hc : Commute t x := hxc t ht
    exact (hc.inv_right).eq

theorem mem_centralInvol {G : Type} [Group G] {T₀ : Subgroup G} {x : G} :
    x ∈ centralInvol T₀ ↔ x ∈ T₀ ∧ (∀ t ∈ T₀, t * x = x * t) ∧ x ^ 2 = 1 := Iff.rfl

theorem exists_ne_one_centralInvol {G : Type} [Group G] [Finite G] {T₀ : Subgroup G}
    (hT₀ : IsPGroup 2 T₀) (hne : T₀ ≠ ⊥) : ∃ x ∈ centralInvol T₀, x ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥T₀ := (Subgroup.nontrivial_iff_ne_bot T₀).2 hne
  haveI : Nontrivial ↥(Subgroup.center ↥T₀) := hT₀.center_nontrivial
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥T₀) := hT₀.to_subgroup (Subgroup.center ↥T₀)
  obtain ⟨n, hn, hcard⟩ := (hZ2.nontrivial_iff_card).1 inferInstance
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.center ↥T₀) := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    norm_num at hx
  refine ⟨(x : ↥T₀).1, ⟨(x : ↥T₀).2, fun t ht => ?_, ?_⟩, fun h => hx1 ?_⟩
  · have := Subgroup.mem_center_iff.1 x.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  · have := congrArg (fun y : ↥(Subgroup.center ↥T₀) => ((y : ↥T₀) : G)) hx2
    simpa using this
  · apply Subtype.ext
    apply Subtype.ext
    simpa using h

end Minimal

section Main

theorem mem_normalizer_of_invariant {G : Type} [Group G] {E U : Subgroup G}
    (hnorm : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U) {x : G} (hx : x ∈ E) :
    x ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hnorm x hx h hh
  · intro hh
    have := hnorm x⁻¹ (E.inv_mem hx) _ hh
    simpa [mul_assoc] using this

theorem exists_minimal_invariant {G : Type} [Group G] [Finite G] {E V : Subgroup G}
    (hV : V ≠ ⊥) (hVinv : ∀ e ∈ E, ∀ v ∈ V, e * v * e⁻¹ ∈ V) :
    ∃ U : Subgroup G, U ≤ V ∧ U ≠ ⊥ ∧ (∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U) ∧
      ∀ W : Subgroup G, W ≤ U → (∀ e ∈ E, ∀ w ∈ W, e * w * e⁻¹ ∈ W) → W = ⊥ ∨ W = U := by
  classical
  let P : ℕ → Prop := fun n => ∃ U : Subgroup G, U ≤ V ∧ U ≠ ⊥ ∧
    (∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U) ∧ Nat.card U = n
  have hP : ∃ n, P n := ⟨Nat.card V, V, le_rfl, hV, hVinv, rfl⟩
  obtain ⟨U, hUV, hUne, hUinv, hUcard⟩ := Nat.find_spec hP
  refine ⟨U, hUV, hUne, hUinv, fun W hWU hWinv => ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    have hle : Nat.find hP ≤ Nat.card W :=
      Nat.find_min' hP ⟨W, hWU.trans hUV, hW, hWinv, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hWU (by omega)

theorem isElemAbelian_two_of_le {G : Type} [Group G] {T₀ U : Subgroup G}
    (hU : U ≤ centralInvol T₀) : IsElemAbelian 2 U := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => (hU hx).2.2⟩
  exact ((hU a.2).2.1 b (hU b.2).1).symm

theorem inner_inf_eq_bot {S : Type} [Group S] [Finite S] {E : Subgroup (MulAut S)}
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3) (hnot : ¬ E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S)
    (hE0 : Nat.card ↥(E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S) = 3 ^ 2) (h1 : SmallF1 S E) (h2 : SmallF2 S E)
    (T : Subgroup (MulAut S)) (hT : IsPGroup 2 T)
    (hN : E ≤ Subgroup.normalizer (T : Set (MulAut S))) : T ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S = ⊥ := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  by_contra hne
  set T₀ : Subgroup (MulAut S) := T ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S with hT₀def
  have hT₀ : IsPGroup 2 T₀ := hT.to_le inf_le_left
  have hT₀inv : ∀ e ∈ E, ∀ x ∈ T₀, e * x * e⁻¹ ∈ T₀ := by
    intro e he x hx
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hN he) x).1 hx.1,
      (inferInstance : (CFSG.ComponentClassification.OuterAutomorphisms.inner S).Normal).conj_mem x hx.2 e⟩
  have hCinv : ∀ e ∈ E, ∀ x ∈ centralInvol T₀, e * x * e⁻¹ ∈ centralInvol T₀ := by
    intro e he x hx
    obtain ⟨hxT, hxc, hx2⟩ := hx
    refine ⟨hT₀inv e he x hxT, fun t ht => ?_, ?_⟩
    · have ht' : e⁻¹ * t * e ∈ T₀ := by
        have := hT₀inv e⁻¹ (E.inv_mem he) t ht
        simpa using this
      have hc : (e⁻¹ * t * e) * x = x * (e⁻¹ * t * e) := hxc _ ht'
      calc t * (e * x * e⁻¹) = e * (e⁻¹ * t * e) * x * e⁻¹ := by group
        _ = e * ((e⁻¹ * t * e) * x) * e⁻¹ := by group
        _ = e * (x * (e⁻¹ * t * e)) * e⁻¹ := by rw [hc]
        _ = (e * x * e⁻¹) * t := by group
    · calc (e * x * e⁻¹) ^ 2 = e * x ^ 2 * e⁻¹ := by rw [sq, sq]; group
        _ = 1 := by rw [hx2]; group
  obtain ⟨x₀, hx₀, hx₀ne⟩ := exists_ne_one_centralInvol hT₀ hne
  have hVne : centralInvol T₀ ≠ ⊥ := by
    intro h
    apply hx₀ne
    have : x₀ ∈ (⊥ : Subgroup (MulAut S)) := h ▸ hx₀
    exact Subgroup.mem_bot.1 this
  obtain ⟨U, hUle, hUne, hUnorm, hUirr⟩ := exists_minimal_invariant hVne hCinv
  have hUel : IsElemAbelian 2 U := isElemAbelian_two_of_le hUle
  have hUN : U ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S := fun x hx => (hUle hx).1.2
  have hUp : IsPGroup 2 U := isPGroup_of_isElemAbelian hUel
  have hcardU := KDRank3SmallMod.card_centralizer_ge_nine hE hEcard hUel hUne hUnorm hUirr
  have h9 : Nat.card ↥(E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S) = 9 := by rw [hE0]; norm_num
  have h9' : 9 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (U : Set (MulAut S))) := by
    have : (3 : ℕ) ^ 2 = 9 := by norm_num
    omega
  by_cases hsub : E ⊓ Subgroup.centralizer (U : Set (MulAut S)) ≤ E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S
  · have heq : E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S = E ⊓ Subgroup.centralizer (U : Set (MulAut S)) :=
      (Subgroup.eq_of_le_of_card_ge hsub (by omega)).symm
    have hEN_C : E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S ≤ Subgroup.centralizer (U : Set (MulAut S)) := by
      rw [heq]
      exact inf_le_right
    exact hUne (h2 U hUp hUN hEN_C)
  · obtain ⟨b, hbmem, hbN⟩ := SetLike.not_le_iff_exists.1 hsub
    obtain ⟨hbE, hbC⟩ := hbmem
    have hbN' : b ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S := fun h => hbN ⟨hbE, h⟩
    have hUC : U ≤ Subgroup.centralizer ({b} : Set (MulAut S)) := by
      intro u hu
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hbC) u hu
    exact h1 b hbE hbN' U hUp hUne hUN hUC
      (fun x hx => mem_normalizer_of_invariant hUnorm hx.1)

theorem twoSub_eq_bot {S : Type} [Group S] [Finite S] {E : Subgroup (MulAut S)}
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3) (hnot : ¬ E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S)
    (hE0 : Nat.card ↥(E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S) = 3 ^ 2) (h1 : SmallF1 S E) (h2 : SmallF2 S E)
    (h3 : SmallF3 S) (T : Subgroup (MulAut S)) (hT : IsPGroup 2 T)
    (hN : E ≤ Subgroup.normalizer (T : Set (MulAut S)))
    (hcomm : (⁅T, E⁆ : Subgroup (MulAut S)) = T) : T = ⊥ := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  have hTN := inner_inf_eq_bot hE hEcard hnot hE0 h1 h2 T hT hN
  let φ : ↥T →* Outer S := (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S)).comp T.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : MulAut S) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S := (QuotientGroup.eq_one_iff _).1 hx
    have hmem : (x : MulAut S) ∈ T ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S := ⟨x.2, hx'⟩
    rw [hTN] at hmem
    exact Subtype.ext (Subgroup.mem_bot.1 hmem)
  have hPh : IsPGroup 2 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact (hT.to_subgroup ⊤).map φ
  have hcycT : IsCyclic ↥T := (MulEquiv.isCyclic (MonoidHom.ofInjective hφ)).2 (h3 _ hPh)
  have hEC : E ≤ Subgroup.centralizer (T : Set (MulAut S)) :=
    centralizes_of_isCyclic_two hE hT hcycT hN
  have hTE : T ≤ Subgroup.centralizer (E : Set (MulAut S)) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.1 (hEC he) t ht).symm
  have hbot : (⁅T, E⁆ : Subgroup (MulAut S)) = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 hTE
  rw [hbot] at hcomm
  exact hcomm.symm

end Main

end KDRank3SmallAbs

end CFSG.LocalAnalysis.GLTheoremA
