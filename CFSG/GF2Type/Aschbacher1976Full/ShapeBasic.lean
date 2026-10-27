module

public import CFSG.GF2Type.Aschbacher1976Full.Defs
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Permutation.FiveTransitive.CoprimeAutomorphismDisplacement
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalizerComplement

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.Blueprint Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Fz_le_Hz (z : G) : Fz z ≤ Hz z := Subgroup.map_subtype_le _

theorem mem_Hz {z x : G} : x ∈ Hz z ↔ x * z = z * x := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact eq_comm

theorem Fz_conj_mem (z : G) {h x : G} (hh : h ∈ Hz z) (hx : x ∈ Fz z) : h * x * h⁻¹ ∈ Fz z := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hN : (generalizedFitting ↥(Hz z)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥(Hz z))).2
  exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hN.conj_mem y hy _, rfl⟩

theorem cent_le_Fz (z : G) {h : G} (hh : h ∈ Hz z) (hc : ∀ x ∈ Fz z, h * x = x * h) :
    h ∈ Fz z := by
  have hmem : (⟨h, hh⟩ : ↥(Hz z)) ∈
      Subgroup.centralizer (generalizedFitting ↥(Hz z) : Set ↥(Hz z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (hc y (Subgroup.mem_map_of_mem _ hy)).symm
  exact Subgroup.mem_map.mpr ⟨_, centralizer_generalizedFitting_le _ hmem, rfl⟩

theorem z_mem_Hz (z : G) : z ∈ Hz z := mem_Hz.mpr rfl

theorem z_mem_Fz (z : G) : z ∈ Fz z :=
  cent_le_Fz z (z_mem_Hz z) fun x hx => (mem_Hz.mp (Fz_le_Hz z hx)).symm

theorem Fz_comm_z (z : G) {x : G} (hx : x ∈ Fz z) : x * z = z * x := mem_Hz.mp (Fz_le_Hz z hx)

theorem genFit_eq_pCore (z : G) (hF2 : IsPGroup 2 ↥(Fz z)) :
    generalizedFitting ↥(Hz z) = pCore 2 ↥(Hz z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (generalizedFitting ↥(Hz z)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥(Hz z))).2
  have hgp : IsPGroup 2 ↥(generalizedFitting ↥(Hz z)) :=
    hF2.of_equiv
      ((generalizedFitting ↥(Hz z)).equivMapOfInjective (Hz z).subtype
        (Hz z).subtype_injective).symm
  have hle : generalizedFitting ↥(Hz z) ≤ pCore 2 ↥(Hz z) := le_sSup ⟨hN, hgp⟩
  refine ((isCharacteristicP_iff_generalizedFitting_eq_pCore ↥(Hz z) 2).mp ?_)
  intro y hy
  refine hle (centralizer_generalizedFitting_le _ ?_)
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  exact fun x hx => hy x (hle hx)

theorem le_Fz_of_normalized_isPGroup {z : G} (hF2 : IsPGroup 2 ↥(Fz z)) {N : Subgroup G}
    (hNH : N ≤ Hz z) (hN : ∀ h ∈ Hz z, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hp : IsPGroup 2 ↥N) :
    N ≤ Fz z := by
  have hnorm : (N.subgroupOf (Hz z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact hN g g.2 n hn
  have hrestr : IsPGroup 2 ↥(N.subgroupOf (Hz z)) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf (Hz z) ≤ generalizedFitting ↥(Hz z) := by
    rw [genFit_eq_pCore z hF2]
    exact le_sSup ⟨hnorm, hrestr⟩
  intro n hn
  exact Subgroup.mem_map.mpr ⟨⟨n, hNH hn⟩, hle hn, rfl⟩

theorem Hz_eq_Fz_of_isPGroup {z : G} (hF2 : IsPGroup 2 ↥(Fz z)) (hH : IsPGroup 2 ↥(Hz z)) :
    Hz z = Fz z :=
  le_antisymm
    (le_Fz_of_normalized_isPGroup hF2 le_rfl
      (fun h hh n hn => mul_mem (mul_mem hh hn) (inv_mem hh)) hH)
    (Fz_le_Hz z)

theorem Hz_le_normalizer (z : G) : Hz z ≤ Subgroup.normalizer ((Fz z : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => Fz_conj_mem z hh hx, fun hx => ?_⟩
  have := Fz_conj_mem z (inv_mem hh) hx
  convert this using 1
  group

@[expose] noncomputable def actF (z : G) : ↥(Hz z) →* MulAut ↥(Fz z) :=
  (Fz z).normalizerMonoidHom.comp (Subgroup.inclusion (Hz_le_normalizer z))

theorem eq_one_of_odd_orderOf {P : Type*} [Group P] (hP : IsPGroup 2 P) {g : P}
    (hodd : Odd (orderOf g)) : g = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP) g
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra hne
    exact (Nat.not_odd_iff_even.mpr (by rw [Nat.even_pow]; exact ⟨even_two, hne⟩)) hodd
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

theorem eq_one_of_stable {z : G} (hF2 : IsPGroup 2 ↥(Fz z)) {u : G} (hu : u ∈ Hz z)
    (hodd : Odd (orderOf u)) {N : Subgroup ↥(Fz z)} [N.Normal]
    (hfix : ∀ n : ↥(Fz z), n ∈ N → u * (n : G) * u⁻¹ = n)
    (hq : ∀ x : ↥(Fz z), ∃ n : ↥(Fz z), n ∈ N ∧ u * (x : G) * u⁻¹ = x * n) : u = 1 := by
  set a : MulAut ↥(Fz z) := actF z ⟨u, hu⟩ with ha
  have hak : a ^ (orderOf u) = 1 := by
    rw [ha, ← map_pow]
    have : (⟨u, hu⟩ : ↥(Hz z)) ^ orderOf u = 1 := by
      rw [← Subgroup.orderOf_mk u hu]
      exact pow_orderOf_eq_one _
    rw [this, map_one]
  have hNp : IsPGroup 2 ↥N := hF2.to_subgroup N
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp hNp)
  have hcop : (orderOf u).Coprime (Nat.card N) := by
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  have h1 : a = 1 := by
    refine FiveTransitive.CoprimeAutomorphismDisplacement.eq_one_of_quotient N a (orderOf u) hak
      hcop (fun n hn => Subtype.ext (hfix n hn)) (fun x => ?_)
    obtain ⟨n, hn, hxn⟩ := hq x
    have : a x = x * n := Subtype.ext hxn
    rw [this, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa using N.inv_mem hn
  have hc : ∀ x ∈ Fz z, u * x = x * u := by
    intro x hx
    have := congrArg (fun f : MulAut ↥(Fz z) => ((f ⟨x, hx⟩ : ↥(Fz z)) : G)) h1
    have h2 : u * x * u⁻¹ = x := this
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have huF : u ∈ Fz z := cent_le_Fz z hu hc
  have : (⟨u, huF⟩ : ↥(Fz z)) = 1 :=
    eq_one_of_odd_orderOf hF2 (by rw [Subgroup.orderOf_mk]; exact hodd)
  exact congrArg Subtype.val this

theorem fixes_of_cyclic {z : G} (hF2 : IsPGroup 2 ↥(Fz z)) {u : G} (hu : u ∈ Hz z)
    (hodd : Odd (orderOf u)) {Z : Subgroup ↥(Fz z)} [Z.Characteristic] (hZ : IsCyclic Z) :
    ∀ c : ↥(Fz z), c ∈ Z → u * (c : G) * u⁻¹ = c := by
  set a : MulAut ↥(Fz z) := actF z ⟨u, hu⟩ with ha
  have hZp : IsPGroup 2 ↥Z := hF2.to_subgroup Z
  have hA : IsPGroup 2 (MulAut ↥Z) :=
    CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup ↥Z hZp
  set φ : MulAut ↥Z := FiveTransitive.CharacteristicAutomorphism.restrict Z a with hφ
  obtain ⟨n, hn⟩ := hA φ
  have hak : a ^ (orderOf u) = 1 := by
    rw [ha, ← map_pow]
    have : (⟨u, hu⟩ : ↥(Hz z)) ^ orderOf u = 1 := by
      rw [← Subgroup.orderOf_mk u hu]
      exact pow_orderOf_eq_one _
    rw [this, map_one]
  have hφu : φ ^ (orderOf u) = 1 := by
    rw [hφ, ← map_pow, hak, map_one]
  have hcop : (2 ^ n).Coprime (orderOf u) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  have h1 : orderOf φ = 1 :=
    (Nat.coprime_self _).mp
      ((hcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hn)).coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one hφu))
  have hφ1 : φ = 1 := orderOf_eq_one_iff.mp h1
  intro c hc
  have := congrArg (fun f : MulAut ↥Z => (((f ⟨c, hc⟩ : ↥Z) : ↥(Fz z)) : G)) hφ1
  exact this

theorem isPGroup_two_of_forall_odd {H : Type*} [Group H] [Finite H]
    (h : ∀ u : H, Odd (orderOf u) → u = 1) : IsPGroup 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.iff_orderOf.mpr fun g => ?_
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨k, ?_⟩
  have hdvd : 2 ^ k ∣ orderOf g := ⟨m, hk⟩
  have h1 : orderOf (g ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hk]
    exact Nat.mul_div_cancel_left m (by positivity)
  have h2 : g ^ 2 ^ k = 1 := h _ (h1 ▸ hm)
  rw [h2, orderOf_one] at h1
  rw [hk, ← h1, mul_one]

theorem Hz_eq_Fz_of_odd {z : G} (hF2 : IsPGroup 2 ↥(Fz z))
    (h : ∀ u ∈ Hz z, Odd (orderOf u) → u = 1) : Hz z = Fz z := by
  refine Hz_eq_Fz_of_isPGroup hF2 (isPGroup_two_of_forall_odd fun u hu => ?_)
  refine Subtype.ext (h u u.2 ?_)
  rwa [← Subgroup.orderOf_coe] at hu

theorem mem_conjugate_iff {S : Subgroup G} {g x : G} : x ∈ conjugate S g ↔ g * x * g⁻¹ ∈ S := by
  unfold conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conjugate_eq_of_invariant {K S : Subgroup G} (hS : ∀ h ∈ K, ∀ x ∈ S, h * x * h⁻¹ ∈ S)
    {h : G} (hh : h ∈ K) : conjugate S h = S := by
  ext x
  rw [mem_conjugate_iff]
  refine ⟨fun hx => ?_, fun hx => hS h hh x hx⟩
  have := hS h⁻¹ (inv_mem hh) _ hx
  convert this using 1
  group

theorem char_conj_mem {z : G} {S : Subgroup ↥(Fz z)} [S.Characteristic] {h : G} (hh : h ∈ Hz z)
    {x : G} (hx : x ∈ S.map (Fz z).subtype) : h * x * h⁻¹ ∈ S.map (Fz z).subtype := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr
    ⟨actF z ⟨h, hh⟩ s, FiveTransitive.CharacteristicAutomorphism.mem S _ hs, rfl⟩

theorem eq_one_of_stable_cyclic {z : G} (hF2 : IsPGroup 2 ↥(Fz z)) {u : G} (hu : u ∈ Hz z)
    (hodd : Odd (orderOf u)) {Z : Subgroup ↥(Fz z)} [Z.Characteristic] (hZ : IsCyclic Z)
    (hfix : ∀ d : ↥(Fz z), (∀ y ∈ Z, y * d = d * y) → u * (d : G) * u⁻¹ = d) : u = 1 := by
  haveI : (Subgroup.centralizer (Z : Set ↥(Fz z))).Normal := Subgroup.normal_centralizer
  have hfixZ := fixes_of_cyclic hF2 hu hodd hZ
  refine eq_one_of_stable hF2 hu hodd (N := Subgroup.centralizer (Z : Set ↥(Fz z)))
    (fun n hn => hfix n (Subgroup.mem_centralizer_iff.mp hn)) (fun x => ?_)
  refine ⟨x⁻¹ * ⟨u * (x : G) * u⁻¹, Fz_conj_mem z hu x.2⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hy1 : (u : G)⁻¹ * y * u = y := by
      have := hfixZ y hy
      rw [mul_inv_eq_iff_eq_mul] at this
      calc (u : G)⁻¹ * y * u = u⁻¹ * (y * u) := by rw [mul_assoc]
        _ = u⁻¹ * (u * y) := by rw [this]
        _ = y := by group
    have hy2 := hfixZ (x * y * x⁻¹) (Subgroup.Normal.conj_mem inferInstance y hy x)
    have hy2' : u * ((x : G) * y * (x : G)⁻¹) * u⁻¹ = (x : G) * y * (x : G)⁻¹ := hy2
    change (y : G) * ((x : G)⁻¹ * (u * (x : G) * u⁻¹)) = ((x : G)⁻¹ * (u * (x : G) * u⁻¹)) * y
    have h3 : ((x : G)⁻¹ * (u * (x : G) * u⁻¹)) * y * ((x : G)⁻¹ * (u * (x : G) * u⁻¹))⁻¹ = y := by
      calc ((x : G)⁻¹ * (u * (x : G) * u⁻¹)) * y * ((x : G)⁻¹ * (u * (x : G) * u⁻¹))⁻¹
          = (x : G)⁻¹ * (u * ((x : G) * (u⁻¹ * y * u) * (x : G)⁻¹) * u⁻¹) * x := by group
        _ = (x : G)⁻¹ * (u * ((x : G) * y * (x : G)⁻¹) * u⁻¹) * x := by rw [hy1]
        _ = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x := by rw [hy2']
        _ = y := by group
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  · change u * (x : G) * u⁻¹ = (x : G) * ((x : G)⁻¹ * (u * (x : G) * u⁻¹))
    group

end CFSG.GF2Type.Aschbacher1976Full.Shape
