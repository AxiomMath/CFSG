module

public import CFSG.ClassicalInvolution.Balance.BootstrapBootTriple
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

section FixedPoint

variable {G : Type*} [Group G]

theorem exists_conj_fixed_of_isPGroup {A N : Subgroup G} (hA : IsPGroup 2 A)
    (hN : Odd (Nat.card N)) (hAN : ∀ x ∈ A, ∀ n ∈ N, x * n * x⁻¹ ∈ N) {z : G} (hz : z * z = 1)
    (hzN : ∀ n ∈ N, z * n * z⁻¹ ∈ N) (hzA : ∀ x ∈ A, z * (x * z * x⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ x ∈ A, x * (n * z * n⁻¹) * x⁻¹ = n * z * n⁻¹ := by
  classical
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set S : Set G := {u | u * u = 1 ∧ z * u ∈ N} with hS
  let _ : MulAction N G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have hsmul : ∀ (o : N) (g : G), o • g = (o : G) * g * (o : G)⁻¹ := fun o g => by
    show ConjAct.toConjAct (o : G) • g = _
    rw [ConjAct.smul_def]
    rfl
  have hSorb : S = MulAction.orbit N z := by
    ext u
    constructor
    · rintro ⟨hu, hzu⟩
      obtain ⟨o, ho, hzo⟩ := exists_conj_of_mul_mem hu hz hN hzu
      refine ⟨⟨o⁻¹, N.inv_mem ho⟩, ?_⟩
      show (⟨o⁻¹, N.inv_mem ho⟩ : N) • z = u
      rw [hsmul]
      show o⁻¹ * z * o⁻¹⁻¹ = u
      rw [hzo]
      group
    · rintro ⟨o, rfl⟩
      show o • z ∈ S
      rw [hsmul]
      refine ⟨?_, ?_⟩
      · calc _ = (o : G) * (z * z) * (o : G)⁻¹ := by group
          _ = 1 := by rw [hz]; group
      · have h1 := N.mul_mem (hzN o o.2) (N.inv_mem o.2)
        have e : z * ((o : G) * z * (o : G)⁻¹) = z * (o : G) * z⁻¹ * (o : G)⁻¹ := by
          rw [hzinv]
          group
        rw [e]
        exact h1
  have hodd : ¬ 2 ∣ Nat.card S := by
    rw [hSorb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer N z]
    have hd : (MulAction.stabilizer N z).index ∣ Nat.card N := Subgroup.index_dvd_card _
    intro h2
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (h2.trans hd))
  have hAS : ∀ x ∈ A, ∀ u ∈ S, x * u * x⁻¹ ∈ S := by
    rintro x hx u ⟨hu, hzu⟩
    refine ⟨?_, ?_⟩
    · calc _ = x * (u * u) * x⁻¹ := by group
        _ = 1 := by rw [hu]; group
    · have hw := N.mul_mem (hzA x hx) (hAN x hx _ hzu)
      have e : z * (x * u * x⁻¹) = z * (x * z * x⁻¹) * (x * (z * u) * x⁻¹) := by
        calc z * (x * u * x⁻¹) = z * (x * (z * (z * u)) * x⁻¹) := by
              rw [← mul_assoc z z u, hz, one_mul]
          _ = _ := by group
      rw [e]
      exact hw
  let _ : MulAction A S :=
    { smul := fun x u => ⟨(x : G) * u * (x : G)⁻¹, hAS x x.2 u u.2⟩
      one_smul := fun u => Subtype.ext
        (show ((1 : A) : G) * (u : G) * ((1 : A) : G)⁻¹ = u by simp)
      mul_smul := fun x y u => Subtype.ext
        (show ((x * y : A) : G) * (u : G) * ((x * y : A) : G)⁻¹ =
          (x : G) * ((y : G) * (u : G) * (y : G)⁻¹) * (x : G)⁻¹ by simp [mul_assoc]) }
  obtain ⟨u, hu⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card S hodd
  have hu' : (u : G) ∈ MulAction.orbit N z := hSorb ▸ u.2
  obtain ⟨o, ho⟩ := hu'
  have ho' : o • z = (u : G) := ho
  rw [hsmul] at ho'
  refine ⟨o, o.2, fun x hx => ?_⟩
  rw [ho']
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hu ⟨x, hx⟩)

end FixedPoint

section Lemmas

open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem members_eq_or_commute {L L' : Subgroup G} {w : G} (hL : IsClassicalMember p f L w)
    (hL' : IsClassicalMember p f L' w) (hqL : CFSG.Open.IsQuasisimple L)
    (hqL' : CFSG.Open.IsQuasisimple L') : L = L' ∨ Commutes L L' := by
  have hc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({w} : Set G)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mpr
      ⟨isSubnormal_le hL.subnormal, hL.subnormal, hqL⟩
  have hc' : CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer ({w} : Set G)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mpr
      ⟨isSubnormal_le hL'.subnormal, hL'.subnormal, hqL'⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hc hc' with h | h
  · exact Or.inl h
  · refine Or.inr fun x hx y hy => ?_
    have h1 : ⁅x, y⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

omit [Finite G] in
theorem isQuasisimple_of_mem_exactMembers (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {L : Subgroup G} (hL : L ∈ Ω) : CFSG.Open.IsQuasisimple L := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex L hL)
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]
    omega
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e
    (isQuasisimple_specialLinearGroup_two h4)

omit [Finite G] in
theorem oddQuotMk_eq_one_of_mem_oddCoreIn {a n : G}
    (hn : n ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)))
    (hnC : n ∈ Subgroup.centralizer ({a} : Set G)) : oddQuotMk a ⟨n, hnC⟩ = 1 := by
  obtain ⟨n', hn', hn'e⟩ := hn
  have : n' = ⟨n, hnC⟩ := Subtype.ext hn'e
  rw [← this]
  exact oddQuotMk_eq_one_iff.mpr hn'

omit [Finite G] in
theorem oddQuotMk_centralizes_of_closure {a : G} {L : Subgroup (OddQuot a)} {𝒵 : Set G}
    (h𝒵 : ∀ z ∈ 𝒵, ∃ hzC : z ∈ Subgroup.centralizer ({a} : Set G),
      ∀ y ∈ L, oddQuotMk a ⟨z, hzC⟩ * y = y * oddQuotMk a ⟨z, hzC⟩)
    {g : G} (hg : g ∈ Subgroup.closure 𝒵) (hgC : g ∈ Subgroup.centralizer ({a} : Set G))
    (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨g, hgC⟩ * y = y * oddQuotMk a ⟨g, hgC⟩ := by
  let Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))).comap (oddQuotMk a)
  have hsub : Subgroup.closure 𝒵 ≤ Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    obtain ⟨hzC, hcomm⟩ := h𝒵 z hz
    refine ⟨⟨z, hzC⟩, ?_, rfl⟩
    show oddQuotMk a _ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm y hy).symm
  obtain ⟨q, hq, hqg⟩ := hsub hg
  have hqe : q = ⟨g, hgC⟩ := Subtype.ext hqg
  subst hqe
  exact (Subgroup.mem_centralizer_iff.mp hq y hy).symm

end Lemmas

section Main

open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_centralized_component_of_not_inCommonComponent (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {A : Subgroup G}
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) {a : G} (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) {K : Subgroup G} (hK : K ∈ centMembers Ω a)
    (hKL : ∀ L ∈ frameFamily p f Ω A, ¬ InCommonComponent a K L) :
    ∃ Q : Subgroup (OddQuot a), CFSG.IsComponent Q ∧ modOdd a K ≤ Q ∧
      ∀ x, x ∈ A → ∀ (hxC : x ∈ Subgroup.centralizer ({a} : Set G)), ∀ y ∈ Q,
        oddQuotMk a ⟨x, hxC⟩ * y = y * oddQuotMk a ⟨x, hxC⟩ := by
  classical
  have hnorm : (memberJoin Ω a).Normal := memberJoin_normal hΩ.conjInvariant
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2 ModelFacts.modelClauseZero
    fundamentalWholeA1 hΩ hIH hnc
  obtain ⟨i, hi⟩ := D.exists_le _ (⟨K, hK, rfl⟩ : modOdd a K ∈ memberImages Ω a)
  have hQi : CFSG.IsComponent (D.Q i) := (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i)
  have hcom : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hAC : ∀ {x : G}, x ∈ A → x ∈ Subgroup.centralizer ({a} : Set G) := fun hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcom hx ha)
  have hFC : ∀ {L : Subgroup G}, L ∈ frameFamily p f Ω A →
      L ≤ Subgroup.centralizer ({a} : Set G) := fun hL =>
    hL.2.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  refine ⟨D.Q i, hQi, hi, ?_⟩
  intro g hg hgC y hy
  refine oddQuotMk_centralizes_of_closure
    (𝒵 := {z | ∃ L ∈ frameFamily p f Ω A, IsClassicalMember p f L z}) ?_ ?_ hgC y hy
  · rintro z ⟨L, hL, hz⟩
    have hzA := hM.mem_of_isClassicalMember hL hz
    refine ⟨hAC hzA, fun y hy => ?_⟩
    obtain ⟨j, hj⟩ := D.exists_le _
      (⟨L, ⟨hL.1, hFC hL⟩, rfl⟩ : modOdd a L ∈ memberImages Ω a)
    have hne : i ≠ j := by
      rintro rfl
      exact hKL L hL ⟨D.Q i, hQi, hi, hj⟩
    exact (D.commute i j hne y hy _ (hj (oddQuotMk_mem_modOdd hz.mem (hAC hzA)))).symm
  · rw [← hM.generate]
    exact hg

theorem exists_member_centralizing_of_not_familyMeetsAt (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω) {A : Subgroup G}
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) {a : G} (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) (hnot : ¬ FamilyMeetsAt p f Ω A a) :
    ∃ M ∈ Ω, M ≤ Subgroup.centralizer (A : Set G) ∧
      ∃ z : G, IsClassicalMember p f M z ∧ z ∉ A := by
  classical
  obtain ⟨K, hK, hKL⟩ : ∃ K ∈ centMembers Ω a,
      ∀ L ∈ frameFamily p f Ω A, ¬ InCommonComponent a K L := by
    by_contra hcon
    apply hnot
    intro K hK
    by_contra h'
    exact hcon ⟨K, hK, fun L hL hcc => h' ⟨L, hL, hcc⟩⟩
  obtain ⟨Q, hQ, hi, hgen⟩ :=
    exists_centralized_component_of_not_inCommonComponent hp2 hΩ hIH hM ha hnc hK hKL
  have hcom : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hAC : ∀ {x : G}, x ∈ A → x ∈ Subgroup.centralizer ({a} : Set G) := fun hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcom hx ha)
  have hApg : IsPGroup 2 A := IsPGroup.of_card (n := 3) (by rw [hM.card]; norm_num)
  have hcommN : ∀ x ∈ A, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈
      oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
    intro x hx k hk
    have hkC : k ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hk
    exact (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) (hAC hx) hkC).mp
      (hgen x hx (hAC hx) _ (hi (oddQuotMk_mem_modOdd hk hkC)))
  obtain ⟨z, hz⟩ := hΩ.classical K hK.1
  have hzC : z ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hz.mem
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (sq_eq_one hz)
  obtain ⟨n, hnN, hfix⟩ := exists_conj_fixed_of_isPGroup (A := A)
    (N := oddCoreIn (Subgroup.centralizer ({a} : Set G))) hApg
    (odd_card_oddCoreIn _) (fun x hx m hm => conj_mem_oddCoreIn (hAC hx) hm) (sq_eq_one hz)
    (fun m hm => conj_mem_oddCoreIn hzC hm) (by
      intro x hx
      have h1 := (oddCoreIn _).inv_mem (hcommN x hx z hz.mem)
      have e : z * (x * z * x⁻¹) = (x * z * x⁻¹ * z⁻¹)⁻¹ := by
        have h2 : (x * z * x⁻¹ * z⁻¹)⁻¹ = z * x * z⁻¹ * x⁻¹ := by group
        rw [h2, hzinv]
        group
      rw [e]
      exact h1)
  have hnC : n ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hnN
  have hn1 : oddQuotMk a ⟨n, hnC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn hnN hnC
  have hK'Ω : conjSub n K ∈ Ω := hΩ.conjInvariant n K hK.1
  have hK'C : conjSub n K ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    have h1 : n⁻¹ * y * n ∈ K := mem_conjSub_iff.mp hy
    have e : y = n * (n⁻¹ * y * n) * n⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnC (hK.2 h1)) (Subgroup.inv_mem _ hnC)
  have hz' : IsClassicalMember p f (conjSub n K) (n * z * n⁻¹) := hz.conj n
  have himg : ∀ (y : G) (hy : y ∈ conjSub n K) (hyC : y ∈ Subgroup.centralizer ({a} : Set G)),
      ∃ k ∈ K, ∃ hkC : k ∈ Subgroup.centralizer ({a} : Set G),
        oddQuotMk a ⟨y, hyC⟩ = oddQuotMk a ⟨k, hkC⟩ := by
    intro y hy hyC
    have hk : n⁻¹ * y * n ∈ K := mem_conjSub_iff.mp hy
    have hkC : n⁻¹ * y * n ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hk
    refine ⟨n⁻¹ * y * n, hk, hkC, ?_⟩
    have e : (⟨y, hyC⟩ : Subgroup.centralizer ({a} : Set G)) =
        ⟨n, hnC⟩ * ⟨n⁻¹ * y * n, hkC⟩ * ⟨n, hnC⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
    rw [e, map_mul, map_mul, map_inv, hn1]
    simp
  have hcommN' : ∀ x ∈ A, ∀ y ∈ conjSub n K,
      x * y * x⁻¹ * y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
    intro x hx y hy
    have hyC := hK'C hy
    obtain ⟨k, hk, hkC, hyk⟩ := himg y hy hyC
    refine (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) (hAC hx) hyC).mp ?_
    have h1 := hgen x hx (hAC hx) _ (hi (oddQuotMk_mem_modOdd hk hkC))
    rw [← hyk] at h1
    exact h1
  have hKbot : conjSub n K ⊓ oddCoreIn (Subgroup.centralizer ({a} : Set G)) = ⊥ := by
    have hle : conjSub n K ⊓ oddCoreIn (Subgroup.centralizer ({a} : Set G)) ≤
        oddCoreIn (conjSub n K) := by
      refine le_oddCoreIn_of_normalizes inf_le_left ?_
        ((odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro s
      have hkinv : k⁻¹ ∈ conjSub n K := Subgroup.inv_mem _ hk
      have hkC := hK'C hk
      have hkinvC := hK'C hkinv
      constructor
      · rintro ⟨hs1, hs2⟩
        exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hs1) hkinv,
          conj_mem_oddCoreIn hkC hs2⟩
      · rintro ⟨hs1, hs2⟩
        have e : s = k⁻¹ * (k * s * k⁻¹) * k := by group
        rw [e]
        refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hkinv hs1) hk, ?_⟩
        have := conj_mem_oddCoreIn hkinvC hs2
        simpa [mul_assoc] using this
    have hOK' : oddCoreIn (conjSub n K) = ⊥ := by
      have h' : componentClassificationOddCore (conjSub n K) = ⊥ := hex _ hK'Ω
      show (componentClassificationOddCore (conjSub n K)).map (conjSub n K).subtype = ⊥
      rw [h']
      exact Subgroup.map_bot _
    exact le_bot_iff.mp (hle.trans hOK'.le)
  have hKcent : conjSub n K ≤ Subgroup.centralizer (A : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hxA
    have hx : x ∈ A := hxA
    have hK''Ω : conjSub x (conjSub n K) ∈ Ω := hΩ.conjInvariant x _ hK'Ω
    have hz'' : IsClassicalMember p f (conjSub x (conjSub n K)) (n * z * n⁻¹) := by
      have := hz'.conj x
      rwa [hfix x hx] at this
    rcases members_eq_or_commute hz'' hz' (isQuasisimple_of_mem_exactMembers hq hΩ hex hK''Ω)
      (isQuasisimple_of_mem_exactMembers hq hΩ hex hK'Ω) with heq | hcomm
    ·
      have h1 : x * y * x⁻¹ ∈ conjSub n K := heq ▸ conj_mem_conjSub hy
      have h2 : x * y * x⁻¹ * y⁻¹ ∈ conjSub n K ⊓ oddCoreIn (Subgroup.centralizer ({a} : Set G)) :=
        ⟨Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy), hcommN' x hx y hy⟩
      rw [hKbot, Subgroup.mem_bot] at h2
      calc x * y = x * y * x⁻¹ * y⁻¹ * y * x := by group
        _ = y * x := by rw [h2]; group
    ·
      exfalso
      have hperf : ⁅conjSub n K, conjSub n K⁆ = conjSub n K := by
        have := hz'.perfect
        exact Subgroup.commutator_eq_self
      have hle : conjSub n K ≤ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
        rw [← hperf]
        refine Subgroup.commutator_le.mpr fun k₁ hk₁ k₂ hk₂ => ?_
        have hc := hcommN' x hx k₁ hk₁
        have hconj := conj_mem_oddCoreIn (hK'C hk₂) hc
        have h2 := hcomm _ (conj_mem_conjSub hk₁) k₂ hk₂
        have h3 : (x * k₁ * x⁻¹)⁻¹ * k₂ * (x * k₁ * x⁻¹) = k₂ := by
          calc _ = (x * k₁ * x⁻¹)⁻¹ * (k₂ * (x * k₁ * x⁻¹)) := by group
            _ = (x * k₁ * x⁻¹)⁻¹ * ((x * k₁ * x⁻¹) * k₂) := by rw [h2]
            _ = k₂ := by group
        have e : ⁅k₁, k₂⁆ = (x * k₁ * x⁻¹ * k₁⁻¹)⁻¹ * (k₂ * (x * k₁ * x⁻¹ * k₁⁻¹) * k₂⁻¹) := by
          calc ⁅k₁, k₂⁆ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := rfl
            _ = k₁ * ((x * k₁ * x⁻¹)⁻¹ * k₂ * (x * k₁ * x⁻¹)) * k₁⁻¹ * k₂⁻¹ := by rw [h3]
            _ = _ := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hconj
      exact hz'.ne_one (eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn _)
        (hle hz'.mem) (sq_eq_one hz'))
  refine ⟨conjSub n K, hK'Ω, hKcent, n * z * n⁻¹, hz', fun hzA => ?_⟩
  refine hKL (conjSub n K) ⟨hK'Ω, hKcent, _, hzA, hz'⟩ ⟨Q, hQ, hi, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨k, hk, hkC, hyk⟩ := himg (y' : G) hy' y'.2
  show oddQuotMk a ⟨(y' : G), y'.2⟩ ∈ Q
  rw [hyk]
  exact hi (oddQuotMk_mem_modOdd hk hkC)

@[expose] def FrameSaturated (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (A : Subgroup G) :
    Prop :=
  ∀ M ∈ Ω, M ≤ Subgroup.centralizer (A : Set G) → ∀ z : G, IsClassicalMember p f M z → z ∈ A

theorem familyMeetsAt_of_saturated (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω) {A : Subgroup G}
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) (hsat : FrameSaturated p f Ω A) {a : G}
    (ha : a ∈ A) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) : FamilyMeetsAt p f Ω A a := by
  by_contra hnot
  obtain ⟨M, hMΩ, hMA, z, hz, hzA⟩ :=
    exists_member_centralizing_of_not_familyMeetsAt hp2 hq hΩ hIH hex hM ha hnc hnot
  exact hzA (hsat M hMΩ hMA z hz)

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
