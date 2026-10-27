module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelGen

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rwa [show g * (g⁻¹ * h * g) * g⁻¹ = h by group]
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem isElemTwo_conjugate {H : Subgroup G} (hH : IsElemTwo H) (g : G) :
    IsElemTwo (conjugate H g) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h1 := hH.1 _ (mem_conjugate_iff.1 hx) _ (mem_conjugate_iff.1 hy)
    calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = y * x := by group
  · have h1 := hH.2 _ (mem_conjugate_iff.1 hx)
    calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = 1 := by rw [h1]; group

theorem card_conjugate (H : Subgroup G) (g : G) : Nat.card (conjugate H g) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_le {H J : Subgroup G} (hH : H ≤ J) {g : G} (hg : g ∈ J) :
    conjugate H g ≤ J := fun x hx => by
  have h1 := hH (mem_conjugate_iff.1 hx)
  have := J.mul_mem (J.mul_mem (J.inv_mem hg) h1) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem comm_conjugate {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (g : G) :
    ∀ x ∈ conjugate X g, ∀ y ∈ conjugate Y g, x * y = y * x := by
  intro x hx y hy
  have h1 := hc _ (mem_conjugate_iff.1 hx) _ (mem_conjugate_iff.1 hy)
  calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
    _ = y * x := by group

variable [Finite G] {J P : Subgroup G}

theorem exists_omegaZ (hP : IsSylowTwoIn P J) :
    ∃ K : Subgroup G, ∀ z, z ∈ K ↔ z ∈ P ⊓ zStarIn J ∧ z * z = 1 := by
  refine ⟨{ carrier := {z | z ∈ P ⊓ zStarIn J ∧ z * z = 1}
            one_mem' := ⟨one_mem _, mul_one 1⟩
            mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, ?_⟩
            inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ },
    fun z => Iff.rfl⟩
  have hab := comm_of_mem_Z hP ha.1 (mem_inf.mp hb.1).1
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = a * a * (b * b) := by group
    _ = 1 := by rw [ha.2, hb.2, one_mul]

theorem card_omegaZ
    {q : Jhat J →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat J} (hQ : IsQSetting q l)
    (hP : IsSylowTwoIn P J) (hcyc : ¬ IsCyclic ↥(P ⊓ zStarIn J)) {K : Subgroup G}
    (hK : ∀ z, z ∈ K ↔ z ∈ P ⊓ zStarIn J ∧ z * z = 1) : Nat.card K = 4 := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hKP : K ≤ P := fun z hz => (mem_inf.mp ((hK z).1 hz).1).1
  have hmulP : ∀ {u v : G} (hu : u ∈ P) (hv : v ∈ P),
      jq J ⟨u * v, hP.1 (P.mul_mem hu hv)⟩ = jq J ⟨u, hP.1 hu⟩ * jq J ⟨v, hP.1 hv⟩ :=
    fun hu hv => by rw [← map_mul]; rfl
  have hle : Nat.card K ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun k => (⟨jq J ⟨k.1, hP.1 (hKP k.2)⟩, ?_, ?_⟩ :
        {e : Jhat J // e ∈ q.ker ∧ e * e = 1})) fun a b hab => ?_) hQ.card_omega_ker_le
    · rw [hQ.ker]
      exact (mem_zStarIn_iff _).1 (mem_inf.mp ((hK _).1 k.2).1).2
    · rw [← hmulP (hKP k.2) (hKP k.2)]
      have : (⟨k.1 * k.1, hP.1 (P.mul_mem (hKP k.2) (hKP k.2))⟩ : J) = 1 :=
        Subtype.ext ((hK _).1 k.2).2
      rw [this, map_one]
    · exact Subtype.ext (eq_of_jq_eq hP.1 hP2 (hKP a.2) (hKP b.2) (congrArg Subtype.val hab))
  have hge : 2 < Nat.card K := by
    by_contra hle2
    push Not at hle2
    obtain ⟨ζ, -⟩ := exists_zeta hP hQ.ker
    set T : Subgroup (Jhat J) := (K.subgroupOf P).map ((jq J).comp (Subgroup.inclusion hP.1))
      with hTd
    have hTmem : ∀ e, e ∈ T ↔ e ∈ q.ker ∧ e * e = 1 := by
      intro e
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hk : (k : G) ∈ K := hk
        obtain ⟨hkZ, hk2⟩ := (hK _).1 hk
        refine ⟨?_, ?_⟩
        · rw [hQ.ker]
          exact (mem_zStarIn_iff _).1 (mem_inf.mp hkZ).2
        · show jq J (Subgroup.inclusion hP.1 k) * jq J (Subgroup.inclusion hP.1 k) = 1
          rw [← map_mul]
          have : Subgroup.inclusion hP.1 k * Subgroup.inclusion hP.1 k = 1 := Subtype.ext hk2
          rw [this, map_one]
      · rintro ⟨he, he2⟩
        have he' := he
        rw [hQ.ker] at he'
        obtain ⟨z, hzP, hzJ, rfl⟩ := exists_mem_of_mem_center hP he'
        have hzZ : z ∈ P ⊓ zStarIn J := mem_inf.mpr ⟨hzP, (mem_zStarIn_iff hzJ).2 he'⟩
        have hz2 : z * z = 1 := eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hzP hzP)
          (by rw [hmulP hzP hzP]; exact he2)
        exact ⟨⟨z, hzP⟩, (hK z).2 ⟨hzZ, hz2⟩, rfl⟩
    have hTcard : Nat.card T = Nat.card K := by
      rw [hTd, Subgroup.card_map_of_injective]
      · exact Nat.card_congr (subgroupOfEquivOfLe hKP).toEquiv
      · intro a b hab
        exact Subtype.ext (eq_of_jq_eq hP.1 hP2 a.2 b.2 hab)
    have hcyc' := isCyclic_of_card_le_two hQ.ker_le (fun z hz => pow_four_of_ker' hQ hz) hTmem
      (hTcard ▸ hle2)
    exact hcyc (isCyclic_of_surjective ζ.symm.toMonoidHom ζ.symm.surjective)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : IsPGroup 2 K := fun k => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact ((hK _).1 k.2).2)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := K)).1 hKp
  rw [hm] at hle hge ⊢
  have hm2 : m = 2 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m <;> simp at hge
    · rcases Nat.lt_or_ge m 3 with h' | h'
      · omega
      · have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h'
        omega
  rw [hm2]
  rfl

theorem exists_tg4_conj
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hP : IsSylowTwoIn P J)
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat J))
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e)
    {U : Subgroup (Equiv.Perm (Fin 42))} (hUT : U ≤ T0)
    (hU : ∀ v ∈ U, v ≠ 1 → ∃ s ∈ S, s ∈ normalizer (U : Set (Equiv.Perm (Fin 42))) ∧
      s * v * s⁻¹ = wordPerm (tg 4))
    {e : G} (he : e ∈ P) (heU : q (jq J ⟨e, hP.1 he⟩) ∈ U) (he1 : q (jq J ⟨e, hP.1 he⟩) ≠ 1) :
    ∃ n ∈ J, (∀ k ∈ P ⊓ zStarIn J, n * k * n⁻¹ = k) ∧
      ∃ he' : n * e * n⁻¹ ∈ P, q (jq J ⟨n * e * n⁻¹, hP.1 he'⟩) = wordPerm (tg 4) := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨s, hsS, hsU, hst⟩ := hU _ heU he1
  obtain ⟨n, hnJ, hnN, hnU⟩ := exists_lift_normalizer hP hqsurj hT hUT hsS hsU
  have heT : e ∈ pullP J P hP.1 (U.comap q) := mem_pullP.2 ⟨he, heU⟩
  have he'P := pullP_le _ ((mem_normalizer_iff.mp hnN e).mp heT)
  refine ⟨n, hnJ, fun k hk => ?_, he'P, ?_⟩
  · obtain ⟨hkP, hkZ⟩ := mem_inf.mp hk
    have hkc := (mem_zStarIn_iff (hP.1 hkP)).1 hkZ
    have hk1 : q (jq J ⟨k, hP.1 hkP⟩) = 1 := by
      rw [← MonoidHom.mem_ker, hqker]
      exact hkc
    have hkT : k ∈ pullP J P hP.1 (U.comap q) := by
      refine mem_pullP.2 ⟨hkP, ?_⟩
      rw [mem_comap, hk1]
      exact U.one_mem
    have hk'P := pullP_le _ ((mem_normalizer_iff.mp hnN k).mp hkT)
    apply eq_of_jq_eq hP.1 hP2 hk'P hkP
    have e1 : (⟨n * k * n⁻¹, hP.1 hk'P⟩ : J) = ⟨n, hnJ⟩ * ⟨k, hP.1 hkP⟩ * (⟨n, hnJ⟩ : J)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, mem_center_iff.mp hkc (jq J ⟨n, hnJ⟩),
      mul_inv_cancel_right]
  · have e1 : (⟨n * e * n⁻¹, hP.1 he'P⟩ : J) = ⟨n, hnJ⟩ * ⟨e, hP.1 he⟩ * (⟨n, hnJ⟩ : J)⁻¹ := rfl
    have hc := mem_centralizer_singleton_iff.mp
      (T0_le_centralizer_tg (k := 4) (by decide) (hUT hnU))
    rw [e1]
    simp only [map_mul, map_inv]
    calc q (jq J ⟨n, hnJ⟩) * q (jq J ⟨e, hP.1 he⟩) * (q (jq J ⟨n, hnJ⟩))⁻¹ =
        (q (jq J ⟨n, hnJ⟩) * s⁻¹) * (s * q (jq J ⟨e, hP.1 he⟩) * s⁻¹) *
          (q (jq J ⟨n, hnJ⟩) * s⁻¹)⁻¹ := by group
      _ = (q (jq J ⟨n, hnJ⟩) * s⁻¹) * wordPerm (tg 4) * (q (jq J ⟨n, hnJ⟩) * s⁻¹)⁻¹ := by
        rw [hst]
      _ = wordPerm (tg 4) := by rw [hc]; group

end CFSG.ComponentClassification.GrSLit.L34Facts
