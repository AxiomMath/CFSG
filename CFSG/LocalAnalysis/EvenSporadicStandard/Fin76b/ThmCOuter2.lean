module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup MulAction CFSG.RankThree.Transfer

namespace OuterConfig

variable {G : Type} [Group G] {A : Subgroup G} {z t : G} {T : Subgroup G}
  (h : OuterConfig G A z t T)

include h in
theorem inf_centralizer_eq {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hTQ : T ≤ Q) :
    Q ⊓ centralizer ({z} : Set G) = T := by
  refine le_antisymm (fun q hq => h.mem_T_of_two_group hq.2 hQ hTQ hq.1) ?_
  exact fun y hy => ⟨hTQ hy, h.T_le hy⟩

include h in
theorem t_central_Q [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hTQ : T ≤ Q) {x : G}
    (hxQ : x ∈ Q) (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = t) :
    ∀ q ∈ Q, q * t = t * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzQ : z ∈ Q := hTQ h.z_mem
  have hnt : Nontrivial Q := ⟨⟨1, ⟨z, hzQ⟩, fun h' => h.z_ne (congrArg Subtype.val h'.symm)⟩⟩
  have hcnt : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  obtain ⟨⟨c, hcc⟩, hc1⟩ := exists_ne (1 : Subgroup.center Q)
  have hq1 : (c : G) ≠ 1 := fun h' => hc1 (Subtype.ext (Subtype.ext h'))
  have hcc' : ∀ y ∈ Q, y * (c : G) = (c : G) * y := fun y hy =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.1 hcc) ⟨y, hy⟩)
  have hcz : (c : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (hcc' z hzQ).symm
  have hcT : (c : G) ∈ T := h.mem_T_of_two_group hcz hQ hTQ c.2
  have hxc : x * (c : G) * x⁻¹ = c := by
    calc x * (c : G) * x⁻¹ = (c : G) * x * x⁻¹ := by rw [hcc' x hxQ]
      _ = c := by group
  have hct : (c : G) = t := by
    rcases h.center_T c hcT (fun y hy => hcc' y (hTQ hy)) with e | e | e | e
    · exact absurd e hq1
    · exfalso
      rw [e, hxz] at hxc
      exact h.t_ne (mul_left_cancel (hxc.trans (mul_one z).symm))
    · exact e
    · exfalso
      rw [e] at hxc
      have h1 : x * (z * t) * x⁻¹ = (x * z * x⁻¹) * (x * t * x⁻¹) := by group
      rw [h1, hxt, hxz] at hxc
      have h2 : (z * t) * t = (z * t) * 1 := by rw [mul_one]; exact hxc
      exact h.t_ne (mul_left_cancel h2)
  intro q hq
  have := hcc' q hq
  rwa [hct] at this

include h in
theorem mem_T_of_commute {w : G} (hw2 : w * w = 1) (hw : ∀ p ∈ T, p * w = w * p) : w ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hw1 : w = 1
  · rw [hw1]; exact one_mem T
  have hworder : orderOf w = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  have hpg : IsPGroup 2 (zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hworder, pow_one])
  have hTn : T ≤ normalizer (zpowers w : Set G) := by
    intro y hy
    have hk : ∀ u ∈ T, ∀ k ∈ zpowers w, u * k * u⁻¹ = k := by
      intro u hu k hk
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
      have := ((Commute.zpow_right (show Commute u w from hw u hu) n).eq)
      rw [this]; group
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hmem => by rw [hk y hy k hmem]; exact hmem, fun hmem => ?_⟩
    have h2 := hk y⁻¹ (inv_mem hy) _ hmem
    have h3 : y⁻¹ * (y * k * y⁻¹) * y⁻¹⁻¹ = k := by group
    rw [h3] at h2
    rw [h2]; exact hmem
  have hQ : IsPGroup 2 (T ⊔ zpowers w : Subgroup G) := h.T_pgroup.to_sup_of_normal_right' hpg hTn
  have hwH : w ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (hw z h.z_mem).symm
  exact h.mem_T_of_two_group hwH hQ le_sup_left (mem_sup_right (mem_zpowers w))

include h in
theorem hom_central_eq_one [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {B : Type*} [CommGroup B] [Finite B] (ψ : centralizer ({t} : Set G) →* B) :
    ψ ⟨z, mem_centralizer_singleton_iff.2 h.t_comm_z.symm⟩ = 1 := by
  classical
  by_contra hne
  obtain ⟨g, hg⟩ := h.fused_eq hnonab
  have : Fintype (fixedPoints T (G ⧸ centralizer ({t} : Set G))) := Fintype.ofFinite _
  have h1 := McLStd.prod_fixedPoints_eq_one (K := centralizer ({t} : Set G)) (t := z) hnonab h.z_sq
    h.T_pgroup h.z_mem h.z_central_T ψ
  have hmemM : ∀ p ∈ T, p ∈ centralizer ({t} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.2 (h.t_central p hp)
  have hone : ((1 : G) : G ⧸ centralizer ({t} : Set G)) ∈
      fixedPoints T (G ⧸ centralizer ({t} : Set G)) := by
    rw [McLStd.coe_mem_fixedPoints_iff]
    intro p hp
    simpa using hmemM p hp
  have hall : ∀ X : fixedPoints T (G ⧸ centralizer ({t} : Set G)), X = ⟨_, hone⟩ := by
    rintro ⟨X, hX⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective X
    rw [McLStd.coe_mem_fixedPoints_iff] at hX
    have hcomm : ∀ p ∈ T, p * (x * t * x⁻¹) = (x * t * x⁻¹) * p := by
      intro p hp
      have hpx := mem_centralizer_singleton_iff.1 (hX p hp)
      calc p * (x * t * x⁻¹) = x * ((x⁻¹ * p * x) * t) * x⁻¹ := by group
        _ = x * (t * (x⁻¹ * p * x)) * x⁻¹ := by rw [hpx]
        _ = (x * t * x⁻¹) * p := by group
    have hsq : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [h.t_sq]; group
    have hT' : x * t * x⁻¹ ∈ T := h.mem_T_of_commute hsq hcomm
    have hxt : x * t * x⁻¹ = t := by
      rcases h.center_T _ hT' hcomm with e | e | e | e
      · exfalso
        apply h.t_ne
        calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
          _ = 1 := by rw [e]; group
      · exact absurd e (h.conj_t_ne_z x)
      · exact e
      · exfalso
        refine h.conj_t_ne_z (g⁻¹ * x) ?_
        calc g⁻¹ * x * t * (g⁻¹ * x)⁻¹ = g⁻¹ * (x * t * x⁻¹) * g := by group
          _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [e, hg]
          _ = z := by group
    have hxM : x ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * x := by rw [hxt]
    apply Subtype.ext
    show (x : G ⧸ centralizer ({t} : Set G)) = ((1 : G) : G ⧸ centralizer ({t} : Set G))
    rw [QuotientGroup.eq]
    simpa using inv_mem hxM
  rw [Fintype.prod_eq_single (⟨_, hone⟩ : fixedPoints T (G ⧸ centralizer ({t} : Set G)))
    (fun X hX => absurd (hall X) hX)] at h1
  have hz1 : (1 : G)⁻¹ * z * 1 ∈ centralizer ({t} : Set G) := by
    simpa using mem_centralizer_singleton_iff.2 h.t_comm_z.symm
  have h2 := cosetValue_coe ψ hz1
  apply hne
  rw [← h1]
  show ψ ⟨z, _⟩ = cosetValue ψ z (((1 : G) : G ⧸ centralizer ({t} : Set G)))
  rw [h2]
  congr 1
  exact Subtype.ext (by simp)

include h in
theorem z_mem_commutator [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    (⟨z, mem_centralizer_singleton_iff.2 h.t_comm_z.symm⟩ : centralizer ({t} : Set G)) ∈
      commutator (centralizer ({t} : Set G)) := by
  have := h.hom_central_eq_one hnonab
    (Abelianization.of : centralizer ({t} : Set G) →* Abelianization (centralizer ({t} : Set G)))
  have hmem : (⟨z, mem_centralizer_singleton_iff.2 h.t_comm_z.symm⟩ :
      centralizer ({t} : Set G)) ∈ (Abelianization.of :
        centralizer ({t} : Set G) →* Abelianization (centralizer ({t} : Set G))).ker :=
    MonoidHom.mem_ker.2 this
  rwa [Abelianization.ker_of] at hmem

end OuterConfig

end CFSG.EvenSporadicStandard.Fin76b
