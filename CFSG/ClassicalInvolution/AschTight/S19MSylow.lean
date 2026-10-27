module

public import CFSG.ClassicalInvolution.SmallCases.DSplitDefs
public import CFSG.Dihedral.DisconnectedInvolutionGraph.NormalSylowIntersection

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19M

open CFSG.ClassicalInvolution

variable {G : Type} [Group G]

theorem exists_sylow_inf_of_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {H E : Subgroup G}
    (hEH : E ≤ H) (hHE : H ≤ Subgroup.normalizer (E : Set G)) (P : Sylow p H) :
    ∃ T : Sylow p E, (T : Subgroup E).map E.subtype = E ⊓ (P : Subgroup H).map H.subtype := by
  let Ek := E.subgroupOf H
  have : Ek.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEH).mpr hHE
  obtain ⟨rel, hrel⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection p Ek P
  let F : Ek ≃* E := Subgroup.subgroupOfEquivOfLe hEH
  have hF : Function.Surjective F.toMonoidHom := F.surjective
  refine ⟨rel.mapSurjective hF, ?_⟩
  rw [Sylow.coe_mapSurjective, hrel, Subgroup.map_map]
  have hcomp : E.subtype.comp F.toMonoidHom = H.subtype.comp Ek.subtype := by
    ext
    rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hEH, inf_comm]

theorem map_le_normalizer_map (φ : G ≃* G) {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) :
    H.map φ.toMonoidHom ≤ Subgroup.normalizer ((K.map φ.toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxK := Subgroup.mem_normalizer_iff.mp (h hx) (φ.symm y)
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, hxK]
  simp [mul_assoc]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.mp hg _).mpr (by simpa [mul_assoc] using hx),
      by simp [mul_assoc]⟩

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (hg : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hg]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hg] at hh
    obtain ⟨y, hy, hyh⟩ := hh
    have : y = h := by simpa using hyh
    rwa [← this]

theorem exists_sylow_le_normalizer_of_dEdgeless [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : ∀ L ∈ Ω, ∀ g : G, L.map (MulAut.conj g).toMonoidHom ∈ Ω)
    (hDE : Disconnected.DEdgeless Ω) {L : Subgroup G} (hL : L ∈ Ω) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (L : Set G) with hN
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 N) := inferInstance
  set T : Subgroup G := (P₀ : Subgroup N).map N.subtype with hT
  have hTN : T ≤ N := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := P₀.isPGroup'.map N.subtype
  obtain ⟨S, hTS⟩ := hT2.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hSN
  have hSNT : (S : Subgroup G) ⊓ N ≤ T := by
    have hQ : IsPGroup 2 ((S : Subgroup G).subgroupOf N) := S.isPGroup'.comap_subtype
    have hle : (P₀ : Subgroup N) ≤ (S : Subgroup G).subgroupOf N := fun x hx =>
      hTS ⟨x, hx, rfl⟩
    have heq := P₀.is_maximal' hQ hle
    rintro x ⟨hxS, hxN⟩
    have hx : (⟨x, hxN⟩ : N) ∈ (P₀ : Subgroup N) := by
      rw [← heq]
      exact hxS
    exact ⟨_, hx, rfl⟩
  have hTlt : T.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hSN
    intro x hxS
    have hx : (⟨x, hxS⟩ : S) ∈ T.subgroupOf S := by
      rw [htop]
      trivial
    exact hTN hx
  have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  obtain ⟨s, hsN, hsT⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hTlt)
  have hsT' : (s : G) ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hh : h ∈ (S : Subgroup G)
    · have := Subgroup.mem_normalizer_iff.mp hsN ⟨h, hh⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · have h1 : h ∉ T := fun h' => hh (hTS h')
      have h2 : (s : G) * h * (s : G)⁻¹ ∉ T := by
        intro h'
        apply hh
        have e : h = (s : G)⁻¹ * ((s : G) * h * (s : G)⁻¹) * s := by group
        rw [e]
        exact S.mul_mem (S.mul_mem (S.inv_mem s.2) (hTS h')) s.2
      exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
  have hsL : (s : G) ∉ N := fun h => hsT (by
    rw [Subgroup.mem_subgroupOf]
    exact hSNT ⟨s.2, h⟩)
  set J := L.map (MulAut.conj (s : G)).toMonoidHom with hJ
  have hJΩ : J ∈ Ω := hΩ L hL s
  have hJL : J ≠ L := fun h => hsL (mem_normalizer_of_map_conj_eq h)
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_inf_of_le_normalizer Subgroup.le_normalizer le_rfl P₀
  let e : L ≃* J := L.equivMapOfInjective (MulAut.conj (s : G)).toMonoidHom
    (MulAut.conj (s : G)).injective
  have he : Function.Surjective e.toMonoidHom := e.surjective
  have hQ : ((Q₀.mapSurjective he : Sylow 2 J) : Subgroup J).map J.subtype = J ⊓ T := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : J.subtype.comp e.toMonoidHom =
        (MulAut.conj (s : G)).toMonoidHom.comp L.subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hQ₀, Subgroup.map_inf _ _ _ (MulAut.conj (s : G)).injective,
      map_conj_eq_of_mem_normalizer hsT']
  apply hDE L hL J hJΩ
  exact Or.inl ⟨hJΩ, hJL, J ⊓ T, ⟨J, hJΩ, Q₀.mapSurjective he, hQ.symm⟩, inf_le_left,
    inf_le_right.trans hTN⟩

theorem exists_sylow_map_eq [Finite G] (φ : MulAut G) (hφ : φ * φ = 1) :
    ∃ S : Sylow 2 G, (S : Subgroup G).map φ.toMonoidHom = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 (Subgroup.zpowers φ) := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : g ^ 2 = 1 := by
      obtain ⟨_, k, rfl⟩ := g
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hφ, one_zpow]
    have h2 : orderOf g ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one hg
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    exact ⟨i, hi⟩
  obtain ⟨S, hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 G)
    (not_dvd_card_sylow 2 G)
  refine ⟨S, ?_⟩
  have h1 : φ • S = S := hS ⟨φ, Subgroup.mem_zpowers φ⟩
  calc (S : Subgroup G).map φ.toMonoidHom = ((φ • S : Sylow 2 G) : Subgroup G) := by
        rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
        rfl
    _ = S := by rw [h1]

theorem exists_map_eq_of_dEdgeless [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : ∀ L ∈ Ω, ∀ g : G, L.map (MulAut.conj g).toMonoidHom ∈ Ω) (hne : Ω.Nonempty)
    (hDE : Disconnected.DEdgeless Ω) (φ : MulAut G) (hφ : φ * φ = 1)
    (hφΩ : ∀ L ∈ Ω, L.map φ.toMonoidHom ∈ Ω) : ∃ L ∈ Ω, L.map φ.toMonoidHom = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L₀, hL₀⟩ := hne
  obtain ⟨S₀, hS₀⟩ := exists_sylow_le_normalizer_of_dEdgeless hΩ hDE hL₀
  obtain ⟨S, hS⟩ := exists_sylow_map_eq φ hφ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S
  set L := L₀.map (MulAut.conj g).toMonoidHom with hLdef
  have hL : L ∈ Ω := hΩ L₀ hL₀ g
  have hSL : (S : Subgroup G) ≤ Subgroup.normalizer (L : Set G) := by
    have h1 : ((g • S₀ : Sylow 2 G) : Subgroup G) =
        (S₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [← hg, h1]
    exact map_le_normalizer_map (MulAut.conj g) hS₀
  refine ⟨L, hL, ?_⟩
  by_contra hne'
  set L' := L.map φ.toMonoidHom with hL'def
  have hL' : L' ∈ Ω := hφΩ L hL
  have hSL' : (S : Subgroup G) ≤ Subgroup.normalizer (L' : Set G) := by
    rw [← hS]
    exact map_le_normalizer_map φ hSL
  obtain ⟨Q, hQ⟩ := exists_sylow_inf_of_le_normalizer Subgroup.le_normalizer le_rfl
    (S.subtype hSL')
  have hS' : ((S.subtype hSL' : Sylow 2 _) : Subgroup _).map
      (Subgroup.normalizer (L' : Set G)).subtype = S := by
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hSL']
  rw [hS'] at hQ
  apply hDE L hL L' hL'
  exact Or.inl ⟨hL', hne', L' ⊓ S, ⟨L', hL', Q, hQ.symm⟩, inf_le_left, inf_le_right.trans hSL⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19M
