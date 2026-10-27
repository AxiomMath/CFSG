module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2FusionTwoCentral

public section

namespace CFSG.SeitzReduction

open Subgroup

variable {G : Type} [Group G]

theorem mul_mem_of_commute_sylow_of_autU2 [Finite G] {L : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU2 : ∀ (U : Sylow 2 L) (β : MulAut L), β ^ 2 = 1 →
      (∀ u ∈ (U : Subgroup L), β u = u) → β ∈ (MulAut.conj : L →* MulAut L).range)
    (U : Sylow 2 L) {g : G} (hgC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hgU : ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) :
    t * (g⁻¹ * t * g) ∈ L := by
  set s := g⁻¹ * t * g with hs
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hss : s * s = 1 := by
    rw [hs]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  set β : MulAut L := L.normalizerMonoidHom ⟨s, hCN hgC⟩
  have hβ : ∀ l : L, ((β l : L) : G) = s * l * s⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hCN hgC⟩ l
  have hββ : β ^ 2 = 1 := by
    have h1 : (⟨s, hCN hgC⟩ : normalizer (L : Set G)) ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, sq, hss, OneMemClass.coe_one])
    change L.normalizerMonoidHom ⟨s, hCN hgC⟩ ^ 2 = 1
    rw [← map_pow, h1, map_one]
  obtain ⟨c, hc⟩ := hAutU2 U β hββ fun u hu => Subtype.ext (by
    rw [hβ, ← hgU u hu, mul_inv_cancel_right])
  have hsc : ∀ y ∈ L, s * y * s⁻¹ = c * y * (c : G)⁻¹ := fun y hy => by
    have h := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hc
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [← hβ ⟨y, hy⟩, ← h]
  rcases LinearPilot.eq_or_eq_mul_of_conj_eq' hLt ht hKt hgC c.2 hsc with h | h
  · exact absurd hgU (hnot U g (by rw [← hs, h]; exact c.2))
  · have hct : (c : G) * t = t * c := mem_centralizer_singleton_iff.1 (hLt c.2)
    have e : t * s = c := by
      rw [h, ← mul_assoc, ← hct, mul_assoc, htt, mul_one]
    rw [e]
    exact c.2

noncomputable abbrev conjugateMulEquiv (L : Subgroup G) (x : G) : L ≃* CFSG.conjugate L x :=
  L.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective

theorem coe_conjugateMulEquiv (L : Subgroup G) (x : G) (l : L) :
    ((conjugateMulEquiv L x l : CFSG.conjugate L x) : G) = x⁻¹ * l * x := by
  change (MulAut.conj x⁻¹) (l : G) = _
  rw [MulAut.conj_apply, inv_inv]

variable [Finite G]

theorem exists_conj_eq_mul_twoSided_of_two_dvd_index_of_mul_mem {L : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hA : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      (∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) →
        t * (g⁻¹ * t * g) ∈ L)
    (h2 : 2 ∣ (centralizer ({t} : Set G)).index) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨U⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨S, x, hSt, hUS, htS, hxN, hxt⟩ := SeitzQ2.exists_normalizer_of_two_dvd_index ht hLt U h2
  set t' := x⁻¹ * t * x with ht'def
  have hxS : ∀ s ∈ S, x⁻¹ * s * x ∈ S := fun s hs => (mem_normalizer_iff''.1 hxN s).1 hs
  have hxS' : ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.1 hxN s).1 hs
  have hst : ∀ s ∈ S, s * t = t * s := fun s hs => mem_centralizer_singleton_iff.1 (hSt hs)
  have ht'S : t' ∈ S := hxS t htS
  have hcomm : ∀ s ∈ S, s * t' = t' * s := by
    intro s hs
    have h' := hst _ (hxS' s hs)
    calc s * t' = x⁻¹ * (x * s * x⁻¹ * t) * x := by rw [ht'def]; group
      _ = x⁻¹ * (t * (x * s * x⁻¹)) * x := by rw [h']
      _ = t' * s := by rw [ht'def]; group
  have htt' : t * t' = t' * t := (hst t' ht'S).symm
  have hzL : t * t' ∈ L := hA U x (hSt ht'S) fun u hu => hcomm u (hUS u hu)
  have hxtC : x⁻¹⁻¹ * t * x⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff, inv_inv]
    calc x * t * x⁻¹ * t = x * (t * t') * x⁻¹ := by rw [ht'def]; group
      _ = x * (t' * t) * x⁻¹ := by rw [htt']
      _ = t * (x * t * x⁻¹) := by rw [ht'def]; group
  have hxtU : ∀ u ∈ (U : Subgroup L),
      (u : G) * (x⁻¹⁻¹ * t * x⁻¹) = (x⁻¹⁻¹ * t * x⁻¹) * u := by
    intro u hu
    rw [inv_inv]
    have h' := hst _ (hxS _ (hUS u hu))
    calc (u : G) * (x * t * x⁻¹) = x * ((x⁻¹ * u * x) * t) * x⁻¹ := by group
      _ = x * (t * (x⁻¹ * u * x)) * x⁻¹ := by rw [h']
      _ = x * t * x⁻¹ * u := by group
  have hz'L : t * (x⁻¹⁻¹ * t * x⁻¹) ∈ L := hA U x⁻¹ hxtC hxtU
  rw [inv_inv] at hz'L
  have hzLx : t * t' ∈ CFSG.conjugate L x := by
    rw [SeitzQ2.mem_conjugate_iff_conj_mem]
    have e : x * (t * t') * x⁻¹ = (t * (x * t * x⁻¹))⁻¹ := by
      rw [ht'def, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, htinv]
      group
    rw [e]
    exact inv_mem hz'L
  have ht'C : ∀ l ∈ CFSG.conjugate L x, l * t' = t' * l := by
    intro l hl
    have hl' := SeitzQ2.mem_conjugate_iff_conj_mem.1 hl
    have h' : x * l * x⁻¹ * t = t * (x * l * x⁻¹) := mem_centralizer_singleton_iff.1 (hLt hl')
    calc l * t' = x⁻¹ * (x * l * x⁻¹ * t) * x := by rw [ht'def]; group
      _ = x⁻¹ * (t * (x * l * x⁻¹)) * x := by rw [h']
      _ = t' * l := by rw [ht'def]; group
  refine ⟨x, t * t', ⟨hzL, hzLx⟩, ?_, ?_, ⟨U, fun u hu => ?_⟩,
    ⟨Sylow.mapSurjective (f := (conjugateMulEquiv L x).toMonoidHom)
      (conjugateMulEquiv L x).surjective U, fun u hu => ?_⟩, fun l hl => ?_⟩
  · rw [← mul_assoc, htt, one_mul]
  · intro h1
    apply hxt
    calc x⁻¹ * t * x = t' := rfl
      _ = t * (t * t') := by rw [← mul_assoc, htt, one_mul]
      _ = t := by rw [h1, mul_one]
  · have hs := hUS u hu
    exact (Commute.mul_right (hst _ hs) (hcomm u hs)).eq
  · change u ∈ (U : Subgroup L).map (conjugateMulEquiv L x).toMonoidHom at hu
    rw [mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    have hvx : ((conjugateMulEquiv L x).toMonoidHom v : G) = x⁻¹ * v * x :=
      coe_conjugateMulEquiv L x v
    rw [hvx]
    have hvS : x⁻¹ * (v : G) * x ∈ S := hxS _ (hUS v hv)
    have hvL : x⁻¹ * (v : G) * x ∈ CFSG.conjugate L x := by
      rw [← hvx]
      exact ((conjugateMulEquiv L x).toMonoidHom v).2
    exact (Commute.mul_right (hst _ hvS) (ht'C _ hvL)).eq
  · have h' := ht'C l hl
    calc t * l * t⁻¹ = t * (l * t') * t'⁻¹ * t⁻¹ := by group
      _ = t * (t' * l) * t'⁻¹ * t⁻¹ := by rw [h']
      _ = t * t' * l * (t * t')⁻¹ := by group

theorem two_dvd_index_of_commutator_eq_top_of_mul_mem (hperf : commutator G = ⊤)
    {L : Subgroup G} {t : G} (ht : orderOf t = 2) (htL : t ∉ L)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hA : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      (∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) →
        t * (g⁻¹ * t * g) ∈ L)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L) :
    2 ∣ (centralizer ({t} : Set G)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h2
  obtain ⟨S, -, hSt⟩ := CFSG.SeitzReduction.exists_sylow_mem_le_of_not_dvd_index h2
    (mem_centralizer_singleton_iff.2 rfl) (ht.trans (pow_one 2).symm)
  refine LinearPilot.commutator_ne_top_of_sylow_le_centralizer ht htL S hSt
    (habel S hSt) (fun g hg => ?_) hperf
  have htS := LinearPilot.mem_sylow_of_le_centralizer ht S hSt
  have hgS : g⁻¹ * t * g ∈ (S : Subgroup G) := (mem_normalizer_iff''.1 hg t).1 htS
  have hcomm : ∀ s ∈ (S : Subgroup G), s * (g⁻¹ * t * g) = g⁻¹ * t * g * s := by
    intro s hs
    have hs' : g * s * g⁻¹ ∈ (S : Subgroup G) := (mem_normalizer_iff.1 hg s).1 hs
    have h' : g * s * g⁻¹ * t = t * (g * s * g⁻¹) :=
      mem_centralizer_singleton_iff.1 (hSt hs')
    calc s * (g⁻¹ * t * g) = g⁻¹ * (g * s * g⁻¹ * t) * g := by group
      _ = g⁻¹ * (t * (g * s * g⁻¹)) * g := by rw [h']
      _ = g⁻¹ * t * g * s := by group
  have hKn : (L.subgroupOf (centralizer ({t} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLt).2 hCN
  have hodd : ¬ 2 ∣ ((S : Subgroup G).subgroupOf L).index := by
    have h := CFSG.QuasiDihedralFusion.not_dvd_relIndex_of_normal (S.subtype hSt)
      (L.subgroupOf (centralizer ({t} : Set G)))
    rw [Sylow.coe_subtype] at h
    have e : (((S : Subgroup G).subgroupOf (centralizer ({t} : Set G))).subgroupOf
        (L.subgroupOf (centralizer ({t} : Set G)))).index =
          ((S : Subgroup G).subgroupOf L).index :=
      Subgroup.relIndex_subgroupOf hLt
    rwa [e] at h
  have hSLp : IsPGroup 2 ((S : Subgroup G).subgroupOf L) := S.isPGroup'.comap_subtype
  set U : Sylow 2 L := hSLp.toSylow hodd with hUdef
  have hUS : ∀ u ∈ (U : Subgroup L), (u : G) ∈ (S : Subgroup G) := by
    intro u hu
    rw [hUdef, IsPGroup.toSylow_coe] at hu
    exact Subgroup.mem_subgroupOf.1 hu
  exact hA U g (hSt hgS) fun u hu => hcomm u (hUS u hu)

omit [Finite G] in
theorem not_mem_of_not_forall_commute_sylow {L : Subgroup G} {t : G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) : t ∉ L := by
  obtain ⟨U₀⟩ : Nonempty (Sylow 2 L) := inferInstance
  exact fun htL => hnot U₀ 1 (by simpa using htL) fun u _ => by
    simpa using (mem_centralizer_singleton_iff.1 (hLt u.2))

theorem exists_conj_eq_mul_twoSided_of_commutator_eq_top_of_autU2 (hperf : commutator G = ⊤)
    {L : Subgroup G} {t : G} (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU2 : ∀ (U : Sylow 2 L) (β : MulAut L), β ^ 2 = 1 →
      (∀ u ∈ (U : Subgroup L), β u = u) → β ∈ (MulAut.conj : L →* MulAut L).range)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have hA : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      (∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) →
        t * (g⁻¹ * t * g) ∈ L :=
    fun U g hgC hgU => mul_mem_of_commute_sylow_of_autU2 ht hLt hCN hKt hnot hAutU2 U hgC hgU
  exact exists_conj_eq_mul_twoSided_of_two_dvd_index_of_mul_mem ht hLt hA
    (two_dvd_index_of_commutator_eq_top_of_mul_mem hperf ht
      (not_mem_of_not_forall_commute_sylow hLt hnot) hLt hCN hA habel)

theorem exists_conj_eq_mul_of_commutator_eq_top_of_autU2 (hperf : commutator G = ⊤)
    {L : Subgroup G} {t : G} (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU2 : ∀ (U : Sylow 2 L) (β : MulAut L), β ^ 2 = 1 →
      (∀ u ∈ (U : Subgroup L), β u = u) → β ∈ (MulAut.conj : L →* MulAut L).range)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  obtain ⟨x, z, hz, hxz, hz1, hU, -, -⟩ :=
    exists_conj_eq_mul_twoSided_of_commutator_eq_top_of_autU2 hperf ht hLt hCN hKt hnot hAutU2
      habel
  exact ⟨x, z, hz.1, hxz, hz1, hU⟩

theorem exists_normal_index_two_of_rigid_sylow {t : G} (ht : orderOf t = 2) (S : Sylow 2 G)
    (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (χ : (S : Subgroup G) →* Multiplicative (ZMod 2)) (hχS : ∃ s : (S : Subgroup G), χ s ≠ 1)
    (hrig : ∀ g y : G, g⁻¹ * t * g ∈ (S : Subgroup G) →
      ∀ (hy : y ∈ (S : Subgroup G)) (hgy : g * y * g⁻¹ ∈ (S : Subgroup G)),
        y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y → χ ⟨y, hy⟩ = χ ⟨g * y * g⁻¹, hgy⟩) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := χ.ker.map (S : Subgroup G).subtype with hMdef
  have hmemM : ∀ y (hy : y ∈ (S : Subgroup G)), y ∈ M ↔ χ ⟨y, hy⟩ = 1 := by
    intro y hy
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = ⟨y, hy⟩ := Subtype.ext hzy
      rw [← this]
      exact hz
    · intro h
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hMS : M ≤ (S : Subgroup G) := map_subtype_le _
  obtain ⟨⟨s₀, hs₀⟩, hχs₀⟩ := hχS
  have hMidx : M.relIndex (S : Subgroup G) = 2 := by
    rw [relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨s₀, hs₀, fun h => hχs₀ ((hmemM s₀ hs₀).1 h), fun b hb => ?_⟩
    have hmul : χ ⟨b * s₀, mul_mem hb hs₀⟩ = χ ⟨b, hb⟩ * χ ⟨s₀, hs₀⟩ := by
      rw [← map_mul]
      rfl
    by_cases hbM : χ ⟨b, hb⟩ = 1
    · exact Or.inr ((hmemM b hb).2 hbM)
    · left
      rw [hmemM _ (mul_mem hb hs₀), hmul]
      exact LinearPilot.zmod_two_mul_eq_one _ hbM _ hχs₀
  classical
  have hex : ∃ k : ℕ, ∃ y ∈ (S : Subgroup G), y ∉ M ∧ orderOf y = k :=
    ⟨_, s₀, hs₀, fun h => hχs₀ ((hmemM s₀ hs₀).1 h), rfl⟩
  obtain ⟨x, hxS, hxM, hxk⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ (S : Subgroup G), y ∉ M → orderOf x ≤ orderOf y := by
    intro y hy hyM
    rw [hxk]
    exact Nat.find_min' hex ⟨y, hy, hyM, rfl⟩
  rcases LinearPilot.exists_normal_index_two_or_conj_mem_of_min S.isPGroup' S.not_dvd_index hMS
    hMidx hxS hxM hmin with h | ⟨g, hgM, hcall⟩
  · exact h
  · exfalso
    have htS : t ∈ (S : Subgroup G) := LinearPilot.mem_sylow_of_le_centralizer ht S hSt
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hSt hxS)
    have htC : t ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G) :=
      ⟨htS, mem_centralizer_singleton_iff.2 hxt.symm⟩
    obtain ⟨hgtS, hgtC⟩ := hcall t htC
    set y := g⁻¹ * x * g with hydef
    have hyS : y ∈ (S : Subgroup G) := hMS hgM
    have hgy : g * y * g⁻¹ = x := by rw [hydef]; group
    have hyt : y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y :=
      (mem_centralizer_singleton_iff.1 hgtC).symm
    have h := hrig g y hgtS hyS (by rw [hgy]; exact hxS) hyt
    have h1 : χ ⟨y, hyS⟩ = 1 := (hmemM y hyS).1 hgM
    have h2 : χ ⟨g * y * g⁻¹, by rw [hgy]; exact hxS⟩ = χ ⟨x, hxS⟩ := by
      congr 1
      exact Subtype.ext hgy
    exact hxM ((hmemM x hxS).2 (by rw [← h2, ← h, h1]))

end CFSG.SeitzReduction
