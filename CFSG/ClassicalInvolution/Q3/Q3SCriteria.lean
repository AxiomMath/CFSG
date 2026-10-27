module

public import CFSG.ClassicalInvolution.Q3.Q3SSylow
public import CFSG.ClassicalInvolution.Q3.Q3RSectionalFour

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn map_centralizer_subtype)

theorem NoWeakClassical3At.of_map {F F' : Type} [Group F] [Group F'] (e : F ≃* F') {z : F}
    (h : NoWeakClassical3At (e z)) : NoWeakClassical3At z := fun L hL =>
  h (L.map e.toMonoidHom) (hL.map_mulEquiv e)

theorem NoWeakClassical3At.conj {F : Type} [Group F] {z : F} (h : NoWeakClassical3At z) (g : F) :
    NoWeakClassical3At (g * z * g⁻¹) := by
  refine NoWeakClassical3At.of_map (MulAut.conj g⁻¹) ?_
  have : (MulAut.conj g⁻¹) (g * z * g⁻¹) = z := by
    simp only [MulAut.conj_apply]; group
  rwa [this]

theorem NoWeakClassical3.of_conj_reps {F : Type} [Group F] (S : Set F)
    (hS : ∀ z : F, orderOf z = 2 → ∃ s ∈ S, IsConj s z)
    (h : ∀ s ∈ S, NoWeakClassical3At s) : NoWeakClassical3 F := by
  intro L z hL
  obtain ⟨s, hs, hsz⟩ := hS z hL.orderOf_eq_two
  obtain ⟨c, hc⟩ := isConj_iff.mp hsz
  have := (h s hs).conj c
  rw [hc] at this
  exact this L hL

theorem NoWeakClassical3At.of_index_two {F : Type} [Group F] [Finite F] {z : F} (N : Subgroup F)
    (hidx : (N.subgroupOf (Subgroup.centralizer ({z} : Set F))).index = 2) (hzN : z ∉ N) :
    NoWeakClassical3At z := by
  intro L hL
  obtain ⟨x, hxL, hx⟩ := hL.exists_orderOf_eq_four
  have hxC : x ∈ Subgroup.centralizer ({z} : Set F) := hL.le_centralizer hxL
  have hsq := Subgroup.mul_self_mem_of_index_two hidx ⟨x, hxC⟩
  rw [Subgroup.mem_subgroupOf] at hsq
  apply hzN
  have : x * x = z := hL.mul_self_eq_of_orderOf_eq_four hxL hx
  rw [← this]
  exact hsq

theorem NoWeakClassical3At.of_ambient_index_two {M : Type} [Group M] (H : Subgroup M) [Finite H]
    (t : H) (N : Subgroup M) (hNK : N ≤ centralizerIn H (t : M))
    (hcard : Nat.card (centralizerIn H (t : M)) = 2 * Nat.card N) (htN : (t : M) ∉ N) :
    NoWeakClassical3At t := by
  set C : Subgroup H := Subgroup.centralizer ({t} : Set H) with hC
  set N'' : Subgroup C := (N.subgroupOf H).subgroupOf C with hN''
  have hmapC : C.map H.subtype = centralizerIn H (t : M) := map_centralizer_subtype H t
  have hcardC : Nat.card C = Nat.card (centralizerIn H (t : M)) := by
    rw [← hmapC, Subgroup.card_map_of_injective H.subtype_injective]
  have hf : Function.Injective (H.subtype.comp C.subtype) :=
    H.subtype_injective.comp C.subtype_injective
  have hmapN : N''.map (H.subtype.comp C.subtype) = N := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hx
      have hxK := hNK hx
      rw [← hmapC] at hxK
      obtain ⟨y, hy, rfl⟩ := hxK
      exact ⟨⟨y, hy⟩, hx, rfl⟩
  have hcardN : Nat.card N'' = Nat.card N := by
    rw [← hmapN, Subgroup.card_map_of_injective hf]
  have hNH : N ≤ H := fun x hx => (mem_centralizerIn.1 (hNK hx)).1
  have : Finite N := Finite.of_injective (Subgroup.inclusion hNH) (Subgroup.inclusion_injective _)
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hidx : N''.index = 2 := by
    have h := Subgroup.card_mul_index N''
    rw [hcardN, hcardC, hcard] at h
    have : Nat.card N * N''.index = Nat.card N * 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  refine NoWeakClassical3At.of_index_two (N.subgroupOf H) hidx ?_
  rw [Subgroup.mem_subgroupOf]
  exact htN

theorem NoWeakClassical3At.of_ambient_witness {M : Type} [Group M] (H : Subgroup M) [Finite H]
    {r : M} (hr : r ∈ H) (h9 : ¬ 9 ∣ Nat.card (centralizerIn H r)) {g₁ g₂ : M} (h₁ : g₁ ∈ H)
    (h₂ : g₂ ∈ H) (c₁ : g₁ * r = r * g₁) (c₂ : g₂ * r = r * g₂) (hg₁ : g₁ ^ 3 = 1)
    (hg₂ : g₂ ^ 3 = 1) (ht : (g₁ * g₂) ^ 2 = 1) (ht1 : g₁ * g₂ ≠ 1) (htz : g₁ * g₂ ≠ r) :
    NoWeakClassical3At (⟨r, hr⟩ : H) := by
  have hcard : Nat.card (Subgroup.centralizer ({(⟨r, hr⟩ : H)} : Set H)) =
      Nat.card (centralizerIn H r) := by
    rw [← map_centralizer_subtype H ⟨r, hr⟩, Subgroup.card_map_of_injective H.subtype_injective]
  refine NoWeakClassical3At.of_witness (g₁ := ⟨g₁, h₁⟩) (g₂ := ⟨g₂, h₂⟩) (by rwa [hcard]) ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  · rw [Subgroup.mem_centralizer_singleton_iff]; exact Subtype.ext c₁
  · rw [Subgroup.mem_centralizer_singleton_iff]; exact Subtype.ext c₂
  · exact Subtype.ext hg₁
  · exact Subtype.ext hg₂
  · exact Subtype.ext ht
  · intro h1; exact ht1 (congrArg Subtype.val h1)
  · intro h1; exact htz (congrArg Subtype.val h1)

theorem noWeakClassical3_of_sylow_cover_at {M : Type} [Group M] (H S : Subgroup M) [Finite H]
    (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ (S.subgroupOf H).index) {z : M} (hz : z ∈ H)
    (hSz : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ H, s = c * z * c⁻¹)
    (hgood : NoWeakClassical3At (⟨z, hz⟩ : H)) : NoWeakClassical3 H := by
  refine NoWeakClassical3.of_conj_reps {x : H | (x : M) = z} ?_ ?_
  · intro u hu
    have hu' : orderOf (u : M) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hu
    obtain ⟨c, hc, he⟩ := cover_of_sylow H S hS hidx z hSz u u.2 hu'
    refine ⟨⟨z, hz⟩, rfl, ?_⟩
    rw [isConj_iff]
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    simp [he]
  · rintro s hs
    have : s = ⟨z, hz⟩ := Subtype.ext hs
    rw [this]
    exact hgood

theorem noWeakClassical3_of_reps {M : Type} [Group M] (H : Subgroup M) (reps : List M)
    (hcov : ∀ u ∈ H, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ H, u = c * r * c⁻¹)
    (hgood : ∀ (r : M) (hr : r ∈ H), r ∈ reps → NoWeakClassical3At (⟨r, hr⟩ : H)) :
    NoWeakClassical3 H := by
  refine NoWeakClassical3.of_conj_reps {x : H | (x : M) ∈ reps} ?_ ?_
  · intro z hz
    have hz' : orderOf (z : M) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hz
    obtain ⟨r, hr, c, hc, hzr⟩ := hcov z z.2 hz'
    refine ⟨⟨r, ?_⟩, hr, ?_⟩
    · have : r = (c : M)⁻¹ * z * c := by rw [hzr]; group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem hc) z.2) hc
    · rw [isConj_iff]
      refine ⟨⟨c, hc⟩, ?_⟩
      apply Subtype.ext
      simp [hzr]
  · intro s hs
    exact hgood s s.2 hs

theorem NoWeakClassical3At.of_isQuasisimple_centralizer {F : Type} [Group F] [Finite F] {z : F}
    (hC : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({z} : Set F)))
    (hZ : Nat.card (Subgroup.center ↥(Subgroup.centralizer ({z} : Set F))) = 2)
    (hcard : Nat.card (Subgroup.centralizer ({z} : Set F)) ≠ 24) : NoWeakClassical3At z := by
  intro L hL
  have hLC : L ≤ Subgroup.centralizer ({z} : Set F) := hL.le_centralizer
  have hsub : IsSubnormal (L.subgroupOf (Subgroup.centralizer ({z} : Set F))) ⊤ := by
    have := isSubnormal_subgroupOf hL.subnormal (Subgroup.centralizer ({z} : Set F))
    rwa [Subgroup.subgroupOf_self] at this
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hC _ hsub with
    hcen | htop
  · exact (hL.subgroupOf hLC).not_le_center hcen
  · have hCL : Subgroup.centralizer ({z} : Set F) ≤ L := Subgroup.subgroupOf_eq_top.mp htop
    have hLeq : L = Subgroup.centralizer ({z} : Set F) := le_antisymm hLC hCL
    rw [hLeq] at hL
    have hodd := hL.odd_card_oddCore
    have hO : classicalInvolutionOddCore (Subgroup.centralizer ({z} : Set F)) = ⊥ := by
      rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hC
        (classicalInvolutionOddCore (Subgroup.centralizer ({z} : Set F))) with h | h
      · have hdvd : Nat.card (classicalInvolutionOddCore (Subgroup.centralizer ({z} : Set F))) ∣
            2 := by
          rw [← hZ]
          exact Subgroup.card_dvd_of_le h
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact Subgroup.card_eq_one.mp h1
        · rw [h2] at hodd
          exact absurd hodd (by decide)
      · exfalso
        rw [h, Subgroup.card_top] at hodd
        have h2 : 2 ∣ Nat.card (Subgroup.centralizer ({z} : Set F)) := by
          rw [← hZ]
          exact Subgroup.card_subgroup_dvd_card _
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    apply hcard
    rw [hL.card_eq, hO, Subgroup.card_bot]

theorem NoWeakClassical3At.of_ambient_quasisimple {M : Type} [Group M] (H : Subgroup M) [Finite H]
    (t : H) (K : Subgroup M) (hK : centralizerIn H (t : M) = K)
    (hq : CFSG.Open.IsQuasisimple ↥K) (hZ : Nat.card (Subgroup.center ↥K) = 2)
    (hcard : Nat.card K ≠ 24) : NoWeakClassical3At t := by
  have hmapC : (Subgroup.centralizer ({t} : Set H)).map H.subtype = K := by
    rw [map_centralizer_subtype H t, hK]
  let e : ↥(Subgroup.centralizer ({t} : Set H)) ≃* ↥K :=
    (Subgroup.centralizer ({t} : Set H)).equivMapOfInjective H.subtype H.subtype_injective
      |>.trans (MulEquiv.subgroupCongr hmapC)
  have hqC : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({t} : Set H)) :=
    isQuasisimple_of_mulEquiv e.symm hq
  have hZC : Nat.card (Subgroup.center ↥(Subgroup.centralizer ({t} : Set H))) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hZ
  have hcardC : Nat.card (Subgroup.centralizer ({t} : Set H)) = Nat.card K :=
    Nat.card_congr e.toEquiv
  exact NoWeakClassical3At.of_isQuasisimple_centralizer hqC hZC (by rw [hcardC]; exact hcard)

theorem noWeakClassical3_of_single_class_quasisimple {M : Type} [Group M] (H S K : Subgroup M)
    [Finite H] (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ (S.subgroupOf H).index) {z : M} (hz : z ∈ H)
    (hSz : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ H, s = c * z * c⁻¹)
    (hK : centralizerIn H z = K) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hZ : Nat.card (Subgroup.center ↥K) = 2) (hcard : Nat.card K ≠ 24) : NoWeakClassical3 H :=
  noWeakClassical3_of_sylow_cover_at H S hS hidx hz hSz
    (NoWeakClassical3At.of_ambient_quasisimple H ⟨z, hz⟩ K hK hq hZ hcard)

end CFSG.ClassicalInvolution.Q3
