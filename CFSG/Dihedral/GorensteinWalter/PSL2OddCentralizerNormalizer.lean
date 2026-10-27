module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflection
public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionRootSupport
public import CFSG.GroupTheory.CentralizerMap

public noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.External

universe u

theorem odd_centralizer_normalizer_of_reflected_torus
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (s w : G)
    (hsU : s ∈ U) (hsI : BenderSuzuki.PFAppendixIII.IsInvolution s)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hnormalizer : ∀ A : Subgroup G, A ≤ U → A ≠ ⊥ →
      Subgroup.normalizer (A : Set G) = U ⊔ Subgroup.zpowers w)
    (X : Subgroup G) (hXne : X ≠ ⊥)
    (hXodd : ∀ x : G, x ∈ X → Odd (orderOf x))
    (hXcent : X ≤ Subgroup.centralizer ({s} : Set G)) :
    Subgroup.normalizer (X : Set G) = Subgroup.centralizer ({s} : Set G) := by
  have hXU := odd_centralizer_le_torus_of_inverting_join U s w
    hsU hsI hwU hwsq hwinv hnormalizer X hXodd hXcent
  have hsord : orderOf s = 2 := orderOf_eq_prime hsI.2 hsI.1
  let i : DisconnectedInvolutionGraph.Helpers.Involution G := ⟨s, hsord⟩
  have hz : Subgroup.zpowers s ≠ ⊥ := by
    intro h
    exact hsI.1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers s))
  calc
    Subgroup.normalizer (X : Set G) = U ⊔ Subgroup.zpowers w :=
      hnormalizer X hXU hXne
    _ = Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
      (hnormalizer (Subgroup.zpowers s) (Subgroup.zpowers_le.mpr hsU) hz).symm
    _ = Subgroup.centralizer ({s} : Set G) :=
      DisconnectedInvolutionGraph.Helpers.involution_zpowers_normalizer_eq_centralizer i

theorem odd_centralizer_normalizer_of_even_torus
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (U : Subgroup (PSL2 K)) (w : PSL2 K)
    (hUeven : Even (Nat.card U)) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : PSL2 K, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hnormalizer : ∀ A : Subgroup (PSL2 K), A ≤ U → A ≠ ⊥ →
      Subgroup.normalizer (A : Set (PSL2 K)) = U ⊔ Subgroup.zpowers w)
    {t : PSL2 K} (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (X : Subgroup (PSL2 K)) (hXne : X ≠ ⊥)
    (hXodd : ∀ x : PSL2 K, x ∈ X → Odd (orderOf x))
    (hXcent : X ≤ Subgroup.centralizer ({t} : Set (PSL2 K))) :
    Subgroup.normalizer (X : Set (PSL2 K)) =
      Subgroup.centralizer ({t} : Set (PSL2 K)) := by
  obtain ⟨sU, hsUord⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 hUeven.two_dvd
  let s0 : PSL2 K := sU
  have hs0ord : orderOf s0 = 2 :=
    (orderOf_injective U.subtype U.subtype_injective sU).trans hsUord
  have hs0I : BenderSuzuki.PFAppendixIII.IsInvolution s0 := by
    refine ⟨?_, ?_⟩
    · intro h
      simp [h] at hs0ord
    · simpa only [hs0ord] using pow_orderOf_eq_one s0
  obtain ⟨g, hgt⟩ := psl2_involutions_conjugate_of_odd_prime_power K hK s0 t hs0I ht
  let e : PSL2 K ≃* PSL2 K := MulAut.conj g
  let X0 : Subgroup (PSL2 K) := X.comap e.toMonoidHom
  have hX0map : X0.map e.toMonoidHom = X :=
    Subgroup.map_comap_eq_self (by
      intro x _
      exact ⟨e.symm x, e.apply_symm_apply x⟩)
  have hX0ne : X0 ≠ ⊥ := by
    intro h
    apply hXne
    rw [← hX0map, h, Subgroup.map_bot]
  have hX0odd : ∀ x : PSL2 K, x ∈ X0 → Odd (orderOf x) := by
    intro x hx
    have ho := hXodd (e x) hx
    rwa [e.orderOf_eq] at ho
  have hX0cent : X0 ≤ Subgroup.centralizer ({s0} : Set (PSL2 K)) := by
    intro x hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply e.injective
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hXcent hx)
    change e x * t = t * e x at hcomm
    have he : e s0 = t := hgt
    simpa only [map_mul, he] using hcomm
  have hbase := odd_centralizer_normalizer_of_reflected_torus U s0 w
    sU.2 hs0I hwU hwsq hwinv hnormalizer X0 hX0ne hX0odd hX0cent
  calc
    Subgroup.normalizer (X : Set (PSL2 K)) =
        (Subgroup.normalizer (X0 : Set (PSL2 K))).map e.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq, hX0map]
    _ = (Subgroup.centralizer ({s0} : Set (PSL2 K))).map e.toMonoidHom := by
      rw [hbase]
    _ = Subgroup.centralizer ({t} : Set (PSL2 K)) := by
      rw [centralizer_singleton_map]
      change Subgroup.centralizer ({g * s0 * g⁻¹} : Set (PSL2 K)) = _
      rw [hgt]

theorem psl2_odd_centralizer_normalizer
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    {t : PSL2 K} (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (X : Subgroup (PSL2 K)) (hXne : X ≠ ⊥)
    (hXodd : ∀ x : PSL2 K, x ∈ X → Odd (orderOf x))
    (hXcent : X ≤ Subgroup.centralizer ({t} : Set (PSL2 K))) :
    Subgroup.normalizer (X : Set (PSL2 K)) =
      Subgroup.centralizer ({t} : Set (PSL2 K)) := by
  have hqodd : Odd (Nat.card K) := by
    rcases hK with ⟨p, f, _, hpodd, _, hcard⟩
    rw [hcard]
    exact hpodd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 :=
    gcd_sub_one_two_of_odd hqodd
  rcases hK with ⟨p, f, hp, hpodd, hf, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hKfull : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hpodd, hf, hcard⟩
  rcases Nat.even_or_odd ((Nat.card K - 1) / 2) with hsplit | hnonsplit
  · obtain ⟨U, w, _hUcyc, hUcard, _hwN, hwU, hwsq, hwinv, _hDcard, hnormalizer⟩ :=
      huppert_II_8_3_split_torus_reflection_data (F := K) (p := p) (f := f) hcard
    have hUeven : Even (Nat.card U) := by
      rw [hUcard, hgcd]
      exact hsplit
    exact odd_centralizer_normalizer_of_even_torus hKfull U w hUeven hwU hwsq
      hwinv hnormalizer ht X hXne hXodd hXcent
  · obtain ⟨U, w, _hUcyc, hUcard, _hwN, hwU, hwsq, hwinv, _hDcard, hnormalizer⟩ :=
      huppert_II_8_4_nonsplit_torus_reflection_data (F := K) (p := p) (f := f) hcard
    have hhalfEven : Even ((Nat.card K + 1) / 2) := by
      rcases hnonsplit with ⟨k, hk⟩
      use k + 1
      omega
    have hUeven : Even (Nat.card U) := by
      rw [hUcard, hgcd]
      exact hhalfEven
    exact odd_centralizer_normalizer_of_even_torus hKfull U w hUeven hwU hwsq
      hwinv hnormalizer ht X hXne hXodd hXcent

end CFSG.GorensteinWalter
