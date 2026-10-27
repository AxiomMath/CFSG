module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G]

theorem four_le_card_sylow_of_isQuasisimple {M : Type*} [Group M] [Finite M]
    (hq : CFSG.IsQuasisimple M) (P : Sylow 2 M) : 4 ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  have hcyc : ∀ Q : Sylow 2 M, IsCyclic Q := by
    intro Q
    have h1 : Nat.card Q = Nat.card P := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
    have hn1 : n ≤ 1 := by
      by_contra hn2
      push Not at hn2
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    interval_cases n
    · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.1 (by simpa using hn)).1
      infer_instance
    · exact isCyclic_of_prime_card (by simpa using hn)
  have hsolv := isSolvable_of_cyclic_sylow_two hcyc
  have := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsPerfect M := hq.1
  exact Group.IsPerfect.not_isSolvable M hsolv

theorem normal_of_component_of_card_sylow [Finite G] {M X : Subgroup G} (hM : IsCompIn M X)
    (hSyl : ∀ S : Sylow 2 (centralizer (M : Set G)), Nat.card S = 2) :
    (M.subgroupOf X).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hM.1]
  intro h hh
  rw [CFSG.EvenSporadicStandard.Solomon78.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set N : Subgroup G := M.map (MulAut.conj h).toMonoidHom with hN
  have hNc : IsCompIn N X := hM.map_conj hh
  have hNM : N ≤ centralizer (M : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => (hNc.commute_of_ne hM hne a ha b hb).symm
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥N) := inferInstance
  have h4 := four_le_card_sylow_of_isQuasisimple hNc.isQuasisimple P
  let P' : Subgroup G := (P : Subgroup ↥N).map N.subtype
  have hP'le : P' ≤ centralizer (M : Set G) := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact hNM y.2
  let Q : Subgroup ↥(centralizer (M : Set G)) := P'.subgroupOf (centralizer (M : Set G))
  have hcardQ : Nat.card Q = Nat.card P := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'le).toEquiv,
      Subgroup.card_map_of_injective N.subtype_injective]
  have hQp : IsPGroup 2 Q := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (by rw [hcardQ]; exact hn)
  obtain ⟨S, hS⟩ := hQp.exists_le_sylow
  have := Subgroup.card_le_of_le hS
  have h2 := hSyl S
  omega

theorem inn_normal (M : Type) [Group M] : ((MulAut.conj : M →* MulAut M).range).Normal := by
  refine ⟨fun a ha β => ?_⟩
  obtain ⟨l, rfl⟩ := ha
  refine ⟨β l, ?_⟩
  ext x
  simp [MulAut.conj_apply]

omit [Group G] in
theorem relIndex_le_two_of_outTwo [Group G] {M H : Subgroup G} (hMH : M ≤ H)
    (hMn : (M.subgroupOf H).Normal) (hout : OutTwo ↥M) :
    (M ⊔ (centralizer (M : Set G) ⊓ H)).relIndex H ≤ 2 := by
  set D : Subgroup G := centralizer (M : Set G) ⊓ H with hD
  have hHN : H ≤ normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMH).1 hMn
  let ψ : ↥H →* MulAut ↥M := (Subgroup.normalizerMonoidHom M).comp (Subgroup.inclusion hHN)
  have hψ : ∀ (h : ↥H) (m : ↥M), ((ψ h m : ↥M) : G) = h * m * (h : G)⁻¹ := fun h m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨h, hHN h.2⟩ m
  let Inn : Subgroup (MulAut ↥M) := (MulAut.conj : ↥M →* MulAut ↥M).range
  have : Inn.Normal := inn_normal ↥M
  let q : MulAut ↥M →* MulAut ↥M ⧸ Inn := QuotientGroup.mk' Inn
  let φ : ↥H →* MulAut ↥M ⧸ Inn := q.comp ψ
  have hker : ∀ h : ↥H, h ∈ φ.ker ↔ ∃ l : ↥M, ψ h = MulAut.conj l := by
    intro h
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk (ψ h) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨l, hl⟩
      exact ⟨l, hl.symm⟩
    · rintro ⟨l, hl⟩
      exact ⟨l, hl.symm⟩
  have hsub : (M ⊔ D).subgroupOf H = φ.ker := by
    apply le_antisymm
    · intro h hh
      have hle : M ⊔ D ≤ φ.ker.map H.subtype := by
        refine sup_le ?_ ?_
        · intro m hm
          refine ⟨⟨m, hMH hm⟩, ?_, rfl⟩
          show (⟨m, hMH hm⟩ : ↥H) ∈ φ.ker
          rw [hker]
          refine ⟨⟨m, hm⟩, ?_⟩
          ext x
          rw [hψ]
          simp [MulAut.conj_apply]
        · intro d hd
          refine ⟨⟨d, hd.2⟩, ?_, rfl⟩
          show (⟨d, hd.2⟩ : ↥H) ∈ φ.ker
          rw [hker]
          refine ⟨1, ?_⟩
          ext x
          rw [hψ]
          have hcomm : (x : G) * d = d * x := mem_centralizer_iff.1 hd.1 x x.2
          simp only [map_one, MulAut.one_apply]
          calc d * (x : G) * d⁻¹ = (x * d) * d⁻¹ := by rw [hcomm]
            _ = x := by group
      obtain ⟨h', hh', hh'e⟩ := hle (mem_subgroupOf.1 hh)
      have : h' = h := Subtype.ext hh'e
      rwa [this] at hh'
    · intro h hh
      rw [mem_subgroupOf]
      obtain ⟨l, hl⟩ := (hker h).1 hh
      have hmem : (l : G)⁻¹ * h ∈ D := by
        refine ⟨mem_centralizer_iff.2 fun m hm => ?_, ?_⟩
        · have h1 := hψ h ⟨m, hm⟩
          rw [hl] at h1
          simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
          calc m * ((l : G)⁻¹ * h) = (l : G)⁻¹ * ((l : G) * m * (l : G)⁻¹) * h := by group
            _ = (l : G)⁻¹ * (h * m * (h : G)⁻¹) * h := by rw [h1]
            _ = ((l : G)⁻¹ * h) * m := by group
        · exact H.mul_mem (H.inv_mem (hMH l.2)) h.2
      have : (h : G) = (l : G) * ((l : G)⁻¹ * h) := by group
      rw [this]
      exact mul_mem_sup l.2 hmem
  rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
  by_cases hall : ∀ a ∈ φ.range, a = 1
  · have : Subsingleton φ.range := ⟨fun a b => Subtype.ext ((hall a a.2).trans (hall b b.2).symm)⟩
    have : Nat.card φ.range = 1 := Nat.card_unique
    omega
  · push Not at hall
    obtain ⟨y, hy, hy1⟩ := hall
    have hsurj : Function.Surjective (fun b : Bool =>
        if b then (⟨y, hy⟩ : φ.range) else 1) := by
      intro a
      obtain ⟨α₀, hα₀⟩ := QuotientGroup.mk_surjective (a : MulAut ↥M ⧸ Inn)
      obtain ⟨β₀, hβ₀⟩ := QuotientGroup.mk_surjective y
      rcases hout α₀ β₀ with h1 | h1 | h1
      · refine ⟨false, ?_⟩
        apply Subtype.ext
        obtain ⟨l, hl⟩ := h1
        have : (a : MulAut ↥M ⧸ Inn) = 1 := by
          rw [← hα₀]
          exact (QuotientGroup.eq_one_iff _).2 ⟨l, hl.symm⟩
        simp [this]
      · exfalso
        obtain ⟨l, hl⟩ := h1
        apply hy1
        rw [← hβ₀]
        exact (QuotientGroup.eq_one_iff _).2 ⟨l, hl.symm⟩
      · refine ⟨true, ?_⟩
        apply Subtype.ext
        obtain ⟨l, hl⟩ := h1
        have h2 : (QuotientGroup.mk α₀ : MulAut ↥M ⧸ Inn)⁻¹ * QuotientGroup.mk β₀ = 1 := by
          rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
          exact (QuotientGroup.eq_one_iff _).2 ⟨l, hl.symm⟩
        rw [hα₀, hβ₀] at h2
        have : (a : MulAut ↥M ⧸ Inn) = y := by
          rwa [inv_mul_eq_one] at h2
        simp [this]
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this

omit [Group G] in
theorem false_of_typeL_component [Group G] [Finite G] {u : G} (hu : orderOf u = 2)
    {M : Subgroup G} (hM : IsCompIn M (centralizer ({u} : Set G)))
    (hMz : Odd (Nat.card (center ↥M))) (hout : OutTwo ↥M)
    (hSyl : ∀ S : Sylow 2 (centralizer (M : Set G)), Nat.card S = 2)
    (hcomm : u ∈ ⁅centralizer ({u} : Set G), centralizer ({u} : Set G)⁆) : False := by
  have hMn := normal_of_component_of_card_sylow hM hSyl
  have hidx := relIndex_le_two_of_outTwo hM.1 hMn hout
  exact not_mem_commutator_of_transfer hu hM.1 hMn hMz hSyl hidx hcomm

end CFSG.EvenSporadicStandard.Induction
