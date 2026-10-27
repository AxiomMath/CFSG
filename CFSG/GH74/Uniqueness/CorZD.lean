module

public import CFSG.GH74.KGH
public import CFSG.GH74.Uniqueness.Statements

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem isBenderGroup_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.BenderSuzuki.IsBenderGroup B) : CFSG.BenderSuzuki.IsBenderGroup A := by
  rcases h with ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩
  · exact CFSG.BenderSuzuki.IsBenderGroup.isPSL2 n hn (e.trans e')
  · exact CFSG.BenderSuzuki.IsBenderGroup.isSuzuki n hn (e.trans e')
  · exact CFSG.BenderSuzuki.IsBenderGroup.isPSU3 n hn (e.trans e')

theorem IsInvariantInvolutionSet.normal_closure {X : Type*} [Group X] {Z : Set X}
    (hZ : IsInvariantInvolutionSet Z) : (Subgroup.closure Z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem z hz =>
    have := hZ.2 z hz g⁻¹
    rw [inv_inv] at this
    exact Subgroup.subset_closure this
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

theorem exists_mulEquiv_derivedBar (Y : Type*) [Group Y] (hD : commutator Y = ⊤)
    (hN : pPrimeCore 2 Y = ⊥) :
    ∃ e : Y ≃* derivedBar Y, ∀ M : Subgroup Y, derivedBarImage M = M.map e.toMonoidHom := by
  have hmem : ∀ y : Y, y ∈ commutator Y := fun y => hD ▸ Subgroup.mem_top y
  let q : Y →* derivedBar Y :=
    (QuotientGroup.mk' ((pPrimeCore 2 Y).subgroupOf (commutator Y))).comp
      ((MonoidHom.id Y).codRestrict (commutator Y) hmem)
  have hinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : (⟨y, hmem y⟩ : ↥(commutator Y)) ∈ (pPrimeCore 2 Y).subgroupOf (commutator Y) :=
      (QuotientGroup.eq_one_iff _).mp hy
    have h2 : y ∈ pPrimeCore 2 Y := h1
    rw [hN, Subgroup.mem_bot] at h2
    exact (Subgroup.mem_bot).2 h2
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨d, rfl⟩
  refine ⟨MulEquiv.ofBijective q ⟨hinj, hsurj⟩, fun M => ?_⟩
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨(d : Y), (Subgroup.mem_inf.mp hd).1, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hmem y⟩, Subgroup.mem_inf.mpr ⟨hy, hmem y⟩, rfl⟩

open scoped commutatorElement in
theorem S_CorZD_of_S_ZD_gen (h : S_ZD_gen) : S_CorZD := by
  intro X _ _ hsimple hnonab Z M hZ hPD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hclos : Subgroup.closure Z = ⊤ := by
    have hnormal := hZ.normal_closure
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.closure Z) with hb | ht
    · exfalso
      obtain ⟨z, hz, -⟩ := hPD.2.1
      have hz' : z ∈ Subgroup.closure Z := Subgroup.subset_closure hz
      rw [hb, Subgroup.mem_bot] at hz'
      have h2 := hZ.1 z hz
      rw [hz', orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact ht
  have hD : commutator X = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (commutator X) with hb | ht
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact ht
  have hN : pPrimeCore 2 X = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (pPrimeCore 2 X) with hb | ht
    · exact hb
    · exfalso
      have hcop := pPrimeCore_coprime_card (p := 2) (G := X)
      rw [ht, Subgroup.card_top] at hcop
      exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp hcop))
        (even_card_of_nonabelian_simple hnonab)
  rcases h X Z M hZ hclos hPD with hrank | ⟨u, -, -, -, -, -, -, -, hBender, hBorel, -⟩
  · exfalso
    have h2 : 2 ≤ Open.twoRank X := CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound X
      hnonab (even_card_of_nonabelian_simple hnonab)
    omega
  · obtain ⟨e, he⟩ := exists_mulEquiv_derivedBar X hD hN
    refine ⟨isBenderGroup_of_mulEquiv e hBender, ?_⟩
    obtain ⟨S', hS'⟩ := hBorel
    have hsurj : Function.Surjective (e.symm.toMonoidHom : derivedBar X →* X) := e.symm.surjective
    have hbij : Function.Bijective (e.symm.toMonoidHom : derivedBar X →* X) := e.symm.bijective
    refine ⟨Sylow.mapSurjective hsurj S', ?_⟩
    have hcoe : ((Sylow.mapSurjective hsurj S' : Sylow 2 X) : Subgroup X) =
        (S' : Subgroup (derivedBar X)).map e.symm.toMonoidHom := rfl
    change M = normalizer (((Sylow.mapSurjective hsurj S' : Sylow 2 X) : Subgroup X) : Set X)
    rw [hcoe, ← Subgroup.map_normalizer_eq_of_bijective _ hbij, ← hS', he]
    ext x
    simp [Subgroup.mem_map]

end CFSG.GH74.Uniqueness
