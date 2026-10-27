module

public import CFSG.GH74.Uniqueness.Section7Lemma711Aux
public import CFSG.GH74.Uniqueness.Theorem1Final

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.exists_bender_quotient_of_two_le_pRank
    (S : ZDSetup X Z M) {F : Subgroup X}
    (hF : F ≠ ⊤) (hFM : ¬ F ≤ M) (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hrank : 2 ≤ Open.pRank 2 (zHull Z F)) :
    ∃ (K : Type) (_ : Group K) (ψ : ↥(zHull Z F) →* K) (T₀ : Sylow 2 K),
      Function.Surjective ψ ∧ ψ.ker = pPrimeCore 2 ↥(zHull Z F) ∧
      CFSG.BenderSuzuki.IsBenderGroup K ∧
      ∀ g : ↥(zHull Z F), ψ g ∈ normalizer ((T₀ : Subgroup K) : Set K) ↔ (g : X) ∈ M := by
  have hrank2 : 2 ≤ Open.twoRank ↥(zHull Z F) := two_le_twoRank_of_two_le_pRank hrank
  have hLM : ¬ zHull Z F ≤ M := S.not_zHull_le hFM hne
  have hIH := S.zdConclusion_zHull hF hFM hne
  rw [zdConclusion_iff] at hIH
  obtain ⟨u₀, hdata⟩ :
      ∃ u, ZDData ↥(zHull Z F) {l | (l : X) ∈ Z} (M.comap (zHull Z F).subtype) u := by
    rcases hIH with h | h
    · omega
    · exact h
  have hD := hdata.toXData
  have hSE := S.prop44 benderFacts (S.no_solvable_normal benderFacts) hF hFM hne
  have hu1 : (u₀ : X) = 1 := by
    rcases hD.eq_one_or_orderOf_eq_two with h | h2
    · exact h
    · exfalso
      have hu : u₀ ∈ (M ⊓ zHull Z F).subgroupOf (zHull Z F) := by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨hD.mem_M, u₀.2⟩
      have hcent := centralizer_le_of_isStronglyEmbedded hSE hu (by rwa [← Subgroup.orderOf_coe])
      apply hLM
      intro l hl
      obtain ⟨o, ho, c, hcL, huc, rfl⟩ := hD.exists_mul_centralizer_L hl
      have hcY : (⟨c, hcL⟩ : ↥(zHull Z F)) ∈ centralizer ({u₀} : Set ↥(zHull Z F)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext huc.symm
      have hcM : c ∈ M := by
        have := hcent hcY
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at this
        exact this.1
      exact M.mul_mem (hD.O_M ho) hcM
  have hu₀ : u₀ = 1 := Subtype.ext hu1
  have hcomm : commutator ↥(zHull Z F) = ⊤ := by
    have h := hdata.sup
    rwa [hu₀, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at h
  obtain ⟨K, instK, φ, hφs, hφk, hKB, T₀, hT₀⟩ := hdata.bar
  have hmem : ∀ g : ↥(zHull Z F), g ∈ commutator ↥(zHull Z F) := fun g =>
    hcomm ▸ Subgroup.mem_top g
  let ι : ↥(zHull Z F) →* ↥(commutator ↥(zHull Z F)) :=
    (MonoidHom.id ↥(zHull Z F)).codRestrict (commutator ↥(zHull Z F)) hmem
  let ψ : ↥(zHull Z F) →* K := φ.comp ι
  have hψ : ∀ g : ↥(zHull Z F), ψ g = φ ⟨g, hmem g⟩ := fun g => rfl
  have hker : ψ.ker = pPrimeCore 2 ↥(zHull Z F) := by
    ext g
    rw [MonoidHom.mem_ker, hψ, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  refine ⟨K, instK, ψ, T₀, ?_, hker, hKB, ?_⟩
  · intro k
    obtain ⟨x, hx⟩ := hφs k
    exact ⟨x, by rw [hψ]; exact hx⟩
  · intro g
    have hle : ∀ x : ↥(zHull Z F), x ∈ pPrimeCore 2 ↥(zHull Z F) → (x : X) ∈ M := fun x hx =>
      hdata.le_M hx
    constructor
    · intro hg
      rw [← hT₀, hψ] at hg
      obtain ⟨m, hmA, hm⟩ := hg
      set x : ↥(commutator ↥(zHull Z F)) := ⟨g, hmem g⟩ with hx
      have hmx : m⁻¹ * x ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hm, inv_mul_cancel]
      have h1 : ((m⁻¹ * x : ↥(commutator ↥(zHull Z F))) : ↥(zHull Z F)) ∈
          pPrimeCore 2 ↥(zHull Z F) := by
        rw [hφk, Subgroup.mem_subgroupOf] at hmx
        exact hmx
      have hmM : ((m : ↥(zHull Z F)) : X) ∈ M := by
        have := hmA
        simpa [Subgroup.mem_subgroupOf] using this
      have h2 := hle _ h1
      have e : (g : X) = ((m : ↥(zHull Z F)) : X) *
          (((m⁻¹ * x : ↥(commutator ↥(zHull Z F))) : ↥(zHull Z F)) : X) := by
        simp [hx]
      rw [e]
      exact M.mul_mem hmM h2
    · intro hg
      rw [← hT₀, hψ]
      exact ⟨⟨g, hmem g⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

theorem ZDSetup.comm_mem_pPrimeCoreIn_zHull
    (S : ZDSetup X Z M) {F : Subgroup X} (hF : F ≠ ⊤)
    (hFM : ¬ F ≤ M) (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hrank : 2 ≤ Open.pRank 2 (zHull Z F)) {a b : X} (ha : a ∈ M ⊓ zHull Z F)
    (hb : b ∈ M ⊓ zHull Z F) (ha2 : a * a = 1) (hb2 : b * b = 1) :
    a * b * a⁻¹ * b⁻¹ ∈ pPrimeCoreIn (zHull Z F) := by
  obtain ⟨K, instK, ψ, T₀, -, hker, hKB, hT₀⟩ :=
    S.exists_bender_quotient_of_two_le_pRank hF hFM hne hrank
  have : Finite K := by
    obtain ⟨n, i, e, h⟩ := Bender.isBenderGroup_iff_exists_benderType.mp hKB
    cases h with
    | linear n hn e => exact Finite.of_equiv _ e.symm.toEquiv
    | suzuki a ha e => exact Finite.of_equiv _ e.symm.toEquiv
    | unitary n hn e => exact Finite.of_equiv _ e.symm.toEquiv
  set a' : ↥(zHull Z F) := ⟨a, (Subgroup.mem_inf.mp ha).2⟩ with ha'
  set b' : ↥(zHull Z F) := ⟨b, (Subgroup.mem_inf.mp hb).2⟩ with hb'
  have haN : ψ a' ∈ normalizer ((T₀ : Subgroup K) : Set K) := (hT₀ a').mpr (Subgroup.mem_inf.mp ha).1
  have hbN : ψ b' ∈ normalizer ((T₀ : Subgroup K) : Set K) := (hT₀ b').mpr (Subgroup.mem_inf.mp hb).1
  have ha2' : ψ a' * ψ a' = 1 := by
    rw [← map_mul]
    have : a' * a' = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hb2' : ψ b' * ψ b' = 1 := by
    rw [← map_mul]
    have : b' * b' = 1 := Subtype.ext hb2
    rw [this, map_one]
  have hc := commute_of_mem_normalizer_sylow_of_isBenderGroup hKB T₀ haN hbN ha2' hb2'
  have hmem : a' * b' * a'⁻¹ * b'⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  rw [hker] at hmem
  exact ⟨_, hmem, rfl⟩

theorem ZDSetup.exists_conj_of_involutions_zHull
    (S : ZDSetup X Z M) {F : Subgroup X}
    (hF : F ≠ ⊤) (hFM : ¬ F ≤ M) (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty)
    {a b : X} (ha : a ∈ M ⊓ zHull Z F) (hb : b ∈ M ⊓ zHull Z F) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) : ∃ g ∈ M ⊓ zHull Z F, g⁻¹ * a * g = b := by
  have hSE := S.prop44 benderFacts (S.no_solvable_normal benderFacts) hF hFM hne
  have hnat : CFSG.BenderSuzuki.IsStronglyEmbedded ((M ⊓ zHull Z F).subgroupOf (zHull Z F)) :=
    CFSG.BenderSuzuki.isStronglyEmbedded_of_parity _
      (isStronglyEmbeddedOrder_of_isStronglyEmbedded hSE)
  set a' : ↥(zHull Z F) := ⟨a, (Subgroup.mem_inf.mp ha).2⟩ with ha'
  set b' : ↥(zHull Z F) := ⟨b, (Subgroup.mem_inf.mp hb).2⟩ with hb'
  have haM : a' ∈ (M ⊓ zHull Z F).subgroupOf (zHull Z F) := Subgroup.mem_subgroupOf.mpr ha
  have hbM : b' ∈ (M ⊓ zHull Z F).subgroupOf (zHull Z F) := Subgroup.mem_subgroupOf.mpr hb
  have ha2' : orderOf a' = 2 := by rw [ha', Subgroup.orderOf_mk]; exact ha2
  have hb2' : orderOf b' = 2 := by rw [hb', Subgroup.orderOf_mk]; exact hb2
  have haI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution a' :=
    ⟨(orderOf_eq_prime_iff.mp ha2').2, (orderOf_eq_prime_iff.mp ha2').1⟩
  have hbI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution b' :=
    ⟨(orderOf_eq_prime_iff.mp hb2').2, (orderOf_eq_prime_iff.mp hb2').1⟩
  obtain ⟨g, hg, hgab⟩ := hnat.involutions_conjugate_in haM haI hbM hbI
  refine ⟨(g : X), Subgroup.mem_subgroupOf.mp hg, ?_⟩
  have := congrArg Subtype.val hgab
  simpa [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem] using this

end CFSG.GH74.Uniqueness
