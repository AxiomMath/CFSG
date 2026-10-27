module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParND
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParRank1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {K : Type*} {S : Type} [Group K] [Finite K] [Group S] [Finite S] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* S} {M : ℕ}

theorem eq_one_of_mem_ker_posUnipotent (h : BorelQuotient D n H π M) {z : K}
    (hz : z ∈ posUnipotent D) (hk : z ∈ π.ker) : z = 1 := by
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  obtain ⟨s, hs⟩ := (IsPGroup.iff_orderOf.1 hU2) ⟨z, hz⟩
  have hs' : orderOf z = 2 ^ s := by rw [← hs, ← Subgroup.orderOf_coe]
  have hM := h.ker_pow z hk
  have hcop : Nat.Coprime (2 ^ s) M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 h.odd)
  have h1 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop (hs' ▸ dvd_rfl)
    (orderOf_dvd_of_pow_eq_one hM)
  exact orderOf_eq_one_iff.1 h1

theorem false_of_odd_centralizes (h : BorelQuotient D n H π M) {j k : Fin D.rank} (hjk : j ≠ k)
    (hcart : D.cartan j k ≠ 0) {Wb Nb : Subgroup S}
    (hW : Wb ≤ Subgroup.normalizer (Nb : Set S))
    (hrank : (rankOne D.rootGroup j).map π ≤ Wb)
    (hXk : (D.rootGroup (Pi.single k 1)).map π ≤ Nb)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ y ∈ Wb, (∃ a : ℕ, orderOf y = p ^ a) →
      ∀ c ∈ Nb, y * c * y⁻¹ = c) : False := by
  classical
  have hαj : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  have hαk : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
  have hαj' : (-Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hαj
  let θ : ↥Wb →* MulAut ↥Nb := (Nb.normalizerMonoidHom).comp (Subgroup.inclusion hW)
  have hθ : ∀ (y : ↥Wb) (c : ↥Nb), ((θ y c : ↥Nb) : S) = (y : S) * c * (y : S)⁻¹ := fun y c =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (H := Nb) ⟨(y : S), hW y.2⟩ c
  have hθ2 : ∀ g : ↥Wb, ∃ s : ℕ, orderOf (θ g) = 2 ^ s := by
    intro g
    have hne : orderOf (θ g) ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (orderOf_map_dvd θ g) (orderOf_pos g)).ne'
    obtain ⟨s, m, hm, hr⟩ := Nat.exists_eq_two_pow_mul_odd hne
    by_cases hm1 : m = 1
    · exact ⟨s, by rw [hr, hm1, mul_one]⟩
    exfalso
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hpm)
    have hpr : p ∣ orderOf (θ g) := hr ▸ dvd_mul_of_dvd_right hpm _
    set g' : ↥Wb := g ^ (orderOf (θ g) / p) with hg'def
    have hg' : orderOf (θ g') = p := by
      rw [hg'def, map_pow]; exact orderOf_pow_orderOf_div hne hpr
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, ⟨a, ha⟩, hfe⟩ := exists_pElement_lift θ (p := p) (x := g')
      ⟨1, by rw [hg', pow_one]⟩
    have hcent := hodd p hp hp2 ((g' ^ e : ↥Wb) : S) (g' ^ e).2
      ⟨a, by rw [Subgroup.orderOf_coe]; exact ha⟩
    have h1 : θ (g' ^ e) = 1 := by
      refine MulEquiv.ext fun c => Subtype.ext ?_
      rw [hθ]
      exact hcent c c.2
    rw [hfe] at h1
    have := orderOf_eq_one_iff.2 h1
    rw [hg'] at this
    exact hp.one_lt.ne' this
  have hrk : ∀ x ∈ rankOne D.rootGroup j, π x ∈ Wb := fun x hx => hrank ⟨x, hx, rfl⟩
  set 𝒢 : Subgroup ↥Wb := ((rankOne D.rootGroup j).map π).subgroupOf Wb with h𝒢
  set A₀ : Subgroup ↥Wb := ((D.rootGroup (Pi.single j 1)).map π).subgroupOf Wb with hA₀
  set B₀ : Subgroup ↥Wb := ((D.rootGroup (-Pi.single j 1)).map π).subgroupOf Wb with hB₀
  set H₀ : Subgroup ↥Wb := ((H j).map π).subgroupOf Wb with hH₀
  set n₀ : ↥Wb := ⟨π (n j), hrk _ (h.ct.n_mem j)⟩ with hn₀
  have hXr : D.rootGroup (Pi.single j 1) ≤ rankOne D.rootGroup j := le_sup_left
  have hHr : H j ≤ rankOne D.rootGroup j := h.ct.H_le j
  have hle : A₀.map θ ≤ B₀.map θ := by
    refine map_le_map_of_two_group_image θ (𝒢 := 𝒢) (A := A₀) (B := B₀) (H := H₀) (n := n₀)
      (M := M) h.odd ?_ ?_ ?_ ?_ ?_ ?_ (fun g _ => hθ2 g)
    ·
      intro g hg
      obtain ⟨x, hx, hxg⟩ := (Subgroup.mem_subgroupOf.1 hg)
      rcases h.extras.rankOne_bruhat j x hx with ⟨t, ht, u, hu, rfl⟩ | ⟨u, hu, t, ht, v, hv, rfl⟩
      · left
        refine ⟨⟨π t, hrk t (hHr ht)⟩, Subgroup.mem_map_of_mem π ht,
          ⟨π u, hrk u (hXr hu)⟩, Subgroup.mem_map_of_mem π hu, ?_⟩
        apply Subtype.ext
        rw [← hxg, map_mul]
        rfl
      · right
        refine ⟨⟨π u, hrk u (hXr hu)⟩, Subgroup.mem_map_of_mem π hu,
          ⟨π t, hrk t (hHr ht)⟩, Subgroup.mem_map_of_mem π ht,
          ⟨π v, hrk v (hXr hv)⟩, Subgroup.mem_map_of_mem π hv, ?_⟩
        apply Subtype.ext
        rw [← hxg, map_mul, map_mul, map_mul]
        rfl
    · exact Subgroup.mem_map_of_mem π (h.ct.n_mem j)
    · intro x hx
      exact Subgroup.map_mono hXr hx
    · intro x hx
      exact Subgroup.map_mono hHr hx
    · rintro ⟨x, hxW⟩ hx
      obtain ⟨t, ht, rfl⟩ := hx
      apply Subtype.ext
      show (π t) ^ M = 1
      rw [← map_pow, h.torus_pow j t ht, map_one]
    · rintro ⟨x, hxW⟩ hx
      obtain ⟨a, ha, rfl⟩ := hx
      have h1 := (actsAs_n h.ct j).conj_mem hαj ha
      have h2 : weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j) (Pi.single j 1) =
          -Pi.single j 1 := weylAction_simple_single D.isFiniteType j
      rw [h2] at h1
      show π (n j) * π a * (π (n j))⁻¹ ∈ (D.rootGroup (-Pi.single j 1)).map π
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map_of_mem π h1
  obtain ⟨a, ha, c, hc, hac⟩ := exists_not_commute_of_cartan_ne_zero h.ct h.extras hjk hcart
  have haW : π a ∈ Wb := hrk a (hXr ha)
  have hcN : π c ∈ Nb := hXk (Subgroup.mem_map_of_mem π hc)
  have hmem : (⟨π a, haW⟩ : ↥Wb) ∈ A₀ := Subgroup.mem_map_of_mem π ha
  obtain ⟨b', hb', hb'e⟩ := hle (Subgroup.mem_map_of_mem θ hmem)
  obtain ⟨b, hb, hbπ⟩ := Subgroup.mem_subgroupOf.1 hb'
  have e1 := congrArg (fun φ : MulAut ↥Nb => ((φ ⟨π c, hcN⟩ : ↥Nb) : S)) hb'e
  simp only [hθ] at e1
  have e2 : (b' : S) * π c * (b' : S)⁻¹ = π c := by
    rw [← hbπ]
    have := commute_neg_single_single h.extras hjk hb hc
    rw [← map_inv, ← map_mul, ← map_mul, this]
    group
  have e3 : π a * π c * (π a)⁻¹ = π c := e1.symm.trans e2
  have hker : a * c * a⁻¹ * c⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [e3]; group
  have hU : a * c * a⁻¹ * c⁻¹ ∈ posUnipotent D := by
    have haU : a ∈ posUnipotent D := rootGroup_le_posUnipotent hαj (ht_single_pos j) ha
    have hcU : c ∈ posUnipotent D := rootGroup_le_posUnipotent hαk (ht_single_pos k) hc
    exact mul_mem (mul_mem (mul_mem haU hcU) (inv_mem haU)) (inv_mem hcU)
  have h1 := eq_one_of_mem_ker_posUnipotent h hU hker
  apply hac
  have : a * c * a⁻¹ * c⁻¹ = 1 := h1
  have h2 := mul_inv_eq_one.1 this
  exact mul_inv_eq_iff_eq_mul.1 h2

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
