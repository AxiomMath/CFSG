module

public import CFSG.ClassicalInvolution.Asc77.AscIHHelp
public import CFSG.ClassicalInvolution.Asc77.AscIHSL2
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsG2
public import CFSG.ClassicalInvolution.Asc77.AscIHWitness

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Centralizer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem not_aEmpty_of_centralizer_witness (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hnc : ¬ ∃ g : G, conjSub g K = J) {z : G}
    (hz : IsUniqueInvolution K z) (P : Sylow 2 ↥J) (u : ↥J) (huP : u ∈ (P : Subgroup ↥J))
    (hidx : (Subgroup.zpowers u).relIndex (P : Subgroup ↥J) = 2) (hnoncen : ∃ w : ↥J, u * w ≠ w * u)
    (huz : (u : G) * z = z * (u : G))
    (hb : ∀ P' : Sylow 2 ↥J, ∃ x ∈ (P' : Subgroup ↥J), (x : G) * z ≠ z * (x : G)) :
    ¬ AEmpty Ω K := by
  have hKJ : K ≠ J := fun h => hnc ⟨1, by rw [conjSub_one, h]⟩
  have hu2 : IsPGroup 2 (Subgroup.zpowers (u : G)) := by
    have h1 : IsPGroup 2 ((P : Subgroup ↥J).map J.subtype) := P.isPGroup'.map _
    refine h1.to_le ?_
    rw [Subgroup.zpowers_le]
    exact ⟨u, huP, rfl⟩
  obtain ⟨w, hw⟩ := hnoncen
  have hun : (u : G) ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.omega5 K hK J hJ hKJ z hz (u : G) u.2 (fun h => hw (Subtype.ext (h w w.2))) hu2 huz
  refine not_aEmpty_of_u2Witness hp2 hq hΩ hK hJ hnc ⟨⟨P, Subgroup.zpowers u, ?_, ?_, hidx, ?_⟩, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact huP
  · infer_instance
  · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact hun
  · intro P' hP'
    obtain ⟨x, hxP', hx⟩ := hb P'
    have h1 : (x : G) ∈ Subgroup.normalizer (K : Set G) := hP' ⟨x, hxP', rfl⟩
    have h2 := hz.conj_eq (conjSub_eq_of_mem_normalizer h1)
    apply hx
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2

end Centralizer

section G2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem g2_model_involutions_conj {t : StatedLieTag} {n e : ℕ} (ht : t = .G2) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) {z z' : (modelUniv t n p e Fact.out).K}
    (hz : z * z = 1) (hz' : z' * z' = 1) (hz1 : z ≠ 1) (hz1' : z' ≠ 1) :
    ∃ h, h * z * h⁻¹ = z' := by
  subst ht
  have hK : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  exact Balance.Bootstrap.g2_involutions_conj hK hz hz' hz1 hz1'

private theorem eq_of_map_eq_of_injOn {M X : Type*} [Group M] [Group X] (ψ : M →* X)
    {T : Subgroup M}
    (hinj : ∀ x ∈ T, ψ x = 1 → x = 1) {x y : M} (hx : x ∈ T) (hy : y ∈ T) (h : ψ x = ψ y) :
    x = y := by
  have : x⁻¹ * y = 1 := hinj _ (T.mul_mem (T.inv_mem hx) hy) (by simp [map_mul, map_inv, h])
  exact inv_mul_eq_one.mp this

theorem false_of_g2_pair (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    (hA : ∀ K ∈ Ω, AEmpty Ω K) (D : OmegaLie p f Ω) (i : Fin D.card) (hG2 : D.tag i = .G2)
    {R S : Subgroup (D.model i).K} (hR : R ∈ fundamentalSubgroups (D.tag i) (D.model i).D)
    (hS : S ∈ fundamentalSubgroups (D.tag i) (D.model i).D)
    (hK : R.map (D.hom i) ∈ Ω) (hJ : S.map (D.hom i) ∈ Ω)
    (hnc : ¬ ∃ g : G, conjSub g (R.map (D.hom i)) = S.map (D.hom i)) : False := by
  have hne : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := fun h => by
    rw [hG2] at h
    exact absurd h.1 (by decide)
  have hker := D.ker_le_center i
  have hinjR := D.injOn_fund i hne hR
  have hinjS := D.injOn_fund i hne hS
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp2 hq
  set K := R.map (D.hom i) with hKdef
  set J := S.map (D.hom i) with hJdef
  obtain ⟨zK, hzK0⟩ := hΩ.classical K hK
  obtain ⟨zJ, hzJ0⟩ := hΩ.classical J hJ
  have hzK := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hzK0
  have hzJ := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hzJ0
  obtain ⟨rR, hrR, hψrR⟩ := hzK.mem
  obtain ⟨rS, hrS, hψrS⟩ := hzJ.mem
  have hrR2 : rR * rR = 1 := by
    refine eq_of_map_eq_of_injOn (D.hom i) hinjR (R.mul_mem hrR hrR) R.one_mem ?_
    rw [map_mul, hψrR, map_one, hzK.sq]
  have hrS2 : rS * rS = 1 := by
    refine eq_of_map_eq_of_injOn (D.hom i) hinjS (S.mul_mem hrS hrS) S.one_mem ?_
    rw [map_mul, hψrS, map_one, hzJ.sq]
  have hrR1 : rR ≠ 1 := fun h => hzK.ne_one (by rw [← hψrR, h, map_one])
  have hrS1 : rS ≠ 1 := fun h => hzJ.ne_one (by rw [← hψrS, h, map_one])
  obtain ⟨g, hg⟩ := g2_model_involutions_conj hG2 hp2 (D.admissible i) hrR2 hrS2 hrR1 hrS1
  set K₀ := conjSub (D.hom i g) K with hK₀def
  have hK₀Ω : K₀ ∈ Ω := hΩ.conjInvariant _ K hK
  have hzK₀ : IsUniqueInvolution K₀ zJ := by
    have h1 := hzK.conj (D.hom i g)
    have e : D.hom i g * zK * (D.hom i g)⁻¹ = zJ := by
      rw [← hψrR, ← hψrS, ← hg]
      simp [map_mul, map_inv]
    rwa [e] at h1
  have hK₀J : K₀ ≠ J := fun h => hnc ⟨D.hom i g, h⟩
  obtain ⟨hv, hcommv⟩ := hΩ.omega4 K₀ hK₀Ω J hJ hK₀J
  have hdvd2 : 2 ∣ Nat.card ↥(K₀ ⊓ J) := by
    have hmem : zJ ∈ K₀ ⊓ J := ⟨hzK₀.mem, hzJ.mem⟩
    have := Subgroup.orderOf_dvd_natCard (K₀ ⊓ J) hmem
    rwa [hzJ0.orderOf_eq_two] at this
  have hcard0 : Nat.card ↥(K₀ ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have hcomm : Commutes K₀ J := by
    apply hcommv
    have := one_le_padicValNat_of_dvd hcard0 hdvd2
    omega
  obtain ⟨eK⟩ := hzK0.nonempty_equiv_sl2 (hΩ.exact K hK)
  obtain ⟨eJ⟩ := hzJ0.nonempty_equiv_sl2 (hΩ.exact J hJ)
  obtain ⟨-, -, cK, -, -, -, -, hcKo, -⟩ := sl2_witness hodd eK
  obtain ⟨P, u, j, huP, hidx, hnoncen, hju, hjo, hb⟩ := sl2_witness hodd eJ
  have hsq_eq : ∀ {L : Subgroup G} {w y : G}, IsUniqueInvolution L w → y ∈ L → orderOf y = 4 →
      y ^ 2 = w := by
    intro L w y hw hy hoy
    have h4 : y ^ 2 * y ^ 2 = 1 := by
      rw [← pow_add]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hoy])
    rcases hw.unique (y ^ 2) (L.pow_mem hy 2) h4 with h | h
    · exfalso
      have := orderOf_dvd_of_pow_eq_one h
      rw [hoy] at this
      omega
    · exact h
  have hcK : (cK : G) ^ 2 = zK :=
    hsq_eq hzK cK.2 (by rw [Subgroup.orderOf_coe]; exact hcKo)
  have hj : (j : G) ^ 2 = zJ :=
    hsq_eq hzJ j.2 (by rw [Subgroup.orderOf_coe]; exact hjo)
  obtain ⟨c₀, hc₀R, hψc₀⟩ : (cK : G) ∈ K := cK.2
  obtain ⟨j₀, hj₀S, hψj₀⟩ : (j : G) ∈ J := j.2
  have hc₀sq : c₀ * c₀ = rR := by
    refine eq_of_map_eq_of_injOn (D.hom i) hinjR (R.mul_mem hc₀R hc₀R) hrR ?_
    rw [map_mul, hψc₀, hψrR, ← sq, hcK]
  have hj₀sq : j₀ * j₀ = rS := by
    refine eq_of_map_eq_of_injOn (D.hom i) hinjS (S.mul_mem hj₀S hj₀S) hrS ?_
    rw [map_mul, hψj₀, hψrS, ← sq, hj]
  set c₁ : (D.model i).K := g * c₀ * g⁻¹ with hc₁def
  have hc₁sq : c₁ * c₁ = rS := by
    rw [hc₁def, ← hg]
    calc g * c₀ * g⁻¹ * (g * c₀ * g⁻¹) = g * (c₀ * c₀) * g⁻¹ := by group
      _ = g * rR * g⁻¹ := by rw [hc₀sq]
  have hψc₁ : D.hom i c₁ = D.hom i g * (cK : G) * (D.hom i g)⁻¹ := by
    rw [hc₁def, map_mul, map_mul, map_inv, hψc₀]
  have hc₁K₀ : D.hom i c₁ ∈ K₀ := by
    rw [hψc₁]
    exact conj_mem_conjSub cK.2
  have hperfK : Group.IsPerfect ↥K := hzK0.perfect
  have hperfR : Group.IsPerfect ↥R := isPerfect_of_map (D.hom i) hinjR hperfK
  have hperfR₀ : Group.IsPerfect ↥(R.map (MulAut.conj g).toMonoidHom) :=
    Group.IsPerfect.map (MulAut.conj g).toMonoidHom
  have hcommM : Commutes (R.map (MulAut.conj g).toMonoidHom) S :=
    RouteD.commutes_of_commutes_map (D.hom i) hker hperfR₀
      (by rw [map_conj_eq_conjSub_map]; exact hcomm)
  have hc₁S : c₁ * j₀ = j₀ * c₁ := hcommM c₁ ⟨c₀, hc₀R, rfl⟩ j₀ hj₀S
  set m₁ : (D.model i).K := j₀ * c₁ with hm₁def
  have hm₁sq : m₁ * m₁ = 1 := by
    calc j₀ * c₁ * (j₀ * c₁) = j₀ * (c₁ * j₀) * c₁ := by group
      _ = j₀ * (j₀ * c₁) * c₁ := by rw [hc₁S]
      _ = (j₀ * j₀) * (c₁ * c₁) := by group
      _ = 1 := by rw [hj₀sq, hc₁sq, hrS2]
  set z₁ : G := (j : G) * D.hom i c₁ with hz₁def
  have hψm₁ : D.hom i m₁ = z₁ := by rw [hm₁def, map_mul, hψj₀]
  have hjo' : orderOf (j : G) = 4 := by rw [Subgroup.orderOf_coe]; exact hjo
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    have hjc : (j : G) = (D.hom i c₁)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hmem : (j : G) ∈ K₀ ⊓ J := ⟨by rw [hjc]; exact K₀.inv_mem hc₁K₀, j.2⟩
    have h4 : 2 ^ 2 ∣ Nat.card ↥(K₀ ⊓ J) := by
      have := Subgroup.orderOf_dvd_natCard (K₀ ⊓ J) hmem
      rwa [hjo'] at this
    have := (padicValNat_dvd_iff_le hcard0).mp h4
    omega
  have hm₁1 : m₁ ≠ 1 := fun h => hz₁1 (by rw [← hψm₁, h, map_one])
  obtain ⟨h, hh⟩ := g2_model_involutions_conj hG2 hp2 (D.admissible i) hrR2 hm₁sq hrR1 hm₁1
  set K' := conjSub (D.hom i h) K with hK'def
  have hK'Ω : K' ∈ Ω := hΩ.conjInvariant _ K hK
  have hzK' : IsUniqueInvolution K' z₁ := by
    have h1 := hzK.conj (D.hom i h)
    have e : D.hom i h * zK * (D.hom i h)⁻¹ = z₁ := by
      rw [← hψrR, ← hψm₁, ← hh]
      simp [map_mul, map_inv]
    rwa [e] at h1
  have hnc' : ¬ ∃ g' : G, conjSub g' K' = J := fun hcon =>
    hnc (conjSub_rel_trans ⟨D.hom i h, rfl⟩ hcon)
  have huz : (u : G) * z₁ = z₁ * (u : G) := by
    have hju' : (u : G) * (j : G) = (j : G) * (u : G) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hju
      rw [← hk]
      exact congrArg Subtype.val ((Commute.refl u).zpow_right k).eq
    have huc : (u : G) * D.hom i c₁ = D.hom i c₁ * (u : G) := (hcomm _ hc₁K₀ u u.2).symm
    rw [hz₁def]
    calc (u : G) * ((j : G) * D.hom i c₁) = ((u : G) * (j : G)) * D.hom i c₁ := by group
      _ = ((j : G) * (u : G)) * D.hom i c₁ := by rw [hju']
      _ = (j : G) * ((u : G) * D.hom i c₁) := by group
      _ = (j : G) * (D.hom i c₁ * (u : G)) := by rw [huc]
      _ = ((j : G) * D.hom i c₁) * (u : G) := by group
  have hb' : ∀ P' : Sylow 2 ↥J, ∃ x ∈ (P' : Subgroup ↥J), (x : G) * z₁ ≠ z₁ * (x : G) := by
    intro P'
    obtain ⟨x, hxP', hx⟩ := hb P'
    refine ⟨x, hxP', fun hxz => hx ?_⟩
    have hxc : (x : G) * D.hom i c₁ = D.hom i c₁ * (x : G) := (hcomm _ hc₁K₀ x x.2).symm
    have h1 : (x : G) * (j : G) * D.hom i c₁ = (j : G) * (x : G) * D.hom i c₁ := by
      calc (x : G) * (j : G) * D.hom i c₁ = (x : G) * ((j : G) * D.hom i c₁) := by group
        _ = ((j : G) * D.hom i c₁) * (x : G) := hxz
        _ = (j : G) * (D.hom i c₁ * (x : G)) := by group
        _ = (j : G) * ((x : G) * D.hom i c₁) := by rw [hxc]
        _ = (j : G) * (x : G) * D.hom i c₁ := by group
    exact Subtype.ext (mul_right_cancel h1)
  exact not_aEmpty_of_centralizer_witness hp2 hq hΩ hK'Ω hJ hnc' hzK' P u huP hidx hnoncen huz hb'
    (hA K' hK'Ω)

end G2

end CFSG.ClassicalInvolution.Asc77
