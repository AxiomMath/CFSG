module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpEndU
public import CFSG.ClassicalInvolution.Q3.Sec13PerpEndH
public import CFSG.ClassicalInvolution.Q3.Sec13End10
public import CFSG.ClassicalInvolution.Q3.Sec13PerpB
public import CFSG.ClassicalInvolution.Q3.Sec13PerpC

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace CaseBU

variable {K : Subgroup G} {P₁ P₂ : Set (Subgroup G)} {g u h e : G} {T : Subgroup G}

theorem false (c : CaseBU Ω K P₁ P₂ g u h e T)
    (I : AEIdent P₁ 5) (hI : I.φ.ker = ⊥) : False := by
  have hΩ := c.hyp.thmD.hyp
  have hKΩ : K ∈ Ω := by
    have hmem : conjSub g K ∈ dComp Ω K := by
      rw [c.dcomp]
      exact Or.inr c.gP
    have hne : conjSub g K ≠ K := by
      intro heq
      have hKP₂ : K ∈ P₂ := heq ▸ c.gP
      exact Set.disjoint_left.mp c.disj c.hK hKP₂
    have hmem' : Relation.ReflTransGen _ K (conjSub g K) := hmem
    have hJΩ : conjSub g K ∈ Ω := by
      rcases Relation.ReflTransGen.cases_tail hmem' with h1 | ⟨M, -, hM⟩
      · exact absurd h1 hne
      · exact hM.1
    have hK' := hΩ.conjInvariant g⁻¹ _ hJΩ
    rwa [conjSub_inv_conjSub] at hK'
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hKΩ
  have hzeq : z = u * (e⁻¹ * h⁻¹ * e * h) := c.z_eq z hz
  have hTΩ : T ∈ Ω := c.T_mem.1
  have hTu : ∀ y ∈ T, Commute y u := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (c.T_mem.2 hy)
  have hCeu : Commute e u := c.e_u
  have hconj : conjSub e T ∈ Generic.centMembers Ω u := by
    have hsub : conjSub e T ≤ Subgroup.centralizer ({u} : Set G) := fun x hx => by
      rw [mem_conjSub_iff] at hx
      have key : Commute (e * (e⁻¹ * x * e) * e⁻¹) u :=
        (hCeu.mul_left (hTu _ hx)).mul_left hCeu.inv_left
      have hxe : e * (e⁻¹ * x * e) * e⁻¹ = x := by group
      rw [hxe] at key
      exact Subgroup.mem_centralizer_singleton_iff.mpr key
    exact (⟨hΩ.conjInvariant e T hTΩ, hsub⟩ :
      conjSub e T ∈ Ω ∧ conjSub e T ≤ Subgroup.centralizer ({u} : Set G))
  have hhT : ∀ y ∈ T, Commute h y := fun y hy => commute_h c I hI T c.T_mem y hy
  have hhT' : ∀ y ∈ T, Commute h (e * y * e⁻¹) := fun y hy =>
    commute_h c I hI (conjSub e T) hconj _ (conj_mem_conjSub hy)
  have hkey : ∀ y ∈ T, Commute (e⁻¹ * h⁻¹ * e * h) y := by
    intro y hy
    have h1 : h * y = y * h := hhT y hy
    have h2 : h⁻¹ * (e * y * e⁻¹) = (e * y * e⁻¹) * h⁻¹ := (hhT' y hy).inv_left.eq
    show (e⁻¹ * h⁻¹ * e * h) * y = y * (e⁻¹ * h⁻¹ * e * h)
    calc (e⁻¹ * h⁻¹ * e * h) * y = e⁻¹ * h⁻¹ * e * (h * y) := by group
      _ = e⁻¹ * h⁻¹ * e * (y * h) := by rw [h1]
      _ = e⁻¹ * (h⁻¹ * (e * y * e⁻¹)) * e * h := by group
      _ = e⁻¹ * ((e * y * e⁻¹) * h⁻¹) * e * h := by rw [h2]
      _ = y * (e⁻¹ * h⁻¹ * e * h) := by group
  have hzT : ∀ y ∈ T, Commute z y := fun y hy => by
    rw [hzeq]
    exact (hTu y hy).symm.mul_left (hkey y hy)
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzT y hy).symm
  have hV : IsSylow2In T (T ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf le_rfl hTz, c.hyp.thmD.two T hTΩ,
      fun V' hV' _ hTV' => le_antisymm (hV'.trans inf_le_left) hTV'⟩
  have hTK : T ≠ K := by
    rintro rfl
    exact c.T_not (Or.inl c.hK)
  have hdc_of_nbr : ∀ M ∈ omegaNbr Ω K, M ∈ dComp Ω K := fun M hM => by
    show Relation.ReflTransGen _ K M
    exact Relation.ReflTransGen.single ⟨hM.1, Or.inl hM⟩
  have hnot_dc : T ∉ dComp Ω K := by
    rw [c.dcomp]
    exact c.T_not
  have htw : T ∉ twinSet Ω K := by
    rintro ⟨-, z', hz'K, hz'T⟩
    exact hnot_dc (hdc_of_nbr T (Q3CL.T3.twin_mem_omegaNbr hΩ hKΩ hTΩ hTK hz'K hz'T))
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hTΩ
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  have hT8 : Nat.card T = 8 := c.hyp.card_eq_eight hTΩ
  rcases Sec6Gen.l6_2Gen G Ω hΩ K hKΩ z hz T hTΩ htw t ht T hV ht.mem with
    ⟨hTt, -⟩ | ⟨hTt, -⟩ | ⟨hTU, -⟩ | ⟨hTR, hcomm⟩
  · rw [hTt, Nat.card_zpowers, ht2] at hT8
    omega
  · rw [hTt, Nat.card_zpowers, ht2] at hT8
    omega
  · obtain ⟨R, -, J', hJ', hRJ', -, -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hTU
    have hle : Nat.card R ≤ Nat.card J' := Subgroup.card_le_of_le hRJ'.1
    rw [c.hyp.card_eq_eight hJ'] at hle
    rw [hT8] at hcard
    omega
  ·
    have hO : oddCoreOf K = ⊥ := TL4.oddCoreOf_eq_bot_of_isPGroup (c.hyp.thmD.two K hKΩ)
    rw [hO] at hcomm
    have hcK : Commutes T K := fun x hx y hy => by
      have hc := hcomm (Subgroup.commutator_mem_commutator hx hy)
      rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    have hnbr : T ∈ omegaNbr Ω K :=
      ⟨hTΩ, hTK, T, hTR, le_rfl, Asc77.AscL62.le_normalizer_of_commutes hcK⟩
    exact hnot_dc (hdc_of_nbr T hnbr)

end CaseBU

namespace EndHyp

theorem false_of_caseB (h : EndHyp Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) (hne : KPerp Ω J ≠ KPerp Ω K) : False := by
  obtain ⟨hwyl, P₁, P₂, hKP₁, hdc, hdisj, hcomm, ⟨g, hgP, hswap⟩, hinv, htr, hodd, ⟨I⟩⟩ :=
    caseB_structure h hK hJ hne
  have hAEC : TL4.AECoverHyp I :=
    caseB_aeCoverHyp h hK hJ hne hKP₁ hdc hdisj hcomm ⟨g, hgP, hswap⟩ hinv htr hodd I
  have hI : I.φ.ker = ⊥ := TL4.aeCoverOddKer_proved G P₁ 5 I (by norm_num) ⟨2, rfl⟩ hAEC
  let cS : CaseBSit Ω K P₁ P₂ g :=
    ⟨h, hKP₁, hdc, hdisj, hcomm, hgP, hswap, hinv, htr, hodd, hwyl⟩
  obtain ⟨u, h', e, T, c⟩ := cS.exists_caseBU I hI
  exact CaseBU.false c I hI

theorem kPerp_eq_twinSet (h : EndHyp Ω) :
    ∀ K ∈ Ω, KPerp Ω K = twinSet Ω K := by
  by_cases hA : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, KPerp Ω J = KPerp Ω L
  · exact kPerp_eq_twinSet_of_caseA h hA
  · push Not at hA
    obtain ⟨L, hL, J, hJ, hne⟩ := hA
    exact (false_of_caseB h hL hJ hne).elim

theorem perp9 (h : EndHyp Ω) : Perp9 Ω := by
  intro K hK J hJ hc z j hz hj
  by_cases hKJ : J = K
  · subst hKJ
    exact hz.eq hj
  · have hnbr : J ∈ omegaNbr Ω K :=
      ⟨hJ, hKJ, J, TC.mem_RSet_of_isPGroup hJ (h.thmD.two J hJ),
        le_rfl, Asc77.AscL62.le_normalizer_of_commutes hc.symm⟩
    have hmem : J ∈ KPerp Ω K := Set.mem_insert_of_mem K hnbr
    rw [kPerp_eq_twinSet h K hK] at hmem
    obtain ⟨-, z', hz'K, hz'J⟩ := hmem
    exact (hz.eq hz'K).trans (hz'J.eq hj)

end EndHyp


end CFSG.ClassicalInvolution.Q3.Sec13
