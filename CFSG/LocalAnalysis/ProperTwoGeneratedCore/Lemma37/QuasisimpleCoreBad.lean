module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverSetup
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreFour

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.BenderSuzuki.PFchapter1section1

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z : J}

theorem Setting.two_dvd_card_map (h : Setting J Q B) {P : Subgroup J} (hP : IsPGroup 2 P)
    (hPc : ¬ IsCyclic P) : 2 ∣ Nat.card (P.map (QuotientGroup.mk' (Subgroup.center J))) := by
  have hZc : IsCyclic (Subgroup.center J) := isCyclic_of_prime_card h.center_card
  obtain ⟨p, hpP, hpZ⟩ : ∃ p ∈ P, p ∉ Subgroup.center J := by
    by_contra hall
    push Not at hall
    exact hPc (Subgroup.isCyclic_of_le hall)
  obtain ⟨n, hn⟩ := (hP.map (QuotientGroup.mk' (Subgroup.center J))).exists_card_eq
  rw [hn]
  rcases n with _ | n
  · exfalso
    rw [pow_zero, Subgroup.card_eq_one] at hn
    have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center J)) hpP
    rw [hn, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hpZ hmem
  · exact dvd_pow_self 2 n.succ_ne_zero

namespace FourGen

theorem mem_of_setting (hz : FourGen Q z) (h : Setting J Q B) : z ∈ B :=
  h.sylow_le hz.mem

omit [Finite J] in
theorem mk_ne_one (hz : FourGen Q z) : (z : J ⧸ Subgroup.center J) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff]
  exact hz.not_mem_center

omit [Finite J] in
theorem orderOf_mk (hz : FourGen Q z) : orderOf (z : J ⧸ Subgroup.center J) = 2 :=
  orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, ← hz.order, pow_orderOf_eq_one,
    QuotientGroup.mk_one]) hz.mk_ne_one

theorem mk_mem_map (hz : FourGen Q z) (h : Setting J Q B) :
    (z : J ⧸ Subgroup.center J) ∈ B.map (QuotientGroup.mk' (Subgroup.center J)) :=
  (h.mk_mem_map_iff z).mpr (hz.mem_of_setting h)

theorem unique_containment (hz : FourGen Q z) (h : Setting J Q B) (g : J ⧸ Subgroup.center J) :
    (z : J ⧸ Subgroup.center J) ∈
        rightConjugate (B.map (QuotientGroup.mk' (Subgroup.center J))) g ↔
      g ∈ B.map (QuotientGroup.mk' (Subgroup.center J)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rw [h.mk_mem_map_iff]
  constructor
  · intro hmem
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hmem
    have hw' : w = ((x * z * x⁻¹ : J) : J ⧸ Subgroup.center J) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hwz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hw', h.mk_mem_map_iff] at hw
    exact h.mem_of_conj_mem (hz.mem_of_setting h) hz.order hz.not_mem_center hw
  · intro hx
    refine Subgroup.mem_map.mpr ⟨((x * z * x⁻¹ : J) : J ⧸ Subgroup.center J), ?_, ?_⟩
    · rw [h.mk_mem_map_iff]
      exact B.mul_mem (B.mul_mem hx (hz.mem_of_setting h)) (B.inv_mem hx)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv]
      group

theorem centralizer_le (hz : FourGen Q z) (h : Setting J Q B) :
    Subgroup.centralizer ({(z : J ⧸ Subgroup.center J)} : Set (J ⧸ Subgroup.center J)) ≤
      B.map (QuotientGroup.mk' (Subgroup.center J)) :=
  h.centralizer_mk_le (hz.mem_of_setting h) hz.order hz.not_mem_center

theorem centralSylow (hz : FourGen Q z) :
    InvolutionPointCentralSylow (z : J ⧸ Subgroup.center J) := by
  refine ⟨Lemma37.centralSylow Q, mk_mem_centralSylow Q ⟨z, hz.mem⟩, ?_⟩
  rw [Subgroup.mem_center_iff]
  rintro ⟨s, hs⟩
  apply Subtype.ext
  rw [Sylow.coe_mapSurjective] at hs
  obtain ⟨q, hq, rfl⟩ := hs
  exact ((commute_mk_iff q z).mpr (hz.comm_mem_center q hq)).eq

theorem exists_bad
    (hz : FourGen Q z) (h : Setting J Q B) :
    ∃ u : J ⧸ Subgroup.center J, orderOf u = 2 ∧ Commute u (z : J ⧸ Subgroup.center J) ∧
      ¬ Subgroup.centralizer ({u} : Set (J ⧸ Subgroup.center J)) ≤
        B.map (QuotientGroup.mk' (Subgroup.center J)) ∧
      ¬ fusionStronglyEmbedded ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
        (localInvolutionPointHull (z : J ⧸ Subgroup.center J) u)) := by
  by_contra hno
  have hloc : InvolutionPointLocalEmbedding (B.map (QuotientGroup.mk' (Subgroup.center J)))
      (z : J ⧸ Subgroup.center J) :=
    { proper := h.map_ne_top
      distinguished_mem := hz.mk_mem_map h
      distinguished_order := hz.orderOf_mk
      unique_containment := hz.unique_containment h
      local_embedding := fun u hu huz hesc => by
        by_contra hf
        exact hno ⟨u, hu, huz, hesc, hf⟩ }
  have hsimple := h.simple
  have hstrong := theoremTwo _ _ _ hloc hz.centralSylow
  rw [involutionPointHull_eq_top hz.mk_ne_one] at hstrong
  have hH := fusionStronglyEmbedded_of_subgroupOf_top hstrong
  obtain ⟨j, hjB, P, hP, hPc, hPB⟩ := h.quaternion
  have hj : ((j : J ⧸ Subgroup.center J))⁻¹ ∉ B.map (QuotientGroup.mk' (Subgroup.center J)) := by
    rw [← QuotientGroup.mk_inv, h.mk_mem_map_iff]
    exact fun h' => hjB (by simpa using B.inv_mem h')
  refine Nat.not_even_iff_odd.mpr (hH.2.2 _ hj) (even_iff_two_dvd.mpr ?_)
  refine (h.two_dvd_card_map hP hPc).trans (Subgroup.card_dvd_of_le ?_)
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨(h.mk_mem_map_iff p).mpr (hPB p hp).1, Subgroup.mem_map.mpr
    ⟨((j⁻¹ * p * j : J) : J ⧸ Subgroup.center J), (h.mk_mem_map_iff _).mpr (hPB p hp).2, ?_⟩⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk'_apply]
  group

theorem sq_eq_centralElt_of_bad (hz : FourGen Q z) (h : Setting J Q B) {u : J}
    (hu : orderOf (u : J ⧸ Subgroup.center J) = 2)
    (huz : Commute (u : J ⧸ Subgroup.center J) (z : J ⧸ Subgroup.center J))
    (hesc : ¬ Subgroup.centralizer ({(u : J ⧸ Subgroup.center J)} : Set (J ⧸ Subgroup.center J))
      ≤ B.map (QuotientGroup.mk' (Subgroup.center J))) :
    u ∈ B ∧ u * u = centralElt J := by
  have huB : u ∈ B := by
    rw [← h.mk_mem_map_iff]
    exact hz.centralizer_le h (Subgroup.mem_centralizer_singleton_iff.mpr huz.eq)
  refine ⟨huB, ?_⟩
  have huu : u * u ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hu, pow_orderOf_eq_one]
  have hu1 : (u : J ⧸ Subgroup.center J) ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu
    exact absurd hu (by decide)
  have huZ : u ∉ Subgroup.center J := fun h' => hu1 ((QuotientGroup.eq_one_iff u).mpr h')
  refine (h.mem_center_iff.mp huu).resolve_left fun h1 => hesc ?_
  have huord : orderOf u = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h1) fun h' => huZ (h' ▸ (Subgroup.center J).one_mem)
  exact h.centralizer_mk_le huB huord huZ

end FourGen

theorem Setting.exists_bad
    (h : Setting J Q B) :
    ∃ z : J, FourGen Q z ∧
      ∃ u : J ⧸ Subgroup.center J, orderOf u = 2 ∧ Commute u (z : J ⧸ Subgroup.center J) ∧
        ¬ Subgroup.centralizer ({u} : Set (J ⧸ Subgroup.center J)) ≤
          B.map (QuotientGroup.mk' (Subgroup.center J)) ∧
        ¬ fusionStronglyEmbedded ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
          (localInvolutionPointHull (z : J ⧸ Subgroup.center J) u)) := by
  obtain ⟨z, hz⟩ := h.exists_fourGen
  exact ⟨z, hz, hz.exists_bad h⟩

theorem Setting.exists_bad_lift
    (h : Setting J Q B) :
    ∃ z : J, FourGen Q z ∧ ∃ u : J, u ∈ B ∧ u * u = centralElt J ∧
      Commute (u : J ⧸ Subgroup.center J) (z : J ⧸ Subgroup.center J) ∧
      ¬ Subgroup.centralizer ({(u : J ⧸ Subgroup.center J)} : Set (J ⧸ Subgroup.center J)) ≤
        B.map (QuotientGroup.mk' (Subgroup.center J)) ∧
      ¬ fusionStronglyEmbedded ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
        (localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J))) := by
  obtain ⟨z, hz, v, hv, hvz, hesc, hnot⟩ := h.exists_bad
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨huB, hu⟩ := hz.sq_eq_centralElt_of_bad h hv hvz hesc
  exact ⟨z, hz, u, huB, hu, hvz, hesc, hnot⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
