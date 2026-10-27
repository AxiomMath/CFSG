module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Defs
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution
public import CFSG.Milestones.LR_Brauer_Suzuki_central_involution
public import CFSG.Holt.TwoGroups

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits

theorem exists_sylow {G : Type} [Group G] {M L : Subgroup G} (h : fusionIsSylowIn 2 M L) :
    ∃ P : Sylow 2 L, (P : Subgroup L) = M.subgroupOf L := by
  obtain ⟨hML, hM, hmax⟩ := h
  refine ⟨⟨M.subgroupOf L, hM.comap_subtype, fun {Q} hQ hMQ => ?_⟩, rfl⟩
  have h1 := hmax (Q.map L.subtype) (Subgroup.map_subtype_le Q) (hQ.map L.subtype)
    fun s hs => ⟨⟨s, hML hs⟩, hMQ (show (⟨s, hML hs⟩ : L) ∈ M.subgroupOf L from hs), rfl⟩
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective L.subtype_injective Q).symm

theorem uniqueInv_subgroupOf {G : Type} [Group G] {M L : Subgroup G}
    (h : Sec622UniqueInv M) : Sec622UniqueInv (M.subgroupOf L) := by
  intro a ha b hb hao hbo
  rw [← Subgroup.orderOf_coe] at hao hbo
  exact Subtype.ext (h a ha b hb hao hbo)

theorem centralInv_subgroupOf {G : Type} [Group G] {M L : Subgroup G} (hML : M ≤ L)
    (h : Sec622CentralInv M) : Sec622CentralInv (M.subgroupOf L) := by
  obtain ⟨hcent, z₀, hz₀, hsq, m₀, hm₀, hm₀z⟩ := h
  have hz₀L : z₀ ∈ L := hm₀z ▸ pow_mem (hML hm₀) 2
  refine ⟨fun e he hsq1 m hm => ?_, ⟨z₀, hz₀L⟩, ?_, fun m hm => ?_, ⟨m₀, hML hm₀⟩, hm₀, ?_⟩
  · exact Subtype.ext (hcent e he (congrArg Subtype.val hsq1) m hm)
  · rw [← Subgroup.orderOf_coe]; exact hz₀
  · rcases hsq m hm with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · exact Subtype.ext hm₀z

theorem orderOf_conj_inv {K : Type*} [Group K] (g z : K) :
    orderOf (g⁻¹ * z * g) = orderOf z := by
  have h : SemiconjBy g⁻¹ z (g⁻¹ * z * g) := by unfold SemiconjBy; group
  exact h.orderOf_eq.symm

variable {L : Type} [Group L] [Finite L]

theorem false_of_central_mod_oddCore [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a)
    {z : L} (hz : orderOf z = 2)
    (hmem : (QuotientGroup.mk z : L ⧸ CFSG.oddCore L) ∈ Subgroup.center (L ⧸ CFSG.oddCore L)) :
    False := by
  have hodd : CFSG.oddCore L = ⊥ := by
    refine eq_bot_iff.mpr (sSup_le fun N ⟨hN, hNodd⟩ => ?_)
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h.le
    · subst h
      rw [Subgroup.card_top] at hNodd
      obtain ⟨m, hm⟩ := hNodd
      obtain ⟨c, hc⟩ := (hz ▸ orderOf_dvd_natCard z : 2 ∣ Nat.card L)
      omega
  have hcomm : ∀ g : L, g * z = z * g := by
    intro g
    have h1 := Subgroup.mem_center_iff.mp hmem (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hodd,
      Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hcenter : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact (hab (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h) a b)).elim
  have hz1 : z = 1 := by
    have : z ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr hcomm
    rwa [hcenter, Subgroup.mem_bot] at this
  rw [hz1, orderOf_one] at hz
  omega

theorem exists_conj_mem_ne [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a)
    (S : Sylow 2 L) {z : L} (hzS : z ∈ (S : Subgroup L))
    (hzc : ∀ m ∈ (S : Subgroup L), m * z = z * m) (hz : orderOf z = 2) :
    ∃ g : L, g⁻¹ * z * g ∈ (S : Subgroup L) ∧ g⁻¹ * z * g ≠ z := by
  by_contra hcon
  push Not at hcon
  have hZ : (⟨z, hzS⟩ : (S : Subgroup L)) ∈ Subgroup.center (S : Subgroup L) :=
    Subgroup.mem_center_iff.mpr fun m => Subtype.ext (hzc m m.2)
  have key := CFSG.Milestones.glauberman_zStar_central_sylow_involution S ⟨z, hzS⟩ hZ
    (by rw [Subgroup.orderOf_mk]; exact hz) hcon
  exact false_of_central_mod_oddCore hnab hz key.2

theorem exists_normalizer_conj (S : Sylow 2 L) {x g : L}
    (hx : ∀ m ∈ (S : Subgroup L), m * x = x * m)
    (hy : ∀ m ∈ (S : Subgroup L), m * (g⁻¹ * x * g) = g⁻¹ * x * g * m) :
    ∃ n ∈ normalizer (S : Subgroup L), g⁻¹ * x * g = n⁻¹ * x * n :=
  S.conj_eq_normalizer_conj_of_mem_centralizer x g (Subgroup.mem_centralizer_iff.mpr hx)
    (Subgroup.mem_centralizer_iff.mpr hy)

theorem conj_mem_of_mem_normalizer {H : Subgroup L} {n x : L} (hn : n ∈ normalizer H)
    (hx : x ∈ H) : n⁻¹ * x * n ∈ H := by
  have := (mem_normalizer_iff.mp (inv_mem hn) x).mp hx
  simpa using this

theorem uniqueInv_false [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a) (P : Sylow 2 L)
    (hinv : ∃ e ∈ (P : Subgroup L), orderOf e = 2) (huniq : Sec622UniqueInv (P : Subgroup L)) :
    False := by
  obtain ⟨e, heP, he⟩ := hinv
  have hP : CFSG.ComponentClassification.AschbacherToolkit.AtMostOneInvolution
      (P : Subgroup L) := fun a b ha hb => by
    apply Subtype.ext
    apply huniq a a.2 b b.2
    · rw [Subgroup.orderOf_coe]; exact ha
    · rw [Subgroup.orderOf_coe]; exact hb
  rcases CFSG.Holt.isCyclic_or_quaternion_of_atMostOneInvolution P.isPGroup' hP with h | ⟨n, hn, hq⟩
  · have heven : Even (Nat.card L) := by
      have h1 : 2 ∣ Nat.card L := he ▸ orderOf_dvd_natCard e
      exact even_iff_two_dvd.mpr h1
    exact CFSG.TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_nonabelian_simple L hnab heven
      P h
  · exact false_of_central_mod_oddCore hnab he
      (CFSG.Milestones.brauer_suzuki n hn P hq e heP he)

theorem centralInv_false [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a) (P : Sylow 2 L)
    (hc : Sec622CentralInv (P : Subgroup L)) : False := by
  obtain ⟨hcent, z₀, hz₀, hsq, m₀, hm₀, hm₀z⟩ := hc
  have hz₀P : z₀ ∈ (P : Subgroup L) := hm₀z ▸ pow_mem hm₀ 2
  have hz₀sq : z₀ ^ 2 = 1 := hz₀ ▸ pow_orderOf_eq_one z₀
  have hz₀ne : z₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hz₀; omega
  have hz₀c : ∀ m ∈ (P : Subgroup L), m * z₀ = z₀ * m := fun m hm => hcent z₀ hz₀P hz₀sq m hm
  have hfix : ∀ n ∈ normalizer (P : Subgroup L), n⁻¹ * z₀ * n = z₀ := by
    intro n hn
    have hsq' : n⁻¹ * z₀ * n = (n⁻¹ * m₀ * n) ^ 2 := by
      have := conj_pow (a := n⁻¹) (b := m₀) (i := 2)
      rw [inv_inv] at this
      rw [this, hm₀z]
    have hmem := conj_mem_of_mem_normalizer hn hm₀
    have hne : n⁻¹ * z₀ * n ≠ 1 := fun h1 => by
      have := orderOf_conj_inv n z₀
      rw [h1, orderOf_one, hz₀] at this
      omega
    rcases hsq _ hmem with h | h
    · exact absurd (hsq'.trans h) hne
    · exact hsq'.trans h
  obtain ⟨g, hgP, hgne⟩ := exists_conj_mem_ne hnab P hz₀P hz₀c hz₀
  have hysq : (g⁻¹ * z₀ * g) ^ 2 = 1 := by
    have := conj_pow (a := g⁻¹) (b := z₀) (i := 2)
    rw [inv_inv] at this
    rw [this, hz₀sq]; group
  obtain ⟨n, hn, hyn⟩ := exists_normalizer_conj P hz₀c
    (fun m hm => hcent _ hgP hysq m hm)
  exact hgne (hyn.trans (hfix n hn))

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl
