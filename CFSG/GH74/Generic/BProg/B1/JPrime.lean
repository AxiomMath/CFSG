module

public import CFSG.GH74.Generic.BProg.Frozen
public import CFSG.GH74.Generic.ComponentShapes
import CFSG.GH74.Generic.BProg.B1.Sp4Rank
import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.Generic.JMaxCongr

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem eq_of_proj_eq_of_involutions {G : Type} [Group G] [Finite G] {x a b : G}
    (ha : a ∈ centralizer ({x} : Set G)) (hb : b ∈ centralizer ({x} : Set G))
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a)
    (h : proj x ⟨a, ha⟩ = proj x ⟨b, hb⟩) : a = b := by
  set a' : ↥(centralizer ({x} : Set G)) := ⟨a, ha⟩ with ha'
  set b' : ↥(centralizer ({x} : Set G)) := ⟨b, hb⟩ with hb'
  have hcomm' : a' * b' = b' * a' := Subtype.ext hab
  have hao' : a' * a' = 1 := Subtype.ext haa
  have hbo' : b' * b' = 1 := Subtype.ext hbb
  have hn1 : proj x (a'⁻¹ * b') = 1 := by
    rw [map_mul, map_inv, h]
    exact inv_mul_cancel _
  have hodd := proj_odd x _ hn1
  have hsq : (a'⁻¹ * b') * (a'⁻¹ * b') = 1 := by
    have ha'inv : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right hao'
    rw [ha'inv]
    calc a' * b' * (a' * b') = a' * (b' * a') * b' := by group
      _ = a' * (a' * b') * b' := by rw [hcomm']
      _ = (a' * a') * (b' * b') := by group
      _ = 1 := by rw [hao', hbo', one_mul]
  have hdvd : orderOf (a'⁻¹ * b') ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  have hord1 : orderOf (a'⁻¹ * b') = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  have h1 : a'⁻¹ * b' = 1 := orderOf_eq_one_iff.1 hord1
  have h2 : a' = b' := inv_mul_eq_one.1 h1
  exact congrArg Subtype.val h2

theorem not_shapeS2_of_rank_two {G : Type} [Group G] [Finite G] (hgen : Gen4 G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup G} (hKpc : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hr : 1 < pRank 2 ↥(CxK x K)) (hS2 : ShapeS2 x (imgBar x K)) : False := by
  obtain ⟨⟨F, _, _, hodd, ⟨Φ⟩⟩, hxK⟩ := hS2
  obtain ⟨a, b, haH, hbH, ha2, hb2, hab, hne⟩ :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.exists_two_involutions_of_two_le_pRank
      (Nat.succ_le_of_lt hr)
  obtain ⟨e, heH, he2, hex⟩ : ∃ e : G, e ∈ CxK x K ∧ orderOf e = 2 ∧ e ≠ x := by
    by_cases hax : a = x
    · exact ⟨b, hbH, hb2, fun h => hne (hax.trans h.symm)⟩
    · exact ⟨a, haH, ha2, hax⟩
  have heC : e ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.1 heH).1
  have hee : e * e = 1 := by
    have := pow_orderOf_eq_one e
    rwa [he2, pow_two] at this
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  set eb : CentralizerBar x := proj x ⟨e, heC⟩ with heb
  have hebeb : eb * eb = 1 := by
    rw [heb, ← map_mul]
    have : (⟨e, heC⟩ : ↥(centralizer ({x} : Set G))) * ⟨e, heC⟩ = 1 := Subtype.ext hee
    rw [this, map_one]
  have hcent : ∀ w ∈ imgBar x K, eb * w = w * eb := by
    intro w hw
    obtain ⟨g, hgK, rfl⟩ := mem_imgBar.1 hw
    have h1 := CFSG.GH74.GLS.C3.Layer1.PumpCalc.map_eq_of_mem_cSec hKpc heC
      (Subgroup.mem_inf.1 heH).2 g (Subgroup.mem_subgroupOf.2 hgK)
    have h2 : eb * proj x g * eb⁻¹ = proj x g := by
      simp only [map_mul, map_inv] at h1
      exact h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  by_cases hmem : eb ∈ imgBar x K
  · have hzc : (⟨eb, hmem⟩ : ↥(imgBar x K)) ∈ Subgroup.center ↥(imgBar x K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcent g g.2).symm
    have hxc : (⟨xbar x, hxK⟩ : ↥(imgBar x K)) ∈ Subgroup.center ↥(imgBar x K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (xbar_comm x g)
    have hmapc : ∀ u : ↥(imgBar x K), u ∈ Subgroup.center ↥(imgBar x K) →
        Φ u ∈ Subgroup.center ↥(StatedSp 2 F) := by
      intro u hu
      rw [Subgroup.mem_center_iff] at hu ⊢
      intro g
      obtain ⟨g', rfl⟩ := Φ.surjective g
      rw [← map_mul, ← map_mul, hu g']
    have hxsq : (⟨xbar x, hxK⟩ : ↥(imgBar x K)) * ⟨xbar x, hxK⟩ = 1 :=
      Subtype.ext (xbar_mul_self hx)
    have hesq : (⟨eb, hmem⟩ : ↥(imgBar x K)) * ⟨eb, hmem⟩ = 1 := Subtype.ext hebeb
    have hx1 : (⟨xbar x, hxK⟩ : ↥(imgBar x K)) ≠ 1 := fun h =>
      xbar_ne_one hx (congrArg Subtype.val h)
    by_cases he1 : (⟨eb, hmem⟩ : ↥(imgBar x K)) = 1
    · have h1 : eb = 1 := congrArg Subtype.val he1
      have h2 : proj x ⟨e, heC⟩ = proj x ⟨1, one_mem _⟩ := by
        rw [← heb, h1]
        exact (map_one (proj x)).symm
      have h3 := eq_of_proj_eq_of_involutions heC (one_mem _) hee (one_mul 1)
        (by rw [mul_one, one_mul]) h2
      rw [h3, orderOf_one] at he2
      omega
    · have hΦ := statedSp2_central_involutions_eq (hmapc _ hzc) (hmapc _ hxc)
        (by rw [← map_mul, hesq, map_one]) (by rw [← map_mul, hxsq, map_one])
        (fun h => he1 (Φ.injective (by rw [h, map_one])))
        (fun h => hx1 (Φ.injective (by rw [h, map_one])))
      have h2 : (⟨eb, hmem⟩ : ↥(imgBar x K)) = ⟨xbar x, hxK⟩ := Φ.injective hΦ
      have h3 : eb = xbar x := congrArg Subtype.val h2
      have h4 : proj x ⟨e, heC⟩ = proj x ⟨x, hxC⟩ := h3
      exact hex (eq_of_proj_eq_of_involutions heC hxC hee hxx
        (Subgroup.mem_centralizer_singleton_iff.1 heC) h4)
  · exact false_of_commuting_involution_sp4 (gen4_centralizerBar hgen x) hodd Φ hebeb hcent hmem

theorem jPrimeNS_of_known_facts
    (hF : GenericKnownFacts) : JPrimeNS := by
  intro G _ _ hyp _ x K hJ hr
  have hILo : IsILo 2 x K := hJ.1.1
  have hx : orderOf x = 2 := hILo.1
  have hKpc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hG2K : InG2 (↥K ⧸ pPrimeCore 2 ↥K) := hJ.1.2
  obtain ⟨eMK⟩ := CFSG.GH74.GLS.C3.Layer1.PumpCalc.kBar_equiv_bar hKpc
  have eMK' : (↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(imgBar x K) := eMK
  have hG2 : InG2 ↥(imgBar x K) := inG2_of_mulEquiv eMK' hG2K
  rcases generic_shapes_of_inG2 hF hyp.simple hyp.nonab hyp.gen4 hyp.kgh hx hG2 with
    h1 | h2 | h3 | h4 | h5
  · exact QShapeNS.of_mulEquiv eMK'.symm (Or.inl h1.1)
  · exact (not_shapeS2_of_rank_two hyp.gen4 hx hKpc hr h2).elim
  · obtain ⟨⟨p, f, hp, hp2, h5le, hL⟩, -⟩ := h3
    exact QShapeNS.of_mulEquiv eMK'.symm (Or.inr (Or.inl ⟨p, f, hp, hp2, by omega, hL⟩))
  · exact QShapeNS.of_mulEquiv eMK'.symm (Or.inr (Or.inr (Or.inl h4.1)))
  · exact QShapeNS.of_mulEquiv eMK'.symm (Or.inr (Or.inr (Or.inr h5.1)))

end CFSG.GH74.Generic.BProg.B1
