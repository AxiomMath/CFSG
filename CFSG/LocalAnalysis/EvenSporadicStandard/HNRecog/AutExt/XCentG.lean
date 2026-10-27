module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XInnerG
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XSubtype
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XTransport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem aut_X_cent_of_facts (hF : XCentFacts) (h : F5Base a z) {b t : G} (hb : b ∈ orb2B a z a)
    (ht : t ∈ orb2A a a ∧ (t ∈ orb2A a b ∨ t ∈ orb2B a z b)) {η : G → G}
    (hη : IsIsoOn (Gxy a b) (Gxy a b) η) (hfix : ∀ x ∈ Gxyz a b t, η x = x) :
    (∀ x ∈ Gxy a b, η x = x) ∨ ∀ x ∈ Gxy a b, η x = t * x * t⁻¹ := by
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨ht1, ht2⟩ := ht
  have haa : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← h.typ.orderOf_a]; exact pow_orderOf_eq_one a
    simpa [pow_two] using h2
  have hab : a * b = b * a := h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hb1) (Or.inr hb2)
  have haz₀ : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
  have hxa : a * b ∈ Gx a := mem_Gx.2 (by rw [mul_assoc, ← hab])
  have hta : a * t = t * a := h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl ht1.1) (Or.inl ht1.2)
  have htb : b * t = t * b := by
    rcases ht2 with ht2 | ht2
    · exact h.mul_comm (Or.inl hb1) (Or.inl ht2.1) (Or.inl ht2.2)
    · exact h.mul_comm (Or.inl hb1) (Or.inl ht2.1) (Or.inr ht2.2)
  have htx : (a * b) * t = t * (a * b) :=
    calc (a * b) * t = a * (b * t) := mul_assoc a b t
      _ = a * (t * b) := by rw [htb]
      _ = (a * t) * b := (mul_assoc a t b).symm
      _ = (t * a) * b := by rw [hta]
      _ = t * (a * b) := mul_assoc t a b
  have hqa : a ∈ Qz (a * b) :=
    Section3.mem_Qz_of_isConj_mul h.iface h.typ h.loc.fusion1 (IsConj.refl a) hb2
      (by rw [mul_assoc, ← hab]) (by rw [haz₀]; exact hb1)
  have hX : XStruct a (a * b) a :=
    (h.loc.structX a (a * b) (IsConj.refl a) hb2).x_struct a hqa (IsConj.refl a)
  obtain ⟨E, z₀, b₀, u₀, hE, L, hD⟩ := exists_hSideData_base h
  let x : ↥(Gx a) := ⟨a * b, hxa⟩
  have hx : IsConj z₀ x := (L.isConj_z₀_iff (t := x) hb2).2 (by
    show IsConj a (a * (a * b))
    rw [haz₀]
    exact hb1)
  obtain ⟨T, hT⟩ : ∃ T : ↥(Gx x), ((T : ↥(Gx a)) : G) = t :=
    ⟨⟨⟨t, mem_Gx.2 hta⟩, mem_Gx.2 (Subtype.ext htx)⟩, rfl⟩
  have hT2 : T * T = 1 := by
    have h2 : t ^ 2 = 1 := by
      rw [← h.orderOf_eq_two (Or.inl ht1.1)]
      exact pow_orderOf_eq_one t
    refine Subtype.ext (Subtype.ext ?_)
    show ((T : ↥(Gx a)) : G) * ((T : ↥(Gx a)) : G) = 1
    rw [hT, ← pow_two]
    exact h2
  have hcard : Nat.card ↥(Subgroup.centralizer ({T} : Set ↥(Gx x))) = 768 ∨
      Nat.card ↥(Subgroup.centralizer ({T} : Set ↥(Gx x))) = 384 := by
    rw [natCard_centralizer_eq_Gxy_inf x (q := a * b) rfl T, hT]
    rcases ht2 with ht2 | ht2
    · left
      have hmem : t ∈ orb2A a a ∩ orb2A a (a * (a * b)) := ⟨ht1, by rw [haz₀]; exact ht2⟩
      exact (hX.o1.2 t hmem).trans (by norm_num)
    · right
      have hmem : t ∈ orb2A a a ∩ orb2B a (a * b) (a * (a * b)) :=
        ⟨ht1, by rw [haz₀]; exact ⟨ht2.1, hb2.symm.trans ht2.2⟩⟩
      exact (hX.o2.2 t hmem).trans (by norm_num)
  have key : XAutCent ↥(Gx x) T :=
    hF ↥(Gx a) E hE (GxSelf a) z₀ b₀ u₀ L.facts hD x hx T hT2 hcard
  obtain ⟨e, he⟩ := exists_mulEquiv_Gx_Gxy x (q := a * b) rfl
  rw [← Gxy_mul_left a b] at hη ⊢
  refine eq_or_conj_of_xAutCent e key (t := t) (by rw [he T, hT]) hη ?_
  intro y hy hyt
  refine hfix y ?_
  rw [Gxyz_eq_inf]
  exact Subgroup.mem_inf.2 ⟨(Gxy_mul_left a b) ▸ hy, mem_Gx.2 hyt.symm⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
