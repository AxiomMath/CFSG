module

public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Model
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Quot

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbG23

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Bridge


theorem generation_of_outer_cfg (hpin : G23Pinned phi) {H : Type} [Group H]
    {G L Y S : Subgroup H} {t : H} [Group.IsPerfect ↥L]
    (hodd : ∀ z ∈ Subgroup.center ↥L, Odd (orderOf z))
    (hLG : L ≤ G) (htG : t ∈ G) (htt : t * t = 1) (htL : t ∉ L)
    (hC : ∀ c ∈ G, (∀ x ∈ L, c * x = x * c) → c ∈ L)
    (hnorm : ∀ h, h ∈ L ↔ t * h * t⁻¹ ∈ L)
    (hYL : Y ≤ L) (hSY : S ≤ Y) [Group.IsPerfect ↥Y] (hY : Nat.card Y = 504)
    (hS : Nat.card S = 8) (htY : ∀ y ∈ Y, t * y = y * t)
    (hYZ : ∀ y : ↥L, (y : H) ∈ Y → y ∈ Subgroup.center ↥L → y = 1)
    (hm : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .G2 3 1) :
    ∃ g ∈ L, g ∈ Subgroup.normalizer (S : Set H) ∧
      Y ⊔ Y.map (MulAut.conj g).toMonoidHom = L := by
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZ
  set mk : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hmk
  set Y₀ : Subgroup ↥L := Y.subgroupOf L with hY₀
  set S₀ : Subgroup ↥L := S.subgroupOf L with hS₀
  have hSL : S ≤ L := hSY.trans hYL
  have hS₀Y₀ : S₀ ≤ Y₀ := fun x hx => hSY hx
  have hinj : ∀ a ∈ Y₀, ∀ b ∈ Y₀, mk a = mk b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ Z := QuotientGroup.eq.1 hab
    have h2 : ((a⁻¹ * b : ↥L) : H) ∈ Y := Y.mul_mem (Y.inv_mem ha) hb
    have h3 := hYZ _ h2 h1
    calc a = a * (a⁻¹ * b) := by rw [h3]; simp
      _ = b := by group
  have hbij : ∀ A : Subgroup ↥L, A ≤ Y₀ → Function.Bijective (mk.subgroupMap A) := by
    intro A hA
    refine ⟨fun a b hab => ?_, MonoidHom.subgroupMap_surjective mk A⟩
    have h1 : mk (a : ↥L) = mk (b : ↥L) := congrArg Subtype.val hab
    exact Subtype.ext (hinj a (hA a.2) b (hA b.2) h1)
  have hY₀card : Nat.card Y₀ = 504 := by
    rw [← hY]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv
  have hS₀card : Nat.card S₀ = 8 := by
    rw [← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  have hYbcard : Nat.card (Y₀.map mk) = 504 := by
    rw [← hY₀card]
    exact (Nat.card_congr (Equiv.ofBijective _ (hbij Y₀ le_rfl))).symm
  have hSbcard : Nat.card (S₀.map mk) = 8 := by
    rw [← hS₀card]
    exact (Nat.card_congr (Equiv.ofBijective _ (hbij S₀ hS₀Y₀))).symm
  have hperfY₀ : Group.IsPerfect ↥Y₀ :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYL).symm.surjective
  have hperfYb : Group.IsPerfect ↥(Y₀.map mk) :=
    Group.IsPerfect.ofSurjective (f := mk.subgroupMap Y₀) (MonoidHom.subgroupMap_surjective mk Y₀)
  have hα := quotAut_mul_self L t hnorm htt
  have hout := quotAut_not_inner L t hnorm hLG htG hC htL
  have hfix : Y₀.map mk ≤ fixedGroup (quotAut L t hnorm) := by
    rintro _ ⟨y, hy, rfl⟩
    show quotAut L t hnorm (mk y) = mk y
    rw [hmk]
    show quotAut L t hnorm (QuotientGroup.mk y) = QuotientGroup.mk y
    rw [quotAut_mk]
    congr 1
    apply Subtype.ext
    have h1 : t * (y : H) = (y : H) * t := htY (y : H) hy
    rw [conjOn_coe, h1]
    simp
  obtain ⟨gb, hgb, hgen⟩ := g23_generation_of_outer hpin hm hα hout hfix hYbcard
    (Subgroup.map_mono hS₀Y₀) hSbcard
  obtain ⟨gL, rfl⟩ := QuotientGroup.mk_surjective gb
  obtain ⟨hgS, hgenL⟩ := lift_generation hodd hS₀card hgb hgen
  refine ⟨(gL : H), gL.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_normalizer_iff] at hgS
    constructor
    · intro hh
      have := (hgS ⟨h, hSL hh⟩).1 hh
      exact this
    · intro hh
      have hhL : (gL : H) * h * (gL : H)⁻¹ ∈ L := hSL hh
      have hhL' : h ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem gL.2) hhL) gL.2
        simpa [mul_assoc] using this
      exact (hgS ⟨h, hhL'⟩).2 hh
  · apply le_antisymm
    · apply sup_le hYL
      rintro _ ⟨y, hy, rfl⟩
      exact L.mul_mem (L.mul_mem gL.2 (hYL hy)) (L.inv_mem gL.2)
    · intro x hx
      have hx' : (⟨x, hx⟩ : ↥L) ∈ Y₀ ⊔ Y₀.map (MulAut.conj gL).toMonoidHom := by
        rw [hgenL]
        exact Subgroup.mem_top _
      have hle : Y₀ ⊔ Y₀.map (MulAut.conj gL).toMonoidHom ≤
          (Y ⊔ Y.map (MulAut.conj (gL : H)).toMonoidHom).subgroupOf L := by
        apply sup_le
        · intro y hy
          exact Subgroup.mem_sup_left hy
        · rintro _ ⟨y, hy, rfl⟩
          exact Subgroup.mem_sup_right ⟨(y : H), hy, rfl⟩
      exact hle hx'

end Bridge

end CFSG.CGT.PushingUpLit.CGT6.EmbG23
