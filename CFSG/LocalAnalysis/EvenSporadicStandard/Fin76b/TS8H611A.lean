module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H610E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611Def
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611A
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H610N2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem Zg_cent_Q {α : G} (hα : AlphaSpec S z t α) {a : G}
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) :
    a ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ∧
      ∀ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G), a * q = q * a :=
  (h.center_QF hα).2 ((h.mem_Zg hα).1 ha)

theorem E_le_Qs {α : G} (hα : AlphaSpec S z t α) :
    E ≤ Fsub h hα ⊓ centralizer ({α} : Set G) := fun e he =>
  ⟨h.U_le_Fsub hα (mem_sup_right he),
    mem_centralizer_singleton_iff.2 (h.S_comm_E α hα.mem e he).symm⟩

theorem Zg_le_Qs {α : G} (hα : AlphaSpec S z t α) :
    (zpowers α ⊔ zpowers t : Subgroup G) ≤ Fsub h hα ⊓ centralizer ({α} : Set G) :=
  fun _ ha => (h.Zg_cent_Q hα ha).1

theorem cmt_mem {α : G} (hα : AlphaSpec S z t α) {q r : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    q * r * q⁻¹ * r⁻¹ ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  obtain ⟨c, hc, hqr⟩ := h.QF_comm hα hq hr
  have : q * r * q⁻¹ * r⁻¹ = c := by rw [hqr]; group
  rw [this]
  exact (h.mem_Zg hα).2 hc

theorem cmt_central {α : G} (hα : AlphaSpec S z t α) {q r s : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hs : s ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    s * (q * r * q⁻¹ * r⁻¹) = (q * r * q⁻¹ * r⁻¹) * s :=
  ((h.Zg_cent_Q hα (h.cmt_mem hα hq hr)).2 s hs).symm

theorem cmt_mul_left {α : G} (hα : AlphaSpec S z t α) {q q' r : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hq' : q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    (q * q') * r * (q * q')⁻¹ * r⁻¹ = (q * r * q⁻¹ * r⁻¹) * (q' * r * q'⁻¹ * r⁻¹) := by
  have hc := h.cmt_mem hα hq hr
  have hc' := h.cmt_mem hα hq' hr
  have hc'q := h.cmt_central hα hq' hr hq
  calc (q * q') * r * (q * q')⁻¹ * r⁻¹
      = q * (q' * r * q'⁻¹ * r⁻¹) * q⁻¹ * (q * r * q⁻¹ * r⁻¹) := by group
    _ = (q' * r * q'⁻¹ * r⁻¹) * (q * r * q⁻¹ * r⁻¹) := by rw [hc'q]; group
    _ = (q * r * q⁻¹ * r⁻¹) * (q' * r * q'⁻¹ * r⁻¹) := h.Zg_comm hα hc' hc

theorem cmt_mul_right {α : G} (hα : AlphaSpec S z t α) {q r r' : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr : r ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hr' : r' ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    q * (r * r') * q⁻¹ * (r * r')⁻¹ = (q * r * q⁻¹ * r⁻¹) * (q * r' * q⁻¹ * r'⁻¹) := by
  have hc' := h.cmt_central hα hq hr' hr
  calc q * (r * r') * q⁻¹ * (r * r')⁻¹
      = (q * r * q⁻¹ * r⁻¹) * (r * (q * r' * q⁻¹ * r'⁻¹) * r⁻¹) := by group
    _ = (q * r * q⁻¹ * r⁻¹) * (q * r' * q⁻¹ * r'⁻¹) := by rw [hc']; group

theorem W_cent_Z {α : G} (hα : AlphaSpec S z t α) {w a : G}
    (hw : w ∈ L ⊓ centralizer ({t} : Set G))
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) : w * a = a * w := by
  have hZS : a ∈ S := by
    rcases (h.mem_Zg hα).1 ha with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact h.t_mem_S
    · exact hα.mem
    · exact mul_mem hα.mem h.t_mem_S
  exact h.W_cent_S hw hZS

theorem W_norm_Qs {α : G} (hα : AlphaSpec S z t α) {w q : G}
    (hw : w ∈ L ⊓ centralizer ({t} : Set G))
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    w * q * w⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) :=
  h.QF_normal hα (h.W_mem_M hw) hq

theorem chi_conj_W {α : G} (hα : AlphaSpec S z t α) {w q e : G}
    (hw : w ∈ L ⊓ centralizer ({t} : Set G))
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) (he : e ∈ E) :
    (w * q * w⁻¹) * e * (w * q * w⁻¹)⁻¹ * e⁻¹ =
      q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹ := by
  have he' : w⁻¹ * e * w ∈ E := by
    have := h.W_norm_E (inv_mem hw) he
    simpa using this
  have hc := h.cmt_mem hα hq (h.E_le_Qs hα he')
  have hwc : w * (q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹) =
      (q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹) * w := h.W_cent_Z hα hw hc
  calc (w * q * w⁻¹) * e * (w * q * w⁻¹)⁻¹ * e⁻¹
      = w * (q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹) * w⁻¹ := by group
    _ = q * (w⁻¹ * e * w) * q⁻¹ * (w⁻¹ * e * w)⁻¹ := by rw [hwc]; group

theorem chi_conj_z {q e : G} (he : e ∈ E) :
    (z * q * z⁻¹) * e * (z * q * z⁻¹)⁻¹ * e⁻¹ = z * (q * e * q⁻¹ * e⁻¹) * z⁻¹ := by
  have hze : z * e = e * z := h.S_comm_E z h.zS e he
  have h1 : z⁻¹ * e * z = e := by
    calc z⁻¹ * e * z = z⁻¹ * (e * z) := by group
      _ = z⁻¹ * (z * e) := by rw [hze]
      _ = e := by group
  have h3 : z⁻¹ * e⁻¹ * z = e⁻¹ := by
    calc z⁻¹ * e⁻¹ * z = (z⁻¹ * e * z)⁻¹ := by group
      _ = e⁻¹ := by rw [h1]
  calc (z * q * z⁻¹) * e * (z * q * z⁻¹)⁻¹ * e⁻¹
      = z * q * (z⁻¹ * e * z) * q⁻¹ * z⁻¹ * e⁻¹ := by group
    _ = z * q * e * q⁻¹ * z⁻¹ * e⁻¹ := by rw [h1]
    _ = z * (q * e * q⁻¹ * (z⁻¹ * e⁻¹ * z)) * z⁻¹ := by group
    _ = z * (q * e * q⁻¹ * e⁻¹) * z⁻¹ := by rw [h3]

theorem z_norm_Qs {α : G} (hα : AlphaSpec S z t α) {q : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    z * q * z⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) :=
  h.QF_normal hα (le_normalizer (mem_sup_left h.zS)) hq

theorem z_conj_t : z * t * z⁻¹ = t := h.conj_t_of_M h.z_mem_M

theorem card_Zs {α : G} (hα : AlphaSpec S z t α) :
    Nat.card ↥(zpowers α ⊔ zpowers t : Subgroup G) = 4 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have hset : ((zpowers α ⊔ zpowers t : Subgroup G) : Set G) = {1, t, α, α * t} := by
    ext u
    simpa using h.mem_Zg hα
  have hαt1 : α * t ≠ 1 := by
    intro h1
    apply hα.ne_t
    have := eq_inv_of_mul_eq_one_left h1
    rw [this, hti]
  have hαtt : α * t ≠ t := fun h1 => hα.ne_one (mul_eq_right.1 h1)
  have hαta : α * t ≠ α := fun h1 => h.t_ne (mul_eq_left.1 h1)
  have hc : Nat.card ↥(zpowers α ⊔ zpowers t : Subgroup G) =
      Set.ncard ({1, t, α, α * t} : Set G) := by
    rw [← hset]
    exact Nat.card_coe_set_eq _
  have n1 : (1 : G) ∉ ({t, α, α * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h1 => h.t_ne h1.symm, fun h1 => hα.ne_one h1.symm, fun h1 => hαt1 h1.symm⟩
  have n2 : t ∉ ({α, α * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h1 => hα.ne_t h1.symm, fun h1 => hαtt h1.symm⟩
  have n3 : α ≠ α * t := fun h1 => hαta h1.symm
  rw [hc, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_pair n3]

@[expose] noncomputable def cmtHom {α : G} (hα : AlphaSpec S z t α) {e : G}
    (he : e ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    ↥(Fsub h hα ⊓ centralizer ({α} : Set G)) →* ↥(zpowers α ⊔ zpowers t : Subgroup G) where
  toFun q := ⟨(q : G) * e * (q : G)⁻¹ * e⁻¹, h.cmt_mem hα q.2 he⟩
  map_one' := Subtype.ext (by simp)
  map_mul' q q' := Subtype.ext (h.cmt_mul_left hα q.2 q'.2 he)

@[expose] noncomputable def Phi4 {α : G} (hα : AlphaSpec S z t α) {a b c d : G}
    (ha : a ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hb : b ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hc : c ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hd : d ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    ↥(Fsub h hα ⊓ centralizer ({α} : Set G)) →*
      ↥(zpowers α ⊔ zpowers t : Subgroup G) × ↥(zpowers α ⊔ zpowers t : Subgroup G) ×
        ↥(zpowers α ⊔ zpowers t : Subgroup G) × ↥(zpowers α ⊔ zpowers t : Subgroup G) :=
  (h.cmtHom hα ha).prod ((h.cmtHom hα hb).prod ((h.cmtHom hα hc).prod (h.cmtHom hα hd)))

theorem Phi4_surj (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) {a b c d : G}
    (hE : Subgroup.closure ({a, b, c, d} : Set G) = E) (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hd : d ∈ E) (c₁ c₂ c₃ c₄ : G) (h₁ : c₁ ∈ (zpowers α ⊔ zpowers t : Subgroup G))
    (h₂ : c₂ ∈ (zpowers α ⊔ zpowers t : Subgroup G))
    (h₃ : c₃ ∈ (zpowers α ⊔ zpowers t : Subgroup G))
    (h₄ : c₄ ∈ (zpowers α ⊔ zpowers t : Subgroup G)) :
    ∃ q ∈ Fsub h hα ⊓ centralizer ({α} : Set G), q * a * q⁻¹ * a⁻¹ = c₁ ∧
      q * b * q⁻¹ * b⁻¹ = c₂ ∧ q * c * q⁻¹ * c⁻¹ = c₃ ∧ q * d * q⁻¹ * d⁻¹ = c₄ := by
  set f := h.Phi4 hα (h.E_le_Qs hα ha) (h.E_le_Qs hα hb) (h.E_le_Qs hα hc)
    (h.E_le_Qs hα hd) with hf
  have hfq : ∀ q : ↥(Fsub h hα ⊓ centralizer ({α} : Set G)),
      f q = (⟨(q : G) * a * (q : G)⁻¹ * a⁻¹, h.cmt_mem hα q.2 (h.E_le_Qs hα ha)⟩,
        ⟨(q : G) * b * (q : G)⁻¹ * b⁻¹, h.cmt_mem hα q.2 (h.E_le_Qs hα hb)⟩,
        ⟨(q : G) * c * (q : G)⁻¹ * c⁻¹, h.cmt_mem hα q.2 (h.E_le_Qs hα hc)⟩,
        ⟨(q : G) * d * (q : G)⁻¹ * d⁻¹, h.cmt_mem hα q.2 (h.E_le_Qs hα hd)⟩) := fun q => rfl
  have hker : f.ker = (zpowers α ⊔ zpowers t : Subgroup G).subgroupOf
      (Fsub h hα ⊓ centralizer ({α} : Set G)) := by
    ext q
    rw [MonoidHom.mem_ker, mem_subgroupOf, hfq]
    constructor
    · intro h0
      have h1 := congrArg (fun p => ((p.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) h0
      have h2 := congrArg (fun p => ((p.2.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) h0
      have h3 := congrArg (fun p => ((p.2.2.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) h0
      have h4 := congrArg (fun p => ((p.2.2.2 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) h0
      simp only [Prod.fst_one, Prod.snd_one, Subgroup.coe_one] at h1 h2 h3 h4
      have hcl : Subgroup.closure ({a, b, c, d} : Set G) ≤ centralizer ({(q : G)} : Set G) := by
        rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        rcases hg with rfl | rfl | rfl | rfl
        · exact (cmt_eq_one_iff.1 h1).symm
        · exact (cmt_eq_one_iff.1 h2).symm
        · exact (cmt_eq_one_iff.1 h3).symm
        · exact (cmt_eq_one_iff.1 h4).symm
      have hcent : ∀ e ∈ E, (q : G) * e = e * (q : G) := by
        intro e he
        rw [← hE] at he
        have := hcl he
        rw [mem_centralizer_singleton_iff] at this
        exact this.symm
      exact (h.mem_Zg hα).2 (h.QF_cent_E hα q.2 hcent)
    · intro hqZ
      have hc' : ∀ e ∈ E, (q : G) * e * (q : G)⁻¹ * e⁻¹ = 1 := fun e he =>
        cmt_eq_one_iff.2 (h.Zg_comm_E hα hqZ he)
      refine Prod.ext (Subtype.ext (hc' a ha)) (Prod.ext (Subtype.ext (hc' b hb))
        (Prod.ext (Subtype.ext (hc' c hc)) (Subtype.ext (hc' d hd))))
  have hcardker : Nat.card f.ker = 4 := by
    rw [hker, ← h.card_Zs hα]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.Zg_le_Qs hα)).toEquiv
  have hidx := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hcardker, h.card_QF hM hα] at hidx
  have hrange : Nat.card f.range = 256 := by omega
  have htarget : Nat.card (↥(zpowers α ⊔ zpowers t : Subgroup G) ×
      ↥(zpowers α ⊔ zpowers t : Subgroup G) × ↥(zpowers α ⊔ zpowers t : Subgroup G) ×
        ↥(zpowers α ⊔ zpowers t : Subgroup G)) = 256 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, h.card_Zs hα]
  have htop : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, htarget])
  have hmem : ((⟨c₁, h₁⟩, ⟨c₂, h₂⟩, ⟨c₃, h₃⟩, ⟨c₄, h₄⟩) : ↥(zpowers α ⊔ zpowers t : Subgroup G) ×
      ↥(zpowers α ⊔ zpowers t : Subgroup G) × ↥(zpowers α ⊔ zpowers t : Subgroup G) ×
        ↥(zpowers α ⊔ zpowers t : Subgroup G)) ∈ f.range := by
    rw [htop]
    exact mem_top _
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 hmem
  rw [hfq] at hq
  have e1 := congrArg (fun p => ((p.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) hq
  have e2 := congrArg (fun p => ((p.2.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) hq
  have e3 := congrArg (fun p => ((p.2.2.1 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) hq
  have e4 := congrArg (fun p => ((p.2.2.2 : ↥(zpowers α ⊔ zpowers t : Subgroup G)) : G)) hq
  exact ⟨q, q.2, e1, e2, e3, e4⟩

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
