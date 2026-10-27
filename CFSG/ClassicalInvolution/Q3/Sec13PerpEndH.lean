module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpEndAE
import CFSG.ClassicalInvolution.Q3.Sec13StarAE5
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent6
public import CFSG.ClassicalInvolution.Q3.Sec13PerpEndModel
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Model

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

private def endH_lo (m : ℕ) (hm : 4 ≤ m) : Fin 4 ↪ Fin m where
  toFun i := ⟨i.1, lt_of_lt_of_le i.2 hm⟩
  inj' i j hij := Fin.ext (Fin.mk.inj_iff.mp hij)

private def endH_hi (m : ℕ) (hm : 4 ≤ m) : Fin 4 ↪ Fin m where
  toFun i := ⟨m - 4 + i.1, by have := i.2; omega⟩
  inj' i j hij := Fin.ext (by have h := Fin.mk.inj_iff.mp hij; have := i.2; have := j.2; omega)

private theorem endH_cover {m : ℕ} (hm4 : 4 ≤ m) (hm7 : m ≤ 7) (p : Fin m) :
    p ∈ Set.range (endH_lo m hm4) ∨ p ∈ Set.range (endH_hi m hm4) := by
  have hp := p.2
  rcases Nat.lt_or_ge p.1 4 with h | h
  · left
    exact ⟨⟨p.1, h⟩, Fin.ext rfl⟩
  · right
    exact ⟨⟨p.1 - (m - 4), by omega⟩, Fin.ext (by show m - 4 + (p.1 - (m - 4)) = p.1; omega)⟩

private theorem endH_exists_not_mem {m : ℕ} (hm : 5 ≤ m) (ι : Fin 4 ↪ Fin m) :
    ∃ p, p ∉ Set.range ι := by
  by_contra hcon
  push_neg at hcon
  have hs : Function.Surjective (⇑ι) := fun p => hcon p
  have := Fintype.card_le_of_surjective (⇑ι) hs
  simp only [Fintype.card_fin] at this
  omega

private theorem endH_zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem endH_eq_one_of_comm {m : ℕ} (h5 : 5 ≤ m) (h7 : m ≤ 7) {x : AEQ m}
    (hx : ∀ a ∈ (aeSub m).map (mkQ m), x * a = a * x) : x = 1 := by
  have hm4 : 4 ≤ m := by omega
  have hK : ∀ ι : Fin 4 ↪ Fin m, ∀ a ∈ kList,
      x * mkQ m (embed ι a) = mkQ m (embed ι a) * x := by
    intro ι a ha
    apply hx
    refine Subgroup.mem_map_of_mem _ (memK_le_aeSub ι ?_)
    exact Subgroup.mem_map_of_mem _ (mem_kQ.mpr ha)
  have hS : ∀ ι : Fin 4 ↪ Fin m, ∀ a ∈ kStarList,
      x * mkQ m (embed ι a) = mkQ m (embed ι a) * x := by
    intro ι a ha
    apply hx
    refine Subgroup.mem_map_of_mem _ (memKStar_le_aeSub ι ?_)
    exact Subgroup.mem_map_of_mem _ (mem_kQStar.mpr ha)
  have hcore : ∀ ι : Fin 4 ↪ Fin m, ∃ w : Wr m, x = mkQ m w ∧ (∀ j, w.perm (ι j) = ι j) ∧
      ((fun i => w.vec (ι i)) = 0 ∨ (fun i => w.vec (ι i)) = fun _ => 1) := by
    intro ι
    obtain ⟨p, hp⟩ := endH_exists_not_mem h5 ι
    obtain ⟨w, hw, h1, h2, -⟩ :=
      CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5.cent_core ι hp (hK ι) (hS ι)
    exact ⟨w, hw, h1, h2⟩
  obtain ⟨w₁, hw₁, hf₁, hv₁⟩ := hcore (endH_lo m hm4)
  obtain ⟨w₂, hw₂, hf₂, hv₂⟩ := hcore (endH_hi m hm4)
  have hrel : ((∀ p, w₂.vec p = w₁.vec p) ∧ w₂.perm = w₁.perm) ∨
      ((∀ p, w₂.vec p = w₁.vec p + 1) ∧ w₂.perm = w₁.perm) := by
    have hq : mkQ m w₁ = mkQ m w₂ := hw₁.symm.trans hw₂
    rcases mkQ_eq_iff.mp hq with h | h
    · left
      have hw : w₂ = w₁ := (inv_mul_eq_one.mp h).symm
      rw [hw]
      exact ⟨fun p => rfl, rfl⟩
    · right
      have h2 : w₂ = w₁ * allOnes m := by
        rw [← h, mul_inv_cancel_left]
      rw [h2]
      exact ⟨fun p => by rw [mul_vec]; rfl, by rw [mul_perm, show (allOnes m).perm = 1 from rfl,
        mul_one]⟩
  have hpp : w₂.perm = w₁.perm := by
    rcases hrel with h | h
    · exact h.2
    · exact h.2
  have hperm : w₁.perm = 1 := by
    refine Equiv.ext fun p => ?_
    rcases endH_cover hm4 h7 p with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact hf₁ j
    · rw [← hpp]
      exact hf₂ j
  have hT : ∀ p q, w₂.vec p = w₂.vec q → w₁.vec p = w₁.vec q := by
    intro p q hpq
    rcases hrel with h | h
    · rw [h.1 p, h.1 q] at hpq
      exact hpq
    · rw [h.1 p, h.1 q] at hpq
      exact add_right_cancel hpq
  have hlo : ∀ i j : Fin 4, w₁.vec (endH_lo m hm4 i) = w₁.vec (endH_lo m hm4 j) := by
    intro i j
    rcases hv₁ with h | h
    · have hi : w₁.vec (endH_lo m hm4 i) = 0 := congrFun h i
      have hj : w₁.vec (endH_lo m hm4 j) = 0 := congrFun h j
      rw [hi, hj]
    · have hi : w₁.vec (endH_lo m hm4 i) = 1 := congrFun h i
      have hj : w₁.vec (endH_lo m hm4 j) = 1 := congrFun h j
      rw [hi, hj]
  have hhi : ∀ i j : Fin 4, w₂.vec (endH_hi m hm4 i) = w₂.vec (endH_hi m hm4 j) := by
    intro i j
    rcases hv₂ with h | h
    · have hi : w₂.vec (endH_hi m hm4 i) = 0 := congrFun h i
      have hj : w₂.vec (endH_hi m hm4 j) = 0 := congrFun h j
      rw [hi, hj]
    · have hi : w₂.vec (endH_hi m hm4 i) = 1 := congrFun h i
      have hj : w₂.vec (endH_hi m hm4 j) = 1 := congrFun h j
      rw [hi, hj]
  have hall : ∀ p, w₁.vec p = w₁.vec (endH_lo m hm4 0) := by
    intro p
    rcases endH_cover hm4 h7 p with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact hlo j 0
    · have h1 := hT _ (endH_hi m hm4 0) (hhi j 0)
      rw [h1]
      have h2 : endH_hi m hm4 0 = endH_lo m hm4 ⟨m - 4, by omega⟩ := Fin.ext (by
        show m - 4 + 0 = m - 4
        rfl)
      rw [h2]
      exact hlo _ 0
  have hone : w₁ = 1 ∨ w₁ = allOnes m := by
    rcases endH_zmod2_cases (w₁.vec (endH_lo m hm4 0)) with ha | ha
    · left
      exact Wr.ext (funext fun p => by rw [hall p, ha]; rfl) hperm
    · right
      exact Wr.ext (funext fun p => by rw [hall p, ha]; rfl) hperm
  rw [hw₁]
  rcases hone with h | h
  · rw [h, map_one]
  · rw [h]
    exact (QuotientGroup.eq_one_iff (allOnes m)).mpr (mem_piSub.mpr (Or.inr rfl))

private theorem endH_comm_comm {H : Type*} [Group H] {a b : H} (h : a * b = b * a) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [show a * b * a⁻¹ * b⁻¹ = a * b * (b * a)⁻¹ by group, h, mul_inv_cancel]

private theorem endH_mul_self_of_permBar {m : ℕ} {y : AEQ m} (h : TL4.permBar m y = 1) :
    y * y = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (piSub m) y
  rw [TL4.permBar_mkQ] at h
  have ha : a = Wr.ofVec a.vec := Wr.ext rfl h
  rw [← map_mul, ha, TL4.ofVec_mul_ofVec]
  have h2 : a.vec + a.vec = 0 := funext fun i => Wr.zmod_two_add_self _
  rw [h2, show Wr.ofVec (0 : Fin m → ZMod 2) = 1 from rfl, map_one]

private theorem endH_five_perms : ∃ c₁ c₂ : Equiv.Perm (Fin 5),
    AE.Wr.wsum (AE.Wr.ofPerm c₁) = 0 ∧ Equiv.Perm.sign c₁ = 1 ∧
    AE.Wr.wsum (AE.Wr.ofPerm c₂) = 0 ∧ Equiv.Perm.sign c₂ = 1 ∧
    (AE.Wr.ofPerm c₁) ^ 5 = 1 ∧ (AE.Wr.ofPerm c₂) ^ 5 = 1 ∧
    (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) ≠ 1 :=
  ⟨⟨![1, 2, 3, 4, 0], ![4, 0, 1, 2, 3], by decide, by decide⟩,
    ⟨![2, 4, 1, 0, 3], ![3, 2, 0, 4, 1], by decide, by decide⟩,
    by decide, by decide, by decide, by decide, by decide⟩

end Model

section Ident

variable {P Q : Set (Subgroup G)}

private theorem endH_conj_mem_pSpan {k : G} (hk : ∀ L ∈ P, conjSub k L ∈ Q) {y : G}
    (hy : y ∈ pSpan P) : k * y * k⁻¹ ∈ pSpan Q :=
  (pSpan_le (H := (pSpan Q).comap (MulAut.conj k).toMonoidHom) fun L hL _ hl =>
    le_pSpan (hk L hL) (conj_mem_conjSub hl)) hy

private def endH_conjHom {k : G} (hk : ∀ L ∈ P, conjSub k L ∈ Q) :
    ↥(pSpan P) →* ↥(pSpan Q) where
  toFun y := ⟨k * y * k⁻¹, endH_conj_mem_pSpan hk y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

private theorem endH_conjAut {k : G} (hk : ∀ L ∈ P, conjSub k L ∈ P)
    (hk' : ∀ L ∈ P, conjSub k⁻¹ L ∈ P) :
    ∃ ca : ↥(pSpan P) ≃* ↥(pSpan P), (∀ y, (ca y : G) = k * y * k⁻¹) ∧
      ∀ y, (ca.symm y : G) = k⁻¹ * y * k := by
  refine ⟨{ toFun := fun y => ⟨k * y * k⁻¹, endH_conj_mem_pSpan hk y.2⟩
            invFun := fun y => ⟨k⁻¹ * y * k, by
              have := endH_conj_mem_pSpan hk' y.2
              rwa [inv_inv] at this⟩
            left_inv := fun y => Subtype.ext (by simp [mul_assoc])
            right_inv := fun y => Subtype.ext (by simp [mul_assoc])
            map_mul' := fun y y' => Subtype.ext (by simp [mul_assoc]) }, fun _ => rfl, fun _ => rfl⟩

private theorem endH_exists_conj {m : ℕ} (h5 : 5 ≤ m)
    (h7 : m ≤ 7) (I : AEIdent P m) (c : ↥(pSpan P) ≃* ↥(pSpan P))
    (hc : ∀ L ∈ P, ∃ L' ∈ P,
      (L.subgroupOf (pSpan P)).map c.toMonoidHom = L'.subgroupOf (pSpan P)) :
    ∃ x : AE.AEQ m, ∀ y : ↥(pSpan P), I.φ (c y) = x * I.φ y * x⁻¹ := by
  have hZ : Subgroup.center ↥(pSpan P) ≤ I.φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    refine endH_eq_one_of_comm h5 h7 fun a ha => ?_
    rw [← I.range_eq] at ha
    obtain ⟨y, rfl⟩ := ha
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y).symm]
  obtain ⟨f, hf⟩ : ∃ f : ↥(pSpan P) →* ↥((AE.aeSub m).map (AE.mkQ m)),
      ∀ y, (f y : AE.AEQ m) = I.φ y :=
    ⟨I.φ.codRestrict _ fun y => by rw [← I.range_eq]; exact ⟨y, rfl⟩, fun _ => rfl⟩
  have hfs : Function.Surjective f := by
    rintro ⟨a, ha⟩
    rw [← I.range_eq] at ha
    obtain ⟨y, rfl⟩ := ha
    exact ⟨y, Subtype.ext (hf y)⟩
  have hfk : f.ker = Subgroup.center ↥(pSpan P) := by
    refine le_antisymm (fun y hy => I.ker_le ?_) fun y hy => ?_
    · rw [MonoidHom.mem_ker, ← hf, MonoidHom.mem_ker.mp hy]
      rfl
    · exact MonoidHom.mem_ker.mpr (Subtype.ext ((hf y).trans (MonoidHom.mem_ker.mp (hZ hy))))
  have hck : f.ker.map c.toMonoidHom = f.ker := by
    rw [hfk]
    exact Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (Subgroup.center ↥(pSpan P)).Characteristic) c
  obtain ⟨β, hβ⟩ : ∃ β : MulAut ↥((AE.aeSub m).map (AE.mkQ m)), ∀ y, β (f y) = f (c y) := by
    refine ⟨((QuotientGroup.quotientKerEquivOfSurjective f hfs).symm.trans
      (QuotientGroup.congr f.ker f.ker c hck)).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun y => ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f y) =
        (y : ↥(pSpan P) ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
    rfl
  have hsub : ∀ H : Subgroup ↥(pSpan P),
      (H.map I.φ).subgroupOf ((AE.aeSub m).map (AE.mkQ m)) = H.map f := by
    intro H
    ext a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hym⟩
      exact ⟨y, hy, Subtype.ext ((hf y).trans hym)⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (hf y).symm⟩
  have hcomp : β.toMonoidHom.comp f = f.comp c.toMonoidHom := MonoidHom.ext hβ
  obtain ⟨x, hx⟩ := TL4.model117_proved m h5 h7 β fun α hα b => by
    obtain ⟨L, hL, hLe⟩ := I.label_surj α hα b
    obtain ⟨L', hL', hcL⟩ := hc L hL
    obtain ⟨α', hα', b', hL'e⟩ := I.label L' hL'
    refine ⟨α', hα', b', ?_⟩
    rw [← hLe, ← hL'e, hsub, hsub, Subgroup.map_map, hcomp, ← Subgroup.map_map, hcL]
  refine ⟨x, fun y => ?_⟩
  rw [← hf (c y), ← hβ, hx, hf]

end Ident

namespace CaseBU

variable {K : Subgroup G} {P₁ P₂ : Set (Subgroup G)} {g u h e : G} {T : Subgroup G}

theorem commute_h (c : CaseBU Ω K P₁ P₂ g u h e T)
    (I : AEIdent P₁ 5) (hI : I.φ.ker = ⊥) :
    ∀ L ∈ Generic.centMembers Ω u, ∀ y ∈ L, h * y = y * h := by
  obtain ⟨m, hm, ⟨J⟩⟩ := c.exists_aeIdent I hI
  have h5 : 5 ≤ m := by omega
  have h7 : m ≤ 7 := by omega
  have hS : StarHyp Ω := c.hyp.toStarHyp
  have hcard : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => c.hyp.card_eq_eight hL
  set P := Generic.centMembers Ω u with hPdef
  have hPΩ : P ⊆ Ω := fun L hL => (Generic.mem_centMembers.mp hL).1
  have hP₂Ω : ∀ L ∈ P₂, L ∈ Ω := by
    intro L hL
    have hd : L ∈ dComp Ω K := by rw [c.dcomp]; exact Or.inr hL
    rcases Relation.ReflTransGen.cases_tail hd with hLK | ⟨M, -, hML⟩
    · have hLP₁ : L ∈ P₁ := hLK ▸ c.hK
      exact absurd hL (Set.disjoint_left.mp c.disj hLP₁)
    · exact hML.1
  have hP₂ : ∀ L ∈ P₂, L ∈ P := fun L hL =>
    Generic.mem_centMembers.mpr ⟨hP₂Ω L hL, c.P₂_u L hL⟩
  have hP₂sub : pSpan P₂ ≤ pSpan P := pSpan_le fun L hL => le_pSpan (hP₂ L hL)
  have hconj : ∀ n : G, n * u = u * n → ∀ L ∈ P, conjSub n L ∈ P := by
    intro n hn L hL
    have h1 := Generic.conjSub_mem_centMembers c.hyp.thmD.hyp.conjInvariant (a := u) (n := n) hL
    rwa [show n * u * n⁻¹ = u by rw [hn, mul_inv_cancel_right]] at h1
  have hhcomm : Commute h u := c.h_u
  obtain ⟨ca, hca₁, hca₂⟩ := endH_conjAut (hconj h c.h_u) (hconj h⁻¹ hhcomm.inv_left)
  have hcL : ∀ L ∈ P,
      (L.subgroupOf (pSpan P)).map ca.toMonoidHom = (conjSub h L).subgroupOf (pSpan P) := by
    intro L hL
    ext y
    rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, mem_conjSub_iff, ← hca₂]
    rfl
  have hg12 : ∀ L ∈ P₁, conjSub g L ∈ P₂ := fun L hL =>
    (c.swap (conjSub g L)).mpr (by rw [conjSub_inv_conjSub]; exact hL)
  obtain ⟨Yh, hYh⟩ : ∃ Yh : ↥(pSpan P₁) →* ↥(pSpan P), ∀ t, (Yh t : G) = g * t * g⁻¹ :=
    ⟨endH_conjHom (fun L hL => hP₂ _ (hg12 L hL)), fun t => rfl⟩
  have hYinj : Function.Injective Yh := fun a b hab => by
    apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    rw [hYh, hYh] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have hYP₂ : ∀ t : ↥(pSpan P₁), (Yh t : G) ∈ pSpan P₂ := fun t => by
    rw [hYh]
    exact endH_conj_mem_pSpan hg12 t.2
  have hPh : pSpan P₂ ≤ Subgroup.centralizer ({h} : Set G) :=
    pSpan_le fun L hL y hy => Subgroup.mem_centralizer_singleton_iff.mpr (c.h_P₂ L hL y hy).symm
  have hPh' : ∀ y ∈ pSpan P₂, h * y = y * h := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hPh hy)).symm
  obtain ⟨c₁, c₂, hc₁w, hc₁s, hc₂w, hc₂s, hc₁5, hc₂5, hK⟩ := endH_five_perms
  obtain ⟨t₁, ht₁⟩ : ∃ t : ↥(pSpan P₁), I.φ t = AE.mkQ 5 (AE.Wr.ofPerm c₁) := by
    have hr : AE.mkQ 5 (AE.Wr.ofPerm c₁) ∈ I.φ.range := by
      rw [I.range_eq]
      exact ⟨_, AE.mem_aeSub.mpr ⟨hc₁w, hc₁s⟩, rfl⟩
    exact MonoidHom.mem_range.mp hr
  obtain ⟨t₂, ht₂⟩ : ∃ t : ↥(pSpan P₁), I.φ t = AE.mkQ 5 (AE.Wr.ofPerm c₂) := by
    have hr : AE.mkQ 5 (AE.Wr.ofPerm c₂) ∈ I.φ.range := by
      rw [I.range_eq]
      exact ⟨_, AE.mem_aeSub.mpr ⟨hc₂w, hc₂s⟩, rfl⟩
    exact MonoidHom.mem_range.mp hr
  have ht₁5 : t₁ ^ 5 = 1 := by
    have h1 : t₁ ^ 5 ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ht₁, ← map_pow, hc₁5, map_one]
    rwa [hI, Subgroup.mem_bot] at h1
  have ht₂5 : t₂ ^ 5 = 1 := by
    have h1 : t₂ ^ 5 ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ht₂, ← map_pow, hc₂5, map_one]
    rwa [hI, Subgroup.mem_bot] at h1
  set V : ↥(pSpan P₁) := t₁ * t₂ * t₁⁻¹ * t₂⁻¹ with hVdef
  have hpermI : TL4.permBar 5 (I.φ V) = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by
    rw [hVdef]
    simp only [map_mul, map_inv, ht₁, ht₂, TL4.permBar_mkQ]
    rfl
  have hnc : TL4.permBar m (J.φ (Yh t₁)) * TL4.permBar m (J.φ (Yh t₂)) ≠
      TL4.permBar m (J.φ (Yh t₂)) * TL4.permBar m (J.φ (Yh t₁)) := by
    intro hcomm
    have hperm : TL4.permBar m (J.φ (Yh V)) = 1 := by
      have e : J.φ (Yh V) =
          J.φ (Yh t₁) * J.φ (Yh t₂) * (J.φ (Yh t₁))⁻¹ * (J.φ (Yh t₂))⁻¹ := by
        simp only [hVdef, map_mul, map_inv]
      rw [e]
      simp only [map_mul, map_inv]
      exact endH_comm_comm hcomm
    have hsq : J.φ (Yh V) * J.φ (Yh V) = 1 := endH_mul_self_of_permBar hperm
    have hWW : Yh V * Yh V ∈ Subgroup.center ↥(pSpan P) :=
      J.ker_le (by rw [MonoidHom.mem_ker, map_mul]; exact hsq)
    have hVcen : ∀ s : ↥(pSpan P₁), s * (V * V) = (V * V) * s := fun s =>
      hYinj (by
        have h1 := Subgroup.mem_center_iff.mp hWW (Yh s)
        simp only [map_mul]
        exact h1)
    have hA : I.φ (V * V) = 1 := by
      refine endH_eq_one_of_comm (m := 5) le_rfl (by norm_num) fun a ha => ?_
      rw [← I.range_eq] at ha
      obtain ⟨s, rfl⟩ := ha
      rw [← map_mul, ← map_mul, hVcen s]
    have hsqI : I.φ V * I.φ V = 1 := by
      rw [← map_mul]
      exact hA
    have hp := congrArg (TL4.permBar 5) hsqI
    rw [map_mul, map_one, hpermI] at hp
    exact hK hp
  have ha₁ : J.φ (Yh t₁) ≠ 1 := fun h1 => hnc (by rw [h1, map_one, one_mul, mul_one])
  have ha₂ : J.φ (Yh t₂) ≠ 1 := fun h2 => hnc (by rw [h2, map_one, mul_one, one_mul])
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hY₁ : Yh t₁ ^ 5 = 1 := by rw [← map_pow, ht₁5, map_one]
  have hY₂ : Yh t₂ ^ 5 = 1 := by rw [← map_pow, ht₂5, map_one]
  have ho₁ : orderOf (J.φ (Yh t₁)) = 5 :=
    orderOf_eq_prime (by rw [← map_pow, hY₁, map_one]) ha₁
  have ho₂ : orderOf (J.φ (Yh t₂)) = 5 :=
    orderOf_eq_prime (by rw [← map_pow, hY₂, map_one]) ha₂
  have hYfix : ∀ t : ↥(pSpan P₁), ca (Yh t) = Yh t := fun t => by
    apply Subtype.ext
    rw [hca₁]
    rw [hPh' _ (hYP₂ t), mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨x, hx⟩ := endH_exists_conj h5 h7 J ca
    (fun L hL => ⟨conjSub h L, hconj h c.h_u L hL, hcL L hL⟩)
  have hcx : ∀ t : ↥(pSpan P₁), x * J.φ (Yh t) = J.φ (Yh t) * x := by
    intro t
    have h1 := hx (Yh t)
    rw [hYfix t] at h1
    calc x * J.φ (Yh t) = x * J.φ (Yh t) * x⁻¹ * x := by group
      _ = J.φ (Yh t) * x := by rw [← h1]
  have hx4 : x ^ 4 = 1 :=
    AEQEnd.pow_four_eq_one_of_comm_five h7 ho₁ ho₂ hnc (hcx t₁) (hcx t₂)
  have hca3 : ∀ y : ↥(pSpan P), ca (ca (ca y)) = y := by
    intro y
    apply Subtype.ext
    rw [hca₁, hca₁, hca₁]
    have h3 : h * (h * h) = 1 := by
      have := pow_orderOf_eq_one h
      rw [c.h_three, pow_three] at this
      exact this
    calc h * (h * (h * (y : G) * h⁻¹) * h⁻¹) * h⁻¹ =
          (h * (h * h)) * (y : G) * (h * (h * h))⁻¹ := by group
      _ = y := by rw [h3]; simp
  have hthree : ∀ y : ↥(pSpan P), J.φ y = x ^ 3 * J.φ y * (x ^ 3)⁻¹ := by
    intro y
    have e1 := hx y
    have e2 := hx (ca y)
    have e3 := hx (ca (ca y))
    rw [hca3 y] at e3
    calc J.φ y = x * J.φ (ca (ca y)) * x⁻¹ := e3
      _ = x * (x * J.φ (ca y) * x⁻¹) * x⁻¹ := by rw [e2]
      _ = x * (x * (x * J.φ y * x⁻¹) * x⁻¹) * x⁻¹ := by rw [e1]
      _ = x ^ 3 * J.φ y * (x ^ 3)⁻¹ := by rw [pow_three]; group
  have hcomm3 : ∀ y : ↥(pSpan P), Commute (x ^ 3) (J.φ y) := fun y =>
    ((eq_mul_inv_iff_mul_eq).mp (hthree y)).symm
  have hxinv : x = (x ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ']; exact hx4)
  have hxcomm : ∀ a ∈ (AE.aeSub m).map (AE.mkQ m), x * a = a * x := by
    intro a ha
    rw [← J.range_eq] at ha
    obtain ⟨y, rfl⟩ := ha
    rw [hxinv]
    exact (hcomm3 y).inv_left
  have hfixJ : ∀ y : ↥(pSpan P), J.φ (ca y) = J.φ y := fun y => by
    have hmem : J.φ y ∈ (AE.aeSub m).map (AE.mkQ m) := by
      rw [← J.range_eq]
      exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
    rw [hx y, hxcomm (J.φ y) hmem, mul_assoc, mul_inv_cancel, mul_one]
  have hcomp2 : J.φ.comp ca.toMonoidHom = J.φ := MonoidHom.ext hfixJ
  have hLfix : ∀ L ∈ P, conjSub h L = L := by
    intro L hL
    refine (hS.aeIdent_map_injective hPΩ J hL (hconj h c.h_u L hL) ?_).symm
    rw [← hcL L hL, Subgroup.map_map, hcomp2]
  intro L hL y hy
  have hmem : h * y * h⁻¹ ∈ L := by
    have h1 := conj_mem_conjSub (n := h) hy
    rwa [hLfix L hL] at h1
  obtain ⟨α, hα, b, hlab⟩ := J.label L hL
  have he : J.φ ⟨h * y * h⁻¹, le_pSpan hL hmem⟩ = J.φ ⟨y, le_pSpan hL hy⟩ := by
    have hyv : ca ⟨y, le_pSpan hL hy⟩ = ⟨h * y * h⁻¹, le_pSpan hL hmem⟩ :=
      Subtype.ext (hca₁ _)
    rw [← hyv]
    exact hfixJ _
  have hyy := J.injOn h5 hL (hcard L (hPΩ hL)) hlab hmem hy he
  exact mul_inv_eq_iff_eq_mul.mp hyy

end CaseBU

end CFSG.ClassicalInvolution.Q3.Sec13
