module

public import CFSG.CGT.PushingUpLit.BHS5.AmbientJ
public import CFSG.CGT.PushingUpLit.BHS7.VFacts

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def Seven14Pair (G T E A : Subgroup Γ) : Prop :=
  A ≤ baum T ∧ ⁅E, A⁆ = E ∧ ⁅⁅vSub G T, A⁆, A⁆ = ⊥ ∧
    (vSub G T ⊓ Subgroup.centralizer (A : Set Γ)).relIndex (vSub G T) =
      (A ⊓ Subgroup.centralizer (vSub G T : Set Γ)).relIndex A ∧
    ∀ a ∈ A, a ∉ Subgroup.centralizer (vSub G T : Set Γ) →
      vSub G T ⊓ Subgroup.centralizer (A : Set Γ) =
        vSub G T ⊓ Subgroup.centralizer ({a} : Set Γ)

@[expose] def ySet (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  {A | ∃ E : Subgroup Γ, IsBTBlock G T E ∧ ¬ E ≤ cStarIn G T ∧ Seven14Pair G T E A}

@[expose] noncomputable def dBar (G T : Subgroup Γ) : Set (Subgroup (MulAut ↥(vSub G T))) :=
  {B | ∃ g ∈ autOn G (vSub G T), ∃ A ∈ ySet G T, B = A1b.conjSub g (autOn A (vSub G T))}

@[expose] noncomputable def pBar (G T : Subgroup Γ) : Subgroup (MulAut ↥(vSub G T)) :=
  (⨆ B ∈ dBar G T, B) ⊔ autOn T (vSub G T)

@[expose] noncomputable def mBar (G T : Subgroup Γ) : Subgroup (MulAut ↥(vSub G T)) :=
  pBar G T ⊓ autOn (cStarIn G T) (vSub G T)

theorem autOn_commutator_eq {V X R : Subgroup Γ}
    (hX : X ≤ Subgroup.normalizer (V : Set Γ)) (hR : R ≤ Subgroup.normalizer (V : Set Γ)) :
    autOn ⁅X, R⁆ V = ⁅autOn X V, autOn R V⁆ := by
  set N : Subgroup Γ := Subgroup.normalizer (V : Set Γ) with hN
  have h1 : ⁅X, R⁆ ≤ N := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hX hx) (hR hy)) (N.inv_mem (hX hx)))
      (N.inv_mem (hR hy))
  unfold autOn
  have h2 : ⁅X, R⁆.subgroupOf N = ⁅X.subgroupOf N, R.subgroupOf N⁆ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le h1, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hR]
  rw [h2, Subgroup.map_commutator]

section Fixed

variable {V : Type} [CommGroup V]

theorem mem_fixV_zpowers {a : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers a) ↔ a v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_conjSub_aut (g : MulAut V) (X : Subgroup (MulAut V)) :
    Nat.card (A1b.conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))

structure Good41 (B : Subgroup (MulAut V)) : Prop where
  ne_bot : B ≠ ⊥
  elemAb : IsElemAbelian2 B
  quad : IsQuadratic B
  card_eq : Nat.card V = Nat.card B * Nat.card (fixV B)
  fixV_eq : ∀ b ∈ B, b ≠ 1 → fixV (Subgroup.zpowers b) = fixV B

theorem Good41.conj {B : Subgroup (MulAut V)} (h : Good41 B) (g : MulAut V) :
    Good41 (A1b.conjSub g B) := by
  have hfix : ∀ X : Subgroup (MulAut V), fixV (A1b.conjSub g X) = (fixV X).map g.toMonoidHom :=
    fun X => Glauberman.fixV_map_conj g X
  refine ⟨?_, isElemAbelian2_conjSub h.elemAb g, ?_, ?_, ?_⟩
  · intro hb
    apply h.ne_bot
    rw [← (A1b.conjSub_inj g).1 (hb.trans (Subgroup.map_bot _).symm)]
  · have h1 : commV (A1b.conjSub g B) = (commV B).map g.toMonoidHom :=
      B19.commV_map_conj g B
    intro x hx
    rw [h1] at hx
    rw [hfix]
    exact Subgroup.map_mono h.quad hx
  · rw [card_conjSub_aut, hfix, Subgroup.card_map_of_injective g.injective]
    exact h.card_eq
  · intro b hb hb1
    have hb' : g⁻¹ * b * g ∈ B := (A1b.mem_conjSub_iff).1 hb
    have hb1' : g⁻¹ * b * g ≠ 1 := fun h' => hb1 (by
      have : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
      rw [this, h']
      group)
    have e : Subgroup.zpowers b = A1b.conjSub g (Subgroup.zpowers (g⁻¹ * b * g)) := by
      show Subgroup.zpowers b = (Subgroup.zpowers (g⁻¹ * b * g)).map (MulAut.conj g).toMonoidHom
      have hb2 : (MulAut.conj g).toMonoidHom (g⁻¹ * b * g) = b := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [MonoidHom.map_zpowers, hb2]
    rw [e, hfix, h.fixV_eq _ hb' hb1', ← hfix]

end Fixed

section Members

variable [Finite Γ] {G T : Subgroup Γ}

omit [Finite Γ] in
theorem not_le_centralizer_vSub_of_commutator {E A : Subgroup Γ} (hEG : E ≤ G)
    (hEA : ⁅E, A⁆ = E) (hE : ¬ E ≤ cStarIn G T) :
    ¬ A ≤ Subgroup.centralizer (vSub G T : Set Γ) := by
  intro hA
  apply hE
  have hGV : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have h1 : ⁅E, A⁆ ≤ Subgroup.centralizer (vSub G T : Set Γ) := by
    refine Subgroup.commutator_le.2 fun e he a ha => ?_
    rw [commutatorElement_def]
    have hC : e * a * e⁻¹ ∈ Subgroup.centralizer (vSub G T : Set Γ) :=
      (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_centralizer hGV (hEG he)) a).mp (hA ha)
    exact (Subgroup.centralizer (vSub G T : Set Γ)).mul_mem hC
      ((Subgroup.centralizer (vSub G T : Set Γ)).inv_mem (hA ha))
  intro x hx
  exact centralizer_vSub_le_cStarIn G T ⟨hEG hx, h1 (by rw [hEA]; exact hx)⟩

omit [Finite Γ] in
theorem good41_autOn {V A : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hAN : A ≤ Subgroup.normalizer (V : Set Γ)) (hne : ¬ A ≤ Subgroup.centralizer (V : Set Γ))
    (hq : ⁅⁅V, A⁆, A⁆ = ⊥)
    (hrel : (V ⊓ Subgroup.centralizer (A : Set Γ)).relIndex V =
      (A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A)
    (hfix : ∀ a ∈ A, a ∉ Subgroup.centralizer (V : Set Γ) →
      V ⊓ Subgroup.centralizer (A : Set Γ) = V ⊓ Subgroup.centralizer ({a} : Set Γ)) :
    @Good41 ↥V (commGroupOfElemAbelian hV) (autOn A V) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hV.2 v v.2)
  have hquad : IsQuadratic (autOn A V) := by
    intro c hc
    have hc' : (c : Γ) ∈ ⁅V, A⁆ := by
      rw [← map_commV_autOn hV hAN]
      exact ⟨c, hc, rfl⟩
    rw [mem_fixV_autOn_iff hV hAN, Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : ⁅(c : Γ), a⁆ ∈ (⁅⁅V, A⁆, A⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hc' ha
    rw [hq, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  refine ⟨CFSG.CGT.PushingUpLit.BHS5.autOn_ne_bot_of_not_le_centralizer hAN hne,
    isElemAbelian2_of_isQuadratic hV2 hquad, hquad, ?_, ?_⟩
  · rw [card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hV hAN, ← hrel]
    have h3 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set Γ)) V
    rw [inf_of_le_left inf_le_left] at h3
    exact h3.symm
  · intro a ha hne1
    obtain ⟨a', ha'A, rfl⟩ := mem_autOn_iff.1 ha
    have hnc : (a' : Γ) ∉ Subgroup.centralizer (V : Set Γ) := fun h =>
      hne1 ((conjAct_eq_one_iff V a').2 h)
    have h := hfix a' ha'A hnc
    ext v
    rw [mem_fixV_zpowers, mem_fixV_autOn_iff hV hAN]
    constructor
    · intro h1
      have hv : (v : Γ) ∈ V ⊓ Subgroup.centralizer ({(a' : Γ)} : Set Γ) := by
        refine ⟨v.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have h2 := congrArg (fun w : ↥V => (w : Γ)) h1
        simp only [conjAct_apply'] at h2
        exact (calc (a' : Γ) * v = ((a' : Γ) * v * (a' : Γ)⁻¹) * a' := by group
          _ = v * a' := by rw [h2]).symm
      rw [← h] at hv
      exact hv.2
    · intro h1
      have hv : (v : Γ) ∈ V ⊓ Subgroup.centralizer ({(a' : Γ)} : Set Γ) := by
        rw [← h]
        exact ⟨v.2, h1⟩
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 hv.2
      apply Subtype.ext
      rw [conjAct_apply']
      calc (a' : Γ) * v * (a' : Γ)⁻¹ = (v * a') * (a' : Γ)⁻¹ := by rw [← h2]
        _ = v := by group

omit [Finite Γ] in
theorem conj_mem_dBar {B : Subgroup (MulAut ↥(vSub G T))} (hB : B ∈ dBar G T)
    {g : MulAut ↥(vSub G T)} (hg : g ∈ autOn G (vSub G T)) : A1b.conjSub g B ∈ dBar G T := by
  obtain ⟨g', hg', A, hA, rfl⟩ := hB
  exact ⟨g * g', (autOn G (vSub G T)).mul_mem hg hg', A, hA, (A1b.conjSub_mul g g' _).symm⟩

omit [Finite Γ] in
theorem le_baum_of_mem_ySet {A : Subgroup Γ} (hA : A ∈ ySet G T) : A ≤ baum T := by
  obtain ⟨E, -, -, hpair⟩ := hA
  exact hpair.1

end Members

end CFSG.CGT.PushingUpLit.BHS7
