module

public import Certificates.Data.Y63.Spec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LPres
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LInst

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.OddStandard.HigherRank.G2Three.Sec2

@[ext] structure Y63TG where
  val : ℕ
  lt : val < 512

@[expose] def Y63TG.equivFin : Y63TG ≃ Fin 512 where
  toFun x := ⟨x.val, x.lt⟩
  invFun i := ⟨i.val, i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Y63TG := Fintype.ofEquiv (Fin 512) Y63TG.equivFin.symm

instance : DecidableEq Y63TG :=
  fun a b => decidable_of_iff (a.val = b.val) (by simp [Y63TG.ext_iff])

theorem Y63TG.card : Nat.card Y63TG = 512 := by
  rw [Nat.card_congr Y63TG.equivFin, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem y63_invCode_eq (c : ℕ) :
    CFSG.Certificates.CosetEnumeration.invCode c = if c % 2 = 0 then c + 1 else c - 1 := by
  unfold CFSG.Certificates.CosetEnumeration.invCode
  by_cases h : c % 2 = 0
  · have : Nat.beq (Nat.mod c 2) 0 = true := by rw [Nat.beq_eq]; exact h
    rw [this]; simp [h]
  · have : Nat.beq (Nat.mod c 2) 0 = false := by
      cases hb : Nat.beq (Nat.mod c 2) 0 with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [this]; simp [h]

theorem y63_tg (D : Y63Chk.Data) (hT : D.TabSpec)
    (hW : D.WordSpec) (hM : D.MulSpec) :
    ∃ (_ : Group Y63TG) (f : PresentedGroup (rels26 2 false) ≃* Y63TG),
      (∀ x y : Y63TG, (x * y).val = D.mt x.val y.val) ∧ (1 : Y63TG).val = 0 ∧
        (∀ i : Fin 5, (f (PresentedGroup.of i)).val = D.T 0 (2 * i.val)) ∧
        Subgroup.closure (Set.range fun i : Fin 5 => f (PresentedGroup.of i)) = ⊤ := by
  rw [y2l_rels26_eq 2 false]
  let S : Set (FreeGroup (Fin 5)) :=
    {r : FreeGroup (Fin 5) | r ∈ (y2l_ws26 2 false).map FreeGroup.mk}
  let c0 : {c : ℕ // c < 512} := ⟨0, by norm_num⟩
  have hcodes : Y63Chk.relCodes () =
      CFSG.Certificates.CosetEnumeration.codes (y2l_ws26 2 false) := rfl
  have hlive : ∀ c, c < 512 → ∀ x < 2 * 5, D.T c x < 512 := by
    intro c hc x hx
    exact hT.1 c hc x (by omega)
  have hinv : ∀ c, c < 512 → ∀ x < 2 * 5,
      D.T (D.T c x) (CFSG.Certificates.CosetEnumeration.invCode x) = c := by
    intro c hc x hx
    rw [y63_invCode_eq]
    exact hT.2.1 c hc x (by omega)
  have hrel : ∀ c, c < 512 →
      ∀ r ∈ CFSG.Certificates.CosetEnumeration.codes (y2l_ws26 2 false),
        r.foldl D.T c = c := by
    intro c hc r hr
    rw [← hcodes] at hr
    exact hT.2.2 r hr c hc
  obtain ⟨ψ, hψ⟩ := CFSG.CosetTable.exists_action_step (y2l_ws26 2 false) (fun c => c < 512)
    (fun c x => D.T c x) hlive hinv hrel
  have hWlt : ∀ y < 512, ∀ z ∈ D.W y, z < 2 * 5 := by
    intro y hy z hz
    have := (hW y hy).1 z hz
    omega
  let gen := CFSG.Certificates.CosetEnumeration.presLetter S
  let e : PresentedGroup S → Y63TG :=
    fun g => ⟨((ψ g).unop c0).1, ((ψ g).unop c0).2⟩
  have hsurj : Function.Surjective e := by
    intro y
    refine ⟨CFSG.Certificates.CosetEnumeration.evalWord gen (D.W y.val), ?_⟩
    apply Y63TG.ext
    show ((ψ (CFSG.Certificates.CosetEnumeration.evalWord gen (D.W y.val))).unop c0).1 = y.val
    rw [CFSG.CosetTable.act_evalWord_step (gen := gen) ψ hψ (D.W y.val) (hWlt y.val y.lt) c0]
    exact (hW y.val y.lt).2
  haveI hfinPi : Finite (PresentedGroup S) := by
    change Finite (PresentedGroup
      {r : FreeGroup (Fin 5) | r ∈ (y2l_ws26 2 false).map FreeGroup.mk})
    rw [← y2l_rels26_eq 2 false]
    exact (y2l_card_P2_le false).1
  have hcard : Nat.card (PresentedGroup S) ≤ 512 := by
    change Nat.card (PresentedGroup
      {r : FreeGroup (Fin 5) | r ∈ (y2l_ws26 2 false).map FreeGroup.mk}) ≤ 512
    rw [← y2l_rels26_eq 2 false]
    exact (y2l_card_P2_le false).2
  have he : Function.Bijective e :=
    hsurj.bijective_of_nat_card_le (by rw [Y63TG.card]; exact hcard)
  let E : PresentedGroup S ≃ Y63TG := Equiv.ofBijective e he
  letI : Group Y63TG := Equiv.group E.symm
  let f : PresentedGroup S ≃* Y63TG := (Equiv.mulEquiv E.symm).symm
  have hf : ∀ g : PresentedGroup S, f g = E g := fun g => rfl
  refine ⟨inferInstance, f, ?_, ?_, ?_, ?_⟩
  · intro x y
    change (E (E.symm x * E.symm y)).val = D.mt x.val y.val
    have hgy : E (CFSG.Certificates.CosetEnumeration.evalWord gen (D.W y.val)) = y := by
      apply Y63TG.ext
      show ((ψ (CFSG.Certificates.CosetEnumeration.evalWord gen (D.W y.val))).unop c0).1 = y.val
      rw [CFSG.CosetTable.act_evalWord_step (gen := gen) ψ hψ (D.W y.val) (hWlt y.val y.lt) c0]
      exact (hW y.val y.lt).2
    have hsub : E.symm y = CFSG.Certificates.CosetEnumeration.evalWord gen (D.W y.val) := by
      apply E.injective
      rw [E.apply_symm_apply, hgy]
    rw [hsub]
    show ((ψ (E.symm x * CFSG.Certificates.CosetEnumeration.evalWord gen (D.W y.val))).unop
      c0).1 = D.mt x.val y.val
    rw [CFSG.CosetTable.act_mul,
      CFSG.CosetTable.act_evalWord_step (gen := gen) ψ hψ (D.W y.val) (hWlt y.val y.lt)
        ((ψ (E.symm x)).unop c0)]
    have hxval : ((ψ (E.symm x)).unop c0).1 = x.val :=
      congrArg Y63TG.val (E.apply_symm_apply x)
    rw [hxval]
    exact ((hM x.val x.lt y.val y.lt).1).symm
  · change (E 1).val = 0
    show ((ψ (1 : PresentedGroup S)).unop c0).1 = 0
    rw [CFSG.CosetTable.act_one]
  · intro i
    rw [hf]
    show (E (PresentedGroup.of i)).val = D.T 0 (2 * i.val)
    rw [← CFSG.CosetTable.presLetter_even S i]
    exact hψ (2 * i.val) (by omega) c0
  · have hrange : Set.range (fun i : Fin 5 => f (PresentedGroup.of i)) =
        f.toMonoidHom '' Set.range (PresentedGroup.of : Fin 5 → PresentedGroup S) := by
      ext g; constructor
      · rintro ⟨i, rfl⟩
        exact ⟨PresentedGroup.of i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hrange, ← MonoidHom.map_closure f.toMonoidHom
        (Set.range (PresentedGroup.of : Fin 5 → PresentedGroup S)),
      PresentedGroup.closure_range_of (α := Fin 5) (rels := S),
      Subgroup.map_top_of_surjective f.toMonoidHom f.surjective]

theorem y63_isPres26_pi : IsPres26 2 false (PresentedGroup (rels26 2 false))
    (PresentedGroup.of 0) (PresentedGroup.of 1) (PresentedGroup.of 2) (PresentedGroup.of 3)
    (PresentedGroup.of 4) := by
  have hfun : (![PresentedGroup.of 0, PresentedGroup.of 1, PresentedGroup.of 2,
      PresentedGroup.of 3, PresentedGroup.of 4] : Fin 5 → PresentedGroup (rels26 2 false)) =
      PresentedGroup.of := by
    funext i
    fin_cases i <;> rfl
  have hlift : FreeGroup.lift (![PresentedGroup.of 0, PresentedGroup.of 1, PresentedGroup.of 2,
      PresentedGroup.of 3, PresentedGroup.of 4] : Fin 5 → PresentedGroup (rels26 2 false)) =
      PresentedGroup.mk (rels26 2 false) := by
    rw [hfun]
    apply FreeGroup.ext_hom
    intro x
    rw [FreeGroup.lift_apply_of]
    rfl
  have hrel : ∀ x ∈ rels26 2 false,
      FreeGroup.lift (![PresentedGroup.of 0, PresentedGroup.of 1, PresentedGroup.of 2,
        PresentedGroup.of 3, PresentedGroup.of 4] :
        Fin 5 → PresentedGroup (rels26 2 false)) x = 1 := by
    intro x hx
    rw [hlift]
    exact PresentedGroup.one_of_mem hx
  refine ⟨hrel, ?_⟩
  have hto : PresentedGroup.toGroup hrel = MonoidHom.id (PresentedGroup (rels26 2 false)) := by
    apply PresentedGroup.ext
    intro i
    rw [PresentedGroup.toGroup.of]
    fin_cases i <;> rfl
  rw [hto]
  exact Function.bijective_id

theorem y63_equiv_P [Group Y63TG] (f : PresentedGroup (rels26 2 false) ≃* Y63TG)
    (h26HS : Lemma26HS) (hfin : Finite TauCeti.SporadicName.HS.Group) {P : Type} [Group P]
    (hP : IsHSType P) : Nonempty (P ≃* Y63TG) := by
  have hPi : IsHSType (PresentedGroup (rels26 2 false)) :=
    h26HS (PresentedGroup (rels26 2 false)) (PresentedGroup.of 0) (PresentedGroup.of 1)
      (PresentedGroup.of 2) (PresentedGroup.of 3) (PresentedGroup.of 4) y63_isPres26_pi
  letI := hfin
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow 2 TauCeti.SporadicName.HS.Group))
  obtain ⟨eP⟩ := hP S
  obtain ⟨ePi⟩ := hPi S
  exact ⟨eP.trans (ePi.symm.trans f)⟩

end CFSG.OddStandard.HigherRank.YamadaG23
