module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusLemma24

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

variable {A B : Type} [Group A] [Group B]

theorem pPrimeCore_map_of_ker [Finite A] (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ pPrimeCore 2 A) : (pPrimeCore 2 A).map φ = pPrimeCore 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective φ hφ
  have hOA : Nat.Coprime 2 (Nat.card (pPrimeCore 2 A)) := pPrimeCore_coprime_card
  apply le_antisymm
  · refine le_sSup ⟨Subgroup.Normal.map pPrimeCore_normal φ hφ, ?_⟩
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ φ) hOA
  · have hOB : Nat.Coprime 2 (Nat.card (pPrimeCore 2 B)) := pPrimeCore_coprime_card
    set D := (pPrimeCore 2 B).comap φ with hD
    have hDn : D.Normal := Subgroup.Normal.comap pPrimeCore_normal φ
    have hDodd : Nat.Coprime 2 (Nat.card D) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h2 => ?_
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 h2
      have hxA : orderOf (x : A) = 2 := by rw [Subgroup.orderOf_coe, hx]
      have hφx : φ (x : A) ∈ pPrimeCore 2 B := x.2
      have hord : orderOf (φ (x : A)) ∣ 2 := hxA ▸ orderOf_map_dvd φ (x : A)
      have hord2 : orderOf (φ (x : A)) ∣ Nat.card (pPrimeCore 2 B) :=
        Subgroup.orderOf_dvd_natCard _ hφx
      have h1 : orderOf (φ (x : A)) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord hOB) hord2
      have hker1 : (x : A) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        exact orderOf_eq_one_iff.mp h1
      have h3 : orderOf (x : A) ∣ Nat.card (pPrimeCore 2 A) :=
        Subgroup.orderOf_dvd_natCard _ (hker hker1)
      rw [hxA] at h3
      have := Nat.Coprime.eq_one_of_dvd hOA h3
      omega
    have hDle : D ≤ pPrimeCore 2 A := le_sSup ⟨hDn, hDodd⟩
    calc pPrimeCore 2 B = D.map φ := (Subgroup.map_comap_eq_self_of_surjective hφ _).symm
      _ ≤ (pPrimeCore 2 A).map φ := Subgroup.map_mono hDle

@[expose] noncomputable def quotEquivOfKer [Finite A] (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ pPrimeCore 2 A) : (A ⧸ pPrimeCore 2 A) ≃* (B ⧸ pPrimeCore 2 B) :=
  have hle : pPrimeCore 2 A ≤ (pPrimeCore 2 B).comap φ := by
    rw [← pPrimeCore_map_of_ker φ hφ hker]
    exact Subgroup.le_comap_map _ _
  MulEquiv.ofBijective (QuotientGroup.map (pPrimeCore 2 A) (pPrimeCore 2 B) φ hle)
    ⟨by
      intro x y
      induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      intro h
      rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.eq] at h
      rw [QuotientGroup.eq]
      have h' : φ (a⁻¹ * b) ∈ (pPrimeCore 2 A).map φ := by
        rw [pPrimeCore_map_of_ker φ hφ hker, map_mul, map_inv]
        exact h
      obtain ⟨o, ho, hoeq⟩ := h'
      have hk : o⁻¹ * (a⁻¹ * b) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hoeq]
        group
      have := (pPrimeCore 2 A).mul_mem ho (hker hk)
      simpa using this,
     by
      intro y
      induction y using QuotientGroup.induction_on with | H b => ?_
      obtain ⟨a, rfl⟩ := hφ b
      exact ⟨QuotientGroup.mk a, QuotientGroup.map_mk _ _ _ _ _⟩⟩

theorem LPlus_comap [Finite A] (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ pPrimeCore 2 A) : (LPlus B).comap φ = LPlus A := by
  let e := quotEquivOfKer φ hφ hker
  have hcomp : (QuotientGroup.mk' (pPrimeCore 2 B)).comp φ =
      e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 A)) := by
    ext a
    rfl
  unfold LPlus
  rw [Subgroup.comap_comap, hcomp, ← Subgroup.comap_comap, ← EPlus_map e,
    Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective]

theorem LPlus_map_equiv [Finite A] (e : A ≃* B) : (LPlus A).map e.toMonoidHom = LPlus B := by
  have h := LPlus_comap e.toMonoidHom e.surjective (by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := e.injective (by simpa using hx)
    rw [this]
    exact one_mem _)
  rw [← h]
  exact Subgroup.map_comap_eq_self_of_surjective e.surjective _

theorem LPlus_map_aut [Finite A] (φ : MulAut A) : (LPlus A).map φ.toMonoidHom = LPlus A :=
  LPlus_map_equiv φ

theorem LPlus_eq_EPlus [Finite B] (h : pPrimeCore 2 B = ⊥) : LPlus B = EPlus B := by
  have hinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 B)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', h]
  let e : B ≃* (B ⧸ pPrimeCore 2 B) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (pPrimeCore 2 B))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  unfold LPlus
  have : (EPlus (B ⧸ pPrimeCore 2 B)) = (EPlus B).map e.toMonoidHom := (EPlus_map e).symm
  change (EPlus (B ⧸ pPrimeCore 2 B)).comap e.toMonoidHom = EPlus B
  rw [this, Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective]

section Lemma25

variable {X : Type} [Group X]

theorem pPrimeCore_eq_bot_of_normal [Finite X] (h : pPrimeCore 2 X = ⊥) (Y : Subgroup X)
    [Y.Normal] : pPrimeCore 2 Y = ⊥ := by
  have hQ0 : (pPrimeCore 2 Y).map Y.subtype = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← h]
    refine le_sSup ⟨?_, ?_⟩
    · refine ⟨fun x hx g => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      have hinv : (pPrimeCore 2 Y).map (MulAut.conjNormal g).toMonoidHom = pPrimeCore 2 Y :=
        pPrimeCore_map_iso 2 (MulAut.conjNormal g)
      have hmem : (MulAut.conjNormal g : MulAut Y) y ∈ pPrimeCore 2 Y := by
        have : (MulAut.conjNormal g : MulAut Y) y ∈
            (pPrimeCore 2 Y).map (MulAut.conjNormal g).toMonoidHom := ⟨y, hy, rfl⟩
        rwa [hinv] at this
      exact ⟨_, hmem, by simp⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact pPrimeCore_coprime_card
  exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hQ0

theorem pCore_three_eq_bot [Finite X] (h : pPrimeCore 2 X = ⊥) : pCore 3 X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : (pCore 3 X).Normal := pCore_normal
  have hp : IsPGroup 3 (pCore 3 X) := pCore_isPGroup
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hcop : Nat.Coprime 2 (Nat.card (pCore 3 X)) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hle : pCore 3 X ≤ pPrimeCore 2 X := le_sSup ⟨hn, hcop⟩
  rw [h] at hle
  exact le_bot_iff.mp hle

theorem EPlus_le_of_normal [Finite X] (B : Subgroup X) [B.Normal] (h3 : pCore 3 B = ⊥) :
    (EPlus B).map B.subtype ≤ EPlus X := by
  unfold EPlus
  rw [Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le_sup (sup_le_sup ?_ ?_) ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨?_, ?_⟩
    · exact LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective K B.subtype B.subtype_injective) hK.1
    · exact Subgroup.IsSubnormal.trans' hK.2 (‹B.Normal›.isSubnormal)
  · obtain ⟨-, hNc, -⟩ := lemma_2_4_one h3
    have hnormN : ((NOne B).map B.subtype).Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      have hmem : (MulAut.conjNormal g : MulAut B) y ∈ NOne B := by
        have : (MulAut.conjNormal g : MulAut B) y ∈
            (NOne B).map (MulAut.conjNormal g).toMonoidHom := ⟨y, hy, rfl⟩
        rwa [NOne_map_aut] at this
      exact ⟨_, hmem, by simp⟩
    exact le_NOne hnormN (hNc.map_hom B.subtype B.subtype_injective)
  · obtain ⟨-, hNc, -⟩ := lemma_2_4_two h3
    have hnormN : ((NTwo B).map B.subtype).Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      have hmem : (MulAut.conjNormal g : MulAut B) y ∈ NTwo B := by
        have : (MulAut.conjNormal g : MulAut B) y ∈
            (NTwo B).map (MulAut.conjNormal g).toMonoidHom := ⟨y, hy, rfl⟩
        rwa [NTwo_map_aut] at this
      exact ⟨_, hmem, by simp⟩
    exact le_NTwo hnormN (hNc.map_hom B.subtype B.subtype_injective)

theorem lPlus_le_of_normal [Finite X] (Y : Subgroup X) [Y.Normal] :
    (LPlus ↥Y).map Y.subtype ≤ LPlus X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (pPrimeCore 2 X) with hq
  set Yb : Subgroup (X ⧸ pPrimeCore 2 X) := Y.map q with hYb
  have hYbn : Yb.Normal := Subgroup.Normal.map ‹Y.Normal› q (QuotientGroup.mk'_surjective _)
  let φ : ↥Y →* ↥Yb := (q.comp Y.subtype).codRestrict Yb (fun y => ⟨y, y.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : φ.ker ≤ pPrimeCore 2 ↥Y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hyq : q (y : X) = 1 := congrArg Subtype.val hy
    have hyO : (y : X) ∈ pPrimeCore 2 X := (QuotientGroup.eq_one_iff _).mp hyq
    set D : Subgroup ↥Y := (pPrimeCore 2 X).subgroupOf Y with hD
    have hDn : D.Normal := Subgroup.normal_subgroupOf
    have hDcop : Nat.Coprime 2 (Nat.card D) := by
      have hle : D.map Y.subtype ≤ pPrimeCore 2 X := by
        rintro _ ⟨d, hd, rfl⟩
        exact hd
      have hdvd : Nat.card D ∣ Nat.card (pPrimeCore 2 X) := by
        have hcard : Nat.card (D.map Y.subtype) = Nat.card D :=
          Subgroup.card_map_of_injective Y.subtype_injective
        rw [← hcard]
        exact Subgroup.card_dvd_of_le hle
      exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
    exact (le_sSup ⟨hDn, hDcop⟩ : D ≤ pPrimeCore 2 ↥Y) hyO
  have hcomap := LPlus_comap φ hφs hker
  have hO : pPrimeCore 2 ↥Yb = ⊥ :=
    pPrimeCore_eq_bot_of_normal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) Yb
  have hLE : LPlus ↥Yb = EPlus ↥Yb := LPlus_eq_EPlus hO
  have hE := EPlus_le_of_normal Yb (pCore_three_eq_bot hO)
  rintro _ ⟨y, hy, rfl⟩
  have hy' : φ y ∈ LPlus ↥Yb := by
    have : y ∈ (LPlus ↥Yb).comap φ := hcomap ▸ hy
    exact this
  rw [hLE] at hy'
  exact hE ⟨φ y, hy', rfl⟩

end Lemma25

end CFSG.OddStandard.Solomon75
