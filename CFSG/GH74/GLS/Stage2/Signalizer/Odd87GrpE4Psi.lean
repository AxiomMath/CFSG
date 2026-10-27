module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Sl2Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section

variable {A : Type} [Group A] {a : A} {p : ℕ} {X J : Subgroup A}

@[expose] def secPsi (a : A) (X J : Subgroup A) : ↥J →* ↥(secJ a X J) where
  toFun j := ⟨secMk a X J j (J_le_secY a X J j.2), secMk_mem_secJ j.2⟩
  map_one' := Subtype.ext secMk_one
  map_mul' j₁ j₂ := Subtype.ext (secMk_mul (J_le_secY a X J j₁.2) (J_le_secY a X J j₂.2))

@[simp] theorem secPsi_coe (j : ↥J) :
    ((secPsi a X J j : ↥(secJ a X J)) : secB a X J) = secMk a X J j (J_le_secY a X J j.2) := rfl

theorem secPsi_surjective : Function.Surjective (secPsi a X J) := by
  intro b
  obtain ⟨j, hj, hb⟩ := mem_secJ_iff.mp b.2
  exact ⟨⟨j, hj⟩, Subtype.ext hb.symm⟩

theorem secPsi_eq_one_iff (j : ↥J) :
    secPsi a X J j = 1 ↔
      (⟨(j : A), J_le_secY a X J j.2⟩ : ↥(secY a X J)) ∈ pPrimeCore 2 ↥(secY a X J) := by
  constructor
  · intro h
    exact (secMk_eq_one_iff _).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((secMk_eq_one_iff _).mpr h)

section Fin

variable [Finite A]

theorem secPsi_ker_central (h : SubHyp a p X J) : (secPsi a X J).ker ≤ center ↥J := by
  intro j hj
  rw [Subgroup.mem_center_iff]
  intro j'
  apply Subtype.ext
  have := N_comm_J h ((secPsi_eq_one_iff j).mp hj) j'.2
  exact this.symm

theorem secPsi_ker_odd (_h : SubHyp a p X J) : Odd (Nat.card (secPsi a X J).ker) := by
  let f : (secPsi a X J).ker →* pPrimeCore 2 ↥(secY a X J) :=
    { toFun := fun j => ⟨⟨(j.1 : A), J_le_secY a X J j.1.2⟩, (secPsi_eq_one_iff j.1).mp j.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective f := by
    intro j₁ j₂ hj
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t => ((t : ↥(secY a X J)) : A)) (congrArg Subtype.val hj)
  exact Odd.of_dvd_nat N_odd (Subgroup.card_dvd_of_injective f hinj)

theorem secPsi_ker_eq_bot (h : SubHyp a p X J) (hN1 : pPrimeCoreOf 2 J = ⊥) :
    (secPsi a X J).ker = ⊥ := by
  have hbot : pPrimeCore 2 ↥J = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp hN1
  have hle := SubAbs.le_pPrimeCore_of_odd (G := ↥J) (secPsi a X J).ker (secPsi_ker_odd h)
  rw [eq_bot_iff]
  exact hle.trans hbot.le

theorem secPsi_ker_eq (h : SubHyp a p X J) : (secPsi a X J).ker = pPrimeCore 2 ↥J := by
  apply le_antisymm (SubAbs.le_pPrimeCore_of_odd (G := ↥J) _ (secPsi_ker_odd h))
  intro m hm
  have hmem : ((m : ↥J) : A) ∈ pPrimeCoreOf 2 J := ⟨m, hm, rfl⟩
  obtain ⟨hmY, hmN⟩ := pPrimeCoreOf_le_N h hmem
  exact (secPsi_eq_one_iff m).mpr hmN

@[expose] noncomputable def secPsiEquiv (h : SubHyp a p X J) (hN1 : pPrimeCoreOf 2 J = ⊥) :
    ↥J ≃* ↥(secJ a X J) :=
  MulEquiv.ofBijective (secPsi a X J)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (secPsi_ker_eq_bot h hN1), secPsi_surjective⟩

end Fin

theorem secPsi_map_X (hXJ : X ≤ J) :
    ((X.subgroupOf J).map (secPsi a X J)).map (secJ a X J).subtype = secX a X J := by
  ext b
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact mem_secX_iff.mpr ⟨x, hx, rfl⟩
  · intro hb
    obtain ⟨x, hx, rfl⟩ := mem_secX_iff.mp hb
    exact ⟨secPsi a X J ⟨x, hXJ hx⟩, ⟨⟨x, hXJ hx⟩, hx, rfl⟩, rfl⟩

theorem card_X_eq_secX (hXJ : X ≤ J) (hker : (secPsi a X J).ker = ⊥) :
    Nat.card ↥X = Nat.card ↥(secX a X J) := by
  have hinj := (MonoidHom.ker_eq_bot_iff _).mp hker
  have h1 : Nat.card ↥X = Nat.card ↥(X.subgroupOf J) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXJ).toEquiv).symm
  have h2 : Nat.card ↥((X.subgroupOf J).map (secPsi a X J)) = Nat.card ↥(X.subgroupOf J) :=
    Subgroup.card_map_of_injective hinj
  have h3 : Nat.card ↥(((X.subgroupOf J).map (secPsi a X J)).map (secJ a X J).subtype) =
      Nat.card ↥((X.subgroupOf J).map (secPsi a X J)) :=
    Subgroup.card_map_of_injective (secJ a X J).subtype_injective
  rw [secPsi_map_X hXJ] at h3
  rw [h1, ← h2, h3]


@[expose] def secChi (a : A) (X J : Subgroup A) : ↥X →* ↥(secX a X J) where
  toFun x := ⟨secMk a X J x (X_le_secY a X J x.2), secMk_mem_secX x.2⟩
  map_one' := Subtype.ext secMk_one
  map_mul' x₁ x₂ := Subtype.ext (secMk_mul (X_le_secY a X J x₁.2) (X_le_secY a X J x₂.2))

theorem secChi_surjective : Function.Surjective (secChi a X J) := by
  intro b
  obtain ⟨x, hx, hb⟩ := mem_secX_iff.mp b.2
  exact ⟨⟨x, hx⟩, Subtype.ext hb.symm⟩

theorem secChi_injective [Finite A] (h : SubHyp a p X J) (hXC : X ⊓ centralizer (J : Set A) = ⊥) :
    Function.Injective (secChi a X J) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : secMk a X J x (X_le_secY a X J x.2) = 1 := congrArg Subtype.val hx
  have h2 : (x : A) ∈ centralizer (J : Set A) := (secB_X_ker h x.2).mp h1
  have h3 : (x : A) ∈ X ⊓ centralizer (J : Set A) := ⟨x.2, h2⟩
  rw [hXC] at h3
  exact Subtype.ext (Subgroup.mem_bot.mp h3)

theorem card_X_eq_secX_of_chi [Finite A] (h : SubHyp a p X J) (hXC : X ⊓ centralizer (J : Set A) = ⊥) :
    Nat.card ↥X = Nat.card ↥(secX a X J) :=
  Nat.card_congr (Equiv.ofBijective (secChi a X J) ⟨secChi_injective h hXC, secChi_surjective⟩)

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
