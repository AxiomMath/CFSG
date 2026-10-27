module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal5
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

variable {h} {i : Fin r} {P : Subgroup H} (hP : h.IsSelected i P)

include hP

theorem IsSelected.odd_mem_Dat {g : MulAut ↥W} (hg : g ∈ P.map h.rho) (hodd : Odd (orderOf g)) :
    g ∈ h.Dat i := by
  let _ := h.cg
  obtain ⟨d, hd, b, hb, rfl⟩ := Layer.mem_sup_mul (h.T0_le_normalizer_Dat i) (hP.map_rho_le hg)
  have key : ∀ n : ℕ, ∃ d' ∈ h.Dat i, (d * b) ^ n = d' * b ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, (h.Dat i).one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨d', hd', hn⟩ := ih
      have hconj : b ^ n * d * (b ^ n)⁻¹ ∈ h.Dat i :=
        (Subgroup.mem_normalizer_iff.mp (h.T0_le_normalizer_Dat i (h.T0.pow_mem hb n)) d).mp hd
      refine ⟨d' * (b ^ n * d * (b ^ n)⁻¹), (h.Dat i).mul_mem hd' hconj, ?_⟩
      rw [pow_succ, hn]
      group
  obtain ⟨k, hk⟩ := h.T0_sylow.2.1 ⟨b, hb⟩
  have hbk : b ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨d', hd', hn⟩ := key (2 ^ k)
  exact mem_of_odd_orderOf_of_pow_mem hodd (k := k) (by rw [hn, hbk, mul_one]; exact hd')

theorem IsSelected.map_rho_odd : (oddOrderSubgroup P).map h.rho = h.Dat i := by
  let _ := h.cg
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact hP.odd_mem_Dat ⟨x, hx.1, rfl⟩ (Odd.of_dvd_nat hx.2 (orderOf_map_dvd h.rho x))
  · obtain ⟨p, hp, hpD, x0, hx0, hx0ne⟩ := hP.exists_odd_acting
    exact (cubeAt_le_zpowers h.planeFamily hpD ⟨x0, hx0, hx0ne⟩).trans
      ((Subgroup.zpowers_le).mpr ⟨p, hp, rfl⟩)

theorem IsSelected.I_le_odd : I i ≤ oddOrderSubgroup P := by
  let _ := h.cg
  intro x hx
  have hxW : x ∈ W := h.I_le i hx
  obtain ⟨p, hp, hpD, x0, hx0, hx0ne⟩ := hP.exists_odd_acting
  obtain ⟨y, hy, hyd⟩ := exists_div_eq_of_cubeAt h.planeFamily hpD ⟨x0, hx0, hx0ne⟩
    (x := ⟨x, hxW⟩) hx
  have hxeq : x = p * ((y : ↥W) : H) * p⁻¹ * ((y : ↥W) : H)⁻¹ := by
    have := congrArg (fun a : ↥W => (a : H)) hyd
    simp only [h.rho_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this.symm
  have hyI : ((y : ↥W) : H) ∈ I i := hy
  have hyN : ((y : ↥W) : H) ∈ Subgroup.normalizer ((oddOrderSubgroup P : Subgroup H) : Set H) :=
    normalizer_le_normalizer_oddOrderSubgroup P (Subgroup.le_normalizer (hP.I_le_P i hyI))
  have h1 : ((y : ↥W) : H) * p⁻¹ * ((y : ↥W) : H)⁻¹ ∈ oddOrderSubgroup P :=
    (Subgroup.mem_normalizer_iff.mp hyN _).mp ((oddOrderSubgroup P).inv_mem hp)
  rw [hxeq]
  have : p * ((y : ↥W) : H) * p⁻¹ * ((y : ↥W) : H)⁻¹ =
      p * (((y : ↥W) : H) * p⁻¹ * ((y : ↥W) : H)⁻¹) := by group
  rw [this]
  exact (oddOrderSubgroup P).mul_mem hp h1

theorem IsSelected.blockQ_odd_eq (hK4 : Nat.card ↥(blockQ (oddOrderSubgroup P)) = 4) :
    blockQ (oddOrderSubgroup P) = I i := by
  have hIK := hP.I_le_odd
  have hnormal : ((I i).subgroupOf (oddOrderSubgroup P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIK).mpr fun k hk =>
      hP.le_normalizer_I i (oddOrderSubgroup_le P hk)
  have hI2 : IsPGroup 2 ↥(I i) := fun x =>
    ⟨1, Subtype.ext (by simpa using h.W_elem.2 _ (h.I_le i x.2))⟩
  have hle : I i ≤ blockQ (oddOrderSubgroup P) :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hIK hnormal hI2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hK4, h.I_card i])).symm

theorem IsSelected.conj {t : H} (ht : t ∈ R) :
    h.IsSelected (h.piH t i) (P.map (MulAut.conj t).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSn : t ∈ Subgroup.normalizer ((elemBaumannIn 2 R : Subgroup H) : Set H) :=
    le_normalizer_elemBaumannIn R ht
  have hSt : (elemBaumannIn 2 R).map (MulAut.conj t).toMonoidHom = elemBaumannIn 2 R :=
    GammaExtra.map_conj_eq_self_of_mem_normalizer hSn
  have hSt' : (elemBaumannIn 2 R).map (MulAut.conj t⁻¹).toMonoidHom = elemBaumannIn 2 R :=
    GammaExtra.map_conj_eq_self_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hSn)
  have hMt : M.map (MulAut.conj t).toMonoidHom = M :=
    GammaExtra.map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer (h.le_M ht))
  have hψφ : ∀ X : Subgroup H, (X.map (MulAut.conj t⁻¹).toMonoidHom).map
      (MulAut.conj t).toMonoidHom = X := by
    intro X
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨t⁻¹ * x * t, ⟨x, hx, by simp [mul_assoc]⟩,
        by simp [MulAut.conj_apply, mul_assoc]⟩
  have hφψ : ∀ X : Subgroup H, (X.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj t⁻¹).toMonoidHom = X := by
    intro X
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨t * x * t⁻¹, ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩,
        by simp [mul_assoc]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hSt]
    exact Subgroup.map_mono hP.S_le
  · calc P.map (MulAut.conj t).toMonoidHom
        ≤ (h.Yi i ⊔ elemBaumannIn 2 R).map (MulAut.conj t).toMonoidHom :=
          Subgroup.map_mono hP.P_le
      _ = (h.Yi i).map (MulAut.conj t).toMonoidHom ⊔
            (elemBaumannIn 2 R).map (MulAut.conj t).toMonoidHom := Subgroup.map_sup _ _ _
      _ ≤ h.Yi (h.piH t i) ⊔ elemBaumannIn 2 R := by
          rw [hSt]
          refine sup_le_sup_right ?_ _
          rintro _ ⟨y, hy, rfl⟩
          exact h.Yi_conj hy
  · intro hle
    apply hP.not_le_M
    intro x hx
    have h1 : t * x * t⁻¹ ∈ M := hle ⟨x, hx, rfl⟩
    have : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [this]
    exact M.mul_mem (M.mul_mem (M.inv_mem (h.le_M ht)) h1) (h.le_M ht)
  · intro Y hSY hYP
    have hY'P : Y.map (MulAut.conj t⁻¹).toMonoidHom ≤ P := by
      have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hYP.le
      rwa [hφψ] at this
    have hSY' : elemBaumannIn 2 R ≤ Y.map (MulAut.conj t⁻¹).toMonoidHom := by
      have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hSY
      rwa [hSt'] at this
    have hY'ne : Y.map (MulAut.conj t⁻¹).toMonoidHom ≠ P := by
      intro heq
      apply hYP.ne
      rw [← hψφ Y, heq]
    have := hP.minimal _ hSY' (lt_of_le_of_ne hY'P hY'ne)
    rw [← hψφ Y, ← hMt]
    exact Subgroup.map_mono this

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
