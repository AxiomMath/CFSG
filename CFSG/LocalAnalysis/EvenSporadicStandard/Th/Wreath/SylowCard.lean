module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.EInvariant
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowBoundsCount
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Aa

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

@[expose]
noncomputable def ThLocalIn.conjAut (L A : Subgroup G) (n : ↥(normInL L A)) : MulAut ↥A where
  toFun a := ⟨(n : G) * (a : G) * (n : G)⁻¹, n.2.2 a a.2⟩
  invFun a := ⟨(n : G)⁻¹ * (a : G) * (n : G), by
    simpa using ((normInL L A).inv_mem n.2).2 a a.2⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose]
noncomputable def ThLocalIn.conjHom (L A : Subgroup G) : ↥(normInL L A) →* MulAut ↥A where
  toFun := ThLocalIn.conjAut L A
  map_one' := MulEquiv.ext fun a => Subtype.ext (by simp [ThLocalIn.conjAut])
  map_mul' n m := MulEquiv.ext fun a => Subtype.ext (by simp [ThLocalIn.conjAut, mul_assoc])

theorem ThLocalIn.conjHom_apply (L A : Subgroup G) (n : ↥(normInL L A)) (a : ↥A) :
    ((ThLocalIn.conjHom L A n a : ↥A) : G) = (n : G) * (a : G) * (n : G)⁻¹ := rfl

private lemma card_mulAut_of_sixteen {A : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hsq : ∀ a ∈ A, a ^ 2 = 1) (hA16 : Nat.card A = 16) :
    Nat.card (MulAut ↥A) = 20160 := by
  have hpow : ∀ a : ↥A, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hsq (a : G) a.2)
  have hcomm' : ∀ a b : ↥A, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := ↥A) hcomm' hpow (n := 4) (by rw [hA16]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL (p := 2) e,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 4]
  decide

private theorem B_le_normInL (W : ThLocalIn L S A B z) : B ≤ normInL L A := by
  intro x hx
  refine mem_normInL.2 ⟨W.B_le hx, fun a ha => ?_⟩
  have hc := (W.mem_B_iff x (W.B_le hx)).1 hx a ha
  have hxa : x * a * x⁻¹ = a := by
    calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [hc]
      _ = a := by group
  rw [hxa]
  exact ha

theorem ThLocalIn.conjHom_surjective (W : ThLocalIn L S A B z) :
    Function.Surjective (ThLocalIn.conjHom L A) := by
  intro φ
  classical
  let f : G → G := fun a => if ha : a ∈ A then ((φ ⟨a, ha⟩ : ↥A) : G) else 1
  have hfA : ∀ a ∈ A, f a ∈ A := by
    intro a ha
    dsimp [f]
    rw [dif_pos ha]
    exact (φ ⟨a, ha⟩).2
  have hfmul : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b := by
    intro a ha b hb
    dsimp [f]
    rw [dif_pos (A.mul_mem ha hb), dif_pos ha, dif_pos hb]
    exact congrArg (fun x : ↥A => (x : G)) (φ.map_mul ⟨a, ha⟩ ⟨b, hb⟩)
  have hfinj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b := by
    intro a ha b hb hab
    dsimp [f] at hab
    rw [dif_pos ha, dif_pos hb] at hab
    exact congrArg (fun x : ↥A => (x : G)) (φ.injective (Subtype.ext hab))
  obtain ⟨l, hlL, hl⟩ := W.surj f hfA hfmul hfinj
  have hlA : ∀ a ∈ A, l * a * l⁻¹ ∈ A := fun a ha => by
    rw [hl a ha]
    exact hfA a ha
  have hlN : l ∈ normInL L A := mem_normInL.2 ⟨hlL, hlA⟩
  refine ⟨⟨l, hlN⟩, ?_⟩
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  rw [ThLocalIn.conjHom_apply, hl (a : G) a.2]
  simp [f, a.2]

theorem ThLocalIn.conjHom_ker (W : ThLocalIn L S A B z) :
    (ThLocalIn.conjHom L A).ker = B.subgroupOf (normInL L A) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine (W.mem_B_iff (x : G) x.2.1).2 fun a ha => ?_
    have hconj := congrArg (fun ψ : MulAut ↥A => ((ψ ⟨a, ha⟩ : ↥A) : G)) h
    rw [ThLocalIn.conjHom_apply] at hconj
    have hxa : (x : G) * a * (x : G)⁻¹ = a := by
      simpa [MulAut.one_apply] using hconj
    calc (x : G) * a = ((x : G) * a * (x : G)⁻¹) * (x : G) := by group
      _ = a * (x : G) := by rw [hxa]
  · intro hxB
    refine MulEquiv.ext fun a => Subtype.ext ?_
    have hc := (W.mem_B_iff (x : G) x.2.1).1 hxB a a.2
    rw [ThLocalIn.conjHom_apply, MulAut.one_apply]
    calc (x : G) * (a : G) * (x : G)⁻¹ = ((a : G) * (x : G)) * (x : G)⁻¹ := by rw [hc]
      _ = (a : G) := by group

theorem ThLocalIn.card_S (W : ThLocalIn L S A B z) : Nat.card S = 2 ^ 15 := by
  classical
  have hSleN : S ≤ normInL L A := fun s hs =>
    mem_normInL.2 ⟨W.S_le hs, fun x hx => W.conj_mem_A_of_mem_S hs hx⟩
  have hBleN : B ≤ normInL L A := B_le_normInL W
  let SN : Subgroup ↥(normInL L A) := S.subgroupOf (normInL L A)
  have hSNp : IsPGroup 2 SN := W.pgroup.comap_subtype
  let SNsyl : Sylow 2 ↥(normInL L A) :=
    ⟨SN, hSNp, by
      intro Q hQ hle
      refine le_antisymm (fun q hq => ?_) hle
      have hQL : Q.map (normInL L A).subtype ≤ L :=
        (Subgroup.map_subtype_le Q).trans (fun x hx => (mem_normInL.1 hx).1)
      have hSle : S ≤ Q.map (normInL L A).subtype := by
        intro s hs
        exact ⟨⟨s, hSleN hs⟩, hle hs, rfl⟩
      have hmax := W.maximal (Q.map (normInL L A).subtype) hQL
        (hQ.map (normInL L A).subtype) hSle
      exact hmax ⟨q, hq, rfl⟩⟩
  let ψ : ↥SN →* MulAut ↥A := (ThLocalIn.conjHom L A).domRestrict SN
  have hsurj : Function.Surjective (ThLocalIn.conjHom L A) :=
    ThLocalIn.conjHom_surjective W
  have hker : Nat.card ψ.ker = Nat.card B := by
    dsimp only [ψ]
    rw [MonoidHom.ker_domRestrict, ThLocalIn.conjHom_ker W]
    have hle : B.subgroupOf (normInL L A) ≤ S.subgroupOf (normInL L A) :=
      Subgroup.subgroupOf_mono (normInL L A) W.B_le_S
    calc
      Nat.card ((B.subgroupOf (normInL L A)).subgroupOf
          (S.subgroupOf (normInL L A)))
          = Nat.card (B.subgroupOf (normInL L A)) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      _ = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBleN).toEquiv
  have hfac : Nat.factorization 20160 2 = 6 := by
    have h6 : 6 ≤ Nat.factorization 20160 2 := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := 6) Nat.prime_two
        (by norm_num : 20160 ≠ 0)]
      norm_num
    have h7 : ¬ 7 ≤ Nat.factorization 20160 2 := by
      intro h
      have hdvd : 2 ^ 7 ∣ 20160 :=
        (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := 7) Nat.prime_two
          (by norm_num : 20160 ≠ 0)).mpr h
      exact (by norm_num : ¬ (2 ^ 7 ∣ 20160)) hdvd
    omega
  have hcardφ :
      Nat.card (SNsyl.mapSurjective hsurj : Subgroup (MulAut ↥A)) = 2 ^ 6 := by
    rw [Sylow.card_eq_multiplicity]
    rw [show Nat.card (MulAut ↥A) = 20160 from
      card_mulAut_of_sixteen W.A_comm W.A_sq W.A_card]
    rw [hfac]
  have hcoerange : (SNsyl.mapSurjective hsurj : Subgroup (MulAut ↥A)) = ψ.range := by
    dsimp only [ψ, SNsyl]
    simp only [Sylow.coe_mapSurjective, MonoidHom.domRestrict_range]
  have hrange : Nat.card ψ.range = 2 ^ 6 := by
    rw [← hcoerange]
    exact hcardφ
  have hcard : Nat.card SN = Nat.card ψ.ker * Nat.card ψ.range :=
    (Subgroup.card_ker_mul_card_range ψ).symm
  have hSN : Nat.card SN = 2 ^ 15 := by
    rw [hcard, hker, hrange, W.B_card]
    norm_num
  have hSNcard : Nat.card SN = Nat.card S := by
    simpa [SN] using Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleN).toEquiv
  rw [← hSNcard]
  exact hSN

theorem ThLocalIn.relIndex_B_S (W : ThLocalIn L S A B z) : B.relIndex S = 64 := by
  have h := Subgroup.relIndex_mul_card (H := B) (K := S)
  rw [inf_of_le_left W.B_le_S] at h
  have hS : Nat.card S = 64 * Nat.card B := by
    rw [ThLocalIn.card_S W, W.B_card]
    norm_num
  rw [hS] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

end CFSG.EvenSporadicStandard.ThStd
