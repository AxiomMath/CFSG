module

public import CFSG.GH74.Generic.BProg.B3.S3Rk1Four
public import CFSG.GH74.Generic.BProg.B2.FixFourS3
public import CFSG.GH74.Generic.BProg.B2.Thm2Comp
public import CFSG.GH74.Generic.BProg.B1.PilotS1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped Pointwise

namespace S3Rk2Conj

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_le_sup {O B B' : Subgroup G} (hB'O : B' ≤ normalizer (O : Set G))
    (hOodd : Odd (Nat.card O)) (hB2 : IsPGroup 2 B) (hB'2 : IsPGroup 2 B')
    (hcard : Nat.card B = Nat.card B') (hle : B ≤ B' ⊔ O) :
    ∃ h ∈ B' ⊔ O, B.map (MulAut.conj h).toMonoidHom = B' := by
  classical
  set Y : Subgroup G := B' ⊔ O with hY
  have hOY : O ≤ Y := le_sup_right
  have hBY : B' ≤ Y := le_sup_left
  have hYN : Y ≤ normalizer (O : Set G) := sup_le hB'O Subgroup.le_normalizer
  let B'' : Subgroup Y := B'.subgroupOf Y
  let O' : Subgroup Y := O.subgroupOf Y
  let Q' : Subgroup Y := B.subgroupOf Y
  have hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).2 hYN
  have hO'odd : Odd (Nat.card O') := by
    rw [show Nat.card O' = Nat.card O from S3Rk1Four.card_subgroupOf_of_le hOY]
    exact hOodd
  have hB''2 : IsPGroup 2 B'' := hB'2.comap_subtype
  have hQ'2 : IsPGroup 2 Q' := hB2.comap_subtype
  have hsup : B'' ⊔ O' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBY hOY]
    exact Subgroup.subgroupOf_self _
  have hdec : ∀ y : Y, ∃ o ∈ O', ∃ b ∈ B'', y = o * b := by
    intro y
    have hy : y ∈ O' ⊔ B'' := by rw [sup_comm, hsup]; exact Subgroup.mem_top y
    rw [Subgroup.mem_sup_of_normal_left] at hy
    obtain ⟨o, ho, b, hb, rfl⟩ := hy
    exact ⟨o, ho, b, hb, rfl⟩
  have hmax : ∀ {P : Subgroup Y}, IsPGroup 2 P → B'' ≤ P → P = B'' := by
    intro P hP hle'
    apply le_antisymm _ hle'
    intro p hp
    obtain ⟨o, ho, b, hb, rfl⟩ := hdec p
    have hbP : b ∈ P := hle' hb
    have hoP : o ∈ P := by
      have := P.mul_mem hp (P.inv_mem hbP)
      simpa using this
    have := S3Rk1Four.eq_one_of_pGroup_of_odd hP hO'odd hoP ho
    rw [this, one_mul]
    exact hb
  let SB : Sylow 2 Y := ⟨B'', hB''2, fun {P} hP hle' => hmax hP hle'⟩
  obtain ⟨S, hQS⟩ := hQ'2.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq Y SB S
  have hScoe : (S : Subgroup Y) = MulAut.conj h • (B'' : Subgroup Y) := by
    rw [← hh, Sylow.coe_subgroup_smul]
  have hcardQ : Nat.card Q' = Nat.card B'' := by
    rw [show Nat.card Q' = Nat.card B from S3Rk1Four.card_subgroupOf_of_le hle,
      show Nat.card B'' = Nat.card B' from S3Rk1Four.card_subgroupOf_of_le hBY]
    exact hcard
  have hSc : Nat.card (S : Subgroup Y) = Nat.card B'' := by
    rw [hScoe]
    exact Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hQeq : Q' = (S : Subgroup Y) := by
    refine Subgroup.eq_of_le_of_card_ge hQS ?_
    rw [hSc, hcardQ]
  have hle2 : B.map (MulAut.conj (h : G)⁻¹).toMonoidHom ≤ B' := by
    rintro _ ⟨z, hz, rfl⟩
    have hzY : z ∈ Y := hle hz
    have hz' : (⟨z, hzY⟩ : Y) ∈ Q' := Subgroup.mem_subgroupOf.2 hz
    rw [hQeq, hScoe, Subgroup.mem_smul_pointwise_iff_exists] at hz'
    obtain ⟨s, hs, hsz⟩ := hz'
    have hs' : (s : G) ∈ B' := Subgroup.mem_subgroupOf.1 hs
    have hsz' : (h : G) * (s : G) * (h : G)⁻¹ = z := by
      have := congrArg Subtype.val hsz
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    have key : (h : G)⁻¹ * z * (h : G) = (s : G) := by
      rw [← hsz']
      group
    have hc : (MulAut.conj (h : G)⁻¹).toMonoidHom z = (s : G) := by
      simpa [MulAut.conj_apply] using key
    rw [hc]
    exact hs'
  refine ⟨(h : G)⁻¹, Y.inv_mem h.2, Subgroup.eq_of_le_of_card_ge hle2 ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hcard]

end Sylow

section Four

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_four {K E F : Subgroup G} (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hEK : E ≤ K) (hFK : F ≤ K) (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE4 : Nat.card ↥E = 4)
    (hFel : CFSG.IsElementaryAbelian 2 ↥F) (hF4 : Nat.card ↥F = 4) :
    ∃ k ∈ K, F.map (MulAut.conj k).toMonoidHom = E := by
  classical
  have hOodd : Odd (Nat.card (pPrimeCoreOf 2 K)) := TwoThin.card_pPrimeCoreOf_odd K
  set π : ↥K →* ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  set E' : Subgroup ↥K := E.subgroupOf K with hE'
  set F' : Subgroup ↥K := F.subgroupOf K with hF'
  have hE'el : CFSG.IsElementaryAbelian 2 ↥E' := CFSG.IsElementaryAbelian.subgroupOf hEK
  have hF'el : CFSG.IsElementaryAbelian 2 ↥F' := CFSG.IsElementaryAbelian.subgroupOf hFK
  have hE'p : IsPGroup 2 ↥E' := CFSG.IsElementaryAbelian.isPGroup 2 ↥E'
  have hF'p : IsPGroup 2 ↥F' := CFSG.IsElementaryAbelian.isPGroup 2 ↥F'
  have hE'4 : Nat.card ↥E' = 4 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE4]
  have hF'4 : Nat.card ↥F' = 4 := by
    rw [hF', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFK).toEquiv, hF4]
  have hEtel : CFSG.IsElementaryAbelian 2 ↥(E'.map π) := CFSG.IsElementaryAbelian.map π
  have hFtel : CFSG.IsElementaryAbelian 2 ↥(F'.map π) := CFSG.IsElementaryAbelian.map π
  have hEt4 : Nat.card ↥(E'.map π) = 4 := by
    rw [B1.PilotS1.card_map_eq_of_inj π E' (B2.Thm2Comp.eq_one_of_isPGroup hE'p), hE'4]
  have hFt4 : Nat.card ↥(F'.map π) = 4 := by
    rw [B1.PilotS1.card_map_eq_of_inj π F' (B2.Thm2Comp.eq_one_of_isPGroup hF'p), hF'4]
  obtain ⟨gt, hgt⟩ := B2.FixFourS3.fourConj_shape3 _ h3 (F'.map π) (E'.map π) hFtel hFt4 hEtel hEt4
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) gt
  have hle : F.map (MulAut.conj (g' : G)).toMonoidHom ≤ E ⊔ pPrimeCoreOf 2 K := by
    rintro _ ⟨f, hf, rfl⟩
    have hfF' : (⟨f, hFK hf⟩ : ↥K) ∈ F' := Subgroup.mem_subgroupOf.2 hf
    have hmem : π (g' * ⟨f, hFK hf⟩ * g'⁻¹) ∈ E'.map π := by
      rw [hgt]
      refine ⟨π ⟨f, hFK hf⟩, ⟨_, hfF', rfl⟩, ?_⟩
      simp [MulAut.conj_apply, hπ]
    obtain ⟨e, he, hπe⟩ := hmem
    have h1 : e⁻¹ * (g' * ⟨f, hFK hf⟩ * g'⁻¹) ∈ pPrimeCore 2 ↥K :=
      QuotientGroup.eq.1 hπe
    have h2 : (e : G)⁻¹ * (g' * ⟨f, hFK hf⟩ * g'⁻¹ : ↥K) ∈ pPrimeCoreOf 2 K := ⟨_, h1, rfl⟩
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.1 he
    have h3' : ((g' * ⟨f, hFK hf⟩ * g'⁻¹ : ↥K) : G) =
        (e : G) * ((e : G)⁻¹ * (g' * ⟨f, hFK hf⟩ * g'⁻¹ : ↥K)) := by group
    have h4 : (MulAut.conj (g' : G)).toMonoidHom f = ((g' * ⟨f, hFK hf⟩ * g'⁻¹ : ↥K) : G) := by
      simp [MulAut.conj_apply]
    rw [h4, h3']
    exact mul_mem (Subgroup.mem_sup_left heE) (Subgroup.mem_sup_right h2)
  have hEN : E ≤ normalizer (pPrimeCoreOf 2 K : Set G) := fun b hb =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hEK hb))
  have hFg2 : IsPGroup 2 ↥(F.map (MulAut.conj (g' : G)).toMonoidHom) :=
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥F).map _
  have hcard : Nat.card ↥(F.map (MulAut.conj (g' : G)).toMonoidHom) = Nat.card ↥E := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (g' : G)).injective, hF4, hE4]
  obtain ⟨h, hh, hmap⟩ := exists_conj_of_le_sup hEN hOodd hFg2
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥E) hcard hle
  have hOK : pPrimeCoreOf 2 K ≤ K := Subgroup.map_subtype_le _
  have hhK : h ∈ K := sup_le hEK hOK hh
  refine ⟨h * (g' : G), mul_mem hhK g'.2, ?_⟩
  rw [← hmap, Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

end Four

end S3Rk2Conj

end CFSG.GH74.Generic.BProg.B3
