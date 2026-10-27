module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.DihedralPerm
public import Mathlib.GroupTheory.Nilpotent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

variable {X : Type*} [Group X]

abbrev altCentralizer {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) : Subgroup X :=
  (altSubgroup.comap e.toMonoidHom).map (centralizer ({u} : Set X)).subtype

abbrev dihedralCentralizer {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) : Subgroup X :=
  (dihedralSubgroup.comap e.toMonoidHom).map (centralizer ({u} : Set X)).subtype

structure SwapData {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    (B S : Subgroup X) (τ : X) : Prop where
  card_B : Nat.card ↥B = 2 ^ 6
  le_centralizer : B ≤ centralizer ({u} : Set X)
  le_S : B ≤ S
  card_S : Nat.card ↥S = 2 ^ 7
  mem_S : τ ∈ S
  normal : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B
  not_commute : τ * u ≠ u * τ
  mem_B : u ∈ B
  dihedral_le : dihedralCentralizer e ≤ B
  inf_eq_bot :
    dihedralCentralizer e ⊓ (dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom = ⊥
  sup_eq : dihedralCentralizer e ⊔ (dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom = B

theorem mk_eq_symm_r_two {u : X} (hu1 : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    (⟨u, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({u} : Set X))) =
      e.symm (DihedralGroup.r 2, 1) := by
  have hc : (⟨u, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({u} : Set X))) ∈
      Subgroup.center ↥(centralizer ({u} : Set X)) := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.1 c.2)
  rcases (mem_center_iff_of_mulEquiv_dihedral_prod_perm e _).1 hc with h | h
  · exact absurd (congrArg Subtype.val h) hu1
  · exact h

private theorem card_centralizer_960 {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    Nat.card ↥(centralizer ({u} : Set X)) = 960 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

private theorem factorization_960_two : Nat.factorization 960 2 = 6 := by
  have hcop : Nat.Coprime (2 ^ 6) 15 := by norm_num
  have h960 : (960 : ℕ) = 2 ^ 6 * 15 := by norm_num
  rw [h960, Nat.factorization_mul_apply_of_coprime hcop,
    Nat.factorization_pow_self (p := 2) (n := 6) Nat.prime_two]
  have h15 : (15 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h15, Nat.add_zero]

private theorem center_dihedral_four (x : DihedralGroup 4) :
    x ∈ Subgroup.center (DihedralGroup 4) ↔ x = 1 ∨ x = DihedralGroup.r 2 := by
  revert x; decide +kernel

private noncomputable def dihedralSubgroupIso :
    ↥dihedralSubgroup ≃* DihedralGroup 4 where
  toFun x := x.1.1
  invFun d := ⟨(d, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩⟩
  left_inv x := by
    have hx2 : x.1.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp x.2).2
    exact Subtype.ext (Prod.ext rfl hx2.symm)
  right_inv d := rfl
  map_mul' x y := rfl

private noncomputable def dihedralCentralizerIso {u : X}
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    ↥(dihedralCentralizer e) ≃* DihedralGroup 4 where
  toFun z := (e ⟨z.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) z.2⟩).1
  invFun d := ⟨(e.symm (d, 1)).1, by
    refine Subgroup.mem_map.mpr ⟨e.symm (d, 1), ?_, rfl⟩
    rw [Subgroup.mem_comap]
    change e (e.symm (d, 1)) ∈ dihedralSubgroup
    rw [MulEquiv.apply_symm_apply]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩⟩
  left_inv z := by
    apply Subtype.ext
    have hzD : (⟨z.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) z.2⟩ :
        ↥(centralizer ({u} : Set X))) ∈ dihedralSubgroup.comap e.toMonoidHom := by
      obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp z.2
      rw [Subgroup.mem_comap] at hc
      rw [Subgroup.mem_comap]
      have hcz : (⟨z.1, Subgroup.map_subtype_le
          (dihedralSubgroup.comap e.toMonoidHom) z.2⟩ :
          ↥(centralizer ({u} : Set X))) = c := Subtype.ext hceq.symm
      rw [hcz]
      exact hc
    have h2 : (e ⟨z.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) z.2⟩).2 = 1 := by
      have := hzD
      rw [Subgroup.mem_comap] at this
      exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp this).2
    show (e.symm ((e ⟨z.1, _⟩).1, 1)).1 = z.1
    rw [show ((e ⟨z.1, _⟩).1, (1 : Equiv.Perm (Fin 5))) = e ⟨z.1, _⟩ from
      Prod.ext rfl h2.symm]
    rw [MulEquiv.symm_apply_apply]
  right_inv d := by
    show (e ⟨(e.symm (d, 1)).1, _⟩).1 = d
    have h : (⟨(e.symm (d, 1)).1, _⟩ : ↥(centralizer ({u} : Set X))) = e.symm (d, 1) :=
      Subtype.ext rfl
    rw [h, MulEquiv.apply_symm_apply]
  map_mul' z w := by
    have h : (⟨(z * w).1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom)
          (z * w).2⟩ : ↥(centralizer ({u} : Set X))) =
        ⟨z.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) z.2⟩ *
        ⟨w.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) w.2⟩ :=
      Subtype.ext rfl
    calc (e ⟨(z * w).1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom)
            (z * w).2⟩).1
        = (e (⟨z.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) z.2⟩ *
            ⟨w.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) w.2⟩)).1 := by
          rw [h]
      _ = (e ⟨z.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) z.2⟩ *
            e ⟨w.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) w.2⟩).1 := by
          rw [map_mul]
      _ = (e ⟨z.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) z.2⟩).1 *
            (e ⟨w.1, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) w.2⟩).1 :=
          rfl

private theorem dihedralCentralizerIso_u {u : X} (hu1 : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    (huD : u ∈ dihedralCentralizer e) :
    dihedralCentralizerIso e ⟨u, huD⟩ = DihedralGroup.r 2 := by
  have h : (⟨u, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) huD⟩ :
      ↥(centralizer ({u} : Set X))) = e.symm (DihedralGroup.r 2, 1) :=
    mk_eq_symm_r_two hu1 e
  show (e ⟨u, Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) huD⟩).1 = _
  rw [h, MulEquiv.apply_symm_apply]

private theorem mem_center_dihedralCentralizer {u : X} (hu1 : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    (huD : u ∈ dihedralCentralizer e) (z : ↥(dihedralCentralizer e)) :
    z ∈ Subgroup.center ↥(dihedralCentralizer e) ↔ (z : X) = 1 ∨ (z : X) = u := by
  have hΦu : dihedralCentralizerIso e ⟨u, huD⟩ = DihedralGroup.r 2 :=
    dihedralCentralizerIso_u hu1 e huD
  constructor
  · intro hz
    have hz' : dihedralCentralizerIso e z ∈ Subgroup.center (DihedralGroup 4) := by
      rw [← Subgroup.map_center_eq (dihedralCentralizerIso e)]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    rcases (center_dihedral_four _).mp hz' with h | h
    · left
      have h' : z = 1 := (dihedralCentralizerIso e).injective (by rw [h, map_one])
      exact congrArg Subtype.val h'
    · right
      have h' : z = ⟨u, huD⟩ := by
        apply (dihedralCentralizerIso e).injective
        rw [h, hΦu]
      exact congrArg Subtype.val h'
  · rintro (h | h)
    · rw [show z = 1 from Subtype.ext h]
      exact Subgroup.one_mem _
    · rw [show z = ⟨u, huD⟩ from Subtype.ext h, Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (mem_centralizer_singleton_iff.mp
        (Subgroup.map_subtype_le (dihedralSubgroup.comap e.toMonoidHom) w.2))

theorem exists_swapData [Finite X] {u : X} (hu1 : u ≠ 1)
    (e : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    (P : Sylow 2 X) (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7) :
    ∃ (B S : Subgroup X) (τ : X), SwapData e B S τ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardC : Nat.card ↥(centralizer ({u} : Set X)) = 960 := card_centralizer_960 e
  let Q : Sylow 2 ↥(centralizer ({u} : Set X)) := default
  let B : Subgroup X := (Q : Subgroup ↥(centralizer ({u} : Set X))).map
    (centralizer ({u} : Set X)).subtype
  have hcardQ : Nat.card ↥(Q : Subgroup ↥(centralizer ({u} : Set X))) = 2 ^ 6 := by
    rw [Sylow.card_eq_multiplicity Q, hcardC, factorization_960_two]
  have hcardB : Nat.card ↥B = 2 ^ 6 := by
    show Nat.card ↥((Q : Subgroup ↥(centralizer ({u} : Set X))).map
      (centralizer ({u} : Set X)).subtype) = 2 ^ 6
    rw [Subgroup.card_map_of_injective (centralizer ({u} : Set X)).subtype_injective]
    exact hcardQ
  have hBC : B ≤ centralizer ({u} : Set X) :=
    Subgroup.map_subtype_le (Q : Subgroup ↥(centralizer ({u} : Set X)))
  have hB2 : IsPGroup 2 B := IsPGroup.iff_card.mpr ⟨6, hcardB⟩
  obtain ⟨S, hBS⟩ := IsPGroup.exists_le_sylow hB2
  have hcardS : Nat.card ↥(S : Subgroup X) = 2 ^ 7 := by
    rw [Sylow.card_eq_multiplicity S, ← Sylow.card_eq_multiplicity P, hP]
  have hidx : (B.subgroupOf (S : Subgroup X)).index = 2 := by
    have hmul := (B.subgroupOf (S : Subgroup X)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv, hcardB, hcardS] at hmul
    norm_num at hmul
    omega
  have hnormalBS : (B.subgroupOf (S : Subgroup X)).Normal :=
    Subgroup.normal_of_index_eq_two hidx
  have hnormalField : ∀ s ∈ (S : Subgroup X), ∀ b ∈ B, s * b * s⁻¹ ∈ B :=
    fun s hs b hb => (Subgroup.normal_subgroupOf_iff hBS).mp hnormalBS b s hb hs
  have hBneS : B ≠ (S : Subgroup X) := by
    intro h
    have h1 : Nat.card ↥(S : Subgroup X) = 2 ^ 6 := h ▸ hcardB
    rw [hcardS] at h1
    norm_num at h1
  have hBSlt : B < (S : Subgroup X) := lt_of_le_of_ne hBS hBneS
  obtain ⟨τ, hτS, hτB⟩ := IsConcreteLE.exists_of_lt hBSlt
  have huB : u ∈ B := by
    let uC : ↥(centralizer ({u} : Set X)) := ⟨u, mem_centralizer_singleton_iff.mpr rfl⟩
    have huC2 : uC ^ 2 = 1 := by
      have h : uC = e.symm (DihedralGroup.r 2, 1) := mk_eq_symm_r_two hu1 e
      rw [h, ← map_pow,
        show (DihedralGroup.r 2, (1 : Equiv.Perm (Fin 5))) ^ 2 = 1 by decide +kernel, map_one]
    have huCcenter : uC ∈ Subgroup.center ↥(centralizer ({u} : Set X)) := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (mem_centralizer_singleton_iff.1 c.2)
    haveI : (Subgroup.zpowers uC).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr huCcenter)
    have hzp2 : IsPGroup 2 (Subgroup.zpowers uC) := by
      apply IsPGroup.of_card_dvd_pow (n := 1)
      rw [pow_one, Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr huC2
    have hle : Subgroup.zpowers uC ≤ (Q : Subgroup ↥(centralizer ({u} : Set X))) :=
      IsPGroup.le_sylow_of_normal hzp2 Q
    show u ∈ B
    rw [show B = (Q : Subgroup ↥(centralizer ({u} : Set X))).map
        (centralizer ({u} : Set X)).subtype from rfl]
    exact Subgroup.mem_map.mpr ⟨uC, hle (Subgroup.mem_zpowers uC), rfl⟩
  have hu_central : ∀ c ∈ centralizer ({u} : Set X), u * c = c * u :=
    fun c hc => (mem_centralizer_singleton_iff.mp hc).symm
  have hDC2 : IsPGroup 2 (dihedralSubgroup.comap e.toMonoidHom) :=
    IsPGroup.of_card (n := 3) (by rw [card_comap_dihedralSubgroup e]; norm_num)
  have huD : u ∈ dihedralCentralizer e := by
    show u ∈ (dihedralSubgroup.comap e.toMonoidHom).map (centralizer ({u} : Set X)).subtype
    refine Subgroup.mem_map.mpr ⟨⟨u, mem_centralizer_singleton_iff.mpr rfl⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h := mk_eq_symm_r_two hu1 e
    rw [h]
    change e (e.symm (DihedralGroup.r 2, 1)) ∈ dihedralSubgroup
    rw [MulEquiv.apply_symm_apply]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩
  have hDC_le_Q : dihedralSubgroup.comap e.toMonoidHom ≤
      (Q : Subgroup ↥(centralizer ({u} : Set X))) :=
    IsPGroup.le_sylow_of_normal hDC2 Q
  have hD_le_B : dihedralCentralizer e ≤ B := Subgroup.map_mono hDC_le_Q
  have hD2 : IsPGroup 2 (dihedralCentralizer e) := hDC2.map (centralizer ({u} : Set X)).subtype
  have hDC_normal : (dihedralSubgroup.comap e.toMonoidHom).Normal := inferInstance
  have hD_normal_B : B ≤ Subgroup.normalizer (dihedralCentralizer e : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb h hh
    obtain ⟨bC, hbC, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨hC, hhC, rfl⟩ := Subgroup.mem_map.mp hh
    have heq : (centralizer ({u} : Set X)).subtype bC * (centralizer ({u} : Set X)).subtype hC *
        ((centralizer ({u} : Set X)).subtype bC)⁻¹ =
        (centralizer ({u} : Set X)).subtype (bC * hC * bC⁻¹) := by
      rw [← map_mul, ← map_inv, ← map_mul]
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨bC * hC * bC⁻¹, hDC_normal.conj_mem hC hhC bC, rfl⟩
  let Dτ : Subgroup X := (dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom
  have hDτ_le_B : Dτ ≤ B := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    change τ * d * τ⁻¹ ∈ B
    exact hnormalField τ hτS d (hD_le_B hd)
  have hDτ_normal_B : B ≤ Subgroup.normalizer (Dτ : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    change b * (τ * d * τ⁻¹) * b⁻¹ ∈ Dτ
    have hb' : τ⁻¹ * b * τ ∈ B := by
      simpa using hnormalField τ⁻¹ ((S : Subgroup X).inv_mem hτS) b hb
    have hd' : (τ⁻¹ * b * τ) * d * (τ⁻¹ * b * τ)⁻¹ ∈ dihedralCentralizer e :=
      (Subgroup.le_normalizer_iff.mp hD_normal_B) (τ⁻¹ * b * τ) hb' d hd
    refine Subgroup.mem_map.mpr ⟨(τ⁻¹ * b * τ) * d * (τ⁻¹ * b * τ)⁻¹, hd', ?_⟩
    show τ * ((τ⁻¹ * b * τ) * d * (τ⁻¹ * b * τ)⁻¹) * τ⁻¹ = b * (τ * d * τ⁻¹) * b⁻¹
    group
  have hnotcomm : τ * u ≠ u * τ := by
    intro hcomm
    have hτC : τ ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr hcomm
    let τC : ↥(centralizer ({u} : Set X)) := ⟨τ, hτC⟩
    have hB_eq : B = (Q : Subgroup ↥(centralizer ({u} : Set X))).map
        (centralizer ({u} : Set X)).subtype := rfl
    have hQcomap : (Q : Subgroup ↥(centralizer ({u} : Set X))) =
        B.comap (centralizer ({u} : Set X)).subtype := by
      rw [hB_eq]
      exact (Subgroup.comap_map_eq_self_of_injective
        (centralizer ({u} : Set X)).subtype_injective (Q : Subgroup _)).symm
    have hconjQ : ∀ q ∈ (Q : Subgroup ↥(centralizer ({u} : Set X))),
        τC * q * τC⁻¹ ∈ (Q : Subgroup ↥(centralizer ({u} : Set X))) := by
      intro q hq
      rw [hQcomap, Subgroup.mem_comap] at hq ⊢
      show τ * (q : X) * τ⁻¹ ∈ B
      exact hnormalField τ hτS (q : X) hq
    have hconjQinv : ∀ q ∈ (Q : Subgroup ↥(centralizer ({u} : Set X))),
        τC⁻¹ * q * τC ∈ (Q : Subgroup ↥(centralizer ({u} : Set X))) := by
      intro q hq
      rw [hQcomap, Subgroup.mem_comap] at hq ⊢
      show τ⁻¹ * (q : X) * τ ∈ B
      simpa using hnormalField τ⁻¹ ((S : Subgroup X).inv_mem hτS) (q : X) hq
    have hnormQ : τC ∈ Subgroup.normalizer
        ((Q : Subgroup ↥(centralizer ({u} : Set X))) : Set ↥(centralizer ({u} : Set X))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro q
      exact ⟨fun hq => hconjQ q hq, fun hq => by
        have := hconjQinv (τC * q * τC⁻¹) hq
        convert this using 1
        group⟩
    have hzpτ : IsPGroup 2 (Subgroup.zpowers τ) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hτS)
    have hmap : (Subgroup.zpowers τC).map (centralizer ({u} : Set X)).subtype =
        Subgroup.zpowers τ := by
      rw [MonoidHom.map_zpowers]
      rfl
    have hzpτC : IsPGroup 2 (Subgroup.zpowers τC) :=
      hzpτ.of_equiv ((Subgroup.equivMapOfInjective (Subgroup.zpowers τC)
        (centralizer ({u} : Set X)).subtype
        (centralizer ({u} : Set X)).subtype_injective).trans (MulEquiv.subgroupCongr hmap)).symm
    have hsup2 : IsPGroup 2 (((Q : Subgroup ↥(centralizer ({u} : Set X))) ⊔
        Subgroup.zpowers τC : Subgroup ↥(centralizer ({u} : Set X)))) :=
      IsPGroup.to_sup_of_normal_left' Q.isPGroup' hzpτC (Subgroup.zpowers_le.mpr hnormQ)
    have hτC_notin : τC ∉ (Q : Subgroup ↥(centralizer ({u} : Set X))) := by
      intro h
      apply hτB
      rw [hB_eq]
      exact Subgroup.mem_map.mpr ⟨τC, h, rfl⟩
    have hEq : ((Q : Subgroup ↥(centralizer ({u} : Set X))) ⊔ Subgroup.zpowers τC) = Q :=
      Q.is_maximal' hsup2 le_sup_left
    have : τC ∈ (Q : Subgroup ↥(centralizer ({u} : Set X))) := by
      rw [← hEq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τC)
    exact hτC_notin this
  have hD_le_normDτ : dihedralCentralizer e ≤ Subgroup.normalizer (Dτ : Set X) :=
    le_trans hD_le_B hDτ_normal_B
  have hinf : dihedralCentralizer e ⊓ Dτ = ⊥ := by
    by_contra hne
    have hNne : Dτ.subgroupOf (dihedralCentralizer e) ≠ ⊥ := by
      intro hbot
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.1⟩ : ↥(dihedralCentralizer e)) ∈
          Dτ.subgroupOf (dihedralCentralizer e) := hx.2
      rw [hbot, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
    haveI : (Dτ.subgroupOf (dihedralCentralizer e)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hD_le_normDτ
    haveI : Group.IsNilpotent ↥(dihedralCentralizer e) := hD2.isNilpotent
    obtain ⟨y, hy_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hNne)
    have hyDτ : (y : X) ∈ Dτ := by
      have h := (Subgroup.mem_inf.mp y.2).1
      rwa [Subgroup.mem_subgroupOf] at h
    have hycenter : y.val ∈ Subgroup.center ↥(dihedralCentralizer e) :=
      (Subgroup.mem_inf.mp y.2).2
    have hyu : (y : X) = u := by
      rcases (mem_center_dihedralCentralizer hu1 e huD y.val).mp hycenter with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hy_ne
      · exact h
    have huDτ : u ∈ Dτ := by rw [← hyu]; exact hyDτ
    obtain ⟨d, hdD, hd_eq⟩ := Subgroup.mem_map.mp huDτ
    change τ * d * τ⁻¹ = u at hd_eq
    have hd_central : (⟨d, hdD⟩ : ↥(dihedralCentralizer e)) ∈
        Subgroup.center ↥(dihedralCentralizer e) := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      show (x : X) * d = d * (x : X)
      have hxτDτ : τ * (x : X) * τ⁻¹ ∈ Dτ :=
        Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
      have hcomm_u : (τ * d * τ⁻¹) * (τ * (x : X) * τ⁻¹) =
          (τ * (x : X) * τ⁻¹) * (τ * d * τ⁻¹) := by
        rw [hd_eq]
        exact hu_central (τ * (x : X) * τ⁻¹) (hBC (hDτ_le_B hxτDτ))
      calc (x : X) * d = τ⁻¹ * ((τ * (x : X) * τ⁻¹) * (τ * d * τ⁻¹)) * τ := by group
        _ = τ⁻¹ * ((τ * d * τ⁻¹) * (τ * (x : X) * τ⁻¹)) * τ := by rw [← hcomm_u]
        _ = d * (x : X) := by group
    rcases (mem_center_dihedralCentralizer hu1 e huD ⟨d, hdD⟩).mp hd_central with hd1 | hdu
    · have hd1' : d = 1 := hd1
      apply hu1
      rw [← hd_eq, hd1', mul_one, mul_inv_cancel]
    · have hdu' : d = u := hdu
      apply hnotcomm
      rw [hdu'] at hd_eq
      calc τ * u = (τ * u * τ⁻¹) * τ := by group
        _ = u * τ := by rw [hd_eq]
  have hDτ_le_normD : Dτ ≤ Subgroup.normalizer (dihedralCentralizer e : Set X) :=
    le_trans hDτ_le_B hD_normal_B
  have hcardD : Nat.card ↥(dihedralCentralizer e) = 8 := by
    show Nat.card ↥((dihedralSubgroup.comap e.toMonoidHom).map
      (centralizer ({u} : Set X)).subtype) = 8
    rw [Subgroup.card_map_of_injective (centralizer ({u} : Set X)).subtype_injective,
      card_comap_dihedralSubgroup e]
  have hcardDτ : Nat.card ↥Dτ = 8 := by
    show Nat.card ↥((dihedralCentralizer e).map (MulAut.conj τ).toMonoidHom) = 8
    rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective, hcardD]
  have hcard_sup : Nat.card ↥(dihedralCentralizer e ⊔ Dτ) = 64 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (dihedralCentralizer e) Dτ hDτ_le_normD (disjoint_iff.mpr hinf), hcardD, hcardDτ]
  have hsup_eq : dihedralCentralizer e ⊔ Dτ = B := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hD_le_B hDτ_le_B)
    rw [hcardB, hcard_sup]
    norm_num
  exact ⟨B, (S : Subgroup X), τ, {
    card_B := hcardB
    le_centralizer := hBC
    le_S := hBS
    card_S := hcardS
    mem_S := hτS
    normal := hnormalField
    not_commute := hnotcomm
    mem_B := huB
    dihedral_le := hD_le_B
    inf_eq_bot := hinf
    sup_eq := hsup_eq }⟩

end CFSG.EvenSporadicStandard.TwoHS.GH312
