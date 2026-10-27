module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.SimpleSection

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec14.Main148 CFSG.RankThree.PartTwo.Sec14.HJRes148 CFSG.Blueprint

section Props


@[expose] def Sec13HJPointOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) →
        d ∈ YB → b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) →
        ∀ a ∈ B, a ≠ 1 → a ^ 3 = 1 → a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
          Subgroup.zpowers a ∈ omegaA A ∧
            ∃ La ∈ lA A a, Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃*
              CFSG.Blueprint.NativeSporadic.J2)

@[expose] def Sec13HJPointSection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) →
        d ∈ YB → b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) →
        ∀ a ∈ B, a ≠ 1 → a ^ 3 = 1 → a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
          ∀ La ∈ lA A a, Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃*
              CFSG.Blueprint.NativeSporadic.J2) →
          ∀ P : Subgroup G, P ≤ J ⊓ Subgroup.centralizer ({a} : Set G) →
            A ≤ Subgroup.normalizer (P : Set G) → Group.IsPerfect ↥P →
            img148 A Y P = img148 A Y J →
            P ≤ La ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))

end Props

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_inf_of_le {A N J : Subgroup G} (hN : A ≤ Subgroup.normalizer (N : Set G))
    (hJ : A ≤ Subgroup.normalizer (J : Set G)) : A ≤ Subgroup.normalizer ((N ⊓ J : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 := (Subgroup.mem_normalizer_iff.mp (hN hx) h)
  have h2 := (Subgroup.mem_normalizer_iff.mp (hJ hx) h)
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr h1 h2

theorem exists_mem_inf_centralizer_of_mem_sectionCentralizer {A Y J : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hJY : J ≤ Y) {a : G} (ha3 : a ^ 3 = 1)
    (haC : a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) {g : G} (hg : g ∈ J) :
    ∃ y ∈ J ⊓ Subgroup.centralizer ({a} : Set G), g⁻¹ * y ∈ pPrimeCoreOf 3 Y := by
  have hAN : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  set N : Subgroup G := pPrimeCoreOf 3 Y ⊓ J with hNdef
  let S : Subgroup G := sectionCentralizerSubgroup148 A J (pPrimeCoreOf 3 Y) hAJ hAN
  have haS : a ∈ S := haC
  have hzS : Subgroup.zpowers a ≤ S := (Subgroup.zpowers_le).2 haS
  have hB3 : IsPGroup 3 (Subgroup.zpowers a) := by
    refine isPGroup_three_of_pow148 fun b hb => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
  have hN3 : Nat.Coprime 3 (Nat.card N) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 Y)
  have haA : a ∈ A := haC.1
  have hBN : Subgroup.zpowers a ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.zpowers_le).2 (le_normalizer_inf_of_le hAN hAJ haA)
  have hgY : g ∈ Y := hJY hg
  obtain ⟨y, hy, hyfix⟩ := exists_commute_mem_coset148 (B := Subgroup.zpowers a) (N := N) hB3 hN3
    hBN (k := g) (fun b hb => by
      have hbS := hzS hb
      have hbA : b ∈ A := hbS.1
      have h1 : b * g * b⁻¹ * g⁻¹ ∈ pPrimeCoreOf 3 Y := hbS.2 g hg
      have h2 : g⁻¹ * (b * g * b⁻¹ * g⁻¹) * g⁻¹⁻¹ ∈ pPrimeCoreOf 3 Y :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf 3 Y (Y.inv_mem hgY))
          (b * g * b⁻¹ * g⁻¹)).mp h1
      rw [inv_inv] at h2
      have e : g⁻¹ * (b * g * b⁻¹) = g⁻¹ * (b * g * b⁻¹ * g⁻¹) * g := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [e]; exact h2
      · exact J.mul_mem (J.inv_mem hg) ((Subgroup.mem_normalizer_iff.mp (hAJ hbA) g).mp hg))
  refine ⟨y, ⟨?_, ?_⟩, hy.1⟩
  · have : y = g * (g⁻¹ * y) := by group
    rw [this]
    exact J.mul_mem hg hy.2
  · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hyfix h (Subgroup.mem_zpowers h)

section Img

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem range_eq_img148 {X : Subgroup G} (hX : X ≤ Y ⊔ A) :
    ((QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hX)).range = img148 A Y X := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact mem_img148_iff.mpr ⟨c.1, hX c.2, c.2, rfl⟩
  · intro hx
    obtain ⟨g, hg, hgX, rfl⟩ := mem_img148_iff.mp hx
    exact ⟨⟨g, hgX⟩, rfl⟩

theorem img148_inf_centralizer_eq (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {J : Subgroup G} (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hJY : J ≤ Y) {a : G}
    (ha3 : a ^ 3 = 1) (haC : a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    img148 A Y (J ⊓ Subgroup.centralizer ({a} : Set G)) = img148 A Y J := by
  refine le_antisymm (img148_mono inf_le_left) ?_
  intro x hx
  obtain ⟨g, hg, hgJ, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨y, hy, hyN⟩ := exists_mem_inf_centralizer_of_mem_sectionCentralizer hAY hAJ hJY ha3 haC hgJ
  have hyYA : y ∈ Y ⊔ A := Subgroup.mem_sup_left (hJY hy.1)
  refine mem_img148_iff.mpr ⟨y, hyYA, hy, ?_⟩
  exact (mk'_ker148_eq_iff (g := ⟨g, hg⟩) (h := ⟨y, hyYA⟩)).mpr hyN |>.symm

theorem img148_perfectResidual_eq {X : Subgroup G} (hX : X ≤ Y ⊔ A)
    (hperf : Group.IsPerfect ↥(img148 A Y X)) :
    img148 A Y (inSubgroup perfectResidual X) = img148 A Y X := by
  set ψ : ↥X →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hX) with hψ
  have hrange : ψ.range = img148 A Y X := range_eq_img148 hX
  have hperf' : Group.IsPerfect ↥ψ.range := by rw [hrange]; exact hperf
  have h1 := (perfect_residual_transport ψ).1
  have h2 : (perfectResidual ↥ψ.range).map ψ.range.subtype = ψ.range :=
    inSubgroup_perfectResidual_of_isPerfect hperf'
  have h3 : (perfectResidual ↥X).map ψ = ψ.range := h1.trans h2
  have h4 : img148 A Y (inSubgroup perfectResidual X) = (perfectResidual ↥X).map ψ := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, hg, hgP, rfl⟩ := mem_img148_iff.mp hx
      obtain ⟨c, hc, rfl⟩ := hgP
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact mem_img148_iff.mpr ⟨c.1, hX c.2, ⟨c, hc, rfl⟩, rfl⟩
  rw [h4, h3, hrange]

end Img

theorem le_normalizer_inSubgroup_perfectResidual {A X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    A ≤ Subgroup.normalizer (inSubgroup perfectResidual X : Set G) := by
  have key : ∀ y ∈ A, ∀ p ∈ inSubgroup perfectResidual X,
      y * p * y⁻¹ ∈ inSubgroup perfectResidual X := by
    intro y hy p hp
    obtain ⟨q, hq, rfl⟩ := hp
    let σ : MulAut ↥X := Subgroup.normalizerMonoidHom X ⟨y, hAX hy⟩
    have hσ : ((σ q : ↥X) : G) = y * (q : G) * y⁻¹ := rfl
    have hchar := (perfect_residual_characterization (G := ↥X)).2.1
    have hmap := Subgroup.characteristic_iff_map_eq.mp hchar σ
    have hσq : σ q ∈ perfectResidual ↥X := hmap ▸ Subgroup.mem_map_of_mem σ.toMonoidHom hq
    exact ⟨σ q, hσq, hσ⟩
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key x hx h
  · intro hh
    have := key x⁻¹ (A.inv_mem hx) _ hh
    simpa [mul_assoc] using this

omit [Finite G] in
theorem conj_mul_comm_iff {x a h : G} (hxa : x * a = a * x) :
    (x * h * x⁻¹) * a = a * (x * h * x⁻¹) ↔ h * a = a * h := by
  have hxi : x⁻¹ * a = a * x⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hxa, mul_assoc, mul_inv_cancel, mul_one]
  have e1 : (x * h * x⁻¹) * a = x * (h * a) * x⁻¹ := by
    calc (x * h * x⁻¹) * a = x * h * (x⁻¹ * a) := by group
      _ = x * h * (a * x⁻¹) := by rw [hxi]
      _ = x * (h * a) * x⁻¹ := by group
  have e2 : a * (x * h * x⁻¹) = x * (a * h) * x⁻¹ := by
    calc a * (x * h * x⁻¹) = (a * x) * h * x⁻¹ := by group
      _ = (x * a) * h * x⁻¹ := by rw [hxa]
      _ = x * (a * h) * x⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro h'
    exact mul_left_cancel (mul_right_cancel h')
  · intro hh
    rw [hh]

section Main



theorem step148HJM24Cent_of_hbar (hΩ : Sec13HJPointOmega) (hS : Sec13HJPointSection) :
    Step148HJM24Cent := by
  intro G _ _ A c L hStd Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hb hM a haB ha1 ha3 haC
  exfalso
  have hker : (ker148 A Y).Normal := ker148_normal hY.2
  obtain ⟨hΩa, La, hLa, eLa⟩ := hΩ G A c L hStd Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle
    J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hb hM a haB ha1 ha3 haC
  obtain ⟨e⟩ := hM
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA : Late.IsE27 A := hStd.isE27
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩)
  have haA : a ∈ A := haC.1
  set Cja : Subgroup G := J ⊓ Subgroup.centralizer ({a} : Set G) with hCja
  have hCjaYA : Cja ≤ Y ⊔ A := (inf_le_left.trans hJY).trans le_sup_left
  have himg1 : img148 A Y Cja = img148 A Y J :=
    img148_inf_centralizer_eq hAY hAJ hJY ha3 haC
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))).trans
      (Subgroup.card_dvd_of_le hYdJ)
  have hperfJ : Group.IsPerfect ↥(img148 A Y J) :=
    (img148_isQuasisimple (A := A) (Y := Y) hJ h3J).1.1
  have hperfC : Group.IsPerfect ↥(img148 A Y Cja) := by rw [himg1]; exact hperfJ
  set P : Subgroup G := inSubgroup perfectResidual Cja with hPdef
  have himgP : img148 A Y P = img148 A Y J :=
    (img148_perfectResidual_eq hCjaYA hperfC).trans himg1
  have hPleC : P ≤ Cja := Subgroup.map_subtype_le _
  have hPle : P ≤ J ⊓ Subgroup.centralizer ({a} : Set G) := hPleC
  have hACja : A ≤ Subgroup.normalizer (Cja : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [hCja, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (hAJ hx) h)
      (Iff.symm (conj_mul_comm_iff (hcomm x hx a haA)))
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_inSubgroup_perfectResidual hACja
  have hPperf : Group.IsPerfect ↥P := by
    have hperf := (perfect_residual_characterization (G := ↥Cja)).2.2.1
    exact Group.IsPerfect.map Cja.subtype
  have hPsub := hS G A c L hStd Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd
    hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hb ⟨e⟩ a haB ha1 ha3 haC La hLa eLa P hPle hAP
    hPperf himgP
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set T : Subgroup ↥C := aschbacherSolvableCore 3 ↥C with hT
  have hTsolv : Group.IsSolvable T :=
    (solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three).1
  have hTchar : T.Characteristic :=
    (solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three).2.1
  haveI : T.Normal := inferInstance
  obtain ⟨L', hL', hLaeq0⟩ := hLa.1
  have hLaeq : L'.map C.subtype = La := hLaeq0
  set K : Subgroup ↥L' := aschbacherSolvableCore 3 ↥L' with hK
  have hKT : K.map L'.subtype ≤ T := by
    have h := aschbacherSolvableCore_eq_subgroupOf (p := 3) (H := ↥C) Nat.prime_three hL'.2.1
    rintro _ ⟨k, hk, rfl⟩
    rw [hK, h] at hk
    exact Subgroup.mem_subgroupOf.mp hk
  haveI : IsSimpleGroup NativeSporadic.M24 := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).2.2
  have hM24ns : ¬ Group.IsSolvable NativeSporadic.M24 := by
    intro hsol
    have hc := (IsSimpleGroup.comm_iff_isSolvable (G := NativeSporadic.M24)).2 hsol
    have h := hc CFSG.Sporadic.Mathieu.m24a CFSG.Sporadic.Mathieu.m24b
    have hne : ¬ (CFSG.Sporadic.Mathieu.m24a * CFSG.Sporadic.Mathieu.m24b =
        CFSG.Sporadic.Mathieu.m24b * CFSG.Sporadic.Mathieu.m24a) := by
      decide +kernel
    exact hne h
  have hPC : P ≤ C := hPle.trans inf_le_right
  have hPYA : P ≤ Y ⊔ A := hPle.trans ((inf_le_left.trans hJY).trans le_sup_left)
  set P' : Subgroup ↥C := P.subgroupOf C with hP'
  have hP'le : P' ≤ L' ⊔ T := by
    intro x hx
    have hxP : (x : G) ∈ P := hx
    have h1 : (x : G) ∈ La ⊔ inSubgroup (aschbacherSolvableCore 3) C := hPsub hxP
    have e : La ⊔ inSubgroup (aschbacherSolvableCore 3) C = (L' ⊔ T).map C.subtype := by
      rw [Subgroup.map_sup, hLaeq]; rfl
    rw [e] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  let ψP : ↥P →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hPYA)
  have hψrange : ψP.range = img148 A Y J := (range_eq_img148 hPYA).trans himgP
  let φ0 : ↥P →* ↥(img148 A Y J) :=
    ψP.codRestrict (img148 A Y J) fun p => hψrange ▸ ⟨p, rfl⟩
  have hφ0 : Function.Surjective φ0 := by
    rintro ⟨y, hy⟩
    rw [← hψrange] at hy
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, Subtype.ext hp⟩
  let eP : ↥P' ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPC
  let φ : ↥P' →* NativeSporadic.M24 := (e.toMonoidHom.comp φ0).comp eP.toMonoidHom
  have hφ : Function.Surjective φ := e.surjective.comp (hφ0.comp eP.surjective)
  have hcardL : Nat.card (↥L' ⧸ K) = 604800 := by
    let eL : ↥L' ≃* ↥La :=
      (L'.equivMapOfInjective C.subtype C.subtype_injective).trans (MulEquiv.subgroupCongr hLaeq)
    have hmap : K.map eL.toMonoidHom = aschbacherSolvableCore 3 ↥La :=
      CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eL
    let eQ : ↥L' ⧸ K ≃* ↥La ⧸ aschbacherSolvableCore 3 ↥La := QuotientGroup.congr K _ eL hmap
    rw [Nat.card_congr (eQ.trans eLa.some).toEquiv,
      Nat.card_congr CFSG.Sporadic.J2.nativeEquiv.toEquiv, CFSG.Sporadic.J2.card_J]
  have hle := card_le_of_simple_section T hTsolv L' K hKT hM24ns P' hP'le φ hφ
  rw [CFSG.Sporadic.Mathieu.card_M24, hcardL] at hle
  omega

theorem step148HJM24Outer2_of_hbar
    (hΩ : Sec13HJPointOmega) (hS : Sec13HJPointSection) : Step148HJM24Outer2 :=
  step148HJM24Outer2_of_cent (step148HJM24Cent_of_hbar hΩ hS)

end Main

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24
