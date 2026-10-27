module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Not9
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7N

variable {Y : Type} [Group Y] [Finite Y]

theorem sq_eq_one_of_mem_closure {Q : Type} [Group Q] {X : Set Q}
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hX2 : ∀ x ∈ X, x * x = 1) :
    ∀ a ∈ Subgroup.closure X, a * a = 1 := by
  have hcomm := F7I.closure_comm hXc
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hX2 x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hxy := hcomm x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    rw [← mul_inv_rev, ihx, inv_one]

theorem conjSub_inv_mul_eq {Q : Type} [Group Q] {a b : Q} {K : Subgroup Q}
    (h : conjSub a K = conjSub b K) : conjSub (a⁻¹ * b) K = K := by
  ext x
  rw [mem_conjSub_iff]
  have h1 : (a⁻¹ * b)⁻¹ * x * (a⁻¹ * b) = b⁻¹ * (a * x * a⁻¹) * b := by group
  rw [h1, ← mem_conjSub_iff, ← h, mem_conjSub_iff]
  have h2 : a⁻¹ * (a * x * a⁻¹) * a = x := by group
  rw [h2]

theorem conj_cent_of_perm {Q : Type} [Group Q] {A B : Subgroup Q} {eb : Q}
    (hperm : ∀ q : Q, (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A))
    (heA : ∀ x ∈ A, eb * x = x * eb) (heB : ∀ x ∈ B, eb * x = x * eb) (γ : Q) :
    (∀ x ∈ A, γ * eb * γ⁻¹ * x = x * (γ * eb * γ⁻¹)) ∧
      (∀ x ∈ B, γ * eb * γ⁻¹ * x = x * (γ * eb * γ⁻¹)) := by
  have key : ∀ x : Q, (γ⁻¹ * x * γ ∈ A ∨ γ⁻¹ * x * γ ∈ B) →
      γ * eb * γ⁻¹ * x = x * (γ * eb * γ⁻¹) := by
    intro x hx
    have h1 : eb * (γ⁻¹ * x * γ) = (γ⁻¹ * x * γ) * eb := by
      rcases hx with hx | hx
      · exact heA _ hx
      · exact heB _ hx
    calc γ * eb * γ⁻¹ * x = γ * (eb * (γ⁻¹ * x * γ)) * γ⁻¹ := by group
      _ = γ * ((γ⁻¹ * x * γ) * eb) * γ⁻¹ := by rw [h1]
      _ = x * (γ * eb * γ⁻¹) := by group
  have hmem : ∀ (H : Subgroup Q) (x : Q), x ∈ H → γ⁻¹ * x * γ ∈ conjSub γ⁻¹ H := by
    intro H x hx
    rw [mem_conjSub_iff]
    have e : γ⁻¹⁻¹ * (γ⁻¹ * x * γ) * γ⁻¹ = x := by group
    rw [e]
    exact hx
  constructor
  · intro x hx
    apply key
    rcases hperm γ⁻¹ with ⟨h1, -⟩ | ⟨h1, -⟩
    · left; rw [← h1]; exact hmem A x hx
    · right; rw [← h1]; exact hmem A x hx
  · intro x hx
    apply key
    rcases hperm γ⁻¹ with ⟨-, h1⟩ | ⟨-, h1⟩
    · right; rw [← h1]; exact hmem B x hx
    · left; rw [← h1]; exact hmem B x hx

theorem normal_closure_of_conj {Q : Type} [Group Q] {X : Set Q}
    (hX : ∀ q x, x ∈ X → q * x * q⁻¹ ∈ X) : (Subgroup.closure X).Normal := by
  refine ⟨fun x hx q => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hX q x hx)
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ ihx ihy =>
    have h : q * (x * y) * q⁻¹ = (q * x * q⁻¹) * (q * y * q⁻¹) := by group
    rw [h]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    have h : q * x⁻¹ * q⁻¹ = (q * x * q⁻¹)⁻¹ := by group
    rw [h]
    exact Subgroup.inv_mem _ ihx

theorem exists_zdata (C : Subgroup Y) (Pb : Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C))
    (hPn : Pb.Normal) (hPc : ∀ a ∈ Pb, ∀ b ∈ Pb, a * b = b * a) (hP2 : ∀ a ∈ Pb, a * a = 1)
    (e t u : ↥C) (heP : F7I.piC C e ∈ Pb) (htP : F7I.piC C t ∈ Pb)
    (huP : ∀ a ∈ Pb, F7I.piC C u * a = a * F7I.piC C u)
    (he2 : e * e = 1) (ht2 : t * t = 1) (hu2 : u * u = 1)
    (het : e * t = t * e) (heu : e * u = u * e) (htu : t * u = u * t) :
    ∃ Z : Subgroup Y, (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) ∧ (∀ a ∈ Z, a * a = 1) ∧
      (e : Y) ∈ Z ∧ (t : Y) ∈ Z ∧ Z ≤ C ∧ Z ≤ Subgroup.centralizer ({(u : Y)} : Set Y) ∧
      (∀ c ∈ C, ∃ o ∈ oddCoreOf C, ∃ m ∈ C ⊓ Subgroup.normalizer (Z : Set Y), c = o * m) ∧
      (∀ a (ha : a ∈ Z), ∃ hC : a ∈ C, F7I.piC C ⟨a, hC⟩ ∈ Pb) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := F7I.piC C with hπ
  set P : Subgroup Y := (Pb.comap π).map C.subtype with hPdef
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have memP : ∀ c : ↥C, (c : Y) ∈ P ↔ π c ∈ Pb := by
    intro c
    constructor
    · rintro ⟨c', hc', hcc'⟩
      rw [Subtype.ext hcc'] at hc'
      exact hc'
    · intro h
      exact ⟨c, h, rfl⟩
  set O := oddCoreOf C with hOdef
  have hOP : O ≤ P := by
    rintro _ ⟨c, hc, rfl⟩
    refine (memP c).mpr ?_
    have : π c = 1 := (F7I.piC_eq_one_iff c).mpr ⟨c, hc, rfl⟩
    rw [this]
    exact Pb.one_mem
  have hPnorm : ∀ c ∈ C, ∀ p ∈ P, c * p * c⁻¹ ∈ P := by
    intro c hc p hp
    obtain ⟨p', hp', rfl⟩ := hp
    have hmem : ((⟨c, hc⟩ * p' * (⟨c, hc⟩ : ↥C)⁻¹ : ↥C) : Y) ∈ P := by
      refine (memP _).mpr ?_
      rw [map_mul, map_mul, map_inv]
      exact hPn.conj_mem _ hp' _
    exact hmem
  set X : Set Y := {(e : Y), (t : Y), (u : Y)} with hXdef
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    have he' : (e : Y) * t = t * e := congrArg Subtype.val het
    have hu' : (e : Y) * u = u * e := congrArg Subtype.val heu
    have ht' : (t : Y) * u = u * t := congrArg Subtype.val htu
    simp only [hXdef, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl)
    all_goals first
      | rfl
      | exact he'
      | exact hu'
      | exact ht'
      | exact he'.symm
      | exact hu'.symm
      | exact ht'.symm
  have hX2 : ∀ x ∈ X, x * x = 1 := by
    simp only [hXdef, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro x (rfl | rfl | rfl)
    · exact congrArg Subtype.val he2
    · exact congrArg Subtype.val ht2
    · exact congrArg Subtype.val hu2
  set B := Subgroup.closure X with hBdef
  have hB2 : IsPGroup 2 B := by
    intro b
    refine ⟨1, ?_⟩
    ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one, pow_two]
    exact sq_eq_one_of_mem_closure hXc hX2 b b.2
  set H := P ⊔ Subgroup.zpowers (u : Y) with hHdef
  have hBH : B ≤ H := by
    refine (Subgroup.closure_le _).mpr ?_
    simp only [hXdef, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Subgroup.mem_sup_left ((memP e).mpr heP), Subgroup.mem_sup_left ((memP t).mpr htP),
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
  have hHC : H ≤ C := sup_le hPC ((Subgroup.zpowers_le).mpr u.2)
  have hHN : H ≤ Subgroup.normalizer (P : Set Y) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨hPnorm h (hHC hh) p, fun hp => ?_⟩
    have := hPnorm h⁻¹ (C.inv_mem (hHC hh)) _ hp
    simpa [mul_assoc] using this
  obtain ⟨T, hT, hBT⟩ := IsSylow2In.exists_ge hB2 hBH
  have hZP : IsSylow2In (T ⊓ P) P := Asc77.isSylow2In_inf_of_le_normalizer hT le_sup_left hHN
  set Z := T ⊓ P with hZdef
  have hT2 : IsPGroup 2 T := hT.2.1
  have hTC : T ≤ C := hT.1.trans hHC
  set Pu := Pb ⊔ Subgroup.zpowers (π u) with hPudef
  have hPuc : ∀ a ∈ Pu, ∀ b ∈ Pu, a * b = b * a := by
    have hcl : Pu = Subgroup.closure ((Pb : Set _) ∪ {π u}) := by
      rw [hPudef, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
    rw [hcl]
    apply F7I.closure_comm
    rintro x (hx | hx) y (hy | hy)
    · exact hPc x hx y hy
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact (huP x hx).symm
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact huP y hy
    · rw [Set.mem_singleton_iff] at hx hy; rw [hx, hy]
  have hHPu : H ≤ (Pu.comap π).map C.subtype := by
    refine sup_le ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨c, Subgroup.mem_sup_left hc, rfl⟩
    · refine (Subgroup.zpowers_le).mpr ⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), rfl⟩
  have hTPu : ∀ a (ha : a ∈ T), π ⟨a, hTC ha⟩ ∈ Pu := by
    intro a ha
    obtain ⟨c, hc, hca⟩ := hHPu (hT.1 ha)
    have : c = ⟨a, hTC ha⟩ := Subtype.ext hca
    rw [← this]
    exact hc
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    have h1 : π (⟨a, hTC ha⟩ * ⟨b, hTC hb⟩) = π (⟨b, hTC hb⟩ * ⟨a, hTC ha⟩) := by
      rw [map_mul, map_mul]
      exact hPuc _ (hTPu a ha) _ (hTPu b hb)
    have h2 := F7I.piC_inj hT2 (T.mul_mem ha hb) (T.mul_mem hb ha) h1
    exact congrArg Subtype.val h2
  have hZT : Z ≤ T := inf_le_left
  have hZ2 : IsPGroup 2 Z := hT2.to_le hZT
  have hZC : Z ≤ C := hZT.trans hTC
  have hPOZ : P ≤ O ⊔ Z := by
    have h1 : (O ⊔ Z).relIndex P ∣ Z.relIndex P := Subgroup.relIndex_dvd_of_le_left P le_sup_right
    have h2 : (O ⊔ Z).relIndex P ∣ O.relIndex P := Subgroup.relIndex_dvd_of_le_left P le_sup_left
    have hodd : ¬ 2 ∣ Z.relIndex P := Sylow.not_dvd_index (AscL62.sylowOfIsSylow2In'' hZP)
    have hPb2 : IsPGroup 2 Pb := by
      intro a
      refine ⟨1, ?_⟩
      ext
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact hP2 a a.2
    obtain ⟨n, hn⟩ := hPb2.exists_card_eq
    have hidx : O.relIndex P = 2 ^ n := by
      rw [hOdef, hPdef, oddCoreOf, Subgroup.relIndex_map_map_of_injective _ _ C.subtype_injective]
      have hker : π.ker = classicalInvolutionOddCore ↥C := QuotientGroup.ker_mk' _
      refine (congrArg (fun K : Subgroup ↥C => K.relIndex (Pb.comap π)) hker.symm).trans ?_
      rw [← MonoidHom.comap_bot, Subgroup.relIndex_comap,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
        Subgroup.relIndex_bot_left, hn]
    rw [hidx] at h2
    have hcop : Nat.Coprime ((O ⊔ Z).relIndex P) (2 ^ n) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (fun h => hodd (h.trans h1)) |>.symm)
    have h3 : (O ⊔ Z).relIndex P = 1 := Nat.Coprime.eq_one_of_dvd hcop h2
    exact Subgroup.relIndex_eq_one.mp h3
  have hZN : Z ≤ Subgroup.normalizer (O : Set Y) := hZC.trans (Sec7.le_normalizer_oddCoreOf C)
  refine ⟨Z, fun a ha b hb => hTab a (hZT ha) b (hZT hb), ?_, ⟨hBT (Subgroup.subset_closure
    (by simp [hXdef])), (memP e).mpr heP⟩, ⟨hBT (Subgroup.subset_closure (by simp [hXdef])),
    (memP t).mpr htP⟩, hZC, ?_, ?_, ?_⟩
  · intro a ha
    have haC := hZC ha
    obtain ⟨c, hc, hca⟩ := (inf_le_right : Z ≤ P) ha
    have hc' : c = ⟨a, haC⟩ := Subtype.ext hca
    have h1 : π (⟨a, haC⟩ * ⟨a, haC⟩) = π 1 := by
      rw [map_mul, map_one, ← hc']
      exact hP2 _ hc
    have h2 := F7I.piC_inj hZ2 (Z.mul_mem ha ha) Z.one_mem h1
    exact congrArg Subtype.val h2
  · intro a ha
    have huT : (u : Y) ∈ T := hBT (Subgroup.subset_closure (by simp [hXdef]))
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hTab _ huT a (hZT ha)).symm
  · intro c hc
    have hcZ : conjSub c Z ≤ P := by
      rintro _ ⟨z, hz, rfl⟩
      exact hPnorm c hc z ((inf_le_right : Z ≤ P) hz)
    have hcZ2 : IsPGroup 2 (conjSub c Z) := hZ2.map _
    obtain ⟨p, hp, hle⟩ := Asc77.exists_conj_of_isSylow2In hZP hcZ2 hcZ
    have hcard : Nat.card (conjSub p Z) ≤ Nat.card (conjSub c Z) := by
      rw [show Nat.card (conjSub p Z) = Nat.card Z from
          Subgroup.card_map_of_injective (MulAut.conj p).injective,
        show Nat.card (conjSub c Z) = Nat.card Z from
          Subgroup.card_map_of_injective (MulAut.conj c).injective]
    have heq : conjSub c Z = conjSub p Z := Subgroup.eq_of_le_of_card_ge hle hcard
    have hp' : p ∈ ((O ⊔ Z : Subgroup Y) : Set Y) := hPOZ hp
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN] at hp'
    obtain ⟨o, ho, z, hz, rfl⟩ := hp'
    refine ⟨o, ho, z * ((o * z)⁻¹ * c), ⟨?_, ?_⟩, by group⟩
    · exact C.mul_mem (hZC hz) (C.mul_mem (C.inv_mem (C.mul_mem (hPC (hOP ho)) (hZC hz))) hc)
    · have hzN : z ∈ Subgroup.normalizer (Z : Set Y) := Subgroup.le_normalizer hz
      have hnN : (o * z)⁻¹ * c ∈ Subgroup.normalizer (Z : Set Y) :=
        mem_normalizer_iff_conjSub_eq.mpr (conjSub_inv_mul_eq heq.symm)
      exact Subgroup.mul_mem _ hzN hnN
  · intro a ha
    refine ⟨hZC ha, ?_⟩
    obtain ⟨c, hc, hca⟩ := (inf_le_right : Z ≤ P) ha
    have hc' : c = ⟨a, hZC ha⟩ := Subtype.ext hca
    rw [← hc']
    exact hc

end F7N

section Apply


variable {n : ℕ}

theorem p23E7ZEx_proved : P23E7ZEx n := by
  intro hcit hP Y _ _ R S t K' W u e g hc _ _ hZ
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have htC : t ∈ C := hWt hd.hzW
  have heC : e ∈ C := hWt heW
  have huC : u ∈ C := hWt hd.huW
  have ht2 : t * t = 1 := (Inner.isUniqueInvolution_core hC.datum).sq
  set A := ((tightCore R).subgroupOf C).map (F7I.piC C) with hAdef
  set B := (K'.subgroupOf C).map (F7I.piC C) with hBdef
  obtain ⟨-, -, -, -, -, -, -, heA, heB, b₁, b', hub, hb₁, hb', -⟩ := p23_twin_q8 hc hCdef htC heC
  have hperm : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _) ∨
      (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _)
    rw [hAdef, hBdef, F7I.conjSub_map_piC, F7I.conjSub_map_piC]
    rcases p23_conj_twins hc c.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
  have hMB' := p23MBar_proved hcit hP Y R S t K' W u e g hc hZ ⟨e, heC⟩ rfl
  have hcc := F7I.conj_comm_of_cent hperm heA heB hMB'
  have hcAB := F7N.conj_cent_of_perm hperm heA heB
  set π := F7I.piC C with hπ
  set eb := π ⟨e, heC⟩ with hebdef
  set tb := π ⟨t, htC⟩ with htbdef
  have htcen : ∀ x : ↥C ⧸ classicalInvolutionOddCore ↥C, tb * x = x * tb := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) x
    have hct : (c : Y) * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
    have h : (⟨t, htC⟩ : ↥C) * c = c * ⟨t, htC⟩ := Subtype.ext hct.symm
    change π _ * π c = π c * π _
    rw [← map_mul, ← map_mul, h]
  have he2' : (⟨e, heC⟩ : ↥C) * ⟨e, heC⟩ = 1 := Subtype.ext hd.he2
  have ht2' : (⟨t, htC⟩ : ↥C) * ⟨t, htC⟩ = 1 := Subtype.ext ht2
  have hu2' : (⟨u, huC⟩ : ↥C) * ⟨u, huC⟩ = 1 := Subtype.ext hd.hu2
  have heb2 : eb * eb = 1 := by rw [hebdef, ← map_mul, he2', map_one]
  have htb2 : tb * tb = 1 := by rw [htbdef, ← map_mul, ht2', map_one]
  obtain ⟨Sb, hSb⟩ : ∃ Sb : Set (↥C ⧸ classicalInvolutionOddCore ↥C),
      Sb = {x | ∃ c : ↥C, ((c : Y) = t ∨ ∃ d ∈ C, (c : Y) = d * e * d⁻¹) ∧ π c = x} := ⟨_, rfl⟩
  have hgen : ∀ x ∈ Sb, x = tb ∨ ∃ γ, x = γ * eb * γ⁻¹ := by
    intro x hx
    rw [hSb] at hx
    obtain ⟨c, hcX, rfl⟩ := hx
    rcases hcX with hct | ⟨d, hdC, hcd⟩
    · left
      have h : c = ⟨t, htC⟩ := Subtype.ext hct
      rw [h]
    · right
      refine ⟨π ⟨d, hdC⟩, ?_⟩
      have h : c = ⟨d, hdC⟩ * ⟨e, heC⟩ * (⟨d, hdC⟩ : ↥C)⁻¹ := Subtype.ext hcd
      rw [h, map_mul, map_mul, map_inv]
  have hSinv : ∀ q x, x ∈ Sb → q * x * q⁻¹ ∈ Sb := by
    intro q x hx
    rw [hSb] at hx ⊢
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    obtain ⟨c, hcX, rfl⟩ := hx
    refine ⟨d * c * d⁻¹, ?_, ?_⟩
    · have hdt : (d : Y) * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp d.2
      show (d : Y) * c * (d : Y)⁻¹ = t ∨ ∃ d' ∈ C, (d : Y) * c * (d : Y)⁻¹ = d' * e * d'⁻¹
      rcases hcX with hct | ⟨d', hd'C, hcd⟩
      · left
        rw [hct, hdt, mul_inv_cancel_right]
      · right
        refine ⟨d * d', C.mul_mem d.2 hd'C, ?_⟩
        rw [hcd]
        group
    · change π (d * c * d⁻¹) = π d * π c * (π d)⁻¹
      rw [map_mul, map_mul, map_inv]
  have hScomm : ∀ x ∈ Sb, ∀ y ∈ Sb, x * y = y * x := by
    intro x hx y hy
    rcases hgen x hx with rfl | ⟨γ, rfl⟩
    · exact htcen y
    · rcases hgen y hy with rfl | ⟨δ, rfl⟩
      · exact (htcen _).symm
      · exact hcc γ δ
  have hS2 : ∀ x ∈ Sb, x * x = 1 := by
    intro x hx
    rcases hgen x hx with rfl | ⟨γ, rfl⟩
    · exact htb2
    · calc γ * eb * γ⁻¹ * (γ * eb * γ⁻¹) = γ * (eb * eb) * γ⁻¹ := by group
        _ = 1 := by rw [heb2, mul_one, mul_inv_cancel]
  set Pb := Subgroup.closure Sb with hPbdef
  have hPn : Pb.Normal := F7N.normal_closure_of_conj hSinv
  have hPc : ∀ a ∈ Pb, ∀ b ∈ Pb, a * b = b * a := F7I.closure_comm hScomm
  have hP2 : ∀ a ∈ Pb, a * a = 1 := F7N.sq_eq_one_of_mem_closure hScomm hS2
  have hu' : (⟨u, huC⟩ : ↥C) = b₁ * b' := Subtype.ext hub.symm
  have huS : ∀ x ∈ Sb, x * π ⟨u, huC⟩ = π ⟨u, huC⟩ * x := by
    intro x hx
    rcases hgen x hx with rfl | ⟨γ, rfl⟩
    · exact htcen _
    · rw [hu', map_mul]
      have h1 := (hcAB γ).1 _ hb₁
      have h2 := (hcAB γ).2 _ hb'
      calc γ * eb * γ⁻¹ * (π b₁ * π b') = (γ * eb * γ⁻¹ * π b₁) * π b' := by group
        _ = π b₁ * (γ * eb * γ⁻¹ * π b') := by rw [h1]; group
        _ = π b₁ * (π b' * (γ * eb * γ⁻¹)) := by rw [h2]
        _ = π b₁ * π b' * (γ * eb * γ⁻¹) := by group
  have huP : ∀ a ∈ Pb, π ⟨u, huC⟩ * a = a * π ⟨u, huC⟩ := by
    have hle : Pb ≤ Subgroup.centralizer ({π ⟨u, huC⟩} : Set _) := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr (huS x hx)
    intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm
  have heP : eb ∈ Pb := by
    refine Subgroup.subset_closure ?_
    rw [hSb]
    exact ⟨⟨e, heC⟩, Or.inr ⟨1, C.one_mem, by group⟩, rfl⟩
  have htP : tb ∈ Pb := by
    refine Subgroup.subset_closure ?_
    rw [hSb]
    exact ⟨⟨t, htC⟩, Or.inl rfl, rfl⟩
  have het : (⟨e, heC⟩ : ↥C) * ⟨t, htC⟩ = ⟨t, htC⟩ * ⟨e, heC⟩ :=
    Subtype.ext (hWab e heW t hd.hzW)
  have heu : (⟨e, heC⟩ : ↥C) * ⟨u, huC⟩ = ⟨u, huC⟩ * ⟨e, heC⟩ :=
    Subtype.ext (hWab e heW u hd.huW)
  have htu : (⟨t, htC⟩ : ↥C) * ⟨u, huC⟩ = ⟨u, huC⟩ * ⟨t, htC⟩ :=
    Subtype.ext (hWab t hd.hzW u hd.huW)
  obtain ⟨Z, hab, hsq, heZ, htZ, hZC, hZu, hfr, himg⟩ :=
    F7N.exists_zdata C Pb hPn hPc hP2 ⟨e, heC⟩ ⟨t, htC⟩ ⟨u, huC⟩ heP htP huP he2' ht2' hu2' het
      heu htu
  set Q := Subgroup.closure (({t} : Set Y) ∪ {f | ∃ c ∈ C, f = c * e * c⁻¹}) with hQdef
  have hPbQ : Pb ≤ (Q.subgroupOf C).map π := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rw [hSb] at hx
    obtain ⟨c, hcX, rfl⟩ := hx
    refine ⟨c, Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ?_), rfl⟩
    rcases hcX with h | ⟨d, hdC, h⟩
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ ⟨d, hdC, h⟩
  refine ⟨Z, ⟨hab, hsq, heZ, htZ, hZC, hZu, hfr, ?_⟩⟩
  intro a ha
  obtain ⟨haC, hπa⟩ := himg a ha
  obtain ⟨q, hq, hqa⟩ := hPbQ hπa
  have ho : ((q⁻¹ * ⟨a, haC⟩ : ↥C) : Y) ∈ oddCoreOf C := (F7I.piC_eq_iff q ⟨a, haC⟩).mp hqa
  have hqQ : (q : Y) ∈ Q := Subgroup.mem_subgroupOf.mp hq
  have h : a = (q : Y) * ((q⁻¹ * ⟨a, haC⟩ : ↥C) : Y) := by
    show a = (q : Y) * ((q : Y)⁻¹ * a)
    group
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hqQ) (Subgroup.mem_sup_left ho)

theorem p23E7Not9C_of_leaves (h7 : P23E7N7 n) (h1 : P23E7LL1 n) (h2 : P23E7LL2 n) (h3 : P23E7LL3 n) :
    P23E7Not9C n :=
  p23E7Not9C_of_steps p23E7ZEx_proved h7 h1 h2 h3

end Apply

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
