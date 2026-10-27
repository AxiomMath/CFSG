module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCoreBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport
public import CFSG.LocalAnalysis.ComponentClassification.AS81Basic

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag
open scoped Pointwise

section OddQuotient

variable {A : Type} [Group A] [Finite A] {N : Subgroup A} [N.Normal]

omit [N.Normal] in
theorem inf_eq_bot_of_isPGroup {P : Subgroup A} (hP : IsPGroup 2 P)
    (hN : Odd (Nat.card N)) : P ⊓ N = ⊥ :=
  AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ N hP.to_inf_left hN inf_le_right

theorem mk'_injOn {P : Subgroup A} (hP : IsPGroup 2 P) (hN : Odd (Nat.card N)) {x y : A}
    (hx : x ∈ P) (hy : y ∈ P) (h : QuotientGroup.mk' N x = QuotientGroup.mk' N y) : x = y := by
  have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.mp h
  have h2 : x⁻¹ * y ∈ P ⊓ N := ⟨P.mul_mem (P.inv_mem hx) hy, h1⟩
  rw [inf_eq_bot_of_isPGroup hP hN, mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem exists_sylow_map_eq (S : Sylow 2 (A ⧸ N)) {Q : Subgroup A} (hQ : IsPGroup 2 Q)
    (hQS : Q ≤ (S : Subgroup (A ⧸ N)).comap (QuotientGroup.mk' N)) :
    ∃ T : Sylow 2 A, Q ≤ T ∧ (T : Subgroup A).map (QuotientGroup.mk' N) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := (S : Subgroup (A ⧸ N)).comap (QuotientGroup.mk' N)
  obtain ⟨P, hQP⟩ := (hQ.comap_subtype : IsPGroup 2 (Q.subgroupOf M)).exists_le_sylow
  have hPsyl : ABGLocalTools.IsSylowOf 2 ((P : Subgroup M).map M.subtype) M := ⟨P, rfl⟩
  have hMmap : M.map (QuotientGroup.mk' N) = S :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  have hPmap : ((P : Subgroup M).map M.subtype).map (QuotientGroup.mk' N) = S := by
    have h := AschbacherTheorem3.IsSylowOf.map hPsyl (QuotientGroup.mk' N)
    rw [hMmap] at h
    exact (h.eq_of_le h.le le_rfl S.2).symm
  obtain ⟨T, hPT⟩ := (P.2.map M.subtype).exists_le_sylow
  refine ⟨T, fun q hq => hPT ⟨⟨q, hQS hq⟩, hQP hq, rfl⟩, ?_⟩
  have hle : (S : Subgroup (A ⧸ N)) ≤ (T : Subgroup A).map (QuotientGroup.mk' N) := by
    rw [← hPmap]
    exact map_mono hPT
  exact (S.3 (T.2.map _) hle)

end OddQuotient

structure L34Cover (A : Type) [Group A] [Finite A] where
  k : Type
  [field : Field k]
  [finite : Finite k]
  card_k : Nat.card k = 4
  π : A ⧸ standardComponentOddCore A →* projectiveSL 3 k
  surj : Function.Surjective π
  ker_eq : π.ker = (center A).map (QuotientGroup.mk' (standardComponentOddCore A))
  elem : CFSG.IsElementaryAbelian 2 π.ker

attribute [instance] L34Cover.field L34Cover.finite

section Cover

variable {A : Type} [Group A] [Finite A]

theorem oddCore_le_center (hA : commutator A = ⊤) (hs : IsSimpleGroup (A ⧸ center A)) :
    standardComponentOddCore A ≤ center A := by
  set N := standardComponentOddCore A
  set f := QuotientGroup.mk' (center A)
  have hodd : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  have hnormal : (N.map f).Normal :=
    (RankTwoSporadic.standardComponentOddCore_normal).map f (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with hbot | htop
  · rw [← QuotientGroup.ker_mk' (center A)]
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  · exfalso
    have hAp : Group.IsPerfect A := (Group.isPerfect_def).2 hA
    have hcard : Odd (Nat.card (A ⧸ center A)) := by
      have h1 : Nat.card (N.map f) ∣ Nat.card N := card_map_dvd _ _
      rw [htop, card_top] at h1
      exact hodd.of_dvd_nat h1
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard
    have hnt : Nontrivial (A ⧸ center A) := hs.toNontrivial
    exact Group.IsPerfect.not_isSolvable (A ⧸ center A) hsolv

theorem exists_l34Cover (hA : commutator A = ⊤) (hL : TypeL34 (A ⧸ center A))
    (hs : IsSimpleGroup (A ⧸ center A))
    (hC : ∀ z ∈ center A, IsPGroup 2 (zpowers z) → z ^ 2 = 1) : Nonempty (L34Cover A) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
  let e' : A ⧸ center A ≃* projectiveSL 3 K :=
    (e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  set N := standardComponentOddCore A
  have hNZ : N ≤ (center A).comap (MonoidHom.id A) := oddCore_le_center hA hs
  let m : A ⧸ N →* A ⧸ center A := QuotientGroup.map N (center A) (MonoidHom.id A) hNZ
  have hm : Function.Surjective m :=
    QuotientGroup.map_surjective_of_surjective N (center A) (MonoidHom.id A)
      (fun x => QuotientGroup.mk_surjective x) hNZ
  have hker : (e'.toMonoidHom.comp m).ker = (center A).map (QuotientGroup.mk' N) := by
    have h1 : (e'.toMonoidHom.comp m).ker = m.ker := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [h1, QuotientGroup.ker_map, comap_id]
  refine ⟨⟨K, by rw [hK]; norm_num, e'.toMonoidHom.comp m, e'.surjective.comp hm, hker, ?_⟩⟩
  rw [hker]
  refine isElementaryAbelian_of_sq_eq_one ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hy2, w, hw, hwo, rfl⟩ := exists_two_mul_odd z
  have hyZ : y ∈ center A := (zpowers_le.mpr hz) hy
  have hwZ : w ∈ center A := (zpowers_le.mpr hz) hw
  have hwN : w ∈ N := by
    have hnorm : (zpowers w).Normal := normal_of_le_center ((zpowers_le.mpr hwZ))
    refine RankTwoSporadic.le_standardComponentOddCore hnorm ?_ (mem_zpowers w)
    rwa [Nat.card_zpowers]
  have hyw : y * w = w * y := (mem_center_iff.mp hyZ w).symm
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [Commute.mul_pow hyw, hC y hyZ hy2, one_mul]
  exact N.pow_mem hwN 2

end Cover

section Transport

variable {A : Type} [Group A] [Finite A] {N : Subgroup A} [N.Normal]

theorem card_map_mk'_of_le {P Q : Subgroup A} (hP : IsPGroup 2 P) (hN : Odd (Nat.card N))
    (hQP : Q ≤ P) : Nat.card (Q.map (QuotientGroup.mk' N)) = Nat.card Q := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp P.subtype) := fun x y h =>
    Subtype.ext (mk'_injOn hP hN x.2 y.2 h)
  have h1 : (Q.subgroupOf P).map ((QuotientGroup.mk' N).comp P.subtype) =
      Q.map (QuotientGroup.mk' N) := by
    rw [← map_map, subgroupOf_map_subtype, inf_eq_left.mpr hQP]
  rw [← h1, card_map_of_injective hinj, Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv]

omit [Finite A] in
theorem map_inf_comap_eq {P : Subgroup A} {Y₁ : Subgroup (A ⧸ N)}
    (hY : Y₁ ≤ P.map (QuotientGroup.mk' N)) :
    (P ⊓ Y₁.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = Y₁ := by
  apply le_antisymm
  · rintro _ ⟨t, ⟨-, ht⟩, rfl⟩
    exact ht
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := hY hy
    exact ⟨t, ⟨ht, hy⟩, rfl⟩

theorem eq_of_map_eq {P Q₁ Q₂ : Subgroup A} (hP : IsPGroup 2 P) (hN : Odd (Nat.card N))
    (h₁ : Q₁ ≤ P) (h₂ : Q₂ ≤ P)
    (h : Q₁.map (QuotientGroup.mk' N) = Q₂.map (QuotientGroup.mk' N)) : Q₁ = Q₂ := by
  have key : ∀ {Q Q' : Subgroup A}, Q ≤ P → Q' ≤ P →
      Q.map (QuotientGroup.mk' N) = Q'.map (QuotientGroup.mk' N) → Q ≤ Q' := by
    intro Q Q' hQ hQ' hQQ x hx
    obtain ⟨y, hy, hxy⟩ : QuotientGroup.mk' N x ∈ Q'.map (QuotientGroup.mk' N) :=
      hQQ ▸ ⟨x, hx, rfl⟩
    rw [← mk'_injOn hP hN (hQ' hy) (hQ hx) hxy]
    exact hy
  exact le_antisymm (key h₁ h₂ h) (key h₂ h₁ h.symm)

end Transport

section Sylow

variable {A : Type} [Group A] [Finite A]

theorem L34Cover.ker_le_center (c : L34Cover A) :
    c.π.ker ≤ center (A ⧸ standardComponentOddCore A) := by
  rw [c.ker_eq]
  exact map_center_le_center (QuotientGroup.mk'_surjective _)

theorem exists_sylow_le_centralizer (c : L34Cover A) {a : A} (ha : a ^ 2 = 1) (ha1 : a ≠ 1) :
    ∃ T : Sylow 2 A, a ∈ (T : Subgroup A) ∧ (T : Subgroup A) ≤ centralizer ({a} : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := standardComponentOddCore A
  have hN : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  set p := QuotientGroup.mk' N
  obtain ⟨-, -, -, -, -, -, -, hlevi⟩ := field_four_central_two_cover_parabolic_normalizers
    c.card_k c.π c.surj c.ker_le_center c.elem
  obtain ⟨⟨σ, -, -, hσ, -⟩, -⟩ := hlevi 0
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hinv⟩, -, -⟩ :=
    field_four_central_cover_exact_Sylow_geometry c.card_k c.π c.surj c.ker_le_center c.elem σ hσ
  have hpa : orderOf (p a) = 2 := by
    refine orderOf_eq_prime (by rw [← map_pow, ha, map_one]) fun h => ha1 ?_
    have haN : a ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      exact h
    have h2 : orderOf a = 2 := orderOf_eq_prime ha ha1
    have := hN.of_dvd_nat (h2 ▸ Subgroup.orderOf_dvd_natCard N haN)
    exact absurd this (by decide)
  obtain ⟨S, hpaS, hSC⟩ := hinv (p a) hpa
  have h2a : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime ha ha1, pow_one])
  obtain ⟨T, haT, hTS⟩ := exists_sylow_map_eq S h2a (zpowers_le.mpr hpaS)
  refine ⟨T, haT (mem_zpowers a), fun t ht => ?_⟩
  rw [mem_centralizer_singleton_iff]
  have hpt : p t ∈ (S : Subgroup _) := hTS ▸ ⟨t, ht, rfl⟩
  have hcomm : p t * p a = p a * p t := mem_centralizer_singleton_iff.mp (hSC hpt)
  rw [← map_mul, ← map_mul] at hcomm
  exact mk'_injOn T.2 hN (T.mul_mem ht (haT (mem_zpowers a)))
    (T.mul_mem (haT (mem_zpowers a)) ht) hcomm

theorem card_ker_eq (c : L34Cover A) (T : Sylow 2 A) :
    Nat.card c.π.ker = Nat.card ↥((T : Subgroup A) ⊓ Subgroup.center A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := standardComponentOddCore A
  have hN : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  suffices heq : (center A).map (QuotientGroup.mk' N) =
      ((T : Subgroup A) ⊓ center A).map (QuotientGroup.mk' N) by
    rw [c.ker_eq, heq, card_map_mk'_of_le T.2 hN inf_le_left]
  refine le_antisymm ?_ (map_mono inf_le_right)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hy2, w, hw, hwo, rfl⟩ := exists_two_mul_odd z
  have hyZ : y ∈ center A := (zpowers_le.mpr hz) hy
  have hwZ : w ∈ center A := (zpowers_le.mpr hz) hw
  have hwN : w ∈ N := by
    have hnorm : (zpowers w).Normal := normal_of_le_center ((zpowers_le.mpr hwZ))
    refine RankTwoSporadic.le_standardComponentOddCore hnorm ?_ (mem_zpowers w)
    rwa [Nat.card_zpowers]
  have hyT : y ∈ (T : Subgroup A) := by
    have hTN : (T : Subgroup A) ≤ normalizer ((zpowers y : Subgroup A) : Set A) := by
      have := normal_of_le_center (zpowers_le.mpr hyZ)
      exact le_normalizer_of_normal
    have hsup := T.3 (T.2.to_sup_of_normal_right' hy2 hTN) le_sup_left
    exact hsup ▸ mem_sup_right (mem_zpowers y)
  refine ⟨y, ⟨hyT, hyZ⟩, ?_⟩
  rw [map_mul, QuotientGroup.mk'_apply N w, (QuotientGroup.eq_one_iff w).mpr hwN, mul_one]

theorem sylow_structure (c : L34Cover A) (T : Sylow 2 A) :
    ∃ H₁ H₂ : Subgroup A, H₁ ≤ T ∧ H₂ ≤ T ∧ IsElemAbelian 2 H₁ ∧ IsElemAbelian 2 H₂ ∧
      Nat.card H₁ = 16 * Nat.card c.π.ker ∧ Nat.card H₂ = 16 * Nat.card c.π.ker ∧
      H₁ ⊔ H₂ = T ∧ H₁ ⊓ H₂ = centerIn (T : Subgroup A) ∧
      Nat.card (centerIn (T : Subgroup A)) = 4 * Nat.card c.π.ker ∧
      (commutator A = ⊤ →
        ⁅(T : Subgroup A), (T : Subgroup A)⁆ = centerIn (T : Subgroup A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := standardComponentOddCore A
  have hN : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  set p := QuotientGroup.mk' N
  set S : Sylow 2 (A ⧸ N) := T.mapSurjective (QuotientGroup.mk'_surjective N)
  have hS : (S : Subgroup (A ⧸ N)) = (T : Subgroup A).map p := Sylow.coe_mapSurjective _ _
  obtain ⟨-, -, ⟨S₀, hS₀⟩, -⟩ := field_four_central_two_cover_parabolic_normalizers
    c.card_k c.π c.surj c.ker_le_center c.elem
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (A ⧸ N) S₀ S
  set π' := c.π.comp (MulAut.conj x⁻¹).toMonoidHom
  have hker' : π'.ker = c.π.ker := by
    ext y
    simp only [π', MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker]
    constructor
    · intro h
      have := (MonoidHom.normal_ker c.π).conj_mem _ h x
      simpa [mul_assoc] using this
    · intro h
      have := (MonoidHom.normal_ker c.π).conj_mem _ h x⁻¹
      simpa [mul_assoc] using this
  have hsurj' : Function.Surjective π' := c.surj.comp (MulAut.conj x⁻¹).surjective
  have hCZ' : π'.ker ≤ center (A ⧸ N) := hker' ▸ c.ker_le_center
  have helem' : CFSG.IsElementaryAbelian 2 π'.ker := hker' ▸ c.elem
  have hT' : (projUnip c.k).comap π' = (S : Subgroup (A ⧸ N)) := by
    rw [← hx, Sylow.coe_subgroup_smul, hS₀]
    ext y
    rw [mem_pointwise_smul_iff_inv_smul_mem, mem_comap, mem_comap]
    simp [π', MulAut.smul_def]
  obtain ⟨hH, hmul, -, -, hinter, hcenter, hcardZ, hlevi⟩ :=
    field_four_central_two_cover_parabolic_normalizers c.card_k π' hsurj' hCZ' helem'
  obtain ⟨⟨σ, -, -, hσ, -⟩, -⟩ := hlevi 0
  obtain ⟨-, -, hperf⟩ :=
    field_four_central_cover_exact_Sylow_geometry c.card_k π' hsurj' hCZ' helem' σ hσ
  rw [hT'] at hmul hinter hcenter hperf
  set H' : Fin 2 → Subgroup (A ⧸ N) := fun i => (projRad c.k i).comap π'
  have hH'S : ∀ i, H' i ≤ (T : Subgroup A).map p := by
    intro i y hy
    rw [← hS, ← SetLike.mem_coe, ← hmul]
    fin_cases i
    · exact ⟨y, hy, 1, one_mem _, mul_one y⟩
    · exact ⟨1, one_mem _, y, hy, one_mul y⟩
  set H : Fin 2 → Subgroup A := fun i => (T : Subgroup A) ⊓ (H' i).comap p
  have hHmap : ∀ i, (H i).map p = H' i := fun i => map_inf_comap_eq (hH'S i)
  have hHT : ∀ i, H i ≤ T := fun i => inf_le_left
  have hHelem : ∀ i, IsElemAbelian 2 (H i) := by
    intro i
    have hel := (hH i).1
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun h hh => ?_⟩
    · have hc : p a * p b = p b * p a := by
        have := (hel.toIsMulCommutative.is_comm.comm ⟨p a, a.2.2⟩ ⟨p b, b.2.2⟩)
        exact congrArg Subtype.val this
      rw [← map_mul, ← map_mul] at hc
      exact mk'_injOn T.2 hN (T.mul_mem a.2.1 b.2.1) (T.mul_mem b.2.1 a.2.1) hc
    · have h2 : p h ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := H' i) _ hh.2
      rw [← map_pow, ← map_one p] at h2
      exact mk'_injOn T.2 hN (T.pow_mem hh.1 2) (one_mem _) h2
  have hHcard : ∀ i, Nat.card (H i) = 16 * Nat.card c.π.ker := by
    intro i
    rw [← card_map_mk'_of_le T.2 hN (hHT i), hHmap, (hH i).2, hker']
  have hsup : H 0 ⊔ H 1 = T := by
    refine le_antisymm (sup_le (hHT 0) (hHT 1)) fun t ht => ?_
    have hpt : p t ∈ ((H' 0 : Set (A ⧸ N)) * (H' 1 : Set (A ⧸ N))) := by
      rw [hmul, hS]
      exact ⟨t, ht, rfl⟩
    obtain ⟨y₀, hy₀, y₁, hy₁, hy⟩ := hpt
    obtain ⟨t₀, ht₀, rfl⟩ : y₀ ∈ (H 0).map p := (hHmap 0).symm ▸ hy₀
    obtain ⟨t₁, ht₁, rfl⟩ : y₁ ∈ (H 1).map p := (hHmap 1).symm ▸ hy₁
    have hy' : p (t₀ * t₁) = p t := by rw [map_mul]; exact hy
    rw [← mk'_injOn T.2 hN (T.mul_mem (hHT 0 ht₀) (hHT 1 ht₁)) ht hy']
    exact mul_mem (mem_sup_left ht₀) (mem_sup_right ht₁)
  have hZmap : (centerIn (T : Subgroup A)).map p = (center S).map (S : Subgroup _).subtype := by
    apply le_antisymm
    · rintro _ ⟨t, ⟨htT, htC⟩, rfl⟩
      refine ⟨⟨p t, hS ▸ ⟨t, htT, rfl⟩⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      rintro ⟨y, hy⟩
      obtain ⟨s, hs, rfl⟩ : y ∈ (T : Subgroup A).map p := hS ▸ hy
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp htC s hs]
    · rintro _ ⟨⟨y, hy⟩, hyZ, rfl⟩
      obtain ⟨t, htT, rfl⟩ : y ∈ (T : Subgroup A).map p := hS ▸ hy
      refine ⟨t, ⟨htT, ?_⟩, rfl⟩
      show t ∈ centralizer ((T : Subgroup A) : Set A)
      rw [mem_centralizer_iff]
      intro s hs
      have hc := congrArg Subtype.val (mem_center_iff.mp hyZ ⟨p s, hS ▸ ⟨s, hs, rfl⟩⟩)
      simp only [coe_mul] at hc
      rw [← map_mul, ← map_mul] at hc
      exact mk'_injOn T.2 hN (T.mul_mem hs htT) (T.mul_mem htT hs) hc
  have hZle : centerIn (T : Subgroup A) ≤ T := inf_le_left
  have hinf : H 0 ⊓ H 1 = centerIn (T : Subgroup A) := by
    refine eq_of_map_eq T.2 hN (inf_le_left.trans (hHT 0)) hZle ?_
    rw [hZmap, ← hinter]
    have : H 0 ⊓ H 1 = (T : Subgroup A) ⊓ (H' 0 ⊓ H' 1).comap p := by
      ext y
      simp only [H, mem_inf, mem_comap]
      tauto
    rw [this, map_inf_comap_eq (inf_le_left.trans (hH'S 0))]
  refine ⟨H 0, H 1, hHT 0, hHT 1, hHelem 0, hHelem 1, hHcard 0, hHcard 1, hsup, hinf, ?_, ?_⟩
  · rw [← card_map_mk'_of_le T.2 hN hZle, hZmap, hcenter, hcardZ, hker']
  · intro hA
    have hX : Group.IsPerfect (A ⧸ N) := by
      have : Group.IsPerfect A := (Group.isPerfect_def).2 hA
      exact Group.IsPerfect.ofSurjective (f := p) (QuotientGroup.mk'_surjective N)
    obtain ⟨-, -, hc, hf, -⟩ := hperf hX
    refine eq_of_map_eq T.2 hN (commutator_le_self _) hZle ?_
    rw [map_commutator, ← hS, hZmap, hc, hf]

end Sylow

end CFSG.ComponentClassification.AS81
