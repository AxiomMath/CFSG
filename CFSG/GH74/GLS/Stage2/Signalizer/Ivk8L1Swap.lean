module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Zc

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

section Swap

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

@[expose] def cs (g : A) (H : Subgroup A) : Subgroup A := H.map (MulAut.conj g).toMonoidHom

omit [Finite A] in
theorem mem_cs {g x : A} {H : Subgroup A} : x ∈ cs g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite A] in
theorem cs_cs (g h : A) (H : Subgroup A) : cs g (cs h H) = cs (g * h) H := by
  ext x
  simp only [mem_cs]
  rw [mul_inv_rev]
  simp [mul_assoc]

omit [Finite A] in
theorem cs_one (H : Subgroup A) : cs 1 H = H := by
  ext x
  simp [mem_cs]

omit [Finite A] in
theorem cs_injective (g : A) : Function.Injective (cs g : Subgroup A → Subgroup A) := by
  intro H K h
  have h1 : cs g⁻¹ (cs g H) = cs g⁻¹ (cs g K) := by rw [h]
  rwa [cs_cs, cs_cs, inv_mul_cancel, cs_one, cs_one] at h1

omit [Finite A] in
theorem cs_inv_cs (g : A) (H : Subgroup A) : cs g⁻¹ (cs g H) = H := by
  rw [cs_cs, inv_mul_cancel, cs_one]

omit [Finite A] in
theorem cs_eq_iff_mem_normalizer {g : A} {H : Subgroup A} :
    cs g H = H ↔ g ∈ normalizer (H : Set A) :=
  ⟨mem_normalizer_of_map_conj_eq, map_conj_eq_of_mem_normalizer⟩

omit [Finite A] in
theorem isComponent_cs (hJ : IsComponent J) (g : A) : IsComponent (cs g J) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ


variable (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) {s : A} (hs : cs s J ≠ J)
include hfr hJ hs

theorem cs_cases (g : A) : cs g J = J ∨ cs g J = cs s J := by
  have hJ' := isComponent_cs hJ s
  have hJg := isComponent_cs hJ g
  rcases hfr.comps_le_two hJ hJ' hJg with h | h | h
  · exact absurd h.symm hs
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem cs_fix (g : A) (h : cs g J = J) : cs g (cs s J) = cs s J := by
  have hJ' := isComponent_cs hJ s
  rcases hfr.comps_le_two hJ hJ' (isComponent_cs hJ' g) with h1 | h1 | h1
  · exact absurd h1.symm hs
  · exfalso
    apply hs
    apply cs_injective g
    rw [h, ← h1]
  · exact h1.symm

theorem cs_swap (g : A) (h : cs g J = cs s J) : cs g (cs s J) = J := by
  have hJ' := isComponent_cs hJ s
  rcases hfr.comps_le_two hJ hJ' (isComponent_cs hJ' g) with h1 | h1 | h1
  · exact absurd h1.symm hs
  · exact h1.symm
  · exfalso
    apply hs
    apply cs_injective g
    rw [h, ← h1]


end Swap

section Central

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem exists_central_c (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) (hZ : center ↥J ≠ ⊥) :
    ∃ c : A, c ∈ J ∧ (∀ j ∈ J, c * j = j * c) ∧ orderOf c = 2 ∧
      ∀ t ∈ Sb ⊓ normalizer (J : Set A), t * c = c * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₀ : Subgroup A := Sb ⊓ normalizer (J : Set A) with hS₀
  set Zs : Subgroup A := (center ↥J).map J.subtype with hZs
  have hZ2 : IsPGroup 2 ↥Zs := (hfr.isPGroup_center_two hJ).map J.subtype
  have hS₀2 : IsPGroup 2 ↥S₀ := hfr.sylow.isPGroup.to_le inf_le_left
  have hZsmem : ∀ x ∈ Zs, x ∈ J ∧ ∀ j ∈ J, x * j = j * x := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, fun j hj => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨j, hj⟩).symm
  have hZsN : ∀ t ∈ S₀, ∀ x ∈ Zs, t * x * t⁻¹ ∈ Zs := by
    intro t ht x hx
    obtain ⟨hxJ, hxc⟩ := hZsmem x hx
    have htN : t ∈ normalizer (J : Set A) := (Subgroup.mem_inf.mp ht).2
    have hconj : ∀ h, h ∈ J ↔ t * h * t⁻¹ ∈ J := fun h => Subgroup.mem_normalizer_iff.mp htN h
    have htJ : t * x * t⁻¹ ∈ J := (hconj x).mp hxJ
    refine ⟨⟨t * x * t⁻¹, htJ⟩, ?_, rfl⟩
    show (⟨t * x * t⁻¹, htJ⟩ : ↥J) ∈ center ↥J
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : A) * (t * x * t⁻¹) = t * x * t⁻¹ * (g : A)
    have hj' : t⁻¹ * (g : A) * t ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) (g : A)).mp g.2
      simpa using this
    calc (g : A) * (t * x * t⁻¹) = t * ((t⁻¹ * (g : A) * t) * x) * t⁻¹ := by group
      _ = t * (x * (t⁻¹ * (g : A) * t)) * t⁻¹ := by rw [← hxc _ hj']
      _ = t * x * t⁻¹ * (g : A) := by group
  have hZsne : Zs ≠ ⊥ := by
    intro h
    apply hZ
    rw [eq_bot_iff]
    intro x hx
    have : (x : A) ∈ Zs := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hS₀N : S₀ ≤ normalizer (Zs : Set A) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hZsN t ht h hh
    · intro hh
      have h1 := hZsN t⁻¹ (inv_mem ht) _ hh
      have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
      rwa [e] at h1
  have hQle : Zs ⊔ S₀ ≤ normalizer (Zs : Set A) := sup_le Subgroup.le_normalizer hS₀N
  have hnormQ : (Zs.subgroupOf (Zs ⊔ S₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hQle
  have hQ2 : IsPGroup 2 ↥(Zs ⊔ S₀) := hZ2.to_sup_of_normal_left' hS₀2 hS₀N
  have hne : Zs.subgroupOf (Zs ⊔ S₀) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZsne
    have : (⟨(x : A), (le_sup_left : Zs ≤ Zs ⊔ S₀) x.2⟩ : ↥(Zs ⊔ S₀)) ∈ Zs.subgroupOf (Zs ⊔ S₀) :=
      Subgroup.mem_subgroupOf.mpr x.2
    rw [h, Subgroup.mem_bot] at this
    exact hx1 (Subtype.ext (congrArg (fun y : ↥(Zs ⊔ S₀) => (y : A)) this))
  obtain ⟨c, hcN, hcc, hc2⟩ := Gen.exists_involution_center_of_normal hQ2 hne
  have hcZ : ((c : ↥(Zs ⊔ S₀)) : A) ∈ Zs := Subgroup.mem_subgroupOf.mp hcN
  obtain ⟨hcJ, hcJc⟩ := hZsmem _ hcZ
  refine ⟨((c : ↥(Zs ⊔ S₀)) : A), hcJ, fun j hj => (hcJc j hj), ?_, fun t ht => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hc2
  · have htQ : t ∈ Zs ⊔ S₀ := (le_sup_right : S₀ ≤ Zs ⊔ S₀) ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcc ⟨t, htQ⟩)

end Central

section SwapMain

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem mem_Sb_of_centralizes (hfr : AFrame A zb Sb Vb) {y : A} (hy2 : orderOf y = 2)
    (hyc : ∀ t ∈ Sb, t * y = y * t) : y ∈ Sb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSb2 : IsPGroup 2 ↥Sb := hfr.sylow.isPGroup
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hy2]
    norm_num
  have hzN : Subgroup.zpowers y ≤ normalizer (Sb : Set A) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : y * h * y⁻¹ = h := by
        rw [← hyc h hh]
        group
      rw [h1]
      exact hh
    · intro hh
      have h1 : y⁻¹ * (y * h * y⁻¹) * y = y * h * y⁻¹ := by
        have := hyc _ hh
        calc y⁻¹ * (y * h * y⁻¹) * y = y⁻¹ * ((y * h * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * h * y⁻¹)) := by rw [← this]
          _ = y * h * y⁻¹ := by group
      have h2 : h = y * h * y⁻¹ := by
        calc h = y⁻¹ * (y * h * y⁻¹) * y := by group
          _ = y * h * y⁻¹ := h1
      rw [h2]
      exact hh
  have hsup : IsPGroup 2 ↥(Sb ⊔ Subgroup.zpowers y) := hSb2.to_sup_of_normal_left' hz2 hzN
  have heq : Sb ⊔ Subgroup.zpowers y = Sb :=
    hfr.sylow.eq_of_le le_sup_left le_top hsup
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

omit [Finite A] in
theorem orderOf_conj_eq (s c : A) : orderOf (s * c * s⁻¹) = orderOf c := by
  have := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective c
  simpa [MulAut.conj_apply] using this

theorem swap_zb (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) (hZ : center ↥J ≠ ⊥)
    {s : A} (hsS : s ∈ Sb) (hs : cs s J ≠ J) :
    (∀ j ∈ J, zb * j = j * zb) ∧ ∀ j ∈ cs s J, zb * j = j * zb := by
  obtain ⟨c, hcJ, hcc, hc2, hcS⟩ := exists_central_c hfr hJ hZ
  have hJ' : IsComponent (cs s J) := isComponent_cs hJ s
  have hne : J ≠ cs s J := fun h => hs h.symm
  have hcomm := Gen.comm_of_ne_components hJ hJ' hne
  set c' : A := s * c * s⁻¹ with hc'
  have hc'J' : c' ∈ cs s J := mem_cs.mpr (by simpa [hc', mul_assoc] using hcJ)
  have hc'cent : ∀ j ∈ cs s J, c' * j = j * c' := by
    intro j hj
    have hj' : s⁻¹ * j * s ∈ J := mem_cs.mp hj
    have h1 := hcc _ hj'
    calc c' * j = s * (c * (s⁻¹ * j * s)) * s⁻¹ := by simp only [hc']; group
      _ = s * ((s⁻¹ * j * s) * c) * s⁻¹ := by rw [h1]
      _ = j * c' := by simp only [hc']; group
  have hc'2 : orderOf c' = 2 := by rw [hc', orderOf_conj_eq]; exact hc2
  have hcc' : c * c' = c' * c := hcomm c hcJ c' hc'J'
  have hssJ : cs (s * s) J = J := by rw [← cs_cs]; exact cs_swap hfr hJ hs s rfl
  have hssS : s * s ∈ Sb ⊓ normalizer (J : Set A) :=
    ⟨Sb.mul_mem hsS hsS, cs_eq_iff_mem_normalizer.mp hssJ⟩
  have hsc' : s * c' * s⁻¹ = c := by
    have h1 := hcS _ hssS
    calc s * c' * s⁻¹ = s * s * c * (s * s)⁻¹ := by simp only [hc']; group
      _ = c * (s * s) * (s * s)⁻¹ := by rw [h1]
      _ = c := by group
  have hsq : ∀ {y : A}, orderOf y = 2 → y * y = 1 := fun {y} hy => by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hne1 : ∀ {y : A}, orderOf y = 2 → y ≠ 1 := fun {y} hy h => by
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  by_cases hcc'' : c = c'
  · have hcent : ∀ t ∈ Sb, t * c = c * t := by
      intro t ht
      by_cases htN : t ∈ normalizer (J : Set A)
      · exact hcS t ⟨ht, htN⟩
      · have hcsJ : cs t J = cs s J := (cs_cases hfr hJ hs t).resolve_left
          (fun h => htN (cs_eq_iff_mem_normalizer.mp h))
        have hu : s⁻¹ * t ∈ normalizer (J : Set A) := by
          rw [← cs_eq_iff_mem_normalizer, ← cs_cs, hcsJ, cs_inv_cs]
        have huS : s⁻¹ * t ∈ Sb := Sb.mul_mem (Sb.inv_mem hsS) ht
        have h1 := hcS _ ⟨huS, hu⟩
        calc t * c = s * (s⁻¹ * t * c) := by group
          _ = s * (c * (s⁻¹ * t)) := by rw [h1]
          _ = (s * c * s⁻¹) * t := by group
          _ = c * t := by rw [← hc', ← hcc'']
    have hcSb : c ∈ Sb := mem_Sb_of_centralizes hfr hc2 hcent
    have hczb : c = zb := hfr.zcen c hcSb hcent hc2
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [← hczb]
      exact hcc j hj
    · rw [← hczb, hcc'']
      exact hc'cent j hj
  · exfalso
    obtain ⟨V, hV, hVmem⟩ := exists_four_of_involutions (hsq hc2) (hsq hc'2) hcc' (hne1 hc2)
      (hne1 hc'2) hcc''
    have hJV : J ≤ centralizer (V : Set A) := by
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rcases hVmem v hv with h | h | h | h <;> rw [h]
      · simp
      · exact hcc j hj
      · exact (hcomm j hj c' hc'J').symm
      · calc c * c' * j = c * (c' * j) := mul_assoc _ _ _
          _ = c * (j * c') := by rw [(hcomm j hj c' hc'J').symm]
          _ = (c * j) * c' := (mul_assoc _ _ _).symm
          _ = (j * c) * c' := by rw [hcc j hj]
          _ = j * (c * c') := mul_assoc _ _ _
    exact hfr.false_of_comp_cent_four hV hJ hJV

theorem pPrimeCore_eq_bot_of_invariant (hfr : AFrame A zb Sb Vb) {E : Subgroup A}
    (hE : ∀ a : A, cs a E = E) : pPrimeCore 2 ↥E = ⊥ := by
  have hEn : E.Normal := ⟨fun x hx a => by
    have : a * x * a⁻¹ ∈ cs a E :=
      mem_cs.mpr (by rw [show a⁻¹ * (a * x * a⁻¹) * a = x by group]; exact hx)
    rwa [hE a] at this⟩
  let O : Subgroup A := (pPrimeCore 2 ↥E).map E.subtype
  have hOn : O.Normal := ⟨by
    rintro _ ⟨y, hy, rfl⟩ a
    refine ⟨MulAut.conjNormal a y, ?_, rfl⟩
    have h := pPrimeCore_map_iso 2 (MulAut.conjNormal a : ↥E ≃* ↥E)
    rw [← h]
    exact ⟨y, hy, rfl⟩⟩
  have hOcop : Nat.Coprime 2 (Nat.card ↥O) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact pPrimeCore_coprime_card
  have hOb : O = ⊥ := (pPrimeCore_eq_bot_iff.mp hfr.core) O hOn hOcop
  rw [eq_bot_iff]
  intro x hx
  have : (x : A) ∈ O := ⟨x, hx, rfl⟩
  rw [hOb, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (Subtype.ext this)

theorem sup_invariant (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) {s : A} (hs : cs s J ≠ J)
    (g : A) : cs g (J ⊔ cs s J) = J ⊔ cs s J := by
  have hmap : cs g (J ⊔ cs s J) = cs g J ⊔ cs g (cs s J) := Subgroup.map_sup _ _ _
  rw [hmap]
  rcases cs_cases hfr hJ hs g with h | h
  · rw [h, cs_fix hfr hJ hs g h]
  · rw [h, cs_swap hfr hJ hs g h, sup_comm]

theorem card_dvd_factorial_of_centralizes (hfr : AFrame A zb Sb Vb) {R : Subgroup A}
    (hR : R ≤ centralizer ({zb} : Set A)) (hbot : pPrimeCore 2 ↥R = ⊥) :
    Nat.card ↥R ∣ Nat.factorial 11 := by
  obtain ⟨n, K, instK, R', hn, hcov, ⟨e⟩⟩ := hfr.cbar zb hfr.zb_ord R hR
  obtain ⟨hKq, hZ, ⟨eK⟩⟩ := hcov
  have hKcard : Nat.card K = Nat.factorial n := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
    rw [hZ, Nat.card_congr eK.toEquiv] at h
    have h2 : 2 * Nat.card ↥(alternatingGroup (Fin n)) = Nat.factorial n := by
      have hn' : Nontrivial (Fin n) := by rcases hn with rfl | rfl <;> infer_instance
      have := two_mul_nat_card_alternatingGroup (α := Fin n)
      have h3 : Nat.card (Fin n) = n := by simp
      rw [Nat.card_perm, h3] at this
      exact this
    omega
  have hq1 : Nat.card ↥(pPrimeCore 2 ↥R) = 1 := by rw [hbot]; exact Subgroup.card_bot
  have hRq : Nat.card ↥R = Nat.card (↥R ⧸ pPrimeCore 2 ↥R) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥R)
    rw [hq1, mul_one] at h
    exact h
  have h1 : Nat.card ↥R ∣ Nat.card K := by
    rw [hRq, Nat.card_congr e.toEquiv]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card R')
  rw [hKcard] at h1
  refine h1.trans (Nat.factorial_dvd_factorial ?_)
  rcases hn with rfl | rfl <;> norm_num

theorem swap_card_sq (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) (hZ : center ↥J ≠ ⊥)
    (hns : ¬ Sb ≤ normalizer (J : Set A)) :
    (Nat.card (↥J ⧸ center ↥J)) ^ 2 ∣ Nat.factorial 11 := by
  obtain ⟨s, hsS, hsN⟩ := Set.not_subset.mp hns
  have hs : cs s J ≠ J := fun h => hsN (cs_eq_iff_mem_normalizer.mp h)
  obtain ⟨hzJ, hzJ'⟩ := swap_zb hfr hJ hZ hsS hs
  have hJ' : IsComponent (cs s J) := isComponent_cs hJ s
  have hcomm : ∀ a ∈ cs s J, ∀ b ∈ J, a * b = b * a := Gen.comm_of_ne_components hJ' hJ hs
  have hEbot : pPrimeCore 2 ↥(J ⊔ cs s J) = ⊥ :=
    pPrimeCore_eq_bot_of_invariant hfr (sup_invariant hfr hJ hs)
  have hEzb : J ⊔ cs s J ≤ centralizer ({zb} : Set A) := by
    refine sup_le (fun j hj => ?_) (fun j hj => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hzJ j hj).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hzJ' j hj).symm
  have hEdvd := card_dvd_factorial_of_centralizes hfr hEzb hEbot
  obtain ⟨hprod, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute J (cs s J)
    (fun x hx y hy => (hcomm y hy x hx).symm)
  have hcsJ : Nat.card ↥(cs s J) = Nat.card ↥J :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hinfle : J ⊓ cs s J ≤ (center ↥J).map J.subtype := by
    intro x hx
    obtain ⟨hxJ, hxJ'⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
    show (⟨x, hxJ⟩ : ↥J) ∈ center ↥J
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hcomm x hxJ' g g.2).symm
  have hmdvd : Nat.card ↥(J ⊓ cs s J) ∣ Nat.card ↥(center ↥J) := by
    have := Subgroup.card_dvd_of_le hinfle
    rwa [Subgroup.card_map_of_injective J.subtype_injective] at this
  have hJcard : Nat.card ↥J = Nat.card (↥J ⧸ center ↥J) * Nat.card ↥(center ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥J)
  obtain ⟨k, hk⟩ := hmdvd
  have hm0 : 0 < Nat.card ↥(J ⊓ cs s J) := Nat.card_pos
  set a := Nat.card (↥J ⧸ center ↥J) with ha
  set m := Nat.card ↥(J ⊓ cs s J) with hm
  have hEeq : Nat.card ↥(J ⊔ cs s J) = a ^ 2 * (m * k ^ 2) := by
    apply Nat.eq_of_mul_eq_mul_right hm0
    rw [hprod, hcsJ, hJcard, hk]
    ring
  have : a ^ 2 ∣ Nat.card ↥(J ⊔ cs s J) := ⟨m * k ^ 2, hEeq⟩
  exact this.trans hEdvd

end SwapMain

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
