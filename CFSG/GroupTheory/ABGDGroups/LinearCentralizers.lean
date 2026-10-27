module

public import Mathlib
public import CFSG.GroupTheory.ABGDGroups.LinearOddCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicIndexTwoSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import Certificates.Certificate1
public import Certificates.Certificate2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower pGammaL2PSLRange
  pGammaL2PGLRange mem_pGammaL2PSLRange_iff)

section General

variable {G G' : Type*} [Group G] [Group G']

theorem map_inf_centralizer_of_injective (f : G →* G') (hf : Function.Injective f)
    (A : Subgroup G) (x : G) :
    (A ⊓ Subgroup.centralizer ({x} : Set G)).map f =
      A.map f ⊓ Subgroup.centralizer ({f x} : Set G') := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨a, ⟨ha, hax⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, by rw [← map_mul, hax, map_mul]⟩
  · rintro ⟨⟨a, ha, rfl⟩, h⟩
    exact ⟨a, ⟨ha, hf (by rw [map_mul, h, map_mul])⟩, rfl⟩

theorem nonempty_mulEquiv_dihedral_of_reflected [Finite G] {T : Subgroup G} [hT : IsCyclic T]
    {s : G} (hsT : s ∉ T) (hs : s * s = 1) (hinv : ∀ x ∈ T, s * x * s⁻¹ = x⁻¹) :
    Nonempty ((T ⊔ Subgroup.zpowers s : Subgroup G) ≃* DihedralGroup (Nat.card T)) := by
  obtain ⟨⟨g, hgT⟩, hg⟩ := hT.exists_generator
  have hTg : T = Subgroup.zpowers g := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact hgT
  set C := T ⊔ Subgroup.zpowers s with hCdef
  let ρ : C := ⟨g, Subgroup.mem_sup_left hgT⟩
  let σ : C := ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩
  have hgen : (⊤ : Subgroup C) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    change C = Subgroup.zpowers g ⊔ Subgroup.zpowers s
    rw [hCdef, ← hTg]
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simp [σ, sq, hs])
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by simpa [ρ, σ] using hinv g hgT)
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hsT
    have h' : g ^ k = s := by
      have h'' := congrArg Subtype.val hk
      simpa only [SubgroupClass.coe_zpow] using h''
    rw [← h']
    exact T.zpow_mem hgT k
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hord : orderOf ρ = Nat.card T := by
    rw [Subgroup.orderOf_mk, hTg, Nat.card_zpowers]
  exact hord ▸ ⟨e⟩

theorem exists_mul_sq_eq_one_of_dihedral {m : ℕ} (hm : 4 ∣ m) (hm0 : m ≠ 0) {D : Subgroup G}
    (e : DihedralGroup m ≃* D) {x : G} (hxD : x ∈ Subgroup.normalizer (D : Set G)) (i : ZMod m)
    (hxσ : x * (e (DihedralGroup.sr i) : G) = (e (DihedralGroup.sr i) : G) * x)
    (hx2 : x ^ 2 = (e (DihedralGroup.r ((m / 2 : ℕ) : ZMod m)) : G)) :
    ∃ d ∈ D, (x * d) ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have hk0 : k ≠ 0 := by rintro rfl; exact hm0 rfl
  have : NeZero (4 * k) := ⟨hm0⟩
  set f : DihedralGroup (4 * k) →* G := D.subtype.comp e.toMonoidHom with hfdef
  have hf : Function.Injective f := D.subtype_injective.comp e.injective
  have hfD : ∀ a, f a ∈ D := fun a => (e a).2
  have hfe : ∀ a, (e a : G) = f a := fun a => rfl
  set c : ZMod (4 * k) := (k : ZMod (4 * k)) with hc
  have hm2 : ((4 * k / 2 : ℕ) : ZMod (4 * k)) = c + c := by
    rw [show 4 * k / 2 = k + k by omega, Nat.cast_add]
  have h4 : c + c + c + c = 0 := by
    have h := ZMod.natCast_self (4 * k)
    push_cast at h
    rw [hc]
    linear_combination h
  have h2ne : c + c ≠ 0 := by
    intro h
    have h' : ((k + k : ℕ) : ZMod (4 * k)) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by omega) h'
    omega
  set ρ := f (DihedralGroup.r c)
  set σ := f (DihedralGroup.sr i)
  set z := f (DihedralGroup.r (c + c))
  have hx2' : x ^ 2 = z := by rw [hx2, hfe, hm2]
  have hxz : x * z = z * x := by rw [← hx2', ← pow_succ, ← pow_succ']
  have hρ2 : ρ * ρ = z := by rw [← map_mul, DihedralGroup.r_mul_r]
  have hzz : z * z = 1 := by
    rw [← map_mul, DihedralGroup.r_mul_r, show c + c + (c + c) = c + c + c + c by ring, h4,
      DihedralGroup.r_zero, map_one]
  have hy : x⁻¹ * ρ * x ∈ D := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxD) ρ).mp (hfD _)
    rwa [inv_inv] at h
  obtain ⟨a, ha⟩ : ∃ a, f a = x⁻¹ * ρ * x := ⟨e.symm ⟨_, hy⟩, by simp [f]⟩
  have hya : f (a * a) = z := by
    rw [map_mul, ha]
    calc x⁻¹ * ρ * x * (x⁻¹ * ρ * x) = x⁻¹ * (ρ * ρ) * x := by group
      _ = x⁻¹ * (z * x) := by rw [hρ2, mul_assoc]
      _ = z := by rw [← hxz]; group
  rcases a with j | j
  · rw [DihedralGroup.r_mul_r] at hya
    have hj : j + j = c + c := DihedralGroup.r.inj (hf hya)
    have hjc : -(j - c) = j - c := by linear_combination -hj
    rcases (ZMod.neg_eq_self_iff _).mp hjc with h | h
    ·
      have hjc' : j = c := by linear_combination h
      subst hjc'
      have hxρ : ρ * x = x * ρ := by
        have h' : x * (x⁻¹ * ρ * x) = x * ρ := by rw [← ha]
        rwa [show x * (x⁻¹ * ρ * x) = ρ * x by group] at h'
      refine ⟨ρ, hfD _, ?_⟩
      calc (x * ρ) ^ 2 = x * (ρ * x) * ρ := by rw [sq]; group
        _ = x ^ 2 * (ρ * ρ) := by rw [hxρ, sq]; group
        _ = 1 := by rw [hx2', hρ2, hzz]
    ·
      have hjv : j - c = c + c := by
        rw [← ZMod.natCast_zmod_val (j - c), show (j - c).val = k + k by omega, Nat.cast_add]
      have hj3 : j = -c := by linear_combination hjv + h4
      subst hj3
      have hxρ : ρ * x = x * ρ⁻¹ := by
        have h' : x * (x⁻¹ * ρ * x) = x * f (DihedralGroup.r (-c)) := by rw [← ha]
        rw [show x * (x⁻¹ * ρ * x) = ρ * x by group, ← DihedralGroup.inv_r, map_inv] at h'
        exact h'
      have hσρ : σ * ρ⁻¹ * σ * ρ = z := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, DihedralGroup.inv_r,
          DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r]
        congr 2
        ring
      have hxσ' : x * σ = σ * x := hxσ
      refine ⟨σ * ρ, Subgroup.mul_mem _ (hfD _) (hfD _), ?_⟩
      calc (x * (σ * ρ)) ^ 2 = x * σ * (ρ * x) * σ * ρ := by rw [sq]; group
        _ = x * (σ * x) * ρ⁻¹ * σ * ρ := by rw [hxρ]; group
        _ = x ^ 2 * (σ * ρ⁻¹ * σ * ρ) := by rw [← hxσ', sq]; group
        _ = 1 := by rw [hσρ, hx2', hzz]
  · rw [DihedralGroup.sr_mul_self] at hya
    have h := hf (show f 1 = f (DihedralGroup.r (c + c)) from hya)
    rw [DihedralGroup.one_def] at h
    exact (h2ne (DihedralGroup.r.inj h).symm).elim

end General

section Involutions

variable {F : Type} [Field F] [Finite F]

theorem psl2_centralizer_involution_dihedral (hF : IsOddPrimePower (Nat.card F)) {ε : ℤ}
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1) {t : PSL2 F}
    (ht : orderOf t = 2) :
    ∃ m : ℕ, (2 * m : ℤ) = Nat.card F - ε ∧
      Nonempty (Subgroup.centralizer ({t} : Set (PSL2 F)) ≃* DihedralGroup m) := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have htI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution t :=
    ⟨ht1, by have h := pow_orderOf_eq_one t; rwa [ht] at h⟩
  obtain ⟨T, s, hTcyc, -, hsI, hsT, hinv, hC, heven, hcard⟩ :=
    CFSG.GorensteinWalter.psl2_reflected_torus_card hF htI
  have hqodd : Odd (Nat.card F) := by
    obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
    rw [hq]
    exact hpodd.pow
  have : IsCyclic T := hTcyc
  obtain ⟨e⟩ := nonempty_mulEquiv_dihedral_of_reflected hsT
    (by have h := hsI.2; rwa [sq] at h) hinv
  refine ⟨Nat.card T, ?_, ⟨(MulEquiv.subgroupCongr hC).trans e⟩⟩
  obtain ⟨j, hj⟩ := heven
  obtain ⟨a, ha⟩ := hqodd
  unfold Int.ModEq at hε
  rcases hε1 with rfl | rfl <;> rcases hcard with h | h <;> omega

theorem pgl2_inf_centralizer_outer_involution_dihedral (hF : IsOddPrimePower (Nat.card F))
    {ε : ℤ} (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1) {g : PGL2 F}
    (hg : orderOf g = 2)
    (hgJ : g ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    ∃ m : ℕ, (2 * m : ℤ) = Nat.card F + ε ∧
      Nonempty (↥((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ⊓
        Subgroup.centralizer ({g} : Set (PGL2 F))) ≃* DihedralGroup m) := by
  classical
  set J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hJdef
  have hJindex : J.index = 2 := CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJindex
  have hqodd : Odd (Nat.card F) := by
    obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
    rw [hq]
    exact hpodd.pow
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact absurd hg (by norm_num)
  have hgI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution g :=
    ⟨hg1, by have h := pow_orderOf_eq_one g; rwa [hg] at h⟩
  by_cases h3 : Nat.card F = 3
  ·
    have hε' : ε = -1 := by
      unfold Int.ModEq at hε
      rw [h3] at hε
      rcases hε1 with rfl | rfl
      · norm_num at hε
      · rfl
    refine ⟨1, by rw [hε', h3]; norm_num, ?_⟩
    let : Fintype F := Fintype.ofFinite F
    have hFcard : Fintype.card F = 3 := by rwa [← Nat.card_eq_fintype_card]
    let eK : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hFcard
    let E : PGL2 F ≃* Equiv.Perm (Fin 4) :=
      (CFSG.GorensteinWalter.pgl2RingEquiv eK).symm.trans
        CFSG.GorensteinWalter.pgl2_three_equiv_perm
    have hJE : J.map E.toMonoidHom = alternatingGroup (Fin 4) := by
      apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
      exact (Subgroup.index_map_equiv J E).trans hJindex
    set π := E g
    have hπ2 : π ^ 2 = 1 := by
      have h := pow_orderOf_eq_one g
      rw [hg] at h
      rw [← map_pow, h, map_one]
    have hπA : Equiv.Perm.sign π ≠ 1 := by
      intro h
      apply hgJ
      have hπ : π ∈ J.map E.toMonoidHom := by rw [hJE]; exact h
      obtain ⟨g', hg', hgg'⟩ := hπ
      rwa [← E.injective hgg']
    have hmap := map_inf_centralizer_of_injective E.toMonoidHom E.injective J g
    rw [hJE] at hmap
    have hcard : Nat.card ↥(J ⊓ Subgroup.centralizer ({g} : Set (PGL2 F))) = 2 := by
      rw [← Subgroup.card_map_of_injective (f := E.toMonoidHom) E.injective, hmap]
      have hP : ∀ y : Equiv.Perm (Fin 4), y ∈ alternatingGroup (Fin 4) ⊓
          Subgroup.centralizer ({E.toMonoidHom g} : Set (Equiv.Perm (Fin 4))) ↔
          Equiv.Perm.sign y = 1 ∧ y * π = π * y := fun y => by
        rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup,
          Subgroup.mem_centralizer_singleton_iff]
        rfl
      rw [Nat.card_congr (Equiv.subtypeEquivRight hP), Nat.card_eq_fintype_card,
        Fintype.card_subtype]
      have key : ∀ π' : Equiv.Perm (Fin 4), π' ^ 2 = 1 → Equiv.Perm.sign π' ≠ 1 →
          (Finset.univ.filter (fun y : Equiv.Perm (Fin 4) =>
            Equiv.Perm.sign y = 1 ∧ y * π' = π' * y)).card = 2 := by
        decide +kernel
      exact key π hπ2 hπA
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨mulEquivOfPrimeCardEq hcard (by rw [DihedralGroup.nat_card])⟩
  · have h3' : 3 < Nat.card F := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      obtain ⟨a, ha⟩ := hqodd
      omega
    have hJc : commutator (PGL2 F) = J :=
      CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F hF h3'
    obtain ⟨U, s, t, w, hUcyc, hUhalf, hUcard, hsU, hsJ, hs1, hss, htJ, htU, htt, htinv, htw, hwU,
      hww, hwinv, hcent⟩ := CFSG.GorensteinWalter.pgl2_low_two_part_torus_reflection_data F hF h3'
    rw [hJc] at hsJ htJ
    have hUeven : Nat.card U = 2 * (Nat.card U / 2) := by
      obtain ⟨a, ha⟩ := hqodd
      rcases hUcard with h | h <;> omega
    obtain ⟨D, hDdef, hDJ, -, hDcard, ⟨eD⟩⟩ :=
      CFSG.GorensteinWalter.exists_dihedral_subgroup_le_index_two_of_reflected_cyclic J U hJindex
        hUcyc (Nat.card U / 2) hUeven (fun h => hsJ (h hsU)) t htJ htU htt htinv
    have hCs : Nat.card (Subgroup.centralizer ({s} : Set (PGL2 F))) = Nat.card U * 2 := by
      rw [hcent]
      exact card_sup_zpowers_of_inverts hwU hww hwinv
    have hrel : J.relIndex (Subgroup.centralizer ({s} : Set (PGL2 F))) = 2 := by
      have hdvd := Subgroup.relIndex_dvd_index_of_normal J
        (Subgroup.centralizer ({s} : Set (PGL2 F)))
      rw [hJindex] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd ((Subgroup.relIndex_eq_one.mp h)
          (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hsJ
      · exact h
    have hJC := Subgroup.relIndex_mul_card (H := J) (K := Subgroup.centralizer ({s} : Set (PGL2 F)))
    rw [hrel, hCs] at hJC
    have hDle : D ≤ J ⊓ Subgroup.centralizer ({s} : Set (PGL2 F)) := by
      refine le_inf hDJ ?_
      rw [hDdef, hcent]
      refine sup_le (inf_le_left.trans le_sup_left) ?_
      rw [Subgroup.zpowers_le]
      rcases htw with rfl | rfl
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_left hsU)
    have hDeq : D = J ⊓ Subgroup.centralizer ({s} : Set (PGL2 F)) :=
      Subgroup.eq_of_le_of_card_ge hDle (by
        rw [hDcard]
        exact (Nat.eq_of_mul_eq_mul_left (by norm_num) (hJC.trans (mul_comm _ _))).le)
    have hsI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s := ⟨hs1, by rw [sq]; exact hss⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp (CFSG.GorensteinWalter.pgl2_outer_involutions_conjugate F hF
      h3' hgI hsI (by rwa [hJc]) (by rwa [hJc]))
    have hmap := map_inf_centralizer_of_injective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective J g
    rw [map_conj_eq_of_normal hJn, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc] at hmap
    refine ⟨Nat.card U / 2, ?_, ⟨((Subgroup.equivMapOfInjective _ _ (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr (hmap.trans hDeq.symm))).trans eD⟩⟩
    obtain ⟨a, ha⟩ := hqodd
    obtain ⟨b, hb⟩ := hUhalf
    unfold Int.ModEq at hε
    rcases hε1 with rfl | rfl <;> rcases hUcard with h | h <;> omega

end Involutions

namespace IsLinearDecomposition

variable {H : Type} [Group H] [Finite H] {F : Type} [Field F] [Finite F] {ι : H →* PGammaL2 F}
  {L E : Subgroup H} {S : Sylow 2 H}

omit [Finite H] in
private theorem mem_of_orderOf_eq_two [Finite H] (hd : IsLinearDecomposition ι L E S) {x : H}
    (hx : orderOf x = 2) : x ∈ L := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  exact hd.sylow_le P (hP (Subgroup.mem_zpowers x))

omit [Finite H] in
theorem centralizer_dihedral_of_mem_linearCore (hd : IsLinearDecomposition ι L E S)
    {ε : ℤ} (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1)
    {x : H} (hx : orderOf x = 2) (hxL : x ∈ linearCore ι) :
    ∃ m : ℕ, (2 * m : ℤ) = Nat.card F - ε ∧
      Nonempty (↥(linearCore ι ⊓ Subgroup.centralizer ({x} : Set H)) ≃* DihedralGroup m) := by
  have hF := hd.isOddPrimePower_card
  set f' : PSL2 F →* PGammaL2 F := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) with hf'def
  have hf' : Function.Injective f' :=
    SemidirectProduct.inl_injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  obtain ⟨x', hx'⟩ := (mem_pGammaL2PSLRange_iff F _).mp (show ι x ∈ pGammaL2PSLRange F from hxL)
  have hx'' : f' x' = ι x := hx'
  have hx'2 : orderOf x' = 2 := by
    rw [← orderOf_injective f' hf' x', hx'', orderOf_injective ι hd.injective, hx]
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_centralizer_involution_dihedral hF hε hε1 hx'2
  have hmap : (linearCore ι ⊓ Subgroup.centralizer ({x} : Set H)).map ι =
      (⊤ ⊓ Subgroup.centralizer ({x'} : Set (PSL2 F))).map f' := by
    rw [map_inf_centralizer_of_injective ι hd.injective, hd.map_linearCore,
      map_inf_centralizer_of_injective f' hf', hx'', ← MonoidHom.range_eq_map]
    rfl
  refine ⟨m, hm, ⟨((Subgroup.equivMapOfInjective _ ι hd.injective).trans
    (MulEquiv.subgroupCongr hmap)).trans
    (((Subgroup.equivMapOfInjective _ f' hf').symm.trans
      (MulEquiv.subgroupCongr (top_inf_eq _))).trans e)⟩⟩

theorem centralizer_dihedral_of_not_mem_linearCore (hd : IsLinearDecomposition ι L E S)
    {ε : ℤ} (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1)
    {x : H} (hx : orderOf x = 2) (hxL : x ∉ linearCore ι) :
    ∃ m : ℕ, (2 * m : ℤ) = Nat.card F + ε ∧
      Nonempty (↥(linearCore ι ⊓ Subgroup.centralizer ({x} : Set H)) ≃* DihedralGroup m) := by
  have hF := hd.isOddPrimePower_card
  have hxP : ι x ∈ pGammaL2PGLRange F :=
    hd.isStandardLayer.mem_pGLRange_of_orderOf_eq_two hF ⟨x, hd.mem_of_orderOf_eq_two hx, rfl⟩
      (by rw [orderOf_injective ι hd.injective, hx])
  obtain ⟨g, hg⟩ := hxP
  have hgJ : g ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    rintro ⟨y, hy⟩
    apply hxL
    change ι x ∈ pGammaL2PSLRange F
    rw [← hg, ← hy]
    exact ⟨y, rfl⟩
  have hg2 : orderOf g = 2 := by
    rw [← orderOf_injective (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
      SemidirectProduct.inl_injective g, hg,
      orderOf_injective ι hd.injective, hx]
  obtain ⟨m, hm, ⟨e⟩⟩ := pgl2_inf_centralizer_outer_involution_dihedral hF hε hε1 hg2 hgJ
  have hmap : (linearCore ι ⊓ Subgroup.centralizer ({x} : Set H)).map ι =
      ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ⊓
        Subgroup.centralizer ({g} : Set (PGL2 F))).map SemidirectProduct.inl := by
    rw [map_inf_centralizer_of_injective ι hd.injective, hd.map_linearCore, ← hg,
      map_inf_centralizer_of_injective _ SemidirectProduct.inl_injective, pGammaL2PSLRange,
      MonoidHom.range_comp]
  exact ⟨m, hm, ⟨((Subgroup.equivMapOfInjective _ ι hd.injective).trans
    (MulEquiv.subgroupCongr hmap)).trans
    ((Subgroup.equivMapOfInjective _ _ SemidirectProduct.inl_injective).symm.trans e)⟩⟩

private theorem odd_sq_mod_eight {a : ℕ} (ha : Odd a) : a ^ 2 % 8 = 1 := by
  obtain ⟨b, rfl⟩ := ha
  obtain ⟨c, hc⟩ := Nat.even_mul_succ_self b
  have h : (2 * b + 1) ^ 2 = 4 * (b * (b + 1)) + 1 := by ring
  rw [h, hc]
  omega

theorem centralizer_kleinFour
    (hd : IsLinearDecomposition ι L E S) {T : Subgroup H}
    (hT : IsKleinFour T) (hTS : T ≤ S) :
    Subgroup.centralizer (T : Set H) = T ⊔ E ∧ L ⊓ Subgroup.centralizer (T : Set H) = T := by
  classical
  have hF := hd.isOddPrimePower_card
  have hTL : T ≤ L := hTS.trans (hd.sylow_le S)
  have hTsq : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => by
    have h := Monoid.pow_exponent_eq_one (⟨t, ht⟩ : T)
    rw [hT.exponent_two] at h
    simpa using congrArg Subtype.val h
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => by
    have h1 := hTsq _ (T.mul_mem ha hb)
    have h2 := hTsq a ha
    have h3 := hTsq b hb
    rw [sq] at h1 h2 h3
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [h2, h3, one_mul, mul_one]
  have hTC : T ≤ Subgroup.centralizer (T : Set H) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => hTcomm u hu t ht
  have hT2 : ∀ t ∈ T, t ≠ 1 → orderOf t = 2 := fun t ht ht1 => orderOf_eq_prime (hTsq t ht) ht1
  have hTP : T.map ι ≤ pGammaL2PGLRange F := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases ht1 : t = 1
    · rw [ht1, map_one]
      exact Subgroup.one_mem _
    exact hd.isStandardLayer.mem_pGLRange_of_orderOf_eq_two hF ⟨t, hTL ht, rfl⟩
      (by rw [orderOf_injective ι hd.injective, hT2 t ht ht1])
  set T₁ := (T.map ι).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  let eT : T₁ ≃* T :=
    (((T.map ι).comap SemidirectProduct.inl).equivMapOfInjective _
      SemidirectProduct.inl_injective).trans
      ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hTP)).trans
        (T.equivMapOfInjective ι hd.injective).symm)
  have hT₁ : IsKleinFour T₁ :=
    ⟨by rw [Nat.card_congr eT.toEquiv]; exact hT.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv eT]; exact hT.exponent_two⟩
  have hCT₁ := CFSG.GorensteinWalter.pgl2_kleinFour_centralizer_eq_self F hF T₁ hT₁
  have hA : ∀ y ∈ L ⊓ Subgroup.centralizer (T : Set H), ι y ∈ pGammaL2PGLRange F → y ∈ T := by
    rintro y ⟨-, hyC⟩ ⟨g, hg⟩
    have hg' : g ∈ Subgroup.centralizer (T₁ : Set (PGL2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro t₁ ⟨t, ht, htt⟩
      have hinl : Function.Injective (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) :=
        SemidirectProduct.inl_injective
      apply hinl
      rw [map_mul, map_mul, ← htt, hg, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_iff.mp hyC t ht]
    rw [hCT₁] at hg'
    obtain ⟨t, ht, htt⟩ := hg'
    rwa [← hd.injective (htt.trans hg)]
  have hB : ∀ y ∈ L ⊓ Subgroup.centralizer (T : Set H), ι y ∈ pGammaL2PGLRange F := by
    rintro y ⟨hyL, hyC⟩
    rcases hd.map_eq with hPSL | hPGL | hstar
    · exact pGammaL2PSLRange_le_pGLRange (hPSL ▸ ⟨y, hyL, rfl⟩)
    · exact hPGL ▸ ⟨y, hyL, rfl⟩
    by_contra hyP
    have hιL : ι y ∈ pGammaL2PGLStar F := hstar ▸ ⟨y, hyL, rfl⟩
    have hyL₀ : y ∉ linearCore ι := fun h => hyP (pGammaL2PSLRange_le_pGLRange h)
    have hinvL : ∀ w ∈ L, orderOf w = 2 → w ∈ linearCore ι := fun w hw h2 =>
      mem_pGammaL2PSLRange_of_mem_pGLStar hF (hstar ▸ ⟨w, hw, rfl⟩)
        (by rw [orderOf_injective ι hd.injective, h2])
    have hy2L₀ : y ^ 2 ∈ linearCore ι := by
      change ι (y ^ 2) ∈ pGammaL2PSLRange F
      rw [map_pow]
      exact sq_mem_pGammaL2PSLRange hF hιL.1
    have hy2T : y ^ 2 ∈ T := hA (y ^ 2) ⟨L.pow_mem hyL 2, Subgroup.pow_mem _ hyC 2⟩
      (pGammaL2PSLRange_le_pGLRange hy2L₀)
    have hy1 : y ≠ 1 := fun h => hyL₀ (h ▸ Subgroup.one_mem _)
    have hy2 : y ^ 2 ≠ 1 := fun h => hyL₀ (hinvL y hyL (orderOf_eq_prime h hy1))
    set t₀ := y ^ 2 with ht₀def
    have ht₀ : orderOf t₀ = 2 := hT2 t₀ hy2T hy2
    have hq8 : Nat.card F % 8 = 1 := by
      obtain ⟨p, f, hp, hpodd, -, hq⟩ := hF
      have hσ : (ι y).right ≠ 1 := fun h => hyP (by
        rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
        exact h)
      have hord : orderOf (ι y).right = 2 := orderOf_eq_prime hιL.1 hσ
      have hdvd : 2 ∣ f := by
        have h := orderOf_dvd_natCard (ι y).right
        rwa [hord, CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card F hp hq] at h
      obtain ⟨c, rfl⟩ := hdvd
      rw [hq, pow_mul, ← pow_mul, mul_comm, pow_mul]
      exact odd_sq_mod_eight hpodd.pow
    have hε : (Nat.card F : ℤ) ≡ 1 [ZMOD 4] := by
      unfold Int.ModEq
      omega
    obtain ⟨m, hm, ⟨eD⟩⟩ := hd.centralizer_dihedral_of_mem_linearCore hε (Or.inl rfl) ht₀ hy2L₀
    have hm4 : 4 ∣ m := by omega
    have hm0 : m ≠ 0 := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      omega
    have : NeZero m := ⟨hm0⟩
    set D := linearCore ι ⊓ Subgroup.centralizer ({t₀} : Set H) with hDdef
    have hTD : T ≤ D := fun u hu => by
      refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr (hTcomm u hu t₀ hy2T)⟩
      by_cases hu1 : u = 1
      · rw [hu1]
        exact Subgroup.one_mem _
      exact hinvL u (hTL hu) (hT2 u hu hu1)
    have h2m : ∀ j : ZMod m, DihedralGroup.r j * DihedralGroup.r j = 1 →
        j = 0 ∨ j = ((m / 2 : ℕ) : ZMod m) := fun j hj => by
      rw [DihedralGroup.r_mul_r, DihedralGroup.one_def] at hj
      have hj' : -j = j := by linear_combination -(DihedralGroup.r.inj hj)
      rcases (ZMod.neg_eq_self_iff j).mp hj' with h | h
      · exact Or.inl h
      · right
        rw [← ZMod.natCast_zmod_val j, show j.val = m / 2 by omega]
    have hrz : eD ⟨t₀, hTD hy2T⟩ = DihedralGroup.r ((m / 2 : ℕ) : ZMod m) := by
      have hc : ∀ a : DihedralGroup m, eD ⟨t₀, hTD hy2T⟩ * a = a * eD ⟨t₀, hTD hy2T⟩ := by
        intro a
        obtain ⟨d, rfl⟩ := eD.surjective a
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_singleton_iff.mp d.2.2).symm
      rcases h : eD ⟨t₀, hTD hy2T⟩ with j | j
      · have h1 := hc (DihedralGroup.sr 0)
        rw [h, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h1
        have h2 : DihedralGroup.r j * DihedralGroup.r j = 1 := by
          rw [← h, ← map_mul, ← map_one eD]
          congr 1
          apply Subtype.ext
          change t₀ * t₀ = 1
          rw [← sq]
          exact hTsq t₀ hy2T
        rcases h2m j h2 with rfl | hj
        · exfalso
          apply hy2
          have : eD ⟨t₀, hTD hy2T⟩ = eD 1 := by rw [h, map_one, DihedralGroup.one_def]
          exact congrArg Subtype.val (eD.injective this)
        · rw [hj]
      · exfalso
        have h1 := hc (DihedralGroup.r 1)
        rw [h, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at h1
        have h2 : (2 : ZMod m) = 0 := by linear_combination DihedralGroup.sr.inj h1
        have h3 : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h2
        rw [ZMod.natCast_eq_zero_iff] at h3
        have := Nat.le_of_dvd (by norm_num) h3
        omega
    obtain ⟨u, huT, hu1, hut⟩ : ∃ u ∈ T, u ≠ 1 ∧ u ≠ t₀ := by
      by_contra h
      push Not at h
      have hle : T ≤ Subgroup.zpowers t₀ := fun u hu => by
        by_cases hu1 : u = 1
        · rw [hu1]
          exact Subgroup.one_mem _
        rw [h u hu hu1]
        exact Subgroup.mem_zpowers t₀
      have := Subgroup.card_le_of_le hle
      rw [hT.card_four, Nat.card_zpowers, ht₀] at this
      omega
    obtain ⟨i, hi⟩ : ∃ i : ZMod m, eD ⟨u, hTD huT⟩ = DihedralGroup.sr i := by
      rcases h : eD ⟨u, hTD huT⟩ with j | j
      · exfalso
        have h2 : DihedralGroup.r j * DihedralGroup.r j = 1 := by
          rw [← h, ← map_mul, ← map_one eD]
          congr 1
          apply Subtype.ext
          change u * u = 1
          rw [← sq]
          exact hTsq u huT
        rcases h2m j h2 with rfl | hj
        · apply hu1
          have : eD ⟨u, hTD huT⟩ = eD 1 := by rw [h, map_one, DihedralGroup.one_def]
          exact congrArg Subtype.val (eD.injective this)
        · apply hut
          have : eD ⟨u, hTD huT⟩ = eD ⟨t₀, hTD hy2T⟩ := by rw [h, hrz, hj]
          exact congrArg Subtype.val (eD.injective this)
      · exact ⟨j, rfl⟩
    have hyN : y ∈ Subgroup.normalizer (D : Set H) := by
      apply Subgroup.mem_normalizer_fintype
      rintro d ⟨hdL, hdC'⟩
      have hdC : d * t₀ = t₀ * d := Subgroup.mem_centralizer_singleton_iff.mp hdC'
      refine ⟨hd.linearCore_normal.conj_mem d hdL y, ?_⟩
      change y * d * y⁻¹ ∈ Subgroup.centralizer ({t₀} : Set H)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyt : y * t₀ = t₀ * y := by rw [ht₀def, ← pow_succ', ← pow_succ]
      have hyt' : y⁻¹ * t₀ = t₀ * y⁻¹ := by
        calc y⁻¹ * t₀ = y⁻¹ * (t₀ * y) * y⁻¹ := by
              rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
          _ = y⁻¹ * (y * t₀) * y⁻¹ := by rw [hyt]
          _ = t₀ * y⁻¹ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      calc y * d * y⁻¹ * t₀ = y * d * (t₀ * y⁻¹) := by rw [mul_assoc, hyt']
        _ = y * (t₀ * d) * y⁻¹ := by rw [← hdC]; simp only [mul_assoc]
        _ = t₀ * y * d * y⁻¹ := by rw [← hyt]; simp only [mul_assoc]
        _ = t₀ * (y * d * y⁻¹) := by simp only [mul_assoc]
    have hσ : y * (eD.symm (DihedralGroup.sr i) : H) = (eD.symm (DihedralGroup.sr i) : H) * y := by
      rw [← hi, MulEquiv.symm_apply_apply]
      exact (Subgroup.mem_centralizer_iff.mp hyC u huT).symm
    have hz : y ^ 2 = (eD.symm (DihedralGroup.r ((m / 2 : ℕ) : ZMod m)) : H) := by
      rw [← hrz, MulEquiv.symm_apply_apply]
    obtain ⟨d, hdD, hd2⟩ := exists_mul_sq_eq_one_of_dihedral hm4 hm0 eD.symm hyN i hσ hz
    have hdL₀ : d ∈ linearCore ι := hdD.1
    have hyd1 : y * d ≠ 1 := fun h => hyL₀ (by
      rw [show y = d⁻¹ by rw [← mul_eq_one_iff_eq_inv.mp h]]
      exact Subgroup.inv_mem _ hdL₀)
    have hyd := hinvL (y * d) (L.mul_mem hyL (hd.linearCore_le hdL₀)) (orderOf_eq_prime hd2 hyd1)
    apply hyL₀
    have := Subgroup.mul_mem _ hyd (Subgroup.inv_mem _ hdL₀)
    rwa [mul_inv_cancel_right] at this
  have h2 : L ⊓ Subgroup.centralizer (T : Set H) = T :=
    le_antisymm (fun y hy => hA y hy (hB y hy)) (le_inf hTL hTC)
  have hEC : E ≤ Subgroup.centralizer (T : Set H) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_iff.mp (hd.le_centralizer he) t (hTS ht)
  refine ⟨le_antisymm ?_ (sup_le hTC hEC), h2⟩
  intro c hc
  have := hd.normal
  have hc' : c ∈ ((L ⊔ E : Subgroup H) : Set H) := by
    rw [hd.sup_eq_top]
    exact Subgroup.mem_top c
  rw [Subgroup.normal_mul] at hc'
  obtain ⟨l, hl, e', he', rfl⟩ := hc'
  have hlC : l ∈ Subgroup.centralizer (T : Set H) := by
    have := Subgroup.mul_mem _ hc (hEC (E.inv_mem he'))
    rwa [mul_inv_cancel_right] at this
  have hlT : l ∈ T := h2 ▸ ⟨hl, hlC⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlT) (Subgroup.mem_sup_right he')

end IsLinearDecomposition

end CFSG.ABGDGroups
