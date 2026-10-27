module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSmallCentOuter
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSmallCentGrp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFactsAssembly
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSmallCentA7

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

theorem map_centralizer_singleton {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    (centralizer ({x} : Set X)).map e.toMonoidHom = centralizer ({e x} : Set Y) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w * x = x * w := mem_centralizer_singleton_iff.mp hw
    refine mem_centralizer_singleton_iff.mpr ?_
    change e w * e x = e x * e w
    rw [← map_mul, ← map_mul, hw']
  · intro hy
    have hy' : y * e x = e x * y := mem_centralizer_singleton_iff.mp hy
    refine ⟨e.symm y, mem_centralizer_singleton_iff.mpr ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hy']

theorem eqLocus_conj_eq_centralizer {S : Type*} [Group S] (r : S) :
    MonoidHom.eqLocus (MulAut.conj r).toMonoidHom (MonoidHom.id S) =
      centralizer ({r} : Set S) := by
  ext s
  rw [mem_centralizer_singleton_iff]
  show (MulAut.conj r) s = s ↔ s * r = r * s
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc s * r = r * s * r⁻¹ * r := by rw [h]
      _ = r * s := by group
  · intro h
    rw [← h]
    group

theorem exists_d8_gens {X : Type*} [Group X] {H : Subgroup X} (ψ : DihedralGroup (2 ^ 2) ≃* H) :
    ∃ z u u' : X, z ∈ H ∧ u ∈ H ∧ u' ∈ H ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧ u ^ 2 = 1 ∧ u ≠ 1 ∧
      u' ^ 2 = 1 ∧ u' ≠ 1 ∧ u ≠ z ∧ u' ≠ z ∧ z * u = u * z ∧ z * u' = u' * z ∧
      u * u' ≠ u' * u ∧ ∀ K : Subgroup X, z ∈ K → u ∈ K → u' ∈ K → H ≤ K := by
  set f : DihedralGroup (2 ^ 2) →* X := H.subtype.comp ψ.toMonoidHom with hf
  have hfinj : Function.Injective f := Subtype.val_injective.comp ψ.injective
  have hfH : ∀ a, f a ∈ H := fun a => (ψ a).2
  have hsq : ∀ a : DihedralGroup (2 ^ 2), a ^ 2 = 1 → f a ^ 2 = 1 := fun a ha => by
    rw [← map_pow, ha, map_one]
  have hne : ∀ a b : DihedralGroup (2 ^ 2), a ≠ b → f a ≠ f b := fun a b hab h => hab (hfinj h)
  have hne1 : ∀ a : DihedralGroup (2 ^ 2), a ≠ 1 → f a ≠ 1 := fun a ha h =>
    ha (hfinj (by rw [h, map_one]))
  have hcomm : ∀ a b : DihedralGroup (2 ^ 2), a * b = b * a → f a * f b = f b * f a :=
    fun a b h => by rw [← map_mul, h, map_mul]
  have hncomm : ∀ a b : DihedralGroup (2 ^ 2), a * b ≠ b * a → f a * f b ≠ f b * f a :=
    fun a b h h' => h (hfinj (by rw [map_mul, map_mul, h']))
  refine ⟨f (DihedralGroup.r 2), f (DihedralGroup.sr 0), f (DihedralGroup.sr 1), hfH _, hfH _,
    hfH _, hsq _ (by decide), hne1 _ (by decide), hsq _ (by decide), hne1 _ (by decide),
    hsq _ (by decide), hne1 _ (by decide), hne _ _ (by decide), hne _ _ (by decide),
    hcomm _ _ (by decide), hcomm _ _ (by decide), hncomm _ _ (by decide), ?_⟩
  intro K hz hu hu' h hh
  obtain ⟨a, ha⟩ : ∃ a, f a = h := ⟨ψ.symm ⟨h, hh⟩, by simp [hf]⟩
  rw [← ha]
  have hall : ∀ x : DihedralGroup (2 ^ 2), x = 1 ∨ x = DihedralGroup.r 2 ∨
      x = DihedralGroup.sr 0 ∨ x = DihedralGroup.sr 1 ∨
      x = DihedralGroup.sr 0 * DihedralGroup.sr 1 ∨ x = DihedralGroup.sr 1 * DihedralGroup.sr 0 ∨
      x = DihedralGroup.r 2 * DihedralGroup.sr 0 ∨ x = DihedralGroup.r 2 * DihedralGroup.sr 1 := by
    decide
  rcases hall a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_one]
    exact one_mem K
  · exact hz
  · exact hu
  · exact hu'
  all_goals rw [map_mul]
  · exact mul_mem hu hu'
  · exact mul_mem hu' hu
  · exact mul_mem hz hu
  · exact mul_mem hz hu'

theorem kleinFour_of_pair {X : Type*} [Group X] [Finite X] {z u : X} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (huz : u ≠ z) (hzu : z * u = u * z) :
    IsKleinFour ↥(zpowers z ⊔ zpowers u) ∧ Nat.card ↥(zpowers z ⊔ zpowers u) = 4 ∧
      ∀ a ∈ zpowers z ⊔ zpowers u, ∀ b ∈ zpowers z ⊔ zpowers u, a * b = b * a := by
  have hV := isKleinFour_sup_zpowers hz2 hu2 hz1 hu1 huz hzu
  exact ⟨hV, hV.card_four, fun a ha b hb =>
    commute_of_sq_eq_one (fun x hx => sq_eq_one_of_isKleinFour hV hx) ha hb⟩

theorem iSup_eqLocus_eq_top_of_sylow_gen (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (hD : GorensteinWalter.HasDihedralSylowTwo S) (h8 : ∀ P : Sylow 2 S, Nat.card P = 8)
    (hinner : ∀ R : Sylow 2 S, invCentSup (R : Subgroup S) = ⊤) {T : Subgroup (MulAut S)}
    (hTiso : ∃ P : Sylow 2 S, Nonempty ((P : Subgroup S) ≃* T)) :
    ⨆ (τ : MulAut S) (_ : τ ∈ T) (_ : orderOf τ = 2),
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut S) := Finite.of_injective (fun σ : MulAut S => (σ : S → S))
    (fun a b h => MulEquiv.ext (congrFun h))
  obtain ⟨-, hZ⟩ := open_isQuasisimple_of_isSimpleGroup hnc
  set c : S →* MulAut S := MulAut.conj with hc
  have hcinj : Function.Injective c := injective_mulAut_conj hZ
  obtain ⟨P, ⟨eP⟩⟩ := hTiso
  obtain ⟨m, -, ⟨eD⟩⟩ := hD P
  have hm : m = 2 := by
    have h1 := h8 P
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card] at h1
    have h2 : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl h2
  subst hm
  obtain ⟨z, u, u', hzT, huT, hu'T, hz2, hz1, hu2, hu1, hu'2, hu'1, huz, hu'z, hzu, hzu', huu',
    hgen⟩ := exists_d8_gens (eD.symm.trans eP)
  set Tgt := ⨆ (τ : MulAut S) (_ : τ ∈ T) (_ : orderOf τ = 2),
    MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) with hTgt
  have hTle : ∀ τ ∈ T, orderOf τ = 2 →
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) ≤ Tgt := fun τ hτ hτ2 =>
    le_iSup₂_of_le (f := fun τ (_ : τ ∈ T) => ⨆ (_ : orderOf τ = 2),
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S)) τ hτ
      (le_iSup (fun _ : orderOf τ = 2 => MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S)) hτ2)
  have hfour : ∀ v : MulAut S, v ∈ T → v ^ 2 = 1 → v ≠ 1 → v ≠ z → z * v = v * z →
      (z ∉ c.range ∨ v ∉ c.range) → Tgt = ⊤ := by
    intro v hvT hv2 hv1 hvz hzv hout
    obtain ⟨hV, -, -⟩ := kleinFour_of_pair hz2 hz1 hv2 hv1 hvz hzv
    have hVI : ¬ zpowers z ⊔ zpowers v ≤ c.range := fun h => by
      rcases hout with h' | h'
      · exact h' (h (mem_sup_left (mem_zpowers z)))
      · exact h' (h (mem_sup_right (mem_zpowers v)))
    have hgen' := iSup_eqLocus_eq_top_of_not_le_range hK hnc
      (hasDihedralSylowTwo_of_gorensteinWalter hD) hV hVI
    rw [eq_top_iff, ← hgen']
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    have hwT : w ∈ T := sup_le (zpowers_le.mpr hzT) (zpowers_le.mpr hvT) hw
    exact hTle w hwT (orderOf_eq_prime (sq_eq_one_of_isKleinFour hV hw) hw1)
  by_cases hzI : z ∈ c.range
  swap
  · exact hfour u huT hu2 hu1 huz hzu (Or.inl hzI)
  by_cases huI : u ∈ c.range
  swap
  · exact hfour u huT hu2 hu1 huz hzu (Or.inr huI)
  by_cases hu'I : u' ∈ c.range
  swap
  · exact hfour u' hu'T hu'2 hu'1 hu'z hzu' (Or.inr hu'I)
  have hTI : T ≤ c.range := hgen _ hzI huI hu'I
  set R := T.comap c with hR
  have hRT : R.map c = T := map_comap_eq_self hTI
  have hRcard : Nat.card R = 2 ^ (Nat.card S).factorization 2 := by
    rw [← card_map_of_injective hcinj, hRT, ← Nat.card_congr eP.toEquiv]
    exact Sylow.card_eq_multiplicity P
  have hRtop := hinner (Sylow.ofCard R hRcard)
  rw [Sylow.coe_ofCard] at hRtop
  rw [eq_top_iff, ← hRtop]
  refine iSup₂_le fun r hr => iSup_le fun hr2 => ?_
  rw [← eqLocus_conj_eq_centralizer]
  exact hTle (c r) hr (by rw [orderOf_injective c hcinj r]; exact hr2)

theorem invCentSup_psl2_eq_top {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hcard : Nat.card S = 168 ∨ Nat.card S = 360)
    (hD : GorensteinWalter.HasDihedralSylowTwo S) (h8 : ∀ P : Sylow 2 S, Nat.card P = 8)
    (hc8 : ∀ x : S, orderOf x = 2 → Nat.card (centralizer ({x} : Set S)) = 8)
    (R : Sylow 2 S) : invCentSup (R : Subgroup S) = ⊤ := by
  obtain ⟨m, -, ⟨eD⟩⟩ := hD R
  have hm : m = 2 := by
    have h1 := h8 R
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card] at h1
    have h2 : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl h2
  subst hm
  obtain ⟨z, u, u', hzR, huR, hu'R, hz2, hz1, hu2, hu1, hu'2, hu'1, huz, hu'z, hzu, hzu', huu',
    -⟩ := exists_d8_gens eD.symm
  obtain ⟨-, hU4, hUc⟩ := kleinFour_of_pair hz2 hz1 hu2 hu1 huz hzu
  obtain ⟨-, hU'4, hU'c⟩ := kleinFour_of_pair hz2 hz1 hu'2 hu'1 hu'z hzu'
  have hord : ∀ x : S, x ^ 2 = 1 → x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    orderOf_eq_prime hx hx1
  have hJz := centralizer_le_invCentSup hzR (hord z hz2 hz1)
  have hJu := centralizer_le_invCentSup huR (hord u hu2 hu1)
  have hJu' := centralizer_le_invCentSup hu'R (hord u' hu'2 hu'1)
  rcases hcard with h168 | h360
  · exact eq_top_of_three_centralizers_le_168 h168 hU4 hU'4 hUc hU'c
      (mem_sup_left (mem_zpowers z)) (mem_sup_left (mem_zpowers z)) hz1
      (mem_sup_right (mem_zpowers u)) (mem_sup_right (mem_zpowers u')) huu'
      (hc8 z (hord z hz2 hz1)) (hc8 u (hord u hu2 hu1)) (hc8 u' (hord u' hu'2 hu'1)) hJz hJu hJu'
  · exact Foote47.eq_top_of_three_centralizers_le h360 hU4 hU'4 hUc hU'c
      (mem_sup_left (mem_zpowers z)) (mem_sup_left (mem_zpowers z)) hz1
      (mem_sup_right (mem_zpowers u)) (mem_sup_right (mem_zpowers u')) huu'
      (hc8 z (hord z hz2 hz1)) (hc8 u (hord u hu2 hu1)) (hc8 u' (hord u' hu'2 hu'1)) hJz hJu hJu'

theorem two_pow_factorization_eq_eight {n : ℕ} (hn : n = 2520 ∨ n = 168 ∨ n = 360) :
    2 ^ n.factorization 2 = 8 := by
  have key : ∀ k : ℕ, ¬ 2 ∣ k → 2 ^ (2 ^ 3 * k).factorization 2 = 8 := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => hk (h ▸ dvd_zero 2)
    rw [Nat.factorization_mul (by norm_num) hk0, Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self, Nat.factorization_eq_zero_of_not_dvd hk]
  rcases hn with rfl | rfl | rfl
  · exact key 315 (by norm_num)
  · exact key 21 (by norm_num)
  · exact key 45 (by norm_num)

theorem footeSmallCentralizers_holds :
    FooteSmallCentralizers := by
  intro S _ _ hsmall hnab T hT hTiso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := AschbacherKnownGroup.knownGroupFacts_holds
  have hnc : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 S))
    obtain ⟨x, -, y, -, hxy⟩ := hnab P
    exact ⟨x, y, hxy⟩
  have h8 : ∀ (n : ℕ), (n = 2520 ∨ n = 168 ∨ n = 360) → Nat.card S = n →
      ∀ P : Sylow 2 S, Nat.card P = 8 := by
    intro n hn hSn P
    rw [Sylow.card_eq_multiplicity P, hSn]
    exact two_pow_factorization_eq_eight hn
  rcases hsmall with ⟨⟨e⟩⟩ | ⟨p, f, hpf, hmodel⟩
  ·
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
    have : IsSimpleGroup S := e.isSimpleGroup
    have hSc : Nat.card S = 2520 := by
      rw [Nat.card_congr e.toEquiv]
      exact AutL2Facts.card_alternatingGroup_seven
    have hD : GorensteinWalter.HasDihedralSylowTwo S :=
      GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
        GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven
    refine iSup_eqLocus_eq_top_of_sylow_gen hK hnc hD (h8 2520 (Or.inl rfl) hSc) (fun R => ?_)
      hTiso
    have hRe : Nat.card ((R : Subgroup S).map e.toMonoidHom) =
        2 ^ (Nat.card (alternatingGroup (Fin 7))).factorization 2 := by
      rw [card_map_of_injective e.injective, h8 2520 (Or.inl rfl) hSc R,
        AutL2Facts.card_alternatingGroup_seven]
      exact (two_pow_factorization_eq_eight (Or.inl rfl)).symm
    have h1 := invCentSup_a7_eq_top (Sylow.ofCard _ hRe)
    rw [Sylow.coe_ofCard] at h1
    have h2 := invCentSup_eq_top_of_map e.symm h1
    rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S by
      ext; simp, Subgroup.map_id] at h2
  ·
    obtain ⟨-, hsimp⟩ := LieType.Simplicity.fam_PSL_simplicity S 2 p f hmodel
    obtain ⟨⟨hp, hf, -⟩, K, _, _, hK', ⟨e₀⟩⟩ := hmodel
    have : Fact p.Prime := ⟨hp⟩
    set e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
      e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
      with he
    have hq : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 := by
      simpa using hpf
    have hpodd : Odd p := by
      rcases Nat.Prime.eq_two_or_odd' hp with rfl | h
      · exfalso
        have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        rcases hq with h | h | h <;> omega
      · exact h
    have hodd : GorensteinWalter.IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hpodd, hf, hK'⟩
    have hSc : Nat.card S = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv]
      exact GorensteinWalter.psl2_card_formula K hodd
    have hD : GorensteinWalter.HasDihedralSylowTwo S :=
      GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
        (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd)
    rcases hq with h5 | h79
    ·
      exfalso
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 S))
      have hP4 : Nat.card P = 2 ^ 2 := by
        rw [Sylow.card_eq_multiplicity P, hSc, hK', h5,
          show 5 * (5 ^ 2 - 1) / 2 = 2 ^ 2 * 15 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
        simp [Nat.prime_two.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]
      obtain ⟨x, hx, y, hy, hxy⟩ := hnab P
      have hab := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP4
      have h1 : (⟨x, hx⟩ : ↥(P : Subgroup S)) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
        hab.is_comm.comm _ _
      exact hxy (congrArg Subtype.val h1)
    · have hSc' : Nat.card S = 168 ∨ Nat.card S = 360 := by
        rw [hSc, hK']
        rcases h79 with h | h <;> rw [h] <;> norm_num
      have h8' := h8 (Nat.card S) (by rcases hSc' with h | h <;> simp [h]) rfl
      have hc8 : ∀ x : S, orderOf x = 2 → Nat.card (centralizer ({x} : Set S)) = 8 := by
        intro x hx
        rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, map_centralizer_singleton e x]
        have hx' : orderOf (e x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
        obtain ⟨h1, h3⟩ := Walter.psl2_centralizer_involution K hK' hpodd (by omega) hx'
        rcases h79 with h | h
        · rw [(h3 (by rw [h])).1, h]
        · rw [(h1 (by rw [h])).1, h]
      exact iSup_eqLocus_eq_top_of_sylow_gen hK hnc hD h8'
        (invCentSup_psl2_eq_top hSc' hD h8' hc8) hTiso

end CFSG.ComponentClassification.FooteLit
