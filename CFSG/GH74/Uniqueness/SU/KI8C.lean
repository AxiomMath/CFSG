module

public import CFSG.GH74.Uniqueness.SU.KI8Basic
public import CFSG.GH74.Uniqueness.SU.KI8CStmt
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.L2.Lemma13

public section

namespace CFSG.GH74.Uniqueness.SU.K.KI8

open Subgroup CFSG.GorensteinWalter CFSG.Blueprint CFSG.GH74.Uniqueness.SU.SU4
open CFSG.GH74.GLS.IVK (L2 L2Field)

variable {H : Type} [Group H] [Finite H]

structure SetC (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (z : H) : Prop where
  core : pPrimeCore 2 H = ⊥
  hz2 : orderOf z = 2
  hzT : z ∈ (T : Subgroup H)
  hzc : ∀ t ∈ (T : Subgroup H), t * z = z * t
  hT4 : Nat.card (T : Subgroup H) = 4
  hC4 : Nat.card (CBar H z) = 4
  hOC : Open.IsElemAbelian 3 (OC H z)

omit [Finite H] in
theorem card_cen_eq (z : H) :
    Nat.card (centralizer ({z} : Set H)) =
      Nat.card (pPrimeCore 2 ↥(centralizer ({z} : Set H))) * Nat.card (CBar H z) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥(centralizer ({z} : Set H))),
    mul_comm]

theorem odd_card_pPrimeCore (G : Type) [Group G] [Finite G] : Odd (Nat.card (pPrimeCore 2 G)) :=
  Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))

theorem isCyclic_of_odd_card_dihedral {k : ℕ} [NeZero k] (X : Subgroup (DihedralGroup k))
    (hX : Odd (Nat.card X)) : IsCyclic X := by
  have hrot : ∀ x ∈ X, ∃ i : ZMod k, x = DihedralGroup.r i := by
    intro x hx
    cases x with
    | r i => exact ⟨i, rfl⟩
    | sr i =>
      exfalso
      have h2 : orderOf (⟨DihedralGroup.sr i, hx⟩ : X) = 2 := by
        rw [Subgroup.orderOf_mk]; exact DihedralGroup.orderOf_sr i
      have := orderOf_dvd_natCard (⟨DihedralGroup.sr i, hx⟩ : X)
      rw [h2] at this
      exact (Nat.not_even_iff_odd.mpr hX) (even_iff_two_dvd.mpr this)
  have hle : X ≤ zpowers (DihedralGroup.r 1 : DihedralGroup k) := by
    intro x hx
    obtain ⟨i, rfl⟩ := hrot x hx
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(i.val : ℤ), ?_⟩
    rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  exact Subgroup.isCyclic_of_le hle

theorem card_dvd_three_of_cyclic {Y : Type} [Group Y] [Finite Y] [IsCyclic Y]
    (h : ∀ y : Y, y ^ 3 = 1) : Nat.card Y ∣ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Y)
  have h1 : orderOf g = Nat.card Y := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [← h1]
  exact orderOf_dvd_of_pow_eq_one (h g)


theorem T_mem_cen_barImage_top {T : Sylow 2 H} {z : H} (S : SetC H T z) :
    barImage (centralizer ({z} : Set H)) (T : Subgroup H) = ⊤ := by
  have hcard : Nat.card (barImage (centralizer ({z} : Set H)) (T : Subgroup H)) =
      Nat.card (CBar H z) := by
    rw [S.hC4, ← S.hT4]
    exact (Nat.card_congr (mulEquivBarImage (centralizer ({z} : Set H)) T.isPGroup'
      (T_le_cen S.hzc)).toEquiv).symm
  exact Subgroup.eq_top_of_card_eq _ hcard

theorem exists_Y {T : Sylow 2 H} {z : H} (S : SetC H T z) {L : Subgroup H}
    (hTL : (T : Subgroup H) ≤ L) :
    ∃ Y : Subgroup ↥(centralizer ({(⟨z, hTL S.hzT⟩ : L)} : Set L)),
      Nat.card ↥(centralizer ({(⟨z, hTL S.hzT⟩ : L)} : Set L)) = 4 * Nat.card Y ∧
        (∀ y : Y, y ^ 3 = 1) ∧ Odd (Nat.card Y) := by
  set zL : L := ⟨z, hTL S.hzT⟩ with hzL
  set D₀ : Subgroup L := centralizer ({zL} : Set L) with hD₀
  set C : Subgroup H := centralizer ({z} : Set H) with hCdef
  let g : ↥D₀ →* ↥C :=
    { toFun := fun d => ⟨((d : L) : H), by
        have := mem_centralizer_singleton_iff.mp d.2
        exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hginj : Function.Injective g := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥C => (x : H)) hab))
  let ψ : ↥D₀ →* CBar H z := (proj C).comp g
  have hψ : Function.Surjective ψ := by
    intro cb
    have hcb : cb ∈ barImage C (T : Subgroup H) := by
      rw [T_mem_cen_barImage_top S]; exact Subgroup.mem_top cb
    obtain ⟨m, hmT, hmcb⟩ := (mem_barImage C).mp hcb
    refine ⟨⟨⟨(m : H), hTL hmT⟩, ?_⟩, ?_⟩
    · exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp m.2))
    · show proj C (g _) = cb
      rw [← hmcb]
      congr 1
  have hrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψ
  have hcard : Nat.card D₀ = 4 * Nat.card ψ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    rw [hrange, Subgroup.card_top, S.hC4] at h1
    rw [← h1, mul_comm]
  have hker : ∀ y : ↥D₀, y ∈ ψ.ker → ((y : L) : H) ∈ OC H z := by
    intro y hy
    have h1 : g y ∈ (proj C).ker := hy
    rw [ker_proj C] at h1
    exact ⟨g y, h1, rfl⟩
  refine ⟨ψ.ker, hcard, ?_, ?_⟩
  · intro y
    have h1 := S.hOC.2 _ (hker y y.2)
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  ·
    let κ : ↥ψ.ker →* ↥(pPrimeCore 2 ↥C) :=
      (g.comp ψ.ker.subtype).codRestrict (pPrimeCore 2 ↥C) (fun y => by
        have h1 : g y.1 ∈ (proj C).ker := y.2
        rwa [ker_proj C] at h1)
    have hκ : Function.Injective κ := by
      intro a b hab
      apply Subtype.ext
      apply hginj
      exact congrArg Subtype.val hab
    have hdvd := Subgroup.card_dvd_of_injective _ hκ
    exact Odd.of_dvd_nat (odd_card_pPrimeCore ↥C) hdvd


theorem q_cases {T : Sylow 2 H} {z : H} (S : SetC H T z) {L : Subgroup H}
    {K : Type} [Field K] [Finite K] (hF : L2Field K) (e : L ≃* L2 K)
    (hTL : (T : Subgroup H) ≤ L) :
    Nat.card K = 5 ∨ Nat.card K = 11 ∨ Nat.card K = 13 := by
  set zL : L := ⟨z, hTL S.hzT⟩ with hzL
  have hzL2 : orderOf zL = 2 := by rw [hzL, Subgroup.orderOf_mk]; exact S.hz2
  obtain ⟨Y, hcard, hexp, hodd⟩ := exists_Y S hTL
  have hmod : Nat.card K % 4 = 1 ∨ Nat.card K % 4 = 3 := by
    have := Nat.odd_iff.mp hF.1
    omega
  have h3 : 3 < Nat.card K := hF.2
  have hdih : ∃ d : ℕ, CFSG.GH74.GLS.IVK.IsDihedralOrder ↥(centralizer ({zL} : Set L)) d ∧
      ((Nat.card K % 4 = 1 ∧ d + 1 = Nat.card K) ∨ (Nat.card K % 4 = 3 ∧ d = Nat.card K + 1)) := by
    rcases hmod with hm | hm
    · obtain ⟨-, hd, -⟩ := CFSG.GH74.GLS.IVK.ivk_1_3a K hF L e 1 (Or.inl rfl)
        (by simp only [Int.ModEq]; omega) (Nat.card K - 1) (by omega) zL hzL2
      exact ⟨_, hd, Or.inl ⟨hm, by omega⟩⟩
    · obtain ⟨-, hd, -⟩ := CFSG.GH74.GLS.IVK.ivk_1_3a K hF L e (-1) (Or.inr rfl)
        (by simp only [Int.ModEq]; omega) (Nat.card K + 1) (by omega) zL hzL2
      exact ⟨_, hd, Or.inr ⟨hm, rfl⟩⟩
  obtain ⟨d, ⟨k, hdk, hk2, ⟨eD⟩⟩, hdq⟩ := hdih
  have : NeZero k := ⟨by omega⟩
  have hDcard : Nat.card ↥(centralizer ({zL} : Set L)) = d := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, hdk]
  have hYcyc : IsCyclic Y := by
    let X : Subgroup (DihedralGroup k) := Y.map eD.toMonoidHom
    have hXcard : Nat.card X = Nat.card Y := Subgroup.card_map_of_injective eD.injective
    have hXcyc : IsCyclic X := isCyclic_of_odd_card_dihedral X (hXcard ▸ hodd)
    exact (Subgroup.equivMapOfInjective Y eD.toMonoidHom eD.injective).isCyclic.mpr hXcyc
  have hY3 : Nat.card Y ∣ 3 := card_dvd_three_of_cyclic hexp
  have hd : d = 4 ∨ d = 12 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hY3 with h | h
    · left; rw [← hDcard, hcard, h]
    · right; rw [← hDcard, hcard, h]
  omega


theorem card_aut_eq {K : Type} [Field K] [Finite K] (hF : L2Field K) {G : Type} [Group G]
    [Finite G] (e : G ≃* L2 K) {q : ℕ} (hq : Nat.Prime q) (hKq : Nat.card K = q) :
    Nat.card (MulAut G) = 2 * Nat.card G := by
  obtain ⟨N⟩ := CFSG.GH74.GLS.IVK.exists_notation hF e
  have h1 := CFSG.GH74.GLS.IVK.ivk_1_2e K hF G e
  have hn : Nat.card (CFSG.GH74.GLS.IVK.fieldAutSub e) = 1 :=
    h1.2.2 q 1 hq (by rw [pow_one]; exact hKq)
  have hbot : CFSG.GH74.GLS.IVK.fieldAutSub e = ⊥ := Subgroup.eq_bot_of_card_eq _ hn
  have hstruct := CFSG.GH74.GLS.IVK.ivk_1_2a_struct K hF G e N
  have hd := CFSG.GH74.GLS.IVK.ivk_1_2d K hF G e N
  have htop : CFSG.GH74.GLS.IVK.innDiagSub e = ⊤ := by
    rw [← hd.1]
    have := hstruct.1
    rwa [hbot, sup_bot_eq] at this
  have h2 : Nat.card (CFSG.GH74.GLS.IVK.innDiagSub e) = Nat.card (MulAut G) := by
    rw [htop, Subgroup.card_top]
  rw [← h2]
  exact CFSG.GH74.GLS.IVK.card_innDiagSub e hF


theorem cen_card {K : Type} [Field K] [Finite K] (hF : L2Field K) {G : Type} [Group G] [Finite G]
    (e : G ≃* L2 K) (u : G) (hu : orderOf u = 2) :
    ∃ d : ℕ, Nat.card ↥(centralizer ({u} : Set G)) = d ∧
      ((Nat.card K % 4 = 1 ∧ d + 1 = Nat.card K) ∨ (Nat.card K % 4 = 3 ∧ d = Nat.card K + 1)) := by
  have hmod : Nat.card K % 4 = 1 ∨ Nat.card K % 4 = 3 := by
    have := Nat.odd_iff.mp hF.1
    omega
  have h3 : 3 < Nat.card K := hF.2
  have hdih : ∃ d : ℕ, CFSG.GH74.GLS.IVK.IsDihedralOrder ↥(centralizer ({u} : Set G)) d ∧
      ((Nat.card K % 4 = 1 ∧ d + 1 = Nat.card K) ∨ (Nat.card K % 4 = 3 ∧ d = Nat.card K + 1)) := by
    rcases hmod with hm | hm
    · obtain ⟨-, hd, -⟩ := CFSG.GH74.GLS.IVK.ivk_1_3a K hF G e 1 (Or.inl rfl)
        (by simp only [Int.ModEq]; omega) (Nat.card K - 1) (by omega) u hu
      exact ⟨_, hd, Or.inl ⟨hm, by omega⟩⟩
    · obtain ⟨-, hd, -⟩ := CFSG.GH74.GLS.IVK.ivk_1_3a K hF G e (-1) (Or.inr rfl)
        (by simp only [Int.ModEq]; omega) (Nat.card K + 1) (by omega) u hu
      exact ⟨_, hd, Or.inr ⟨hm, rfl⟩⟩
  obtain ⟨d, ⟨k, hdk, hk2, ⟨eD⟩⟩, hdq⟩ := hdih
  have : NeZero k := ⟨by omega⟩
  refine ⟨d, ?_, hdq⟩
  rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, hdk]

theorem lieModel_psl2 {G : Type} [Group G] {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : Nat.card K = p) (h4 : 4 ≤ p) (e : G ≃* L2 K) :
    LieModel G .PSL 2 p 1 := by
  refine Or.inl ⟨by simp [classicalTags], ⟨hp, le_rfl, le_rfl, ?_, ?_⟩, K, inferInstance,
    inferInstance, by rw [pow_one]; exact hK, ⟨e⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and, pow_one] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and, pow_one] at h
    omega

theorem centralizer_eq_bot (hO : pPrimeCore 2 H = ⊥) {L : Subgroup H} [L.Normal]
    (hLi : Odd L.index) (hZ : Subgroup.center L = ⊥) : centralizer (L : Set H) = ⊥ := by
  have hDn : (centralizer (L : Set H)).Normal := inferInstance
  have hDodd : Odd (Nat.card (centralizer (L : Set H))) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have h2 : 2 ∣ Nat.card (centralizer (L : Set H)) := even_iff_two_dvd.mp hne
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer (L : Set H))) 2 h2
    have hxo : orderOf (x : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have hP : IsPGroup 2 (zpowers (x : H)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; simp)
    have hxL : (x : H) ∈ L := le_of_isPGroup_of_odd_index hLi hP (Subgroup.mem_zpowers _)
    have hcen : (⟨(x : H), hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := Subgroup.mem_centralizer_iff.mp x.2 (y : H) y.2
      exact Subtype.ext this
    rw [hZ, Subgroup.mem_bot] at hcen
    have h1 : (x : H) = 1 := congrArg Subtype.val hcen
    rw [h1, orderOf_one] at hxo
    omega
  exact (pPrimeCore_eq_bot_iff).mp hO _ hDn (Nat.coprime_two_left.mpr hDodd)


theorem card_A4 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel


omit [Finite H] in
theorem card_OC (z : H) :
    Nat.card (OC H z) = Nat.card (pPrimeCore 2 ↥(centralizer ({z} : Set H))) :=
  Subgroup.card_map_of_injective (centralizer ({z} : Set H)).subtype_injective


theorem a4_branch {T : Sylow 2 H} {z : H} (S : SetC H T z) {L : Subgroup H} [L.Normal]
    (hLi : Odd L.index) (eA : L ≃* alternatingGroup (Fin 4)) :
    OC H z = ⊥ ∧ Nonempty (H ≃* alternatingGroup (Fin 4)) := by
  have hZA : Subgroup.center (alternatingGroup (Fin 4)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hZL : Subgroup.center L = ⊥ := center_eq_bot_of_mulEquiv eA hZA
  have hC : centralizer (L : Set H) = ⊥ := centralizer_eq_bot S.core hLi hZL
  have hLcard : Nat.card L = 12 := by rw [Nat.card_congr eA.toEquiv]; exact card_A4
  have hAut : Nat.card (MulAut L) = 24 := by
    have e1 : MulAut L ≃ MulAut (alternatingGroup (Fin 4)) := (MulAut.congr eA).toEquiv
    have e2 : Equiv.Perm (Fin 4) ≃ MulAut (alternatingGroup (Fin 4)) :=
      Equiv.ofBijective _ GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
    rw [Nat.card_congr (e1.trans e2.symm), Nat.card_perm]
    simp [Nat.factorial]
  have hTop : L = ⊤ := eq_top_of_aut_card hLi hC (by rw [hAut, hLcard])
  let eH : H ≃* alternatingGroup (Fin 4) :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hTop.symm)).trans eA
  refine ⟨?_, ⟨eH⟩⟩
  have hZH : Subgroup.center H = ⊥ := center_eq_bot_of_mulEquiv eH hZA
  have hH12 : Nat.card H = 12 := by rw [Nat.card_congr eH.toEquiv]; exact card_A4
  set C := centralizer ({z} : Set H) with hCdef
  have hcardC : Nat.card C = Nat.card (pPrimeCore 2 ↥C) * 4 := by
    have := card_cen_eq z
    rw [S.hC4] at this
    exact this
  have hCdvd : Nat.card C ∣ 12 := hH12 ▸ Subgroup.card_subgroup_dvd_card C
  have hodd := odd_card_pPrimeCore (↥C)
  have hO1 : Nat.card (pPrimeCore 2 ↥C) = 1 := by
    have h3 : Nat.card (pPrimeCore 2 ↥C) ∣ 3 := by
      have h12 : Nat.card (pPrimeCore 2 ↥C) * 4 ∣ 3 * 4 := by
        have := hcardC ▸ hCdvd
        simpa using this
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h12
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact h
    · exfalso
      have hC12 : Nat.card C = 12 := by omega
      have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hC12, hH12])
      have hzcen : z ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro g
        have : g ∈ C := hCtop ▸ Subgroup.mem_top g
        exact (mem_centralizer_singleton_iff.mp this)
      rw [hZH, Subgroup.mem_bot] at hzcen
      have := S.hz2
      rw [hzcen, orderOf_one] at this
      omega
  have : pPrimeCore 2 ↥C = ⊥ := Subgroup.eq_bot_of_card_eq _ hO1
  unfold OC
  rw [← hCdef, this, Subgroup.map_bot]


theorem big_branch {T : Sylow 2 H} {z : H} (S : SetC H T z) {L : Subgroup H} [L.Normal]
    (hLi : Odd L.index) {K : Type} [Field K] [Finite K] (hF : L2Field K) (e : L ≃* L2 K) :
    (OC H z = ⊥ ∧ LieModel H .PSL 2 5 1) ∨
      (Nat.card (OC H z) = 3 ∧ (LieModel H .PSL 2 11 1 ∨ LieModel H .PSL 2 13 1)) := by
  have hTL : (T : Subgroup H) ≤ L := le_of_isPGroup_of_odd_index hLi T.isPGroup'
  have hq := q_cases S hF e hTL
  have hZ : Subgroup.center L = ⊥ :=
    center_eq_bot_of_mulEquiv (e.trans (CFSG.GH74.GLS.IVK.L2.equivPSL K)) (psl2_center_eq_bot K)
  have hC : centralizer (L : Set H) = ⊥ := centralizer_eq_bot S.core hLi hZ
  have hqp : Nat.Prime (Nat.card K) := by
    rcases hq with h | h | h <;> rw [h] <;> norm_num
  have hTop : L = ⊤ := by
    refine eq_top_of_aut_card hLi hC ?_
    rw [card_aut_eq hF e hqp rfl]
  let eH : H ≃* L2 K :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hTop.symm)).trans e
  have hz2 := S.hz2
  obtain ⟨d, hd, hdq⟩ := cen_card hF eH z hz2
  have hcardC := card_cen_eq z
  rw [S.hC4, hd] at hcardC
  have hOCcard := card_OC z
  have h4 : 4 ≤ Nat.card K := by omega
  rcases hq with h | h | h
  ·
    left
    have hO1 : Nat.card (pPrimeCore 2 ↥(centralizer ({z} : Set H))) = 1 := by
      rw [h] at hdq; omega
    refine ⟨?_, lieModel_psl2 (p := 5) (by norm_num) h (by omega) eH⟩
    have : pPrimeCore 2 ↥(centralizer ({z} : Set H)) = ⊥ := Subgroup.eq_bot_of_card_eq _ hO1
    unfold OC
    rw [this, Subgroup.map_bot]
  · right
    have hO3 : Nat.card (pPrimeCore 2 ↥(centralizer ({z} : Set H))) = 3 := by
      rw [h] at hdq; omega
    exact ⟨by rw [hOCcard, hO3], Or.inl (lieModel_psl2 (p := 11) (by norm_num) h (by omega) eH)⟩
  · right
    have hO3 : Nat.card (pPrimeCore 2 ↥(centralizer ({z} : Set H))) = 3 := by
      rw [h] at hdq; omega
    exact ⟨by rw [hOCcard, hO3], Or.inr (lieModel_psl2 (p := 13) (by norm_num) h (by omega) eH)⟩


theorem v4_sq (v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : v * v = 1 := by
  revert v; decide

theorem card_v4 : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem isKleinFour_T {T : Sylow 2 H} {z : H} (hzc : ∀ t ∈ (T : Subgroup H), t * z = z * t)
    (e : CBar H z ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    IsKleinFour (T : Subgroup H) := by
  have hcard : Nat.card (CBar H z) = 2 ^ 2 * 1 := by
    rw [Nat.card_congr e.toEquiv, card_v4]; norm_num
  have hT : Nat.card (T : Subgroup H) = 2 ^ 2 := card_T_of_card_cbar hzc odd_one hcard
  let C := centralizer ({z} : Set H)
  let f : (T : Subgroup H) →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    e.toMonoidHom.comp ((proj C).comp (Subgroup.inclusion (T_le_cen hzc)))
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : proj C (Subgroup.inclusion (T_le_cen hzc) a) =
        proj C (Subgroup.inclusion (T_le_cen hzc) b) := e.injective hab
    have h2 := eq_of_proj_eq_of_isPGroup C T.isPGroup' (T_le_cen hzc)
      (a := Subgroup.inclusion (T_le_cen hzc) a) (b := Subgroup.inclusion (T_le_cen hzc) b)
      a.2 b.2 h1
    exact Subgroup.inclusion_injective _ h2
  have hsq : ∀ t : (T : Subgroup H), t * t = 1 := fun t =>
    hfinj (by rw [map_mul, v4_sq, map_one])
  have hnt : Nontrivial (T : Subgroup H) := by
    exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hT]; norm_num)
  refine ⟨by rw [hT]; norm_num, ?_⟩
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  exact orderOf_eq_prime (by rw [sq]; exact hsq g) hg


theorem hasDihedral {T : Sylow 2 H} (hK : IsKleinFour (T : Subgroup H)) :
    HasDihedralSylowTwo H := by
  intro S
  obtain ⟨eT⟩ : Nonempty ((T : Subgroup H) ≃* DihedralGroup 2) := IsKleinFour.nonempty_mulEquiv
  exact ⟨1, le_rfl, ⟨(S.equiv T).trans (by simpa using eT)⟩⟩

theorem false_of_isPGroup {T : Sylow 2 H} (hK : IsKleinFour (T : Subgroup H))
    (hone : ∀ u v : H, orderOf u = 2 → orderOf v = 2 → IsConj u v) (hP : IsPGroup 2 H) : False := by
  classical
  have htop : (T : Subgroup H) = ⊤ := by
    have h1 : IsPGroup 2 ↥(⊤ : Subgroup H) := hP.of_equiv Subgroup.topEquiv.symm
    exact (T.is_maximal' h1 le_top).symm
  have hcomm : ∀ a b : H, a * b = b * a := by
    intro a b
    have ha : a ∈ (T : Subgroup H) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ (T : Subgroup H) := htop ▸ Subgroup.mem_top b
    exact congrArg Subtype.val (mul_comm_of_exponent_two hK.exponent_two
      (⟨a, ha⟩ : (T : Subgroup H)) ⟨b, hb⟩)
  have hcard : Nat.card (T : Subgroup H) = 4 := hK.card_four
  have : Fintype (T : Subgroup H) := Fintype.ofFinite _
  have : Nontrivial (T : Subgroup H) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨a, ha1⟩ : ∃ a : (T : Subgroup H), a ≠ 1 := exists_ne 1
  have hlt : ({1, a} : Finset (T : Subgroup H)).card < Fintype.card (T : Subgroup H) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact lt_of_le_of_lt (Finset.card_le_two) (by norm_num)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  have hexp : ∀ x : (T : Subgroup H), x ≠ 1 → orderOf (x : H) = 2 := by
    intro x hx
    have := (Monoid.exponent_eq_prime_iff Nat.prime_two).mp hK.exponent_two x hx
    exact (orderOf_injective (T : Subgroup H).subtype (Subgroup.subtype_injective _) x).trans this
  have hc := hone a b (hexp a ha1) (hexp b hb.1)
  rw [isConj_iff] at hc
  obtain ⟨g, hg⟩ := hc
  have : (a : H) = b := by rw [← hg, hcomm g a]; group
  exact hb.2 (Subtype.ext this).symm

theorem card_H_dvd {T : Sylow 2 H} (hT : Nat.card (T : Subgroup H) = 4) :
    ∃ m : ℕ, Odd m ∧ Nat.card H = 4 * m := by
  refine ⟨(T : Subgroup H).index, ?_, ?_⟩
  · have := T.not_dvd_index
    rw [Nat.odd_iff]; omega
  · rw [← hT]; exact (Subgroup.card_mul_index _).symm

theorem false_of_alt7 {T : Sylow 2 H} (hT : Nat.card (T : Subgroup H) = 4)
    (e : H ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨m, hm, hH⟩ := card_H_dvd hT
  have : Nat.card H = 2520 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [Nat.odd_iff] at hm
  omega


theorem isOddPrimePower_facts {q : ℕ} (h : IsOddPrimePower q) : Odd q ∧ 3 ≤ q := by
  obtain ⟨p, n, hp, hpodd, hn, rfl⟩ := h
  refine ⟨hpodd.pow, ?_⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hp3 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  have : 3 ≤ p := by omega
  exact this.trans (Nat.le_self_pow (by omega) p)

theorem false_of_pgl2 {T : Sylow 2 H} (hT : Nat.card (T : Subgroup H) = 4) {L : Subgroup H}
    {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (e : L ≃* PGL2 K) : False := by
  obtain ⟨m, hm, hH⟩ := card_H_dvd hT
  have hL : Nat.card L = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, pgl2_card_formula]
  have hdvd : Nat.card L ∣ Nat.card H := Subgroup.card_subgroup_dvd_card L
  obtain ⟨hqodd, -⟩ := isOddPrimePower_facts hK
  obtain ⟨j, hj⟩ := hqodd
  have h8 : 8 ∣ Nat.card K ^ 2 - 1 := by
    have h1 : Nat.card K ^ 2 = 4 * (j * (j + 1)) + 1 := by rw [hj]; ring
    obtain ⟨i, hi⟩ := Nat.even_mul_succ_self j
    have : Nat.card K ^ 2 - 1 = 8 * i := by omega
    exact ⟨i, this⟩
  have h8' : 8 ∣ Nat.card L := hL ▸ Dvd.dvd.mul_left h8 _
  have h8'' : 8 ∣ Nat.card H := h8'.trans hdvd
  rw [Nat.odd_iff] at hm
  omega

omit [Finite H] in
theorem exists_normal_of_core_bot (hO : pPrimeCore 2 H = ⊥) (L : Subgroup (H ⧸ pPrimeCore 2 H))
    (hLn : L.Normal) (hLi : Odd L.index) :
    ∃ L' : Subgroup H, L'.Normal ∧ Odd L'.index ∧ Nonempty (L ≃* L') := by
  let φ : H ⧸ pPrimeCore 2 H ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  refine ⟨L.map φ.toMonoidHom, hLn.map _ φ.surjective, ?_,
    ⟨L.equivMapOfInjective φ.toMonoidHom φ.injective⟩⟩
  rw [Subgroup.index_map_of_bijective φ.bijective]
  exact hLi

theorem psl2_branch {T : Sylow 2 H} {z : H} (S : SetC H T z) {L : Subgroup H} [L.Normal]
    (hLi : Odd L.index) {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (eL : L ≃* PSL2 K) :
    (OC H z = ⊥ ∧ (Nonempty (H ≃* alternatingGroup (Fin 4)) ∨ LieModel H .PSL 2 5 1)) ∨
      (Nat.card (OC H z) = 3 ∧ (LieModel H .PSL 2 11 1 ∨ LieModel H .PSL 2 13 1)) := by
  obtain ⟨hqodd, hq3⟩ := isOddPrimePower_facts hK
  by_cases h3 : Nat.card K = 3
  · have : Fintype K := Fintype.ofFinite K
    have hFcard : Fintype.card K = 3 := by simpa [Nat.card_eq_fintype_card] using h3
    let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hFcard
    let eA : L ≃* alternatingGroup (Fin 4) :=
      eL.trans ((psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup)
    obtain ⟨h1, h2⟩ := a4_branch S hLi eA
    exact Or.inl ⟨h1, Or.inl h2⟩
  · have hF : L2Field K := ⟨hqodd, by omega⟩
    let e : L ≃* L2 K := eL.trans (CFSG.GH74.GLS.IVK.L2.equivPSL K).symm
    rcases big_branch S hLi hF e with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, Or.inr h2⟩
    · exact Or.inr h

end CFSG.GH74.Uniqueness.SU.K.KI8

namespace CFSG.GH74.Uniqueness.SU.K

open Subgroup CFSG.GorensteinWalter CFSG.Blueprint

theorem ki8c
    : KI8c := by
  intro H _ _ hO hone T z hzT hz2 hzc he hOC
  obtain ⟨e⟩ := he
  have hKF : IsKleinFour (T : Subgroup H) := KI8.isKleinFour_T hzc e
  have hT4 : Nat.card (T : Subgroup H) = 4 := hKF.card_four
  have hC4 : Nat.card (CBar H z) = 4 := by rw [Nat.card_congr e.toEquiv, KI8.card_v4]
  have S : KI8.SetC H T z := ⟨hO, hz2, hzT, hzc, hT4, hC4, hOC⟩
  have hD : IsDGroup H := gorensteinWalter.{0} H (KI8.hasDihedral hKF)
  rcases hD with ⟨-, h2⟩ | ⟨-, ⟨e7⟩⟩ | ⟨-, K, hKpp, L, hLn, hLi, hL⟩
  · let φ : H ⧸ pPrimeCore 2 H ≃* H :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    exact (KI8.false_of_isPGroup hKF hone (h2.of_equiv φ)).elim
  · let φ : H ⧸ pPrimeCore 2 H ≃* H :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    exact (KI8.false_of_alt7 hT4 (φ.symm.trans e7)).elim
  · obtain ⟨L', hL'n, hL'i, ⟨eL'⟩⟩ := KI8.exists_normal_of_core_bot hO L hLn hLi
    have := hL'n
    rcases hL with ⟨⟨eL⟩⟩ | ⟨⟨eL⟩⟩
    · exact KI8.psl2_branch S hL'i hKpp (eL'.symm.trans eL)
    · exact (KI8.false_of_pgl2 hT4 hKpp (eL'.symm.trans eL)).elim

end CFSG.GH74.Uniqueness.SU.K
