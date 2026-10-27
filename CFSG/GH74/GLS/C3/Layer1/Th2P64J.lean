module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR2
public import CFSG.GH74.GLS.C3.Layer1.Th2P64H
public import CFSG.GH74.GLS.C3.Layer1.Th2PumpTerm

public section

open Equiv Equiv.Perm Subgroup CFSG
open CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs CFSG.ABGLocalTools CFSG.GH74.GLS.IVK
open scoped commutatorElement

namespace CFSG.GH74.GLS.Th2.Obs

theorem isSolvable_centralizer_conj {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type}
    [Group K] [Finite K] (e : K ≃* L2 F) {u : K} (hu : orderOf u = 2) :
    Group.IsSolvable ↥(centralizer ({MulAut.conj u} : Set (MulAut K))) := by
  classical
  obtain ⟨ε, hε, hmod⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨m, hm⟩ := hF.1
    have h4 : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by omega
    rcases h4 with h | h
    · exact ⟨1, Or.inl rfl, by rw [Int.ModEq]; omega⟩
    · exact ⟨-1, Or.inr rfl, by rw [Int.ModEq]; omega⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
    ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
  have hdih := (ivk_1_3a F hF K e ε hε hmod d hd u hu).1
  have hsolv : Group.IsSolvable ↥(centralizer ({MulAut.conj u} : Set (MulAut K)) ⊓ innDiagSub e) :=
    Lifted.isSolvable_of_isDihedralOrder hdih
  set H : Subgroup (MulAut K) := centralizer ({MulAut.conj u} : Set (MulAut K)) with hH
  let f : ↥H →* (F ≃+* F) := (fieldProj e).comp H.subtype
  have hcyc : IsCyclic (F ≃+* F) := ringAut_isCyclic F
  have hker : Group.IsSolvable ↥f.ker := by
    let g : ↥f.ker →* ↥(H ⊓ innDiagSub e) :=
      ((H.subtype).comp f.ker.subtype).codRestrict _ (fun x => by
        refine ⟨x.1.2, ?_⟩
        exact (mem_innDiagSub_iff _ _).2 x.2)
    have hginj : Function.Injective g := by
      intro x y hxy
      have h1 := congrArg (fun z : ↥(H ⊓ innDiagSub e) => (z : MulAut K)) hxy
      exact Subtype.ext (Subtype.ext h1)
    exact Group.isSolvable_of_isSolvable_injective hginj
  have hrange : Group.IsSolvable ↥f.range := by
    have : IsMulCommutative (F ≃+* F) := hcyc.isMulCommutative
    infer_instance
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

section Rank5

variable {G : Type} [Group G] [Finite G]

theorem false_of_klein_centralizing (hr4 : pRank 2 G = 4) {u' : G} (hu'o : orderOf u' = 2)
    {K'' : Subgroup G} (hK'' : IsPCompIn 2 (centralizer ({u'} : Set G)) K'')
    (hcen'' : CenterlessBar K'') {E : Subgroup G} (hEC : E ≤ centralizer ({u'} : Set G))
    (hEsq : ∀ e ∈ E, e * e = 1) (hE4 : 4 ∣ Nat.card ↥E) (hu'E : u' ∉ E)
    (hcomm : ∀ e ∈ E, e ∈ centralizerSection K'' (pPrimeCoreOf 2 K'')) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu'sq : u' * u' = 1 := by
    have := pow_orderOf_eq_one u'
    rwa [hu'o, sq] at this
  have hu'1 : u' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu'o
    omega
  obtain ⟨hcommB, hBsq, hBcard⟩ := C3.Layer1.P47.zpowers_sup_facts hu'sq hu'1 hEC hEsq hu'E
  set B : Subgroup G := zpowers u' ⊔ E with hB
  have hBea : CFSG.IsElementaryAbelian 2 ↥B :=
    IVK.Proofs2.isElementaryAbelian_two_of_mul_self B hBsq
  have hu'sec : u' ∈ centralizerSection K'' (pPrimeCoreOf 2 K'') :=
    C3.Layer1.Back.mem_centralizerSection_of_centralizes
      (fun k hk => (mem_centralizer_singleton_iff.1 (hK''.1 hk)).symm) (TwoThin.pPrimeCoreOf_le K'')
  have hBsec : B ≤ centralizerSection K'' (pPrimeCoreOf 2 K'') :=
    sup_le ((Subgroup.zpowers_le).2 hu'sec) (fun e he => hcomm e he)
  have hq'' : CFSG.IsQuasisimple (kBar K'') := TwoThin.isQuasisimple_hat hK''
  obtain ⟨V'', hV''el, hV''4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq''
      (by rw [PumpTerm.center_eq_bot_of_centerlessBar hcen'', Subgroup.card_bot]; exact odd_one))
  have hV''sq : ∀ v ∈ V'', v * v = 1 := fun v hv => by
    have := (GH74.Uniqueness.SU.SU1.isElemAbelian_iff.1 hV''el).2 v hv
    rwa [sq] at this
  obtain ⟨m, Q, hm2, hQsq, hQcard⟩ := IVK.Proofs2.exists_big_elemAbelian K'' B hBea hBsec V''
    hV''sq (by rw [hV''4]) hcen''
  have hQea : CFSG.IsElementaryAbelian 2 ↥Q := IVK.Proofs2.isElementaryAbelian_two_of_mul_self Q hQsq
  have hBpg : IsPGroup 2 ↥B := CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  obtain ⟨j, hj⟩ := hBpg.exists_card_eq
  have hE4' : 4 ≤ Nat.card ↥E := Nat.le_of_dvd Nat.card_pos hE4
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have hlt' : j < 3 := not_le.mp hlt
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrank := le_pRank_group_of_elem hQea (k := j + m) (by rw [hQcard, hj, pow_add])
  omega

end Rank5

section KeStep

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem false_of_swap_in_E (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hG : C3Hyp G)
    (hs : Th2Std x y K T S) (hL2 : HasL2Model (kBar K) Odd)
    {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) {b : G} {J : Subgroup G}
    (h : Obstr52 B b J) (e₇ : kBar J ≃* alternatingGroup (Fin 7))
    {a q : G} (haK : a ∈ K) (haB : a ∈ B) (hqC : q ∈ CxK x K) (hqB : q ∈ B) (hab : a * q = b)
    (hbC : b ∉ CxK x K) {e : G} (heC : e ∈ CxK x K) (heB : e ∈ B)
    (heN : e ∈ normalizer (J : Set G)) (hesw : (a7Act J e₇ ⟨e, heN⟩).IsSwap) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have he2 : e * e = 1 := hBsq e heB
  have he1 : e ≠ 1 := by
    intro h1
    have h2 : a7Act J e₇ ⟨e, heN⟩ = 1 := by
      have : (⟨e, heN⟩ : ↥(normalizer (J : Set G))) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hesw.isCycle.ne_one h2
  have heo : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact he2) he1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b h.mem) h.ne_one
  have hterm : IsTwoTerminal x K := hs.v2ss.isV2Triple.2.1
  have hxo := hs.orderOf_x
  have hR3 : 3 ≤ pRank 2 ↥(centralizer ({e} : Set G)) :=
    TwoThin.rankThreeCentralizers G hG.kproper.1 hG.kproper.2.1 (by rw [hr4]; norm_num) e heo
  obtain ⟨Ke, hlt⟩ := TwoThin.exists_pumpup_of_involution hxo heo hs.comp heC.1 heC.2 hterm.1 hR3
  obtain ⟨⟨eKe⟩, hKecen, hKe2, hKeN⟩ := hs.pumpup_facts hG hL34 h102 heo hlt
  have hKec : IsPCompIn 2 (centralizer ({e} : Set G)) Ke := hlt.2.1.2.2
  have htr := hterm.2.1 e Ke hlt
  obtain ⟨Λ, hΛ⟩ := C3.Layer1.Iv251.exists_trivData hlt htr
  have ha2 : a * a = 1 := hBsq a haB
  have hae : a * e = e * a := hBc a haB e heB
  have haΛ : a ∈ Λ := hΛ.lam.twoElt a ⟨haK, mem_centralizer_singleton_iff.2 hae⟩
    ⟨1, by rw [pow_one, pow_two]; exact ha2⟩
  have haKe : a ∈ Ke := hΛ.le haΛ
  have hqe : e * q = q * e := hBc e heB q hqB
  have hqKe : q ∈ CxK e Ke := hΛ.cent q hqC hqe
  have ha1 : a ≠ 1 := by
    intro h1
    apply hbC
    rw [h1, one_mul] at hab
    exact hab ▸ hqC
  set ā : kBar Ke := QuotientGroup.mk (⟨a, haKe⟩ : ↥Ke) with hā
  have hā1 : ā ≠ 1 := by
    intro h1
    have hO : a ∈ pPrimeCoreOf 2 Ke := ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
    have hodd : Odd (orderOf a) :=
      Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd Ke) (Subgroup.orderOf_dvd_natCard _ hO)
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
    have h2 : orderOf a = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h0 | h0
      · exact h0
      · rw [h0] at hodd; exact absurd hodd (by decide)
    exact ha1 (orderOf_eq_one_iff.1 h2)
  have hā2 : orderOf ā = 2 := by
    refine orderOf_eq_prime ?_ hā1
    rw [sq, ← QuotientGroup.mk_mul]
    have : (⟨a, haKe⟩ * ⟨a, haKe⟩ : ↥Ke) = 1 := Subtype.ext ha2
    rw [this]
    exact QuotientGroup.mk_one _
  have hbe : b * e = e * b := hBc b h.mem e heB
  have hbN : b ∈ normalizer (Ke : Set G) := hKeN b (mem_centralizer_singleton_iff.2 hbe)
  have hqN : q ∈ normalizer (Ke : Set G) := hKeN q (mem_centralizer_singleton_iff.2 hqe.symm)
  have hρb : barAct Ke ⟨b, hbN⟩ = MulAut.conj ā := by
    have h1 : (⟨b, hbN⟩ : ↥(normalizer (Ke : Set G))) =
        ⟨a, Subgroup.le_normalizer haKe⟩ * ⟨q, hqN⟩ := Subtype.ext hab.symm
    rw [h1, map_mul, barAct_of_mem haKe, (barAct_eq_one_iff _).2 hqKe.2, mul_one]
  have hL2e : HasL2Model (kBar Ke) Odd := TwoThin.hasL2Model_of_mulEquiv eKe.symm hL2
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := C3.Layer1.Thm1.exists_l2_model_of_hasL2Model hL2e
  have hsolv : Group.IsSolvable ↥(centralizer ({MulAut.conj ā} : Set (MulAut (kBar Ke)))) :=
    isSolvable_centralizer_conj hF e₀ hā2
  set S₀ : Subgroup G := J ⊓ centralizer ({e} : Set G) with hS₀
  have hS₀N : S₀ ≤ normalizer (Ke : Set G) := fun s hs => hKeN s hs.2
  let ρ' : ↥S₀ →* MulAut (kBar Ke) := (barAct Ke).comp (Subgroup.inclusion hS₀N)
  have hρ'le : ρ'.range ≤ centralizer ({MulAut.conj ā} : Set (MulAut (kBar Ke))) := by
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hρb]
    show barAct Ke ⟨s.1, hS₀N s.2⟩ * barAct Ke ⟨b, hbN⟩ =
      barAct Ke ⟨b, hbN⟩ * barAct Ke ⟨s.1, hS₀N s.2⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (h.comp.1 s.2.1))
  have hsolvρ : Group.IsSolvable ↥ρ'.range := by
    have := hsolv
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hρ'le)
      (Subgroup.inclusion_injective hρ'le)
  set t' : Perm (Fin 7) := a7Act J e₇ ⟨e, heN⟩ with ht'
  obtain ⟨α⟩ := A7.centralizer_A7_swap_equiv hesw
  let ψ₀ : ↥S₀ →* Perm (Fin 7) := (a7Act J e₇).comp (Subgroup.inclusion
    (fun s hs => Subgroup.le_normalizer hs.1 : S₀ ≤ normalizer (J : Set G)))
  have hψ₀Γ : ∀ s : ↥S₀,
      ψ₀ s ∈ centralizer ({t'} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
    intro s
    refine ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · show a7Act J e₇ ⟨s.1, Subgroup.le_normalizer s.2.1⟩ * a7Act J e₇ ⟨e, heN⟩ =
        a7Act J e₇ ⟨e, heN⟩ * a7Act J e₇ ⟨s.1, Subgroup.le_normalizer s.2.1⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 s.2.2)
    · show a7Act J e₇ ⟨s.1, Subgroup.le_normalizer s.2.1⟩ ∈ alternatingGroup (Fin 7)
      rw [a7Act_of_mem e₇ s.2.1]
      exact (e₇ _).2
  let φ₀ : ↥S₀ →* ↥(centralizer ({t'} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :=
    ψ₀.codRestrict _ hψ₀Γ
  let φ : ↥S₀ →* Perm (Fin 5) := α.toMonoidHom.comp φ₀
  have hφsurj : Function.Surjective φ := by
    intro v
    obtain ⟨y, hy⟩ := α.surjective v
    obtain ⟨y', hy'J, hy'e, hy'ψ⟩ := exists_J_lift e₇ heN he2 he1 y.2.2
      (mem_centralizer_singleton_iff.1 y.2.1)
    refine ⟨⟨y', hy'J, mem_centralizer_singleton_iff.2 hy'e.symm⟩, ?_⟩
    show α (φ₀ ⟨y', hy'J, mem_centralizer_singleton_iff.2 hy'e.symm⟩) = v
    rw [← hy]
    congr 1
    exact Subtype.ext hy'ψ
  obtain ⟨A, hAle, hAsq, hA4⟩ := exists_klein_alt5
  let φX : ↥ρ'.ker →* Perm (Fin 5) := φ.comp ρ'.ker.subtype
  have hAX : A ≤ φX.range := by
    intro v hv
    obtain ⟨s, hs', hsv⟩ := exists_mem_ker_of_solvable_range φ hφsurj ρ' hsolvρ (hAle hv)
    exact ⟨⟨s, hs'⟩, hsv⟩
  set ι₁ : ↥ρ'.ker →* G := S₀.subtype.comp ρ'.ker.subtype with hι₁
  have hι₁inj : Function.Injective ι₁ := S₀.subtype_injective.comp ρ'.ker.subtype_injective
  have hkerX : Odd (Nat.card φX.ker) := by
    have hle : φX.ker.map ι₁ ≤ pPrimeCoreOf 2 J := by
      rintro _ ⟨⟨⟨s, hsS⟩, hsk⟩, hs', rfl⟩
      have hs1 : φ ⟨s, hsS⟩ = 1 := hs'
      have h2 : α (φ₀ ⟨s, hsS⟩) = 1 := hs1
      have h3 : φ₀ ⟨s, hsS⟩ = 1 := by
        rw [← map_one α] at h2
        exact α.injective h2
      have h4 : ψ₀ ⟨s, hsS⟩ = 1 := congrArg Subtype.val h3
      have h5 : a7Act J e₇ ⟨s, Subgroup.le_normalizer hsS.1⟩ = 1 := h4
      have h6 := (barAct_eq_one_iff _).1 ((a7Act_eq_one_iff e₇ _).1 h5)
      exact mem_pPrimeCoreOf_of_commutators h.centerlessBar hsS.1 (fun k hk => h6.2.2 k hk)
    have h7 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective hι₁inj] at h7
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd J) h7
  obtain ⟨EX, hEXsq, hEX4⟩ := exists_exp_two_lift φX hkerX hAX hAsq hA4
  set E : Subgroup G := EX.map ι₁ with hE
  have hEC : E ≤ centralizer ({e} : Set G) := by
    rintro _ ⟨x', -, rfl⟩
    exact x'.1.2.2
  have hEsq : ∀ g ∈ E, g * g = 1 := by
    rintro _ ⟨x', hx', rfl⟩
    rw [← map_mul, hEXsq x' hx', map_one]
  have hE4 : 4 ∣ Nat.card ↥E := by
    rw [hE, Subgroup.card_map_of_injective hι₁inj]
    exact hEX4
  have heE : e ∉ E := by
    rintro ⟨x', -, hx'⟩
    have heJ : e ∈ J := by
      rw [← hx']
      exact x'.1.2.1
    have h1 := a7Act_of_mem e₇ heJ
    have h2 : a7Act J e₇ ⟨e, heN⟩ ∈ alternatingGroup (Fin 7) := by
      rw [show (⟨e, heN⟩ : ↥(normalizer (J : Set G))) = ⟨e, Subgroup.le_normalizer heJ⟩ from rfl,
        h1]
      exact (e₇ _).2
    have h3 := Equiv.Perm.mem_alternatingGroup.1 h2
    have hsw_sign : ∀ g : Perm (Fin 7), g.IsSwap → Equiv.Perm.sign g = -1 := by
      rintro g ⟨a₁, a₂, hne, rfl⟩
      exact Equiv.Perm.sign_swap hne
    have h4 := hsw_sign _ hesw
    rw [h3] at h4
    exact absurd h4 (by decide)
  have hcomm : ∀ g ∈ E, g ∈ centralizerSection Ke (pPrimeCoreOf 2 Ke) := by
    rintro _ ⟨x', -, rfl⟩
    have h1 : ρ' x'.1 = 1 := x'.2
    exact (barAct_eq_one_iff _).1 h1
  exact false_of_klein_centralizing hr4 heo hKec hKecen hEC hEsq hE4 heE hcomm

end KeStep

end CFSG.GH74.GLS.Th2.Obs
