module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64J
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

open Equiv Equiv.Perm Subgroup CFSG
open CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs CFSG.ABGLocalTools CFSG.GH74.GLS.IVK
open scoped commutatorElement

namespace CFSG.GH74.GLS.Th2.Obs

theorem isSolvable_centralizer_conj_A7 {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 7)) {u : K} (hu : orderOf u = 2) :
    Group.IsSolvable ↥(Subgroup.centralizer ({MulAut.conj u} : Set (MulAut K))) := by
  classical
  set θ := Th2.Bal.a7Theta e with hθ
  set σ : Perm (Fin 7) := ((e u : alternatingGroup (Fin 7)) : Perm (Fin 7)) with hσ
  have hθσ : θ σ = MulAut.conj u := by
    rw [hσ, hθ, Th2.Bal.a7Theta_even e (e u), e.symm_apply_apply]
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu
    omega
  have hσsq : σ ^ 2 = 1 := by
    have h1 : (e u) ^ 2 = 1 := by
      rw [← map_pow, show u ^ 2 = 1 by rw [← hu]; exact pow_orderOf_eq_one u, map_one]
    have := congrArg Subtype.val h1
    simpa [hσ] using this
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hu1
    have h2 : e u = 1 := Subtype.ext h1
    exact e.injective (h2.trans (map_one e).symm)
  have hσeven : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.1 (e u).2
  have hcard48 : Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 7)))) = 48 := by
    rcases A7.involution_cycleType σ hσsq hσ1 with h | h | h
    · exfalso
      rw [Equiv.Perm.sign_of_cycleType, h] at hσeven
      revert hσeven
      decide
    · exact A7.card_centralizer_S7_two_two h
    · exact A7.card_centralizer_S7_two_two_two h
  have hcent : Subgroup.centralizer ({MulAut.conj u} : Set (MulAut K)) =
      (centralizer ({σ} : Set (Perm (Fin 7)))).map θ.toMonoidHom := by
    ext g
    obtain ⟨g', rfl⟩ := θ.surjective g
    rw [Subgroup.mem_centralizer_singleton_iff, ← hθσ, Subgroup.mem_map]
    constructor
    · intro hg
      refine ⟨g', ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply θ.injective
      rw [map_mul, map_mul]
      exact hg
    · rintro ⟨h', hh', hh⟩
      have hh'' : h' = g' := θ.injective hh
      subst hh''
      have := Subgroup.mem_centralizer_singleton_iff.1 hh'
      show θ h' * θ σ = θ σ * θ h'
      rw [← map_mul, ← map_mul, this]
  have hcard : Nat.card ↥(Subgroup.centralizer ({MulAut.conj u} : Set (MulAut K))) = 48 := by
    rw [hcent, Subgroup.card_map_of_injective θ.injective]
    exact hcard48
  exact CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcard]; norm_num)

section KeStep

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem exists_klein_data_of_fixed_S5
    {B : Subgroup G} {b e a : G} {Ke J : Subgroup G}
    (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (h : Obstr52 B b J) (e7 : kBar J ≃* alternatingGroup (Fin 7))
    (heB : e ∈ B) (heN : e ∈ normalizer (J : Set G))
    (hesw : (a7Act J e7 ⟨e, heN⟩).IsSwap)
    (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (haKe : a ∈ Ke)
    (hKeN : ∀ g ∈ centralizer ({e} : Set G), g ∈ normalizer (Ke : Set G))
    (hKe7 : Nonempty (kBar Ke ≃* alternatingGroup (Fin 7)))
    (hbN : b ∈ normalizer (Ke : Set G))
    (hρb : barAct Ke ⟨b, hbN⟩ =
      MulAut.conj (QuotientGroup.mk (⟨a, haKe⟩ : ↥Ke))) :
    ∃ E : Subgroup G, E ≤ centralizer ({e} : Set G) ∧
      (∀ x ∈ E, x * x = 1) ∧ 4 ∣ Nat.card ↥E ∧ e ∉ E ∧
        E ≤ centralizerSection Ke (pPrimeCoreOf 2 Ke) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have he2 : e * e = 1 := hBsq e heB
  have he1 : e ≠ 1 := by
    intro h1
    have h2 : a7Act J e7 ⟨e, heN⟩ = 1 := by
      have : (⟨e, heN⟩ : ↥(normalizer (J : Set G))) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hesw.isCycle.ne_one h2
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
  obtain ⟨eK⟩ := hKe7
  have hsolv : Group.IsSolvable ↥(centralizer ({MulAut.conj ā} : Set (MulAut (kBar Ke)))) :=
    isSolvable_centralizer_conj_A7 (eK) hā2
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
  set t' : Perm (Fin 7) := a7Act J e7 ⟨e, heN⟩ with ht'
  obtain ⟨α⟩ := A7.centralizer_A7_swap_equiv hesw
  let ψ₀ : ↥S₀ →* Perm (Fin 7) := (a7Act J e7).comp (Subgroup.inclusion
    (fun s hs => Subgroup.le_normalizer hs.1 : S₀ ≤ normalizer (J : Set G)))
  have hψ₀Γ : ∀ s : ↥S₀,
      ψ₀ s ∈ centralizer ({t'} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
    intro s
    refine ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · show a7Act J e7 ⟨s.1, Subgroup.le_normalizer s.2.1⟩ * a7Act J e7 ⟨e, heN⟩ =
        a7Act J e7 ⟨e, heN⟩ * a7Act J e7 ⟨s.1, Subgroup.le_normalizer s.2.1⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 s.2.2)
    · show a7Act J e7 ⟨s.1, Subgroup.le_normalizer s.2.1⟩ ∈ alternatingGroup (Fin 7)
      rw [a7Act_of_mem e7 s.2.1]
      exact (e7 _).2
  let φ₀ : ↥S₀ →* ↥(centralizer ({t'} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) :=
    ψ₀.codRestrict _ hψ₀Γ
  let φ : ↥S₀ →* Perm (Fin 5) := α.toMonoidHom.comp φ₀
  have hφsurj : Function.Surjective φ := by
    intro v
    obtain ⟨y, hy⟩ := α.surjective v
    obtain ⟨y', hy'J, hy'e, hy'ψ⟩ := exists_J_lift e7 heN he2 he1 y.2.2
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
      have h5 : a7Act J e7 ⟨s, Subgroup.le_normalizer hsS.1⟩ = 1 := h4
      have h6 := (barAct_eq_one_iff _).1 ((a7Act_eq_one_iff e7 _).1 h5)
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
    have h1 := a7Act_of_mem e7 heJ
    have h2 : a7Act J e7 ⟨e, heN⟩ ∈ alternatingGroup (Fin 7) := by
      rw [show (⟨e, heN⟩ : ↥(normalizer (J : Set G))) = ⟨e, Subgroup.le_normalizer heJ⟩ from rfl,
        h1]
      exact (e7 _).2
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
  exact ⟨E, hEC, hEsq, hE4, heE, hcomm⟩

theorem false_of_swap_in_E_A7 (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hG : C3Hyp G)
    (hs : Th2Std x y K T S) (hA7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
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
  have hKe7 : Nonempty (kBar Ke ≃* alternatingGroup (Fin 7)) :=
    ⟨eKe.trans (Classical.choice hA7)⟩
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
  have hρb' : barAct Ke ⟨b, hbN⟩ =
      MulAut.conj (QuotientGroup.mk (⟨a, haKe⟩ : ↥Ke)) := by
    simpa [hā] using hρb
  obtain ⟨E, hEC, hEsq, hE4, heE, hcomm⟩ :=
    exists_klein_data_of_fixed_S5 hB h e₇ heB heN hesw ha1 ha2 haKe hKeN hKe7 hbN hρb'
  exact false_of_klein_centralizing hr4 heo hKec hKecen hEC hEsq hE4 heE hcomm

end KeStep

variable {G : Type} [Group G] [Finite G]

end CFSG.GH74.GLS.Th2.Obs
