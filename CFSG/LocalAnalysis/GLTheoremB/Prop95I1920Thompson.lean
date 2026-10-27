module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Direct
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Cop
public import CFSG.RankThree.PartOne.MB3.FixedPoint

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open CFSG.LieType.ChevTwo (Chev2CoreCent Chev2KDOut autCentralizer)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

theorem mem_normalizer_of_map_conj_eq_self {t : X}
    (h : K.map (MulAut.conj t).toMonoidHom = K) : t ∈ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    have h1 : t * x * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := by rw [h]; exact hx
    obtain ⟨y, hy, hyx⟩ := h1
    have hyx' : t * y * t⁻¹ = t * x * t⁻¹ := hyx
    have : y = x := mul_left_cancel (mul_right_cancel hyx')
    rw [← this]
    exact hy

theorem exists_pow_central_of_not_mem_normalizer (hK : IsComponentOf K ⊤) {d t : X}
    (ht : t ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set X)))
    (htK : t ∉ Subgroup.normalizer (K : Set X)) {y : X} (hy : y ∈ K) (hyd : y * d = d * y) :
    ∃ e : ℕ, ∀ k ∈ K, y ^ (2 ^ e) * k = k * y ^ (2 ^ e) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₀ := pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) with hT₀
  have hyC : y ∈ Subgroup.centralizer ({d} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 hyd
  have hyT : y * t * y⁻¹ ∈ T₀ :=
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hyC) t).1 ht
  have hc : y * t * y⁻¹ * t⁻¹ ∈ T₀ := T₀.mul_mem hyT (T₀.inv_mem ht)
  obtain ⟨e, he⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
    (Subgroup.centralizer ({d} : Set X))) ⟨_, hc⟩
  have hc1 : (y * t * y⁻¹ * t⁻¹) ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val he
  have hne : K ≠ K.map (MulAut.conj t).toMonoidHom := by
    intro h
    exact htK (mem_normalizer_of_map_conj_eq_self h.symm)
  have hKt := isComponentOf_conj hK t
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * (t * b * t⁻¹) = (t * b * t⁻¹) * a := fun a ha b hb =>
    comp_comm hK hKt hne ha ⟨b, hb, rfl⟩
  refine ⟨e, fun k hk => ?_⟩
  set n := 2 ^ e with hn
  set σ := t * y * t⁻¹ with hσ
  have hcyσ : Commute y σ⁻¹ := (show Commute y σ from hcomm y hy y hy).inv_right
  have hceq : y * t * y⁻¹ * t⁻¹ = y * σ⁻¹ := by simp only [hσ]; group
  rw [hceq, hcyσ.mul_pow, inv_pow] at hc1
  have hyσ : y ^ n = σ ^ n := mul_inv_eq_one.1 hc1
  have hσn : σ ^ n = t * y ^ n * t⁻¹ := by
    simp only [hσ]
    exact (map_pow (MulAut.conj t) y n).symm.trans (by simp [MulAut.conj_apply])
  have hyn : y ^ n ∈ K := Subgroup.pow_mem _ hy n
  have h3 : y ^ n = t * y ^ n * t⁻¹ := hyσ.trans hσn
  have h4 := hcomm k hk (y ^ n) hyn
  rw [← h3] at h4
  exact h4.symm

theorem exists_mem_CKE_pow_eq {E : Subgroup ↥(Subgroup.normalizer (K : Set X))} (k : ↥K)
    (hk : (QuotientGroup.mk k : Kbar K) ∈ autCentralizer (E.map (rhoK K))) :
    ∃ y ∈ CKE K E, (QuotientGroup.mk y : Kbar K) = (QuotientGroup.mk k) ^ Nat.card ↥E := by
  classical
  haveI : Fintype ↥E := Fintype.ofFinite _
  have hz : ∀ e : ↥E, k⁻¹ * K.normalizerMonoidHom (e : ↥(Subgroup.normalizer (K : Set X))) k ∈
      Subgroup.center ↥K := by
    intro e
    have h1 : rhoK K e (QuotientGroup.mk k) = QuotientGroup.mk k :=
      hk (rhoK K e) (Subgroup.mem_map_of_mem _ e.2)
    rw [rhoK_mk] at h1
    exact QuotientGroup.eq.1 h1.symm
  obtain ⟨y, hyfix, w, hw, hyw⟩ := average_fixed (K.normalizerMonoidHom.comp E.subtype) k hz
  refine ⟨y, fun e he => hyfix ⟨e, he⟩, ?_⟩
  rw [hyw, QuotientGroup.mk_mul, QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff w).2 hw, mul_one,
    Nat.card_eq_fintype_card]

theorem isPGroup_two_autCentralizer {p : ℕ} (hp : p.Prime) (hndvd : ¬ p ∣ Nat.card ↥K) {d : X}
    (hd : d ^ p = 1) (hdN : d ∈ Subgroup.normalizer (K : Set X))
    (hT : ∀ y ∈ K, y * d = d * y → ∃ e : ℕ, ∀ k ∈ K, y ^ (2 ^ e) * k = k * y ^ (2 ^ e)) :
    IsPGroup 2 ↥(autCentralizer ((Subgroup.zpowers
      (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set X)))).map (rhoK K))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set E : Subgroup ↥(Subgroup.normalizer (K : Set X)) :=
    Subgroup.zpowers (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set X))) with hE
  have hdE : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈ E := Subgroup.mem_zpowers _
  have hEp : IsPGroup p E := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [hE, Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hd))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hEp
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨y, hyC, hyk⟩ := exists_mem_CKE_pow_eq k hg
  have hyd : (y : X) * d = d * (y : X) := by
    have h1 := congrArg (fun z : ↥K => (z : X)) (hyC _ hdE)
    have h2 : d * (y : X) * d⁻¹ = (y : X) := h1
    calc (y : X) * d = (d * (y : X) * d⁻¹) * d := by rw [h2]
      _ = d * (y : X) := by group
  obtain ⟨e, he⟩ := hT (y : X) y.2 hyd
  have hy1 : (QuotientGroup.mk y : Kbar K) ^ (2 ^ e) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g'
    apply Subtype.ext
    have := he (g' : X) g'.2
    simpa using this.symm
  have hpow : (QuotientGroup.mk k : Kbar K) ^ (Nat.card ↥E * 2 ^ e) = 1 := by
    rw [pow_mul, ← hyk, hy1]
  have hdvd1 : orderOf (QuotientGroup.mk k : Kbar K) ∣ Nat.card ↥E * 2 ^ e :=
    orderOf_dvd_of_pow_eq_one hpow
  have hdvdK : orderOf (QuotientGroup.mk k : Kbar K) ∣ Nat.card ↥K :=
    (orderOf_dvd_natCard _).trans (Subgroup.card_quotient_dvd_card _)
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk k : Kbar K)) (Nat.card ↥E) := by
    rw [hm]
    refine Nat.Coprime.pow_right m ?_
    refine (Nat.Coprime.coprime_dvd_left hdvdK ?_)
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd |>.symm
  have hdvd2 : orderOf (QuotientGroup.mk k : Kbar K) ∣ 2 ^ e := hcop.dvd_of_dvd_mul_left hdvd1
  refine ⟨e, ?_⟩
  apply Subtype.ext
  simpa using orderOf_dvd_iff_pow_eq_one.1 hdvd2

theorem pCoreOf_le_normalizer_of_coprime (hCore : Chev2CoreCent) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : IsComponentOf K ⊤) (hCh : IsChevTwo (Kbar K))
    (hndvd : ¬ p ∣ Nat.card ↥K) {d : X} (hd : d ^ p = 1)
    (hdN : d ∈ Subgroup.normalizer (K : Set X)) :
    pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht
  by_contra htK
  have hT : ∀ y ∈ K, y * d = d * y → ∃ e : ℕ, ∀ k ∈ K, y ^ (2 ^ e) * k = k * y ^ (2 ^ e) :=
    fun y hy hyd => exists_pow_central_of_not_mem_normalizer hK ht htK hy hyd
  have h2 := isPGroup_two_autCentralizer hp hndvd hd hdN hT
  haveI : IsSimpleGroup (Kbar K) := hK.2.2.2
  have hnab := (isQuasisimple_of_comp hK).2.2
  set dN : ↥(Subgroup.normalizer (K : Set X)) := ⟨d, hdN⟩ with hdNdef
  set R : Subgroup (MulAut (Kbar K)) := (Subgroup.zpowers dN).map (rhoK K) with hR
  have hRp : IsPGroup p R := by
    haveI : Fact p.Prime := ⟨hp⟩
    refine IsPGroup.map (IsPGroup.of_card_dvd_pow (n := 1) ?_) _
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hd))
  have hbot : autCentralizer R = ⊥ := by
    have h1 := hCore (Kbar K) inferInstance hnab hCh p hp hp2 R hRp
    have h3 : autCentralizer R ≤ pCoreOf 2 (autCentralizer R) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl
        (fun x hx => Subgroup.le_normalizer hx) (by simpa using h2)
    rw [h1] at h3
    exact eq_bot_iff.2 h3
  set a : MulAut (Kbar K) := rhoK K dN with ha
  have hRa : R = Subgroup.zpowers a := MonoidHom.map_zpowers _ _
  have hfix : ∀ x : Kbar K, a x = x → x = 1 := by
    intro x hx
    have hx' : x ∈ autCentralizer R := by
      intro α hα
      rw [hRa] at hα
      have hstab : a ∈ MulAction.stabilizer (MulAut (Kbar K)) x := hx
      exact Subgroup.zpowers_le.2 hstab hα
    rw [hbot, Subgroup.mem_bot] at hx'
    exact hx'
  have ha1 : a ≠ 1 := by
    intro h
    haveI : Nontrivial (Kbar K) := IsSimpleGroup.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : Kbar K)
    exact hx (hfix x (by rw [h]; rfl))
  have hap : a ^ p = 1 := by
    rw [ha, ← map_pow]
    have : dN ^ p = 1 := Subtype.ext (by simpa using hd)
    rw [this, map_one]
  have hprime : (orderOf a).Prime := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hap) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) ha1
    · rw [h1]
      exact hp
  have hnil := CFSG.RankThree.PartOne.MB3.isNilpotent_of_fixedPointFree_prime a hprime hfix
  have hle := Group.nilpotencyClass_le_one_of_isSimple_of_isNilpotent (G := Kbar K)
  have hcomm := (Group.IsNilpotent.nilpotencyClass_le_one_iff).mp hle
  obtain ⟨u, v, huv⟩ := hnab
  exact huv (hcomm.is_comm.comm u v)

theorem pCoreOf_le_normalizer_of_chev (hCore : Chev2CoreCent) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : IsComponentOf K ⊤) (hCh : IsChevTwo (Kbar K)) {d : X} (hd : d ^ p = 1) :
    pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  by_cases hdvd : p ∣ Nat.card ↥K
  · exact pCoreOf_centralizer_singleton_le_normalizer_of_dvd hp hp2 hK hdvd hd
  · by_cases hdN : d ∈ Subgroup.normalizer (K : Set X)
    · exact pCoreOf_le_normalizer_of_coprime hCore hp hp2 hK hCh hdvd hd hdN
    · exact pCoreOf_le_normalizer_of_not_mem_normalizer hp hp2 hK hd hdN

theorem pNormalizesLarge_of_coreCent (hCore : Chev2CoreCent) : PNormalizesLarge :=
  fun _ _ _ _ hp hp2 _ hK hCh _ _ hd => pCoreOf_le_normalizer_of_chev hCore hp hp2 hK hCh hd

theorem input19_20_2_of_kdout_corecent (hKD : Chev2KDOut) (hCore : Chev2CoreCent) : Input19_20_2 :=
  input19_20_2_direct hKD hCore (pNormalizesLarge_of_coreCent hCore)

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
