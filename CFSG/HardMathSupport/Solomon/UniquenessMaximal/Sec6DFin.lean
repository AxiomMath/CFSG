module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DAct

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_normalizes_sylow {p : ℕ} [hp : Fact p.Prime] {R P M : Subgroup G} (hRM : R ≤ M)
    (hRc : Nat.card R = p ^ (Nat.card M).factorization p) (hRp : IsPGroup p ↥R)
    (hP : IsPGroup p ↥P) (hPM : P ≤ M) (hPR : P ≤ Subgroup.normalizer (R : Set G)) : P ≤ R := by
  have hcard := card_sup_mul_card_inf hPR
  have hsup : IsPGroup p ↥(R ⊔ P) := by
    obtain ⟨a, ha⟩ := exists_card_eq_pow hRp
    obtain ⟨b, hb⟩ := exists_card_eq_pow hP
    have hdvd : Nat.card ↥(R ⊔ P) ∣ p ^ (a + b) := by
      rw [pow_add, ← ha, ← hb, ← hcard]; exact Dvd.intro _ rfl
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
    exact IsPGroup.of_card hc
  have := eq_of_le_sylow (p := p) le_sup_left (sup_le hRM hPM) hsup hRc
  calc P ≤ R ⊔ P := le_sup_right
    _ = R := this.symm

section HES

variable {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q']

theorem index_mul_card_of_le' {N H : Subgroup Q} (h : N ≤ H) :
    (N.subgroupOf H).index * Nat.card N = Nat.card H := by
  have := Subgroup.index_mul_card (H := N.subgroupOf H)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at this

theorem HasElemSection3.map_of_inj (f : Q →* Q') (hf : Function.Injective f) {S : Subgroup Q}
    {n : ℕ} (h : HasElemSection3 S n) : HasElemSection3 (S.map f) n := by
  obtain ⟨H, N, hNH, hHS, hnorm, hcomm, hexp, hidx⟩ := h
  refine ⟨H.map f, N.map f, Subgroup.map_mono hNH, Subgroup.map_mono hHS, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩ _ ⟨k, hk, rfl⟩
    exact ⟨h * k * h⁻¹, hnorm h hh k hk, by simp⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact ⟨g * h * g⁻¹ * h⁻¹, hcomm g hg h hh, by simp⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨g ^ 3, hexp g hg, by simp⟩
  · have h1 := index_mul_card_of_le' hNH
    have h2 := index_mul_card_of_le' (Subgroup.map_mono (f := f) hNH)
    rw [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf] at h2
    have : ((N.map f).subgroupOf (H.map f)).index = (N.subgroupOf H).index :=
      Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := N)) (h2.trans h1.symm)
    rw [this]; exact hidx

theorem HasElemSection3.of_subgroupOf {S M : Subgroup Q} (hSM : S ≤ M) {n : ℕ}
    (h : HasElemSection3 S n) : HasElemSection3 (S.subgroupOf M) n := by
  obtain ⟨H, N, hNH, hHS, hnorm, hcomm, hexp, hidx⟩ := h
  refine ⟨H.subgroupOf M, N.subgroupOf M, fun z hz => hNH hz, fun z hz => hHS hz, ?_, ?_, ?_, ?_⟩
  · intro h hh k hk
    have := hnorm h hh k hk
    exact this
  · intro g hg h hh
    exact hcomm g hg h hh
  · intro g hg
    exact hexp g hg
  · have hNM : N ≤ M := hNH.trans (hHS.trans hSM)
    have hHM : H ≤ M := hHS.trans hSM
    have h1 := index_mul_card_of_le' hNH
    have h2 := index_mul_card_of_le' (N := N.subgroupOf M) (H := H.subgroupOf M) (fun z hz => hNH hz)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv] at h2
    have : ((N.subgroupOf M).subgroupOf (H.subgroupOf M)).index = (N.subgroupOf H).index :=
      Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := N)) (h2.trans h1.symm)
    rw [this]; exact hidx

end HES

theorem conj_mem_cq {Ka : Subgroup G} {y c : G} (hy : y ∈ Subgroup.normalizer (Ka : Set G))
    (hc : c ∈ LocalBalance.centralizerQuot Ka (GLAPPrimeCoreOf 3 Ka)) :
    y * c * y⁻¹ ∈ LocalBalance.centralizerQuot Ka (GLAPPrimeCoreOf 3 Ka) := by
  have hcN : c ∈ Subgroup.normalizer (Ka : Set G) := hc.1
  have hyc : y * c * y⁻¹ ∈ Subgroup.normalizer (Ka : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hcN) (Subgroup.inv_mem _ hy)
  rw [Lemma513Ns.mem_centralizerQuot_iff_barAut' 3 (⟨y * c * y⁻¹, hyc⟩ :
    ↥(Subgroup.normalizer (Ka : Set G)))]
  have h1 : barAut 3 Ka ⟨c, hcN⟩ = 1 :=
    (Lemma513Ns.mem_centralizerQuot_iff_barAut' 3 (⟨c, hcN⟩ :
      ↥(Subgroup.normalizer (Ka : Set G)))).1 hc
  have : (⟨y * c * y⁻¹, hyc⟩ : ↥(Subgroup.normalizer (Ka : Set G))) =
      ⟨y, hy⟩ * ⟨c, hcN⟩ * ⟨y, hy⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]

theorem final_contra (iL3 : InputL3U3Facts) (iK : InputKType) (h514 : Lemma514) (h515 : Lemma515)
    {m : ℕ} {B : Subgroup G} {b : G} {L A : Subgroup G} (e : Env m B b L A) {x y : G}
    (hxB : x ∈ B) (hx1 : x ≠ 1) {K : Subgroup G}
    (hK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K) (hy : y ∈ B)
    (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (h3 : (Subgroup.normalizer (K : Set G)).relIndex B = 3) {R K₀ : Subgroup G}
    (hR : RData (Subgroup.centralizer ({x} : Set G)) B K y R) (hk : K0Data B K x y K₀)
    (hxW : x ∈ Zc R) (hWfix : ∀ z ∈ Zc R, y * z = z * y → z ∈ Subgroup.zpowers x)
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hxA : x ∉ A) : False := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥B := isPGroup_of_isElemAbelian e.X.Bel
  set X := Subgroup.centralizer ({x} : Set G) with hX
  have hBX : B ≤ X := fun c hc => by
    rw [hX, Subgroup.mem_centralizer_singleton_iff]; exact ea_comm e.X.Bel hc hxB
  have hKst : bClosure B K ≤ Subgroup.normalizer (K : Set G) :=
    bClosure_le_normalizer e.X.Bel hBX hK hy hyN h3
  have hK₀st : K₀ ≤ bClosure B K := hk.le.trans inf_le_left
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_le_centralizer hK.1
  have hx3 : x ^ 3 = 1 := e.X.Bel.2 x hxB
  have cx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  set D := Subgroup.zpowers x ⊔ (B ⊓ K₀) with hD
  have hxR : Subgroup.zpowers x ≤ R := Subgroup.zpowers_le.2 (Zc_le R hxW)
  have hDst : D ≤ bClosure B K :=
    sup_le (hxR.trans hR.R_le) (inf_le_right.trans hK₀st)
  have hDM : D ≤ B ⊓ Subgroup.normalizer (K : Set G) :=
    sup_le (le_inf (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hxN))
      (le_inf inf_le_left (inf_le_right.trans (hK₀st.trans hKst)))
  have hinfx : Subgroup.zpowers x ⊓ (B ⊓ K₀) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have : u ∈ (B ⊓ K₀) ⊓ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := ⟨hu.2, Subgroup.mem_sup_left hu.1⟩
    rw [hk.inf_cq] at this
    exact this
  have hBK₀p : IsPGroup 3 ↥(B ⊓ K₀) := hBp.to_inf_left
  have hBK₀c : 3 ≤ Nat.card ↥(B ⊓ K₀) := by
    obtain ⟨j, hj⟩ := exists_card_eq_pow hBK₀p
    have hj1 : j ≠ 0 := by
      rintro rfl
      exact hk.ne (Subgroup.eq_bot_of_card_eq _ (by simpa using hj))
    rw [hj]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hDc : 9 ≤ Nat.card ↥D := by
    have hN : B ⊓ K₀ ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro u hu
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (Commute.zpow_left (show Commute x u from ea_comm e.X.Bel hxB hu.1) i).eq
    have h : Nat.card ↥D * Nat.card ↥(⊥ : Subgroup G) =
        Nat.card ↥(Subgroup.zpowers x) * Nat.card ↥(B ⊓ K₀) := by
      have := card_sup_mul_card_inf hN
      rwa [hinfx] at this
    rw [Subgroup.card_bot, cx] at h
    omega
  have hMc : Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set G)) = 27 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (K : Set G)) (K := B)
    rw [h3, e.X.Bc, inf_comm] at h
    omega
  have hAM : A ≤ B ⊓ Subgroup.normalizer (K : Set G) := le_inf e.X.AB hAN
  have hAD : A ⊓ D ≠ ⊥ := by
    intro h0
    have hN : D ≤ Subgroup.normalizer (A : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro u hu
      exact Subgroup.mem_centralizer_iff.2 fun a ha => (ea_comm e.X.Bel (e.X.AB ha) (hDM hu).1)
    have h := card_sup_mul_card_inf hN
    rw [h0, Subgroup.card_bot, e.X.Ac] at h
    have h2 : Nat.card ↥(A ⊔ D) ≤ 27 := hMc ▸ Subgroup.card_le_of_le (sup_le hAM hDM)
    omega
  obtain ⟨a, haAD, ha1⟩ : ∃ a ∈ A ⊓ D, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hAD ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have haA : a ∈ A := haAD.1
  have haB : a ∈ B := e.X.AB haA
  have haD : a ∈ D := haAD.2
  have haR : a ∈ R := by
    have hle : B ⊓ bClosure B K ≤ R :=
      le_of_normalizes_sylow (p := 3) hR.R_le hR.R_card hR.R_p hBp.to_inf_left inf_le_right
        (inf_le_left.trans hR.R_inv)
    exact hle ⟨haB, hDst haD⟩
  have hay : a * y = y * a := ea_comm e.X.Bel haB hy
  have haW : a ∉ Zc R := by
    intro haZ
    have hz := hWfix a haZ hay.symm
    have ha3 : a ^ 3 = 1 := e.X.Bel.2 a haB
    have ca : Nat.card ↥(Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
    have heq : Subgroup.zpowers a = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz) (by rw [ca, cx])
    have : x ∈ Subgroup.zpowers a := by rw [heq]; exact Subgroup.mem_zpowers x
    exact hxA ((Subgroup.zpowers_le.2 haA) this)
  have hσa : sg y⁻¹ a = a := by
    show y⁻¹ * a * y⁻¹⁻¹ = a
    rw [inv_inv]
    calc y⁻¹ * a * y = y⁻¹ * (a * y) := by group
      _ = y⁻¹ * (y * a) := by rw [hay]
      _ = a := by group
  have hRa : a ∈ Triple.R y⁻¹ (R ⊓ K) := by rw [hR.Rdef]; exact haR
  have hnaW : a ∉ Triple.W y⁻¹ (R ⊓ K) := by rw [hR.Wdef]; exact haW
  obtain ⟨S', hS'R, hS'a, hS'Z, hS'sec⟩ := hR.triple.exists_section hR.W_card hRa hσa hnaW
  rw [hR.Rdef] at hS'R
  have hS'Z' : ∀ z ∈ S', (∀ s ∈ S', z * s = s * z) → z ∈ Zc R := by
    intro z hz hzc
    have := hS'Z z hz hzc
    rwa [hR.Wdef] at this
  have hS'p : IsPGroup 3 ↥S' := hR.R_p.to_le hS'R
  set Ka := kOf L A a with hKa
  have hS'N : S' ≤ Subgroup.normalizer (Ka : Set G) := by
    intro s hs
    refine Ka_N h515 e haA ha1 ?_
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (show Commute a s from (hS'a s hs).symm) i).eq
  have hYt : IsLThreeEps (barOf 3 Ka) := Ka_type iK e haA ha1
  set φ : ↥S' →* MulAut (barOf 3 Ka) := (barAut 3 Ka).comp (Subgroup.inclusion hS'N) with hφ
  by_cases hker : φ.ker = ⊥
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
    have h1 := (hS'sec.of_subgroupOf (le_refl S')).map_of_inj φ hinj
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h1
    have hP : IsPGroup 3 ↥φ.range := hS'p.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    exact (iL3 (barOf 3 Ka) hYt).2.2.2 φ.range hP h1
  ·
    set T : Subgroup G := φ.ker.map S'.subtype with hT
    have hTS : T ≤ S' := Subgroup.map_subtype_le _
    have hT0 : T ≠ ⊥ := fun h0 =>
      hker ((Subgroup.map_eq_bot_iff_of_injective _ S'.subtype_injective).1 h0)
    have hTp : IsPGroup 3 ↥T := hR.R_p.to_le (hTS.trans hS'R)
    have hTN : S' ≤ Subgroup.normalizer (T : Set G) := by
      intro s hs
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨t0, ht0, rfl⟩ := hn
      refine ⟨⟨s, hs⟩ * t0 * ⟨s, hs⟩⁻¹, ?_, rfl⟩
      exact (inferInstance : φ.ker.Normal).conj_mem t0 ht0 ⟨s, hs⟩
    obtain ⟨n, hnT, hn1, hnc⟩ := exists_fixed_ne_one (p := 3) hS'p hTN hT0 hTp
    obtain ⟨t0, ht0, rfl⟩ := hnT
    have hnS : (t0 : G) ∈ S' := t0.2
    have hnZ : (t0 : G) ∈ Zc R := hS'Z' _ hnS fun s hs => (hnc s hs).symm
    have hφt : barAut 3 Ka ⟨(t0 : G), hS'N hnS⟩ = 1 := ht0
    have hncq : (t0 : G) ∈ LocalBalance.centralizerQuot Ka (GLAPPrimeCoreOf 3 Ka) :=
      (Lemma513Ns.mem_centralizerQuot_iff_barAut' 3 (⟨(t0 : G), hS'N hnS⟩ :
        ↥(Subgroup.normalizer (Ka : Set G)))).2 hφt
    set D' : Subgroup G := Zc R ⊓ LocalBalance.centralizerQuot Ka (GLAPPrimeCoreOf 3 Ka) with hD'
    have hD'ne : D' ≠ ⊥ := by
      intro h0
      have : (t0 : G) ∈ D' := ⟨hnZ, hncq⟩
      rw [h0, Subgroup.mem_bot] at this
      exact hn1 this
    have hD'p : IsPGroup 3 ↥D' := hR.R_p.to_le (inf_le_left.trans (Zc_le R))
    have hyKa : y ∈ Subgroup.normalizer (Ka : Set G) := Ka_B h515 e haA ha1 hy
    have hyD' : y ∈ Subgroup.normalizer (D' : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun c hc => ?_
      have hyZ := normalizer_Zc (hR.R_inv hy)
      exact ⟨(Subgroup.mem_normalizer_iff.1 hyZ c).1 hc.1, conj_mem_cq hyKa hc.2⟩
    obtain ⟨z, hzD, hz1, hzc⟩ := exists_fixed_ne_one (p := 3) (P := Subgroup.zpowers y)
      (hBp.to_le (Subgroup.zpowers_le.2 hy)) (Subgroup.zpowers_le.2 hyD') hD'ne hD'p
    have hzx : z ∈ Subgroup.zpowers x :=
      hWfix z hzD.1 (hzc y (Subgroup.mem_zpowers y))
    have hzB : z ∈ B := (Subgroup.zpowers_le.2 hxB) hzx
    have hz3 : z ^ 3 = 1 := e.X.Bel.2 z hzB
    have cz : Nat.card ↥(Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
    have heq : Subgroup.zpowers z = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzx) (by rw [cz, cx])
    have hxD' : x ∈ D' := by
      have : x ∈ Subgroup.zpowers z := by rw [heq]; exact Subgroup.mem_zpowers x
      exact (Subgroup.zpowers_le.2 hzD) this
    exact hxA (mem_A_of_centralizes iL3 iK h514 h515 e haA ha1 hxB hxD'.2.2.2)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
