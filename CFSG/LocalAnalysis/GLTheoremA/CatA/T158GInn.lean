module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I91
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S3
open CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Basic

variable {Ω : Type} [Group Ω]

theorem t158g_mem_sup_zpowers {x₁ x₂ : Ω} (hc : x₁ * x₂ = x₂ * x₁) {a : Ω}
    (ha : a ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) : ∃ i j : ℤ, a = x₁ ^ i * x₂ ^ j := by
  have hnorm : Subgroup.zpowers x₁ ≤ Subgroup.normalizer (Subgroup.zpowers x₂ : Set Ω) := by
    intro u hu
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ((Commute.zpow_zpow (show Commute x₁ x₂ from hc) i j).eq).symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at ha
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.1 ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  exact ⟨i, j, rfl⟩

theorem t158g_comm_of_mem_sup {x₁ x₂ : Ω} (hc : x₁ * x₂ = x₂ * x₁) {a a' : Ω}
    (ha : a ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
    (ha' : a' ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) : a * a' = a' * a := by
  obtain ⟨i, j, rfl⟩ := t158g_mem_sup_zpowers hc ha
  obtain ⟨k, l, rfl⟩ := t158g_mem_sup_zpowers hc ha'
  have h : Commute x₁ x₂ := hc
  have h1 : Commute (x₁ ^ i * x₂ ^ j) (x₁ ^ k) :=
    (Commute.zpow_zpow_self x₁ i k).mul_left (h.symm.zpow_zpow j k)
  have h2 : Commute (x₁ ^ i * x₂ ^ j) (x₂ ^ l) :=
    (h.zpow_zpow i l).mul_left (Commute.zpow_zpow_self x₂ j l)
  exact (h1.mul_right h2).eq

theorem t158g_zpow_pow {x : Ω} {p : ℕ} (hx : x ^ p = 1) (k : ℤ) : (x ^ k) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem t158g_pow_eq_one_of_mem_sup {p : ℕ} {x₁ x₂ : Ω} (hc : x₁ * x₂ = x₂ * x₁) (hx1 : x₁ ^ p = 1)
    (hx2 : x₂ ^ p = 1) {a : Ω} (ha : a ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) : a ^ p = 1 := by
  obtain ⟨i, j, rfl⟩ := t158g_mem_sup_zpowers hc ha
  have hcij : Commute (x₁ ^ i) (x₂ ^ j) := Commute.zpow_zpow (show Commute x₁ x₂ from hc) i j
  rw [hcij.mul_pow, t158g_zpow_pow hx1 i, t158g_zpow_pow hx2 j, mul_one]

theorem t158g_indRel_eq {p : ℕ} {L : Subgroup Ω} {a a' : Ω}
    (h : ∀ l ∈ L, a⁻¹ * l * a = a'⁻¹ * l * a') : indRel p L a = indRel p L a' := by
  funext q q'
  apply propext
  constructor
  · rintro ⟨l, l', hl, hl', hll'⟩
    exact ⟨l, l', hl, hl', by rw [hll', h l l.2]⟩
  · rintro ⟨l, l', hl, hl', hll'⟩
    exact ⟨l, l', hl, hl', by rw [hll', ← h l l.2]⟩

theorem t158g_innDiagOn_of_conj_eq {p : ℕ} {L : Subgroup Ω} {a a' : Ω}
    (ha' : a' ∈ Subgroup.normalizer (L : Set Ω))
    (h : ∀ k : ℤ, ∀ l ∈ L, (a ^ k)⁻¹ * l * a ^ k = (a' ^ k)⁻¹ * l * a' ^ k)
    (hA : InnDiagOn p (Subgroup.zpowers a) L) : InnDiagOn p (Subgroup.zpowers a') L := by
  refine ⟨Subgroup.zpowers_le.2 ha', Canonical.largeEvenMarking_mono ?_ hA.2⟩
  intro _ _ _ _ _ θ hP b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  obtain ⟨φ, hφ, hind⟩ := hP (a ^ k) (Subgroup.zpow_mem_zpowers a k)
  refine ⟨φ, hφ, ?_⟩
  rwa [← t158g_indRel_eq (h k)]

theorem t158g_innDiagOn_of_mul_pow {p : ℕ} {L : Subgroup Ω} {x₁ x₂ : Ω} (hc : x₁ * x₂ = x₂ * x₁)
    (hLc : L ≤ Subgroup.centralizer ({x₁} : Set Ω)) (hx2L : x₂ ∈ Subgroup.normalizer (L : Set Ω)) (m : ℤ)
    (h : InnDiagOn p (Subgroup.zpowers (x₂ * x₁ ^ m)) L) : InnDiagOn p (Subgroup.zpowers x₂) L := by
  refine t158g_innDiagOn_of_conj_eq hx2L (fun k l hl => ?_) h
  have hcomm : Commute x₂ (x₁ ^ m) := (show Commute x₁ x₂ from hc).symm.zpow_right m
  rw [hcomm.mul_zpow]
  have hy : (x₂ ^ k)⁻¹ * l * x₂ ^ k ∈ L := by
    have hk : (x₂ ^ k)⁻¹ ∈ Subgroup.normalizer (L : Set Ω) :=
      Subgroup.inv_mem _ (Subgroup.zpow_mem _ hx2L k)
    have := (Subgroup.mem_normalizer_iff.1 hk l).1 hl
    simpa using this
  have hcy : Commute ((x₁ ^ m) ^ k) ((x₂ ^ k)⁻¹ * l * x₂ ^ k) := by
    have h1 : (x₂ ^ k)⁻¹ * l * x₂ ^ k ∈ Subgroup.centralizer ({x₁} : Set Ω) := hLc hy
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact ((Commute.zpow_left (show Commute x₁ _ from h1.symm) m).zpow_left k)
  calc (x₂ ^ k * (x₁ ^ m) ^ k)⁻¹ * l * (x₂ ^ k * (x₁ ^ m) ^ k)
      = ((x₁ ^ m) ^ k)⁻¹ * ((x₂ ^ k)⁻¹ * l * x₂ ^ k) * (x₁ ^ m) ^ k := by group
    _ = ((x₁ ^ m) ^ k)⁻¹ * ((x₁ ^ m) ^ k * ((x₂ ^ k)⁻¹ * l * x₂ ^ k)) := by
        rw [hcy.eq]
        group
    _ = (x₂ ^ k)⁻¹ * l * x₂ ^ k := by group

theorem t158g_normalizer_of_fgOn {p : ℕ} {g : Ω} {L : Subgroup Ω} (h : FGOn p g L) :
    g ∈ Subgroup.normalizer (L : Set Ω) :=
  h.elim (fun h => h.1) (fun h => h.1.1)

end Basic

section Fin

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem t158g_card_pSimple_dvd {p : ℕ} (J : Subgroup Ω) : Nat.card (PSimple p J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem t158g_prime_dvd_card_pSimple {p : ℕ} (hp : p.Prime) {X J : Subgroup Ω} (hJ : GLAPComponent p X J) :
    p ∣ Nat.card (PSimple p J) := by
  by_contra hnd
  obtain ⟨-, hnab⟩ := chev_pSimple_simple_nonabelian hp hJ
  obtain ⟨a, b, hab⟩ := hnab
  have hbot := glaPPrimeCore_pSimple_eq_bot hp hJ
  have htop : (⊤ : Subgroup (PSimple p J)) ≤ GLAPPrimeCore p (PSimple p J) := by
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [Subgroup.card_top]
    exact (hp.coprime_iff_not_dvd).2 hnd
  rw [hbot, top_le_iff] at htop
  apply hab
  have ha : a = 1 := by rw [← Subgroup.mem_bot, htop]; trivial
  have hb : b = 1 := by rw [← Subgroup.mem_bot, htop]; trivial
  rw [ha, hb]

theorem t158g_exists_fixed_of_pow {S : Type*} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (x : MulAut S) (hx : x ^ p = 1) (hdvd : p ∣ Nat.card S) : ∃ y ∈ fixSubgroup x, orderOf y = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime x hx
  have hcard : Nat.card {y : S // x y = y} = Nat.card (fixSubgroup x) :=
    Nat.card_congr (Equiv.refl _)
  have hdvd' : p ∣ Nat.card (fixSubgroup x) := by
    rw [← hcard, Nat.dvd_iff_mod_eq_zero]
    rw [← hmod]
    exact Nat.dvd_iff_mod_eq_zero.1 hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := fixSubgroup x) p hdvd'
  refine ⟨y.1, y.2, ?_⟩
  rwa [Subgroup.orderOf_coe]

theorem t158g_chevAut_mem_stab {p : ℕ} {K J : Subgroup Ω} {b : Ω} (hJK : J ≤ K)
    (hbK : b ∈ Subgroup.normalizer (K : Set Ω)) (hbJ : b ∈ Subgroup.normalizer (J : Set Ω)) :
    chevAut p K ⟨b, hbK⟩ ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer p K J) := by
  have key : ∀ (c : Ω) (hcN : c ∈ Subgroup.normalizer (K : Set Ω))
      (_ : c ∈ Subgroup.normalizer (J : Set Ω)),
      (chevTransfer p K J).map (chevAut p K ⟨c, hcN⟩).toMonoidHom ≤ chevTransfer p K J := by
    intro c hcN hcJ
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hkJ : (k : Ω) ∈ J := Subgroup.mem_subgroupOf.1 hk
    have hck : c * k * c⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hcJ k).1 hkJ
    refine ⟨K.normalizerMonoidHom ⟨c, hcN⟩ k, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · rw [chev_coe_normalizerMonoidHom]
      exact hck
    · exact (chevAut_chevQuotHom p K ⟨c, hcN⟩ k).symm
  have h1 := key b hbK hbJ
  have h2 := key b⁻¹ (Subgroup.inv_mem _ hbK) (Subgroup.inv_mem _ hbJ)
  change (chevTransfer p K J).map (chevAut p K ⟨b, hbK⟩).toMonoidHom = chevTransfer p K J
  refine le_antisymm h1 ?_
  intro s hs
  refine ⟨chevAut p K ⟨b⁻¹, Subgroup.inv_mem _ hbK⟩ s, h2 ⟨s, hs, rfl⟩, ?_⟩
  change chevAut p K ⟨b, hbK⟩ (chevAut p K ⟨b⁻¹, Subgroup.inv_mem _ hbK⟩ s) = s
  rw [← MulAut.mul_apply, ← map_mul]
  have : (⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set Ω))) * ⟨b⁻¹, Subgroup.inv_mem _ hbK⟩ = 1 :=
    Subtype.ext (mul_inv_cancel b)
  rw [this, map_one, MulAut.one_apply]

theorem t158g_indAut_of_mem {p : ℕ} {S : Subgroup Ω} (l : ↥S) :
    indAut p S (l : Ω) (Subgroup.le_normalizer l.2) = MulAut.conj (chevQuotHom p S l)⁻¹ := by
  ext s
  obtain ⟨k, rfl⟩ := chevQuotHom_surjective p S s
  have hk : (l : Ω)⁻¹ * k * l ∈ S := S.mul_mem (S.mul_mem (S.inv_mem l.2) k.2) l.2
  have h1 : indAut p S (l : Ω) (Subgroup.le_normalizer l.2) (chevQuotHom p S k) =
      chevQuotHom p S ⟨(l : Ω)⁻¹ * k * l, hk⟩ :=
    indAut_apply_mk (Subgroup.le_normalizer l.2) ⟨k, ⟨_, hk⟩, rfl, rfl, rfl⟩
  have h2 : (⟨(l : Ω)⁻¹ * k * l, hk⟩ : ↥S) = l⁻¹ * k * l := Subtype.ext (by simp)
  rw [h1, h2, map_mul, map_mul, map_inv, MulAut.conj_apply, inv_inv]

theorem t158g_comm_of_indAut_eq_one {p : ℕ} (hp : p.Prime) {S : Subgroup Ω} (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hSc : GLAPComponent p S S) {g : Ω} (hg : g ∈ Subgroup.normalizer (S : Set Ω))
    (h1 : indAut p S g hg = 1) : ∀ y ∈ S, g * y = y * g := by
  have hchev1 : chevAut p S ⟨g, hg⟩ = 1 := by
    rw [OutCyc.indAut_eq_inv_chevAut, inv_eq_one] at h1
    exact h1
  have hgC : g ∈ centModSubgroup p S := centMod_iff.1 ((chevAut_eq_one_iff hp hSc hg).1 hchev1)
  intro y hy
  have h3 := (mem_centModSubgroup.1 hgC).2 y hy
  rw [glaPPrimeCoreOf_eq_bot_p hcore, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3.symm


theorem t158g_conj_comm {R : Type*} [Group R] {φ : MulAut R} {r : R} (h : φ r = r) :
    MulAut.conj r * φ = φ * MulAut.conj r := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h]

theorem t158g_eq_one_of_conj_eq_one {R : Type*} [Group R] (hZ : Subgroup.center R = ⊥) {r : R}
    (h : MulAut.conj r = 1) : r = 1 := by
  have hr : r ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun f : MulAut R => f y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * r = r * y * r⁻¹ * r := by rw [h1]
      _ = r * y := by group
  rw [hZ] at hr
  exact Subgroup.mem_bot.1 hr

end Fin

section Core


variable {Ω : Type} [Group Ω] [Finite Ω]

theorem t158g_core {p : ℕ} (hp : p.Prime) {S : Subgroup Ω} {b c : Ω} {L : Subgroup Ω}
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hSc : GLAPComponent p S S)
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hcN : c ∈ Subgroup.normalizer (S : Set Ω))
    (hbp : b ^ p = 1) (hcp : c ^ p = 1) (hbc : b * c = c * b)
    (hL : GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L)
    (hchevL : IsChevSimple 2 (PSimple p L)) (hcL : c ∈ Subgroup.normalizer (L : Set Ω))
    {R : Type} [Group R] (θ : PSimple p S ≃* R) {I F : Set (MulAut R)}
    (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a) (hRaw : MI.RawInnBody p R I F)
    (hcI : MulAut.congr θ (indAut p S c hcN) ∈ I)
    (hFA : T156.FixAlt p I (MulAut.congr θ (indAut p S b hbN))) :
    InnDiagOn p (Subgroup.zpowers c) L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite R := Finite.of_equiv (PSimple p S) θ.toEquiv
  set β := indAut p S b hbN with hβ
  set x := MulAut.congr θ β with hx
  set φc := MulAut.congr θ (indAut p S c hcN) with hφc
  have hap : IsPGroup p (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hbp
  have hLS : L ≤ S := hL.1.trans inf_le_left
  have hLX : L ≤ S ⊓ Subgroup.centralizer ({b} : Set Ω) := hL.1
  have hφx : φc * x = x * φc := by
    have h3 : indAut p S (c * b) (Subgroup.mul_mem _ hcN hbN) =
        indAut p S (b * c) (Subgroup.mul_mem _ hbN hcN) := T156.indAut_congr hbc.symm _ _
    rw [T156.indAut_mul hcN hbN, T156.indAut_mul hbN hcN] at h3
    rw [hφc, hx, ← map_mul, ← map_mul, h3]
  have hφp : φc ^ p = 1 := by rw [hφc, ← map_pow, T156.indAut_pow_eq_one hcN hcp, map_one]
  have hJc := glaPComponent_chevTransfer hp hbN hap hL
  have hpJ : p ∣ Nat.card ↥(chevTransfer p S L) := by
    obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer hp hbN hap hL
    have h1 : p ∣ Nat.card (PSimple p L) := t158g_prime_dvd_card_pSimple hp hL
    rw [Nat.card_congr e.toEquiv] at h1
    exact h1.trans (t158g_card_pSimple_dvd _)
  by_contra hnot
  rcases hFA with ⟨lab₀, hlab₀, hraw₀⟩ | hcyc
  ·
    obtain ⟨R₀, _, I₀, F₀, hs₀, hna₀, θ₀, -⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw₀
    set E : Subgroup (PSimple p S) := ggFixDer β with hEdef
    have hθE : (ggFixDer β).map θ.toMonoidHom = ggFixDer x := (T156.ggFixDer_congr θ β).symm
    let eSx : ↥E ≃* ↥(ggFixDer x) := (θ.subgroupMap E).trans (MulEquiv.subgroupCongr hθE)
    have heSx : ∀ e : ↥E, ((eSx e : ↥(ggFixDer x)) : R) = θ e := fun e => rfl
    let eS0 : ↥E ≃* R₀ := eSx.trans θ₀
    have hEs : IsSimpleGroup ↥E := (MulEquiv.isSimpleGroup_congr eS0).2 hs₀
    have hEna : ∃ u v : ↥E, u * v ≠ v * u := by
      obtain ⟨u, v, huv⟩ := hna₀
      exact ⟨eS0.symm u, eS0.symm v, fun h => huv (by simpa using congrArg eS0 h)⟩
    have hfix : FP.fixSub β = ggFixSub β := by
      ext y
      exact Iff.rfl
    have hEle : E ≤ ggFixSub β := Subgroup.commutator_le.2 fun g hg h hh =>
      (ggFixSub β).mul_mem ((ggFixSub β).mul_mem ((ggFixSub β).mul_mem hg hh)
        ((ggFixSub β).inv_mem hg)) ((ggFixSub β).inv_mem hh)
    have hEC : E ≤ fixSubgroup (chevAut p S ⟨b, hbN⟩) := by
      rw [← FR.fixSub_indAut hbN, hfix]
      exact hEle
    have hperf : ∀ T : Subgroup (PSimple p S), T ≤ fixSubgroup (chevAut p S ⟨b, hbN⟩) →
        ⁅T, T⁆ = T → T ≤ E := by
      intro T hT hTT
      rw [← FR.fixSub_indAut hbN, hfix] at hT
      rw [← hTT, hEdef, ggFixDer]
      exact Subgroup.commutator_mono hT hT
    have hLE : chevTransfer p S L = E := FR.eq_core_of_glaPComponent hEs hEC hperf hJc
    have hpE : p ∣ Nat.card ↥E := hLE ▸ hpJ
    obtain ⟨Θ, hΘ⟩ := T156.exists_pSimple_equiv hp hL inf_le_left hEs hEna hpE hLE
    have hπJ : ∀ (m : Ω) (_ : m ∈ L) (hmS : m ∈ S), chevQuotHom p S ⟨m, hmS⟩ ∈ E := by
      intro m hm hmS
      rw [← hLE]
      exact ⟨⟨m, hmS⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
    have hind : ∀ (a : Ω) (ha : a ∈ Subgroup.normalizer (S : Set Ω)) (m : Ω) (hmS : m ∈ S)
        (hm' : a⁻¹ * m * a ∈ S),
        indAut p S a ha (chevQuotHom p S ⟨m, hmS⟩) = chevQuotHom p S ⟨a⁻¹ * m * a, hm'⟩ := by
      intro a ha m hmS hm'
      exact indAut_apply_mk ha ⟨⟨m, hmS⟩, ⟨a⁻¹ * m * a, hm'⟩, rfl, rfl, rfl⟩
    apply hnot
    refine ⟨Subgroup.zpowers_le.2 hcL, ?_⟩
    have hq₀ := isQuasisimple_pQuot_of_glaPComponent hp hL
    refine ⟨hq₀.1, lab₀, hlab₀, Canonical.largeEvenRawDatum_mono ?_ hraw₀⟩
    rintro R₀' _ I₀' F₀' ⟨hs', hna', θ₀', hFG'⟩
    refine ⟨hs', hna', Θ.trans (eSx.trans θ₀'), ?_⟩
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hckN : c ^ k ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.zpow_mem _ hcN k
    have hck : indAut p S (c ^ k) hckN = indAut p S c hcN ^ k := T156.indAut_zpow hcN k
    have hckI : MulAut.congr θ (indAut p S (c ^ k) hckN) ∈ I := by
      rw [hck, map_zpow]
      exact (OutCyc.rawSubgroup hRaw).zpow_mem hcI k
    have hckp : MulAut.congr θ (indAut p S (c ^ k) hckN) ^ p = 1 := by
      rw [← map_pow, T156.indAut_pow_eq_one hckN (t158g_zpow_pow hcp k), map_one]
    have hckx : MulAut.congr θ (indAut p S (c ^ k) hckN) * x =
        x * MulAut.congr θ (indAut p S (c ^ k) hckN) := by
      rw [hck, map_zpow]
      exact (Commute.zpow_left (show Commute φc x from hφx) k).eq
    obtain ⟨φ₀, hφ₀, hφ₀eq⟩ := hFG'.1 _ hckI hckp hckx
    refine ⟨φ₀, hφ₀, ?_⟩
    rintro l l' ⟨m, m', rfl, rfl, hmm'⟩
    have hmS : (m : Ω) ∈ S := (hLX m.2).1
    have hm'S : (m' : Ω) ∈ S := (hLX m'.2).1
    have hkey : MulAut.congr θ (indAut p S (c ^ k) hckN) (θ (chevQuotHom p S ⟨m, hmS⟩)) =
        θ (chevQuotHom p S ⟨m', hm'S⟩) := by
      show θ (indAut p S (c ^ k) hckN (θ.symm (θ (chevQuotHom p S ⟨m, hmS⟩)))) = _
      rw [MulEquiv.symm_apply_apply, hind (c ^ k) hckN m hmS (hmm' ▸ hm'S)]
      congr 2
      exact Subtype.ext hmm'.symm
    have hmemx : ∀ (y : Ω) (_ : y ∈ L) (hyS : y ∈ S), θ (chevQuotHom p S ⟨y, hyS⟩) ∈ ggFixDer x := by
      intro y hy hyS
      rw [← hθE]
      exact ⟨_, hπJ y hy hyS, rfl⟩
    have hθ' : ∀ (y : ↥L) (hyS : (y : Ω) ∈ S),
        (Θ.trans (eSx.trans θ₀')) (QuotientGroup.mk (QuotientGroup.mk y : PQuot p L)) =
          θ₀' ⟨θ (chevQuotHom p S ⟨y, hyS⟩), hmemx y y.2 hyS⟩ := by
      intro y hyS
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
      congr 1
      apply Subtype.ext
      rw [heSx, hΘ y]
    rw [hθ' m hmS, hθ' m' hm'S, ← hφ₀eq _ (hmemx m m.2 hmS)]
    congr 1
    exact Subtype.ext hkey
  ·
    haveI := hs
    have hZ : Subgroup.center R = ⊥ := T156.center_eq_bot_of_simple_noncomm hna
    have hcS' : c⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hcN
    have hcL' : c⁻¹ ∈ Subgroup.normalizer (L : Set Ω) := Subgroup.inv_mem _ hcL
    have hstab : indAut p S c hcN ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer p S L) :=
      t158g_chevAut_mem_stab hLS hcS' hcL'
    set γ := CFSG.GroupActions.subgroupStabRestrict (chevTransfer p S L) ⟨_, hstab⟩ with hγ
    have hγp : γ ^ p = 1 := by
      rw [hγ, ← map_pow]
      have h1 : (⟨indAut p S c hcN, hstab⟩ :
          ↥(CFSG.GroupActions.subgroupStabAut (chevTransfer p S L))) ^ p = 1 :=
        Subtype.ext (by simpa using T156.indAut_pow_eq_one hcN hcp)
      rw [h1, map_one]
    obtain ⟨t', ht'fix, ht'ord⟩ := t158g_exists_fixed_of_pow hp γ hγp hpJ
    have htJ : (t' : PSimple p S) ∈ chevTransfer p S L := t'.2
    have htc : indAut p S c hcN (t' : PSimple p S) = t' := by
      have h1 : γ t' = t' := mem_fixSubgroup.1 ht'fix
      have h2 := congrArg Subtype.val h1
      rwa [hγ, CFSG.GroupActions.subgroupStabRestrict_apply] at h2
    have htb : β (t' : PSimple p S) = t' := by
      have h1 : (t' : PSimple p S) ∈ fixSubgroup (chevAut p S ⟨b, hbN⟩) := hJc.1 htJ
      rw [← FR.fixSub_indAut hbN] at h1
      exact FP.mem_fixSub.1 h1
    have htord : orderOf (t' : PSimple p S) = p := by rw [Subgroup.orderOf_coe]; exact ht'ord
    set t : PSimple p S := (t' : PSimple p S) with htdef
    set ct : MulAut R := MulAut.conj (θ t) with hct
    have hctI : ct ∈ I := hRaw.2.2.1 (θ t)
    have hxt : x (θ t) = θ t := by
      show θ (β (θ.symm (θ t))) = θ t
      rw [MulEquiv.symm_apply_apply, htb]
    have hφt : φc (θ t) = θ t := by
      show θ (indAut p S c hcN (θ.symm (θ t))) = θ t
      rw [MulEquiv.symm_apply_apply, htc]
    have hctx : ct * x = x * ct := t158g_conj_comm hxt
    have hctφ : ct * φc = φc * ct := t158g_conj_comm hφt
    have hct1 : ct ≠ 1 := by
      intro h1
      have h2 : θ t = 1 := t158g_eq_one_of_conj_eq_one hZ h1
      have h3 : t = 1 := by
        rw [← map_one θ] at h2
        exact θ.injective h2
      rw [h3, orderOf_one] at htord
      exact hp.one_lt.ne htord
    have htp : t ^ p = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [htord] at h
    have hctp : ct ^ p = 1 := by
      rw [hct, ← map_pow, ← map_pow, htp, map_one, map_one]
    have hctord : orderOf ct = p := orderOf_eq_prime hctp hct1
    have hφct : φc * ct = ct * φc := hctφ.symm
    set E : Subgroup (MulAut R) := Subgroup.zpowers φc ⊔ Subgroup.zpowers ct with hEdef
    have hEab : IsElemAbelian p E := by
      refine ⟨⟨⟨fun u v => Subtype.ext (t158g_comm_of_mem_sup hφct u.2 v.2)⟩⟩, fun φ hφ => ?_⟩
      exact t158g_pow_eq_one_of_mem_sup hφct hφp hctp hφ
    have hEI : ∀ φ ∈ E, φ ∈ I ∧ φ * x = x * φ := by
      intro φ hφ
      obtain ⟨i, j, rfl⟩ := t158g_mem_sup_zpowers hφct hφ
      refine ⟨(OutCyc.rawSubgroup hRaw).mul_mem ((OutCyc.rawSubgroup hRaw).zpow_mem hcI i)
        ((OutCyc.rawSubgroup hRaw).zpow_mem hctI j), ?_⟩
      exact ((Commute.zpow_left (show Commute φc x from hφx) i).mul_left
        (Commute.zpow_left (show Commute ct x from hctx) j)).eq
    have hcard := hcyc E hEab hEI
    have hle : Subgroup.zpowers ct ≤ E := le_sup_right
    have hEeq : Subgroup.zpowers ct = E := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, hctord]; exact hcard)
    have hφE : φc ∈ Subgroup.zpowers ct := by
      rw [hEeq]
      exact (le_sup_left : Subgroup.zpowers φc ≤ E) (Subgroup.mem_zpowers φc)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hφE
    have hc_inner : indAut p S c hcN = MulAut.conj (t ^ j) := by
      apply (MulAut.congr θ).injective
      rw [← hφc, ← hj, hct, MI.congr_conj, map_zpow, map_zpow]
    obtain ⟨l₀, hl₀L, hl₀⟩ := Subgroup.mem_map.1 (Subgroup.zpow_mem _ htJ j)
    have hl₀N : (l₀ : Ω) ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.le_normalizer l₀.2
    have h1 : indAut p S (c * l₀) (Subgroup.mul_mem _ hcN hl₀N) = 1 := by
      rw [T156.indAut_mul hcN hl₀N, t158g_indAut_of_mem l₀, hc_inner, ← hl₀, ← map_mul, inv_mul_cancel,
        map_one]
    have hcomm := t158g_comm_of_indAut_eq_one hp hcore hSc (Subgroup.mul_mem _ hcN hl₀N) h1
    have hin : InducesInnerMod p L c := by
      refine ⟨(l₀ : Ω)⁻¹, L.inv_mem (Subgroup.mem_subgroupOf.1 hl₀L), fun y hy => ?_⟩
      have h2 := hcomm y (hLS hy)
      have h3 : c⁻¹ * y * c = (l₀ : Ω) * y * (l₀ : Ω)⁻¹ := by
        calc c⁻¹ * y * c = c⁻¹ * (y * (c * l₀)) * (l₀ : Ω)⁻¹ := by group
          _ = c⁻¹ * ((c * l₀) * y) * (l₀ : Ω)⁻¹ := by rw [← h2]
          _ = (l₀ : Ω) * y * (l₀ : Ω)⁻¹ := by group
      rw [h3, inv_inv, inv_mul_cancel]
      exact Subgroup.one_mem _
    exact hnot (MI.inner_innDiag_holds hp hL hchevL hcL hin)

theorem t158g_geom : T156.T156Geom :=
  T156.t156Geom_of_rest (T156.t156Rest_of_rest₂ (T156.t156Rest₂_of_rest₃ (T156.t156Rest₃_of_rest₄
    (T156.t156Rest₄_of_rest₅ (T156.t156Rest₅_of_rest₆ T156.t156Rest₆_holds)))))

theorem t158g_hall {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ∀ lab, LargeEvenInLambda2 lab →
    MI.CAll lab (LargeEvenSimpleGuard
      (fun R _ I F => T156.GeomBody p lab R I F ∧ MI.RawInnBody p R I F)) := fun lab hlab =>
  MI.CAll.mono (fun R _ I F h hs hna => ⟨h.1, h.2 hs hna⟩)
    (MI.CAll.and (t158g_geom p hp hp2 lab hlab) (MI.canonRawInn' hp hp2 hlab))

theorem t158g_field_restrict {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup Ω} {b c : Ω} {L : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hcN : c ∈ Subgroup.normalizer (S : Set Ω))
    (hbp : b ^ p = 1) (hcp : c ^ p = 1) (hbc : b * c = c * b) (hF : FieldOn p b S)
    (hcInn : InnDiagOn p (Subgroup.zpowers c) S)
    (hL : GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L)
    (hchevL : IsChevSimple 2 (PSimple p L)) (hcL : c ∈ Subgroup.normalizer (L : Set Ω))
    (hU : ¬ (p = 3 ∧ catalogIs (PSimple 3 S) S9.isU3eight)) :
    InnDiagOn p (Subgroup.zpowers c) L := by
  have hSc : GLAPComponent p S S := glaPComponent_self_p hq hcore
  have h₁ : CFSG.Assembly.LargeEvenMarking (PQuot p S) fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (indRel p S c) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh c (Subgroup.mem_zpowers c)) hcInn.2
  have hM := MI.marking_transport (indRel p S c) h₁ hF.2
  have hM' := FP.canon_marking_and_labelAll_simple'
    (P' := fun lab R _ I F => T156.GeomBody p lab R I F ∧ MI.RawInnBody p R I F) (t158g_hall hp hp2) hM
  obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨hPF, φ, hφ, hindc⟩, hGB, hRaw⟩ :=
    Canonical.largeEvenMarking_exists hM'
  obtain ⟨hne, f, hf, u, hu, hord, hind⟩ := hPF
  have hx : MulAut.congr θ (indAut p S b hbN) = u * f * u⁻¹ :=
    ((induces_indRel_iff hbN θ).1 hind).symm
  have hcI : MulAut.congr θ (indAut p S c hcN) ∈ I := by
    rw [← (induces_indRel_iff hcN θ).1 hindc]
    exact hφ
  have hne' : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h1, h2⟩
    rcases hne with h | h
    · exact h h1
    · exact h h2
  rcases (hGB hs hna).1 hne' f hf hord with hFA | ⟨h3, hU3⟩
  · have hFA' : T156.FixAlt p I (MulAut.congr θ (indAut p S b hbN)) := by
      rw [hx]
      exact T156.fixAlt_conj (J := OutCyc.rawSubgroup hRaw) hu hFA
    exact t158g_core hp hcore hSc hbN hcN hbp hcp hbc hL hchevL hcL θ hs hna hRaw hcI hFA'
  · subst h3
    exact (hU ⟨rfl, (catalogIs_congr θ).2 hU3⟩).elim

theorem t158g_td4_restrict {S : Subgroup Ω} {b c : Ω} {L : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥S) (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hTD4 : IsTD4 3 S)
    (hchev : IsChevSimple 2 (PSimple 3 S))
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hcN : c ∈ Subgroup.normalizer (S : Set Ω))
    (hbp : b ^ 3 = 1) (hcp : c ^ 3 = 1) (hbc : b * c = c * b) (hnon : NonInnDiag 3 b S)
    (hG2 : centCard2 3 S b = Nat.sqrt (card2 3 S))
    (hcInn : InnDiagOn 3 (Subgroup.zpowers c) S)
    (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L)
    (hchevL : IsChevSimple 2 (PSimple 3 L)) (hcL : c ∈ Subgroup.normalizer (L : Set Ω)) :
    InnDiagOn 3 (Subgroup.zpowers c) L := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hSc : GLAPComponent 3 S S := glaPComponent_self_p hq hcore
  have hqP : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent hp hSc
  have h₁ : CFSG.Assembly.LargeEvenMarking (PQuot 3 S) fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (indRel 3 S c) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh c (Subgroup.mem_zpowers c)) hcInn.2
  have M₀ := Canonical.largeEvenMarking_markedModel
    (CFSG.StandardType.ChevTwo.ys08_holds (PQuot 3 S) hqP hchev)
  have hM := MI.marking_transport (indRel 3 S c) h₁ M₀
  have hM' := FP.canon_marking_and_labelAll_simple'
    (P' := fun lab R _ I F => T156.GeomBody 3 lab R I F ∧ MI.RawInnBody 3 R I F) (t158g_hall hp hp2) hM
  obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨⟨-, hMM⟩, φ, hφ, hindc⟩, hGB, hRaw⟩ :=
    Canonical.largeEvenMarking_exists hM'
  haveI : Finite R := Finite.of_equiv (PSimple 3 S) θ.toEquiv
  have htag : lab.tag = .triD4 := tag_triD4_of_isTD4 hMM hTD4 θ
  have hcI : MulAut.congr θ (indAut 3 S c hcN) ∈ I := by
    rw [← (induces_indRel_iff hcN θ).1 hindc]
    exact hφ
  have hx3 : MulAut.congr θ (indAut 3 S b hbN) ^ 3 = 1 := by
    rw [← map_pow, T156.indAut_pow_eq_one hbN hbp, map_one]
  have hxni : MulAut.congr θ (indAut 3 S b hbN) ∉ (MulAut.conj : R →* MulAut R).range := by
    rintro ⟨r, hr⟩
    apply hnon.2
    apply MI.inner_innDiag_holds hp hSc hchev hbN
    apply (indAut_mem_inner_iff hp hSc hbN).1
    refine ⟨θ.symm r, ?_⟩
    apply (MulAut.congr θ).injective
    rw [MI.congr_conj, MulEquiv.apply_symm_apply, hr]
  have hx2 : S10.twoPart (FP.fixNum (MulAut.congr θ (indAut 3 S b hbN))) =
      Nat.sqrt (S10.twoPart (Nat.card R)) := by
    have h1 := hG2
    rw [FP.centCard2_eq_twoPart_fixNum hbN (FP.odd_card_center_pQuot hp hp2 S),
      FP.card2_eq_twoPart_card_pSimple hp hp2 S] at h1
    rw [FP.fixNum_congr, h1, Nat.card_congr θ.toEquiv]
  have hFA := (hGB hs hna).2 htag rfl _ hx3 hxni hx2
  exact t158g_core hp hcore hSc hbN hcN hbp hcp hbc hL hchevL hcL θ hs hna hRaw hcI hFA

end Core

@[expose] def T158GOmega (p : ℕ) : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x₁ x₂ : Ω) (L₁ L₂ : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    catalogIs (PSimple p S) T158.t158FamTwo →
    x₁ ^ p = 1 → x₂ ^ p = 1 → x₁ * x₂ = x₂ * x₁ →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁ → IsChevSimple 2 (PSimple p L₁) →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x₂} : Set Ω)) L₂ → IsChevSimple 2 (PSimple p L₂) →
    FGOn p x₁ L₂ → FGOn p x₂ L₁ →
    InnDiagOn p (Subgroup.zpowers x₁) S

@[expose] def T158GU38Core : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (b : Ω) (L : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ →
    catalogIs (PSimple 3 S) S9.isU3eight → b ^ 3 = 1 → FieldOn 3 b S →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L → False

@[expose] def T158GTD4Core : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (b c : Ω) (L : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ → IsTD4 3 S →
    IsChevSimple 2 (PSimple 3 S) →
    b ^ 3 = 1 → c ^ 3 = 1 → b * c = c * b → NonInnDiag 3 b S →
    centCard2 3 S b ≠ Nat.sqrt (card2 3 S) → InnDiagOn 3 (Subgroup.zpowers c) S →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L → IsChevSimple 2 (PSimple 3 L) →
    c ∈ Subgroup.normalizer (L : Set Ω) → InnDiagOn 3 (Subgroup.zpowers c) L

@[expose] def T158GD4Core : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x₁ x₂ : Ω) (L₁ L₂ : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ → catalogIs (PSimple 3 S) isD4any →
    IsChevSimple 2 (PSimple 3 S) →
    x₁ ^ 3 = 1 → x₂ ^ 3 = 1 → x₁ * x₂ = x₂ * x₁ →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁ → IsChevSimple 2 (PSimple 3 L₁) →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₂} : Set Ω)) L₂ → IsChevSimple 2 (PSimple 3 L₂) →
    FGOn 3 x₁ L₂ → FGOn 3 x₂ L₁ → NonInnDiag 3 x₁ S → False

section Assembly


theorem t158g_not_innDiagOn_of_fgOn {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup Ω} {g : Ω} (h : FGOn p g L) : ¬ InnDiagOn p (Subgroup.zpowers g) L := by
  rcases h with hF | hG
  · exact (MI.field_nonInnDiag_holds hp hp2 hF).2
  · exact hG.1.2

theorem t158gOmega_of_cores (hU8 : T158GU38Core) (hTD4 : T158GTD4Core) (hD4 : T158GD4Core) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : T158GOmega p := by
  intro Ω _ _ S x₁ x₂ L₁ L₂ hSn hq hcore hTwo hx1 hx2 hc hL1 hC1 hL2 hC2 hF12 hF21
  have hSc : GLAPComponent p S S := glaPComponent_self_p hq hcore
  have hqP : CFSG.Open.IsQuasisimple (PQuot p S) := isQuasisimple_pQuot_of_glaPComponent hp hSc
  have hN : ∀ y : Ω, y ∈ Subgroup.normalizer (S : Set Ω) := fun y => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top y
  have hchev : IsChevSimple 2 (PSimple p S) := Or.inl hTwo
  by_contra hnot
  have hnon : NonInnDiag p x₁ S := ⟨hN x₁, hnot⟩
  have hx2L1 : x₂ ∈ Subgroup.normalizer (L₁ : Set Ω) := t158g_normalizer_of_fgOn hF21
  have hL1C : L₁ ≤ Subgroup.centralizer ({x₁} : Set Ω) := hL1.1.trans inf_le_right
  have hx1A : x₁ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx2A : x₂ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  have hexp : ∀ a ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, a ^ p = 1 := fun a ha =>
    t158g_pow_eq_one_of_mem_sup hc hx1 hx2 ha
  by_cases hnt : ∀ c ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, NonInnDiag p c S →
      FieldOn p c S ∨ (p = 3 ∧ IsTD4 3 S)
  ·
    obtain ⟨A₀, hA₀A, hA₀inn, hcard, -⟩ :=
      T156.t156_split hp hp2 hqP hchev (fun a _ => hN a) hexp hnt
    have hx1A₀ : x₁ ∉ A₀ := fun h => hnot (T156.innDiagOn_mono (Subgroup.zpowers_le.2 h) hA₀inn)
    obtain ⟨a₀, ha₀, k, hk⟩ := T156.exists_decomp hp hA₀A (fun a ha a' ha' => t158g_comm_of_mem_sup hc ha ha')
      hexp hcard hx1A hx1A₀ x₂ hx2A
    have ha₀eq : a₀ = x₂ * x₁ ^ (-k) := by rw [hk]; group
    have ha₀inn : InnDiagOn p (Subgroup.zpowers a₀) S :=
      T156.innDiagOn_mono (Subgroup.zpowers_le.2 ha₀) hA₀inn
    have ha₀A : a₀ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := hA₀A ha₀
    have ha₀p : a₀ ^ p = 1 := hexp a₀ ha₀A
    have hx1a₀ : x₁ * a₀ = a₀ * x₁ := t158g_comm_of_mem_sup hc hx1A ha₀A
    have hx1L1 : x₁ ∈ Subgroup.normalizer (L₁ : Set Ω) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hL1C hl))
    have ha₀L : a₀ ∈ Subgroup.normalizer (L₁ : Set Ω) := by
      rw [ha₀eq]
      exact Subgroup.mul_mem _ hx2L1 (Subgroup.zpow_mem _ hx1L1 _)
    have hres : InnDiagOn p (Subgroup.zpowers a₀) L₁ := by
      rcases hnt x₁ hx1A hnon with hF | ⟨rfl, hT⟩
      · by_cases hU : p = 3 ∧ catalogIs (PSimple 3 S) S9.isU3eight
        · obtain ⟨rfl, hU⟩ := hU
          exact (hU8 Ω S x₁ L₁ hSn hq hcore hU hx1 hF hL1).elim
        · exact t158g_field_restrict hp hp2 hq hcore (hN x₁) (hN a₀) hx1 ha₀p hx1a₀ hF ha₀inn hL1 hC1
            ha₀L hU
      · by_cases hG2 : centCard2 3 S x₁ = Nat.sqrt (card2 3 S)
        · exact t158g_td4_restrict hq hcore hT hchev (hN x₁) (hN a₀) hx1 ha₀p hx1a₀ hnon hG2 ha₀inn hL1 hC1
            ha₀L
        · exact hTD4 Ω S x₁ a₀ L₁ hSn hq hcore hT hchev hx1 ha₀p hx1a₀ hnon hG2 ha₀inn hL1 hC1 ha₀L
    rw [ha₀eq] at hres
    exact t158g_not_innDiagOn_of_fgOn hp hp2 hF21 (t158g_innDiagOn_of_mul_pow hc hL1C hx2L1 (-k) hres)
  ·
    obtain ⟨c, hcA, hcnot⟩ : ∃ c ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂,
        ¬ (NonInnDiag p c S → FieldOn p c S ∨ (p = 3 ∧ IsTD4 3 S)) := by
      by_contra hall
      exact hnt fun c hc => Classical.byContradiction fun h => hall ⟨c, hc, h⟩
    have hcnon : NonInnDiag p c S := by
      by_contra h
      exact hcnot fun h' => absurd h' h
    have hcF : ¬ FieldOn p c S := fun h => hcnot fun _ => Or.inl h
    have hcT : ¬ (p = 3 ∧ IsTD4 3 S) := fun h => hcnot fun _ => Or.inr h
    rcases i91_holds Ω p hp hp2 S S c hSc hchev (hN c) (hexp c hcA) hcnon with hF | ⟨rfl, hD | hT⟩
    · exact hcF hF
    · exact hD4 Ω S x₁ x₂ L₁ L₂ hSn hq hcore hD hchev hx1 hx2 hc hL1 hC1 hL2 hC2 hF12 hF21 hnon
    · exact hcT ⟨rfl, hT⟩

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.T158G

end
