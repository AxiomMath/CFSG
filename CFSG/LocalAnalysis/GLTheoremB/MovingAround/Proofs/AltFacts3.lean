module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk barOf coprime_card_gLAPPrimeCore_aux)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

namespace AltFacts3

open scoped commutatorElement
open AltFacts2 (isPiGroup_of_mulEquiv le_Ke_of_component core_le_Ke Ke_le piLayer_le
  eq_top_of_map_center_eq_top)

theorem exists_fixed_mem_coset_p {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (d : G)
    (hd : d ^ p = 1) (Q : Subgroup G) [Finite Q] (hcop : ¬ p ∣ Nat.card Q)
    (hQn : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) (x : G) (hx : x⁻¹ * (d * x * d⁻¹) ∈ Q) :
    ∃ q ∈ Q, d * (x * q) * d⁻¹ = x * q := by
  classical
  have hφ : ∀ q ∈ Q, x⁻¹ * (d * (x * q) * d⁻¹) ∈ Q := by
    intro q hq
    have e : x⁻¹ * (d * (x * q) * d⁻¹) = (x⁻¹ * (d * x * d⁻¹)) * (d * q * d⁻¹) := by group
    rw [e]
    exact Q.mul_mem hx (hQn q hq)
  let f : Function.End Q := fun q => ⟨x⁻¹ * (d * (x * q) * d⁻¹), hφ q q.2⟩
  have hiter : ∀ (n : ℕ) (q : Q), ((f ^ n) q : G) = x⁻¹ * (d ^ n * (x * q) * (d ^ n)⁻¹) := by
    intro n
    induction n with
    | zero =>
      intro q
      show (q : G) = x⁻¹ * (d ^ 0 * (x * q) * (d ^ 0)⁻¹)
      simp
    | succ n ih =>
      intro q
      have e1 : ((f ^ (n + 1)) q : G) = x⁻¹ * (d * (x * ((f ^ n) q : G)) * d⁻¹) := by
        show ((f^[n + 1] q : Q) : G) = _
        rw [Function.iterate_succ_apply']
        rfl
      rw [e1, ih q, pow_succ' d n]
      simp only [mul_inv_rev]
      group
  have hfp : f ^ p = 1 := by
    funext q
    apply Subtype.ext
    show ((f ^ p) q : G) = (q : G)
    rw [hiter p q, hd]
    simp
  have hf : f ^ p ^ 1 = 1 := by simpa using hfp
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Fintype Q := Fintype.ofFinite Q
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  have hne : Fintype.card (Function.fixedPoints f) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    apply hcop
    rw [Nat.card_eq_fintype_card]
    exact (Nat.modEq_zero_iff_dvd).1 hmod
  obtain ⟨⟨q, hq⟩⟩ := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hne)
  have hq' : f q = q := Function.mem_fixedPoints_iff.1 hq
  refine ⟨q, q.2, ?_⟩
  have h1 : x⁻¹ * (d * (x * q) * d⁻¹) = (q : G) := congrArg Subtype.val hq'
  calc d * (x * q) * d⁻¹ = x * (x⁻¹ * (d * (x * q) * d⁻¹)) := by group
    _ = x * q := by rw [h1]

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_lift {p : ℕ} (hp : p.Prime) {K : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (K : Set G)) (hdp : d ^ p = 1) {k : barOf p K}
    (hk : barAut p K ⟨d, hdN⟩ k = k) :
    ∃ y : ↥K, (y : G) ∈ Subgroup.centralizer ({d} : Set G) ∧
      (QuotientGroup.mk y : barOf p K) = k := by
  classical
  set Q : Subgroup G := GLAPPrimeCoreOf p K with hQ
  have hcop : ¬ p ∣ Nat.card Q := by
    intro h
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (card_gLAPPrimeCoreOf_coprime p K) (dvd_refl p) h)
  have hQn : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q := fun q hq => conj_mem_glaPPrimeCoreOf p hdN hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
  rw [barAut_mk] at hk
  have h1 : ((K.normalizerMonoidHom ⟨d, hdN⟩ x)⁻¹ * x : ↥K) ∈ GLAPPrimeCore p ↥K :=
    QuotientGroup.eq.1 hk
  have hx : (x : G)⁻¹ * (d * (x : G) * d⁻¹) ∈ Q := by
    have h2 : ((K.normalizerMonoidHom ⟨d, hdN⟩ x)⁻¹ * x : ↥K)⁻¹ ∈ GLAPPrimeCore p ↥K := inv_mem h1
    have hcoe : ((K.normalizerMonoidHom ⟨d, hdN⟩ x : ↥K) : G) = d * (x : G) * d⁻¹ := rfl
    have h3 := (mem_gLAPPrimeCoreOf_iff p K
      (((K.normalizerMonoidHom ⟨d, hdN⟩ x)⁻¹ * x : ↥K)⁻¹ : G)).2
      ⟨((K.normalizerMonoidHom ⟨d, hdN⟩ x)⁻¹ * x : ↥K)⁻¹.2, h2⟩
    have e : (((K.normalizerMonoidHom ⟨d, hdN⟩ x)⁻¹ * x : ↥K)⁻¹ : G) =
        (x : G)⁻¹ * (d * (x : G) * d⁻¹) := by
      simp only [Subgroup.coe_inv, Subgroup.coe_mul, hcoe]
      group
    rw [e] at h3
    exact h3
  obtain ⟨q, hqQ, hq⟩ := exists_fixed_mem_coset_p hp d hdp Q hcop hQn (x : G) hx
  have hqK : q ∈ K := gLAPPrimeCoreOf_le p K hqQ
  have hxq : (x : G) * q ∈ K := K.mul_mem x.2 hqK
  refine ⟨⟨(x : G) * q, hxq⟩, ?_, ?_⟩
  · show (x : G) * q ∈ Subgroup.centralizer ({d} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : G) * q * d = d * ((x : G) * q) * d⁻¹ * d := by rw [hq]
      _ = d * ((x : G) * q) := by group
  · rw [QuotientGroup.eq]
    have hq' : (⟨(x : G) * q, hxq⟩ : ↥K)⁻¹ * x = (⟨q⁻¹, K.inv_mem hqK⟩ : ↥K) := by
      apply Subtype.ext
      simp [mul_inv_rev, mul_assoc]
    rw [hq']
    obtain ⟨_, h2⟩ := (mem_gLAPPrimeCoreOf_iff p K q⁻¹).1 (inv_mem hqQ)
    exact h2

theorem fixedSub_barAut_eq_p {p : ℕ} (hp : p.Prime) {K : Subgroup G} {d : G} (hdp : d ^ p = 1)
    (hdN : d ∈ Subgroup.normalizer (K : Set G)) :
    fixedSub (barAut p K ⟨d, hdN⟩) = barX p K (K ⊓ Subgroup.centralizer ({d} : Set G)) := by
  ext k
  constructor
  · intro hk
    obtain ⟨y, hy, hyk⟩ := exists_fixed_lift hp hdN hdp (show barAut p K ⟨d, hdN⟩ k = k from hk)
    exact ⟨y, Subgroup.mem_subgroupOf.2 ⟨y.2, hy⟩, hyk⟩
  · rintro ⟨⟨h, hhK⟩, hh, rfl⟩
    have hh' : h ∈ K ⊓ Subgroup.centralizer ({d} : Set G) := Subgroup.mem_subgroupOf.1 hh
    have hcomm : d * h = h * d := (Subgroup.mem_centralizer_singleton_iff.1 hh'.2).symm
    show barAut p K ⟨d, hdN⟩ (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨h, hhK⟩) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨h, hhK⟩
    have := barAut_mk p K ⟨d, hdN⟩ ⟨h, hhK⟩
    rw [show (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) ⟨h, hhK⟩ =
      (QuotientGroup.mk ⟨h, hhK⟩ : barOf p K) from rfl, this]
    congr 1
    apply Subtype.ext
    show d * h * d⁻¹ = h
    rw [hcomm]; group

end Lift

section AltBasic

theorem isSimple_alt {m : ℕ} (hm : 5 ≤ m) : IsSimpleGroup (alternatingGroup (Fin m)) :=
  alternatingGroup.isSimpleGroup (by simpa using hm)

theorem center_alt {m : ℕ} (hm : 4 ≤ m) : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
  alternatingGroup.center_eq_bot (by simpa using hm)

theorem isQuasisimple_alt {m : ℕ} (hm : 5 ≤ m) :
    CFSG.Open.IsQuasisimple ↥(alternatingGroup (Fin m)) := by
  haveI := isSimple_alt hm
  have hnc : ∃ a b : ↥(alternatingGroup (Fin m)), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : ↥(alternatingGroup (Fin m)))).1 inferInstance
    have h1 : a ∈ Subgroup.center ↥(alternatingGroup (Fin m)) :=
      Subgroup.mem_center_iff.2 fun g => hc g a
    rw [center_alt (by omega)] at h1
    exact ha (Subgroup.mem_bot.1 h1)
  refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq (center_alt (by omega : 4 ≤ m))).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (commutator ↥(alternatingGroup (Fin m))) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · exact h

theorem p_dvd_card_alt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hpm : p ≤ m) :
    p ∣ Nat.card (alternatingGroup (Fin m)) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by have := hp.two_le; omega)
  have h2 := two_mul_card_alternatingGroup (α := Fin m)
  rw [Fintype.card_perm, Fintype.card_fin] at h2
  have h3 : p ∣ 2 * Fintype.card (alternatingGroup (Fin m)) := by
    rw [h2]
    exact Nat.dvd_factorial hp.pos hpm
  rw [Nat.card_eq_fintype_card]
  exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) h3

theorem core_eq_bot_of_simple {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hdvd : p ∣ Nat.card Y) : GLAPPrimeCore p Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p Y) with h | h
  · exact h
  · exfalso
    have hcop := coprime_card_gLAPPrimeCore_aux p Y
    rw [h, Subgroup.card_top] at hcop
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hdvd)

theorem isPiGroup_alt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    IsPiGroup p (alternatingGroup (Fin (k * p + 2))) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h5 : 5 ≤ k * p + 2 := by nlinarith
  haveI := isSimple_alt h5
  refine ⟨isQuasisimple_alt h5, core_eq_bot_of_simple hp
    (p_dvd_card_alt hp hp2 (by nlinarith)), Or.inl ⟨k, ⟨?_⟩⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq (center_alt (by omega))).trans QuotientGroup.quotientBot

end AltBasic

section LiftComp

variable {G : Type} [Group G] [Finite G]

theorem ker_inclusion_le_core (p : ℕ) {K C : Subgroup G} (hCK : C ≤ K) :
    ((QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hCK)).ker ≤
      GLAPPrimeCore p ↥C := by
  set N := ((QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hCK)).ker with hN
  have hle : N.map C.subtype ≤ GLAPPrimeCoreOf p K := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : QuotientGroup.mk' (GLAPPrimeCore p ↥K) (Subgroup.inclusion hCK x) = 1 := hx
    exact (mem_gLAPPrimeCoreOf_iff p K _).2 ⟨hCK x.2, (QuotientGroup.eq_one_iff _).1 hx'⟩
  have hcop : Nat.Coprime p (Nat.card N) := by
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective C.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 (card_gLAPPrimeCoreOf_coprime p K)
  exact CFSG.le_pPrimeCore_of_normal_coprime inferInstance hcop

theorem lift_component {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G} {e : G}
    (heN : e ∈ Subgroup.normalizer (K : Set G)) (hep : e ^ p = 1)
    {A₀ : Subgroup (barOf p K)}
    (hA₀F : A₀ ≤ fixedSub (barAut p K ⟨e, heN⟩))
    (hA₀N : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), y ∈ Subgroup.normalizer (A₀ : Set (barOf p K)))
    {k : ℕ} (hk : 1 ≤ k) (g : ↥A₀ ≃* alternatingGroup (Fin (k * p + 2))) :
    A₀ ≤ barX p K (Prop1116.Ke p K e) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h5 : 5 ≤ k * p + 2 := by nlinarith
  haveI hsimpAlt := isSimple_alt h5
  haveI hsimpA : IsSimpleGroup ↥A₀ := g.isSimpleGroup
  haveI hntA : Nontrivial ↥A₀ := hsimpA.toNontrivial
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({e} : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hF : fixedSub (barAut p K ⟨e, heN⟩) = barX p K C := fixedSub_barAut_eq_p hp hep heN
  let ρ : ↥C →* barOf p K :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hCK)
  have hρF : ∀ c : ↥C, ρ c ∈ fixedSub (barAut p K ⟨e, heN⟩) := by
    intro c
    rw [hF]
    exact ⟨⟨c, hCK c.2⟩, Subgroup.mem_subgroupOf.2 c.2, rfl⟩
  have hρsurj : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), ∃ c : ↥C, ρ c = y := by
    intro y hy
    rw [hF] at hy
    obtain ⟨⟨c, hcK⟩, hc, rfl⟩ := hy
    exact ⟨⟨c, Subgroup.mem_subgroupOf.1 hc⟩, rfl⟩
  have hkerC : ∀ x : ↥C, ρ x = 1 → x ∈ GLAPPrimeCore p ↥C := fun x hx =>
    ker_inclusion_le_core p hCK (MonoidHom.mem_ker.2 hx)
  set NC : Subgroup ↥C := GLAPPrimeCore p ↥C with hNC
  set R : Subgroup (barOf p K) := NC.map ρ with hR
  have hRcop : Nat.Coprime p (Nat.card R) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ ρ) (coprime_card_gLAPPrimeCore_aux p ↥C)
  have hRnorm : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    obtain ⟨c, rfl⟩ := hρsurj y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hr
    refine Subgroup.mem_map.2 ⟨c * n * c⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (GLAPPrimeCore.normal p ↥C).conj_mem n hn c
  have hpdvd : p ∣ Nat.card ↥A₀ := by
    rw [Nat.card_congr g.toEquiv]
    exact p_dvd_card_alt hp hp2 (by nlinarith)
  have hRA : ∀ a ∈ A₀, a ∈ R → a = 1 := by
    have hnormS : (R.subgroupOf A₀).Normal := ⟨fun r hr a => by
      have hr' : (r : barOf p K) ∈ R := hr
      show ((a * r * a⁻¹ : ↥A₀) : barOf p K) ∈ R
      simpa using hRnorm (a : barOf p K) (hA₀F a.2) _ hr'⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf A₀) with h | h
    · intro a ha haR
      have h1 : (⟨a, ha⟩ : ↥A₀) ∈ R.subgroupOf A₀ := haR
      rw [h, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · exfalso
      have hle : A₀ ≤ R := fun a ha => by
        have h1 : (⟨a, ha⟩ : ↥A₀) ∈ R.subgroupOf A₀ := by rw [h]; exact Subgroup.mem_top _
        exact h1
      have hd : Nat.card ↥A₀ ∣ Nat.card ↥R := Subgroup.card_dvd_of_le hle
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hRcop (dvd_refl p) (hpdvd.trans hd))
  set P : Subgroup ↥C := A₀.comap ρ with hP
  have hPnorm : P.Normal := ⟨fun x hx c => by
    have hx' : ρ x ∈ A₀ := hx
    show ρ (c * x * c⁻¹) ∈ A₀
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hA₀N _ (hρF c)) (ρ x)).1 hx'⟩
  set K' : Subgroup (↥C ⧸ NC) := P.map (QuotientGroup.mk' NC) with hK'
  let π₁ : ↥P →* ↥A₀ := (ρ.comp P.subtype).codRestrict A₀ (fun x => x.2)
  have hπ₁ : Function.Surjective π₁ := by
    intro a
    obtain ⟨c, hc⟩ := hρsurj (a : barOf p K) (hA₀F a.2)
    have hcP : c ∈ P := by
      show ρ c ∈ A₀
      rw [hc]; exact a.2
    exact ⟨⟨c, hcP⟩, Subtype.ext hc⟩
  let π₂ : ↥P →* ↥K' := ((QuotientGroup.mk' NC).comp P.subtype).codRestrict K' (fun x => ⟨x, x.2, rfl⟩)
  have hπ₂ : Function.Surjective π₂ := by
    rintro ⟨_, ⟨c, hc, rfl⟩⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  have hker12 : π₁.ker ≤ π₂.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : ρ (x : ↥C) = 1 := congrArg Subtype.val hx
    have h2 : (x : ↥C) ∈ NC := hkerC _ h1
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h2)
  let f1 : ↥A₀ →* ↥K' :=
    (QuotientGroup.lift π₁.ker π₂ hker12).comp
      (QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).symm.toMonoidHom
  have hf1 : ∀ x : ↥P, f1 (π₁ x) = π₂ x := by
    intro x
    show (QuotientGroup.lift π₁.ker π₂ hker12)
      ((QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).symm (π₁ x)) = _
    have : (QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).symm (π₁ x) =
        (QuotientGroup.mk x : ↥P ⧸ π₁.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    rw [this, QuotientGroup.lift_mk]
  have hf1s : Function.Surjective f1 := by
    intro y
    obtain ⟨x, rfl⟩ := hπ₂ y
    exact ⟨π₁ x, hf1 x⟩
  have hKnt : Nontrivial ↥K' := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hPN : ∀ x : ↥C, x ∈ P → x ∈ NC := by
      intro x hx
      have h1 : π₂ ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).1 (congrArg Subtype.val h1)
    have hA₀1 : ∀ a ∈ A₀, a = 1 := by
      intro a ha
      obtain ⟨c, hc⟩ := hρsurj a (hA₀F ha)
      have hcP : c ∈ P := by
        show ρ c ∈ A₀
        rw [hc]; exact ha
      exact hRA a ha ⟨c, hPN c hcP, hc⟩
    obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : ↥A₀)).1 hntA
    exact ha (Subtype.ext (hA₀1 a a.2))
  have hf1i : Function.Injective f1 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f1.ker with h | h
    · exact h
    · exfalso
      have h1 : ∀ x : ↥A₀, f1 x = 1 := fun x => by
        rw [← MonoidHom.mem_ker, h]; exact Subgroup.mem_top x
      obtain ⟨y, hy⟩ := (nontrivial_iff_exists_ne (1 : ↥K')).1 hKnt
      obtain ⟨x, rfl⟩ := hf1s y
      exact hy (h1 x)
  let e₂ : ↥A₀ ≃* ↥K' := MulEquiv.ofBijective f1 ⟨hf1i, hf1s⟩
  have hKq : CFSG.Open.IsQuasisimple ↥K' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (g.symm.trans e₂)
      (isQuasisimple_alt h5)
  have hcomp : IsComponentOf K' (⊤ : Subgroup (↥C ⧸ NC)) := by
    refine ⟨le_top, ?_, hKq⟩
    haveI : K'.Normal := hPnorm.map _ (QuotientGroup.mk'_surjective NC)
    exact IsSubnormal.step le_top (Subgroup.Normal.subgroupOf inferInstance _) (IsSubnormal.refl _)
  obtain ⟨J, hJ, hJK⟩ := exists_glaPComponent_barX_eq (p := p) C hcomp
  let φ : barOf p J ≃* alternatingGroup (Fin (k * p + 2)) :=
    (barXEquiv hp hJ.2.1).trans ((MulEquiv.subgroupCongr hJK).trans (e₂.symm.trans g))
  have hPi : IsPiGroup p (barOf p J) := isPiGroup_of_mulEquiv φ.symm (isPiGroup_alt hp hp2 hk)
  have hJKe : J ≤ Prop1116.Ke p K e := le_Ke_of_component hJ hPi
  intro a ha
  obtain ⟨c, hc⟩ := hρsurj a (hA₀F ha)
  have hcP : c ∈ P := by
    show ρ c ∈ A₀
    rw [hc]; exact ha
  have hmem : QuotientGroup.mk' NC c ∈ barX p C J := by
    rw [hJK]; exact ⟨c, hcP, rfl⟩
  obtain ⟨j', hj', hjc⟩ := hmem
  have hn : j'⁻¹ * c ∈ NC := QuotientGroup.eq.1 hjc
  have hcKe : (c : G) ∈ Prop1116.Ke p K e := by
    have h1 : (j' : G) ∈ Prop1116.Ke p K e := hJKe (Subgroup.mem_subgroupOf.1 hj')
    have h2 : ((j'⁻¹ * c : ↥C) : G) ∈ GLAPPrimeCoreOf p C := (mem_gLAPPrimeCoreOf_iff p C _).2 ⟨(j'⁻¹ * c).2, hn⟩
    have h3 : ((j'⁻¹ * c : ↥C) : G) ∈ Prop1116.Ke p K e := core_le_Ke p K e h2
    have h4 := (Prop1116.Ke p K e).mul_mem h1 h3
    simpa using h4
  refine ⟨⟨(c : G), hCK c.2⟩, Subgroup.mem_subgroupOf.2 hcKe, ?_⟩
  exact hc

end LiftComp

section Gen3

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

def tc (a b c : α) : Perm α := swap a b * swap b c

theorem tc_conj (g : Perm α) (a b c : α) : g * tc a b c * g⁻¹ = tc (g a) (g b) (g c) := by
  unfold tc
  rw [swap_apply_apply g a b, swap_apply_apply g b c]
  group

theorem tc_rot {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : tc b c a = tc a b c := by
  ext w
  simp only [tc, Perm.coe_mul, Function.comp_apply, swap_apply_def]
  split_ifs <;> grind

theorem tc_inv (a b c : α) : (tc a b c)⁻¹ = tc c b a := by
  unfold tc
  rw [mul_inv_rev, swap_inv, swap_inv, swap_comm c b, swap_comm b a]

def Gs (Γ : Subgroup (Perm α)) (s : Set α) : Prop :=
  ∀ a b c, a ∈ s → b ∈ s → c ∈ s → a ≠ b → b ≠ c → a ≠ c → tc a b c ∈ Γ

theorem Gs_of_tc {Γ : Subgroup (Perm α)} {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h : tc a b c ∈ Γ) : Gs Γ {a, b, c} := by
  have h1 : tc b c a ∈ Γ := by rwa [tc_rot hab hbc hac]
  have h2 : tc c a b ∈ Γ := by
    rw [tc_rot hbc hac.symm hab.symm]; exact h1
  have h3 : tc c b a ∈ Γ := by rw [← tc_inv]; exact Γ.inv_mem h
  have h4 : tc b a c ∈ Γ := by rw [← tc_inv]; exact Γ.inv_mem h2
  have h5 : tc a c b ∈ Γ := by rw [← tc_inv]; exact Γ.inv_mem h1
  intro u v w hu hv hw huv hvw huw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv hw
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl <;> first | assumption | (exfalso; grind)

theorem Gs_conj {Γ : Subgroup (Perm α)} {s : Set α} (h : Gs Γ s) {g : Perm α} (hg : g ∈ Γ) :
    Gs Γ (g '' s) := by
  rintro _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ hab hbc hac
  rw [← tc_conj]
  exact Γ.mul_mem (Γ.mul_mem hg (h a b c ha hb hc (fun e => hab (by rw [e])) (fun e => hbc (by rw [e]))
    (fun e => hac (by rw [e])))) (Γ.inv_mem hg)

theorem alternatingGroup_le_of_swap_mul_swap {Γ : Subgroup (Perm α)} {x y : α} (hxy : x ≠ y)
    (h : ∀ i, i ≠ x → i ≠ y → swap x y * swap x i ∈ Γ) : alternatingGroup α ≤ Γ := by
  have hA : ∀ i, i ≠ x → i ≠ y → Gs Γ {y, x, i} := by
    intro i hix hiy
    refine Gs_of_tc hxy.symm hix.symm hiy.symm ?_
    have := h i hix hiy
    rwa [tc, swap_comm y x]
  have hA' : ∀ i, i ≠ x → i ≠ y → Gs Γ {x, y, i} := by
    intro i hix hiy
    have := hA i hix hiy
    rwa [Set.insert_comm y x] at this
  have hB : ∀ i j, i ≠ j → i ≠ x → i ≠ y → j ≠ x → j ≠ y → Gs Γ {x, i, j} := by
    intro i j hij hix hiy hjx hjy
    have hgi : swap x y * swap x i ∈ Γ := h i hix hiy
    have hc := Gs_conj (hA j hjx hjy) hgi
    have e1 : (swap x y * swap x i) y = x := by
      simp [swap_apply_of_ne_of_ne, hxy, hxy.symm, hix, hix.symm, hiy, hiy.symm]
    have e2 : (swap x y * swap x i) x = i := by
      simp [swap_apply_of_ne_of_ne, hxy, hxy.symm, hix, hix.symm, hiy, hiy.symm]
    have e3 : (swap x y * swap x i) j = j := by
      simp [swap_apply_of_ne_of_ne, hxy, hxy.symm, hix, hix.symm, hiy, hiy.symm, hij, hij.symm,
        hjx, hjy, hjx.symm, hjy.symm]
    simpa only [Set.image_insert_eq, Set.image_singleton, e1, e2, e3] using hc
  have hB' : ∀ i j, i ≠ j → i ≠ x → i ≠ y → j ≠ x → j ≠ y → Gs Γ {y, i, j} := by
    intro i j hij hix hiy hjx hjy
    have hgi : swap x y * swap y i ∈ Γ := by
      have := (hA' i hix hiy) x y i (by simp) (by simp) (by simp) hxy hiy.symm hix.symm
      exact this
    have hc := Gs_conj (hA' j hjx hjy) hgi
    have e1 : (swap x y * swap y i) x = y := by
      simp [swap_apply_of_ne_of_ne, hxy, hxy.symm, hix, hix.symm, hiy, hiy.symm]
    have e2 : (swap x y * swap y i) y = i := by
      simp [swap_apply_of_ne_of_ne, hxy, hxy.symm, hix, hix.symm, hiy, hiy.symm]
    have e3 : (swap x y * swap y i) j = j := by
      simp [swap_apply_of_ne_of_ne, hxy, hxy.symm, hix, hix.symm, hiy, hiy.symm, hij, hij.symm,
        hjx, hjy, hjx.symm, hjy.symm]
    simpa only [Set.image_insert_eq, Set.image_singleton, e1, e2, e3] using hc
  have hC : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → a ≠ x → a ≠ y → b ≠ x → b ≠ y → c ≠ x → c ≠ y →
      Gs Γ {b, a, c} := by
    intro a b c hab hbc hac hax hay hbx hby hcx hcy
    have hgb : swap x y * swap x b ∈ Γ := h b hbx hby
    have hc := Gs_conj (hB a c hac hax hay hcx hcy) hgb
    have e1 : (swap x y * swap x b) x = b := by
      simp [swap_apply_of_ne_of_ne, hxy, hxy.symm, hbx, hbx.symm, hby, hby.symm]
    have e2 : (swap x y * swap x b) a = a := by
      simp [swap_apply_of_ne_of_ne, hxy, hxy.symm, hax, hax.symm, hay, hay.symm, hab, hab.symm,
        hbx, hbx.symm, hby, hby.symm]
    have e3 : (swap x y * swap x b) c = c := by
      simp [swap_apply_of_ne_of_ne, hxy, hxy.symm, hcx, hcx.symm, hcy, hcy.symm, hbc, hbc.symm,
        hbx, hbx.symm, hby, hby.symm]
    simpa only [Set.image_insert_eq, Set.image_singleton, e1, e2, e3] using hc
  have key : ∀ a b c : α, a ≠ b → b ≠ c → a ≠ c → tc a b c ∈ Γ := by
    intro a b c hab hbc hac
    have hxpos : x = a ∨ x = b ∨ x = c ∨ (x ≠ a ∧ x ≠ b ∧ x ≠ c) := by grind
    have hypos : y = a ∨ y = b ∨ y = c ∨ (y ≠ a ∧ y ≠ b ∧ y ≠ c) := by grind
    have cover : ∃ s : Set α, Gs Γ s ∧ a ∈ s ∧ b ∈ s ∧ c ∈ s := by
      rcases hxpos with hx | hx | hx | ⟨hxa, hxb, hxc⟩ <;>
        rcases hypos with hy | hy | hy | ⟨hya, hyb, hyc⟩
      · exact absurd (hx.trans hy.symm) hxy
      · exact ⟨{x, y, c}, hA' c (by grind) (by grind), by simp [hx], by simp [hy], by simp⟩
      · exact ⟨{x, y, b}, hA' b (by grind) (by grind), by simp [hx], by simp, by simp [hy]⟩
      · exact ⟨{x, b, c}, hB b c hbc (by grind) (by grind) (by grind) (by grind), by simp [hx],
          by simp, by simp⟩
      · exact ⟨{x, y, c}, hA' c (by grind) (by grind), by simp [hy], by simp [hx], by simp⟩
      · exact absurd (hx.trans hy.symm) hxy
      · exact ⟨{x, y, a}, hA' a (by grind) (by grind), by simp, by simp [hx], by simp [hy]⟩
      · exact ⟨{x, a, c}, hB a c hac (by grind) (by grind) (by grind) (by grind), by simp,
          by simp [hx], by simp⟩
      · exact ⟨{x, y, b}, hA' b (by grind) (by grind), by simp [hy], by simp, by simp [hx]⟩
      · exact ⟨{x, y, a}, hA' a (by grind) (by grind), by simp, by simp [hy], by simp [hx]⟩
      · exact absurd (hx.trans hy.symm) hxy
      · exact ⟨{x, a, b}, hB a b hab (by grind) (by grind) (by grind) (by grind), by simp,
          by simp, by simp [hx]⟩
      · exact ⟨{y, b, c}, hB' b c hbc (by grind) (by grind) (by grind) (by grind), by simp [hy],
          by simp, by simp⟩
      · exact ⟨{y, a, c}, hB' a c hac (by grind) (by grind) (by grind) (by grind), by simp,
          by simp [hy], by simp⟩
      · exact ⟨{y, a, b}, hB' a b hab (by grind) (by grind) (by grind) (by grind), by simp,
          by simp, by simp [hy]⟩
      · exact ⟨{b, a, c}, hC a b c hab hbc hac (by grind) (by grind) (by grind) (by grind)
          (by grind) (by grind), by simp, by simp, by simp⟩
    obtain ⟨s, hs, ha, hb, hc⟩ := cover
    exact hs a b c ha hb hc hab hbc hac
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro g hg
  have hg3 : g.IsThreeCycle := hg
  obtain ⟨a, ha⟩ := hg3.isCycle.nonempty_support
  have hnodup := hg3.nodup_iff_mem_support.2 ha
  have hgeq := (hg3.eq_swap_mul_swap_iff_mem_support (a := a)).2 ha
  have hdist : a ≠ g a ∧ g a ≠ g (g a) ∧ a ≠ g (g a) := by
    have h1 : (¬a = g a ∧ ¬a = g (g a)) ∧ ¬a = g a := by simpa using hnodup
    exact ⟨h1.1.1, fun h => h1.1.1 (g.injective h), h1.1.2⟩
  show g ∈ (Γ : Set (Perm α))
  rw [hgeq]
  exact key a (g a) (g (g a)) hdist.1 hdist.2.1 hdist.2.2

end Gen3

section Count

open Equiv Equiv.Perm

theorem card_fixedPoints_modEq {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] (hQ : IsPGroup p Q)
    {n : ℕ} (σ : Q →* Perm (Fin n)) :
    Nat.card {i : Fin n // ∀ q, σ q i = i} ≡ n [MOD p] := by
  letI : MulAction Q (Fin n) := MulAction.compHom (Fin n) σ
  have h := hQ.card_modEq_card_fixedPoints (Fin n)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have e : Nat.card (MulAction.fixedPoints Q (Fin n)) = Nat.card {i : Fin n // ∀ q, σ q i = i} :=
    rfl
  rw [e] at h
  exact h.symm

theorem card_fix_modEq {p : ℕ} [Fact p.Prime] {n : ℕ} (τ : Perm (Fin n)) (hτ : τ ^ p = 1) :
    Nat.card {i : Fin n // τ i = i} ≡ n [MOD p] := by
  let f : Function.End (Fin n) := fun i => τ i
  have hf : f ^ p ^ 1 = 1 := by
    funext i
    rw [pow_one]
    show (⇑τ)^[p] i = i
    rw [Equiv.Perm.iterate_eq_pow, hτ]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  rw [Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  exact h.symm

theorem two_le_card_globalFix {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q]
    (hQ : IsPGroup p Q) {n : ℕ} (σ : Q →* Perm (Fin n)) (hn2 : n % p = 2) (hp3 : 3 ≤ p) :
    2 ≤ Nat.card {j : Fin n // ∀ q, σ q j = j} := by
  have hmod := card_fixedPoints_modEq hQ σ
  have h1 : Nat.card {j : Fin n // ∀ q, σ q j = j} % p = 2 := by rw [hmod]; exact hn2
  by_contra hlt
  push Not at hlt
  have : Nat.card {j : Fin n // ∀ q, σ q j = j} % p = Nat.card {j : Fin n // ∀ q, σ q j = j} :=
    Nat.mod_eq_of_lt (by omega)
  omega

theorem exists_fixing_point {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) {n : ℕ} (σ : Q →* Perm (Fin n)) (hn2 : n % p = 2) (hp3 : 3 ≤ p)
    (hnQ : n ≤ Nat.card Q) (i : Fin n) : ∃ q : Q, q ≠ 1 ∧ σ q i = i := by
  by_contra hcon
  push Not at hcon
  have hn2' : 2 ≤ n := by have := Nat.mod_le n p; omega
  have hF2 := two_le_card_globalFix hQ σ hn2 hp3
  haveI hQnt : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨q₀, hq₀⟩ := exists_ne (1 : Q)
  have hiF : ¬ ∀ q, σ q i = i := fun h => hcon q₀ hq₀ (h q₀)
  let φ : Q → Fin n := fun q => σ q i
  have hφ : Function.Injective φ := by
    intro q q' hqq
    by_contra hne
    have hne' : q⁻¹ * q' ≠ 1 := fun h => hne (inv_mul_eq_one.1 h)
    apply hcon (q⁻¹ * q') hne'
    have hqq' : σ q' i = σ q i := hqq.symm
    simp only [map_mul, map_inv, Perm.coe_mul, Function.comp_apply]
    rw [hqq']
    exact (σ q).symm_apply_apply i
  have hdisj : ∀ q, ¬ ∀ r, σ r (σ q i) = σ q i := by
    intro q h
    apply hiF
    have h1 : σ q⁻¹ (σ q i) = σ q i := h q⁻¹
    have h2 : σ q⁻¹ (σ q i) = i := by
      simp only [map_inv]
      exact (σ q).symm_apply_apply i
    rw [h2] at h1
    intro r
    have := h r
    rwa [← h1] at this
  have hcard : Nat.card Q + Nat.card {j : Fin n // ∀ q, σ q j = j} ≤ n := by
    let ψ : Q ⊕ {j : Fin n // ∀ q, σ q j = j} → Fin n := Sum.elim φ (fun f => f.1)
    have hψ : Function.Injective ψ := by
      rintro (q | f) (q' | f') h
      · exact congrArg Sum.inl (hφ h)
      · have h' : σ q i = f'.1 := h
        exact absurd (fun r => by rw [h']; exact f'.2 r) (hdisj q)
      · have h' : σ q' i = f.1 := h.symm
        exact absurd (fun r => by rw [h']; exact f.2 r) (hdisj q')
      · exact congrArg Sum.inr (Subtype.ext h)
    have := Nat.card_le_card_of_injective ψ hψ
    rwa [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
  omega

end Count

section AltOn

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop) [DecidablePred P]

def altOn : Subgroup (Perm α) :=
  (alternatingGroup {i // P i}).map (Equiv.Perm.ofSubtype (p := P))

theorem altOn_le : altOn P ≤ alternatingGroup α := by
  rintro _ ⟨τ', hτ', rfl⟩
  have hτ'' : τ' ∈ alternatingGroup {i // P i} := hτ'
  rw [mem_alternatingGroup] at hτ'' ⊢
  rw [Equiv.Perm.sign_ofSubtype]
  exact hτ''

theorem apply_eq_of_mem_altOn {τ : Perm α} (hτ : τ ∈ altOn P) {i : α} (hi : ¬ P i) : τ i = i := by
  obtain ⟨τ', -, rfl⟩ := hτ
  exact Equiv.Perm.ofSubtype_apply_of_not_mem τ' hi

theorem mem_altOn_of {τ : Perm α} (hτ : τ ∈ alternatingGroup α) (h : ∀ i, ¬ P i → τ i = i) :
    τ ∈ altOn P := by
  have h₁ : ∀ x, P (τ x) ↔ P x := by
    intro x
    constructor
    · intro hx
      by_contra hnx
      have := h x hnx
      rw [this] at hx
      exact hnx hx
    · intro hx
      by_contra hnx
      have h2 := h (τ x) hnx
      have : τ x = x := τ.injective h2
      rw [this] at hnx
      exact hnx hx
  have h₂ : ∀ x, τ x ≠ x → P x := fun x hx => by
    by_contra hnx
    exact hx (h x hnx)
  refine ⟨Equiv.Perm.subtypePerm τ h₁, ?_, Equiv.Perm.ofSubtype_subtypePerm h₁ h₂⟩
  show Equiv.Perm.subtypePerm τ h₁ ∈ alternatingGroup {i // P i}
  rw [mem_alternatingGroup, Equiv.Perm.sign_subtypePerm τ h₁ h₂]
  exact hτ

theorem conj_mem_altOn {g τ : Perm α} (hg : ∀ x, P (g x) ↔ P x) (hτ : τ ∈ altOn P) :
    g * τ * g⁻¹ ∈ altOn P := by
  refine mem_altOn_of P ((alternatingGroup.normal).conj_mem τ (altOn_le P hτ) g) ?_
  intro i hi
  have hgi : ¬ P (g⁻¹ i) := by
    intro h
    apply hi
    have := (hg (g⁻¹ i)).2 h
    rwa [show g (g⁻¹ i) = i from g.apply_symm_apply i] at this
  have := apply_eq_of_mem_altOn P hτ hgi
  simp only [Perm.coe_mul, Function.comp_apply, this]
  exact g.apply_symm_apply i

theorem comm_of_mem_altOn {σ' τ : Perm α} (hτ : τ ∈ altOn (fun i => σ' i = i)) :
    τ * σ' = σ' * τ := by
  ext i
  simp only [Perm.coe_mul, Function.comp_apply]
  by_cases hi : σ' i = i
  ·
    have h1 : σ' (τ i) = τ i := by
      by_contra hne
      have h2 : τ (τ i) = τ i := apply_eq_of_mem_altOn _ hτ (fun h => hne h)
      have : τ i = i := τ.injective h2
      rw [this] at hne
      exact hne hi
    rw [hi, h1]
  · have h1 : τ i = i := apply_eq_of_mem_altOn _ hτ hi
    have h2 : τ (σ' i) = σ' i := by
      apply apply_eq_of_mem_altOn _ hτ
      intro h
      apply hi
      have : σ' i = i := σ'.injective (by rw [h])
      exact this
    rw [h1, h2]

theorem swap_mul_swap_mem_altOn {x y i : α} (hx : P x) (hy : P y) (hi : P i) (hxy : x ≠ y)
    (hxi : x ≠ i) (hyi : y ≠ i) : swap x y * swap x i ∈ altOn P := by
  refine mem_altOn_of P (Equiv.Perm.isThreeCycle_swap_mul_swap_same hxy hxi hyi).mem_alternatingGroup ?_
  intro j hj
  have hjx : j ≠ x := fun h => hj (h ▸ hx)
  have hjy : j ≠ y := fun h => hj (h ▸ hy)
  have hji : j ≠ i := fun h => hj (h ▸ hi)
  simp [swap_apply_of_ne_of_ne, hjx, hjy, hji]

noncomputable def altOnEquiv : alternatingGroup {i // P i} ≃* altOn P :=
  Subgroup.equivMapOfInjective _ _ Equiv.Perm.ofSubtype_injective

end AltOn

section A0

open Equiv Equiv.Perm

variable {Y : Type*} [Group Y] {n : ℕ}

def permHom (f : Y ≃* alternatingGroup (Fin n)) : Y →* Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp f.toMonoidHom

theorem permHom_injective (f : Y ≃* alternatingGroup (Fin n)) : Function.Injective (permHom f) :=
  Subtype.coe_injective.comp f.injective

theorem permHom_mem (f : Y ≃* alternatingGroup (Fin n)) (x : Y) :
    permHom f x ∈ alternatingGroup (Fin n) :=
  (f x).2

theorem exists_permHom_eq (f : Y ≃* alternatingGroup (Fin n)) {τ : Perm (Fin n)}
    (hτ : τ ∈ alternatingGroup (Fin n)) : ∃ x, permHom f x = τ :=
  ⟨f.symm ⟨τ, hτ⟩, by simp [permHom]⟩

def A0 (f : Y ≃* alternatingGroup (Fin n)) (P : Fin n → Prop) [DecidablePred P] : Subgroup Y :=
  (altOn P).comap (permHom f)

theorem mem_A0 (f : Y ≃* alternatingGroup (Fin n)) (P : Fin n → Prop) [DecidablePred P] {x : Y} :
    x ∈ A0 f P ↔ permHom f x ∈ altOn P := Iff.rfl

noncomputable def A0Equiv (f : Y ≃* alternatingGroup (Fin n)) (P : Fin n → Prop)
    [DecidablePred P] : ↥(A0 f P) ≃* alternatingGroup {i // P i} :=
  (MulEquiv.ofBijective (((permHom f).comp (A0 f P).subtype).codRestrict (altOn P) (fun x => x.2))
    ⟨fun x y h => by
       have h' : permHom f (x : Y) = permHom f (y : Y) := by
         have := congrArg (fun z : ↥(altOn P) => (z : Perm (Fin n))) h
         exact this
       exact Subtype.ext (permHom_injective f h'),
     fun τ => by
       obtain ⟨x, hx⟩ := exists_permHom_eq f (altOn_le P τ.2)
       exact ⟨⟨x, by rw [mem_A0, hx]; exact τ.2⟩, Subtype.ext hx⟩⟩).trans (altOnEquiv P).symm

noncomputable def A0EquivFin (f : Y ≃* alternatingGroup (Fin n)) (P : Fin n → Prop)
    [DecidablePred P] {m : ℕ} (hm : Fintype.card {i // P i} = m) :
    ↥(A0 f P) ≃* alternatingGroup (Fin m) :=
  (A0Equiv f P).trans (Equiv.altCongrHom (Fintype.equivFinOfCardEq hm))

theorem A0_props (f : Y ≃* alternatingGroup (Fin n)) (α : MulAut Y) (τ : Perm (Fin n))
    (hτ : ∀ x, permHom f (α x) = τ * permHom f x * τ⁻¹) :
    A0 f (fun i => τ i = i) ≤ fixedSub α ∧
      ∀ y ∈ fixedSub α, y ∈ Subgroup.normalizer (A0 f (fun i => τ i = i) : Set Y) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hcomm : permHom f x * τ = τ * permHom f x := comm_of_mem_altOn hx
    show α x = x
    apply permHom_injective f
    rw [hτ x, ← hcomm]
    group
  · intro y hy
    have hyα : α y = y := hy
    have hconj : ∀ y' ∈ fixedSub α, ∀ h ∈ A0 f (fun i => τ i = i),
        y' * h * y'⁻¹ ∈ A0 f (fun i => τ i = i) := by
      intro y' hy' h hh
      have hy'α : α y' = y' := hy'
      have hcomm' : τ * permHom f y' = permHom f y' * τ := by
        have h1 := hτ y'
        rw [hy'α] at h1
        calc τ * permHom f y' = (τ * permHom f y' * τ⁻¹) * τ := by group
          _ = permHom f y' * τ := by rw [← h1]
      have hpres' : ∀ i, τ (permHom f y' i) = permHom f y' i ↔ τ i = i := by
        intro i
        have h2 : τ (permHom f y' i) = permHom f y' (τ i) := by
          have := congrArg (fun σ : Perm (Fin n) => σ i) hcomm'
          simpa using this
        rw [h2]
        exact (permHom f y').injective.eq_iff
      rw [mem_A0, map_mul, map_mul, map_inv]
      exact conj_mem_altOn (fun i => τ i = i) hpres' hh
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj y hy h hh, fun hh => ?_⟩
    have := hconj y⁻¹ ((fixedSub α).inv_mem hy) _ hh
    simpa [mul_assoc] using this

end A0

open Equiv Equiv.Perm in
theorem inputAltGenFixed_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G),
      GLAPComponent p X K → B ≤ X → B ≤ Subgroup.normalizer (K : Set G) → IsElemAbelian p B →
      2 ≤ CFSG.Open.pRank p B → ∀ n : ℕ, n % p = 2 → IsAltType n (barOf p K) →
        barX p X K ≤ barX p X (⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Prop1116.Ke p K e) ∨
          p ^ CFSG.Open.pRank p B < n := by
  intro G _ _ p hp hp2 X K B hK hBX hBn hBel hBrk n hn2 hAlt
  by_cases hlt : p ^ CFSG.Open.pRank p B < n
  · exact Or.inr hlt
  refine Or.inl ?_
  have hnle : n ≤ p ^ CFSG.Open.pRank p B := not_lt.1 hlt
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set H : Subgroup G := ⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Prop1116.Ke p K e with hH
  have hHK : H ≤ K := iSup_le fun e => iSup_le fun _ => iSup_le fun _ => Ke_le p K e
  have hKe_le : ∀ e ∈ B, e ≠ 1 → Prop1116.Ke p K e ≤ H := fun e he he1 =>
    le_iSup_of_le e (le_iSup_of_le he (le_iSup_of_le he1 le_rfl))
  suffices htop : barX p K H = ⊤ by
    have hcov := (barX_eq_top_iff p hHK).1 htop
    exact ((barX_eq_iff_cov hp hK.2.1 hHK).2 hcov).ge
  have hq : CFSG.Open.IsQuasisimple (barOf p K) :=
    (isQuasisimple_barX_iff hp hK.2.1).1 hK.2.2.1.2.2
  obtain ⟨f⟩ := hAlt
  haveI hnt : Nontrivial (barOf p K) := by
    haveI := hq.2.toNontrivial
    exact (QuotientGroup.mk_surjective (s := Subgroup.center (barOf p K))).nontrivial
  have h5 : 5 ≤ n := by
    by_contra h
    have h4 : n ≤ 4 := by omega
    haveI : Group.IsSolvable (alternatingGroup (Fin n)) :=
      alternatingGroup.isSolvable (by simpa using h4)
    haveI : Group.IsSolvable (barOf p K) := solvable_of_solvable_injective (f := f.toMonoidHom) f.injective
    exact absurd hq.1 (Group.IsSolvable.commutator_lt_top_of_nontrivial (barOf p K)).ne
  have h6 : n ≠ 6 := by
    rintro rfl
    have h2 : (2 : ℕ) % p = 2 := Nat.mod_eq_of_lt (by omega)
    have h3 : (6 - 2) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by rw [hn2, h2])
    have h4 : p ∣ 2 ^ 2 := Nat.dvd_of_mod_eq_zero (by simpa using h3)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  let Φ : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n h5 h6)
  let σ : ↥B →* Perm (Fin n) :=
    Φ.symm.toMonoidHom.comp ((MulAut.congr f).toMonoidHom.comp
      ((barAut p K).comp (Subgroup.inclusion hBn)))
  have hσ : ∀ (b : ↥B) (x : barOf p K),
      permHom f (barAut p K ⟨(b : G), hBn b.2⟩ x) = σ b * permHom f x * (σ b)⁻¹ := by
    intro b x
    have h : Φ (σ b) = MulAut.congr f (barAut p K ⟨(b : G), hBn b.2⟩) := Φ.apply_symm_apply _
    have h2 := congrArg (fun ψ : MulAut ↥(alternatingGroup (Fin n)) =>
      ((ψ (f x) : ↥(alternatingGroup (Fin n))) : Perm (Fin n))) h
    simpa [Φ, MulAut.conjNormal_apply, permHom] using h2.symm
  have hB3 : IsPGroup p ↥B := fun g => ⟨1, Subtype.ext (by simpa using hBel.2 g g.2)⟩
  have hBcard : n ≤ Nat.card ↥B := by
    obtain ⟨E, hEB, -, hE⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (le_refl (CFSG.Open.pRank p B))
    have h1 := Subgroup.card_le_of_le hEB
    rw [hE] at h1
    exact hnle.trans h1
  have hFcard := two_le_card_globalFix hB3 σ hn2 hp3
  haveI hnt2 : Nontrivial {j : Fin n // ∀ b : ↥B, σ b j = j} :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne {j : Fin n // ∀ b : ↥B, σ b j = j}
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have hgen : alternatingGroup (Fin n) ≤ (barX p K H).map (permHom f) := by
    refine alternatingGroup_le_of_swap_mul_swap hxy' ?_
    intro i hix hiy
    obtain ⟨b, hb1, hbi⟩ := exists_fixing_point hB3 σ hn2 hp3 hBcard i
    have hbG : (b : G) ∈ B := b.2
    have hbG1 : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hbp : (σ b) ^ p = 1 := by
      rw [← map_pow]
      have : b ^ p = 1 := Subtype.ext (by simpa using hBel.2 b b.2)
      rw [this, map_one]
    have hm3 : 3 ≤ Fintype.card {j : Fin n // σ b j = j} := by
      rw [Fintype.card_subtype]
      have hsub : ({x.1, y.1, i} : Finset (Fin n)) ⊆ Finset.univ.filter (fun j => σ b j = j) := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hj with rfl | rfl | rfl
        · exact x.2 b
        · exact y.2 b
        · exact hbi
      have := Finset.card_le_card hsub
      rwa [Finset.card_eq_three.2 ⟨x.1, y.1, i, hxy', hix.symm, hiy.symm, rfl⟩] at this
    have hmmod : Fintype.card {j : Fin n // σ b j = j} % p = 2 := by
      have h1 := card_fix_modEq (σ b) hbp
      rw [Nat.card_eq_fintype_card] at h1
      rw [h1]
      exact hn2
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card {j : Fin n // σ b j = j} = k * p + 2 :=
      ⟨Fintype.card {j : Fin n // σ b j = j} / p, by
        have := Nat.div_add_mod (Fintype.card {j : Fin n // σ b j = j}) p
        rw [hmmod] at this
        linarith⟩
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have : k = 0 := by omega
      rw [this] at hk
      omega
    have hA0 := A0_props f (barAut p K ⟨(b : G), hBn b.2⟩) (σ b) (hσ b)
    have hlift := lift_component hp hp2 (hBn b.2) (hBel.2 _ b.2) hA0.1 hA0.2 hk1
      (A0EquivFin f (fun j => σ b j = j) hk)
    have hτ : swap x.1 y.1 * swap x.1 i ∈ altOn (fun j => σ b j = j) :=
      swap_mul_swap_mem_altOn _ (x.2 b) (y.2 b) hbi hxy' hix.symm hiy.symm
    obtain ⟨a, ha⟩ := exists_permHom_eq f (altOn_le _ hτ)
    have haA0 : a ∈ A0 f (fun j => σ b j = j) := by rw [mem_A0, ha]; exact hτ
    have haH : a ∈ barX p K H := barX_mono_of_le p (hKe_le _ hbG hbG1) (hlift haA0)
    exact Subgroup.mem_map.2 ⟨a, haH, ha⟩
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.1 (hgen (permHom_mem f z))
  exact (permHom_injective f hmz) ▸ hm

theorem prop1117_of_inputs_fixed (h112 : Prop112Statement) (h115 : Prop115Statement)
    (h117 : Prop117_cex_falseStatement) (hI19 : Input19_19) (hI22 : Input22_3_2)
    (hI18 : Input18_3_diag) (hNot27 : Prop1116.InputNotL27Pi) (hOmDvd : Prop1116.InputOmegaDvd)
    (hOm : Prop1116.InputOmegaGen)
    (hSchur : Prop1116.InputSchurAlt) :
    Prop1117Statement := by
  have hAlt := inputAltGenFixed_holds
  intro G _ _ m p B M E A h a ha ha1
  obtain ⟨hp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    have hb := h.standing.beta
    unfold GLABeta at hb
    exact ⟨hb.1, hb.2.1⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3le : 3 ≤ p := by have := hp.two_le; omega
  have h111 : Prop111Statement := prop111_of_prop112 h112
  by_cases hA1 : ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1
  · obtain ⟨A1, hA1, haA1⟩ := hA1
    exact le_sup_right.trans (hA1.2.clause_a a haA1 ha1)
  · have hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := hA1
    have h11 : GLAPPrimeCoreOf p (Cg a) ≤ M := h111 h ha ha1
    unfold piOf piLayer
    refine iSup₂_le fun K hK => ?_
    obtain ⟨hKc, hKpi⟩ := hK
    by_contra hKM
    obtain ⟨hDDp, -⟩ := h.pair
    obtain ⟨-, hDp, hrA0⟩ := hDDp
    obtain ⟨hSCs, -⟩ := hDp
    obtain ⟨hSCp, -⟩ := hSCs
    obtain ⟨-, hAel, -⟩ := hSCp
    have hACg : A ≤ Subgroup.centralizer ({a} : Set G) := Prop1116.le_cg_of_mem_elemAbelian hAel ha
    have hBle : E ⊓ A ≤ Subgroup.centralizer ({a} : Set G) := inf_le_right.trans hACg
    have hBel : IsElemAbelian p (E ⊓ A) := l119_isElemAbelian_of_le inf_le_right hAel
    have hBrk : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := hrA0
    have hKpi' : IsPiGroup p (barOf p K) := hKpi
    have hquasi : CFSG.Open.IsQuasisimple (barOf p K) := hKpi'.1
    have hO : GLAPPrimeCore p (barOf p K) = ⊥ := hKpi'.2.1
    have hPi : Prop1116.Pi19Ty p (barOf p K ⧸ Subgroup.center (barOf p K)) :=
      Prop1116.pi19Ty_of_isPiGroup hp hp2 hKpi'
    have hJ0 := Prop1116.no_bad hp hp2 h ha ha1 hKc hKM hnotD hPi h111 hI22 hI18 hI19 hNot27
      hOmDvd h115
    have hNorm : ∀ e ∈ E ⊓ A, e ≠ 1 → e ∈ Subgroup.normalizer (K : Set G) := by
      intro e he he1
      by_contra hn
      exact hJ0 ⟨⟨e, hBle he⟩, he, he1, Or.inl hn⟩
    have hBnorm : E ⊓ A ≤ Subgroup.normalizer (K : Set G) := by
      intro e he
      by_cases he1 : e = 1
      · rw [he1]; exact (Subgroup.normalizer (K : Set G)).one_mem
      · exact hNorm e he he1
    have hKe : ∀ e ∈ E ⊓ A, e ≠ 1 → Prop1116.Ke p K e ≤ M := by
      intro e he he1
      have hsub : IsSubnormal (K ⊓ Subgroup.centralizer ({e} : Set G)) (Cg2 e a) := by
        have h1 : IsSubnormal (K ⊓ Subgroup.centralizer ({e} : Set G))
            (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) :=
          isSubnormal_inf hKc.2.1 (Subgroup.centralizer ({e} : Set G))
        rw [← l119_cg2_eq a e] at h1
        exact h1
      have hO2 : GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({e} : Set G)) ≤ M := by
        refine (glaPPrimeCoreOf_le_of_isSubnormal hp hsub).trans ?_
        rcases h112 h ha ha1 he he1 with hM | ⟨A1, hA1, haA1⟩
        · exact hM
        · exact absurd ⟨A1, hA1, haA1⟩ hnotD
      refine sup_le hO2 (iSup_le fun J => iSup_le fun hJ => ?_)
      obtain ⟨hJc, hJpi⟩ := hJ
      have hJ2 : GLAPComponent p (Cg2 e a) J := l119_glaPComponent_of_isSubnormal hp hsub hJc
      have hJq : CFSG.Open.IsQuasisimple (barOf p J) := hJpi.1
      have hJPi : Prop1116.Pi19Ty p (barOf p J ⧸ Subgroup.center (barOf p J)) :=
        Prop1116.pi19Ty_of_isPiGroup hp hp2 hJpi
      have h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p J) :=
        hI19 (barOf p J) hJq p hp hp2 (Prop1116.pi19Ty_input hJPi)
      have h2 : p = 3 → IsLTwoTwentySeven (barOf p J) → ¬ IsCompLocallyOTwoBalanced p 1 A J := by
        intro hp3 hL27 _
        exact (hNot27 (barOf p J) hL27 (hp3 ▸ hJPi)).elim
      rcases h115 h ha ha1 he he1 hJ2 h1 h2 with hJM | ⟨A1, hA1, haA1⟩
      · exact hJM
      · exact absurd ⟨A1, hA1, haA1⟩ hnotD
    have hMsup : (⨆ (e : G) (_ : e ∈ E ⊓ A) (_ : e ≠ 1), Prop1116.Ke p K e) ≤ M :=
      iSup_le fun e => iSup_le fun he => iSup_le fun he1 => hKe e he he1
    have hcover : barX p (Cg a) K ≤ barX p (Cg a)
        (⨆ (e : G) (_ : e ∈ E ⊓ A) (_ : e ≠ 1), Prop1116.Ke p K e) → False := by
      intro hle
      apply hKM
      intro k hk
      obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (hle.trans (CFSG.LocalAnalysis.GLTheoremB.barX_mono p hMsup)) hk (hKc.1 hk)
      have hm := h11 hjk
      simpa using M.mul_mem hj hm
    rcases hKpi'.2.2 with ⟨k, ⟨f⟩⟩ | ⟨n, ε, hn, hO', hfp⟩ | ⟨hp3, ⟨f⟩⟩
    ·
      have hn2 : (k * p + 2) % p = 2 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      have hsch : Subgroup.center (barOf p K) = ⊥ :=
        hSchur (barOf p K) p hp hp2 hquasi hO (k * p + 2) hn2 ⟨f⟩
      have hAltTy : IsAltType (k * p + 2) (barOf p K) :=
        ⟨(l119_center_bot_quot hsch).symm.trans f⟩
      have hnd : ¬ p ∣ k * p + 2 := by
        intro hd
        have h2 : p ∣ 2 := (Nat.dvd_add_right (dvd_mul_left p k)).1 hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
      rcases hAlt G p hp hp2 (Cg a) K (E ⊓ A) hKc hBle hBnorm hBel hBrk (k * p + 2) hn2 hAltTy with
        hcov | hlt
      · exact hcover hcov
      · exact Prop1116.cex117_false h117
          { toSec11 := h, ha := ⟨ha, ha1⟩, hK := hKc,
            ht := Or.inl ⟨k * p + 2, hAltTy, hlt, hnd⟩, notM := hKM, notD := hnotD }
    ·
      exact hcover (hOm G p hp hp2 (Cg a) K (E ⊓ A) hKc hBle hBnorm hBel hBrk ⟨ε, n, hn, hO', hfp⟩)
    ·
      subst hp3
      exact hcover (AltFacts2.inputA7Gen_holds G (Cg a) K (E ⊓ A) hKc hBle hBnorm hBel hBrk ⟨f⟩)

theorem prop1117_of_inputs_noAlt (h112 : Prop112Statement) (h115 : Prop115Statement)
    (h117 : Prop117_cex_falseStatement) (hI19 : Input19_19) (hI22 : Input22_3_2)
    (hI18 : Input18_3_diag) (hNot27 : Prop1116.InputNotL27Pi) (hOmDvd : Prop1116.InputOmegaDvd)
    (hOm : Prop1116.InputOmegaGen) (hSchur : Prop1116.InputSchurAlt) :
    Prop1117Statement :=
  prop1117_of_inputs_fixed h112 h115 h117 hI19 hI22 hI18 hNot27 hOmDvd
    hOm hSchur

end AltFacts3

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
