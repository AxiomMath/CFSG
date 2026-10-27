module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.AGLEmbeddingD2.OuterBorel

open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

variable {U : Type*} [Group U]

theorem exists_mul_pow_of_mem_sup [Finite U] {R : Subgroup U} {t : U}
    (ht : t ∈ Subgroup.normalizer (R : Set U)) {n : U} (hn : n ∈ R ⊔ Subgroup.zpowers t) :
    ∃ r ∈ R, ∃ k : ℕ, n = r * t ^ k := by
  have hconj : ∀ (g : U), g ∈ Subgroup.normalizer (R : Set U) → ∀ r ∈ R, g * r * g⁻¹ ∈ R :=
    fun g hg r hr => (Subgroup.mem_normalizer_iff.mp hg r).mp hr
  have hinv : ∀ k : ℕ, (t ^ k)⁻¹ = t ^ ((orderOf t - 1) * k) := by
    intro k
    have hpos := orderOf_pos t
    rw [pow_mul, ← inv_pow]
    congr 1
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  let S : Subgroup U :=
    { carrier := {n | ∃ r ∈ R, ∃ k : ℕ, n = r * t ^ k}
      mul_mem' := by
        rintro _ _ ⟨r₁, hr₁, k₁, rfl⟩ ⟨r₂, hr₂, k₂, rfl⟩
        refine ⟨r₁ * (t ^ k₁ * r₂ * (t ^ k₁)⁻¹),
          R.mul_mem hr₁ (hconj _ (Subgroup.pow_mem _ ht k₁) r₂ hr₂), k₁ + k₂, ?_⟩
        rw [pow_add]
        group
      one_mem' := ⟨1, R.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨r, hr, k, rfl⟩
        refine ⟨(t ^ k)⁻¹ * r⁻¹ * ((t ^ k)⁻¹)⁻¹,
          hconj _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ ht k)) _ (R.inv_mem hr),
          (orderOf t - 1) * k, ?_⟩
        rw [← hinv k]
        group }
  have hRS : R ≤ S := fun r hr => ⟨r, hr, 0, by simp⟩
  have htS : Subgroup.zpowers t ≤ S := by
    rw [Subgroup.zpowers_le]
    exact ⟨1, R.one_mem, 1, by simp⟩
  exact (sup_le hRS htS) hn

theorem exists_pow_mul_pow [Finite U] {R : Subgroup U} {t : U}
    (ht : t ∈ Subgroup.normalizer (R : Set U)) {r : U} (hr : r ∈ R) (k : ℕ) :
    ∀ c : ℕ, ∃ r' ∈ R, (r * t ^ k) ^ c = r' * t ^ (k * c) := by
  intro c
  induction c with
  | zero => exact ⟨1, R.one_mem, by simp⟩
  | succ c ih =>
    obtain ⟨r', hr', h⟩ := ih
    have hmem : t ^ (k * c) * r * (t ^ (k * c))⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht (k * c)) r).mp hr
    refine ⟨r' * (t ^ (k * c) * r * (t ^ (k * c))⁻¹), R.mul_mem hr' hmem, ?_⟩
    rw [pow_succ, h, Nat.mul_succ, pow_add]
    group

theorem exists_conj_eq_mul [Finite U] {R : Subgroup U} {t : U}
    (ht : t ∈ Subgroup.normalizer (R : Set U)) (hCR : ∀ r ∈ R, t * r = r * t → r = 1)
    {r₁ : U} (hr₁ : r₁ ∈ R) : ∃ r ∈ R, r * t * r⁻¹ = r₁ * t := by
  have hmem : ∀ r ∈ R, r * t * r⁻¹ * t⁻¹ ∈ R := by
    intro r hr
    have h := (Subgroup.mem_normalizer_iff.mp ht r⁻¹).mp (R.inv_mem hr)
    have : r * t * r⁻¹ * t⁻¹ = r * (t * r⁻¹ * t⁻¹) := by group
    rw [this]
    exact R.mul_mem hr h
  let f : R → R := fun r => ⟨(r : U) * t * (r : U)⁻¹ * t⁻¹, hmem r r.2⟩
  have hf : Function.Injective f := by
    intro r s hrs
    have h : (r : U) * t * (r : U)⁻¹ * t⁻¹ = (s : U) * t * (s : U)⁻¹ * t⁻¹ :=
      congrArg Subtype.val hrs
    have h2 : t * ((s : U)⁻¹ * r) = ((s : U)⁻¹ * r) * t := by
      have h3 : (r : U) * t * (r : U)⁻¹ = (s : U) * t * (s : U)⁻¹ := by
        simpa using h
      calc t * ((s : U)⁻¹ * r) = (s : U)⁻¹ * ((s : U) * t * (s : U)⁻¹) * r := by group
        _ = (s : U)⁻¹ * ((r : U) * t * (r : U)⁻¹) * r := by rw [h3]
        _ = ((s : U)⁻¹ * r) * t := by group
    have h4 := hCR _ (R.mul_mem (R.inv_mem s.2) r.2) h2
    apply Subtype.ext
    calc (r : U) = s * ((s : U)⁻¹ * r) := by group
      _ = s := by rw [h4, mul_one]
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hf) ⟨r₁, hr₁⟩
  refine ⟨r, r.2, ?_⟩
  have h := congrArg Subtype.val hr
  change (r : U) * t * (r : U)⁻¹ * t⁻¹ = r₁ at h
  rw [← h]
  group

theorem exists_not_mem_inv_mul_mem {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQ : IsPGroup p Q) (K : Subgroup Q) [K.Normal] (hK : K ≠ ⊤) (β : Q ≃* Q)
    (hβK : K.map β.toMonoidHom = K) {e : ℕ} (hβe : β ^ (p ^ e) = 1) :
    ∃ q : Q, q ∉ K ∧ q⁻¹ * β q ∈ K := by
  classical
  let σ : MulAut (Q ⧸ K) := QuotientGroup.congr K K β hβK
  have hσ : ∀ (n : ℕ) (q : Q), (σ ^ n) (q : Q ⧸ K) = (((β ^ n) q : Q) : Q ⧸ K) := by
    intro n
    induction n with
    | zero => intro q; rfl
    | succ n ih =>
      intro q
      rw [pow_succ', MulAut.mul_apply, ih, pow_succ', MulAut.mul_apply]
      rfl
  have hσe : σ ^ (p ^ e) = 1 := by
    ext x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hσ, hβe]
    rfl
  let G : Subgroup (MulAut (Q ⧸ K)) := Subgroup.zpowers σ
  have hG : IsPGroup p G := by
    rw [IsPGroup.iff_card]
    have hdvd : Nat.card G ∣ p ^ e := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hσe
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
    exact ⟨k, hk⟩
  have hcard : p ∣ Nat.card (Q ⧸ K) := by
    obtain ⟨k, hk⟩ := (hQ.to_quotient K).exists_card_eq
    rcases k with _ | k
    · exfalso
      apply hK
      rw [pow_zero] at hk
      exact Subgroup.index_eq_one.mp hk
    · rw [hk]
      exact dvd_pow_self p (Nat.succ_ne_zero k)
  have hfix : (1 : Q ⧸ K) ∈ MulAction.fixedPoints G (Q ⧸ K) := by
    intro g
    show (g : MulAut (Q ⧸ K)) (1 : Q ⧸ K) = 1
    exact map_one (g : MulAut (Q ⧸ K))
  obtain ⟨x, hx, hx1⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Q ⧸ K) hcard hfix
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨q, fun hq => hx1 ?_, ?_⟩
  · exact ((QuotientGroup.eq_one_iff q).mpr hq).symm
  · have h1 : σ (q : Q ⧸ K) = (q : Q ⧸ K) := hx (⟨σ, Subgroup.mem_zpowers σ⟩ : G)
    have h2 : σ (q : Q ⧸ K) = ((β q : Q) : Q ⧸ K) := rfl
    rw [h2, QuotientGroup.eq] at h1
    have := K.inv_mem h1
    simpa using this

theorem eq_of_fix_of_irreducible [Finite U] {p : ℕ} [Fact p.Prime] {R Z : Subgroup U} {t : U}
    (hRp : IsPGroup p R) (hZ : Z = ⁅R, R⁆) (hZc : Z ≤ Subgroup.centralizer (R : Set U))
    (hcard : Nat.card Z * Nat.card Z < Nat.card R)
    (ht : t ∈ Subgroup.normalizer (R : Set U))
    (hirr : ∀ Y : Subgroup U, Z ≤ Y → Y ≤ R → t ∈ Subgroup.normalizer (Y : Set U) →
      Y = Z ∨ Y = R)
    (α : MulAut U) (hαR : ∀ r ∈ R, α r ∈ R) (hαt : α t = t) {e : ℕ} (hαe : α ^ (p ^ e) = 1) :
    ∀ r ∈ R, α r = r := by
  classical
  have hZR : Z ≤ R := by
    rw [hZ, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
  have hcomm : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z := fun z hz r hr =>
    ((Subgroup.mem_centralizer_iff.mp (hZc hz)) r hr).symm
  have hmapR : R.map α.toMonoidHom = R := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact hαR r hr
    · rw [Subgroup.card_map_of_injective α.injective]
  have hmapZ : Z.map α.toMonoidHom = Z := by
    rw [hZ, Subgroup.map_commutator, hmapR]
  have hαZ : ∀ z ∈ Z, α z ∈ Z := fun z hz => hmapZ ▸ ⟨z, hz, rfl⟩
  have hmapRt : R.map (MulAut.conj t).toMonoidHom = R := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp ht r).mp hr
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hmapZt : Z.map (MulAut.conj t).toMonoidHom = Z := by
    rw [hZ, Subgroup.map_commutator, hmapRt]
  have htZ : ∀ h : U, h ∈ Z ↔ t * h * t⁻¹ ∈ Z := by
    intro h
    constructor
    · intro hh
      exact hmapZt ▸ ⟨h, hh, rfl⟩
    · intro hh
      rw [← hmapZt] at hh
      obtain ⟨z, hz, hzh⟩ := hh
      have : z = h := by
        have h' : t * z * t⁻¹ = t * h * t⁻¹ := hzh
        simpa using h'
      exact this ▸ hz
  let C : Subgroup U :=
    { carrier := {r | r ∈ R ∧ r⁻¹ * α r ∈ Z}
      mul_mem' := by
        rintro r s ⟨hr, hrZ⟩ ⟨hs, hsZ⟩
        refine ⟨R.mul_mem hr hs, ?_⟩
        have hc := hcomm _ hrZ _ (R.inv_mem hs)
        have : (r * s)⁻¹ * α (r * s) = (r⁻¹ * α r) * (s⁻¹ * α s) := by
          calc (r * s)⁻¹ * α (r * s) = s⁻¹ * (r⁻¹ * α r) * α s := by rw [map_mul]; group
            _ = (r⁻¹ * α r) * s⁻¹ * α s := by rw [← hc]
            _ = (r⁻¹ * α r) * (s⁻¹ * α s) := by group
        rw [this]
        exact Z.mul_mem hrZ hsZ
      one_mem' := ⟨R.one_mem, by simp⟩
      inv_mem' := by
        rintro r ⟨hr, hrZ⟩
        refine ⟨R.inv_mem hr, ?_⟩
        have hcz : Commute (r⁻¹ * α r) r := hcomm _ hrZ _ hr
        have : r⁻¹⁻¹ * α r⁻¹ = (r⁻¹ * α r)⁻¹ := by
          calc r⁻¹⁻¹ * α r⁻¹ = r * (r⁻¹ * α r)⁻¹ * r⁻¹ := by rw [map_inv]; group
            _ = (r⁻¹ * α r)⁻¹ * r * r⁻¹ := by rw [← hcz.inv_left.eq]
            _ = (r⁻¹ * α r)⁻¹ := by group
        rw [this]
        exact Z.inv_mem hrZ }
  have hZC : Z ≤ C := fun z hz => ⟨hZR hz, Z.mul_mem (Z.inv_mem hz) (hαZ z hz)⟩
  have hCR : C ≤ R := fun r hr => hr.1
  have htC : t ∈ Subgroup.normalizer (C : Set U) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have key : (t * h * t⁻¹)⁻¹ * α (t * h * t⁻¹) = t * (h⁻¹ * α h) * t⁻¹ := by
      rw [map_mul, map_mul, map_inv, hαt]
      group
    constructor
    · rintro ⟨hh, hhZ⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp ht h).mp hh, key ▸ (htZ _).mp hhZ⟩
    · rintro ⟨hh, hhZ⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp ht h).mpr hh, (htZ _).mpr (key ▸ hhZ)⟩
  have hCeq : C = R := by
    rcases hirr C hZC hCR htC with h | h
    · exfalso
      let K : Subgroup R := Z.subgroupOf R
      have hKn : K.Normal := by
        constructor
        intro n hn g
        have hn' : (n : U) ∈ Z := hn
        show ((g * n * g⁻¹ : R) : U) ∈ Z
        have : (g : U) * n * (g : U)⁻¹ = n := by
          rw [← hcomm _ hn' _ g.2]
          group
        simpa [this] using hn'
      have hKtop : K ≠ ⊤ := by
        intro hK
        have hRZ : R ≤ Z := fun r hr => by
          have : (⟨r, hr⟩ : R) ∈ K := hK ▸ Subgroup.mem_top _
          exact this
        have h1 := Subgroup.card_le_of_le hRZ
        have h2 : 1 ≤ Nat.card Z := Nat.card_pos
        nlinarith
      let β : R ≃* R := (α.subgroupMap R).trans (MulEquiv.subgroupCongr hmapR)
      have hβ : ∀ r : R, (β r : U) = α r := fun r => rfl
      have hβK : K.map β.toMonoidHom = K := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          show ((β y : R) : U) ∈ Z
          rw [hβ]
          exact hαZ _ hy
        · intro hx
          have hx' : (x : U) ∈ Z.map α.toMonoidHom := hmapZ.symm ▸ hx
          obtain ⟨z, hz, hzx⟩ := hx'
          refine ⟨⟨z, hZR hz⟩, hz, ?_⟩
          apply Subtype.ext
          exact hzx
      have hβe : β ^ (p ^ e) = 1 := by
        have hpow : ∀ (n : ℕ) (r : R), ((β ^ n) r : U) = (α ^ n) r := by
          intro n
          induction n with
          | zero => intro r; rfl
          | succ n ih =>
            intro r
            rw [pow_succ', MulAut.mul_apply, hβ, ih, pow_succ', MulAut.mul_apply]
        ext r
        rw [hpow, hαe]
        rfl
      have := hKn
      obtain ⟨q, hqK, hq⟩ := exists_not_mem_inv_mul_mem hRp K hKtop β hβK hβe
      have hqC : (q : U) ∈ C := ⟨q.2, by
        have : ((q⁻¹ * β q : R) : U) ∈ Z := hq
        simpa [hβ] using this⟩
      rw [h] at hqC
      exact hqK hqC
    · exact h
  have hf : ∀ r ∈ R, r⁻¹ * α r ∈ Z := fun r hr => ((hCeq.symm ▸ hr : r ∈ C)).2
  have hfmul : ∀ r ∈ R, ∀ s ∈ R, (r * s)⁻¹ * α (r * s) = (r⁻¹ * α r) * (s⁻¹ * α s) := by
    intro r hr s hs
    have hc := hcomm _ (hf r hr) _ (R.inv_mem hs)
    calc (r * s)⁻¹ * α (r * s) = s⁻¹ * (r⁻¹ * α r) * α s := by rw [map_mul]; group
      _ = (r⁻¹ * α r) * s⁻¹ * α s := by rw [← hc]
      _ = (r⁻¹ * α r) * (s⁻¹ * α s) := by group
  have hfinv : ∀ r ∈ R, r⁻¹⁻¹ * α r⁻¹ = (r⁻¹ * α r)⁻¹ := by
    intro r hr
    have h := hfmul r hr r⁻¹ (R.inv_mem hr)
    rw [mul_inv_cancel, map_one, inv_one, one_mul] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  let K : Subgroup U :=
    { carrier := {r | r ∈ R ∧ α r = r}
      mul_mem' := by
        rintro r s ⟨hr, hαr⟩ ⟨hs, hαs⟩
        exact ⟨R.mul_mem hr hs, by rw [map_mul, hαr, hαs]⟩
      one_mem' := ⟨R.one_mem, map_one α⟩
      inv_mem' := by
        rintro r ⟨hr, hαr⟩
        exact ⟨R.inv_mem hr, by rw [map_inv, hαr]⟩ }
  have hmemK : ∀ r ∈ R, r⁻¹ * α r = 1 → r ∈ K := fun r hr h1 =>
    ⟨hr, by
      have := congrArg (fun x => r * x) h1
      simpa using this⟩
  have hZK : Z ≤ K := by
    rw [hZ, Subgroup.commutator_le]
    intro r hr s hs
    have hmem : ⁅r, s⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hr hs) (R.inv_mem hr)) (R.inv_mem hs)
    refine hmemK _ hmem ?_
    rw [commutatorElement_def, hfmul _ (R.mul_mem (R.mul_mem hr hs) (R.inv_mem hr)) _
      (R.inv_mem hs), hfmul _ (R.mul_mem hr hs) _ (R.inv_mem hr), hfmul _ hr _ hs,
      hfinv _ hr, hfinv _ hs]
    have hc : (r⁻¹ * α r) * (s⁻¹ * α s) = (s⁻¹ * α s) * (r⁻¹ * α r) :=
      hcomm _ (hf r hr) _ (hZR (hf s hs))
    calc (r⁻¹ * α r) * (s⁻¹ * α s) * (r⁻¹ * α r)⁻¹ * (s⁻¹ * α s)⁻¹
        = (s⁻¹ * α s) * (r⁻¹ * α r) * (r⁻¹ * α r)⁻¹ * (s⁻¹ * α s)⁻¹ := by rw [hc]
      _ = 1 := by group
  have hKR : K ≤ R := fun r hr => hr.1
  have htK : t ∈ Subgroup.normalizer (K : Set U) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have key : α (t * h * t⁻¹) = t * α h * t⁻¹ := by
      rw [map_mul, map_mul, map_inv, hαt]
    constructor
    · rintro ⟨hh, hαh⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp ht h).mp hh, by rw [key, hαh]⟩
    · rintro ⟨hh, hαh⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp ht h).mpr hh, ?_⟩
      rw [key] at hαh
      simpa using hαh
  rcases hirr K hZK hKR htK with hKZ | hKR'
  · exfalso
    let g : R → Z := fun r => ⟨(r : U)⁻¹ * α r, hf r r.2⟩
    have hg : ∀ r s : R, g r = g s → (r : U) * (s : U)⁻¹ ∈ Z := by
      intro r s hrs
      have h1 : (r : U)⁻¹ * α r = (s : U)⁻¹ * α s := congrArg Subtype.val hrs
      have hrs' : (r : U) * (s : U)⁻¹ ∈ R := R.mul_mem r.2 (R.inv_mem s.2)
      rw [← hKZ]
      refine hmemK _ hrs' ?_
      rw [hfmul _ r.2 _ (R.inv_mem s.2), hfinv _ s.2, h1]
      group
    have : Nonempty R := ⟨1⟩
    let sel : Z → R := Function.invFun g
    have hsel : ∀ r : R, g (sel (g r)) = g r := fun r => Function.invFun_eq ⟨r, rfl⟩
    let φ : R → Z × Z := fun r =>
      (g r, ⟨(r : U) * ((sel (g r) : R) : U)⁻¹, hg r (sel (g r)) (hsel r).symm⟩)
    have hφ : Function.Injective φ := by
      intro r s hrs
      have h1 : g r = g s := congrArg Prod.fst hrs
      have h2 : (r : U) * ((sel (g r) : R) : U)⁻¹ = (s : U) * ((sel (g s) : R) : U)⁻¹ :=
        congrArg (fun x => (x.2 : U)) hrs
      rw [h1] at h2
      apply Subtype.ext
      simpa using h2
    have h := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_prod] at h
    omega
  · intro r hr
    exact ((hKR'.symm ▸ hr : r ∈ K)).2

theorem modEq_one_of_pow_prime_pow {m k p e : ℕ} (hm : 0 < m) (hp0 : p ≠ 0)
    (hp : Nat.Coprime p (Nat.totient m)) (hk : k ^ (p ^ e) ≡ 1 [MOD m]) : k ≡ 1 [MOD m] := by
  have : NeZero m := ⟨hm.ne'⟩
  have h1 : (k : ZMod m) ^ (p ^ e) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ m).mpr hk
    push_cast at this
    exact this
  have hu : IsUnit (k : ZMod m) := IsUnit.of_pow_eq_one h1 (pow_ne_zero _ hp0)
  have hu1 : hu.unit ^ (p ^ e) = 1 := by
    ext
    simp [h1]
  have hu2 : hu.unit ^ (Nat.totient m) = 1 := ZMod.pow_totient _
  have hord : orderOf hu.unit ∣ Nat.gcd (p ^ e) (Nat.totient m) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu1) (orderOf_dvd_of_pow_eq_one hu2)
  rw [Nat.Coprime.pow_left e hp, Nat.dvd_one, orderOf_eq_one_iff] at hord
  have hk1 : (k : ZMod m) = 1 := by
    have := congrArg Units.val hord
    simpa using this
  exact (ZMod.natCast_eq_natCast_iff _ _ m).mp (by simpa using hk1)

theorem not_dvd_card_outer_of_borel [Finite U] {p : ℕ} [hp : Fact p.Prime]
    (hZU : Subgroup.center U = ⊥) (R : Sylow p U) (Z : Subgroup U)
    (hZ : Z = ⁅(R : Subgroup U), (R : Subgroup U)⁆)
    (hZc : Z ≤ Subgroup.centralizer ((R : Subgroup U) : Set U))
    (hcard : Nat.card Z * Nat.card Z < Nat.card (R : Subgroup U)) (t : U)
    (hN : Subgroup.normalizer ((R : Subgroup U) : Set U) = (R : Subgroup U) ⊔ Subgroup.zpowers t)
    (hpt : Nat.Coprime p (orderOf t)) (hφ : Nat.Coprime p (Nat.totient (orderOf t)))
    (hCR : ∀ r ∈ (R : Subgroup U), t * r = r * t → r = 1)
    (hirr : ∀ Y : Subgroup U, Z ≤ Y → Y ≤ R → t ∈ Subgroup.normalizer (Y : Set U) →
      Y = Z ∨ Y = R)
    (w : U) (hgen : Subgroup.closure
      (insert w (Subgroup.normalizer ((R : Subgroup U) : Set U) : Set U)) = ⊤)
    (hwt : w * t * w⁻¹ ∈ Subgroup.normalizer ((R : Subgroup U) : Set U))
    (hCt : Subgroup.centralizer ({t} : Set U) ≤ Subgroup.zpowers t) :
    ¬ p ∣ Nat.card (Outer U) := by
  classical
  intro hdvd
  set N := Subgroup.normalizer ((R : Subgroup U) : Set U) with hNdef
  have htN : t ∈ N := hN ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  let ι : U →* MulAut U := MulAut.conj
  have hι : Function.Injective ι := by
    intro a b hab
    have hc : b⁻¹ * a ∈ Subgroup.center U := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut U => φ g) hab
      simp only [ι, MulAut.conj_apply] at h
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * b * b⁻¹ * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * b * b⁻¹ * a := by rw [h]
        _ = b⁻¹ * a * g := by group
    rw [hZU, Subgroup.mem_bot] at hc
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [hc, mul_one]
  have hιapp : ∀ g x : U, ι g x = g * x * g⁻¹ := fun g x => MulAut.conj_apply g x
  have hconjι : ∀ (σ : MulAut U) (g : U), σ * ι g * σ⁻¹ = ι (σ g) := by
    intro σ g
    ext x
    simp only [MulAut.mul_apply, hιapp, map_mul, map_inv, MulAut.apply_inv_self]
  set PI := (R : Subgroup U).map ι with hPIdef
  have hPIp : IsPGroup p PI := R.isPGroup'.map ι
  obtain ⟨S, hS⟩ := hPIp.exists_le_sylow
  have hcardPI : Nat.card PI = Nat.card (R : Subgroup U) :=
    Subgroup.card_map_of_injective hι
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner U with hIdef
  have hIrange : I = ι.range := rfl
  have hcardI : Nat.card I = Nat.card U := by
    rw [hIrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have hcardAut : Nat.card (MulAut U) = Nat.card U * Nat.card (Outer U) := by
    rw [mul_comm, ← hcardI]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup I
  have hU0 : Nat.card U ≠ 0 := Nat.card_pos.ne'
  have hO0 : Nat.card (Outer U) ≠ 0 := Nat.card_pos.ne'
  have hlt : PI < S := by
    refine lt_of_le_of_ne hS (fun heq => ?_)
    have h1 : Nat.card (S : Subgroup (MulAut U)) =
        p ^ (Nat.card (MulAut U)).factorization p := S.card_eq_multiplicity
    have h2 : Nat.card (R : Subgroup U) = p ^ (Nat.card U).factorization p :=
      R.card_eq_multiplicity
    have h3 : (Nat.card (MulAut U)).factorization p =
        (Nat.card U).factorization p + (Nat.card (Outer U)).factorization p := by
      rw [hcardAut, Nat.factorization_mul hU0 hO0]
      rfl
    have h4 : 1 ≤ (Nat.card (Outer U)).factorization p :=
      (hp.out.dvd_iff_one_le_factorization hO0).mp hdvd
    have h5 : Nat.card (S : Subgroup (MulAut U)) = Nat.card (R : Subgroup U) := by
      rw [← heq, hcardPI]
    rw [h1, h2, h3] at h5
    have h6 := Nat.pow_right_injective hp.out.two_le h5
    omega
  have hSp : IsPGroup p (S : Subgroup (MulAut U)) := S.isPGroup'
  have : Group.IsNilpotent (S : Subgroup (MulAut U)) := hSp.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := (S : Subgroup (MulAut U)))
  have hHlt : PI.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hle : (S : Subgroup (MulAut U)) ≤ PI := by
      intro x hx
      have : (⟨x, hx⟩ : (S : Subgroup (MulAut U))) ∈ PI.subgroupOf S :=
        htop ▸ Subgroup.mem_top _
      exact this
    exact (not_le_of_gt hlt) hle
  obtain ⟨x, hxN, hxH⟩ := IsConcreteLE.exists_of_lt (hnc _ hHlt)
  set β : MulAut U := (x : MulAut U) with hβdef
  have hβS : β ∈ (S : Subgroup (MulAut U)) := x.2
  have hβPI : β ∉ PI := hxH
  have hβR : ∀ r ∈ (R : Subgroup U), β r ∈ (R : Subgroup U) := by
    intro r hr
    let h : (S : Subgroup (MulAut U)) := ⟨ι r, hS (Subgroup.mem_map_of_mem ι hr)⟩
    have hh : h ∈ PI.subgroupOf S := Subgroup.mem_map_of_mem ι hr
    have hxh := (Subgroup.mem_normalizer_iff.mp hxN h).mp hh
    have hmem : β * ι r * β⁻¹ ∈ PI := hxh
    rw [hconjι] at hmem
    obtain ⟨r', hr', hr'e⟩ := hmem
    rw [← hι hr'e]
    exact hr'
  have hmapR : (R : Subgroup U).map β.toMonoidHom = R := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact hβR r hr
    · rw [Subgroup.card_map_of_injective β.injective]
  have hβR' : ∀ r ∈ (R : Subgroup U), β⁻¹ r ∈ (R : Subgroup U) := by
    intro r hr
    rw [← hmapR] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    have h : β⁻¹ (β.toMonoidHom r₀) = r₀ := MulAut.inv_apply_self U β r₀
    rw [h]
    exact hr₀
  have hβI : β ∉ I := by
    rintro ⟨u, hu⟩
    have hP' : IsPGroup p ((S : Subgroup (MulAut U)).comap ι) := hSp.comap_of_injective ι hι
    have hRP' : (R : Subgroup U) ≤ (S : Subgroup (MulAut U)).comap ι := fun r hr =>
      hS (Subgroup.mem_map_of_mem ι hr)
    have heq := R.is_maximal' hP' hRP'
    have hu' : u ∈ (S : Subgroup (MulAut U)).comap ι := by
      show ι u ∈ (S : Subgroup (MulAut U))
      rw [hu]
      exact hβS
    rw [heq] at hu'
    exact hβPI (hu ▸ Subgroup.mem_map_of_mem ι hu')
  obtain ⟨e, he⟩ := hSp ⟨β, hβS⟩
  have hβe : β ^ (p ^ e) = 1 := congrArg Subtype.val he
  have hβN : ∀ n ∈ N, β n ∈ N := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have key : β n * h * (β n)⁻¹ = β (n * β⁻¹ h * n⁻¹) := by
      simp [map_mul, map_inv]
    constructor
    · intro hh
      rw [key]
      exact hβR _ ((Subgroup.mem_normalizer_iff.mp hn _).mp (hβR' h hh))
    · intro hh
      rw [key] at hh
      have h1 := hβR' _ hh
      rw [MulAut.inv_apply_self] at h1
      have h2 := (Subgroup.mem_normalizer_iff.mp hn _).mpr h1
      have h3 := hβR _ h2
      simpa using h3
  obtain ⟨r₁, hr₁, k, hk⟩ := exists_mul_pow_of_mem_sup htN (hN ▸ hβN t htN)
  have hcop : ∀ r ∈ (R : Subgroup U), r ∈ Subgroup.zpowers t → r = 1 := by
    intro r hr hrt
    obtain ⟨j, hj⟩ := R.isPGroup' ⟨r, hr⟩
    have h1 : orderOf r ∣ p ^ j := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hj)
    have h2 : orderOf r ∣ orderOf t := orderOf_dvd_of_mem_zpowers hrt
    have h3 : Nat.Coprime (p ^ j) (orderOf t) := hpt.pow_left j
    have h4 : orderOf r ∣ 1 := by
      rw [← h3.gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hβpow : ∀ j : ℕ, ∃ r ∈ (R : Subgroup U), (β ^ j) t = r * t ^ (k ^ j) := by
    intro j
    induction j with
    | zero => exact ⟨1, (R : Subgroup U).one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨r, hr, hrj⟩ := ih
      obtain ⟨r', hr', hr'e⟩ := exists_pow_mul_pow htN hr₁ k (k ^ j)
      refine ⟨β r * r', (R : Subgroup U).mul_mem (hβR r hr) hr', ?_⟩
      rw [pow_succ', MulAut.mul_apply, hrj, map_mul, map_pow, hk, hr'e, pow_succ' k j,
        mul_assoc]
  obtain ⟨r₂, hr₂, hr₂e⟩ := hβpow (p ^ e)
  rw [hβe] at hr₂e
  have hr₂1 : r₂ = 1 := by
    refine hcop r₂ hr₂ ?_
    have : r₂ = t * (t ^ (k ^ (p ^ e)))⁻¹ := by
      rw [show (1 : MulAut U) t = t from rfl] at hr₂e
      calc r₂ = r₂ * t ^ (k ^ (p ^ e)) * (t ^ (k ^ (p ^ e)))⁻¹ := by group
        _ = t * (t ^ (k ^ (p ^ e)))⁻¹ := by rw [← hr₂e]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers t)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers t) _))
  rw [hr₂1, one_mul] at hr₂e
  have hkmod : k ^ (p ^ e) ≡ 1 [MOD orderOf t] := by
    have h := (pow_eq_pow_iff_modEq (x := t) (n := 1) (m := k ^ (p ^ e))).mp
      (by rw [pow_one]; exact hr₂e)
    exact h.symm
  have hk1 : k ≡ 1 [MOD orderOf t] :=
    modEq_one_of_pow_prime_pow (orderOf_pos t) hp.out.ne_zero hφ hkmod
  have hβt : β t = r₁ * t := by
    rw [hk, (pow_eq_pow_iff_modEq (x := t) (n := k) (m := 1)).mpr hk1, pow_one]
  obtain ⟨r, hr, hre⟩ := exists_conj_eq_mul htN hCR hr₁
  set β' : MulAut U := (ι r)⁻¹ * β with hβ'def
  have hβ'app : ∀ x : U, β' x = r⁻¹ * β x * r := by
    intro x
    rw [hβ'def, MulAut.mul_apply, ← map_inv, hιapp, inv_inv]
  have hβ't : β' t = t := by
    rw [hβ'app, hβt, ← hre]
    group
  have hβ'R : ∀ x ∈ (R : Subgroup U), β' x ∈ (R : Subgroup U) := by
    intro x hx
    rw [hβ'app]
    exact (R : Subgroup U).mul_mem ((R : Subgroup U).mul_mem ((R : Subgroup U).inv_mem hr)
      (hβR x hx)) hr
  have hβ'S : β' ∈ (S : Subgroup (MulAut U)) :=
    (S : Subgroup (MulAut U)).mul_mem ((S : Subgroup (MulAut U)).inv_mem
      (hS (Subgroup.mem_map_of_mem ι hr))) hβS
  obtain ⟨e', he'⟩ := hSp ⟨β', hβ'S⟩
  have hβ'e : β' ^ (p ^ e') = 1 := congrArg Subtype.val he'
  have hfixR := eq_of_fix_of_irreducible R.isPGroup' hZ hZc hcard htN hirr β' hβ'R hβ't hβ'e
  have hfixN : ∀ n ∈ N, β' n = n := by
    intro n hn
    obtain ⟨r'', hr'', c, rfl⟩ := exists_mul_pow_of_mem_sup htN (hN ▸ hn)
    rw [map_mul, map_pow, hfixR r'' hr'', hβ't]
  set c := w⁻¹ * β' w with hcdef
  have hβ'w : β' w = w * c := by rw [hcdef]; group
  have hct : c ∈ Subgroup.centralizer ({t} : Set U) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have h1 := hfixN _ hwt
    rw [map_mul, map_mul, map_inv, hβ't, hβ'w] at h1
    have h2 : c * g * c⁻¹ = g := by
      calc c * g * c⁻¹ = w⁻¹ * (w * c * g * (w * c)⁻¹) * w := by group
        _ = w⁻¹ * (w * g * w⁻¹) * w := by rw [h1]
        _ = g := by group
    calc g * c = c * g * c⁻¹ * c := by rw [h2]
      _ = c * g := by group
  have hcN : c ∈ N := (Subgroup.zpowers_le.mpr htN) (hCt hct)
  have hβ'c : β' c = c := hfixN c hcN
  have hiter : ∀ j : ℕ, (β' ^ j) w = w * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hβ'c, hβ'w, pow_succ', mul_assoc]
  have hc1 : c = 1 := by
    have h := hiter (p ^ e')
    rw [hβ'e] at h
    have hcp : c ^ (p ^ e') = 1 := by
      have : w = w * c ^ (p ^ e') := h
      simpa using this.symm
    have h1 : orderOf c ∣ p ^ e' := orderOf_dvd_of_pow_eq_one hcp
    have h2 : orderOf c ∣ orderOf t := orderOf_dvd_of_mem_zpowers (hCt hct)
    have h4 : orderOf c ∣ 1 := by
      rw [← (hpt.pow_left e').gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hfixw : β' w = w := by rw [hβ'w, hc1, mul_one]
  have hβ'1 : β' = 1 := by
    have hle : Subgroup.closure (insert w (N : Set U)) ≤
        MonoidHom.eqLocus β'.toMonoidHom (MonoidHom.id U) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · exact hfixw
      · exact hfixN x hx
    rw [hgen] at hle
    ext x
    exact hle (Subgroup.mem_top x)
  apply hβPI
  have : β = ι r := by
    calc β = ι r * ((ι r)⁻¹ * β) := by group
      _ = ι r * β' := by rw [hβ'def]
      _ = ι r := by rw [hβ'1, mul_one]
  rw [this]
  exact Subgroup.mem_map_of_mem ι hr

end CFSG.AGLEmbeddingD2.OuterBorel
