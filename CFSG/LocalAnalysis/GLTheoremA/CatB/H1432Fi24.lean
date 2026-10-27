module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Facts2
public import CFSG.LocalAnalysis.SectionRank.QTK.SectionLiftB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MatOpsChecks
public import CFSG.Sporadic.Bridge.Catalogue
public import Certificates.Certificate9602

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.WitFi24

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.CoverCore CFSG.AGLEmbedding.R3
open scoped commutatorElement

section Log

variable {K : Type} [Group K] {p : ℕ}

theorem exists_additive_ne_zero_of_module {A : Type} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
    [Module (ZMod p) A] {c : A} (hc : c ≠ 0) :
    ∃ f : A → ZMod p, (∀ a b, f (a + b) = f a + f b) ∧ f c ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod p) A, φ c ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hc
    rw [← Module.eval_apply_eq_zero_iff (ZMod p) c]
    ext φ
    exact hall φ
  exact ⟨fun x => φ x, fun a b => map_add φ a b, hφ⟩

theorem exists_additive_ne_zero {C : Type} [CommGroup C] {p : ℕ} [Fact p.Prime]
    (hC : ∀ x : C, x ^ p = 1) {c : C} (hc : c ≠ 1) :
    ∃ f : C → ZMod p, (∀ a b, f (a * b) = f a + f b) ∧ f c ≠ 0 := by
  have hmod : ∀ x : Additive C, p • x = 0 := fun x => by
    show Additive.ofMul (Additive.toMul x ^ p) = Additive.ofMul 1
    rw [hC]
  obtain ⟨f, hf, hfc⟩ := @exists_additive_ne_zero_of_module (Additive C) _ p _
    (AddCommGroup.zmodModule hmod) (Additive.ofMul c) hc
  exact ⟨fun x => f (Additive.ofMul x), fun a b => hf _ _, hfc⟩

open scoped IsMulCommutative in
theorem exists_log_omega_ne (hp : p.Prime) {c : K} (hc : c ∈ Subgroup.center K) (hcp : c ^ p = 1)
    (hc1 : c ≠ 1) :
    ∃ f : K → ZMod p, (∀ z w, z ∈ Subgroup.center K → z ^ p = 1 → w ∈ Subgroup.center K →
      w ^ p = 1 → f (z * w) = f z + f w) ∧ f c ≠ 0 := by
  haveI := Fact.mk hp
  obtain ⟨χ, hχ, hχc⟩ := exists_additive_ne_zero (C := ((powMonoidHom p).ker :
    Subgroup (Subgroup.center K))) (p := p)
    (fun x => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact x.2))
    (c := ⟨⟨c, hc⟩, Subtype.ext hcp⟩) (fun h => hc1 (by
      have := congrArg (fun x : ((powMonoidHom p).ker : Subgroup (Subgroup.center K)) =>
        ((x : Subgroup.center K) : K)) h
      exact this))
  classical
  refine ⟨fun z => if h : z ∈ Subgroup.center K ∧ z ^ p = 1 then
    χ ⟨⟨z, h.1⟩, Subtype.ext h.2⟩ else 0, ?_, ?_⟩
  · intro z w hz hz' hw hw'
    have hzw : z * w ∈ Subgroup.center K ∧ (z * w) ^ p = 1 :=
      ⟨mul_mem hz hw, by
        rw [(show Commute z w from Subgroup.mem_center_iff.mp hz w |>.symm).mul_pow, hz', hw',
          one_mul]⟩
    simp only [dite_eq_left hzw, dite_eq_left (And.intro hz hz'), dite_eq_left (And.intro hw hw')]
    rw [← hχ]
    rfl
  · simp only [dite_eq_left (And.intro hc hcp)]
    exact hχc

end Log

section Form

variable {K X : Type} [Group K] [Group X] {p : ℕ} (D : ModuleSpec X p) (π : K →* X)

theorem exists_commForm_of_log (hp : p.Prime) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (f : K → ZMod p)
    (hfmul : ∀ z w, z ∈ Subgroup.center K → z ^ p = 1 → w ∈ Subgroup.center K →
      w ^ p = 1 → f (z * w) = f z + f w) :
    ∃ B : Matrix (Fin D.n) (Fin D.n) (ZMod p),
      B.transpose = -B ∧ (∀ j, (D.M j).transpose * B * D.M j = B) ∧
      ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, ∀ c d, π x = D.elt c → π y = D.elt d →
        f ⁅x, y⁆ = ∑ i, c i * ∑ k, d k * B i k := by
  have := Fact.mk hp
  have hf1 : f 1 = 0 := by
    have h0 := hfmul 1 1 (one_mem _) (one_pow p) (one_mem _) (one_pow p)
    rwa [mul_one, left_eq_add] at h0
  have hfinv : ∀ {u v : X}, u ∈ D.span → v ∈ D.span →
      f (coverComm π hπ u v)⁻¹ = -f (coverComm π hπ u v) := by
    intro u v hu hv
    have h1 := D.coverComm_mem_center π hπ hker hu hv
    have h2 := D.coverComm_pow π hπ hker hu hv
    have h := hfmul _ _ (inv_mem h1) (by rw [inv_pow, h2, inv_one]) h1 h2
    rw [inv_mul_cancel, hf1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  let b : (Fin D.n → ZMod p) → (Fin D.n → ZMod p) → ZMod p :=
    fun c d => f (coverComm π hπ (D.elt c) (D.elt d))
  have hb1 : ∀ c c' d, b (c + c') d = b c d + b c' d := fun c c' d => by
    simp only [b, D.elt_add, D.coverComm_mul_left π hπ hker (D.elt_mem c') (D.elt_mem d)]
    exact hfmul _ _ (D.coverComm_mem_center π hπ hker (D.elt_mem c) (D.elt_mem d))
      (D.coverComm_pow π hπ hker (D.elt_mem c) (D.elt_mem d))
      (D.coverComm_mem_center π hπ hker (D.elt_mem c') (D.elt_mem d))
      (D.coverComm_pow π hπ hker (D.elt_mem c') (D.elt_mem d))
  have hb2 : ∀ c d d', b c (d + d') = b c d + b c d' := fun c d d' => by
    simp only [b, D.elt_add, D.coverComm_mul_right π hπ hker (D.elt_mem c) (D.elt_mem d)
      (D.elt_mem d')]
    exact hfmul _ _ (D.coverComm_mem_center π hπ hker (D.elt_mem c) (D.elt_mem d))
      (D.coverComm_pow π hπ hker (D.elt_mem c) (D.elt_mem d))
      (D.coverComm_mem_center π hπ hker (D.elt_mem c) (D.elt_mem d'))
      (D.coverComm_pow π hπ hker (D.elt_mem c) (D.elt_mem d'))
  let B : Matrix (Fin D.n) (Fin D.n) (ZMod p) :=
    Matrix.of fun i k => b (Pi.single i 1) (Pi.single k 1)
  have hexp : ∀ c d, b c d = ∑ i, c i * ∑ k, d k * B i k := fun c d => by
    rw [eq_sum_of_map_add (F := fun c => b c d) (fun c c' => hb1 c c' d) c]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eq_sum_of_map_add (F := b (Pi.single i 1)) (hb2 (Pi.single i 1)) d]
    rfl
  refine ⟨B, ?_, fun j => ?_, ?_⟩
  · ext i k
    simp only [B, b, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    rw [coverComm_swap π hπ, hfinv (D.elt_mem _) (D.elt_mem _)]
    rfl
  · ext i k
    have h1 : B i k = b (fun l => D.M j l i) (fun l => D.M j l k) := by
      simp only [B, b, Matrix.of_apply, D.elt_col, D.elt_single,
        D.coverComm_conj π hπ hker _ (D.a_mem_span i) (D.a_mem_span k)]
    rw [h1, hexp]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · intro x _ y _ c d hxc hyd
    rw [commutatorElement_eq_coverComm π hπ hker, hxc, hyd]
    exact hexp c d

theorem commute_of_noAlt_any (hp : p.Prime) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (hD : D.NoAlt) :
    ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x := by
  have := Fact.mk hp
  intro x hx y hy
  rw [← commutatorElement_eq_one_iff_mul_comm]
  by_contra h1
  obtain ⟨f, hfmul, hfc⟩ := exists_log_omega_ne hp (D.commutator_mem_center π hker hx hy)
    (D.commutator_pow_eq_one π hker hx hy) h1
  obtain ⟨B, hBt, hBM, hform⟩ := exists_commForm_of_log D π hp hπ hker f hfmul
  obtain rfl : B = 0 := hD B hBt hBM
  obtain ⟨c, hc⟩ := D.exists_elt hx
  obtain ⟨d, hd⟩ := D.exists_elt hy
  apply hfc
  rw [hform x hx y hy c d hc.symm hd.symm]
  simp

end Form

section Witness

theorem actsBy_pow {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (D : ModuleSpec X p) {g : X}
    {A : Matrix (Fin D.n) (Fin D.n) (ZMod p)} (h : ActsBy D g A) : ∀ n : ℕ, ActsBy D (g ^ n) (A ^ n)
  | 0 => by simpa using actsBy_one D
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact actsBy_mul D (actsBy_pow D h n) h

theorem actsBy_unique {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (D : ModuleSpec X p) {g : X}
    {A B : Matrix (Fin D.n) (Fin D.n) (ZMod p)} (hA : ActsBy D g A) (hB : ActsBy D g B) : A = B := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ext k i
  have h := (conj_elt D hA (Pi.single i 1)).symm.trans (conj_elt D hB (Pi.single i 1))
  have := congrFun (D.elt_injective h) k
  simpa [Matrix.mulVec_single_one] using this

theorem card_comap_center {Y : Type} [Group Y] [Finite Y] (H : Subgroup (Y ⧸ Subgroup.center Y)) :
    Nat.card (H.comap (QuotientGroup.mk' (Subgroup.center Y))) =
      Nat.card (Subgroup.center Y) * Nat.card H := by
  set π := QuotientGroup.mk' (Subgroup.center Y)
  let ψ : ↥(H.comap π) →* ↥H := (π.comp (H.comap π).subtype).codRestrict H (fun x => x.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨h, hh⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) h
    exact ⟨⟨y, hh⟩, rfl⟩
  have hk : Nat.card ψ.ker = Nat.card (Subgroup.center Y) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          have h1 : ψ x.1 = 1 := x.2
          have h2 : π x.1.1 = 1 := congrArg Subtype.val h1
          exact (QuotientGroup.eq_one_iff _).1 h2⟩
        invFun := fun z => ⟨⟨z.1, by
          show π z.1 ∈ H
          rw [show π z.1 = 1 from (QuotientGroup.eq_one_iff _).2 z.2]
          exact H.one_mem⟩, Subtype.ext ((QuotientGroup.eq_one_iff _).2 z.2)⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
  rw [← Subgroup.card_ker_mul_card_of_surjective hψ, hk]

theorem hasTwoLocalWitness_of_spec {Y : Type} [Group Y] [Finite Y]
    (D : ModuleSpec (Y ⧸ Subgroup.center Y) 3) (hD : D.NoAlt) {w : Y ⧸ Subgroup.center Y}
    {A : Matrix (Fin D.n) (Fin D.n) (ZMod 3)} (hw : ActsBy D w A) (hA2 : A * A = 1) (hA1 : A ≠ 1)
    {r : ℕ} (v : Fin r → Fin D.n → ZMod 3) (hv : ∀ i, A.mulVec (v i) = v i)
    (hind : ∀ a : Fin r → ZMod 3, ∑ i, a i • v i = 0 → a = 0) : HasTwoLocalWitness Y r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center Y := QuotientGroup.ker_mk' _
  set Ebar : Subgroup (Y ⧸ Subgroup.center Y) :=
    D.span ⊓ Subgroup.centralizer ({w} : Set (Y ⧸ Subgroup.center Y)) with hEbar
  have hfix : ∀ c, A.mulVec c = c → D.elt c ∈ Ebar := fun c hc => by
    refine ⟨D.elt_mem c, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := conj_elt D hw c
    rw [hc] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  let lin : (Fin r → ZMod 3) → (Fin D.n → ZMod 3) := fun a => ∑ i, a i • v i
  have hlinA : ∀ a, A.mulVec (lin a) = lin a := fun a => by
    simp only [lin, Matrix.mulVec_sum, Matrix.mulVec_smul, hv]
  have hlin_inj : Function.Injective lin := by
    intro a b hab
    have hab' : ∑ i, a i • v i = ∑ i, b i • v i := hab
    have h0 : ∑ i, (a - b) i • v i = 0 := by
      have e : ∀ i, (a - b) i • v i = a i • v i - b i • v i := fun i => by
        ext k
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl (fun i _ => e i)]
      ext k
      have := congrFun hab' k
      simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      have h := Finset.sum_sub_distrib (s := Finset.univ) (f := fun x => a x * v x k)
        (g := fun x => b x * v x k)
      exact h.trans (sub_eq_zero.2 this)
    exact sub_eq_zero.1 (hind _ h0)
  have hEbar_card : 3 ^ r ≤ Nat.card Ebar := by
    let Φ : (Fin r → ZMod 3) → Ebar := fun a => ⟨D.elt (lin a), hfix _ (hlinA a)⟩
    have hΦ : Function.Injective Φ := fun a b h =>
      hlin_inj (D.elt_injective (congrArg Subtype.val h))
    have := Nat.card_le_card_of_injective Φ hΦ
    rwa [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at this
  set Ehat : Subgroup Y := Ebar.comap π with hEhat
  have hcomm : ∀ x ∈ Ehat, ∀ y ∈ Ehat, x * y = y * x := fun x hx y hy =>
    commute_of_noAlt_any D π Nat.prime_three hπ hker hD x (Subgroup.comap_mono inf_le_left hx) y
      (Subgroup.comap_mono inf_le_left hy)
  have hcube : ∀ x ∈ Ehat, x ^ 3 ∈ Subgroup.center Y := fun x hx => by
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact D.pow_eq_one_of_mem hx.1
  let Ω : Subgroup Y :=
    { carrier := {x | x ∈ Ehat ∧ x ^ 3 = 1}
      mul_mem' := fun {x y} hx hy => ⟨Ehat.mul_mem hx.1 hy.1, by
        rw [(Commute.mul_pow (hcomm x hx.1 y hy.1)), hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨Ehat.one_mem, one_pow 3⟩
      inv_mem' := fun {x} hx => ⟨Ehat.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hΩe : IsElemAbelian 3 Ω := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hx.2⟩
  let κ : ↥Ehat →* ↥(Subgroup.center Y) :=
    { toFun := fun x => ⟨(x : Y) ^ 3, hcube x x.2⟩
      map_one' := Subtype.ext (one_pow 3)
      map_mul' := fun x y => Subtype.ext (by
        show ((x : Y) * y) ^ 3 = (x : Y) ^ 3 * (y : Y) ^ 3
        exact Commute.mul_pow (hcomm _ x.2 _ y.2) 3) }
  have hκ : Nat.card κ.ker = Nat.card Ω := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hΩcard : 3 ^ r ≤ Nat.card Ω := by
    have h1 := Subgroup.card_ker_mul_card_range κ
    have h2 : Nat.card κ.range ≤ Nat.card (Subgroup.center Y) := Subgroup.card_le_card_group _
    have h3 := card_comap_center Ebar
    have hZ : 0 < Nat.card (Subgroup.center Y) := Nat.card_pos
    rw [← hκ]
    have h4 : Nat.card (Subgroup.center Y) * Nat.card Ebar ≤
        Nat.card κ.ker * Nat.card (Subgroup.center Y) := by
      rw [← h3]
      show Nat.card ↥Ehat ≤ _
      rw [← h1]
      exact Nat.mul_le_mul_left _ h2
    have h5 : Nat.card Ebar ≤ Nat.card κ.ker := by
      rw [mul_comm] at h4
      exact Nat.le_of_mul_le_mul_right h4 hZ
    exact hEbar_card.trans h5
  have hΩ3 : IsPGroup 3 Ω := fun g => ⟨1, Subtype.ext (by simpa using g.2.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hΩ3
  have hrm : r ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hm ▸ hΩcard)
  obtain ⟨E, hEΩ, hEe, hEc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hΩe
    (n := r) (by rw [hm]; exact pow_dvd_pow 3 hrm)
  have hwo : orderOf w ≠ 0 := (orderOf_pos w).ne'
  have hw2 : 2 ∣ orderOf w := by
    by_contra hodd
    have hodd' : Odd (orderOf w) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    obtain ⟨k, hk⟩ := hodd'
    have hpow := actsBy_pow D hw (orderOf w + 1)
    rw [pow_succ, pow_orderOf_eq_one, one_mul, hk,
      show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, sq, hA2, one_pow] at hpow
    exact hA1 (actsBy_unique D hw hpow)
  set u := w ^ (orderOf w / 2) with hu
  have hu2 : orderOf u = 2 := orderOf_pow_orderOf_div hwo hw2
  set R : Subgroup (Y ⧸ Subgroup.center Y) := Subgroup.zpowers u
  have hR : R ≠ ⊥ := by
    intro h
    have : u = 1 := (Subgroup.mem_bot).1 (h ▸ Subgroup.mem_zpowers u)
    rw [this, orderOf_one] at hu2
    norm_num at hu2
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  have hEbarR : ∀ g ∈ Ebar, g ∈ Subgroup.normalizer (R : Set (Y ⧸ Subgroup.center Y)) := by
    intro g hg
    have hgw : g * w = w * g := Subgroup.mem_centralizer_singleton_iff.1 hg.2
    have hgu : Commute g u := by
      rw [hu]
      exact Commute.pow_right hgw (orderOf w / 2)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by
        show u ^ n = g * u ^ n * g⁻¹
        rw [(hgu.zpow_right n).eq, mul_inv_cancel_right]⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hn' : u ^ n = g * h * g⁻¹ := hn
      have hz := (hgu.zpow_right n).eq
      show u ^ n = h
      calc u ^ n = g⁻¹ * (g * u ^ n) := by group
        _ = g⁻¹ * (u ^ n * g) := by rw [hz]
        _ = g⁻¹ * (g * h * g⁻¹ * g) := by rw [← hn']
        _ = h := by group
  obtain ⟨R₂, hR₂, hR₂2, hN⟩ := CFSG.SectionRank.QTK.exists_two_subgroup_normalized hR hR2
  refine ⟨R₂, E, hR₂, hR₂2, fun y hy => hN y (hEbarR _ (hEΩ hy).1), hEe, hEc⟩

end Witness

section Cert

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank CFSG.SectionRank.Native

theorem hasTwoLocalWitness_of_modCheckV {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ}
    (Sp : OpsSpec O c d) {sA sB : String} {nregs : ℕ} {prog : List Op} {m : NMod}
    {tops : List Pc} {tidx : List ℕ} {s : ℕ} {orb : List (ℕ × ℕ)} {cf : ℕ → ℕ → ℕ → ℤ}
    {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : modCheckV O sA sB nregs prog 3 m tops tidx s orb cf ci ct = true)
    {Y : Type} [Group Y] [Finite Y] (ψ : (certMonoid c d sA sB)ˣ ≃* Y ⧸ Subgroup.center Y)
    (j : Fin m.acts.length) (k : ℕ) {r : ℕ} (v : Fin r → Fin m.basis.length → ZMod 3)
    (hA2 : (actMatN 3 m.basis.length (m.acts.get j)) ^ k *
      (actMatN 3 m.basis.length (m.acts.get j)) ^ k = 1)
    (hA1 : (actMatN 3 m.basis.length (m.acts.get j)) ^ k ≠ 1)
    (hv : ∀ i, ((actMatN 3 m.basis.length (m.acts.get j)) ^ k).mulVec (v i) = v i)
    (hind : ∀ a : Fin r → ZMod 3, ∑ i, a i • v i = 0 → a = 0) : HasTwoLocalWitness Y r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold modCheckV at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hw⟩, -⟩, -⟩, -⟩, -⟩, -⟩, halt⟩ := h
  let C : MCert := ⟨nregs, prog, m.modFactsW 3 tops⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have hf : ∀ f ∈ m.facts 3, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFactsW 3 tops
    simp only [NMod.modFactsW, List.mem_append]
    exact Or.inl hf
  let DS := NMod.specO Sp hC' m hf hw
  have hA : DS.NoAlt := fun B hB hinv => noAlt_of_altOK halt B hB hinv
  let D' := DS.map ψ.toMonoidHom ψ.injective
  have hD' : D'.NoAlt := hA
  exact hasTwoLocalWitness_of_spec D' hD' (actsBy_pow D' (actsBy_g D' j) k) hA2 hA1 v hv hind

end Cert

open CFSG.RankThree.Asc83Table CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
open CFSG.AGLEmbedding.R3.AlphaFi24

@[expose] def j9 : Fin fi24Mod.acts.length := ⟨9, by decide⟩

@[expose] def A9 : Matrix (Fin fi24Mod.basis.length) (Fin fi24Mod.basis.length) (ZMod 3) :=
  (actMatN 3 fi24Mod.basis.length (fi24Mod.acts.get j9)) ^ 9

@[expose] def fixTab : Fin 5 → Fin 7 → ZMod 3 :=
  ![![2, 1, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0], ![0, 0, 1, 0, 1, 0, 0],
    ![1, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 1]]

@[expose] def fixVec : Fin 5 → Fin fi24Mod.basis.length → ZMod 3 :=
  fun i k => fixTab i (Fin.cast (by decide) k)

theorem A9_sq : A9 * A9 = 1 := by decide +kernel

theorem A9_ne_one : A9 ≠ 1 := by decide +kernel

theorem A9_fix : ∀ i, A9.mulVec (fixVec i) = fixVec i := by decide +kernel

theorem fixVec_indep : ∀ a : Fin 5 → ZMod 3, ∑ i, a i • fixVec i = 0 → a = 0 := by decide +kernel


set_option maxRecDepth 100000 in
theorem i1432WitFi24_holds : I1432WitFi24 := by
  intro Y _ _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi24Prime
  let ψ0 : NativeSporadic.Carrier .Fi24Prime ≃*
      (certMonoid 3 781 NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2)ˣ :=
    MulEquiv.refl _
  have ψ : (certMonoid 3 781 NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2)ˣ ≃*
      Y ⧸ Subgroup.center Y := (ψ0.symm.trans b).trans e.symm
  exact hasTwoLocalWitness_of_modCheckV (CFSG.RankThree.Asc83Table.matOpsSpec 3 781)
    (modCheckV_matOps Certificates.certificate9602) ψ j9 9
    fixVec A9_sq A9_ne_one A9_fix fixVec_indep

end CFSG.LocalAnalysis.GLTheoremA.H1420.WitFi24

end
