module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_fixed_sylow_of_action {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {A : Type*} [Group A] (hA : IsPGroup p A) (ψ : A →* MulAut M) {H : Subgroup M}
    (hH : ∀ a, ∀ h ∈ H, ψ a h ∈ H) :
    ∃ S : Subgroup M, S ≤ H ∧ Nat.card S = p ^ (Nat.card H).factorization p ∧
      ∀ a, ∀ s ∈ S, ψ a s ∈ S := by
  have : Fact p.Prime := ⟨hp⟩
  let φ : A →* MulAut H :=
    { toFun := fun a =>
        { toFun := fun h => ⟨ψ a h, hH a h h.2⟩
          invFun := fun h => ⟨ψ a⁻¹ h, hH a⁻¹ h h.2⟩
          left_inv := fun h => Subtype.ext (by
            show (ψ a⁻¹) ((ψ a) h) = h
            rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl)
          right_inv := fun h => Subtype.ext (by
            show (ψ a) ((ψ a⁻¹) h) = h
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
          map_mul' := fun x y => Subtype.ext (by
            show (ψ a) ((x : M) * y) = (ψ a) x * (ψ a) y
            exact map_mul _ _ _) }
      map_one' := by
        ext h
        show (ψ 1) h = h
        rw [map_one]; rfl
      map_mul' := fun a b => by
        ext h
        show (ψ (a * b)) h = (ψ a) ((ψ b) h)
        rw [map_mul]; rfl }
  let _ : MulDistribMulAction A H := MulDistribMulAction.compHom H φ
  obtain ⟨S, hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (α := Sylow p H)
    (not_dvd_card_sylow p H)
  refine ⟨(S : Subgroup H).map H.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Sylow.card_eq_multiplicity S
  · intro a s hs
    obtain ⟨t, ht, rfl⟩ := hs
    have h1 : a • S = S := hS a
    have h2 : a • (S : Subgroup H) = S := by
      have := congrArg (fun T : Sylow p H => (T : Subgroup H)) h1
      exact this
    have h3 : φ a t ∈ (S : Subgroup H) := by
      rw [← h2]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ ht
    exact ⟨_, h3, rfl⟩

private theorem eq_one_of_orderOf_dvd_coprime {H : Type*} [Group H] {x : H} {m n : ℕ}
    (hmn : Nat.Coprime m n) (h1 : orderOf x ∣ m) (h2 : orderOf x ∣ n) : x = 1 := by
  have h : Nat.Coprime (orderOf x) (orderOf x) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.coprime_dvd_right h2 hmn)
  exact orderOf_eq_one_iff.1 (Nat.coprime_self _ |>.1 h)

theorem exists_fixed_section_of_inner {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (P : Subgroup M) [P.Normal] (hP : Nat.Coprime p (Nat.card P))
    {A : Type*} [Group A] (hA : IsPGroup p A) (ψ : A →* MulAut M) (φ : A →* MulAut (M ⧸ P))
    (hφ : ∀ a (x : M), φ a (QuotientGroup.mk x) = QuotientGroup.mk (ψ a x))
    (hSyl : ∀ Q : Sylow p (M ⧸ P), IsElemAbelian p (Q : Subgroup (M ⧸ P)))
    (hInn : ∀ σ : MulAut (M ⧸ P), IsPGroup p (Subgroup.zpowers σ) →
      ∃ k : M ⧸ P, σ = MulAut.conj k)
    (hZ : Subgroup.center (M ⧸ P) = ⊥) :
    ∃ S : Subgroup M, (∀ s ∈ S, s ∈ P → s = 1) ∧ (∀ a, ∀ s ∈ S, ψ a s = s) ∧
      (∀ a, ∃ f ∈ S, φ a = MulAut.conj (QuotientGroup.mk f : M ⧸ P)) ∧ IsElemAbelian p S ∧
      Nat.card S = p ^ (Nat.card (M ⧸ P)).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hAφ : IsPGroup p φ.range := hA.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hker : IsPGroup p (MulAut.conj : (M ⧸ P) →* MulAut (M ⧸ P)).ker := by
    intro x
    refine ⟨0, ?_⟩
    have hx : (x : M ⧸ P) = 1 := by
      have hxc : (x : M ⧸ P) ∈ Subgroup.center (M ⧸ P) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h := congrArg (fun σ : MulAut (M ⧸ P) => σ g) (MonoidHom.mem_ker.1 x.2)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        exact (mul_inv_eq_iff_eq_mul.1 h).symm
      rw [hZ] at hxc
      simpa using hxc
    ext
    simp [hx]
  have hR : IsPGroup p (φ.range.comap (MulAut.conj : (M ⧸ P) →* MulAut (M ⧸ P))) :=
    hAφ.comap_of_ker_isPGroup _ hker
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  have hzp : ∀ a, IsPGroup p (Subgroup.zpowers (φ a)) := fun a => by
    have h : Subgroup.zpowers (φ a) ≤ φ.range :=
      (Subgroup.zpowers_le).2 (MonoidHom.mem_range.2 ⟨a, rfl⟩)
    exact hAφ.of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)
  choose k hk using fun a => hInn (φ a) (hzp a)
  have hkQ : ∀ a, k a ∈ (Q : Subgroup (M ⧸ P)) := fun a => by
    apply hRQ
    rw [Subgroup.mem_comap, ← hk a]
    exact MonoidHom.mem_range.2 ⟨a, rfl⟩
  have hQab := hSyl Q
  have hQc : ∀ x ∈ (Q : Subgroup (M ⧸ P)), ∀ y ∈ (Q : Subgroup (M ⧸ P)), x * y = y * x :=
    fun x hx y hy => by
      have := hQab.1
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : (Q : Subgroup (M ⧸ P))) ⟨y, hy⟩)
  let H : Subgroup M := (Q : Subgroup (M ⧸ P)).comap (QuotientGroup.mk' P)
  have hmemH : ∀ x : M, x ∈ H ↔ (QuotientGroup.mk x : M ⧸ P) ∈ (Q : Subgroup (M ⧸ P)) :=
    fun x => Iff.rfl
  have hHinv : ∀ a, ∀ h ∈ H, ψ a h ∈ H := fun a h hh => by
    rw [hmemH, ← hφ, hk a, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hkQ a) ((hmemH h).1 hh)) (Subgroup.inv_mem _ (hkQ a))
  obtain ⟨S, hSH, hScard, hSinv⟩ := exists_fixed_sylow_of_action hp hA ψ hHinv
  have hKQ : Nat.card (Q : Subgroup (M ⧸ P)) = p ^ (Nat.card (M ⧸ P)).factorization p :=
    Sylow.card_eq_multiplicity Q
  have hHcard : Nat.card H = Nat.card (Q : Subgroup (M ⧸ P)) * Nat.card P := by
    have h1 := Subgroup.card_mul_index H
    have h2 := Subgroup.card_mul_index (Q : Subgroup (M ⧸ P))
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup P
    have hidx : H.index = (Q : Subgroup (M ⧸ P)).index :=
      Subgroup.index_comap_of_surjective (Q : Subgroup (M ⧸ P)) (QuotientGroup.mk'_surjective P)
    have hpos : 0 < (Q : Subgroup (M ⧸ P)).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at h1
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc Nat.card H * (Q : Subgroup (M ⧸ P)).index = Nat.card M := h1
      _ = Nat.card (M ⧸ P) * Nat.card P := h3
      _ = (Nat.card (Q : Subgroup (M ⧸ P)) * (Q : Subgroup (M ⧸ P)).index) * Nat.card P := by
        rw [h2]
      _ = Nat.card (Q : Subgroup (M ⧸ P)) * Nat.card P * (Q : Subgroup (M ⧸ P)).index := by ring
  have hPnd : ¬ p ∣ Nat.card P := (Nat.Prime.coprime_iff_not_dvd hp).1 hP
  have hPpos : Nat.card P ≠ 0 := Nat.card_pos.ne'
  have hSQ : Nat.card S = Nat.card (Q : Subgroup (M ⧸ P)) := by
    rw [hScard, hHcard, hKQ, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hPpos,
      Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hPnd, add_zero]
  have hSP : ∀ s ∈ S, s ∈ P → s = 1 := fun s hs hsP => by
    refine eq_one_of_orderOf_dvd_coprime (m := Nat.card S) (n := Nat.card P) ?_
      (Subgroup.orderOf_dvd_natCard S hs) (Subgroup.orderOf_dvd_natCard P hsP)
    rw [hSQ, hKQ]
    exact hP.pow_left _
  have hinj : ∀ s ∈ S, ∀ t ∈ S, (QuotientGroup.mk s : M ⧸ P) = QuotientGroup.mk t → s = t := by
    intro s hs t ht hst
    have h1 : s⁻¹ * t ∈ P := QuotientGroup.eq.1 hst
    have := hSP _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) ht) h1
    exact (inv_mul_eq_one.1 this)
  have hSmem : ∀ s ∈ S, (QuotientGroup.mk s : M ⧸ P) ∈ (Q : Subgroup (M ⧸ P)) :=
    fun s hs => (hmemH s).1 (hSH hs)
  have hQS : ∀ q ∈ (Q : Subgroup (M ⧸ P)), ∃ f ∈ S, (QuotientGroup.mk f : M ⧸ P) = q := by
    have hle : S.map (QuotientGroup.mk' P) ≤ (Q : Subgroup (M ⧸ P)) := by
      rintro _ ⟨s, hs, rfl⟩
      exact hSmem s hs
    have hcard : Nat.card (Q : Subgroup (M ⧸ P)) ≤ Nat.card (S.map (QuotientGroup.mk' P)) := by
      rw [← hSQ]
      refine Nat.card_le_card_of_injective
        (fun s : S => (⟨QuotientGroup.mk' P s, Subgroup.mem_map_of_mem _ s.2⟩ :
          S.map (QuotientGroup.mk' P))) ?_
      intro s t hst
      have : (QuotientGroup.mk (s : M) : M ⧸ P) = QuotientGroup.mk (t : M) :=
        congrArg Subtype.val hst
      exact Subtype.ext (hinj _ s.2 _ t.2 this)
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    intro q hq
    rw [← heq] at hq
    obtain ⟨f, hf, rfl⟩ := hq
    exact ⟨f, hf, rfl⟩
  have hfix : ∀ a, ∀ s ∈ S, ψ a s = s := fun a s hs => by
    refine hinj _ (hSinv a s hs) _ hs ?_
    rw [← hφ, hk a, MulAut.conj_apply]
    have := hQc _ (hkQ a) _ (hSmem s hs)
    rw [this]
    group
  refine ⟨S, hSP, hfix, fun a => ?_, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨f, hf, hfk⟩ := hQS _ (hkQ a)
    exact ⟨f, hf, by rw [hk a, hfk]⟩
  · exact hinj ((x : M) * y) (Subgroup.mul_mem _ x.2 y.2) ((y : M) * x) (Subgroup.mul_mem _ y.2 x.2)
      (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hQc _ (hSmem _ x.2) _ (hSmem _ y.2))
  · refine hinj _ (Subgroup.pow_mem _ hx _) _ (Subgroup.one_mem _) ?_
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_one]
    exact hQab.2 _ (hSmem x hx)
  · rw [hSQ, hKQ]

private theorem mem_gLAPPrimeCoreOf_iff {p : ℕ} {L : Subgroup G} {z : G} :
    z ∈ GLAPPrimeCoreOf p L ↔ ∃ h : z ∈ L, (⟨z, h⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hz⟩
    exact ⟨⟨z, h⟩, hz, rfl⟩

private theorem conj_mem_gLAPPrimeCoreOf {p : ℕ} {L : Subgroup G} {g z : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hz : z ∈ GLAPPrimeCoreOf p L) :
    g * z * g⁻¹ ∈ GLAPPrimeCoreOf p L := by
  obtain ⟨hzL, hzP⟩ := mem_gLAPPrimeCoreOf_iff.1 hz
  have hgL : g * z * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hg z).1 hzL
  refine mem_gLAPPrimeCoreOf_iff.2 ⟨hgL, ?_⟩
  exact map_gLAPPrimeCore_le p (L.normalizerMonoidHom ⟨g, hg⟩)
    (Subgroup.mem_map_of_mem _ hzP)

private theorem mem_centralizerQuot_iff {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ centralizerQuot L (GLAPPrimeCoreOf p L) ↔ barAut p L ⟨g, hg⟩ = 1 := by
  have hσ : ∀ x : ↥L, ((L.normalizerMonoidHom ⟨g, hg⟩ x : ↥L) : G) = g * x * g⁻¹ :=
    fun x => rfl
  have hiff : barAut p L ⟨g, hg⟩ = 1 ↔
      ∀ x : ↥L, (L.normalizerMonoidHom ⟨g, hg⟩ x)⁻¹ * x ∈ GLAPPrimeCore p ↥L := by
    constructor
    · intro h x
      have := congrArg (fun σ : MulAut (barOf p L) => σ (QuotientGroup.mk x)) h
      simp only [barAut_mk, MulAut.one_apply] at this
      exact QuotientGroup.eq.1 this
    · intro h
      refine MulEquiv.ext fun z => ?_
      refine QuotientGroup.induction_on z fun x => ?_
      rw [barAut_mk, MulAut.one_apply]
      exact QuotientGroup.eq.2 (h x)
  rw [hiff]
  constructor
  · rintro ⟨-, -, hc⟩ x
    have h1 := Subgroup.inv_mem _ (hc ((x : G)⁻¹) (Subgroup.inv_mem _ x.2))
    obtain ⟨hzL, hzP⟩ := mem_gLAPPrimeCoreOf_iff.1 h1
    convert hzP using 1
    apply Subtype.ext
    simp [hσ]
    group
  · intro h
    refine ⟨hg, ?_, fun x hx => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · exact conj_mem_gLAPPrimeCoreOf hg
      · intro hz
        have := conj_mem_gLAPPrimeCoreOf (Subgroup.inv_mem _ hg) hz
        simpa [mul_assoc] using this
    · have hz : (((L.normalizerMonoidHom ⟨g, hg⟩ (⟨x, hx⟩ : ↥L)⁻¹)⁻¹ * (⟨x, hx⟩ : ↥L)⁻¹ : ↥L) : G)
          ∈ GLAPPrimeCoreOf p L := ⟨_, h _, rfl⟩
      have := Subgroup.inv_mem _ hz
      convert this using 1
      simp [hσ]
      group

private theorem isElemAbelian_sup_of_commute' {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E)
    (hF : IsElemAbelian p F) (hc : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e) :
    IsElemAbelian p (E ⊔ F) := CFSG.Open.IsElemAbelian.sup_of_commute hE hF hc

theorem lemma43_one_core [Finite G] {p : ℕ} (hp : p.Prime) {B L : Subgroup G}
    (hBmax : IsSCp p ⊤ B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center (barOf p L) = ⊥)
    (hSyl : ∀ Q : Sylow p (barOf p L), IsElemAbelian p (Q : Subgroup (barOf p L)))
    (hInn : ∀ φ : MulAut (barOf p L), IsPGroup p (Subgroup.zpowers φ) →
      ∃ k : barOf p L, φ = MulAut.conj k) :
    cBarB p B L ⊔ B ⊓ L = B ∧ cBarB p B L ⊓ (B ⊓ L) = ⊥ ∧ IsElemAbelian p (B ⊓ L) ∧
      Nat.card ↥(B ⊓ L) = p ^ (Nat.card L).factorization p := by
  have hpf : Fact p.Prime := ⟨hp⟩
  let ψ : ↥B →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  let φ : ↥B →* MulAut (barOf p L) := (barAut p L).comp (Subgroup.inclusion hBN)
  have hφ : ∀ (b : ↥B) (x : ↥L), φ b (QuotientGroup.mk x) = QuotientGroup.mk (ψ b x) :=
    fun b x => barAut_mk p L _ x
  have hA : IsPGroup p ↥B := fun x => ⟨1, Subtype.ext (by simpa using hBmax.2.1.2 x x.2)⟩
  have hP : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥L)) :=
    coprime_card_gLAPPrimeCore_aux p ↥L
  have hPnd : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥L) := (Nat.Prime.coprime_iff_not_dvd hp).1 hP
  obtain ⟨S, hSP, hSψ, hSf, hSel, hScard⟩ :=
    exists_fixed_section_of_inner hp (GLAPPrimeCore p ↥L) hP hA ψ φ hφ hSyl hInn hZ
  let S' : Subgroup G := S.map L.subtype
  have hS'L : S' ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hS'comm : ∀ b ∈ B, ∀ s ∈ S', b * s = s * b := by
    rintro b hb _ ⟨t, ht, rfl⟩
    have h2 : ((ψ ⟨b, hb⟩ t : ↥L) : G) = t := congrArg Subtype.val (hSψ ⟨b, hb⟩ t ht)
    have h3 : b * (t : G) * b⁻¹ = t := h2
    exact mul_inv_eq_iff_eq_mul.1 h3
  have hS'el : IsElemAbelian p S' := by
    have hc : ∀ a ∈ S', ∀ b ∈ S', a * b = b * a := by
      rintro _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩
      have := hSel.1
      exact congrArg Subtype.val (congrArg Subtype.val
        (mul_comm' (⟨t, ht⟩ : S) ⟨u, hu⟩))
    refine ⟨⟨⟨fun x y => Subtype.ext (hc x x.2 y y.2)⟩⟩, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact congrArg Subtype.val (hSel.2 t ht)
  have hsup : IsElemAbelian p (B ⊔ S') :=
    isElemAbelian_sup_of_commute' hBmax.2.1 hS'el hS'comm
  have hS'B : S' ≤ B := le_sup_right.trans (hBmax.2.2 _ le_top hsup le_sup_left).le
  have hext : ∀ β ∈ B, ∃ f ∈ S', β * f⁻¹ ∈ cBarB p B L := by
    intro β hβ
    obtain ⟨f, hfS, hφf⟩ := hSf ⟨β, hβ⟩
    have hf'S' : (f : G) ∈ S' := ⟨f, hfS, rfl⟩
    have hf'B := hS'B hf'S'
    refine ⟨f, hf'S', ?_⟩
    have hgB : β * (f : G)⁻¹ ∈ B := mul_mem hβ (inv_mem hf'B)
    refine ⟨hgB, (mem_centralizerQuot_iff (hBN hgB)).2 ?_⟩
    have e1 : (⟨β * (f : G)⁻¹, hBN hgB⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨β, hBN hβ⟩ * (⟨f, hBN hf'B⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ := rfl
    rw [e1, map_mul, map_inv, mul_inv_eq_one]
    have h1 : barAut p L ⟨β, hBN hβ⟩ = φ ⟨β, hβ⟩ := rfl
    have h2 : barAut p L ⟨f, hBN hf'B⟩ = φ ⟨f, hf'B⟩ := rfl
    rw [h1, h2, hφf]
    refine MulEquiv.ext fun z => ?_
    refine QuotientGroup.induction_on z fun x => ?_
    rw [hφ, MulAut.conj_apply]
    have e : ψ ⟨f, hf'B⟩ x = f * x * f⁻¹ := Subtype.ext rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hkey : ∀ a ∈ B, a ∈ L → a ∈ cBarB p B L → a = 1 := by
    intro a haB haL hac
    have h1 : barAut p L ⟨a, hBN haB⟩ = 1 := (mem_centralizerQuot_iff (hBN haB)).1 hac.2
    have hxc : (QuotientGroup.mk (⟨a, haL⟩ : ↥L) : barOf p L) ∈ Subgroup.center (barOf p L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      refine QuotientGroup.induction_on z fun y => ?_
      have := congrArg (fun σ : MulAut (barOf p L) => σ (QuotientGroup.mk y)) h1
      simp only [barAut_mk, MulAut.one_apply] at this
      have e : L.normalizerMonoidHom ⟨a, hBN haB⟩ y = (⟨a, haL⟩ : ↥L) * y * (⟨a, haL⟩ : ↥L)⁻¹ :=
        Subtype.ext rfl
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxc
    have hxp : (⟨a, haL⟩ : ↥L) ^ p = 1 := Subtype.ext (by simpa using hBmax.2.1.2 a haB)
    have hx1 : (⟨a, haL⟩ : ↥L) = 1 :=
      eq_one_of_orderOf_dvd_coprime hP (orderOf_dvd_of_pow_eq_one hxp)
        (Subgroup.orderOf_dvd_natCard _ hxc)
    exact congrArg Subtype.val hx1
  have hc : B ⊓ L = S' := by
    refine le_antisymm ?_ (le_inf hS'B hS'L)
    rintro β ⟨hβB, hβL⟩
    obtain ⟨f, hfS', hfc⟩ := hext β hβB
    have ha : β * (f : G)⁻¹ = 1 :=
      hkey _ hfc.1 (mul_mem hβL (inv_mem (hS'L hfS'))) hfc
    rw [mul_inv_eq_one.1 ha]
    exact hfS'
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_antisymm (sup_le inf_le_left inf_le_left) fun β hβ => ?_
    obtain ⟨f, hfS', hfc⟩ := hext β hβ
    have := Subgroup.mul_mem_sup hfc (show f ∈ B ⊓ L from ⟨hS'B hfS', hS'L hfS'⟩)
    simpa using this
  · rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hkey x hx.2.1 hx.2.2 hx.1)
  · rw [hc]; exact hS'el
  · rw [hc, Subgroup.card_map_of_injective L.subtype_injective, hScard,
      Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore p ↥L),
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hPnd, add_zero]

@[expose] def Fi22Facts : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsFiTwentyTwo K →
    Subgroup.center K = ⊥ ∧ (Nat.card K).factorization 5 = 2 ∧ (∀ x : K, orderOf x ≠ 25) ∧
    ∀ φ : MulAut K, IsPGroup 5 (Subgroup.zpowers φ) → ∃ k : K, φ = MulAut.conj k


theorem lemma43_i_of_facts (hF : Fi22Facts) (h112 : Input11_2) (h23 : Lemma23) {G : Type}
    [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 5) {B : Subgroup G} (hB : IsBOneMax 5 B)
    {b : G} (hb : b ∈ B) {L : Subgroup G}
    (hL : GLAPComponent 5 (Subgroup.centralizer ({b} : Set G)) L)
    (hM : IsFiTwentyTwo (barOf 5 L)) :
    cBarB 5 B L ⊔ B ⊓ L = B ∧ cBarB 5 B L ⊓ (B ⊓ L) = ⊥ ∧ IsPPlane 5 (B ⊓ L) ∧
      Nat.card ↥(B ⊓ L) = 5 ^ (Nat.card L).factorization 5 := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have hBsc : IsSCp 5 ⊤ B := h23 G m 5 hS B hB
  have hBel : IsElemAbelian 5 B := hB.1.1
  have hBC : B ≤ Subgroup.centralizer ({b} : Set G) := le_centralizer_of_mem hBel hb
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := by
    by_contra hn
    have hrk : GLATwoLocalRank 5 ↥(Subgroup.centralizer ({b} : Set G)) ≤ CFSG.Open.pRank 5 B :=
      (glaTwoLocalRank_subgroup_le hp _).trans (hS.rank_eq.le.trans (hS.le_pRank' hB))
    have := (h112 G m 5 hS _ B L hBel hBC hrk hL hn).1
    omega
  obtain ⟨hZ, hv, hord, hInn⟩ := hF (barOf 5 L) hM
  have hSyl : ∀ Q : Sylow 5 (barOf 5 L), IsElemAbelian 5 (Q : Subgroup (barOf 5 L)) := by
    intro Q
    have hcard : Nat.card (Q : Subgroup (barOf 5 L)) = 5 ^ 2 := by
      rw [Sylow.card_eq_multiplicity, hv]
    refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard, fun x hx => ?_⟩
    have hdvd : orderOf (x : barOf 5 L) ∣ 5 ^ 2 := by
      rw [← hcard]
      have h := orderOf_dvd_natCard (⟨x, hx⟩ : (Q : Subgroup (barOf 5 L)))
      rwa [← Subgroup.orderOf_coe] at h
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hk2 : k ≠ 2 := fun h => hord x (by rw [hk', h]; norm_num)
    have hk1 : k ≤ 1 := by omega
    exact orderOf_dvd_iff_pow_eq_one.1 (hk' ▸ (pow_dvd_pow 5 hk1))
  obtain ⟨h1, h2, h3, h4⟩ := lemma43_one_core hp hBsc hBN hZ hSyl hInn
  have hLcard : Nat.card L = Nat.card (barOf 5 L) * Nat.card (GLAPPrimeCore 5 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 5 ↥L)
  have hfac : (Nat.card L).factorization 5 = 2 := by
    rw [hLcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hv,
      Nat.factorization_eq_zero_of_not_dvd
        ((hp.coprime_iff_not_dvd).1 (coprime_card_gLAPPrimeCore_aux 5 ↥L))]
  refine ⟨h1, h2, ⟨h3, ?_⟩, h4⟩
  rw [h4, hfac]

end CFSG.HardMathSupport.Solomon.LocalBalance
