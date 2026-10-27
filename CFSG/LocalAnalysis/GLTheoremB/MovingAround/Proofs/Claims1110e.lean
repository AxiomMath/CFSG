module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs183eqv
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110e

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut Fi22Facts IsFiTwentyTwo)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  (conj_mem_gLAPPrimeCoreOf gLAPPrimeCoreOf_le mem_gLAPPrimeCoreOf_iff card_gLAPPrimeCoreOf_coprime)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

@[expose] def InputA5Up : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 5 K = ⊥ →
    ∀ x : MulAut K, Lemma1314.PumpupVia 5 ↥(alternatingGroup (Fin 5)) K x →
      ((∀ k : ℕ, 1 ≤ k → ¬ IsUpType (5 * k) 4 (K ⧸ Subgroup.center K)) →
          Subgroup.center K = ⊥ ∧
            CFSG.Open.pRank 5 (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer K)) ≤ 1) ∧
      ∀ k : ℕ, 1 ≤ k → IsUpType (5 * k) 4 (K ⧸ Subgroup.center K) →
        IsChevSimple 2 (K ⧸ Subgroup.center K) ∧ ¬ Claims1116.Exc5 (K ⧸ Subgroup.center K) ∧
        (∃ F : Subgroup K, F ≤ Lemma1314.fixSub x ∧ IsElemAbelian 5 F ∧
          omegaOne 5 (Subgroup.center K) ≤ F ∧
          Nat.card F = 5 ^ (5 * k - 2) * Nat.card (omegaOne 5 (Subgroup.center K))) ∧
        (k = 1 → ∀ P : Subgroup (MulAut K), IsPGroup 5 P →
          ∀ E : Subgroup (MulAut K), E ≤ P → IsElemAbelian 5 E → 5 ^ 3 ≤ Nat.card E →
          ∀ F : Subgroup K, IsElemAbelian 5 F → F.map (MulAut.conj : K →* MulAut K) ≤ P →
            5 ^ 3 ≤ Nat.card (F.map (MulAut.conj : K →* MulAut K)) →
            ∀ β ∈ E, ∀ f ∈ F, β f = f)

section Basics

theorem center_eq_bot_of_isAltType_five {Y : Type*} [Group Y] (hY : IsAltType 5 Y) :
    Subgroup.center Y = ⊥ := by
  obtain ⟨ψ⟩ := hY
  have h := Subgroup.map_center_eq ψ
  rw [alternatingGroup.center_eq_bot (by simp)] at h
  rw [eq_bot_iff]
  intro z hz
  have hz' : ψ z ∈ (Subgroup.center Y).map ψ := ⟨z, hz, rfl⟩
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact ψ.injective (by rw [hz', map_one])

theorem card_map_mul_card_inf_ker {A B : Type*} [Group A] [Group B] (f : A →* B) (H : Subgroup A) :
    Nat.card (H.map f) * Nat.card ↥(H ⊓ f.ker) = Nat.card H := by
  have h := Subgroup.card_ker_mul_card_range (f.comp H.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hk : Nat.card ↥(f.comp H.subtype).ker = Nat.card ↥(H ⊓ f.ker) := by
    have e1 : (f.comp H.subtype).ker = (H ⊓ f.ker).subgroupOf H := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [e1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hk] at h
  rw [mul_comm]
  exact h

theorem outRankLeOne_of_pRank {J : Type} [Group J] [Finite J]
    (h : CFSG.Open.pRank 5 (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer J)) ≤ 1) :
    Claims1110d.OutRankLeOne J := by
  intro X hX hc h5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set N := CFSG.ComponentClassification.OuterAutomorphisms.inner J with hN
  set q := QuotientGroup.mk' N with hq
  have hker : q.ker = innerAut J := by
    rw [hq, QuotientGroup.ker_mk']
    rfl
  set Xb := X.map q with hXb
  have hXbp : IsPGroup 5 Xb := hX.map q
  have hXbel : IsElemAbelian 5 Xb := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxu⟩ := u.2
      obtain ⟨y, hy, hyv⟩ := v.2
      apply Subtype.ext
      show (u : CFSG.ComponentClassification.OuterAutomorphisms.Outer J) * v = v * u
      rw [← hxu, ← hyv, ← map_mul, ← map_mul]
      have hm : x * y * x⁻¹ * y⁻¹ ∈ q.ker := by rw [hker]; exact hc x hx y hy
      rw [MonoidHom.mem_ker] at hm
      have e1 : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      rw [e1, map_mul, hm, one_mul]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have hm : x ^ 5 ∈ q.ker := by rw [hker]; exact h5 x hx
      exact hm
  obtain ⟨k, hk⟩ := hXbp.exists_card_eq
  have hk1 : k ≤ 1 :=
    (CFSG.SectionRank.le_pRank (by norm_num : 1 < 5) le_top hXbel hk).trans h
  have hcard := card_map_mul_card_inf_ker q X
  rw [hker] at hcard
  have hle : Nat.card Xb ≤ 5 := by
    rw [hk]
    calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 5 := pow_one 5
  calc Nat.card X = Nat.card Xb * Nat.card ↥(X ⊓ innerAut J) := hcard.symm
    _ ≤ 5 * Nat.card ↥(X ⊓ innerAut J) := Nat.mul_le_mul_right _ hle

theorem outRankLeOne_of_isAltType_five {Y : Type} [Group Y] [Finite Y] (hY : IsAltType 5 Y) :
    Claims1110d.OutRankLeOne Y := by
  intro X hX _ _
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ψ⟩ := hY
  have hA : Nat.card (MulAut Y) = 120 := by
    rw [CFSG.LargeExtraspecial.S12Tri.card_mulAut_congr ψ]
    exact CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hdvd : 5 ^ k ∣ 120 := hk ▸ hA ▸ Subgroup.card_subgroup_dvd_card X
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h25 : 5 ^ 2 ∣ 120 := (pow_dvd_pow 5 (by omega)).trans hdvd
    norm_num at h25
  have hpos : 0 < Nat.card ↥(X ⊓ innerAut Y) := Nat.card_pos
  rw [hk]
  calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 5 * 1 := by norm_num
    _ ≤ 5 * Nat.card ↥(X ⊓ innerAut Y) := Nat.mul_le_mul_left _ hpos

end Basics

section Eqv

variable {G : Type} [Group G] [Finite G]

theorem alt_of_eqv {e a : G} {J₁ L : Subgroup G} (hJ₁ : GLAPComponent 5 (Cg e) J₁)
    (hL : GLAPComponent 5 (Cg2 e a) L) (hLA5 : IsAltType 5 (barOf 5 L))
    (hLI : L ≤ ⨆ g ∈ Subgroup.zpowers a, GLBConj g J₁) (hae : a ∈ Cg e) (ha5 : a ^ 5 = 1) (ha1 : a ≠ 1)
    (hcase : a ∉ Subgroup.normalizer (J₁ : Set G) ∨ ∀ q ∈ barX 5 (Cg e) J₁,
      QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a, hae⟩ * q =
        q * QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a, hae⟩) :
    Subgroup.center (barOf 5 J₁) = ⊥ ∧ IsAltType 5 (barOf 5 J₁) := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hBel : IsElemAbelian 5 (Subgroup.zpowers a) := Claims1116.isElemAbelian_zpowers ha5
  have hBC : Subgroup.zpowers a ≤ Cg e := (Subgroup.zpowers_le).2 hae
  have hL' : GLAPComponent 5 (Cg e ⊓ Subgroup.centralizer ({a} : Set G)) L := by
    rw [Claims1110d.cg2_eq_inf, inf_comm] at hL
    exact hL
  have hle : barX 5 (Cg e) L ≤ barX 5 (Cg e) (⨆ y ∈ Subgroup.zpowers a, GLBConj y J₁) :=
    Claims1116.bar_mono hLI
  obtain ⟨π, hπs, hπk, -⟩ := Inputs183eqv.input18_3_eqv_holds G 5 hp (by norm_num) (Cg e) J₁
    (Subgroup.zpowers a) hJ₁ hBel hBC a (Subgroup.mem_zpowers a) ha1 hae hcase L hL' hle
  obtain ⟨ψ⟩ := hLA5
  have hZS : Subgroup.center (barOf 5 L) = ⊥ := center_eq_bot_of_isAltType_five ⟨ψ⟩
  have hker : π.ker = Subgroup.center (barOf 5 J₁) := by
    refine le_antisymm hπk fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hzc : π z ∈ Subgroup.center (barOf 5 L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨v, rfl⟩ := hπs w
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) v]
    rw [hZS, Subgroup.mem_bot] at hzc
    exact hzc
  have e₁ : (barOf 5 J₁ ⧸ Subgroup.center (barOf 5 J₁)) ≃* barOf 5 L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective π hπs)
  have hZ : Subgroup.center (barOf 5 J₁) = ⊥ :=
    SchurFacts.inputSchurFiveSeven_holds hp (by norm_num) hJ₁ (Or.inl ⟨e₁.trans ψ⟩)
  have hinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hZ]
  exact ⟨hZ, ⟨(MulEquiv.ofBijective π ⟨hinj, hπs⟩).trans ψ⟩⟩

theorem centralizes_barX_of_barAut_eq_one {e a : G} {J₁ : Subgroup G} (hJ₁ : GLAPComponent 5 (Cg e) J₁)
    (hae : a ∈ Cg e) (ha : a ∈ Subgroup.normalizer (J₁ : Set G)) (hx : barAut 5 J₁ ⟨a, ha⟩ = 1) :
    ∀ q ∈ barX 5 (Cg e) J₁,
      QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a, hae⟩ * q =
        q * QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a, hae⟩ := by
  rintro _ ⟨⟨y, hyC⟩, hy, rfl⟩
  have hyJ : y ∈ J₁ := Subgroup.mem_subgroupOf.1 hy
  have h1 := Claims1110d.comm_mem_core_of_barAut_eq_one ha hx y hyJ
  have h2 := CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 5 hJ₁.2.1 h1
  obtain ⟨hzC, hz⟩ := (mem_gLAPPrimeCoreOf_iff 5 (Cg e) _).1 h2
  have h3 : QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a * y * a⁻¹ * y⁻¹, hzC⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).2 hz
  have e1 : (⟨a * y * a⁻¹ * y⁻¹, hzC⟩ : ↥(Cg e)) = ⟨a, hae⟩ * ⟨y, hyC⟩ * ⟨a, hae⟩⁻¹ * ⟨y, hyC⟩⁻¹ :=
    Subtype.ext rfl
  rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv] at h3
  calc QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a, hae⟩ *
        QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨y, hyC⟩
      = (QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a, hae⟩ *
          QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨y, hyC⟩ *
          (QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a, hae⟩)⁻¹ *
          (QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨y, hyC⟩)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨y, hyC⟩ *
          QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) ⟨a, hae⟩) := by group
    _ = _ := by rw [h3, one_mul]

end Eqv

section Tools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A) (H : Subgroup G) :
    IsElemAbelian p (A.subgroupOf H) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · have hx : ((x : ↥H) : G) ∈ A := Subgroup.mem_subgroupOf.1 x.2
    have hy : ((y : ↥H) : G) ∈ A := Subgroup.mem_subgroupOf.1 y.2
    simpa using hA.comm hx hy
  · have hx' : ((x : ↥H) : G) ∈ A := Subgroup.mem_subgroupOf.1 hx
    simpa using hA.2 _ hx'

theorem card_sup_mul_card_inf_of_commute' (L R : Subgroup G)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup G) * Nat.card (L ⊓ R : Subgroup G) = Nat.card L * Nat.card R := by
  let μ : L × R →* G := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]; exact this

omit [Finite G] in
theorem exists_pGroup_le_map_eq {B : Type*} [Group B] [Finite G] {p : ℕ} [Fact p.Prime] (π : G →* B)
    {W : Subgroup G} {Q : Subgroup B} (hQ : IsPGroup p Q) (hQW : Q ≤ W.map π) :
    ∃ P : Subgroup G, P ≤ W ∧ IsPGroup p P ∧ P.map π = Q := by
  let φ : ↥W →* ↥(W.map π) := (π.comp W.subtype).codRestrict (W.map π) fun w => ⟨w, w.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hQ' : IsPGroup p ↥(Q.subgroupOf (W.map π)) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQW).symm
  obtain ⟨P', -, hP'p, hP'⟩ := Claims1116.exists_pGroup_map_eq φ hφ hQ' (E := ⊥) IsPGroup.of_bot
    (by rw [Subgroup.map_bot]; exact bot_le)
  refine ⟨P'.map W.subtype, ?_, hP'p.map _, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · have e1 : (P'.map W.subtype).map π = (P'.map φ).map (W.map π).subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [e1, hP', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQW]

theorem le_M_of_seitz (hSeitz : Claims1116.Input23_10) (h111 : Prop111Statement) {m : ℕ}
    {B M E A : Subgroup G} (h : Sec11 G m 5 B M E A) {e : G} (heA : e ∈ A) (he1 : e ≠ 1)
    {J₁ B₁ : Subgroup G} (hJ₁ : GLAPComponent 5 (Cg e) J₁) (hB₁D : inD 5 M B₁)
    (hB₁el : IsElemAbelian 5 B₁) (hB₁c : Nat.card B₁ = 5 ^ m) (hm4 : 4 ≤ m) (hB₁C : B₁ ≤ Cg e)
    (hB₁N : B₁ ≤ Subgroup.normalizer (J₁ : Set G))
    (hchev : IsChevSimple 2 (barOf 5 J₁ ⧸ Subgroup.center (barOf 5 J₁)))
    (hexc : ¬ Claims1116.Exc5 (barOf 5 J₁ ⧸ Subgroup.center (barOf 5 J₁))) : J₁ ≤ M := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨B₃, ⟨-, hB₃el, hB₃c⟩, hB₃B₁⟩ := Claims1110.exists_isEkIn_le (k := 3) (X := ⊤) le_top hB₁el
    (by rw [hB₁c]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have hB₃C : B₃ ≤ Cg e := hB₃B₁.trans hB₁C
  have hB₃N : B₃ ≤ Subgroup.normalizer (J₁ : Set G) := hB₃B₁.trans hB₁N
  set O := GLAPPrimeCoreOf 5 (Cg e) with hO
  have hOM : O ≤ M := h111 h heA he1
  have hOcop : Nat.Coprime 5 (Nat.card ↥O) := by
    have h1 : Nat.card ↥O = Nat.card ↥(GLAPPrimeCore 5 ↥(Cg e)) :=
      Subgroup.card_map_of_injective (Cg e).subtype_injective
    rw [h1]
    exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥(Cg e)
  have hCeO : Cg e ≤ Subgroup.normalizer (O : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => conj_mem_gLAPPrimeCoreOf 5 (Cg e) hx hy,
      fun hy => by
        have := conj_mem_gLAPPrimeCoreOf 5 (Cg e) ((Cg e).inv_mem hx) hy
        simpa [mul_assoc] using this⟩
  have hB₃p : IsPGroup 5 ↥B₃ := Claims1110.isPGroup_of_elemAb hB₃el
  set π := QuotientGroup.mk' (GLAPPrimeCore 5 ↥(Cg e)) with hπ
  have hBbN : barX 5 (Cg e) B₃ ≤
      Subgroup.normalizer (barX 5 (Cg e) J₁ : Set (↥(Cg e) ⧸ GLAPPrimeCore 5 ↥(Cg e))) := by
    rintro _ ⟨⟨b, hbC⟩, hb, rfl⟩
    exact Claims1116.bar_mem_normalizer hJ₁.1 hbC
      (gLBConj_eq_of_mem_normalizer (hB₃N (Subgroup.mem_subgroupOf.1 hb)))
  have hBbc : Nat.card (barX 5 (Cg e) B₃) = 5 ^ 3 := by
    rw [Claims1116.card_barX_of_isPGroup hp hB₃p hB₃C, hB₃c]
  have hgen := hSeitz hp (by norm_num) (by norm_num : (2 : ℕ) ≠ 5) hJ₁ hB₃C hB₃el hB₃c.le hchev
    (by
      rintro ⟨-, h3 | ⟨-, hx⟩⟩
      · norm_num at h3
      · exact hexc hx)
  refine Claims1116.le_of_bar_le hJ₁.1 hOM (hgen.trans (iSup₂_le fun F hF => ?_))
  obtain ⟨hFle, hFcard⟩ := hF
  rw [inf_eq_left.2 hBbN, hBbc] at hFcard
  have hFB : F ≤ barX 5 (Cg e) B₃ := hFle.trans inf_le_left
  set V : Subgroup G := B₃ ⊓ (F.comap π).map (Cg e).subtype with hV
  have hVB : V ≤ B₃ := inf_le_left
  have hmemV : ∀ (v : G) (hv : v ∈ V), π ⟨v, hB₃C hv.1⟩ ∈ F := by
    rintro v ⟨-, ⟨w, hw, rfl⟩⟩
    exact hw
  have hFV : Nat.card F ≤ Nat.card V := by
    refine Nat.card_le_card_of_surjective (fun v => ⟨π ⟨v, hB₃C v.2.1⟩, hmemV v v.2⟩) ?_
    rintro ⟨f, hf⟩
    obtain ⟨w, hw, rfl⟩ := hFB hf
    exact ⟨⟨w, Subgroup.mem_subgroupOf.1 hw, ⟨w, hf, rfl⟩⟩, rfl⟩
  have hV2 : 5 ^ 2 ≤ Nat.card V := by omega
  have hVel : IsElemAbelian 5 V := Claims1116.isElemAbelian_of_le hB₃el hVB
  obtain ⟨E₀, hE₀, hE₀V⟩ := Claims1110.exists_isEkIn_le (k := 2) (X := ⊤) le_top hVel hV2
  have hE₀rk : 2 ≤ CFSG.Open.pRank 5 E₀ :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE₀.2.1 hE₀.2.2
  have hNE₀ : Subgroup.normalizer (E₀ : Set G) ≤ M :=
    (l1110_normalizer_le_glbCore ((hE₀V.trans hVB).trans hB₃B₁) hE₀rk).trans hB₁D.2.clause_d
  rintro _ ⟨⟨⟨z, hzC⟩, hz, rfl⟩, hq⟩
  have hcomm : ∀ v ∈ V, v * z * v⁻¹ * z⁻¹ ∈ O := by
    intro v hv
    have hvF := hmemV v hv
    have h1 : π ⟨v, hB₃C hv.1⟩ * π ⟨z, hzC⟩ = π ⟨z, hzC⟩ * π ⟨v, hB₃C hv.1⟩ :=
      (Subgroup.mem_centralizer_iff.1 hq) _ hvF
    have h2 : π (⟨v, hB₃C hv.1⟩ * ⟨z, hzC⟩ * ⟨v, hB₃C hv.1⟩⁻¹ * ⟨z, hzC⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    exact (mem_gLAPPrimeCoreOf_iff 5 (Cg e) _).2 ⟨_, (QuotientGroup.eq_one_iff _).1 h2⟩
  obtain ⟨c, hc, o, ho, hzco⟩ := Claims1110b.exists_fixed_mul (Claims1110.isPGroup_of_elemAb hVel)
    (hVB.trans hB₃C) hCeO hOcop hzC hcomm
  have hcN : c ∈ Subgroup.normalizer (E₀ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hE₀V hc)
  have hzM : z ∈ M := by
    rw [hzco]
    exact M.mul_mem (hNE₀ hcN) (hOM ho)
  exact ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.2 hzM, rfl⟩

theorem comm_of_U5 {J₁ B₁ F R : Subgroup G} {m : ℕ} (hRp : IsPGroup 5 ↥R)
    (hrank : ∀ X : Subgroup G, X ≤ R → IsElemAbelian 5 X → Nat.card X ≤ 5 ^ m)
    (hB₁R : B₁ ≤ R) (hB₁N : B₁ ≤ Subgroup.normalizer (J₁ : Set G)) (hB₁el : IsElemAbelian 5 B₁)
    (hB₁c : Nat.card B₁ = 5 ^ m) (hFR : F ≤ R) (hFJ : F ≤ J₁) (hFel : IsElemAbelian 5 F)
    (hFc : Nat.card F = 5 ^ 3 * Nat.card (omegaOne 5 (Subgroup.center (barOf 5 J₁))))
    (hcl : ∀ P : Subgroup (MulAut (barOf 5 J₁)), IsPGroup 5 P →
      ∀ E : Subgroup (MulAut (barOf 5 J₁)), E ≤ P → IsElemAbelian 5 E → 5 ^ 3 ≤ Nat.card E →
      ∀ F : Subgroup (barOf 5 J₁), IsElemAbelian 5 F →
        F.map (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁)) ≤ P →
        5 ^ 3 ≤ Nat.card (F.map (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁))) →
        ∀ β ∈ E, ∀ f ∈ F, β f = f) :
    ∀ b ∈ B₁, ∀ f ∈ F, b * f = f * b := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set N := Subgroup.normalizer (J₁ : Set G) with hN
  set πJ : ↥J₁ →* barOf 5 J₁ := QuotientGroup.mk' (GLAPPrimeCore 5 ↥J₁) with hπJ
  set Z1 := omegaOne 5 (Subgroup.center (barOf 5 J₁)) with hZ1
  have hcore : ∀ z ∈ R, z ∈ GLAPPrimeCoreOf 5 J₁ → z = 1 := fun z hz hzO => by
    obtain ⟨k, hk⟩ := Claims1110d.exists_pow_eq_one_of_isPGroup hRp hz
    exact Claims1110d.eq_one_of_mem_core hzO hk
  have hinj : ∀ (u v : G) (hu : u ∈ J₁) (hv : v ∈ J₁), u ∈ R → v ∈ R →
      πJ ⟨u, hu⟩ = πJ ⟨v, hv⟩ → u = v := by
    intro u v hu hv huR hvR huv
    have h1 : (⟨u, hu⟩ : ↥J₁)⁻¹ * ⟨v, hv⟩ ∈ GLAPPrimeCore 5 ↥J₁ := QuotientGroup.eq.1 huv
    have h2 : u⁻¹ * v ∈ GLAPPrimeCoreOf 5 J₁ :=
      (mem_gLAPPrimeCoreOf_iff 5 J₁ _).2 ⟨J₁.mul_mem (J₁.inv_mem hu) hv, h1⟩
    have h3 := hcore _ (R.mul_mem (R.inv_mem huR) hvR) h2
    calc u = u * (u⁻¹ * v) := by rw [h3, mul_one]
      _ = v := by group
  set φ : ↥B₁ →* MulAut (barOf 5 J₁) := (barAut 5 J₁).comp (Subgroup.inclusion hB₁N) with hφ
  set Eb : Subgroup (MulAut (barOf 5 J₁)) := φ.range with hEb
  set C : Subgroup G := φ.ker.map B₁.subtype with hC
  have hCB : C ≤ B₁ := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hmemC : ∀ (c : G) (hc : c ∈ C), barAut 5 J₁ ⟨c, hB₁N (hCB hc)⟩ = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    exact hc
  have hCcard : Nat.card C = Nat.card φ.ker := Subgroup.card_map_of_injective B₁.subtype_injective
  have hCel : IsElemAbelian 5 C := Claims1116.isElemAbelian_of_le hB₁el hCB
  have hCF : ∀ c ∈ C, ∀ f ∈ F, c * f = f * c := by
    intro c hc f hf
    have h1 := Claims1110d.comm_mem_core_of_barAut_eq_one (hB₁N (hCB hc)) (hmemC c hc) f (hFJ hf)
    have hcR : c ∈ R := hB₁R (hCB hc)
    have hfR : f ∈ R := hFR hf
    have h2 := hcore _ (R.mul_mem (R.mul_mem (R.mul_mem hcR hfR) (R.inv_mem hcR)) (R.inv_mem hfR)) h1
    calc c * f = (c * f * c⁻¹ * f⁻¹) * (f * c) := by group
      _ = f * c := by rw [h2, one_mul]
  have hT := card_sup_mul_card_inf_of_commute' C F hCF
  have hTel : IsElemAbelian 5 (C ⊔ F) := CFSG.Open.IsElemAbelian.sup_of_commute hCel hFel hCF
  have hTm : Nat.card ↥(C ⊔ F) ≤ 5 ^ m := hrank _ (sup_le (hCB.trans hB₁R) hFR) hTel
  have hCFZ : Nat.card ↥(C ⊓ F) ≤ Nat.card Z1 := by
    refine Nat.card_le_card_of_injective (fun z => ⟨πJ ⟨z, hFJ z.2.2⟩, ?_⟩) ?_
    · have h1 := hmemC z z.2.1
      have h2 : barAut 5 J₁ ⟨z, Subgroup.le_normalizer (hFJ z.2.2)⟩ =
          MulAut.conj (πJ ⟨z, hFJ z.2.2⟩) := Claims1110.barAut_of_mem (hFJ z.2.2)
      have h3 : MulAut.conj (πJ ⟨z, hFJ z.2.2⟩) = 1 := by
        rw [← h2]
        exact h1
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · rw [Subgroup.mem_center_iff]
        intro w
        have h4 := congrArg (fun ψ : MulAut (barOf 5 J₁) => ψ w) h3
        simp only [MulAut.conj_apply, MulAut.one_apply] at h4
        exact (mul_inv_eq_iff_eq_mul.1 h4).symm
      · rw [← map_pow]
        have h5 : (⟨(z : G), hFJ z.2.2⟩ : ↥J₁) ^ 5 = 1 := Subtype.ext (by simpa using hFel.2 _ z.2.2)
        rw [h5, map_one]
    · intro z₁ z₂ h12
      apply Subtype.ext
      exact hinj _ _ _ _ (hFR z₁.2.2) (hFR z₂.2.2) (congrArg Subtype.val h12)
  have hZ1pos : 0 < Nat.card Z1 := Nat.card_pos
  have hCFpos : 0 < Nat.card ↥(C ⊓ F) := Nat.card_pos
  have hT3 : Nat.card C * 5 ^ 3 ≤ Nat.card ↥(C ⊔ F) := by
    have h1 : Nat.card C * 5 ^ 3 * Nat.card ↥(C ⊓ F) ≤ Nat.card ↥(C ⊔ F) * Nat.card ↥(C ⊓ F) := by
      rw [hT, hFc]
      calc Nat.card C * 5 ^ 3 * Nat.card ↥(C ⊓ F) ≤ Nat.card C * 5 ^ 3 * Nat.card Z1 :=
            Nat.mul_le_mul_left _ hCFZ
        _ = Nat.card C * (5 ^ 3 * Nat.card Z1) := by ring
    exact Nat.le_of_mul_le_mul_right h1 hCFpos
  have hE3 : 5 ^ 3 ≤ Nat.card Eb := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hB₁c] at h1
    have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
    have h2 : Nat.card φ.ker * 5 ^ 3 ≤ Nat.card φ.ker * Nat.card Eb := by
      rw [h1, ← hCcard]
      exact hT3.trans hTm
    exact Nat.le_of_mul_le_mul_left h2 hkpos
  have hEbel : IsElemAbelian 5 Eb := by
    have hTop : IsElemAbelian 5 (⊤ : Subgroup ↥B₁) := by
      have := isElemAbelian_subgroupOf hB₁el B₁
      rwa [Subgroup.subgroupOf_self] at this
    rw [hEb, MonoidHom.range_eq_map]
    exact CFSG.SectionRank.isElemAbelian_map hTop φ
  have hTN : B₁ ⊔ F ≤ N := sup_le hB₁N (hFJ.trans Subgroup.le_normalizer)
  have hTR : B₁ ⊔ F ≤ R := sup_le hB₁R hFR
  set P : Subgroup (MulAut (barOf 5 J₁)) := ((B₁ ⊔ F).subgroupOf N).map (barAut 5 J₁) with hP
  have hPp : IsPGroup 5 P :=
    ((hRp.to_le hTR).of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm).map _
  have hEbP : Eb ≤ P := by
    rintro _ ⟨b, rfl⟩
    exact ⟨Subgroup.inclusion hB₁N b, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left b.2), rfl⟩
  set Fb : Subgroup (barOf 5 J₁) := (F.subgroupOf J₁).map πJ with hFb
  have hFbel : IsElemAbelian 5 Fb := CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hFel J₁) πJ
  have hFbP : Fb.map (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁)) ≤ P := by
    rintro _ ⟨_, ⟨⟨f, hfJ⟩, hf, rfl⟩, rfl⟩
    have hf' : f ∈ F := Subgroup.mem_subgroupOf.1 hf
    show MulAut.conj (πJ ⟨f, hfJ⟩) ∈ P
    have e1 : MulAut.conj (πJ ⟨f, hfJ⟩) = barAut 5 J₁ ⟨f, Subgroup.le_normalizer hfJ⟩ :=
      (Claims1110.barAut_of_mem hfJ).symm
    rw [e1]
    exact ⟨⟨f, Subgroup.le_normalizer hfJ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hf'), rfl⟩
  have hFbcard : Nat.card Fb = Nat.card F := by
    have hi : Function.Injective (πJ.comp (F.subgroupOf J₁).subtype) := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      exact hinj _ _ (u : ↥J₁).2 (v : ↥J₁).2 (hFR (Subgroup.mem_subgroupOf.1 u.2))
        (hFR (Subgroup.mem_subgroupOf.1 v.2)) huv
    have h1 : (πJ.comp (F.subgroupOf J₁).subtype).range = Fb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFJ).toEquiv
  have hFb3 : 5 ^ 3 ≤ Nat.card (Fb.map (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁))) := by
    have h1 := card_map_mul_card_inf_ker (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁)) Fb
    have h2 : Fb ⊓ (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁)).ker ≤ Z1 := by
      intro u hu
      obtain ⟨huF, huk⟩ := Subgroup.mem_inf.1 hu
      refine Subgroup.subset_closure ⟨?_, hFbel.2 u huF⟩
      rw [Subgroup.mem_center_iff]
      intro w
      have h4 := congrArg (fun ψ : MulAut (barOf 5 J₁) => ψ w) (MonoidHom.mem_ker.1 huk)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h4
      exact (mul_inv_eq_iff_eq_mul.1 h4).symm
    have h3 := Subgroup.card_le_of_le h2
    rw [hFbcard, hFc] at h1
    have h4 : 5 ^ 3 * Nat.card Z1 ≤
        Nat.card (Fb.map (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁))) * Nat.card Z1 := by
      rw [← h1]
      exact Nat.mul_le_mul_left _ h3
    exact Nat.le_of_mul_le_mul_right h4 hZ1pos
  have hfix := hcl P hPp Eb hEbP hEbel hE3 Fb hFbel hFbP hFb3
  intro b hb f hf
  have hbN : b ∈ N := hB₁N hb
  have hbf : b * f * b⁻¹ ∈ J₁ := (Subgroup.mem_normalizer_iff.1 hbN f).1 (hFJ hf)
  have h1 := hfix (φ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩ (πJ ⟨f, hFJ hf⟩)
    ⟨⟨f, hFJ hf⟩, Subgroup.mem_subgroupOf.2 hf, rfl⟩
  have h2 := CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk 5 J₁ ⟨b, hbN⟩ ⟨f, hFJ hf⟩
  have h3 : πJ ⟨b * f * b⁻¹, hbf⟩ = πJ ⟨f, hFJ hf⟩ := by
    rw [← h1]
    exact h2.symm
  have hbR : b ∈ R := hB₁R hb
  have hfR : f ∈ R := hFR hf
  have h4 := hinj _ _ hbf (hFJ hf) (R.mul_mem (R.mul_mem hbR hfR) (R.inv_mem hbR)) hfR h3
  calc b * f = (b * f * b⁻¹) * b := by group
    _ = f * b := by rw [h4]

end Tools

section ExclU

variable {G : Type} [Group G] [Finite G]

theorem false_of_isUpType (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (hSeitz : Claims1116.Input23_10)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 5 B M E A a K)
    {R : Subgroup G} (hR : IsSylowIn 5 M R) {e : G} (heA : e ∈ A) (he1 : e ≠ 1) (hRC : R ≤ Cg e)
    (ha5 : a ^ 5 = 1) {J₁ : Subgroup G} (hJ₁ : GLAPComponent 5 (Cg e) J₁)
    (hT : IsSylowIn 5 J₁ (R ⊓ J₁)) (ha : a ∈ Subgroup.normalizer (J₁ : Set G)) {k : ℕ} (hk : 1 ≤ k)
    (hchev : IsChevSimple 2 (barOf 5 J₁ ⧸ Subgroup.center (barOf 5 J₁)))
    (hexc : ¬ Claims1116.Exc5 (barOf 5 J₁ ⧸ Subgroup.center (barOf 5 J₁)))
    {F : Subgroup (barOf 5 J₁)} (hFfix : F ≤ Lemma1314.fixSub (barAut 5 J₁ ⟨a, ha⟩))
    (hFel : IsElemAbelian 5 F)
    (hFc : Nat.card F = 5 ^ (5 * k - 2) * Nat.card (omegaOne 5 (Subgroup.center (barOf 5 J₁))))
    (hcl : k = 1 → ∀ P : Subgroup (MulAut (barOf 5 J₁)), IsPGroup 5 P →
      ∀ E : Subgroup (MulAut (barOf 5 J₁)), E ≤ P → IsElemAbelian 5 E → 5 ^ 3 ≤ Nat.card E →
      ∀ F : Subgroup (barOf 5 J₁), IsElemAbelian 5 F →
        F.map (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁)) ≤ P →
        5 ^ 3 ≤ Nat.card (F.map (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁))) →
        ∀ β ∈ E, ∀ f ∈ F, β f = f) : False := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hRp : IsPGroup 5 ↥R := hR.2.1
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS.standing hS.bOne hS.pre
  have hBel : IsElemAbelian 5 B := hS.bOne.1.1
  obtain ⟨y₀, hy₀M, T, hTp, hTM, hRT, hBT⟩ :=
    exists_conj_le_pGroup' hR.1 hR.2.1 hBM (Claims1110.isPGroup_of_elemAb hBel)
  have hTR : T = R := hR.2.2 T hTM hTp hRT
  rw [hTR] at hBT
  set B₁ := GLBConj y₀ B with hB₁
  have hB₁D : inD 5 M B₁ := (lemma101_i_holds hS hy₀M (lemma101_ii_holds hS) h.pair.1.2.1).1
  have hB₁el : IsElemAbelian 5 B₁ := Claims1110.isElemAbelian_conj y₀ hBel
  have hB₁c : Nat.card ↥B₁ = 5 ^ m := by
    rw [hB₁, Claims1110.card_conj, hS.standing.card_eq hS.bOne]
  have hm4 : 4 ≤ m := hS.standing.four_le
  have hB₁C : B₁ ≤ Cg e := hBT.trans hRC
  have hB₁rk : CFSG.Open.pRank 5 B₁ = m := by
    have h1 := l1110_card_eq_pow_pRank hB₁el
    rw [hB₁c] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1).symm
  have hB₁rank : GLATwoLocalRank 5 ↥(Cg e) ≤ CFSG.Open.pRank 5 B₁ := by
    rw [hB₁rk]
    exact (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp _).trans
      hS.standing.rank_eq.le
  have hB₁N : B₁ ≤ Subgroup.normalizer (J₁ : Set G) := by
    by_contra hn
    have := (h112 G m 5 hS.standing (Cg e) B₁ J₁ hB₁el hB₁C hB₁rank hJ₁ hn).1
    norm_num at this
  have hJM : J₁ ≤ M := le_M_of_seitz hSeitz h111 h.toCex117Base.toSec11 heA he1 hJ₁ hB₁D hB₁el hB₁c
    hm4 hB₁C hB₁N hchev hexc
  have hrank : ∀ X : Subgroup G, X ≤ R → IsElemAbelian 5 X → Nat.card X ≤ 5 ^ m := by
    intro X hXR hXel
    obtain ⟨j, hj⟩ := (Claims1110.isPGroup_of_elemAb hXel).exists_card_eq
    have hj' : j ≤ GLATwoLocalRank 5 G :=
      Lemma116.le_twoLocalRank hp hS.pre.1.1 (hXR.trans hR.1) hXel hj
    rw [hS.standing.rank_eq] at hj'
    rw [hj]
    exact Nat.pow_le_pow_right (by norm_num) hj'
  set πJ : ↥J₁ →* barOf 5 J₁ := QuotientGroup.mk' (GLAPPrimeCore 5 ↥J₁) with hπJ
  have hfix := AltFacts3.fixedSub_barAut_eq_p hp ha5 ha
  have hFW : F ≤ ((J₁ ⊓ Cg a).subgroupOf J₁).map πJ := by
    have e1 : Lemma1314.fixSub (barAut 5 J₁ ⟨a, ha⟩) =
        CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub (barAut 5 J₁ ⟨a, ha⟩) :=
      Subgroup.ext fun _ => Iff.rfl
    rw [e1, hfix] at hFfix
    exact hFfix
  obtain ⟨P, hPW, hPp, hPF⟩ := exists_pGroup_le_map_eq πJ (Claims1110.isPGroup_of_elemAb hFel) hFW
  set F' : Subgroup G := P.map J₁.subtype with hF'
  have hF'J : F' ≤ J₁ := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hF'a : F' ≤ Cg a := by
    rintro _ ⟨u, hu, rfl⟩
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (hPW hu))).2
  have hF'p : IsPGroup 5 ↥F' := hPp.map _
  have hcoreJ : ∀ u : ↥J₁, u ∈ P → πJ u = 1 → u = 1 := by
    intro u hu hu1
    have hu' : (u : G) ∈ GLAPPrimeCoreOf 5 J₁ :=
      (mem_gLAPPrimeCoreOf_iff 5 J₁ _).2 ⟨u.2, (QuotientGroup.eq_one_iff _).1 hu1⟩
    obtain ⟨j, hj⟩ := hPp ⟨u, hu⟩
    have hj' : (u : G) ^ (5 ^ j) = 1 := by
      have := congrArg (fun w : ↥P => ((w : ↥J₁) : G)) hj
      simpa using this
    exact Subtype.ext (Claims1110d.eq_one_of_mem_core hu' hj')
  have hPFmem : ∀ u ∈ P, πJ u ∈ F := fun u hu => by
    rw [← hPF]
    exact ⟨u, hu, rfl⟩
  have hF'el : IsElemAbelian 5 F' := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨u, hu, hux⟩ := x.2
      obtain ⟨v, hv, hvy⟩ := y.2
      apply Subtype.ext
      show (x : G) * y = y * x
      rw [← hux, ← hvy]
      have hc : πJ (u * v * u⁻¹ * v⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hFel.comm (hPFmem u hu) (hPFmem v hv)]
        group
      have h1 := hcoreJ _ (P.mul_mem (P.mul_mem (P.mul_mem hu hv) (P.inv_mem hu)) (P.inv_mem hv)) hc
      have h2 : u * v = v * u := by
        calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
          _ = v * u := by rw [h1, one_mul]
      exact congrArg Subtype.val h2
    · rintro _ ⟨u, hu, rfl⟩
      have h5 : πJ (u ^ 5) = 1 := by
        rw [map_pow]
        exact hFel.2 _ (hPFmem u hu)
      have := hcoreJ _ (P.pow_mem hu 5) h5
      simpa using congrArg Subtype.val this
  have hF'c : Nat.card F' = Nat.card F := by
    have h1 : Nat.card F' = Nat.card P := Subgroup.card_map_of_injective J₁.subtype_injective
    have hi : Function.Injective (πJ.comp P.subtype) := by
      intro u v huv
      have h2 : πJ ((u : ↥J₁)⁻¹ * (v : ↥J₁)) = 1 := by
        have huv' : πJ (u : ↥J₁) = πJ (v : ↥J₁) := huv
        rw [map_mul, map_inv, huv', inv_mul_cancel]
      have h3 := hcoreJ _ (P.mul_mem (P.inv_mem u.2) v.2) h2
      apply Subtype.ext
      calc (u : ↥J₁) = (u : ↥J₁) * ((u : ↥J₁)⁻¹ * (v : ↥J₁)) := by rw [h3, mul_one]
        _ = v := by group
    have h2 : (πJ.comp P.subtype).range = F := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPF]
    rw [h1, ← h2]
    exact Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
  obtain ⟨y, hyJ, S, hSp, hSJ, hRS, hF'S⟩ :=
    exists_conj_le_pGroup' (inf_le_right : R ⊓ J₁ ≤ J₁) (hRp.to_le inf_le_left) hF'J hF'p
  have hSR : S = R ⊓ J₁ := hT.2.2 S hSJ hSp hRS
  rw [hSR] at hF'S
  have hyM : y ∈ M := hJM hyJ
  set F'' := GLBConj y F' with hF''
  have hF''R : F'' ≤ R := hF'S.trans inf_le_left
  have hF''J : F'' ≤ J₁ := hF'S.trans inf_le_right
  have hF''el : IsElemAbelian 5 F'' := Claims1110.isElemAbelian_conj y hF'el
  have hF''c : Nat.card F'' = Nat.card F := by rw [hF'', Claims1110.card_conj, hF'c]
  have hza : IsElemAbelian 5 (Subgroup.zpowers a) := Claims1116.isElemAbelian_zpowers ha5
  have hAel : IsElemAbelian 5 (Subgroup.zpowers a ⊔ F') := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute hza hF'el fun x hx f hf => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hfa : f * a = a * f := Subgroup.mem_centralizer_singleton_iff.1 (hF'a hf)
    exact (Commute.zpow_left (show Commute a f from hfa.symm) j).eq
  obtain ⟨A₁, hA₁sc, hA₁⟩ := Claims1110.exists_isSCp_top_above' hAel
  have haA₁ : a ∈ A₁ := hA₁ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hF'A₁ : F' ≤ A₁ := le_sup_right.trans hA₁
  have hZpos : 0 < Nat.card (omegaOne 5 (Subgroup.center (barOf 5 J₁))) := Nat.card_pos
  obtain ⟨D, U, hDD, hDel, hD3, hU, hUF'', hUD⟩ : ∃ D U : Subgroup G, inD 5 M D ∧ IsElemAbelian 5 D ∧
      5 ^ 3 ≤ Nat.card D ∧ IsEkIn 5 3 ⊤ U ∧ U ≤ F'' ∧ U ≤ Subgroup.centralizer (D : Set G) := by
    by_cases hk1 : k = 1
    · subst hk1
      have h53 : 5 * 1 - 2 = 3 := by norm_num
      have hF''c' : Nat.card F'' = 5 ^ 3 * Nat.card (omegaOne 5 (Subgroup.center (barOf 5 J₁))) := by
        rw [hF''c, hFc, h53]
      have hcomm := comm_of_U5 hRp hrank hBT hB₁N hB₁el hB₁c hF''R hF''J hF''el hF''c' (hcl rfl)
      have h3 : 5 ^ 3 ≤ Nat.card F'' := by
        rw [hF''c']
        exact Nat.le_mul_of_pos_right _ hZpos
      obtain ⟨U, hU, hUF⟩ := Claims1110.exists_isEkIn_le (k := 3) (X := ⊤) le_top hF''el h3
      refine ⟨B₁, U, hB₁D, hB₁el, ?_, hU, hUF, ?_⟩
      · rw [hB₁c]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact hcomm b hb u (hUF hu)
    · have h5 : 5 ^ 5 ≤ Nat.card F'' := by
        rw [hF''c, hFc]
        calc 5 ^ 5 ≤ 5 ^ (5 * k - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ 5 ^ (5 * k - 2) * Nat.card (omegaOne 5 (Subgroup.center (barOf 5 J₁))) :=
            Nat.le_mul_of_pos_right _ hZpos
      obtain ⟨E₅, hE₅, hE₅F⟩ := Claims1110.exists_isEkIn_le (k := 5) (X := R) hF''R hF''el h5
      obtain ⟨-, -, D, hDD, hE₅D⟩ := (lemma104_iv_holds hS h.pair hrk hR).1 E₅ hE₅
      obtain ⟨U, hU, hUE⟩ := Claims1110.exists_isEkIn_le (k := 3) (X := ⊤) le_top hE₅.2.1
        (by rw [hE₅.2.2]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
      have hDel : IsElemAbelian 5 D := hDD.1.1.2.1
      refine ⟨D, U, hDD, hDel, ?_, hU, hUE.trans hE₅F, ?_⟩
      · calc 5 ^ 3 = Nat.card U := hU.2.2.symm
          _ ≤ Nat.card D := Subgroup.card_le_of_le (hUE.trans hE₅D)
      · exact Claims1110.le_centralizer_of_le hDel (hUE.trans hE₅D) le_rfl
  set A₁' := GLBConj y A₁ with hA₁'
  have hA₁'sc : IsSCp 5 ⊤ A₁' := isSCp_gLBConj_of_mem (Subgroup.mem_top y) hA₁sc
  have hUA₁' : U ≤ A₁' := hUF''.trans (gLBConj_mono y hF'A₁)
  have hA₁'U : A₁' ≤ Subgroup.centralizer (U : Set G) :=
    Claims1110.le_centralizer_of_le hA₁'sc.2.1 le_rfl hUA₁'
  have hconn : IsKConnectedIn 5 (CFSG.Open.pRank 5 (E ⊓ A) + 1) ⊤ A₁' D := by
    rw [hrk]
    refine ⟨le_top, hA₁'sc.2.1, ?_, le_top, hDel, hD3, Or.inr ⟨U, U, hU, hU, hA₁'U,
      Relation.ReflTransGen.refl, hUD⟩⟩
    calc 5 ^ 3 = Nat.card ↥U := hU.2.2.symm
      _ ≤ Nat.card ↥A₁' := Subgroup.card_le_of_le hUA₁'
  have hA₁'D : inD 5 M A₁' := lemma104_iii_holds hS h.pair hA₁'sc hDD hconn
  have hA₁D : inD 5 M A₁ := by
    have := (lemma101_i_holds hS (M.inv_mem hyM) hA₁'D h.pair.1.2.1).1
    rwa [hA₁', gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at this
  exact h.notD ⟨A₁, hA₁D, haA₁⟩

end ExclU

section Single

variable {G : Type} [Group G] [Finite G]

theorem isKHat_barOf {m : ℕ} (hS : GLStanding G m 5) {e : G} (he1 : e ≠ 1) {J : Subgroup G}
    (hJ : GLAPComponent 5 (Cg e) J) : CFSG.LocalAnalysis.GLTheoremA.IsKHat (barOf 5 J) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq : CFSG.Open.IsQuasisimple (barOf 5 J) := Lemma1313.isQuasisimple_barOf_of_pComp hJ
  have hX : CFSG.Open.IsKGroup ↥(Cg e) :=
    hS.kProper.isKGroup (Cg e) (centralizer_singleton_ne_top hS he1)
  have hKG : CFSG.Open.IsKGroup (barOf 5 J) := (hX.of_le hJ.1).quotient _
  exact ⟨hq, CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' hKG hq⟩

theorem pumpup_of_single {e a : G} {J₁ L : Subgroup G} (hJ₁ : GLAPComponent 5 (Cg e) J₁)
    (hL : GLAPComponent 5 (Cg2 e a) L) (hLA5 : IsAltType 5 (barOf 5 L)) (hLJ : L ≤ J₁) (ha5 : a ^ 5 = 1)
    (ha : a ∈ Subgroup.normalizer (J₁ : Set G)) (hx1 : barAut 5 J₁ ⟨a, ha⟩ ≠ 1) :
    Lemma1314.PumpupVia 5 ↥(alternatingGroup (Fin 5)) (barOf 5 J₁) (barAut 5 J₁ ⟨a, ha⟩) := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hxp : (barAut 5 J₁ ⟨a, ha⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨a, ha⟩ : ↥(Subgroup.normalizer (J₁ : Set G))) ^ 5 = 1 := Subtype.ext (by simpa using ha5)
    rw [this, map_one]
  have hL' : GLAPComponent 5 (J₁ ⊓ Cg a) L := by
    have hle : J₁ ⊓ Cg a ≤ Cg2 e a := by
      rw [Claims1110d.cg2_eq_inf]
      exact le_inf inf_le_right (inf_le_left.trans hJ₁.1)
    have hLa : L ≤ Cg a := hL.1.trans (by rw [Claims1110d.cg2_eq_inf]; exact inf_le_left)
    exact glaPComponent_of_le hp hL (le_inf hLJ hLa) hle
  have hfix := AltFacts3.fixedSub_barAut_eq_p hp ha5 ha
  refine ⟨orderOf_eq_prime hxp hx1, barX 5 J₁ L, ?_, ?_⟩
  · have h := Prop115b.barX_glaPComponent_of_le hp (inf_le_left : J₁ ⊓ Cg a ≤ J₁) hL'
    have e1 : Lemma1314.fixSub (barAut 5 J₁ ⟨a, ha⟩) = barX 5 J₁ (J₁ ⊓ Cg a) := by
      rw [← hfix]
      rfl
    rw [e1]
    exact h
  · obtain ⟨ψ⟩ := hLA5
    exact ⟨(Prop115.barOfIso hLJ).symm.trans ψ⟩

theorem single_facts (hA5 : InputA5Up) (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (hSeitz : Claims1116.Input23_10)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 5 B M E A a K)
    {R : Subgroup G} (hR : IsSylowIn 5 M R) {e : G} (heA : e ∈ A) (he1 : e ≠ 1) (hRC : R ≤ Cg e)
    (ha5 : a ^ 5 = 1) {J₁ : Subgroup G} (hJ₁ : GLAPComponent 5 (Cg e) J₁)
    (hT : IsSylowIn 5 J₁ (R ⊓ J₁)) (ha : a ∈ Subgroup.normalizer (J₁ : Set G))
    (hx1 : barAut 5 J₁ ⟨a, ha⟩ ≠ 1) {L : Subgroup G} (hL : GLAPComponent 5 (Cg2 e a) L)
    (hLA5 : IsAltType 5 (barOf 5 L)) (hLJ : L ≤ J₁) :
    Subgroup.center (barOf 5 J₁) = ⊥ ∧ Claims1110d.OutRankLeOne (barOf 5 J₁) := by
  have hp : Nat.Prime 5 := by norm_num
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hKH := isKHat_barOf hS.standing he1 hJ₁
  have hO : GLAPPrimeCore 5 (barOf 5 J₁) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hpump := pumpup_of_single hJ₁ hL hLA5 hLJ ha5 ha hx1
  obtain ⟨h1, h2⟩ := hA5 (barOf 5 J₁) hKH hO _ hpump
  by_cases hU : ∃ k : ℕ, 1 ≤ k ∧ IsUpType (5 * k) 4 (barOf 5 J₁ ⧸ Subgroup.center (barOf 5 J₁))
  · obtain ⟨k, hk, hUk⟩ := hU
    obtain ⟨hchev, hexc, ⟨F, hFfix, hFel, -, hFc⟩, hcl⟩ := h2 k hk hUk
    exact (false_of_isUpType h119 h111 h112 hSeitz h hR heA he1 hRC ha5 hJ₁ hT ha hk hchev hexc
      hFfix hFel hFc hcl).elim
  · obtain ⟨hZ, hOut⟩ := h1 fun k hk hUk => hU ⟨k, hk, hUk⟩
    exact ⟨hZ, outRankLeOne_of_pRank hOut⟩

end Single

section Data

variable {G : Type} [Group G] [Finite G]

theorem exists_J1_data (hI1421 : Input14_21) (hF : Fi22Facts) (h119 : Lemma119Statement)
    (h111 : Prop111Statement) (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (h183 : Prop115.Input18_3Gen) (hSeitz : Claims1116.Input23_10) (hA5 : InputA5Up)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 5 B M E A a K)
    (hfi : IsSporType .Fi22 (barOf 5 K)) {R : Subgroup G} (hR : IsSylowIn 5 M R) (hEAR : E ⊔ A ≤ R)
    {e : G} (heZ : e ∈ omegaOne 5 (centerOf R)) (he1 : e ≠ 1) :
    ∃ J₁ : Subgroup G, GLAPComponent 5 (Cg e) J₁ ∧
      Claims1110b.IeOf K e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J₁ ∧
      Subgroup.center (barOf 5 J₁) = ⊥ ∧ Claims1110d.OutRankLeOne (barOf 5 J₁) ∧
      (a ∉ Subgroup.normalizer (J₁ : Set G) → IsAltType 5 (barOf 5 J₁)) := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hZle : omegaOne 5 (centerOf R) ≤ E ⊓ A :=
    le_inf (l1110_omegaOne_centerOf_le hsc.1 (le_sup_left.trans hEAR))
      (l1110_omegaOne_centerOf_le hsc.2 (le_sup_right.trans hEAR))
  have heEA : e ∈ E ⊓ A := hZle heZ
  have heA : e ∈ A := (Subgroup.mem_inf.1 heEA).2
  have hRC : R ≤ Cg e := Claims1110c.le_cg_of_mem_omegaOne heZ
  have hRG : IsSylowIn 5 ⊤ R := (lemma104_iv_holds hS h.pair hrk hR).2.2
  have hRCe : IsSylowIn 5 (Cg e) R := Claims1110d.isSylowIn_of_top hRG hRC
  have haA : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hAel : IsElemAbelian 5 A := Prop1116Design.sec11_isElemAbelian_A h.toCex117Base.toSec11
  have hae : a ∈ Cg e := Subgroup.mem_centralizer_singleton_iff.2 (hAel.comm haA heA)
  have ha5 : a ^ 5 = 1 := hAel.2 a haA
  obtain ⟨hKe1, hKeA5⟩ := Claims1110d.ke_facts hI1421 hF h119 h hfi heEA he1
  have hKe2 := Claims1110d.ke_glaPComponent_cg2 h hKe1
  obtain ⟨J₁, hJ₁, hI⟩ := Prop1116Design.exists_J1_of_input18_3 h183 h.toCex117Base.toSec11 haA ha1
    heEA he1 hKe2
  have hI' : Claims1110b.IeOf K e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J₁ := hI
  have hKeI : GLAPLayer 5 (K ⊓ Cg e) ≤ ⨆ g ∈ Subgroup.zpowers a, GLBConj g J₁ :=
    hI' ▸ Claims1110b.ke_le_ieOf K e
  have hIs : Claims1110c.IeStarOf K e = ⨆ c ∈ Cg e, GLBConj c J₁ := Claims1110d.ieStarOf_eq_iSup K hae hI'
  have hW : IsSylowIn 5 (Claims1110c.IeStarOf K e) (R ⊓ Claims1110c.IeStarOf K e) :=
    Claims1110d.isSylowIn_inf' hRCe (Claims1110c.ieStarOf_le_cg K e) (Claims1110c.cg_le_normalizer_ieStarOf K e)
  have hJ₁I : J₁ ≤ Claims1110c.IeStarOf K e := by
    rw [hIs]
    exact le_iSup₂_of_le 1 (Subgroup.one_mem _) (le_of_eq (gLBConj_one J₁).symm)
  have hIN : Claims1110c.IeStarOf K e ≤ Subgroup.normalizer (J₁ : Set G) := by
    have h1 := Claims1110d.iSup_conj_le_normalizer hp hJ₁ (Subgroup.one_mem (Cg e))
    rwa [gLBConj_one, ← hIs] at h1
  have hT' := Claims1110d.isSylowIn_inf' hW hJ₁I hIN
  have hT : IsSylowIn 5 J₁ (R ⊓ J₁) := by
    rwa [inf_assoc, inf_eq_right.2 hJ₁I] at hT'
  by_cases haN : a ∈ Subgroup.normalizer (J₁ : Set G)
  · by_cases hx1 : barAut 5 J₁ ⟨a, haN⟩ = 1
    · obtain ⟨hZ, hA5'⟩ := alt_of_eqv hJ₁ hKe2 hKeA5 hKeI hae ha5 ha1
        (Or.inr (centralizes_barX_of_barAut_eq_one hJ₁ hae haN hx1))
      exact ⟨J₁, hJ₁, hI', hZ, outRankLeOne_of_isAltType_five hA5', fun hn => absurd haN hn⟩
    · have hKeJ : GLAPLayer 5 (K ⊓ Cg e) ≤ J₁ := hKeI.trans (iSup₂_le fun g hg =>
        le_of_eq (gLBConj_eq_of_mem_normalizer ((Subgroup.zpowers_le.2 haN) hg)))
      obtain ⟨hZ, hOut⟩ := single_facts hA5 h119 h111 h112 hSeitz h hR heA he1 hRC ha5 hJ₁ hT haN hx1
        hKe2 hKeA5 hKeJ
      exact ⟨J₁, hJ₁, hI', hZ, hOut, fun hn => absurd haN hn⟩
  · obtain ⟨hZ, hA5'⟩ := alt_of_eqv hJ₁ hKe2 hKeA5 hKeI hae ha5 ha1 (Or.inl haN)
    exact ⟨J₁, hJ₁, hI', hZ, outRankLeOne_of_isAltType_five hA5', fun _ => hA5'⟩

theorem conj_mem_of_cRIe_isCyclic {K : Subgroup G} {e a : G} {J₁ : Subgroup G}
    (hJ₁ : GLAPComponent 5 (Cg e) J₁) (hae : a ∈ Cg e)
    (hI : Claims1110b.IeOf K e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J₁)
    {R : Subgroup G} (hR : IsSylowIn 5 (Cg e) R) (heR : e ∈ R) (he5 : e ^ 5 = 1)
    (heI : e ∉ Claims1110c.IeStarOf K e) (hcyc : IsCyclic ↥(Claims1110b.CRIe R K e)) :
    ∀ c ∈ Cg e, ∃ g ∈ Subgroup.zpowers a, GLBConj c J₁ = GLBConj g J₁ := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  intro c hc
  by_contra hne
  push Not at hne
  set I := Claims1110c.IeStarOf K e with hIdef
  have hIs : I = ⨆ c ∈ Cg e, GLBConj c J₁ := Claims1110d.ieStarOf_eq_iSup K hae hI
  set J' := GLBConj c J₁ with hJ'def
  have hJ' : GLAPComponent 5 (Cg e) J' := Claims1110d.glaPComponent_gLBConj_cg hc hJ₁
  have hW : IsSylowIn 5 I (R ⊓ I) := Claims1110d.isSylowIn_inf' hR (Claims1110c.ieStarOf_le_cg K e)
    (Claims1110c.cg_le_normalizer_ieStarOf K e)
  have hJ'I : J' ≤ I := by
    rw [hIs]
    exact le_iSup₂_of_le c hc le_rfl
  have hIN' : I ≤ Subgroup.normalizer (J' : Set G) := by
    have h := Claims1110d.iSup_conj_le_normalizer hp hJ₁ hc
    rwa [← hIs] at h
  have hWL : IsSylowIn 5 J' (R ⊓ I ⊓ J') := Claims1110d.isSylowIn_inf' hW hJ'I hIN'
  have hcard := Claims1110.card_of_isSylowIn hWL
  have hdvd : 5 ∣ Nat.card ↥(R ⊓ I ⊓ J') := by
    rw [hcard]
    have h1 : (Nat.card J').factorization 5 ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne'
        (Claims1110d.prime_dvd_card_of_glaPComponent hp hJ')).ne'
    exact dvd_pow_self 5 h1
  obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := ↥(R ⊓ I ⊓ J')) 5 hdvd
  have hxo' : orderOf x = 5 := by rw [← hxo, Subgroup.orderOf_mk]
  have hxR : x ∈ R := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1
  have hxI : x ∈ I := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2
  have hxJ : x ∈ J' := (Subgroup.mem_inf.1 hx).2
  have hxC : x ∈ Cg e := hJ'.1 hxJ
  have hx5 : x ^ 5 = 1 := hxo' ▸ pow_orderOf_eq_one x
  have hxV : x ∈ Claims1110b.CRIe R K e := by
    refine (Claims1110b.mem_cRIe).2 ⟨hxR, hxC, ?_⟩
    have hIeC : Claims1110b.IeOf K e ≤ Cg e := Claims1110b.ieOf_le_cg K e
    have hz : Subgroup.zpowers x ≤ Cg e := (Subgroup.zpowers_le).2 hxC
    have h1 : Claims1110b.IeOf K e ≤ Claims1110d.centMod 5 (Cg e) (Subgroup.zpowers x) := by
      rw [hI]
      refine iSup₂_le fun g hg => ?_
      have hgC : g ∈ Cg e := (Subgroup.zpowers_le.2 hae) hg
      have hJg : GLAPComponent 5 (Cg e) (GLBConj g J₁) := Claims1110d.glaPComponent_gLBConj_cg hgC hJ₁
      have h2 : J' ≤ Claims1110d.centMod 5 (Cg e) (GLBConj g J₁) :=
        Claims1110d.le_centMod_of_ne hp hJg hJ' (hne g hg)
      have h3 : Subgroup.zpowers x ≤ Claims1110d.centMod 5 (Cg e) (GLBConj g J₁) :=
        (Subgroup.zpowers_le).2 (h2 hxJ)
      exact Claims1110d.le_centMod_comm hJg.1 h3
    have h4 : Subgroup.zpowers x ≤ Claims1110d.centMod 5 (Cg e) (Claims1110b.IeOf K e) :=
      Claims1110d.le_centMod_comm hz h1
    exact (Claims1110d.mem_centMod.1 (h4 (Subgroup.mem_zpowers x))).2
  have heV : e ∈ Claims1110b.CRIe R K e := by
    refine (Claims1110b.mem_cRIe).2 ⟨heR, Subgroup.mem_centralizer_singleton_iff.2 rfl, fun y hy => ?_⟩
    have hyC : y ∈ Cg e := Claims1110b.ieOf_le_cg K e hy
    have hye : y * e = e * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
    have h1 : e * y * e⁻¹ * y⁻¹ = 1 := by
      calc e * y * e⁻¹ * y⁻¹ = (y * e) * e⁻¹ * y⁻¹ := by rw [hye]
        _ = 1 := by group
    rw [h1]
    exact Subgroup.one_mem _
  have hen : e ∉ Subgroup.zpowers x := fun hm => heI ((Subgroup.zpowers_le.2 hxI) hm)
  have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
  have hcard2 := Claims1110.card_sup_zpowers hen he5 (fun y hy => by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute x e from hxe) j).eq)
  rw [Nat.card_zpowers, hxo'] at hcard2
  set T : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers e with hT
  have hTV : T ≤ Claims1110b.CRIe R K e := sup_le ((Subgroup.zpowers_le).2 hxV) ((Subgroup.zpowers_le).2 heV)
  have hTel : IsElemAbelian 5 T := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute (Claims1116.isElemAbelian_zpowers hx5)
      (Claims1116.isElemAbelian_zpowers he5) fun u hu w hw => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact (Commute.zpow_zpow (show Commute x e from hxe) i j).eq
  set T' : Subgroup ↥(Claims1110b.CRIe R K e) := T.subgroupOf (Claims1110b.CRIe R K e) with hT'
  haveI : IsCyclic ↥(Claims1110b.CRIe R K e) := hcyc
  have hT'card : Nat.card ↥T' = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTV).toEquiv
  have h5 := Claims1110b.card_le_of_isCyclic_of_pow (T := T') inferInstance (fun t ht => Subtype.ext
    (by rw [Subgroup.coe_pow, OneMemClass.coe_one]; exact hTel.2 _ (Subgroup.mem_subgroupOf.1 ht)))
  rw [hT'card, hcard2] at h5
  norm_num at h5

end Data

section Main

theorem ieLayerClaim_of (hI1421 : Input14_21) (hF : Fi22Facts) (h119 : Lemma119Statement)
    (h183 : Prop115.Input18_3Gen) : Claims1110b.IeLayerClaim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR e heZ he1
  obtain ⟨rfl, hfi⟩ := hb
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  have hZle : omegaOne 5 (centerOf R) ≤ E ⊓ A :=
    le_inf (l1110_omegaOne_centerOf_le hsc.1 (le_sup_left.trans hEAR))
      (l1110_omegaOne_centerOf_le hsc.2 (le_sup_right.trans hEAR))
  have heEA : e ∈ E ⊓ A := hZle heZ
  have heA : e ∈ A := (Subgroup.mem_inf.1 heEA).2
  have hAel : IsElemAbelian 5 A := Prop1116Design.sec11_isElemAbelian_A h.toCex117Base.toSec11
  have hae : a ∈ Cg e := Subgroup.mem_centralizer_singleton_iff.2 (hAel.comm h.ha.1 heA)
  obtain ⟨hKe1, -⟩ := Claims1110d.ke_facts hI1421 hF h119 h hfi heEA he1
  have hKe2 := Claims1110d.ke_glaPComponent_cg2 h hKe1
  obtain ⟨J₁, hJ₁, hI⟩ := Prop1116Design.exists_J1_of_input18_3 h183 h.toCex117Base.toSec11 h.ha.1 h.ha.2
    heEA he1 hKe2
  refine ⟨{L | ∃ g ∈ Subgroup.zpowers a, L = GLBConj g J₁}, ?_, ?_⟩
  · rintro L ⟨g, hg, rfl⟩
    exact Claims1110d.glaPComponent_gLBConj_cg ((Subgroup.zpowers_le.2 hae) hg) hJ₁
  · have hI' : Claims1110b.IeOf K e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J₁ := hI
    rw [hI']
    apply le_antisymm
    · exact iSup₂_le fun g hg => le_sSup ⟨g, hg, rfl⟩
    · exact sSup_le fun L ⟨g, hg, hL⟩ => hL ▸ le_iSup₂_of_le g hg le_rfl

theorem ieStarClaim_of (hI1421 : Input14_21) (hF : Fi22Facts) (h119 : Lemma119Statement)
    (h111 : Prop111Statement) (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2)
    (h183 : Prop115.Input18_3Gen) (hSeitz : Claims1116.Input23_10) (hA5 : InputA5Up) :
    Claims1110c.IeStarClaim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR e heZ he1
  obtain ⟨rfl, hfi⟩ := hb
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨J₁, hJ₁, hI, hZ, hOut, hA5'⟩ :=
    exists_J1_data hI1421 hF h119 h111 h112 h183 hSeitz hA5 h hfi hR hEAR heZ he1
  have hS := h.toCex117Base.toSec11.toSec10Fails
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hRC : R ≤ Cg e := Claims1110c.le_cg_of_mem_omegaOne heZ
  have hRG : IsSylowIn 5 ⊤ R := (lemma104_iv_holds hS h.pair hrk hR).2.2
  have hRCe : IsSylowIn 5 (Cg e) R := Claims1110d.isSylowIn_of_top hRG hRC
  have hsc := lemma104_ii_holds hS h.pair
  have hZle : omegaOne 5 (centerOf R) ≤ E ⊓ A :=
    le_inf (l1110_omegaOne_centerOf_le hsc.1 (le_sup_left.trans hEAR))
      (l1110_omegaOne_centerOf_le hsc.2 (le_sup_right.trans hEAR))
  have heA : e ∈ A := (Subgroup.mem_inf.1 (hZle heZ)).2
  have hAel : IsElemAbelian 5 A := Prop1116Design.sec11_isElemAbelian_A h.toCex117Base.toSec11
  have hae : a ∈ Cg e := Subgroup.mem_centralizer_singleton_iff.2 (hAel.comm h.ha.1 heA)
  have ha5 : a ^ 5 = 1 := hAel.2 a h.ha.1
  have he5 : e ^ 5 = 1 := hAel.2 e heA
  have heR : e ∈ R := Claims1110.centerOf_le' R (Claims1110.omegaOne_le' 5 _ heZ)
  have hIs : Claims1110c.IeStarOf K e = ⨆ c ∈ Cg e, GLBConj c J₁ :=
    Claims1110d.ieStarOf_eq_iSup K hae hI
  have hcomm_e : ∀ y ∈ Claims1110c.IeStarOf K e, e * y * e⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 5 (Cg e) := by
    intro y hy
    have hye : y * e = e * y :=
      Subgroup.mem_centralizer_singleton_iff.1 (Claims1110c.ieStarOf_le_cg K e hy)
    have h1 : e * y * e⁻¹ * y⁻¹ = 1 := by
      calc e * y * e⁻¹ * y⁻¹ = (y * e) * e⁻¹ * y⁻¹ := by rw [hye]
        _ = 1 := by group
    rw [h1]
    exact Subgroup.one_mem _
  have hi : e ∉ Claims1110c.IeStarOf K e := fun heI =>
    he1 (Claims1110d.eq_one_of_mem_ieStar hJ₁ hZ hIs (Subgroup.mem_centralizer_singleton_iff.2 rfl) heI
      hcomm_e (k := 1) (by rw [pow_one]; exact he5))
  have hsingle : (∀ c ∈ Cg e, GLBConj c J₁ = J₁) →
      Claims1110c.IeStarOf K e = J₁ ∧ Cg e ≤ Subgroup.normalizer (J₁ : Set G) := by
    intro hall
    refine ⟨?_, fun c hc => ?_⟩
    · rw [hIs]
      apply le_antisymm
      · exact iSup₂_le fun c hc => le_of_eq (hall c hc)
      · exact le_iSup₂_of_le 1 (Subgroup.one_mem _) (le_of_eq (gLBConj_one J₁).symm)
    · have h1 := hall c⁻¹ ((Cg e).inv_mem hc)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have : c * y * c⁻¹ ∈ GLBConj c⁻¹ J₁ := by
          rw [mem_gLBConj]
          simpa [mul_assoc] using hy
        rwa [h1] at this
      · intro hy
        have : y ∈ GLBConj c J₁ := mem_gLBConj.2 hy
        rwa [hall c hc] at this
  refine ⟨hi, ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨hxR, hxI⟩, hxC⟩ := hx
    obtain ⟨k, hk⟩ := Claims1110d.exists_pow_eq_one_of_isPGroup hR.2.1 hxR
    exact Subgroup.mem_bot.2
      (Claims1110d.eq_one_of_mem_ieStar hJ₁ hZ hIs (hRC hxR) hxI (Claims1110c.mem_cRIeStar.1 hxC).2.2 hk)
  ·
    intro hcyc F hFR hFel
    obtain ⟨hIJ, hN⟩ := hsingle (Claims1110d.conj_eq_of_isCyclic hJ₁ hZ hIs hRCe hcyc)
    refine Claims1110d.card_le_of_single hJ₁ hZ hIJ hN hRCe hOut hFR (fun x hx y hy => ?_)
      (fun x hx => ?_)
    · rw [hFel.comm hx hy]
      simp only [mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [hFel.2 x hx]
      exact Subgroup.one_mem _
  ·
    intro _ _ _ _ _ _ hKe _ X hWVX hXR hXc hX5
    have hLay : Claims1110b.IeLayerClaim := ieLayerClaim_of hI1421 hF h119 h183
    have hcycC : IsCyclic ↥(Claims1110b.CRIe R K e) := by
      by_contra hnc
      exact hKe ((Claims1110b.ke_le_ieOf K e).trans
        (Claims1110b.ieOf_le_M_of_not_isCyclic h119 h111 h112 hLay h ⟨rfl, hfi⟩ hR hEAR heZ he1 hnc))
    have hconj := conj_mem_of_cRIe_isCyclic hJ₁ hae hI hRCe heR he5 hi hcycC
    by_cases haN : a ∈ Subgroup.normalizer (J₁ : Set G)
    · have hall : ∀ c ∈ Cg e, GLBConj c J₁ = J₁ := by
        intro c hc
        obtain ⟨g, hg, hcg⟩ := hconj c hc
        rw [hcg]
        exact gLBConj_eq_of_mem_normalizer ((Subgroup.zpowers_le.2 haN) hg)
      obtain ⟨hIJ, hN⟩ := hsingle hall
      have h := Claims1110d.card_le_of_single hJ₁ hZ hIJ hN hRCe hOut hXR hXc hX5
      rwa [inf_eq_right.2 hWVX] at h
    · have hIa : Claims1110c.IeStarOf K e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J₁ := by
        rw [hIs]
        apply le_antisymm
        · refine iSup₂_le fun c hc => ?_
          obtain ⟨g, hg, hcg⟩ := hconj c hc
          rw [hcg]
          exact le_iSup₂_of_le g hg le_rfl
        · exact iSup₂_le fun g hg => le_iSup₂_of_le g ((Subgroup.zpowers_le.2 hae) hg) le_rfl
      exact Claims1110d.card_le_of_cycled hJ₁ hae ha5 (hA5' haN) hIa hconj hRCe hXR

theorem lemma1110CaseB_of_A5Up' (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (h183 : Prop115.Input18_3Gen)
    (hSeitz : Claims1116.Input23_10) (hA5 : InputA5Up) (hF : Fi22Facts)
    (hI : Claims1110.InputFi22OneClassFive) (hK0 : Claims1110b.Input24_2K0) (h6 : Claims1110b.Step6Claim) :
    Lemma1110CaseB := by
  intro G _ _ m p B M E A a K h hb h1 h2 h3 hI1421
  exact Claims1110c.lemma1110CaseB_of_ieStar h119 h111 hK0 hF hI
    (ieStarClaim_of hI1421 hF h119 h111 h112 h183 hSeitz hA5) h6 h hb h1 h2 h3 hI1421

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110e
