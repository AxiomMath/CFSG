module

public import CFSG.GH74.Uniqueness.SU.KI1r3Pow
public import CFSG.GH74.Uniqueness.SU.KI1r3Fitting
public import CFSG.GH74.Uniqueness.SU.KI1r4L82
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3
open CFSG.GH74.Uniqueness.SU.K.R4.L82 CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem exists_normal_elemAb_central {Q : Subgroup H} (hQn : Q.Normal) (hQ : IsPGroup 2 Q)
    (hne : Q ≠ ⊥) :
    ∃ A : Subgroup H, A.Normal ∧ Open.IsElemAbelian 2 A ∧ A ≠ ⊥ ∧ A ≤ Q ∧
      ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a := by
  let A : Subgroup H :=
    { carrier := {a | a ∈ Q ∧ (∀ q ∈ Q, a * q = q * a) ∧ a * a = 1}
      one_mem' := ⟨Q.one_mem, fun q _ => by simp, by simp⟩
      mul_mem' := by
        rintro a b ⟨haQ, hac, ha2⟩ ⟨hbQ, hbc, hb2⟩
        refine ⟨Q.mul_mem haQ hbQ, fun q hq => ?_, ?_⟩
        · rw [mul_assoc, hbc q hq, ← mul_assoc, hac q hq, mul_assoc]
        · calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hbc a haQ]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2]; group
      inv_mem' := by
        rintro a ⟨haQ, hac, ha2⟩
        have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [hinv]
        exact ⟨haQ, hac, ha2⟩ }
  have hAmem : ∀ a, a ∈ A ↔ a ∈ Q ∧ (∀ q ∈ Q, a * q = q * a) ∧ a * a = 1 := fun a => Iff.rfl
  refine ⟨A, ?_, ?_, ?_, fun a ha => ((hAmem a).mp ha).1,
    fun a ha q hq => ((hAmem a).mp ha).2.1 q hq⟩
  · refine ⟨fun a ha g => ?_⟩
    obtain ⟨haQ, hac, ha2⟩ := (hAmem a).mp ha
    rw [hAmem]
    refine ⟨hQn.conj_mem a haQ g, fun q hq => ?_, ?_⟩
    · have hq' : g⁻¹ * q * g ∈ Q := by
        have := hQn.conj_mem q hq g⁻¹
        simpa using this
      have := hac _ hq'
      calc g * a * g⁻¹ * q = g * (a * (g⁻¹ * q * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * q * g) * a) * g⁻¹ := by rw [this]
        _ = q * (g * a * g⁻¹) := by group
    · calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [ha2]; group
  · rw [SU1.isElemAbelian_iff]
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · exact ((hAmem a).mp ha).2.1 b ((hAmem b).mp hb).1
    · rw [pow_two]; exact ((hAmem a).mp ha).2.2
  · have hQnt : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
    have hZ : Nontrivial (Subgroup.center Q) := IsPGroup.center_nontrivial hQ
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center Q)
    set z₀ : Q := (z : Q) with hz₀
    have hz₀1 : z₀ ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQ) z₀
    have hj1 : j ≠ 0 := by
      rintro rfl
      exact hz₀1 (orderOf_eq_one_iff.mp (by simpa using hj))
    have hord : orderOf z₀ ≠ 0 := by rw [hj]; positivity
    have h2dvd : 2 ∣ orderOf z₀ := by
      rw [hj]; exact dvd_pow_self 2 hj1
    set w : Q := z₀ ^ (orderOf z₀ / 2) with hw
    have hwo : orderOf w = 2 := orderOf_pow_orderOf_div hord h2dvd
    have hw2 : w * w = 1 := by
      have : w ^ 2 = 1 := hwo ▸ pow_orderOf_eq_one w
      rwa [pow_two] at this
    have hwc : w ∈ Subgroup.center Q := Subgroup.pow_mem _ z.2 _
    have hw1 : w ≠ 1 := by
      intro h; rw [h, orderOf_one] at hwo; omega
    intro hbot
    have hwA : (w : H) ∈ A := by
      rw [hAmem]
      refine ⟨w.2, fun q hq => ?_, ?_⟩
      · have := Subgroup.mem_center_iff.mp hwc ⟨q, hq⟩
        exact congrArg Subtype.val this.symm
      · exact congrArg Subtype.val hw2
    have : (w : H) ∈ (⊥ : Subgroup H) := hbot ▸ hwA
    rw [Subgroup.mem_bot] at this
    exact hw1 (Subtype.ext this)

structure RData (T : Sylow 2 H) (x : H) (A R : Subgroup H) (y : H) : Prop where
  A_normal : A.Normal
  A_elem : Open.IsElemAbelian 2 A
  A_card : Nat.card A = 4
  A_le : A ≤ R
  R_eq : R = (T : Subgroup H) ⊓ centralizer (A : Set H)
  R_two : IsPGroup 2 R
  x_sq : x * x = 1
  x_not_mem : x ∉ R
  x_norm : ∀ r ∈ R, x * r * x⁻¹ ∈ R
  T_eq : (T : Subgroup H) = R ⊔ zpowers x
  x_act : ∃ a ∈ A, x * a * x⁻¹ ≠ a
  y_norm : ∀ r ∈ R, y * r * y⁻¹ ∈ R
  y_three : IsPGroup 3 (zpowers y)
  xy : x * y * x⁻¹ = y⁻¹
  y_A : ∀ a ∈ A, a ≠ 1 → y * a * y⁻¹ ≠ a
  y_free : ∀ r ∈ R, y * r * y⁻¹ = r → r = 1
  rank : Open.pRank 2 (centralizer ({x} : Set H) ⊓ R) ≤ 1
  y_cube : ∀ r ∈ R, y ^ 3 * r * (y ^ 3)⁻¹ = r

theorem Cfg.rdata {T : Sylow 2 H} {x : H} (h : Cfg H T x) {A : Subgroup H} (hAn : A.Normal)
    (hAel : Open.IsElemAbelian 2 A) (hAne : A ≠ ⊥) :
    ∃ y : H, RData T x A ((T : Subgroup H) ⊓ centralizer (A : Set H)) y := by
  have := hAn
  obtain ⟨hcard, hxA⟩ := h.normal_elemAb hAel hAne
  have hxx := h.mul_self_x
  have hA2 : IsPGroup 2 A := by
    have := isElementaryAbelian_of_isElemAbelian hAel
    exact IsElementaryAbelian.isPGroup 2 A
  have hAT : A ≤ (T : Subgroup H) := hA2.le_sylow_of_normal T
  set R : Subgroup H := (T : Subgroup H) ⊓ centralizer (A : Set H) with hRdef
  have hR2 : IsPGroup 2 R := T.isPGroup'.to_le inf_le_left
  have hAC : A ≤ centralizer (A : Set H) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (SU1.isElemAbelian_iff.mp hAel).1 b hb a ha
  have hAR : A ≤ R := le_inf hAT hAC
  have hxN : x ∈ normalizer (R : Set H) := mem_normalizer_inf h.xT
  have hxnR : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp hxN r).mp hr
  have hxR : x ∉ R := by
    intro hx
    obtain ⟨a, haA, hxa⟩ := hxA
    apply hxa
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 a haA
    calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [← this]
      _ = a := by group
  have hTeq := sylow_eq_sup hcard T.isPGroup' h.xT hxA
  obtain ⟨y, hyN, hy3, hxy, hyA⟩ := exists_y h.cen hcard T hxx h.xT hxA
  have hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp hyN r).mp hr
  have hCy : ∀ r ∈ R, y * r * y⁻¹ = r → r = 1 := by
    intro r hr hyr
    by_contra hr1
    set X : Subgroup H := centralizer ({y} : Set H) ⊓ R with hX
    have hrX : r ∈ X := by
      refine Subgroup.mem_inf.mpr ⟨?_, hr⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      symm
      calc y * r = y * r * y⁻¹ * y := by group
        _ = r * y := by rw [hyr]
    have hXne : X ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hrX
      exact hr1 hrX
    have hX2 : IsPGroup 2 X := hR2.to_le inf_le_right
    have hxy' : x⁻¹ * y * x = y⁻¹ := by
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      rw [hxi]
      calc x * y * x = x * y * x⁻¹ := by rw [hxi]
        _ = y⁻¹ := hxy
    have hxX : ∀ s ∈ X, x * s * x⁻¹ ∈ X := by
      intro s hs
      refine Subgroup.mem_inf.mpr ⟨?_, hxnR s (Subgroup.mem_inf.mp hs).2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      symm
      have hs' := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs).1
      calc y * (x * s * x⁻¹) = x * (x⁻¹ * y * x) * s * x⁻¹ := by group
        _ = x * y⁻¹ * s * x⁻¹ := by rw [hxy']
        _ = x * (y⁻¹ * s * y) * y⁻¹ * x⁻¹ := by group
        _ = x * s * y⁻¹ * x⁻¹ := by
          have : y⁻¹ * s * y = s := by
            calc y⁻¹ * s * y = y⁻¹ * (s * y) := by group
              _ = y⁻¹ * (y * s) := by rw [hs']
              _ = s := by group
          rw [this]
        _ = x * s * x⁻¹ * (x * y⁻¹ * x⁻¹) := by group
        _ = x * s * x⁻¹ * y := by
          have : x * y⁻¹ * x⁻¹ = y := by
            calc x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
              _ = y := by rw [hxy]; group
          rw [this]
    obtain ⟨u, huX, hu1, hu2, hxu⟩ := exists_fixed_involution hX2 hXne hxx hxX
    obtain ⟨a₀, ha₀A, ha₀1, hxa₀⟩ := exists_fixed_nonidentity A hcard x hxx
    have ha₀2 : a₀ * a₀ = 1 := by
      have := (SU1.isElemAbelian_iff.mp hAel).2 a₀ ha₀A
      rwa [pow_two] at this
    have huR : u ∈ R := (Subgroup.mem_inf.mp huX).2
    have hyu : y * u * y⁻¹ = u := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp huX).1
      calc y * u * y⁻¹ = u * y * y⁻¹ := by rw [this]
        _ = u := by group
    have hcomm : a₀ * u = u * a₀ :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp huR).2 a₀ ha₀A
    have hnot : a₀ ∉ zpowers u := by
      intro hmem
      rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hu2 hmem with h1 | h1
      · exact ha₀1 h1
      · exact hyA a₀ ha₀A ha₀1 (by rw [h1]; exact hyu)
    obtain ⟨hVel, hVcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two
      (a := u) (y := a₀) (by rw [pow_two]; exact hu2) (by rw [pow_two]; exact ha₀2) hu1 hnot
      hcomm.symm
    have hVR : zpowers u ⊔ zpowers a₀ ≤ R :=
      sup_le (Subgroup.zpowers_le.mpr huR) (Subgroup.zpowers_le.mpr (hAR ha₀A))
    have hVx : ∀ v ∈ zpowers u ⊔ zpowers a₀, v * x = x * v := by
      have : zpowers u ⊔ zpowers a₀ ≤ centralizer ({x} : Set H) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          symm
          calc x * u = x * u * x⁻¹ * x := by group
            _ = u * x := by rw [hxu]
        · rw [Subgroup.mem_centralizer_singleton_iff]
          symm
          calc x * a₀ = x * a₀ * x⁻¹ * x := by group
            _ = a₀ * x := by rw [hxa₀]
      intro v hv
      exact (Subgroup.mem_centralizer_singleton_iff.mp (this hv))
    have hxV : x ∉ zpowers u ⊔ zpowers a₀ := fun hx => hxR (hVR hx)
    obtain ⟨hel, hc8⟩ := sup_zpowers_ge_eight hVel (by rw [hVcard]; norm_num) hxx hVx hxV
    exact h.no_E8 hel hc8 1 (by simpa using Subgroup.mem_sup_right (mem_zpowers x))
  have hrk := h.pRank_centralizer_inf_le_one hxR
  have hy3' := r3pow R hR2 y x hxx hxnR hyR hy3 hxy hCy hrk
  exact ⟨y, ⟨hAn, hAel, hcard, hAR, rfl, hR2, hxx, hxR, hxnR, hTeq, hxA, hyR, hy3, hxy, hyA, hCy,
    hrk, hy3'⟩⟩

theorem pRank_two_congr {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] (e : A ≃* B) :
    CFSG.pRank 2 A = CFSG.pRank 2 B := CFSG.pRank_congr_of_mulEquiv e 2

@[expose] def Lemma82Concl (R : Subgroup H) (x y : H) : Prop :=
  ((∀ r ∈ R, ∀ s ∈ R, r * s = s * r) ∧ ∃ c ∈ R, x * c * x⁻¹ = c ∧
      zpowers c ⊔ zpowers (y * c * y⁻¹) = R ∧ Nat.card R = orderOf c ^ 2) ∨
    (Nat.card R = 64 ∧ Nat.card (center ↥R) = 4 ∧ frattini ↥R = center ↥R ∧
      (∀ u : ↥R, u * u ∈ center ↥R) ∧
      (∀ u v : ↥R, ⁅u, v⁆ ∈ center ↥R) ∧ (∀ a ∈ center ↥R, a * a = 1) ∧
      Nonempty (↥(centralizer ({x} : Set H) ⊓ R) ≃* QuaternionGroup 2))

theorem RData.lemma82 {T : Sylow 2 H} {x : H} {A R : Subgroup H} {y : H} (hR : RData T x A R y)
    {R' : Subgroup H} (hR'R : R' ≤ R) (hx : ∀ r ∈ R', x * r * x⁻¹ ∈ R')
    (hy : ∀ r ∈ R', y * r * y⁻¹ ∈ R') : Lemma82Concl R' x y := by
  have hR'2 : IsPGroup 2 R' := hR.R_two.to_le hR'R
  have hyN := Pow.mem_normalizer_of_forall_mem R' hy
  have hxN := Pow.mem_normalizer_of_forall_mem R' hx
  let σ : MulAut R' := R'.normalizerMonoidHom ⟨y, hyN⟩
  let τ : MulAut R' := R'.normalizerMonoidHom ⟨x, hxN⟩
  have hσapp : ∀ r : R', ((σ r : R') : H) = y * r * y⁻¹ := fun r => rfl
  have hτapp : ∀ r : R', ((τ r : R') : H) = x * r * x⁻¹ := fun r => rfl
  have hDih : Pow.DihAct σ τ 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 : σ ^ 3 = 1 := by
        refine MulEquiv.ext fun r => ?_
        have h0 : ((σ ^ 3) r : R') = σ (σ (σ r)) := by
          simp [pow_succ, MulAut.mul_apply]
        rw [h0]
        show σ (σ (σ r)) = r
        apply Subtype.ext
        rw [hσapp, hσapp, hσapp]
        have h3 := hR.y_cube r (hR'R r.2)
        have hy3 : y ^ 3 = y * y * y := by rw [pow_succ, pow_two]
        rw [hy3] at h3
        calc y * (y * (y * (r : H) * y⁻¹) * y⁻¹) * y⁻¹
            = y * y * y * r * (y * y * y)⁻¹ := by group
          _ = r := h3
      simpa using h1
    · have : (⟨x, hxN⟩ : normalizer (R' : Set H)) ^ 2 = 1 :=
        Subtype.ext (by simpa [pow_two] using hR.x_sq)
      change R'.normalizerMonoidHom ⟨x, hxN⟩ ^ 2 = 1
      rw [← map_pow, this, map_one]
    · have : (⟨x, hxN⟩ : normalizer (R' : Set H)) * ⟨y, hyN⟩ *
          (⟨x, hxN⟩ : normalizer (R' : Set H))⁻¹ = (⟨y, hyN⟩ : normalizer (R' : Set H))⁻¹ :=
        Subtype.ext (by simpa using hR.xy)
      have h2 := congrArg R'.normalizerMonoidHom this
      simpa only [map_mul, map_inv] using h2
    · intro r hr
      exact Subtype.ext (hR.y_free r (hR'R r.2) (by rw [← hσapp r, hr]))
  let eC : fixSub τ ≃* ↥(centralizer ({x} : Set H) ⊓ R') :=
    { toFun := fun c => ⟨((c.1 : R') : H), by
        refine Subgroup.mem_inf.mpr ⟨?_, c.1.2⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : ((τ c.1 : R') : H) = (c.1 : H) := congrArg Subtype.val c.2
        rw [hτapp] at h1
        calc (c.1 : H) * x = x * (c.1 : H) * x⁻¹ * x := by rw [h1]
          _ = x * (c.1 : H) := by group⟩
      invFun := fun d => ⟨⟨(d.1 : H), (Subgroup.mem_inf.mp d.2).2⟩, by
        apply Subtype.ext
        rw [hτapp]
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp d.2).1
        calc x * (d.1 : H) * x⁻¹ = (d.1 : H) * x * x⁻¹ := by rw [h1]
          _ = d.1 := by group⟩
      left_inv := fun c => rfl
      right_inv := fun d => rfl
      map_mul' := fun a b => rfl }
  have hrk : CFSG.pRank 2 (fixSub τ) ≤ 1 := by
    rw [pRank_two_congr eC, CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two]
    exact (SU1.pRank_mono (by norm_num) (inf_le_inf_left _ hR'R)).trans hR.rank
  rcases L82.lemma82 hR'2 hDih hrk with ⟨hcomm, c, hc, hgen, hcard⟩ |
      ⟨h64, hZ, hcomm, hfr, hsq, hcsq, ⟨eQ⟩⟩
  · refine Or.inl ⟨fun r hr s hs => ?_, (c : H), c.2, ?_, ?_, ?_⟩
    · have := hcomm.is_comm.comm ⟨r, hr⟩ ⟨s, hs⟩
      exact congrArg Subtype.val this
    · have h1 : ((τ c : R') : H) = (c : H) := congrArg Subtype.val hc
      rwa [hτapp] at h1
    · have h1 := congrArg (Subgroup.map R'.subtype) hgen
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h1
      have h2 : (⊤ : Subgroup R').map R'.subtype = R' := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [h2] at h1
      exact h1
    · rw [Subgroup.orderOf_coe]
      exact hcard
  · refine Or.inr ⟨h64, hZ, hfr, hsq, fun u v => ?_, hcsq, ⟨eC.symm.trans eQ⟩⟩
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end CFSG.GH74.Uniqueness.SU.K.R4
