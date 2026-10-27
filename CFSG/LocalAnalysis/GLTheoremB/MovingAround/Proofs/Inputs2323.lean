module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1314c2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2323

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

@[expose] def BadFactor (p : ℕ) {X : Type} [Group X] (K Z : Subgroup X) (z : X) (L : Subgroup X) : Prop :=
  L ≤ K ⊓ Subgroup.centralizer ({z} : Set X) ∧ Z ≤ Subgroup.normalizer (L : Set X) ∧
    (∀ y ∈ L ⊓ Subgroup.centralizer (L : Set X), y ^ p = 1 → y = 1) ∧ ¬ p ^ 2 ∣ Nat.card L ∧
    ∃ L₀ : Subgroup X, L₀ ≤ L ∧ (L₀.subgroupOf L).Normal ∧ p ∣ Nat.card L₀ ∧
      (L₀ ≤ GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
        GLAPLayer p (K ⊓ Subgroup.centralizer ({z} : Set X)) ∨ Nat.card L₀ = p)

@[expose] def Input14_1Bad : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (K Z : Subgroup X),
    CFSG.Open.IsQuasisimple ↥K → IsLieChar (· = 2) ↥K →
    IsElemAbelian p Z → Nat.card Z = p ^ 2 → Z ≤ Subgroup.normalizer (K : Set X) →
    Z ⊓ Subgroup.centralizer (K : Set X) = ⊥ → (p = 5 → ¬ Lemma1314.I2310Exc5 K) →
    ∀ z ∈ Z, z ≠ 1 →
      CFSG.GH74.GLS.oPrimeResidualOf 2 (K ⊓ Subgroup.centralizer ({z} : Set X)) ≤
        GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
          GLAPLayer p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
          ⨆ (L : Subgroup X) (_ : BadFactor p K Z z L), L

@[expose] def Input23_11Two : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (K B : Subgroup X),
    CFSG.Open.IsQuasisimple ↥K → IsLieChar (· = 2) ↥K →
    IsElemAbelian p B → Nat.card B = p ^ 2 → B ≤ Subgroup.normalizer (K : Set X) →
    B ⊓ Subgroup.centralizer (K : Set X) = ⊥ → (p = 5 → ¬ Lemma1314.I2310Exc5 K) →
    (∃ b ∈ B, b ≠ 1 ∧ ¬ Group.IsSolvable ↥(K ⊓ Subgroup.centralizer ({b} : Set X))) →
      K = ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1),
        CFSG.GH74.GLS.oPrimeResidualOf 2 (K ⊓ Subgroup.centralizer ({b} : Set X))

section GroupTheory

variable {X : Type} [Group X] [Finite X]

theorem le_core_sup_layer_of_isQuasisimple (p : ℕ) {K : Subgroup X} (hK : CFSG.Open.IsQuasisimple ↥K) :
    K ≤ GLAPPrimeCoreOf p K ⊔ GLAPLayer p K := by
  by_cases hO : GLAPPrimeCore p ↥K = ⊤
  · have hK' : GLAPPrimeCoreOf p K = K := by
      show (GLAPPrimeCore p ↥K).map K.subtype = K
      rw [hO, Subgroup.map_top, Subgroup.range_subtype]
    rw [hK']
    exact le_sup_left
  · have hOZ : GLAPPrimeCore p ↥K ≤ Subgroup.center ↥K :=
      CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hK (GLAPPrimeCore.normal p ↥K) hO
    have hQ : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) :=
      CFSG.ComponentClassification.Quasisimple.central_quotient hK _ hOZ
    have hbar := (CFSG.LocalAnalysis.GLTheoremA.glaPLayer_of_isQuasisimple hQ).2.2
    have hle : GLAPLayer p K ≤ K := sSup_le fun L hL => (show GLAPComponent p K L from hL).1
    have h := CFSG.LocalAnalysis.GLTheoremA.sup_glaPPrimeCoreOf_eq_of_barX_eq_top hle hbar
    rw [sup_comm] at h
    exact h.ge

theorem gLBConj_inv_eq (k : X) (H : Subgroup X) :
    GLBConj k⁻¹ H = H.map (MulAut.conj k).toMonoidHom := by
  show H.map (MulAut.conj k⁻¹⁻¹).toMonoidHom = H.map (MulAut.conj k).toMonoidHom
  rw [inv_inv]

theorem gLBConj_glaPLayer_le (p : ℕ) (g : X) (H : Subgroup X) :
    GLBConj g (GLAPLayer p H) ≤ GLAPLayer p (GLBConj g H) := by
  refine (Subgroup.map_le_iff_le_comap).2 (sSup_le fun L hL => ?_)
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_gLBConj hL g)

theorem map_conj_inf_centralizer {K : Subgroup X} {k : X} (hk : k ∈ K) (z : X) :
    (K ⊓ Subgroup.centralizer ({z} : Set X)).map (MulAut.conj k).toMonoidHom =
      K ⊓ Subgroup.centralizer ({k * z * k⁻¹} : Set X) := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwK : w ∈ K := (Subgroup.mem_inf.1 hw).1
    have hwz' : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hw).2
    refine Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem hk hwK) (K.inv_mem hk), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show k * w * k⁻¹ * (k * z * k⁻¹) = k * z * k⁻¹ * (k * w * k⁻¹)
    calc k * w * k⁻¹ * (k * z * k⁻¹) = k * (w * z) * k⁻¹ := by group
      _ = k * (z * w) * k⁻¹ := by rw [hwz']
      _ = k * z * k⁻¹ * (k * w * k⁻¹) := by group
  · intro hx
    have hxK : x ∈ K := (Subgroup.mem_inf.1 hx).1
    have hxz' : x * (k * z * k⁻¹) = k * z * k⁻¹ * x :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
    refine ⟨k⁻¹ * x * k, Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc k⁻¹ * x * k * z = k⁻¹ * (x * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * (k * z * k⁻¹ * x) * k := by rw [hxz']
        _ = z * (k⁻¹ * x * k) := by group
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group

theorem inf_centralizer_mul_of_mem_centralizer {K : Subgroup X} {c : X}
    (hc : c ∈ Subgroup.centralizer (K : Set X)) (z : X) :
    K ⊓ Subgroup.centralizer ({z * c} : Set X) = K ⊓ Subgroup.centralizer ({z} : Set X) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxK, h⟩
    refine ⟨hxK, ?_⟩
    have hcx : x * c = c * x := (Subgroup.mem_centralizer_iff.1 hc) x hxK
    calc x * z = x * (z * c) * c⁻¹ := by group
      _ = z * c * x * c⁻¹ := by rw [h]
      _ = z * (x * c) * c⁻¹ := by rw [mul_assoc z c x, ← hcx]
      _ = z * x := by group
  · rintro ⟨hxK, h⟩
    refine ⟨hxK, ?_⟩
    have hcx : x * c = c * x := (Subgroup.mem_centralizer_iff.1 hc) x hxK
    calc x * (z * c) = x * z * c := by group
      _ = z * x * c := by rw [h]
      _ = z * c * x := by rw [mul_assoc z x c, hcx, ← mul_assoc]

theorem mem_normalizer_sup {H K : Subgroup X} {g : X} (hH : g ∈ Subgroup.normalizer (H : Set X))
    (hK : g ∈ Subgroup.normalizer (K : Set X)) : g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup X) : Set X) := by
  rw [← GL83.CompFam.cj_eq_iff_mem_normalizer] at hH hK ⊢
  unfold GL83.CompFam.cj at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem exists_mem_inf_of_isSCp {p : ℕ} [hp : Fact p.Prime] {A L : Subgroup X} (hA : IsSCp p ⊤ A)
    (hAL : A ≤ Subgroup.normalizer (L : Set X)) (hpL : p ∣ Nat.card L) :
    ∃ y ∈ A ⊓ L, y ≠ 1 := by
  classical
  have hAel : IsElemAbelian p A := hA.2.1
  letI : MulAction ↥A ↥L :=
    { smul := fun a l => ⟨(a : X) * l * (a : X)⁻¹, (Subgroup.mem_normalizer_iff.1 (hAL a.2) l).1 l.2⟩
      one_smul := fun l => Subtype.ext (by show (1 : X) * l * (1 : X)⁻¹ = l; group)
      mul_smul := fun a b l => Subtype.ext (by
        show ((a : X) * b) * l * ((a : X) * b)⁻¹ = a * (b * l * (b : X)⁻¹) * (a : X)⁻¹
        group) }
  have hApg : IsPGroup p ↥A := CFSG.Open.IsElemAbelian.isPGroup hAel
  have hmod := hApg.card_modEq_card_fixedPoints ↥L
  have hfix : Nat.card (MulAction.fixedPoints ↥A ↥L) =
      Nat.card ↥(L ⊓ Subgroup.centralizer (A : Set X)) := by
    refine Nat.card_congr
      ⟨fun l => ⟨((l : ↥L) : X), Subgroup.mem_inf.2 ⟨(l : ↥L).2,
          Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩⟩,
        fun x => ⟨⟨x, (Subgroup.mem_inf.1 x.2).1⟩, fun a => Subtype.ext ?_⟩,
        fun l => rfl, fun x => rfl⟩
    · have h : (a : X) * l * a⁻¹ = l := congrArg Subtype.val (l.2 ⟨a, ha⟩)
      calc a * (l : X) = a * l * a⁻¹ * a := by group
        _ = l * a := by rw [h]
    · have h : (a : X) * x = x * a :=
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 x.2).2) a a.2
      show (a : X) * x * (a : X)⁻¹ = x
      rw [h]
      group
  have hdvd : p ∣ Nat.card ↥(L ⊓ Subgroup.centralizer (A : Set X)) := by
    rw [← hfix]
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hpL))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hyp : (x : X) ^ p = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    exact congrArg Subtype.val h
  have hy1 : (x : X) ≠ 1 := by
    intro h
    have hx1 : x = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  have hyC : (x : X) ∈ Subgroup.centralizer (A : Set X) := (Subgroup.mem_inf.1 x.2).2
  have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers (x : X), a * b = b * a :=
    GL83.CompFam.zpowers_commute fun a ha => Subgroup.mem_centralizer_iff.1 hyC a ha
  have hE := CFSG.Open.IsElemAbelian.sup_of_commute hAel (CFSG.Open.isElemAbelian_zpowers hyp) hcomm
  have hEA := hA.2.2 _ le_top hE le_sup_left
  have hyA : (x : X) ∈ A := hEA.le (Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : X)))
  exact ⟨x, Subgroup.mem_inf.2 ⟨hyA, (Subgroup.mem_inf.1 x.2).1⟩, hy1⟩

theorem mem_of_pow_eq_one_of_normal {p : ℕ} [hp : Fact p.Prime] {L L₀ : Subgroup X} (hL₀L : L₀ ≤ L)
    (hn : (L₀.subgroupOf L).Normal) (hpL₀ : p ∣ Nat.card L₀) (hp2 : ¬ p ^ 2 ∣ Nat.card L) {y : X}
    (hyL : y ∈ L) (hyp : y ^ p = 1) : y ∈ L₀ := by
  set N : Subgroup ↥L := L₀.subgroupOf L with hN
  haveI : N.Normal := hn
  have hcardN : Nat.card N = Nat.card L₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₀L).toEquiv
  set y' : ↥L := ⟨y, hyL⟩ with hy'
  have hy'p : y' ^ p = 1 := Subtype.ext (by simpa [hy'] using hyp)
  have hidx : ¬ p ∣ Nat.card (↥L ⧸ N) := by
    intro h
    apply hp2
    have h1 : Nat.card N * N.index = Nat.card ↥L := Subgroup.card_mul_index N
    rw [← h1, hcardN, pow_two]
    exact mul_dvd_mul hpL₀ h
  have h1 : (QuotientGroup.mk' N y') ^ (Nat.card (↥L ⧸ N)) = 1 := pow_card_eq_one'
  have h2 : (QuotientGroup.mk' N y') ^ (p ^ 1) = 1 := by rw [pow_one, ← map_pow, hy'p, map_one]
  have hyN : y' ∈ N := (QuotientGroup.eq_one_iff y').1 (Lemma114Layer.eq_one_of_pow_eq_one hidx h1 h2)
  exact Subgroup.mem_subgroupOf.1 hyN

theorem le_sup_inf_normalizer_zpowers {p : ℕ} [hp : Fact p.Prime] {L L₀ : Subgroup X} (hL₀L : L₀ ≤ L)
    (hn : (L₀.subgroupOf L).Normal) (hpL₀ : p ∣ Nat.card L₀) (hp2 : ¬ p ^ 2 ∣ Nat.card L) {y : X}
    (hyL : y ∈ L) (hy1 : y ≠ 1) (hyp : y ^ p = 1) :
    L ≤ L₀ ⊔ (L ⊓ Subgroup.normalizer (Subgroup.zpowers y : Set X)) := by
  classical
  set N : Subgroup ↥L := L₀.subgroupOf L with hN
  haveI : N.Normal := hn
  have hcardN : Nat.card N = Nat.card L₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₀L).toEquiv
  set y' : ↥L := ⟨y, hyL⟩ with hy'
  have hy'p : y' ^ p = 1 := Subtype.ext (by simpa [hy'] using hyp)
  have hy'1 : y' ≠ 1 := fun h => hy1 (by simpa [hy'] using congrArg Subtype.val h)
  have hord : orderOf y' = p := orderOf_eq_prime hy'p hy'1
  have hyN : y' ∈ N :=
    Subgroup.mem_subgroupOf.2 (mem_of_pow_eq_one_of_normal hL₀L hn hpL₀ hp2 hyL hyp)
  have hpL : p ∣ Nat.card ↥L := hpL₀.trans (hcardN ▸ Subgroup.card_subgroup_dvd_card N)
  have hfac : (Nat.card ↥L).factorization p = 1 := by
    have hL0 : Nat.card ↥L ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card ↥L).factorization p :=
      (hp.out.pow_dvd_iff_le_factorization hL0).1 (by rwa [pow_one])
    have h2 : ¬ 2 ≤ (Nat.card ↥L).factorization p := fun h =>
      hp2 ((hp.out.pow_dvd_iff_le_factorization hL0).2 h)
    omega
  let P : Sylow p ↥L := Sylow.ofCard (Subgroup.zpowers y') (by
    rw [Nat.card_zpowers, hord, hfac, pow_one])
  have hPN : (P : Subgroup ↥L) ≤ N := (Subgroup.zpowers_le).2 hyN
  have hF : Subgroup.normalizer ((Subgroup.zpowers y' : Subgroup ↥L) : Set ↥L) ⊔ N = ⊤ :=
    Sylow.normalizer_sup_eq_top' P hPN
  have h1 : (Subgroup.normalizer ((Subgroup.zpowers y' : Subgroup ↥L) : Set ↥L)).map L.subtype ≤
      L ⊓ Subgroup.normalizer (Subgroup.zpowers y : Set X) := by
    rintro _ ⟨n, hn, rfl⟩
    refine Subgroup.mem_inf.2 ⟨n.2, Subgroup.mem_normalizer_fintype fun h hh => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have h1 : n * y' * n⁻¹ ∈ Subgroup.zpowers y' :=
      (Subgroup.mem_normalizer_iff.1 hn y').1 (Subgroup.mem_zpowers y')
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h1
    have hj' : y ^ j = (n : X) * y * (n : X)⁻¹ := by
      have h2 := congrArg Subtype.val hj
      simpa [hy'] using h2
    show (n : X) * y ^ k * (n : X)⁻¹ ∈ Subgroup.zpowers y
    rw [← conj_zpow, ← hj', ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers y _
  have h2 : N.map L.subtype ≤ L₀ := by
    rw [hN, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hle : (Subgroup.normalizer ((Subgroup.zpowers y' : Subgroup ↥L) : Set ↥L)).map L.subtype ⊔
      N.map L.subtype ≤ L₀ ⊔ (L ⊓ Subgroup.normalizer (Subgroup.zpowers y : Set X)) :=
    sup_le (le_sup_of_le_right h1) (le_sup_of_le_left h2)
  intro l hl
  have hmem : (⟨l, hl⟩ : ↥L) ∈
      Subgroup.normalizer ((Subgroup.zpowers y' : Subgroup ↥L) : Set ↥L) ⊔ N := by
    rw [hF]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem L.subtype hmem
  rw [Subgroup.map_sup] at hmap
  exact hle hmap

theorem card_cen_eq_and_sup {p : ℕ} [hp : Fact p.Prime] {K A Z : Subgroup X} (hAel : IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 3) (hZA : Z ≤ A) (hZcard : Nat.card Z = p ^ 2)
    (hfaith : Z ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hC : A ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) :
    Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set X)) = p ∧
      Z ⊔ (A ⊓ Subgroup.centralizer (K : Set X)) = A := by
  set C := A ⊓ Subgroup.centralizer (K : Set X) with hCdef
  have hCA : C ≤ A := inf_le_left
  have hcomm : ∀ a ∈ Z, ∀ b ∈ C, a * b = b * a := fun a ha b hb => hAel.comm (hZA ha) (hCA hb)
  have hd : Z ⊓ C = ⊥ := le_bot_iff.1 (hfaith ▸ inf_le_inf_left Z inf_le_right)
  have hcard := GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcomm hd
  have hle : Z ⊔ C ≤ A := sup_le hZA hCA
  have hcle : Nat.card ↥(Z ⊔ C) ≤ Nat.card A := Subgroup.card_le_of_le hle
  obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow (hAel.mono hCA)
  have hk1 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hC (Subgroup.card_eq_one.1 hk)
  have hkle : k ≤ 1 := by
    rw [hcard, hZcard, hk, hAcard, ← pow_add] at hcle
    have := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hcle
    omega
  have hk' : k = 1 := by omega
  rw [hk', pow_one] at hk
  refine ⟨hk, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [hcard, hZcard, hk, hAcard]
  ring_nf
  exact le_rfl

theorem inf_normalizer_zpowers_le {p : ℕ} [hp : Fact p.Prime] {K A L : Subgroup X} {z y : X}
    (hAel : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hCcard : Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set X)) = p)
    (hzA : z ∈ A) (hzK : z ∉ Subgroup.centralizer (K : Set X)) (hyA : y ∈ A) (hyL : y ∈ L) (hy1 : y ≠ 1)
    (hLK : L ≤ K ⊓ Subgroup.centralizer ({z} : Set X))
    (hZL : ∀ w ∈ L ⊓ Subgroup.centralizer (L : Set X), w ^ p = 1 → w = 1) :
    L ⊓ Subgroup.normalizer (Subgroup.zpowers y : Set X) ≤ K ⊓ Subgroup.normalizer (A : Set X) := by
  set C := A ⊓ Subgroup.centralizer (K : Set X) with hCdef
  have hCA : C ≤ A := inf_le_left
  set H := C ⊔ Subgroup.zpowers z with hHdef
  have hHA : H ≤ A := sup_le hCA (Subgroup.zpowers_le.2 hzA)
  have hzC : z ∉ C := fun h => hzK (Subgroup.mem_inf.1 h).2
  have hcardH : Nat.card H = p * p := by
    rw [hHdef, GL83.CompFam.card_sup_zpowers hAel hCA hzA hzC, hCcard]
  have hyH : y ∉ H := by
    intro hy
    have hcomm : ∀ c ∈ C, ∀ w ∈ Subgroup.zpowers z, c * w = w * c :=
      GL83.CompFam.zpowers_commute fun c hc => hAel.comm (hCA hc) hzA
    obtain ⟨c, hc, w, hw, hcw⟩ := (GL83.CompFam.mem_sup_of_commute hcomm).1 hy
    apply hy1
    refine hZL y (Subgroup.mem_inf.2 ⟨hyL, ?_⟩) (hAel.2 y hyA)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlK : l ∈ K := (Subgroup.mem_inf.1 (hLK hl)).1
    have hlz : l * z = z * l := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hLK hl)).2
    have hlc : l * c = c * l := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2) l hlK
    have hlw : l * w = w * l := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact ((Commute.zpow_right (show Commute l z from hlz) i)).eq
    rw [← hcw]
    calc l * (c * w) = c * (l * w) := by rw [← mul_assoc, hlc, mul_assoc]
      _ = c * w * l := by rw [hlw, mul_assoc]
  have hEq : H ⊔ Subgroup.zpowers y = A := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hHA (Subgroup.zpowers_le.2 hyA)) ?_
    rw [GL83.CompFam.card_sup_zpowers hAel hHA hyA hyH, hcardH, hAcard]
    ring_nf
    exact le_rfl
  intro n hn
  obtain ⟨hnL, hny⟩ := Subgroup.mem_inf.1 hn
  have hnK : n ∈ K := (Subgroup.mem_inf.1 (hLK hnL)).1
  have hnz : n * z = z * n := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hLK hnL)).2
  refine Subgroup.mem_inf.2 ⟨hnK, ?_⟩
  rw [← hEq]
  refine mem_normalizer_sup (mem_normalizer_sup ?_ ?_) hny
  · apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2) n hnK).symm
  · apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left (show Commute z n from hnz.symm) i)).eq

theorem inf_normalizer_le_normalizer_hyperW (p : ℕ) {K A Z : Subgroup X} (hZA : Z ≤ A)
    (hAel : IsElemAbelian p A) (hsup : Z ⊔ (A ⊓ Subgroup.centralizer (K : Set X)) = A)
    (hfaith : Z ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    K ⊓ Subgroup.normalizer (A : Set X) ≤ Subgroup.normalizer (Claims1314c2.hyperW p K Z : Set X) := by
  set C := A ⊓ Subgroup.centralizer (K : Set X) with hCdef
  have hcomm : ∀ a ∈ Z, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    hAel.comm (hZA ha) ((inf_le_left : C ≤ A) hb)
  refine Lemma114Layer.le_normalizer_of_conj fun k hk w hw => ?_
  obtain ⟨hkK, hkA⟩ := Subgroup.mem_inf.1 hk
  have hmap : (Claims1314c2.hyperW p K Z).map (MulAut.conj k).toMonoidHom ≤
      Claims1314c2.hyperW p K Z := by
    show (⨆ (z : X) (_ : z ∈ Z) (_ : z ≠ 1),
        (GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
          GLAPLayer p (K ⊓ Subgroup.centralizer ({z} : Set X)))).map (MulAut.conj k).toMonoidHom ≤ _
    rw [Subgroup.map_iSup]
    refine iSup_le fun z => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hz => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hz1 => ?_
    have haA : k * z * k⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hkA z).1 (hZA hz)
    rw [← hsup] at haA
    obtain ⟨z', hz', c, hc, hzc⟩ := (GL83.CompFam.mem_sup_of_commute hcomm).1 haA
    have hcK : c ∈ Subgroup.centralizer (K : Set X) := (Subgroup.mem_inf.1 hc).2
    have hz'1 : z' ≠ 1 := by
      rintro rfl
      rw [one_mul] at hzc
      have hck : k * c = c * k := (Subgroup.mem_centralizer_iff.1 hcK) k hkK
      have hzeq : z = c := by
        calc z = k⁻¹ * (k * z * k⁻¹) * k := by group
          _ = k⁻¹ * c * k := by rw [hzc]
          _ = c := by rw [mul_assoc, ← hck, ← mul_assoc, inv_mul_cancel, one_mul]
      have hmem : z ∈ Z ⊓ Subgroup.centralizer (K : Set X) := Subgroup.mem_inf.2 ⟨hz, hzeq ▸ hcK⟩
      rw [hfaith, Subgroup.mem_bot] at hmem
      exact hz1 hmem
    have hcent : (K ⊓ Subgroup.centralizer ({z} : Set X)).map (MulAut.conj k).toMonoidHom =
        K ⊓ Subgroup.centralizer ({z'} : Set X) := by
      rw [map_conj_inf_centralizer hkK, ← hzc, inf_centralizer_mul_of_mem_centralizer hcK]
    rw [Subgroup.map_sup]
    refine le_iSup₂_of_le z' hz' (le_iSup_of_le hz'1 (sup_le_sup ?_ ?_))
    · rw [← gLBConj_inv_eq, ← glaPPrimeCoreOf_gLBConj, gLBConj_inv_eq, hcent]
    · rw [← gLBConj_inv_eq]
      refine (gLBConj_glaPLayer_le p k⁻¹ _).trans ?_
      rw [gLBConj_inv_eq, hcent]
  exact hmap ⟨w, hw, rfl⟩

theorem badFactor_le_normalizer {p : ℕ} [hp : Fact p.Prime] {K A Z : Subgroup X} {z : X}
    (hAsc : IsSCp p ⊤ A) (hAcard : Nat.card A = p ^ 3) (hZA : Z ≤ A)
    (hCcard : Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set X)) = p)
    (hsup : Z ⊔ (A ⊓ Subgroup.centralizer (K : Set X)) = A)
    (hfaith : Z ⊓ Subgroup.centralizer (K : Set X) = ⊥) (hz : z ∈ Z) (hz1 : z ≠ 1)
    {L : Subgroup X} (hL : BadFactor p K Z z L) :
    L ≤ Subgroup.normalizer (Claims1314c2.hyperW p K Z : Set X) := by
  obtain ⟨hLK, hZL, hcen, hp2, L₀, hL₀L, hn, hpL₀, hL₀W⟩ := hL
  have hAel : IsElemAbelian p A := hAsc.2.1
  have hCL : A ⊓ Subgroup.centralizer (K : Set X) ≤ Subgroup.normalizer (L : Set X) := by
    intro c hc
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2) l (Subgroup.mem_inf.1 (hLK hl)).1
  have hAL : A ≤ Subgroup.normalizer (L : Set X) := hsup ▸ sup_le hZL hCL
  have hpL : p ∣ Nat.card L := hpL₀.trans (Subgroup.card_dvd_of_le hL₀L)
  obtain ⟨y, hy, hy1⟩ := exists_mem_inf_of_isSCp hAsc hAL hpL
  obtain ⟨hyA, hyL⟩ := Subgroup.mem_inf.1 hy
  have hyp : y ^ p = 1 := hAel.2 y hyA
  have hzK : z ∉ Subgroup.centralizer (K : Set X) := fun h => hz1 (by
    have hmem : z ∈ Z ⊓ Subgroup.centralizer (K : Set X) := Subgroup.mem_inf.2 ⟨hz, h⟩
    rwa [hfaith, Subgroup.mem_bot] at hmem)
  have hF := le_sup_inf_normalizer_zpowers hL₀L hn hpL₀ hp2 hyL hy1 hyp
  have hN := inf_normalizer_zpowers_le hAel hAcard hCcard (hZA hz) hzK hyA hyL hy1 hLK hcen
  have hW := inf_normalizer_le_normalizer_hyperW p hZA hAel hsup hfaith
  have hWW : Claims1314c2.hyperW p K Z ≤
      Subgroup.normalizer (Claims1314c2.hyperW p K Z : Set X) := Subgroup.le_normalizer
  refine hF.trans (sup_le ?_ (hN.trans hW))
  rcases hL₀W with hL₀W | hL₀p
  · refine hL₀W.trans (le_trans ?_ hWW)
    exact le_iSup₂_of_le z hz (le_iSup_of_le hz1 le_rfl)
  ·
    have hyL₀ : y ∈ L₀ := mem_of_pow_eq_one_of_normal hL₀L hn hpL₀ hp2 hyL hyp
    have hY : Subgroup.zpowers y = L₀ := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyL₀) ?_
      rw [hL₀p, Nat.card_zpowers, orderOf_eq_prime hyp hy1]
    refine le_trans ?_ (hN.trans hW)
    rw [← hY]
    exact le_inf (Subgroup.zpowers_le.2 hyL) Subgroup.le_normalizer

end GroupTheory

theorem input23_23N_of_inputs (hI11 : Input23_11Two) (hB : Input14_1Bad) :
    Claims1314c2.Input23_23N := by
  intro p hp hp5 X _ _ K A Z hKc hKlie hAsc hArank hAcent hZ hZN hexc hns
  haveI : Fact p.Prime := ⟨hp⟩
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKc.2.2
  obtain ⟨hZA, hZel, hZcard⟩ := hZ
  by_cases hfaith : Z ⊓ Subgroup.centralizer (K : Set X) = ⊥
  · have hAel : IsElemAbelian p A := hAsc.2.1
    have hAcard : Nat.card A = p ^ 3 := by rw [GL83.PiGen.card_eq_pow_pRank hAel, hArank]
    obtain ⟨hCcard, hsup⟩ := card_cen_eq_and_sup hAel hAcard hZA hZcard hfaith hAcent
    have hgen := hI11 p hp hp5 X K Z hKq hKlie hZel hZcard hZN hfaith hexc hns
    refine hgen.le.trans (iSup₂_le fun z hz => iSup_le fun hz1 => ?_)
    refine (hB p hp hp5 X K Z hKq hKlie hZel hZcard hZN hfaith hexc z hz hz1).trans ?_
    refine sup_le (le_trans ?_ Subgroup.le_normalizer)
      (iSup₂_le fun L hL => badFactor_le_normalizer hAsc hAcard hZA hCcard hsup hfaith hz hz1 hL)
    exact le_iSup₂_of_le z hz (le_iSup_of_le hz1 le_rfl)
  · obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hfaith
    obtain ⟨hzZ, hzK⟩ := Subgroup.mem_inf.1 hzmem
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hKz : K ⊓ Subgroup.centralizer ({z} : Set X) = K :=
      inf_eq_left.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hzK) k hk)
    have h1 : GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
        GLAPLayer p (K ⊓ Subgroup.centralizer ({z} : Set X)) ≤ Claims1314c2.hyperW p K Z :=
      le_iSup₂_of_le z hzZ (le_iSup_of_le hz1' le_rfl)
    rw [hKz] at h1
    have hWeq : Claims1314c2.hyperW p K Z = K :=
      le_antisymm (Claims1314c2.hyperW_le p K Z) ((le_core_sup_layer_of_isQuasisimple p hKq).trans h1)
    rw [hWeq]
    exact Subgroup.le_normalizer

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2323

end
