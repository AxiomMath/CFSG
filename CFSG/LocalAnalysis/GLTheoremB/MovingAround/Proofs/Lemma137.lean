module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13d

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk barOf)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff)
open scoped MatrixGroups

@[expose] def InputI2710 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (J B : Subgroup X),
    p ∣ Nat.card ↥J →
    ((∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) J) ∨ (∃ k : ℕ, IsAltType (k * p + 2) J) ∨
      (∃ n : ℕ, Nonempty (↥J ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
        (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J ∧ HasFixedPointFreeOrder ε n p)) →
    IsElemAbelian p B → B ≤ Subgroup.normalizer (J : Set X) →
    (B ⊓ J) ⊔ (B ⊓ Subgroup.centralizer (J : Set X)) = B →
    (B ⊓ J) ⊓ (B ⊓ Subgroup.centralizer (J : Set X)) = ⊥ →
    CFSG.Open.pRank p (B ⊓ J) = CFSG.Open.pRank p J →
    2 ≤ CFSG.Open.pRank p B →
    ∃ E : Subgroup X, E ≤ B ∧ Nat.card B = p ^ 2 * Nat.card ↥E ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥

@[expose] def InputOmegaTwoPerfect : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (ε : Bool) (n : ℕ), 1 ≤ n → HasFixedPointFreeOrder ε n p →
    ∀ (Y : Type) [Group Y] [Finite Y], IsOmegaTwo ε (n + 1) Y → commutator Y = ⊤


namespace Lemma137

theorem dvd_card_of_pPrimeCore_eq_bot {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    [Nontrivial H] (hH : GLAPPrimeCore p H = ⊥) : p ∣ Nat.card H := by
  by_contra hd
  have hcop : Nat.Coprime (Nat.card H) p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hd).symm
  have hle : (⊤ : Subgroup H) ≤ GLAPPrimeCore p H :=
    CFSG.le_pPrimeCore_of_normal_coprime (N := (⊤ : Subgroup H)) inferInstance
      (by rw [Subgroup.card_top]; exact hcop.symm)
  rw [hH] at hle
  have h1 : ∀ x : H, x = 1 := fun x => Subgroup.mem_bot.1 (hle (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne H
  exact hab ((h1 a).trans (h1 b).symm)

theorem mem_sup_of_comm {X : Type*} [Group X] {H K : Subgroup X}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) : ∀ x ∈ H ⊔ K, ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let S : Subgroup X :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := by
        rintro _ _ ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
        refine ⟨h1 * h2, H.mul_mem hh1 hh2, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
        calc h1 * k1 * (h2 * k2) = h1 * (k1 * h2) * k2 := by group
          _ = h1 * (h2 * k1) * k2 := by rw [hc h2 hh2 k1 hk1]
          _ = h1 * h2 * (k1 * k2) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev]
        exact (Commute.inv_inv (show Commute h k from hc h hh k hk)).eq.symm }
  intro x hx
  have hle : H ⊔ K ≤ S := by
    refine sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, (mul_one h).symm⟩)
      (fun k hk => ⟨1, H.one_mem, k, hk, (one_mul k).symm⟩)
  obtain ⟨h, hh, k, hk, hx'⟩ := hle hx
  exact ⟨h, hh, k, hk, hx'⟩

theorem inf_eq_bot_of_pGroup {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    {E Y : Subgroup H} (k : ℕ) (hk : Nat.card E = p ^ k) (hY : ¬ p ∣ Nat.card ↥Y) : E ⊓ Y = ⊥ := by
  have hd1 : Nat.card ↥(E ⊓ Y) ∣ p ^ k := hk ▸ Subgroup.card_dvd_of_le inf_le_left
  have hd2 : Nat.card ↥(E ⊓ Y) ∣ Nat.card ↥Y :=
    Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card ↥(E ⊓ Y)) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hY (h.trans hd2))).symm
  exact Subgroup.eq_bot_of_card_eq _
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hd1)

theorem pRank_map_eq_of_kernel {p : ℕ} (hp : p.Prime) {H H' : Type*} [Group H] [Finite H]
    [Group H'] [Finite H'] (f : H →* H') (A : Subgroup H)
    (hY : ¬ p ∣ Nat.card ↥(A ⊓ f.ker)) :
    CFSG.Open.pRank p (A.map f) = CFSG.Open.pRank p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hker : ∀ (E : Subgroup H), E ≤ A → ∀ k : ℕ, Nat.card E = p ^ k → E ⊓ f.ker = ⊥ := by
    intro E hEA k hk
    have h := inf_eq_bot_of_pGroup hp k hk hY
    have hEY : E ⊓ (A ⊓ f.ker) = E ⊓ f.ker := by
      rw [← inf_assoc, inf_eq_left.2 hEA]
    rwa [hEY] at h
  have hcardmap : ∀ (E : Subgroup H), E ⊓ f.ker = ⊥ → Nat.card ↥(E.map f) = Nat.card ↥E := by
    intro E hE
    have hinj : Function.Injective (f.comp E.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : (x : H) ∈ E ⊓ f.ker := Subgroup.mem_inf.2 ⟨x.2, hx⟩
      rw [hE, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact Subtype.ext hx'
    have hmap : E.map f = (⊤ : Subgroup ↥E).map (f.comp E.subtype) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
      · rintro ⟨x, -, rfl⟩
        exact ⟨x, x.2, rfl⟩
    rw [hmap, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  apply le_antisymm
  ·
    obtain ⟨E', hE'sub, hE'ab, hE'card⟩ := CFSG.SectionRank.exists_pRank hp1 (A.map f)
    have hE'comm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := fun x hx y hy => by
      have := hE'ab.1.is_comm.comm (⟨x, hx⟩ : ↥E') ⟨y, hy⟩
      exact congrArg Subtype.val this
    have hE'exp : ∀ x ∈ E', x ^ p = 1 := hE'ab.2
    set P : Subgroup H := A ⊓ Subgroup.comap f E' with hP
    have hPA : P ≤ A := inf_le_left
    have hfE : ∀ x ∈ P, f x ∈ E' := fun x hx => Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hx).2
    set g : ↥P →* H' := f.comp P.subtype with hg
    have hrange : g.range = E' := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
        rw [← hx]
        exact hfE x.1 x.2
      · intro hy
        obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.1 (hE'sub hy)
        have haP : a ∈ P := Subgroup.mem_inf.2 ⟨ha, by rw [Subgroup.mem_comap, hfa]; exact hy⟩
        exact MonoidHom.mem_range.2 ⟨⟨a, haP⟩, by simp [hg, hfa]⟩
    have hPdvd : p ^ CFSG.Open.pRank p (A.map f) ∣ Nat.card ↥P := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hE'card]
      exact dvd_mul_right _ _
    obtain ⟨K, hKcard, -⟩ := Sylow.exists_subgroup_card_pow_prime_le (n := 0) p hPdvd ⊥
      (by simp) (Nat.zero_le _)
    set S : Subgroup H := K.map P.subtype with hS
    have hSP : S ≤ P := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hScard : Nat.card ↥S = p ^ CFSG.Open.pRank p (A.map f) := by
      rw [hS, Subgroup.card_map_of_injective P.subtype_injective, hKcard]
    have hSA : S ≤ A := hSP.trans hPA
    have hSker : S ⊓ f.ker = ⊥ := hker S hSA _ hScard
    have hSfE : ∀ x ∈ S, f x ∈ E' := fun x hx => hfE x (hSP hx)
    have hSab : IsElemAbelian p S := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · have hc : ((a : H) * b) * ((b : H) * a)⁻¹ ∈ S ⊓ f.ker := by
          refine Subgroup.mem_inf.2 ⟨S.mul_mem (S.mul_mem a.2 b.2) (S.inv_mem (S.mul_mem b.2 a.2)), ?_⟩
          rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul]
          rw [hE'comm _ (hSfE a a.2) _ (hSfE b b.2)]
          group
        rw [hSker, Subgroup.mem_bot, mul_inv_eq_one] at hc
        exact Subtype.ext hc
      · have hxp : f (x ^ p) = 1 := by
          rw [map_pow]
          exact hE'exp _ (hSfE x hx)
        have hm : x ^ p ∈ S ⊓ f.ker :=
          Subgroup.mem_inf.2 ⟨S.pow_mem hx p, (MonoidHom.mem_ker).2 hxp⟩
        rw [hSker, Subgroup.mem_bot] at hm
        exact hm
    exact CFSG.SectionRank.le_pRank hp1 hSA hSab hScard
  ·
    obtain ⟨E, hEA, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 A
    have hE := hker E hEA _ hEcard
    have hmapcard := hcardmap E hE
    exact CFSG.SectionRank.le_pRank hp1 (Subgroup.map_mono hEA)
      (CFSG.SectionRank.isElemAbelian_map hEab f) (by rw [hmapcard, hEcard])

variable {G : Type} [Group G] [Finite G]

theorem one_le_pRank_of_dvd {p : ℕ} (hp : p.Prime) {H : Subgroup G} (h : p ∣ Nat.card ↥H) :
    1 ≤ CFSG.Open.pRank p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) p h
  have hxG : orderOf (x : G) = p := (orderOf_injective H.subtype H.subtype_injective x).trans hx
  have hxp : (x : G) ^ p = 1 := by rw [← hxG]; exact pow_orderOf_eq_one _
  set E : Subgroup G := Subgroup.zpowers (x : G) with hE
  have hEH : E ≤ H := (Subgroup.zpowers_le).2 x.2
  have hEcard : Nat.card E = p := by rw [hE, Nat.card_zpowers, hxG]
  have hcomm : ∀ a b : E, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    apply Subtype.ext
    exact ((Commute.refl (x : G)).zpow_zpow i j).eq
  have hpow : ∀ a ∈ E, a ^ p = 1 := by
    rintro a ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hE' : CFSG.Open.IsElemAbelian p E := ⟨⟨⟨fun a b => hcomm a b⟩⟩, hpow⟩
  exact CFSG.SectionRank.le_pRank hp.one_lt hEH hE' (k := 1) (by rw [hEcard, pow_one])

theorem pRank_barX_eq {p : ℕ} (hp : p.Prime) {N K : Subgroup G} (hKN : K ≤ N) :
    CFSG.Open.pRank p (barX p N K) = CFSG.Open.pRank p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk : (QuotientGroup.mk' (GLAPPrimeCore p ↥N)).ker = GLAPPrimeCore p ↥N :=
    QuotientGroup.ker_mk' _
  have hY : ∀ A : Subgroup ↥N, ¬ p ∣ Nat.card ↥(A ⊓ (QuotientGroup.mk' (GLAPPrimeCore p ↥N)).ker) := by
    intro A hdvd
    apply not_dvd_card_pPrimeCore hp N
    refine hdvd.trans ?_
    have hk' : Nat.card ↥(QuotientGroup.mk' (GLAPPrimeCore p ↥N)).ker =
        Nat.card ↥(GLAPPrimeCore p ↥N) := congrArg (fun S : Subgroup ↥N => Nat.card ↥S) hk
    exact (Subgroup.card_dvd_of_le inf_le_right).trans hk'.dvd
  have h1 : CFSG.Open.pRank p (barX p N K) = CFSG.Open.pRank p (K.subgroupOf N) :=
    pRank_map_eq_of_kernel hp (QuotientGroup.mk' (GLAPPrimeCore p ↥N)) (K.subgroupOf N) (hY _)
  have h2 : CFSG.Open.pRank p (K.subgroupOf N) = CFSG.Open.pRank p K := by
    rw [← pRank_map_eq_of_injective hp.one_lt N.subtype N.subtype_injective (K.subgroupOf N),
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hKN]
  exact h1.trans h2

theorem mk_mem_barX' {p : ℕ} {X K : Subgroup G} (hKX : K ≤ X) {x : G} (hx : x ∈ K) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨x, hKX hx⟩ : ↥X)) ∈ barX p X K :=
  Subgroup.mem_map.2 ⟨⟨x, hKX hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩

theorem eq_one_of_centralizes_simple {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ¬ IsMulCommutative H) {z : H} (hz : ∀ h : H, h * z = z * h) : z = 1 := by
  have hc : Subgroup.center H = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (H := Subgroup.center H) with h | h
    · exact h
    · exfalso
      apply hnc
      refine ⟨⟨fun a b => ?_⟩⟩
      have hb : b ∈ Subgroup.center H := by rw [h]; exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.1 hb a
  have hz' : z ∈ Subgroup.center H := Subgroup.mem_center_iff.2 hz
  rw [hc, Subgroup.mem_bot] at hz'
  exact hz'

theorem gLAPPrimeCoreOf_le_of_simple {p : ℕ} (hp : p.Prime) {N K : Subgroup G} (hKN : K ≤ N)
    (hsimp : IsSimpleGroup ↥(barX p N K)) (hdvd : p ∣ Nat.card ↥(barX p N K)) :
    GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hPK : GLAPPrimeCoreOf p K ≤ K := by
    intro x hx
    exact ((mem_gLAPPrimeCoreOf_iff p K x).1 hx).1
  have hPN : GLAPPrimeCoreOf p K ≤ N := hPK.trans hKN
  set P : Subgroup G := GLAPPrimeCoreOf p K with hP
  set Pt : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N) := barX p N P with hPt
  have hPtK : Pt ≤ barX p N K := barX_mono_of_le p hPK
  have hnorm : (Pt.subgroupOf (barX p N K)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hkK, hkg⟩ := (mem_barX_iff p (g : ↥N ⧸ GLAPPrimeCore p ↥N)).1 g.2
    obtain ⟨y, hyP, hyn⟩ := (mem_barX_iff p (n : ↥N ⧸ GLAPPrimeCore p ↥N)).1 hn
    have hconj : (k : G) * y * (k : G)⁻¹ ∈ GLAPPrimeCoreOf p K :=
      conj_mem_glaPPrimeCoreOf p (Subgroup.le_normalizer hkK) hyP
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (k * y * k⁻¹ : ↥N) ∈ Pt :=
      mk_mem_barX' (p := p) (X := N) (K := P) hPN hconj
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hkg, ← hyn]
    rw [← map_inv, ← map_mul, ← map_mul]
    exact hmem
  rcases Subgroup.Normal.eq_bot_or_eq_top (H := Pt.subgroupOf (barX p N K)) with hbot | htop
  · intro x hx
    have hxK : x ∈ K := hPK hx
    have hxN : x ∈ N := hKN hxK
    have hmemPt : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨x, hxN⟩ : ↥N) ∈ Pt :=
      mk_mem_barX' (p := p) (X := N) (K := P) hPN hx
    have hmemsub : (⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨x, hxN⟩ : ↥N), hPtK hmemPt⟩ :
        ↥(barX p N K)) ∈ Pt.subgroupOf (barX p N K) :=
      Subgroup.mem_subgroupOf.2 hmemPt
    rw [hbot, Subgroup.mem_bot] at hmemsub
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨x, hxN⟩ : ↥N) = 1 :=
      congrArg Subtype.val hmemsub
    have h2 : (⟨x, hxN⟩ : ↥N) ∈ GLAPPrimeCore p ↥N := by
      exact (QuotientGroup.eq_one_iff (⟨x, hxN⟩ : ↥N)).1 h1
    exact (mem_gLAPPrimeCoreOf_iff p N x).2 ⟨hxN, h2⟩
  · exfalso
    have hc1 : Nat.card ↥(Pt.subgroupOf (barX p N K)) = Nat.card ↥Pt :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPtK).toEquiv
    rw [htop, Subgroup.card_top] at hc1
    have hPN' : Nat.card ↥(P.subgroupOf N) = Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
    have hdvdP : Nat.card ↥Pt ∣ Nat.card ↥P := by
      rw [← hPN']
      exact Subgroup.card_map_dvd (P.subgroupOf N) (QuotientGroup.mk' (GLAPPrimeCore p ↥N))
    have hdvdP' : p ∣ Nat.card ↥P := by
      have h := hdvd
      rw [hc1] at h
      exact h.trans hdvdP
    exact not_dvd_card_glaPPrimeCoreOf hp K hdvdP'

theorem centBar_barX_commute {p : ℕ} (hp : p.Prime) {N K B : Subgroup G} (hKN : K ≤ N)
    (hOK : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p N) {c : G} (hc : c ∈ centBar p B K)
    (hcN : c ∈ N) :
    ∀ y ∈ barX p N K, y * QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨c, hcN⟩ : ↥N) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨c, hcN⟩ : ↥N) * y := by
  intro y hy
  obtain ⟨k, hkK, hky⟩ := (mem_barX_iff p y).1 hy
  rw [← hky]
  obtain ⟨-, γ, hγc, hγ⟩ := Sec13d.mem_centBar_iff.1 hc
  subst hγc
  have hkey : barAut p K γ (QuotientGroup.mk (⟨(k : G), hkK⟩ : ↥K)) =
      QuotientGroup.mk (⟨(k : G), hkK⟩ : ↥K) := by
    rw [hγ, MulAut.one_apply]
  rw [barAut_mk] at hkey
  have hu : (K.normalizerMonoidHom γ ⟨(k : G), hkK⟩)⁻¹ * (⟨(k : G), hkK⟩ : ↥K) ∈
      GLAPPrimeCore p ↥K :=
    QuotientGroup.eq.1 hkey
  have hu' : ((γ : G) * (k : G) * (γ : G)⁻¹)⁻¹ * (k : G) ∈ GLAPPrimeCoreOf p K :=
    (mem_gLAPPrimeCoreOf_iff p K _).2 ⟨((K.normalizerMonoidHom γ ⟨(k : G), hkK⟩)⁻¹ *
      (⟨(k : G), hkK⟩ : ↥K)).2, hu⟩
  have hcomm_K : (γ : G) * (k : G) * (γ : G)⁻¹ * (k : G)⁻¹ ∈ GLAPPrimeCoreOf p K := by
    have e : (γ : G) * (k : G) * (γ : G)⁻¹ * (k : G)⁻¹ =
        (k : G) * (((γ : G) * (k : G) * (γ : G)⁻¹)⁻¹ * (k : G))⁻¹ * (k : G)⁻¹ := by
      group
    rw [e]
    exact conj_mem_glaPPrimeCoreOf p (Subgroup.le_normalizer hkK) (Subgroup.inv_mem _ hu')
  have hcomm_N : (γ : G) * (k : G) * (γ : G)⁻¹ * (k : G)⁻¹ ∈ GLAPPrimeCoreOf p N := hOK hcomm_K
  obtain ⟨hmemN, hone⟩ := (mem_gLAPPrimeCoreOf_iff p N _).1 hcomm_N
  have hone' : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨_, hmemN⟩ : ↥N) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hone
  have hsplit : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨_, hmemN⟩ : ↥N) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨(γ : G), hcN⟩ : ↥N) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥N) k *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨(γ : G), hcN⟩ : ↥N))⁻¹ *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥N) k)⁻¹ := by
    simp only [← map_inv, ← map_mul]
    rfl
  rw [hsplit] at hone'
  calc QuotientGroup.mk' (GLAPPrimeCore p ↥N) k * QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨(γ : G), hcN⟩ : ↥N)
      = (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨(γ : G), hcN⟩ : ↥N) *
          QuotientGroup.mk' (GLAPPrimeCore p ↥N) k *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨(γ : G), hcN⟩ : ↥N))⁻¹ *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥N) k)⁻¹)⁻¹ *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨(γ : G), hcN⟩ : ↥N) *
            QuotientGroup.mk' (GLAPPrimeCore p ↥N) k) := by group
    _ = QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨(γ : G), hcN⟩ : ↥N) *
          QuotientGroup.mk' (GLAPPrimeCore p ↥N) k := by rw [hone', inv_one, one_mul]

theorem barX_centBar_mem_centralizer {p : ℕ} (hp : p.Prime) {N K B : Subgroup G} (hKN : K ≤ N)
    (hOK : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p N) (hC : centBar p B K ≤ N) :
    barX p N (centBar p B K) ≤
      Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
  intro x hx
  obtain ⟨c, hcC, rfl⟩ := (mem_barX_iff p x).1 hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact centBar_barX_commute hp hKN hOK hcC (hC hcC) h hh

theorem isElemAbelian_mono {p : ℕ} {E F : Subgroup G} (hEF : E ≤ F) (hF : IsElemAbelian p F) :
    IsElemAbelian p E := by
  have hcomm : ∀ a b : ↥E, a * b = b * a := by
    intro a b
    apply Subtype.ext
    have := hF.1.is_comm.comm (⟨(a : G), hEF a.2⟩ : ↥F) ⟨(b : G), hEF b.2⟩
    exact congrArg (fun x : ↥F => (x : G)) this
  exact ⟨⟨⟨hcomm⟩⟩, fun x hx => hF.2 x (hEF hx)⟩

theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p ↥E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩

theorem barX_sup_of_le {p : ℕ} {N X Y : Subgroup G} (hX : X ≤ N) (hY : Y ≤ N) :
    barX p N (X ⊔ Y) = barX p N X ⊔ barX p N Y := by
  unfold barX
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem conj_mem_barX {p : ℕ} {N K : Subgroup G} (hKN : K ≤ N) {b : G} (hb : b ∈ N)
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) {h : ↥N ⧸ GLAPPrimeCore p ↥N}
    (hh : h ∈ barX p N K) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N) * h *
      (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N))⁻¹ ∈ barX p N K := by
  obtain ⟨k, hkK, rfl⟩ := (mem_barX_iff p h).1 hh
  have hbk : b * (k : G) * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hbK (k : G)).1 hkK
  have e : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N) *
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) k *
      (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N))⁻¹ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b * (k : G) * b⁻¹, N.mul_mem (N.mul_mem hb k.2)
        (N.inv_mem hb)⟩ : ↥N) := by
    simp only [← map_inv, ← map_mul]
    rfl
  rw [e]
  exact mk_mem_barX' (p := p) (X := N) (K := K) hKN hbk

theorem barX_mem_normalizer {p : ℕ} {N K : Subgroup G} (hKN : K ≤ N) {b : G} (hb : b ∈ N)
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N) ∈
      Subgroup.normalizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_barX (p := p) hKN hb hbK
  · intro hh
    have hb' : b⁻¹ ∈ N := N.inv_mem hb
    have hb'K : b⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).inv_mem hbK
    have h1 := conj_mem_barX (p := p) hKN hb' hb'K hh
    have e : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b⁻¹, hb'⟩ : ↥N) =
        (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N))⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e] at h1
    have e2 : (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N))⁻¹ *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N) * h *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N))⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨b, hb⟩ : ↥N))⁻¹)⁻¹ = h := by
      group
    rw [e2] at h1
    exact h1

theorem barX_transfer {p : ℕ} (hp : p.Prime) {N K B : Subgroup G} (hKN : K ≤ N) (hBN : B ≤ N)
    (hOK : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p N) [IsSimpleGroup ↥(barX p N K)]
    (hnc : ¬ IsMulCommutative ↥(barX p N K))
    (hBdec : B = (B ⊓ K) ⊔ centBar p B K) (hBel : IsElemAbelian p B)
    (hrank : CFSG.Open.pRank p (B ⊓ K) = CFSG.Open.pRank p K) :
    barX p N B = barX p N (B ⊓ K) ⊔ barX p N (centBar p B K) ∧
    barX p N B = (barX p N B ⊓ barX p N K) ⊔
      (barX p N B ⊓ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))) ∧
    (barX p N B ⊓ barX p N K) ⊓
      (barX p N B ⊓ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))) = ⊥ ∧
    barX p N B ⊓ barX p N K = barX p N (B ⊓ K) ∧
    CFSG.Open.pRank p (barX p N B ⊓ barX p N K) = CFSG.Open.pRank p (barX p N K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hCB : centBar p B K ≤ B := fun c hc => (Sec13d.mem_centBar_iff.1 hc).1
  have hCN : centBar p B K ≤ N := hCB.trans hBN
  have hRN : B ⊓ K ≤ N := inf_le_left.trans hBN
  have hBsplit : barX p N B = barX p N (B ⊓ K) ⊔ barX p N (centBar p B K) := by
    have h1 := congrArg (barX p N) hBdec
    rw [barX_sup_of_le hRN hCN] at h1
    exact h1
  have hRK : barX p N (B ⊓ K) ≤ barX p N K := barX_mono_of_le p inf_le_right
  have hRB : barX p N (B ⊓ K) ≤ barX p N B := barX_mono_of_le p inf_le_left
  have hCc : ∀ x ∈ barX p N (centBar p B K),
      x ∈ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) :=
    fun x hx => barX_centBar_mem_centralizer hp hKN hOK hCN hx
  have hcomm : ∀ a ∈ barX p N (B ⊓ K), ∀ c ∈ barX p N (centBar p B K), a * c = c * a :=
    fun a ha c hc => (Subgroup.mem_centralizer_iff.1 (hCc c hc)) a (hRK ha)
  have hBK : barX p N B ⊓ barX p N K = barX p N (B ⊓ K) := by
    apply le_antisymm
    · rintro y ⟨hyB, hyK⟩
      rw [hBsplit] at hyB
      obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_comm hcomm _ hyB
      have hcK : c ∈ barX p N K := by
        have h1 : a⁻¹ * (a * c) ∈ barX p N K := (barX p N K).mul_mem ((barX p N K).inv_mem (hRK ha)) hyK
        simpa using h1
      have hc1 : c = 1 := by
        have h2 := eq_one_of_centralizes_simple (H := ↥(barX p N K)) hnc (z := ⟨c, hcK⟩)
          (fun h => Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hCc c hc)) h.1 h.2))
        exact congrArg Subtype.val h2
      rw [hc1, mul_one]
      exact ha
    · exact le_inf hRB hRK
  have hsplit2 : barX p N B = (barX p N B ⊓ barX p N K) ⊔
      (barX p N B ⊓ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))) := by
    apply le_antisymm
    · intro y hy
      rw [hBsplit] at hy
      obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_comm hcomm _ hy
      have haB : a ∈ barX p N B := hRB ha
      have haK : a ∈ barX p N K := hRK ha
      have hcB : c ∈ barX p N B := by
        rw [hBsplit]
        exact (le_sup_right : barX p N (centBar p B K) ≤
          barX p N (B ⊓ K) ⊔ barX p N (centBar p B K)) hc
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨haB, haK⟩)
        (Subgroup.mem_inf.2 ⟨hcB, hCc c hc⟩)
    · exact sup_le inf_le_left inf_le_left
  have hinter : (barX p N B ⊓ barX p N K) ⊓
      (barX p N B ⊓ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨-, hyK⟩, -, hyC⟩
    have h1 := eq_one_of_centralizes_simple (H := ↥(barX p N K)) hnc (z := ⟨y, hyK⟩)
      (fun h => Subtype.ext ((Subgroup.mem_centralizer_iff.1 hyC) h.1 h.2))
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1
  have hBKp : IsPGroup p ↥(B ⊓ K) := isPGroup_of_isElemAbelian (isElemAbelian_mono inf_le_left hBel)
  refine ⟨hBsplit, hsplit2, hinter, hBK, ?_⟩
  rw [hBK, rank_barX_of_isPGroup hp hBKp hRN, hrank, pRank_barX_eq hp hKN]

theorem exists_pullback {p : ℕ} (hp : p.Prime) {N B : Subgroup G} (hBN : B ≤ N)
    (hBp : IsPGroup p ↥B) {Ē : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)} (hĒ : Ē ≤ barX p N B) :
    ∃ F : Subgroup G, F ≤ B ∧ barX p N F = Ē ∧ Nat.card ↥F = Nat.card ↥Ē ∧
      Nat.card ↥B = Nat.card ↥(barX p N B) := by
  classical
  have hinj := injective_barX_comp hp hBp hBN
  have hcardB : Nat.card ↥(barX p N B) = Nat.card ↥B := by
    have hr : ((QuotientGroup.mk' (GLAPPrimeCore p ↥N)).comp (B.subgroupOf N).subtype).range =
        barX p N B := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    rw [← hr, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv]
  set F' : Subgroup ↥N := (B.subgroupOf N) ⊓ Ē.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥N)) with hF'
  set F : Subgroup G := F'.map N.subtype with hF
  have hFB : F ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hx).1
  have hFsub : F.subgroupOf N = F' := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hbarF : barX p N F = Ē := by
    unfold barX
    rw [hFsub]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hx).2
    · intro y hy
      obtain ⟨x, hxB, rfl⟩ := (mem_barX_iff p y).1 (hĒ hy)
      exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hxB,
        Subgroup.mem_comap.2 hy⟩, rfl⟩
  have hF'B : F' ≤ B.subgroupOf N := inf_le_left
  have hψ : Function.Injective ((QuotientGroup.mk' (GLAPPrimeCore p ↥N)).comp F'.subtype) := by
    intro a b hab
    apply Subtype.ext
    have hab' : (QuotientGroup.mk' (GLAPPrimeCore p ↥N)).comp (B.subgroupOf N).subtype
        ⟨a.1, hF'B a.2⟩ = (QuotientGroup.mk' (GLAPPrimeCore p ↥N)).comp (B.subgroupOf N).subtype
          ⟨b.1, hF'B b.2⟩ := hab
    have := hinj hab'
    exact congrArg (fun x : ↥(B.subgroupOf N) => (x : ↥N)) this
  have hEq1 : Nat.card ↥F = Nat.card ↥F' := by
    rw [hF, Subgroup.card_map_of_injective N.subtype_injective]
  have hEq2 : Nat.card ↥Ē = Nat.card ↥F' := by
    rw [← hbarF]
    unfold barX
    rw [hFsub]
    have hr : ((QuotientGroup.mk' (GLAPPrimeCore p ↥N)).comp F'.subtype).range = F'.map
        (QuotientGroup.mk' (GLAPPrimeCore p ↥N)) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm]
  exact ⟨F, hFB, hbarF, hEq1.trans hEq2.symm, hcardB.symm⟩

theorem map_commutator_subtype {X : Type} [Group X] (J : Subgroup X) :
    (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
  unfold commutator
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem eqv_commutator {X : Type} [Group X] (J : Subgroup X) :
    Nonempty (↥(commutator ↥J) ≃* ↥(⁅J, J⁆ : Subgroup X)) :=
  ⟨(Subgroup.equivMapOfInjective (commutator ↥J) J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_commutator_subtype J))⟩

theorem mulEquiv_commutator {H H' : Type} [Group H] [Group H'] (e : H ≃* H') :
    Nonempty (↥(commutator H) ≃* ↥(commutator H')) := by
  have h : (commutator H).map e.toMonoidHom = commutator H' := by
    unfold commutator
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
  exact ⟨(Subgroup.equivMapOfInjective (commutator H) e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr h)⟩

theorem commutator_eq_top_of_mulEquiv {H H' : Type} [Group H] [Group H'] [Finite H] [Finite H']
    (e : H ≃* H') (h : commutator H' = ⊤) : commutator H = ⊤ := by
  obtain ⟨f⟩ := mulEquiv_commutator e
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_congr f.toEquiv, h, Subgroup.card_top]
  exact (Nat.card_congr e.toEquiv).symm

theorem kt_types {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hOm : InputOmegaTwoPerfect) {Jt Kt : Subgroup X} (hKeq : Kt = ⁅Jt, Jt⁆)
    [IsSimpleGroup ↥Kt] (hnc : ¬ IsMulCommutative ↥Kt) (hdvd : p ∣ Nat.card ↥Jt)
    (hJt : (∃ k : ℕ, IsAltType (k * p + 2) ↥Jt) ∨
      (∃ k : ℕ, Nonempty (↥Jt ≃* Equiv.Perm (Fin (k * p)))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
        Nonempty (↥Jt ≃* ↥(StatedSp n (ZMod 2)))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) ↥Jt ∧ HasFixedPointFreeOrder ε n p)) :
    (∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) ↥Kt) ∨
      (∃ k : ℕ, IsAltType (k * p + 2) ↥Kt) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
        Nonempty (↥Kt ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ :
          Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) ↥Kt ∧ HasFixedPointFreeOrder ε n p) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨eK⟩ : Nonempty (↥(commutator ↥Jt) ≃* ↥Kt) :=
    ⟨(eqv_commutator Jt).some.trans (MulEquiv.subgroupCongr hKeq.symm)⟩
  have hKJ_of : commutator ↥Jt = ⊤ → Kt = Jt := by
    intro h
    rw [hKeq, ← map_commutator_subtype, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rcases hJt with ⟨k, ⟨eJ⟩⟩ | ⟨k, ⟨eJ⟩⟩ | ⟨ε, n, hn, hfp, ⟨eJ⟩⟩ | ⟨ε, n, hn, hOmJ, hfp⟩
  ·
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk : k = 0 := by omega
      subst hk
      have h2 := two_mul_nat_card_alternatingGroup (α := Fin (0 * p + 2))
      have hperm : Nat.card (Equiv.Perm (Fin (0 * p + 2))) = 2 := by
        rw [Nat.card_perm]
        simp
      rw [hperm] at h2
      have hJcard : Nat.card ↥Jt = 1 := by
        rw [Nat.card_congr eJ.toEquiv]
        omega
      rw [hJcard] at hdvd
      exact hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
    have h5 : 5 ≤ Nat.card (Fin (k * p + 2)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      nlinarith
    have hJcomm : commutator ↥Jt = ⊤ :=
      commutator_eq_top_of_mulEquiv eJ (commutator_alternatingGroup_eq_top h5)
    exact Or.inr (Or.inl ⟨k, by rw [hKJ_of hJcomm]; exact ⟨eJ⟩⟩)
  ·
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk : k = 0 := by omega
      subst hk
      have hJcard : Nat.card ↥Jt = 1 := by
        rw [Nat.card_congr eJ.toEquiv, Nat.card_perm]
        simp
      rw [hJcard] at hdvd
      exact hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
    by_cases h5 : 5 ≤ k * p
    · have h5' : 5 ≤ Nat.card (Fin (k * p)) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        exact h5
      obtain ⟨f1⟩ := mulEquiv_commutator eJ
      have hcp : commutator (Equiv.Perm (Fin (k * p))) = alternatingGroup (Fin (k * p)) :=
        alternatingGroup.commutator_perm_eq h5'
      have f3 : ↥Kt ≃* ↥(alternatingGroup (Fin (k * p))) :=
        eK.symm.trans (f1.trans (MulEquiv.subgroupCongr hcp))
      exact Or.inl ⟨k, h5, ⟨f3⟩⟩
    ·
      exfalso
      have hk2 : k ≤ 1 := by
        by_contra hc
        have : 2 * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
        omega
      have hk1' : k = 1 := by omega
      have hp4 : p ≤ 4 := by subst hk1'; omega
      have hp4' : p ≠ 4 := by rintro rfl; norm_num at hp
      have hp3' : p = 3 := by omega
      subst hk1'
      subst hp3'
      have hA3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
        have h2 := two_mul_nat_card_alternatingGroup (α := Fin 3)
        have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
          rw [Nat.card_perm, Nat.card_fin]
          rfl
        rw [hperm] at h2
        omega
      have hdvdK : Nat.card (commutator (Equiv.Perm (Fin (1 * 3)))) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le (alternatingGroup.commutator_perm_le (α := Fin 3))
        rw [hA3] at h
        exact h
      have hcardK : Nat.card ↥Kt = Nat.card ↥(commutator (Equiv.Perm (Fin (1 * 3)))) := by
        obtain ⟨f1⟩ := mulEquiv_commutator eJ
        exact Nat.card_congr (eK.symm.trans f1).toEquiv
      have hnt : Nontrivial ↥Kt := inferInstance
      have hKgt : 1 < Nat.card ↥Kt := Finite.one_lt_card_iff_nontrivial.2 hnt
      have hdvd3 : Nat.card ↥Kt ∣ 3 := by
        rw [hcardK]
        exact hdvdK
      have hK3 : Nat.card ↥Kt = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h | h
        · omega
        · exact h
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic ↥Kt := isCyclic_of_prime_card hK3
      exact hnc inferInstance
  ·
    obtain ⟨f1⟩ := mulEquiv_commutator eJ
    obtain ⟨f2⟩ := eqv_commutator (StatedSp n (ZMod 2))
    exact Or.inr (Or.inr (Or.inl ⟨ε, n, hn, hfp, ⟨eK.symm.trans (f1.trans f2)⟩⟩))
  ·
    have hJcomm : commutator ↥Jt = ⊤ := hOm p hp hp2 ε n hn hfp ↥Jt hOmJ
    exact Or.inr (Or.inr (Or.inr ⟨ε, n, hn, by rw [hKJ_of hJcomm]; exact hOmJ, hfp⟩))

theorem type2710_of_fp {X : Type} [Group X] {p : ℕ} {K : Subgroup X}
    (h : (∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) ↥K) ∨ (∃ k : ℕ, IsAltType (k * p + 2) ↥K) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
        Nonempty (↥K ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ :
          Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) ↥K ∧ HasFixedPointFreeOrder ε n p)) :
    (∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) ↥K) ∨ (∃ k : ℕ, IsAltType (k * p + 2) ↥K) ∨
      (∃ n : ℕ, Nonempty (↥K ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ :
        Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) ↥K ∧ HasFixedPointFreeOrder ε n p) := by
  rcases h with h1 | h1 | ⟨-, n, -, -, he⟩ | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl ⟨n, he⟩))
  · exact Or.inr (Or.inr (Or.inr h1))

theorem dvd_card_of_one_le_pRank {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (h : 1 ≤ CFSG.Open.pRank p H) : p ∣ Nat.card ↥H := by
  obtain ⟨E, hEH, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  have hpE : p ∣ Nat.card ↥E := by
    rw [hcard]
    exact dvd_pow_self p (by omega)
  exact hpE.trans (Subgroup.card_dvd_of_le hEH)

theorem dvd_card_kt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    {Jt Kt : Subgroup X} (hKeq : Kt = ⁅Jt, Jt⁆) (hdvd : p ∣ Nat.card ↥Jt) {j : ℕ}
    (hj : Subgroup.index (commutator ↥Jt) = 2 ^ j) : p ∣ Nat.card ↥Kt := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card ↥(commutator ↥Jt) = Nat.card ↥Kt :=
    Nat.card_congr (((eqv_commutator Jt).some.trans (MulEquiv.subgroupCongr hKeq.symm)).toEquiv)
  have hmul : Subgroup.index (commutator ↥Jt) * Nat.card ↥(commutator ↥Jt) = Nat.card ↥Jt :=
    Subgroup.index_mul_card (commutator ↥Jt)
  rw [hj, hcard] at hmul
  rw [← hmul] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  · exact h

theorem normalizer_normalizer_fwd {T : Subgroup G} {g y : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) (hy : y ∈ Subgroup.normalizer (T : Set G)) :
    g * y * g⁻¹ ∈ Subgroup.normalizer (T : Set G) := by
  have hg1 : ∀ x : G, x ∈ T ↔ g * x * g⁻¹ ∈ T := fun x => Subgroup.mem_normalizer_iff.1 hg x
  have hy1 : ∀ x : G, x ∈ T ↔ y * x * y⁻¹ ∈ T := fun x => Subgroup.mem_normalizer_iff.1 hy x
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have e1 : (g * y * g⁻¹) * t * (g * y * g⁻¹)⁻¹ = g * (y * (g⁻¹ * t * g) * y⁻¹) * g⁻¹ := by
    group
  have e3 : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
  rw [e1, ← hg1, ← hy1, hg1 (g⁻¹ * t * g), e3]

theorem mem_normalizer_normalizer_of {T : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact normalizer_normalizer_fwd hg
  · intro hy
    have h := normalizer_normalizer_fwd (Subgroup.inv_mem _ hg) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e] at h
    exact h

end Lemma137

open Lemma137

theorem lemma137_iv_of_inputs (hL133 : Lemma133Statement) (hL137i : Lemma137_iStatement)
    (hL137ii : Lemma137_ii_iiiStatement) (hPi : InputPiCenter) (hAb : InputAbIdx2)
    (hNo7 : Lemma137_noA7Statement) (hI : InputI2710) (hOm : InputOmegaTwoPerfect) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G}
      (h : Sec13 G m p B M E A D T) {L : Subgroup G}
      (hL : GLAPComponent p (Istar p M D) L) (hL1 : 3 < p ∨ 2 ≤ CFSG.Open.pRank p L),
      (∃ F : Subgroup G, F ≤ B ∧ Nat.card B ≤ p ^ 2 * Nat.card F ∧
        GLAPLayer p (barX p (Nof T) (derivedInf (Nof T ⊓ L)) ⊓
          Subgroup.centralizer ((barX p (Nof T) F : Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T))) :
            Set (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)))) ≠ ⊥) := by
  intro G _ _ m p B M E A D T h L hL hL1
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hBp : IsPGroup p ↥B := isPGroup_of_isElemAbelian hBel
  have hBN : B ≤ Nof T := hL137i h
  have hcardB : Nat.card B = p ^ m := hS.card_eq h.bOne
  have hm4 : 4 ≤ m := hS.four_le
  have h133 := (hL133 h).2 L hL
  have hPiL : IsPiGroup p (↥L ⧸ CFSG.pCore 2 ↥L) := h133.1.2.1
  have hnhL : ¬ IsHatSeven (↥L ⧸ CFSG.pCore 2 ↥L) := h133.1.2.2
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := h133.2.1
  have hrankBL : CFSG.Open.pRank p (B ⊓ L) = CFSG.Open.pRank p L := h133.2.2.2.2
  have h137 := hL137ii h hL hL1
  have hKeq := h137.1
  have hsimp : IsSimpleGroup ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) := h137.2.1
  have hnc := h137.2.2.1
  have hv := (lemma137_v_of_inputs hL133 hL137i hL137ii hPi hAb hNo7) h hL hL1
  have hBdec := hv.2.1
  have hrankK := hv.2.2
  have hΩ : ∀ (ε : Bool) (n : ℕ), IsOmegaTwo ε (n + 1) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥(StatedSp n (ZMod 2)))) := by
    intro ε n hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137.2.2.2.1 ε n hX).1 hc)
    · exact Or.inr ((h137.2.2.2.1 ε n hX).2 hc)
  have hA : ∀ k : ℕ, IsAltType (k * p + 2) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsAltType (k * p + 2) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* Equiv.Perm (Fin (k * p)))) := by
    intro k hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137.2.2.2.2 k hX).1 hc)
    · exact Or.inr ((h137.2.2.2.2 k hX).2 hc)
  obtain ⟨j, hj⟩ := Sec13d.index_pow_two_of_piType hPi hAb hp hp2 hPiL hnhL
    (fun h3 => hNo7 h hL h3) hΩ hA
  have hLnt : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := by
    haveI := hPiL.1.2
    exact Function.Surjective.nontrivial
      (f := QuotientGroup.mk (s := Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
      QuotientGroup.mk_surjective
  have hdvdL : p ∣ Nat.card ↥L :=
    (dvd_card_of_pPrimeCore_eq_bot hp hPiL.2.1).trans (Subgroup.card_quotient_dvd_card _)
  have hJt1 : 1 ≤ CFSG.Open.pRank p (barX p (Nof T) (Nof T ⊓ L)) := by
    have hBLp : IsPGroup p ↥(B ⊓ L) := Lemma137.isPGroup_of_isElemAbelian (Lemma137.isElemAbelian_mono (E := B ⊓ L) (F := B) inf_le_left hBel)
    have hBLN : B ⊓ L ≤ Nof T := inf_le_left.trans hBN
    have h1 : 1 ≤ CFSG.Open.pRank p (barX p (Nof T) (B ⊓ L)) := by
      rw [rank_barX_of_isPGroup hp hBLp hBLN, hrankBL]
      exact one_le_pRank_of_dvd hp hdvdL
    exact h1.trans (CFSG.SectionRank.pRank_mono hp1 (barX_mono_of_le p (inf_le_inf_right L hBN)))
  have hdvdJt : p ∣ Nat.card ↥(barX p (Nof T) (Nof T ⊓ L)) := Lemma137.dvd_card_of_one_le_pRank hp hJt1
  have hJtTypes : (∃ k : ℕ, IsAltType (k * p + 2) ↥(barX p (Nof T) (Nof T ⊓ L))) ∨
      (∃ k : ℕ, Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* Equiv.Perm (Fin (k * p)))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥(StatedSp n (ZMod 2)))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (Nof T ⊓ L)) ∧
        HasFixedPointFreeOrder ε n p) := by
    have hz : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := hPi _ p hp hp2 hPiL hnhL
    let hY : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    obtain ⟨-, -, hcases⟩ := hPiL
    rcases hcases with ⟨k, ⟨e⟩⟩ | ⟨n, ε, hn, hΩX, hfp⟩ | ⟨h3, ⟨e⟩⟩
    · have hAX : IsAltType (k * p + 2) (↥L ⧸ CFSG.pCore 2 ↥L) := ⟨hY.symm.trans e⟩
      rcases hA k hAX with h1 | ⟨e1⟩
      · exact Or.inl ⟨k, h1⟩
      · exact Or.inr (Or.inl ⟨k, e1⟩)
    · have hΩX' : IsOmegaTwo ε (n + 1) (↥L ⧸ CFSG.pCore 2 ↥L) :=
        Sec13d.isOmegaTwo_of_mulEquiv hY.symm hΩX
      rcases hΩ ε n hΩX' with h1 | ⟨e1⟩
      · exact Or.inr (Or.inr (Or.inr ⟨ε, n, hn, h1, hfp⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨ε, n, hn, hfp, e1⟩))
    · exact absurd ⟨hY.symm.trans e⟩ (hNo7 h hL h3)
  haveI : IsSimpleGroup ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) := hsimp
  have hKt := type2710_of_fp (kt_types hp hp2 hOm hKeq hnc hdvdJt hJtTypes)
  have hKN : derivedInf (Nof T ⊓ L) ≤ Nof T := (Sec13d.derivedInf_le _).trans inf_le_left
  have hdvdKt : p ∣ Nat.card ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) :=
    Lemma137.dvd_card_kt hp hp2 hKeq hdvdJt hj
  have hOK : GLAPPrimeCoreOf p (derivedInf (Nof T ⊓ L)) ≤ GLAPPrimeCoreOf p (Nof T) :=
    Lemma137.gLAPPrimeCoreOf_le_of_simple hp hKN hsimp hdvdKt
  have hBnorm : ∀ b ∈ B, b ∈ Subgroup.normalizer
      ((derivedInf (Nof T ⊓ L) : Subgroup G) : Set G) := by
    intro b hb
    have hN : b ∈ Subgroup.normalizer ((Nof T : Subgroup G) : Set G) :=
      Lemma137.mem_normalizer_normalizer_of (hBN hb)
    exact Sec13d.mem_normalizer_derivedInf (Sec13d.mem_normalizer_inf_of hN (hBL hb))
  have hBKnorm : barX p (Nof T) B ≤
      Subgroup.normalizer (barX p (Nof T) (derivedInf (Nof T ⊓ L)) : Set _) := by
    intro y hy
    obtain ⟨b, hbB, rfl⟩ := (mem_barX_iff p y).1 hy
    exact Lemma137.barX_mem_normalizer hKN b.2 (hBnorm _ hbB)
  obtain ⟨-, hsplit2, hdirect, -, hpRank⟩ :=
    Lemma137.barX_transfer hp hKN hBN hOK hnc hBdec hBel hrankK
  have hBtrank : 2 ≤ CFSG.Open.pRank p (barX p (Nof T) B) := by
    rw [rank_barX_of_isPGroup hp hBp hBN]
    have := CFSG.SectionRank.le_pRank hp1 (le_refl B) hBel hcardB
    omega
  have hBtel : IsElemAbelian p (barX p (Nof T) B) := isElemAbelian_barX hBel
  obtain ⟨Ē, hĒB, hcardĒ, hlay⟩ := hI (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)) p hp hp2
    (barX p (Nof T) (derivedInf (Nof T ⊓ L))) (barX p (Nof T) B) hdvdKt hKt hBtel hBKnorm
    hsplit2.symm hdirect hpRank hBtrank
  obtain ⟨F, hFB, hFbar, hFcard, hBcard⟩ := Lemma137.exists_pullback hp hBN hBp hĒB
  refine ⟨F, hFB, ?_, ?_⟩
  · have h1 : Nat.card ↥B = p ^ 2 * Nat.card ↥F := by
      rw [hBcard, hcardĒ, hFcard]
    exact le_of_eq h1
  · rw [hFbar]
    exact hlay

theorem lemma137_iv_v_of_inputs (hL133 : Lemma133Statement) (hL137i : Lemma137_iStatement)
    (hL137ii : Lemma137_ii_iiiStatement) (hPi : InputPiCenter) (hAb : InputAbIdx2)
    (hNo7 : Lemma137_noA7Statement) (hI : InputI2710) (hOm : InputOmegaTwoPerfect) :
    Lemma137_iv_vStatement := by
  intro G _ _ m p B M E A D T h L hL hL1
  exact ⟨lemma137_iv_of_inputs hL133 hL137i hL137ii hPi hAb hNo7 hI hOm h hL hL1,
    ((lemma137_v_of_inputs hL133 hL137i hL137ii hPi hAb hNo7) h hL hL1).1,
    ((lemma137_v_of_inputs hL133 hL137i hL137ii hPi hAb hNo7) h hL hL1).2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
