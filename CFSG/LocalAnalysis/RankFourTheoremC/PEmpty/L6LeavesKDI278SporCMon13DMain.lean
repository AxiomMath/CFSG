module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13DGen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13DSL
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13Bal
public import CFSG.HardMathSupport.Dickson.BMRows.M13Normal
public import CFSG.HardMathSupport.Dickson.BMRows.M13L33Invol

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup CFSG.HardMathSupport.Dickson.BMRows CFSG.HardMathSupport.Dickson.BMRows.M13L33
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalGL

theorem noSig_of_structure {G : Type} [Group G] [Finite G]
    {x c : G} (hx : orderOf x = 13) (hc : orderOf c = 13)
    {Q : Subgroup G} (hQC : Q ≤ centralizer ({x} : Set G))
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))
    (hC : Nat.card ↥(centralizer ({x} : Set G)) ≤ 451 * 936)
    (hI : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u →
      Nat.card ↥(centralizer ({u} : Set G) ⊓ centralizer ({x} : Set G)) ≤ 936)
    (hSL : SL33Thirteen)
    (hbal : ∀ R Y : Subgroup G, CFSG.Open.IsElemAbelian 13 R → Nat.card R = 13 ^ 2 → c ∈ R →
      Y ≤ centralizer ({c} : Set G) → ¬ 13 ∣ Nat.card Y →
      R ≤ normalizer (Y : Set G) → Y = ⊥)
    {S₀ : Subgroup G} (hSp : IsPGroup 13 S₀)
    (hSmax : ∀ T : Subgroup G, IsPGroup 13 T → S₀ ≤ T → T = S₀)
    (hScard : Nat.card S₀ = 13 ^ 3)
    (hSnab : ∃ a ∈ S₀, ∃ b ∈ S₀, a * b ≠ b * a)
    (hcS : c ∈ S₀) (hcc : ∀ s ∈ S₀, c * s = s * c) :
    ∀ R Y : Subgroup G, CFSG.Open.IsElemAbelian 13 R → Nat.card R = 13 ^ 2 → x ∈ R →
      Y ≤ centralizer ({x} : Set G) → ¬ 13 ∣ Nat.card Y →
      R ≤ normalizer (Y : Set G) → Y = ⊥ := by
  intro R Y hR hR2 hxR hYH hY hRY
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI hsQ : IsSimpleGroup ↥Q := isSimple_of_equiv_sl e
  have hQcard : Nat.card ↥Q = 5616 := card_of_equiv_sl e
  have hnab : ∃ a b : ↥Q, a * b ≠ b * a := noncomm_of_equiv_sl e
  have hZ := M13Normal.eq_one_of_central hnab
  set H : Subgroup G := centralizer ({x} : Set G) with hHdef
  have hxH : x ∈ H := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hQH : ∀ g ∈ H, ∀ l ∈ Q, g * l * g⁻¹ ∈ Q :=
    M13Normal.conj_mem_of_small_index hnab hQC (by rw [hQcard]; norm_num)
      (by rw [hQcard, Nat.card_zpowers, hx]; show Nat.card ↥H < 6 * (13 * 5616); omega)
  have hQx : ∀ q ∈ Q, q * x = x * q := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.1 (hQC hq)
  have hzx : ∀ k : ℤ, ∀ q ∈ Q, q * x ^ k = x ^ k * q := fun k q hq =>
    (Commute.zpow_right (hQx q hq : Commute q x) k).eq
  have hxQ : ∀ z ∈ Subgroup.zpowers x, z ∈ Q → z = 1 := by
    intro z hz hzQ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact hZ _ hzQ fun q hq => hzx k q hq
  have hcommQz : ∀ q ∈ Q, ∀ z ∈ Subgroup.zpowers x, q * z = z * q := by
    intro q hq z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact hzx k q hq
  let N : Subgroup G :=
    { carrier := {g | ∃ q ∈ Q, ∃ z ∈ Subgroup.zpowers x, g = q * z}
      mul_mem' := by
        rintro _ _ ⟨q₁, hq₁, z₁, hz₁, rfl⟩ ⟨q₂, hq₂, z₂, hz₂, rfl⟩
        refine ⟨q₁ * q₂, Q.mul_mem hq₁ hq₂, z₁ * z₂, Subgroup.mul_mem _ hz₁ hz₂, ?_⟩
        calc q₁ * z₁ * (q₂ * z₂) = q₁ * (z₁ * q₂) * z₂ := by group
          _ = q₁ * (q₂ * z₁) * z₂ := by rw [hcommQz q₂ hq₂ z₁ hz₁]
          _ = q₁ * q₂ * (z₁ * z₂) := by group
      one_mem' := ⟨1, Q.one_mem, 1, Subgroup.one_mem _, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨q, hq, z, hz, rfl⟩
        refine ⟨q⁻¹, Q.inv_mem hq, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
        have hc' : Commute q z := hcommQz q hq z hz
        rw [mul_inv_rev]
        exact (Commute.inv_inv hc').eq.symm }
  have hNH : N ≤ H := by
    rintro _ ⟨q, hq, z, hz, rfl⟩
    exact H.mul_mem (hQC hq) ((Subgroup.zpowers_le.2 hxH) hz)
  have hNcard : 13 * 5616 ≤ Nat.card ↥N := by
    let f : ↥Q × ↥(Subgroup.zpowers x) → ↥N :=
      fun p => ⟨(p.1 : G) * (p.2 : G), ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩
    have hf : Function.Injective f := by
      rintro ⟨q, z⟩ ⟨q', z'⟩ h
      have h' : (q : G) * (z : G) = (q' : G) * (z' : G) := congrArg Subtype.val h
      have hw : (q' : G)⁻¹ * (q : G) = (z' : G) * (z : G)⁻¹ := by
        calc (q' : G)⁻¹ * (q : G) = (q' : G)⁻¹ * ((q : G) * (z : G)) * (z : G)⁻¹ := by group
          _ = (q' : G)⁻¹ * ((q' : G) * (z' : G)) * (z : G)⁻¹ := by rw [h']
          _ = (z' : G) * (z : G)⁻¹ := by group
      have hwQ : (q' : G)⁻¹ * (q : G) ∈ Q := Q.mul_mem (Q.inv_mem q'.2) q.2
      have hwZ : (q' : G)⁻¹ * (q : G) ∈ Subgroup.zpowers x := by
        rw [hw]
        exact Subgroup.mul_mem _ z'.2 (Subgroup.inv_mem _ z.2)
      have hw1 := hxQ _ hwZ hwQ
      have hqq : (q : G) = q' := by
        have h2 : (q : G) = (q' : G) * ((q' : G)⁻¹ * (q : G)) := by group
        rw [h2, hw1, mul_one]
      have hzz : (z : G) = z' := by
        have h3 := h'
        rw [hqq] at h3
        exact mul_left_cancel h3
      exact Prod.ext (Subtype.ext hqq) (Subtype.ext hzz)
    have hle := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, hQcard, Nat.card_zpowers, hx] at hle
    omega
  have hQHs : Q ≤ H := hQC
  let Qh : Subgroup ↥H := Q.subgroupOf H
  haveI hQhN : Qh.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hQH (g : G) g.2 _ hn⟩
  let φ : ↥H →* MulAut ↥Qh := MulAut.conjNormal
  have hMA : Nat.card (MulAut ↥Qh) = 11232 := by
    have e' : ↥Qh ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
      (Subgroup.subgroupOfEquivOfLe hQHs).trans e
    exact card_mulAut_of_equiv_sl e'
  haveI : Finite (MulAut ↥Qh) := Nat.finite_of_card_ne_zero (by rw [hMA]; norm_num)
  let K₀ : Subgroup ↥H := φ.ker
  have hK₀C : ∀ h ∈ K₀, (h : G) ∈ centralizer (Q : Set G) := by
    intro h hh q hq
    have h1 : φ h = 1 := hh
    have key : (h : G) * q * (h : G)⁻¹ = q :=
      congrArg (fun y : ↥Qh => ((y : ↥H) : G))
        (congrArg (fun α : MulAut ↥Qh => α ⟨⟨q, hQHs hq⟩, Subgroup.mem_subgroupOf.2 hq⟩) h1)
    calc (q : G) * (h : G) = (h : G) * q * (h : G)⁻¹ * (h : G) := by rw [key]
      _ = (h : G) * q := by group
  have hcent : Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer (Q : Set G)) ≤ 19 := by
    obtain ⟨u, hu2, hu1, hu48⟩ := exists_involution_cent_ge e
    have hcm := M13Normal.card_mul_cent_le hQC hZ u
    have hu2' : (u : G) * u = 1 := by simpa using congrArg Subtype.val hu2
    have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hux : (u : G) * x = x * u := Subgroup.mem_centralizer_singleton_iff.1 (hQC u.2)
    have h936 := hI u hu2' hu1' hux
    have h1 := Nat.mul_le_mul_left
      (Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer (Q : Set G))) hu48
    have h2 := le_trans h1 (le_trans hcm h936)
    omega
  have hK₀card : Nat.card ↥K₀ ≤ 13 := by
    have hle : Nat.card ↥K₀ ≤ Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer (Q : Set G)) :=
      Nat.card_le_card_of_injective
        (fun h : ↥K₀ => (⟨(h.1 : G), Subgroup.mem_inf.2 ⟨h.1.2, hK₀C h.1 h.2⟩⟩ :
          ↥(centralizer ({x} : Set G) ⊓ centralizer (Q : Set G))))
        (by
          intro a b hab
          have hab' := congrArg (fun z : ↥(centralizer ({x} : Set G) ⊓ centralizer (Q : Set G)) =>
            (z : G)) hab
          exact Subtype.ext (Subtype.ext hab'))
    have hxK : (⟨x, hxH⟩ : ↥H) ∈ K₀ := by
      show φ _ = 1
      apply MulEquiv.ext
      intro n
      apply Subtype.ext
      apply Subtype.ext
      show x * ((n.1 : ↥H) : G) * x⁻¹ = ((n.1 : ↥H) : G)
      have hq : ((n.1 : ↥H) : G) ∈ Q := Subgroup.mem_subgroupOf.1 n.2
      rw [← hQx _ hq, mul_inv_cancel_right]
    have h13 : 13 ∣ Nat.card ↥K₀ := by
      have h := orderOf_dvd_natCard (⟨⟨x, hxH⟩, hxK⟩ : ↥K₀)
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hx] at h
    have hcard19 := le_trans hle hcent
    obtain ⟨m, hm⟩ := h13
    omega
  have hHcard : Nat.card ↥H ≤ 13 * 11232 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.range ≤ Nat.card (MulAut ↥Qh) :=
      Nat.card_le_card_of_injective (fun y : φ.range => (y : MulAut ↥Qh)) Subtype.val_injective
    rw [← h1]
    exact Nat.mul_le_mul hK₀card (h2.trans (le_of_eq hMA))
  have hRH : R ≤ H := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (hR.1.is_comm.comm (⟨r, hr⟩ : ↥R) ⟨x, hxR⟩))
  obtain ⟨d, hdR, hdQ, hd1⟩ : ∃ d : G, d ∈ R ∧ d ∈ Q ∧ d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    let f : ↥R × ↥Q → ↥H := fun p => ⟨(p.1 : G) * (p.2 : G), H.mul_mem (hRH p.1.2) (hQHs p.2.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨r, q⟩ ⟨r', q'⟩ h
      have h' : (r : G) * (q : G) = (r' : G) * (q' : G) := congrArg Subtype.val h
      have hw : (r' : G)⁻¹ * (r : G) = (q' : G) * (q : G)⁻¹ := by
        calc (r' : G)⁻¹ * (r : G) = (r' : G)⁻¹ * ((r : G) * (q : G)) * (q : G)⁻¹ := by group
          _ = (r' : G)⁻¹ * ((r' : G) * (q' : G)) * (q : G)⁻¹ := by rw [h']
          _ = (q' : G) * (q : G)⁻¹ := by group
      have hwR : (r' : G)⁻¹ * (r : G) ∈ R := R.mul_mem (R.inv_mem r'.2) r.2
      have hwQ : (r' : G)⁻¹ * (r : G) ∈ Q := by
        rw [hw]
        exact Q.mul_mem q'.2 (Q.inv_mem q.2)
      have hw1 := hcon _ hwR hwQ
      have hrr : (r : G) = r' := by
        have h2 : (r : G) = (r' : G) * ((r' : G)⁻¹ * (r : G)) := by group
        rw [h2, hw1, mul_one]
      have hqq : (q : G) = q' := by
        have h3 := h'
        rw [hrr] at h3
        exact mul_left_cancel h3
      exact Prod.ext (Subtype.ext hrr) (Subtype.ext hqq)
    have hle := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, hR2, hQcard] at hle
    omega
  have hd13 : d ^ 13 = 1 := hR.2 d hdR
  have hdord : orderOf d = 13 := orderOf_eq_prime hd13 hd1
  have hdH : d ∈ H := hQHs hdQ
  set Y₀ : Subgroup G := Y ⊓ Q with hY₀def
  have hY₀Y : Y₀ ≤ Y := inf_le_left
  have hY₀Q : Y₀ ≤ Q := inf_le_right
  have hY13 : ¬ 13 ∣ Nat.card ↥Y₀ := fun h => hY (h.trans (Subgroup.card_dvd_of_le hY₀Y))
  have hcop : Nat.Coprime 13 (Nat.card ↥Y₀) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hY13
  have hdY₀ : ∀ y ∈ Y₀, d * y * d⁻¹ ∈ Y₀ := by
    intro y hy
    refine Subgroup.mem_inf.2 ⟨?_, hQH d hdH y hy.2⟩
    exact (mem_normalizer_iff.1 (hRY hdR) y).1 hy.1
  have hfix0 : ∀ y ∈ Y₀, d * y = y * d → y = 1 := by
    intro y hy hcomm
    have hyz : y ∈ Subgroup.zpowers d :=
      centralizer_thirteen_of_equiv e hdQ hdord hy.2 hcomm.symm
    have h1 : orderOf y ∣ 13 := by
      have := orderOf_dvd_of_mem_zpowers hyz
      rwa [hdord] at this
    have h2 : orderOf y ∣ Nat.card ↥Y₀ := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : ↥Y₀)
      rwa [Subgroup.orderOf_mk] at this
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hmod : Nat.card ↥Y₀ ≡ 1 [MOD 13] := card_modEq_one_of_fixed hdord hdY₀ hfix0
  have hdvd5616 : Nat.card ↥Y₀ ∣ 5616 := by
    have := Subgroup.card_dvd_of_le hY₀Q
    rwa [hQcard] at this
  have hdvd432 : Nat.card ↥Y₀ ∣ 432 := by
    have h' : Nat.card ↥Y₀ ∣ 432 * 13 := by
      have : (432 * 13 : ℕ) = 5616 := by norm_num
      rw [this]
      exact hdvd5616
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h'
  have hcases := eq_of_dvd_432 hdvd432 (by unfold Nat.ModEq at hmod; omega)
  have hY₀bot : Y₀ = ⊥ := by
    rcases hcases with h1 | h27 | h144
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd hdY₀ (not_normalizes_of_equiv hSL e hdQ hdord hY₀Q h27)
    · exfalso
      set A : Subgroup ↥Q := Y₀.subgroupOf Q with hA
      have hAcard : Nat.card A = 144 := by
        rw [hA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY₀Q).toEquiv, h144]
      have hu : orderOf (⟨d, hdQ⟩ : ↥Q) = 13 := (Subgroup.orderOf_mk d hdQ).trans hdord
      have hdA : ∀ y ∈ A, (⟨d, hdQ⟩ : ↥Q) * y * (⟨d, hdQ⟩ : ↥Q)⁻¹ ∈ A := by
        intro y hy
        rw [hA, Subgroup.mem_subgroupOf] at hy ⊢
        simpa using hdY₀ _ hy
      have hdM : (⟨d, hdQ⟩ : ↥Q) ∈ normalizer (A : Set ↥Q) :=
        mem_normalizer_of_orderOf_thirteen hu hdA
      set M : Subgroup ↥Q := normalizer (A : Set ↥Q) with hM
      have hAM : A ≤ M := Subgroup.le_normalizer
      have h144M : 144 ∣ Nat.card ↥M := hAcard ▸ Subgroup.card_dvd_of_le hAM
      have h13M : 13 ∣ Nat.card ↥M := by
        have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hdM)
        rwa [Nat.card_zpowers, hu] at h
      have h1872 : 1872 ∣ Nat.card ↥M := by
        have : (1872 : ℕ) = 144 * 13 := by norm_num
        rw [this]
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h144M h13M
      have hMdvd : Nat.card ↥M ∣ 5616 := by
        have := Subgroup.card_subgroup_dvd_card M
        rwa [hQcard] at this
      obtain ⟨j, hj⟩ := h1872
      have hj3 : j ∣ 3 := by
        have h' : 1872 * j ∣ 1872 * 3 := by
          have : (1872 * 3 : ℕ) = 5616 := by norm_num
          rw [this, ← hj]
          exact hMdvd
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
      rcases (Nat.dvd_prime Nat.prime_three).1 hj3 with hj1 | hj1
      ·
        have hidx : M.index = 3 := by
          have h := Subgroup.card_mul_index M
          rw [hQcard, hj, hj1] at h
          omega
        have hMtop : M ≠ ⊤ := by
          intro h
          rw [h, Subgroup.card_top, hQcard] at hj
          omega
        exact false_of_index_le_three (by rw [hQcard]; norm_num) hMtop (le_of_eq hidx)
      ·
        have hMtop : M = ⊤ := Subgroup.eq_top_of_card_eq M (by rw [hQcard, hj, hj1])
        have hAnorm : A.Normal := Subgroup.normalizer_eq_top_iff.1 hMtop
        rcases Subgroup.Normal.eq_bot_or_eq_top A with h0 | h0
        · rw [h0, Subgroup.card_bot] at hAcard
          omega
        · rw [h0, Subgroup.card_top, hQcard] at hAcard
          omega
  have hYN : ∀ y ∈ Y, y ∈ N → y = 1 := by
    intro y hyY hyN
    obtain ⟨q, hq, z, hz, rfl⟩ := hyN
    have hm : orderOf (q * z) ∣ Nat.card ↥Y := by
      have := orderOf_dvd_natCard (⟨q * z, hyY⟩ : ↥Y)
      rwa [Subgroup.orderOf_mk] at this
    have hmY : ¬ 13 ∣ orderOf (q * z) := fun h => hY (h.trans hm)
    have hcomm' : Commute q z := hcommQz q hq z hz
    have hpow1 : q ^ orderOf (q * z) * z ^ orderOf (q * z) = 1 := by
      rw [← hcomm'.mul_pow, pow_orderOf_eq_one]
    have hqm : q ^ orderOf (q * z) = (z ^ orderOf (q * z))⁻¹ := eq_inv_of_mul_eq_one_left hpow1
    have hqmZ : q ^ orderOf (q * z) ∈ Subgroup.zpowers x := by
      rw [hqm]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hz _)
    have hqm1 : q ^ orderOf (q * z) = 1 := hxQ _ hqmZ (Q.pow_mem hq _)
    have hzm : z ^ orderOf (q * z) = 1 := by
      rw [hqm1, one_mul] at hpow1
      exact hpow1
    have hz1 : z = 1 := by
      have h1 : orderOf z ∣ 13 := by
        have := orderOf_dvd_of_mem_zpowers hz
        rwa [hx] at this
      have h2 : orderOf z ∣ orderOf (q * z) := orderOf_dvd_of_pow_eq_one hzm
      have h3 := Nat.dvd_gcd h1 h2
      rw [((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hmY).gcd_eq_one] at h3
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    have hqY : q ∈ Y := by
      have h := hyY
      rwa [hz1, mul_one] at h
    have hqY0 : q ∈ Y₀ := Subgroup.mem_inf.2 ⟨hqY, hq⟩
    rw [hY₀bot, Subgroup.mem_bot] at hqY0
    rw [hz1, mul_one, hqY0]
  have hY2 : Nat.card ↥Y ≤ 2 := by
    let f : ↥Y × ↥N → ↥H := fun p => ⟨(p.1 : G) * (p.2 : G), H.mul_mem (hYH p.1.2) (hNH p.2.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨y, n⟩ ⟨y', n'⟩ h
      have h' : (y : G) * (n : G) = (y' : G) * (n' : G) := congrArg Subtype.val h
      have hw : (y' : G)⁻¹ * (y : G) = (n' : G) * (n : G)⁻¹ := by
        calc (y' : G)⁻¹ * (y : G) = (y' : G)⁻¹ * ((y : G) * (n : G)) * (n : G)⁻¹ := by group
          _ = (y' : G)⁻¹ * ((y' : G) * (n' : G)) * (n : G)⁻¹ := by rw [h']
          _ = (n' : G) * (n : G)⁻¹ := by group
      have hwY : (y' : G)⁻¹ * (y : G) ∈ Y := Y.mul_mem (Y.inv_mem y'.2) y.2
      have hwN : (y' : G)⁻¹ * (y : G) ∈ N := by
        rw [hw]
        exact N.mul_mem n'.2 (N.inv_mem n.2)
      have hw1 := hYN _ hwY hwN
      have hyy : (y : G) = y' := by
        have h2 : (y : G) = (y' : G) * ((y' : G)⁻¹ * (y : G)) := by group
        rw [h2, hw1, mul_one]
      have hnn : (n : G) = n' := by
        have h3 := h'
        rw [hyy] at h3
        exact mul_left_cancel h3
      exact Prod.ext (Subtype.ext hyy) (Subtype.ext hnn)
    have hle := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at hle
    have hmul : Nat.card ↥Y * (13 * 5616) ≤ Nat.card ↥Y * Nat.card ↥N :=
      Nat.mul_le_mul_left _ hNcard
    have hsum : Nat.card ↥Y * (13 * 5616) ≤ Nat.card ↥H := le_trans hmul hle
    omega
  by_contra hne
  obtain ⟨y0, hy0Y, hy0ne⟩ : ∃ y0 ∈ Y, y0 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hcon y hy))
  have hYne : Nat.card ↥Y ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq Y h)
  have hYpos : 0 < Nat.card ↥Y := Nat.card_pos
  have hY2' : Nat.card ↥Y = 2 := by omega
  have hord2 : orderOf y0 = 2 := by
    have h := orderOf_dvd_natCard (⟨y0, hy0Y⟩ : ↥Y)
    rw [Subgroup.orderOf_mk, hY2'] at h
    rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hy0ne
    · exact h1
  have hYzp : Y = Subgroup.zpowers y0 :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hy0Y)
      (by rw [hY2', Nat.card_zpowers, hord2])).symm
  obtain ⟨g, hgz⟩ := exists_conj_mem_of_elemAbelian_sq hSp hSmax hScard hSnab hcS hcc hR hR2
  have hcomm0 : (g * c * g⁻¹) * y0 = y0 * (g * c * g⁻¹) := by
    have hw : (g * c * g⁻¹) * y0 * (g * c * g⁻¹)⁻¹ ∈ Y :=
      (mem_normalizer_iff.1 (hRY hgz) y0).1 hy0Y
    rw [hYzp] at hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hw
    have hkmod : y0 ^ k = y0 ^ (k % 2) := by
      have := zpow_mod_orderOf y0 k
      rw [hord2] at this
      simpa using this.symm
    have hk2 : k % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exfalso
        apply hy0ne
        have h1' : (g * c * g⁻¹) * y0 * (g * c * g⁻¹)⁻¹ = 1 := by
          rw [← hk, hkmod, h0, zpow_zero]
        have h2 : y0 = (g * c * g⁻¹)⁻¹ * ((g * c * g⁻¹) * y0 * (g * c * g⁻¹)⁻¹) *
            (g * c * g⁻¹) := by group
        rw [h2, h1', mul_one, inv_mul_cancel]
      · exact h1
    rw [hkmod, hk2, zpow_one] at hk
    calc (g * c * g⁻¹) * y0 = ((g * c * g⁻¹) * y0 * (g * c * g⁻¹)⁻¹) * (g * c * g⁻¹) := by group
      _ = y0 * (g * c * g⁻¹) := by rw [← hk]
  have hcommz : Commute (g * c * g⁻¹) y0 := hcomm0
  have hYC : Y ≤ centralizer ({g * c * g⁻¹} : Set G) := by
    intro y hy
    rw [hYzp] at hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.zpow_right hcommz j).eq).symm
  have hbot := inf_centralizer_eq_bot_of_conj hc hbal hR hR2 hY hRY hgz (m := g⁻¹) (k := 1)
    (by norm_num) (by rw [inv_inv, pow_one]; group)
  have hYeq : Y = ⊥ := by
    rw [← inf_eq_left.2 hYC, hbot]
  exact hne hYeq

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
