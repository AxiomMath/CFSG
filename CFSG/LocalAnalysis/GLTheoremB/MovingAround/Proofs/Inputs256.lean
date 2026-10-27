module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Norm
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcCore
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Rank
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporMathieu
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveBAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Five
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporHN
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.LyFive
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicBMData
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2b
public import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Co1Chev
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Seven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import Certificates.Certificate41501

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open GL83.CompFam
open CFSG.Yardstones.Md0ec50421ce4 (PSimple PQuot IsChevSimple)

section Generic

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem mem_of_isSCp {A : Subgroup Y} (hA : IsSCp p ⊤ A) {e : Y}
    (he : ∀ a ∈ A, a * e = e * a) (hep : e ^ p = 1) : e ∈ A := by
  have hEl : IsElemAbelian p (A ⊔ Subgroup.zpowers e) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute hA.2.1 (CFSG.Open.isElemAbelian_zpowers hep) ?_
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute a e from he a ha) i).eq
  have h := hA.2.2 _ le_top hEl le_sup_left
  rw [← h]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)

theorem inf_zpowers_eq_bot (hp : p.Prime) {H : Subgroup Y} {x : Y} (hx : x ^ p = 1)
    (hxH : x ∉ H) : H ⊓ Subgroup.zpowers x = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine eq_bot_iff.2 fun y hy => ?_
  rw [Subgroup.mem_bot]
  by_contra hy1
  obtain ⟨hyH, hyx⟩ := Subgroup.mem_inf.1 hy
  have hx1 : x ≠ 1 := fun h => hxH (h ▸ H.one_mem)
  have hxo : orderOf x = p := orderOf_eq_prime hx hx1
  have hyp : y ^ p = 1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
  have heq : Subgroup.zpowers y = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyx) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hyo]
  apply hxH
  have hxy : x ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.2 hyH) hxy

theorem card_sup_zpowers (hp : p.Prime) {H : Subgroup Y} {x : Y} (hx : x ^ p = 1) (hxH : x ∉ H)
    (hc : ∀ h ∈ H, h * x = x * h) :
    Nat.card (H ⊔ Subgroup.zpowers x : Subgroup Y) = Nat.card H * p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := fun h => hxH (h ▸ H.one_mem)
  have hxo : orderOf x = p := orderOf_eq_prime hx hx1
  have hcomm : ∀ h ∈ H, ∀ k ∈ Subgroup.zpowers x, h * k = k * h := by
    intro h hh k hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (show Commute h x from hc h hh) i).eq
  rw [card_sup_of_commute_of_inf_eq_bot hcomm (inf_zpowers_eq_bot hp hx hxH), Nat.card_zpowers, hxo]

@[expose] def actSub (K S : Subgroup Y) : Subgroup Y where
  carrier := {y | y ∈ Subgroup.normalizer (K : Set Y) ∧
    ∃ g ∈ S, g ∈ Subgroup.normalizer (K : Set Y) ∧ ∀ x ∈ K, y * x * y⁻¹ = g * x * g⁻¹}
  mul_mem' := by
    rintro y₁ y₂ ⟨h₁, g₁, hg₁, hn₁, e₁⟩ ⟨h₂, g₂, hg₂, hn₂, e₂⟩
    refine ⟨Subgroup.mul_mem _ h₁ h₂, g₁ * g₂, S.mul_mem hg₁ hg₂, Subgroup.mul_mem _ hn₁ hn₂,
      fun x hx => ?_⟩
    have hx' : g₂ * x * g₂⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hn₂ x).1 hx
    calc y₁ * y₂ * x * (y₁ * y₂)⁻¹ = y₁ * (y₂ * x * y₂⁻¹) * y₁⁻¹ := by group
      _ = y₁ * (g₂ * x * g₂⁻¹) * y₁⁻¹ := by rw [e₂ x hx]
      _ = g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := e₁ _ hx'
      _ = g₁ * g₂ * x * (g₁ * g₂)⁻¹ := by group
  one_mem' := ⟨Subgroup.one_mem _, 1, S.one_mem, Subgroup.one_mem _, fun x _ => by group⟩
  inv_mem' := by
    rintro y ⟨h, g, hg, hn, e⟩
    refine ⟨Subgroup.inv_mem _ h, g⁻¹, S.inv_mem hg, Subgroup.inv_mem _ hn, fun x hx => ?_⟩
    have hw : y⁻¹ * x * y ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h) x).1 hx
      simpa using this
    have h1 := e _ hw
    have h2 : x = g * (y⁻¹ * x * y) * g⁻¹ := by rw [← h1]; group
    calc y⁻¹ * x * y⁻¹⁻¹ = g⁻¹ * (g * (y⁻¹ * x * y) * g⁻¹) * g := by group
      _ = g⁻¹ * x * g⁻¹⁻¹ := by rw [← h2, inv_inv]

theorem mem_actSub_of_center {K S : Subgroup Y} {z : Y} (hz : z ∈ Subgroup.center Y) :
    z ∈ actSub K S := by
  have hzc : ∀ y : Y, y * z = z * y := fun y => Subgroup.mem_center_iff.1 hz y
  have hzx : ∀ x : Y, z * x * z⁻¹ = x := fun x => by rw [← hzc x]; group
  refine ⟨Subgroup.mem_normalizer_iff.2 fun x => by rw [hzx], 1, S.one_mem, Subgroup.one_mem _,
    fun x _ => ?_⟩
  rw [hzx]
  group

theorem mem_actSub_of_act {K S : Subgroup Y} {y g : Y} (hy : y ∈ Subgroup.normalizer (K : Set Y))
    (hgS : g ∈ S) (hgK : g ∈ K) (h : ∀ x ∈ K, y * x * y⁻¹ = g * x * g⁻¹) : y ∈ actSub K S :=
  ⟨hy, g, hgS, Subgroup.le_normalizer hgK, h⟩

theorem eq_of_act_eq (hp : p.Prime) {K : Subgroup Y} (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    {x y : Y} (hx : x ∈ K) (hy : y ∈ K) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (h : ∀ w ∈ K, x * w * x⁻¹ = y * w * y⁻¹) : x = y := by
  set c := y⁻¹ * x with hc
  have hcK : c ∈ K := K.mul_mem (K.inv_mem hy) hx
  have hcc : ∀ w ∈ K, c * w = w * c := by
    intro w hw
    have h1 := h w hw
    calc c * w = y⁻¹ * (x * w * x⁻¹) * x := by rw [hc]; group
      _ = y⁻¹ * (y * w * y⁻¹) * x := by rw [h1]
      _ = w * c := by rw [hc]; group
  have hcy : Commute y c := (hcc y hy).symm
  have hcp : c ^ p = 1 := by
    have hxyc : x = y * c := by rw [hc]; group
    have h2 : x ^ p = y ^ p * c ^ p := by rw [hxyc]; exact hcy.mul_pow p
    rw [hxp, hyp, one_mul] at h2
    exact h2.symm
  have hc1 : c = 1 := InputsSeitz.eq_one_of_mem_center hp hZ hcK hcc hcp
  calc x = y * c := by rw [hc]; group
    _ = y := by rw [hc1, mul_one]

theorem card_le_sq_of_lt (hp : p.Prime) {A N : Subgroup Y} (hAel : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 3) (hNA : N ≤ A) (hne : N ≠ A) : Nat.card N ≤ p ^ 2 := by
  have hdvd : Nat.card N ∣ p ^ 3 := hAc ▸ Subgroup.card_dvd_of_le hNA
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rw [hj]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hj2
  have hj3' : j = 3 := by omega
  apply hne
  exact Subgroup.eq_of_le_of_card_ge hNA (by rw [hAc, hj, hj3'])

theorem false_of_sq_le_zpowers (hp : p.Prime) {E : Subgroup Y} {x : Y} (hx : x ^ p = 1)
    (hE : p ^ 2 ≤ Nat.card E) (hEx : E ≤ Subgroup.zpowers x) : False := by
  have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hEx
  have h2 : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hx)
  have h3 : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  omega

theorem pow_eq_one_of_mem_zpowers {k x : Y} (hk : k ^ p = 1) (hx : x ∈ Subgroup.zpowers k) :
    x ^ p = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem false_of_isSCp (hp : p.Prime) {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    (hinn : ∀ y ∈ Subgroup.normalizer (K : Set Y), y ^ p = 1 →
      ∃ k ∈ K, k ^ p = 1 ∧ ∀ x ∈ K, y * x * y⁻¹ = k * x * k⁻¹)
    (hiso : ∀ k ∈ K, k ^ p = 1 →
      ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ p ^ 2 ≤ Nat.card E ∧ k ∈ E)
    {d : Y} (hdN : d ∈ Subgroup.normalizer (K : Set Y)) (hdK : ∃ x ∈ K, d * x * d⁻¹ ≠ x)
    (hplane : ∀ k ∈ K, k ^ p = 1 → (∀ x ∈ K, d * x * d⁻¹ = k * x * k⁻¹) →
      ∀ a ∈ K, a ^ p = 1 → a * k = k * a →
      ∃ e ∈ K, e ^ p = 1 ∧ e * k = k * e ∧ e * a = a * e ∧
        e ∉ actSub K (Subgroup.closure ({k, a} : Set Y)))
    {A : Subgroup Y} (hA : IsSCp p ⊤ A) (hdA : d ∈ A) (hAc : Nat.card A = p ^ 3)
    {z : Y} (hzA : z ∈ A) (hzZ : z ∈ Subgroup.center Y) (hz1 : z ≠ 1) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAel : IsElemAbelian p A := hA.2.1
  have hApow : ∀ a ∈ A, a ^ p = 1 := hAel.2
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => elem_comm hAel ha hb
  have hzc : ∀ y : Y, y * z = z * y := fun y => Subgroup.mem_center_iff.1 hzZ y
  have hzN : z ∈ Subgroup.normalizer (K : Set Y) := (mem_actSub_of_center (S := ⊥) hzZ).1
  have hH1 : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hApow z hzA) hz1]
  have hH1A : Subgroup.zpowers z ≤ A := Subgroup.zpowers_le.2 hzA
  have hdz : d ∉ Subgroup.zpowers z := by
    intro h
    have hle : Subgroup.zpowers z ≤ actSub K ⊥ := Subgroup.zpowers_le.2 (mem_actSub_of_center hzZ)
    obtain ⟨-, g, hg, -, hge⟩ := hle h
    rw [Subgroup.mem_bot] at hg
    subst hg
    obtain ⟨x, hx, hne⟩ := hdK
    exact hne (by rw [hge x hx]; group)
  have hH2 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers d : Subgroup Y) = p ^ 2 := by
    rw [card_sup_zpowers hp (hApow d hdA) hdz (fun h hh => hAcomm h (hH1A hh) d hdA), hH1, sq]
  have hH2A : Subgroup.zpowers z ⊔ Subgroup.zpowers d ≤ A := sup_le hH1A (Subgroup.zpowers_le.2 hdA)
  obtain ⟨kd, hkdK, hkdp, hkd⟩ := hinn d hdN (hApow d hdA)
  obtain ⟨E, hEK, hEel, hEcard, hkdE⟩ := hiso kd hkdK hkdp
  have hEcomm : ∀ e ∈ E, e * kd = kd * e := fun e he => elem_comm hEel he hkdE
  have hEd : ∀ e ∈ E, d * e * d⁻¹ = e := fun e he => by
    rw [hkd e (hEK he), ← hEcomm e he, mul_inv_cancel_right]
  have hdact : d ∈ actSub K (Subgroup.zpowers kd) :=
    mem_actSub_of_act hdN (Subgroup.mem_zpowers kd) hkdK hkd
  by_cases hAN : A ≤ Subgroup.normalizer (K : Set Y)
  · by_cases hall : A ≤ actSub K (Subgroup.zpowers kd)
    ·
      have hEA : E ≤ A := by
        intro e he
        refine mem_of_isSCp hA (fun a ha => ?_) (hEel.2 e he)
        obtain ⟨-, g, hg, -, hge⟩ := hall ha
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        have h1 := hge e (hEK he)
        have h2 : kd ^ i * e * (kd ^ i)⁻¹ = e := by
          have hc : Commute (kd ^ i) e := (Commute.zpow_left (show Commute kd e from
            (hEcomm e he).symm) i)
          rw [hc.eq, mul_inv_cancel_right]
        calc a * e = a * e * a⁻¹ * a := by group
          _ = e * a := by rw [h1, h2]
      have hEz : E ≤ Subgroup.zpowers kd := by
        intro e he
        obtain ⟨-, g, hg, -, hge⟩ := hall (hEA he)
        have hgK : g ∈ K := (Subgroup.zpowers_le.2 hkdK) hg
        rw [eq_of_act_eq hp hZ (hEK he) hgK (hEel.2 e he) (pow_eq_one_of_mem_zpowers hkdp hg) hge]
        exact hg
      exact false_of_sq_le_zpowers hp hkdp hEcard hEz
    ·
      obtain ⟨a, haA, ha⟩ := SetLike.not_le_iff_exists.1 hall
      obtain ⟨ka, hkaK, hkap, hka⟩ := hinn a (hAN haA) (hApow a haA)
      have hka' : ∀ w ∈ K, ka⁻¹ * w * ka = a⁻¹ * w * a := by
        intro w hw
        have hw1 : a⁻¹ * w * a ∈ K := by
          have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hAN haA)) w).1 hw
          simpa using this
        have h1 := hka _ hw1
        have h2 : w = ka * (a⁻¹ * w * a) * ka⁻¹ := by rw [← h1]; group
        calc ka⁻¹ * w * ka = ka⁻¹ * (ka * (a⁻¹ * w * a) * ka⁻¹) * ka := by rw [← h2]
          _ = a⁻¹ * w * a := by group
      have hcomm : ka * kd = kd * ka := by
        have hx : ka * kd * ka⁻¹ ∈ K := K.mul_mem (K.mul_mem hkaK hkdK) (K.inv_mem hkaK)
        have hxp : (ka * kd * ka⁻¹) ^ p = 1 := by rw [conj_pow, hkdp, mul_one, mul_inv_cancel]
        have hact : ∀ w ∈ K, (ka * kd * ka⁻¹) * w * (ka * kd * ka⁻¹)⁻¹ = kd * w * kd⁻¹ := by
          intro w hw
          have hw1 : a⁻¹ * w * a ∈ K := by
            have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hAN haA)) w).1 hw
            simpa using this
          have hw2 : kd * (a⁻¹ * w * a) * kd⁻¹ ∈ K :=
            K.mul_mem (K.mul_mem hkdK hw1) (K.inv_mem hkdK)
          have hda : a * d * a⁻¹ = d := by rw [hAcomm a haA d hdA]; group
          calc (ka * kd * ka⁻¹) * w * (ka * kd * ka⁻¹)⁻¹
              = ka * (kd * (ka⁻¹ * w * ka) * kd⁻¹) * ka⁻¹ := by group
            _ = ka * (kd * (a⁻¹ * w * a) * kd⁻¹) * ka⁻¹ := by rw [hka' w hw]
            _ = a * (kd * (a⁻¹ * w * a) * kd⁻¹) * a⁻¹ := (hka _ hw2).symm
            _ = a * (d * (a⁻¹ * w * a) * d⁻¹) * a⁻¹ := by rw [hkd _ hw1]
            _ = (a * d * a⁻¹) * w * (a * d * a⁻¹)⁻¹ := by group
            _ = d * w * d⁻¹ := by rw [hda]
            _ = kd * w * kd⁻¹ := hkd w hw
        have h1 := eq_of_act_eq hp hZ hx hkdK hxp hkdp hact
        calc ka * kd = ka * kd * ka⁻¹ * ka := by group
          _ = kd * ka := by rw [h1]
      obtain ⟨e, heK, hep, hek, hea, hnot⟩ := hplane kd hkdK hkdp hkd ka hkaK hkap hcomm
      set S2 : Subgroup Y := Subgroup.closure ({kd, ka} : Set Y) with hS2
      have hS2e : S2 ≤ Subgroup.centralizer ({e} : Set Y) := by
        rw [hS2, Subgroup.closure_le]
        rintro x (rfl | hx)
        · exact Subgroup.mem_centralizer_singleton_iff.2 hek.symm
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact Subgroup.mem_centralizer_singleton_iff.2 hea.symm
      have hkdS2 : kd ∈ S2 := Subgroup.subset_closure (by simp)
      have hkaS2 : ka ∈ S2 := Subgroup.subset_closure (by simp)
      have hAS : A ≤ actSub K S2 := by
        by_contra hnle
        obtain ⟨a', ha'A, ha'⟩ := SetLike.not_le_iff_exists.1 hnle
        have ha2 : a ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers d := by
          intro h
          have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers d ≤ actSub K (Subgroup.zpowers kd) :=
            sup_le (Subgroup.zpowers_le.2 (mem_actSub_of_center hzZ)) (Subgroup.zpowers_le.2 hdact)
          exact ha (hle h)
        have hH3 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a :
            Subgroup Y) = p ^ 3 := by
          rw [card_sup_zpowers hp (hApow a haA) ha2 (fun h hh => hAcomm h (hH2A hh) a haA), hH2]
          ring
        have hH3A : Subgroup.zpowers z ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a ≤ A :=
          sup_le hH2A (Subgroup.zpowers_le.2 haA)
        have ha'3 : a' ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a := by
          intro h
          have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a ≤ actSub K S2 :=
            sup_le (sup_le (Subgroup.zpowers_le.2 (mem_actSub_of_center hzZ))
              (Subgroup.zpowers_le.2 (mem_actSub_of_act hdN hkdS2 hkdK hkd)))
              (Subgroup.zpowers_le.2 (mem_actSub_of_act (hAN haA) hkaS2 hkaK hka))
          exact ha' (hle h)
        have hH4 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a ⊔
            Subgroup.zpowers a' : Subgroup Y) = p ^ 4 := by
          rw [card_sup_zpowers hp (hApow a' ha'A) ha'3 (fun h hh => hAcomm h (hH3A hh) a' ha'A), hH3]
          ring
        have hH4A : Subgroup.zpowers z ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a ⊔
            Subgroup.zpowers a' ≤ A := sup_le hH3A (Subgroup.zpowers_le.2 ha'A)
        have h1 := Subgroup.card_le_of_le hH4A
        rw [hH4, hAc] at h1
        have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
        omega
      have heA : e ∈ A := by
        refine mem_of_isSCp hA (fun a' ha' => ?_) hep
        obtain ⟨-, g, hg, -, hge⟩ := hAS ha'
        have h1 := hge e heK
        have h2 : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.1 (hS2e hg)
        calc a' * e = a' * e * a'⁻¹ * a' := by group
          _ = g * e * g⁻¹ * a' := by rw [h1]
          _ = e * a' := by rw [h2, mul_inv_cancel_right]
      exact hnot (hAS heA)
  ·
    obtain ⟨b, hbA, hbN⟩ := SetLike.not_le_iff_exists.1 hAN
    have hF := isFam_conjSet hAel hK
    have hbstab : b ∉ stab A K := fun h => hbN (Subgroup.mem_inf.1 h).2
    have hc : NormComm p K b := hF.normComm (mem_conjSet_self A K) hbA hbstab
    have hb3 : b ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers d := by
      intro h
      exact hbN ((sup_le (Subgroup.zpowers_le.2 hzN) (Subgroup.zpowers_le.2 hdN)) h)
    have hH3 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers b :
        Subgroup Y) = p ^ 3 := by
      rw [card_sup_zpowers hp (hApow b hbA) hb3 (fun h hh => hAcomm h (hH2A hh) b hbA), hH2]
      ring
    have hH3A : Subgroup.zpowers z ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers b = A :=
      Subgroup.eq_of_le_of_card_ge (sup_le hH2A (Subgroup.zpowers_le.2 hbA)) (by rw [hH3, hAc])
    let ν : ↥E →* Y := (normHom hc).comp (Subgroup.inclusion hEK)
    have hνapp : ∀ x : ↥E, ν x = normPi hc (fun _ => Subgroup.inclusion hEK x) := fun _ => rfl
    have hνd : ∀ x : ↥E, d * ν x = ν x * d := by
      intro x
      rw [hνapp, normPi_apply]
      refine (Finset.noncommProd_commute _ _ _ d fun i _ => ?_).eq
      rw [cjEmb_apply]
      have hdb : Commute d (b ^ i.val) := Commute.pow_right (hAcomm d hdA b hbA) i.val
      have hdx : Commute d (Subgroup.inclusion hEK x : Y) := by
        show d * (x : Y) = (x : Y) * d
        calc d * (x : Y) = d * x * d⁻¹ * d := by group
          _ = x * d := by rw [hEd x x.2]
      exact (hdb.mul_right hdx).mul_right hdb.inv_right
    have hνp : ∀ x : ↥E, (ν x) ^ p = 1 := by
      intro x
      have hxp : x ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hEel.2 x x.2)
      rw [← map_pow, hxp, map_one]
    have hνA : ∀ x : ↥E, ν x ∈ A := by
      intro x
      refine mem_of_isSCp hA (fun a ha => ?_) (hνp x)
      rw [← hH3A] at ha
      have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers b ≤
          Subgroup.centralizer ({ν x} : Set Y) := by
        refine sup_le (sup_le ?_ ?_) ?_
        · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hzc (ν x)).symm)
        · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hνd x))
        · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
          have h1 := normHom_fixed hc (hApow b hbA) (Subgroup.inclusion hEK x)
          calc b * ν x = b * ν x * b⁻¹ * b := by group
            _ = ν x * b := by rw [show b * ν x * b⁻¹ = ν x from h1]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
    have hνinj : Function.Injective ν := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hker : Subgroup.inclusion hEK x ∈ (normHom hc).ker := hx
      have hcen := normHom_ker_le_center hc hker
      apply Subtype.ext
      show (x : Y) = 1
      refine InputsSeitz.eq_one_of_mem_center hp hZ (hEK x.2) (fun y hy => ?_) (hEel.2 x x.2)
      have h1 := Subgroup.mem_center_iff.1 hcen ⟨y, hy⟩
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion] at h2
      exact h2.symm
    set F : Subgroup Y := ν.range with hF
    have hFcard : Nat.card F = Nat.card E :=
      (Nat.card_congr (MonoidHom.ofInjective hνinj).toEquiv).symm
    have hνdec : ∀ x : ↥E, ∃ δ ∈ Subgroup.centralizer (K : Set Y), ν x = (x : Y) * δ := by
      intro x
      obtain ⟨δ, hδ, hνx⟩ := normHom_decomp hc (Subgroup.inclusion hEK x)
      exact ⟨δ, hδ, hνx⟩
    have hFN : F ≤ A ⊓ Subgroup.normalizer (K : Set Y) := by
      rintro _ ⟨x, rfl⟩
      refine ⟨hνA x, ?_⟩
      obtain ⟨δ, hδ, hνx⟩ := hνdec x
      rw [hνx]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer (hEK x.2))
        (Subgroup.centralizer_le_normalizer _ hδ)
    have hFz : F ⊓ Subgroup.zpowers z = ⊥ := by
      refine eq_bot_iff.2 fun y hy => ?_
      obtain ⟨hyF, hyz⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨x, rfl⟩ := hyF
      rw [Subgroup.mem_bot]
      have hyc : ν x ∈ Subgroup.center Y := (Subgroup.zpowers_le.2 hzZ) hyz
      obtain ⟨δ, hδ, hνx⟩ := hνdec x
      have hx1 : (x : Y) = 1 := by
        refine InputsSeitz.eq_one_of_mem_center hp hZ (hEK x.2) (fun w hw => ?_) (hEel.2 x x.2)
        have hxe : (x : Y) = ν x * δ⁻¹ := by rw [hνx]; group
        have hδw : δ⁻¹ * w = w * δ⁻¹ :=
          (Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ hδ) w hw).symm
        rw [hxe]
        calc ν x * δ⁻¹ * w = ν x * (w * δ⁻¹) := by rw [mul_assoc, hδw]
          _ = (ν x * w) * δ⁻¹ := by group
          _ = (w * ν x) * δ⁻¹ := by rw [(Subgroup.mem_center_iff.1 hyc w).symm]
          _ = w * (ν x * δ⁻¹) := by group
      have hx : x = 1 := Subtype.ext hx1
      rw [hx, map_one]
    have hFzc : ∀ f ∈ F, ∀ k ∈ Subgroup.zpowers z, f * k = k * f := by
      intro f _ k hk
      exact Subgroup.mem_center_iff.1 ((Subgroup.zpowers_le.2 hzZ) hk) f
    have hcardFz : Nat.card (F ⊔ Subgroup.zpowers z : Subgroup Y) = Nat.card E * p := by
      rw [card_sup_of_commute_of_inf_eq_bot hFzc hFz, hFcard, hH1]
    have hFzN : F ⊔ Subgroup.zpowers z ≤ A ⊓ Subgroup.normalizer (K : Set Y) :=
      sup_le hFN (le_inf hH1A (Subgroup.zpowers_le.2 hzN))
    have hNne : A ⊓ Subgroup.normalizer (K : Set Y) ≠ A := fun h =>
      hbN (Subgroup.mem_inf.1 (h.ge hbA)).2
    have hNle := card_le_sq_of_lt hp hAel hAc inf_le_left hNne
    have h1 := Subgroup.card_le_of_le hFzN
    rw [hcardFz] at h1
    have h2 : p ^ 2 * p ≤ Nat.card E * p := Nat.mul_le_mul_right p hEcard
    have h3 : p ^ 2 < p ^ 2 * p := by
      have hp2 := hp.two_le
      have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith
    omega

end Generic

section Lift

open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom centerQuotientHom_injective
  onCenterQuotient onCenterQuotient_apply_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem conj_injective_of_center {S : Type*} [Group S] (hcen : Subgroup.center S = ⊥) {a b : S}
    (h : MulAut.conj a = MulAut.conj b) : a = b := by
  have hc : b⁻¹ * a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun f : MulAut S => f g) h
    simp only [MulAut.conj_apply] at h1
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
      _ = b⁻¹ * a * g := by group
  rw [hcen, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem coprime_ker_mk' {G : Type*} [Group G] (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center G)) :
    Nat.Coprime (Nat.card (QuotientGroup.mk' (Subgroup.center G)).ker) p := by
  rw [QuotientGroup.ker_mk']
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hZ)

theorem exists_inner_of_pow (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup Y}
    (hperf : commutator ↥K = ⊤) (hcen : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥)
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥K ⧸ Subgroup.center ↥K)) ≤ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {y : Y}
    (hy : y ∈ Subgroup.normalizer (K : Set Y)) (hyp : y ^ p = 1) :
    ∃ k ∈ K, k ^ p = 1 ∧ ∀ x ∈ K, y * x * y⁻¹ = k * x * k⁻¹ := by
  haveI : Group.IsPerfect ↥K := ⟨hperf⟩
  set β : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨y, hy⟩ with hβ
  have hβapp : ∀ k : ↥K, ((β k : ↥K) : Y) = y * k * y⁻¹ := fun k => rfl
  have hβp : β ^ p = 1 := by
    rw [hβ, ← map_pow]
    have h1 : (⟨y, hy⟩ : Subgroup.normalizer (K : Set Y)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hyp)
    rw [h1, map_one]
  obtain ⟨s, hs, hsp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen
    hout (centerQuotientHom ↥K β) (by rw [← map_pow, hβp, map_one])
  obtain ⟨k, hk, hkp⟩ := CFSG.StandardType.OrdPInnerExc.exists_preimage_pow_eq_one hp
    (coprime_ker_mk' hp hZ) (MonoidHom.mem_range.2 (QuotientGroup.mk'_surjective _ s)) hsp
  have hconj : MulAut.conj k = β := by
    apply centerQuotientHom_injective ↥K
    rw [← hs, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj, hk]
  refine ⟨k, k.2, by rw [← Subgroup.coe_pow, hkp, Subgroup.coe_one], fun x hx => ?_⟩
  have h1 := congrArg (fun f : MulAut ↥K => ((f ⟨x, hx⟩ : ↥K) : Y)) hconj
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  rw [← hβapp ⟨x, hx⟩]
  exact h1.symm

theorem exists_elemAbelian_of_quot (hp : p.Prime) {K : Subgroup Y}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    (hE₀ : ∃ E₀ : Subgroup (↥K ⧸ Subgroup.center ↥K), IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2)
    {k : Y} (hk : k ∈ K) (hkp : k ^ p = 1) :
    ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ p ^ 2 ≤ Nat.card E ∧ k ∈ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  set k' : ↥K := ⟨k, hk⟩ with hk'
  have hk'p : k' ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hkp)
  set π := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  obtain ⟨B, hB, hBc, hkB⟩ : ∃ B : Subgroup (↥K ⧸ Subgroup.center ↥K), IsElemAbelian p B ∧
      p ^ 2 ≤ Nat.card B ∧ π k' ∈ B := by
    by_cases h1 : π k' = 1
    · obtain ⟨E₀, hE₀el, hE₀c⟩ := hE₀
      exact ⟨E₀, hE₀el, hE₀c.ge, h1 ▸ E₀.one_mem⟩
    · have ho : orderOf (π k') = p :=
        orderOf_eq_prime (by rw [← map_pow, hk'p, map_one]) h1
      exact CFSG.HardMathSupport.Dickson.I271.exists_elemAbelian_sq_of_mem hp hE₀ ho
  have hkc : π.ker ≤ Subgroup.center ↥K := by rw [hπ, QuotientGroup.ker_mk']
  obtain ⟨A, hA, hkA, hAc⟩ := CFSG.StandardType.OrdPInnerExc.exists_elemAbelian_lift_mem hp hkc
    (coprime_ker_mk' hp hZ) hB (fun b _ => MonoidHom.mem_range.2 (QuotientGroup.mk'_surjective _ b))
    hk'p hkB
  refine ⟨A.map K.subtype, Subgroup.map_subtype_le A, CFSG.SectionRank.isElemAbelian_map hA _, ?_,
    ⟨k', hkA, rfl⟩⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact hBc.trans hAc

@[expose] def PlaneOK (p : ℕ) {T : Type*} [Group T] (s : T) : Prop :=
  ∀ a : T, a * s = s * a → a ^ p = 1 → ∃ e : T, e ^ p = 1 ∧ e * s = s * e ∧ e * a = a * e ∧
    e ∉ Subgroup.closure ({s, a} : Set T)

theorem PlaneOK.of_mulEquiv {T T' : Type*} [Group T] [Group T'] (σ : T ≃* T') {s : T}
    (h : PlaneOK p s) : PlaneOK p (σ s) := by
  intro a has hap
  have has' : σ.symm a * s = s * σ.symm a := by
    apply σ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, has]
  have hap' : (σ.symm a) ^ p = 1 := by rw [← map_pow, hap, map_one]
  obtain ⟨e, hep, hes, hea, hne⟩ := h _ has' hap'
  refine ⟨σ e, by rw [← map_pow, hep, map_one], by rw [← map_mul, hes, map_mul],
    by rw [← MulEquiv.apply_symm_apply σ a, ← map_mul, hea, map_mul], fun hmem => hne ?_⟩
  have h1 : σ.symm (σ e) ∈ (Subgroup.closure ({σ s, a} : Set T')).map σ.symm.toMonoidHom :=
    Subgroup.mem_map_of_mem _ hmem
  rw [MonoidHom.map_closure, Set.image_pair] at h1
  simpa using h1

theorem hplane_of_planeOK (hp : p.Prime) {K : Subgroup Y} (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    {d : Y} (hP : ∀ (k : Y) (hk : k ∈ K), k ^ p = 1 → (∀ x ∈ K, d * x * d⁻¹ = k * x * k⁻¹) →
      PlaneOK p (QuotientGroup.mk' (Subgroup.center ↥K) ⟨k, hk⟩)) :
    ∀ k ∈ K, k ^ p = 1 → (∀ x ∈ K, d * x * d⁻¹ = k * x * k⁻¹) →
      ∀ a ∈ K, a ^ p = 1 → a * k = k * a →
      ∃ e ∈ K, e ^ p = 1 ∧ e * k = k * e ∧ e * a = a * e ∧
        e ∉ actSub K (Subgroup.closure ({k, a} : Set Y)) := by
  intro k hk hkp hkd a ha hap hak
  set π := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  have hkc : π.ker ≤ Subgroup.center ↥K := by rw [hπ, QuotientGroup.ker_mk']
  have hcop := coprime_ker_mk' (G := ↥K) hp hZ
  set k' : ↥K := ⟨k, hk⟩
  set a' : ↥K := ⟨a, ha⟩
  have hk'p : k' ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hkp)
  have ha'p : a' ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hap)
  have hak' : a' * k' = k' * a' := Subtype.ext (by simpa using hak)
  obtain ⟨eb, hebp, hebs, heba, hebn⟩ := hP k hk hkp hkd (π a') (by rw [← map_mul, hak', map_mul])
    (by rw [← map_pow, ha'p, map_one])
  obtain ⟨e', he', he'p⟩ := CFSG.StandardType.OrdPInnerExc.exists_preimage_pow_eq_one hp hcop
    (MonoidHom.mem_range.2 (QuotientGroup.mk'_surjective _ eb)) hebp
  have hek : e' * k' = k' * e' := CFSG.StandardType.OrdPInnerExc.commute_of_lift hkc hcop he'p
    (by rw [he']; exact hebs)
  have hea : e' * a' = a' * e' := CFSG.StandardType.OrdPInnerExc.commute_of_lift hkc hcop he'p
    (by rw [he']; exact heba)
  refine ⟨e', e'.2, by rw [← Subgroup.coe_pow, he'p, Subgroup.coe_one],
    congrArg Subtype.val hek, congrArg Subtype.val hea, fun hmem => hebn ?_⟩
  obtain ⟨-, g, hg, -, hge⟩ := hmem
  have hle : Subgroup.closure ({k, a} : Set Y) ≤
      ((Subgroup.closure ({π k', π a'} : Set (↥K ⧸ Subgroup.center ↥K))).comap π).map K.subtype := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact ⟨k', Subgroup.subset_closure (by simp), rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨a', Subgroup.subset_closure (by simp), rfl⟩
  obtain ⟨g', hg'm, rfl⟩ := hle hg
  have hcen : g'⁻¹ * e' ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : (e' : Y) * w * (e' : Y)⁻¹ = (g' : Y) * w * (g' : Y)⁻¹ := hge w w.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (w : Y) * ((g' : Y)⁻¹ * e') = (g' : Y)⁻¹ * ((g' : Y) * w * (g' : Y)⁻¹) * e' := by group
      _ = (g' : Y)⁻¹ * ((e' : Y) * w * (e' : Y)⁻¹) * e' := by rw [← h1]
      _ = (g' : Y)⁻¹ * e' * w := by group
  have hmk : π e' = π g' := by
    have h2 : π (g'⁻¹ * e') = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hcen
    rw [map_mul, map_inv] at h2
    exact (inv_mul_eq_one.1 h2).symm
  rw [← he', hmk]
  exact hg'm

theorem transfer_comp (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup Y}
    (hcen : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥)
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥K ⧸ Subgroup.center ↥K)) ≤ 2)
    {d : Y} (hdN : d ∈ Subgroup.normalizer (K : Set Y)) (hdp : d ^ p = 1)
    {J : Subgroup Y} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set Y)) J) :
    ∃ s : ↥K ⧸ Subgroup.center ↥K, s ^ p = 1 ∧
      (∀ (k : Y) (hk : k ∈ K), (∀ x ∈ K, d * x * d⁻¹ = k * x * k⁻¹) →
        QuotientGroup.mk' (Subgroup.center ↥K) ⟨k, hk⟩ = s) ∧
      ∃ I : Subgroup (↥K ⧸ Subgroup.center ↥K),
        GLAPComponent p (Subgroup.centralizer ({s} : Set (↥K ⧸ Subgroup.center ↥K))) I ∧
        Nonempty (PSimple p J ≃* PSimple p I) := by
  set β : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨d, hdN⟩ with hβ
  have hβapp : ∀ k : ↥K, ((β k : ↥K) : Y) = d * k * d⁻¹ := fun k => rfl
  have hβp : β ^ p = 1 := by
    rw [hβ, ← map_pow]
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (K : Set Y)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hdp)
    rw [h1, map_one]
  have hfix : fixSubgroup β = (K ⊓ Subgroup.centralizer ({d} : Set Y)).subgroupOf K := by
    ext k
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      have h1 : ((β k : ↥K) : Y) = (k : Y) := congrArg Subtype.val hk
      rw [hβapp] at h1
      exact ⟨k.2, (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
    · rintro ⟨-, hk⟩
      apply Subtype.ext
      rw [hβapp]
      exact mul_inv_eq_iff_eq_mul.2 hk.symm
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hJ' : GLAPComponent p (fixSubgroup β) (J.subgroupOf K) := by
    rw [hfix]
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp inf_le_left hJ
  obtain ⟨hJ'', ⟨eJ⟩⟩ := Inputs1415.center_transfer hp β hJ'
  obtain ⟨s, hs, hsp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen
    hout (centerQuotientHom ↥K β) (by rw [← map_pow, hβp, map_one])
  refine ⟨s, hsp, fun k hk hkd => ?_, (J.subgroupOf K).map (QuotientGroup.mk' _), ?_, ?_⟩
  · have hconj : MulAut.conj (⟨k, hk⟩ : ↥K) = β := by
      ext x
      rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hβapp]
      exact (hkd x x.2).symm
    apply conj_injective_of_center hcen
    rw [← CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj, hconj, hs]
  · rw [← hs, Inputs1415.fixSubgroup_conj] at hJ''
    exact hJ''
  · obtain ⟨e0⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pQuot_equiv_subgroupOf p hJK
    let e1 : PSimple p (J.subgroupOf K) ≃* PSimple p J :=
      QuotientGroup.congr _ _ e0 (Subgroup.map_center_eq e0)
    exact ⟨e1.symm.trans eJ⟩

end Lift

section A5A5

open CFSG.HardMathSupport.Dickson.I271.TabCo1 (isPerfect_closure_pair exists_noncomm_of_perfect)

variable {G : Type} [Group G]

theorem closure_comm {S T : Set G} (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer T := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    exact (h s hs t ht).symm
  intro x hx y hy
  have hxT : ∀ t ∈ T, x * t = t * x := fun t ht =>
    (Subgroup.mem_centralizer_iff.1 (h1 hx) t ht).symm
  have h3 : Subgroup.closure T ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.closure_le]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.2 (hxT t ht).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (h3 hy)).symm

theorem eq_one_of_comm_of_center {L : Subgroup G} (hZ : Subgroup.center ↥L = ⊥) {g : G}
    (hg : g ∈ L) (hc : ∀ l ∈ L, g * l = l * g) : g = 1 := by
  have h1 : (⟨g, hg⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hc l l.2).symm
  rw [hZ, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

variable [Finite G]

theorem planeOK_of_A5A5 (P : Subgroup G) (k x₁ y₁ τ : G) (hkP : k ∈ P)
    (hk5 : k ^ 5 = 1) (hk1 : k ≠ 1) (hx₁ : x₁ ∈ P) (hy₁ : y₁ ∈ P) (hτ : τ ∈ P)
    (hkx₁ : k * x₁ = x₁ * k) (hky₁ : k * y₁ = y₁ * k) (hkτ : k * τ = τ * k) (hτ2 : τ * τ = 1)
    (hc₁ : x₁ * (τ * x₁ * τ⁻¹) = (τ * x₁ * τ⁻¹) * x₁)
    (hc₂ : x₁ * (τ * y₁ * τ⁻¹) = (τ * y₁ * τ⁻¹) * x₁)
    (hc₃ : y₁ * (τ * x₁ * τ⁻¹) = (τ * x₁ * τ⁻¹) * y₁)
    (hc₄ : y₁ * (τ * y₁ * τ⁻¹) = (τ * y₁ * τ⁻¹) * y₁)
    (hL : Nat.card ↥(Subgroup.closure ({x₁, y₁} : Set G)) = 60)
    (hX : ∃ u ∈ Subgroup.closure ({x₁, y₁} : Set G), ∃ v ∈ Subgroup.closure ({x₁, y₁} : Set G),
      x₁ = u * v * u⁻¹ * v⁻¹)
    (hY : ∃ u ∈ Subgroup.closure ({x₁, y₁} : Set G), ∃ v ∈ Subgroup.closure ({x₁, y₁} : Set G),
      y₁ = u * v * u⁻¹ * v⁻¹)
    (hEcard : Nat.card ↥(Subgroup.closure ({k, x₁, y₁, τ} : Set G)) = 36000)
    (hCbd : Nat.card ↥(Subgroup.centralizer ({k} : Set G) ⊓ P) ≤ 36000)
    {a : G} (haP : a ∈ P) (hak : a * k = k * a) (ha5 : a ^ 5 = 1) :
    ∃ e ∈ P, e ^ 5 = 1 ∧ e * k = k * e ∧ e * a = a * e ∧
      e ∉ Subgroup.closure ({k, a} : Set G) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set x₂ := τ * x₁ * τ⁻¹ with hx₂
  set y₂ := τ * y₁ * τ⁻¹ with hy₂
  set L₁ := Subgroup.closure ({x₁, y₁} : Set G) with hL₁
  set L₂ := Subgroup.closure ({x₂, y₂} : Set G) with hL₂
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have h12 : ∀ u ∈ L₁, ∀ v ∈ L₂, u * v = v * u := by
    refine closure_comm ?_
    intro s hs t ht
    rcases hs with rfl | hs <;> rcases ht with rfl | ht
    · exact hc₁
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hc₂
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hc₃
    · rw [Set.mem_singleton_iff] at hs ht
      rw [hs, ht]
      exact hc₄
  have cτk : Commute k τ := hkτ
  have hkx₂ : k * x₂ = x₂ * k :=
    ((cτk.mul_right (show Commute k x₁ from hkx₁)).mul_right cτk.inv_right).eq
  have hky₂ : k * y₂ = y₂ * k :=
    ((cτk.mul_right (show Commute k y₁ from hky₁)).mul_right cτk.inv_right).eq
  have hk1L : ∀ u ∈ L₁, k * u = u * k := by
    have := closure_comm (S := ({k} : Set G)) (T := ({x₁, y₁} : Set G)) ?_
    · intro u hu
      exact this k (Subgroup.subset_closure rfl) u hu
    · intro s hs t ht
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rcases ht with rfl | ht
      · exact hkx₁
      · rw [Set.mem_singleton_iff] at ht
        rw [ht]
        exact hky₁
  have hk2L : ∀ u ∈ L₂, k * u = u * k := by
    have := closure_comm (S := ({k} : Set G)) (T := ({x₂, y₂} : Set G)) ?_
    · intro u hu
      exact this k (Subgroup.subset_closure rfl) u hu
    · intro s hs t ht
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rcases ht with rfl | ht
      · exact hkx₂
      · rw [Set.mem_singleton_iff] at ht
        rw [ht]
        exact hky₂
  have hperf : Group.IsPerfect ↥L₁ := isPerfect_closure_pair x₁ y₁ hX hY
  have hs₁ : IsSimpleGroup ↥L₁ :=
    CFSG.Quasithin.A312J2.isSimpleGroup_of_perfect_card_sixty hperf hL
  have hZ₁ : Subgroup.center ↥L₁ = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup
      (exists_noncomm_of_perfect hperf (by rw [hL]; norm_num))
  have hL₂map : ∀ v ∈ L₂, ∃ u ∈ L₁, v = τ * u * τ⁻¹ := by
    intro v hv
    have hmap : L₂ = L₁.map (MulAut.conj τ).toMonoidHom :=
      CFSG.HardMathSupport.Dickson.I271.TabCo1.closure_pair_conj τ x₁ y₁
    rw [hmap] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨u, hu, rfl⟩
  have hL₁conj : ∀ u ∈ L₁, τ * u * τ⁻¹ ∈ L₂ := by
    intro u hu
    have hmap : L₂ = L₁.map (MulAut.conj τ).toMonoidHom :=
      CFSG.HardMathSupport.Dickson.I271.TabCo1.closure_pair_conj τ x₁ y₁
    rw [hmap]
    exact ⟨u, hu, rfl⟩
  have hcen₂ : ∀ g ∈ L₂, (∀ l ∈ L₂, g * l = l * g) → g = 1 := by
    intro g hg hc
    obtain ⟨u, hu, rfl⟩ := hL₂map g hg
    have hu1 : u = 1 := by
      refine eq_one_of_comm_of_center hZ₁ hu fun l hl => ?_
      have h1 := hc _ (hL₁conj l hl)
      have h2 : τ * (u * l) * τ⁻¹ = τ * (l * u) * τ⁻¹ := by
        calc τ * (u * l) * τ⁻¹ = (τ * u * τ⁻¹) * (τ * l * τ⁻¹) := by group
          _ = (τ * l * τ⁻¹) * (τ * u * τ⁻¹) := h1
          _ = τ * (l * u) * τ⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
    rw [hu1]
    group
  obtain ⟨u₁, hu₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥L₁) 5 (by rw [hL]; norm_num)
  have hu₁5 : (u₁ : G) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← hu₁, pow_orderOf_eq_one, Subgroup.coe_one]
  have hu₁1 : (u₁ : G) ≠ 1 := by
    intro h
    have h1 : u₁ = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hu₁
    norm_num at hu₁
  have hu₂mem : τ * u₁ * τ⁻¹ ∈ L₂ := hL₁conj u₁ u₁.2
  have hu₂5 : (τ * u₁ * τ⁻¹) ^ 5 = 1 := by rw [conj_pow, hu₁5, mul_one, mul_inv_cancel]
  have hu₂1 : τ * u₁ * τ⁻¹ ≠ 1 := by
    intro h
    apply hu₁1
    calc (u₁ : G) = τ⁻¹ * (τ * u₁ * τ⁻¹) * τ := by group
      _ = 1 := by rw [h]; group
  set C := Subgroup.closure ({k, x₁, y₁, τ} : Set G) with hC
  have hCle : C ≤ Subgroup.centralizer ({k} : Set G) ⊓ P := by
    rw [hC, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | hg)
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hkP⟩
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hkx₁.symm, hx₁⟩
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hky₁.symm, hy₁⟩
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hkτ.symm, hτ⟩
  have hCeq : C = Subgroup.centralizer ({k} : Set G) ⊓ P :=
    Subgroup.eq_of_le_of_card_ge hCle (by rw [hEcard]; exact hCbd)
  have haC : a ∈ C := by
    rw [hCeq]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hak, haP⟩
  set E : Subgroup G := Subgroup.zpowers k ⊔ L₁ ⊔ L₂ with hE
  have hkL₂c : Subgroup.zpowers k ⊔ L₁ ≤ Subgroup.centralizer (L₂ : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hk2L v hv).symm
    · intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (h12 u hu v hv).symm
  have hkL₁c : ∀ c ∈ Subgroup.zpowers k, ∀ u ∈ L₁, c * u = u * c := by
    intro c hc u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact (Commute.zpow_left (show Commute k u from hk1L u hu) i).eq
  have hdec : ∀ g ∈ E, ∃ c ∈ Subgroup.zpowers k, ∃ u ∈ L₁, ∃ v ∈ L₂, g = c * u * v := by
    intro g hg
    obtain ⟨h, hh, v, hv, rfl⟩ := (mem_sup_of_commute (fun h hh v hv =>
      (Subgroup.mem_centralizer_iff.1 (hkL₂c hh) v hv).symm)).1 hg
    obtain ⟨c, hc, u, hu, rfl⟩ := (mem_sup_of_commute hkL₁c).1 hh
    exact ⟨c, hc, u, hu, v, hv, rfl⟩
  have hmemE : ∀ c ∈ Subgroup.zpowers k, ∀ u ∈ L₁, ∀ v ∈ L₂, c * u * v ∈ E := fun c hc u hu v hv =>
    E.mul_mem (E.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hc))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hu))) (Subgroup.mem_sup_right hv)
  have hτE : ∀ g ∈ E, τ * g * τ⁻¹ ∈ E := by
    intro g hg
    obtain ⟨c, hc, u, hu, v, hv, rfl⟩ := hdec g hg
    obtain ⟨w, hw, rfl⟩ := hL₂map v hv
    have hτc : τ * c * τ⁻¹ = c := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      rw [← (Commute.zpow_left cτk i).eq, mul_inv_cancel_right]
    have hcomm := h12 w hw _ (hL₁conj u hu)
    have e1 : τ * (c * u * (τ * w * τ⁻¹)) * τ⁻¹ = c * w * (τ * u * τ⁻¹) := by
      calc τ * (c * u * (τ * w * τ⁻¹)) * τ⁻¹
          = (τ * c * τ⁻¹) * (τ * u * τ⁻¹) * ((τ * τ) * w * (τ * τ)⁻¹) := by group
        _ = c * (τ * u * τ⁻¹) * w := by rw [hτc, hτ2]; group
        _ = c * ((τ * u * τ⁻¹) * w) := by group
        _ = c * (w * (τ * u * τ⁻¹)) := by rw [← hcomm]
        _ = c * w * (τ * u * τ⁻¹) := by group
    rw [e1]
    exact hmemE c hc w hw _ (hL₁conj u hu)
  have hCE : ∀ g ∈ C, g ∈ E ∨ τ * g ∈ E := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl | rfl | hg
      · exact Or.inl (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
      · exact Or.inl (Subgroup.mem_sup_left (Subgroup.mem_sup_right
          (Subgroup.subset_closure (by simp))))
      · exact Or.inl (Subgroup.mem_sup_left (Subgroup.mem_sup_right
          (Subgroup.subset_closure (by simp))))
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact Or.inr (by rw [hτ2]; exact E.one_mem)
    | one => exact Or.inl E.one_mem
    | mul g h _ _ hg hh =>
      rcases hg with hg | hg <;> rcases hh with hh | hh
      · exact Or.inl (E.mul_mem hg hh)
      · right
        have e : τ * (g * h) = (τ * g * τ⁻¹) * (τ * h) := by group
        rw [e]
        exact E.mul_mem (hτE g hg) hh
      · right
        rw [← mul_assoc]
        exact E.mul_mem hg hh
      · left
        have e : g * h = (τ * (τ * g) * τ⁻¹) * (τ * h) := by
          calc g * h = (τ * τ) * g * h := by rw [hτ2, one_mul]
            _ = (τ * (τ * g) * τ⁻¹) * (τ * h) := by group
        rw [e]
        exact E.mul_mem (hτE _ hg) hh
    | inv g _ hg =>
      rcases hg with hg | hg
      · exact Or.inl (E.inv_mem hg)
      · right
        have e : τ * g⁻¹ = τ * (τ * g)⁻¹ * τ⁻¹ := by
          calc τ * g⁻¹ = τ * g⁻¹ * (τ * τ)⁻¹ := by rw [hτ2, inv_one, mul_one]
            _ = τ * (τ * g)⁻¹ * τ⁻¹ := by group
        rw [e]
        exact hτE _ (E.inv_mem hg)
  have haE : a ∈ E := by
    rcases hCE a haC with h | h
    · exact h
    · have ha2 : a * a ∈ E := by
        have e : a * a = (τ * (τ * a) * τ⁻¹) * (τ * a) := by
          calc a * a = (τ * τ) * a * a := by rw [hτ2, one_mul]
            _ = (τ * (τ * a) * τ⁻¹) * (τ * a) := by group
        rw [e]
        exact E.mul_mem (hτE _ h) h
      have e : a = (a * a) ^ 3 := by
        calc a = a * a ^ 5 := by rw [ha5, mul_one]
          _ = a ^ 6 := (pow_succ' a 5).symm
          _ = (a * a) ^ 3 := by rw [← sq, ← pow_mul]
      rw [e]
      exact E.pow_mem ha2 3
  have hL₁P : L₁ ≤ P := by
    rw [hL₁, Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact hx₁
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hy₁
  have hL₂P : L₂ ≤ P := by
    rw [hL₂, Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact P.mul_mem (P.mul_mem hτ hx₁) (P.inv_mem hτ)
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact P.mul_mem (P.mul_mem hτ hy₁) (P.inv_mem hτ)
  obtain ⟨c, hc, l₁, hl₁, l₂, hl₂, rfl⟩ := hdec a haE
  have hc5 : c ^ 5 = 1 := pow_eq_one_of_mem_zpowers hk5 hc
  have hcl₁ : Commute c l₁ := hkL₁c c hc l₁ hl₁
  have hcl₂ : Commute c l₂ := (Subgroup.mem_centralizer_iff.1
    (hkL₂c (Subgroup.mem_sup_left hc)) l₂ hl₂).symm
  have hl₁l₂ : Commute l₁ l₂ := h12 l₁ hl₁ l₂ hl₂
  have hpow : (c * l₁ * l₂) ^ 5 = c ^ 5 * l₁ ^ 5 * l₂ ^ 5 := by
    rw [Commute.mul_pow (hcl₂.mul_left hl₁l₂), Commute.mul_pow hcl₁]
  have h15 : l₁ ^ 5 * l₂ ^ 5 = 1 := by
    have h1 := hpow
    rw [ha5, hc5, one_mul] at h1
    exact h1.symm
  have hl15 : l₁ ^ 5 = 1 := by
    have h2 : l₁ ^ 5 = (l₂ ^ 5)⁻¹ := eq_inv_of_mul_eq_one_left h15
    refine eq_one_of_comm_of_center hZ₁ (L₁.pow_mem hl₁ 5) fun l hl => ?_
    rw [h2]
    exact (h12 l hl _ (L₂.inv_mem (L₂.pow_mem hl₂ 5))).symm
  have hl25 : l₂ ^ 5 = 1 := by
    rw [hl15, one_mul] at h15
    exact h15
  obtain ⟨e₁, he₁L, he₁5, he₁1, he₁a⟩ : ∃ e₁ ∈ L₁, e₁ ^ 5 = 1 ∧ e₁ ≠ 1 ∧
      e₁ * (c * l₁ * l₂) = (c * l₁ * l₂) * e₁ := by
    by_cases h : l₁ = 1
    · subst h
      refine ⟨u₁, u₁.2, hu₁5, hu₁1, ?_⟩
      have h1 : Commute (u₁ : G) c := (hkL₁c c hc u₁ u₁.2).symm
      have h2 : Commute (u₁ : G) l₂ := h12 u₁ u₁.2 l₂ hl₂
      exact ((h1.mul_right (Commute.one_right (u₁ : G))).mul_right h2).eq
    · exact ⟨l₁, hl₁, hl15, h, ((hcl₁.symm.mul_right (Commute.refl l₁)).mul_right hl₁l₂).eq⟩
  obtain ⟨e₂, he₂L, he₂5, he₂1, he₂a⟩ : ∃ e₂ ∈ L₂, e₂ ^ 5 = 1 ∧ e₂ ≠ 1 ∧
      e₂ * (c * l₁ * l₂) = (c * l₁ * l₂) * e₂ := by
    by_cases h : l₂ = 1
    · subst h
      refine ⟨τ * u₁ * τ⁻¹, hu₂mem, hu₂5, hu₂1, ?_⟩
      have h1 : Commute (τ * u₁ * τ⁻¹) c :=
        Subgroup.mem_centralizer_iff.1 (hkL₂c (Subgroup.mem_sup_left hc)) _ hu₂mem
      have h2 : Commute (τ * u₁ * τ⁻¹) l₁ := (h12 l₁ hl₁ _ hu₂mem).symm
      exact ((h1.mul_right h2).mul_right (Commute.one_right _)).eq
    · exact ⟨l₂, hl₂, hl25, h, ((hcl₂.symm.mul_right hl₁l₂.symm).mul_right (Commute.refl l₂)).eq⟩
  set a' := c * l₁ * l₂ with ha'
  have hQ : Nat.card ↥(Subgroup.closure ({k, a'} : Set G)) ≤ 25 := by
    have hle : Subgroup.closure ({k, a'} : Set G) ≤ Subgroup.zpowers k ⊔ Subgroup.zpowers a' := by
      rw [Subgroup.closure_le]
      rintro g (rfl | hg)
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    refine (Subgroup.card_le_of_le hle).trans ?_
    by_cases hak' : a' ∈ Subgroup.zpowers k
    · rw [sup_eq_left.2 (Subgroup.zpowers_le.2 hak'), Nat.card_zpowers]
      exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hk5)).trans (by norm_num)
    · have hcomm : ∀ h ∈ Subgroup.zpowers k, h * a' = a' * h := fun h hh => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        exact (Commute.zpow_left (show Commute k a' from hak.symm) i).eq
      rw [card_sup_zpowers Nat.prime_five ha5 hak' hcomm, Nat.card_zpowers, orderOf_eq_prime hk5 hk1]
  have he₁k : e₁ ∉ Subgroup.zpowers k := by
    intro h
    apply he₁1
    refine eq_one_of_comm_of_center hZ₁ he₁L fun l hl => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    exact (Commute.zpow_left (show Commute k l from hk1L l hl) i).eq
  have hke₁ : ∀ h ∈ Subgroup.zpowers k, h * e₁ = e₁ * h := fun h hh => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute k e₁ from hk1L e₁ he₁L) i).eq
  have hR2 : Nat.card ↥(Subgroup.zpowers k ⊔ Subgroup.zpowers e₁ : Subgroup G) = 25 := by
    rw [card_sup_zpowers Nat.prime_five he₁5 he₁k hke₁, Nat.card_zpowers, orderOf_eq_prime hk5 hk1]
  have hke₁c : Subgroup.zpowers k ⊔ Subgroup.zpowers e₁ ≤ Subgroup.centralizer (L₂ : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hk2L v hv).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (h12 e₁ he₁L v hv).symm
  have he₂k : e₂ ∉ Subgroup.zpowers k ⊔ Subgroup.zpowers e₁ := by
    intro h
    apply he₂1
    refine hcen₂ e₂ he₂L fun l hl => ?_
    exact (Subgroup.mem_centralizer_iff.1 (hke₁c h) l hl).symm
  have hke₂ : ∀ h ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers e₁, h * e₂ = e₂ * h := fun h hh =>
    (Subgroup.mem_centralizer_iff.1 (hke₁c hh) e₂ he₂L).symm
  have hR : Nat.card ↥(Subgroup.zpowers k ⊔ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ :
      Subgroup G) = 125 := by
    rw [card_sup_zpowers Nat.prime_five he₂5 he₂k hke₂, hR2]
  by_contra hcon
  push Not at hcon
  have he₁Q := hcon e₁ (hL₁P he₁L) he₁5 (hk1L e₁ he₁L).symm he₁a
  have he₂Q := hcon e₂ (hL₂P he₂L) he₂5 (hk2L e₂ he₂L).symm he₂a
  have hRle : Subgroup.zpowers k ⊔ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ ≤
      Subgroup.closure ({k, a'} : Set G) :=
    sup_le (sup_le (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
      (Subgroup.zpowers_le.2 he₁Q)) (Subgroup.zpowers_le.2 he₂Q)
  have h1 := Subgroup.card_le_of_le hRle
  rw [hR] at h1
  omega

end A5A5

section Co1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA
  CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabCo1
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem planeOK_fiveB (x : ↥GA) (hx : MRep repD1 (x : GL24)) : PlaneOK 5 x := by
  haveI : Finite ↥GA := finite_GA
  obtain ⟨k, x₁, y₁, τ, hk, hkGA, hx₁, hy₁, hτ, hk5, hk1, hkx, hky, hkt, htt, hc1, hc2, hc3, hc4,
    hL, hX, hY, hE, hCbd, -⟩ := fiveB_data
  have hxk : (x : GL24) = k := hx.eq hk
  intro a hax ha5
  have hak : (a : GL24) * k = k * a := by
    have h := congrArg Subtype.val hax
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hxk] at h
    exact h
  have ha5' : (a : GL24) ^ 5 = 1 := by rw [← Subgroup.coe_pow, ha5, Subgroup.coe_one]
  obtain ⟨e, heP, he5, hek, hea, hne⟩ := planeOK_of_A5A5 GA k x₁ y₁ τ hkGA hk5 hk1 hx₁ hy₁ hτ hkx hky
    hkt htt hc1 hc2 hc3 hc4 hL hX hY hE hCbd a.2 hak ha5'
  refine ⟨⟨e, heP⟩, Subtype.ext (by rw [Subgroup.coe_pow, he5, Subgroup.coe_one]),
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hxk]; exact hek),
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hea), fun hmem => hne ?_⟩
  have h1 : ((⟨e, heP⟩ : ↥GA) : GL24) ∈
      (Subgroup.closure ({x, a} : Set ↥GA)).map GA.subtype := Subgroup.mem_map_of_mem _ hmem
  rw [MonoidHom.map_closure, Set.image_pair] at h1
  simpa [hxk] using h1

theorem planeOK_Co1 (hbr : SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] (eT : T ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group)
    {s : T} (hs : orderOf s = 5)
    (hJ : ∃ I : Subgroup T, GLAPComponent 5 (Subgroup.centralizer ({s} : Set T)) I ∧
      IsChevSimple 2 (PSimple 5 I)) : PlaneOK 5 s := by
  haveI : Finite ↥GA := finite_GA
  obtain ⟨-, -, -, ⟨b⟩⟩ := co1_model_five hbr
  obtain ⟨σ, -⟩ : ∃ σ : @MulEquiv T ↥GA _ MulOneClass.toMul, True := ⟨eT.trans b.symm, trivial⟩
  have hx : orderOf (σ s) = 5 := by rw [MulEquiv.orderOf_eq, hs]
  obtain ⟨c, hc⟩ := tabCo1_census Certificates.certificate13670 (σ s) hx
  obtain ⟨I, hI, hIc⟩ := hJ
  obtain ⟨hI₁, ⟨eI₁⟩⟩ := Inputs1415.comp_transport Nat.prime_five σ hI
  obtain ⟨hI₂, ⟨eI₂⟩⟩ := Inputs1415.comp_transport Nat.prime_five (MulAut.conj c) hI₁
  have hIc₂ := isChevSimple_of_mulEquiv eI₂ (isChevSimple_of_mulEquiv eI₁ hIc)
  rw [MulAut.conj_apply] at hI₂
  rcases hc with h0 | h1 | h5
  · exfalso
    obtain ⟨hrep, hk5, hk1, hku, hkv, hu1, hw1, hw2, hw3, hbound⟩ := fiveA_data
    obtain ⟨h1', h2', h3'⟩ := relators_of_wordG hw1 hw2 hw3
    have hsh := shapeRkAt_J2_of_data_good (Good := fun T _ => ¬ IsChevSimple 2 T)
      (fun _ _ _ _ e h hc => h (isChevSimple_of_mulEquiv e.symm hc))
      (fun _ _ e => not_isChevSimple_J2 hb e 2) GA (c * σ s * c⁻¹) _ _ _ (h0.eq hrep)
      (kG_mem ext 89) (kG_mem ext 90) hk5 hk1 hku hkv hu1 h1' h2' h3' hbound
    rcases hsh with hcon | ⟨J, -, huniq, hgood, -⟩
    · exact no_glaPComponent_of_pConstrainedShape Nat.prime_five hcon hI₂
    · rw [huniq _ hI₂] at hIc₂
      exact hgood hIc₂
  · have hP := ((planeOK_fiveB _ h1).of_mulEquiv (MulAut.conj c).symm).of_mulEquiv σ.symm
    have h2 : σ.symm ((MulAut.conj c).symm (c * σ s * c⁻¹)) = s := by
      rw [MulAut.conj_symm_apply, show c⁻¹ * (c * σ s * c⁻¹) * c = σ s by group,
        MulEquiv.symm_apply_apply]
    rwa [h2] at hP
  · exact (no_glaPComponent_of_pConstrainedShape Nat.prime_five (tabCo1_fiveC _ h5) hI₂).elim

end Co1

@[expose] def SporNoChevTwoDown (p : ℕ) (name : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
    ∀ s : S, orderOf s = p → ∀ I : Subgroup S,
      GLAPComponent p (Subgroup.centralizer ({s} : Set S)) I → ¬ IsChevSimple 2 (PSimple p I)

section HN

open CFSG.HardMathSupport.Dickson.I271
open CFSG.Open CFSG.Blueprint CFSG.Sporadic.HNSchreier
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows
open scoped commutatorElement

theorem hn_noChev2_f (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) (I : Subgroup ↥JH)
    (hI : GLAPComponent 5 (Subgroup.centralizer ({fJ} : Set ↥JH)) I) : ¬ IsChevSimple 2 (PSimple 5 I) := by
  obtain ⟨hcomm, -, -, -, hC, hcardI, -, hder, -⟩ :=
    CFSG.Sporadic.HNOddCore.ctuc_hn_five_centralizer_perfect_factor
  haveI hsimple : IsSimpleGroup ↥IJ :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity IJ 3 5 1 CFSG.RankThree.PartOne.HNB.model_IJ).2
  haveI : Finite ↥IJ := Nat.finite_of_card_ne_zero (by rw [hcardI]; norm_num)
  have hLC : IJ ≤ Subgroup.centralizer ({fJ} : Set ↥JH) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm fJ (Subgroup.mem_zpowers _) x hx).symm
  have hnp : ¬ (Nat.card ↥IJ).Prime := by
    rw [hcardI]
    norm_num
  have hnab : ∃ a b : ↥IJ, a * b ≠ b * a := exists_noncomm_of_simple_card (G := ↥IJ) hnp
  have h5 : 5 ∣ Nat.card ↥IJ := by
    rw [hcardI]
    norm_num
  have hk : Nat.card ↥(Subgroup.centralizer ({fJ} : Set ↥JH)) = Nat.card ↥IJ * 5 ^ 1 := by
    rw [hC, hcardI]
    norm_num
  have hT : ¬ IsChevSimple 2 ↥IJ := not_isChevSimple_two_of_card hb (a := 4) (m := 7875)
    (by rw [hcardI]; norm_num) (by decide) (by norm_num) (by norm_num)
  haveI : Finite ↥JH := by
    have : Nat.card ↥JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  have hLn : ∀ g ∈ Subgroup.centralizer ({fJ} : Set ↥JH), ∀ l ∈ IJ, g * l * g⁻¹ ∈ IJ := by
    intro g hg l hl
    have h1 : ⁅g, l⁆ ∈
        ⁅Subgroup.centralizer ({fJ} : Set ↥JH), Subgroup.centralizer ({fJ} : Set ↥JH)⁆ :=
      Subgroup.commutator_mem_commutator hg (hLC hl)
    rw [hder] at h1
    have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
      rw [commutatorElement_def]; group
    rw [h3]
    exact IJ.mul_mem h1 hl
  have hsh := shapeRkAt_of_data (Good := fun T _ => ¬ IsChevSimple 2 T) (Rk := fun _ _ => True)
    Nat.prime_five (fun _ _ _ _ e h hc => h (isChevSimple_of_mulEquiv e.symm hc))
    (fun _ _ _ _ _ h => h) fJ IJ hLC hLn hsimple hnab h5 hk hT trivial
  rcases hsh with hc | ⟨J, -, huniq, hgood, -⟩
  · exact (no_glaPComponent_of_pConstrainedShape Nat.prime_five hc hI).elim
  · rw [huniq I hI]
    exact hgood

theorem hn_noChev2 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) (k : ↥JH)
    (hk5 : orderOf k = 5) (I : Subgroup ↥JH)
    (hI : GLAPComponent 5 (Subgroup.centralizer ({k} : Set ↥JH)) I) : ¬ IsChevSimple 2 (PSimple 5 I) := by
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  by_cases h5A : ∃ e : ℕ, IsConj k (fJ ^ e)
  · obtain ⟨e, he⟩ := h5A
    obtain ⟨c, hc⟩ := isConj_iff.1 he
    have hko : orderOf (fJ ^ e) = 5 := by
      rw [← hc]
      exact (orderOf_conj_eq c k).trans hk5
    have hcent : Subgroup.centralizer ({fJ ^ e} : Set JH) = Subgroup.centralizer ({fJ} : Set JH) :=
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq (by rw [hko, orderOf_fJ])
        (by rw [orderOf_fJ]; norm_num)
    obtain ⟨hI', ⟨eI⟩⟩ := Inputs1415.comp_transport Nat.prime_five (MulAut.conj c) hI
    rw [MulAut.conj_apply, hc, hcent] at hI'
    intro hch
    exact hn_noChev2_f hb _ hI' (isChevSimple_of_mulEquiv eI hch)
  · push Not at h5A
    have hord : Nat.card ↥(Subgroup.centralizer ({k} : Set JH)) ∣ 2 ^ 14 * 3 * 5 ^ 6 :=
      hnFiveOrders_holds k hk5 h5A
    have hO := hnFiveRest_of_orders hnFiveOrders_holds k hk5 h5A
    by_cases h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({k} : Set JH))
    · have h9 : ¬ 3 ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({k} : Set JH)) := fun h => by
        have := h.trans hord
        norm_num at this
      obtain ⟨Q, hQC, hQn, hQs, s, hsC, hso, hq⟩ := hnFiveMoved_holds k hk5 h5A h3
      exact (hnNoComp_of_normal_solvable hQC hQn hQs hO hord
        (hnMoved_of_sylow hQC hQn h9 hsC hso hq) I hI).elim
    · have hcop : Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({k} : Set JH))) 3 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3 |>.symm
      have hd : Nat.card ↥(Subgroup.centralizer ({k} : Set JH)) ∣ 2 ^ 14 * 5 ^ 6 := by
        have e : 2 ^ 14 * 3 * 5 ^ 6 = 3 * (2 ^ 14 * 5 ^ 6) := by ring
        rw [e] at hord
        exact Nat.Coprime.dvd_of_dvd_mul_left hcop hord
      exact (no_glaPComponent_of_pConstrainedShape Nat.prime_five
        (pConstrainedShape_of_solvable Nat.prime_five (isSolvable_of_card_dvd_two_five hd) hO) hI).elim

theorem sporNoChevTwoDown_HN (hbr : SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : SporNoChevTwoDown 5 .HN := by
  intro S _ _ ⟨eS⟩ s hs I hI
  have e : CFSG.Blueprint.NativeSporadic.HN ≃* ↥JH := CFSG.Sporadic.HNSchreier.hnEquivJ
  have b : ↥JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group := e.symm.trans (hbr .HN).some
  obtain ⟨σ, -⟩ : ∃ σ : @MulEquiv S ↥JH _ MulOneClass.toMul, True := ⟨eS.trans b.symm, trivial⟩
  obtain ⟨hI', ⟨eI⟩⟩ := Inputs1415.comp_transport Nat.prime_five σ hI
  intro hch
  exact hn_noChev2 hb (σ s) (by rw [MulEquiv.orderOf_eq, hs]) _ hI'
    (isChevSimple_of_mulEquiv eI hch)

end HN

section Ly

open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem sporNoChevTwoDown_Ly (hbr : SporadicBridges) : SporNoChevTwoDown 5 .Ly := by
  intro S _ _ ⟨eS⟩ s hs I hI
  exact (no_glaPComponent_of_pConstrainedShape Nat.prime_five
    (pConstrainedShape_Ly_five S ⟨eS.trans (hbr .Ly).some.symm⟩ hs) hI).elim

end Ly

section Rank

open CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Dickson.I271
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom centerQuotientHom_injective)

variable {p : ℕ}

theorem onePair_of_three_le (hp : p.Prime) (hp2 : p ≠ 2)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName, OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) {name : TauCeti.SporadicName}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic name).Group)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut K))) : SporadicOnePair name p := by
  by_contra hnot
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hcen := CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout := hOut _ hq.2 hnab name ⟨e⟩
  have hR := autRankLe2_of_offPair hp hp2 hnot (hOff name) (e.trans (hbr name).some.symm) hcen hout
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
    have h1 := hR (E.map (centerQuotientHom K)) (CFSG.SectionRank.isElemAbelian_map hE _)
    rwa [Subgroup.card_map_of_injective (centerQuotientHom_injective K)] at h1
  omega

theorem exists_sq_of_three_le (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hout : Nat.card (Outer (K ⧸ Subgroup.center K)) ≤ 2)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut K))) :
    ∃ E₀ : Subgroup (K ⧸ Subgroup.center K), IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hcen := CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (MulAut K))
  set F := E.map (centerQuotientHom K) with hF
  have hFel : IsElemAbelian p F := CFSG.SectionRank.isElemAbelian_map hE _
  have hFc : Nat.card F = p ^ CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) := by
    rw [hF, Subgroup.card_map_of_injective (centerQuotientHom_injective K), hEc]
  have hFinn : F ≤ (MulAut.conj : K ⧸ Subgroup.center K →* MulAut (K ⧸ Subgroup.center K)).range := by
    intro f hf
    obtain ⟨s, hs, -⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen hout f (hFel.2 f hf)
    exact ⟨s, hs⟩
  have hinj : Function.Injective
      (MulAut.conj : K ⧸ Subgroup.center K →* MulAut (K ⧸ Subgroup.center K)) :=
    fun _ _ h => conj_injective_of_center hcen h
  set E' := F.comap (MulAut.conj : K ⧸ Subgroup.center K →* MulAut (K ⧸ Subgroup.center K)) with hE'
  have hE'map : E'.map MulAut.conj = F := by
    rw [hE', Subgroup.map_comap_eq, inf_eq_right.2 hFinn]
  have hE'c : Nat.card E' = Nat.card F := by
    rw [← hE'map, Subgroup.card_map_of_injective hinj]
  have hE'el : IsElemAbelian p E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact elem_comm hFel a.2 b.2
    · rw [map_pow, hFel.2 _ hx, map_one]
  have hdvd : p ^ 2 ∣ Nat.card E' := by
    rw [hE'c, hFc]
    exact pow_dvd_pow p (by omega)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine ⟨H.map E'.subtype, CFSG.Open.IsElemAbelian.mono hE'el (Subgroup.map_subtype_le H), ?_⟩
  rw [Subgroup.card_map_of_injective E'.subtype_injective, hH]

end Rank

section Holds

theorem notChev2_of_mem : ∀ name : TauCeti.SporadicName,
    name ∈ ({.Co1, .HN, .Ly, .B, .M} : Finset TauCeti.SporadicName) →
    ∀ (S : Type) [Group S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ¬ IsChevSimple 2 S := by
  intro name hname S _ he
  obtain ⟨e⟩ := he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl
  · exact CFSG.LocalAnalysis.GLTheoremA.No5.co1_not_chev2 e
  all_goals
    exact CFSG.LocalAnalysis.GLTheoremA.List93.notChev2_holds S _
      (Or.inl ⟨_, rfl, 5, by simp [CFSG.Yardstones.Md0ec50421ce4.k2Spor]⟩) ⟨e⟩

end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256

end
