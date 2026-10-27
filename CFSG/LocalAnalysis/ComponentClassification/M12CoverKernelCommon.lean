module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelExternal
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelAction
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStarFourGroup

public section

namespace CFSG.ComponentClassification.M12Cover

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

namespace CyclicKernel

variable {X : Type*} [Group X] [Finite X]

theorem centralizer_eq_sup_closure_of_lift {L H S A : Subgroup X} (hLH : L ≤ H)
    (hHN : H ≤ normalizer (L : Set X)) {t : X} (htL : t ∈ L) (ht : orderOf t = 2)
    (htH : ∀ h ∈ H, h * t = t * h) (hLC : L ⊓ centralizer (L : Set X) = zpowers t)
    (hS : S = H ⊓ centralizer (L : Set X)) (hScyc : IsCyclic S) {p : X} (hpH : p ∈ H)
    (hp : orderOf p = 2) (hpLS : p ∉ L ⊔ S) (hHp : L ⊔ S ⊔ zpowers p = H)
    (hSp : S ⊓ centralizer {p} = zpowers t) (hAL : A ≤ L)
    (hsupA : zpowers t ⊔ A = L ⊓ centralizer {p}) (hinfA : zpowers t ⊓ A = ⊥)
    (hAperf : ⁅A, A⁆ = A) (hAZ : center A = ⊥) {v : X} (hvL : v ∈ L) (hv2 : v ^ 2 = t)
    (hpv : p * v * p⁻¹ = v * t) (hvA : ∀ x ∈ A, v * x = x * v)
    (hlift : ∀ l ∈ L, p * l * p⁻¹ = l * t → v⁻¹ * l ∈ L ⊓ centralizer {p}) {a : X}
    (haS : a ∈ S) (ha2 : a ^ 2 = t) :
    p * a * p⁻¹ = a⁻¹ ∧ orderOf (a * v) = 2 ∧ a * v ∈ L ⊔ S ∧ a * v ∉ L ∧
    closure ({t, p, a * v} : Set X) ⊔ A = H ⊓ centralizer {p} ∧
    closure ({t, p, a * v} : Set X) ⊓ A = ⊥ ∧
    (∀ x ∈ closure ({t, p, a * v} : Set X), ∀ y ∈ A, x * y = y * x) ∧
    Nat.card (closure ({t, p, a * v} : Set X)) = 8 ∧
    CFSG.IsElementaryAbelian 2 (closure ({t, p, a * v} : Set X)) ∧
    (center (H ⊓ centralizer {p} : Subgroup X)).map (H ⊓ centralizer {p}).subtype =
      closure ({t, p, a * v} : Set X) ∧
    ⁅H ⊓ centralizer {p}, H ⊓ centralizer {p}⁆ = A := by
  classical
  subst hS
  set S := H ⊓ centralizer (L : Set X) with hSdef
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hpp : p * p = 1 := by rw [← sq, ← hp, pow_orderOf_eq_one]
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hp1 : p ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hp
    exact absurd hp (by norm_num)
  have htLC : t ∈ L ⊓ centralizer (L : Set X) := by rw [hLC]; exact mem_zpowers t
  have htS : t ∈ S := ⟨hLH htL, htLC.2⟩
  have hpt : p * t = t * p := htH p hpH
  have htp : t * p = p * t := hpt.symm
  have hLsub : L ≤ L ⊔ S := le_sup_left
  have hpL : p ∉ L := fun h => hpLS (hLsub h)
  have haH : a ∈ H := haS.1
  have haC : a ∈ centralizer (L : Set X) := haS.2
  have haL : ∀ l ∈ L, a * l = l * a := fun l hl => (mem_centralizer_iff.mp haC l hl).symm
  have hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy => mul_comm_of_isCyclic hScyc hx hy
  have hLS : ∀ l ∈ L, ∀ s ∈ S, l * s = s * l := fun l hl s hs => mem_centralizer_iff.mp hs.2 l hl
  have hzt : ∀ x ∈ zpowers t, x = 1 ∨ x = t := fun x hx =>
    eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hx
  have hsq1 : ∀ x : X, x = 1 ∨ x = t → x ^ 2 = 1 := by
    rintro x (rfl | rfl)
    · exact one_pow 2
    · rw [sq, htt]
  have hpN : p ∈ normalizer (L : Set X) := hHN hpH
  have hpLc : ∀ l ∈ L, p * l * p⁻¹ ∈ L := fun l hl => (mem_normalizer_iff.mp hpN l).mp hl
  have hpLc' : ∀ l ∈ L, p⁻¹ * l * p ∈ L := fun l hl => by
    have h := hpLc l hl
    rw [hpinv] at h ⊢
    exact h
  have hpS : ∀ s ∈ S, p * s * p⁻¹ ∈ S := by
    intro s hs
    have hsH : s ∈ H := hs.1
    have hsC : s ∈ centralizer (L : Set X) := hs.2
    refine mem_inf.mpr ⟨H.mul_mem (H.mul_mem hpH hsH) (H.inv_mem hpH), ?_⟩
    rw [mem_centralizer_iff]
    intro l hl
    have h1 := mem_centralizer_iff.mp hsC _ (hpLc' l hl)
    calc l * (p * s * p⁻¹) = p * ((p⁻¹ * l * p) * s) * p⁻¹ := by group
      _ = p * (s * (p⁻¹ * l * p)) * p⁻¹ := by rw [h1]
      _ = p * s * p⁻¹ * l := by group
  have hta : t * a = a * t := (htH a haH).symm
  have hata : t * a = a⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    calc a * (t * a) = t * (a * a) := by rw [← mul_assoc, ← hta, mul_assoc]
      _ = 1 := by rw [← sq, ha2, htt]
  have haLf : a ∉ L := by
    intro haL'
    have h : a ∈ L ⊓ centralizer (L : Set X) := ⟨haL', haC⟩
    rw [hLC] at h
    have h2 := hsq1 a (hzt a h)
    rw [ha2] at h2
    exact ht1 h2
  have hpa : p * a * p⁻¹ = a⁻¹ := by
    have hbS : p * a * p⁻¹ ∈ S := hpS a haS
    have hb2 : (p * a * p⁻¹) ^ 2 = t := by rw [conj_pow, ha2, hpt, mul_inv_cancel_right]
    have hab : a⁻¹ * (p * a * p⁻¹) = (p * a * p⁻¹) * a⁻¹ := hSab _ (inv_mem haS) _ hbS
    have hba : (p * a * p⁻¹ * a⁻¹) ^ 2 = 1 := by
      have hb2' : (p * a * p⁻¹) * (p * a * p⁻¹) = t := by rw [← sq, hb2]
      have ha2' : a * a = t := by rw [← sq, ha2]
      calc (p * a * p⁻¹ * a⁻¹) ^ 2 = (p * a * p⁻¹) * (a⁻¹ * (p * a * p⁻¹)) * a⁻¹ := by
            rw [sq]; group
        _ = ((p * a * p⁻¹) * (p * a * p⁻¹)) * (a * a)⁻¹ := by rw [hab]; group
        _ = 1 := by rw [hb2', ha2', mul_inv_cancel]
    rcases eq_one_or_eq_of_sq_eq_one_of_isCyclic hScyc htS ht (mul_mem hbS (inv_mem haS)) hba
      with h | h
    · exfalso
      have hba' : p * a * p⁻¹ = a := mul_inv_eq_one.mp h
      have haP : a ∈ S ⊓ centralizer {p} := by
        refine mem_inf.mpr ⟨haS, ?_⟩
        rw [mem_centralizer_singleton_iff]
        calc a * p = p * a * p⁻¹ * p := by rw [hba']
          _ = p * a := by group
      rw [hSp] at haP
      have h2 := hsq1 a (hzt a haP)
      rw [ha2] at h2
      exact ht1 h2
    · rw [← hata]
      exact mul_inv_eq_iff_eq_mul.mp h
  have hav : a * v = v * a := haL v hvL
  have htv : t * v = v * t := (htH v (hLH hvL)).symm
  have hwL : a * v ∉ L := fun h => haLf (by simpa using L.mul_mem h (L.inv_mem hvL))
  have hw2 : (a * v) ^ 2 = 1 := by
    calc (a * v) ^ 2 = a * (v * a) * v := by rw [sq]; group
      _ = (a * a) * (v * v) := by rw [← hav]; group
      _ = 1 := by rw [← sq a, ← sq v, ha2, hv2, htt]
  have hw1 : a * v ≠ 1 := fun h => hwL (h ▸ L.one_mem)
  have hwo : orderOf (a * v) = 2 := orderOf_eq_prime hw2 hw1
  have hwLS : a * v ∈ L ⊔ S := by
    rw [hav]
    exact mul_mem_sup hvL haS
  have hpw : p * (a * v) * p⁻¹ = a * v := by
    calc p * (a * v) * p⁻¹ = (p * a * p⁻¹) * (p * v * p⁻¹) := by group
      _ = (t * a) * (v * t) := by rw [hpa, hpv, ← hata]
      _ = a * (t * v) * t := by rw [hta]; group
      _ = a * v * (t * t) := by rw [htv]; group
      _ = a * v := by rw [htt, mul_one]
  have hwC : a * v ∈ centralizer {p} := by
    rw [mem_centralizer_singleton_iff]
    calc a * v * p = p * (a * v) * p⁻¹ * p := by rw [hpw]
      _ = p * (a * v) := by group
  have hwH : a * v ∈ H := H.mul_mem haH (hLH hvL)
  set w := a * v with hwdef
  have htw : t * w = w * t := (htH w hwH).symm
  have hpw' : p * w = w * p := (mem_centralizer_singleton_iff.mp hwC).symm
  set V := closure ({t, p} : Set X) with hV
  have htne : t ≠ p := fun h => hpL (h ▸ htL)
  have hVcard : Nat.card V = 4 :=
    StandardRecognition.card_closure_pair_of_involutions htt hpp htp ht1 hp1 htne
  have hVmem : ∀ x, x ∈ V ↔ x = 1 ∨ x = t ∨ x = p ∨ x = t * p := fun x =>
    StandardRecognition.mem_closure_pair_iff htt hpp htp
  have hwV : ∀ x ∈ V, x * w = w * x := by
    intro x hx
    rcases (hVmem x).mp hx with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact htw
    · exact hpw'
    · rw [mul_assoc, hpw', ← mul_assoc, htw, mul_assoc]
  have hVw : ∀ x ∈ V, ∀ y ∈ zpowers w, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (show Commute x w from hwV x hx).zpow_right k
  have hVwinf : V ⊓ zpowers w = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyV, hyw⟩
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hwo hyw with rfl | rfl
    · exact one_mem _
    · exfalso
      rcases (hVmem _).mp hyV with h | h | h | h
      · exact hw1 h
      · exact hwL (h ▸ htL)
      · exact hpLS (h ▸ hwLS)
      · apply hpLS
        have h' : p = t * w := by rw [h, ← mul_assoc, htt, one_mul]
        rw [h']
        exact mul_mem (hLsub htL) hwLS
  have hE : closure ({t, p, w} : Set X) = V ⊔ zpowers w := closure_triple_eq_sup t p w
  have hEcard : Nat.card (closure ({t, p, w} : Set X)) = 8 := by
    rw [hE, card_sup_of_commute hVw hVwinf, hVcard, Nat.card_zpowers, hwo]
  have hEcomm : ∀ x ∈ closure ({t, p, w} : Set X), ∀ y ∈ closure ({t, p, w} : Set X),
      x * y = y * x := by
    have hle : closure ({t, p, w} : Set X) ≤
        centralizer (closure ({t, p, w} : Set X) : Set X) := by
      rw [centralizer_closure, closure_le]
      intro g hg
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro h hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
      rcases hg with hg | hg | hg <;> rcases hh with hh | hh | hh <;> rw [hg, hh]
      all_goals first
        | exact htp
        | exact htp.symm
        | exact htw
        | exact htw.symm
        | exact hpw'
        | exact hpw'.symm
    intro x hx y hy
    exact mem_centralizer_iff.mp (hle hy) x hx
  have hEsq : ∀ x ∈ closure ({t, p, w} : Set X), x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact htt
      · exact hpp
      · rw [← sq]
        exact hw2
    | one => exact mul_one 1
    | mul x y hx hy hx' hy' =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hEcomm y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx', hy', one_mul]
    | inv x hx hx' => rw [← mul_inv_rev, hx', inv_one]
  have hEelem : CFSG.IsElementaryAbelian 2 (closure ({t, p, w} : Set X)) :=
    { is_comm := ⟨fun x y => Subtype.ext (hEcomm x x.2 y y.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa [sq] using hEsq x x.2) }
  have hAp : ∀ y ∈ A, y ∈ L ⊓ centralizer {p} := fun y hy => hsupA ▸ mem_sup_right hy
  have hEA : ∀ x ∈ closure ({t, p, w} : Set X), ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have hyL : y ∈ L := hAL hy
    have hyC : y ∈ centralizer (closure ({t, p, w} : Set X) : Set X) := by
      rw [centralizer_closure, mem_centralizer_iff]
      intro h hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl | rfl
      · exact (mem_centralizer_iff.mp htLC.2 y hyL).symm
      · exact (mem_centralizer_singleton_iff.mp (hAp y hy).2).symm
      · calc a * v * y = a * (y * v) := by rw [mul_assoc, hvA y hy]
          _ = y * (a * v) := by rw [← mul_assoc, haL y hyL, mul_assoc]
    exact mem_centralizer_iff.mp hyC x hx
  have htA : t ∉ A := fun h => ht1 (by
    have h' : t ∈ zpowers t ⊓ A := ⟨mem_zpowers t, h⟩
    rw [hinfA] at h'
    exact h')
  have hEAinf : closure ({t, p, w} : Set X) ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyA⟩
    have hyL : y ∈ L := hAL hyA
    rw [hE] at hyE
    obtain ⟨u, hu, n, hn, rfl⟩ := exists_mul_of_mem_sup_of_commute hVw hyE
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hwo hn with hn1 | hn1
    · rw [hn1, mul_one] at hyL hyA ⊢
      rcases (hVmem u).mp hu with h | h | h | h
      · rw [h]
        exact one_mem _
      · rw [h] at hyA
        exact absurd hyA htA
      · rw [h] at hyL
        exact absurd hyL hpL
      · rw [h] at hyL
        exact absurd (by simpa using L.mul_mem (L.inv_mem htL) hyL) hpL
    · exfalso
      rw [hn1] at hyL
      rcases (hVmem u).mp hu with h | h | h | h <;> rw [h] at hyL
      · rw [one_mul] at hyL
        exact hwL hyL
      · exact hwL (by simpa using L.mul_mem (L.inv_mem htL) hyL)
      · apply hpLS
        have h' : p = p * w * w⁻¹ := by group
        rw [h']
        exact mul_mem (hLsub hyL) (inv_mem hwLS)
      · apply hpLS
        have h' : p = t⁻¹ * (t * p * w) * w⁻¹ := by group
        rw [h']
        exact mul_mem (mul_mem (inv_mem (hLsub htL)) (hLsub hyL)) (inv_mem hwLS)
  have hfwd : ∀ y ∈ L ⊔ S, p * y * p⁻¹ ∈ L ⊔ S := by
    intro y hy
    obtain ⟨l, hl, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_commute hLS hy
    rw [show p * (l * s) * p⁻¹ = (p * l * p⁻¹) * (p * s * p⁻¹) by group]
    exact mul_mem_sup (hpLc l hl) (hpS s hs)
  have hpNLS : p ∈ normalizer ((L ⊔ S : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hfwd y, fun hy => ?_⟩
    have h := hfwd _ hy
    rwa [show p * (p * y * p⁻¹) * p⁻¹ = y by rw [hpinv, ← mul_assoc, ← mul_assoc, hpp, one_mul,
      mul_assoc, hpp, mul_one]] at h
  have hTE : zpowers t ≤ closure ({t, p, w} : Set X) :=
    zpowers_le.mpr (subset_closure (by simp))
  have hCpE : L ⊓ centralizer {p} ≤ closure ({t, p, w} : Set X) ⊔ A := by
    rw [← hsupA]
    exact sup_le_sup_right hTE A
  have hwE : w ∈ closure ({t, p, w} : Set X) := subset_closure (by simp)
  have hclaim : ∀ y ∈ L ⊔ S, y ∈ centralizer {p} → y ∈ closure ({t, p, w} : Set X) ⊔ A := by
    intro y hy hyp
    obtain ⟨l, hl, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_commute hLS hy
    have hyp' : p * (l * s) * p⁻¹ = l * s := by
      rw [mem_centralizer_singleton_iff] at hyp
      rw [← hyp]
      group
    have hprod : (p * l * p⁻¹) * (p * s * p⁻¹) = l * s := by
      rw [← hyp']
      group
    have hδeq : l⁻¹ * (p * l * p⁻¹) = s * (p * s * p⁻¹)⁻¹ := by
      calc l⁻¹ * (p * l * p⁻¹)
          = l⁻¹ * ((p * l * p⁻¹) * (p * s * p⁻¹)) * (p * s * p⁻¹)⁻¹ := by group
        _ = s * (p * s * p⁻¹)⁻¹ := by rw [hprod]; group
    have hδZ : l⁻¹ * (p * l * p⁻¹) ∈ zpowers t := by
      rw [← hLC]
      refine mem_inf.mpr ⟨mul_mem (inv_mem hl) (hpLc l hl), ?_⟩
      rw [hδeq]
      exact (mul_mem hs (inv_mem (hpS s hs))).2
    rcases hzt _ hδZ with hδ | hδ
    ·
      have hlp : p * l * p⁻¹ = l := (inv_mul_eq_one.mp hδ).symm
      have hsp : p * s * p⁻¹ = s := by
        rw [hδeq] at hδ
        exact (mul_inv_eq_one.mp hδ).symm
      have hlC : l ∈ L ⊓ centralizer {p} := by
        refine mem_inf.mpr ⟨hl, ?_⟩
        rw [mem_centralizer_singleton_iff]
        calc l * p = p * l * p⁻¹ * p := by rw [hlp]
          _ = p * l := by group
      have hsC : s ∈ zpowers t := by
        rw [← hSp]
        refine mem_inf.mpr ⟨hs, ?_⟩
        rw [mem_centralizer_singleton_iff]
        calc s * p = p * s * p⁻¹ * p := by rw [hsp]
          _ = p * s := by group
      exact hCpE (mul_mem hlC (hsupA ▸ mem_sup_left hsC))
    ·
      have hlt : p * l * p⁻¹ = l * t := by
        rw [← hδ]
        group
      have hc := hlift l hl hlt
      have hsp : p * s * p⁻¹ = t * s := by
        rw [hδeq] at hδ
        have h1 : p * s * p⁻¹ = t⁻¹ * s := by
          rw [← hδ]
          group
        rw [h1, htinv]
      have hu : s * a⁻¹ ∈ zpowers t := by
        rw [← hSp]
        refine mem_inf.mpr ⟨mul_mem hs (inv_mem haS), ?_⟩
        rw [mem_centralizer_singleton_iff]
        have hpu : p * (s * a⁻¹) * p⁻¹ = s * a⁻¹ := by
          calc p * (s * a⁻¹) * p⁻¹ = (p * s * p⁻¹) * (p * a * p⁻¹)⁻¹ := by group
            _ = t * s * a := by rw [hsp, hpa, inv_inv]
            _ = s * (t * a) := by rw [hSab t htS s hs]; group
            _ = s * a⁻¹ := by rw [hata]
        calc s * a⁻¹ * p = p * (s * a⁻¹) * p⁻¹ * p := by rw [hpu]
          _ = p * (s * a⁻¹) := by group
      have hcu : (v⁻¹ * l) * (s * a⁻¹) ∈ L ⊓ centralizer {p} :=
        mul_mem hc (hsupA ▸ mem_sup_left hu)
      have hal : a * l = l * a := haL l hl
      have has : a * s = s * a := hSab a haS s hs
      have hy : l * s = w * ((v⁻¹ * l) * (s * a⁻¹)) := by
        have h1 : a * (l * s) * a⁻¹ = l * s := by
          rw [← mul_assoc, hal, mul_assoc l a s, has]
          group
        rw [hwdef]
        calc l * s = a * (l * s) * a⁻¹ := h1.symm
          _ = a * v * (v⁻¹ * l * (s * a⁻¹)) := by group
      rw [hy]
      exact mul_mem (mem_sup_left hwE) (hCpE hcu)
  have hCHp : closure ({t, p, w} : Set X) ⊔ A = H ⊓ centralizer {p} := by
    apply le_antisymm
    · apply sup_le
      · rw [closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact mem_inf.mpr ⟨hLH htL, mem_centralizer_singleton_iff.mpr htp⟩
        · exact mem_inf.mpr ⟨hpH, mem_centralizer_singleton_iff.mpr rfl⟩
        · exact mem_inf.mpr ⟨hwH, hwC⟩
      · intro x hx
        obtain ⟨hxL, hxp⟩ := mem_inf.mp (hAp x hx)
        exact mem_inf.mpr ⟨hLH hxL, hxp⟩
    · rintro y ⟨hyH, hyp⟩
      rw [← hHp] at hyH
      rcases mem_or_mul_mem_of_mem_sup_zpowers hpNLS hpp hyH with h | h
      · exact hclaim y h hyp
      · have hyp' : y * p ∈ centralizer {p} :=
          mul_mem hyp (mem_centralizer_singleton_iff.mpr rfl)
        have h' := hclaim _ h hyp'
        have hpE : p ∈ closure ({t, p, w} : Set X) ⊔ A := mem_sup_left (subset_closure (by simp))
        have hy' : y = y * p * p := by rw [mul_assoc, hpp, mul_one]
        rw [hy']
        exact mul_mem h' hpE
  have hcenter : (center (H ⊓ centralizer {p} : Subgroup X)).map (H ⊓ centralizer {p}).subtype =
      closure ({t, p, w} : Set X) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxE : (x : X) ∈ closure ({t, p, w} : Set X) ⊔ A := by rw [hCHp]; exact x.2
      obtain ⟨e, he, a', ha', hxea⟩ := exists_mul_of_mem_sup_of_commute hEA hxE
      have ha'Z : (⟨a', ha'⟩ : A) ∈ center A := by
        rw [mem_center_iff]
        intro b
        apply Subtype.ext
        have hbC : (b : X) ∈ H ⊓ centralizer {p} := by rw [← hCHp]; exact mem_sup_right b.2
        have hxb := congrArg Subtype.val (mem_center_iff.mp hx ⟨b, hbC⟩)
        simp only [Subgroup.coe_mul] at hxb ⊢
        rw [hxea] at hxb
        have heb := hEA e he b b.2
        calc (b : X) * a' = e⁻¹ * (b * (e * a')) := by rw [← mul_assoc (b : X) e a', ← heb]; group
          _ = e⁻¹ * (e * a' * b) := by rw [hxb]
          _ = a' * b := by group
      rw [hAZ, mem_bot] at ha'Z
      have ha'1 : a' = 1 := congrArg Subtype.val ha'Z
      show (x : X) ∈ _
      rw [hxea, ha'1, mul_one]
      exact he
    · intro x hx
      have hxC : x ∈ H ⊓ centralizer {p} := by rw [← hCHp]; exact mem_sup_left hx
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro g
      apply Subtype.ext
      have hg : (g : X) ∈ closure ({t, p, w} : Set X) ⊔ A := by rw [hCHp]; exact g.2
      exact (commute_of_mem_sup_of_commute hEcomm hEA hx hg).symm
  have hder : ⁅H ⊓ centralizer {p}, H ⊓ centralizer {p}⁆ = A := by
    rw [← hCHp, commutator_sup_eq_of_commute hEcomm hEA, hAperf]
  exact ⟨hpa, hwo, hwLS, hwL, hCHp, hEAinf, hEA, hEcard, hEelem, hcenter, hder⟩

theorem outer_involution_fixed_factor {L : Subgroup X} (hLq : CFSG.Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {p : X}
    (hpN : p ∈ normalizer (L : Set X)) (hp : orderOf p = 2)
    (hpC : ∀ l ∈ L, l * p ∉ centralizer (L : Set X)) (α : MulAut NativeSporadic.M12)
    (hα : ∀ l l' : L, (l' : X) = p * l * p⁻¹ → α (π l) = π l')
    {D : Subgroup NativeSporadic.M12} (hD : D = ⁅fixSub α, fixSub α⁆)
    {A : Subgroup X} (hA : A = ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆) :
    orderOf α = 2 ∧ α ∉ inner NativeSporadic.M12 ∧ A ≤ L ∧
    zpowers (t : X) ⊔ A = L ⊓ centralizer {p} ∧ zpowers (t : X) ⊓ A = ⊥ ∧
    (∃ e : A.subgroupOf L ≃* D, ∀ a, (e a : NativeSporadic.M12) = π a) ∧
    ⁅A, A⁆ = A ∧ Nat.card A = 60 ∧ center A = ⊥ ∧ Nat.card (Outer A) ∣ 2 ∧
    D.comap π = (centralizer {p}).subgroupOf L ∧
    (∀ q : X, q * p ∈ L → orderOf q = 2 → ∃ l : L, (l : X) * p * (l : X)⁻¹ = q) ∧
    ∃ z : NativeSporadic.M12, z ∈ fixSub α ∧ (∀ c ∈ fixSub α, c * z = z * c) ∧ z ∉ D ∧
      orderOf z = 2 ∧ fixedCount z = 0 ∧ zpowers z ⊔ D = fixSub α ∧ zpowers z ⊓ D = ⊥ ∧
      ∀ v : L, π v = z → (v : X) ^ 2 = t ∧ p * v * p⁻¹ = v * t ∧
        (∀ x ∈ A, (v : X) * x = x * v) ∧
        ∀ l : L, p * l * p⁻¹ = l * t → (v : X)⁻¹ * l ∈ L ⊓ centralizer {p} := by
  classical
  subst hD hA
  obtain ⟨hα2, hαo, -, hfus, ⟨g, hg⟩, hmap, hsup, hinf, eC, heC⟩ :=
    external_data_of_mem_normalizer hLq ht hZ π hπ hker hpN hp hpC α hα
  have htpc : (t : X) * p = p * t := by
    calc (t : X) * p = p * t * p⁻¹ * p := by
          rw [conj_eq_of_mem_normalizer_of_center_eq_zpowers hZ ht hpN]
      _ = p * t := by group
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have htZ : t ∈ center L := hZ ▸ mem_zpowers t
  have hD : ⁅fixSub α, fixSub α⁆ = fixedD.map (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact commutator_fixSub_conj_beta g
  have hfix : fixSub α = (fixSub beta).map (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact fixSub_conj_beta g
  have hAeq : ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ =
      ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆.map L.subtype := by
    rw [map_commutator, subgroupOf_map_subtype, inf_comm]
  have hAL : ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ ≤ L := by
    rw [hAeq]
    exact map_subtype_le _
  have hAsub : (⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆).subgroupOf L =
      ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ := by
    rw [hAeq]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hTX : zpowers (t : X) = (zpowers t).map L.subtype := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hsupX : zpowers (t : X) ⊔ ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ =
      L ⊓ centralizer {p} := by
    rw [hTX, hAeq, ← Subgroup.map_sup, hsup, subgroupOf_map_subtype, inf_comm]
  have hinfX : zpowers (t : X) ⊓ ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ = ⊥ := by
    rw [hTX, hAeq, ← map_inf_eq _ _ _ L.subtype_injective, hinf, Subgroup.map_bot]
  let eA : (⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆.subgroupOf L : Subgroup L) ≃*
      (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12) :=
    (MulEquiv.subgroupCongr hAsub).trans eC
  have heA : ∀ a, (eA a : NativeSporadic.M12) = π a := fun a => heC _
  let eAX : (⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ : Subgroup X) ≃*
      (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12) :=
    (subgroupOfEquivOfLe hAL).symm.trans eA
  have hAcard : Nat.card (⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ : Subgroup X) = 60 := by
    rw [Nat.card_congr eAX.toEquiv, hD, card_fixedD_map_conj]
  have hAperf : ⁅⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆,
      ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆⁆ = ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ := by
    have : Group.IsPerfect (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12) :=
      Subgroup.isPerfect_iff.2 (by rw [hD]; exact fixedD_map_conj_perfect g)
    exact Subgroup.isPerfect_iff.1
      (Group.IsPerfect.ofSurjective (f := eAX.symm.toMonoidHom) eAX.symm.surjective)
  have hAZ : center (⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ : Subgroup X) = ⊥ := by
    let e5 : (⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ : Subgroup X) ≃*
        alternatingGroup (Fin 5) :=
      eAX.trans ((MulEquiv.subgroupCongr hD).trans ((conjFixedDEquiv g).trans fivePointEquiv))
    have h := map_center_eq e5.symm
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.map_bot] at h
    exact h.symm
  have hAout : Nat.card (Outer (⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ : Subgroup X)) ∣ 2 := by
    rw [Nat.card_congr (equivalence eAX).toEquiv, hD]
    exact card_outer_fixedD_map_conj_dvd g
  have htCL : t ∈ (centralizer {p}).subgroupOf L := by
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    exact htpc
  have hcomap : ⁅fixSub α, fixSub α⁆.comap π = (centralizer {p}).subgroupOf L := by
    have hkerK : π.ker ≤ (centralizer {p}).subgroupOf L := by
      rw [hker, zpowers_le]
      exact htCL
    rw [← hmap, comap_map_eq, sup_eq_left.2 hkerK]
  have hz2' : elemZ * elemZ = 1 := by rw [← sq, ← orderOf_elemZ, pow_orderOf_eq_one]
  have hzcomm₀ : ∀ c₀ ∈ fixSub beta, c₀ * elemZ = elemZ * c₀ := by
    intro c₀ hc₀
    rcases mem_fixSub_iff_decomp hc₀ with h | h
    · exact (elemZ_comm_fixedD c₀ h).symm
    · obtain ⟨d, hd, hdc⟩ : ∃ d ∈ fixedD, c₀ = elemZ * d :=
        ⟨elemZ * c₀, h, by rw [← mul_assoc, hz2', one_mul]⟩
      rw [hdc, mul_assoc, ← elemZ_comm_fixedD d hd]
  refine ⟨hα2, hαo, hAL, hsupX, hinfX, ⟨eA, heA⟩, hAperf, hAcard, hAZ, hAout, hcomap, hfus,
    g * elemZ * g⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun v hvz => ?_⟩
  · rw [mem_fixSub, hg]
    exact conj_beta_apply_conj g elemZ (mem_fixSub.mp elemZ_mem_fixSub)
  · intro c hc
    rw [hfix] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * c₀ * g⁻¹ * (g * elemZ * g⁻¹) = g * (c₀ * elemZ) * g⁻¹ := by group
      _ = g * (elemZ * c₀) * g⁻¹ := by rw [hzcomm₀ c₀ hc₀]
      _ = g * elemZ * g⁻¹ * (g * c₀ * g⁻¹) := by group
  · rw [hD]
    rintro ⟨d, hd, hdz⟩
    apply elemZ_not_mem
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hdz
    rwa [← mul_left_cancel (mul_right_cancel hdz)]
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_elemZ]
  · rw [fixedCount_conj, fixedCount_elemZ]
  · rw [hD, hfix, ← zpowers_sup_fixedD, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  · rw [hD, show zpowers (g * elemZ * g⁻¹) = (zpowers elemZ).map (MulAut.conj g).toMonoidHom by
      rw [MonoidHom.map_zpowers]; rfl, ← map_inf_eq _ _ _ (MulAut.conj g).injective,
      zpowers_inf_fixedD, Subgroup.map_bot]
  have hzfix : g * elemZ * g⁻¹ ∈ fixSub α := by
    rw [mem_fixSub, hg]
    exact conj_beta_apply_conj g elemZ (mem_fixSub.mp elemZ_mem_fixSub)
  have hzD : g * elemZ * g⁻¹ ∉ ⁅fixSub α, fixSub α⁆ := by
    rw [hD]
    rintro ⟨d, hd, hdz⟩
    apply elemZ_not_mem
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hdz
    rwa [← mul_left_cancel (mul_right_cancel hdz)]
  have hzc : ∀ c ∈ fixSub α, c * (g * elemZ * g⁻¹) = g * elemZ * g⁻¹ * c := by
    intro c hc
    rw [hfix] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * c₀ * g⁻¹ * (g * elemZ * g⁻¹) = g * (c₀ * elemZ) * g⁻¹ := by group
      _ = g * (elemZ * c₀) * g⁻¹ := by rw [hzcomm₀ c₀ hc₀]
      _ = g * elemZ * g⁻¹ * (g * c₀ * g⁻¹) := by group
  have hzo : orderOf (g * elemZ * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_elemZ]
  have hzdec : ∀ c ∈ fixSub α, c ∈ ⁅fixSub α, fixSub α⁆ ∨
      g * elemZ * g⁻¹ * c ∈ ⁅fixSub α, fixSub α⁆ := by
    intro c hc
    rw [hfix] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    rw [hD]
    rcases mem_fixSub_iff_decomp hc₀ with h | h
    · exact Or.inl ⟨c₀, h, rfl⟩
    · refine Or.inr ⟨elemZ * c₀, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hlift := (m12_double_cover_involution_lift_orders hLq ht hZ π hπ hker).2.2
  obtain ⟨hv2, -⟩ := hlift v (by rw [hvz]; exact hzo)
    (by rw [hvz, fixedCount_conj, fixedCount_elemZ])
  have hv2X : (v : X) ^ 2 = t := by rw [← SubgroupClass.coe_pow, hv2]
  have hpvL : p * v * p⁻¹ ∈ L := (mem_normalizer_iff.mp hpN v).mp v.2
  have hπv : π ⟨p * v * p⁻¹, hpvL⟩ = π v := by
    rw [← hα v ⟨p * v * p⁻¹, hpvL⟩ rfl, hvz]
    exact hzfix
  have hk : v⁻¹ * ⟨p * v * p⁻¹, hpvL⟩ ∈ zpowers t := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hπv, inv_mul_cancel]
  have hpv : p * v * p⁻¹ = v * t := by
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hk with h | h
    · exfalso
      apply hzD
      rw [← hvz, ← hmap]
      refine ⟨v, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf, mem_centralizer_singleton_iff]
      have h' : (⟨p * v * p⁻¹, hpvL⟩ : L) = v := (inv_mul_eq_one.mp h).symm
      have h'' : p * (v : X) * p⁻¹ = v := congrArg Subtype.val h'
      calc (v : X) * p = p * v * p⁻¹ * p := by rw [h'']
        _ = p * v := by group
    · have h' := congrArg Subtype.val (inv_mul_eq_iff_eq_mul.mp h)
      simpa using h'
  have hvCX : ∀ c ∈ L ⊓ centralizer {p}, (v : X) * c * (v : X)⁻¹ ∈ L ⊓ centralizer {p} := by
    intro c hc
    have hcL : c ∈ L := (mem_inf.mp hc).1
    have hcp : c ∈ centralizer {p} := (mem_inf.mp hc).2
    refine mem_inf.mpr ⟨L.mul_mem (L.mul_mem v.2 hcL) (L.inv_mem v.2), ?_⟩
    rw [mem_centralizer_singleton_iff] at hcp ⊢
    have htc : (t : X) * c = c * t := (congrArg Subtype.val (mem_center_iff.mp htZ ⟨c, hcL⟩)).symm
    have hpc : p * c * p⁻¹ = c := by
      rw [← hcp]
      group
    have h : p * ((v : X) * c * (v : X)⁻¹) * p⁻¹ = (v : X) * c * (v : X)⁻¹ := by
      calc p * ((v : X) * c * (v : X)⁻¹) * p⁻¹
          = (p * v * p⁻¹) * (p * c * p⁻¹) * (p * v * p⁻¹)⁻¹ := by group
        _ = ((v : X) * t) * c * ((v : X) * t)⁻¹ := by rw [hpv, hpc]
        _ = (v : X) * ((t : X) * c) * (t : X)⁻¹ * (v : X)⁻¹ := by group
        _ = (v : X) * c * (v : X)⁻¹ := by rw [htc]; group
    calc (v : X) * c * (v : X)⁻¹ * p = p * ((v : X) * c * (v : X)⁻¹) * p⁻¹ * p := by rw [h]
      _ = p * ((v : X) * c * (v : X)⁻¹) := by group
  have hvA : ∀ x ∈ ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆, (v : X) * x = x * v := by
    intro x hx
    have hle : (L ⊓ centralizer {p}).map (MulAut.conj (v : X)).toMonoidHom ≤
        L ⊓ centralizer {p} := by
      rintro _ ⟨c, hc, rfl⟩
      exact hvCX c hc
    have hxv : (v : X) * x * (v : X)⁻¹ ∈ ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ := by
      have h := mem_map_of_mem (MulAut.conj (v : X)).toMonoidHom hx
      rw [map_commutator] at h
      exact commutator_mono hle hle h
    have hxL : x ∈ L := hAL hx
    have hxvL : (v : X) * x * (v : X)⁻¹ ∈ L := hAL hxv
    have hxD : π ⟨x, hxL⟩ ∈ fixSub α := by
      have h := (eA ⟨⟨x, hxL⟩, hx⟩).2
      rw [heA] at h
      exact commutator_le_self _ h
    have hπeq : eA ⟨⟨_, hxvL⟩, hxv⟩ = eA ⟨⟨x, hxL⟩, hx⟩ := by
      apply Subtype.ext
      refine (heA _).trans (Eq.trans ?_ (heA _).symm)
      show π ⟨(v : X) * x * (v : X)⁻¹, hxvL⟩ = π ⟨x, hxL⟩
      have hval : (⟨(v : X) * x * (v : X)⁻¹, hxvL⟩ : L) = v * ⟨x, hxL⟩ * v⁻¹ := rfl
      rw [hval, map_mul, map_mul, map_inv, hvz, ← hzc _ hxD, mul_inv_cancel_right]
    have h1 : (v : X) * x * (v : X)⁻¹ = x :=
      congrArg Subtype.val (congrArg Subtype.val (eA.injective hπeq))
    calc (v : X) * x = (v : X) * x * (v : X)⁻¹ * v := by group
      _ = x * v := by rw [h1]
  have hlift' : ∀ l : L, p * l * p⁻¹ = l * t → (v : X)⁻¹ * l ∈ L ⊓ centralizer {p} := by
    intro l hl
    have hplL : p * l * p⁻¹ ∈ L := (mem_normalizer_iff.mp hpN l).mp l.2
    have hl' : (⟨p * l * p⁻¹, hplL⟩ : L) = l * t := Subtype.ext hl
    have hπt : π t = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact mem_zpowers t
    have hfixl : π l ∈ fixSub α := by
      rw [mem_fixSub, hα l ⟨p * l * p⁻¹, hplL⟩ rfl, hl', map_mul, hπt, mul_one]
    rcases hzdec _ hfixl with h | h
    · exfalso
      have hlC : l ∈ (centralizer {p}).subgroupOf L := by
        rw [← hcomap]
        exact h
      rw [mem_subgroupOf, mem_centralizer_singleton_iff] at hlC
      have h2 : p * (l : X) * p⁻¹ = l := by
        rw [← hlC]
        group
      rw [h2] at hl
      exact ht1 (Subtype.ext (mul_eq_left.mp hl.symm))
    · have hvl : v⁻¹ * l ∈ (centralizer {p}).subgroupOf L := by
        rw [← hcomap, mem_comap, map_mul, map_inv, hvz]
        have hzinv : (g * elemZ * g⁻¹)⁻¹ = g * elemZ * g⁻¹ :=
          inv_eq_of_mul_eq_one_right (by rw [← sq, ← hzo, pow_orderOf_eq_one])
        rw [hzinv]
        exact h
      rw [mem_subgroupOf] at hvl
      refine mem_inf.mpr ⟨mul_mem (inv_mem v.2) l.2, ?_⟩
      simpa using hvl
  exact ⟨hv2X, hpv, hvA, hlift'⟩

theorem inf_centralizer_eq_zpowers {Y : Type*} [Group Y] {L : Subgroup Y} {t : L}
    (hZ : center L = zpowers t) : L ⊓ centralizer (L : Set Y) = zpowers (t : Y) := by
  have h : (center L).map L.subtype = zpowers (t : Y) := by
    rw [hZ, MonoidHom.map_zpowers]
    rfl
  rw [← h]
  ext x
  constructor
  · intro hx
    obtain ⟨hxL, hxC⟩ := mem_inf.mp hx
    exact ⟨⟨x, hxL⟩, mem_center_iff.mpr fun l =>
      Subtype.ext (mem_centralizer_iff.mp hxC l l.2), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact mem_inf.mpr ⟨y.2, mem_centralizer_iff.mpr fun l hl =>
      congrArg Subtype.val (mem_center_iff.mp hy ⟨l, hl⟩)⟩

end CyclicKernel

open CyclicKernel

theorem ctss_m12_outer_involution_full_cyclic_kernel_common_centralizer_ambient
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} (hLq : CFSG.Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t)
    (hN : centralizer {(t : G)} ≤ normalizer (L : Set G)) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {S : Subgroup G}
    (hS : S = centralizer {(t : G)} ⊓ centralizer (L : Set G)) (hScyc : IsCyclic S)
    (hS2 : IsPGroup 2 S) (hS4 : 4 ≤ Nat.card S) {p : G} (hpH : p ∈ centralizer {(t : G)})
    (hp : orderOf p = 2) (hpLS : p ∉ L ⊔ S) (hHp : L ⊔ S ⊔ zpowers p = centralizer {(t : G)})
    (hSp : S ⊓ centralizer {p} = zpowers (t : G)) {A : Subgroup G}
    (hA : A = ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆) :
    A ≤ L ∧ ⁅A, A⁆ = A ∧ Nat.card A = 60 ∧ center A = ⊥ ∧ Nat.card (Outer A) ∣ 2 ∧
    centralizer (closure ({(t : G), p} : Set G) : Set G) =
      centralizer {(t : G)} ⊓ centralizer {p} ∧
    ⁅centralizer (closure ({(t : G), p} : Set G) : Set G),
      centralizer (closure ({(t : G), p} : Set G) : Set G)⁆ = A ∧
    (A.subgroupOf (centralizer (closure ({(t : G), p} : Set G) : Set G))).Characteristic ∧
    ∃ w : G, w ∈ L ⊔ S ∧ w ∉ L ∧ orderOf w = 2 ∧
      closure ({(t : G), p, w} : Set G) ⊔ A =
        centralizer (closure ({(t : G), p} : Set G) : Set G) ∧
      closure ({(t : G), p, w} : Set G) ⊓ A = ⊥ ∧
      Nat.card (closure ({(t : G), p, w} : Set G)) = 8 ∧
      CFSG.IsElementaryAbelian 2 (closure ({(t : G), p, w} : Set G)) ∧
      (center (centralizer (closure ({(t : G), p} : Set G) : Set G))).map
          (centralizer (closure ({(t : G), p} : Set G) : Set G)).subtype =
        closure ({(t : G), p, w} : Set G) := by
  classical
  have htX : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htZ : t ∈ center L := hZ ▸ mem_zpowers t
  have hLH : L ≤ centralizer {(t : G)} := fun l hl => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_center_iff.mp htZ ⟨l, hl⟩))
  have hpN : p ∈ normalizer (L : Set G) := hN hpH
  have hpC : ∀ l ∈ L, l * p ∉ centralizer (L : Set G) := fun l hl h => hpLS (by
    have h' : p = l⁻¹ * (l * p) := by group
    rw [h']
    refine mul_mem (mem_sup_left (inv_mem hl)) (mem_sup_right ?_)
    rw [hS]
    exact mem_inf.mpr ⟨mul_mem (hLH hl) hpH, h⟩)
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  obtain ⟨θ, hθ, -⟩ := exists_normalizer_action hN π hπ (hker.trans hZ.symm)
  obtain ⟨-, -, hAL, hsupA, hinfA, -, hAperf, hAcard, hAZ, hAout, -, -, z, -, -, -, -, -, -, -,
    hv⟩ := outer_involution_fixed_factor hLq ht hZ π hπ hker hpN hp hpC (θ ⟨p, hpH⟩)
      (fun l l' h => hθ ⟨p, hpH⟩ l l' h) rfl hA
  obtain ⟨v, hvz⟩ := hπ z
  obtain ⟨hv2, hpv, hvA, hlift⟩ := hv v hvz
  have htS : (t : G) ∈ S := by
    have h : (t : G) ∈ L ⊓ centralizer (L : Set G) := by
      rw [inf_centralizer_eq_zpowers hZ]
      exact mem_zpowers _
    rw [hS]
    exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, (mem_inf.mp h).2⟩
  obtain ⟨a, haS, ha4⟩ := exists_orderOf_eq_four_of_isCyclic hScyc hS2 (by omega)
  have ha2 : a ^ 2 = t := by
    refine eq_of_orderOf_eq_two_of_isCyclic hScyc (pow_mem haS 2) htS ?_ htX
    have h := orderOf_pow_orderOf_div (x := a) (n := 2) (by rw [ha4]; norm_num)
      (by rw [ha4]; norm_num)
    rw [ha4] at h
    norm_num at h
    exact h
  obtain ⟨-, hwo, hwLS, hwL, hCHp, hEAinf, -, hEcard, hEelem, hcenter, hder⟩ :=
    centralizer_eq_sup_closure_of_lift hLH hN t.2 htX
      (fun h hh => mem_centralizer_singleton_iff.mp hh) (inf_centralizer_eq_zpowers hZ) hS
      hScyc hpH hp hpLS hHp hSp hAL hsupA hinfA hAperf hAZ v.2 hv2 hpv hvA
      (fun l hl h => hlift ⟨l, hl⟩ h) haS ha2
  have hCV : centralizer (closure ({(t : G), p} : Set G) : Set G) =
      centralizer {(t : G)} ⊓ centralizer {p} := centralizer_closure_pair (t : G) p
  have hderC : ⁅centralizer (closure ({(t : G), p} : Set G) : Set G),
      centralizer (closure ({(t : G), p} : Set G) : Set G)⁆ = A := by
    rw [hCV]
    exact hder
  refine ⟨hAL, hAperf, hAcard, hAZ, hAout, hCV, hderC, ?_, a * v, hwLS, hwL, hwo, ?_, hEAinf,
    hEcard, hEelem, ?_⟩
  · have h : A.subgroupOf (centralizer (closure ({(t : G), p} : Set G) : Set G)) =
        _root_.commutator (centralizer (closure ({(t : G), p} : Set G) : Set G)) := by
      rw [← hderC, ← map_subtype_commutator]
      exact comap_map_eq_self_of_injective (subtype_injective _) _
    rw [h]
    infer_instance
  · rw [hCV]
    exact hCHp
  · rw [hCV]
    exact hcenter

end CFSG.ComponentClassification.M12Cover
