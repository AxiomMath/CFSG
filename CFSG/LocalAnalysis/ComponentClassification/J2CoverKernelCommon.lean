module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelExternal
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelCommon

public section

namespace CFSG.ComponentClassification.J2Cover

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

namespace CyclicKernel

open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_mul_of_mem_sup_of_commute
  card_sup_of_commute mem_or_mul_mem_of_mem_sup_zpowers
  eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two eq_one_or_eq_of_sq_eq_one_of_isCyclic
  mul_comm_of_isCyclic closure_triple_eq_sup centralizer_closure_pair inf_centralizer_eq_zpowers
  exists_orderOf_eq_four_of_isCyclic eq_of_orderOf_eq_two_of_isCyclic)

variable {X : Type*} [Group X]

theorem exists_mul_of_mem_sup_of_normalizes {E A : Subgroup X}
    (hEA : ∀ e ∈ E, ∀ x ∈ A, e * x * e⁻¹ ∈ A) {y : X} (hy : y ∈ E ⊔ A) :
    ∃ e ∈ E, ∃ x ∈ A, y = e * x := by
  let M : Subgroup X :=
    { carrier := {y | ∃ e ∈ E, ∃ x ∈ A, y = e * x}
      one_mem' := ⟨1, E.one_mem, 1, A.one_mem, by rw [one_mul]⟩
      mul_mem' := by
        rintro _ _ ⟨e₁, he₁, x₁, hx₁, rfl⟩ ⟨e₂, he₂, x₂, hx₂, rfl⟩
        refine ⟨e₁ * e₂, E.mul_mem he₁ he₂, e₂⁻¹ * x₁ * e₂⁻¹⁻¹ * x₂,
          A.mul_mem (hEA _ (E.inv_mem he₂) _ hx₁) hx₂, by group⟩
      inv_mem' := by
        rintro _ ⟨e, he, x, hx, rfl⟩
        exact ⟨e⁻¹, E.inv_mem he, e * x⁻¹ * e⁻¹, hEA _ he _ (A.inv_mem hx), by group⟩ }
  have hle : E ⊔ A ≤ M := sup_le (fun e he => ⟨e, he, 1, A.one_mem, by rw [mul_one]⟩)
    (fun x hx => ⟨1, E.one_mem, x, hx, by rw [one_mul]⟩)
  exact hle hy

theorem commutator_sup_le_of_normalizes {E A : Subgroup X}
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEA : ∀ e ∈ E, ∀ x ∈ A, e * x * e⁻¹ ∈ A) :
    ⁅E ⊔ A, E ⊔ A⁆ ≤ A := by
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨e₁, he₁, a₁, ha₁, rfl⟩ := exists_mul_of_mem_sup_of_normalizes hEA hx
  obtain ⟨e₂, he₂, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_normalizes hEA hy
  have hX : (e₂⁻¹ * a₁ * e₂) * a₂ * a₁⁻¹ * (e₁⁻¹ * a₂ * e₁)⁻¹ ∈ A := by
    refine A.mul_mem (A.mul_mem (A.mul_mem ?_ ha₂) (A.inv_mem ha₁)) (A.inv_mem ?_)
    · simpa using hEA _ (E.inv_mem he₂) _ ha₁
    · simpa using hEA _ (E.inv_mem he₁) _ ha₂
  have key : ⁅e₁ * a₁, e₂ * a₂⁆ =
      (e₁ * e₂) * ((e₂⁻¹ * a₁ * e₂) * a₂ * a₁⁻¹ * (e₁⁻¹ * a₂ * e₁)⁻¹) * (e₂ * e₁)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [key, ← hE e₁ he₁ e₂ he₂]
  exact hEA _ (E.mul_mem he₁ he₂) _ hX

variable [Finite X]

theorem centralizer_eq_sup_closure_of_outer_lift {L H S A : Subgroup X} (hLH : L ≤ H)
    (hHN : H ≤ normalizer (L : Set X)) {t : X} (htL : t ∈ L) (ht : orderOf t = 2)
    (htH : ∀ h ∈ H, h * t = t * h) (hLC : L ⊓ centralizer (L : Set X) = zpowers t)
    (hS : S = H ⊓ centralizer (L : Set X)) (hScyc : IsCyclic S) {p : X} (hpH : p ∈ H)
    (hp : orderOf p = 2) (hpLS : p ∉ L ⊔ S) (hHp : L ⊔ S ⊔ zpowers p = H)
    (hSp : S ⊓ centralizer {p} = zpowers t) (hAL : A ≤ L)
    (hsupA : zpowers t ⊔ A = L ⊓ centralizer {p}) (hinfA : zpowers t ⊓ A = ⊥)
    (hAperf : ⁅A, A⁆ = A) (hAZ : center A = ⊥) {v : X} (hvL : v ∈ L) (hv2 : v ^ 2 = t)
    (hpv : p * v * p⁻¹ = v * t) (hvA : ∀ x ∈ A, v * x * v⁻¹ ∈ A)
    (hvout : ¬ ∃ b ∈ A, ∀ x ∈ A, v * x * v⁻¹ = b * x * b⁻¹)
    (hlift : ∀ l ∈ L, p * l * p⁻¹ = l * t → v⁻¹ * l ∈ L ⊓ centralizer {p}) {a : X}
    (haS : a ∈ S) (ha2 : a ^ 2 = t) :
    p * a * p⁻¹ = a⁻¹ ∧ orderOf (a * v) = 2 ∧ a * v ∈ L ⊔ S ∧ a * v ∉ L ∧
    a * v ∈ centralizer {p} ∧
    closure ({t, p, a * v} : Set X) ⊔ A = H ⊓ centralizer {p} ∧
    closure ({t, p, a * v} : Set X) ⊓ A = ⊥ ∧
    (∀ e ∈ closure ({t, p, a * v} : Set X), ∀ x ∈ A, e * x * e⁻¹ ∈ A) ∧
    closure ({t, p, a * v} : Set X) ⊓ centralizer (A : Set X) = closure ({t, p} : Set X) ∧
    Nat.card (closure ({t, p, a * v} : Set X)) = 8 ∧
    CFSG.IsElementaryAbelian 2 (closure ({t, p, a * v} : Set X)) ∧
    (center (H ⊓ centralizer {p} : Subgroup X)).map (H ⊓ centralizer {p}).subtype =
      closure ({t, p} : Set X) ∧
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
  have hwA : ∀ x ∈ A, (a * v) * x * (a * v)⁻¹ = v * x * v⁻¹ := by
    intro x hx
    have h1 : a * (v * x * v⁻¹) = (v * x * v⁻¹) * a := haL _ (hAL (hvA x hx))
    calc (a * v) * x * (a * v)⁻¹ = a * (v * x * v⁻¹) * a⁻¹ := by group
      _ = v * x * v⁻¹ := by rw [h1, mul_inv_cancel_right]
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
  have hVC : V ≤ centralizer (A : Set X) := by
    rw [hV, closure_le]
    intro g hg
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact mem_centralizer_iff.mp htLC.2 y (hAL hy)
    · exact mem_centralizer_singleton_iff.mp (hAp y hy).2
  have hVA : ∀ u ∈ V, ∀ x ∈ A, u * x * u⁻¹ = x := by
    intro u hu x hx
    rw [show u * x = x * u from (mem_centralizer_iff.mp (hVC hu) x hx).symm, mul_inv_cancel_right]
  have hEdec : ∀ e ∈ closure ({t, p, w} : Set X), e ∈ V ∨ ∃ u ∈ V, e = u * w := by
    intro e he
    rw [hE] at he
    obtain ⟨u, hu, n, hn, rfl⟩ := exists_mul_of_mem_sup_of_commute hVw he
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hwo hn with rfl | rfl
    · left
      rwa [mul_one]
    · exact Or.inr ⟨u, hu, rfl⟩
  have hEnA : ∀ e ∈ closure ({t, p, w} : Set X), ∀ x ∈ A, e * x * e⁻¹ ∈ A := by
    intro e he x hx
    rcases hEdec e he with h | ⟨u, hu, rfl⟩
    · rw [hVA e h x hx]
      exact hx
    · have h1 : u * w * x * (u * w)⁻¹ = u * (w * x * w⁻¹) * u⁻¹ := by group
      rw [h1, hVA u hu _ (by rw [hwA x hx]; exact hvA x hx), hwA x hx]
      exact hvA x hx
  have hVE : V ≤ closure ({t, p, w} : Set X) := by
    rw [hV, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
  have hwout : ∀ u ∈ V, u * w ∉ centralizer (A : Set X) := by
    intro u hu h
    apply hvout
    refine ⟨1, A.one_mem, fun x hx => ?_⟩
    have h1 : (u * w) * x * (u * w)⁻¹ = x := by
      rw [show (u * w) * x = x * (u * w) from (mem_centralizer_iff.mp h x hx).symm,
        mul_inv_cancel_right]
    have h2 : (u * w) * x * (u * w)⁻¹ = v * x * v⁻¹ := by
      rw [show (u * w) * x * (u * w)⁻¹ = u * (w * x * w⁻¹) * u⁻¹ by group,
        hVA u hu _ (by rw [hwA x hx]; exact hvA x hx), hwA x hx]
    rw [← h2, h1, one_mul, inv_one, mul_one]
  have hkerE : closure ({t, p, w} : Set X) ⊓ centralizer (A : Set X) = V := by
    apply le_antisymm
    · rintro e ⟨he, hec⟩
      rcases hEdec e he with h | ⟨u, hu, rfl⟩
      · exact h
      · exact absurd hec (hwout u hu)
    · exact le_inf hVE hVC
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
      V := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hzE : (z : X) ∈ closure ({t, p, w} : Set X) ⊔ A := by rw [hCHp]; exact z.2
      obtain ⟨e, he, b, hb, hzeb⟩ := exists_mul_of_mem_sup_of_normalizes hEnA hzE
      have hzA : ∀ x ∈ A, (z : X) * x * (z : X)⁻¹ = x := by
        intro x hx
        have hxC : x ∈ H ⊓ centralizer {p} := by rw [← hCHp]; exact mem_sup_right hx
        have h := congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hxC⟩)
        simp only [Subgroup.coe_mul] at h
        rw [← h, mul_inv_cancel_right]
      show (z : X) ∈ V
      rcases hEdec e he with heV | ⟨u, hu, rfl⟩
      ·
        have hbZ : (⟨b, hb⟩ : A) ∈ center A := by
          rw [mem_center_iff]
          intro y
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          have h1 := hzA y y.2
          rw [hzeb, show e * b * (y : X) * (e * b)⁻¹ = e * (b * y * b⁻¹) * e⁻¹ by group,
            hVA e heV _ (A.mul_mem (A.mul_mem hb y.2) (A.inv_mem hb))] at h1
          calc (y : X) * b = b * y * b⁻¹ * b := by rw [h1]
            _ = b * y := by group
        rw [hAZ, mem_bot] at hbZ
        have hb1 : b = 1 := congrArg Subtype.val hbZ
        rw [hzeb, hb1, mul_one]
        exact heV
      ·
        exfalso
        apply hvout
        refine ⟨b⁻¹, A.inv_mem hb, fun x hx => ?_⟩
        have hy : b⁻¹ * x * b ∈ A := by
          simpa using A.mul_mem (A.mul_mem (A.inv_mem hb) hx) hb
        have h1 := hzA _ hy
        have hbxb : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
        rw [hzeb, show u * w * b * (b⁻¹ * x * b) * (u * w * b)⁻¹ =
          u * (w * (b * (b⁻¹ * x * b) * b⁻¹) * w⁻¹) * u⁻¹ by group, hbxb, hwA x hx,
          hVA u hu _ (hvA x hx)] at h1
        rw [h1, inv_inv]
    · intro x hx
      have hxC : x ∈ H ⊓ centralizer {p} := by rw [← hCHp]; exact mem_sup_left (hVE hx)
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have hgV : (g : X) ∈ centralizer (V : Set X) := by
        rw [hV, centralizer_closure, mem_centralizer_iff]
        intro h hh
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
        rcases hh with rfl | rfl
        · exact (htH g (mem_inf.mp g.2).1).symm
        · exact (mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).2).symm
      exact (mem_centralizer_iff.mp hgV x hx).symm
  have hder : ⁅H ⊓ centralizer {p}, H ⊓ centralizer {p}⁆ = A := by
    rw [← hCHp]
    refine le_antisymm (commutator_sup_le_of_normalizes hEcomm hEnA) ?_
    calc A = ⁅A, A⁆ := hAperf.symm
      _ ≤ _ := commutator_mono le_sup_right le_sup_right
  exact ⟨hpa, hwo, hwLS, hwL, hwC, hCHp, hEAinf, hEnA, hkerE, hEcard, hEelem, hcenter, hder⟩

theorem exists_sq_eq_of_isCyclic {S : Subgroup X} (hScyc : IsCyclic S) (hS2 : IsPGroup 2 S)
    (hS4 : 4 ≤ Nat.card S) {t : X} (htS : t ∈ S) (ht : orderOf t = 2) : ∃ a ∈ S, a ^ 2 = t := by
  obtain ⟨a, haS, ha4⟩ := exists_orderOf_eq_four_of_isCyclic hScyc hS2 (by omega)
  refine ⟨a, haS, eq_of_orderOf_eq_two_of_isCyclic hScyc (pow_mem haS 2) htS ?_ ht⟩
  have h := orderOf_pow_orderOf_div (x := a) (n := 2) (by rw [ha4]; norm_num)
    (by rw [ha4]; norm_num)
  rwa [ha4, show (4 : ℕ) / 2 = 2 by norm_num] at h

end CyclicKernel

open CyclicKernel
open CFSG.ComponentClassification.M12Cover.CyclicKernel (inf_centralizer_eq_zpowers
  centralizer_closure_pair)

theorem ctss_j2_outer_involution_full_cyclic_kernel_common_centralizer_ambient
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} (hLq : CFSG.Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t)
    (hN : centralizer {(t : G)} ≤ normalizer (L : Set G)) (π : L →* P)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {S : Subgroup G}
    (hS : S = centralizer {(t : G)} ⊓ centralizer (L : Set G)) (hScyc : IsCyclic S)
    (hS2 : IsPGroup 2 S) (hS4 : 4 ≤ Nat.card S) {p : G} (hpH : p ∈ centralizer {(t : G)})
    (hp : orderOf p = 2) (hpLS : p ∉ L ⊔ S) (hHp : L ⊔ S ⊔ zpowers p = centralizer {(t : G)})
    (hSp : S ⊓ centralizer {p} = zpowers (t : G)) {A : Subgroup G}
    (hA : A = ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆) :
    A ≤ L ∧ ⁅A, A⁆ = A ∧ Nat.card A = 168 ∧ center A = ⊥ ∧ Nat.card (Outer A) ∣ 2 ∧
    centralizer (closure ({(t : G), p} : Set G) : Set G) =
      centralizer {(t : G)} ⊓ centralizer {p} ∧
    ⁅centralizer (closure ({(t : G), p} : Set G) : Set G),
      centralizer (closure ({(t : G), p} : Set G) : Set G)⁆ = A ∧
    (A.subgroupOf (centralizer (closure ({(t : G), p} : Set G) : Set G))).Characteristic ∧
    (center (centralizer (closure ({(t : G), p} : Set G) : Set G))).map
        (centralizer (closure ({(t : G), p} : Set G) : Set G)).subtype =
      closure ({(t : G), p} : Set G) ∧
    ∃ w : G, w ∈ L ⊔ S ∧ w ∉ L ∧ orderOf w = 2 ∧
      closure ({(t : G), p, w} : Set G) ⊔ A =
        centralizer (closure ({(t : G), p} : Set G) : Set G) ∧
      closure ({(t : G), p, w} : Set G) ⊓ A = ⊥ ∧
      (∀ e ∈ closure ({(t : G), p, w} : Set G), ∀ x ∈ A, e * x * e⁻¹ ∈ A) ∧
      closure ({(t : G), p, w} : Set G) ⊓ centralizer (A : Set G) =
        closure ({(t : G), p} : Set G) ∧
      Nat.card (closure ({(t : G), p, w} : Set G)) = 8 ∧
      CFSG.IsElementaryAbelian 2 (closure ({(t : G), p, w} : Set G)) := by
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
  obtain ⟨θ, hθ, -⟩ :=
    M12Cover.CyclicKernel.exists_normalizer_action hN π hπ (hker.trans hZ.symm)
  obtain ⟨hAL, hsupA, hinfA, hAperf, hAcard, hAZ, hAout, -, v, hvL, hv2, hpv, -, hvA, hvout,
    hlift⟩ := j2_outer_involution_fixed_factor hLq ht hZ π hπ hker hpN hp hpC (θ ⟨p, hpH⟩)
      (fun l l' h => hθ ⟨p, hpH⟩ l l' h) hA
  have htS : (t : G) ∈ S := by
    have h : (t : G) ∈ L ⊓ centralizer (L : Set G) := by
      rw [inf_centralizer_eq_zpowers hZ]
      exact mem_zpowers _
    rw [hS]
    exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, (mem_inf.mp h).2⟩
  obtain ⟨a, haS, ha2⟩ := exists_sq_eq_of_isCyclic hScyc hS2 hS4 htS htX
  obtain ⟨-, hwo, hwLS, hwL, -, hCHp, hEAinf, hEnA, hkerE, hEcard, hEelem, hcenter, hder⟩ :=
    centralizer_eq_sup_closure_of_outer_lift hLH hN t.2 htX
      (fun h hh => mem_centralizer_singleton_iff.mp hh) (inf_centralizer_eq_zpowers hZ) hS
      hScyc hpH hp hpLS hHp hSp hAL hsupA hinfA hAperf hAZ hvL hv2 hpv hvA hvout hlift haS ha2
  have hCV : centralizer (closure ({(t : G), p} : Set G) : Set G) =
      centralizer {(t : G)} ⊓ centralizer {p} := centralizer_closure_pair (t : G) p
  have hderC : ⁅centralizer (closure ({(t : G), p} : Set G) : Set G),
      centralizer (closure ({(t : G), p} : Set G) : Set G)⁆ = A := by
    rw [hCV]
    exact hder
  refine ⟨hAL, hAperf, hAcard, hAZ, hAout, hCV, hderC, ?_, by rw [hCV]; exact hcenter, a * v,
    hwLS, hwL, hwo, by rw [hCV]; exact hCHp, hEAinf, hEnA, hkerE, hEcard, hEelem⟩
  have h : A.subgroupOf (centralizer (closure ({(t : G), p} : Set G) : Set G)) =
      _root_.commutator (centralizer (closure ({(t : G), p} : Set G) : Set G)) := by
    rw [← hderC, ← map_subtype_commutator]
    exact comap_map_eq_self_of_injective (subtype_injective _) _
  rw [h]
  infer_instance

end CFSG.ComponentClassification.J2Cover
