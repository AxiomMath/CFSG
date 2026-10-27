module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenRes

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

@[expose] def omegaZ {G : Type*} [Group G] (P : Subgroup G) (p : ℕ) : Subgroup G where
  carrier := {z | z ∈ P ∧ (∀ a ∈ P, a * z = z * a) ∧ z ^ p = 1}
  one_mem' := ⟨one_mem _, fun a _ => by simp, one_pow _⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun c hc => by
    rw [← mul_assoc, ha.2.1 c hc, mul_assoc, hb.2.1 c hc, ← mul_assoc], by
    rw [(show Commute a b from hb.2.1 a ha.1).mul_pow, ha.2.2, hb.2.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun c hc => by
    have := ha.2.1 c hc
    calc c * a⁻¹ = a⁻¹ * (a * c) * a⁻¹ := by group
      _ = a⁻¹ * (c * a) * a⁻¹ := by rw [this]
      _ = a⁻¹ * c := by group, by rw [inv_pow, ha.2.2, inv_one]⟩

section Invariant

variable {V : Type} [CommGroup V]

theorem mem_stabW_fixV {E : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (E : Set (MulAut V))) : g ∈ stabW (fixV E) := by
  intro w
  constructor
  · intro hw e he
    have hconj : g⁻¹ * e * g ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) e).mp he
    have h1 := hw (g⁻¹ * e * g) hconj
    have h2 : e (g w) = g ((g⁻¹ * e * g) w) := by simp [MulAut.mul_apply]
    rw [h2, h1]
  · intro hw e he
    have hconj : g * e * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hg e).mp he
    have h1 := hw (g * e * g⁻¹) hconj
    have h2 : (g * e * g⁻¹) (g w) = g (e w) := by simp [MulAut.mul_apply]
    rw [h2] at h1
    exact g.injective h1

theorem mem_stabW_ker_normK (E : Subgroup (MulAut V)) [Fintype ↥E] {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (E : Set (MulAut V))) : g ∈ stabW (normK E).ker := by
  intro v
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, normK_apply_of_mem_normalizer E hg v]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    exact g.injective (by rw [h, map_one])

end Invariant

section Main

@[expose] def NoCaseB : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ Y : Subgroup (MulAut V), Small16 Y →
      ∀ (P : Subgroup (MulAut V)) (p : ℕ), p.Prime → Odd p → IsPGroup p P →
        Y ≤ Subgroup.normalizer (P : Set (MulAut V)) →
        ¬ P ≤ Subgroup.centralizer (Y : Set (MulAut V)) →
        (∀ Q : Subgroup (MulAut V), Q < P → Y ≤ Subgroup.normalizer (Q : Set (MulAut V)) →
          Q ≤ Subgroup.centralizer (Y : Set (MulAut V))) →
        (¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) → fixV (omegaZ P p) = ⊥ → False

theorem card_lt_of_ne_top {V : Type} [CommGroup V] [Finite V] {W : Subgroup V} (h : W ≠ ⊤) :
    Nat.card W < Nat.card V :=
  lt_of_le_of_ne (Subgroup.card_le_card_group W) fun heq => h (Subgroup.eq_top_of_card_eq W heq)

theorem le_centralizer_of_small16_aux (hB : NoCaseB) (n : ℕ) :
    ∀ (V : Type) [CommGroup V] [Finite V], Nat.card V = n → (∀ v : V, v ^ 2 = 1) →
      ∀ Y : Subgroup (MulAut V), Small16 Y → ∀ X : Subgroup (MulAut V), Odd (Nat.card X) →
        Y ≤ Subgroup.normalizer (X : Set (MulAut V)) →
          X ≤ Subgroup.centralizer (Y : Set (MulAut V)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ hn hV Y hY X hX hYX
  by_contra hne
  obtain ⟨p, P, hp, hpodd, hPX, hP, hYP, hPne, hmin⟩ := exists_minimal_pSubgroup hY.1 hX hYX hne
  by_cases hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  · exact false_of_abelian_minimal hV hY hp hpodd hP hab hYP hmin hPne
  have : Fact p.Prime := ⟨hp⟩
  have hoddP : Odd (Nat.card P) := Odd.of_dvd_nat hX (Subgroup.card_dvd_of_le hPX)
  have hEP : omegaZ P p ≤ P := fun z hz => hz.1
  have hEc : ∀ e ∈ omegaZ P p, ∀ a ∈ P, a * e = e * a := fun e he a ha => he.2.1 a ha
  have hEne : omegaZ P p ≠ ⊥ := by
    intro hbot
    have hPbot : P ≠ ⊥ := fun h => hPne (h ▸ bot_le)
    have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPbot
    have : Nontrivial ↥(Subgroup.center ↥P) := hP.center_nontrivial
    have hZp : IsPGroup p ↥(Subgroup.center ↥P) := hP.to_subgroup _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1 := Finite.one_lt_card_iff_nontrivial.mpr
        (inferInstance : Nontrivial ↥(Subgroup.center ↥P))
      rw [hk, pow_zero] at h1
      exact lt_irrefl _ h1
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥P)) p
      (hk ▸ dvd_pow_self p hk0)
    have hzE : (((z : ↥P) : MulAut V)) ∈ omegaZ P p := by
      refine ⟨(z : ↥P).2, fun a ha => ?_, ?_⟩
      · have := Subgroup.mem_center_iff.mp z.2 ⟨a, ha⟩
        exact congrArg Subtype.val this
      · have h1 : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
        exact congrArg (fun t : ↥(Subgroup.center ↥P) => (((t : ↥P)) : MulAut V)) h1
    have hz1 : ((z : ↥P) : MulAut V) = 1 := by
      rw [hbot] at hzE
      exact hzE
    have : z = 1 := Subtype.ext (Subtype.ext hz1)
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hconjE : ∀ y ∈ Y, ∀ z ∈ omegaZ P p, y * z * y⁻¹ ∈ omegaZ P p := by
    intro y hy z hz
    have hyn := hYP hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp hyn z).mp (hEP hz), fun a ha => ?_, ?_⟩
    · have ha' : y⁻¹ * a * y ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hyn) a).mp ha
      have h1 := hEc z hz _ ha'
      calc a * (y * z * y⁻¹) = y * ((y⁻¹ * a * y) * z) * y⁻¹ := by group
        _ = y * (z * (y⁻¹ * a * y)) * y⁻¹ := by rw [h1]
        _ = (y * z * y⁻¹) * a := by group
    · rw [conj_pow, hz.2.2]; group
  have hYE : Y ≤ Subgroup.normalizer (omegaZ P p : Set (MulAut V)) := fun y hy =>
    normalizer_mem_of_conj (hconjE y hy) (fun z hz => by
      simpa using hconjE y⁻¹ (inv_mem hy) z hz)
  have hPE : P ≤ Subgroup.normalizer (omegaZ P p : Set (MulAut V)) := by
    intro g hg
    have key : ∀ z ∈ omegaZ P p, g * z * g⁻¹ = z := fun z hz => by
      rw [hEc z hz g hg, mul_inv_cancel_right]
    exact normalizer_mem_of_conj (fun z hz => by rw [key z hz]; exact hz) (fun z hz => by
      have : g⁻¹ * z * g = z := by
        calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [key z hz]
          _ = z := by group
      rw [this]; exact hz)
  have hEltP : omegaZ P p < P := lt_of_le_of_ne hEP fun h => hab fun a ha b hb => by
    have hbE : b ∈ omegaZ P p := by rw [h]; exact hb
    exact hEc b hbE a ha
  have hEC : omegaZ P p ≤ Subgroup.centralizer (Y : Set (MulAut V)) := hmin _ hEltP hYE
  have : Fintype ↥(omegaZ P p) := Fintype.ofFinite _
  have hoddE : Odd (Fintype.card ↥(omegaZ P p)) := by
    rw [← Nat.card_eq_fintype_card]
    exact Odd.of_dvd_nat hoddP (Subgroup.card_dvd_of_le hEP)
  have hsup := normK_ker_sup_fixV (omegaZ P p) hoddE hV
  have hinf := normK_ker_inf_fixV (omegaZ P p) hoddE hV
  have hYW : Y ≤ stabW (fixV (omegaZ P p)) := fun y hy => mem_stabW_fixV (hYE hy)
  have hPW : P ≤ stabW (fixV (omegaZ P p)) := fun y hy => mem_stabW_fixV (hPE hy)
  have hYV : Y ≤ stabW (normK (omegaZ P p)).ker := fun y hy =>
    mem_stabW_ker_normK _ (hYE hy)
  have hPV : P ≤ stabW (normK (omegaZ P p)).ker := fun y hy =>
    mem_stabW_ker_normK _ (hPE hy)
  have hV' : ∀ (W : Subgroup V) (v : ↥W), v ^ 2 = 1 := fun W v =>
    Subtype.ext (by simpa using hV (v : V))
  let K : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ P ∧ ∀ w ∈ fixV (omegaZ P p), g w = w}
      one_mem' := ⟨one_mem _, fun w _ => rfl⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun w hw => by
        show a (b w) = w
        rw [hb.2 w hw, ha.2 w hw]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun w hw => by
        calc a⁻¹ w = a⁻¹ (a w) := by rw [ha.2 w hw]
          _ = w := by simp⟩ }
  have hKP : K ≤ P := fun g hg => hg.1
  have hKconj : ∀ g : MulAut V, g ∈ stabW (fixV (omegaZ P p)) → (∀ k ∈ P, g * k * g⁻¹ ∈ P) →
      ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg hgP k hk
    refine ⟨hgP k hk.1, fun w hw => ?_⟩
    have hw' : g⁻¹ w ∈ fixV (omegaZ P p) :=
      (mem_stabW.mp hg (g⁻¹ w)).mpr (by rw [MulAut.apply_inv_self]; exact hw)
    show g (k (g⁻¹ w)) = w
    rw [hk.2 _ hw']
    simp
  have hPK : P ≤ Subgroup.normalizer (K : Set (MulAut V)) := fun g hg =>
    normalizer_mem_of_conj
      (hKconj g (hPW hg) (fun k hk => mul_mem (mul_mem hg hk) (inv_mem hg)))
      (fun k hk => by
        simpa using hKconj g⁻¹ (inv_mem (hPW hg))
          (fun k hk => mul_mem (mul_mem (inv_mem hg) hk) (inv_mem (inv_mem hg))) k hk)
  have hYK : Y ≤ Subgroup.normalizer (K : Set (MulAut V)) := fun g hg =>
    normalizer_mem_of_conj
      (hKconj g (hYW hg) (fun k hk => (Subgroup.mem_normalizer_iff.mp (hYP hg) k).mp hk))
      (fun k hk => by
        simpa using hKconj g⁻¹ (inv_mem (hYW hg))
          (fun k hk => (Subgroup.mem_normalizer_iff.mp (hYP (inv_mem hg)) k).mp hk) k hk)
  have hPoddRes : ∀ (W : Subgroup V) (hPW : P ≤ stabW W),
      Odd (Nat.card (resRange W P hPW)) := fun W hPW =>
    Odd.of_dvd_nat hoddP (card_resRange_dvd W P hPW)
  by_cases hK : K < P
  ·
    have hKC : K ≤ Subgroup.centralizer (Y : Set (MulAut V)) := hmin K hK hYK
    have hWtop : fixV (omegaZ P p) ≠ ⊤ := fun h => by
      rw [h, inf_top_eq] at hinf
      exact ker_normK_ne_bot hV (omegaZ P p) hoddE hEne hinf
    have hWlt : Nat.card (fixV (omegaZ P p)) < n := hn ▸ card_lt_of_ne_top hWtop
    have hcent := ih _ hWlt ↥(fixV (omegaZ P p)) rfl (hV' _) _ (small16_res hY _ hYW) _
      (hPoddRes _ hPW) (resRange_le_normalizer hYW hPW hYP)
    have hd : ∀ x ∈ P, ∀ y ∈ Y, x⁻¹ * (y * x * y⁻¹) ∈ K := by
      intro x hx y hy
      refine ⟨mul_mem (inv_mem hx) ((Subgroup.mem_normalizer_iff.mp (hYP hy) x).mp hx),
        fun w hw => ?_⟩
      have h5 := apply_comm_of_resRange hYW hPW hcent (inv_mem hx) hy w hw
      have h6 : x⁻¹ * (y * x * y⁻¹) = x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ := by group
      rw [h6]
      exact h5
    exact hPne (le_centralizer_of_stable hY.1 hPK hKC hd)
  · have hKeq : K = P := by
      by_contra hne'
      exact hK (lt_of_le_of_ne hKP hne')
    have hPKle : P ≤ K := hKeq.ge
    by_cases hW0 : fixV (omegaZ P p) = ⊥
    · exact hB V hV Y hY P p hp hpodd hP hYP hPne hmin hab hW0
    ·
      have hV₁top : (normK (omegaZ P p)).ker ≠ ⊤ := fun h => hW0 (by
        rw [h, top_inf_eq] at hinf
        exact hinf)
      have hV₁lt : Nat.card (normK (omegaZ P p)).ker < n := hn ▸ card_lt_of_ne_top hV₁top
      have hcent := ih _ hV₁lt ↥(normK (omegaZ P p)).ker rfl (hV' _) _
        (small16_res hY _ hYV) _ (hPoddRes _ hPV) (resRange_le_normalizer hYV hPV hYP)
      have hall : ∀ x ∈ P, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ = 1 := by
        intro x hx y hy
        ext v
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top v)
        rw [map_mul]
        have h1 := apply_comm_of_resRange hYV hPV hcent hx hy a ha
        have hyb : y⁻¹ b ∈ fixV (omegaZ P p) :=
          (mem_stabW.mp (hYW hy) (y⁻¹ b)).mpr (by rw [MulAut.apply_inv_self]; exact hb)
        have h2 : (x * y * x⁻¹ * y⁻¹) b = b := by
          show x (y (x⁻¹ (y⁻¹ b))) = b
          rw [(hPKle (inv_mem hx)).2 _ hyb, MulAut.apply_inv_self]
          exact (hPKle hx).2 b hb
        rw [h1, h2]
        rfl
      refine hPne fun x hx y hy => ?_
      have := hall x hx y hy
      rw [mul_inv_eq_one] at this
      calc y * x = (x * y * x⁻¹) * x := by rw [this]
        _ = x * y := by group

theorem le_centralizer_of_small16 (hB : NoCaseB) {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)} (hY : Small16 Y)
    {X : Subgroup (MulAut V)} (hX : Odd (Nat.card X))
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    X ≤ Subgroup.centralizer (Y : Set (MulAut V)) :=
  le_centralizer_of_small16_aux hB _ V rfl hV Y hY X hX hYX

end Main

end CFSG.CGT.PushingUpLit.CGT6
