module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.GH74.GLS.TwoThin.Rank
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpRigid

open Subgroup CFSG CFSG.LocalCores CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open scoped commutatorElement

section Bar

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem exists_noncomm_of_isComponent {L : Subgroup Q} (hL : IsComponent L) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hL.1
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a'.1, a'.2, b'.1, b'.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext h

theorem eq_of_diag_le_sup {L L' C₁ C₂ D : Subgroup Q} (hL : IsComponent L) (hC₁ : IsComponent C₁)
    (hC₂ : IsComponent C₂) (hLL' : ⁅L, L'⁆ = ⊥) (hD : D ≤ C₁ ⊔ C₂)
    (hproj : ∀ b ∈ L, ∃ b' ∈ L', b * b' ∈ D) : L = C₁ ∨ L = C₂ := by
  by_contra h
  rw [not_or] at h
  have h1 : C₁ ≤ centralizer (L : Set Q) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact (distinct_components_commute hL hC₁).resolve_left h.1
  have h2 : C₂ ≤ centralizer (L : Set Q) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact (distinct_components_commute hL hC₂).resolve_left h.2
  have h3 : D ≤ centralizer (L : Set Q) := hD.trans (sup_le h1 h2)
  have h4 : L' ≤ centralizer (L : Set Q) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hLL'
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_isComponent hL
  obtain ⟨b', hb', hbb'⟩ := hproj b hb
  have e1 := Subgroup.mem_centralizer_iff.mp (h3 hbb') a ha
  have e2 := Subgroup.mem_centralizer_iff.mp (h4 hb') a ha
  apply hab
  have : a * b * b' = b * a * b' := by
    calc a * b * b' = a * (b * b') := by group
      _ = (b * b') * a := e1
      _ = b * (b' * a) := by group
      _ = b * (a * b') := by rw [e2]
      _ = b * a * b' := by group
  exact mul_right_cancel this

omit [Finite Q] in
theorem commute_of_swapDiag {L : Subgroup Q} {t : Q} (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥)
    (hinj : Function.Injective (swapDiag hAB)) {r : Q} (hrt : r * t = t * r)
    (hrL : ∀ b ∈ L, r * b * r⁻¹ ∈ L)
    (hrD : ∀ b : L, r * swapDiag hAB b * r⁻¹ = swapDiag hAB b) {b : Q} (hb : b ∈ L) :
    r * b * r⁻¹ = b := by
  have h1 : t⁻¹ * r = r * t⁻¹ := by
    calc t⁻¹ * r = t⁻¹ * (r * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * r) * t⁻¹ := by rw [hrt]
      _ = r * t⁻¹ := by group
  have h2 : r⁻¹ * t = t * r⁻¹ := by
    calc r⁻¹ * t = r⁻¹ * (t * r) * r⁻¹ := by group
      _ = r⁻¹ * (r * t) * r⁻¹ := by rw [hrt]
      _ = t * r⁻¹ := by group
  have key : swapDiag hAB ⟨r * b * r⁻¹, hrL b hb⟩ = swapDiag hAB ⟨b, hb⟩ := by
    rw [← hrD ⟨b, hb⟩, swapDiag_apply, swapDiag_apply]
    have e : t⁻¹ * (r * b * r⁻¹) * t = r * (t⁻¹ * b * t) * r⁻¹ := by
      calc t⁻¹ * (r * b * r⁻¹) * t = (t⁻¹ * r) * b * (r⁻¹ * t) := by group
        _ = (r * t⁻¹) * b * (t * r⁻¹) := by rw [h1, h2]
        _ = r * (t⁻¹ * b * t) * r⁻¹ := by group
    change r * b * r⁻¹ * (t⁻¹ * (r * b * r⁻¹) * t) = r * (b * (t⁻¹ * b * t)) * r⁻¹
    rw [e]
    group
  exact congrArg Subtype.val (hinj key)

omit [Finite Q] in
theorem inf_conj_eq_bot_of_injective {L : Subgroup Q} {s : Q} (hs : orderOf s = 2)
    (hZ : IsPGroup 2 ↥(center ↥L)) (hAB : ⁅L, conjSub s⁻¹ L⁆ = ⊥)
    (hinj : Function.Injective (swapDiag hAB)) : L ⊓ conjSub s⁻¹ L = ⊥ := by
  have hss : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs, sq] at this
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hmem : ∀ c : Q, c ∈ L ⊓ conjSub s⁻¹ L ↔ c ∈ L ∧ s * c * s ∈ L := by
    intro c
    rw [Subgroup.mem_inf, TwoThin.mem_conjSub_iff', inv_inv, hsinv]
  have hcomm : ∀ c ∈ L ⊓ conjSub s⁻¹ L, ∀ l ∈ L, l * c = c * l := by
    intro c hc l hl
    have h1 : L ≤ centralizer ((conjSub s⁻¹ L : Subgroup Q) : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB
    exact (Subgroup.mem_centralizer_iff.mp (h1 hl) c (Subgroup.mem_inf.mp hc).2).symm
  by_contra hne
  obtain ⟨c, hc, hc1⟩ := (Subgroup.bot_or_exists_ne_one (L ⊓ conjSub s⁻¹ L)).resolve_left hne
  have hcL : (c : Q) ∈ L := (Subgroup.mem_inf.mp hc).1
  have hcen : ∀ g : ↥L, g * (⟨c, hcL⟩ : ↥L) = ⟨c, hcL⟩ * g := fun g =>
    Subtype.ext (hcomm c hc g g.2)
  obtain ⟨n, hn⟩ := hZ ⟨⟨c, hcL⟩, Subgroup.mem_center_iff.mpr hcen⟩
  have hcn : c ^ (2 ^ n) = 1 := by
    have := congrArg (fun z : center ↥L => (((z : ↥L)) : Q)) hn
    simpa using this
  obtain ⟨m, -, hordc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hcn)
  have hn1 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hordc
    exact hc1 hordc
  set v : Q := c ^ (orderOf c / 2) with hv
  have hv2 : orderOf v = 2 := by
    rw [hv]
    exact orderOf_pow_orderOf_div (by rw [hordc]; positivity) (by rw [hordc]; exact dvd_pow_self 2 hn1)
  have hvI : v ∈ L ⊓ conjSub s⁻¹ L := Subgroup.pow_mem _ hc _
  have hvL : v ∈ L := (Subgroup.mem_inf.mp hvI).1
  have hvv : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv2, sq] at this
  obtain ⟨hv1, hv2'⟩ := (hmem v).mp hvI
  set w : Q := s * v * s with hw
  have hwI : w ∈ L ⊓ conjSub s⁻¹ L := by
    refine (hmem w).mpr ⟨hv2', ?_⟩
    have : s * w * s = v := by
      calc s * w * s = (s * s) * v * (s * s) := by rw [hw]; group
        _ = v := by rw [hss]; group
    rw [this]; exact hv1
  have hwL : w ∈ L := (Subgroup.mem_inf.mp hwI).1
  have hvw : v * w = w * v := (hcomm v hvI w hwL).symm
  obtain ⟨z, hzL, hz1, hzz, hzs⟩ : ∃ z : Q, z ∈ L ∧ z ≠ 1 ∧ z * z = 1 ∧ s * z * s = z := by
    by_cases hwv : w = v
    · refine ⟨v, hvL, ?_, hvv, ?_⟩
      · intro h
        rw [h, orderOf_one] at hv2
        omega
      · exact hwv
    · refine ⟨v * w, mul_mem hvL hwL, ?_, ?_, ?_⟩
      · intro h
        apply hwv
        have : w = v⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this, inv_eq_of_mul_eq_one_left hvv]
      · calc v * w * (v * w) = v * (w * v) * w := by group
          _ = v * (v * w) * w := by rw [hvw]
          _ = (v * v) * (w * w) := by group
          _ = 1 := by
            have hww : w * w = 1 := by
              calc w * w = s * v * (s * s) * v * s := by rw [hw]; group
                _ = s * (v * v) * s := by rw [hss]; group
                _ = 1 := by rw [hvv, mul_one, hss]
            rw [hvv, hww]; group
      · calc s * (v * w) * s = (s * v * s) * (s * w * s) := by
              calc s * (v * w) * s = s * v * (s * s) * w * s := by rw [hss]; group
                _ = (s * v * s) * (s * w * s) := by group
          _ = w * v := by
            have : s * w * s = v := by
              calc s * w * s = (s * s) * v * (s * s) := by rw [hw]; group
                _ = v := by rw [hss]; group
            rw [this]
          _ = v * w := hvw.symm
  have hδ : swapDiag hAB ⟨z, hzL⟩ = swapDiag hAB 1 := by
    rw [swapDiag_apply, map_one]
    change z * (s⁻¹ * z * s) = 1
    rw [hsinv, hzs]
    exact hzz
  exact hz1 (congrArg Subtype.val (hinj hδ))

end Bar

section Lift

open CFSG.GH74.GLS.TwoThin

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem card_comap_barMk (T : Subgroup (barQ Y)) :
    Nat.card ↥(T.comap (barMk Y)) = Nat.card ↥T * Nat.card ↥(barMk Y).ker := by
  let P := T.comap (barMk Y)
  let f : ↥P →* ↥T := ((barMk Y).comp P.subtype).codRestrict T fun p => p.2
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨y, hy⟩ := barMk_surjective (Y := Y) (h : barQ Y)
    exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact h.2⟩, Subtype.ext hy⟩
  have hkerle : (barMk Y).ker ≤ P := fun y hy => by
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker).mp hy]
    exact one_mem T
  have hker : f.ker = (barMk Y).ker.subgroupOf P := by
    ext p
    simp only [f, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  calc Nat.card ↥P = Nat.card (↥P ⧸ f.ker) * Nat.card f.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = Nat.card ↥T * Nat.card ↥(barMk Y).ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hker,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv]

theorem factorization_card_comap_barMk (T : Subgroup (barQ Y)) :
    (Nat.card ↥(T.comap (barMk Y))).factorization 2 = (Nat.card ↥T).factorization 2 := by
  have : ¬ 2 ∣ Nat.card ↥(barMk Y).ker := by
    have := odd_card_ker_barMk (Y := Y)
    exact fun h => (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
  rw [card_comap_barMk, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd this, add_zero]

theorem pRank_comap_barMk (T : Subgroup (barQ Y)) :
    pRank 2 ↥(T.comap (barMk Y)) = pRank 2 ↥T := by
  let P := T.comap (barMk Y)
  let f : ↥P →* ↥T := ((barMk Y).comp P.subtype).codRestrict T fun p => p.2
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨y, hy⟩ := barMk_surjective (Y := Y) (h : barQ Y)
    exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact h.2⟩, Subtype.ext hy⟩
  have hodd : ¬ 2 ∣ Nat.card ↥f.ker := by
    have h1 : f.ker = ((barMk Y).domRestrict P).ker := MonoidHom.ker_codRestrict _ _ _
    have h2 := OddKernel.odd_card_restriction_kernel (barMk Y) odd_card_ker_barMk P
    rw [h1]
    exact fun h => (Nat.not_even_iff_odd.mpr h2) (even_iff_two_dvd.mpr h)
  have e1 := GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two f.ker hodd
  have e2 : pRank 2 (↥P ⧸ f.ker) = pRank 2 ↥T := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  rw [← e1, e2]

end Lift

section Prod

variable {Z : Type} [Group Z] [Finite Z]

omit [Finite Z] in
theorem exists_injective_prod {A B : Subgroup Z} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hi : A ⊓ B = ⊥) : ∃ f : ↥A × ↥B →* Z, Function.Injective f ∧ f.range ≤ A ⊔ B := by
  have hc : ∀ (m : ↥A) (n : ↥B), Commute (A.subtype m) (B.subtype n) := by
    intro m n
    exact hcomm m m.2 n n.2
  refine ⟨MonoidHom.noncommCoprod A.subtype B.subtype hc, ?_, ?_⟩
  · intro p q hpq
    simp only [MonoidHom.noncommCoprod_apply, Subgroup.coe_subtype] at hpq
    have h1 : ((p.1 : Z)⁻¹ * q.1) = ((p.2 : Z) * (q.2 : Z)⁻¹) := by
      have e1 := hcomm (p.1 : Z)⁻¹ (inv_mem p.1.2) (q.2 : Z) q.2.2
      calc (p.1 : Z)⁻¹ * q.1 = (p.1 : Z)⁻¹ * (q.1 * q.2) * (q.2 : Z)⁻¹ := by group
        _ = (p.1 : Z)⁻¹ * (p.1 * p.2) * (q.2 : Z)⁻¹ := by rw [hpq]
        _ = (p.2 : Z) * (q.2 : Z)⁻¹ := by group
    have hA : ((p.1 : Z)⁻¹ * q.1) ∈ A := mul_mem (inv_mem p.1.2) q.1.2
    have hB : ((p.1 : Z)⁻¹ * q.1) ∈ B := by rw [h1]; exact mul_mem p.2.2 (inv_mem q.2.2)
    have hbot : ((p.1 : Z)⁻¹ * q.1) ∈ (A ⊓ B : Subgroup Z) := ⟨hA, hB⟩
    rw [hi, Subgroup.mem_bot] at hbot
    have hp1 : (p.1 : Z) = q.1 := inv_mul_eq_one.mp hbot
    have hp2 : (p.2 : Z) = q.2 := by
      have h2 : (p.2 : Z) * (q.2 : Z)⁻¹ = 1 := by rw [← h1]; exact hbot
      exact mul_inv_eq_one.mp h2
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)
  · rintro _ ⟨p, rfl⟩
    simp only [MonoidHom.noncommCoprod_apply, Subgroup.coe_subtype]
    exact mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)

theorem pRank_add_le_of_commute {A B H : Subgroup Z} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hi : A ⊓ B = ⊥) (hH : A ⊔ B ≤ H) :
    CFSG.Open.pRank 2 A + CFSG.Open.pRank 2 B ≤ CFSG.Open.pRank 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₁, hE₁A, hE₁, hc₁⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two A
  obtain ⟨E₂, hE₂B, hE₂, hc₂⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two B
  obtain ⟨f, hf, hfr⟩ := exists_injective_prod (A := E₁) (B := E₂)
    (fun a ha b hb => hcomm a (hE₁A ha) b (hE₂B hb))
    (eq_bot_iff.mpr (fun z hz => by
      have : z ∈ (A ⊓ B : Subgroup Z) := ⟨hE₁A hz.1, hE₂B hz.2⟩
      rw [hi] at this
      exact this))
  refine CFSG.SectionRank.le_pRank_of_injective Nat.one_lt_two (A := ↥E₁ × ↥E₂) ?_ ?_ ?_ f hf
    (hfr.trans ((sup_le_sup hE₁A hE₂B).trans hH))
  · intro a b
    have h1 := hE₁.1.is_comm.comm
    have h2 := hE₂.1.is_comm.comm
    exact Prod.ext (h1 a.1 b.1) (h2 a.2 b.2)
  · intro a
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hE₁.2 a.1 a.1.2
    · exact hE₂.2 a.2 a.2.2
  · rw [Nat.card_prod, hc₁, hc₂, pow_add]

theorem factorization_add_le_of_commute {A B H : Subgroup Z}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) (hH : A ⊔ B ≤ H) :
    (Nat.card ↥A).factorization 2 + (Nat.card ↥B).factorization 2 ≤
      (Nat.card ↥H).factorization 2 := by
  obtain ⟨f, hf, hfr⟩ := exists_injective_prod hcomm hi
  have hdvd : Nat.card (↥A × ↥B) ∣ Nat.card ↥H := by
    have h1 : Nat.card (↥A × ↥B) = Nat.card ↥f.range :=
      Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    rw [h1]
    exact Subgroup.card_dvd_of_le (hfr.trans hH)
  rw [Nat.card_prod] at hdvd
  have := (Nat.factorization_le_iff_dvd (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
    Nat.card_pos.ne').mpr hdvd 2
  rwa [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at this

end Prod

section Lift2

open CFSG.GH74.GLS.TwoThin

variable {Y : Type} [Group Y] [Finite Y]

theorem pRank_le_of_le_comap {X : Subgroup Y} {T : Subgroup (barQ Y)}
    (h : T.comap (barMk Y) ≤ X) : pRank 2 ↥T ≤ pRank 2 ↥X := by
  rw [← pRank_comap_barMk T, pRank_two_subgroup_eq_open, pRank_two_subgroup_eq_open]
  exact CFSG.SectionRank.pRank_mono Nat.one_lt_two h

theorem factorization_le_of_le_comap {X : Subgroup Y} {T : Subgroup (barQ Y)}
    (h : T.comap (barMk Y) ≤ X) :
    (Nat.card ↥T).factorization 2 ≤ (Nat.card ↥X).factorization 2 := by
  rw [← factorization_card_comap_barMk T]
  have hd := Subgroup.card_dvd_of_le h
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hd 2

end Lift2

section Misc

theorem isPGroup_two_center_hat (X : Type) [Group X] [Finite X] :
    IsPGroup 2 ↥(center (X ⧸ pPrimeCore 2 X)) :=
  TBLit.center_isPGroup_two_of_pPrimeCore_eq_bot (pPrimeCore_quotient_eq_bot X)

theorem two_le_pRank_of_isSimple {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hn : ∃ a b : S, a * b ≠ b * a) : 2 ≤ pRank 2 S :=
  have := hs
  two_le_pRank_of_isQuasisimple_of_odd_center (isQuasisimple_of_isSimpleGroup hn) (by
    rw [center_eq_bot_of_isSimpleGroup hn, Subgroup.card_bot]
    exact odd_one)

theorem four_dvd_card_of_isQuasisimple {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L) :
    4 ∣ Nat.card L := by
  obtain ⟨-, hs, a, b, hab⟩ := hL
  have h2 := two_le_pRank_of_isSimple hs ⟨a, b, hab⟩
  obtain ⟨E, -, hE⟩ := exists_four_group_of_two_le_pRank h2
  have h4 : 4 ∣ Nat.card (L ⧸ center L) := by
    rw [← hE]
    exact Subgroup.card_subgroup_dvd_card E
  exact h4.trans (Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)).symm)

theorem one_le_pRank_of_involution {Z : Type} [Group Z] [Finite Z] {X : Subgroup Z} {x : Z}
    (hx : x ∈ X) (ho : orderOf x = 2) : 1 ≤ CFSG.Open.pRank 2 X := by
  have hx2 : x ^ 2 = 1 := (orderOf_eq_prime_iff.mp ho).1
  have helem : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self x i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  exact CFSG.SectionRank.le_pRank Nat.one_lt_two (Subgroup.zpowers_le.mpr hx) helem
    (by rw [Nat.card_zpowers, ho]; rfl)

theorem one_le_pRank_of_two_dvd {Z : Type} [Group Z] [Finite Z] {X : Subgroup Z}
    (h : 2 ∣ Nat.card ↥X) : 1 ≤ CFSG.Open.pRank 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 h
  exact one_le_pRank_of_involution x.2 (by rw [Subgroup.orderOf_coe]; exact hx)

end Misc

end CFSG.GH74.GLS.C3.Layer1.PumpRigid
