module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerConfig
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.FullnessCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Invol
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Steps
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section General

variable {G : Type*} [Group G]

theorem mem_or_inv_mul_mem_of_mem_sup_zpowers {A : Subgroup G} {t : G} (ht : t * t = 1)
    (hc : ∀ a ∈ A, a * t = t * a) {x : G} (hx : x ∈ A ⊔ zpowers t) : x ∈ A ∨ t⁻¹ * x ∈ A := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let M : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, x = a ∨ x = t * a}
      one_mem' := ⟨1, A.one_mem, Or.inl rfl⟩
      mul_mem' := by
        rintro x y ⟨a, ha, hx | hx⟩ ⟨b, hb, hy | hy⟩ <;> rw [hx, hy]
        · exact ⟨a * b, A.mul_mem ha hb, Or.inl rfl⟩
        · exact ⟨a * b, A.mul_mem ha hb, Or.inr (by rw [← mul_assoc, hc a ha, mul_assoc])⟩
        · exact ⟨a * b, A.mul_mem ha hb, Or.inr (by rw [mul_assoc])⟩
        · refine ⟨a * b, A.mul_mem ha hb, Or.inl ?_⟩
          calc t * a * (t * b) = t * (a * t) * b := by simp only [mul_assoc]
            _ = t * (t * a) * b := by rw [hc a ha]
            _ = (t * t) * a * b := by simp only [mul_assoc]
            _ = a * b := by rw [ht, one_mul]
      inv_mem' := by
        rintro x ⟨a, ha, hx | hx⟩ <;> rw [hx]
        · exact ⟨a⁻¹, A.inv_mem ha, Or.inl rfl⟩
        · refine ⟨a⁻¹, A.inv_mem ha, Or.inr ?_⟩
          have h1 : a⁻¹ * t = t * a⁻¹ := hc _ (A.inv_mem ha)
          rw [mul_inv_rev, hti, h1] }
  have hM : A ⊔ zpowers t ≤ M := by
    refine sup_le (fun a ha => ⟨a, ha, Or.inl rfl⟩)
      ((zpowers_le).2 ⟨1, A.one_mem, Or.inr (by simp)⟩)
  obtain ⟨a, ha, rfl | rfl⟩ := hM hx
  · exact Or.inl ha
  · exact Or.inr (by rw [hti, ← mul_assoc, ht, one_mul]; exact ha)

theorem card_le_two_mul_card_inf [Finite G] {D L : Subgroup G} {t : G}
    (h : ∀ x ∈ D, x ∈ L ∨ t⁻¹ * x ∈ L) : Nat.card D ≤ 2 * Nat.card ↥(D ⊓ L) := by
  by_cases hD : D ≤ L
  · have : D ⊓ L = D := inf_eq_left.2 hD
    rw [this]
    omega
  · obtain ⟨x₀, hx₀D, hx₀L⟩ := IsConcreteLE.not_le_iff_exists.1 hD
    have key : ∀ x ∈ D, x ∉ L → x₀⁻¹ * x ∈ D ⊓ L := by
      intro x hx hxL
      refine ⟨D.mul_mem (D.inv_mem hx₀D) hx, ?_⟩
      have h1 : t⁻¹ * x₀ ∈ L := (h x₀ hx₀D).resolve_left hx₀L
      have h2 : t⁻¹ * x ∈ L := (h x hx).resolve_left hxL
      have := L.mul_mem (L.inv_mem h1) h2
      simpa [mul_assoc] using this
    classical
    let f : D → ↥(D ⊓ L) × Bool := fun x =>
      if hx : (x : G) ∈ L then (⟨x, x.2, hx⟩, false) else (⟨x₀⁻¹ * x, key x x.2 hx⟩, true)
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : (x : G) ∈ L <;> by_cases hy : (y : G) ∈ L
      · simp only [f, hx, hy, dite_true, Prod.mk.injEq, and_true] at hxy
        exact Subtype.ext (Subtype.mk.inj hxy)
      · simp [f, hx, hy] at hxy
      · simp [f, hx, hy] at hxy
      · simp only [f, hx, hy, dite_false, Prod.mk.injEq, and_true] at hxy
        have := congrArg Subtype.val hxy
        exact Subtype.ext (mul_left_cancel this)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    omega

theorem card_centralizer_subtype (L : Subgroup G) {ℓ : G} (hℓ : ℓ ∈ L) :
    Nat.card (centralizer ({(⟨ℓ, hℓ⟩ : ↥L)} : Set ↥L)) =
      Nat.card ↥(L ⊓ centralizer ({ℓ} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, mem_centralizer_singleton_iff.2 (by
        have := mem_centralizer_singleton_iff.1 x.2
        exact (congrArg Subtype.val this))⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext (by
        exact mem_centralizer_singleton_iff.1 x.2.2))⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

end General

section Config

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem mul_self_eq_one_of_orderOf_eq_two_fullness {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [hx, pow_two] at this

theorem t_not_mem_of_isSporadic_hs (hL : IsSporadic ↥L .HS)
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) : t ∉ L := by
  intro h
  have hZ := center_eq_bot_of_isSporadic_hs hL
  have hc : (⟨t, h⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 htL g g.2)
  rw [hZ, mem_bot] at hc
  have h1 : t = 1 := congrArg Subtype.val hc
  rw [h1, orderOf_one] at ht2
  omega

theorem card_centralizer_t (hL : IsSporadic ↥L .HS) (htL : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) :
    Nat.card (centralizer ({t} : Set G)) = 88704000 := by
  have hL' := card_eq_of_isSporadic_hs hL
  have ht : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness ht2
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 htL a ha
  have htn := t_not_mem_of_isSporadic_hs hL htL ht2
  have hle := card_le_two_mul_card_inf (D := L ⊔ zpowers t) (L := L) (t := t)
    (fun x hx => mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc hx)
  rw [inf_eq_right.2 le_sup_left] at hle
  have hge := two_mul_card_le_of_exists (K := L) (C := L ⊔ zpowers t) le_sup_left
    ⟨t, mem_sup_right (mem_zpowers t), htn⟩
  rw [hin]
  omega

theorem card_centralizer_t_in_P_le (c : InnerD8Config L t) (htL : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) :
    Nat.card (centralizer ({(⟨t, c.t_mem_P⟩ : ↥c.P)} : Set ↥c.P)) ≤ 5760 := by
  have ht : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness ht2
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 htL a ha
  rw [card_centralizer_subtype c.P c.t_mem_P]
  have hle := card_le_two_mul_card_inf (D := c.P ⊓ centralizer ({t} : Set G)) (L := L) (t := t)
    (fun x hx => by
      have := hx.2
      rw [hin] at this
      exact mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc this)
  have hsub : c.P ⊓ centralizer ({t} : Set G) ⊓ L ≤ L ⊓ centralizer ({c.u} : Set G) :=
    fun x hx => ⟨hx.2, hx.1.1⟩
  have h2 := Subgroup.card_le_of_le hsub
  rw [c.card_centralizer_u] at h2
  omega

theorem center_L₁_eq_bot (c : InnerD8Config L t) : center ↥c.L₁ = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have h1 : c.eL₁ a ∈ center (alternatingGroup (Fin 6)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := c.eL₁.surjective y
    rw [← map_mul, ← map_mul, mem_center_iff.1 ha k]
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h1
  have : a = 1 := c.eL₁.injective (h1.trans (map_one c.eL₁).symm)
  rw [this]
  exact one_mem _

theorem card_L₁ (c : InnerD8Config L t) : Nat.card ↥c.L₁ = 360 := by
  rw [Nat.card_congr c.eL₁.toEquiv, nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem dvd_card_P (c : InnerD8Config L t) : 129600 ∣ Nat.card ↥c.P := by
  have hK₂P : conjSub t c.L₁ ≤ c.P := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_mem (mul_mem c.t_mem_P (c.pair.K_le hb)) (inv_mem c.t_mem_P)
  have comm : ∀ (m : ↥c.L₁) (n : ↥(conjSub t c.L₁)),
      Commute (c.L₁.subtype m) ((conjSub t c.L₁).subtype n) := by
    rintro m ⟨_, b, hb, rfl⟩
    exact c.pair.comm m m.2 b hb
  let φ := MonoidHom.noncommCoprod c.L₁.subtype (conjSub t c.L₁).subtype comm
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    have h1 : (a : G) * b = 1 := h
    have hab : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hz : a ∈ center ↥c.L₁ := by
      rw [mem_center_iff]
      intro k
      refine Subtype.ext ?_
      show (k : G) * a = a * k
      rw [hab]
      exact (comm k b).inv_right.eq
    rw [center_L₁_eq_bot c, mem_bot] at hz
    have ha1 : (a : G) = 1 := by rw [hz]; rfl
    have hb1 : (b : G) = 1 := by
      rw [ha1] at hab
      exact (inv_eq_one.1 hab.symm)
    refine Prod.ext hz ?_
    exact Subtype.ext hb1
  have hcard : Nat.card (↥c.L₁ × ↥(conjSub t c.L₁)) = 129600 := by
    rw [Nat.card_prod, card_L₁ c, Subgroup.card_map_of_injective (MulAut.conj t).injective,
      card_L₁ c]
  have hle : φ.range ≤ c.P := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact mul_mem (c.pair.K_le a.2) (hK₂P b.2)
  have := Subgroup.card_dvd_of_le hle
  rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hcard] at this

theorem not_isConj_t_u (c : InnerD8Config L t) (hL : IsSporadic ↥L .HS)
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) : ¬ IsConj t c.u := by
  intro h
  have h1 := card_centralizer_eq_of_isConj h
  rw [card_centralizer_t hL htL ht2 hin] at h1
  have h2 := dvd_card_P c
  have h3 : Nat.card ↥c.P = 88704000 := h1.symm
  rw [h3] at h2
  omega

theorem card_inf_centralizer_of_involution (hL : IsSporadic ↥L .HS) {ℓ : G} (hℓ : ℓ ∈ L)
    (h2 : orderOf ℓ = 2) :
    Nat.card ↥(L ⊓ centralizer ({ℓ} : Set G)) = 7680 ∨
      Nat.card ↥(L ⊓ centralizer ({ℓ} : Set G)) = 2880 := by
  have := card_centralizer_of_involution_hs hL ⟨ℓ, hℓ⟩
    ((Subgroup.orderOf_coe (⟨ℓ, hℓ⟩ : ↥L)).symm.trans h2)
  rwa [card_centralizer_subtype L hℓ] at this

theorem exists_conj_in_L (hL : IsSporadic ↥L .HS) {ℓ ℓ' : G} (hℓ : ℓ ∈ L) (hℓ' : ℓ' ∈ L)
    (h2 : orderOf ℓ = 2) (h2' : orderOf ℓ' = 2)
    (hc : Nat.card ↥(L ⊓ centralizer ({ℓ} : Set G)) = Nat.card ↥(L ⊓ centralizer ({ℓ'} : Set G))) :
    ∃ g ∈ L, g * ℓ * g⁻¹ = ℓ' := by
  have := isConj_of_card_centralizer_eq_hs hL ⟨ℓ, hℓ⟩ ⟨ℓ', hℓ'⟩
    ((Subgroup.orderOf_coe (⟨ℓ, hℓ⟩ : ↥L)).symm.trans h2)
    ((Subgroup.orderOf_coe (⟨ℓ', hℓ'⟩ : ↥L)).symm.trans h2')
    (by rw [card_centralizer_subtype L hℓ, card_centralizer_subtype L hℓ']; exact hc)
  obtain ⟨g, hg⟩ := isConj_iff.1 this
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

theorem card_inf_centralizer_z (hL : IsSporadic ↥L .HS) (htL : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hin : centralizer ({t} : Set G) = L ⊔ zpowers t)
    {S : Subgroup G} {z n : G} (hf : HSFusionData L t S z n) :
    Nat.card ↥(L ⊓ centralizer ({z} : Set G)) = 7680 := by
  rcases card_inf_centralizer_of_involution hL hf.zL hf.z2 with h | h
  · exact h
  exfalso
  have ht : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness ht2
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 htL a ha
  have hCt := card_centralizer_t hL htL ht2 hin
  have hrel := Subgroup.relIndex_mul_card (H := S) (K := centralizer ({t} : Set G))
  rw [inf_eq_left.2 hf.le, hCt] at hrel
  have hcop : Nat.Coprime (2 ^ 10) (S.relIndex (centralizer ({t} : Set G))) :=
    Nat.Coprime.pow_left 10 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hf.index)
  have hdvd : 2 ^ 10 ∣ Nat.card S := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [hrel]
    norm_num
  have hS : 1024 ≤ Nat.card S := by
    have := Nat.le_of_dvd Nat.card_pos hdvd
    norm_num at this
    exact this
  have hSL := card_le_two_mul_card_inf (D := S) (L := L) (t := t) (fun x hx => by
    have := hf.le hx
    rw [hin] at this
    exact mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc this)
  have hsub : S ⊓ L ≤ L ⊓ centralizer ({z} : Set G) := by
    intro x hx
    have hzx : z ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L := by
      rw [hf.zc]; exact mem_zpowers z
    refine ⟨hx.2, mem_centralizer_singleton_iff.2 ?_⟩
    exact mem_centralizer_iff.1 hzx.1 x hx
  have hdvd2 : Nat.card ↥(S ⊓ L) ∣ 2880 := h ▸ Subgroup.card_dvd_of_le hsub
  obtain ⟨m, hm⟩ := (hf.pgroup.to_inf_left (K := L)).exists_card_eq
  have h9 : 9 ≤ m := by
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 2 ^ 9 ∣ 2880 := (Nat.pow_dvd_pow 2 h9).trans (hm ▸ hdvd2)
  omega

theorem isConj_t_mul (c : InnerD8Config L t) (hL : IsSporadic ↥L .HS)
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) : ∀ ℓ ∈ L, ℓ * ℓ = 1 → IsConj t (t * ℓ) := by
  intro ℓ hℓ hℓ2
  by_cases h1 : ℓ = 1
  · subst h1
    rw [mul_one]
  have hord : orderOf ℓ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rwa [pow_two]) h1
  have hct : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 htL l hl
  have key : ∀ m ∈ L, ∀ ℓ' : G, m * ℓ * m⁻¹ = ℓ' → IsConj (t * ℓ) (t * ℓ') := by
    intro m hm ℓ' h
    refine isConj_iff.2 ⟨m, ?_⟩
    rw [← h]
    calc m * (t * ℓ) * m⁻¹ = (m * t) * ℓ * m⁻¹ := by simp only [mul_assoc]
      _ = t * m * ℓ * m⁻¹ := by rw [hct m hm]
      _ = t * (m * ℓ * m⁻¹) := by simp only [mul_assoc]
  rcases card_inf_centralizer_of_involution hL hℓ hord with h | h
  · obtain ⟨g, hg, hgz⟩ := exists_conj_in_L hL hℓ hf.zL hord hf.z2
      (h.trans (card_inf_centralizer_z hL htL ht2 hin hf).symm)
    have hzt : IsConj t (t * z) := isConj_iff.2 ⟨n, by rw [hf.nt]; exact hct z hf.zL⟩
    exact hzt.trans (key g hg z hgz).symm
  · obtain ⟨g, hg, hgu⟩ := exists_conj_in_L hL hℓ c.u_mem hord c.u_ord
      (h.trans c.card_centralizer_u.symm)
    exact c.t_conj_tu.trans (key g hg c.u hgu).symm

theorem ncard_conjCommSet_u_t_le (c : InnerD8Config L t) (hL : IsSporadic ↥L .HS)
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) : (conjCommSet c.u t).ncard ≤ 21175 := by
  have ht : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 htL a ha
  have hsub : conjCommSet c.u t ⊆ {g : G | g ∈ L ∧ orderOf g = 2} := by
    rintro g ⟨hug, hgt⟩
    have hord : orderOf g = 2 := (orderOf_eq_of_isConj' hug).symm.trans c.u_ord
    have hg2 : g * g = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness hord
    have hgC : g ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hgt.eq
    rw [hin] at hgC
    rcases mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc hgC with hgL | hgL
    · exact ⟨hgL, hord⟩
    · exfalso
      have hgt' : g * t = t * g := hgt
      have hℓ2 : (t⁻¹ * g) * (t⁻¹ * g) = 1 := by
        rw [hti]
        calc t * g * (t * g) = t * (g * t) * g := by simp only [mul_assoc]
          _ = t * (t * g) * g := by rw [hgt']
          _ = (t * t) * (g * g) := by simp only [mul_assoc]
          _ = 1 := by rw [ht, hg2, one_mul]
      have h1 := isConj_t_mul c hL htL ht2 hin hf _ hgL hℓ2
      rw [hti, ← mul_assoc, ht, one_mul] at h1
      exact not_isConj_t_u c hL htL ht2 hin (h1.trans hug.symm)
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
    (ncard_involutions_hs_le_of_le L hL).le

theorem ncard_conj_in_P_mul_lt (c : InnerD8Config L t) (hL : IsSporadic ↥L .HS)
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) :
    {g : G | IsConj t g ∧ g ∈ c.P}.ncard * 3840 < Nat.card ↥c.P := by
  have hset : {g : G | IsConj t g ∧ g ∈ c.P} = conjCommSet t c.u := by
    ext g
    refine and_congr_right fun _ => ?_
    change g ∈ centralizer ({c.u} : Set G) ↔ g * c.u = c.u * g
    exact mem_centralizer_singleton_iff
  have h := ncard_conjCommSet_mul_card_centralizer t c.u
  rw [card_centralizer_t hL htL ht2 hin] at h
  have h2 := ncard_conjCommSet_u_t_le c hL htL ht2 hin hf
  have hP : 0 < Nat.card ↥c.P := Nat.card_pos
  have h3 : (conjCommSet c.u t).ncard * Nat.card ↥c.P ≤ 21175 * Nat.card ↥c.P :=
    Nat.mul_le_mul_right _ h2
  have h4 : (conjCommSet t c.u).ncard * 88704000 ≤ 21175 * Nat.card ↥c.P := by
    rw [h]; exact h3
  rw [hset]
  omega

theorem exists_involution_rho (c : InnerD8Config L t) (htL : t ∈ centralizer (L : Set G))
    {a : MulAut (alternatingGroup (Fin 6))} (ha : a * a = 1) (ha1 : a ≠ 1) :
    ∃ x : G, x ∈ L ∧ ∃ hxP : x ∈ c.P, x * x = 1 ∧
      (c.rho ⟨x, hxP⟩ = base a a ∨ c.rho ⟨x, hxP⟩ = base a a * tau) := by
  set e := MulAut.congr c.eL₁ with he
  have ha' : e.symm a * e.symm a = 1 := by rw [← map_mul, ha, map_one]
  have ha1' : e.symm a ≠ 1 := fun h => ha1 (by simpa using congrArg e h)
  obtain ⟨x, hxL, hxC, hxx, hcase⟩ := c.diag (e.symm a) ha' ha1'
  have hxt : x * t = t * x := mem_centralizer_iff.1 htL x hxL
  have hxP : x ∈ c.P := hxC
  refine ⟨x, hxL, hxP, hxx, ?_⟩
  have hrho : ∀ w : ↥c.P, c.rho w = mapEquiv e (c.pair.rho w) := c.rho_apply
  rcases hcase with ⟨hn, hconj⟩ | ⟨hn, hconj⟩
  · left
    rw [hrho, c.pair.rho_of_commute_t_of_normalizes ⟨x, hxP⟩ hn hxt]
    show mapEquiv e (base (conjAutOf c.L₁ hn) (conjAutOf c.L₁ hn)) = _
    rw [hconj, mapEquiv_base, MulEquiv.apply_symm_apply]
  · right
    have hxn : x ∉ normalizer (c.L₁ : Set G) := by
      intro hxn
      have htn : t ∈ normalizer (c.L₁ : Set G) := by
        have := mul_mem (inv_mem hxn) hn
        simpa using this
      exact c.pair.ne ((mem_normalizer_iff_map_eq c.L₁ t).1 htn)
    have hsw := c.pair.map_conj_eq_of_not_mem_normalizer hxP hxn
    obtain ⟨a₀, hρ, hk⟩ := c.pair.rho_of_commute_t_of_swaps ⟨x, hxP⟩ hsw hxt
    have ha₀ : a₀ = e.symm a := by
      refine MulEquiv.ext fun k => Subtype.ext ?_
      rw [hk, ← hconj, conjAutOf_apply]
    rw [hrho, hρ, ha₀, map_mul, mapEquiv_base, mapEquiv_tau, MulEquiv.apply_symm_apply]

theorem base_diag_mem_range (c : InnerD8Config L t) (htL : t ∈ centralizer (L : Set G))
    (hgen : closure {a : MulAut (alternatingGroup (Fin 6)) | a * a = 1} = ⊤)
    (d : MulAut (alternatingGroup (Fin 6))) : base d d ∈ c.rho.range := by
  let T : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    c.rho.range.comap
      ((SemidirectProduct.inl : (MulAut (alternatingGroup (Fin 6)) ×
        MulAut (alternatingGroup (Fin 6))) →* Wr2 (MulAut (alternatingGroup (Fin 6)))).comp
        ((MonoidHom.id _).prod (MonoidHom.id _)))
  have htR : (tau : Wr2 (MulAut (alternatingGroup (Fin 6)))) ∈ c.rho.range :=
    ⟨⟨t, c.t_mem_P⟩, c.rho_t⟩
  have hinvol : ∀ a : MulAut (alternatingGroup (Fin 6)), a * a = 1 → a ∈ T := by
    intro a ha
    by_cases ha1 : a = 1
    · subst ha1
      exact T.one_mem
    obtain ⟨x, -, hxP, -, h | h⟩ := exists_involution_rho c htL ha ha1
    · exact ⟨_, h⟩
    · have : base a a = c.rho ⟨x, hxP⟩ * tau := by
        rw [h, mul_assoc, tau_mul_tau, mul_one]
      show base a a ∈ c.rho.range
      rw [this]
      exact c.rho.range.mul_mem ⟨_, rfl⟩ htR
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le T).mpr hinvol
  have : d ∈ T := hT ▸ Subgroup.mem_top d
  exact this

theorem InnerD8Config.rho_range_eq_top (c : InnerD8Config L t) (hL : IsSporadic ↥L .HS)
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n)
    (hCA : ∀ a : MulAut (alternatingGroup (Fin 6)), a * a = 1 → a ≠ 1 →
      Nat.card (centralizer ({a} : Set (MulAut (alternatingGroup (Fin 6))))) ≤ 48)
    (hgen : closure {a : MulAut (alternatingGroup (Fin 6)) | a * a = 1} = ⊤) :
    c.rho.range = ⊤ := by
  refine range_eq_top_of_conj_count c.t_mem_P c.rho c.rho_t (le_of_eq c.card_ker_rho)
    CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6 hCA hgen
    (base_diag_mem_range c htL hgen) (card_centralizer_t_in_P_le c htL ht2 hin) ?_
    (ncard_conj_in_P_mul_lt c hL htL ht2 hin hf)
  intro a ha ha1
  obtain ⟨x, hxL, hxP, hxx, h⟩ := exists_involution_rho c htL ha ha1
  exact ⟨⟨x, hxP⟩, isConj_t_mul c hL htL ht2 hin hf x hxL hxx, h⟩

theorem InnerD8Config.rho_surjective (c : InnerD8Config L t) (hL : IsSporadic ↥L .HS)
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) : c.rho.range = ⊤ :=
  c.rho_range_eq_top hL htL ht2 hin hf card_centralizer_le_of_involution
    closure_involutions_eq_top

end Config

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
