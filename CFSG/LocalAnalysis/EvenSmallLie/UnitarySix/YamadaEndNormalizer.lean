module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndCentralizer
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndDefs
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools
open scoped Pointwise MatrixGroups

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem map_center_eq (e : X ≃* Y) : (center X).map e.toMonoidHom = center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (MulEquivClass.apply_mem_center_iff e).2 hx
  · intro hy
    refine ⟨e.symm y, (MulEquivClass.apply_mem_center_iff e).1 ?_, e.apply_symm_apply y⟩
    rw [e.apply_symm_apply]
    exact hy

noncomputable def quotientCenterEquiv (e : X ≃* Y) : X ⧸ center X ≃* Y ⧸ center Y :=
  QuotientGroup.congr (center X) (center Y) e (map_center_eq e)

theorem isQuasisimple_of_mulEquiv (e : X ≃* Y) (h : CFSG.Open.IsQuasisimple X) :
    CFSG.Open.IsQuasisimple Y :=
  h.of_mulEquiv e.symm

end Transport

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_centerSub (R : Subgroup G) :
    normalizer (R : Set G) ≤ normalizer (centerSub R : Set G) := by
  intro x hx
  have hxi : x⁻¹ ∈ normalizer (R : Set G) := inv_mem hx
  have hR : ∀ r, r ∈ R ↔ x * r * x⁻¹ ∈ R := mem_normalizer_iff.mp hx
  have hRi : ∀ r, r ∈ R ↔ x⁻¹ * r * x ∈ R := fun r => by
    simpa using mem_normalizer_iff.mp hxi r
  have hC : ∀ z, z ∈ centralizer (R : Set G) → x * z * x⁻¹ ∈ centralizer (R : Set G) := by
    intro z hz
    rw [mem_centralizer_iff] at hz ⊢
    intro r hr
    have h := hz _ ((hRi r).mp hr)
    calc r * (x * z * x⁻¹) = x * ((x⁻¹ * r * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * r * x)) * x⁻¹ := by rw [h]
      _ = x * z * x⁻¹ * r := by group
  have hCi : ∀ z, z ∈ centralizer (R : Set G) → x⁻¹ * z * x ∈ centralizer (R : Set G) := by
    intro z hz
    rw [mem_centralizer_iff] at hz ⊢
    intro r hr
    have h := hz _ ((hR r).mp hr)
    calc r * (x⁻¹ * z * x) = x⁻¹ * ((x * r * x⁻¹) * z) * x := by group
      _ = x⁻¹ * (z * (x * r * x⁻¹)) * x := by rw [h]
      _ = x⁻¹ * z * x * r := by group
  rw [mem_normalizer_iff]
  intro z
  refine ⟨fun ⟨h1, h2⟩ => ⟨(hR z).mp h1, hC z h2⟩, fun ⟨h1, h2⟩ => ⟨(hR z).mpr h1, ?_⟩⟩
  have := hCi _ h2
  simpa [mul_assoc] using this

theorem le_normalizer_of_conj_mem {V R : Subgroup G}
    (h : ∀ v ∈ V, ∀ r ∈ R, v * r * v⁻¹ ∈ R) : V ≤ normalizer (R : Set G) := by
  intro v hv
  rw [mem_normalizer_iff]
  intro r
  refine ⟨fun hr => h v hv r hr, fun hr => ?_⟩
  have := h v⁻¹ (inv_mem hv) _ hr
  simpa [mul_assoc] using this

theorem mul_comm_of_sq {V : Subgroup G} (hV : ∀ v ∈ V, v * v = 1) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hV b hb)
  calc a * b = (b * a)⁻¹ := by rw [mul_inv_rev, ha', hb']
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right (show b * a * (b * a) = 1 by
          have := hV _ (mul_mem hb ha); exact this)]

theorem mem_normalizer_inf {A B : Subgroup G} {a : G} (hA : a ∈ normalizer (A : Set G))
    (hB : a ∈ normalizer (B : Set G)) : a ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  exact ⟨fun ⟨h1, h2⟩ => ⟨(hA x).mp h1, (hB x).mp h2⟩,
    fun ⟨h1, h2⟩ => ⟨(hA x).mpr h1, (hB x).mpr h2⟩⟩

theorem commutator_eq_self_of_isPerfect {X : Subgroup G} (h : Group.IsPerfect X) :
    ⁅X, X⁆ = X := by
  have h' := congrArg (map X.subtype) (Group.isPerfect_def.1 h)
  rwa [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h'

theorem map_conj_eq_of_mem_normalizer {K : Subgroup G} {t : G}
    (ht : t ∈ normalizer (K : Set G)) : K.map (MulAut.conj t).toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp ht y).mp hy
  · intro hx
    refine ⟨t⁻¹ * x * t, ?_, by simp [mul_assoc]⟩
    have := (mem_normalizer_iff.mp (inv_mem ht) x).mp hx
    simpa using this

theorem mem_normalizer_of_map_conj_eq {Q : Subgroup G} {x : G}
    (hx : Q.map (MulAut.conj x).toMonoidHom = Q) : x ∈ normalizer (Q : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hx]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hx] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    have : z = y := by
      have := congrArg (fun w => x⁻¹ * w * x) hzy
      simpa [mul_assoc] using this
    rwa [← this]

theorem le_normalizer_centralizer (K : Subgroup G) :
    K ≤ normalizer (centralizer (K : Set G) : Set G) := by
  refine le_normalizer_of_conj_mem fun k hk c hc => ?_
  rw [mem_centralizer_iff] at hc ⊢
  intro y hy
  calc y * (k * c * k⁻¹) = y * k * c * k⁻¹ := by group
    _ = k * c * k⁻¹ * y := by
      have h3 := hc (k⁻¹ * y * k) (mul_mem (mul_mem (inv_mem hk) hy) hk)
      calc y * k * c * k⁻¹ = k * ((k⁻¹ * y * k) * c) * k⁻¹ := by group
        _ = k * (c * (k⁻¹ * y * k)) * k⁻¹ := by rw [h3]
        _ = k * c * k⁻¹ * y := by group

theorem centralizer_map_conj (X : Subgroup G) (g : G) :
    centralizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rw [mem_centralizer_iff] at hy
    intro x hx
    have := hy (g * x * g⁻¹) ⟨x, hx, rfl⟩
    calc x * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * y * g * x := by group
  · rintro ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff] at hc
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have := hc x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * c * g⁻¹) = g * (x * c) * g⁻¹ := by group
      _ = g * (c * x) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * (g * x * g⁻¹) := by group

theorem conj_component_eq {Q₁ Q₂ : Subgroup G} {x : G} (h₁ : CFSG.Open.IsQuasisimple Q₁)
    (h₂ : CFSG.Open.IsQuasisimple Q₂) (hc : ⁅Q₁, Q₂⁆ = ⊥)
    (hx : x ∈ normalizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G)) :
    Q₁.map (MulAut.conj x).toMonoidHom = Q₁ ∨ Q₁.map (MulAut.conj x).toMonoidHom = Q₂ := by
  set K := Q₁ ⊔ Q₂ with hK
  have h21 : Q₂ ≤ centralizer (Q₁ : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp (by rw [commutator_comm]; exact hc)
  have hKN : K ≤ normalizer (Q₁ : Set G) :=
    sup_le le_normalizer (h21.trans (centralizer_le_normalizer _))
  have hq : CFSG.Open.IsQuasisimple (Q₁.map (MulAut.conj x).toMonoidHom) :=
    isQuasisimple_of_mulEquiv (Q₁.equivMapOfInjective _ (MulAut.conj x).injective) h₁
  refine eq_or_eq_of_quasisimple_of_le_sup h₁ h₂ hq hc ?_ ?_
  · calc Q₁.map (MulAut.conj x).toMonoidHom ≤ K.map (MulAut.conj x).toMonoidHom :=
          map_mono le_sup_left
      _ = K := map_conj_eq_of_mem_normalizer hx
  · refine le_normalizer_of_conj_mem fun k hk q hq' => ?_
    obtain ⟨q₁, hq₁, rfl⟩ := hq'
    have hk' : x⁻¹ * k * x ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hx) k).mp hk
      simpa using this
    have hq₂ : (x⁻¹ * k * x) * q₁ * (x⁻¹ * k * x)⁻¹ ∈ Q₁ :=
      (mem_normalizer_iff.mp (hKN hk') q₁).mp hq₁
    refine ⟨_, hq₂, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem eq_one_of_sq_of_odd {A : Subgroup G} (hA : Odd (Nat.card A)) {x : G} (hx : x ∈ A)
    (hsq : x * x = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  have h2 : orderOf (⟨x, hx⟩ : A) ∣ Nat.card A := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h2
  have h3 : orderOf x ∣ Nat.gcd 2 (Nat.card A) := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd 2 (Nat.card A) = 1 :=
    Nat.Coprime.symm (Nat.coprime_two_right.2 hA) |>.gcd_eq_one
  rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] [Finite G] {Q K : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨P', hP'⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(P' : Subgroup K).map K.subtype, ⟨P', rfl⟩, fun q hq => ?_⟩
  exact ⟨⟨q, hQK hq⟩, hP' hq, rfl⟩

theorem card_le_of_isSylowOf {p : ℕ} [Fact p.Prime] [Finite G] {P Q K : Subgroup G}
    (hP : IsSylowOf p P K) (hQK : Q ≤ K) (hQ : IsPGroup p Q) : Nat.card Q ≤ Nat.card P := by
  obtain ⟨P', hP'⟩ := exists_isSylowOf_ge hQK hQ
  rw [hP.card_eq, ← hP'.1.card_eq]
  exact card_le_of_le hP'.2

theorem mem_of_mem_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] [Finite G] {S L : Subgroup G}
    (hS : IsSylowOf p S L) {x : G} (hxL : x ∈ L) (hxN : x ∈ normalizer (S : Set G)) {k : ℕ}
    (hk : x ^ p ^ k = 1) : x ∈ S := by
  have hx : IsPGroup p (zpowers x) := by
    rintro ⟨y, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hle : zpowers x ≤ normalizer (S : Set G) := by rw [zpowers_le]; exact hxN
  have hpg := IsPGroup.to_sup_of_normal_left' hS.isPGroup hx hle
  have heq := hS.eq_of_le le_sup_left (sup_le hS.le (by rw [zpowers_le]; exact hxL)) hpg
  rw [← heq]
  exact mem_sup_right (mem_zpowers x)

variable [Finite G] {F : Type} [Field F] [Finite F] {L : Subgroup G} {t : G}
  {S A₁ V₁ G₀ : Subgroup G}

theorem zpowers_le_centralizer_S (h : YamadaG0 F L t S A₁ V₁ G₀) :
    zpowers t ≤ centralizer (S : Set G) := by
  rw [zpowers_le, mem_centralizer_iff]
  intro s hs
  exact mem_centralizer_iff.mp h.t_mem s (h.sylow.le hs)

theorem inf_centralizer_L_eq_bot (h : YamadaG0 F L t S A₁ V₁ G₀) :
    L ⊓ centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyL, hyC⟩
  have hz : (⟨y, hyL⟩ : L) ∈ center L := mem_center_iff.mpr fun l =>
    Subtype.ext (mem_centralizer_iff.mp hyC l l.2)
  rw [h.center_eq, mem_bot] at hz
  exact congrArg Subtype.val hz

theorem sup_zpowers_inf_L (h : YamadaG0 F L t S A₁ V₁ G₀) :
    (S ⊔ zpowers t) ⊓ L = S := by
  refine le_antisymm ?_ (le_inf le_sup_left h.sylow.le)
  rintro x ⟨hx, hxL⟩
  have hmul : (↑(S ⊔ zpowers t) : Set G) = (S : Set G) * (zpowers t : Set G) :=
    coe_mul_of_right_le_normalizer_left S (zpowers t)
      ((zpowers_le_centralizer_S h).trans (centralizer_le_normalizer _))
  have hx' : x ∈ (S : Set G) * (zpowers t : Set G) := hmul ▸ hx
  obtain ⟨s, hs, z, hz, rfl⟩ := hx'
  have hzL : z ∈ L := by
    have := L.mul_mem (L.inv_mem (h.sylow.le hs)) hxL
    simpa using this
  have hzC : z ∈ centralizer (L : Set G) := by
    have : zpowers t ≤ centralizer (L : Set G) := by rw [zpowers_le]; exact h.t_mem
    exact this hz
  have hz1 : z = 1 := by
    have := (inf_centralizer_L_eq_bot h).le ⟨hzL, hzC⟩
    rwa [mem_bot] at this
  simpa [hz1] using hs

theorem t_mem_normalizer_V₁ (h : YamadaG0 F L t S A₁ V₁ G₀) :
    t ∈ normalizer (V₁ : Set G) := by
  apply h.V₁_normal
  apply normalizer_le_normalizer_centerSub
  exact le_normalizer (mem_sup_right (mem_zpowers t))

theorem V₁_le_normalizer_R (h : YamadaG0 F L t S A₁ V₁ G₀) :
    V₁ ≤ normalizer ((S ⊔ zpowers t : Subgroup G) : Set G) := by
  have ht2 : t * t = 1 := by rw [← sq, ← h.order_t]; exact pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htN := t_mem_normalizer_V₁ h
  have hconj : ∀ v ∈ V₁, v * t * v⁻¹ ∈ S ⊔ zpowers t := by
    intro v hv
    set w := t * v * t⁻¹ with hw
    have hwV : w ∈ V₁ := (mem_normalizer_iff.mp htN v).mp hv
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.V₁_sq v hv)
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right (h.V₁_sq w hwV)
    set u := v * w with hu
    have huV : u ∈ V₁ := mul_mem hv hwV
    have e1 : u * t = v * t * v := by
      rw [hu, hw, hti]
      simp only [mul_assoc, ht2, mul_one]
    have e2 : t * u = v * t * v := by
      rw [hu, mul_comm_of_sq h.V₁_sq hv hwV, hw, hti]
      simp only [← mul_assoc, ht2, one_mul]
    have hut : u ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff, e1, e2]
    have huS : u ∈ S := h.V₁_fix ⟨huV, hut⟩
    have : v * t * v⁻¹ = u * t := by rw [e1, hvi]
    rw [this]
    exact mul_mem (mem_sup_left huS) (mem_sup_right (mem_zpowers t))
  refine le_normalizer_of_conj_mem fun v hv r hr => ?_
  have hmap : (S ⊔ zpowers t).map (MulAut.conj v).toMonoidHom ≤ S ⊔ zpowers t := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      have hc := mem_centralizer_iff.mp (h.V₁_comm hv) s hs
      have : (MulAut.conj v).toMonoidHom s = s := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← hc, mul_inv_cancel_right]
      rw [this]
      exact mem_sup_left hs
    · rw [MonoidHom.map_zpowers, zpowers_le]
      exact hconj v hv
  exact hmap (mem_map_of_mem _ hr)

theorem normalizer_R_le (h : YamadaG0 F L t S A₁ V₁ G₀) :
    normalizer ((S ⊔ zpowers t : Subgroup G) : Set G) ≤
      (normalizer (S : Set G) ⊓ centralizer ({t} : Set G)) ⊔ V₁ := by
  intro x hx
  have hxZ := normalizer_le_normalizer_centerSub _ hx
  rw [h.normalizer_center] at hxZ
  have hle : normalizer (A₁ : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (V₁ : Set G) :=
    (le_sup_left.trans h.normalizer_center.ge).trans h.V₁_normal
  have hxm : x ∈ ((normalizer (A₁ : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) *
      (V₁ : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ V₁ hle]
    exact hxZ
  obtain ⟨a, ha, v, hv, hav⟩ := hxm
  simp only at hav
  subst hav
  have haR : a ∈ normalizer ((S ⊔ zpowers t : Subgroup G) : Set G) := by
    have := mul_mem hx (inv_mem (V₁_le_normalizer_R h hv))
    simpa using this
  have haL : a ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard h.setting.standard h.t_mem h.order_t ha.2
  have haS : a ∈ normalizer (S : Set G) := by
    have := mem_normalizer_inf haR haL
    rwa [sup_zpowers_inf_L h] at this
  exact mul_mem (mem_sup_left ⟨haS, ha.2⟩) (mem_sup_right hv)

theorem mem_normalizer_of_le_sup
    (h : YamadaG0 F L t S A₁ V₁ G₀) {g : G}
    (hK : ⁅G₀.map (MulAut.conj g).toMonoidHom, G₀.map (MulAut.conj g).toMonoidHom⁆ =
      G₀.map (MulAut.conj g).toMonoidHom)
    (hle : G₀.map (MulAut.conj g).toMonoidHom ≤
      (normalizer (S : Set G) ⊓ centralizer ({t} : Set G)) ⊔ G₀) :
    g ∈ normalizer (G₀ : Set G) := by
  have : Group.IsSolvable (normalizer (S : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    isSolvable_normalizer h.setting.standard h.center_eq h.lie h.order_t h.t_mem h.kernel
      h.card_normalizer
  have hKle := le_of_perfect_of_le_sup h.normalizer_le hK hle
  have heq : G₀.map (MulAut.conj g).toMonoidHom = G₀ :=
    eq_of_le_of_card_ge hKle (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [mul_assoc] using this
    rwa [← this]

theorem yamada_5_5_linear
    (h : YamadaG0 F L t S A₁ V₁ G₀) (hA : L64CentralizerInput)
    (hlin : LinearCase F G₀) (g : G)
    (hg : t ∈ normalizer ((G₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    g ∈ normalizer (G₀ : Set G) := by
  obtain ⟨⟨ψ, hψ, hker⟩, hqs⟩ := hlin
  set K := G₀.map (MulAut.conj g).toMonoidHom with hKdef
  set e : G₀ ≃* K := G₀.equivMapOfInjective _ (MulAut.conj g).injective with he
  set ψK : SL(6, F) →* K := e.toMonoidHom.comp ψ with hψKdef
  have hψK : Function.Surjective ψK := e.surjective.comp hψ
  have hkerK : ψK.ker ≤ center SL(6, F) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    apply e.injective
    rw [map_one]
    exact hx
  have hH2 : ∀ Q ≤ K ⊓ centralizer ({t} : Set G), IsPGroup 2 Q → Nat.card Q ≤ 2 ^ 17 :=
    fun Q hQ hQ2 => card_le_of_isPGroup h.setting.standard h.lie h.order_t h.t_mem h.kernel
      (hQ.trans inf_le_right) hQ2
  obtain ⟨hCperf, hCcard, hgen⟩ := hA G F h.card_field K ψK hψK hkerK t h.order_t hg hH2
  have hCL : K ⊓ centralizer ({t} : Set G) ≤ L :=
    le_of_perfect h.setting.standard h.center_eq h.lie h.order_t h.t_mem h.kernel inf_le_right
      hCperf
  have hcardL : Nat.card L = orderPSU62 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center L), card_of_lieModel_PSU h.lie,
      h.center_eq, card_bot, mul_one, orderPSU62]
  have hCle := card_le_of_le hCL
  have hCeq : K ⊓ centralizer ({t} : Set G) = L := by
    refine eq_of_le_of_card_ge hCL ?_
    rw [hcardL]
    rcases hCcard with h1 | h1 | h1
    · rw [h1, hcardL] at hCle
      exact absurd hCle (by norm_num [orderSL62, orderPSU62])
    · rw [h1, hcardL] at hCle
      exact absurd hCle (by norm_num [orderSU62, orderPSU62])
    · exact h1.ge
  have hCne : Nat.card (K ⊓ centralizer ({t} : Set G) : Subgroup G) ≠ orderSL62 := by
    rw [hCeq, hcardL]
    norm_num [orderSL62, orderPSU62]
  have hSC : IsSylowOf 2 S (K ⊓ centralizer ({t} : Set G)) := hCeq ▸ h.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀, hSP₀⟩ := exists_isSylowOf_ge (hSC.le.trans inf_le_left) hSC.isPGroup
  have hKeq := hgen hCne S P₀ hSC hP₀ hSP₀
  have hKperf : ⁅K, K⁆ = K := by
    have h0 : ⁅G₀, G₀⁆ = G₀ := commutator_eq_self_of_isPerfect hqs.1
    rw [hKdef, ← map_commutator, h0]
  refine mem_normalizer_of_le_sup h hKperf ?_
  change K ≤ _
  rw [hKeq, hCeq]
  refine sup_le (h.L_le.trans le_sup_right) ?_
  exact inf_le_right.trans ((normalizer_R_le h).trans
    (sup_le le_sup_left (h.V₁_le.trans le_sup_right)))

theorem false_of_normalizes_components (h : YamadaG0 F L t S A₁ V₁ G₀) (hU : U62RankInput)
    {Q₁ Q₂ : Subgroup G} (hq₁ : CFSG.Open.IsQuasisimple Q₁) (hq₂ : CFSG.Open.IsQuasisimple Q₂)
    (hl₁ : LieModel (Q₁ ⧸ center Q₁) .PSU 6 2 1) (hl₂ : LieModel (Q₂ ⧸ center Q₂) .PSU 6 2 1)
    (ho₁ : Odd (Nat.card (center Q₁))) (ho₂ : Odd (Nat.card (center Q₂)))
    (hc : ⁅Q₁, Q₂⁆ = ⊥) (hodd : Odd (Nat.card (centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G))))
    (ht₁ : t ∈ normalizer (Q₁ : Set G)) (ht₂ : t ∈ normalizer (Q₂ : Set G)) : False := by
  have ht2 : t * t = 1 := by rw [← sq, ← h.order_t]; exact pow_orderOf_eq_one t
  obtain ⟨E₁, hE₁, hsq₁, hc₁⟩ := hU.1 G Q₁ hq₁ hl₁ ho₁ t ht₁ ht2
  obtain ⟨E₂, hE₂, hsq₂, hc₂⟩ := hU.1 G Q₂ hq₂ hl₂ ho₂ t ht₂ ht2
  have h12 : Q₁ ≤ centralizer (Q₂ : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (h12 (hE₁ ha).1) b (hE₂ hb).1).symm
  have hEle : E₁ ⊔ E₂ ≤ centralizer ({t} : Set G) :=
    sup_le (hE₁.trans inf_le_right) (hE₂.trans inf_le_right)
  have hE₁C : E₁ ≤ centralizer (E₂ : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => (hcomm a ha b hb).symm
  have hE12 : E₁ ≤ normalizer (E₂ : Set G) := hE₁C.trans (centralizer_le_normalizer _)
  have hmul : (↑(E₁ ⊔ E₂) : Set G) = (E₁ : Set G) * (E₂ : Set G) :=
    coe_mul_of_left_le_normalizer_right E₁ E₂ hE12
  have hsq : ∀ e ∈ E₁ ⊔ E₂, e * e = 1 := by
    intro e he
    have he' : e ∈ (E₁ : Set G) * (E₂ : Set G) := hmul ▸ he
    obtain ⟨a, ha, b, hb, hab⟩ := he'
    simp only at hab
    subst hab
    calc a * b * (a * b) = a * a * (b * b) := by
          rw [mul_assoc, ← mul_assoc b a b, ← hcomm a ha b hb]; group
      _ = 1 := by rw [hsq₁ a ha, hsq₂ b hb, one_mul]
  have hup := card_le_of_sq_eq_one h.setting.standard h.lie h.order_t h.t_mem h.kernel hU.2
    hEle hsq
  have hinj : Function.Injective (fun p : E₁ × E₂ =>
      (⟨(p.1 : G) * p.2, by rw [← SetLike.mem_coe, hmul]; exact Set.mul_mem_mul p.1.2 p.2.2⟩ :
        (E₁ ⊔ E₂ : Subgroup G))) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : G) * b = a' * b' := congrArg Subtype.val hab
    set x := (a' : G)⁻¹ * a with hx
    have hxE₁ : x ∈ E₁ := mul_mem (inv_mem a'.2) a.2
    have hxE₂ : x ∈ E₂ := by
      have : x = b' * (b : G)⁻¹ := by
        rw [hx]
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [hab']
          _ = b' * (b : G)⁻¹ := by group
      rw [this]
      exact mul_mem b'.2 (inv_mem b.2)
    have hxC : x ∈ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) :=
      mem_centralizer_sup (fun q hq => (mem_centralizer_iff.mp
          (h12 hq) x (hE₂ hxE₂).1).symm)
        (fun q hq => mem_centralizer_iff.mp (h12 (hE₁ hxE₁).1) q hq)
    have hx1 := eq_one_of_sq_of_odd hodd hxC (hsq₁ x hxE₁)
    have ha : a = a' := Subtype.ext (by
      have := hx1
      rw [hx, inv_mul_eq_one] at this
      exact this.symm)
    subst ha
    have hb : b = b' := Subtype.ext (mul_left_cancel hab')
    rw [hb]
  have hlow := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hlow
  have : 2 ^ 6 * 2 ^ 6 ≤ 2 ^ 10 := (Nat.mul_le_mul hc₁ hc₂).trans (hlow.trans hup)
  norm_num at this

theorem le_sup_of_swap
    (h : YamadaG0 F L t S A₁ V₁ G₀) {Q₁ : Subgroup G}
    (hq₁ : CFSG.Open.IsQuasisimple Q₁)
    (hq₂ : CFSG.Open.IsQuasisimple (Q₁.map (MulAut.conj t).toMonoidHom))
    (hl₁ : LieModel (Q₁ ⧸ center Q₁) .PSU 6 2 1)
    (hc : ⁅Q₁, Q₁.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (htK : t ∈ normalizer ((Q₁ ⊔ Q₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hodd : Odd (Nat.card (centralizer
      ((Q₁ ⊔ Q₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))))
    (hP : ∃ P : Subgroup G, P ≤ Q₁ ⊔ Q₁.map (MulAut.conj t).toMonoidHom ∧ IsPGroup 2 P ∧
      2 ^ 30 ≤ Nat.card P) :
    Q₁ ⊔ Q₁.map (MulAut.conj t).toMonoidHom ≤
      (normalizer (S : Set G) ⊓ centralizer ({t} : Set G)) ⊔ G₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₂ := Q₁.map (MulAut.conj t).toMonoidHom with hQ₂
  set K := Q₁ ⊔ Q₂ with hK
  have ht2 : t * t = 1 := by rw [← sq, ← h.order_t]; exact pow_orderOf_eq_one t
  have h12 : Q₁ ≤ centralizer (Q₂ : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  have hcd : ∀ u ∈ Q₁, ∀ v ∈ Q₁, v * (t * u * t⁻¹) = t * u * t⁻¹ * v := fun u hu v hv =>
    (mem_centralizer_iff.mp (h12 hv) _ ⟨u, hu, rfl⟩).symm
  set φ := diagHom Q₁ t hcd with hφ
  set J := φ.range with hJ
  have hJC : J ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨u, rfl⟩
    exact diagHom_mem_centralizer hcd ht2 u
  have hJperf : ⁅J, J⁆ = J := by
    rw [hJ, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hq₁.1]
  have hJL : J ≤ L :=
    le_of_perfect h.setting.standard h.center_eq h.lie h.order_t h.t_mem h.kernel hJC hJperf
  have hkerZ : φ.ker ≤ center Q₁ := by
    intro u hu
    rw [MonoidHom.mem_ker, hφ, diagHom_apply] at hu
    have hinv : t * (u : G) * t⁻¹ = (u : G)⁻¹ := eq_inv_of_mul_eq_one_right hu
    have huQ₂ : (u : G) ∈ Q₂ := by
      have : (u : G)⁻¹ ∈ Q₂ := hinv ▸ ⟨u, u.2, rfl⟩
      simpa using inv_mem this
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (mem_centralizer_iff.mp (h12 v.2) _ huQ₂).symm
  have hcardL : Nat.card L = 9196830720 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center L), card_of_lieModel_PSU h.lie,
      h.center_eq, card_bot, mul_one]
  have hJcard : Nat.card L ≤ Nat.card J := by
    have h1 : Nat.card Q₁ = Nat.card J * Nat.card φ.ker := by
      rw [card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    have h2 : Nat.card Q₁ = 9196830720 * Nat.card (center Q₁) := by
      rw [card_eq_card_quotient_mul_card_subgroup (center Q₁), card_of_lieModel_PSU hl₁]
    have h3 : Nat.card φ.ker ≤ Nat.card (center Q₁) := card_le_of_le hkerZ
    have h4 : 0 < Nat.card φ.ker := Nat.card_pos
    rw [hcardL]
    by_contra hlt
    push Not at hlt
    have : Nat.card J * Nat.card φ.ker < 9196830720 * Nat.card (center Q₁) :=
      calc Nat.card J * Nat.card φ.ker < 9196830720 * Nat.card φ.ker :=
            Nat.mul_lt_mul_of_pos_right hlt h4
        _ ≤ 9196830720 * Nat.card (center Q₁) := Nat.mul_le_mul_left _ h3
    omega
  have hJeq : J = L := eq_of_le_of_card_ge hJL hJcard
  have hJK : J ≤ K := by
    rintro _ ⟨u, rfl⟩
    rw [hφ, diagHom_apply]
    exact mul_mem (mem_sup_left u.2) (mem_sup_right ⟨u, u.2, rfl⟩)
  have hLK : L ≤ K := hJeq ▸ hJK
  set R := S ⊔ zpowers t with hR
  have hSL := h.sylow.le
  have htC : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hLH : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.t_mem l hl)
  have hRH : R ≤ centralizer ({t} : Set G) :=
    sup_le (hSL.trans hLH) (by rw [zpowers_le]; exact htC)
  have htz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.order_t, pow_one])
  have hR2 : IsPGroup 2 R := IsPGroup.to_sup_of_normal_left' h.sylow.isPGroup htz
    ((zpowers_le_centralizer_S h).trans (centralizer_le_normalizer _))
  have hRcard : Nat.card R ≤ 2 ^ 17 :=
    card_le_of_isPGroup h.setting.standard h.lie h.order_t h.t_mem h.kernel hRH hR2
  set Kp := K ⊔ zpowers t with hKp
  have hRKp : R ≤ Kp := sup_le ((hSL.trans hLK).trans le_sup_left) le_sup_right
  obtain ⟨T, hT, hRT⟩ := exists_isSylowOf_ge hRKp hR2
  have hKpN : Kp ≤ normalizer (K : Set G) := sup_le le_normalizer (by rw [zpowers_le]; exact htK)
  have hP₀ : IsSylowOf 2 (T ⊓ K) K := hT.inf_of_le_normalizer le_sup_left hKpN
  have hP₀card : 2 ^ 30 ≤ Nat.card (T ⊓ K : Subgroup G) := by
    obtain ⟨P, hPK, hP2, hPc⟩ := hP
    exact hPc.trans (card_le_of_isSylowOf hP₀ hPK hP2)
  have hRne : R ≠ T := by
    intro hRTeq
    have h1 : Nat.card (T ⊓ K : Subgroup G) ≤ Nat.card R := hRTeq ▸ card_le_of_le inf_le_left
    omega
  obtain ⟨y, hyT, hyN, hyR⟩ : ∃ y ∈ T, y ∈ normalizer (R : Set G) ∧ y ∉ R := by
    have hT2 : IsPGroup 2 T := hT.isPGroup
    have : Group.IsNilpotent T := hT2.isNilpotent
    have hlt : R.subgroupOf T < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hRne (le_antisymm hRT fun x hx => ?_)
      have : (⟨x, hx⟩ : T) ∈ R.subgroupOf T := htop ▸ mem_top _
      exact this
    obtain ⟨z, hzN, hzR⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    refine ⟨z, z.2, ?_, hzR⟩
    rw [mem_normalizer_iff]
    intro w
    have hz := mem_normalizer_iff.mp hzN
    constructor
    · intro hw
      exact (hz ⟨w, hRT hw⟩).mp hw
    · intro hw
      have hwT : w ∈ T := by
        have := T.mul_mem (T.mul_mem (T.inv_mem z.2) (hRT hw)) z.2
        simpa [mul_assoc] using this
      exact (hz ⟨w, hwT⟩).mpr hw
  have hKpmul : (↑Kp : Set G) = (K : Set G) * (zpowers t : Set G) :=
    coe_mul_of_right_le_normalizer_left K (zpowers t) (by rw [zpowers_le]; exact htK)
  have hy' : y ∈ (K : Set G) * (zpowers t : Set G) := hKpmul ▸ hT.le hyT
  obtain ⟨x, hxK, z, hz, hxz⟩ := hy'
  simp only at hxz
  subst hxz
  have hzR : z ∈ R := mem_sup_right hz
  have hxT : x ∈ T := by
    have := T.mul_mem hyT (T.inv_mem (hRT hzR))
    simpa using this
  have hxN : x ∈ normalizer (R : Set G) := by
    have := mul_mem hyN (inv_mem (le_normalizer hzR))
    simpa using this
  have hxR : x ∉ R := fun hx => hyR (mul_mem hx hzR)
  obtain ⟨k, hk⟩ := hP₀.isPGroup ⟨x, hxT, hxK⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hxJ : x ∉ J ⊔ centralizer (K : Set G) := by
    intro hx
    rw [hJeq] at hx
    have hmul : (↑(L ⊔ centralizer (K : Set G)) : Set G) =
        (L : Set G) * (centralizer (K : Set G) : Set G) :=
      coe_mul_of_left_le_normalizer_right L _ (hLK.trans (le_normalizer_centralizer K))
    have hx' : x ∈ (L : Set G) * (centralizer (K : Set G) : Set G) := hmul ▸ hx
    obtain ⟨l, hl, c, hc', hlc⟩ := hx'
    simp only at hlc
    subst hlc
    have hcomm : l * c = c * l := (mem_centralizer_iff.mp hc' l (hLK hl))
    have hxL : l * c ∈ L := mem_of_mul_central_odd hodd hl hc' hcomm hk'
    have hxNL : l * c ∈ normalizer (L : Set G) := le_normalizer hxL
    have hxNS : l * c ∈ normalizer (S : Set G) := by
      have := mem_normalizer_inf hxN hxNL
      rwa [sup_zpowers_inf_L h] at this
    exact hxR (mem_sup_left (mem_of_mem_normalizer_of_isSylowOf h.sylow hxL hxNS hk'))
  have hgen := le_closure_sup_diag hcd hq₂ hxK hxJ
  refine hgen.trans (sup_le ?_ ?_)
  · rw [closure_le, Set.singleton_subset_iff]
    exact (sup_le le_sup_left (h.V₁_le.trans le_sup_right)) (normalizer_R_le h hxN)
  · exact (le_of_eq hJeq).trans (h.L_le.trans le_sup_right)

theorem yamada_5_5_unitary
    (h : YamadaG0 F L t S A₁ V₁ G₀) (hU : U62RankInput)
    (hun : UnitaryCase G₀ t) (g : G)
    (hg : t ∈ normalizer ((G₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    g ∈ normalizer (G₀ : Set G) := by
  obtain ⟨G₁, hG₀, hc, hne, hq, hlie, hZ3⟩ := hun
  set G₂ := G₁.map (MulAut.conj t).toMonoidHom with hG₂
  set Q₁ := G₁.map (MulAut.conj g).toMonoidHom with hQ₁
  set Q₂ := G₂.map (MulAut.conj g).toMonoidHom with hQ₂
  set K := G₀.map (MulAut.conj g).toMonoidHom with hKdef
  have hK : K = Q₁ ⊔ Q₂ := by rw [hKdef, hG₀, Subgroup.map_sup]
  have hcQ : ⁅Q₁, Q₂⁆ = ⊥ := by rw [hQ₁, hQ₂, ← map_commutator, hc, Subgroup.map_bot]
  have eG₂ : G₁ ≃* G₂ := G₁.equivMapOfInjective _ (MulAut.conj t).injective
  have eQ₁ : G₁ ≃* Q₁ := G₁.equivMapOfInjective _ (MulAut.conj g).injective
  have eQ₂ : G₂ ≃* Q₂ := G₂.equivMapOfInjective _ (MulAut.conj g).injective
  have hq₁ := isQuasisimple_of_mulEquiv eQ₁ hq
  have hq₂ := isQuasisimple_of_mulEquiv eQ₂ (isQuasisimple_of_mulEquiv eG₂ hq)
  have hl₁ : LieModel (Q₁ ⧸ center Q₁) .PSU 6 2 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (quotientCenterEquiv eQ₁) hlie
  have hl₂ : LieModel (Q₂ ⧸ center Q₂) .PSU 6 2 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (quotientCenterEquiv (eG₂.trans eQ₂)) hlie
  have ho : Odd (Nat.card (center G₁)) := Odd.of_dvd_nat (by decide) hZ3
  have ho₁ : Odd (Nat.card (center Q₁)) := by
    rwa [← Nat.card_congr (Subgroup.centerCongr eQ₁).toEquiv]
  have ho₂ : Odd (Nat.card (center Q₂)) := by
    rwa [← Nat.card_congr (Subgroup.centerCongr (eG₂.trans eQ₂)).toEquiv]
  have hoddK : Odd (Nat.card (centralizer (K : Set G))) := by
    rw [hKdef, centralizer_map_conj, card_map_of_injective (MulAut.conj g).injective]
    exact h.odd_centralizer
  have hPK : ∃ P : Subgroup G, P ≤ K ∧ IsPGroup 2 P ∧ 2 ^ 30 ≤ Nat.card P := by
    obtain ⟨P, hP, hP2, hPc⟩ := h.two_subgroup
    exact ⟨P.map (MulAut.conj g).toMonoidHom, map_mono hP, hP2.map _,
      by rwa [card_map_of_injective (MulAut.conj g).injective]⟩
  have htK : t ∈ normalizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) := hK ▸ hg
  have hKperf : ⁅K, K⁆ = K := by
    rw [hK]
    refine le_antisymm (commutator_le_self _) (sup_le ?_ ?_)
    · calc Q₁ = ⁅Q₁, Q₁⁆ := (commutator_eq_self_of_quasisimple hq₁).symm
        _ ≤ _ := commutator_mono le_sup_left le_sup_left
    · calc Q₂ = ⁅Q₂, Q₂⁆ := (commutator_eq_self_of_quasisimple hq₂).symm
        _ ≤ _ := commutator_mono le_sup_right le_sup_right
  refine mem_normalizer_of_le_sup h hKperf ?_
  change K ≤ _
  rcases conj_component_eq hq₁ hq₂ hcQ htK with hT | hT
  · exfalso
    have ht₁ := mem_normalizer_of_map_conj_eq hT
    have htK' : t ∈ normalizer ((Q₂ ⊔ Q₁ : Subgroup G) : Set G) := by rwa [sup_comm]
    have hcQ' : ⁅Q₂, Q₁⁆ = ⊥ := by rw [commutator_comm]; exact hcQ
    rcases conj_component_eq hq₂ hq₁ hcQ' htK' with hT₂ | hT₂
    · exact false_of_normalizes_components h hU hq₁ hq₂ hl₁ hl₂ ho₁ ho₂ hcQ (hK ▸ hoddK) ht₁
        (mem_normalizer_of_map_conj_eq hT₂)
    · have h21 : Q₂ = Q₁ := map_injective (MulAut.conj t).injective (hT₂.trans hT.symm)
      exact hne (map_injective (MulAut.conj g).injective h21)
  · rw [← hT] at hq₂ hcQ hK htK
    rw [hK]
    exact le_sup_of_swap h hq₁ hq₂ hl₁ hcQ htK (hK ▸ hoddK) (hK ▸ hPK)

theorem yamada_5_5
    (h : YamadaG0 F L t S A₁ V₁ G₀) (hA : L64CentralizerInput)
    (hU : U62RankInput) (g : G)
    (hg : t ∈ normalizer ((G₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    g ∈ normalizer (G₀ : Set G) :=
  h.cases.elim (fun hl => yamada_5_5_linear h hA hl g hg)
    (fun hu => yamada_5_5_unitary h hU hu g hg)

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
