module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step48N
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step110Nat
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step110Conf

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Q47 N48

section Cosets

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_of_inj_mod {B D I : Subgroup G} (hIB : I ≤ B) (hID : I ≤ D) (f : G → G)
    (hf : ∀ d ∈ D, f d ∈ B) (hmul : ∀ d ∈ D, ∀ e ∈ D, (f d)⁻¹ * f (d * e) * (f e)⁻¹ ∈ I)
    (hfI : ∀ i ∈ I, f i ∈ I) (hker : ∀ d ∈ D, f d ∈ I → d ∈ I)
    (hcard : Nat.card B ≤ Nat.card D) : ∀ b ∈ B, ∃ d ∈ D, (f d)⁻¹ * b ∈ I := by
  have hrel : ∀ d ∈ D, ∀ e ∈ D, (f d)⁻¹ * f (d * e) ∈ I ↔ e ∈ I := by
    intro d hd e he
    have h1 := hmul d hd e he
    constructor
    · intro h2
      apply hker e he
      have : f e = ((f d)⁻¹ * f (d * e) * (f e)⁻¹)⁻¹ * ((f d)⁻¹ * f (d * e)) := by group
      rw [this]
      exact mul_mem (inv_mem h1) h2
    · intro h2
      have : (f d)⁻¹ * f (d * e) = ((f d)⁻¹ * f (d * e) * (f e)⁻¹) * f e := by group
      rw [this]
      exact mul_mem h1 (hfI e h2)
  have hrel' : ∀ d d' : ↥D, (f d)⁻¹ * f d' ∈ I ↔ (d : G)⁻¹ * d' ∈ I := by
    intro d d'
    have := hrel d d.2 ((d : G)⁻¹ * d') (mul_mem (inv_mem d.2) d'.2)
    rwa [mul_inv_cancel_left] at this
  let Φ : ↥D ⧸ I.subgroupOf D → ↥B ⧸ I.subgroupOf B :=
    Quotient.map' (fun d : ↥D => (⟨f d, hf d d.2⟩ : ↥B)) (fun d d' hdd' => by
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hdd' ⊢
      simpa using (hrel' d d').2 (by simpa using hdd'))
  have hΦ : ∀ d : ↥D, Φ (d : ↥D ⧸ I.subgroupOf D) = ((⟨f d, hf d d.2⟩ : ↥B) : _) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H d => ?_
    induction y using QuotientGroup.induction_on with | H d' => ?_
    rw [hΦ, hΦ, QuotientGroup.eq, mem_subgroupOf] at hxy
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa using (hrel' d d').1 (by simpa using hxy)
  have hcD : Nat.card D = Nat.card (↥D ⧸ I.subgroupOf D) * Nat.card I := by
    rw [card_eq_card_quotient_mul_card_subgroup (I.subgroupOf D),
      Nat.card_congr (subgroupOfEquivOfLe hID).toEquiv]
  have hcB : Nat.card B = Nat.card (↥B ⧸ I.subgroupOf B) * Nat.card I := by
    rw [card_eq_card_quotient_mul_card_subgroup (I.subgroupOf B),
      Nat.card_congr (subgroupOfEquivOfLe hIB).toEquiv]
  have hI0 : 0 < Nat.card I := Nat.card_pos
  have hge : Nat.card (↥B ⧸ I.subgroupOf B) ≤ Nat.card (↥D ⧸ I.subgroupOf D) := by
    rw [hcB, hcD] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hI0
  have hbij := hinj.bijective_of_nat_card_le hge
  intro b hb
  obtain ⟨x, hx⟩ := hbij.2 ((⟨b, hb⟩ : ↥B) : ↥B ⧸ I.subgroupOf B)
  induction x using QuotientGroup.induction_on with | H d => ?_
  refine ⟨d, d.2, ?_⟩
  rw [hΦ, QuotientGroup.eq, mem_subgroupOf] at hx
  simpa using hx

end Cosets

namespace N48

theorem Facts.exists_pair (hF : Facts) {P : Set (Equiv.Perm (Fin 64))} (hP : P ⊆ nstar)
    (h1 : (1 : Equiv.Perm (Fin 64)) ∈ P) (hmul : ∀ a ∈ P, ∀ b ∈ P, a * b ∈ P)
    (hsq : ∀ a ∈ P, a * a = 1) (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∃ α ∈ P, ∃ β ∈ P, ∀ p, p ∈ P ↔ p = 1 ∨ p = α ∨ p = β ∨ p = α * β := by
  by_cases hA : ∃ α ∈ P, α ≠ 1
  · obtain ⟨α, hα, hα1⟩ := hA
    by_cases hB : ∃ β ∈ P, β ≠ 1 ∧ β ≠ α
    · obtain ⟨β, hβ, hβ1, hβα⟩ := hB
      refine ⟨α, hα, β, hβ, fun p => ⟨fun hp => ?_, ?_⟩⟩
      · rcases hF.rank α (hP hα) β (hP hβ) p (hP hp) (hsq α hα) (hsq β hβ) (hsq p hp)
          (hcomm α hα β hβ) (hcomm α hα p hp) (hcomm β hβ p hp) with h | h | h | h | h | h | h
        · exact absurd h hα1
        · exact absurd h hβ1
        · exact absurd h hβα
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · rintro (rfl | rfl | rfl | rfl)
        exacts [h1, hα, hβ, hmul _ hα _ hβ]
    · push Not at hB
      refine ⟨α, hα, α, hα, fun p => ⟨fun hp => ?_, ?_⟩⟩
      · by_cases hp1 : p = 1
        · exact Or.inl hp1
        · exact Or.inr (Or.inl (hB p hp hp1))
      · rintro (rfl | rfl | rfl | rfl)
        exacts [h1, hα, hα, hmul _ hα _ hα]
  · push Not at hA
    refine ⟨1, h1, 1, h1, fun p => ⟨fun hp => Or.inl (hA p hp), ?_⟩⟩
    rintro (rfl | rfl | rfl | rfl) <;> simpa using h1

end N48

theorem xr_eq_zero_iff {u v : Fin 64} : xr u v = 0 ↔ u = v := by
  refine ⟨fun h => ?_, fun h => by rw [h, xr_self]⟩
  rw [← xr_xr_cancel u v, h, xr_comm, xr_zero]

theorem xr_xr_xr_xr (a b c : Fin 64) : xr (xr (xr (xr a b) c) a) b = c := by
  rw [xr_comm (xr a b) c, xr_assoc, xr_assoc, xr_self, xr_zero]

theorem tim77_card_cases {H : Type} [Group H] [Finite H] {V : Subgroup H} {h : H}
    (hcard : Nat.card V = 64) (hT : Tim77Facts V h) :
    Nat.card (tim77B V h) = Nat.card (tim77D V h) ∧ (∃ x₀ ∈ V, x₀ ∉ tim77B V h) ∧
      (Nat.card (tim77B V h) = 32 ∨ 4 * Nat.card (tim77I V h) ≤ Nat.card (tim77D V h)) := by
  refine ⟨hT.card_eq, IsConcreteLE.exists_of_lt hT.lt_B, ?_⟩
  rcases hT.cases with h2 | h4
  · left
    omega
  · exact Or.inr h4

structure NstarCoord {H : Type} [Group H] (V : Subgroup H) (κ : H → Fin 64)
    (δ : H → Equiv.Perm (Fin 64)) : Prop where
  mul : ∀ x ∈ V, ∀ y ∈ V, κ (x * y) = xr (κ x) (κ y)
  eq_one : ∀ x ∈ V, κ x = 0 → x = 1
  surj : ∀ v, ∃ x ∈ V, κ x = v
  mem_nstar : ∀ d ∈ normalizer (V : Set H), δ d ∈ nstar
  conj : ∀ d ∈ normalizer (V : Set H), ∀ x ∈ V, κ (d * x * d⁻¹) = δ d (κ x)

namespace NstarCoord

variable {H : Type} [Group H] {V : Subgroup H} {κ : H → Fin 64} {δ : H → Equiv.Perm (Fin 64)}
  (hc : NstarCoord V κ δ)
include hc

theorem kappa_one : κ 1 = 0 := by
  have := hc.mul 1 V.one_mem 1 V.one_mem
  rwa [mul_one, xr_self] at this

theorem kappa_inv {x : H} (hx : x ∈ V) : κ x⁻¹ = κ x := by
  have := hc.mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, hc.kappa_one, eq_comm, xr_eq_zero_iff] at this
  exact this.symm

theorem inj {x y : H} (hx : x ∈ V) (hy : y ∈ V) (h : κ x = κ y) : x = y := by
  have h1 := hc.mul x hx y⁻¹ (inv_mem hy)
  rw [hc.kappa_inv hy, h, xr_self] at h1
  exact mul_inv_eq_one.mp (hc.eq_one _ (mul_mem hx (inv_mem hy)) h1)

theorem comm {x y : H} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x :=
  hc.inj (mul_mem hx hy) (mul_mem hy hx) (by rw [hc.mul x hx y hy, hc.mul y hy x hx, xr_comm])

theorem mul_self {x : H} (hx : x ∈ V) : x * x = 1 :=
  hc.eq_one _ (mul_mem hx hx) (by rw [hc.mul x hx x hx, xr_self])

theorem isElemAbelian : IsElemAbelian 2 V :=
  ⟨⟨⟨fun a b => Subtype.ext (hc.comm a.2 b.2)⟩⟩, fun x hx => by rw [sq]; exact hc.mul_self hx⟩

theorem card [Finite H] : Nat.card V = 64 := by
  have hb : Function.Bijective fun x : ↥V => κ x :=
    ⟨fun x y h => Subtype.ext (hc.inj x.2 y.2 h), fun v => by
      obtain ⟨x, hx, rfl⟩ := hc.surj v
      exact ⟨⟨x, hx⟩, rfl⟩⟩
  rw [Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_image {A : Subgroup H} (hA : A ≤ V) : (κ '' (A : Set H)).ncard = Nat.card A := by
  rw [Set.InjOn.ncard_image (fun x hx y hy h => hc.inj (hA hx) (hA hy) h)]
  exact (Nat.card_coe_set_eq (A : Set H)).symm

omit hc in
theorem conj_mem {d x : H} (hd : d ∈ normalizer (V : Set H)) (hx : x ∈ V) : d * x * d⁻¹ ∈ V :=
  (mem_normalizer_iff.mp hd x).mp hx

theorem delta_mul {d e : H} (hd : d ∈ normalizer (V : Set H)) (he : e ∈ normalizer (V : Set H)) :
    δ (d * e) = δ d * δ e := by
  refine Equiv.ext fun v => ?_
  obtain ⟨x, hx, rfl⟩ := hc.surj v
  rw [Equiv.Perm.mul_apply, ← hc.conj _ (mul_mem hd he) x hx, ← hc.conj e he x hx,
    ← hc.conj d hd _ (conj_mem he hx)]
  congr 1
  group

theorem delta_one : δ 1 = 1 := by
  refine Equiv.ext fun v => ?_
  obtain ⟨x, hx, rfl⟩ := hc.surj v
  rw [← hc.conj 1 (one_mem _) x hx, Equiv.Perm.one_apply]
  congr 1
  group

theorem apply_eq_iff {d x : H} (hd : d ∈ normalizer (V : Set H)) (hx : x ∈ V) :
    δ d (κ x) = κ x ↔ d * x * d⁻¹ = x := by
  rw [← hc.conj d hd x hx]
  exact ⟨hc.inj (conj_mem hd hx) hx, fun h => by rw [h]⟩

theorem kappa_comm {x d : H} (hx : x ∈ V) (hd : d ∈ normalizer (V : Set H)) :
    κ (x * d * x⁻¹ * d⁻¹) = xr (κ x) (δ d (κ x)) := by
  rw [show x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) by group,
    hc.mul x hx _ (conj_mem hd (inv_mem hx)), hc.conj d hd _ (inv_mem hx), hc.kappa_inv hx]

section Tim

variable {h : H} (hT : Tim77Facts V h)
include hT

omit hc hT in
theorem tim77D_le_normalizer : tim77D V h ≤ normalizer (V : Set H) := inf_le_right

omit hc in
theorem comm_mem_tim77B {x d : H} (hx : x ∈ V) (hd : d ∈ tim77D V h) :
    x * d * x⁻¹ * d⁻¹ ∈ tim77B V h := by
  have hdM : d ∈ tim77M V h := (le_sup_right : tim77D V h ≤ tim77M V h) hd
  have hxL : x ∈ tim77L V h := (le_sup_left : V ≤ tim77L V h) hx
  have h1 : x * d * x⁻¹ ∈ tim77M V h := (mem_normalizer_iff.mp (hT.normal hxL) d).mp hdM
  have h2 : x * d * x⁻¹ * d⁻¹ ∈ V := by
    rw [show x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) by group]
    exact mul_mem hx ((mem_normalizer_iff.mp ((inf_le_right : tim77D V h ≤ _) hd) x⁻¹).mp
      (inv_mem hx))
  rw [← inf_tim77M]
  exact mem_inf.mpr ⟨h2, mul_mem h1 (inv_mem hdM)⟩

omit hc in
theorem mem_tim77I_of_fix {x d : H} (hd : d ∈ tim77D V h) (hx : x ∈ V) (hxB : x ∉ tim77B V h)
    (hxd : x * d * x⁻¹ * d⁻¹ ∈ tim77I V h) : d ∈ tim77I V h := by
  have hdB := hT.fix x hx hxB d ((le_sup_right : tim77D V h ≤ tim77M V h) hd) hxd
  exact ⟨hdB.1, hd.1⟩

omit hc in
theorem commute_of_mem_tim77I {i l : H} (hi : i ∈ tim77I V h) (hl : l ∈ tim77L V h) :
    l * i * l⁻¹ = i := by
  rw [mem_centralizer_iff.mp (hT.le_center hi) l hl, mul_inv_cancel_right]

theorem fixes_tim77I {d i : H} (hd : d ∈ tim77D V h) (hi : i ∈ tim77I V h) :
    δ d (κ i) = κ i :=
  (hc.apply_eq_iff (tim77D_le_normalizer hd) hi.1).2
    (commute_of_mem_tim77I hT hi ((le_sup_right : rightConjugate V h ≤ tim77L V h) hd.1))

theorem delta_eq_one_iff {x₀ d : H} (hx₀ : x₀ ∈ V) (hx₀B : x₀ ∉ tim77B V h)
    (hd : d ∈ tim77D V h) : δ d = 1 ↔ d ∈ tim77I V h := by
  have hdN := tim77D_le_normalizer hd
  constructor
  · intro h1
    refine mem_tim77I_of_fix hT hd hx₀ hx₀B ?_
    have h2 := (hc.apply_eq_iff hdN hx₀).1 (by rw [h1, Equiv.Perm.one_apply])
    rw [show x₀ * d * x₀⁻¹ * d⁻¹ = x₀ * (d * x₀ * d⁻¹)⁻¹ by group, h2, mul_inv_cancel]
    exact one_mem _
  · intro hdI
    refine Equiv.ext fun v => ?_
    obtain ⟨x, hx, rfl⟩ := hc.surj v
    exact (hc.apply_eq_iff hdN hx).2
      (by
        have := commute_of_mem_tim77I hT hdI ((le_sup_left : V ≤ tim77L V h) hx)
        calc d * x * d⁻¹ = (x * d * x⁻¹) * x * d⁻¹ := by rw [this]
          _ = x := by group)

end Tim

theorem not_tim77 [Finite H] (hF : N48.Facts) (h : H) : ¬ Tim77Facts V h := by
  intro hT
  have hV := hc.isElemAbelian
  obtain ⟨hBD, ⟨x₀, hx₀, hx₀B⟩, hcase⟩ := tim77_card_cases hc.card hT
  have hDN : ∀ d ∈ tim77D V h, d ∈ normalizer (V : Set H) := fun d hd => tim77D_le_normalizer hd
  have hPN : δ '' (tim77D V h : Set H) ⊆ nstar := by
    rintro _ ⟨d, hd, rfl⟩
    exact hc.mem_nstar d (hDN d hd)
  have hP1 : (1 : Equiv.Perm (Fin 64)) ∈ δ '' (tim77D V h : Set H) :=
    ⟨1, one_mem _, hc.delta_one⟩
  have hPmul : ∀ a ∈ δ '' (tim77D V h : Set H), ∀ b ∈ δ '' (tim77D V h : Set H),
      a * b ∈ δ '' (tim77D V h : Set H) := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    exact ⟨d * e, mul_mem hd he, hc.delta_mul (hDN d hd) (hDN e he)⟩
  have hPsq : ∀ a ∈ δ '' (tim77D V h : Set H), a * a = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← hc.delta_mul (hDN d hd) (hDN d hd),
      mul_self_eq_one_of_mem_rightConjugate hV (mem_inf.mp hd).1, hc.delta_one]
  have hPcomm : ∀ a ∈ δ '' (tim77D V h : Set H), ∀ b ∈ δ '' (tim77D V h : Set H),
      a * b = b * a := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    rw [← hc.delta_mul (hDN d hd) (hDN e he), ← hc.delta_mul (hDN e he) (hDN d hd),
      commute_of_mem_rightConjugate hV (mem_inf.mp hd).1 (mem_inf.mp he).1]
  obtain ⟨α, hα, β, hβ, hPiff⟩ := hF.exists_pair hPN hP1 hPmul hPsq hPcomm
  have hαα := hPsq α hα
  have hββ := hPsq β hβ
  have hαβ := hPcomm α hα β hβ
  have hPmem : ∀ d ∈ tim77D V h, δ d ∈ ({1, α, β, α * β} : Set (Equiv.Perm (Fin 64))) :=
    fun d hd => (hPiff (δ d)).1 ⟨d, hd, rfl⟩
  obtain ⟨d₁, hd₁, hd₁α⟩ := id hα
  obtain ⟨d₂, hd₂, hd₂β⟩ := id hβ
  have hIC : ∀ i ∈ tim77I V h, κ i ∈ fixS α β := fun i hi =>
    ⟨by rw [← hd₁α]; exact hc.fixes_tim77I hT hd₁ hi,
      by rw [← hd₂β]; exact hc.fixes_tim77I hT hd₂ hi⟩
  have hone : ∀ d ∈ tim77D V h, δ d = 1 ↔ d ∈ tim77I V h := fun d hd =>
    hc.delta_eq_one_iff hT hx₀ hx₀B hd
  have hsurj := exists_mem_of_inj_mod tim77I_le_tim77B tim77I_le_tim77D
    (fun d => x₀ * d * x₀⁻¹ * d⁻¹) (fun d hd => comm_mem_tim77B hT hx₀ hd)
    (fun d hd e he => by
      have := inv_mem (comm_tim77B_tim77D (comm_mem_tim77B hT hx₀ he) hd)
      convert this using 1
      group)
    (fun i hi => by
      show x₀ * i * x₀⁻¹ * i⁻¹ ∈ tim77I V h
      rw [commute_of_mem_tim77I hT hi ((le_sup_left : V ≤ tim77L V h) hx₀), mul_inv_cancel]
      exact one_mem _)
    (fun d hd hdI => mem_tim77I_of_fix hT hd hx₀ hx₀B hdI) hBD.le
  have hBS : κ '' (tim77B V h : Set H) ⊆ spanS α β := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨d, hd, hj⟩ := hsurj b hb
    have hcm := comm_mem_tim77B hT hx₀ hd
    have hbj : b = (x₀ * d * x₀⁻¹ * d⁻¹) * ((x₀ * d * x₀⁻¹ * d⁻¹)⁻¹ * b) := by group
    refine ⟨κ x₀, δ d, hPmem d hd, ?_⟩
    rw [hbj, hc.mul _ (mem_inf.mp hcm).1 _ (mem_inf.mp hj).1, hc.kappa_comm hx₀ (hDN d hd),
      xr_xr_xr_xr]
    exact hIC _ hj
  have hBV : tim77B V h ≤ V := inf_le_left
  have hcardB : Nat.card (tim77B V h) ≤ (spanS α β).ncard := by
    rw [← hc.ncard_image hBV]
    exact Set.ncard_le_ncard hBS (Set.toFinite _)
  have hne : ¬ (α = 1 ∧ β = 1) := by
    rintro ⟨rfl, rfl⟩
    refine hT.lt_D.not_ge fun d hd => (hone d hd).1 ?_
    rcases hPmem d hd with h1 | h1 | h1 | h1
    · exact h1
    · exact h1
    · exact h1
    · exact h1.trans (mul_one 1)
  have hS16 := hF.span α (hPN hα) β (hPN hβ) hαα hββ hαβ hne
  rcases hcase with h32 | h4
  · omega
  let δD : ↥(tim77D V h) →* Equiv.Perm (Fin 64) :=
    { toFun := fun d => δ d
      map_one' := hc.delta_one
      map_mul' := fun d e => hc.delta_mul (hDN d d.2) (hDN e e.2) }
  have hker : δD.ker = (tim77I V h).subgroupOf (tim77D V h) := by
    ext d
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact hone d d.2
  have hrange : Nat.card δD.range = (δ '' (tim77D V h : Set H)).ncard := by
    have e : (δD.range : Set (Equiv.Perm (Fin 64))) = δ '' (tim77D V h : Set H) := by
      ext p
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨d, d.2, rfl⟩
      · rintro ⟨d, hd, rfl⟩
        exact ⟨⟨d, hd⟩, rfl⟩
    rw [← e]
    exact Nat.card_coe_set_eq _
  have hDc : Nat.card (tim77D V h) =
      (δ '' (tim77D V h : Set H)).ncard * Nat.card (tim77I V h) := by
    rw [card_eq_card_quotient_mul_card_subgroup δD.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange δD).toEquiv, hker, hrange,
      Nat.card_congr (subgroupOfEquivOfLe tim77I_le_tim77D).toEquiv]
  have hPeq : δ '' (tim77D V h : Set H) = ({1, α, β, α * β} : Set (Equiv.Perm (Fin 64))) :=
    Set.ext hPiff
  have hP4 : 4 ≤ (δ '' (tim77D V h : Set H)).ncard := by
    have : 4 * Nat.card (tim77I V h) ≤ (δ '' (tim77D V h : Set H)).ncard * Nat.card (tim77I V h) :=
      by rw [← hDc]; exact h4
    exact Nat.le_of_mul_le_mul_right this Nat.card_pos
  have hle2 : ∀ a b : Equiv.Perm (Fin 64), (∀ p ∈ δ '' (tim77D V h : Set H), p = a ∨ p = b) →
      False := fun a b hab => by
    have : (δ '' (tim77D V h : Set H)).ncard ≤ 2 :=
      calc (δ '' (tim77D V h : Set H)).ncard ≤ ({a, b} : Set (Equiv.Perm (Fin 64))).ncard :=
            Set.ncard_le_ncard (fun p hp => hab p hp) (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton])
    omega
  have hα1 : α ≠ 1 := by
    rintro rfl
    refine hle2 1 β fun p hp => ?_
    rcases (hPiff p).1 hp with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact Or.inr (h1.trans (one_mul β))
  have hβ1 : β ≠ 1 := by
    rintro rfl
    refine hle2 1 α fun p hp => ?_
    rcases (hPiff p).1 hp with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans (mul_one α))
  have hαβ' : α ≠ β := by
    rintro rfl
    refine hle2 1 α fun p hp => ?_
    rcases (hPiff p).1 hp with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact Or.inr h1
    · exact Or.inl (h1.trans hαα)
  have hτmem : ∀ τ ∈ ({α, β, α * β} : Set (Equiv.Perm (Fin 64))),
      τ ≠ 1 ∧ τ ∈ δ '' (tim77D V h : Set H) := by
    rintro τ (rfl | rfl | rfl)
    · exact ⟨hα1, hα⟩
    · exact ⟨hβ1, hβ⟩
    · exact ⟨fun h1 => hαβ' (mul_left_cancel (hαα.trans h1.symm)), hPmul _ hα _ hβ⟩
  obtain ⟨⟨τ, hτ, h16⟩, hrest⟩ := hF.four α (hPN hα) β (hPN hβ) hαα hββ hαβ hα1 hβ1 hαβ'
  obtain ⟨hτ1, d, hd, rfl⟩ := hτmem τ hτ
  have hdI : d ∉ tim77I V h := fun hI => hτ1 ((hone d hd).2 hI)
  have hfixB : fixS (δ d) (δ d) ⊆ κ '' (tim77B V h : Set H) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hc.surj v
    refine ⟨x, ?_, rfl⟩
    by_contra hxB
    refine hdI (mem_tim77I_of_fix hT hd hx hxB ?_)
    rw [show x * d * x⁻¹ * d⁻¹ = x * (d * x * d⁻¹)⁻¹ by group,
      (hc.apply_eq_iff (hDN d hd) hx).1 hv.1, mul_inv_cancel]
    exact one_mem _
  have h16B : 16 ≤ Nat.card (tim77B V h) := by
    rw [← hc.ncard_image hBV]
    exact h16.trans (Set.ncard_le_ncard hfixB (Set.toFinite _))
  have hBeq : κ '' (tim77B V h : Set H) = spanS α β :=
    Set.eq_of_subset_of_ncard_le hBS (by rw [hc.ncard_image hBV]; omega) (Set.toFinite _)
  obtain ⟨hC4, x', hx'S, τ', hτ', hx'C⟩ := hrest (by omega)
  have hP4' : (δ '' (tim77D V h : Set H)).ncard ≤ 4 := by
    rw [hPeq]
    refine (Set.ncard_insert_le _ _).trans ?_
    refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
    rw [Set.ncard_singleton]
  have hI4 : Nat.card (tim77I V h) = 4 := by
    have h1 : (δ '' (tim77D V h : Set H)).ncard = 4 := le_antisymm hP4' hP4
    rw [h1, ← hBD] at hDc
    omega
  have hIV : tim77I V h ≤ V := inf_le_left
  have hIeq : κ '' (tim77I V h : Set H) = fixS α β :=
    Set.eq_of_subset_of_ncard_le (by rintro _ ⟨i, hi, rfl⟩; exact hIC i hi)
      (by rw [hc.ncard_image hIV]; omega) (Set.toFinite _)
  obtain ⟨x, hx, rfl⟩ := hc.surj x'
  have hxB : x ∉ tim77B V h := fun hB => hx'S (hBeq ▸ ⟨x, hB, rfl⟩)
  obtain ⟨hτ'1, d', hd', rfl⟩ := hτmem τ' hτ'
  have hd'I : d' ∉ tim77I V h := fun hI => hτ'1 ((hone d' hd').2 hI)
  refine hd'I (mem_tim77I_of_fix hT hd' hx hxB ?_)
  have hcm := comm_mem_tim77B hT hx hd'
  rw [← hc.kappa_comm hx (hDN d' hd'), ← hIeq] at hx'C
  obtain ⟨i, hi, he⟩ := hx'C
  rw [← hc.inj (mem_inf.mp hi).1 (mem_inf.mp hcm).1 he]
  exact hi

end NstarCoord

end CFSG.ComponentClassification.AS81
