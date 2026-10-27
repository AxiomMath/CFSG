module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.A5Aut

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup

open scoped Pointwise

variable {K : Type*} [Group K]

@[expose] def centerIn (E : Subgroup K) : Subgroup K := E ⊓ centralizer (E : Set K)

private theorem twist_mul (w a b : K)
    (hc : a⁻¹ * (w * a * w⁻¹) * b⁻¹ = b⁻¹ * (a⁻¹ * (w * a * w⁻¹))) :
    (a * b)⁻¹ * (w * (a * b) * w⁻¹) = (a⁻¹ * (w * a * w⁻¹)) * (b⁻¹ * (w * b * w⁻¹)) := by
  calc (a * b)⁻¹ * (w * (a * b) * w⁻¹)
      = b⁻¹ * (a⁻¹ * (w * a * w⁻¹)) * (w * b * w⁻¹) := by group
    _ = (a⁻¹ * (w * a * w⁻¹)) * b⁻¹ * (w * b * w⁻¹) := by rw [← hc]
    _ = (a⁻¹ * (w * a * w⁻¹)) * (b⁻¹ * (w * b * w⁻¹)) := by group

private theorem twist_inv (w a : K)
    (hc : a * (a⁻¹ * (w * a * w⁻¹))⁻¹ = (a⁻¹ * (w * a * w⁻¹))⁻¹ * a) :
    (a⁻¹)⁻¹ * (w * a⁻¹ * w⁻¹) = (a⁻¹ * (w * a * w⁻¹))⁻¹ := by
  calc (a⁻¹)⁻¹ * (w * a⁻¹ * w⁻¹)
      = (a * (a⁻¹ * (w * a * w⁻¹))⁻¹) * a⁻¹ := by group
    _ = ((a⁻¹ * (w * a * w⁻¹))⁻¹ * a) * a⁻¹ := by rw [hc]
    _ = (a⁻¹ * (w * a * w⁻¹))⁻¹ := by group

@[expose] def twistFix (w : K) (E : Subgroup K) : Subgroup K where
  carrier := {g | g ∈ E ∧ g⁻¹ * (w * g * w⁻¹) ∈ centerIn E}
  mul_mem' := by
    rintro a b ⟨haE, ha⟩ ⟨hbE, hb⟩
    refine ⟨E.mul_mem haE hbE, ?_⟩
    rw [twist_mul w a b (mem_centralizer_iff.1 ha.2 b⁻¹ (E.inv_mem hbE)).symm]
    exact (centerIn E).mul_mem ha hb
  one_mem' := ⟨E.one_mem, by simpa using (centerIn E).one_mem⟩
  inv_mem' := by
    rintro a ⟨haE, ha⟩
    refine ⟨E.inv_mem haE, ?_⟩
    rw [twist_inv w a (mem_centralizer_iff.1 ((centerIn E).inv_mem ha).2 a haE)]
    exact (centerIn E).inv_mem ha

theorem mem_twistFix {w : K} {E : Subgroup K} {g : K} :
    g ∈ twistFix w E ↔ g ∈ E ∧ g⁻¹ * (w * g * w⁻¹) ∈ centerIn E := Iff.rfl

theorem twistFix_le (w : K) (E : Subgroup K) : twistFix w E ≤ E := fun _ hg => hg.1

theorem centerIn_le (E : Subgroup K) : centerIn E ≤ E := inf_le_left

theorem card_le_card_mul_card_inf_centralizer [Finite K] {Q Z : Subgroup K} {w : K}
    (hZ : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    (hρ : ∀ q ∈ Q, q⁻¹ * (w * q * w⁻¹) ∈ Z) :
    Nat.card Q ≤ Nat.card Z * Nat.card ↥(Q ⊓ centralizer ({w} : Set K)) := by
  classical
  let f : Q →* Z :=
    { toFun := fun q => ⟨q⁻¹ * (w * q * w⁻¹), hρ q q.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a : K) * (b : K))⁻¹ * (w * ((a : K) * (b : K)) * w⁻¹) =
          ((a : K)⁻¹ * (w * (a : K) * w⁻¹)) * ((b : K)⁻¹ * (w * (b : K) * w⁻¹))
        exact twist_mul w (a : K) (b : K) (hZ _ (hρ a a.2) _ (Q.inv_mem b.2)) }
  have hker : f.ker = (Q ⊓ centralizer ({w} : Set K)).subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hq
      have hq' : (q : K)⁻¹ * (w * (q : K) * w⁻¹) = 1 := by
        have := congrArg (fun x : Z => (x : K)) hq
        simpa [f] using this
      have h2 : w * (q : K) * w⁻¹ = (q : K) := by
        have := congrArg (fun x : K => (q : K) * x) hq'
        simpa [mul_assoc] using this
      have h3 : w * (q : K) = (q : K) * w := by
        calc w * (q : K) = (w * (q : K) * w⁻¹) * w := by group
          _ = (q : K) * w := by rw [h2]
      exact ⟨q.2, Subgroup.mem_centralizer_singleton_iff.2 h3.symm⟩
    · rintro ⟨-, hqw⟩
      apply Subtype.ext
      show (q : K)⁻¹ * (w * (q : K) * w⁻¹) = (1 : K)
      rw [Subgroup.mem_centralizer_singleton_iff] at hqw
      have h2 : w * (q : K) * w⁻¹ = (q : K) := by
        rw [← hqw]
        group
      rw [h2]
      group
  have hcardker : Nat.card f.ker = Nat.card ↥(Q ⊓ centralizer ({w} : Set K)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ⊓ centralizer
      ({w} : Set K) ≤ Q)).toEquiv
  have hrange : Nat.card f.range ≤ Nat.card Z := by
    have h := Subgroup.card_le_of_le (le_top : f.range ≤ (⊤ : Subgroup Z))
    rwa [Subgroup.card_top] at h
  calc Nat.card Q = Nat.card f.ker * Nat.card f.range :=
        (Subgroup.card_ker_mul_card_range f).symm
    _ = Nat.card ↥(Q ⊓ centralizer ({w} : Set K)) * Nat.card f.range := by rw [hcardker]
    _ ≤ Nat.card ↥(Q ⊓ centralizer ({w} : Set K)) * Nat.card Z :=
        Nat.mul_le_mul_left _ hrange
    _ = Nat.card Z * Nat.card ↥(Q ⊓ centralizer ({w} : Set K)) := by ring

private theorem conj_conj {w x : K} (hw : w * w = 1) : w * (w * x * w⁻¹) * w⁻¹ = x := by
  have h1 : w⁻¹ * w⁻¹ = 1 := by
    rw [← mul_inv_rev, hw, inv_one]
  calc w * (w * x * w⁻¹) * w⁻¹
      = (w * w) * x * (w⁻¹ * w⁻¹) := by group
    _ = x := by rw [hw, h1, one_mul, mul_one]

private theorem mem_centerIn_iff_center {E : Subgroup K} {x : K} (hx : x ∈ E) :
    x ∈ centerIn E ↔ (⟨x, hx⟩ : ↥E) ∈ Subgroup.center ↥E := by
  change x ∈ E ⊓ Subgroup.centralizer (E : Set K) ↔ _
  rw [CFSG.GroupTheory.inf_centralizer_eq_map_center E, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, hcx⟩
    have hc' : c = ⟨x, hx⟩ := Subtype.ext hcx
    rwa [hc'] at hc
  · rintro hx'
    exact ⟨⟨x, hx⟩, hx', rfl⟩

private theorem mem_centerIn_iff_center' {E : Subgroup K} (x : ↥E) :
    (x : K) ∈ centerIn E ↔ x ∈ Subgroup.center ↥E :=
  mem_centerIn_iff_center x.2

theorem four_mul_card_centerIn_le_card_twistFix [Finite K] {w : K} (hw : w * w = 1)
    {E : Subgroup K} (hnorm : ∀ g ∈ E, w * g * w⁻¹ ∈ E)
    (e : (↥E ⧸ center ↥E) ≃* alternatingGroup (Fin 5)) :
    4 * Nat.card (centerIn E) ≤ Nat.card (twistFix w E) := by
  classical
  let φHom : ↥E →* ↥E :=
    { toFun := fun y => ⟨w * (y : K) * w⁻¹, hnorm y y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show w * ((a : K) * (b : K)) * w⁻¹ =
          (w * (a : K) * w⁻¹) * (w * (b : K) * w⁻¹)
        group }
  have hφHom : ∀ y : ↥E, φHom (φHom y) = y := by
    intro y
    apply Subtype.ext
    show w * (w * (y : K) * w⁻¹) * w⁻¹ = (y : K)
    exact conj_conj (x := (y : K)) hw
  have hφbij : Function.Bijective φHom :=
    ⟨fun x y hxy => by
      calc x = φHom (φHom x) := (hφHom x).symm
        _ = φHom (φHom y) := by rw [hxy]
        _ = y := hφHom y,
     fun y => ⟨φHom y, hφHom y⟩⟩
  let φ : ↥E ≃* ↥E := MulEquiv.ofBijective φHom hφbij
  have hφφ : ∀ y : ↥E, φ (φ y) = y := by
    intro y
    change φHom (φHom y) = y
    exact hφHom y
  have hφ_apply : ∀ y : ↥E, (φ y : K) = w * (y : K) * w⁻¹ := fun _ => rfl
  have hmap : (Subgroup.center ↥E).map (φ : ↥E →* ↥E) = Subgroup.center ↥E :=
    Subgroup.map_center_eq φ
  let α : (↥E ⧸ Subgroup.center ↥E) ≃* (↥E ⧸ Subgroup.center ↥E) :=
    QuotientGroup.congr _ _ φ hmap
  have hαmk : ∀ y : ↥E, α (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := by
    intro y
    simp [α]
  have hα : ∀ x, α (α x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hαmk y, hαmk (φ y), hφφ y]
  have hfix := CFSG.EvenSporadicStandard.M12Std.PropA.card_fixedPoints_of_alt5 e α hα
  let Fix : Set (↥E ⧸ Subgroup.center ↥E) := {x | α x = x}
  have hfix4 : 4 ≤ Nat.card ↥Fix := by
    rcases hfix with h | h | h
    · exact h.ge
    · exact (show 4 ≤ 6 by norm_num).trans h.ge
    · exact (show 4 ≤ 60 by norm_num).trans h.ge
  have hcardZ : Nat.card (centerIn E) = Nat.card (Subgroup.center ↥E) := by
    change Nat.card ↥(E ⊓ Subgroup.centralizer (E : Set K)) = Nat.card ↥(Subgroup.center ↥E)
    rw [CFSG.GroupTheory.inf_centralizer_eq_map_center E]
    exact Subgroup.card_map_of_injective E.subtype_injective
  have hiff : ∀ y : ↥E, ((y : K) ∈ twistFix w E) ↔
      y⁻¹ * φ y ∈ Subgroup.center ↥E := by
    intro y
    rw [mem_twistFix]
    constructor
    · rintro ⟨-, hy⟩
      have hx : ((y⁻¹ * φ y : ↥E) : K) ∈ centerIn E := by
        simpa [hφ_apply y] using hy
      exact (mem_centerIn_iff_center' (y⁻¹ * φ y)).1 hx
    · intro hy
      refine ⟨y.2, ?_⟩
      have hx := (mem_centerIn_iff_center' (y⁻¹ * φ y)).2 hy
      simpa [hφ_apply y] using hx
  have hcardQ : Nat.card (twistFix w E) = Nat.card ↥(QuotientGroup.mk ⁻¹' Fix) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun g => ⟨⟨g.1, g.2.1⟩, ?_⟩
        invFun := fun x => ⟨x.1.1, ?_⟩
        left_inv := fun g => Subtype.ext rfl
        right_inv := fun x => Subtype.ext (Subtype.ext rfl) }
    · change α (QuotientGroup.mk (⟨g.1, g.2.1⟩ : ↥E)) =
        QuotientGroup.mk (⟨g.1, g.2.1⟩ : ↥E)
      have hyZ : (⟨g.1, g.2.1⟩ : ↥E)⁻¹ * φ ⟨g.1, g.2.1⟩ ∈ Subgroup.center ↥E :=
        (hiff ⟨g.1, g.2.1⟩).1 g.2
      rw [hαmk ⟨g.1, g.2.1⟩]
      exact QuotientGroup.eq.2 (by simpa using (Subgroup.center ↥E).inv_mem hyZ)
    · have hx2 : α (QuotientGroup.mk x.1) = QuotientGroup.mk x.1 := x.2
      rw [hαmk x.1] at hx2
      have hfixed : (φ x.1)⁻¹ * x.1 ∈ Subgroup.center ↥E := QuotientGroup.eq.1 hx2
      have hxZ : x.1⁻¹ * φ x.1 ∈ Subgroup.center ↥E := by
        simpa using (Subgroup.center ↥E).inv_mem hfixed
      exact (hiff x.1).2 hxZ
  have hpre : Nat.card ↥(QuotientGroup.mk ⁻¹' Fix) =
      Nat.card (Subgroup.center ↥E) * Nat.card ↥Fix :=
    QuotientGroup.card_preimage_mk (Subgroup.center ↥E) Fix
  calc 4 * Nat.card (centerIn E)
      = 4 * Nat.card (Subgroup.center ↥E) := by rw [hcardZ]
    _ ≤ Nat.card ↥Fix * Nat.card (Subgroup.center ↥E) := Nat.mul_le_mul_right _ hfix4
    _ = Nat.card (Subgroup.center ↥E) * Nat.card ↥Fix := by ring
    _ = Nat.card ↥(QuotientGroup.mk ⁻¹' Fix) := hpre.symm
    _ = Nat.card (twistFix w E) := hcardQ.symm

theorem card_mul_card_twistFix_le [Finite K] {w : K} (hw : w * w = 1) {E₁ E₂ : Subgroup K}
    (hn₁ : ∀ g ∈ E₁, w * g * w⁻¹ ∈ E₁) (hn₂ : ∀ g ∈ E₂, w * g * w⁻¹ ∈ E₂)
    (hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) :
    Nat.card (twistFix w E₁) * Nat.card (twistFix w E₂) ≤
      Nat.card (centerIn E₁) * Nat.card (centerIn E₂) * Nat.card (centralizer ({w} : Set K)) := by
  classical
  let Q₁ : Subgroup K := twistFix w E₁
  let Q₂ : Subgroup K := twistFix w E₂
  let Z₁ : Subgroup K := centerIn E₁
  let Z₂ : Subgroup K := centerIn E₂
  have hQ12 : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x :=
    fun x hx y hy => hc x (twistFix_le w E₁ hx) y (twistFix_le w E₂ hy)
  have hZ12 : ∀ x ∈ Z₁, ∀ y ∈ Z₂, x * y = y * x :=
    fun x hx y hy => hc x (centerIn_le E₁ hx) y (centerIn_le E₂ hy)
  have hQcomm := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q₁ Q₂ hQ12
  have hZcomm := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z₁ Z₂ hZ12
  have hQset : ((Q₁ ⊔ Q₂ : Subgroup K) : Set K) = (Q₁ : Set K) * (Q₂ : Set K) := hQcomm.2
  have hZset : ((Z₁ ⊔ Z₂ : Subgroup K) : Set K) = (Z₁ : Set K) * (Z₂ : Set K) := hZcomm.2
  have hZ : ∀ z ∈ Z₁ ⊔ Z₂, ∀ q ∈ Q₁ ⊔ Q₂, z * q = q * z := by
    intro z hz q hq
    have hz' : z ∈ (Z₁ : Set K) * (Z₂ : Set K) := by
      rw [← hZset]
      exact hz
    obtain ⟨z₁, hz₁, z₂, hz₂, hzeq⟩ := hz'
    subst hzeq
    have hcz₁ : Commute z₁ q := by
      have hle : Q₁ ⊔ Q₂ ≤ Subgroup.centralizer ({z₁} : Set K) :=
        sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 hz₁.2 a ((twistFix_le w E₁) ha)))
          (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
            ((hc z₁ (centerIn_le E₁ hz₁) b ((twistFix_le w E₂) hb)).symm))
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hq)).symm
    have hcz₂ : Commute z₂ q := by
      have hle : Q₁ ⊔ Q₂ ≤ Subgroup.centralizer ({z₂} : Set K) :=
        sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2
            (hc a ((twistFix_le w E₁) ha) z₂ (centerIn_le E₂ hz₂)))
          (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 hz₂.2 b ((twistFix_le w E₂) hb)))
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hq)).symm
    exact (hcz₁.mul_left hcz₂).eq
  have hρ : ∀ q ∈ Q₁ ⊔ Q₂, q⁻¹ * (w * q * w⁻¹) ∈ Z₁ ⊔ Z₂ := by
    intro q hq
    have hq' : q ∈ (Q₁ : Set K) * (Q₂ : Set K) := by
      rw [← hQset]
      exact hq
    obtain ⟨q₁, hq₁, q₂, hq₂, hqeq⟩ := hq'
    subst hqeq
    have hzq₁ : q₁⁻¹ * (w * q₁ * w⁻¹) ∈ Z₁ := (mem_twistFix.1 hq₁).2
    have hzq₂ : q₂⁻¹ * (w * q₂ * w⁻¹) ∈ Z₂ := (mem_twistFix.1 hq₂).2
    rw [twist_mul w q₁ q₂ (hc _ (centerIn_le E₁ hzq₁) _
      ((twistFix_le w E₂) (Q₂.inv_mem hq₂)))]
    exact mul_mem (Subgroup.mem_sup_left hzq₁) (Subgroup.mem_sup_right hzq₂)
  have hmain : Nat.card ↥(Q₁ ⊔ Q₂) ≤
      Nat.card ↥(Z₁ ⊔ Z₂) * Nat.card ↥((Q₁ ⊔ Q₂) ⊓ centralizer ({w} : Set K)) :=
    card_le_card_mul_card_inf_centralizer hZ hρ
  have hleC : Nat.card ↥((Q₁ ⊔ Q₂) ⊓ centralizer ({w} : Set K)) ≤
      Nat.card (centralizer ({w} : Set K)) :=
    Subgroup.card_le_of_le inf_le_right
  have hinf : Q₁ ⊓ Q₂ ≤ Z₁ ⊓ Z₂ := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.2 ⟨(twistFix_le w E₁) hx1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hc g hg x ((twistFix_le w E₂) hx2)
    · refine Subgroup.mem_inf.2 ⟨(twistFix_le w E₂) hx2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (hc x ((twistFix_le w E₁) hx1) g hg).symm
  have hinfcard : Nat.card ↥(Q₁ ⊓ Q₂) ≤ Nat.card ↥(Z₁ ⊓ Z₂) :=
    Subgroup.card_le_of_le hinf
  calc Nat.card Q₁ * Nat.card Q₂
      = Nat.card ↥(Q₁ ⊔ Q₂) * Nat.card ↥(Q₁ ⊓ Q₂) := hQcomm.1.symm
    _ ≤ Nat.card ↥(Q₁ ⊔ Q₂) * Nat.card ↥(Z₁ ⊓ Z₂) := Nat.mul_le_mul_left _ hinfcard
    _ ≤ (Nat.card ↥(Z₁ ⊔ Z₂) * Nat.card (centralizer ({w} : Set K))) *
          Nat.card ↥(Z₁ ⊓ Z₂) :=
        Nat.mul_le_mul_right _ (hmain.trans (Nat.mul_le_mul_left _ hleC))
    _ = Nat.card ↥(Z₁ ⊔ Z₂) * Nat.card ↥(Z₁ ⊓ Z₂) *
          Nat.card (centralizer ({w} : Set K)) := by ring
    _ = Nat.card Z₁ * Nat.card Z₂ * Nat.card (centralizer ({w} : Set K)) := by
        rw [hZcomm.1]

theorem sixteen_le_card_centralizer_of_alt5_pair [Finite K] {w : K} (hw : w * w = 1)
    {E₁ E₂ : Subgroup K} (hn₁ : ∀ g ∈ E₁, w * g * w⁻¹ ∈ E₁) (hn₂ : ∀ g ∈ E₂, w * g * w⁻¹ ∈ E₂)
    (hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a)
    (e₁ : (↥E₁ ⧸ center ↥E₁) ≃* alternatingGroup (Fin 5))
    (e₂ : (↥E₂ ⧸ center ↥E₂) ≃* alternatingGroup (Fin 5)) :
    16 ≤ Nat.card (centralizer ({w} : Set K)) := by
  have h1 := four_mul_card_centerIn_le_card_twistFix hw hn₁ e₁
  have h2 := four_mul_card_centerIn_le_card_twistFix hw hn₂ e₂
  have h3 := card_mul_card_twistFix_le hw hn₁ hn₂ hc
  have hpos₁ : 0 < Nat.card (centerIn E₁) := Nat.card_pos
  have hpos₂ : 0 < Nat.card (centerIn E₂) := Nat.card_pos
  have h4 : 16 * (Nat.card (centerIn E₁) * Nat.card (centerIn E₂)) ≤
      Nat.card (twistFix w E₁) * Nat.card (twistFix w E₂) := by
    calc 16 * (Nat.card (centerIn E₁) * Nat.card (centerIn E₂))
        = (4 * Nat.card (centerIn E₁)) * (4 * Nat.card (centerIn E₂)) := by ring
      _ ≤ _ := Nat.mul_le_mul h1 h2
  have h5 : (Nat.card (centerIn E₁) * Nat.card (centerIn E₂)) * 16 ≤
      (Nat.card (centerIn E₁) * Nat.card (centerIn E₂)) * Nat.card (centralizer ({w} : Set K)) :=
    by rw [mul_comm _ 16]; exact h4.trans h3
  exact Nat.le_of_mul_le_mul_left h5 (Nat.mul_pos hpos₁ hpos₂)

end CFSG.EvenSporadicStandard.M12Std.Rbc
