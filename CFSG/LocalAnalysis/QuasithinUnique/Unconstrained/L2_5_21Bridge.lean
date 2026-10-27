module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21DS
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

structure SBar {G : Type} [Group G] (S A : Subgroup G) {P : Type} [Group P] [Finite P]
    (π : G → P) (R : Subgroup P) : Prop where
  mul : ∀ a ∈ S, ∀ b ∈ S, π (a * b) = π a * π b
  surj : ∀ p : P, ∃ s ∈ S, π s = p
  ker : ∀ s ∈ S, π s = 1 ↔ s ∈ A
  ds : DS.DSData R

namespace SBar

variable {G : Type} [Group G] {S A : Subgroup G} {P : Type} [Group P] [Finite P] {π : G → P}
  {R : Subgroup P}

theorem pi_one (h : SBar S A π R) : π 1 = 1 := by
  have h1 := h.mul 1 S.one_mem 1 S.one_mem
  rw [mul_one] at h1
  simpa using h1

theorem pi_inv (h : SBar S A π R) {a : G} (ha : a ∈ S) : π a⁻¹ = (π a)⁻¹ := by
  have h1 := h.mul a⁻¹ (S.inv_mem ha) a ha
  rw [inv_mul_cancel, h.pi_one] at h1
  exact (inv_eq_of_mul_eq_one_left h1.symm).symm

theorem pi_eq_iff (h : SBar S A π R) {a b : G} (ha : a ∈ S) (hb : b ∈ S) :
    π a = π b ↔ a⁻¹ * b ∈ A := by
  rw [← h.ker _ (S.mul_mem (S.inv_mem ha) hb), h.mul _ (S.inv_mem ha) _ hb, h.pi_inv ha]
  constructor
  · intro hab; rw [hab]; simp
  · intro h1; exact (inv_mul_eq_one.mp h1)

theorem pi_pow (h : SBar S A π R) {a : G} (ha : a ∈ S) (n : ℕ) : π (a ^ n) = (π a) ^ n := by
  induction n with
  | zero => simpa using h.pi_one
  | succ n ih => rw [pow_succ, h.mul _ (S.pow_mem ha n) _ ha, ih, pow_succ]

@[expose] noncomputable def hom (h : SBar S A π R) : ↥S →* P where
  toFun s := π s
  map_one' := h.pi_one
  map_mul' a b := h.mul a a.2 b b.2

@[simp] theorem hom_apply (h : SBar S A π R) (s : ↥S) : h.hom s = π s := rfl

@[expose] noncomputable def img (h : SBar S A π R) (X : Subgroup G) : Subgroup P :=
  (X.subgroupOf S).map h.hom

theorem mem_img (h : SBar S A π R) {X : Subgroup G} {p : P} :
    p ∈ h.img X ↔ ∃ x, x ∈ X ∧ x ∈ S ∧ π x = p := by
  unfold img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, y.2, rfl⟩
  · rintro ⟨x, hxX, hxS, rfl⟩
    exact ⟨⟨x, hxS⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩

theorem pi_mem_img (h : SBar S A π R) {X : Subgroup G} {x : G} (hx : x ∈ X) (hxS : x ∈ S) :
    π x ∈ h.img X := h.mem_img.mpr ⟨x, hx, hxS, rfl⟩

theorem card_img (h : SBar S A π R) {X : Subgroup G} (hXS : X ≤ S) (hXA : X ⊓ A = ⊥) :
    Nat.card (h.img X) = Nat.card X := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun x : ↥X => (⟨π x, h.pi_mem_img x.2 (hXS x.2)⟩ : ↥(h.img X))) ⟨?_, ?_⟩
  · intro x y hxy
    have hxy' : π (x : G) = π (y : G) := congrArg Subtype.val hxy
    have h1 := (h.pi_eq_iff (hXS x.2) (hXS y.2)).mp hxy'
    have h2 : (x : G)⁻¹ * y ∈ X ⊓ A := ⟨X.mul_mem (X.inv_mem x.2) y.2, h1⟩
    rw [hXA, Subgroup.mem_bot] at h2
    apply Subtype.ext
    exact (inv_mul_eq_one.mp h2)
  · rintro ⟨p, hp⟩
    obtain ⟨x, hxX, hxS, rfl⟩ := h.mem_img.mp hp
    exact ⟨⟨x, hxX⟩, rfl⟩

@[expose] noncomputable def Rt (h : SBar S A π R) : Subgroup G := (R.comap h.hom).map S.subtype

theorem mem_Rt (h : SBar S A π R) {g : G} : g ∈ h.Rt ↔ g ∈ S ∧ π g ∈ R := by
  unfold Rt
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hgS, hgR⟩
    exact ⟨⟨g, hgS⟩, hgR, rfl⟩

theorem _root_.CFSG.QuasithinUnique.IsFourSubgroup.comm {E : Subgroup G} (hE : IsFourSubgroup E)
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  have := hE.1.1
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥E)).comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem _root_.CFSG.QuasithinUnique.IsFourSubgroup.sq {E : Subgroup G} (hE : IsFourSubgroup E)
    {x : G} (hx : x ∈ E) : x * x = 1 := by
  have := hE.1.2 x hx
  rwa [pow_two] at this

theorem isFour_img (h : SBar S A π R) {E : Subgroup G} (hES : E ≤ S) (hEA : E ⊓ A = ⊥)
    (hE : IsFourSubgroup E) : DS.IsFour (h.img E) where
  comm := by
    intro p hp q hq
    obtain ⟨x, hxE, hxS, rfl⟩ := h.mem_img.mp hp
    obtain ⟨y, hyE, hyS, rfl⟩ := h.mem_img.mp hq
    rw [← h.mul x hxS y hyS, ← h.mul y hyS x hxS, hE.comm hxE hyE]
  sq := by
    intro p hp
    obtain ⟨x, hxE, hxS, rfl⟩ := h.mem_img.mp hp
    rw [← h.mul x hxS x hxS, hE.sq hxE, h.pi_one]
  card := by rw [h.card_img hES hEA]; exact hE.2

theorem card_le_four (h : SBar S A π R) {E : Subgroup G} (hES : E ≤ S) (hEA : E ⊓ A = ⊥)
    (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  rw [← h.card_img hES hEA]
  refine h.ds.card_elemAbelian_le fun p hp => ?_
  obtain ⟨x, hxE, hxS, rfl⟩ := h.mem_img.mp hp
  rw [← h.mul x hxS x hxS]
  have := hE.2 x hxE
  rw [pow_two] at this
  rw [this, h.pi_one]

theorem pi_eq_z (h : SBar S A π R) {z₀ : G} (hz₀S : z₀ ∈ S) (hcent : ∀ s ∈ S, z₀ * s = s * z₀)
    (hsq : z₀ * z₀ ∈ A) (hne : z₀ ∉ A) : π z₀ = h.ds.z := by
  have hc : ∀ p : P, π z₀ * p = p * π z₀ := by
    intro p
    obtain ⟨s, hsS, rfl⟩ := h.surj p
    rw [← h.mul z₀ hz₀S s hsS, ← h.mul s hsS z₀ hz₀S, hcent s hsS]
  have hR : π z₀ ∈ R := h.ds.mem_of_central hc
  have h2 : π z₀ * π z₀ = 1 := by
    rw [← h.mul z₀ hz₀S z₀ hz₀S]; exact (h.ker _ (S.mul_mem hz₀S hz₀S)).mpr hsq
  rcases h.ds.eq_one_or_eq_z hR h2 with h1 | h1
  · exact absurd ((h.ker _ hz₀S).mp h1) hne
  · exact h1

theorem hom_surjective (h : SBar S A π R) : Function.Surjective h.hom := by
  intro p
  obtain ⟨s, hs, rfl⟩ := h.surj p
  exact ⟨⟨s, hs⟩, rfl⟩

theorem ker_hom (h : SBar S A π R) : h.hom.ker = A.subgroupOf S := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hom_apply]
  exact h.ker _ s.2

theorem card_S (h : SBar S A π R) (hA : A ≤ S) : Nat.card A * Nat.card P = Nat.card S := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective h.hom_surjective
  rw [ker_hom] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv] at h1
  exact h1

theorem index_img_mul (h : SBar S A π R) {X : Subgroup G} (hXS : X ≤ S) (hXA : X ⊓ A = ⊥) :
    (h.img X).index * Nat.card X = Nat.card P := by
  have h1 := Subgroup.card_mul_index (h.img X)
  rw [h.card_img hXS hXA] at h1
  rw [mul_comm]; exact h1

theorem index_img_le [Finite G] (h : SBar S A π R) (Y : Subgroup G) :
    (h.img Y).index ≤ Y.relIndex S := by
  have h1 := Subgroup.index_map_dvd (H := Y.subgroupOf S) h.hom_surjective
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1

theorem nonabelian_img (h : SBar S A π R) {B : Subgroup G} (hBS : B ≤ S) (hBA : B ⊓ A = ⊥)
    (hB : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) : ∃ a ∈ h.img B, ∃ b ∈ h.img B, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := hB
  refine ⟨π a, h.pi_mem_img ha (hBS ha), π b, h.pi_mem_img hb (hBS hb), fun hcomm => hab ?_⟩
  rw [← h.mul a (hBS ha) b (hBS hb), ← h.mul b (hBS hb) a (hBS ha)] at hcomm
  have h1 := (h.pi_eq_iff (S.mul_mem (hBS ha) (hBS hb)) (S.mul_mem (hBS hb) (hBS ha))).mp hcomm
  have h2 : (a * b)⁻¹ * (b * a) ∈ B ⊓ A :=
    ⟨B.mul_mem (B.inv_mem (B.mul_mem ha hb)) (B.mul_mem hb ha), h1⟩
  rw [hBA, Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.mp h2)

theorem exists_mem_commutator (h : SBar S A π R) {Q : Subgroup G} (hQS : Q ≤ S)
    (hQA : Q ⊓ A = ⊥) (hQR : ¬ Q ≤ h.Rt) {ρ : G} (hρQ : ρ ∈ Q) (hρR : ρ ∈ h.Rt)
    (hρ : ρ * ρ ≠ 1) : ∃ w ∈ ⁅Q, Q⁆, π w = h.ds.z := by
  have hQb : ¬ h.img Q ≤ R := by
    intro hle
    apply hQR
    intro q hq
    rw [h.mem_Rt]
    exact ⟨hQS hq, hle (h.pi_mem_img hq (hQS hq))⟩
  have hρ2 : π ρ * π ρ ≠ 1 := by
    intro h1
    rw [← h.mul ρ (hQS hρQ) ρ (hQS hρQ)] at h1
    have h2 := (h.ker _ (S.mul_mem (hQS hρQ) (hQS hρQ))).mp h1
    have h3 : ρ * ρ ∈ Q ⊓ A := ⟨Q.mul_mem hρQ hρQ, h2⟩
    rw [hQA, Subgroup.mem_bot] at h3
    exact hρ h3
  have hz := h.ds.z_mem_commutator hQb (h.pi_mem_img hρQ (hQS hρQ)) ((h.mem_Rt.mp hρR).2) hρ2
  have himg : h.img Q = (Q.subgroupOf S).map h.hom := rfl
  rw [himg, ← Subgroup.map_commutator, Subgroup.mem_map] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hmap := Subgroup.map_commutator (Q.subgroupOf S) (Q.subgroupOf S) S.subtype
  rw [Subgroup.map_subgroupOf_eq_of_le hQS] at hmap
  have hyQ : (y : G) ∈ ⁅Q, Q⁆ := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  exact ⟨(y : G), hyQ, hyz⟩

theorem central_unique (h : SBar S A π R) {B : Subgroup G} (hBS : B ≤ S) (hBA : B ⊓ A = ⊥)
    (hB : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) {c c' : G} (hcB : c ∈ B) (hc'B : c' ∈ B)
    (hc : ∀ b ∈ B, b * c = c * b) (hc' : ∀ b ∈ B, b * c' = c' * b) (hc1 : c ≠ 1)
    (hc1' : c' ≠ 1) : c = c' := by
  have hBb := h.nonabelian_img hBS hBA hB
  have key : ∀ d : G, d ∈ B → (∀ b ∈ B, b * d = d * b) → d ≠ 1 → π d = h.ds.z := by
    intro d hdB hd hd1
    have hcomm : ∀ p ∈ h.img B, p * π d = π d * p := by
      intro p hp
      obtain ⟨x, hxB, hxS, rfl⟩ := h.mem_img.mp hp
      rw [← h.mul x hxS d (hBS hdB), ← h.mul d (hBS hdB) x hxS, hd x hxB]
    rcases h.ds.central_in_nonabelian hBb hcomm with h1 | h1
    · exfalso
      have h2 := (h.ker _ (hBS hdB)).mp h1
      have h3 : d ∈ B ⊓ A := ⟨hdB, h2⟩
      rw [hBA, Subgroup.mem_bot] at h3
      exact hd1 h3
    · exact h1
  have h1 := key c hcB hc hc1
  have h2 := key c' hc'B hc' hc1'
  have h3 := (h.pi_eq_iff (hBS hcB) (hBS hc'B)).mp (h1.trans h2.symm)
  have h4 : c⁻¹ * c' ∈ B ⊓ A := ⟨B.mul_mem (B.inv_mem hcB) hc'B, h3⟩
  rw [hBA, Subgroup.mem_bot] at h4
  exact inv_mul_eq_one.mp h4

theorem abelian_centralizer [Finite G] (h : SBar S A π R) (h8 : 8 ≤ Nat.card R) {B : Subgroup G}
    (hBS : B ≤ S) (hBA : B ⊓ A = ⊥) (hB4 : 4 ≤ Nat.card B)
    (hidx : (S ⊓ Subgroup.centralizer (B : Set G)).relIndex S ≤ 2) :
    B ≤ h.Rt ∧ ∀ c ∈ S, (∀ b ∈ B, c * b = b * c) → c ∈ h.Rt := by
  have hC : h.img (S ⊓ Subgroup.centralizer (B : Set G)) ≤
      Subgroup.centralizer (h.img B : Set P) := by
    intro p hp
    obtain ⟨c, hcC, hcS, rfl⟩ := h.mem_img.mp hp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨b, hbB, hbS, rfl⟩ := h.mem_img.mp hq
    have hcb : b * c = c * b := Subgroup.mem_centralizer_iff.mp hcC.2 b hbB
    rw [← h.mul b hbS c hcS, ← h.mul c hcS b hbS, hcb]
  have hidx' : (Subgroup.centralizer (h.img B : Set P)).index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hC)).trans
      ((h.index_img_le (S ⊓ Subgroup.centralizer (B : Set G))).trans hidx)
  have hcard : 4 ≤ Nat.card (h.img B) := by rw [h.card_img hBS hBA]; exact hB4
  obtain ⟨hBR, hcen⟩ := h.ds.abelian_centralizer h8 hcard hidx'
  refine ⟨fun b hb => ?_, fun c hc hcB => ?_⟩
  · rw [h.mem_Rt]; exact ⟨hBS hb, hBR (h.pi_mem_img hb (hBS hb))⟩
  · rw [h.mem_Rt]
    refine ⟨hc, ?_⟩
    rw [← hcen, Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨b, hbB, hbS, rfl⟩ := h.mem_img.mp hq
    rw [← h.mul b hbS c hc, ← h.mul c hc b hbS, (hcB b hbB).symm]

theorem exists_conj_four (h : SBar S A π R) {Q : Subgroup G} (hQS : Q ≤ S) (hQA : Q ⊓ A = ⊥)
    (hQn : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) (hQR : ¬ Q ≤ h.Rt) (hQi : (h.img Q).index = 2)
    {E E' : Subgroup G} (hE : IsFourSubgroup E) (hE' : IsFourSubgroup E') (hEQ : E ≤ Q)
    (hE'Q : E' ≤ Q) : ∃ s ∈ S, ∀ x ∈ E, s * x * s⁻¹ ∈ E' := by
  have hEA : E ⊓ A = ⊥ := le_bot_iff.mp (hQA ▸ inf_le_inf_right A hEQ)
  have hE'A : E' ⊓ A = ⊥ := le_bot_iff.mp (hQA ▸ inf_le_inf_right A hE'Q)
  have hFE := h.isFour_img (hEQ.trans hQS) hEA hE
  have hFE' := h.isFour_img (hE'Q.trans hQS) hE'A hE'
  have hQb : ¬ h.img Q ≤ R := by
    intro hle
    apply hQR
    intro q hq
    rw [h.mem_Rt]
    exact ⟨hQS hq, hle (h.pi_mem_img hq (hQS hq))⟩
  have hE1 : h.img E ≤ h.img Q := by
    intro p hp
    obtain ⟨x, hxE, hxS, rfl⟩ := h.mem_img.mp hp
    exact h.pi_mem_img (hEQ hxE) hxS
  have hE2 : h.img E' ≤ h.img Q := by
    intro p hp
    obtain ⟨x, hxE, hxS, rfl⟩ := h.mem_img.mp hp
    exact h.pi_mem_img (hE'Q hxE) hxS
  obtain ⟨p, hpR, hp⟩ := h.ds.exists_conj_four hQi hQb hFE hFE' hE1 hE2
  obtain ⟨s, hsS, rfl⟩ := h.surj p
  refine ⟨s, hsS, fun x hx => ?_⟩
  have hxS : x ∈ S := hQS (hEQ hx)
  have h1 := hp (π x) (h.pi_mem_img hx hxS)
  rw [← h.pi_inv hsS, ← h.mul s hsS x hxS, ← h.mul _ (S.mul_mem hsS hxS) _ (S.inv_mem hsS)] at h1
  obtain ⟨y, hyE', hyS, hy⟩ := h.mem_img.mp h1
  have hsxQ : s * x * s⁻¹ ∈ Q := hQn s hsS x (hEQ hx)
  have hsxS : s * x * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hsS hxS) (S.inv_mem hsS)
  have h2 := (h.pi_eq_iff hyS hsxS).mp hy
  have h3 : y⁻¹ * (s * x * s⁻¹) ∈ Q ⊓ A :=
    ⟨Q.mul_mem (Q.inv_mem (hE'Q hyE')) hsxQ, h2⟩
  rw [hQA, Subgroup.mem_bot] at h3
  have : s * x * s⁻¹ = y := (inv_mul_eq_one.mp h3).symm
  rw [this]; exact hyE'

end SBar

end CFSG.QuasithinUnique
