module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.X1Setup

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G]

@[expose] def thetaHom {W : Subgroup G} (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {g : G}
    (hg : ∀ x, x ∈ W ↔ g * x * g⁻¹ ∈ W) : ↥W →* ↥W :=
  MonoidHom.mk' (fun w => ⟨(w : G) * (g * (w : G) * g⁻¹), W.mul_mem w.2 ((hg w).1 w.2)⟩)
    (fun w₁ w₂ => by
      apply Subtype.ext
      have h1 : (g * (w₁ : G) * g⁻¹) ∈ W := (hg w₁).1 w₁.2
      have h2 := hW _ w₂.2 _ h1
      show (w₁ : G) * (w₂ : G) * (g * ((w₁ : G) * (w₂ : G)) * g⁻¹) =
        (w₁ : G) * (g * (w₁ : G) * g⁻¹) * ((w₂ : G) * (g * (w₂ : G) * g⁻¹))
      calc (w₁ : G) * (w₂ : G) * (g * ((w₁ : G) * (w₂ : G)) * g⁻¹)
          = (w₁ : G) * ((w₂ : G) * (g * (w₁ : G) * g⁻¹)) * (g * (w₂ : G) * g⁻¹) := by group
        _ = (w₁ : G) * ((g * (w₁ : G) * g⁻¹) * (w₂ : G)) * (g * (w₂ : G) * g⁻¹) := by rw [h2]
        _ = _ := by group)

theorem thetaHom_ker {W : Subgroup G} (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hsq : ∀ x ∈ W, x * x = 1) {g : G} (hg : ∀ x, x ∈ W ↔ g * x * g⁻¹ ∈ W) :
    (thetaHom hW hg).ker = (W ⊓ centralizer ({g} : Set G)).subgroupOf W := by
  ext w
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  have hwi : (w : G)⁻¹ = w := inv_eq_of_mul_eq_one_right (hsq w w.2)
  constructor
  · intro hw
    have h1 : (w : G) * (g * (w : G) * g⁻¹) = 1 := congrArg Subtype.val hw
    have h2 : g * (w : G) * g⁻¹ = (w : G) := by
      have := eq_inv_of_mul_eq_one_right h1
      rw [this, hwi]
    refine ⟨w.2, ?_⟩
    calc (w : G) * g = (g * (w : G) * g⁻¹) * g := by rw [h2]
      _ = g * (w : G) := by group
  · rintro ⟨-, h⟩
    apply Subtype.ext
    have h2 : g * (w : G) * g⁻¹ = (w : G) := by
      rw [mul_inv_eq_iff_eq_mul, ← h]
    show (w : G) * (g * (w : G) * g⁻¹) = 1
    rw [h2]
    exact hsq w w.2

theorem thetaHom_range_le {W : Subgroup G} (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {g : G}
    (hg : ∀ x, x ∈ W ↔ g * x * g⁻¹ ∈ W) (hg2 : ∀ x ∈ W, g * g * x = x * (g * g)) :
    (thetaHom hW hg).range ≤ (W ⊓ centralizer ({g} : Set G)).subgroupOf W := by
  rintro _ ⟨w, rfl⟩
  refine Subgroup.mem_subgroupOf.2 (mem_inf.2 ⟨(thetaHom hW hg w).2,
    mem_centralizer_singleton_iff.2 ?_⟩)
  have h1 : (g * (w : G) * g⁻¹) ∈ W := (hg w).1 w.2
  have h3 : g * g * (w : G) * (g⁻¹ * g⁻¹) = (w : G) := by
    have := hg2 w w.2
    calc g * g * (w : G) * (g⁻¹ * g⁻¹) = (g * g * (w : G)) * (g * g)⁻¹ := by group
      _ = (w : G) * (g * g) * (g * g)⁻¹ := by rw [this]
      _ = w := by group
  have h5 : g * ((w : G) * (g * (w : G) * g⁻¹)) * g⁻¹ = (w : G) * (g * (w : G) * g⁻¹) := by
    calc g * ((w : G) * (g * (w : G) * g⁻¹)) * g⁻¹
        = (g * (w : G) * g⁻¹) * (g * g * (w : G) * (g⁻¹ * g⁻¹)) := by group
      _ = (g * (w : G) * g⁻¹) * (w : G) := by rw [h3]
      _ = (w : G) * (g * (w : G) * g⁻¹) := hW _ h1 _ w.2
  exact (mul_inv_eq_iff_eq_mul.1 h5).symm

theorem card_le_sq_card_centralizer [Finite G] {W : Subgroup G}
    (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hsq : ∀ x ∈ W, x * x = 1) {g : G}
    (hg : ∀ x, x ∈ W ↔ g * x * g⁻¹ ∈ W) (hg2 : ∀ x ∈ W, g * g * x = x * (g * g)) :
    Nat.card W ≤ Nat.card ↥(W ⊓ centralizer ({g} : Set G)) ^ 2 := by
  set θ := thetaHom hW hg with hθ
  set Cg := (W ⊓ centralizer ({g} : Set G)).subgroupOf W with hCg
  have h1 := Subgroup.card_ker_mul_card_range θ
  have h2 : Nat.card θ.ker ≤ Nat.card Cg :=
    Subgroup.card_le_of_le (le_of_eq (thetaHom_ker hW hsq hg))
  have h3 : Nat.card θ.range ≤ Nat.card Cg := Subgroup.card_le_of_le (thetaHom_range_le hW hg hg2)
  have h4 : Nat.card Cg = Nat.card ↥(W ⊓ centralizer ({g} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card W = Nat.card θ.ker * Nat.card θ.range := h1.symm
    _ ≤ Nat.card Cg * Nat.card Cg := Nat.mul_le_mul h2 h3
    _ = _ := by rw [h4, sq]

theorem exists_eq_mul_conj_of_card_eq [Finite G] {W : Subgroup G}
    (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hsq : ∀ x ∈ W, x * x = 1) {g : G}
    (hg : ∀ x, x ∈ W ↔ g * x * g⁻¹ ∈ W) (hg2 : ∀ x ∈ W, g * g * x = x * (g * g))
    (hcard : Nat.card W = Nat.card ↥(W ⊓ centralizer ({g} : Set G)) ^ 2) {a : G} (ha : a ∈ W)
    (hag : a * g = g * a) : ∃ w ∈ W, w * (g * w * g⁻¹) = a := by
  set θ := thetaHom hW hg with hθ
  set Cg := (W ⊓ centralizer ({g} : Set G)).subgroupOf W with hCg
  have h4 : Nat.card Cg = Nat.card ↥(W ⊓ centralizer ({g} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range θ
  have hk : Nat.card θ.ker = Nat.card Cg := by rw [thetaHom_ker hW hsq hg]
  have hpos : 0 < Nat.card Cg := Nat.card_pos
  have hr : Nat.card θ.range = Nat.card Cg := by
    rw [hk, hcard, ← h4, sq] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hle := thetaHom_range_le hW hg hg2
  have heq : θ.range = Cg := Subgroup.eq_of_le_of_card_ge hle (by rw [hr])
  have hmem : (⟨a, ha⟩ : ↥W) ∈ Cg :=
    Subgroup.mem_subgroupOf.2 (mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 hag⟩)
  rw [← heq] at hmem
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

variable {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

theorem phiv_conj_of_comm {g : G} (k : G) (hg : g * z = z * g) :
    phiv z (g * k * g⁻¹) = g * phiv z k * g⁻¹ := by
  have hg' : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hg]
      _ = z := by group
  unfold phiv
  calc z * (g * k * g⁻¹ * z * (g * k * g⁻¹)⁻¹)
      = z * (g * k * (g⁻¹ * z * g) * k⁻¹ * g⁻¹) := by group
    _ = z * (g * k * z * k⁻¹ * g⁻¹) := by rw [hg']
    _ = (g * z * g⁻¹) * (g * (k * z * k⁻¹) * g⁻¹) := by
        have : g * z * g⁻¹ = z := by rw [hg]; group
        rw [this]; group
    _ = g * (z * (k * z * k⁻¹)) * g⁻¹ := by group

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem L1_le_K : L1 ≤ Ksub z F := S.K_eq ▸ le_sup_left

theorem card_centralizer_L1_le [Finite G] {g : G} (hgz : g * z = z * g) :
    Nat.card ↥(L1 ⊓ centralizer ({g} : Set G)) ≤
      Nat.card ↥(F ⊓ centralizer ({g} : Set G)) ^ 2 := by
  set A := L1 ⊓ centralizer ({g} : Set G) with hA
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hgc : ∀ a : A, g * (a : G) = (a : G) * g := fun a =>
    (mem_centralizer_singleton_iff.1 (mem_inf.1 a.2).2).symm
  have hphi : ∀ a : A, phiv z (a : G) ∈ F ⊓ centralizer ({g} : Set G) := by
    intro a
    refine mem_inf.2 ⟨phiv_mem S.one S.nd (S.L1_le_K (mem_inf.1 a.2).1),
      mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : g * (a : G) * g⁻¹ = (a : G) := by rw [hgc a]; group
    have h2 := phiv_conj_of_comm (z := z) (a : G) hgz
    rw [h1] at h2
    calc phiv z (a : G) * g = g * phiv z (a : G) * g⁻¹ * g := by rw [← h2]
      _ = g * phiv z (a : G) := by group
  let Φ : ↥A →* ↥(F ⊓ centralizer ({g} : Set G)) :=
    MonoidHom.mk' (fun a => ⟨phiv z (a : G), hphi a⟩) (fun a b =>
      Subtype.ext (phiv_mul S.one S.nd (S.L1_le_K (mem_inf.1 a.2).1)
        (S.L1_le_K (mem_inf.1 b.2).1)))
  have hFA : F ⊓ centralizer ({g} : Set G) ≤ A :=
    inf_le_inf_right _ S.F_le
  have hker : Φ.ker ≤ (F ⊓ centralizer ({g} : Set G)).subgroupOf A := by
    intro a ha
    have h1 : phiv z (a : G) = 1 := congrArg Subtype.val ha
    refine Subgroup.mem_subgroupOf.2 (mem_inf.2 ⟨?_, (mem_inf.1 a.2).2⟩)
    refine S.L1_cz _ (mem_inf.1 a.2).1 ?_
    have h2 : (a : G) * z * (a : G)⁻¹ = z := by
      have := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact (inv_eq_of_mul_eq_one_right hz2).symm ▸ rfl
    calc z * (a : G) = ((a : G) * z * (a : G)⁻¹) * (a : G) := by rw [h2]
      _ = (a : G) * z := by group
  have h1 := Subgroup.card_ker_mul_card_range Φ
  have h2 : Nat.card Φ.ker ≤ Nat.card ↥(F ⊓ centralizer ({g} : Set G)) := by
    calc Nat.card Φ.ker ≤ Nat.card ((F ⊓ centralizer ({g} : Set G)).subgroupOf A) :=
          Subgroup.card_le_of_le hker
      _ = _ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv
  have h3 : Nat.card Φ.range ≤ Nat.card ↥(F ⊓ centralizer ({g} : Set G)) :=
    Subgroup.card_le_card_group _
  calc Nat.card A = Nat.card Φ.ker * Nat.card Φ.range := h1.symm
    _ ≤ _ * _ := Nat.mul_le_mul h2 h3
    _ = _ := by rw [sq]

theorem card_centralizer_L1_eq [Finite G] {g : G} (hgX : g ∈ normalizer (L1 : Set G))
    (hgz : g * z = z * g) (hg2 : g * g ∈ F) (hF : Nat.card ↥(F ⊓ centralizer ({g} : Set G)) ≤ 4) :
    Nat.card ↥(L1 ⊓ centralizer ({g} : Set G)) = 16 := by
  have hup := S.card_centralizer_L1_le hgz
  have hlow : Nat.card L1 ≤ Nat.card ↥(L1 ⊓ centralizer ({g} : Set G)) ^ 2 :=
    card_le_sq_card_centralizer S.L1_comm S.L1_sq (Subgroup.mem_normalizer_iff.1 hgX)
      (fun x hx => (S.L1_comm _ (S.F_le hg2) x hx))
  rw [S.L1_card] at hlow
  have h16 : Nat.card ↥(F ⊓ centralizer ({g} : Set G)) ^ 2 ≤ 16 := by
    calc _ ≤ 4 ^ 2 := Nat.pow_le_pow_left hF 2
      _ = 16 := by norm_num
  have : Nat.card ↥(L1 ⊓ centralizer ({g} : Set G)) ≤ 16 := hup.trans h16
  nlinarith

end Setup

end CFSG.EvenSporadicStandard.M23Std
