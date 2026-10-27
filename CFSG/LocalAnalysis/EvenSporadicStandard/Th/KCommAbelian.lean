module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommAa
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.AbelianOfSinger
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SingerCoord

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

section

variable (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include W W2

theorem ThLocalIn2.eq_of_sq_eq_one {x : G} (hx : x ∈ Aa) (hx2 : x * x = 1) : x ∈ A := by
  have hfinAa : Finite ↥Aa := Nat.finite_of_card_ne_zero (by rw [W2.Aa_card]; norm_num)
  have sq_mem : ∀ y : ↥Aa, (y : G) ^ 2 ∈ A := fun y => (W2.A_eq_sq _).2 ⟨y, y.2, rfl⟩
  let f : ↥Aa →* ↥A := MonoidHom.mk'
    (fun y => ⟨(y : G) ^ 2, sq_mem y⟩) (fun y y' => by
      apply Subtype.ext
      have h := W2.Aa_comm _ y.2 _ y'.2
      show ((y : G) * y') ^ 2 = (y : G) ^ 2 * (y' : G) ^ 2
      calc ((y : G) * y') ^ 2 = (y * y') * (y * y') := sq _
        _ = y * (y' * y) * y' := by group
        _ = y * (y * y') * y' := by rw [← h]
        _ = (y * y) * (y' * y') := by group
        _ = (y : G) ^ 2 * (y' : G) ^ 2 := by rw [sq, sq])
  have hsurj : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨y, hy, rfl⟩ := (W2.A_eq_sq a).1 ha
    exact ⟨⟨y, hy⟩, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (↥Aa ⧸ f.ker) = Nat.card A := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv]
  rw [h2, W2.Aa_card, W.A_card] at h1
  have hker : Nat.card f.ker = 16 := by omega
  have hAAa : A ≤ Aa := fun a ha => by
    obtain ⟨y, hy, rfl⟩ := (W2.A_eq_sq a).1 ha
    exact Aa.pow_mem hy 2
  have hle : A.subgroupOf Aa ≤ f.ker := fun y hy => by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact W.A_sq _ (mem_subgroupOf.1 hy)
  have hcardA : Nat.card (A.subgroupOf Aa) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAAa).toEquiv, W.A_card]
  have heq : A.subgroupOf Aa = f.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hker, hcardA])
  have hxker : (⟨x, hx⟩ : ↥Aa) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show x ^ 2 = 1
    rw [sq]
    exact hx2
  rw [← heq] at hxker
  exact mem_subgroupOf.1 hxker

variable (H : ThCyc G L R t)

include H

theorem ThCyc.kCommutator_comm {k : G} (hkL : k ∈ L) (hkA : ∀ x ∈ A, k * x * k⁻¹ ∈ A)
    (hodd : Odd (orderOf k)) (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1)
    (c : G → (Fin 4 → ZMod 2)) (j : ℕ) (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 8)
    (hcmul : ∀ a ∈ A, ∀ b ∈ A, c (a * b) = c a + c b)
    (hcinj : ∀ a ∈ A, ∀ b ∈ A, c a = c b → a = b) (hconto : ∀ u, ∃ a ∈ A, c a = u)
    (hck : ∀ a ∈ A, c (k * a * k⁻¹) = (singerMat ^ j) *ᵥ c a) :
    ∀ x ∈ kCommutator (Csub A Aa t) k, ∀ y ∈ kCommutator (Csub A Aa t) k, x * y = y * x := by
  have hN := H.Aa_subgroupOf_normal W W2
  obtain ⟨hDC, -, hkD, -, -⟩ := H.kCommutator_factorization W W2 (C := Csub A Aa t) rfl hkL hkA
    hodd hfix
  have hZD : Aa ≤ kCommutator (Csub A Aa t) k := H.Aa_le_kCommutator W W2 hkL hkA hodd hfix
  have hZc : ∀ z ∈ Aa, ∀ x ∈ kCommutator (Csub A Aa t) k, z * x = x * z := fun z hz x hx =>
    (mem_centralizer_iff.1 (hDC hx).2) z hz
  have hsq : ∀ x ∈ kCommutator (Csub A Aa t) k, x * x ∈ Aa := by
    intro x hx
    have h := E_sq_eq_one H W W2 (QuotientGroup.mk (⟨x, hDC hx⟩ : ↥(Csub A Aa t)))
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
    exact h
  have hcomm : ∀ x ∈ kCommutator (Csub A Aa t) k, ∀ y ∈ kCommutator (Csub A Aa t) k,
      x * y * x⁻¹ * y⁻¹ ∈ Aa := by
    intro x hx y hy
    have h := E_mul_comm H W W2 (QuotientGroup.mk ⟨x, hDC hx⟩) (QuotientGroup.mk ⟨y, hDC hy⟩)
    have h' : (QuotientGroup.mk (⟨x, hDC hx⟩ * ⟨y, hDC hy⟩ * ⟨x, hDC hx⟩⁻¹ * ⟨y, hDC hy⟩⁻¹ :
        ↥(Csub A Aa t)) : Equot A Aa t) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, h]
      group
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h'
    exact h'
  have hθker : ∀ x ∈ kCommutator (Csub A Aa t) k, theta t x = 1 → x ∈ Aa := by
    intro x hx h1
    have hker : (⟨x, hDC hx⟩ : ↥(Csub A Aa t)) ∈ (thetaC H W).ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    rw [ThCyc.mem_ker_thetaC H W W2] at hker
    have hmem : x ∈ kCommutator (Csub A Aa t) k ⊓ (Aa ⊔ zpowers t) := ⟨hx, hker⟩
    rwa [H.kCommutator_inf_Aa_sup W W2 hkL hkA hodd hfix] at hmem
  exact commute_of_singer_pairing (D := kCommutator (Csub A Aa t) k) (Z := Aa) (A := A)
    (theta t) c k j hj hZD hZc hsq hcomm (fun z hz hz2 => ThLocalIn2.eq_of_sq_eq_one W W2 hz hz2)
    (fun x hx y hy => H.theta_mul W (hDC hx).1 (hDC hy).1)
    (fun x hx => H.theta_mem_A W (hDC hx).1) hθker
    (fun a ha => H.exists_theta_eq_kCommutator W W2 hkL hkA hodd hfix ha) hkD
    (fun x _ => H.theta_conj hkL x) hcmul hcinj hconto hck

theorem ThCyc.exists_kCommutator_abelian :
    ∃ k ∈ L, (∀ x ∈ A, k * x * k⁻¹ ∈ A) ∧ Odd (orderOf k) ∧
      (∀ x ∈ A, k * x * k⁻¹ = x → x = 1) ∧
      (∀ x ∈ kCommutator (Csub A Aa t) k, ∀ y ∈ kCommutator (Csub A Aa t) k, x * y = y * x) ∧
      Aa ≤ kCommutator (Csub A Aa t) k ∧
      kCommutator (Csub A Aa t) k ⊔ zpowers t = Csub A Aa t ∧
      Disjoint (kCommutator (Csub A Aa t) k) (zpowers t) ∧
      Nat.card (kCommutator (Csub A Aa t) k) = 2 ^ 12 := by
  obtain ⟨k, c, j, hkL, hkA, hodd, hfix, hj, hcmul, hcinj, hconto, hck⟩ :=
    exists_singer_coord (L := L) W.A_comm W.A_sq W.A_card W.surj
  obtain ⟨hsup, hdisj, hcard⟩ := H.kCommutator_complement W W2 hkL hkA hodd hfix
  exact ⟨k, hkL, hkA, hodd, hfix,
    H.kCommutator_comm W W2 hkL hkA hodd hfix c j hj hcmul hcinj hconto hck,
    H.Aa_le_kCommutator W W2 hkL hkA hodd hfix, hsup, hdisj, hcard⟩

end

end CFSG.EvenSporadicStandard.ThStd
