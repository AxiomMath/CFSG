module

public import CFSG.LocalAnalysis.GH72.DDProduct
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.CGT.Foote81L6.TStruct.DihFour

public section

namespace CFSG.GH72

open Subgroup DihedralGroup
open CFSG.CGT.Foote81L6 (zc zc_mul_self zc_ne_one zc_comm eq_one_or_zc_of_comm not_comm_of_two_le
  card_sup_of_le_normalizer le_normalizer_of_comm)
open CFSG.CGT.Foote81L6.TStruct (zc_eq_r r_eq_of_mul_self quarter_add_quarter mem_dihFour_of_comm
  mul_self_of_mem_dihFour comm_of_mul_self)

section Model

variable {k : ℕ}

theorem dih_exists_mul_self_eq_zc (hk : 2 ≤ k) : ∃ u : DihedralGroup (2 ^ k), u * u = zc k :=
  ⟨r ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)), by
    rw [r_mul_r, quarter_add_quarter hk, zc_eq_r (by omega)]⟩

theorem dih_exists_r_of_mul_self_eq_zc (hk : 1 ≤ k) {x : DihedralGroup (2 ^ k)}
    (hx : x * x = zc k) : ∃ j, x = r j := by
  cases x with
  | r j => exact ⟨j, rfl⟩
  | sr i =>
    rw [sr_mul_sr, sub_self, ← one_def] at hx
    exact absurd hx.symm (zc_ne_one hk)

theorem dih_comm_of_comm_noncentral (hk : 2 ≤ k) {x a b : DihedralGroup (2 ^ k)}
    (hx : ∃ g, g * x ≠ x * g) (ha : a * x = x * a) (hb : b * x = x * b) : a * b = b * a := by
  cases x with
  | r i =>
    have hrot : ∀ c : DihedralGroup (2 ^ k), c * r i = r i * c → ∃ j, c = r j := by
      intro c hc
      cases c with
      | r j => exact ⟨j, rfl⟩
      | sr j =>
        exfalso
        rw [sr_mul_r, r_mul_sr] at hc
        have hii : i + i = 0 := by
          have h' := sr.inj hc
          linear_combination h'
        obtain ⟨g, hg⟩ := hx
        apply hg
        have h1 : r i * r i = (1 : DihedralGroup (2 ^ k)) := by rw [r_mul_r, hii, one_def]
        rcases r_eq_of_mul_self (by omega) h1 with h | h
        · rw [h, one_mul, mul_one]
        · rw [h]
          exact zc_comm (by omega) g
    obtain ⟨j₁, rfl⟩ := hrot a ha
    obtain ⟨j₂, rfl⟩ := hrot b hb
    rw [r_mul_r, r_mul_r, add_comm]
  | sr i =>
    exact comm_of_mul_self (mul_self_of_mem_dihFour (by omega) i)
      (mem_dihFour_of_comm (by omega) ha) (mem_dihFour_of_comm (by omega) hb)

theorem dih_card_mul_self_eq_zc_lt (hk : 2 ≤ k) :
    Nat.card {x : DihedralGroup (2 ^ k) // x * x = zc k} <
      Nat.card {x : DihedralGroup (2 ^ k) // x * x = 1} := by
  classical
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  let f : {x : DihedralGroup (2 ^ k) // x * x = zc k} → {x : DihedralGroup (2 ^ k) // x * x = 1} :=
    fun x => ⟨x.1 * sr 0, by
      obtain ⟨j, hj⟩ := dih_exists_r_of_mul_self_eq_zc (by omega) x.2
      rw [hj, r_mul_sr, sr_mul_sr, sub_self, one_def]⟩
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (mul_right_cancel (congrArg Subtype.val h))
  have hnot : (⟨1, one_mul 1⟩ : {x : DihedralGroup (2 ^ k) // x * x = 1}) ∉ Set.range f := by
    rintro ⟨x, hx⟩
    have h1 : x.1 * sr 0 = 1 := congrArg Subtype.val hx
    have h2 : x.1 = sr 0 := (eq_inv_of_mul_eq_one_left h1).trans (inv_sr 0)
    have h3 := x.2
    rw [h2, sr_mul_sr, sub_self, ← one_def] at h3
    exact zc_ne_one (by omega) h3.symm
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem f hf hnot

theorem dih_card_mul_self_eq_zc_pos (hk : 2 ≤ k) :
    0 < Nat.card {x : DihedralGroup (2 ^ k) // x * x = zc k} := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  obtain ⟨u, hu⟩ := dih_exists_mul_self_eq_zc hk
  haveI : Nonempty {x : DihedralGroup (2 ^ k) // x * x = zc k} := ⟨⟨u, hu⟩⟩
  exact Nat.card_pos

end Model

section Abstract

variable {H : Type*} [Group H] {k : ℕ}

theorem mulEquiv_apply_mem_center {K : Type*} [Group K] (ρ : H ≃* K) {z : H}
    (hz : z ∈ center H) : ρ z ∈ center K := by
  rw [mem_center_iff] at hz ⊢
  intro g
  obtain ⟨h, rfl⟩ := ρ.surjective g
  rw [← map_mul, ← map_mul, hz h]

theorem mulEquiv_apply_mem_center_iff {K : Type*} [Group K] (ρ : H ≃* K) {z : H} :
    ρ z ∈ center K ↔ z ∈ center H :=
  ⟨fun h => by simpa using mulEquiv_apply_mem_center ρ.symm h, mulEquiv_apply_mem_center ρ⟩

theorem dih_symm_zc_mem_center (e : H ≃* DihedralGroup (2 ^ k)) (hk : 1 ≤ k) :
    e.symm (zc k) ∈ center H := by
  rw [← mulEquiv_apply_mem_center_iff e, MulEquiv.apply_symm_apply, mem_center_iff]
  exact fun g => zc_comm hk g

theorem dih_symm_zc_mul_self (e : H ≃* DihedralGroup (2 ^ k)) (hk : 1 ≤ k) :
    e.symm (zc k) * e.symm (zc k) = 1 := by
  rw [← map_mul, zc_mul_self hk, map_one]

theorem dih_symm_zc_ne_one (e : H ≃* DihedralGroup (2 ^ k)) (hk : 1 ≤ k) :
    e.symm (zc k) ≠ 1 := by
  rw [Ne, ← map_one e.symm, e.symm.injective.eq_iff]
  exact zc_ne_one hk

theorem dih_eq_one_or_of_mem_center (e : H ≃* DihedralGroup (2 ^ k)) (hk : 2 ≤ k) {z : H}
    (hz : z ∈ center H) : z = 1 ∨ z = e.symm (zc k) := by
  have hz' := mulEquiv_apply_mem_center e hz
  rw [mem_center_iff] at hz'
  rcases eq_one_or_zc_of_comm hk hz' with h | h
  · exact Or.inl (e.injective (h.trans e.map_one.symm))
  · exact Or.inr (by rw [← h, MulEquiv.symm_apply_apply])

theorem dih_mul_self_of_mem_center (e : H ≃* DihedralGroup (2 ^ k)) (hk : 2 ≤ k) {z : H}
    (hz : z ∈ center H) : z * z = 1 := by
  rcases dih_eq_one_or_of_mem_center e hk hz with rfl | rfl
  · exact mul_one 1
  · exact dih_symm_zc_mul_self e (by omega)

theorem dih_mem_center_of_le_one (e : H ≃* DihedralGroup (2 ^ k)) (hk : k ≤ 1) (z : H) :
    z ∈ center H := by
  rw [← mulEquiv_apply_mem_center_iff e, mem_center_iff]
  exact fun g => CFSG.CGT.Foote81L6.mul_comm_of_le_one hk g (e z)

theorem dih_mul_self_of_le_one (e : H ≃* DihedralGroup (2 ^ k)) (hk : 1 ≤ k) (hk1 : k ≤ 1)
    (x : H) : x * x = 1 := by
  obtain rfl : k = 1 := by omega
  apply e.injective
  rw [map_mul, map_one]
  generalize e x = y
  revert y
  decide

theorem dih_exists_mul_self_eq_symm_zc (e : H ≃* DihedralGroup (2 ^ k)) (hk : 2 ≤ k) :
    ∃ u : H, u * u = e.symm (zc k) := by
  obtain ⟨u, hu⟩ := dih_exists_mul_self_eq_zc hk
  exact ⟨e.symm u, by rw [← map_mul, hu]⟩

theorem dih_comm_of_comm_noncentral' (e : H ≃* DihedralGroup (2 ^ k)) (hk : 2 ≤ k)
    {x a b : H} (hx : ∃ g, g * x ≠ x * g) (ha : a * x = x * a) (hb : b * x = x * b) :
    a * b = b * a := by
  have hx' : ∃ g, g * e x ≠ e x * g := by
    obtain ⟨g, hg⟩ := hx
    refine ⟨e g, fun h => hg (e.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have ha' : e a * e x = e x * e a := by rw [← map_mul, ha, map_mul]
  have hb' : e b * e x = e x * e b := by rw [← map_mul, hb, map_mul]
  have h := dih_comm_of_comm_noncentral hk hx' ha' hb'
  apply e.injective
  rw [map_mul, map_mul, h]

theorem card_mul_self_eq_mulEquiv {K : Type*} [Group K] (ρ : H ≃* K) (z : H) :
    Nat.card {x : K // x * x = ρ z} = Nat.card {x : H // x * x = z} :=
  (Nat.card_congr (Equiv.subtypeEquiv ρ.toEquiv fun x => by
    change x * x = z ↔ ρ x * ρ x = ρ z
    rw [← map_mul, ρ.injective.eq_iff])).symm

theorem dih_card_mul_self_lt (e : H ≃* DihedralGroup (2 ^ k)) (hk : 2 ≤ k) :
    0 < Nat.card {x : H // x * x = e.symm (zc k)} ∧
      Nat.card {x : H // x * x = e.symm (zc k)} < Nat.card {x : H // x * x = 1} := by
  have h1 := card_mul_self_eq_mulEquiv e (e.symm (zc k))
  have h2 := card_mul_self_eq_mulEquiv e 1
  rw [MulEquiv.apply_symm_apply] at h1
  rw [map_one] at h2
  rw [← h1, ← h2]
  exact ⟨dih_card_mul_self_eq_zc_pos hk, dih_card_mul_self_eq_zc_lt hk⟩

theorem dih_isPGroup_mulAut (e : H ≃* DihedralGroup (2 ^ k)) (hk : 2 ≤ k) :
    IsPGroup 2 (MulAut H) :=
  (CFSG.GorensteinWalter.dihedral_mulAut_is_twoGroup hk).of_equiv (MulAut.congr e).symm

end Abstract

theorem le_centralizer_of_comm_of_sup_eq {G : Type*} [Group G] {D A B : Subgroup G}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hAB : B ≤ centralizer (A : Set G))
    (hsup : A ⊔ B = D) : A ≤ centralizer (D : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro g hg
  have hle : A ⊔ B ≤ centralizer ({a} : Set G) := sup_le
    (fun a' ha' => mem_centralizer_singleton_iff.2 (hA a' ha' a ha))
    (fun b hb => mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hAB hb)) a ha).symm)
  exact mem_centralizer_singleton_iff.1 (hle (hsup ▸ hg))

theorem IsDihNonab.le_centralizer_or_le_centralizer {G : Type*} [Group G] {D A B : Subgroup G}
    (hD : IsDihNonab D) (hAD : A ≤ D) (hBD : B ≤ D) (hAB : B ≤ centralizer (A : Set G))
    (hsup : A ⊔ B = D) : A ≤ centralizer (D : Set G) ∨ B ≤ centralizer (D : Set G) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hD
  have hCA : ∀ x ∈ D, (∃ g ∈ D, g * x ≠ x * g) → ∀ a ∈ D, ∀ b ∈ D, a * x = x * a →
      b * x = x * b → a * b = b * a := by
    intro x hx hnc a ha b hb hax hbx
    have := dih_comm_of_comm_noncentral' e hk (x := ⟨x, hx⟩) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
      (by
        obtain ⟨g, hg, hgx⟩ := hnc
        exact ⟨⟨g, hg⟩, fun h => hgx (congrArg Subtype.val h)⟩)
      (Subtype.ext hax) (Subtype.ext hbx)
    exact congrArg Subtype.val this
  by_cases hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a
  · exact Or.inl (le_centralizer_of_comm_of_sup_eq hA hAB hsup)
  · right
    push Not at hA
    obtain ⟨a, ha, a', ha', haa'⟩ := hA
    have hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
      hCA a (hAD ha) ⟨a', hAD ha', fun h => haa' h.symm⟩ b (hBD hb) b' (hBD hb')
        ((mem_centralizer_iff.1 (hAB hb)) a ha).symm ((mem_centralizer_iff.1 (hAB hb')) a ha).symm
    exact le_centralizer_of_comm_of_sup_eq hB (le_centralizer_iff.1 hAB)
      (by rw [sup_comm, hsup])

section Product

variable {H₁ H₂ : Type*} [Group H₁] [Group H₂]

theorem card_mul_self_eq_prod (a : H₁) (b : H₂) :
    Nat.card {p : H₁ × H₂ // p * p = (a, b)} =
      Nat.card {x : H₁ // x * x = a} * Nat.card {y : H₂ // y * y = b} := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ((Equiv.subtypeEquivRight
    (q := fun p : H₁ × H₂ => p.1 * p.1 = a ∧ p.2 * p.2 = b) fun p => ?_).trans
      (Equiv.subtypeProdEquivProd (p := fun x : H₁ => x * x = a)
        (q := fun y : H₂ => y * y = b)))
  rw [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul]

theorem prod_dih_center_classification {a b : ℕ} (e₁ : H₁ ≃* DihedralGroup (2 ^ a)) (ha : 2 ≤ a)
    (e₂ : H₂ ≃* DihedralGroup (2 ^ b)) (hb : 2 ≤ b) :
    ∀ p ∈ center (H₁ × H₂),
      p = 1 ∨ p = (e₁.symm (zc a), 1) ∨ p = (1, e₂.symm (zc b)) ∨
        p = (e₁.symm (zc a), e₂.symm (zc b)) := by
  intro p hp
  rw [Subgroup.center_prod, mem_prod] at hp
  rcases dih_eq_one_or_of_mem_center e₁ ha hp.1 with h1 | h1 <;>
    rcases dih_eq_one_or_of_mem_center e₂ hb hp.2 with h2 | h2
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Or.inr (Or.inl (Prod.ext h1 h2)))
  · exact Or.inr (Or.inl (Prod.ext h1 h2))
  · exact Or.inr (Or.inr (Or.inr (Prod.ext h1 h2)))

theorem prod_dih_diag_center_fixed {a b : ℕ} (e₁ : H₁ ≃* DihedralGroup (2 ^ a)) (ha : 2 ≤ a)
    (e₂ : H₂ ≃* DihedralGroup (2 ^ b)) (hb : 2 ≤ b) (σ : MulAut (H₁ × H₂)) :
    σ (e₁.symm (zc a), e₂.symm (zc b)) = (e₁.symm (zc a), e₂.symm (zc b)) := by
  set c₁ := e₁.symm (zc a) with hc₁def
  set c₂ := e₂.symm (zc b) with hc₂def
  have hcen := prod_dih_center_classification e₁ ha e₂ hb
  have hcen' : ∀ p ∈ center (H₁ × H₂),
      p = 1 ∨ p = (c₁, 1) ∨ p = (1, c₂) ∨ p = (c₁, c₂) := by
    intro p hp
    simpa only [hc₁def, hc₂def] using hcen p hp
  have hc₁ : c₁ ∈ center H₁ := dih_symm_zc_mem_center e₁ (by omega)
  have hc₂ : c₂ ∈ center H₂ := dih_symm_zc_mem_center e₂ (by omega)
  have hc₁1 : c₁ ≠ 1 := dih_symm_zc_ne_one e₁ (by omega)
  have hc₂1 : c₂ ≠ 1 := dih_symm_zc_ne_one e₂ (by omega)
  have hc₁2 : c₁ * c₁ = 1 := dih_symm_zc_mul_self e₁ (by omega)
  have hc₂2 : c₂ * c₂ = 1 := dih_symm_zc_mul_self e₂ (by omega)
  have hmem12 : ((c₁, c₂) : H₁ × H₂) ∈ center (H₁ × H₂) := by
    rw [Subgroup.center_prod]
    exact ⟨hc₁, hc₂⟩
  have hN : ∀ p, Nat.card {q : H₁ × H₂ // q * q = σ p} = Nat.card {q : H₁ × H₂ // q * q = p} :=
    fun p => card_mul_self_eq_mulEquiv σ p
  obtain ⟨pos₁, lt₁⟩ := dih_card_mul_self_lt e₁ ha
  obtain ⟨pos₂, lt₂⟩ := dih_card_mul_self_lt e₂ hb
  have N1 : Nat.card {q : H₁ × H₂ // q * q = (c₁, c₂)} <
      Nat.card {q : H₁ × H₂ // q * q = (c₁, 1)} := by
    rw [card_mul_self_eq_prod, card_mul_self_eq_prod]
    exact Nat.mul_lt_mul_of_pos_left lt₂ pos₁
  have N2 : Nat.card {q : H₁ × H₂ // q * q = (c₁, c₂)} <
      Nat.card {q : H₁ × H₂ // q * q = (1, c₂)} := by
    rw [card_mul_self_eq_prod, card_mul_self_eq_prod]
    exact Nat.mul_lt_mul_of_pos_right lt₁ pos₂
  have hσ1 : ∀ p, σ p = 1 → p = 1 := fun p h => σ.injective (h.trans (map_one σ).symm)
  rcases hcen' _ (mulEquiv_apply_mem_center σ hmem12) with h | h | h | h
  · exact absurd (congrArg Prod.fst (hσ1 _ h)) hc₁1
  · have := hN (c₁, c₂)
    rw [h] at this
    omega
  · have := hN (c₁, c₂)
    rw [h] at this
    omega
  · exact h

theorem prod_dih_center_fixed {a b : ℕ} (e₁ : H₁ ≃* DihedralGroup (2 ^ a)) (ha : 2 ≤ a)
    (e₂ : H₂ ≃* DihedralGroup (2 ^ b)) (hb : 2 ≤ b) (σ : MulAut (H₁ × H₂))
    (hσ : Odd (orderOf σ)) {c : H₁ × H₂} (hc : c ∈ center (H₁ × H₂)) : σ c = c := by
  set c₁ := e₁.symm (zc a) with hc₁def
  set c₂ := e₂.symm (zc b) with hc₂def
  have hcen := prod_dih_center_classification e₁ ha e₂ hb
  have hcen' : ∀ p ∈ center (H₁ × H₂),
      p = 1 ∨ p = (c₁, 1) ∨ p = (1, c₂) ∨ p = (c₁, c₂) := by
    intro p hp
    simpa only [hc₁def, hc₂def] using hcen p hp
  have hc₁ : c₁ ∈ center H₁ := dih_symm_zc_mem_center e₁ (by omega)
  have hc₂ : c₂ ∈ center H₂ := dih_symm_zc_mem_center e₂ (by omega)
  have hc₁1 : c₁ ≠ 1 := dih_symm_zc_ne_one e₁ (by omega)
  have hc₂1 : c₂ ≠ 1 := dih_symm_zc_ne_one e₂ (by omega)
  have hc₁2 : c₁ * c₁ = 1 := dih_symm_zc_mul_self e₁ (by omega)
  have hc₂2 : c₂ * c₂ = 1 := dih_symm_zc_mul_self e₂ (by omega)
  have hmem12 : ((c₁, c₂) : H₁ × H₂) ∈ center (H₁ × H₂) := by
    rw [Subgroup.center_prod]
    exact ⟨hc₁, hc₂⟩
  have hmem1 : ((c₁, 1) : H₁ × H₂) ∈ center (H₁ × H₂) := by
    rw [Subgroup.center_prod]
    exact ⟨hc₁, one_mem _⟩
  have hσ1 : ∀ p, σ p = 1 → p = 1 := fun p h => σ.injective (h.trans (map_one σ).symm)
  have hfix12 : σ (c₁, c₂) = (c₁, c₂) := by
    simpa only [hc₁def, hc₂def] using prod_dih_diag_center_fixed e₁ ha e₂ hb σ
  have hrel : ((1, c₂) : H₁ × H₂) = (c₁, 1) * (c₁, c₂) := by
    ext
    · exact hc₁2.symm
    · exact (one_mul c₂).symm
  have h1 : σ (c₁, 1) = (c₁, 1) ∨ σ (c₁, 1) = (1, c₂) := by
    rcases hcen' _ (mulEquiv_apply_mem_center σ hmem1) with h | h | h | h
    · exact absurd (congrArg Prod.fst (hσ1 _ h)) hc₁1
    · exact Or.inl h
    · exact Or.inr h
    · have := σ.injective (h.trans hfix12.symm)
      exact absurd (congrArg Prod.snd this).symm hc₂1
  rcases h1 with h1 | h1
  · have h2 : σ (1, c₂) = (1, c₂) := by rw [hrel, map_mul, h1, hfix12]
    rcases hcen' c hc with rfl | rfl | rfl | rfl
    · exact map_one σ
    · exact h1
    · exact h2
    · exact hfix12
  · exfalso
    have h2 : σ (1, c₂) = (c₁, 1) := by
      rw [hrel, map_mul, h1, hfix12]
      ext
      · exact one_mul c₁
      · exact hc₂2
    have hpow : ∀ m : ℕ, (σ ^ (2 * m + 1)) (c₁, 1) = (1, c₂) := by
      intro m
      induction m with
      | zero => simpa using h1
      | succ m ih =>
        rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, pow_add, MulAut.mul_apply, sq,
          MulAut.mul_apply, h1, h2, ih]
    obtain ⟨m, hm⟩ := hσ
    have := hpow m
    rw [← hm, pow_orderOf_eq_one, MulAut.one_apply] at this
    exact hc₁1 (congrArg Prod.fst this)

theorem prod_dih_unswapped {a b : ℕ} (e₁ : H₁ ≃* DihedralGroup (2 ^ a)) (ha : 2 ≤ a)
    (e₂ : H₂ ≃* DihedralGroup (2 ^ b)) (hb : 2 ≤ b) (σ : MulAut (H₁ × H₂))
    (hfix : ∀ c ∈ center (H₁ × H₂), σ c = c) :
    (∀ x : H₁, (σ (x, 1)).2 ∈ center H₂) ∧ ∀ y : H₂, (σ (1, y)).1 ∈ center H₁ := by
  let f₁ : H₁ →* H₂ := (MonoidHom.snd H₁ H₂).comp (σ.toMonoidHom.comp (MonoidHom.inl H₁ H₂))
  let f₂ : H₂ →* H₂ := (MonoidHom.snd H₁ H₂).comp (σ.toMonoidHom.comp (MonoidHom.inr H₁ H₂))
  let g₁ : H₁ →* H₁ := (MonoidHom.fst H₁ H₂).comp (σ.toMonoidHom.comp (MonoidHom.inl H₁ H₂))
  let g₂ : H₂ →* H₁ := (MonoidHom.fst H₁ H₂).comp (σ.toMonoidHom.comp (MonoidHom.inr H₁ H₂))
  have hcomm : ∀ x y, σ (x, 1) * σ (1, y) = σ (1, y) * σ (x, 1) := by
    intro x y
    rw [← map_mul, ← map_mul]
    congr 1
    ext
    · exact (mul_one x).trans (one_mul x).symm
    · exact (one_mul y).trans (mul_one y).symm
  have hgen : ∀ q : H₁ × H₂, q = σ ((σ.symm q).1, 1) * σ (1, (σ.symm q).2) := by
    intro q
    rw [← map_mul]
    conv_lhs => rw [← σ.apply_symm_apply q]
    congr 1
    ext
    · exact (mul_one _).symm
    · exact (one_mul _).symm
  have hcz₁ : centralizer ((⊤ : Subgroup H₁) : Set H₁) = center H₁ := by
    rw [coe_top, centralizer_univ]
  have hcz₂ : centralizer ((⊤ : Subgroup H₂) : Set H₂) = center H₂ := by
    rw [coe_top, centralizer_univ]
  have hD₂ : IsDihNonab (⊤ : Subgroup H₂) := ⟨b, hb, ⟨topEquiv.trans e₂⟩⟩
  have hD₁ : IsDihNonab (⊤ : Subgroup H₁) := ⟨a, ha, ⟨topEquiv.trans e₁⟩⟩
  have key₂ := hD₂.le_centralizer_or_le_centralizer (A := f₁.range) (B := f₂.range) le_top le_top
    (by
      rintro _ ⟨y, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      exact congrArg Prod.snd (hcomm x y))
    (by
      rw [eq_top_iff]
      intro h _
      have hq : h = (σ ((σ.symm (1, h)).1, 1)).2 * (σ (1, (σ.symm (1, h)).2)).2 :=
        congrArg Prod.snd (hgen ((1 : H₁), h))
      rw [hq]
      exact mul_mem (mem_sup_left ⟨_, rfl⟩) (mem_sup_right ⟨_, rfl⟩))
  have key₁ := hD₁.le_centralizer_or_le_centralizer (A := g₁.range) (B := g₂.range) le_top le_top
    (by
      rintro _ ⟨y, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      exact congrArg Prod.fst (hcomm x y))
    (by
      rw [eq_top_iff]
      intro h _
      have hq : h = (σ ((σ.symm (h, 1)).1, 1)).1 * (σ (1, (σ.symm (h, 1)).2)).1 :=
        congrArg Prod.fst (hgen (h, (1 : H₂)))
      rw [hq]
      exact mul_mem (mem_sup_left ⟨_, rfl⟩) (mem_sup_right ⟨_, rfl⟩))
  rw [hcz₁] at key₁
  rw [hcz₂] at key₂
  refine ⟨fun x => ?_, fun y => ?_⟩
  · rcases key₂ with h | h
    · exact h ⟨x, rfl⟩
    · exfalso
      obtain ⟨u, hu⟩ := dih_exists_mul_self_eq_symm_zc e₂ hb
      have hq : (σ (1, u)).2 * (σ (1, u)).2 = 1 :=
        dih_mul_self_of_mem_center e₂ hb (h ⟨u, rfl⟩)
      have hcz₂ : ((1 : H₁), e₂.symm (zc b)) ∈ center (H₁ × H₂) := by
        rw [Subgroup.center_prod]
        exact ⟨one_mem _, dih_symm_zc_mem_center e₂ (by omega)⟩
      have h1 : σ (1, e₂.symm (zc b)) = σ (1, u) * σ (1, u) := by
        rw [← map_mul]
        congr 1
        ext
        · exact (mul_one 1).symm
        · exact hu.symm
      rw [hfix _ hcz₂] at h1
      have := congrArg Prod.snd h1
      rw [Prod.snd_mul, hq] at this
      exact dih_symm_zc_ne_one e₂ (by omega) this
  · rcases key₁ with h | h
    · exfalso
      obtain ⟨u, hu⟩ := dih_exists_mul_self_eq_symm_zc e₁ ha
      have hq : (σ (u, 1)).1 * (σ (u, 1)).1 = 1 :=
        dih_mul_self_of_mem_center e₁ ha (h ⟨u, rfl⟩)
      have hcz₁ : (e₁.symm (zc a), (1 : H₂)) ∈ center (H₁ × H₂) := by
        rw [Subgroup.center_prod]
        exact ⟨dih_symm_zc_mem_center e₁ (by omega), one_mem _⟩
      have h1 : σ (e₁.symm (zc a), 1) = σ (u, 1) * σ (u, 1) := by
        rw [← map_mul]
        congr 1
        ext
        · exact hu.symm
        · exact (mul_one 1).symm
      rw [hfix _ hcz₁] at h1
      have := congrArg Prod.fst h1
      rw [Prod.fst_mul, hq] at this
      exact dih_symm_zc_ne_one e₁ (by omega) this
    · exact h ⟨y, rfl⟩

theorem prod_core [Finite H₂] (hAut : IsPGroup 2 (MulAut H₂)) (σ : MulAut (H₁ × H₂))
    (hσ : Odd (orderOf σ)) (hc : ∀ c ∈ center H₂, σ (1, c) = (1, c))
    (h₁ : ∀ x : H₁, (σ (x, 1)).2 ∈ center H₂) (h₂ : ∀ y : H₂, (σ (1, y)).1 ∈ center H₁) :
    ∀ y : H₂, y⁻¹ * (σ (1, y)).2 ∈ center H₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let τ : H₂ →* H₂ := (MonoidHom.snd H₁ H₂).comp (σ.toMonoidHom.comp (MonoidHom.inr H₁ H₂))
  have hτ : ∀ y, τ y = (σ (1, y)).2 := fun y => rfl
  have hinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [hτ] at hy
    have hcen : σ (1, y) ∈ center (H₁ × H₂) := by
      rw [Subgroup.center_prod, mem_prod, hy]
      exact ⟨h₂ y, one_mem _⟩
    have hy' : ((1 : H₁), y) ∈ center (H₁ × H₂) := by
      have := mulEquiv_apply_mem_center σ.symm hcen
      rwa [MulEquiv.symm_apply_apply] at this
    rw [Subgroup.center_prod, mem_prod] at hy'
    rw [hc y hy'.2] at hy
    exact hy
  have hsurj : Function.Surjective τ := Finite.injective_iff_surjective.1 hinj
  let τe : MulAut H₂ := MulEquiv.ofBijective τ ⟨hinj, hsurj⟩
  have hτe : ∀ y, τe y = (σ (1, y)).2 := fun y => rfl
  have hind : ∀ m : ℕ, ∀ y : H₂, ((τe ^ m) y)⁻¹ * ((σ ^ m) (1, y)).2 ∈ center H₂ := by
    intro m
    induction m with
    | zero =>
      intro y
      rw [pow_zero, pow_zero, MulAut.one_apply, MulAut.one_apply, inv_mul_cancel]
      exact one_mem _
    | succ m ih =>
      intro y
      set p := (σ ^ m) (1, y) with hp
      have hsplit : σ p = σ (p.1, 1) * σ (1, p.2) := by
        rw [← map_mul]
        congr 1
        ext
        · exact (mul_one _).symm
        · exact (one_mul _).symm
      have hstep : ((σ ^ (m + 1)) (1, y)).2 = (σ (p.1, 1)).2 * τe p.2 := by
        rw [pow_succ', MulAut.mul_apply, ← hp, hsplit, Prod.snd_mul, hτe]
      have hτm : (τe ^ (m + 1)) y = τe ((τe ^ m) y) := by rw [pow_succ', MulAut.mul_apply]
      have hζ := ih y
      have hp2 : p.2 = (τe ^ m) y * (((τe ^ m) y)⁻¹ * p.2) := by group
      rw [hstep, hτm, hp2, map_mul]
      set w := τe ((τe ^ m) y)
      set c := (σ (p.1, 1)).2
      set d := τe (((τe ^ m) y)⁻¹ * p.2)
      have hc' : c ∈ center H₂ := h₁ p.1
      have hd : d ∈ center H₂ := mulEquiv_apply_mem_center τe hζ
      have : w⁻¹ * (c * (w * d)) = c * d := by
        rw [← mul_assoc c, ← mem_center_iff.1 hc' w, mul_assoc, inv_mul_cancel_left]
      rw [this]
      exact mul_mem hc' hd
  have hfin : ∀ y : H₂, ((τe ^ orderOf σ) y)⁻¹ * y ∈ center H₂ := by
    intro y
    have := hind (orderOf σ) y
    rwa [pow_orderOf_eq_one, MulAut.one_apply] at this
  let Zc : Subgroup (MulAut H₂) :=
    { carrier := {ρ | ∀ y, y⁻¹ * ρ y ∈ center H₂}
      mul_mem' := by
        intro ρ₁ ρ₂ hρ₁ hρ₂ y
        simp only [Set.mem_setOf_eq] at hρ₁ hρ₂ ⊢
        rw [MulAut.mul_apply]
        have h3 := mulEquiv_apply_mem_center ρ₁ (hρ₂ y)
        have : ρ₂ y = y * (y⁻¹ * ρ₂ y) := by group
        rw [this, map_mul]
        have h4 : y⁻¹ * (ρ₁ y * ρ₁ (y⁻¹ * ρ₂ y)) = (y⁻¹ * ρ₁ y) * ρ₁ (y⁻¹ * ρ₂ y) := by group
        rw [h4]
        exact mul_mem (hρ₁ y) h3
      one_mem' := by
        intro y
        rw [MulAut.one_apply, inv_mul_cancel]
        exact one_mem _
      inv_mem' := by
        intro ρ hρ y
        simp only [Set.mem_setOf_eq] at hρ ⊢
        have h := hρ (ρ⁻¹ y)
        rw [MulAut.apply_inv_self] at h
        have := inv_mem h
        rwa [mul_inv_rev, inv_inv] at this }
  have hmem : τe ^ orderOf σ ∈ Zc := by
    intro y
    have := inv_mem (hfin y)
    rwa [mul_inv_rev, inv_inv] at this
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hAut) τe
  have hcop : (orderOf σ).Coprime (orderOf τe) := by
    rw [hj]
    exact Nat.Coprime.pow_right j (Nat.coprime_two_right.2 hσ)
  obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime hcop
  have hτZ : τe ∈ Zc := hm' ▸ pow_mem hmem m'
  exact hτZ

theorem conj_mem_center_mul {K : Type*} [Group K] (σ : MulAut K) {p q : K}
    (hp : p⁻¹ * σ p ∈ center K) (hq : q⁻¹ * σ q ∈ center K) :
    (p * q)⁻¹ * σ (p * q) ∈ center K := by
  have h : (p * q)⁻¹ * σ (p * q) = q⁻¹ * ((p⁻¹ * σ p) * σ q) := by
    rw [map_mul]
    group
  rw [h, ← mul_assoc q⁻¹, mem_center_iff.1 hp q⁻¹, mul_assoc]
  exact mul_mem hp hq

theorem prod_dih_conj_mem_center {a b : ℕ} (e₁ : H₁ ≃* DihedralGroup (2 ^ a)) (ha : 1 ≤ a)
    (e₂ : H₂ ≃* DihedralGroup (2 ^ b)) (hb : 2 ≤ b) (σ : MulAut (H₁ × H₂))
    (hσ : Odd (orderOf σ)) (p : H₁ × H₂) : p⁻¹ * σ p ∈ center (H₁ × H₂) := by
  haveI : NeZero (2 ^ a) := ⟨by positivity⟩
  haveI : NeZero (2 ^ b) := ⟨by positivity⟩
  haveI : Finite H₁ := Finite.of_equiv _ e₁.symm.toEquiv
  haveI : Finite H₂ := Finite.of_equiv _ e₂.symm.toEquiv
  suffices hsuff : (∀ x : H₁, ((x, 1) : H₁ × H₂)⁻¹ * σ (x, 1) ∈ center (H₁ × H₂)) ∧
      ∀ y : H₂, ((1, y) : H₁ × H₂)⁻¹ * σ (1, y) ∈ center (H₁ × H₂) by
    have hp : p = (p.1, 1) * (1, p.2) := by
      ext
      · exact (mul_one _).symm
      · exact (one_mul _).symm
    rw [hp]
    exact conj_mem_center_mul σ (hsuff.1 p.1) (hsuff.2 p.2)
  have hy_of : ∀ y : H₂, (σ (1, y)).1 ∈ center H₁ → y⁻¹ * (σ (1, y)).2 ∈ center H₂ →
      ((1, y) : H₁ × H₂)⁻¹ * σ (1, y) ∈ center (H₁ × H₂) := by
    intro y h1 h2
    rw [Subgroup.center_prod, mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
      inv_one, one_mul]
    exact ⟨h1, h2⟩
  have hx_of : ∀ x : H₁, x⁻¹ * (σ (x, 1)).1 ∈ center H₁ → (σ (x, 1)).2 ∈ center H₂ →
      ((x, 1) : H₁ × H₂)⁻¹ * σ (x, 1) ∈ center (H₁ × H₂) := by
    intro x h1 h2
    rw [Subgroup.center_prod, mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
      inv_one, one_mul]
    exact ⟨h1, h2⟩
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  ·
    have hcen₁ : ∀ x : H₁, x ∈ center H₁ := dih_mem_center_of_le_one e₁ (by omega)
    have hxcen : ∀ x : H₁, ((x, 1) : H₁ × H₂) ∈ center (H₁ × H₂) := by
      intro x
      rw [Subgroup.center_prod]
      exact ⟨hcen₁ x, one_mem _⟩
    have hc : ∀ c ∈ center H₂, σ (1, c) = (1, c) := by
      intro c hcc
      rcases dih_eq_one_or_of_mem_center e₂ hb hcc with rfl | rfl
      · exact map_one σ
      · obtain ⟨u, hu⟩ := dih_exists_mul_self_eq_symm_zc e₂ hb
        have hcz : ((1 : H₁), e₂.symm (zc b)) ∈ center (H₁ × H₂) := by
          rw [Subgroup.center_prod]
          exact ⟨one_mem _, dih_symm_zc_mem_center e₂ (by omega)⟩
        have h1 : σ (1, e₂.symm (zc b)) = σ (1, u) * σ (1, u) := by
          rw [← map_mul]
          congr 1
          ext
          · exact (mul_one 1).symm
          · exact hu.symm
        have hcen := mulEquiv_apply_mem_center σ hcz
        rw [Subgroup.center_prod, mem_prod] at hcen
        have hfst : (σ (1, e₂.symm (zc b))).1 = 1 := by
          rw [h1, Prod.fst_mul]
          exact dih_mul_self_of_le_one e₁ ha (by omega) _
        rcases dih_eq_one_or_of_mem_center e₂ hb hcen.2 with h2 | h2
        · exfalso
          have : σ (1, e₂.symm (zc b)) = 1 := Prod.ext hfst h2
          have h3 := σ.injective (this.trans (map_one σ).symm)
          exact dih_symm_zc_ne_one e₂ (by omega) (congrArg Prod.snd h3)
        · exact Prod.ext hfst h2
    have hcore := prod_core (dih_isPGroup_mulAut e₂ hb) σ hσ hc
      (fun x => by
        have := mulEquiv_apply_mem_center σ (hxcen x)
        rw [Subgroup.center_prod, mem_prod] at this
        exact this.2)
      (fun y => hcen₁ _)
    refine ⟨fun x => ?_, fun y => hy_of y (hcen₁ _) (hcore y)⟩
    exact mul_mem (inv_mem (hxcen x)) (mulEquiv_apply_mem_center σ (hxcen x))
  ·
    have hfix := fun c (hc : c ∈ center (H₁ × H₂)) => prod_dih_center_fixed e₁ ha2 e₂ hb σ hσ hc
    obtain ⟨h₁, h₂⟩ := prod_dih_unswapped e₁ ha2 e₂ hb σ hfix
    have hcore₂ := prod_core (dih_isPGroup_mulAut e₂ hb) σ hσ
      (fun c hc => hfix _ (by rw [Subgroup.center_prod]; exact ⟨one_mem _, hc⟩)) h₁ h₂
    let σ' : MulAut (H₂ × H₁) := MulAut.congr (MulEquiv.prodComm (M := H₁) (N := H₂)) σ
    have hσ' : ∀ q : H₂ × H₁, σ' q = ((σ (q.2, q.1)).2, (σ (q.2, q.1)).1) := fun q => rfl
    have hord : orderOf σ' = orderOf σ := MulEquiv.orderOf_eq _ σ
    have hcore₁ := prod_core (dih_isPGroup_mulAut e₁ ha2) σ' (hord ▸ hσ)
      (fun c hc => by
        rw [hσ', hfix _ (by rw [Subgroup.center_prod]; exact ⟨hc, one_mem _⟩)])
      (fun y => by rw [hσ']; exact h₂ y)
      (fun x => by rw [hσ']; exact h₁ x)
    exact ⟨fun x => hx_of x (by simpa only [hσ'] using hcore₁ x) (h₁ x),
      fun y => hy_of y (h₂ y) (hcore₂ y)⟩

end Product

section Transfer

variable {G : Type*} [Group G] {S S₁ S₂ : Subgroup G}

theorem IsDihNonab.exists_mul_ne_mul {D : Subgroup G} (hD : IsDihNonab D) :
    ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hD
  obtain ⟨g, h, hgh⟩ := not_comm_of_two_le hk
  refine ⟨(e.symm g : G), (e.symm g).2, (e.symm h : G), (e.symm h).2, fun hc => hgh ?_⟩
  have : e.symm g * e.symm h = e.symm h * e.symm g := Subtype.ext hc
  rw [← map_mul, ← map_mul] at this
  exact e.symm.injective this

private theorem orderOf_mulAutCongr {H K : Type*} [Group H] [Group K] (φ : H ≃* K)
    (σ : MulAut H) : orderOf (MulAut.congr φ σ) = orderOf σ :=
  MulEquiv.orderOf_eq _ σ

private theorem mulAutCongr_apply_apply {H K : Type*} [Group H] [Group K] (φ : H ≃* K)
    (σ : MulAut H) (x : H) : MulAut.congr φ σ (φ x) = φ (σ x) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]

namespace DDDecomp

variable (hd : DDDecomp S S₁ S₂)
include hd

theorem mul_inv_mem_center_of_odd (σ : MulAut ↥S) (hσ : Odd (orderOf σ)) (x : ↥S) :
    x⁻¹ * σ x ∈ center ↥S := by
  obtain ⟨a, ha, ⟨e₁⟩⟩ := hd.dih₁
  obtain ⟨b, hb, ⟨e₂⟩⟩ := hd.dih₂
  have h := prod_dih_conj_mem_center e₁ ha e₂ hb (MulAut.congr (ddProdEquiv hd) σ)
    (by rwa [orderOf_mulAutCongr]) (ddProdEquiv hd x)
  rw [mulAutCongr_apply_apply] at h
  rw [← mulEquiv_apply_mem_center_iff (ddProdEquiv hd), map_mul, map_inv]
  exact h

end DDDecomp

end Transfer

end CFSG.GH72
