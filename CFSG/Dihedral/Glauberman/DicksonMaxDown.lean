module

public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Dihedral.Glauberman.DicksonMaxB

public section

namespace CFSG.Glauberman.Dickson.MaxDown

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure
open CFSG.Glauberman.Dickson.MaxUp

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem exists_le_conj_unipotent (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    {X : Subgroup (PSL2MatrixGroup F)} (hX : IsPGroup p X) :
    ∃ g : PSL2MatrixGroup F, X ≤ (unipotent F).map (MulAut.conj g).toMonoidHom := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hF2 := ringChar_ne_two hF hp2
  have hUcard : Nat.card (unipotent F) = p ^ f := by
    rw [card_unipotent (Ring.two_ne_zero hF2), ← Nat.card_eq_fintype_card, hF]
  have hU : IsPGroup p (unipotent F) := IsPGroup.of_card hUcard
  obtain ⟨P₁, hUP₁⟩ := hU.exists_le_sylow
  obtain ⟨e₁⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P₁
  have hP₁card : Nat.card (P₁ : Subgroup (PSL2MatrixGroup F)) = p ^ f := by
    rw [← Nat.card_congr e₁.toEquiv]
    exact hF
  have hP₁ : (P₁ : Subgroup (PSL2MatrixGroup F)) = unipotent F :=
    (Subgroup.eq_of_le_of_card_ge hUP₁ (by rw [hP₁card, hUcard])).symm
  obtain ⟨P₂, hXP₂⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2MatrixGroup F) P₁ P₂
  refine ⟨g, ?_⟩
  rw [← hP₁]
  have : ((g • P₁ : Sylow p (PSL2MatrixGroup F)) : Subgroup (PSL2MatrixGroup F)) =
      (P₁ : Subgroup (PSL2MatrixGroup F)).map (MulAut.conj g).toMonoidHom := rfl
  rw [← this, hg]
  exact hXP₂

theorem card_borel_map (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (g : PSL2MatrixGroup F) :
    Nat.card ((borel F).map (MulAut.conj g).toMonoidHom) * 2 = (p ^ f - 1) * p ^ f := by
  let : Fintype F := Fintype.ofFinite F
  rw [card_map_conj, card_borel (Ring.two_ne_zero (ringChar_ne_two hF hp2)),
    ← Nat.card_eq_fintype_card, hF]

theorem borel_map_ne_top (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    (g : PSL2MatrixGroup F) : (borel F).map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
  apply ne_top_of_card_lt
  rw [card_psl2_odd hF hp2]
  apply lt_card_psl2_of
  have h := card_borel_map hF hp2 g
  obtain ⟨t, ht⟩ : ∃ t, p ^ f = t + 1 := ⟨p ^ f - 1, by omega⟩
  have ht4 : 4 ≤ t := by omega
  rw [ht] at h ⊢
  have e1 : (t + 1) ^ 2 - 1 = t * (t + 2) := by
    have : (t + 1) ^ 2 = t * (t + 2) + 1 := by ring
    omega
  rw [e1]
  rw [show t + 1 - 1 = t by omega] at h
  nlinarith

theorem eq_of_isCoatom_le {G : Type*} [Group G] {M K : Subgroup G} (hM : IsCoatom M)
    (hMK : M ≤ K) (hK : K ≠ ⊤) : M = K := by
  rcases (IsCoatom.le_iff hM).mp hMK with h | h
  · exact absurd h hK
  · exact h.symm

theorem not_isPGroup_of_isCoatom (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) (hX : IsPGroup p M) : False := by
  have hp' := hp.out
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  obtain ⟨g, hg⟩ := exists_le_conj_unipotent hF hp2 hX
  let : Fintype F := Fintype.ofFinite F
  have hUB : unipotent F ≤ borel F := by
    rintro x ⟨A, ⟨h1, -, -⟩, rfl⟩
    exact ⟨A, h1, rfl⟩
  have hMB := eq_of_isCoatom_le hM (le_trans hg (Subgroup.map_mono hUB))
    (borel_map_ne_top hF hp2 hq5 g)
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have h := card_borel_map hF hp2 g
  rw [← hMB, hk] at h
  have hcop := coprime_half_sub hp2 hf0
  have hodd : Odd (p ^ f) := (hp'.odd_of_ne_two hp2).pow
  obtain ⟨j, hj⟩ := hodd
  have h' : p ^ k = j * p ^ f := by
    rw [hj] at h
    have : 2 * j + 1 - 1 = 2 * j := by omega
    rw [this] at h
    rw [hj]
    nlinarith
  have hjdvd : j ∣ p ^ k := ⟨p ^ f, h'⟩
  have hjp : (p ^ f - 1) / 2 = j := by omega
  rw [hjp] at hcop
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop.symm) hjdvd
  omega

theorem not_isCyclic_of_isCoatom (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    {ν : F} (hν : ¬ IsSquare ν) {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M)
    (hcyc : IsCyclic M) : False := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hF2 := ringChar_ne_two hF hp2
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hq5' : 5 ≤ Fintype.card F := by omega
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := M)
  have hMx : M = Subgroup.zpowers (x : PSL2MatrixGroup F) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := hx ⟨y, hy⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact x.2
  have key : ∀ (A N : Subgroup (PSL2MatrixGroup F)) (g : PSL2MatrixGroup F), A ≤ N →
      Nat.card A < Nat.card N → N.map (MulAut.conj g).toMonoidHom ≠ ⊤ →
      (x : PSL2MatrixGroup F) ∈ A.map (MulAut.conj g).toMonoidHom → False := by
    intro A N g hAN hlt hN hxA
    have hMA : M ≤ A.map (MulAut.conj g).toMonoidHom := by
      rw [hMx, Subgroup.zpowers_le]
      exact hxA
    have hMN := eq_of_isCoatom_le hM (le_trans hMA (Subgroup.map_mono hAN)) hN
    have h1 := Subgroup.card_le_of_le hMA
    rw [hMN, card_map_conj, card_map_conj] at h1
    omega
  have hconj : ∀ (A : Subgroup (PSL2MatrixGroup F)), (x : PSL2MatrixGroup F) ∈ conjSet A →
      ∃ g, (x : PSL2MatrixGroup F) ∈ A.map (MulAut.conj g).toMonoidHom := by
    rintro A ⟨-, g, hg⟩
    exact ⟨g⁻¹, (mem_map_conj_iff A g⁻¹ _).mpr (by simpa using hg)⟩
  have hTN : Nat.card (splitTorus F) <
      Nat.card (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))) := by
    rw [card_normalizer_splitTorus hF2 hq5']
    have := card_splitTorus (Ring.two_ne_zero hF2) (F := F)
    omega
  have hSN : Nat.card (nonsplitTorus ν) <
      Nat.card (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))) := by
    rw [card_normalizer_nonsplitTorus hF2 hq5' hν]
    have := card_nonsplitTorus hF2 hν
    omega
  have hNne : ∀ (N : Subgroup (PSL2MatrixGroup F)) (g : PSL2MatrixGroup F),
      Nat.card N ≤ p ^ f + 1 → N.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro N g hN
    apply ne_top_of_card_lt
    rw [card_map_conj, card_psl2_odd hF hp2]
    exact half_lt_card_psl2 hq5 hN
  rcases mem_conjSet_cases hF2 hq5' hν (x : PSL2MatrixGroup F) with h1 | hU | hT | hS
  ·
    have hM1 : M = ⊥ := by
      rw [hMx, h1, Subgroup.zpowers_one_eq_bot]
    have hB := eq_of_isCoatom_le hM
      (by rw [hM1]; exact bot_le : M ≤ (borel F).map (MulAut.conj 1).toMonoidHom)
      (borel_map_ne_top hF hp2 hq5 1)
    have h := card_borel_map hF hp2 1
    rw [← hB, hM1, Subgroup.card_bot] at h
    have : 20 ≤ (p ^ f - 1) * p ^ f := Nat.mul_le_mul (by omega : 4 ≤ p ^ f - 1) hq5
    omega
  · obtain ⟨g, hg⟩ := hconj _ hU
    have hUB : unipotent F ≤ borel F := by
      rintro y ⟨A, ⟨h1, -, -⟩, rfl⟩
      exact ⟨A, h1, rfl⟩
    refine key _ _ g hUB ?_ (borel_map_ne_top hF hp2 hq5 g) hg
    have h1 : Nat.card (unipotent F : Subgroup (PSL2MatrixGroup F)) = Fintype.card F :=
      card_unipotent (Ring.two_ne_zero hF2)
    have h2 : Nat.card (borel F : Subgroup (PSL2MatrixGroup F)) * 2 =
        (Fintype.card F - 1) * Fintype.card F := card_borel (Ring.two_ne_zero hF2)
    rw [hq] at h1 h2
    have : 4 * p ^ f ≤ (p ^ f - 1) * p ^ f := Nat.mul_le_mul_right _ (by omega)
    have hlt : Nat.card (unipotent F : Subgroup (PSL2MatrixGroup F)) <
        Nat.card (borel F : Subgroup (PSL2MatrixGroup F)) := by omega
    exact hlt
  · obtain ⟨g, hg⟩ := hconj _ hT
    refine key _ _ g Subgroup.le_normalizer hTN (hNne _ g ?_) hg
    rw [card_normalizer_splitTorus hF2 hq5']
    have := card_splitTorus (Ring.two_ne_zero hF2) (F := F)
    omega
  · obtain ⟨g, hg⟩ := hconj _ hS
    refine key _ _ g Subgroup.le_normalizer hSN (hNne _ g ?_) hg
    rw [card_normalizer_nonsplitTorus hF2 hq5' hν]
    have := card_nonsplitTorus hF2 hν
    omega

end CFSG.Glauberman.Dickson.MaxDown

namespace CFSG.Glauberman.Dickson.MaxDown

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure
open CFSG.Glauberman.Dickson.MaxUp

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem mem_normalizer_zpowers {G : Type*} [Group G] {x g : G}
    (h : g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have hconj : ∀ k : ℤ, g * x ^ k * g⁻¹ = (g * x * g⁻¹) ^ k := fun k => by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  have hginv : g⁻¹ * x * g⁻¹⁻¹ = x ∨ g⁻¹ * x * g⁻¹⁻¹ = x⁻¹ := by
    rcases h with h | h
    · left
      calc g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * (g * x * g⁻¹) * g := by rw [h, inv_inv]
        _ = x := by group
    · right
      calc g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * (g * x * g⁻¹)⁻¹ * g := by rw [h, inv_inv, inv_inv]
        _ = x⁻¹ := by group
  have hstab : ∀ (c : G), (c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹) →
      ∀ y ∈ Subgroup.zpowers x, c * y * c⁻¹ ∈ Subgroup.zpowers x := by
    intro c hc y hy
    obtain ⟨k, rfl⟩ := hy
    have hck : c * x ^ k * c⁻¹ = (c * x * c⁻¹) ^ k := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [hck]
    rcases hc with hc | hc
    · rw [hc]
      exact ⟨k, rfl⟩
    · rw [hc, inv_zpow']
      exact ⟨-k, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hstab g h y
  · intro hy
    have := hstab g⁻¹ hginv _ hy
    simpa [mul_assoc] using this

theorem dihedral_conj_r_one {n : ℕ} (a : DihedralGroup n) :
    a * DihedralGroup.r 1 * a⁻¹ = DihedralGroup.r 1 ∨
      a * DihedralGroup.r 1 * a⁻¹ = (DihedralGroup.r 1)⁻¹ := by
  rcases a with i | i
  · left
    rw [DihedralGroup.inv_r, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
    congr 1
    ring
  · right
    rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
      DihedralGroup.inv_r]
    congr 1
    ring

theorem isCoatom_semidirect_eq (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) (E : Subgroup M) [E.Normal]
    (hE : IsPGroup p E) (hE1 : E ≠ ⊥) :
    ∃ g : PSL2MatrixGroup F, M = (borel F).map (MulAut.conj g).toMonoidHom := by
  let E' : Subgroup (PSL2MatrixGroup F) := E.map M.subtype
  have hE' : IsPGroup p E' := hE.map M.subtype
  have hE'1 : E' ≠ ⊥ := by
    intro h
    apply hE1
    rw [eq_bot_iff]
    intro x hx
    have : (x : PSL2MatrixGroup F) ∈ E' := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  obtain ⟨g, hg⟩ := exists_le_conj_unipotent hF hp2 hE'
  have hMN : M ≤ Subgroup.normalizer (E' : Set (PSL2MatrixGroup F)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, Subgroup.Normal.conj_mem inferInstance y' hy' _, ?_⟩
      simp
    · rintro ⟨y', hy', hy'eq⟩
      have hyM : y ∈ M := by
        have : y = x⁻¹ * (y' : PSL2MatrixGroup F) * x := by
          rw [show (y' : PSL2MatrixGroup F) = x * y * x⁻¹ from hy'eq]
          group
        rw [this]
        exact M.mul_mem (M.mul_mem (M.inv_mem hx) y'.2) hx
      refine ⟨⟨y, hyM⟩, ?_, rfl⟩
      have h1 := Subgroup.Normal.conj_mem (inferInstance : E.Normal) y' hy' ⟨x, hx⟩⁻¹
      have h2 : (⟨x, hx⟩⁻¹ * y' * (⟨x, hx⟩⁻¹)⁻¹ : M) = ⟨y, hyM⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [show (y' : PSL2MatrixGroup F) = x * y * x⁻¹ from hy'eq]
        group
      rwa [h2] at h1
  have hle := le_trans hMN (normalizer_le_of_le_conj_unipotent (ringChar_ne_two hF hp2) g hg hE'1)
  exact ⟨g, eq_of_isCoatom_le hM hle (borel_map_ne_top hF hp2 hq5 g)⟩

end CFSG.Glauberman.Dickson.MaxDown

namespace CFSG.Glauberman.Dickson.MaxDown

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure
open CFSG.Glauberman.Dickson.MaxUp

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem isCoatom_dihedral_cases (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    {ν : F} (hν : ¬ IsSquare ν) {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) {z : ℕ}
    (e : M ≃* DihedralGroup z) (hz2 : 2 ≤ z)
    (hz : z ∣ (p ^ f + 1) / 2 ∨ z ∣ (p ^ f - 1) / 2) :
    (∃ g : PSL2MatrixGroup F,
        M = (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))).map
          (MulAut.conj g).toMonoidHom) ∨
      ∃ g : PSL2MatrixGroup F,
        M = (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))).map
          (MulAut.conj g).toMonoidHom := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hF2 := ringChar_ne_two hF hp2
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hq5' : 5 ≤ Fintype.card F := by omega
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  set r : M := e.symm (DihedralGroup.r 1)
  have hxo : orderOf (r : PSL2MatrixGroup F) = z := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hx1 : (r : PSL2MatrixGroup F) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    omega
  have hMN : M ≤ Subgroup.normalizer
      (Subgroup.zpowers (r : PSL2MatrixGroup F) : Set (PSL2MatrixGroup F)) := by
    intro y hy
    apply mem_normalizer_zpowers
    rcases dihedral_conj_r_one (e ⟨y, hy⟩) with h | h
    · left
      have h' := congrArg (fun t => ((e.symm t : M) : PSL2MatrixGroup F)) h
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h'
      exact h'
    · right
      have h' := congrArg (fun t => ((e.symm t : M) : PSL2MatrixGroup F)) h
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h'
      exact h'
  have hR1 : Subgroup.zpowers (r : PSL2MatrixGroup F) ≠ ⊥ := by
    intro h
    apply hx1
    have : (r : PSL2MatrixGroup F) ∈ Subgroup.zpowers (r : PSL2MatrixGroup F) :=
      Subgroup.mem_zpowers _
    rwa [h, Subgroup.mem_bot] at this
  have hNne : ∀ (N : Subgroup (PSL2MatrixGroup F)) (g : PSL2MatrixGroup F),
      Nat.card N ≤ p ^ f + 1 → N.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro N g hN
    apply ne_top_of_card_lt
    rw [card_map_conj, card_psl2_odd hF hp2]
    exact half_lt_card_psl2 hq5 hN
  rcases mem_conjSet_cases hF2 hq5' hν (r : PSL2MatrixGroup F) with h1 | hU | hT | hS
  · exact absurd h1 hx1
  · exfalso
    obtain ⟨-, g, hg⟩ := hU
    have hUcard : Nat.card (unipotent F : Subgroup (PSL2MatrixGroup F)) = p ^ f := by
      have : Nat.card (unipotent F : Subgroup (PSL2MatrixGroup F)) = Fintype.card F :=
        card_unipotent (Ring.two_ne_zero hF2)
      rw [this, hq]
    have h1 := Subgroup.orderOf_dvd_natCard _ hg
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hxo, hUcard] at h1
    have hcop : Nat.Coprime (p ^ f) z := by
      rcases hz with hz | hz
      · exact Nat.Coprime.coprime_dvd_right hz
          (Nat.Coprime.pow_left f (coprime_half_add hp2 hf0))
      · exact Nat.Coprime.coprime_dvd_right hz
          (Nat.Coprime.pow_left f (coprime_half_sub hp2 hf0))
    have := Nat.Coprime.eq_one_of_dvd hcop.symm h1
    omega
  · left
    obtain ⟨-, g, hg⟩ := hT
    have hxT : (r : PSL2MatrixGroup F) ∈ (splitTorus F).map (MulAut.conj g⁻¹).toMonoidHom :=
      (mem_map_conj_iff _ _ _).mpr (by simpa using hg)
    have hRT : Subgroup.zpowers (r : PSL2MatrixGroup F) ≤
        (splitTorus F).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.zpowers_le]
      exact hxT
    refine ⟨g⁻¹, eq_of_isCoatom_le hM
      (le_trans hMN (normalizer_le_of_le_conj_splitTorus hF2 hq5' g⁻¹ hRT hR1)) (hNne _ _ ?_)⟩
    rw [card_normalizer_splitTorus hF2 hq5']
    have := card_splitTorus (Ring.two_ne_zero hF2) (F := F)
    omega
  · right
    obtain ⟨-, g, hg⟩ := hS
    have hxS : (r : PSL2MatrixGroup F) ∈ (nonsplitTorus ν).map (MulAut.conj g⁻¹).toMonoidHom :=
      (mem_map_conj_iff _ _ _).mpr (by simpa using hg)
    have hRS : Subgroup.zpowers (r : PSL2MatrixGroup F) ≤
        (nonsplitTorus ν).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.zpowers_le]
      exact hxS
    refine ⟨g⁻¹, eq_of_isCoatom_le hM
      (le_trans hMN (normalizer_le_of_le_conj_nonsplitTorus hF2 hq5' hν g⁻¹ hRS hR1))
      (hNne _ _ ?_)⟩
    rw [card_normalizer_nonsplitTorus hF2 hq5' hν]
    have := card_nonsplitTorus hF2 hν
    omega

end CFSG.Glauberman.Dickson.MaxDown

namespace CFSG.Glauberman.Dickson.MaxDown

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure
open CFSG.Glauberman.Dickson.MaxUp

theorem not_isCoatom_of_lt {G : Type*} [Group G] [Finite G] {N K : Subgroup G} (hNK : N ≤ K)
    (hlt : Nat.card N < Nat.card K) (hK : K ≠ ⊤) : ¬ IsCoatom N := by
  intro hN
  have := eq_of_isCoatom_le hN hNK hK
  rw [this] at hlt
  exact lt_irrefl _ hlt

theorem not_isCoatom_of_sylow {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {N K D : Subgroup G} (hN : IsPGroup r N) (hNidx : ¬ r ∣ N.index) (hD : IsPGroup r D)
    (hDK : D ≤ K) (hcard : Nat.card D = Nat.card N) (hK : K ≠ ⊤)
    (hNK : Nat.card N < Nat.card K) : ¬ IsCoatom N := by
  have hDidx : ¬ r ∣ D.index := by
    have h1 := N.card_mul_index
    have h2 := D.card_mul_index
    rw [hcard] at h2
    have : D.index = N.index := Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
    rwa [this]
  let PN := hN.toSylow hNidx
  let PD := hD.toSylow hDidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PD PN
  have hNeq : N = D.map (MulAut.conj g).toMonoidHom := by
    have : ((g • PD : Sylow r G) : Subgroup G) = D.map (MulAut.conj g).toMonoidHom := rfl
    rw [← this, hg]
    rfl
  rw [hNeq, isCoatom_map_conj_iff]
  refine not_isCoatom_of_lt hDK (by rw [hcard]; exact hNK) hK

theorem not_isCoatom_normalizer_of_rotation {G : Type*} [Group G] [Finite G] {r : ℕ}
    [Fact r.Prime] {A K : Subgroup G} (hA : IsPGroup r A) (hAidx : ¬ r ∣ A.index)
    (hNA : Nat.card (Subgroup.normalizer (A : Set G)) = 2 * Nat.card A) (hK : K ≠ ⊤) {y s : G}
    (hy : y ∈ K) (hs : s ∈ K) (hyo : orderOf y = Nat.card A) (hs2 : s * s = 1)
    (hsy : s ∉ Subgroup.zpowers y) (hinv : s * y * s⁻¹ = y⁻¹)
    (hlt : 2 * Nat.card A < Nat.card K) :
    ¬ IsCoatom (Subgroup.normalizer (A : Set G)) := by
  set P := Subgroup.zpowers y with hPdef
  have hPcard : Nat.card P = Nat.card A := by rw [Nat.card_zpowers, hyo]
  have hP : IsPGroup r P := by
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    exact IsPGroup.of_card (hPcard.trans hk)
  have hPidx : ¬ r ∣ P.index := by
    have h1 := A.card_mul_index
    have h2 := P.card_mul_index
    rw [hPcard] at h2
    have : P.index = A.index := Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
    rwa [this]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hA.toSylow hAidx) (hP.toSylow hPidx)
  have hPeq : P = A.map (MulAut.conj g).toMonoidHom := by
    have : ((g • hA.toSylow hAidx : Sylow r G) : Subgroup G) =
        A.map (MulAut.conj g).toMonoidHom := rfl
    rw [← this, hg]
    rfl
  have hinvP : ∀ c ∈ P, s * c * s⁻¹ = c⁻¹ := by
    rintro c ⟨k, rfl⟩
    have h1 : s * y ^ k * s⁻¹ = (s * y * s⁻¹) ^ k := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    simp only at h1 ⊢
    rw [h1, hinv, inv_zpow]
  obtain ⟨e⟩ := nonempty_sup_zpowers_mulEquiv_dihedral P inferInstance s hsy hs2 hinvP
  have hDcard : Nat.card (P ⊔ Subgroup.zpowers s : Subgroup G) = 2 * Nat.card A := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hPcard]
  have hDN : P ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (P : Set G) := by
    apply sup_le Subgroup.le_normalizer
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_zpowers (Or.inr hinv)
  have hNP : Subgroup.normalizer (P : Set G) =
      (Subgroup.normalizer (A : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [hPeq, normalizer_map_conj]
  have hDeq : P ⊔ Subgroup.zpowers s = Subgroup.normalizer (P : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge hDN
    rw [hNP, card_map_conj, hNA, hDcard]
  have hDK : P ⊔ Subgroup.zpowers s ≤ K := by
    apply sup_le
    · rw [hPdef, Subgroup.zpowers_le]
      exact hy
    · rw [Subgroup.zpowers_le]
      exact hs
  rw [← isCoatom_map_conj_iff _ g, ← hNP, ← hDeq]
  exact not_isCoatom_of_lt hDK (by rw [hDcard]; exact hlt) hK

end CFSG.Glauberman.Dickson.MaxDown

namespace CFSG.Glauberman.Dickson.MaxDown

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure
open CFSG.Glauberman.Dickson.MaxUp

theorem exists_pgroup_le {G : Type*} [Group G] [Finite G] (K : Subgroup G) {r k : ℕ}
    [Fact r.Prime] (h : r ^ k ∣ Nat.card K) :
    ∃ D : Subgroup G, D ≤ K ∧ Nat.card D = r ^ k ∧ IsPGroup r D := by
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime r h
  refine ⟨D.map K.subtype, ?_, ?_, ?_⟩
  · rintro x ⟨y, -, rfl⟩
    exact y.2
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hD]
  · exact IsPGroup.of_card (by rw [Subgroup.card_map_of_injective K.subtype_injective, hD])

theorem perm_four_rotation : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) ^ 3 = 1 ∧
    Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2 ≠ 1 ∧
    Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 1 = 1 ∧ Equiv.swap (0 : Fin 4) 1 ≠ 1 ∧
    Equiv.swap (0 : Fin 4) 1 * (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) *
        (Equiv.swap (0 : Fin 4) 1)⁻¹ = (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2)⁻¹ := by
  decide

theorem alternating_five_rotation :
    let y : alternatingGroup (Fin 5) :=
      ⟨finRotate 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    let s : alternatingGroup (Fin 5) :=
      ⟨Equiv.swap 1 4 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    y ^ 5 = 1 ∧ y ≠ 1 ∧ s * s = 1 ∧ s ≠ 1 ∧ s * y * s⁻¹ = y⁻¹ := by
  decide

theorem rotation_of_mulEquiv {G X : Type*} [Group G] [Group X] {K : Subgroup G} (e : K ≃* X)
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {y₀ s₀ : X} (hy : y₀ ^ r = 1) (hy1 : y₀ ≠ 1)
    (hs : s₀ * s₀ = 1) (hs1 : s₀ ≠ 1) (hinv : s₀ * y₀ * s₀⁻¹ = y₀⁻¹) :
    ∃ y ∈ K, ∃ s ∈ K, orderOf y = r ∧ s * s = 1 ∧ s ∉ Subgroup.zpowers y ∧
      s * y * s⁻¹ = y⁻¹ := by
  have hyo : orderOf y₀ = r := orderOf_eq_prime hy hy1
  have hso : orderOf s₀ = 2 := orderOf_eq_prime (by rw [pow_two, hs]) hs1
  refine ⟨(e.symm y₀ : G), (e.symm y₀).2, (e.symm s₀ : G), (e.symm s₀).2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hyo]
  · rw [← Subgroup.coe_mul, ← map_mul, hs, map_one, Subgroup.coe_one]
  · intro h
    have := orderOf_dvd_of_mem_zpowers h
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq,
      hyo, hso] at this
    have hr := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : r.Prime)).mp this
    exact hr2 hr.symm
  · rw [← Subgroup.coe_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      ← map_inv, ← map_inv, ← map_mul, ← map_mul, hinv]

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem eq_prime_of_pow_eq_prime {p f n : ℕ} (hp : p.Prime) (hn : n.Prime) (h : p ^ f = n) :
    p = n ∧ f = 1 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h
    exact hn.one_lt.ne' h.symm
  have hpn : p = n := by
    have hdvd : p ∣ n := h ▸ dvd_pow_self p hf0
    exact (Nat.prime_dvd_prime_iff_eq hp hn).mp hdvd
  subst hpn
  have h' : p ^ f = p ^ 1 := by rw [h, pow_one]
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h'⟩

theorem eq_three_two_of_pow_eq_nine {p f : ℕ} (hp : p.Prime) (h : p ^ f = 9) : p = 3 ∧ f = 2 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 ^ 2 := by rw [show 3 ^ 2 = 9 by norm_num, ← h]; exact dvd_pow_self p hf0
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hdvd)
  subst hp3
  have h' : 3 ^ f = 3 ^ 2 := by rw [h]; norm_num
  exact ⟨rfl, Nat.pow_right_injective (by norm_num) h'⟩

end CFSG.Glauberman.Dickson.MaxDown

namespace CFSG.Glauberman.Dickson.MaxDown

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure
open CFSG.Glauberman.Dickson.MaxUp

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem index_eq_of_card {G : Type*} [Group G] [Finite G] {A : Subgroup G} {a n : ℕ}
    (hA : Nat.card A = a) (hG : Nat.card G = n) (ha : 0 < a) : A.index = n / a := by
  have h := A.card_mul_index
  rw [hA, hG] at h
  rw [← h, Nat.mul_div_cancel_left _ ha]

theorem not_isCoatom_normalizer_splitTorus_of_lt
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ f) (h13 : p ^ f < 13) :
    ¬ IsCoatom (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hF2 := ringChar_ne_two hF hp2
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hq5' : 5 ≤ Fintype.card F := by omega
  have hG := card_psl2_odd hF hp2
  have hT : Nat.card (splitTorus F) = (p ^ f - 1) / 2 := by
    rw [card_splitTorus_eq hF2, hq]
  have hN : Nat.card (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))) =
      2 * ((p ^ f - 1) / 2) := by
    rw [card_normalizer_splitTorus hF2 hq5', hT]
  have hB := dickson_psl2_subgroup_existence hF
  have hodd : Odd (p ^ f) := (hp.out.odd_of_ne_two hp2).pow
  have hq_cases : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 ∨ p ^ f = 11 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hq_cases with hq' | hq' | hq' | hq'
  ·
    obtain ⟨K, ⟨e⟩⟩ := hB.2.2.2.2.2.1 (Or.inl (hp.out.odd_of_ne_two hp2))
    have hK : Nat.card K = 12 := by rw [Nat.card_congr e.toEquiv, card_alternatingFour']
    obtain ⟨D, hDK, hDc, hD⟩ := exists_pgroup_le K (r := 2) (k := 2) (by rw [hK]; norm_num)
    have hG' : Nat.card (PSL2MatrixGroup F) = 60 := by rw [hG, hq']; norm_num
    have hN' : Nat.card (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))) = 4 := by
      rw [hN, hq']
    apply not_isCoatom_of_sylow (r := 2) (IsPGroup.of_card (n := 2) (by rw [hN']; norm_num))
      _ hD hDK (by rw [hDc, hN']; norm_num) (ne_top_of_card_lt (by rw [hK, hG']; norm_num))
      (by rw [hN', hK]; norm_num)
    rw [index_eq_of_card hN' hG' (by norm_num)]
    norm_num
  ·
    obtain ⟨K, ⟨e⟩⟩ := hB.2.2.2.2.2.2.1 (by rw [hq']; decide)
    have hK : Nat.card K = 24 := by rw [Nat.card_congr e.toEquiv, card_permFour]
    obtain ⟨h1, h2, h3, h4, h5⟩ := perm_four_rotation
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy, s, hs, hyo, hs2, hsy, hinv⟩ :=
      rotation_of_mulEquiv e (r := 3) (by norm_num) h1 h2 h3 h4 h5
    have hG' : Nat.card (PSL2MatrixGroup F) = 168 := by rw [hG, hq']; norm_num
    have hT' : Nat.card (splitTorus F) = 3 := by rw [hT, hq']
    have hN' : Nat.card (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))) =
        2 * Nat.card (splitTorus F) := by rw [hN, hT]
    apply not_isCoatom_normalizer_of_rotation (r := 3)
      (IsPGroup.of_card (n := 1) (by rw [hT']; norm_num)) _ hN'
      (ne_top_of_card_lt (by rw [hK, hG']; norm_num)) hy hs (by rw [hyo, hT']) hs2 hsy hinv
      (by rw [hT', hK]; norm_num)
    rw [index_eq_of_card hT' hG' (by norm_num)]
    norm_num
  ·
    obtain ⟨K, ⟨e⟩⟩ := hB.2.2.2.2.2.2.1 (by rw [hq']; decide)
    have hK : Nat.card K = 24 := by rw [Nat.card_congr e.toEquiv, card_permFour]
    obtain ⟨D, hDK, hDc, hD⟩ := exists_pgroup_le K (r := 2) (k := 3) (by rw [hK]; norm_num)
    have hG' : Nat.card (PSL2MatrixGroup F) = 360 := by rw [hG, hq']; norm_num
    have hN' : Nat.card (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))) = 8 := by
      rw [hN, hq']
    apply not_isCoatom_of_sylow (r := 2) (IsPGroup.of_card (n := 3) (by rw [hN']; norm_num))
      _ hD hDK (by rw [hDc, hN']; norm_num) (ne_top_of_card_lt (by rw [hK, hG']; norm_num))
      (by rw [hN', hK]; norm_num)
    rw [index_eq_of_card hN' hG' (by norm_num)]
    norm_num
  ·
    obtain ⟨K, ⟨e⟩⟩ := hB.2.2.2.2.2.2.2 (Or.inr (by rw [hq']; decide))
    have hK : Nat.card K = 60 := by rw [Nat.card_congr e.toEquiv, card_alternatingFive']
    obtain ⟨h1, h2, h3, h4, h5⟩ := alternating_five_rotation
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨y, hy, s, hs, hyo, hs2, hsy, hinv⟩ :=
      rotation_of_mulEquiv e (r := 5) (by norm_num) h1 h2 h3 h4 h5
    have hG' : Nat.card (PSL2MatrixGroup F) = 660 := by rw [hG, hq']; norm_num
    have hT' : Nat.card (splitTorus F) = 5 := by rw [hT, hq']
    have hN' : Nat.card (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))) =
        2 * Nat.card (splitTorus F) := by rw [hN, hT]
    apply not_isCoatom_normalizer_of_rotation (r := 5)
      (IsPGroup.of_card (n := 1) (by rw [hT']; norm_num)) _ hN'
      (ne_top_of_card_lt (by rw [hK, hG']; norm_num)) hy hs (by rw [hyo, hT']) hs2 hsy hinv
      (by rw [hT', hK]; norm_num)
    rw [index_eq_of_card hT' hG' (by norm_num)]
    norm_num

theorem not_isCoatom_normalizer_nonsplitTorus_of
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    {ν : F} (hν : ¬ IsSquare ν) (h79 : p ^ f = 7 ∨ p ^ f = 9) :
    ¬ IsCoatom (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hF2 := ringChar_ne_two hF hp2
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hq5' : 5 ≤ Fintype.card F := by omega
  have hG := card_psl2_odd hF hp2
  have hS : Nat.card (nonsplitTorus ν) = (p ^ f + 1) / 2 := by
    rw [card_nonsplitTorus_eq hF2 hν, hq]
  have hN : Nat.card (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))) =
      2 * ((p ^ f + 1) / 2) := by
    rw [card_normalizer_nonsplitTorus hF2 hq5' hν, hS]
  have hB := dickson_psl2_subgroup_existence hF
  rcases h79 with hq' | hq'
  · obtain ⟨K, ⟨e⟩⟩ := hB.2.2.2.2.2.2.1 (by rw [hq']; decide)
    have hK : Nat.card K = 24 := by rw [Nat.card_congr e.toEquiv, card_permFour]
    obtain ⟨D, hDK, hDc, hD⟩ := exists_pgroup_le K (r := 2) (k := 3) (by rw [hK]; norm_num)
    have hG' : Nat.card (PSL2MatrixGroup F) = 168 := by rw [hG, hq']; norm_num
    have hN' : Nat.card (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))) = 8 :=
      by rw [hN, hq']
    apply not_isCoatom_of_sylow (r := 2) (IsPGroup.of_card (n := 3) (by rw [hN']; norm_num))
      _ hD hDK (by rw [hDc, hN']; norm_num) (ne_top_of_card_lt (by rw [hK, hG']; norm_num))
      (by rw [hN', hK]; norm_num)
    rw [index_eq_of_card hN' hG' (by norm_num)]
    norm_num
  · obtain ⟨K, ⟨e⟩⟩ := hB.2.2.2.2.2.2.2 (Or.inr (by rw [hq']; decide))
    have hK : Nat.card K = 60 := by rw [Nat.card_congr e.toEquiv, card_alternatingFive']
    obtain ⟨h1, h2, h3, h4, h5⟩ := alternating_five_rotation
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨y, hy, s, hs, hyo, hs2, hsy, hinv⟩ :=
      rotation_of_mulEquiv e (r := 5) (by norm_num) h1 h2 h3 h4 h5
    have hG' : Nat.card (PSL2MatrixGroup F) = 360 := by rw [hG, hq']; norm_num
    have hS' : Nat.card (nonsplitTorus ν) = 5 := by rw [hS, hq']
    have hN' : Nat.card (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))) =
        2 * Nat.card (nonsplitTorus ν) := by rw [hN, hS]
    apply not_isCoatom_normalizer_of_rotation (r := 5)
      (IsPGroup.of_card (n := 1) (by rw [hS']; norm_num)) _ hN'
      (ne_top_of_card_lt (by rw [hK, hG']; norm_num)) hy hs (by rw [hyo, hS']) hs2 hsy hinv
      (by rw [hS', hK]; norm_num)
    rw [index_eq_of_card hS' hG' (by norm_num)]
    norm_num

end CFSG.Glauberman.Dickson.MaxDown
