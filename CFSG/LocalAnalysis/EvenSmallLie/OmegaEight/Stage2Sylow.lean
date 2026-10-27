module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Group
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Subgroup Matrix

variable {G : Type*} [Group G]

theorem exists_conj_le_of_not_dvd [Finite G] {p : ℕ} [Fact p.Prime] {P M A : Subgroup G}
    (hAP : A ≤ P) (hA : IsPGroup p A) (hindex : ¬ p ∣ (M.subgroupOf P).index) :
    ∃ y ∈ P, A.map (MulAut.conj y).toMonoidHom ≤ M := by
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p (M.subgroupOf P)))
  have hS₁p : IsPGroup p ((S₀ : Subgroup (M.subgroupOf P)).map (M.subgroupOf P).subtype) :=
    S₀.isPGroup'.map _
  have hS₁i : ¬ p ∣ ((S₀ : Subgroup (M.subgroupOf P)).map (M.subgroupOf P).subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim (Sylow.not_dvd_index S₀) hindex
  have hSM : (hS₁p.toSylow hS₁i : Subgroup P) ≤ M.subgroupOf P := by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subtype_le _
  obtain ⟨c, -, hc⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow ⊤ (hS₁p.toSylow hS₁i)
    le_top (A.subgroupOf P) le_top (hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAP).symm)
  refine ⟨c, c.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 : (MulAut.conj c).toMonoidHom (⟨a, hAP ha⟩ : P) ∈
      (A.subgroupOf P).map (MulAut.conj c).toMonoidHom :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ha)
  have h2 := Subgroup.mem_subgroupOf.1 (hSM (hc h1))
  exact h2

variable (W : Subgroup G) (φ : W ≃* Multiplicative (Fin 12 → ZMod 2))

@[expose] def rhoImg (A : Subgroup G) : Subgroup GL12 := (A.subgroupOf (NW W)).map (rho W φ)

@[expose] def Xof : Subgroup GL12 := (rho W φ).range

variable {W φ}

theorem mem_rhoImg {A : Subgroup G} (hA : A ≤ NW W) {y : GL12} :
    y ∈ rhoImg W φ A ↔ ∃ a ∈ A, rhoG W φ a = y := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.1 ha, rhoG_of_mem a.2⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hA ha⟩, Subgroup.mem_subgroupOf.2 ha, (rhoG_of_mem (hA ha)).symm⟩

theorem rhoG_mem_rhoImg {A : Subgroup G} (hA : A ≤ NW W) {a : G} (ha : a ∈ A) :
    rhoG W φ a ∈ rhoImg W φ A :=
  (mem_rhoImg hA).2 ⟨a, ha, rfl⟩

theorem mem_Xof {y : GL12} : y ∈ Xof W φ ↔ ∃ g ∈ NW W, rhoG W φ g = y := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rhoG_of_mem g.2⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, (rhoG_of_mem hg).symm⟩

theorem rhoG_mem_Xof {g : G} (hg : g ∈ NW W) : rhoG W φ g ∈ Xof W φ := mem_Xof.2 ⟨g, hg, rfl⟩

theorem rhoImg_le_Xof (A : Subgroup G) : rhoImg W φ A ≤ Xof W φ := by
  rintro _ ⟨a, -, rfl⟩
  exact ⟨a, rfl⟩

theorem mem_centralizer_of_rhoG_eq_one {g : G} (hg : g ∈ NW W) (h : rhoG W φ g = 1) :
    g ∈ centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have e := (rhoG_eq_one_iff hg).1 h w hw
  calc w * g = g * w * g⁻¹ * g := by rw [e]
    _ = g * w := by group

theorem centralizer_le_NW : centralizer (W : Set G) ≤ NW W :=
  Subgroup.centralizer_le_normalizer _

theorem rhoG_eq_one_of_mem_centralizer {g : G} (hg : g ∈ centralizer (W : Set G)) :
    rhoG W φ g = 1 := by
  rw [rhoG_eq_one_iff (centralizer_le_NW hg)]
  intro w hw
  rw [Subgroup.mem_centralizer_iff] at hg
  rw [← hg w hw, mul_inv_cancel_right]

theorem card_eq_card_rhoImg_mul {A : Subgroup G} (hA : A ≤ NW W) :
    Nat.card A = Nat.card (rhoImg W φ A) * Nat.card ↥(A ⊓ centralizer (W : Set G)) := by
  set f : A →* GL12 := (rho W φ).comp (Subgroup.inclusion hA) with hf
  have hrange : f.range = rhoImg W φ A := by
    ext y
    rw [MonoidHom.mem_range, mem_rhoImg hA]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, by rw [rhoG_of_mem (hA a.2)]; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, by rw [rhoG_of_mem (hA ha)]; rfl⟩
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ centralizer (W : Set G)) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, ?_⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, ?_⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
    · have h := a.2
      rw [MonoidHom.mem_ker] at h
      exact mem_centralizer_of_rhoG_eq_one (hA a.1.2) (by rw [rhoG_of_mem (hA a.1.2)]; exact h)
    · rw [MonoidHom.mem_ker]
      have := rhoG_eq_one_of_mem_centralizer (φ := φ) a.2.2
      rw [rhoG_of_mem (hA a.2.1)] at this
      exact this
  rw [← hrange, ← hker, ← Subgroup.index_ker f]
  exact (Subgroup.card_mul_index f.ker).symm.trans (mul_comm _ _)

theorem card_inf_centralizer_le {A : Subgroup G} (hA : A ≤ NW W)
    (hAW : A ⊓ centralizer (W : Set G) ≤ W) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {Z : Set Vec12} (hZ : ∀ w : W, (w : G) ∈ A → Multiplicative.toAdd (φ w) ∈ Z) :
    Nat.card ↥(A ⊓ centralizer (W : Set G)) ≤ Nat.card ↥(Z ∩ fixV (rhoImg W φ A)) := by
  refine Nat.card_le_card_of_injective
    (fun a => ⟨Multiplicative.toAdd (φ ⟨a.1, hAW a.2⟩), hZ _ a.2.1, ?_⟩) ?_
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := (mem_rhoImg hA).1 hy
    rw [rhoG_mulVec (hA hb)]
    congr 2
    apply Subtype.ext
    show b * a.1 * b⁻¹ = a.1
    rw [hcomm b hb a.1 a.2.1, mul_inv_cancel_right]
  · intro a a' h
    have h1 := congrArg Subtype.val h
    have h2 := φ.injective (Multiplicative.toAdd.injective h1)
    exact Subtype.ext (congrArg (fun x : W => (x : G)) h2)

theorem inf_centralizer_le_W {A : Subgroup G} (hA : IsPGroup 2 A)
    (hN1 : ∀ S : Subgroup G, S ≤ centralizer (W : Set G) → IsPGroup 2 S → S ≤ W) :
    A ⊓ centralizer (W : Set G) ≤ W :=
  hN1 _ inf_le_right (hA.to_le inf_le_left)

theorem commute_of_sq_eq_one {A : Subgroup G} (hsq : ∀ x ∈ A, x * x = 1) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) : a * b = b * a := by
  have h := hsq _ (A.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
    _ = b * a := by rw [_root_.mul_inv_rev, ha', hb']

theorem isPGroup_of_sq_eq_one {A : Subgroup G} (hsq : ∀ x ∈ A, x * x = 1) : IsPGroup 2 A :=
  fun x => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hsq x x.2)⟩

theorem conj_eq_of_mem_centralizer {t w : G} (h : w ∈ centralizer ({t} : Set G)) :
    t * w * t⁻¹ = w := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  rw [← h, mul_inv_cancel_right]

theorem card_le_of_le_centralizer [Finite G] {t : G} {TH : Subgroup G} {TC : Subgroup GL12}
    (hTHi : ¬ 2 ∣ (TH.subgroupOf (centralizer ({t} : Set G))).index)
    (hTHc : TH ≤ centralizer ({t} : Set G)) (hTHN : TH ≤ NW W)
    (hN1 : ∀ S : Subgroup G, S ≤ centralizer (W : Set G) → IsPGroup 2 S → S ≤ W)
    (hρ : ∀ x ∈ TH, rhoG W φ x ∈ TC) (htN : t ∈ NW W) {B : ℕ}
    (hoff : ∀ E : Subgroup GL12, E ≤ TC → (∀ x ∈ E, x * x = 1) → E ≠ ⊥ →
      Nat.card E * Nat.card ↥(fixM (rhoG W φ t : Mat12) ∩ fixV E) ≤ B)
    (hfix : Nat.card (fixM (rhoG W φ t : Mat12)) ≤ B)
    (E : Subgroup G) (hE : E ≤ centralizer ({t} : Set G)) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, -, hle⟩ := exists_conj_le_of_not_dvd (p := 2) hE (isPGroup_of_sq_eq_one hsq) hTHi
  set E' := E.map (MulAut.conj h).toMonoidHom with hE'
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hsq' : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hsq e he, map_one]
  have hE'N : E' ≤ NW W := hle.trans hTHN
  rw [← hcard, card_eq_card_rhoImg_mul hE'N]
  have hAW := inf_centralizer_le_W (W := W) (isPGroup_of_sq_eq_one hsq') hN1
  have hk := card_inf_centralizer_le (φ := φ) hE'N hAW
    (fun a ha b hb => commute_of_sq_eq_one hsq' ha hb) (Z := fixM (rhoG W φ t : Mat12))
    (fun w hw => (mem_fixM_rhoG_iff htN w).2 (conj_eq_of_mem_centralizer (hTHc (hle hw))))
  by_cases hbot : rhoImg W φ E' = ⊥
  · rw [hbot, Subgroup.card_bot, one_mul]
    rw [hbot] at hk
    exact hk.trans ((Nat.card_mono (Set.toFinite _) Set.inter_subset_left).trans hfix)
  · have hle' : rhoImg W φ E' ≤ TC := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := (mem_rhoImg hE'N).1 hy
      exact hρ a (hle ha)
    have hsq'' : ∀ y ∈ rhoImg W φ E', y * y = 1 := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := (mem_rhoImg hE'N).1 hy
      rw [← rhoG_mul (hE'N ha) (hE'N ha), hsq' a ha, rhoG_one]
    exact (Nat.mul_le_mul_left _ hk).trans (hoff _ hle' hsq'' hbot)

end CFSG.EvenSmallLie.OmegaEight.Stage2
