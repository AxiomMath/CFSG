module

public import CFSG.LargeExtraspecial.AS35CS63Bar
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap

namespace S63

namespace Six

variable {G : Type} [Group G] {S : Setting G} (K : Six S)

@[expose] def CQt : Subgroup (centralizer ({K.t} : Set G)) :=
  S.QG.subgroupOf (centralizer ({K.t} : Set G))

theorem mem_CQt {e : centralizer ({K.t} : Set G)} : e ∈ K.CQt ↔ (e : G) ∈ S.QG := mem_subgroupOf

@[expose] noncomputable def Fbar : Subgroup (Cbar K.t) := K.CQt.map (piC K.t)

theorem mem_Fbar_of {e : centralizer ({K.t} : Set G)} (he : (e : G) ∈ S.QG) :
    piC K.t e ∈ K.Fbar :=
  ⟨e, K.mem_CQt.mpr he, rfl⟩

theorem exists_of_mem_Fbar {x : Cbar K.t} (hx : x ∈ K.Fbar) :
    ∃ e : centralizer ({K.t} : Set G), (e : G) ∈ S.QG ∧ piC K.t e = x := by
  obtain ⟨e, he, rfl⟩ := hx
  exact ⟨e, K.mem_CQt.mp he, rfl⟩

theorem zeta_mem_Fbar : K.zeta ∈ K.Fbar := K.mem_Fbar_of S.z_mem_QG

theorem Fbar_le_centralizer : K.Fbar ≤ centralizer ({K.zeta} : Set (Cbar K.t)) := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := K.exists_of_mem_Fbar hx
  rw [mem_centralizer_singleton_iff, zeta, ← map_mul, ← map_mul]
  exact congrArg (piC K.t) (Subtype.ext (S.z_comm_QG he))

theorem conj_mem_Fbar {c x : Cbar K.t} (hc : c ∈ centralizer ({K.zeta} : Set (Cbar K.t)))
    (hx : x ∈ K.Fbar) : c * x * c⁻¹ ∈ K.Fbar := by
  obtain ⟨c, rfl⟩ := piC_surjective K.t c
  obtain ⟨e, he, rfl⟩ := K.exists_of_mem_Fbar hx
  have hcM : (c : G) ∈ S.M := K.mem_M_of_comm (mem_centralizer_singleton_iff.mp hc)
  rw [← map_inv, ← map_mul, ← map_mul]
  exact K.mem_Fbar_of (S.conj_mem_QG hcM he)

theorem eq_zeta_of_mem_Fbar {τ : Cbar K.t} (hτF : τ ∈ K.Fbar) (hτ : IsConj K.zeta τ) :
    τ = K.zeta := by
  obtain ⟨c, rfl⟩ := K.exists_of_isConj hτ
  obtain ⟨e, he, he'⟩ := K.exists_of_mem_Fbar hτF
  rw [eq_comm, piC_eq_iff K.ht2] at he'
  have hQ : (c : G) * S.z * (c : G)⁻¹ ∈ S.QG := by
    rcases he' with h | h
    · change (e : G) = (c : G) * S.z * (c : G)⁻¹ at h
      rw [← h]
      exact he
    · change (e : G) = (c : G) * S.z * (c : G)⁻¹ * K.t at h
      have h2 : (c : G) * S.z * (c : G)⁻¹ = e * K.t := by
        rw [h]
        calc (c : G) * S.z * (c : G)⁻¹ = (c : G) * S.z * (c : G)⁻¹ * (K.t * K.t) := by
              rw [K.ht2, mul_one]
          _ = (c : G) * S.z * (c : G)⁻¹ * K.t * K.t := by group
      rw [h2]
      exact S.QG.mul_mem he K.htQ
  have h1 := K.hW _ hQ
  rw [zeta]
  exact congrArg (piC K.t) (Subtype.ext h1)

theorem Fbar_le_Hbar : K.Fbar ≤ K.Hbar := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := K.exists_of_mem_Fbar hx
  exact K.mem_Hbar_of (mem_Hhat_of_mem_QG K.htQ K.ht2 he (mem_centralizer_singleton_iff.mp e.2))

theorem centralizer_Fbar_le_Hbar : centralizer (K.Fbar : Set (Cbar K.t)) ≤ K.Hbar := by
  intro x hx
  obtain ⟨c, rfl⟩ := piC_surjective K.t x
  have hcz := mem_centralizer_iff.mp hx K.zeta K.zeta_mem_Fbar
  have hcM : (c : G) ∈ S.M := K.mem_M_of_comm hcz.symm
  refine K.mem_Hbar_of ⟨hcM, mem_centralizer_singleton_iff.mp c.2, fun e he het => ?_⟩
  set e' : centralizer ({K.t} : Set G) := ⟨e, mem_centralizer_singleton_iff.mpr het⟩
  have h1 := mem_centralizer_iff.mp hx (piC K.t e') (K.mem_Fbar_of he)
  rw [← map_mul, ← map_mul, piC_eq_iff K.ht2] at h1
  rcases h1 with h | h
  · change (c : G) * e = e * c at h
    rw [h, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · change (c : G) * e = e * c * K.t at h
    have h2 : (c : G) * e * (c : G)⁻¹ * e⁻¹ = K.t := by
      rw [h, show e * (c : G) * K.t = e * ((c : G) * K.t) by group,
        mem_centralizer_singleton_iff.mp c.2]
      calc e * (K.t * (c : G)) * (c : G)⁻¹ * e⁻¹ = e * K.t * e⁻¹ := by group
        _ = K.t := by rw [het]; group
    rw [h2]
    exact subset_closure (by simp)

theorem sup_centralizer_le_Hbar : K.Fbar ⊔ centralizer (K.Fbar : Set (Cbar K.t)) ≤ K.Hbar :=
  sup_le K.Fbar_le_Hbar K.centralizer_Fbar_le_Hbar

theorem piC_mem_zpowers_of_mem_Z2 {a : centralizer ({K.t} : Set G)}
    (ha : (a : G) ∈ Z2 S K.t) : piC K.t a ∈ zpowers K.zeta := by
  rcases (mem_Z2_iff K.htQ K.ht2).mp ha with h | h | h | h
  · rw [(piC_eq_one_iff K.ht2).mpr (Or.inl h)]
    exact one_mem _
  · have : a = K.zC := Subtype.ext h
    rw [this]
    exact mem_zpowers _
  · rw [(piC_eq_one_iff K.ht2).mpr (Or.inr h)]
    exact one_mem _
  · have : piC K.t a = K.zeta := by
      rw [zeta, piC_eq_iff K.ht2]
      right
      change S.z = (a : G) * K.t
      rw [h, mul_assoc, K.ht2, mul_one]
    rw [this]
    exact mem_zpowers _


theorem mem_zpowers_of_mem_Hbar [Finite G] {a b : Cbar K.t} (ha : a ∈ K.Hbar)
    (hb : b ∈ K.Hbar) :
    a * b * a⁻¹ * b⁻¹ ∈ zpowers K.zeta ∧ a * a ∈ zpowers K.zeta := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  rw [SetLike.mem_coe, mem_subgroupOf] at ha' hb'
  refine ⟨?_, ?_⟩
  · have e : piC K.t a' * piC K.t b' * (piC K.t a')⁻¹ * (piC K.t b')⁻¹ =
        piC K.t (a' * b' * a'⁻¹ * b'⁻¹) := by simp only [map_mul, map_inv]
    rw [e]
    exact K.piC_mem_zpowers_of_mem_Z2 (commutator_mem_Z2_of_mem_Hhat ha' hb')
  · rw [← map_mul]
    exact K.piC_mem_zpowers_of_mem_Z2 (sq_mem_Z2_of_mem_Hhat ha')

theorem comm_of_piC_comm {e f : centralizer ({K.t} : Set G)} (he : (e : G) ∈ S.QG)
    (hf : (f : G) ∈ S.QG) (h : piC K.t e * piC K.t f = piC K.t f * piC K.t e) :
    (e : G) * f = f * e := by
  rw [← map_mul, ← map_mul, piC_eq_iff K.ht2] at h
  rcases h with h | h
  · exact h.symm
  · exfalso
    change (f : G) * e = e * f * K.t at h
    rcases S.mul_comm_or he hf with h' | h'
    · rw [h'] at h
      exact K.ht1 (mul_eq_left.mp h.symm)
    · rw [h'] at h
      have hz' : S.z * ((f : G) * e) = ((f : G) * e) * S.z :=
        (S.z_comm (S.M.mul_mem (S.QG_le_M hf) (S.QG_le_M he))).symm
      rw [hz', mul_assoc] at h
      have h2 : S.z * K.t = 1 := mul_eq_left.mp h.symm
      apply K.htz
      calc K.t = S.z * (S.z * K.t) := by rw [← mul_assoc, S.z_mul_z, one_mul]
        _ = S.z := by rw [h2, mul_one]

theorem mem_center_Fbar_iff [Finite G] {x : Cbar K.t} (hx : x ∈ K.Fbar) :
    (∀ y ∈ K.Fbar, x * y = y * x) ↔ x = 1 ∨ x = K.zeta := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := K.exists_of_mem_Fbar hx
    have hcc : (e : G) ∈
        S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({K.t} : Set G) : Subgroup G) : Set G) := by
      refine ⟨he, mem_centralizer_iff.mpr fun f hf => ?_⟩
      obtain ⟨hfQ, hft⟩ := mem_inf.mp hf
      set f' : centralizer ({K.t} : Set G) := ⟨f, hft⟩
      exact (K.comm_of_piC_comm he hfQ (h _ (K.mem_Fbar_of (e := f') hfQ))).symm
    rcases (S.mem_centralizer_centralizer_iff K.htQ).mp hcc with h1 | h1 | h1 | h1
    · left
      exact (piC_eq_one_iff K.ht2).mpr (Or.inl h1)
    · right
      rw [zeta]
      exact congrArg (piC K.t) (Subtype.ext h1)
    · left
      exact (piC_eq_one_iff K.ht2).mpr (Or.inr h1)
    · right
      rw [zeta, eq_comm, piC_eq_iff K.ht2]
      right
      change (e : G) = S.z * K.t
      rw [h1, S.z_comm_QG K.htQ]
  · rintro (rfl | rfl) y hy
    · group
    · exact (mem_centralizer_singleton_iff.mp (K.Fbar_le_centralizer hy)).symm

theorem commutator_mem_Fbar {x y : Cbar K.t} (hx : x ∈ K.Fbar) (hy : y ∈ K.Fbar) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = K.zeta := by
  obtain ⟨e, he, rfl⟩ := K.exists_of_mem_Fbar hx
  obtain ⟨f, hf, rfl⟩ := K.exists_of_mem_Fbar hy
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rcases S.commutator_eq_one_or_z he hf with h | h
  · left
    exact (piC_eq_one_iff K.ht2).mpr (Or.inl h)
  · right
    exact congrArg (piC K.t) (Subtype.ext h)

theorem sq_mem_Fbar [Finite G] {x : Cbar K.t} (hx : x ∈ K.Fbar) : x ^ 2 = 1 ∨ x ^ 2 = K.zeta := by
  obtain ⟨e, he, rfl⟩ := K.exists_of_mem_Fbar hx
  rw [← map_pow]
  rcases S.sq_eq_one_or_z he with h | h
  · left
    exact (piC_eq_one_iff K.ht2).mpr (Or.inl h)
  · right
    exact congrArg (piC K.t) (Subtype.ext h)

theorem card_CQ [Finite G] :
    Nat.card ↥(S.QG ⊓ centralizer ({K.t} : Set G)) = 2 ^ (2 * S.width) := by
  have h := relIndex_mul_card (S.QG ⊓ centralizer ({K.t} : Set G)) S.QG
  rw [S.relIndex_centralizer_eq_two K.htQ K.ht1 K.htz,
    inf_eq_left.mpr (inf_le_left : S.QG ⊓ centralizer ({K.t} : Set G) ≤ S.QG),
    S.card_QG_eq_card_Q, S.card_Q_eq, pow_add, pow_one] at h
  omega

theorem card_CQ_le : Nat.card ↥(S.QG ⊓ centralizer ({K.t} : Set G)) ≤ 2 * Nat.card K.Fbar := by
  classical
  set φ := (piC K.t).comp (inclusion (inf_le_right :
    S.QG ⊓ centralizer ({K.t} : Set G) ≤ centralizer ({K.t} : Set G))) with hφ
  have hrange : φ.range = K.Fbar := by
    rw [hφ, MonoidHom.range_comp, inclusion_range, inf_subgroupOf_right]
    rfl
  have hker : Nat.card φ.ker ≤ 2 := by
    let f : φ.ker → Bool := fun x => decide (((x : ↥(S.QG ⊓ centralizer ({K.t} : Set G))) : G) =
      K.t)
    have hmem : ∀ x : φ.ker, ((x : ↥(S.QG ⊓ centralizer ({K.t} : Set G))) : G) = 1 ∨
        ((x : ↥(S.QG ⊓ centralizer ({K.t} : Set G))) : G) = K.t :=
      fun x => (piC_eq_one_iff K.ht2).mp (MonoidHom.mem_ker.mp x.2)
    have hf : Function.Injective f := by
      intro a b hab
      refine Subtype.ext (Subtype.ext ?_)
      simp only [f] at hab
      rcases hmem a with ha | ha <;> rcases hmem b with hb | hb
      · rw [ha, hb]
      · rw [ha, hb] at hab
        exact absurd (by simpa using hab) K.ht1.symm
      · rw [ha, hb] at hab
        exact absurd (by simpa using hab.symm) K.ht1.symm
      · rw [ha, hb]
    calc Nat.card φ.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  have h1 := card_mul_index φ.ker
  rw [index_ker, hrange] at h1
  calc Nat.card ↥(S.QG ⊓ centralizer ({K.t} : Set G)) = Nat.card φ.ker * Nat.card K.Fbar :=
        h1.symm
    _ ≤ 2 * Nat.card K.Fbar := Nat.mul_le_mul_right _ hker

theorem card_Fbar [Finite G] (hn : 3 ≤ S.width) : 2 ^ 5 ≤ Nat.card K.Fbar := by
  have h1 := K.card_CQ_le
  rw [K.card_CQ] at h1
  have h2 : 2 ^ 6 ≤ 2 ^ (2 * S.width) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem exists_not_comm_CQ [Finite G] (hn : 2 ≤ S.width) :
    ∃ e ∈ S.QG ⊓ centralizer ({K.t} : Set G), ∃ f ∈ S.QG ⊓ centralizer ({K.t} : Set G),
      e * f ≠ f * e := by
  by_contra h
  push Not at h
  have h1 := S.card_le_of_commute inf_le_left h
  rw [K.card_CQ] at h1
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  omega

theorem isExtraspecial_Fbar [Finite G] (hn : 3 ≤ S.width) : IsExtraspecialPGroup 2 K.Fbar := by
  refine isExtraspecialPGroup_two_of_center (c := K.zeta) (K.isPGroup_Hbar.to_le K.Fbar_le_Hbar)
    K.zeta_mem_Fbar K.zeta_ne_one (fun x hx => K.mem_center_Fbar_iff hx)
    (fun x hx y hy => K.commutator_mem_Fbar hx hy) (fun x hx => K.sq_mem_Fbar hx) ?_
  obtain ⟨e, ⟨heQ, het⟩, f, ⟨hfQ, hft⟩, hef⟩ := K.exists_not_comm_CQ (by omega)
  refine ⟨piC K.t ⟨e, het⟩, K.mem_Fbar_of heQ, piC K.t ⟨f, hft⟩, K.mem_Fbar_of hfQ, ?_⟩
  intro h
  exact hef (K.comm_of_piC_comm (e := ⟨e, het⟩) (f := ⟨f, hft⟩) heQ hfQ h)

end Six

end S63

end CFSG.LargeExtraspecial
