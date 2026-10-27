module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndCtx
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.Quasithin.Background.G6Basic
public import CFSG.Quasithin.H13.GoldschmidtM22EndN1b
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

section Main

variable [Fact (IsElemAbelianMod (UU T L V) (quasithinOmegaOneCenter T))]
  (h : Hyp6Sec2 G T M L V)

include h in

theorem rep_eq_of_mem_V_F4 (h6211 : Stmt6_2_11_F4) (a b : ↥(HH T)) (haV : (a : G) ∈ V)
    (hbV : (b : G) ∈ V) (ha : rep T L V a ≠ 1) (hb : rep T L V b ≠ 1) :
    rep T L V a = rep T L V b := by
  have hidx := relIndex_V_CHU_F4 h h6211
  have hinv : (a : G)⁻¹ ∈ CHU T L V → (a : G) ∈ CHU T L V := fun hh => by
    simpa using (CHU T L V).inv_mem hh
  have hA : (a : G)⁻¹ * b ∈ V ⊓ CHU T L V :=
    mul_mem_of_relIndex_two hidx (V.inv_mem haV) hbV
      (fun hh => ha ((rep_eq_one_iff a).mpr (hinv (Subgroup.mem_inf.mp hh).2)))
      (fun hh => hb ((rep_eq_one_iff b).mpr (Subgroup.mem_inf.mp hh).2))
  have h1 : rep T L V (a⁻¹ * b) = 1 :=
    (rep_eq_one_iff _).mpr (by simpa using (Subgroup.mem_inf.mp hA).2)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

include h in

theorem rep_comm_of_normalizer_F4 (h6211 : Stmt6_2_11_F4) (a : ↥(HH T)) (haV : (a : G) ∈ V)
    (ha1 : rep T L V a ≠ 1) (x : ↥(HH T)) (hx : (x : G) ∈ Subgroup.normalizer (V : Set G)) :
    rep T L V x * rep T L V a = rep T L V a * rep T L V x := by
  have hv1 : ((x * a * x⁻¹ : ↥(HH T)) : G) ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp hx (a : G)).mp haV
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hrep : rep T L V (x * a * x⁻¹) = rep T L V x * rep T L V a * (rep T L V x)⁻¹ := by
    simp [map_mul, map_inv]
  have hne : rep T L V (x * a * x⁻¹) ≠ 1 := by
    rw [hrep]
    intro h1
    apply ha1
    calc rep T L V a = (rep T L V x)⁻¹ * (rep T L V x * rep T L V a * (rep T L V x)⁻¹) *
          rep T L V x := by group
      _ = 1 := by rw [h1]; group
  have heq := rep_eq_of_mem_V_F4 h h6211 a (x * a * x⁻¹) haV hv1 ha1 hne
  rw [hrep] at heq
  exact (mul_inv_eq_iff_eq_mul.mp heq.symm)

include h in

theorem rep_o2_F4 (h6210 : Stmt6_2_10_F4) :
    ∀ P : Subgroup ↥(HH T), P.Normal → (∀ p ∈ P, ∃ k : ℕ, rep T L V p ^ 2 ^ k = 1) →
      P ≤ (rep T L V).ker := by
  intro P hP hk p hp
  have hO := isO2Trivial_CHU_F4 h h6210
  have key : P.map (HH T).subtype ≤ CHU T L V := by
    refine hO _ (Subgroup.map_subtype_le _) ?_ ?_
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro g
      have hconj : ∀ y : G, ∀ hy : y ∈ HH T, ∀ q : ↥(HH T), q ∈ P →
          y * (q : G) * y⁻¹ ∈ P.map (HH T).subtype := fun y hy q hq =>
        ⟨⟨y, hy⟩ * q * ⟨y, hy⟩⁻¹, hP.conj_mem q hq ⟨y, hy⟩, by simp⟩
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hconj x hx q hq
      · intro hg
        obtain ⟨q, hq, hqe⟩ := hg
        have hg' : g = x⁻¹ * (q : G) * x⁻¹⁻¹ := by
          have hqe' : (q : G) = x * g * x⁻¹ := hqe
          rw [hqe']
          group
        rw [hg']
        exact hconj x⁻¹ ((HH T).inv_mem hx) q hq
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨k, hk'⟩ := hk q hq
      refine ⟨k, (rep_eq_one_iff (q ^ 2 ^ k)).mp ?_⟩
      rw [map_pow]
      exact hk'
  exact (rep_eq_one_iff p).mpr (key ⟨p, hp, rfl⟩)

include h in

theorem isQuotientOfSQTK_HH_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h6210 : Stmt6_2_10_F4) :
    IsQuotientOfSQTK ↥(HH T) := by
  have hO2 : pCoreOf 2 (HH T) ≠ ⊥ := by
    intro h0
    have hU := UU_le_pCore_F4 h h6210
    have hZU := Z_le_UU h hZ
    have : quasithinOmegaOneCenter T = ⊥ := le_bot_iff.mp (h0 ▸ hZU.trans hU)
    rw [this] at hZ
    simp at hZ
  have hS := sqtkGroup_of_pCoreOf_ne_bot h.toHyp611.qtke h.toHyp611.simple h.toHyp611.nonabelian hO2
  exact ⟨↥(HH T), inferInstance, inferInstance, SQTKGroup.isSQTKCat hS, MonoidHom.id _,
    Function.surjective_id⟩

end Main

end CFSG.Quasithin.H13.GM22
