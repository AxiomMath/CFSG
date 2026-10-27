module

public import CFSG.Quasithin.H13.L32NInputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneExist

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace Hyp14310One

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem normalizes_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4) :
    T ≤ Subgroup.normalizer (L : Set G) :=
  (h13322 G T L h.hyp.h13 L h.hyp.h13.faithful).1

theorem conjClosure_eq_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4) :
    conjClosure L T = L :=
  le_antisymm
    (conjClosure_le fun _ ht l hl =>
      (Subgroup.mem_normalizer_iff.1 (h.normalizes_F4 h13322 ht) l).1 hl)
    (le_conjClosure L T)

theorem hyp1223_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4) : Hyp1223 G T L V where
  simple := h.fsu.simple
  nonabelian := h.fsu.nonabelian
  qtke := h.fsu.qtke
  sylow := h.fsu.sylow
  notAlt := fun hA => h.hyp.h13.not_excluded (qt13Excluded_of_alt hA)
  maximal := h.fsu.maximal
  faithful := h.fsu.faithful
  quasisimple := h.fsu.quasisimple
  normalizes := h.normalizes_F4 h13322
  irrPlus := by
    have := h.fsu.irrPlus
    rwa [h.conjClosure_eq_F4 h13322] at this

theorem hyp1281One_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) : Hyp1281One G T L V 3 where
  hyp := h.hyp1223_F4 h13322
  n_mem := Or.inl rfl
  quot := nonempty_equiv_SL32_of_lieModel h.hyp.linear
  natural := (hV G T L V h.hyp h.fsu).2.2.2.2
  not_linear := fun hL => h.hyp.h13.not_excluded (Or.inr (Or.inl (Or.inl hL)))
  not_alt9 := fun hA => h.hyp.h13.not_excluded (Or.inr (Or.inr (Or.inl hA)))
  not_m24 := fun hM => h.hyp.h13.not_excluded (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl hM))))))

theorem isTSub_fsuV1_F4 (h : Hyp14310One G T L V) (hV : StmtL32NModule_F4) :
    IsTSub T V (fsuV1 T V) 1 := by
  obtain ⟨-, -, hLTV, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  have hTZ : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    have hZ : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
      (Subgroup.closure_le _).mpr fun _ hz => hz.1
    exact (Subgroup.le_centralizer_iff.mp (hZ.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  refine ⟨inf_le_left, by rw [hV1]; norm_num, fun t ht => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hTV ht) x).mp hxV,
      (Subgroup.mem_normalizer_iff.mp (hTZ ht) x).mp hxZ⟩
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hTV ht) x).mpr hxV,
      (Subgroup.mem_normalizer_iff.mp (hTZ ht) x).mpr hxZ⟩

theorem le_l32nH_F4 (h : Hyp14310One G T L V) (hV : StmtL32NModule_F4) : T ≤ l32nH T V :=
  (h.isTSub_fsuV1_F4 hV).2.2

theorem setting1282One_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) {V₂ : Subgroup G} (hV₂ : IsL32NPlane T V V₂) :
    Setting1282One G T L V 3 (fsuV1 T V) V₂ where
  hyp := h.hyp1281One_F4 h13322 hV
  v1 := h.isTSub_fsuV1_F4 hV
  v2 := hV₂.1
  le := hV₂.2
  nonabelian := h.nonab

theorem exists_plane_F4 (h : Hyp14310One G T L V) (hV : StmtL32NModule_F4) :
    ∃ V₂ : Subgroup G, IsL32NPlane T V V₂ := by
  obtain ⟨hVe, hV8, hLTV, -, -⟩ := hV G T L V h.hyp h.fsu
  have hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨V₂, hV₂, hV₁₂⟩ := exists_tsub_two_of_one (n := 3) h.fsu.sylow.1 hVe.2 hab
    (le_sup_right.trans hLTV) (by rw [hV8]; norm_num) (by norm_num) (h.isTSub_fsuV1_F4 hV)
  exact ⟨V₂, hV₂, hV₁₂⟩

theorem exists_plane_and_g_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) (hg : Exist1282g_F4) :
    ∃ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ ∧ g ∈ p128 T L V ∧
      g ∉ Subgroup.normalizer (fsuV1 T V : Set G) := by
  obtain ⟨V₂, hV₂⟩ := h.exists_plane_F4 hV
  obtain ⟨g, hgP, hgN⟩ := hg G T L V 3 (h.hyp1281One_F4 h13322 hV) (fsuV1 T V) (h.isTSub_fsuV1_F4 hV)
  exact ⟨V₂, g, hV₂, hgP, hgN⟩

end Hyp14310One

end CFSG.Quasithin.H13
