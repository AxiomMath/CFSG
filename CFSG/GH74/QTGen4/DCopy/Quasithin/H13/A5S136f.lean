module

public import CFSG.Quasithin.H13.A5S136f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136e

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem le_normalizer_V_of_Vv_F4 (h1326 : Input1326Two_F4)
    (h : Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G)) :
    Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨l, -, hlσ⟩ := (S.frame.image_L pb).2 pb_sign
  have key : ∀ g ∈ Subgroup.centralizer ({S.v12} : Set G), ∀ x ∈ V, g * x * g⁻¹ ∈ V := by
    intro g hg x hx
    have hgN := h hg

    have huV : (l : G) * S.v12 * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp l.2 _).mp S.v12_mem_V
    have hψu : S.frame.ψ ⟨(l : G) * S.v12 * (l : G)⁻¹, huV⟩ = pact pb E12 := by
      rw [S.psi_conj l ⟨S.v12, S.v12_mem_V⟩, hlσ, S.psi_v12]
    have huVv : (l : G) * S.v12 * (l : G)⁻¹ ∈ S.Vv :=
      S.mem_Vv.2 ⟨huV, by rw [hψu]; exact c01_pb_E12⟩
    have hwVv : g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹ ∈ S.Vv :=
      (Subgroup.mem_normalizer_iff.mp hgN _).mp huVv
    have hwV := S.Vv_le_V hwVv

    have hws : ¬ IsSing (S.frame.ψ ⟨_, hwV⟩) := by
      rw [← h1326 G T L V S g ⟨_, huV⟩ ⟨_, hwV⟩ rfl, hψu]
      exact not_isSing_pb_E12
    have hw1 : S.frame.ψ ⟨_, hwV⟩ ≠ 1 := by
      intro h1
      have h2 : g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹ = 1 :=
        congrArg Subtype.val (S.frame.ψ.injective (h1.trans (map_one _).symm))
      have h3 : (l : G) * S.v12 * (l : G)⁻¹ = 1 := by
        have : (l : G) * S.v12 * (l : G)⁻¹ = g⁻¹ * (g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹) * g :=
          by group
        rw [this, h2]
        group
      have h4 : (⟨_, huV⟩ : ↥V) = 1 := Subtype.ext h3
      rw [h4, map_one] at hψu
      exact pb_E12_ne_one hψu.symm

    obtain ⟨σ', hσ', hσ'w⟩ := exists_alt_pact E12 _ E12_ne_one hw1
      (iff_of_false not_isSing_E12 hws)
    obtain ⟨l', -, hl'σ'⟩ := (S.frame.image_L σ').2 hσ'
    have hl'w : (l' : G) * S.v12 * (l' : G)⁻¹ = g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹ := by
      have hc := S.psi_conj l' ⟨S.v12, S.v12_mem_V⟩
      rw [hl'σ', S.psi_v12, hσ'w] at hc
      exact congrArg Subtype.val (S.frame.ψ.injective hc)

    have hk : (l' : G)⁻¹ * g * l ∈ Subgroup.centralizer ({S.v12} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : (l' : G)⁻¹ * g * l * S.v12 =
          (l' : G)⁻¹ * (g * ((l : G) * S.v12 * (l : G)⁻¹) * g⁻¹) * (g * l) := by group
      rw [e1, ← hl'w]
      group
    have hkN := h hk

    obtain ⟨b, hb, hab⟩ := W5_eq_mul_pb (S.frame.ψ ⟨x, hx⟩)
    set a : W5 := S.frame.ψ ⟨x, hx⟩ * (pact pb b)⁻¹ with ha
    have ha₀ : ((S.frame.ψ.symm a : ↥V) : G) ∈ S.Vv :=
      S.mem_Vv.2 ⟨(S.frame.ψ.symm a).2, by simpa using hab⟩
    have hb₀ : ((S.frame.ψ.symm b : ↥V) : G) ∈ S.Vv :=
      S.mem_Vv.2 ⟨(S.frame.ψ.symm b).2, by simpa using hb⟩
    have hlb : (l : G) * (S.frame.ψ.symm b : ↥V) * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp l.2 _).mp (S.frame.ψ.symm b).2
    have hx_eq : x = ((S.frame.ψ.symm a : ↥V) : G) *
        ((l : G) * (S.frame.ψ.symm b : ↥V) * (l : G)⁻¹) := by
      have e : (⟨x, hx⟩ : ↥V) = S.frame.ψ.symm a * ⟨_, hlb⟩ := by
        apply S.frame.ψ.injective
        rw [map_mul, S.psi_conj l (S.frame.ψ.symm b), hlσ, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply, ha, inv_mul_cancel_right]
      exact congrArg Subtype.val e
    rw [hx_eq]
    have e2 : g * (((S.frame.ψ.symm a : ↥V) : G) *
        ((l : G) * (S.frame.ψ.symm b : ↥V) * (l : G)⁻¹)) * g⁻¹ =
        (g * (S.frame.ψ.symm a : ↥V) * g⁻¹) * ((l' : G) * (((l' : G)⁻¹ * g * l) *
          (S.frame.ψ.symm b : ↥V) * ((l' : G)⁻¹ * g * l)⁻¹) * (l' : G)⁻¹) := by group
    rw [e2]
    refine V.mul_mem (S.Vv_le_V ((Subgroup.mem_normalizer_iff.mp hgN _).mp ha₀)) ?_
    have h5 : ((l' : G)⁻¹ * g * l) * (S.frame.ψ.symm b : ↥V) * ((l' : G)⁻¹ * g * l)⁻¹ ∈ V :=
      S.Vv_le_V ((Subgroup.mem_normalizer_iff.mp hkN _).mp hb₀)
    exact (Subgroup.mem_normalizer_iff.mp l'.2 _).mp h5
  intro g hg
  refine B6.mem_normalizer_of_forall_mem (key g hg) fun x hx => ?_
  simpa using key g⁻¹ (Subgroup.inv_mem _ hg) x hx

theorem le_normalizer_Vv_of_thompsonJ_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hJ : thompsonJ (T ⊓ Subgroup.centralizer ({S.v12} : Set G)) ≤
      Subgroup.centralizer (S.Uv : Set G)) :
    Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G) := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hsyl : IsSylowTwoOf (T ⊓ Gv) Gv :=
    S.isSylowTwoOf_centralizer_F4 h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1

  have hzGv : S.z ∈ Gv := by
    rw [hGv, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (S.elemAbelian_V.1.is_comm.comm ⟨S.z, S.z_mem_V⟩ ⟨S.v12, S.v12_mem_V⟩)
  have hzC : S.z ∈ Subgroup.centralizer ((T ⊓ Gv : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht).1
    calc t * S.z = t * S.z * t⁻¹ * t := by group
      _ = S.z * t := by rw [this]
  have hZ : S.V1 ≤ quasithinOmegaOneCenter (T ⊓ Gv) := by
    rw [V1, Subgroup.zpowers_le]
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨S.V_le_T S.z_mem_V, hzGv⟩, hzC⟩, S.z_sq⟩

  obtain ⟨hUc, hUe⟩ :=
    conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF hZ
  replace hUc : S.Uv ≤ centerOf (pCoreOf 2 Gv) := hUc
  replace hUe : IsElemAbelian 2 S.Uv := hUe
  have hUN : Gv ≤ Subgroup.normalizer (S.Uv : Set G) := le_normalizer_conjClosure S.V1 Gv
  have hUT : S.Uv ≤ T ⊓ Gv :=
    hUc.trans (inf_le_left.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl))

  have hb : baum T = baum ((T ⊓ Gv) ⊓ Subgroup.centralizer (S.Uv : Set G)) := by
    rw [← baum_eq_baum_centralizer hUe hUT (le_inf (B6.thompsonJ_le _) hJ)]
    exact S.lemma_13_6_4.1.symm

  have hNG : Gv ⊓ Subgroup.centralizer (S.Uv : Set G) ≤ Gv := inf_le_left
  have hcent : ∀ g ∈ Gv, ∀ x ∈ Subgroup.centralizer (S.Uv : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer (S.Uv : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro u hu
    have hu' : g⁻¹ * u * g ∈ S.Uv := by
      have := (Subgroup.mem_normalizer_iff.mp (hUN (Gv.inv_mem hg)) u).mp hu
      simpa using this
    have h1 := hx _ hu'
    calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * u := by group
  have hGN : Gv ≤ Subgroup.normalizer
      ((Gv ⊓ Subgroup.centralizer (S.Uv : Set G) : Subgroup G) : Set G) := by
    intro g hg
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · exact ⟨Gv.mul_mem (Gv.mul_mem hg hx.1) (Gv.inv_mem hg), hcent g hg x hx.2⟩
    · have h1 := hcent g⁻¹ (Gv.inv_mem hg) x hx.2
      rw [inv_inv] at h1
      exact ⟨Gv.mul_mem (Gv.mul_mem (Gv.inv_mem hg) hx.1) hg, h1⟩
  have hsylN := A4.isSylowTwoOf_inf_normal hsyl hNG hGN
  have hTN : (T ⊓ Gv) ⊓ (Gv ⊓ Subgroup.centralizer (S.Uv : Set G)) =
      (T ⊓ Gv) ⊓ Subgroup.centralizer (S.Uv : Set G) := by
    rw [← inf_assoc, inf_assoc T Gv Gv, inf_idem]
  refine (B6.frattini_two hNG hGN hsylN).trans (sup_le ?_ ?_)
  ·
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (S.Vv : Set G) :=
      Subgroup.centralizer_le S.Vv_le_Uv (Subgroup.mem_inf.mp hx).2
    exact Subgroup.centralizer_le_normalizer _ hxc
  ·
    intro x hx
    obtain ⟨hxG, hxN⟩ := Subgroup.mem_inf.mp hx
    rw [hTN] at hxN
    have hxb : x ∈ Subgroup.normalizer (baum T : Set G) := by
      rw [hb]
      exact normalizer_le_normalizer_baum _ hxN
    exact S.normalizer_inf_le_normalizer_Vv (S.lemma_13_6_5_F4 h1222 h517 ⟨hxG, hxb⟩)

end Setting

@[expose] def Lemma1366_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) → CharTwo (Subgroup.centralizer ({S.v12} : Set G))

@[expose] def Main1367_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    CharTwo (Subgroup.centralizer ({S.v12} : Set G)) →
    ¬ Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G) →
    ¬ thompsonJ (T ⊓ Subgroup.centralizer ({S.v12} : Set G)) ≤
      Subgroup.centralizer (S.Uv : Set G) →
      False

theorem thm13_6_7_of_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (h1366 : Lemma1366_F4) (hmain : Main1367_F4) : Thm13_6_7_F4 := by
  intro G _ _ T L V S hab
  have hF := h1366 G T L V S hab
  refine S.le_normalizer_V_of_Vv_F4 (input1326Two_of_F4 h1222 h517) ?_
  by_contra hVv
  exact hmain G T L V S hab hF hVv fun hJ =>
    hVv (S.le_normalizer_Vv_of_thompsonJ_F4 h1222 h517 hF hJ)

end CFSG.Quasithin.H13.A5
