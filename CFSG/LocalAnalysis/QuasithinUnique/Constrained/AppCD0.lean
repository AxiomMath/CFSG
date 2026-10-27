module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCMate

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {T M H S L : Subgroup G} (C : Cfg T M H S L)
include C

theorem conj_mem_blockD {s d : G} (hs : s ∈ S) (hd : d ∈ blockD S L) :
    s * d * s⁻¹ ∈ blockD S L := by
  have hsd : s * d * s⁻¹ ∈ S := mul_mem (mul_mem hs hd.1) (inv_mem hs)
  refine ⟨hsd, ?_⟩
  rw [C.hj]
  refine Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => ?_
  have hℓ' : s⁻¹ * ℓ * s ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (C.hSN (inv_mem hs)) ℓ).1 hℓ
    simpa using this
  have h := blockD_comm C.hj hd hℓ'
  calc ℓ * (s * d * s⁻¹) = s * ((s⁻¹ * ℓ * s) * d) * s⁻¹ := by group
    _ = s * (d * (s⁻¹ * ℓ * s)) * s⁻¹ := by rw [h]
    _ = (s * d * s⁻¹) * ℓ := by group

theorem S_le_N_D : S ≤ Subgroup.normalizer (blockD S L : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · exact fun hd => C.conj_mem_blockD hs hd
  · intro h
    have := C.conj_mem_blockD (inv_mem hs) h
    simpa [mul_assoc] using this

theorem D_le_Q : blockD S L ≤ pCoreOf 2 H := blockD_le_pCoreOf C.hcs C.hj

theorem Q_eq : pCoreOf 2 H = blockU L ⊔ blockD S L :=
  pCoreOf_eq_blockU_sup_blockD C.hcs C.hj C.h5

theorem exists_UD {q : G} (hq : q ∈ pCoreOf 2 H) : ∃ u ∈ blockU L, ∃ d ∈ blockD S L, q = u * d :=
  exists_split' C.hcs C.hj C.h5 hq

theorem U_comm_D {u d : G} (hu : u ∈ blockU L) (hd : d ∈ blockD S L) : u * d = d * u := by
  have := blockD_comm C.hj hd (C1.blockQ_le L (C1.blockU_le_blockQ C.hL hu))
  exact this.symm

theorem U_inf_D : blockU L ⊓ blockD S L = ⊥ := blockU_inf_blockD C.hcs C.hj C.h5

end Cfg

namespace Mate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : Cfg T M H S L) (m : Mate S T M₀ x)
include C m

omit [Finite G] C in
theorem S_le_N_conj {D : Subgroup G} (hD : S ≤ Subgroup.normalizer (D : Set G)) :
    S ≤ Subgroup.normalizer (conjSubgroup D x : Set G) := by
  intro s hs
  rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_conjSubgroup]
  have e : x * s = (x * s * x⁻¹) * x := by group
  rw [e, ← conjSubgroup_conjSubgroup, C5.conjSubgroup_eq_self (hD (m.conj_mem_S hs))]

omit [Finite G] C in
theorem conj_conj_eq {D : Subgroup G} (hD : S ≤ Subgroup.normalizer (D : Set G)) :
    conjSubgroup (conjSubgroup D x) x = D := by
  rw [conjSubgroup_conjSubgroup]
  exact C5.conjSubgroup_eq_self (hD m.xx)

theorem D_comm_V {d v : G} (hd : d ∈ blockD S L) (hv : v ∈ conjR (blockU L) x) :
    d * v = v * d := by
  have h1 : d * v * d⁻¹ * v⁻¹ ∈ blockD S L := by
    have := mul_mem hd (C.conj_mem_blockD (m.V_le_S C hv) (inv_mem hd))
    simpa [mul_assoc] using this
  have h2 : d * v * d⁻¹ * v⁻¹ ∈ conjR (blockU L) x := by
    have h3 := (Subgroup.mem_normalizer_iff.1 (m.S_le_N_V C hd.1) v).1 hv
    exact mul_mem h3 (inv_mem hv)
  have h4 : d * v * d⁻¹ * v⁻¹ ∈ pCoreOf 2 H := C.D_le_Q h1
  have h5 := m.V_inf_Q_le_U C h2 h4
  have h6 : d * v * d⁻¹ * v⁻¹ ∈ blockU L ⊓ blockD S L := ⟨h5, h1⟩
  rw [C.U_inf_D, Subgroup.mem_bot] at h6
  calc d * v = (d * v * d⁻¹ * v⁻¹) * (v * d) := by group
    _ = v * d := by rw [h6, one_mul]

@[expose] def K (S L : Subgroup G) (x : G) : Subgroup G :=
  S ⊓ Subgroup.centralizer ((blockU L ⊔ conjR (blockU L) x : Subgroup G) : Set G)

theorem conj_K : conjSubgroup (K S L x) x = K S L x := by
  unfold K
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, C5.conjSubgroup_sup,
    C5.conjSubgroup_eq_self m.xN]
  have h1 : conjSubgroup (conjR (blockU L) x) x = blockU L := m.V_conj C
  rw [h1, sup_comm]
  rfl

theorem D_le_K : blockD S L ≤ K S L x := by
  intro d hd
  refine ⟨hd.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have hU : blockU L ≤ Subgroup.centralizer ({d} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (C.U_comm_D hu hd).symm
  have hV : conjR (blockU L) x ≤ Subgroup.centralizer ({d} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact m.D_comm_V C hd hv
  have := Subgroup.mem_centralizer_iff.1 ((sup_le hU hV) hy) d (Set.mem_singleton d)
  exact this.symm

theorem sqSub_K : C5.sqSub (K S L x) = C5.sqSub (blockD S L) := by
  apply le_antisymm
  · refine C5.sqSub_le_of_forall fun k hk => ?_
    have hkS : k ∈ S := hk.1
    have hkU : k ∈ Subgroup.centralizer (blockU L : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hk.2
    have hkQ : k ∈ pCoreOf 2 H := by rw [← C.hQ]; exact ⟨C.hSH hkS, hkU⟩
    obtain ⟨u, hu, d, hd, rfl⟩ := C.exists_UD hkQ
    have hc : Commute u d := C.U_comm_D hu hd
    have hu2 : u ^ 2 = 1 := C.hU.2 u hu
    rw [hc.mul_pow, hu2, one_mul]
    exact C5.sq_mem_sqSub hd
  · exact C5.sqSub_mono (m.D_le_K C)

theorem sqSub_D : C5.sqSub (blockD S L) = ⊥ := by
  have hne : S ≠ M₀ := fun h => m.hxS (h ▸ m.hx)
  refine C5.eq_bot_of_noCommonNormal (K := L) (x := x) (M₀ := M₀) (H := H) (R := S)
    (C56.noCommonNormal C.hcs m.hSM m.hMT hne) ?_ ?_ ?_ ?_ (C56.H_eq C.hcs C.hj).le
    (le_sup_zpowers_of_relIndex_two m.h2 m.hx m.hxS)
  · exact C5.sqSub_le_self.trans inf_le_left
  · refine C5.sqSub_le_self.trans ?_
    intro d hd
    have := hd.2
    rwa [C.hj] at this
  · intro s hs
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    exact C5.conjSubgroup_sqSub_of_mem_normalizer (C.S_le_N_D hs)
  · rw [← conjSubgroup_eq_iff_mem_normalizer, ← m.sqSub_K C]
    exact C5.conjSubgroup_sqSub_of_mem_normalizer
      (conjSubgroup_eq_iff_mem_normalizer.1 (m.conj_K C))

theorem D_elem : IsElemAbelian 2 (blockD S L) := by
  have h := C5.sqSub_eq_bot_iff.1 (m.sqSub_D C)
  exact C5.isElemAbelian_two_iff.mpr ⟨C5.comm_of_sq_eq_one h, h⟩

theorem Q_elem : IsElemAbelian 2 (pCoreOf 2 H) := by
  rw [C.Q_eq]
  exact B2F.isElemAbelian_sup_of_commute C.hU (m.D_elem C) fun u hu d hd => C.U_comm_D hu hd

theorem D_le_B : blockD S L ≤ baum S := by
  intro d hd
  refine ⟨hd.1, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
  exact B2F.isElemAbelian_comm (m.Q_elem C) (C.omegaOneCenter_le_pCoreOf hz) (C.D_le_Q hd)

theorem Q_le_B : pCoreOf 2 H ≤ baum S := by
  rw [C.Q_eq]
  exact sup_le C.blockU_le_baum (m.D_le_B C)

theorem baumD_eq : baumD S L = blockD S L := by
  apply le_antisymm
  · exact inf_le_inf_right _ inf_le_left
  · exact le_inf (m.D_le_B C) fun d hd => hd.2

theorem D_inf_conj : blockD S L ⊓ conjR (blockD S L) x = ⊥ := by
  have hne : S ≠ M₀ := fun h => m.hxS (h ▸ m.hx)
  have hN := C.S_le_N_D (L := L)
  refine C5.eq_bot_of_noCommonNormal (K := L) (x := x) (M₀ := M₀) (H := H) (R := S)
    (C56.noCommonNormal C.hcs m.hSM m.hMT hne) ?_ ?_ ?_ ?_ (C56.H_eq C.hcs C.hj).le
    (le_sup_zpowers_of_relIndex_two m.h2 m.hx m.hxS)
  · exact inf_le_left.trans inf_le_left
  · refine inf_le_left.trans ?_
    intro d hd
    have := hd.2
    rwa [C.hj] at this
  · intro s hs
    rw [← conjSubgroup_eq_iff_mem_normalizer, C5.conjSubgroup_inf,
      C5.conjSubgroup_eq_self (hN hs)]
    have := m.S_le_N_conj hN hs
    rw [← conjSubgroup_eq_iff_mem_normalizer] at this
    rw [C56.conjR_eq, this]
  · rw [← conjSubgroup_eq_iff_mem_normalizer, C56.conjR_eq, C5.conjSubgroup_inf,
      m.conj_conj_eq hN, inf_comm]

theorem B_le_sup {b : G} (hb : b ∈ baum S) :
    ∃ v ∈ conjR (blockU L) x, v⁻¹ * b ∈ pCoreOf 2 H := by
  have hbS : b ∈ S := hb.1
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := C.hSN hbS
  have hπb : C.P.π ⟨b, hbN⟩ ∈ C.P.im (conjR (blockU L) x) := by
    rw [m.im_V C, ← C.hB]
    exact C.P.pi_mem_im hb
  obtain ⟨v, hvV, hvπ⟩ := (C.P.mem_im).1 hπb
  have h1 : C.P.π (v⁻¹ * ⟨b, hbN⟩) = 1 := by
    rw [map_mul, map_inv, hvπ, inv_mul_cancel]
  have h2 := (C.P.hker (v⁻¹ * ⟨b, hbN⟩)).1 h1
  refine ⟨(v : G), hvV, ?_⟩
  rw [← C.hQ]
  have hvbH : (v : G)⁻¹ * b ∈ H := mul_mem (inv_mem (C.hSH (m.V_le_S C hvV))) (C.hSH hbS)
  refine ⟨hvbH, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
  have := h2 u hu
  have e : ((v⁻¹ * ⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) : G) = (v : G)⁻¹ * b := rfl
  rw [e] at this
  calc u * ((v : G)⁻¹ * b) = (((v : G)⁻¹ * b) * u * ((v : G)⁻¹ * b)⁻¹) * ((v : G)⁻¹ * b) := by
        rw [this]
    _ = ((v : G)⁻¹ * b) * u := by group

theorem B_eq_sup : baum S = conjR (blockU L) x ⊔ pCoreOf 2 H := by
  apply le_antisymm
  · intro b hb
    obtain ⟨v, hv, hq⟩ := m.B_le_sup C hb
    have : b = v * (v⁻¹ * b) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hq)
  · exact sup_le (m.V_le_B C) (m.Q_le_B C)

theorem B_eq : baum S = blockD S L ⊔ blockU L ⊔ conjR (blockU L) x := by
  rw [m.B_eq_sup C, C.Q_eq, sup_comm (blockU L), sup_comm]

end Mate

end CFSG.QuasithinUnique.AppC
