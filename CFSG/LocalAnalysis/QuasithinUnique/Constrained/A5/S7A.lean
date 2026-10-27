module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7Rel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage6

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

@[expose] noncomputable def u0 (C : StdCfg T M H S L) : G := ((C.iV g1w : ↥H) : G)

theorem u0_mem_U (C : StdCfg T M H S L) : C.u0 ∈ blockU L := C.iV_mem_U g1w

theorem u0_mem_H (C : StdCfg T M H S L) : C.u0 ∈ H := (C.iV g1w).2

theorem u0_mul_self (C : StdCfg T M H S L) : C.u0 * C.u0 = 1 :=
  congrArg Subtype.val (C.iV_self g1w)

theorem card_U (C : StdCfg T M H S L) : Nat.card (blockU L) = 16 := by
  rw [Nat.card_congr C.D.β.toEquiv]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5)]
  exact AppC.card_evenWeight

theorem imR (C : StdCfg T M H S L) : ((baum S).subgroupOf H).map C.D.π = Estd := by
  ext σ
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact C.hRE y.1 (Subgroup.mem_subgroupOf.mp hy)
  · intro hσ
    obtain ⟨r, hr, hπ⟩ := C.hRE' σ hσ
    exact ⟨⟨r, baum_le_H C.hcs hr⟩, Subgroup.mem_subgroupOf.mpr hr, hπ⟩

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem u0_ne_one : C.u0 ≠ 1 := by
  intro h
  have h1 : C.iV g1w = C.iV 0 := by
    rw [C.iV_zero]
    exact Subtype.ext h
  exact g1_ne_zero (congrArg Subtype.val (C.iV_inj X.hTC h1))

theorem mem_cent_iff (h : ↥H) :
    (h : G) ∈ centralizerElem C.u0 ↔ vact (C.D.π h) g1w = g1w := by
  rw [centralizerElem, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc
    have h1 : C.u0 * (h : G) = (h : G) * C.u0 := hc C.u0 rfl
    have h2 : h * C.iV g1w = C.iV g1w * h := Subtype.ext h1.symm
    exact X.vact_fixed_of_comm h g1w h2
  · intro hv g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have h1 := C.conj_iV X.hTC h g1w
    rw [hv] at h1
    have h2 : h * C.iV g1w = C.iV g1w * h := by
      calc h * C.iV g1w = h * C.iV g1w * h⁻¹ * h := by group
        _ = C.iV g1w * h := by rw [h1]
    exact (congrArg Subtype.val h2).symm

theorem card_eq_of_pi {Y : Subgroup G} (hYH : Y ≤ H) (hUY : blockU L ≤ Y) :
    Nat.card Y = 16 * Nat.card ((Y.subgroupOf H).map C.D.π) := by
  have h1 := Subgroup.card_ker_mul_card_range (C.D.π.domRestrict (Y.subgroupOf H))
  rw [MonoidHom.domRestrict_range] at h1
  have h2 : Nat.card (Y.subgroupOf H) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv
  have h3 : Nat.card (C.D.π.domRestrict (Y.subgroupOf H)).ker = 16 := by
    rw [← C.card_U]
    refine Nat.card_congr
      { toFun := fun y => ⟨((y.1.1 : ↥H) : G), by
          have hy : C.D.π (y.1.1 : ↥H) = 1 := y.2
          rw [← C.Q_eq_U X.hTC]
          exact (C.hker _).mp hy⟩
        invFun := fun u => ⟨⟨⟨u, C.blockU_le_H u.2⟩, Subgroup.mem_subgroupOf.mpr (hUY u.2)⟩, by
          show C.D.π ⟨u, C.blockU_le_H u.2⟩ = 1
          rw [C.hker, C.Q_eq_U X.hTC]
          exact u.2⟩
        left_inv := fun y => rfl
        right_inv := fun u => rfl }
  calc Nat.card Y = Nat.card (Y.subgroupOf H) := h2.symm
    _ = Nat.card (C.D.π.domRestrict (Y.subgroupOf H)).ker *
        Nat.card ((Y.subgroupOf H).map C.D.π) := h1.symm
    _ = 16 * Nat.card ((Y.subgroupOf H).map C.D.π) := by rw [h3]

theorem card_R : Nat.card (baum S) = 64 := by
  rw [X.card_eq_of_pi (baum_le_H C.hcs) C.U_le_R, C.imR, Estd_card]

theorem card_S : Nat.card S = 128 := by
  rw [X.card_eq_of_pi C.hcs.sylow.le (blockU_le_S C.hcs C.hj), C.piS_eq, Dstd_card]

theorem card_H : Nat.card H = 1920 := by
  rw [X.card_eq_of_pi le_rfl C.blockU_le_H, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr C.hsurj, Subgroup.card_top, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  rfl

theorem R_index : (baum S).relIndex S = 2 := by
  have h1 := Subgroup.relIndex_mul_card (baum S) S
  rw [inf_eq_left.mpr baum_le_S, X.card_R, X.card_S] at h1
  omega

theorem card_M :
    Nat.card M = 2 ^ 8 * 3 ^ 2 := X.M_card'

theorem card_T :
    Nat.card T = 256 := by
  have hT : IsSylowTwoOf T M := C.sylow_T_of_le C.hcs.setting.le
  rw [hT.card_eq]
  unfold twoPart
  rw [X.card_M, Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow,
    Nat.factorization_pow]
  simp [Nat.Prime.factorization Nat.prime_two, Nat.Prime.factorization Nat.prime_three]

theorem Su {u : G} (hu : u = C.u0) (huR : u ∈ centerOf (baum S)) :
    S ⊓ centralizerElem u = baum S := by
  subst hu
  apply le_antisymm
  · rintro s ⟨hsS, hsC⟩
    have hsH : s ∈ H := C.hcs.sylow.le hsS
    have hπ := (X.mem_cent_iff ⟨s, hsH⟩).mp hsC
    have hD : C.D.π ⟨s, hsH⟩ ∈ Dset := (mem_Dstd _).mp (C.pi_mem_Dstd hsS)
    have hE : C.D.π ⟨s, hsH⟩ ∈ Eset :=
      fixD_g1 _ hD (congrArg Subtype.val hπ)
    exact (X.mem_R_iff ⟨s, hsH⟩).mpr hE
  · intro r hr
    refine ⟨baum_le_S hr, ?_⟩
    show r ∈ Subgroup.centralizer ({C.u0} : Set G)
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp huR).2 r hr).symm

end Sec

end CFSG.QuasithinUnique.A5
