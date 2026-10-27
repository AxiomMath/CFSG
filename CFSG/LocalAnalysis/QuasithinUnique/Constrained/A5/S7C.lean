module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7B
public import Certificates.Certificate17027
public import Certificates.Certificate5952

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

theorem g1_four : g1 4 = 0 := by decide +kernel

theorem thRaw_g1 : thRaw (g1, 1) = ![0, 0, 0, 1] := by decide +kernel

theorem inSing_e3 : inSing (![0, 0, 0, 1] : V4) := by decide +kernel

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem u0_mem_P : C.u0 ∈ borelP M L := X.iV_mem_P (e := g1w) g1_four

theorem uvec_eq
    : Multiplicative.toAdd (X.thG ⟨C.u0, X.u0_mem_P⟩) = ![0, 0, 0, 1] := by
  show thRaw (X.rawP ⟨C.u0, X.u0_mem_P⟩) = _
  have : X.rawP ⟨C.u0, X.u0_mem_P⟩ = (g1, 1) := X.raw_iV g1w
  rw [this]
  exact thRaw_g1

@[instance_reducible] noncomputable def actM : MulAction ↥M V4 where
  smul m v := ((X.rho' m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v
  one_smul v := by
    show ((X.rho' 1 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = v
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  mul_smul a b v := by
    show ((X.rho' (a * b) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v =
      ((X.rho' a : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        (((X.rho' b : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem exists_stab {v : V4} (hv : inSing v) :
    ∃ N : Subgroup ↥M, N.index = 9 ∧ ∀ m : ↥M,
      m ∈ N ↔
        ((X.rho' m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = v := by
  let _ := X.actM
  refine ⟨MulAction.stabilizer ↥M v, ?_, fun m => MulAction.mem_stabilizer_iff⟩
  have horb : MulAction.orbit ↥M v = {w | inSing w} := by
    ext w
    constructor
    · rintro ⟨m, rfl⟩
      refine ⟨?_, ?_⟩
      · show quadHyp (((X.rho' m : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = 0
        rw [X.rho'_quad]
        exact hv.1
      · intro h0
        have h1 : ((X.rho' m⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
            (((X.rho' m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) =
            v := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
            Units.val_one, Matrix.one_mulVec]
        have h2 : ((X.rho' m : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = 0 := h0
        rw [h2, Matrix.mulVec_zero] at h1
        exact hv.2 h1.symm
    · intro hw
      obtain ⟨m, hm⟩ := X.trans_sing v w hv hw
      refine ⟨⟨(m : G), C.M1_le_M m.2⟩, ?_⟩
      show ((X.rho' ⟨(m : G), C.M1_le_M m.2⟩ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = w
      rw [X.rho'_eq_rho m]
      exact hm
  have hncard : (MulAction.orbit ↥M v).ncard = 9 := by
    rw [horb]
    have : ({v | inSing v} : Set V4) = ↑(Finset.univ.filter fun v : V4 => inSing v) := by
      ext v
      simp
    rw [this, Set.ncard_coe_finset, nine_sing]
  rw [MulAction.index_stabilizer, hncard]

theorem Tu_eq
    (hR : C.u0 ∈ centerOf (baum S)) :
    T ⊓ centralizerElem C.u0 = M ⊓ centralizerElem C.u0 := by
  obtain ⟨N, hNi, hNmem⟩ := X.exists_stab (v := ![0, 0, 0, 1]) inSing_e3
  let x : ↥(borelP M L) := ⟨C.u0, X.u0_mem_P⟩
  have hkey : ∀ (m : ↥M) (y : ↥(borelP M L)), (y : G) = m * x * m⁻¹ →
      ((X.rho' m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        ![0, 0, 0, 1] = Multiplicative.toAdd (X.thG y) := by
    intro m y hy
    rw [← X.uvec_eq]
    exact (X.rho'_spec m x y hy).symm
  have hcardN : Nat.card N = 256 := by
    have h1 := N.card_mul_index
    rw [hNi, X.card_M] at h1
    omega
  let Nsub : Subgroup G := N.map M.subtype
  have hNsub : Nat.card Nsub = 256 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hcardN
  have hT : T ≤ Nsub := by
    intro t ht
    have htM : t ∈ M := C.hcs.setting.le ht
    refine ⟨⟨t, htM⟩, (hNmem _).mpr ?_, rfl⟩
    have htN : t * C.u0 * t⁻¹ ∈ borelP M L :=
      (Subgroup.mem_normalizer_iff.mp (X.M_le_normalizer_P htM) C.u0).mp X.u0_mem_P
    let y : ↥(borelP M L) := ⟨t * C.u0 * t⁻¹, htN⟩
    have hy : X.thG y = X.thG x := by
      rcases X.T_conj_u0 hR ht with h | h
      · congr 1
        exact Subtype.ext h
      · have hker : y * x⁻¹ ∈ (X.thG).ker := by
          rw [X.thG_ker, Subgroup.mem_subgroupOf]
          show t * C.u0 * t⁻¹ * C.u0⁻¹ ∈ centerOf (borelP M L)
          rw [h]
          have hc : C.u0 * C.zU = C.zU * C.u0 := C.U_comm C.u0_mem_U C.zU_mem
          have : C.u0 * C.zU * C.u0⁻¹ = C.zU := by
            calc C.u0 * C.zU * C.u0⁻¹ = C.zU * C.u0 * C.u0⁻¹ := by rw [hc]
              _ = C.zU := by group
          rw [this]
          exact (X.centerOf_P_iff _).mpr (Or.inr rfl)
        have h0 : X.thG (y * x⁻¹) = 1 := hker
        rw [map_mul, map_inv] at h0
        calc X.thG y = (X.thG y * (X.thG x)⁻¹) * X.thG x := (inv_mul_cancel_right _ _).symm
          _ = X.thG x := by rw [h0, one_mul]
    have h1 := hkey ⟨t, htM⟩ y rfl
    rw [hy, X.uvec_eq] at h1
    exact h1
  have hTN : T = Nsub := Subgroup.eq_of_le_of_card_ge hT (by rw [hNsub, X.card_T])
  apply le_antisymm
  · exact inf_le_inf_right _ C.hcs.setting.le
  · rintro m ⟨hmM, hmC⟩
    refine ⟨?_, hmC⟩
    rw [hTN]
    refine ⟨⟨m, hmM⟩, (hNmem _).mpr ?_, rfl⟩
    have hc : m * C.u0 * m⁻¹ = C.u0 := (mem_Cu_iff m).mp hmC
    have h1 := hkey ⟨m, hmM⟩ x (by show C.u0 = m * C.u0 * m⁻¹; rw [hc])
    exact h1.trans X.uvec_eq

end Sec

end CFSG.QuasithinUnique.A5
