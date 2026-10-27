module

public import CFSG.GH74.Generic.BProg.B3.LocBalSL4Model
public import CFSG.GH74.Generic.BProg.B1.PilotS1Models
public import CFSG.GH74.Generic.BProg.B3.LocBalSL4Basic

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.Assembly.LowTwoRank CFSG.GH74.Generic.BProg.B1.PilotS1
  CFSG.GH74.Generic.BProg.B3.LocBalSL4Model Subgroup

namespace LocBalSL4Inst

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem center_eq_Zs {M : ModelData F}
    (hc : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔ g = 1 ∨ g = M.xK) :
    Subgroup.center ↥M.K4 = Zs M := by
  ext g
  constructor
  · intro hg
    rcases (hc g).1 hg with rfl | rfl
    · exact Subgroup.one_mem _
    · exact xK_mem_Zs M
  · intro hg
    exact Zs_le_center M hg

omit [Finite F] in
theorem centerless_PG {M : ModelData F} (hq : CFSG.IsQuasisimple ↥M.K4)
    (hZ : Subgroup.center ↥M.K4 = Zs M) :
    ∀ k : PG M, (∀ g : PG M, g * k = k * g) → k = 1 := by
  intro k hk
  let ψ : ↥M.K4 ⧸ Subgroup.center ↥M.K4 ≃* PG M := QuotientGroup.quotientMulEquivOfEq hZ
  have h := LocBalSL4Abs.centerless_quotient_of_quasisimple hq (ψ.symm k) (fun g =>
    ψ.injective (by rw [map_mul, map_mul, ψ.apply_symm_apply]; exact hk (ψ g)))
  have : k = ψ (ψ.symm k) := (ψ.apply_symm_apply k).symm
  rw [this, h, map_one]

theorem bigModel_lin (hF : Nat.card F % 4 = 3) (h7 : 4 ≤ Nat.card F) :
    BigModel (ModelData.lin F) (Nat.card F) 1 := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  have h5 : 5 ≤ Nat.card F := by omega
  have hc0 := mem_center_lin_iff hF
  have hc : ∀ g : ↥(ModelData.lin F).K4, g ∈ Subgroup.center ↥(ModelData.lin F).K4 ↔
      g = 1 ∨ g = (ModelData.lin F).xK := by
    intro g
    rw [hc0]
    constructor
    · rintro (h | h)
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext h
    · rintro (rfl | rfl)
      · left
        rfl
      · right
        rfl
  have hone := hone_of_model (ModelData.lin F) hc0 (fun t hT h1 hm1 => hmat_lin h2 t hT h1 hm1)
  have hq : CFSG.IsQuasisimple ↥(StatedSL 4 F) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (specialLinearGroupEquivStatedSL (3 + 1) F)
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 3 F (by norm_num))
  refine ⟨goodModel_lin h2 h5, hone, hc, centerless_PG hq (center_eq_Zs hc), ?_, hodd, by omega,
    Or.inl rfl, ?_, Or.inl ⟨F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩, ?_⟩
  · exact Or.inl ⟨rfl, F, inferInstance, inferInstance, rfl, ⟨MulEquiv.refl _⟩⟩
  · intro h
    unfold Int.ModEq at h
    omega
  · intro E hE hcard
    exact e8_mem_xK (ModelData.lin F) h2 hc0 hone E hE hcard

theorem bigModel_uni {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) (h5 : 5 ≤ p ^ f) :
    BigModel (ModelData.uni hF) (p ^ f) (-1) := by
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card hodd
  have hc0 := mem_center_uni_iff hF hq
  have hc : ∀ g : ↥(ModelData.uni hF).K4, g ∈ Subgroup.center ↥(ModelData.uni hF).K4 ↔
      g = 1 ∨ g = (ModelData.uni hF).xK := by
    intro g
    rw [hc0]
    constructor
    · rintro (h | h)
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext h
    · rintro (rfl | rfl)
      · left
        rfl
      · right
        rfl
  have hone := hone_of_model (ModelData.uni hF) hc0 (fun t hT h1 hm1 => hmat_uni hF h2 t hT h1 hm1)
  have hq4 := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF (n := 4)
    (by norm_num) (fun h => by simp at h)
  refine ⟨goodModel_uni hF hp2 h5, hone, hc, centerless_PG hq4.1 hq4.2, ?_, ?_, by omega,
    Or.inr rfl, ?_, Or.inr ⟨p ^ f, F, inferInstance, inferInstance, hF, hq, ⟨MulEquiv.refl _⟩⟩, ?_⟩
  · exact Or.inr ⟨rfl, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  · exact Nat.odd_iff.2 (by omega)
  · intro h
    unfold Int.ModEq at h
    omega
  · intro E hE hcard
    exact e8_mem_xK (ModelData.uni hF) h2 hc0 hone E hE hcard

section Transport0

variable {Kt : Type} [Group Kt]

omit [Finite F] in
@[expose] noncomputable def quotEquivPG {M : ModelData F}
    (hZ : Subgroup.center ↥M.K4 = Zs M) (e : Kt ≃* ↥M.K4) : Kt ⧸ Subgroup.center Kt ≃* PG M :=
  QuotientGroup.congr (Subgroup.center Kt) (Zs M) e
    (by rw [← hZ]; exact CFSG.LieType.Universal.Unitary.map_center_mulEquiv e)

end Transport0

section Transport

variable {Kt : Type} [Group Kt]

theorem locBal32_of_bigModel {M : ModelData F} {q : ℕ} {ε : ℤ} (hM : BigModel M q ε)
    (e : Kt ≃* ↥M.K4) {Ab : Subgroup Kt} (hAe : CFSG.IsElementaryAbelian 2 ↥Ab)
    (hA8 : Nat.card ↥Ab = 8) (B : Subgroup (MulAut (Kt ⧸ Subgroup.center Kt)))
    (hB : B ≤ (Ab.map (QuotientGroup.mk' (Subgroup.center Kt))).map
      (MulAut.conj : (Kt ⧸ Subgroup.center Kt) →* MulAut (Kt ⧸ Subgroup.center Kt))) :
    IsLocBal32 (Kt ⧸ Subgroup.center Kt) B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := center_eq_Zs hM.center
  let φ : Kt ⧸ Subgroup.center Kt ≃* PG M := quotEquivPG hZ e
  let Ab' : Subgroup ↥M.K4 := Ab.map e.toMonoidHom
  have hAe' : CFSG.IsElementaryAbelian 2 ↥Ab' := IsElementaryAbelian.map e.toMonoidHom
  have hA8' : Nat.card ↥Ab' = 8 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hA8
  let B' : Subgroup (MulAut (PG M)) := B.map (MulAut.congr φ).toMonoidHom
  have hB' : B' ≤ (Ab'.map (mkP M)).map (MulAut.conj : PG M →* MulAut (PG M)) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨y, ⟨a, haA, rfl⟩, hya⟩ := Subgroup.mem_map.mp (hB hb)
    refine ⟨mkP M (e a), ⟨e a, ⟨a, haA, rfl⟩, rfl⟩, ?_⟩
    rw [← hya]
    show MulAut.conj (mkP M (e a)) = MulAut.congr φ (MulAut.conj (QuotientGroup.mk' _ a))
    rw [LocBalSL4Basic.congr_conj]
    rfl
  have h := locBal32_model_big hM hAe' hA8' B' hB'
  have h2 := isLocBal32_of_mulEquiv φ.symm h
  have hBB : B'.map (MulAut.congr φ.symm).toMonoidHom = B := by
    rw [Subgroup.map_map]
    have : (MulAut.congr φ.symm).toMonoidHom.comp (MulAut.congr φ).toMonoidHom =
        MonoidHom.id _ := by
      ext x y
      simp [MulAut.congr_apply]
    rw [this, Subgroup.map_id]
  rwa [hBB] at h2

theorem locBal32_SL4_big (hK : QShape1Big Kt) {Ab : Subgroup Kt}
    (hAe : CFSG.IsElementaryAbelian 2 ↥Ab) (hA8 : Nat.card ↥Ab = 8)
    (B : Subgroup (MulAut (Kt ⧸ Subgroup.center Kt)))
    (hB : B ≤ (Ab.map (QuotientGroup.mk' (Subgroup.center Kt))).map
      (MulAut.conj : (Kt ⧸ Subgroup.center Kt) →* MulAut (Kt ⧸ Subgroup.center Kt))) :
    IsLocBal32 (Kt ⧸ Subgroup.center Kt) B := by
  rcases hK with ⟨F', _, _, hF, h7, ⟨e⟩⟩ | ⟨q, F', _, _, hF, hq, ⟨e⟩⟩
  · exact locBal32_of_bigModel (bigModel_lin hF h7) e hAe hA8 B hB
  · obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
    have h1 : 1 < Nat.card F' := Finite.one_lt_card
    have h5 : 5 ≤ p ^ f := by
      by_contra hlt
      have hb : p ^ f = 1 := by omega
      rw [hb] at hF
      simp only [one_pow] at hF
      omega
    exact locBal32_of_bigModel (bigModel_uni hF hq h5) e hAe hA8 B hB

end Transport

end LocBalSL4Inst

end CFSG.GH74.Generic.BProg.B3
