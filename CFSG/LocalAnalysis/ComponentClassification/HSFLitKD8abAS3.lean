module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAS2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Elem
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7E
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MBFacts
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAD
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abT2b
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Walter.Defs
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open Sec8

macro "elem_ne " φ:term:max e0:term:max e1:term:max e2:term:max hinj:term:max : tactic =>
  `(tactic| (
    try rw [← $e0:term]
    try rw [← $e1:term]
    try rw [← $e2:term]
    try rw [← map_one $φ:term]
    try simp only [← map_mul]
    exact ($hinj).ne (by decide)))

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}

namespace SPkg

variable (P : SPkg A)

omit [Finite X] in
theorem exists_φ : ∃ φ : (Fin 3 → Multiplicative (ZMod 2)) →* X,
    φ (e3 0) = P.z ∧ φ (e3 1) = P.k ∧ φ (e3 2) = P.w :=
  exists_evHom3 P.zk_comm P.zw_comm P.kw P.zz P.kk P.ww

theorem vec_cases : ∀ v : Fin 3 → Multiplicative (ZMod 2), v = 1 ∨ v = e3 0 ∨ v = e3 1 ∨
    v = e3 2 ∨ v = e3 0 * e3 1 ∨ v = e3 0 * e3 2 ∨ v = e3 1 * e3 2 ∨ v = e3 0 * e3 1 * e3 2 := by
  decide

omit [Finite X] in
theorem φ_injective {φ : (Fin 3 → Multiplicative (ZMod 2)) →* X} (e0 : φ (e3 0) = P.z)
    (e1 : φ (e3 1) = P.k) (e2 : φ (e3 2) = P.w) : Function.Injective φ := by
  have hk1 : P.z * P.k ≠ 1 := fun h => P.k_ne_z
    ((inv_eq_of_mul_eq_one_right h).symm.trans P.z_inv)
  have hw1 : P.z * P.w ≠ 1 := fun h => P.w_ne_z
    ((inv_eq_of_mul_eq_one_right h).symm.trans P.z_inv)
  have hkw1 : P.k * P.w ≠ 1 := fun h => P.w_ne_k
    ((inv_eq_of_mul_eq_one_right h).symm.trans (inv_eq_of_mul_eq_one_right P.kk))
  have hzk2 : P.z * P.k * (P.z * P.k) = 1 := by
    rw [show P.z * P.k * (P.z * P.k) = P.z * P.z * (P.k * P.k) by
      rw [mul_assoc, ← mul_assoc P.k, ← P.zk_comm]; group, P.zz, P.kk, one_mul]
  have hzkw1 : P.z * P.k * P.w ≠ 1 := fun h => P.w_ne_zk
    ((inv_eq_of_mul_eq_one_right h).symm.trans (inv_eq_of_mul_eq_one_right hzk2))
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro v hv
  rw [MonoidHom.mem_ker] at hv
  rw [mem_bot]
  rcases vec_cases v with h | h | h | h | h | h | h | h <;> rw [h] at hv ⊢ <;>
    simp only [map_mul, e0, e1, e2] at hv <;>
    first | rfl | exact absurd hv P.z_ne | exact absurd hv P.k_ne₁ | exact absurd hv P.w_ne₁ |
      exact absurd hv hk1 | exact absurd hv hw1 | exact absurd hv hkw1 | exact absurd hv hzkw1

omit [Finite X] in
theorem cz {g : X} (hg : g ∈ P.T₂) : MulAut.conj g P.z = P.z := by
  rw [MulAut.conj_apply]; exact P.conj_z hg

omit [Finite X] in
theorem ck {g : X} (hg : g ∈ P.T₂) :
    MulAut.conj g P.k = P.k ∨ MulAut.conj g P.k = P.z * P.k := by
  simpa only [MulAut.conj_apply] using P.conj_k g hg

theorem exists_SEl_fix (E : P.SEl) : ∃ E' : P.SEl, E'.s * P.w * E'.s⁻¹ = P.w := by
  rcases E.s_w with h | h
  · exact ⟨E, h⟩
  · refine ⟨⟨t * E.s, E.Q, E.hQ, E.hTQ, mul_mem (E.hTQ P.t_mem) E.hsQ,
      mul_mem (le_normalizer P.t_mem) E.hN, fun h' => E.hsT (by
        have := mul_mem (inv_mem P.t_mem) h'
        rwa [inv_mul_cancel_left] at this), ?_⟩, ?_⟩
    · rw [show t * E.s * (t * E.s) = t * (E.s * t * E.s⁻¹) * (E.s * E.s) by group]
      exact mul_mem (mul_mem P.t_mem E.x_mem) E.hs2
    · rw [show t * E.s * P.w * (t * E.s)⁻¹ = t * (E.s * P.w * E.s⁻¹) * t⁻¹ by group, h,
        P.flip_mul_z P.t_flip_w_z P.t_w]

namespace SEl

variable {P} (E : P.SEl)

omit [Finite X] in
theorem csz : MulAut.conj E.s P.z = P.z := by rw [MulAut.conj_apply]; exact E.s_z

theorem csk : MulAut.conj E.s P.k = P.k * P.w ∨ MulAut.conj E.s P.k = P.z * P.k * P.w := by
  simpa only [MulAut.conj_apply] using E.s_k

theorem sq_flip_k (hw : E.s * P.w * E.s⁻¹ = P.w) {a : X} (ha : a ∈ P.T₂)
    (haw : a * P.w * a⁻¹ = P.z * P.w) :
    (a * E.s * (a * E.s)) * P.k * (a * E.s * (a * E.s))⁻¹ = P.z * P.k := by
  rw [← MulAut.conj_apply]
  simp only [map_mul, MulAut.mul_apply]
  have haw' : MulAut.conj a P.w = P.z * P.w := by rw [MulAut.conj_apply]; exact haw
  have hsw : MulAut.conj E.s P.w = P.w := by rw [MulAut.conj_apply]; exact hw
  obtain ⟨φ, e0, e1, e2⟩ := P.exists_φ
  rcases E.csk with h1 | h1 <;> rcases P.ck ha with h2 | h2 <;>
    simp only [h1, h2, haw', P.cz ha, E.csz, hsw, map_mul] <;> elem_eq φ e0 e1 e2 e2

theorem sq_ne_one (hw : E.s * P.w * E.s⁻¹ = P.w) {a : X} (ha : a ∈ P.T₂)
    (haw : a * P.w * a⁻¹ = P.z * P.w) : a * E.s * (a * E.s) ≠ 1 := by
  intro h1
  have h2 := E.sq_flip_k hw ha haw
  rw [h1, one_mul, inv_one, mul_one] at h2
  exact P.k_ne_zk h2

@[expose] noncomputable def T₃ : Subgroup X := P.T₂ ⊔ zpowers E.s

omit [Finite X] in
theorem T₂_le_T₃ : P.T₂ ≤ E.T₃ := le_sup_left

omit [Finite X] in
theorem s_mem_T₃ : E.s ∈ E.T₃ := mem_sup_right (mem_zpowers _)

omit [Finite X] in
theorem T₃_le_Q : E.T₃ ≤ E.Q := sup_le E.hTQ (zpowers_le.mpr E.hsQ)

omit [Finite X] in
theorem isPGroup_T₃ : IsPGroup 2 E.T₃ := E.hQ.to_le E.T₃_le_Q

omit [Finite X] in
theorem mem_T₃ {g : X} (hg : g ∈ E.T₃) : g ∈ P.T₂ ∨ g * E.s⁻¹ ∈ P.T₂ :=
  Sec7.mem_or_of_mem_sup_zpowers E.hN (by rw [pow_two]; exact E.hs2) hg

omit [Finite X] in
theorem card_T₃ : Nat.card E.T₃ = 2 * Nat.card P.T₂ :=
  card_sup_zpowers E.hN E.hs2 E.hsT

omit [Finite X] in
theorem conj_z₃ {g : X} (hg : g ∈ E.T₃) : g * P.z * g⁻¹ = P.z := by
  rcases E.mem_T₃ hg with h | h
  · exact P.conj_z h
  · rw [show g * P.z * g⁻¹ = (g * E.s⁻¹) * (E.s * P.z * E.s⁻¹) * (g * E.s⁻¹)⁻¹ by group, E.s_z,
      P.conj_z h]

omit [Finite X] in
theorem conj_w₃ (hw : E.s * P.w * E.s⁻¹ = P.w) {g : X} (hg : g ∈ E.T₃) :
    g * P.w * g⁻¹ = P.w ∨ g * P.w * g⁻¹ = P.z * P.w := by
  rcases E.mem_T₃ hg with h | h
  · exact P.conj_w g h
  · rw [show g * P.w * g⁻¹ = (g * E.s⁻¹) * (E.s * P.w * E.s⁻¹) * (g * E.s⁻¹)⁻¹ by group, hw]
    exact P.conj_w _ h

theorem conj_x_flip_k {a : X} (ha : a ∈ P.T₂) :
    (a * E.x * a⁻¹) * P.k * (a * E.x * a⁻¹)⁻¹ = P.z * P.k :=
  P.conj_flip P.conj_k ha E.x_z E.x_flip.1

theorem mem_T₂_of_comm_t (ht2 : t * t = 1) {g : X} (hg : g ∈ E.T₃)
    (hgt : t * g * t⁻¹ * g⁻¹ = 1 ∨ t * g * t⁻¹ * g⁻¹ = P.z) : g ∈ P.T₂ := by
  rcases E.mem_T₃ hg with h | h
  · exact h
  · exfalso
    set a := g * E.s⁻¹ with ha
    have hge : g = a * E.s := by rw [ha]; group
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hxinv : E.x⁻¹ = E.x := by
      rw [x, show (E.s * t * E.s⁻¹)⁻¹ = E.s * t⁻¹ * E.s⁻¹ by group, htinv]
    have e : t * g * t⁻¹ * g⁻¹ = t * (a * E.x * a⁻¹) := by
      rw [hge, x, show t * (a * E.s) * t⁻¹ * (a * E.s)⁻¹ = t * (a * (E.s * t⁻¹ * E.s⁻¹) * a⁻¹)
        by group, htinv]
    have hyk := E.conj_x_flip_k h
    have key : ∀ c : X, c = 1 ∨ c = P.z → t * (a * E.x * a⁻¹) = c → False := by
      intro c hc hy
      have hy' : a * E.x * a⁻¹ = t * c := by
        calc a * E.x * a⁻¹ = t⁻¹ * (t * (a * E.x * a⁻¹)) := by group
          _ = t * c := by rw [hy, htinv]
      rw [hy'] at hyk
      have hck : c * P.k * c⁻¹ = P.k := by
        rcases hc with rfl | rfl
        · group
        · rw [P.zk_comm, mul_inv_cancel_right]
      rw [show t * c * P.k * (t * c)⁻¹ = t * (c * P.k * c⁻¹) * t⁻¹ by group, hck, P.t_k] at hyk
      exact P.k_ne_zk hyk
    rcases hgt with h1 | h1
    · exact key 1 (Or.inl rfl) (e ▸ h1)
    · exact key P.z (Or.inr rfl) (e ▸ h1)

theorem center₃ (ht2 : t * t = 1) {g : X} (hg : g ∈ E.T₃) (hc : ∀ h ∈ E.T₃, g * h = h * g) :
    g = 1 ∨ g = P.z := by
  have hgT : g ∈ P.T₂ := E.mem_T₂_of_comm_t ht2 hg (Or.inl (by
    rw [show t * g = g * t from (hc t (E.T₂_le_T₃ P.t_mem)).symm]; group))
  exact P.center g hgT fun h hh => hc h (E.T₂_le_T₃ hh)

theorem Y₃ (ht2 : t * t = 1) (hw : E.s * P.w * E.s⁻¹ = P.w) {g : X} (hg : g ∈ E.T₃)
    (hY : ∀ h ∈ E.T₃, h * g * h⁻¹ = g ∨ h * g * h⁻¹ = P.z * g) :
    g = 1 ∨ g = P.z ∨ g = P.w ∨ g = P.z * P.w := by
  have hgT : g ∈ P.T₂ := by
    refine E.mem_T₂_of_comm_t ht2 hg ?_
    rcases hY t (E.T₂_le_T₃ P.t_mem) with h | h <;> rw [h]
    · left; group
    · right; group
  have hs := hY E.s E.s_mem_T₃
  simp only [← MulAut.conj_apply] at hs
  obtain ⟨φ, e0, e1, e2⟩ := P.exists_φ
  have hinj := P.φ_injective e0 e1 e2
  have hsw : MulAut.conj E.s P.w = P.w := by rw [MulAut.conj_apply]; exact hw
  rcases P.Y g hgT (fun h hh => hY h (E.T₂_le_T₃ hh)) with h | h | h | h | h | h | h | h <;>
    rw [h] at hs ⊢
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  all_goals first
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr rfl))
    | (exfalso
       rcases E.csk with h' | h' <;> simp only [map_mul, h', E.csz, hsw] at hs <;>
         rcases hs with h'' | h'' <;> exact absurd h'' (by elem_ne φ e0 e1 e2 hinj))

theorem h_z (ht2 : t * t = 1) {h : X} (hh : h ∈ normalizer (E.T₃ : Set X)) :
    h * P.z * h⁻¹ = P.z := by
  have hzT : h * P.z * h⁻¹ ∈ E.T₃ := Sec7.conj_mem_of_mem_normalizer hh (E.T₂_le_T₃ P.z_mem)
  have hc : ∀ g ∈ E.T₃, h * P.z * h⁻¹ * g = g * (h * P.z * h⁻¹) := by
    intro g hg
    have hg' : h⁻¹ * g * h ∈ E.T₃ := by
      have := Sec7.conj_mem_of_mem_normalizer (inv_mem hh) hg; rwa [inv_inv] at this
    have h1 : P.z * (h⁻¹ * g * h) = (h⁻¹ * g * h) * P.z := by
      have := E.conj_z₃ hg'
      calc P.z * (h⁻¹ * g * h) = (h⁻¹ * g * h) * P.z * (h⁻¹ * g * h)⁻¹ * (h⁻¹ * g * h) := by
            rw [this]
        _ = (h⁻¹ * g * h) * P.z := by group
    calc h * P.z * h⁻¹ * g = h * (P.z * (h⁻¹ * g * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * g * h) * P.z) * h⁻¹ := by rw [h1]
      _ = g * (h * P.z * h⁻¹) := by group
  rcases E.center₃ ht2 hzT hc with h1 | h1
  · exfalso; apply P.z_ne
    calc P.z = h⁻¹ * (h * P.z * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  · exact h1

theorem h_w (ht2 : t * t = 1) (hw : E.s * P.w * E.s⁻¹ = P.w) {h : X}
    (hh : h ∈ normalizer (E.T₃ : Set X)) : h * P.w * h⁻¹ = P.w ∨ h * P.w * h⁻¹ = P.z * P.w := by
  have hzh := E.h_z ht2 hh
  have hwT : h * P.w * h⁻¹ ∈ E.T₃ := Sec7.conj_mem_of_mem_normalizer hh (E.T₂_le_T₃ P.w_mem)
  have hY : ∀ g ∈ E.T₃, g * (h * P.w * h⁻¹) * g⁻¹ = h * P.w * h⁻¹ ∨
      g * (h * P.w * h⁻¹) * g⁻¹ = P.z * (h * P.w * h⁻¹) := by
    intro g hg
    have hg' : h⁻¹ * g * h ∈ E.T₃ := by
      have := Sec7.conj_mem_of_mem_normalizer (inv_mem hh) hg; rwa [inv_inv] at this
    have e : g * (h * P.w * h⁻¹) * g⁻¹ = h * ((h⁻¹ * g * h) * P.w * (h⁻¹ * g * h)⁻¹) * h⁻¹ := by
      group
    rcases E.conj_w₃ hw hg' with h1 | h1 <;> rw [e, h1]
    · exact Or.inl rfl
    · right
      rw [show h * (P.z * P.w) * h⁻¹ = (h * P.z * h⁻¹) * (h * P.w * h⁻¹) by group, hzh]
  rcases E.Y₃ ht2 hw hwT hY with h1 | h1 | h1 | h1
  · exfalso; apply P.w_ne₁
    calc P.w = h⁻¹ * (h * P.w * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  · exfalso; apply P.w_ne_z
    calc P.w = h⁻¹ * (h * P.w * h⁻¹) * h := by group
      _ = h⁻¹ * (h * P.z * h⁻¹) * h := by rw [h1, hzh]
      _ = P.z := by group
  · exact Or.inl h1
  · exact Or.inr h1

end SEl

end SPkg

end KD8ab

end CFSG.ComponentClassification.HSFLit
