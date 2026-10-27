module

public import CFSG.CGT.PushingUpLit.SYMB.FiveKernel
public import CFSG.CGT.PushingUpLit.SYMB.FiveNormal
public import CFSG.CGT.PushingUpLit.SYMB.SevenFamily

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ} {n : ℕ}
  {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(G6.coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

structure FiveCase (S : SymSetting G T V n φ ψ T') (E : Subgroup Γ) : Prop where
  join : SymJoin G T V φ ψ E
  normal : G ≤ Subgroup.normalizer (E : Set Γ)
  sup : G ≤ E ⊔ T
  comm : ⁅E, pCoreOf 2 G⁆ ≤ V

namespace FiveCase

variable {S : SymSetting G T V n φ ψ T'} {E : Subgroup Γ}

theorem isPGroup_K (h : FiveCase S E) :
    IsPGroup 2 ↥(E ⊓ Subgroup.centralizer (V : Set Γ)) :=
  isPGroup_inf_centralizer_of_comm_le S.charTwo h.join.le h.comm

theorem ker_le_pCore (h : FiveCase S E) : kerG G φ ≤ pCoreOf 2 G :=
  sym_ker_le_pCore S h.join.le h.normal h.sup h.isPGroup_K

theorem ker_le_T (h : FiveCase S E) : kerG G φ ≤ T :=
  sym_ker_le_T S h.join.le h.normal h.sup h.isPGroup_K

omit [Finite Γ] in
theorem K_le_ker (h : FiveCase S E) :
    E ⊓ Subgroup.centralizer (V : Set Γ) ≤ kerG G φ :=
  fun _ hk => sym_mem_kerG S (h.join.le hk.1) hk.2

theorem K_le_pCore (h : FiveCase S E) : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ pCoreOf 2 G :=
  h.K_le_ker.trans h.ker_le_pCore

omit [Finite Γ] in
theorem ker_le_centralizer (S' : SymSetting G T V n φ ψ T') {g : Γ} (hg : g ∈ kerG G φ) :
    g ∈ Subgroup.centralizer (V : Set Γ) := by
  obtain ⟨hgG, hg1⟩ := mem_kerG.1 hg
  have h2 : (⟨g, hgG⟩ : ↥G) ∈ φ.ker := hg1
  rw [S'.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
  exact h2.2

omit [Finite Γ] in
theorem comm_mem_K (h : FiveCase S E) {r e : Γ} (hr : r ∈ kerG G φ) (he : e ∈ E) :
    ⁅r, e⁆ ∈ E ⊓ Subgroup.centralizer (V : Set Γ) := by
  have hrG : r ∈ G := (mem_kerG.1 hr).1
  have h1 : ⁅r, e⁆ ∈ E := by
    have e1 : ⁅r, e⁆ = (r * e * r⁻¹) * e⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e1]
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp (h.normal hrG) e).mp he) (E.inv_mem he)
  have h2 : ⁅r, e⁆ ∈ kerG G φ := by
    have e1 : ⁅r, e⁆ = r * (e * r⁻¹ * e⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e1]
    have heG : e ∈ G := h.join.le he
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerG G φ heG) r⁻¹).mp
      ((kerG G φ).inv_mem hr)
    exact (kerG G φ).mul_mem hr this
  exact ⟨h1, ker_le_centralizer S h2⟩

end FiveCase

omit [Finite Γ] in
theorem comm_V_E_normal (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ}
    (hnorm : G ≤ Subgroup.normalizer (E : Set Γ)) :
    G ≤ Subgroup.normalizer ((⁅V, E⁆ : Subgroup Γ) : Set Γ) := by
  have key : ∀ g ∈ G, ∀ x ∈ (⁅V, E⁆ : Subgroup Γ), g * x * g⁻¹ ∈ (⁅V, E⁆ : Subgroup Γ) := by
    intro g hg x hx
    have hle : (⁅V, E⁆ : Subgroup Γ) ≤ (⁅V, E⁆ : Subgroup Γ).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro v hv e he
      have hv' : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (S.data.normal hg) v).mp hv
      have he' : g * e * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hnorm hg) e).mp he
      have h1 : ⁅g * v * g⁻¹, g * e * g⁻¹⁆ ∈ (⁅V, E⁆ : Subgroup Γ) :=
        Subgroup.commutator_mem_commutator hv' he'
      have e1 : (MulAut.conj g).toMonoidHom ⁅v, e⁆ = ⁅g * v * g⁻¹, g * e * g⁻¹⁆ := by
        simp [commutatorElement_def]
        group
      show (MulAut.conj g).toMonoidHom ⁅v, e⁆ ∈ (⁅V, E⁆ : Subgroup Γ)
      rw [e1]
      exact h1
    exact hle hx
  intro g hg
  exact B6.mem_normalizer_of_forall_mem (key g hg) fun x hx => by
    simpa using key g⁻¹ (G.inv_mem hg) x hx

namespace FiveCase

variable {S : SymSetting G T V n φ ψ T'} {E : Subgroup Γ}

omit [Finite Γ] in
theorem V₁_le_K (h : FiveCase S E) : ⁅V, E⁆ ≤ E ⊓ Subgroup.centralizer (V : Set Γ) :=
  comm_V_E_le_K S h.join.le h.normal

theorem comm_K_E (h : FiveCase S E) :
    ⁅E ⊓ Subgroup.centralizer (V : Set Γ), E⁆ ≤ ⁅V, E⁆ :=
  comm_K_E_le_V₁ S h.join.le h.join.residual h.comm h.K_le_pCore

theorem comm_R_E (h : FiveCase S E) {r : Γ} (hr : r ∈ kerG G φ) {e : Γ} (he : e ∈ E) :
    ⁅r, e⁆ ∈ ⁅V, E⁆ := by
  classical
  set K : Subgroup Γ := E ⊓ Subgroup.centralizer (V : Set Γ) with hK
  set V₁ : Subgroup Γ := ⁅V, E⁆ with hV₁
  have hV1K : V₁ ≤ K := h.V₁_le_K
  have hK2 : IsPGroup 2 ↥K := h.isPGroup_K
  have hZ : (V₁.subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hgG : (g : Γ) ∈ G := h.join.le g.2.1
    have := (Subgroup.mem_normalizer_iff.mp (comm_V_E_normal S h.normal hgG) (x : Γ)).mp hx
    simpa using this
  let d : ↥E → ↥K := fun e' => ⟨⁅r, e'⁆, h.comm_mem_K hr e'.2⟩
  have hd : ∀ e1 e2 : ↥E, (QuotientGroup.mk (d (e1 * e2)) : ↥K ⧸ V₁.subgroupOf K) =
      QuotientGroup.mk (d e1) * QuotientGroup.mk (d e2) := by
    intro e1 e2
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hcK : ⁅r, (e2 : Γ)⁆ ∈ K := h.comm_mem_K hr e2.2
    have hmem : ⁅(e1 : Γ), (⁅r, (e2 : Γ)⁆)⁻¹⁆ ∈ V₁ := by
      have h1 : ⁅(⁅r, (e2 : Γ)⁆)⁻¹, (e1 : Γ)⁆ ∈ ⁅K, E⁆ :=
        Subgroup.commutator_mem_commutator (K.inv_mem hcK) e1.2
      have h2 := h.comm_K_E h1
      have := V₁.inv_mem h2
      rwa [commutatorElement_inv] at this
    show ((⁅r, ((e1 * e2 : ↥E) : Γ)⁆)⁻¹ * (⁅r, (e1 : Γ)⁆ * ⁅r, (e2 : Γ)⁆)) ∈ V₁
    have e3 : (⁅r, ((e1 * e2 : ↥E) : Γ)⁆)⁻¹ * (⁅r, (e1 : Γ)⁆ * ⁅r, (e2 : Γ)⁆) =
        ⁅(e1 : Γ), (⁅r, (e2 : Γ)⁆)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    rw [e3]
    exact hmem
  have := mem_of_oResidualTwo h.join.residual hK2 hZ d hd ⟨e, he⟩
  rw [Subgroup.mem_subgroupOf] at this
  exact this

end FiveCase

end CFSG.CGT.PushingUpLit.SYMB
