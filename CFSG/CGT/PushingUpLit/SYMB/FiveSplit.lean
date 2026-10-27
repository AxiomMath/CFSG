module

public import CFSG.CGT.PushingUpLit.SYMB.Split5
public import CFSG.CGT.PushingUpLit.SYMB.Delta5Fix
public import CFSG.CGT.PushingUpLit.SYMB.FiveCoho
public import CFSG.CGT.PushingUpLit.SYMB.FiveStruct

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {E : Subgroup Γ}

@[expose] def actV (S : SymSetting G T V 5 φ ψ T') (g : ↥G) : MulAut ↥V where
  toFun v := ⟨(g : Γ) * v * (g : Γ)⁻¹, S.data.conj_mem g.2 v.2⟩
  invFun v := ⟨(g : Γ)⁻¹ * v * (g : Γ)⁻¹⁻¹, S.data.conj_mem (G.inv_mem g.2) v.2⟩
  left_inv v := Subtype.ext (by simp [mul_assoc])
  right_inv v := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

omit [Finite Γ] in
theorem actV_apply (S : SymSetting G T V 5 φ ψ T') (g : ↥G) (v : ↥V) :
    ((actV S g v : ↥V) : Γ) = (g : Γ) * v * (g : Γ)⁻¹ := rfl

@[expose] def actVHom (S : SymSetting G T V 5 φ ψ T') : ↥G →* MulAut ↥V where
  toFun := actV S
  map_one' := by
    ext v
    simp [actV_apply]
  map_mul' a b := by
    ext v
    simp [actV_apply, MulAut.mul_apply, mul_assoc]

namespace FiveCase

theorem v1Iso (h : FiveCase S E) : V1Iso S ⁅V, E⁆ := by
  classical
  have hEG : E ≤ G := h.join.le
  have hVcomm : ∀ a b : ↥V, a * b = b * a := fun a b => S.data.elemAbelian.1.is_comm.comm a b
  let _ : CommGroup ↥V := { (inferInstance : Group ↥V) with mul_comm := hVcomm }
  let η : ↥E →* Equiv.Perm (Fin 5) := φ.comp (Subgroup.inclusion hEG)
  have hA : ∀ e, η e ∈ alternatingGroup (Fin 5) := fun e => h.join.map_mem_alt e.2
  have hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, η e = σ := by
    intro σ hσ
    have : σ ∈ imgG G φ E := by
      rw [h.join.img_eq_alt]
      exact hσ
    obtain ⟨e, heG, heE, hφ⟩ := mem_imgG.1 this
    exact ⟨⟨e, heE⟩, hφ⟩
  let act : ↥E →* MulAut ↥V := (actVHom S).comp (Subgroup.inclusion hEG)
  have hact : ∀ (e : ↥E) (v : ↥V), ((act e v : ↥V) : Γ) = (e : Γ) * v * (e : Γ)⁻¹ :=
    fun e v => rfl
  have hX : ∀ x : ↥V, x * x = 1 := fun x => by
    apply Subtype.ext
    have := S.data.elemAbelian.2 (x : Γ) x.2
    simpa [sq] using this
  have hker : ∀ e : ↥E, η e = 1 → ∀ x : ↥V, act e x = x := by
    intro e he x
    apply Subtype.ext
    rw [hact]
    exact S.data.conj_eq_of_map_eq_one (hEG e.2) he x.2
  have hψ : ∀ (e : ↥E) (x : ↥V), ψ (act e x) = G6.coreAct 5 (η e) (ψ x) := fun e x =>
    S.data.equivar ⟨e, hEG e.2⟩ x _
  obtain ⟨s, hψs, hs'⟩ := exists_equivariant_section η hA hs hX act hker ψ S.data.ψ_surj hψ
  have hsub : ∀ w : ↥(G6.coreMod 5), ((s w : ↥V) : Γ) ∈ ⁅V, E⁆ := by
    let Z : Subgroup ↥(G6.coreMod 5) := (⁅V, E⁆.subgroupOf V).comap s
    have hZ : ∀ w, w ∈ Z := by
      intro w
      refine (Subgroup.closure_le Z).2 ?_ (Delta5Fix.comm_closure w)
      rintro x ⟨σ, u, hσ, rfl⟩
      have hσA : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hσ
      obtain ⟨e, he⟩ := hs σ hσA
      show s (G6.coreAct 5 σ u * u⁻¹) ∈ ⁅V, E⁆.subgroupOf V
      rw [map_mul, map_inv, ← he, ← hs' e u, Subgroup.mem_subgroupOf]
      have hmem : ⁅(e : Γ), ((s u : ↥V) : Γ)⁆ ∈ ⁅V, E⁆ := by
        have h1 := Subgroup.commutator_mem_commutator (s u).2 e.2
        have h2 := (⁅V, E⁆).inv_mem h1
        rwa [commutatorElement_inv] at h2
      have e1 : ((act e (s u) * (s u)⁻¹ : ↥V) : Γ) = ⁅(e : Γ), ((s u : ↥V) : Γ)⁆ := by
        rw [Subgroup.coe_mul, hact, Subgroup.coe_inv, commutatorElement_def]
      rw [e1]
      exact hmem
    exact fun w => Subgroup.mem_subgroupOf.1 (hZ w)
  have hsup : ⁅V, E⁆ ≤ (s.range).map V.subtype := by
    rw [Subgroup.commutator_le]
    intro v hv e he
    have hmemV : ⁅v, e⁆ ∈ V := comm_V_E_le_V S hEG (Subgroup.commutator_mem_commutator hv he)
    let v' : ↥V := ⟨v, hv⟩
    let e' : ↥E := ⟨e, he⟩
    let w : ↥(G6.coreMod 5) := ψ v'
    let d : ↥V := v' * (s w)⁻¹
    have hd : ψ d = 1 := by
      show ψ (v' * (s w)⁻¹) = 1
      rw [map_mul, map_inv, hψs w]
      exact mul_inv_cancel w
    have hdc : act e' d = d := by
      have h1 : d ∈ ψ.ker := hd
      rw [S.data.ψ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1
      apply Subtype.ext
      rw [hact]
      have h2 := Subgroup.mem_centralizer_iff.1 h1.2 (e : Γ) (hEG he)
      show (e : Γ) * (d : Γ) * (e : Γ)⁻¹ = d
      rw [h2]
      group
    have hv' : v' = d * s w := (inv_mul_cancel_right v' (s w)).symm
    have hact_v : act e' v' = d * s (G6.coreAct 5 (η e') w) := by
      conv_lhs => rw [hv']
      rw [map_mul, hdc, hs' e' w]
    have key : v' * (act e' v')⁻¹ = s (w * (G6.coreAct 5 (η e') w)⁻¹) := by
      rw [hact_v, map_mul, map_inv]
      rw [hv']
      rw [← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv]
    refine ⟨v' * (act e' v')⁻¹, ⟨w * (G6.coreAct 5 (η e') w)⁻¹, key.symm⟩, ?_⟩
    show ((v' * (act e' v')⁻¹ : ↥V) : Γ) = ⁅v, e⁆
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hact]
    simp only [v', e', commutatorElement_def]
    group
  refine ⟨comm_V_E_le_V S hEG, comm_V_E_normal S h.normal, ?_, ?_⟩
  · intro v hv hψ1
    obtain ⟨x, ⟨w, rfl⟩, hxv⟩ := hsup hv
    have hxv' : s w = v := Subtype.ext hxv
    rw [← hxv', hψs w] at hψ1
    rw [← hxv', hψ1, map_one]
  · intro w
    exact ⟨s w, hsub w, hψs w⟩

end FiveCase

end CFSG.CGT.PushingUpLit.SYMB
