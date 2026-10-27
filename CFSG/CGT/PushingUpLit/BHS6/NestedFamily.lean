module

public import CFSG.CGT.PushingUpLit.BHS6.NestedModel
public import CFSG.CGT.PushingUpLit.BHS6.NestedBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E F : Subgroup Γ}

theorem commutator_eq_pCoreOf_nested (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) (hF : F ∈ btBlocksG G T) (hFE : F ≤ E) :
    ⁅F, pCoreOf 2 E⁆ = pCoreOf 2 F := by
  have hW := pCoreOf_le_of_le_block hG hT hE hF hFE
  obtain ⟨s, hs, hFs⟩ := hF
  refine le_antisymm (commutator_pCoreOf_le_nested hG hT hE ⟨s, hs, hFs⟩) ?_
  calc pCoreOf 2 F = ⁅pCoreOf 2 F, F⁆ := hFs.perfect.symm
    _ ≤ ⁅pCoreOf 2 E, F⁆ := Subgroup.commutator_mono hW le_rfl
    _ = ⁅F, pCoreOf 2 E⁆ := Subgroup.commutator_comm _ _

theorem isIrrSection_autOn_nested (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hF : F ∈ btBlocksG G T) (hFE : F ≤ E) (hWe : IsElemAbelian 2 (pCoreOf 2 E)) :
    @IsIrrSection ↥(pCoreOf 2 E) (commGroupOfElemAbelian hWe) (autOn F (pCoreOf 2 E))
      (commOn hWe F ⊔ fixOn hWe F) (fixOn hWe F) := by
  classical
  let _ : CommGroup ↥(pCoreOf 2 E) := commGroupOfElemAbelian hWe
  have hF' := hF
  obtain ⟨s, hs, hFs⟩ := hF'
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hS : IsSylowOf 2 (A1b.conjSub s T) G :=
    isSylowOf_of_isSylowTwoOf (isSylowTwoOf_conjSub_of_mem hT' hs)
  have hcharF : CharTwo F := charTwo_of_isBTBlock hG hS hFs
  have hW'W := pCoreOf_le_of_le_block hG hT hE hF hFE
  have hFW : F ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) :=
    hFE.trans (le_normalizer_pCoreOf_self E)
  have hcomm : commOn hWe F = (pCoreOf 2 F).subgroupOf (pCoreOf 2 E) := by
    rw [commOn_eq hWe hFW, commutator_eq_pCoreOf_nested hG hT hE hF hFE]
  have hfix : fixOn hWe F = (Subgroup.centralizer (F : Set Γ)).subgroupOf (pCoreOf 2 E) :=
    fixOn_eq hWe hFW
  have hlt := inf_centralizer_lt_pCoreOf hFs hcharF
  refine ⟨?_, fun U hZU hUP hinv => ?_⟩
  · refine lt_of_le_of_ne le_sup_right fun h => ?_
    have hle : commOn hWe F ≤ fixOn hWe F := by rw [h]; exact le_sup_left
    have hWC : pCoreOf 2 F ≤ Subgroup.centralizer (F : Set Γ) := by
      intro w hw
      have hwW : w ∈ pCoreOf 2 E := hW'W hw
      have h1 : (⟨w, hwW⟩ : ↥(pCoreOf 2 E)) ∈ commOn hWe F := by
        rw [hcomm, Subgroup.mem_subgroupOf]
        exact hw
      have h2 := hle h1
      rw [hfix, Subgroup.mem_subgroupOf] at h2
      exact h2
    exact hlt.ne (inf_eq_left.mpr hWC)
  · set N : Subgroup Γ := pCoreOf 2 F ⊓ U.map (pCoreOf 2 E).subtype with hN
    have hCN : pCoreOf 2 F ⊓ Subgroup.centralizer (F : Set Γ) ≤ N := by
      intro w hw
      refine Subgroup.mem_inf.mpr ⟨hw.1, ?_⟩
      have hwW : w ∈ pCoreOf 2 E := hW'W hw.1
      have h1 : (⟨w, hwW⟩ : ↥(pCoreOf 2 E)) ∈ fixOn hWe F := by
        rw [hfix, Subgroup.mem_subgroupOf]
        exact hw.2
      exact ⟨⟨w, hwW⟩, hZU h1, rfl⟩
    have hNW : N ≤ pCoreOf 2 F := inf_le_left
    have hNn : ∀ g ∈ F, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
      intro g hg n hn
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf_self F hg) n).mp hn.1
      · obtain ⟨u, hu, rfl⟩ := hn.2
        have hmem : actOn (pCoreOf 2 E) F hFW ⟨g, hg⟩ ∈ autOn F (pCoreOf 2 E) := by
          rw [← range_actOn (pCoreOf 2 E) F hFW]
          exact ⟨_, rfl⟩
        refine ⟨actOn (pCoreOf 2 E) F hFW ⟨g, hg⟩ u, hinv _ hmem u hu, ?_⟩
        exact actOn_apply_coe hFW ⟨g, hg⟩ u
    have hPmem : ∀ u : ↥(pCoreOf 2 E), u ∈ commOn hWe F ⊔ fixOn hWe F →
        ∃ p ∈ commOn hWe F, ∃ z ∈ fixOn hWe F, p * z = u := fun u hu =>
      Subgroup.mem_sup.mp hu
    rcases pCoreOf_irred hFs hcharF N hCN hNW hNn with h1 | h1
    · left
      refine le_antisymm (fun u hu => ?_) hZU
      obtain ⟨p, hp, z, hz, rfl⟩ := hPmem u (hUP hu)
      have hpU : p ∈ U := by
        have : p = (p * z) * z⁻¹ := by group
        rw [this]
        exact U.mul_mem hu (U.inv_mem (hZU hz))
      have hpN : (p : Γ) ∈ N := by
        refine Subgroup.mem_inf.mpr ⟨?_, ⟨p, hpU, rfl⟩⟩
        rw [hcomm, Subgroup.mem_subgroupOf] at hp
        exact hp
      rw [h1] at hpN
      have hpC : p ∈ fixOn hWe F := by
        rw [hfix, Subgroup.mem_subgroupOf]
        exact hpN.2
      exact (fixOn hWe F).mul_mem hpC hz
    · right
      refine le_antisymm hUP (fun u hu => ?_)
      obtain ⟨p, hp, z, hz, rfl⟩ := hPmem u hu
      have hpW' : (p : Γ) ∈ pCoreOf 2 F := by
        rw [hcomm, Subgroup.mem_subgroupOf] at hp
        exact hp
      have hpN : (p : Γ) ∈ N := by rw [h1]; exact hpW'
      obtain ⟨u', hu', hu'p⟩ := hpN.2
      have hpU : p ∈ U := by
        have : u' = p := Subtype.ext hu'p
        rw [← this]
        exact hu'
      exact U.mul_mem hpU (hZU hz)

section Model

variable {V X : Subgroup Γ}

omit [Finite Γ] in
theorem actOn_mem_normalizer (hXE : X ≤ E) (hEV : E ≤ Subgroup.normalizer (V : Set Γ)) (x : ↥X) :
    actOn V X (hXE.trans hEV) x ∈ Subgroup.normalizer (autOn E V : Set (MulAut ↥V)) :=
  autOn_le_normalizer_autOn (hXE.trans hEV) (hXE.trans Subgroup.le_normalizer) (by
    rw [← range_actOn V X (hXE.trans hEV)]
    exact ⟨x, rfl⟩)

@[expose] noncomputable def modelHom (hXE : X ≤ E) (hEV : E ≤ Subgroup.normalizer (V : Set Γ))
    {S : Type*} [Group S]
    (ψ : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V))) →* S) : ↥X →* S :=
  ψ.comp ((actOn V X (hXE.trans hEV)).codRestrict
    (Subgroup.normalizer (autOn E V : Set (MulAut ↥V))) (actOn_mem_normalizer hXE hEV))

omit [Finite Γ] in
theorem modelHom_apply (hXE : X ≤ E) (hEV : E ≤ Subgroup.normalizer (V : Set Γ)) {S : Type*}
    [Group S] (ψ : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V))) →* S) (x : ↥X) :
    modelHom hXE hEV ψ x = ψ ⟨actOn V X (hXE.trans hEV) x, actOn_mem_normalizer hXE hEV x⟩ :=
  rfl

omit [Finite Γ] in
theorem coreAct_modelHom (hXE : X ≤ E) (hEV : E ≤ Subgroup.normalizer (V : Set Γ)) {n : ℕ}
    (βe : ↥V ≃* ↥(coreMod n))
    (ψ : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V))) →* Equiv.Perm (Fin n))
    (hψ : ∀ (a : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V)))) (w : ↥V),
      βe ((a : MulAut ↥V) w) = coreAct n (ψ a) (βe w)) (x : ↥X) :
    coreAct n (modelHom hXE hEV ψ x) = MulAut.congr βe (actOn V X (hXE.trans hEV) x) := by
  ext d
  obtain ⟨w, rfl⟩ := βe.surjective d
  rw [modelHom_apply, ← hψ ⟨_, actOn_mem_normalizer hXE hEV x⟩ w, congr_apply_apply]

omit [Finite Γ] in
theorem map_range_modelHom (hXE : X ≤ E) (hEV : E ≤ Subgroup.normalizer (V : Set Γ)) {n : ℕ}
    (βe : ↥V ≃* ↥(coreMod n))
    (ψ : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V))) →* Equiv.Perm (Fin n))
    (hψ : ∀ (a : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V)))) (w : ↥V),
      βe ((a : MulAut ↥V) w) = coreAct n (ψ a) (βe w)) :
    (modelHom hXE hEV ψ).range.map (coreAct n) =
      (autOn X V).map (MulAut.congr βe).toMonoidHom := by
  have h1 : (coreAct n).comp (modelHom hXE hEV ψ) =
      (MulAut.congr βe).toMonoidHom.comp (actOn V X (hXE.trans hEV)) :=
    MonoidHom.ext fun x => coreAct_modelHom hXE hEV βe ψ hψ x
  rw [← MonoidHom.range_comp, h1, MonoidHom.range_comp, range_actOn]

omit [Finite Γ] in
theorem mem_range_modelHom_iff (hXE : X ≤ E) (hEV : E ≤ Subgroup.normalizer (V : Set Γ))
    {S : Type*} [Group S]
    (ψ : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V))) →* S) (hψ : Function.Injective ψ)
    (a : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V)))) :
    ψ a ∈ (modelHom hXE hEV ψ).range ↔ (a : MulAut ↥V) ∈ autOn X V := by
  constructor
  · rintro ⟨x, hx⟩
    rw [modelHom_apply] at hx
    have : a = ⟨actOn V X (hXE.trans hEV) x, actOn_mem_normalizer hXE hEV x⟩ := hψ hx.symm
    rw [this, ← range_actOn V X (hXE.trans hEV)]
    exact ⟨x, rfl⟩
  · intro ha
    rw [← range_actOn V X (hXE.trans hEV)] at ha
    obtain ⟨x, hx⟩ := ha
    refine ⟨x, ?_⟩
    rw [modelHom_apply]
    congr 1
    exact Subtype.ext hx

theorem card_range_modelHom (hXE : X ≤ E) (hEV : E ≤ Subgroup.normalizer (V : Set Γ))
    {S : Type*} [Group S]
    (ψ : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V))) →* S) (hψ : Function.Injective ψ) :
    Nat.card ↥(modelHom hXE hEV ψ).range = Nat.card ↥(autOn X V) := by
  have hker : (modelHom hXE hEV ψ).ker = (actOn V X (hXE.trans hEV)).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, modelHom_apply, ← map_one ψ]
    constructor
    · intro h
      exact congrArg Subtype.val (hψ h)
    · intro h
      congr 1
      exact Subtype.ext h
  have h1 := Subgroup.card_ker_mul_card_range (modelHom hXE hEV ψ)
  have h2 := Subgroup.card_ker_mul_card_range (actOn V X (hXE.trans hEV))
  rw [hker, ← h2, range_actOn] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

omit [Finite Γ] in
theorem mem_normalizer_autOn_of_map (hXE : X ≤ E) (hEV : E ≤ Subgroup.normalizer (V : Set Γ))
    {S : Type*} [Group S]
    (ψ : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V))) →* S) (hψ : Function.Injective ψ)
    {z : MulAut ↥V} (hz : z ∈ Subgroup.normalizer (autOn E V : Set (MulAut ↥V)))
    (hmem : ψ ⟨z, hz⟩ ∈ Subgroup.normalizer ((modelHom hXE hEV ψ).range : Set S)) :
    z ∈ Subgroup.normalizer (autOn X V : Set (MulAut ↥V)) := by
  have hAN : autOn X V ≤ Subgroup.normalizer (autOn E V : Set (MulAut ↥V)) := fun a ha => by
    rw [← range_actOn V X (hXE.trans hEV)] at ha
    obtain ⟨x, rfl⟩ := ha
    exact actOn_mem_normalizer hXE hEV x
  have hmem' := Subgroup.mem_normalizer_iff.mp hmem
  have key : ∀ (h' : MulAut ↥V) (hh' : h' ∈ Subgroup.normalizer (autOn E V : Set (MulAut ↥V))),
      h' ∈ autOn X V ↔ ψ ⟨h', hh'⟩ ∈ (modelHom hXE hEV ψ).range := fun h' hh' =>
    (mem_range_modelHom_iff hXE hEV ψ hψ ⟨h', hh'⟩).symm
  have hzN : ∀ h' ∈ Subgroup.normalizer (autOn E V : Set (MulAut ↥V)),
      z * h' * z⁻¹ ∈ Subgroup.normalizer (autOn E V : Set (MulAut ↥V)) := fun h' hh' =>
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hz hh')
      ((Subgroup.normalizer _).inv_mem hz)
  have hψc : ∀ (h' : MulAut ↥V) (hh' : h' ∈ Subgroup.normalizer (autOn E V : Set (MulAut ↥V))),
      ψ ⟨z * h' * z⁻¹, hzN h' hh'⟩ = ψ ⟨z, hz⟩ * ψ ⟨h', hh'⟩ * (ψ ⟨z, hz⟩)⁻¹ := by
    intro h' hh'
    have e : (⟨z * h' * z⁻¹, hzN h' hh'⟩ :
        ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V)))) =
        ⟨z, hz⟩ * ⟨h', hh'⟩ * ⟨z, hz⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhN := hAN hh
    rw [key _ (hzN _ hhN), hψc _ hhN]
    exact (hmem' _).mp ((key _ hhN).mp hh)
  · intro hh
    have hhN' := hAN hh
    have hhN : h ∈ Subgroup.normalizer (autOn E V : Set (MulAut ↥V)) := by
      have e : h = z⁻¹ * (z * h * z⁻¹) * z := by group
      rw [e]
      exact (Subgroup.normalizer _).mul_mem
        ((Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem hz) hhN') hz
    rw [key _ hhN]
    have h1 := (key _ hhN').mp hh
    rw [hψc _ hhN] at h1
    exact (hmem' _).mpr h1

end Model

end CFSG.CGT.PushingUpLit.BHS6
