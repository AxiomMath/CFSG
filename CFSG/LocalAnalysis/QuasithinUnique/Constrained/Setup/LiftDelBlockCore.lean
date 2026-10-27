module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
open scoped commutatorElement

section Main

theorem delBlockCoreProp
    : DelBlockCoreProp := by
  intro G _ _ R M V n F _ r Lc ctx hcore hall hImage
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hfam := del_family_data hS ctx.comps ctx.deleted
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  have hr : 0 < r := hbridge.r_pos
  obtain ⟨Fs0, P0, hP0⟩ := hall ⟨0, hr⟩
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set LS := L ⊔ baum R with hLS
  obtain ⟨hQL, hVL, hUQc⟩ := hP0.sum.commutator
  have hVLS : V ≤ LS := hcore.V_le_S.trans le_sup_right
  have hQLS : pCoreOf 2 LS ≤ LS := CFSG.LieType.BorelTits.pCoreOf_le 2 LS
  have hUQ : ∀ j, modComm V (Lc j) ≤ pCoreOf 2 LS := fun j =>
    (le_iSup (fun j => modComm V (Lc j)) j).trans (hUQc.trans (omegaOneCenterOf_le _))
  have hIV : ∀ j, modComm V (Lc j) ≤ V := fun j => modComm_le V (Lc j)
  have hBLS : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ LS := fun j =>
    (oddOrderSubgroup_le _).trans inf_le_left
  have hBL : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ L := fun j =>
    oddOrderSubgroup_mono le_top
  have hLSnB : ∀ j, LS ≤ Subgroup.normalizer
      ((blockOf (⊤ : Subgroup G) R V hX (Lc j) : Subgroup G) : Set G) := fun j =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hBLS j)).1 (hImage.normal_B j)
  have hLSnLc : ∀ j, autOn LS V ≤ Subgroup.normalizer (Lc j : Set (MulAut V)) := by
    intro j
    have h1 := autOn_le_normalizer_autOn (hnormV LS) (hnormV _) (hLSnB j)
    rwa [hImage.image j] at h1
  have hLSnI : ∀ j, LS ≤ Subgroup.normalizer ((modComm V (Lc j) : Subgroup G) : Set G) := fun j =>
    le_normalizer_modComm (hLSnLc j)
  have hlift : ∀ j, ∀ x ∈ Lc j, ∃ b ∈ blockOf (⊤ : Subgroup G) R V hX (Lc j),
      MulAut.conjNormal (H := V) b = x := by
    intro j x hx
    have hx' : x ∈ (blockOf (⊤ : Subgroup G) R V hX (Lc j)).map (MulAut.conjNormal (H := V)) := by
      rw [← autOn_eq_map_conjNormal, hImage.image j]
      exact hx
    obtain ⟨b, hb, hbx⟩ := hx'
    exact ⟨b, hb, hbx⟩
  have hρmem : ∀ j, ∀ b ∈ blockOf (⊤ : Subgroup G) R V hX (Lc j),
      MulAut.conjNormal (H := V) b ∈ Lc j := by
    intro j b hb
    have : MulAut.conjNormal (H := V) b ∈ autOn (blockOf (⊤ : Subgroup G) R V hX (Lc j)) V := by
      rw [autOn_eq_map_conjNormal]
      exact Subgroup.mem_map_of_mem _ hb
    rwa [hImage.image j] at this
  refine ⟨fun i => ?_, fun i => ?_⟩
  ·
    have hIgen : ∀ u : G, u ∈ modComm V (Lc i) → u ∈ Subgroup.closure
        {g : G | ∃ b ∈ blockOf (⊤ : Subgroup G) R V hX (Lc i), ∃ w ∈ modComm V (Lc i),
          g = ⁅b, w⁆} := by
      intro u hu
      have hu1 := hfam.comm i ⟨u, hIV i hu⟩ hu
      refine (Subgroup.closure_le _).2 ?_ hu1
      rintro g ⟨x, hx, w, hw, rfl⟩
      obtain ⟨b, hb, rfl⟩ := hlift i x hx
      refine Subgroup.subset_closure ⟨b, hb, w, hw, ?_⟩
      rw [MulAut.conjNormal_apply]
      simp [commutatorElement_def]
    have hIB : modComm V (Lc i) ≤ blockOf (⊤ : Subgroup G) R V hX (Lc i) := by
      intro u hu
      refine (Subgroup.closure_le _).2 ?_ (hIgen u hu)
      rintro g ⟨b, hb, w, hw, rfl⟩
      have hwLS : w ∈ LS := hVLS (hIV i hw)
      have h1 : w * b⁻¹ * w⁻¹ ∈ blockOf (⊤ : Subgroup G) R V hX (Lc i) :=
        conj_mem_of_mem_normalizer (hLSnB i hwLS)
          ((blockOf (⊤ : Subgroup G) R V hX (Lc i)).inv_mem hb)
      have h2 : ⁅b, w⁆ = b * (w * b⁻¹ * w⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [h2]
      exact (blockOf (⊤ : Subgroup G) R V hX (Lc i)).mul_mem hb h1
    have hgen : ∀ S' : Subgroup G, modComm V (Lc i) ≤ S' →
        modComm V (Lc i) ≤ ⁅S', blockOf (⊤ : Subgroup G) R V hX (Lc i)⁆ := by
      intro S' hIS' u hu
      refine (Subgroup.closure_le _).2 ?_ (hIgen u hu)
      rintro g ⟨b, hb, w, hw, rfl⟩
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hb (hIS' hw)
    have hUB : ⁅⨆ j, modComm V (Lc j), blockOf (⊤ : Subgroup G) R V hX (Lc i)⁆ ≤
        modComm V (Lc i) := by
      rw [Subgroup.commutator_le]
      intro u hu b hb
      have hmain : u ∈ LS ∧ ∀ b ∈ blockOf (⊤ : Subgroup G) R V hX (Lc i),
          ⁅u, b⁆ ∈ modComm V (Lc i) := by
        refine Subgroup.iSup_induction (fun j => modComm V (Lc j))
          (C := fun u => u ∈ LS ∧ ∀ b ∈ blockOf (⊤ : Subgroup G) R V hX (Lc i),
            ⁅u, b⁆ ∈ modComm V (Lc i)) hu ?_ ?_ ?_
        · intro j u hu
          refine ⟨hVLS (hIV j hu), fun b hb => ?_⟩
          by_cases hji : j = i
          · subst hji
            have h1 : b * u⁻¹ * b⁻¹ ∈ modComm V (Lc j) :=
              conj_mem_of_mem_normalizer (hLSnI j (hBLS j hb)) ((modComm V (Lc j)).inv_mem hu)
            have h2 : ⁅u, b⁆ = u * (b * u⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
            rw [h2]
            exact (modComm V (Lc j)).mul_mem hu h1
          · have h1 := hfam.others j i (Ne.symm hji) (MulAut.conjNormal (H := V) b)
              (hρmem i b hb) ⟨u, hIV j hu⟩ hu
            have h2 : b * u * b⁻¹ = u := by
              have h3 := congrArg (fun z : V => (z : G)) h1
              simpa [MulAut.conjNormal_apply] using h3
            have h3 : u * b = b * u := by
              calc u * b = (b * u * b⁻¹) * b := by rw [h2]
                _ = b * u := by group
            rw [commutatorElement_eq_one_iff_mul_comm.2 h3]
            exact (modComm V (Lc i)).one_mem
        · refine ⟨LS.one_mem, fun b _ => ?_⟩
          simp [commutatorElement_def]
        · rintro x y ⟨hxLS, hx⟩ ⟨hyLS, hy⟩
          refine ⟨LS.mul_mem hxLS hyLS, fun b hb => ?_⟩
          have h1 : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
            simp [commutatorElement_def]
            group
          rw [h1]
          exact (modComm V (Lc i)).mul_mem
            (conj_mem_of_mem_normalizer (hLSnI i hxLS) (hy b hb)) (hx b hb)
      exact hmain.2 b hb
    have hQBle : ⁅pCoreOf 2 LS, blockOf (⊤ : Subgroup G) R V hX (Lc i)⁆ ≤ modComm V (Lc i) := by
      have h1 : ⁅⁅blockOf (⊤ : Subgroup G) R V hX (Lc i), pCoreOf 2 LS⁆,
          blockOf (⊤ : Subgroup G) R V hX (Lc i)⁆ ≤ modComm V (Lc i) := by
        refine le_trans (Subgroup.commutator_mono ?_ le_rfl) hUB
        rw [Subgroup.commutator_comm, ← hVL, ← hQL]
        exact Subgroup.commutator_mono le_rfl (hBL i)
      have h2 := perfect_commutator_le_mod (K := LS) (hBLS i) hQLS (hLSnI i)
        (hImage.perfect_self i) h1
      rwa [Subgroup.commutator_comm] at h2
    have hQB : ⁅pCoreOf 2 LS, blockOf (⊤ : Subgroup G) R V hX (Lc i)⁆ = modComm V (Lc i) :=
      le_antisymm hQBle (hgen _ (hUQ i))
    refine ⟨?_, hQB⟩
    rw [hImage.core i]
    refine le_antisymm ?_ (hgen _ (le_inf hIB (hUQ i)))
    exact (Subgroup.commutator_mono inf_le_right le_rfl).trans hQB.le
  ·
    rw [eq_bot_iff]
    rintro g ⟨hgI, hgC⟩
    have hgV : g ∈ V := hIV i hgI
    have hu : (⟨g, hgV⟩ : ↥V) = 1 := by
      refine hfam.fixed i ⟨g, hgV⟩ hgI ?_
      intro x hx
      obtain ⟨b, hb, rfl⟩ := hlift i x hx
      apply Subtype.ext
      show b * g * b⁻¹ = g
      have h1 := Subgroup.mem_centralizer_iff.1 hgC b hb
      rw [h1]
      group
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hu)

end Main

end CFSG.QuasithinUnique.Setup.Lift
