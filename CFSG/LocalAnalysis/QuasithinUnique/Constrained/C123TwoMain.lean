module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C123TwoCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C123TwoFrattini
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Four
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourMain

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

section Auxiliary

variable {G : Type} [Group G]

theorem c123Two_normalizer_le_of_char {S C : Subgroup G} (hCS : C ≤ S)
    (hC : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  refine le_normalizer_of_forall_conj fun a ha d hd => ?_
  have h := Subgroup.characteristic_iff_le_comap.1 hC (S.normalizerMonoidHom ⟨a, ha⟩)
  have h2 : S.normalizerMonoidHom ⟨a, ha⟩ ⟨d, hCS hd⟩ ∈ C.subgroupOf S :=
    h (show (⟨d, hCS hd⟩ : ↥S) ∈ C.subgroupOf S from hd)
  exact h2

theorem c123Two_omegaOneCenter_le {T R : Subgroup G} (hb : baum T ≤ R) (hRT : R ≤ T) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter R := by
  refine (Subgroup.closure_le _).2 fun z hz => ?_
  have hzB : z ∈ baum T := C1GN.omegaOneCenterOf_le_baum T (Subgroup.subset_closure hz)
  exact Subgroup.subset_closure
    ⟨⟨hb hzB, Subgroup.centralizer_le (fun x hx => hRT hx) hz.1.2⟩, hz.2⟩

end Auxiliary

section Main

variable {G : Type} [Group G] [Finite G]

theorem c123Two_of_isGNChoice
    {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂) : C123TwoStatement C₁ C₂ := by
  intro T R Y L hT hbR hRT hR hY hL hprod hexc
  have hH : Hyp R Y L := ⟨hR, hY, hL, hprod, hexc⟩
  have hT0 : T ≠ ⊥ := fun h => hH.T_ne_bot (le_bot_iff.1 (h ▸ hRT))
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair T hT hT0
  have h1Z' : C₁ T ≤ quasithinOmegaOneCenter T := h1Z
  have hZR : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter R :=
    c123Two_omegaOneCenter_le hbR hRT
  have h1V : C₁ T ≤ VZ R Y := h1Z'.trans (hZR.trans Hyp.Z_le_V)
  have hN : Subgroup.normalizer (baum R : Set G) ≤ Subgroup.normalizer (C₂ T : Set G) := by
    rw [← baum_eq_of_le hbR hRT]
    exact c123Two_normalizer_le_of_char h2B h2char
  set W : Subgroup G :=
    (Y ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (Y ⊓ Subgroup.normalizer (C₂ T : Set G)) with hW
  have hWV : Y ⊓ Subgroup.centralizer (VZ R Y : Set G) ≤ W := fun d hd =>
    Subgroup.mem_sup_left ⟨hd.1, Subgroup.centralizer_le (fun x hx => h1V hx) hd.2⟩
  have hWB : Y ⊓ Subgroup.normalizer (baum R : Set G) ≤ W := fun d hd =>
    Subgroup.mem_sup_right ⟨hd.1, hN hd.2⟩
  have hWZ : Y ⊓ Subgroup.centralizer (quasithinOmegaOneCenter R : Set G) ≤ W := fun d hd =>
    Subgroup.mem_sup_left ⟨hd.1, Subgroup.centralizer_le (fun x hx => (h1Z'.trans hZR) hx) hd.2⟩
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  by_cases hJ : thompsonJ R ≤ Subgroup.centralizer (VZ R Y : Set G)
  · intro y hy
    obtain ⟨n, hn, c, hc, rfl⟩ :=
      exists_mul_baum_of_thompsonJ_le hH.elem hH.V_le_T hH.YN hR hJ y hy
    exact W.mul_mem (hWB hn) (hWV hc)
  · let m : Main R Y L := ⟨hH, excA7CentralZero G L hexc, hJ⟩
    obtain ⟨M, _, φ, π, ρ, D⟩ := exists_modData_four B42A57.asB42A7Four_holds m
    exact coreW m D hWV hWB hWZ

theorem c123Two_holds :
    ∀ (G : Type) [Group G] [Finite G] (C₁ C₂ : Subgroup G → Subgroup G),
      IsGNChoice C₁ C₂ → C123TwoStatement C₁ C₂ :=
  fun _ _ _ _ _ hC => c123Two_of_isGNChoice hC

end Main

end CFSG.QuasithinUnique.L246.C123
