module

public import Certificates.Data.Kernel.Card7H3.CV
public import CFSG.Certificates.Kernel.PermCent.ForceCVSound
public import CFSG.GH74.GLS.C3.Prop121.Card7H3Inputs
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Certificates.Kernel.Card7H3

open CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Prop121.Card7.HC

section Transfer

variable {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]

@[expose] def mapC (φ : G →* H) (C : List (G × List G)) : List (H × List H) :=
  C.map fun c => (φ c.1, c.2.map φ)

theorem b0G_map (φ : G →* H) (hφ : Function.Injective φ) (HL : List G) (T : G) :
    b0G (HL.map φ) (φ T) = (b0G HL T).map φ := by
  simp only [b0G, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp_apply, ← map_mul, hφ.eq_iff]

theorem ilG_map (φ : G →* H) (hφ : Function.Injective φ) (B0 : List G) :
    ilG (B0.map φ) = (ilG B0).map φ := by
  simp only [ilG, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp_apply, ← map_mul, ne_eq, map_eq_one_iff φ hφ]

theorem ccG_map (φ : G →* H) (hφ : Function.Injective φ) (HL : List G) (σ ρ : G) :
    ccG (HL.map φ) (φ σ) (φ ρ) = ccG HL σ ρ := by
  simp only [ccG, List.countP_map]
  congr 1
  funext c
  simp only [Function.comp_apply, ← map_mul, hφ.eq_iff]

theorem clG_map (φ : G →* H) (hφ : Function.Injective φ) (HL : List G) (T : G) (IL : List G)
    (m : ℕ) : clG (HL.map φ) (φ T) (IL.map φ) m = (clG HL T IL m).map φ := by
  simp only [clG, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp_apply, ccG_map φ hφ]

theorem conj_map (φ : G →* H) (hφ : Function.Injective φ) (B0 : List G) (r b : G) :
    ((B0.map φ).any fun g => decide (g * φ r * g⁻¹ = φ b)) =
      B0.any fun g => decide (g * r * g⁻¹ = b) := by
  simp only [List.any_map, Function.comp_def, ← map_inv, ← map_mul, hφ.eq_iff]

theorem classesAuxG_map (φ : G →* H) (hφ : Function.Injective φ) (B0 : List G) :
    ∀ n L, classesAuxG (B0.map φ) n (L.map φ) = mapC φ (classesAuxG B0 n L)
  | 0, L => by simp [classesAuxG, mapC]
  | n + 1, [] => by simp [classesAuxG, mapC]
  | n + 1, r :: rest => by
    have e1 : ((r :: rest).map φ).filter (fun b => (B0.map φ).any fun g => decide (g * φ r * g⁻¹ = b)) =
        ((r :: rest).filter fun b => B0.any fun g => decide (g * r * g⁻¹ = b)).map φ := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro b _
      simp only [Function.comp_apply, conj_map φ hφ]
    have e2 : ((r :: rest).map φ).filter
        (fun b => !(B0.map φ).any fun g => decide (g * φ r * g⁻¹ = b)) =
        ((r :: rest).filter fun b => !B0.any fun g => decide (g * r * g⁻¹ = b)).map φ := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro b _
      simp only [Function.comp_apply, conj_map φ hφ]
    rw [List.map_cons] at e1 e2
    rw [List.map_cons, classesAuxG, classesAuxG, e1, e2, classesAuxG_map φ hφ B0 n, mapC, mapC,
      List.map_cons]

theorem zrG_map (φ : G →* H) (hφ : Function.Injective φ) (R : List (G × List G)) (b : G) :
    zrG (mapC φ R) (φ b) = zrG R b := by
  simp only [zrG, mapC, List.any_map, Function.comp_def, List.mem_map_of_injective hφ]

theorem yPowG_map (φ : G →* H) (hφ : Function.Injective φ) (Y g : G) :
    yPowG (φ Y) (φ g) = yPowG Y g := by
  simp only [yPowG, ← map_pow, hφ.eq_iff]

theorem product_map (φ : G →* H) (A B : List G) :
    (A.map φ) ×ˢ (B.map φ) = (A ×ˢ B).map (Prod.map φ φ) := by
  simp [SProd.sprod, List.product, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]

theorem pairCountG_map (φ : G →* H) (hφ : Function.Injective φ) (IL : List G) (Y : G)
    (R : List (G × List G)) : pairCountG (IL.map φ) (φ Y) (mapC φ R) = pairCountG IL Y R := by
  have h1 : (IL.map φ).filter (zrG (mapC φ R)) = (IL.filter (zrG R)).map φ := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro b _
    simp only [Function.comp_apply, zrG_map φ hφ]
  have h2 : (IL.map φ).filter (fun b => !zrG (mapC φ R) b) =
      (IL.filter fun b => !zrG R b).map φ := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro b _
    simp only [Function.comp_apply, zrG_map φ hφ]
  rw [pairCountG, pairCountG, h1, h2, product_map, List.countP_map]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, ← map_mul, yPowG_map φ hφ]

theorem classesCheckG_map (φ : G →* H) (hφ : Function.Injective φ) (B0 IL : List G)
    (C : List (G × List G)) (Y : G) :
    classesCheckG (B0.map φ) (IL.map φ) (mapC φ C) (φ Y) = classesCheckG B0 IL C Y := by
  simp only [classesCheckG, mapC, List.all_map, List.any_map, Function.comp_def,
    List.mem_map_of_injective hφ, ← map_inv, ← map_mul, hφ.eq_iff]

theorem powCheckG_map (φ : G →* H) (hφ : Function.Injective φ) (IL : List G) :
    powCheckG (IL.map φ) = powCheckG IL := by
  simp only [powCheckG, List.all_map, Function.comp_def, ← map_mul, ← map_pow,
    map_eq_one_iff φ hφ]

theorem ryCheckG_map (φ : G →* H) (hφ : Function.Injective φ) (IL : List G)
    (C : List (G × List G)) (L96 L48 : List G) (Y : G) :
    ryCheckG (IL.map φ) (mapC φ C) (L96.map φ) (L48.map φ) (φ Y) = ryCheckG IL C L96 L48 Y := by
  have hl : ∀ (L : List G) (R : List (G × List G)),
      ((L.map φ).filter (zrG (mapC φ R))).length = (L.filter (zrG R)).length := by
    intro L R
    rw [List.filter_map, List.length_map]
    congr 2
    funext b
    exact zrG_map φ hφ R b
  have hs : (mapC φ C).sublists = C.sublists.map (mapC φ) := List.sublists_map _ _
  rw [ryCheckG, ryCheckG, hs, List.all_map]
  congr 1
  funext R
  simp only [Function.comp_apply, hl, zrG_map φ hφ, pairCountG_map φ hφ]

end Transfer

theorem classesAux_eq : ∀ n L, classesAux n L = classesAuxG B0L n L
  | 0, _ => by simp [classesAux, classesAuxG]
  | n + 1, [] => by simp [classesAux, classesAuxG]
  | n + 1, r :: rest => by rw [classesAux, classesAuxG, classesAux_eq n]

theorem classesCheck_eq : classesCheck = classesCheckG B0L IL classes Y11 := rfl

theorem powCheck_eq : powCheck = powCheckG IL := rfl

theorem ryCheck_eq : ryCheck = ryCheckG IL classes cl96 cl48 Y11 := rfl

theorem B0L_eq : B0L = b0G HL T1 := rfl

theorem IL_eq : IL = ilG B0L := rfl

theorem cl96_eq : cl96 = clG HL T1 IL 96 := rfl

theorem cl48_eq : cl48 = clG HL T1 IL 48 := rfl

theorem T1_eq : T1 = evHom 11 (cOf t1P) := (ev_cOf t1P).symm

theorem Y11_eq : Y11 = evHom 11 (cOf Y11) := (ev_cOf Y11).symm

theorem evHom_injective : Function.Injective (evHom 11) := ev_injective

theorem s4L_sign : (s4L.all fun s => decide (Equiv.Perm.sign s = 1)) = true := by decide +kernel

theorem sign_eq (f s t : P11) (hs : Equiv.Perm.sign s = 1) :
    decide (Equiv.Perm.sign (f * s * t) = 1) =
      (decide (Equiv.Perm.sign f = 1) == decide (Equiv.Perm.sign t = 1)) := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, hs, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign f) with h | h <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign t) with h' | h' <;> simp [h, h']

theorem HL_eq : HL = hlC.map (evHom 11) := by
  have hs4 : ∀ s ∈ s4L, Equiv.Perm.sign s = 1 := by
    have := s4L_sign
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this
  rw [HL, H0, hlC, List.filter_flatMap, List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro f _
  rw [List.filter_flatMap, List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro s hs
  rw [List.filter_map, List.filter_map, List.map_map, List.map_map]
  congr 1
  · funext t
    simp only [Function.comp_apply, map_mul, evHom]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, ev_cOf]
  · apply List.filter_congr
    intro t _
    simp only [Function.comp_apply]
    exact sign_eq f s t (hs4 s hs)

theorem forceCls_eq {β : Sort _} :
    ∀ (l : List (CV 11 × List (CV 11))) (k : List (CV 11 × List (CV 11)) → β), forceCls l k = k l
  | [], _ => rfl
  | c :: l, k => by
    rw [forceCls, forceC_eq, forceCL_eq, forceCls_eq l]

theorem withLists_eq {β : Sort _}
    (k : List (CV 11) → List (CV 11) → List (CV 11) → List (CV 11 × List (CV 11)) → β) :
    withLists k = k hlC (b0G hlC (cOf t1P)) (ilG (b0G hlC (cOf t1P)))
      (classesAuxG (b0G hlC (cOf t1P)) 43 (ilG (b0G hlC (cOf t1P)))) := by
  rw [withLists, forceCL_eq, forceCL_eq, forceCL_eq, forceCls_eq]

theorem B0L_map : B0L = (b0G hlC (cOf t1P)).map (evHom 11) := by
  rw [B0L_eq, HL_eq, T1_eq, b0G_map _ evHom_injective]

theorem IL_map : IL = (ilG (b0G hlC (cOf t1P))).map (evHom 11) := by
  rw [IL_eq, B0L_map, ilG_map _ evHom_injective]

theorem classes_map : classes = mapC (evHom 11)
    (classesAuxG (b0G hlC (cOf t1P)) 43 (ilG (b0G hlC (cOf t1P)))) := by
  rw [classes, classesAux_eq, IL_map, B0L_map, classesAuxG_map _ evHom_injective]

theorem clF_eq (B0 IL : List (CV 11)) (m : ℕ) (HL : List (CV 11)) (T : CV 11)
    (hB : B0 = b0G HL T) : clG HL T IL m = clF B0 IL m := by
  rw [clG, clF, hB]
  apply List.filter_congr
  intro σ _
  rw [ccG, b0G, List.countP_filter]
  congr 2
  apply List.countP_congr
  intro c _
  rw [eq22C_eq]
  simp [and_comm]

theorem cl_map (m : ℕ) : clG HL T1 IL m =
    (clF (b0G hlC (cOf t1P)) (ilG (b0G hlC (cOf t1P))) m).map (evHom 11) := by
  rw [HL_eq, T1_eq, IL_map, clG_map _ evHom_injective, clF_eq _ _ _ _ _ rfl]

theorem classesCheck_of (h : k5082a = true) : classesCheck = true := by
  rw [k5082a, withLists_eq] at h
  rw [classesCheck_eq, classes_map, IL_map, B0L_map, Y11_eq, classesCheckG_map _ evHom_injective]
  exact h

theorem powCheck_of (h : k5082b = true) : powCheck = true := by
  rw [k5082b, withLists_eq] at h
  rw [powCheck_eq, IL_map, powCheckG_map _ evHom_injective]
  exact h

theorem ryCheck_of (h : k5082c = true) : ryCheck = true := by
  rw [k5082c, withLists_eq, forceCL_eq, forceCL_eq] at h
  rw [ryCheck_eq, cl96_eq, cl48_eq, cl_map, cl_map, classes_map, IL_map, Y11_eq,
    ryCheckG_map _ evHom_injective]
  exact h

end CFSG.Certificates.Kernel.Card7H3

end
