module

public import CFSG.Quasithin.H13.L32AC47o
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC47m

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.QuasithinUnique.Vol2Native.A312L.Seven

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K I : Subgroup G}

theorem exists_cube_of_comm_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hHeq : H = K ⊔ (l1 T L V ⊔ T))
    (hcomm : ∀ x ∈ l1 T L V, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (hIU : I ≤ conjClosure V H) [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))] :
    ∃ y : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure I H)), y ^ 3 = 1 ∧
      (∀ w, w * y w * y (y w) = 1) ∧ ∀ γ ∈ autIH (fsuV1 T V) I H K, γ * y = y * γ := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨x, hxL1, hx3, hfpf⟩ := exists_l1_fpf_F4 S.hyp hMod h1222 h1332 h1334
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hxl : x ∈ l1 T L V := hl1eq ▸ hxL1
  have hHL := H_le_N_l1_of_comm_F4 S h1332 hHeq hcomm
  have hθ := cube_mem_F4 h1222 h1332 h1334 S hF hHL hxl hx3 hfpf
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIHU : conjClosure I H ≤ conjClosure V H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIH := le_normalizer_conjClosure I H
  have hxH : x ∈ H := Setting147.l1H' S hxl
  set ψ := actH hF.H_le_normalizer_V₁ hIH with hψ
  refine ⟨ψ ⟨x, hxH⟩, ?_, ?_, ?_⟩
  · have h1 : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [← map_pow, h1, map_one]
  · intro w
    obtain ⟨a, haI, haw⟩ := exists_mk_of_mem_tilde w
    have hwa : w = modMk hIHN (a : G) haI := Subtype.ext haw.symm
    have h1 := (Subgroup.mem_normalizer_iff.mp (hIH hxH) _).mp haI
    have h2 := (Subgroup.mem_normalizer_iff.mp (hIH hxH) _).mp h1
    have hθa := hθ (a : G) (hIHU haI)
    rw [hwa, actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hxH⟩ haI,
      actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hxH⟩ h1]
    apply Subtype.ext
    show secMk _ _ ⟨(a : G), _⟩ * secMk _ _ ⟨x * a * x⁻¹, _⟩ *
      secMk _ _ ⟨x * (x * a * x⁻¹) * x⁻¹, _⟩ = 1
    rw [← map_mul, ← map_mul]
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
      (B := fsuV1 T V) (x := ⟨_, hIHN ((conjClosure I H).mul_mem
        ((conjClosure I H).mul_mem haI h1) h2)⟩)).mpr hθa
  · intro γ hγ
    rw [autIH_eq_map hF hKH] at hγ
    obtain ⟨k, hk, rfl⟩ := hγ
    have hc := hcomm x hxl k (Subgroup.mem_subgroupOf.mp hk)
    have h0 := hF.actH_eq_one_of_mem_pCoreOf hIU
      (x := ⟨x * (k : G) * x⁻¹ * (k : G)⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hxH k.2)
        (H.inv_mem hxH)) (H.inv_mem k.2)⟩) hc
    have e0 : (⟨x * (k : G) * x⁻¹ * (k : G)⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hxH k.2)
        (H.inv_mem hxH)) (H.inv_mem k.2)⟩ : ↥H) = ⟨x, hxH⟩ * k * ⟨x, hxH⟩⁻¹ * k⁻¹ := rfl
    have h1 : ψ (⟨x, hxH⟩ * k * ⟨x, hxH⟩⁻¹ * k⁻¹) = 1 := by
      rw [← e0]
      exact h0
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have e : ψ k * ψ ⟨x, hxH⟩ =
        (ψ ⟨x, hxH⟩ * ψ k * (ψ ⟨x, hxH⟩)⁻¹ * (ψ k)⁻¹)⁻¹ * (ψ ⟨x, hxH⟩ * ψ k) := by group
    rw [e, h1, inv_one, one_mul]

theorem false_of_d310Two_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hHeq : H = K ⊔ (l1 T L V ⊔ T)) (hP : IsPSL 3 2 1 (cStar K))
    (hcomm : ∀ x ∈ l1 T L V, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (hV₁I : fsuV1 T V ≤ I) (hIU : I ≤ conjClosure V H) (hirrT : IsIrrPlusTildeT hF hIU)
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]
    (h3 : D310Two (autIH (fsuV1 T V) I H T) (autIH (fsuV1 T V) I H K)
      (subM (fsuV1 T V) (conjClosure I H) I)) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hMp : autIH (fsuV1 T V) I H (conjClosure K T) = autIH (fsuV1 T V) I H K := by rw [hK₀]

  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := slThree_isSimple
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := ((cStarEquiv K).symm.trans φ).isSimpleGroup
  have hne : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e3⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  have hcard : Nat.card ↥(autIH (fsuV1 T V) I H K) = 168 := by
    rw [← Nat.card_congr e3.toEquiv, Nat.card_congr ((cStarEquiv K).symm.trans φ).toEquiv,
      card_sl32]
  have h8 := relIndex_eq_eight_of_d310Two h3 hcard
  obtain ⟨y, hy3, hcube, hyL⟩ := exists_cube_of_comm_F4 h1222 h1332 h1334 S hF hHeq hcomm hIU

  have hTK : T ≤ Subgroup.normalizer (K : Set G) := fun s hs =>
    Subgroup.mem_normalizer_fintype fun k' hk' => by
      have := mem_conjClosure hs hk'
      rwa [hK₀] at this
  have hTL : ∀ s ∈ autIH (fsuV1 T V) I H T, ∀ γ ∈ autIH (fsuV1 T V) I H K,
      s * γ * s⁻¹ ∈ autIH (fsuV1 T V) I H K := by
    intro s hs γ hγ
    rw [autIH_eq_map hF hTH] at hs
    rw [autIH_eq_map hF hKH] at hγ ⊢
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨k, hk, rfl⟩ := hγ
    refine ⟨t * k * t⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hTK (Subgroup.mem_subgroupOf.mp ht)) _).mp
      (Subgroup.mem_subgroupOf.mp hk)
  have hTL' : ∀ s ∈ autIH (fsuV1 T V) I H T, ∀ γ ∈ autIH (fsuV1 T V) I H K,
      s⁻¹ * γ * s ∈ autIH (fsuV1 T V) I H K := by
    intro s hs γ hγ
    have h1 := hTL s⁻¹ ((autIH (fsuV1 T V) I H T).inv_mem hs) γ hγ
    simpa using h1
  have hW : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure I H)), w * w = 1 := by
    intro w
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H))).2 w w.2
    simpa [pow_two] using this
  exact false_of_d310Two_of_cube hW hMp hirr'.1.2.2.2
    (autIH_le_stabSub_of hF hIU hV₁I hKH hKI') hTL hTL' h3 h8 hy3 hcube hyL

end CFSG.Quasithin.H13.L32A.C
