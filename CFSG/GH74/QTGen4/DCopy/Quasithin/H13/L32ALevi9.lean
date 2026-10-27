module

public import CFSG.Quasithin.H13.L32ALevi9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A702
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AM51d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Equiv Equiv.Perm
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem lemma14751Levi_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK) (h48 : Lemma14_7_48_F4) :
    Lemma14751Levi_F4 := by
  intro G _ _ T L V H S K hK hHKT hl1 hP π hsurj hker I hV₁I hIU hHI Y V₂ T₀ hV2 hYK _ _ _ _ _ _
    _ hcomm
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  obtain ⟨K', hcK', -, -⟩ := h48 G T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    have h1 := cComp_map_mulEquiv (MulAut.conj h) hK
    have e : H.map (MulAut.conj h).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
    rw [e, hcK'] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hpi1 : ∀ h : ↥H, π h = 1 ↔ (h : G) ∈ pCoreOf 2 H := fun h => by
    rw [← MonoidHom.mem_ker, hker, ← CFSG.Quasithin.A3.pCore_eq_openCore, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf]
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH) hHN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hOT : pCoreOf 2 H ≤ T := L32A.pCoreOf_le_of_le S.hyp hTH

  have hπK : (π.comp (Subgroup.inclusion hKH)).range = alternatingGroup (Fin 8) := by
    set φ := π.comp (Subgroup.inclusion hKH) with hφ
    have hkerφ : φ.ker = CFSG.pCore 2 ↥K := by
      ext k
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hpi1, ← pCoreOf_subgroupOf' K,
        Subgroup.mem_subgroupOf]
      exact mem_pCoreOf_iff_of_mem_cComp hK k.2
    have hcard : Nat.card φ.range = 20160 := by
      obtain ⟨ε⟩ := Lin.nonempty_mulEquiv_sl_of_isPSL hP
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hkerφ).toEquiv,
        ← Nat.card_congr (cStarEquiv K).toEquiv,
        Nat.card_congr (ε.trans Lin.slFourEquivAlt8).toEquiv, Alt8.card_alt8]
    have hnorm : ∀ g ∈ alternatingGroup (Fin 8), ∀ y ∈ φ.range, g * y * g⁻¹ ∈ φ.range := by
      rintro g - _ ⟨k, rfl⟩
      obtain ⟨h, rfl⟩ := hsurj g
      have hk' : (h : G) * k * (h : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hKn h.2) k).mp k.2
      refine ⟨⟨_, hk'⟩, ?_⟩
      show π (Subgroup.inclusion hKH ⟨_, hk'⟩) = π h * π (Subgroup.inclusion hKH k) * (π h)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext rfl)
    rcases Alt8.eq_bot_or_le hnorm with h | h
    · rw [h, Subgroup.card_bot] at hcard
      omega
    · exact (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, Alt8.card_alt8])).symm
  have hπKmem : ∀ k (hk : k ∈ K), π ⟨k, hKH hk⟩ ∈ alternatingGroup (Fin 8) := fun k hk => by
    rw [← hπK]
    exact ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨πK, hπs, hkerK, hD, hPar⟩ :=
    exists_coords51_F4 h1222 h1332 h1334 S hK hKn hl1 hP hsurj hker hπK

  have hcent : ∀ h ∈ H, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 K) → h ∈ pCoreOf 2 H := by
    intro h hh hc
    have hcomm' : π ⟨h, hh⟩ ∈ Subgroup.centralizer
        (alternatingGroup (Fin 8) : Set (Perm (Fin 8))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [← hπK] at hg
      obtain ⟨k, rfl⟩ := hg
      have h1 : π (⟨h, hh⟩ * Subgroup.inclusion hKH k * ⟨h, hh⟩⁻¹ *
          (Subgroup.inclusion hKH k)⁻¹) = 1 :=
        (hpi1 _).mpr (hOK (hc k k.2))
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
      (by simp), Subgroup.mem_bot] at hcomm'
    exact (hpi1 ⟨h, hh⟩).mp hcomm'

  have hodd : ∃ t ∈ T, ¬ ∃ k ∈ K, ∀ k' ∈ K,
      (k⁻¹ * t) * k' * (k⁻¹ * t)⁻¹ * k'⁻¹ ∈ pCoreOf 2 K := by
    obtain ⟨t₀, ht₀, hodd⟩ := exists_odd_T S hsurj
    refine ⟨t₀, ht₀, ?_⟩
    rintro ⟨k, hk, hkc⟩
    have hm : k⁻¹ * t₀ ∈ H := H.mul_mem (H.inv_mem (hKH hk)) (hTH ht₀)
    have h1 := (hpi1 ⟨_, hm⟩).mpr (hcent _ hm hkc)
    apply hodd
    have e : (⟨t₀, le_sup_right.trans S.hz.1.1 ht₀⟩ : ↥H) = ⟨k, hKH hk⟩ * ⟨_, hm⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul, h1, mul_one]
    exact hπKmem k hk

  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨z, a, c, hz, hz1, ha, haV, hc, hcV⟩ := S14.exists_basis_F4
  obtain ⟨x, hx, -, hxa, hxc⟩ := S14.exists_x_F4 hz hz1 ha haV hc hcV
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hxl : x ∈ l1 T L V := hl1eq ▸ hx
  have hF := hypF98_of_F4 h1222 h1332 h1334 hA37 hA38 hA39 S
  have hUab : IsElemAbelian 2 (conjClosure V H) := hF.F911_3
  have : IsMulCommutative ↥(conjClosure V H) := hUab.1
  have hVU : V ≤ conjClosure V H := le_conjClosure V H
  have hV₁V : fsuV1 T V ≤ V := inf_le_left
  have hHV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := S.hz.2.1
  have hTa : ∀ t ∈ T, t * a * t⁻¹ * a⁻¹ ∈ fsuV1 T V := by
    intro t ht
    have hta : t * a * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hV2.2.2.1 ht) a).mp ha
    rcases S14.mem_V2_F4 ha haV hta with h | h
    · exfalso
      apply haV
      exact (Subgroup.mem_normalizer_iff.mp (S14.T_V1_F4 ht) a).mpr h
    · have e : t * a * t⁻¹ * a⁻¹ = a * (t * a * t⁻¹) := by
        have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (S14.mul_self_V_F4 (hV2.2.1 ha))
        rw [ha1, S14.comm_V_F4 ((Subgroup.mem_normalizer_iff.mp (S14.TV_F4 ht) a).mp (hV2.2.1 ha))
          (hV2.2.1 ha)]
      rw [e]
      exact h
  have hca : c * a⁻¹ ∉ fsuV1 T V := by
    intro h
    apply hcV
    have := V₂.mul_mem (hV2.1 h) ha
    rwa [inv_mul_cancel_right] at this
  have hO : ∀ h ∈ pCoreOf 2 H, ∀ u ∈ conjClosure V H, h * u * h⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    intro h hh u hu
    rw [hF.toHypF91.pCoreOf_eq_centralizerMod] at hh
    exact (mem_centralizerMod.mp hh).2.2 u hu
  have C : Levi.HSide T L V H K (fsuV1 T V) πK a c x :=
    { hKH := hKH, hTH := hTH, hKn := hKn, hHN := hHN, hπs := hπs, hkerK := hkerK, hD := hD,
      hPar := hPar, hl1K := hl1, hdec := fun h hh => by
        rw [hHKT] at hh
        exact Levi.exists_mul_of_mem_sup (fun t ht => hKn (hTH ht)) hh
      hcent := hcent, hodd := hodd, hOK := hOK, hOT := hOT, hU := hUab,
      hV₁U := hV₁V.trans hVU, hHV₁ := hHV₁, hO := hO, ha := hVU (hV2.2.1 ha), haV₁ := haV,
      hTa := hTa, hx := hxl, hc := hVU hc, hxa := hxa, hxc := hxc, hca := hca }

  have hV₁V₂ : fsuV1 T V ≤ V₂ := hV2.1
  by_cases hfix : ∀ y ∈ Y, y * a * y⁻¹ * a⁻¹ ∈ fsuV1 T V
  · have hYV₂ : conjClosure V₂ Y = V₂ := by
      refine le_antisymm (conjClosure_le fun y hy v hv => ?_) (le_conjClosure V₂ Y)
      have hyH : y ∈ H := hKH (hYK hy)
      have hya : y * a * y⁻¹ ∈ V₂ := by
        have e : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
        rw [e]
        exact V₂.mul_mem (hV₁V₂ (hfix y hy)) ha
      rcases S14.mem_V2_F4 ha haV hv with h | h
      · exact hV₁V₂ ((Subgroup.mem_normalizer_iff.mp (hHV₁ hyH) v).mp h)
      · have e : y * v * y⁻¹ = (y * a * y⁻¹)⁻¹ * (y * (a * v) * y⁻¹) := by group
        rw [e]
        exact V₂.mul_mem (V₂.inv_mem hya)
          (hV₁V₂ ((Subgroup.mem_normalizer_iff.mp (hHV₁ hyH) _).mp h))
    rw [hYV₂]
    have h := relIndex_card_mul hV₁V₂
    rw [S14.card_V1_F4, hV2.2.2.2] at h
    omega
  push Not at hfix
  obtain ⟨y₀, hy₀, hya₀⟩ := hfix
  have hYI : ∀ y ∈ Y, y * a * y⁻¹ * a⁻¹ ∈ I := by
    intro y hy
    have h1 := hcomm (Subgroup.commutator_mem_commutator ha hy)
    rw [commutatorElement_def] at h1
    have e : y * a * y⁻¹ * a⁻¹ = (a * y * a⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact I.inv_mem h1
  have hinf := Setting147.inf_V_eq_F4 S h1222 h1332 h1334 hV₁I hIU hHI
  have hxI : c * a⁻¹ ∉ I := fun h => hca (by
    rw [← hinf]
    exact ⟨V.mul_mem hc (V.inv_mem (hV2.2.1 ha)), h⟩)
  have hYP := Levi.HSide.le_stab_of_r2 (C.U_le_map le_sup_right)
    (C.r2_notMem hYK hHI hV₁I hYI hxI)
  have hbad := C.cent_le_T hYK hYP ⟨y₀, hy₀, hya₀⟩
  have hM := C.hyp hbad

  obtain ⟨B, hBR, hQ⟩ := hF.F916_3_aux
  obtain ⟨hBH, hBab, hBO, hBq, hBidx⟩ := hQ
  rw [hl1eq] at hBR
  exact (C.false_of_offender hM hBR hBH hBab hBO hBq hBidx
    (L32A.pCoreOf_le_of_le S.hyp le_sup_right)).elim

end CFSG.Quasithin.H13.L32A.C
