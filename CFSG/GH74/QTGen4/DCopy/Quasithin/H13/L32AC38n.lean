module

public import CFSG.Quasithin.H13.L32AC38n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC38d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem false_of_perm_five_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H))
    {K₁ : Subgroup (MulAut (IntMod C.Wt C.hUe))} (hrK : C.ψ.range = K₁)
    {π₀ : Equiv.Perm (Fin 5) →* ↥K₁}
    (hπ : (FFModel.symDn 5).RealizesVia K₁ ⊤ ⊥ π₀) : False := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨-, a, -, -, -, ha, haV, -, -⟩ := S14.exists_basis_F4
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf_F4 C.S.hyp hMod h1222 h1332 h1334
  have hxH := C.l1_le_H hxL
  have hπ₀i : Function.Injective π₀ :=
    FFModel.RealizesVia.injective_of_faithful (G64.symDn_faithful (by norm_num)) hπ
  obtain ⟨φ, hφs, -, hφψ⟩ := C.exists_perm_hom hW hrK hπ₀i hπ.1
  obtain ⟨E₀, hE₀⟩ := G64.RealizesVia.exists_secEquiv (C124.YZ.natKer_odd (by decide)) hπ
  let E : IntMod C.Wt C.hUe ≃* ↥(G6.coreMod 5) := E₀
  have hE : ∀ (γ : Equiv.Perm (Fin 5)) (v : IntMod C.Wt C.hUe),
      ((E (((π₀ γ : ↥K₁) : MulAut (IntMod C.Wt C.hUe)) v) : ↥(G6.coreMod 5)) : G6.PermMod 5) =
        G6.permAct 5 γ ((E v : ↥(G6.coreMod 5)) : G6.PermMod 5) := hE₀
  set N := Subgroup.normalizer (fsuV1 T V : Set G) with hN
  have haU : a ∈ conjClosure V H := le_conjClosure V H (hV2.2.1 ha)
  set w₀ : IntMod C.Wt C.hUe := IntMod.mk C.hUe ⟨_, C.tilde_mem_Wt hW haU⟩ with hw₀
  have hw₀v : w₀.val = secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩ := rfl
  set m₀ : G6.PermMod 5 := (E w₀).1 with hm₀

  have hTfix : ∀ t : G, ∀ ht : t ∈ T, C.ψ ⟨t, C.T_le_H ht⟩ w₀ = w₀ := by
    intro t ht
    have htN := C.HN (C.T_le_H ht)
    have hta : t * a * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hV2.2.2.1 ht) a).mp ha
    have htaN : t * a * t⁻¹ ∈ N := C.VN (hV2.2.1 hta)
    have hcases := S14.mem_V2_F4 ha haV hta
    have hat : secMk N (fsuV1 T V) ⟨t * a * t⁻¹, htaN⟩ =
        secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩ := by
      rcases hcases with h | h
      · exfalso
        apply haV
        have := (Subgroup.mem_normalizer_iff.mp (S14.T_V1_F4 (inv_mem ht)) _).mp h
        simpa [mul_assoc] using this
      · have h1 : secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩ *
            secMk N (fsuV1 T V) ⟨t * a * t⁻¹, htaN⟩ = 1 := by
          rw [← map_mul]
          exact secMk_eq_one_iff.mpr h
        have h2 : secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩ *
            secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩ = 1 := by
          rw [← map_mul]
          exact secMk_eq_one_iff.mpr (by
            show a * a ∈ fsuV1 T V
            rw [S14.mul_self_V_F4 (hV2.2.1 ha)]
            exact one_mem _)
        calc secMk N (fsuV1 T V) ⟨t * a * t⁻¹, htaN⟩
            = (secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩ *
                secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩) *
                  secMk N (fsuV1 T V) ⟨t * a * t⁻¹, htaN⟩ := by rw [h2, one_mul]
          _ = secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩ *
                (secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩ *
                  secMk N (fsuV1 T V) ⟨t * a * t⁻¹, htaN⟩) := mul_assoc _ _ _
          _ = secMk N (fsuV1 T V) ⟨a, C.HN (C.UH haU)⟩ := by rw [h1, mul_one]
    apply IntMod.val_injective
    rw [C.ψ_apply_val, hw₀v, ← map_inv, ← map_mul, ← map_mul, ← hat]
    rfl

  have hφT : ∀ t : G, ∀ ht : t ∈ T, G6.permAct 5 (φ ⟨t, C.T_le_H ht⟩) m₀ = m₀ := by
    intro t ht
    rw [hm₀, ← hE, hφψ, hTfix t ht]

  have hTsyl : IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo C.S.hyp.fsu.sylow C.T_le_H
  have hS2 : IsPGroup 2 ↥(T.subgroupOf H) :=
    hTsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe C.T_le_H).symm
  obtain ⟨g, hg⟩ := exists_conj_map_eq_of_sylow φ hφs hS2 hTsyl.2.2 T05_isPGroup T05_index
  set m₁ := G6.permAct 5 g⁻¹ m₀ with hm₁
  have hc5 : G6.permAct 5 c5 m₁ = m₁ := by
    have hmem : c5 ∈ ((T.subgroupOf H).map φ).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hg]
      exact c5_mem_T05
    obtain ⟨p, ⟨t, ht, rfl⟩, hpc⟩ := hmem
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have e : c5 = g⁻¹ * φ t * g := by
      rw [← hpc]
      simp
    have ht' : φ t = φ ⟨(t : G), C.T_le_H htT⟩ := rfl
    rw [e, hm₁, permAct_conj_apply, ht', hφT _ htT]

  have hm₁c : m₁ ∈ G6.coreMod 5 := G6.permAct_mem_coreMod g⁻¹ (E w₀).2
  have hw₀1 : w₀ ≠ 1 := by
    intro h
    have h1 := congrArg IntMod.val h
    rw [hw₀v, IntMod.val_one] at h1
    exact haV (secMk_eq_one_iff.mp h1)
  have hm₁1 : m₁ ≠ 1 := by
    intro h
    apply hw₀1
    have h1 : m₀ = 1 := by
      have := congrArg (G6.permAct 5 g) h
      rwa [hm₁, permAct_apply_inv, map_one] at this
    have h2 : E w₀ = 1 := Subtype.ext h1
    exact (MulEquiv.map_eq_one_iff E).mp h2
  have hm₁e : m₁ = e0123 :=
    (fix_c5 m₁ hc5 (G6.mem_coreMod.mp hm₁c)).resolve_left hm₁1

  set y := g⁻¹ * φ ⟨x, hxH⟩ * g with hy
  have hx3' : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hy3 : y ^ 3 = 1 := by
    rw [hy, show g⁻¹ * φ ⟨x, hxH⟩ * g = MulAut.conj g⁻¹ (φ ⟨x, hxH⟩) by
      simp, ← map_pow, ← map_pow, hx3', map_one, map_one]

  let f : IntMod C.Wt C.hUe → G6.PermMod 5 := fun u => G6.permAct 5 g⁻¹ (E u).1
  have hf_inj : Function.Injective f := by
    intro u v huv
    have h1 : (E u).1 = (E v).1 := (G6.permAct 5 g⁻¹).injective huv
    exact E.injective (Subtype.ext h1)
  have hf_mul : ∀ u v, f (u * v) = f u * f v := fun u v => by
    show G6.permAct 5 g⁻¹ (E (u * v)).1 = G6.permAct 5 g⁻¹ (E u).1 * G6.permAct 5 g⁻¹ (E v).1
    rw [map_mul, Subgroup.coe_mul, map_mul]
  have hf_one : f 1 = 1 := by
    show G6.permAct 5 g⁻¹ (E 1).1 = 1
    rw [map_one, OneMemClass.coe_one, map_one]
  have hf_x : ∀ u, f (C.ψ ⟨x, hxH⟩ u) = G6.permAct 5 y (f u) := fun u => by
    show G6.permAct 5 g⁻¹ (E (C.ψ ⟨x, hxH⟩ u)).1 = G6.permAct 5 y (G6.permAct 5 g⁻¹ (E u).1)
    rw [← hφψ, hE, hy, permAct_conj_apply]
  have hf_w : f w₀ = e0123 := hm₁e

  have hy1 : G6.permAct 5 y e0123 ≠ e0123 := by
    intro h
    have h1 : f (C.ψ ⟨x, hxH⟩ w₀) = f w₀ := by rw [hf_x, hf_w, h]
    have h2 := hf_inj h1
    have h3 := congrArg IntMod.val h2
    rw [C.ψ_apply_val, hw₀v] at h3
    exact hw₀1 (by
      have := fix_eq_one (C.HN hxH) hfpf (secMk_mem_secImg (hV2.2.1 ha)) h3
      exact IntMod.val_injective (by rw [hw₀v, IntMod.val_one]; exact this))

  set u₁ := C.ψ ⟨x, hxH⟩ w₀ with hu₁
  have hmap : ([1, w₀, u₁, w₀ * u₁, C.ψ ⟨x, hxH⟩ (w₀ * u₁)].map f).Nodup := by
    have := nodup_five y hy3 hy1
    simp only [List.map_cons, List.map_nil, hf_one, hf_w, hu₁, hf_mul, hf_x]
    simpa [hf_w] using this
  have hnd := (List.Nodup.of_map f hmap).map IntMod.val_injective
  have hxN : x ∈ N := C.HN hxH
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := by
    obtain ⟨-, -, hLTV, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
    exact le_sup_left.trans hLTV ((oTwoRes_le _ hxL).1)
  have hxVt := mem_normalizer_tildeV hxN hxV
  have hψV : ∀ u : IntMod C.Wt C.hUe, u.val ∈ tildeOf (fsuV1 T V) V →
      (C.ψ ⟨x, hxH⟩ u).val ∈ tildeOf (fsuV1 T V) V := by
    intro u hu
    rw [C.ψ_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp hxVt _).mp hu
  have hw₀V : w₀.val ∈ tildeOf (fsuV1 T V) V := by
    rw [hw₀v]
    exact secMk_mem_secImg (hV2.2.1 ha)
  have hle := length_le_card_of_nodup hnd (A := tildeOf (fsuV1 T V) V) (by
    intro v hv
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [IntMod.val_one]; exact one_mem _
    · exact hw₀V
    · exact hψV _ hw₀V
    · rw [IntMod.val_mul]; exact mul_mem hw₀V (hψV _ hw₀V)
    · refine hψV _ ?_
      rw [IntMod.val_mul]; exact mul_mem hw₀V (hψV _ hw₀V))
  rw [C.card_tildeV_F4 h1332 h1334] at hle
  simp at hle

end Ctx38

end CFSG.Quasithin.H13.L32A.C
