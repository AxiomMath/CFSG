module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Beta
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Y

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem mem_normalizer_X' {c : G}
    (hc : c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :
    c ∈ Subgroup.normalizer (conjSub g (piGen π) : Set G) := by
  have hN := S.normal_cent
  have key : ∀ d ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G),
      ∀ x ∈ conjSub g (piGen π), d * x * d⁻¹ ∈ conjSub g (piGen π) := by
    intro d hd x hx
    have h1 : (⟨x, S.le_cent hx⟩ : ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set G))) ∈
        (conjSub g (piGen π)).subgroupOf (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) := hx
    exact hN.conj_mem _ h1 ⟨d, hd⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key c hc x
  · intro hx
    have := key c⁻¹ (inv_mem hc) _ hx
    simpa [mul_assoc] using this

theorem fam_conj_of_cent' {c : G} (hc : c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G))
    {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) :
    conjSub c L ∈ fam K (conjSub g (piGen π)) := by
  have hQ := S.Q_eq_pi
  have hL0 : conjSub g⁻¹ L ∈ π := by rw [← hQ]; exact ⟨L, hL, rfl⟩
  have hc0 : g⁻¹ * c * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have := hc
    calc g⁻¹ * c * g * z = g⁻¹ * (c * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * c) * g := by rw [this]
      _ = z * (g⁻¹ * c * g) := by group
  have h1 := S.conj_pi_of_cent hc0 hL0
  rw [← hQ] at h1
  obtain ⟨M, hM, hMe⟩ := h1
  have : conjSub c L = M := by
    have e : conjSub c L = conjSub g (conjSub (g⁻¹ * c * g) (conjSub g⁻¹ L)) := by
      have e' : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
      rw [← conjSub_mul, ← conjSub_mul, e']
    rw [e, ← hMe, conjSub_conjSub_inv]
  rw [this]; exact hM

theorem center_X_trivial {n : ℕ} (hn : 5 ≤ n) (J : AEIdent (fam K (conjSub g (piGen π))) n)
    (hker : J.φ.ker = ⊥) {x : G} (hx : x ∈ piGen π) (hc : ∀ w ∈ piGen π, x * w = w * x) :
    x = 1 := by
  have hx' : g * x * g⁻¹ ∈ conjSub g (piGen π) := conj_mem_conjSub hx
  have hx'' : g * x * g⁻¹ ∈ pSpan (fam K (conjSub g (piGen π))) := by rw [S.fam_gen]; exact hx'
  have hZ : Subgroup.center ↥J.φ.range = ⊥ := by
    have := center_eq_bot_of_eq J.range_eq (center_Hn hn)
    exact this
  have hmem : J.φ.rangeRestrict ⟨g * x * g⁻¹, hx''⟩ ∈ Subgroup.center ↥J.φ.range := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨u, rfl⟩ := J.φ.rangeRestrict_surjective r
    apply Subtype.ext
    simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (u : G) * (g * x * g⁻¹) = g * x * g⁻¹ * u
    have hu : g⁻¹ * (u : G) * g ∈ piGen π := by
      have : (u : G) ∈ conjSub g (piGen π) := (SetLike.ext_iff.mp S.fam_gen (u : G)).mp u.2
      have := mem_conjSub_iff.mp this
      simpa using this
    have := hc _ hu
    calc (u : G) * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [← this]
      _ = _ := by group
  rw [hZ, Subgroup.mem_bot] at hmem
  have h1 : (⟨g * x * g⁻¹, hx''⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) ∈ J.φ.ker := by
    rw [MonoidHom.mem_ker]
    have := congrArg Subtype.val hmem
    simpa using this
  rw [hker, Subgroup.mem_bot] at h1
  have := congrArg Subtype.val h1
  simpa using this

theorem y_comm_cent {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (hAut : TwinThinPf8.AEAut n)
    (hC : TwinThinPf8.AEChar n) (J : AEIdent (fam K (conjSub g (piGen π))) n)
    (hker : J.φ.ker = ⊥) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {y : ↥(pSpan (fam K (conjSub g (piGen π))))} (hyφ : J.φ y = AE.yBar α h)
    (hyN : (y : G) ∈ Subgroup.normalizer (piGen π : Set G)) :
    ∀ c ∈ piGen π, c * (g * z * g⁻¹) = (g * z * g⁻¹) * c → (y : G) * c = c * (y : G) := by
  intro c hc hcz
  have hcC' : c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcz
  have hcN := S.mem_normalizer_X' hcC'
  have hcz0 : c ∈ Subgroup.centralizer ({z} : Set G) := S.X_le_cent hc
  have hcN' : c ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G) := by rw [S.fam_gen]; exact hcN
  have hZ : Subgroup.center ↥J.φ.range = ⊥ := center_eq_bot_of_eq J.range_eq (center_Hn hn)
  have hk' : ∀ x : ↥(pSpan (fam K (conjSub g (piGen π)))), x ∈ J.φ.ker → TwinThinPf.conjOn _ c hcN' x ∈ J.φ.ker :=
    fun x hx => TwinThinPf.ker_invariant J.φ hcN' J.ker_le hZ hx
  let σ := TwinThinPf.induced J.φ hcN' hk'
  have hperm : TwinThinPf8.PermMembers J.φ.range σ := by
    intro β hβ cb
    obtain ⟨M, hM, hMlab⟩ := J.label_surj β hβ cb
    have hM' : conjSub c M ∈ (fam K (conjSub g (piGen π))) := S.fam_conj_of_cent' hcC' hM
    obtain ⟨β', hβ', cb', hlab'⟩ := J.label _ hM'
    refine ⟨β', hβ', cb', fun x hx => ?_⟩
    have hx' : (x : AE.AEQ n) ∈ (M.subgroupOf _).map J.φ := by rw [hMlab]; exact hx
    obtain ⟨m, hm, hmx⟩ := J.exists_of_mem_map hM hx'
    have hxe : x = J.φ.rangeRestrict ⟨m, le_pSpan hM hm⟩ := Subtype.ext hmx.symm
    rw [hxe, TwinThinPf.induced_apply, ← hlab']
    exact ⟨TwinThinPf.conjOn _ c hcN' ⟨m, le_pSpan hM hm⟩,
      Subgroup.mem_subgroupOf.mpr (by rw [TwinThinPf.conjOn_apply]; exact conj_mem_conjSub hm), rfl⟩
  have hsurj : Function.Surjective σ := by
    intro r
    obtain ⟨u, rfl⟩ := J.φ.rangeRestrict_surjective r
    have hcN2 : c⁻¹ ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G) := inv_mem hcN'
    refine ⟨J.φ.rangeRestrict (TwinThinPf.conjOn _ c⁻¹ hcN2 u), ?_⟩
    rw [TwinThinPf.induced_apply]
    congr 1
    apply Subtype.ext
    simp [TwinThinPf.conjOn_apply, mul_assoc]
  have hbij : Function.Bijective σ := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  obtain ⟨w, hw⟩ := hAut J.φ.range J.range_eq σ hbij hperm
  have hconj : ∀ u : ↥(pSpan (fam K (conjSub g (piGen π)))), J.φ (TwinThinPf.conjOn _ c hcN' u) =
      AE.mkQ n w * J.φ u * (AE.mkQ n w)⁻¹ := by
    intro u
    have := hw (J.φ.rangeRestrict u)
    rw [TwinThinPf.induced_apply] at this
    exact this
  have hz : AE.mkQ n w * AE.zBar α h * (AE.mkQ n w)⁻¹ = AE.zBar α h := by
    have e1 := J.map_eq_zBar hn S.mem_fam_self (S.card8 K S.hK) hlab S.hz
    have e2 := hconj ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩
    have e3 : TwinThinPf.conjOn _ c hcN' ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ =
        ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ := Subtype.ext (by
      show c * z * c⁻¹ = z
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hcz0)
    rw [e3, e1] at e2
    exact e2.symm
  obtain ⟨L₁, L₂, hL₁, hL₂, hL₁c, hL₂c, hl₁, hl₂⟩ : ∃ L₁ L₂ : Subgroup G, L₁ ∈ (fam K (conjSub g (piGen π))) ∧ L₂ ∈ (fam K (conjSub g (piGen π))) ∧
      L₁ ≤ Subgroup.centralizer (piGen π : Set G) ∧ L₂ ≤ Subgroup.centralizer (piGen π : Set G) ∧
      (L₁.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h true ∧
      (L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h false := by
    have hKK' := S.pair_le_cent
    have hlab' := S.map_twin_eq hn hn8 J hlab
    cases b
    · exact ⟨K', K, S.twin_mem_fam, S.mem_fam_self, hKK'.2, hKK'.1, hlab', hlab⟩
    · exact ⟨K, K', S.mem_fam_self, S.twin_mem_fam, hKK'.1, hKK'.2, hlab, hlab'⟩
  have hfix : ∀ (L : Subgroup G) (hL : L ∈ (fam K (conjSub g (piGen π)))), L ≤ Subgroup.centralizer (piGen π : Set G) →
      ∀ m ∈ (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ, AE.mkQ n w * m * (AE.mkQ n w)⁻¹ = m := by
    intro L hL hLc m hm
    obtain ⟨l, hl, rfl⟩ := J.exists_of_mem_map hL hm
    have h1 := hconj ⟨l, le_pSpan hL hl⟩
    have hcl : TwinThinPf.conjOn _ c hcN' ⟨l, le_pSpan hL hl⟩ = ⟨l, le_pSpan hL hl⟩ :=
      Subtype.ext (by
        show c * l * c⁻¹ = l
        rw [mul_inv_eq_iff_eq_mul]
        exact (Subgroup.mem_centralizer_iff.mp (hLc hl)) c hc)
    rw [hcl] at h1
    exact h1.symm
  obtain ⟨k₁, hk₁, k₂, hk₂, hyk⟩ := TwinThinPf8.exists_conj_yBar hn hC α h (AE.mkQ n w) hz
    (fun m hm => hfix L₁ hL₁ hL₁c m (by rw [hl₁]; exact hm))
  have hk₁' : k₁ ∈ (L₁.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ := by rw [hl₁]; exact hk₁
  have hk₂' : k₂ ∈ (L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ := by rw [hl₂]; exact hk₂
  obtain ⟨l₁, hl₁m, hl₁e⟩ := J.exists_of_mem_map hL₁ hk₁'
  obtain ⟨l₂, hl₂m, hl₂e⟩ := J.exists_of_mem_map hL₂ hk₂'
  have hinj : Function.Injective J.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hyE : TwinThinPf.conjOn _ c hcN' y =
      ⟨l₁, le_pSpan hL₁ hl₁m⟩ * ⟨l₂, le_pSpan hL₂ hl₂m⟩ * y := by
    apply hinj
    rw [hconj, map_mul, map_mul, hl₁e, hl₂e, hyφ]
    exact hyk
  have hval : c * (y : G) * c⁻¹ = l₁ * l₂ * (y : G) := congrArg Subtype.val hyE
  have ht : l₁ * l₂ ∈ piGen π := by
    have e : l₁ * l₂ = c * ((y : G) * c⁻¹ * (y : G)⁻¹) := by
      calc l₁ * l₂ = (l₁ * l₂ * (y : G)) * (y : G)⁻¹ := by group
        _ = (c * (y : G) * c⁻¹) * (y : G)⁻¹ := by rw [hval]
        _ = _ := by group
    rw [e]
    exact mul_mem hc (TwinThinPf.conj_mem_of_normalizer hyN (inv_mem hc))
  have hcomm : ∀ w' ∈ piGen π, l₁ * l₂ * w' = w' * (l₁ * l₂) := by
    intro w' hw'
    have e1 := (Subgroup.mem_centralizer_iff.mp (hL₁c hl₁m)) w' hw'
    have e2 := (Subgroup.mem_centralizer_iff.mp (hL₂c hl₂m)) w' hw'
    calc l₁ * l₂ * w' = l₁ * (l₂ * w') := by group
      _ = l₁ * (w' * l₂) := by rw [← e2]
      _ = (l₁ * w') * l₂ := by group
      _ = (w' * l₁) * l₂ := by rw [← e1]
      _ = _ := by group
  have h1 := S.center_X_trivial hn J hker ht hcomm
  rw [h1, one_mul] at hval
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
