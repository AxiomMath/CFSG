module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Cent

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

@[expose] def Wsub (K K' : Subgroup G) (y : G) : Subgroup G :=
  Subgroup.closure ((K : Set G) ∪ (K' : Set G) ∪ {y})

theorem le_Wsub_K (y : G) : K ≤ Wsub K K' y :=
  fun x hx => Subgroup.subset_closure (Or.inl (Or.inl hx))

theorem le_Wsub_K' (y : G) : K' ≤ Wsub K K' y :=
  fun x hx => Subgroup.subset_closure (Or.inl (Or.inr hx))

theorem y_mem_Wsub (y : G) : y ∈ Wsub K K' y :=
  Subgroup.subset_closure (Or.inr rfl)

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem exists_conj_hom {n : ℕ} (hn : 5 ≤ n) (hAut : TwinThinPf8.AEAut n)
    (J : AEIdent (fam K (conjSub g (piGen π))) n) {c : G}
    (hcC' : c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :
    ∃ w : AE.Wr n, ∀ (u : ↥(pSpan (fam K (conjSub g (piGen π))))) (hcN' : c ∈ Subgroup.normalizer
      (pSpan (fam K (conjSub g (piGen π))) : Set G)),
      J.φ (TwinThinPf.conjOn _ c hcN' u) = AE.mkQ n w * J.φ u * (AE.mkQ n w)⁻¹ := by
  have hcN := S.mem_normalizer_X' hcC'
  have hcN' : c ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G) := by
    rw [S.fam_gen]; exact hcN
  have hZ : Subgroup.center ↥J.φ.range = ⊥ := center_eq_bot_of_eq J.range_eq (center_Hn hn)
  have hk' : ∀ x : ↥(pSpan (fam K (conjSub g (piGen π)))), x ∈ J.φ.ker →
      TwinThinPf.conjOn _ c hcN' x ∈ J.φ.ker :=
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
    have hcN2 : c⁻¹ ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G) :=
      inv_mem hcN'
    refine ⟨J.φ.rangeRestrict (TwinThinPf.conjOn _ c⁻¹ hcN2 u), ?_⟩
    rw [TwinThinPf.induced_apply]
    congr 1
    apply Subtype.ext
    simp [TwinThinPf.conjOn_apply, mul_assoc]
  have hbij : Function.Bijective σ := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  obtain ⟨w, hw⟩ := hAut J.φ.range J.range_eq σ hbij hperm
  refine ⟨w, fun u hcN'' => ?_⟩
  have := hw (J.φ.rangeRestrict u)
  rw [TwinThinPf.induced_apply] at this
  exact this

theorem eq_of_z_mem {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) n) {α : Finset (Fin n)} {h : α.card = 4}
    {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) (hzL : z ∈ L) : L = K ∨ L = K' := by
  obtain ⟨β, hβ, c'', hlab''⟩ := J.label _ hL
  have hzφ := J.mem_map hL hzL
  rw [hlab''] at hzφ
  have e1 := J.map_eq_zBar hn S.mem_fam_self (S.card8 K S.hK) hlab S.hz
  have e1' : J.φ ⟨z, le_pSpan hL hzL⟩ = AE.zBar α h := e1
  rw [e1'] at hzφ
  have hsq : AE.zBar α h * AE.zBar α h = 1 := AE.zBar_mul_self α h
  have hαβ : α = β := by
    rcases AE.eq_of_mem_memBar_mul_self hn hzφ hsq with h1 | h1
    · exact absurd h1 (AE.zBar_ne_one hn α h)
    · exact AE.eq_of_zBar_eq hn8 h1
  subst hαβ
  by_cases hcb : c'' = b
  · subst hcb
    left
    exact S.eq_of_map_le hn J hL S.mem_fam_self (le_of_eq (hlab''.trans hlab.symm))
  · right
    have hc2 : c'' = !b := by cases c'' <;> cases b <;> simp_all
    subst hc2
    have hlab' := S.map_twin_eq hn hn8 J hlab
    exact S.eq_of_map_le hn J hL S.twin_mem_fam (le_of_eq (hlab''.trans hlab'.symm))

theorem conj_K_mem {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) n) {α : Finset (Fin n)} {h : α.card = 4}
    {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {c : G} (hcz : c ∈ Subgroup.centralizer ({z} : Set G))
    (hcC' : c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) {L : Subgroup G}
    (hL : L = K ∨ L = K') : conjSub c L = K ∨ conjSub c L = K' := by
  have hcz1 : c * z * c⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hLf : L ∈ fam K (conjSub g (piGen π)) := by
    rcases hL with rfl | rfl
    · exact S.mem_fam_self
    · exact S.twin_mem_fam
  have hzL : z ∈ L := by
    rcases hL with rfl | rfl
    · exact S.hz.mem
    · obtain ⟨-, z', hz'K, hz'K'⟩ := S.hK'
      have : z' = z := (S.hz.eq hz'K).symm
      rw [this] at hz'K'
      exact hz'K'.mem
  have hzc : z ∈ conjSub c L := by
    have := conj_mem_conjSub (n := c) hzL
    rwa [hcz1] at this
  exact S.eq_of_z_mem hn hn8 J hlab (S.fam_conj_of_cent' hcC' hLf) hzc

theorem conj_y_mem {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (hAut : TwinThinPf8.AEAut n)
    (hC : TwinThinPf8.AEChar n) (J : AEIdent (fam K (conjSub g (piGen π))) n)
    (hker : J.φ.ker = ⊥) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {y : ↥(pSpan (fam K (conjSub g (piGen π))))} (hyφ : J.φ y = AE.yBar α h) {c : G}
    (hcz : c ∈ Subgroup.centralizer ({z} : Set G))
    (hcC' : c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :
    c * (y : G) * c⁻¹ ∈ Wsub K K' (y : G) := by
  have hcN := S.mem_normalizer_X' hcC'
  have hcN' : c ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G) := by
    rw [S.fam_gen]; exact hcN
  obtain ⟨w, hw⟩ := S.exists_conj_hom hn hAut J hcC'
  have hconj : ∀ u : ↥(pSpan (fam K (conjSub g (piGen π)))),
      J.φ (TwinThinPf.conjOn _ c hcN' u) = AE.mkQ n w * J.φ u * (AE.mkQ n w)⁻¹ :=
    fun u => hw u hcN'
  have hz : AE.mkQ n w * AE.zBar α h * (AE.mkQ n w)⁻¹ = AE.zBar α h := by
    have e1 := J.map_eq_zBar hn S.mem_fam_self (S.card8 K S.hK) hlab S.hz
    have e2 := hconj ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩
    have e3 : TwinThinPf.conjOn _ c hcN' ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ =
        ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ := Subtype.ext (by
      show c * z * c⁻¹ = z
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hcz)
    rw [e3, e1] at e2
    exact e2.symm
  obtain ⟨k₁, hk₁, k₂, hk₂, j, hyk⟩ := hC α h (AE.mkQ n w) hz
  obtain ⟨L₁, L₂, hL₁, hL₂, hL₁W, hL₂W, hl₁, hl₂⟩ : ∃ L₁ L₂ : Subgroup G,
      L₁ ∈ fam K (conjSub g (piGen π)) ∧ L₂ ∈ fam K (conjSub g (piGen π)) ∧
      L₁ ≤ Wsub K K' (y : G) ∧ L₂ ≤ Wsub K K' (y : G) ∧
      (L₁.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h true ∧
      (L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h false := by
    have hlab' := S.map_twin_eq hn hn8 J hlab
    cases b
    · exact ⟨K', K, S.twin_mem_fam, S.mem_fam_self, le_Wsub_K' (K := K) (K' := K') _, le_Wsub_K (K := K) (K' := K') _, hlab', hlab⟩
    · exact ⟨K, K', S.mem_fam_self, S.twin_mem_fam, le_Wsub_K (K := K) (K' := K') _, le_Wsub_K' (K := K) (K' := K') _, hlab, hlab'⟩
  have hk₁' : k₁ ∈ (L₁.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ := by
    rw [hl₁]; exact hk₁
  have hk₂' : k₂ ∈ (L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ := by
    rw [hl₂]; exact hk₂
  obtain ⟨l₁, hl₁m, hl₁e⟩ := J.exists_of_mem_map hL₁ hk₁'
  obtain ⟨l₂, hl₂m, hl₂e⟩ := J.exists_of_mem_map hL₂ hk₂'
  have hinj : Function.Injective J.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hyE : TwinThinPf.conjOn _ c hcN' y =
      ⟨l₁, le_pSpan hL₁ hl₁m⟩ * ⟨l₂, le_pSpan hL₂ hl₂m⟩ * y ^ j := by
    apply hinj
    rw [hconj, map_mul, map_mul, map_pow, hl₁e, hl₂e, hyφ]
    exact hyk
  have hval : c * (y : G) * c⁻¹ = l₁ * l₂ * (y : G) ^ j := congrArg Subtype.val hyE
  rw [hval]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hL₁W hl₁m) (hL₂W hl₂m))
    (Subgroup.pow_mem _ (y_mem_Wsub (K := K) (K' := K') _) j)

theorem W_normal_cent {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (hAut : TwinThinPf8.AEAut n)
    (hC : TwinThinPf8.AEChar n) (J : AEIdent (fam K (conjSub g (piGen π))) n)
    (hker : J.φ.ker = ⊥) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {y : ↥(pSpan (fam K (conjSub g (piGen π))))} (hyφ : J.φ y = AE.yBar α h)
    (hyX : ∀ x ∈ piGen π, (y : G) * x = x * (y : G)) :
    ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ w ∈ Wsub K K' (y : G), c * w * c⁻¹ ∈
      Wsub K K' (y : G) := by
  have hKK := S.pair_le_cent
  have hWX : ∀ x ∈ piGen π, ∀ w ∈ Wsub K K' (y : G), x * w = w * x := by
    intro x hx w hw
    have hle : Wsub K K' (y : G) ≤ Subgroup.centralizer {x} := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro t ((ht | ht) | ht)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hKK.1 ht)) x hx).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hKK.2 ht)) x hx).symm
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hyX x hx)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm
  refine S.frattini hWX ?_
  intro c hc w hw
  have hcz := hc.1
  have hcC' := hc.2
  have hgen : (Wsub K K' (y : G)) ≤ (Wsub K K' (y : G)).comap (MulAut.conj c).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ((ht | ht) | ht)
    · rcases S.conj_K_mem hn hn8 J hlab hcz hcC' (Or.inl rfl) with h1 | h1
      · have : c * t * c⁻¹ ∈ conjSub c K := conj_mem_conjSub ht
        rw [h1] at this
        exact le_Wsub_K (K := K) (K' := K') _ this
      · have : c * t * c⁻¹ ∈ conjSub c K := conj_mem_conjSub ht
        rw [h1] at this
        exact le_Wsub_K' (K := K) (K' := K') _ this
    · rcases S.conj_K_mem hn hn8 J hlab hcz hcC' (Or.inr rfl) with h1 | h1
      · have : c * t * c⁻¹ ∈ conjSub c K' := conj_mem_conjSub ht
        rw [h1] at this
        exact le_Wsub_K (K := K) (K' := K') _ this
      · have : c * t * c⁻¹ ∈ conjSub c K' := conj_mem_conjSub ht
        rw [h1] at this
        exact le_Wsub_K' (K := K) (K' := K') _ this
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact S.conj_y_mem hn hn8 hAut hC J hker hlab hyφ hcz hcC'
  exact hgen hw

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
