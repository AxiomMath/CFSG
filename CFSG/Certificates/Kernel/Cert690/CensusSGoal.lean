module

public import CFSG.Certificates.Kernel.Cert690.CensusSGlue
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.C690S

open CFSG.KC.C690 CFSG.KC.Enum CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.O62

theorem exists_mem_of_word {S : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {gens : List ℕ}
    (hS : ∀ q < gens.length, ∃ x ∈ S, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) (gens.getD q 0))
    {w : List ℕ} (hw : ∀ q ∈ w, q < gens.length) :
    ∃ y ∈ S, Code.HasCode (y : V₀ →ₗ[ZMod 2] V₀) (wvS (nthS 0 gens) w oneF) := by
  classical
  let X : ℕ → V₀ ≃ₗ[ZMod 2] V₀ := fun q =>
    if h : q < gens.length then Classical.choose (hS q h) else 1
  have hX : ∀ q ∈ w, X q ∈ S ∧ Code.HasCode (X q : V₀ →ₗ[ZMod 2] V₀) (nthS 0 gens q) := by
    intro q hq
    have h := hw q hq
    simp only [X, dif_pos h, nthS_eq]
    exact Classical.choose_spec (hS q h)
  have h := cd_wvS w (fun q hq => (hX q hq).2) cd_one
  rw [one_mul] at h
  refine ⟨_, list_prod_mem ?_, h⟩
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact (hX q hq).1

theorem codeSubgroup_le_of_words {S : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {gens tg : List ℕ}
    {wa : List (List ℕ)}
    (hS : ∀ q < gens.length, ∃ x ∈ S, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) (gens.getD q 0))
    (h : List.Forall₂ (fun w x => (∀ q ∈ w, q < gens.length) ∧ wvS (nthS 0 gens) w oneF = x)
      wa tg) :
    codeSubgroup tg ≤ S := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨c, hc, hxc⟩
  obtain ⟨w, -, hw, rfl⟩ := forall₂_mem_right h c hc
  obtain ⟨y, hy, hyc⟩ := exists_mem_of_word hS hw
  rw [Code.HasCode.eq_of_equiv hxc hyc]
  exact hy

theorem codeSubgroup_eq_of_bothS {gens tg : List ℕ} {wa wb : List (List ℕ)}
    (hB : BothS gens tg wa wb)
    (hg : ∀ q < gens.length, ∃ x : V₀ ≃ₗ[ZMod 2] V₀,
      Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) (gens.getD q 0)) :
    codeSubgroup gens = codeSubgroup tg := by
  have hS : ∀ q < gens.length, ∃ x ∈ codeSubgroup gens,
      Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) (gens.getD q 0) := by
    intro q hq
    obtain ⟨x, hx⟩ := hg q hq
    exact ⟨x, Subgroup.subset_closure ⟨_, getD_mem_of_lt hq 0, hx⟩, hx⟩
  have hT : ∀ q < tg.length, ∃ x ∈ codeSubgroup tg,
      Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) (tg.getD q 0) := by
    intro q hq
    have h := forall₂_getD 0 [] hB.1.flip q hq
    obtain ⟨y, -, hyc⟩ := exists_mem_of_word hS h.1
    rw [h.2] at hyc
    exact ⟨y, Subgroup.subset_closure ⟨_, getD_mem_of_lt hq 0, hyc⟩, hyc⟩
  exact le_antisymm (codeSubgroup_le_of_words hT hB.2) (codeSubgroup_le_of_words hS hB.1)

theorem subF_eq_codeSubgroup {minus : Bool} {D : GrpData} (hD : GrpFacts minus D) {G : GK}
    (hR : GRel D G) {B : SBase} (hfg : ∀ gs ∈ B.fg, ∀ x ∈ gs, InOS G x) (g : ℕ) :
    subF hD G B g = codeSubgroup (gensS B g) := by
  unfold subF codeSubgroup
  congr 1
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, (cd_eltC hD hR (inOS_of_mem_gensS hfg hc)).1⟩
  · rintro ⟨c, hc, hxc⟩
    exact ⟨c, hc, Code.HasCode.eq_of_equiv (cd_eltC hD hR (inOS_of_mem_gensS hfg hc)).1 hxc⟩

theorem codeSubgroup_conj_eq {C : V₀ ≃ₗ[ZMod 2] V₀} {c ci : ℕ} {kpg : List ℕ}
    (hC : Code.HasCode (C : V₀ →ₗ[ZMod 2] V₀) c)
    (hCi : Code.HasCode ((C⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) ci)
    (hk : ∀ m ∈ kpg, ∃ Y : V₀ ≃ₗ[ZMod 2] V₀, Code.HasCode (Y : V₀ →ₗ[ZMod 2] V₀) m) :
    codeSubgroup (kpg.map fun x => mulF (mulF c x) ci) = conjSub (codeSubgroup kpg) C := by
  unfold codeSubgroup conjSub
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, hm', hyc⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hm'
    obtain ⟨Y, hY⟩ := hk m hm
    refine ⟨Y, ⟨m, hm, hY⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Code.HasCode.eq_of_equiv (cd_mul (cd_mul hC hY) hCi) hyc
  · rintro ⟨Y, ⟨m, hm, hY⟩, rfl⟩
    refine ⟨_, List.mem_map.mpr ⟨m, hm, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact cd_mul (cd_mul hC hY) hCi

theorem spanS_cons (v : ℕ) (V W : List ℕ) :
    spanS (v :: V) W = spanS V (W ++ W.map fun w => Nat.xor w v) := rfl

theorem length_spanS : ∀ (V W : List ℕ), (spanS V W).length = 2 ^ V.length * W.length
  | [], W => by
    change W.length = 2 ^ 0 * W.length
    rw [pow_zero, one_mul]
  | v :: V, W => by
    rw [spanS_cons, length_spanS V, List.length_append, List.length_map, List.length_cons,
      pow_succ]
    ring

theorem vec_mem_of_spanS {Sp : Submodule (ZMod 2) V₀} :
    ∀ (V W : List ℕ), (∀ v ∈ V, Code.vec v ∈ Sp) → (∀ w ∈ W, Code.vec w ∈ Sp) →
      ∀ x ∈ spanS V W, Code.vec x ∈ Sp
  | [], _, _, hW => hW
  | v :: V, W, hV, hW => by
    rw [spanS_cons]
    refine vec_mem_of_spanS V _ (fun v' hv' => hV v' (List.mem_cons_of_mem _ hv')) ?_
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hW w hw
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      change Code.vec (u ^^^ v) ∈ Sp
      rw [vec_xor]
      exact Sp.add_mem (hW u hu) (hV v List.mem_cons_self)

theorem exists_spanS : ∀ (V W : List ℕ) (Sp : Submodule (ZMod 2) V₀),
    (∀ y ∈ Sp, ∃ x ∈ W, Code.vec x = y) →
      ∀ y ∈ Sp ⊔ spanOfList V, ∃ x ∈ spanS V W, Code.vec x = y
  | [], W, Sp, hW => by
    rw [spanOfList_nil, sup_bot_eq]
    exact hW
  | v :: V, W, Sp, hW => by
    rw [spanS_cons, spanOfList_cons, ← sup_assoc]
    refine exists_spanS V _ _ ?_
    intro y hy
    rw [Submodule.mem_sup] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    rw [Submodule.mem_span_singleton] at hb
    obtain ⟨k, rfl⟩ := hb
    obtain ⟨x, hx, rfl⟩ := hW a ha
    rcases zmod2_eq_zero_or_eq_one k with rfl | rfl
    · rw [zero_smul, add_zero]
      exact ⟨x, List.mem_append_left _ hx, rfl⟩
    · rw [one_smul]
      refine ⟨Nat.xor x v, List.mem_append_right _ (List.mem_map.mpr ⟨x, hx, rfl⟩), ?_⟩
      change Code.vec (x ^^^ v) = _
      rw [vec_xor]

theorem invariant_of_closure {S : Set (V₀ ≃ₗ[ZMod 2] V₀)} {W : Submodule (ZMod 2) V₀}
    (h : ∀ g ∈ S, ∀ w ∈ W, g w ∈ W) :
    ∀ g ∈ Subgroup.closure S, ∀ w ∈ W, g w ∈ W := by
  have : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  have hmul : ∀ a b : V₀ ≃ₗ[ZMod 2] V₀, (∀ w ∈ W, a w ∈ W) → (∀ w ∈ W, b w ∈ W) →
      ∀ w ∈ W, (a * b) w ∈ W := fun a b ha hb w hw => by
    rw [LinearEquiv.mul_apply]
    exact ha _ (hb w hw)
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => exact fun w hw => hw
  | mul a b _ _ ha hb => exact hmul a b ha hb
  | inv a _ ha =>
    have hpow : ∀ k : ℕ, ∀ w ∈ W, (a ^ k) w ∈ W := by
      intro k
      induction k with
      | zero => exact fun w hw => hw
      | succ k ih =>
        rw [pow_succ]
        exact hmul _ _ ih ha
    have hinv : a ^ (orderOf a - 1) = a⁻¹ := by
      refine mul_eq_one_iff_eq_inv.mp ?_
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
    rw [← hinv]
    exact hpow _

theorem not_irreducibleSub_of_span {gens V : List ℕ} {v : ℕ} (hv0 : 0 < v) (hv : v < 64)
    (h5 : V.length ≤ 5) (hvW : v ∈ spanS V [0])
    (hinv : ∀ x ∈ gens, ∀ y ∈ V, actS x y ∈ spanS V [0]) :
    ¬ IrreducibleSub (codeSubgroup gens) := by
  classical
  intro hirr
  set W := spanOfList V
  have hVW : ∀ y ∈ V, Code.vec y ∈ W := fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  have hmem : ∀ x ∈ spanS V [0], Code.vec x ∈ W := by
    refine vec_mem_of_spanS V [0] hVW ?_
    intro w hw
    rw [List.mem_singleton] at hw
    rw [hw, vec_zero]
    exact W.zero_mem
  have hgen : ∀ g ∈ {g : V₀ ≃ₗ[ZMod 2] V₀ | ∃ m ∈ gens, Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m},
      ∀ w ∈ W, g w ∈ W := by
    rintro g ⟨m, hm, hgm⟩ w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨y, hy, rfl⟩
      rw [cd_vec hgm]
      exact hmem _ (hinv m hm y hy)
    · rw [map_zero]
      exact W.zero_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact W.add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact W.smul_mem c hx
  rcases hirr W (invariant_of_closure hgen) with hbot | htop
  · have h1 := hmem v hvW
    rw [hbot, Submodule.mem_bot, ← vec_zero] at h1
    exact absurd (vec_injective_of_lt hv (by norm_num) h1) (by omega)
  · have hcov := exists_spanS V [0] ⊥ (by
      intro y hy
      rw [Submodule.mem_bot] at hy
      exact ⟨0, List.mem_singleton_self 0, by rw [hy, vec_zero]⟩)
    have hsub : (Set.univ : Set V₀) ⊆ ↑((spanS V [0]).map Code.vec).toFinset := by
      intro y _
      have hy : y ∈ (⊥ : Submodule (ZMod 2) V₀) ⊔ W := by
        rw [bot_sup_eq, htop]
        exact Submodule.mem_top
      obtain ⟨x, hx, rfl⟩ := hcov y hy
      rw [Finset.mem_coe, List.mem_toFinset]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    have hcard : Nat.card V₀ ≤ (spanS V [0]).length := by
      rw [← Set.ncard_univ]
      calc (Set.univ : Set V₀).ncard
          ≤ (↑((spanS V [0]).map Code.vec).toFinset : Set V₀).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = ((spanS V [0]).map Code.vec).toFinset.card := Set.ncard_coe_finset _
        _ ≤ ((spanS V [0]).map Code.vec).length := List.toFinset_card_le _
        _ = (spanS V [0]).length := List.length_map _
    rw [natCard_eq_sixtyFour (V := V₀) (Module.finrank_fin_fun (ZMod 2)), length_spanS,
      List.length_singleton, mul_one] at hcard
    have : 2 ^ V.length ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) h5
    omega

theorem not_irreducibleSub_of_eq_conj {K H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    {n : V₀ ≃ₗ[ZMod 2] V₀} (hnot : ¬ IrreducibleSub K) (hH : ∀ x, x ∈ H ↔ n⁻¹ * x * n ∈ K) :
    ¬ IrreducibleSub H := by
  intro h
  have hK : K = conjSub H n⁻¹ := by
    ext x
    rw [mem_conjSub, inv_inv, hH, show n⁻¹ * (n * x * n⁻¹) * n = x by group]
  exact hnot (hK ▸ irreducibleSub_conj h)

theorem censusLGoal_of_facts {minus : Bool} (hb : censusBase minus () = true) {G : GK}
    (hR : GRel (grpData minus ()) G) {cs : List ℕ} {B : SBase}
    (hBF : BaseFacts G (ldata minus ()).Llist cs B) (hbind : bindS minus B = true)
    (hcs : (candidatesOf minus (ldata minus ()).Llist).toList = cs)
    (hbq : b0Of minus = B.b) (hnd : B.sing.Nodup) (hblt : B.b < 64)
    (hKP : minus = false → ∀ m ∈ kPGLGens, ∃ Y : V₀ ≃ₗ[ZMod 2] V₀,
      Code.HasCode (Y : V₀ →ₗ[ZMod 2] V₀) m)
    (hF : ∀ g < B.nF, ∃ ginv wg cpar T reps recs cls,
      CheckFFacts B g ginv wg cpar T reps recs cls) :
    ∀ ci < (candidatesOf minus (ldata minus ()).Llist).size, CensusLGoal minus ci := by
  classical
  have hD := grpFacts_of_censusBase hb
  obtain ⟨hog, homg, hkpg, hpgl, hcard⟩ := bindS_sound hbind
  have hS : SFacts minus (grpData minus ()) G B :=
    { rel := hR
      stab := hBF.stab
      tp := hBF.tp
      fg := hBF.fg
      card := by rw [hcard, natCard_O₀]
      nodup := hnd
      sing_lt := fun p hp => by
        rw [← (hBF.tp p hp).2.1]
        exact actS_lt _ _
      b_lt := hblt }
  intro ci hci H hHO _ hirr L hL hC
  have hcl : ci < cs.length := by
    rw [← hcs, Array.length_toList]
    exact hci
  have hget : (candidatesOf minus (ldata minus ()).Llist)[ci]! = cs.getD ci 0 := by
    rw [getElem!_pos _ ci hci, List.getD_eq_getElem _ _ hcl]
    simp only [← hcs, Array.getElem_toList]
  rw [hget] at hL
  have hLF := lFacts_of hb hR hBF.cand hBF.lenLG hcl hL
  rw [hbq] at hC
  obtain ⟨k, hk, -, n, hn, hHk⟩ := exists_conj_subF hD hS hLF
    (hBF.first ci (by rw [← hBF.lenCs]; exact hcl)) hF hHO hC
  have hnO := (mem_censusN.mp hn).1
  obtain ⟨ginv, wg, cpar, T, reps, recs, cls, hFk⟩ := hF k hk
  have hsub := subF_eq_codeSubgroup hD hR hBF.fg k
  have hgens : ∀ q < (gensS B k).length, ∃ x : V₀ ≃ₗ[ZMod 2] V₀,
      Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) ((gensS B k).getD q 0) := fun q hq =>
    ⟨_, (cd_eltC hD hR (inOS_of_mem_gensS hBF.fg (getD_mem_of_lt hq 0))).1⟩
  have hHeq : H = conjSub (subF hD G B k) n := by
    ext x
    rw [hHk, mem_conjSub]
  rcases hFk.clsOK with ⟨-, hv0, hv, h5, -, hvW, hinv⟩ | ⟨-, hB2⟩ | ⟨-, hB3⟩ |
      ⟨-, hpglT, hcP, hcci, hB4⟩
  ·
    exfalso
    refine not_irreducibleSub_of_eq_conj ?_ hHk hirr
    rw [hsub]
    exact not_irreducibleSub_of_span hv0 hv h5 hvW hinv
  ·
    have hΩ : subF hD G B k = Ω₀ minus := by
      rw [hsub, codeSubgroup_eq_of_bothS hB2 hgens, homg, hD.codeOm]
    have hHΩ : H = Ω₀ minus := by
      rw [hHeq, hΩ]
      exact map_conj_omega_eq hnO
    cases minus with
    | true => exact Or.inl hHΩ
    | false => exact Or.inl hHΩ
  ·
    have hO : subF hD G B k = O₀ minus := by
      rw [hsub, codeSubgroup_eq_of_bothS hB3 hgens, hog, hD.codeO]
    have hHO' : H = O₀ minus := by
      rw [hHeq, hO]
      exact map_conj_O_eq hnO
    cases minus with
    | true => exact Or.inr hHO'
    | false => exact Or.inr (Or.inl hHO')
  ·
    have hm : minus = false := by
      rw [hpgl] at hpglT
      cases minus
      · rfl
      · exact absurd hpglT (by decide)
    subst hm
    obtain ⟨hcC, hcO, -⟩ := cd_eltC hD hR (hBF.pglc _ hcP)
    have hcI := cd_inv hcC hcci
    have hK : subF hD G B k = conjSub KPGL (eltC hD G (cls.1.getD 1 0)) := by
      rw [hsub, codeSubgroup_eq_of_bothS hB4 hgens, hkpg]
      exact codeSubgroup_conj_eq hcC hcI (hKP rfl)
    refine Or.inr (Or.inr ⟨n * eltC hD G (cls.1.getD 1 0), mul_mem hnO hcO, fun x => ?_⟩)
    rw [hHk, hK, mem_conjSub]
    rw [show (eltC hD G (cls.1.getD 1 0))⁻¹ * (n⁻¹ * x * n) * eltC hD G (cls.1.getD 1 0) =
      (n * eltC hD G (cls.1.getD 1 0))⁻¹ * x * (n * eltC hD G (cls.1.getD 1 0)) by group]

theorem exists_checkF_of_chunk {B : SBase} {lo n : ℕ} {ginv : List (List ℕ)}
    {wg : List (List (List ℕ))} {cpar : List (List (ℕ × ℕ))} {T : List (List (ℕ × ℕ))}
    {orb : List (List (ℕ × ℕ × ℕ))} {reps : List (List ℕ)} {ranks : List (List (List ℕ))}
    {recs : List (List (List (List ℕ × List (List ℕ))))}
    {cls : List (List ℕ × List (List ℕ) × List (List ℕ))}
    (h : ∀ i < n, checkAt B lo ginv wg cpar T orb reps ranks recs cls i = true) {g : ℕ}
    (h1 : lo ≤ g) (h2 : g < lo + n) :
    ∃ ginv wg cpar T reps recs cls, CheckFFacts B g ginv wg cpar T reps recs cls := by
  have hF := checkAt_sound (h (g - lo) (by omega))
  rw [Nat.add_sub_cancel' h1] at hF
  exact ⟨_, _, _, _, _, _, _, hF⟩

end CFSG.KC.C690S

end
