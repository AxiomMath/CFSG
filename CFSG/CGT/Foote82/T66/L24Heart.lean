module

public import CFSG.CGT.Foote82.T66.L24Vab
public import CFSG.CGT.Foote82.T66.CitedMC2
import CFSG.CGT.Foote82.T66.MC2Perm

public section

namespace CFSG.CGT.Foote82.L24

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv Equiv.Perm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {G : Subgroup (GLV V)} {N : ℕ}

section EW

theorem mem_evenWeight_iff {n : ℕ} {x : Fin n → ZMod 2} : x ∈ evenWeight n ↔ ∑ i, x i = 0 := by
  rw [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]

theorem mem_evenWeightOnes_iff {n : ℕ} {x : evenWeight n} :
    x ∈ evenWeightOnes n ↔ (x : Fin n → ZMod 2) = 0 ∨ (x : Fin n → ZMod 2) = allOnes n := by
  rw [evenWeightOnes, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hk' : ∀ i, (x : Fin n → ZMod 2) i = (k : ZMod 2) := fun i => by
      rw [← hk]
      simp [allOnes]
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (k : ZMod 2) with h0 | h1
    · left
      funext i
      rw [hk' i, h0]
      rfl
    · right
      funext i
      rw [hk' i, h1]
      rfl
  · rintro (h0 | h1)
    · exact ⟨0, by rw [h0, zero_zsmul]⟩
    · exact ⟨1, by rw [h1, one_zsmul]⟩

end EW

section Natural

variable {φ : ↥G ≃* alternatingGroup (Fin N)} {n : ℕ} {τ : Fin n ↪ Fin N}

@[expose] def pairE (i j : Fin n) : evenWeight n :=
  ⟨Pi.single i 1 + Pi.single j 1, mem_evenWeight_iff.2 (by
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      if_true]
    decide)⟩

theorem pairE_apply (i j k : Fin n) :
    (pairE i j : Fin n → ZMod 2) k = (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
  simp [pairE, Pi.single_apply]

@[expose] def res (τ : Fin n ↪ Fin N) (y : Fin N → ZMod 2) : Fin n → ZMod 2 := fun i => y (τ i)

theorem sum_res {F : Finset (Fin N)} (hF : F = Finset.univ.map τ) {y : Fin N → ZMod 2}
    (hy : y ∈ Ew F) : ∑ i, res τ y i = 0 := by
  have h1 : ∑ k, y k = ∑ k ∈ F, y k :=
    (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => hy.1 k hk).symm
  rw [hF, Finset.sum_map] at h1
  rw [← hy.2, h1]
  rfl

@[expose] def resE (τ : Fin n ↪ Fin N) {F : Finset (Fin N)} (hF : F = Finset.univ.map τ)
    {y : Fin N → ZMod 2} (hy : y ∈ Ew F) : evenWeight n :=
  ⟨res τ y, mem_evenWeight_iff.2 (sum_res hF hy)⟩

theorem res_jS {F : Finset (Fin N)} (hF : F = Finset.univ.map τ) : res τ (jS F) = allOnes n := by
  funext i
  simp [res, jS_apply, allOnes, hF]

theorem exists_perm_of_maps {π : Perm (Fin N)} (hπ : ∀ i, ∃ j, π (τ i) = τ j) :
    ∃ σ : Perm (Fin n), ∀ i, π (τ i) = τ (σ i) := by
  choose f hf using hπ
  have hinj : Function.Injective f := fun i j h => by
    have := (hf i).trans (h ▸ (hf j).symm)
    exact τ.injective (π.injective this)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem heartW_of_natural (hn : 1 ≤ n) {F : Finset (Fin N)} (hF : F = Finset.univ.map τ)
    (β : ↥(commSpace (AS φ F) ⊤) →+ altHeart n) (hβs : Function.Surjective β)
    (hβk : β.ker = ((fixedSpace (AS φ F)).comap (commSpace (AS φ F) ⊤).subtype).toAddSubgroup)
    (hβR : ∀ g : ↥G, (g : GLV V) ∈ AS φ F → ∀ σ : Perm (Fin n),
      (∀ i, pm φ g (τ i) = τ (σ i)) → ∀ w w' : ↥(commSpace (AS φ F) ⊤),
        (w' : V) = (g : GLV V) (w : V) → ∀ x : evenWeight n, β w = (x : altHeart n) →
          β w' = (evenWeightPerm σ x : altHeart n)) :
    ∃ θ, HeartW φ F θ := by
  classical
  have hmemF : ∀ k, k ∈ F ↔ ∃ i, τ i = k := fun k => by simp [hF]
  have i₀ : Fin n := ⟨0, by omega⟩
  choose w hw using fun i : Fin n => hβs ((pairE i i₀ : evenWeight n) : altHeart n)
  let θ : (Fin N → ZMod 2) →ₗ[ZMod 2] V :=
    { toFun := fun y => ∑ i, y (τ i) • (w i : V)
      map_add' := fun y z => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c y => by simp [Finset.smul_sum, smul_smul] }
  have hθ : ∀ y, θ y = ∑ i, y (τ i) • (w i : V) := fun _ => rfl
  have hmem : ∀ y, θ y ∈ commSpace (AS φ F) ⊤ := fun y => by
    rw [hθ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (w i).2
  have hθev : ∀ i, θ (ev (τ i)) = (w i : V) := fun i => by
    rw [hθ]
    simp [ev_apply, τ.injective.eq_iff]
  have hβθ : ∀ y (hy : y ∈ Ew F),
      β ⟨θ y, hmem y⟩ = ((resE τ hF hy : evenWeight n) : altHeart n) := by
    intro y hy
    have hspan := Ew_le_span F hy
    induction hspan using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨i, rfl⟩ := (hmemF a).1 ha
      obtain ⟨j, rfl⟩ := (hmemF b).1 hb
      have e1 : (⟨θ (ev (τ i) + ev (τ j)), hmem _⟩ : ↥(commSpace (AS φ F) ⊤)) = w i + w j :=
        Subtype.ext (by
          show θ (ev (τ i) + ev (τ j)) = (w i : V) + (w j : V)
          rw [map_add, hθev, hθev])
      rw [e1, map_add, hw, hw, ← QuotientAddGroup.mk_add]
      congr 1
      apply Subtype.ext
      funext k
      show (pairE i i₀ : Fin n → ZMod 2) k + (pairE j i₀ : Fin n → ZMod 2) k =
        (ev (τ i) + ev (τ j)) (τ k)
      rw [pairE_apply, pairE_apply, Pi.add_apply, ev_apply, ev_apply]
      simp only [τ.injective.eq_iff]
      generalize (if k = i then (1 : ZMod 2) else 0) = p
      generalize (if k = j then (1 : ZMod 2) else 0) = q
      generalize (if k = i₀ then (1 : ZMod 2) else 0) = r
      revert p q r
      decide
    | zero =>
      have e0 : (⟨θ 0, hmem 0⟩ : ↥(commSpace (AS φ F) ⊤)) = 0 :=
        Subtype.ext (map_zero θ)
      rw [e0, map_zero]
      symm
      rw [QuotientAddGroup.eq_zero_iff]
      have : (resE τ hF hy) = 0 := Subtype.ext rfl
      rw [this]
      exact AddSubgroup.zero_mem _
    | add x z hx hz ihx ihz =>
      have hxE : x ∈ Ew F := (Submodule.span_le.2 (by
        rintro _ ⟨a, ha, b, hb, rfl⟩; exact ev_add_ev_mem_Ew ha hb)) hx
      have hzE : z ∈ Ew F := (Submodule.span_le.2 (by
        rintro _ ⟨a, ha, b, hb, rfl⟩; exact ev_add_ev_mem_Ew ha hb)) hz
      have e1 : (⟨θ (x + z), hmem _⟩ : ↥(commSpace (AS φ F) ⊤)) =
          ⟨θ x, hmem x⟩ + ⟨θ z, hmem z⟩ := Subtype.ext (map_add θ x z)
      rw [e1, map_add, ihx hxE, ihz hzE, ← QuotientAddGroup.mk_add]
      rfl
    | smul c x hx ih =>
      have hxE : x ∈ Ew F := (Submodule.span_le.2 (by
        rintro _ ⟨a, ha, b, hb, rfl⟩; exact ev_add_ev_mem_Ew ha hb)) hx
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
      · have e0 : (⟨θ ((0 : ZMod 2) • x), hmem _⟩ : ↥(commSpace (AS φ F) ⊤)) = 0 :=
          Subtype.ext (by
            show θ ((0 : ZMod 2) • x) = 0
            rw [zero_smul, map_zero])
        rw [e0, map_zero]
        symm
        rw [QuotientAddGroup.eq_zero_iff]
        have : (resE τ hF hy) = 0 := Subtype.ext (by funext k; simp [resE, res])
        rw [this]
        exact AddSubgroup.zero_mem _
      · have e1 : (⟨θ ((1 : ZMod 2) • x), hmem _⟩ : ↥(commSpace (AS φ F) ⊤)) = ⟨θ x, hmem x⟩ :=
          Subtype.ext (by
            show θ ((1 : ZMod 2) • x) = θ x
            rw [one_smul])
        rw [e1, ih hxE]
        congr 1
        exact Subtype.ext (by funext k; simp [resE, res])
  have hTiff : ∀ y, θ y ∈ tildeVBot (AS φ F) ↔ β ⟨θ y, hmem y⟩ = 0 := by
    intro y
    rw [← AddMonoidHom.mem_ker, hβk]
    exact ⟨fun h => h.1, fun h => ⟨h, hmem y⟩⟩
  refine ⟨θ, fun y _ => hmem y, ?_, ?_, ?_⟩
  ·
    intro v hv
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (β ⟨v, hv⟩)
    let x : Fin N → ZMod 2 := ∑ i, (z : Fin n → ZMod 2) i • ev (τ i)
    have hxk : ∀ k, x k = ∑ i, (z : Fin n → ZMod 2) i * (if k = τ i then 1 else 0) := fun k => by
      show (∑ i, (z : Fin n → ZMod 2) i • ev (τ i)) k = _
      rw [Finset.sum_apply]
      simp [ev_apply]
    have hxE : x ∈ Ew F := by
      refine ⟨fun k hk => ?_, ?_⟩
      · rw [hxk]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [if_neg fun h => hk ((hmemF k).2 ⟨i, h.symm⟩), mul_zero]
      · simp_rw [hxk]
        rw [Finset.sum_comm]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact mem_evenWeight_iff.1 z.2
    have hres : resE τ hF hxE = z := by
      apply Subtype.ext
      funext j
      show x (τ j) = _
      rw [hxk]
      simp only [τ.injective.eq_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    have hd : (⟨v, hv⟩ : ↥(commSpace (AS φ F) ⊤)) - ⟨θ x, hmem x⟩ ∈ β.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, hβθ x hxE, hres, hz, sub_self]
    rw [hβk] at hd
    have e : v = θ x + (v - θ x) := by abel
    rw [e]
    exact Submodule.add_mem_sup ⟨x, hxE, rfl⟩ ⟨hd, (commSpace (AS φ F) ⊤).sub_mem hv (hmem x)⟩
  ·
    intro y hy
    rw [hTiff y, hβθ y hy, QuotientAddGroup.eq_zero_iff, mem_evenWeightOnes_iff]
    constructor
    · rintro (h0 | h1)
      · left
        funext k
        by_cases hk : k ∈ F
        · obtain ⟨i, rfl⟩ := (hmemF k).1 hk
          exact congrFun h0 i
        · exact hy.1 k hk
      · right
        funext k
        by_cases hk : k ∈ F
        · obtain ⟨i, rfl⟩ := (hmemF k).1 hk
          rw [jS_apply, if_pos hk]
          exact congrFun h1 i
        · rw [jS_apply, if_neg hk]
          exact hy.1 k hk
    · rintro (rfl | rfl)
      · left
        rfl
      · right
        exact res_jS hF
  ·
    intro g hg y hy
    have hmaps : ∀ i, ∃ j, pm φ g (τ i) = τ j := fun i => by
      obtain ⟨j, hj⟩ := (hmemF _).1 (apply_mem_of_mem_altOn hg ((hmemF (τ i)).2 ⟨i, rfl⟩))
      exact ⟨j, hj.symm⟩
    obtain ⟨σ, hσ⟩ := exists_perm_of_maps hmaps
    have hgA : (g : GLV V) ∈ AS φ F := (coe_mem_AS φ).2 hg
    have hpy := pa_mem_Ew hg hy
    have h1 := hβR g hgA σ hσ ⟨θ y, hmem y⟩
      ⟨(g : GLV V) (θ y), apply_mem_commSpace hgA (hmem y)⟩ rfl (resE τ hF hy) (hβθ y hy)
    have h2 := hβθ _ hpy
    have hres : resE τ hF hpy = evenWeightPerm σ (resE τ hF hy) := by
      apply Subtype.ext
      funext j
      show y ((pm φ g)⁻¹ (τ j)) = y (τ (σ⁻¹ j))
      congr 1
      rw [Perm.inv_eq_iff_eq, hσ]
      simp
    have hd : (⟨(g : GLV V) (θ y), apply_mem_commSpace hgA (hmem y)⟩ :
        ↥(commSpace (AS φ F) ⊤)) - ⟨θ (pa (pm φ g) y), hmem _⟩ ∈ β.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, h1, h2, hres, sub_self]
    rw [hβk] at hd
    exact ⟨hd, (commSpace (AS φ F) ⊤).sub_mem (apply_mem_commSpace hgA (hmem y)) (hmem _)⟩

end Natural

section Iso

variable {φ : ↥G ≃* alternatingGroup (Fin N)}

theorem isAltHeartFor_of_heartW_univ (hN : 5 ≤ N) (hirr : IsIrr G ⊤)
    {θ : (Fin N → ZMod 2) →ₗ[ZMod 2] V} (h : HeartW φ Finset.univ θ) : IsAltHeartFor G N := by
  obtain ⟨htop, hbot⟩ := commSpace_eq_top_fixedSpace_eq_bot φ (by omega) hirr
  have hT : tildeVBot (AS φ (Finset.univ : Finset (Fin N))) = ⊥ := by
    rw [AS_univ, tildeVBot, hbot, bot_inf_eq]
  have hW : commSpace (AS φ (Finset.univ : Finset (Fin N))) ⊤ = ⊤ := by
    rw [AS_univ, htop]
  have hEw : ∀ x : evenWeight N, (x : Fin N → ZMod 2) ∈ Ew Finset.univ := fun x =>
    ⟨fun k hk => absurd (Finset.mem_univ k) hk, mem_evenWeight_iff.1 x.2⟩
  let Φ : evenWeight N →+ V :=
    { toFun := fun x => θ x
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hΦ : ∀ x : evenWeight N, Φ x = θ x := fun _ => rfl
  have hsurj : Function.Surjective Φ := by
    intro v
    have hv : v ∈ (Ew Finset.univ).map θ ⊔ tildeVBot (AS φ Finset.univ) :=
      h.span (by rw [hW]; exact Submodule.mem_top)
    rw [hT, sup_bot_eq] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨⟨y, mem_evenWeight_iff.2 hy.2⟩, rfl⟩
  have hj : jS (Finset.univ : Finset (Fin N)) = allOnes N := by
    funext k
    simp [jS_apply, allOnes]
  have hker : Φ.ker = evenWeightOnes N := by
    ext x
    rw [AddMonoidHom.mem_ker, mem_evenWeightOnes_iff, hΦ]
    have := h.ker x (hEw x)
    rw [hT, Submodule.mem_bot, hj] at this
    exact this
  let ψ : V ≃+ altHeart N :=
    (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq hker)
  have hψ : ∀ x : evenWeight N, ψ (Φ x) = (x : altHeart N) := by
    intro x
    have e : (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).symm (Φ x) =
        (x : evenWeight N ⧸ Φ.ker) := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    show QuotientAddGroup.quotientAddEquivOfEq hker
      ((QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).symm (Φ x)) = _
    rw [e, QuotientAddGroup.quotientAddEquivOfEq_mk]
  refine ⟨φ, ψ, fun e v x hvx => ?_⟩
  have hv : v = Φ x := ψ.injective (hvx.trans (hψ x).symm)
  have he := h.equiv e (MC2.mem_altOn_iff.2 ⟨pm_mem_alternatingGroup φ e,
    fun k hk => absurd (Finset.mem_coe.2 (Finset.mem_univ k)) hk⟩) x (hEw x)
  rw [hT, Submodule.mem_bot, sub_eq_zero] at he
  have e3 : (e : GLV V) (Φ x) = Φ (evenWeightPerm (φ e : Perm (Fin N)) x) := he
  rw [hv, e3, hψ]

end Iso

theorem _root_.CFSG.CGT.Foote82.footeLemma24_holds : FooteLemma24 := by
  intro V _ _ _ G L n φ τ hn hLG himg hirr hnat
  set F : Finset (Fin (n + 4)) := Finset.univ.map τ with hF
  have hFτ : ((F : Finset (Fin (n + 4))) : Set (Fin (n + 4))) = Set.range τ := by
    rw [hF, Finset.coe_map, Finset.coe_univ, Set.image_univ]
  have hfi : Function.Injective ((alternatingGroup (Fin (n + 4))).subtype.comp φ.toMonoidHom) :=
    Subtype.val_injective.comp φ.injective
  have hLF : L = AS φ F := by
    rw [AS, hFτ, ← himg, Subgroup.comap_map_eq_self_of_injective hfi,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLG]
  subst hLF
  obtain ⟨β, hβs, hβk, hβR⟩ := hnat
  obtain ⟨θ, hθ⟩ := heartW_of_natural (φ := φ) (τ := τ) (by omega) hF β hβs hβk
    (fun g hg σ hσ w w' hw x hx => hβR g hg σ hσ w w' hw x hx)
  have hFc : 5 ≤ F.card := by
    rw [hF, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    omega
  exact isAltHeartFor_of_heartW_univ (by omega) hirr (hθ.heartW_univ hFc (by omega) hirr)

end CFSG.CGT.Foote82.L24
