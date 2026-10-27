module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbNodes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbLeviRad
public import CFSG.LocalAnalysis.RankThreeUC.K518HANodeSU

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open scoped Pointwise
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar CFSG.AGLEmbeddingD2.Tits.GN516
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section CaseB

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

private theorem natCard_map_rankOne (j : Fin D.rank) (hker : π.ker ⊓ rankOne D.rootGroup j = ⊥) :
    Nat.card ↥((rankOne D.rootGroup j).map π) = Nat.card ↥(rankOne D.rootGroup j) := by
  have hinj : Function.Injective (π.comp (rankOne D.rootGroup j).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine eq_bot_iff.2 fun x hx => ?_
    have hx1 : (x : K) ∈ π.ker ⊓ rankOne D.rootGroup j := ⟨hx, x.2⟩
    rw [hker, Subgroup.mem_bot] at hx1
    rw [Subgroup.mem_bot]
    exact Subtype.ext hx1
  have hrange : (π.comp (rankOne D.rootGroup j).subtype).range = (rankOne D.rootGroup j).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem map_rankOne_inf_eq_bot (h : BorelQuotient D n H π M) {j k : Fin D.rank} (hjk : j ≠ k)
    (hc : D.cartan j k = 0)
    (hcent : Subgroup.center ↥(rankOne D.rootGroup j) = ⊥ ∨
      Subgroup.center ↥(rankOne D.rootGroup k) = ⊥) :
    (rankOne D.rootGroup j).map π ⊓ (rankOne D.rootGroup k).map π = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩ := hx
  rw [Subgroup.mem_bot]
  have hz : u⁻¹ * v ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hvu, inv_mul_cancel]
  have hzc := Subgroup.mem_center_iff.1 (h.ker_central _ hz)
  have hcomm : ∀ a ∈ rankOne D.rootGroup j, ∀ b ∈ rankOne D.rootGroup k, a * b = b * a :=
    fun a ha b hb => Levi.rankOne_commute h.ct h.extras hjk hc ha hb
  have hcomm' : ∀ a ∈ rankOne D.rootGroup k, ∀ b ∈ rankOne D.rootGroup j, a * b = b * a :=
    fun a ha b hb => (hcomm b hb a ha).symm
  rcases hcent with hj | hk
  ·
    have hucen : (⟨u, hu⟩ : ↥(rankOne D.rootGroup j)) ∈ Subgroup.center ↥(rankOne D.rootGroup j) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      change (g : K) * u = u * (g : K)
      have e1 : u = v * (u⁻¹ * v)⁻¹ := by group
      have hgu : Commute (g : K) (v * (u⁻¹ * v)⁻¹) :=
        (show Commute (g : K) v from hcomm g g.2 v hv).mul_right
          (show Commute (g : K) (u⁻¹ * v) from hzc (g : K)).inv_right
      rw [← e1] at hgu
      exact hgu.eq
    rw [hj, Subgroup.mem_bot] at hucen
    have : u = 1 := congrArg Subtype.val hucen
    rw [this, map_one]
  · have hvcen : (⟨v, hv⟩ : ↥(rankOne D.rootGroup k)) ∈ Subgroup.center ↥(rankOne D.rootGroup k) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      change (g : K) * v = v * (g : K)
      have e1 : v = u * (u⁻¹ * v) := by group
      have h1 := hcomm' g g.2 u hu
      have h2 := hzc (g : K)
      calc (g : K) * v = (g : K) * (u * (u⁻¹ * v)) := by rw [← e1]
        _ = ((g : K) * u) * (u⁻¹ * v) := by rw [mul_assoc]
        _ = (u * (g : K)) * (u⁻¹ * v) := by rw [h1]
        _ = u * ((g : K) * (u⁻¹ * v)) := by rw [mul_assoc]
        _ = u * ((u⁻¹ * v) * (g : K)) := by rw [h2]
        _ = (u * (u⁻¹ * v)) * (g : K) := by rw [← mul_assoc]
        _ = v * (g : K) := by rw [← e1]
    rw [hk, Subgroup.mem_bot] at hvcen
    have : v = 1 := congrArg Subtype.val hvcen
    rw [← hvu, this, map_one]


section Orbit

open CFSG.AGLEmbeddingD2.Tits.GN516.Nodes

private theorem toMonoidHom_pow_succ {Y : Type} [Group Y] (c : MulAut Y) (m : ℕ) :
    (c ^ (m + 1)).toMonoidHom = c.toMonoidHom.comp (c ^ m).toMonoidHom := by
  rw [pow_succ']
  exact MonoidHom.ext fun _ => rfl

private theorem map_parJ_pow_nodePerm (h : BorelQuotient D n H π M) (c : MulAut Y)
    (hcS : ((posUnipotent D).map π).map c.toMonoidHom = (posUnipotent D).map π)
    (j : Fin D.rank) (m : ℕ) :
    ((parJ D H {j}).map π).map (c ^ m).toMonoidHom =
      (parJ D H {((nodePerm h c hcS) ^ m) j}).map π := by
  induction m with
  | zero =>
    have h1 : (c ^ 0).toMonoidHom = MonoidHom.id Y := MonoidHom.ext fun _ => rfl
    rw [h1, Subgroup.map_id]
    rfl
  | succ m ih =>
    rw [toMonoidHom_pow_succ, ← Subgroup.map_map, ih,
      map_parJ_singleton_nodePerm h c hcS, pow_succ', Equiv.Perm.mul_apply]

private theorem map_unipJ_pow_nodePerm (h : BorelQuotient D n H π M) (c : MulAut Y)
    (hcS : ((posUnipotent D).map π).map c.toMonoidHom = (posUnipotent D).map π)
    (j : Fin D.rank) (m : ℕ) :
    ((unipJ D {j}).map π).map (c ^ m).toMonoidHom =
      (unipJ D {((nodePerm h c hcS) ^ m) j}).map π := by
  induction m with
  | zero =>
    have h1 : (c ^ 0).toMonoidHom = MonoidHom.id Y := MonoidHom.ext fun _ => rfl
    rw [h1, Subgroup.map_id]
    rfl
  | succ m ih =>
    rw [toMonoidHom_pow_succ, ← Subgroup.map_map, ih, map_unipJ_nodePerm h c hcS,
      Set.image_singleton, pow_succ', Equiv.Perm.mul_apply]

private theorem exists_nonadjacent_orbit (h : BorelQuotient D n H π M) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (c : MulAut Y) (hc : ∃ k : ℕ, orderOf c = p ^ k)
    (hcS : ((posUnipotent D).map π).map c.toMonoidHom = (posUnipotent D).map π) (i : Fin D.rank)
    (hmove : nodePerm h c hcS i ≠ i) :
    ∃ s t : ℕ, ((nodePerm h c hcS) ^ s) i ≠ ((nodePerm h c hcS) ^ t) i ∧
      D.cartan (((nodePerm h c hcS) ^ s) i) (((nodePerm h c hcS) ^ t) i) = 0 := by
  classical
  obtain ⟨k, hk⟩ := hc
  set σ : Equiv.Perm (Fin D.rank) := nodePerm h c hcS with hσ
  have hc1 : c ^ (p ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one c
  have hσp : ∀ j, (σ ^ (p ^ k)) j = j := by
    intro j
    have h1 := map_parJ_pow_nodePerm h c hcS j (p ^ k)
    rw [hc1] at h1
    have h2 : (1 : MulAut Y).toMonoidHom = MonoidHom.id Y := MonoidHom.ext fun _ => rfl
    rw [h2, Subgroup.map_id] at h1
    exact (parJ_map_injective h h1).symm
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have h12 : σ i ≠ i := hmove
  have h23 : σ (σ i) ≠ σ i := fun e => h12 (σ.injective e)
  have h13 : σ (σ i) ≠ i := by
    intro e
    obtain ⟨a, ha⟩ := hodd
    have h4 : ∀ a : ℕ, (σ ^ (2 * a)) i = i := by
      intro a
      induction a with
      | zero => simp
      | succ a ih =>
        rw [show 2 * (a + 1) = 2 * a + 2 by ring, pow_add, Equiv.Perm.mul_apply, pow_two,
          Equiv.Perm.mul_apply, e, ih]
    have h5 : (σ ^ (p ^ k)) i = σ i := by
      rw [ha, pow_succ', Equiv.Perm.mul_apply, h4 a]
    rw [hσp i] at h5
    exact h12 h5.symm
  by_cases hab : D.cartan i (σ i) = 0
  · exact ⟨0, 1, by simpa using h12.symm, by simpa using hab⟩
  · by_cases hac : D.cartan i (σ (σ i)) = 0
    · exact ⟨0, 2, by simpa [pow_two] using h13.symm, by simpa [pow_two] using hac⟩
    · refine ⟨1, 2, by simpa [pow_two] using h23.symm, ?_⟩
      have := D.isFiniteType.apply_eq_zero_of_apply_ne_zero h12.symm h13.symm h23.symm hab hac
      simpa [pow_two] using this


theorem caseB (h : BorelQuotient D n H π M) (hZ : Subgroup.center Y = ⊥)
    (hker : ∀ j, π.ker ⊓ rankOne D.rootGroup j = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : ∀ j, p ∣ Nat.card ↥(rankOne D.rootGroup j))
    (hcent : ∀ j k : Fin D.rank, j ≠ k → Subgroup.center ↥(rankOne D.rootGroup j) = ⊥ ∨
      Subgroup.center ↥(rankOne D.rootGroup k) = ⊥)
    (c : MulAut Y) (hc : ∃ k : ℕ, orderOf c = p ^ k)
    (hcS : ((posUnipotent D).map π).map c.toMonoidHom = (posUnipotent D).map π) (i : Fin D.rank)
    (hmove : nodePerm h c hcS i ≠ i) :
    2 ≤ CFSG.Open.pRank p
      (((unipJ D {i}).map π).map (MulAut.conj : Y →* MulAut Y) ⊔ Subgroup.zpowers c) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    conj_injective_of_center_eq_bot hZ
  obtain ⟨s, t, hst, hcart⟩ := exists_nonadjacent_orbit h hp hp2 c hc hcS i hmove
  set σ : Equiv.Perm (Fin D.rank) := nodePerm h c hcS with hσ
  set x : Fin D.rank := (σ ^ s) i with hx
  set y : Fin D.rank := (σ ^ t) i with hy
  set J : Subgroup (MulAut Y) :=
    ((unipJ D {i}).map π).map (MulAut.conj : Y →* MulAut Y) ⊔ Subgroup.zpowers c with hJ
  have hdx : p ∣ Nat.card ↥((rankOne D.rootGroup x).map π) := by
    rw [natCard_map_rankOne x (hker x)]
    exact hpL x
  have hdy : p ∣ Nat.card ↥((rankOne D.rootGroup y).map π) := by
    rw [natCard_map_rankOne y (hker y)]
    exact hpL y
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hdx
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' p hdy
  have ha' : orderOf (a : Y) = p := by rw [Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf (b : Y) = p := by rw [Subgroup.orderOf_coe]; exact hb
  obtain ⟨u, hu, hua⟩ := a.2
  obtain ⟨v, hv, hvb⟩ := b.2
  have hcomm : Commute (a : Y) (b : Y) := by
    have := Levi.rankOne_commute h.ct h.extras hst hcart hu hv
    show (a : Y) * (b : Y) = (b : Y) * (a : Y)
    rw [← hua, ← hvb, ← map_mul, ← map_mul, this]
  have hnot : (b : Y) ∉ Subgroup.zpowers (a : Y) := by
    intro hmem
    have h1 : (b : Y) ∈ (rankOne D.rootGroup x).map π :=
      (Subgroup.zpowers_le.2 a.2) hmem
    have h2 : (b : Y) ∈ (rankOne D.rootGroup y).map π := b.2
    have h3 := map_rankOne_inf_eq_bot h hst hcart (hcent x y hst)
    have h4 : (b : Y) ∈ (rankOne D.rootGroup x).map π ⊓ (rankOne D.rootGroup y).map π := ⟨h1, h2⟩
    rw [h3, Subgroup.mem_bot] at h4
    have : orderOf (b : Y) = 1 := by rw [h4]; exact orderOf_one
    rw [hb'] at this
    exact hp.one_lt.ne' this
  have hmemJ : ∀ (m : ℕ) (z : Y), z ∈ (unipJ D {(σ ^ m) i}).map π →
      (MulAut.conj z : MulAut Y) ∈ J := by
    intro m z hz
    rw [← map_unipJ_pow_nodePerm h c hcS i m] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have h1 : (MulAut.conj ((c ^ m).toMonoidHom w) : MulAut Y) =
        c ^ m * MulAut.conj w * (c ^ m)⁻¹ := (mulAut_mul_conj_mul_inv (c ^ m) w).symm
    rw [h1]
    have hcm : c ^ m ∈ J := Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) m)
    exact J.mul_mem (J.mul_mem hcm (Subgroup.mem_sup_left ⟨w, hw, rfl⟩)) (J.inv_mem hcm)
  have haJ : (MulAut.conj (a : Y) : MulAut Y) ∈ J :=
    hmemJ s _ (Subgroup.map_mono (rankOne_le_unipJ (Set.mem_singleton _)) a.2)
  have hbJ : (MulAut.conj (b : Y) : MulAut Y) ∈ J :=
    hmemJ t _ (Subgroup.map_mono (rankOne_le_unipJ (Set.mem_singleton _)) b.2)
  refine two_le_pRank_of_commuting hp haJ hbJ ?_ ?_ ?_ ?_
  · rw [orderOf_injective _ hinj]
    exact ha'
  · rw [orderOf_injective _ hinj]
    exact hb'
  · exact hcomm.map _
  · intro hmem
    apply hnot
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine ⟨m, hinj ?_⟩
    rw [map_zpow]
    exact hm

end Orbit

end CaseB

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
