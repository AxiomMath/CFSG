module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks3
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)
open scoped DirectSum CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
variable {p : ℕ}

theorem eq_one_of_blockEnd_eq_one (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D : Hyperplane A p}
    (h : blockEnd A hp hpF hA t ht D = 1) : blockSpace A D.1 = ⊥ := by
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfix : (t D : V ≃ₗ[F] V) v = v := by
    have h1 := blockEnd_apply_mem A hp hpF hA t ht D hv
    rw [h] at h1
    simpa using h1.symm
  exact hv0 (eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) hv hfix)

theorem eq_closure_blockEnd_of_pRank_le (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    [Finite (V ≃ₗ[F] V)] {k : ℕ} (hk : Nat.card ↥A = p ^ k)
    {H : Subgroup (V ≃ₗ[F] V)} (hAH : A ≤ H) (hHH : CFSG.Open.pRank p H ≤ k)
    (htH : ∀ D, blockEnd A hp hpF hA t ht D ∈ H) :
    A = Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_antisymm (le_closure_blockEnd A hp hpF hA t ht) ?_
  refine (Subgroup.closure_le A).mpr (Set.range_subset_iff.mpr fun D => ?_)
  by_contra hmem
  set x : V ≃ₗ[F] V := blockEnd A hp hpF hA t ht D with hxdef
  have hxH : x ∈ H := htH D
  have hx1 : x ≠ 1 := by
    intro h
    exact hmem (by rw [h]; exact Subgroup.one_mem A)
  have hxpow : x ^ p = 1 := blockEnd_pow A hp hpF hA t ht D
  have hcardZ : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hxpow hx1
  have hdisj : A ⊓ Subgroup.zpowers x = ⊥ := by
    have hle : A ⊓ Subgroup.zpowers x ≤ Subgroup.zpowers x := inf_le_right
    have hdvd : Nat.card ↥(A ⊓ Subgroup.zpowers x) ∣ p := by
      have h := Subgroup.card_subgroup_dvd_card
        ((A ⊓ Subgroup.zpowers x).subgroupOf (Subgroup.zpowers x))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardZ] at h
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : A ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hp', hcardZ]))
      have hx : x ∈ A ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
      exact hmem hx.1
  have hzH : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hxH
  have hcomm : ∀ a : ↥A, ∀ b : ↥(Subgroup.zpowers x),
      Commute ((Subgroup.inclusion hAH a : ↥H) : V ≃ₗ[F] V)
        ((Subgroup.inclusion hzH b : ↥H) : V ≃ₗ[F] V) := by
    intro a b
    have hcent : Subgroup.zpowers x ≤ Subgroup.centralizer ({(a : V ≃ₗ[F] V)} : Set (V ≃ₗ[F] V)) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact blockEnd_commute A hp hpF hA t ht D a
    exact Subgroup.mem_centralizer_iff.mp (hcent b.2) _ (Set.mem_singleton _)
  let f : ↥A × ↥(Subgroup.zpowers x) →* ↥H :=
    MonoidHom.noncommCoprod (Subgroup.inclusion hAH) (Subgroup.inclusion hzH)
      (fun m n => Subtype.ext (hcomm m n).eq)
  have hker : ∀ z : ↥A × ↥(Subgroup.zpowers x), f z = 1 → z = 1 := by
    rintro ⟨a, b⟩ hz
    have hzV : (a : V ≃ₗ[F] V) * (b : V ≃ₗ[F] V) = 1 := by
      have h := congrArg (fun w : ↥H => (w : V ≃ₗ[F] V)) hz
      exact h
    have hav : (a : V ≃ₗ[F] V) = (b : V ≃ₗ[F] V)⁻¹ := by
      have h2 : (a : V ≃ₗ[F] V) * (b : V ≃ₗ[F] V) * (b : V ≃ₗ[F] V)⁻¹ = 1 * (b : V ≃ₗ[F] V)⁻¹ := by
        rw [hzV]
      rwa [mul_assoc, mul_inv_cancel, mul_one, one_mul] at h2
    have hmem' : (a : V ≃ₗ[F] V) ∈ A ⊓ Subgroup.zpowers x := by
      refine ⟨a.2, ?_⟩
      rw [hav]
      exact Subgroup.inv_mem _ b.2
    rw [hdisj] at hmem'
    have ha1 : (a : V ≃ₗ[F] V) = 1 := Subgroup.mem_bot.mp hmem'
    have hb1 : (b : V ≃ₗ[F] V) = 1 := by
      rw [ha1, one_mul] at hzV
      exact hzV
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hf_inj : Function.Injective f := by
    intro z w hzw
    have h : f (z * w⁻¹) = 1 := by rw [map_mul, map_inv, hzw, mul_inv_cancel]
    have h' := hker _ h
    rwa [mul_inv_eq_one] at h'
  have hcardprod : Nat.card (↥A × ↥(Subgroup.zpowers x)) = p ^ (k + 1) := by
    rw [Nat.card_prod, hk, hcardZ, pow_succ]
  have hzcomm : ∀ b1 b2 : ↥(Subgroup.zpowers x), b1 * b2 = b2 * b1 := by
    intro b1 b2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp b1.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b2.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn]
    exact zpow_mul_comm x m n
  have hpcomm : ∀ z w : ↥A × ↥(Subgroup.zpowers x), z * w = w * z := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩
    haveI : IsMulCommutative ↥A := hA.1
    exact Prod.ext (mul_comm' a1 a2) (hzcomm b1 b2)
  have hppow : ∀ z : ↥A × ↥(Subgroup.zpowers x), z ^ p = 1 := by
    rintro ⟨a, b⟩
    refine Prod.ext ?_ ?_
    · exact pow_eq_one A hA a
    · have h1 : b ^ Nat.card ↥(Subgroup.zpowers x) = 1 := pow_card_eq_one'
      rwa [hcardZ] at h1
  have hle := CFSG.SectionRank.le_pRank_of_injective (G := ↥H) (p := p) hp.one_lt hpcomm hppow
    hcardprod f hf_inj le_top
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H] at hle
  omega

theorem card_closure_finset_le_pow {G : Type*} [Group G] [Finite G] (s : Finset G)
    {p : ℕ} (hp : p.Prime) (hpow : ∀ x ∈ s, x ^ p = 1)
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    Nat.card ↥(Subgroup.closure (↑s : Set G)) ≤ p ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hpow' : ∀ x ∈ s, x ^ p = 1 := fun x hx => hpow x (Finset.mem_insert_of_mem hx)
    have hcomm' : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := fun x hx y hy =>
      hcomm x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
    have hih := ih hpow' hcomm'
    have hcl : Subgroup.closure (↑(insert a s) : Set G) =
        Subgroup.closure (↑s : Set G) ⊔ Subgroup.zpowers a := by
      refine le_antisymm ?_ (sup_le (Subgroup.closure_mono (by
        intro z hz; exact Finset.mem_insert_of_mem hz)) (Subgroup.zpowers_le.mpr ?_))
      · refine (Subgroup.closure_le _).mpr ?_
        intro z hz
        have hz' : z = a ∨ z ∈ s := by simpa using hz
        rcases hz' with rfl | hz'
        · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
        · exact Subgroup.mem_sup_left (Subgroup.subset_closure hz')
      · exact Subgroup.subset_closure (Finset.mem_insert_self a s)
    have hLR : ∀ x ∈ Subgroup.closure (↑s : Set G), ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
      intro x hx y hy
      have hLx : x ∈ Subgroup.centralizer ({a} : Set G) := by
        have hle : Subgroup.closure (↑s : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
          refine (Subgroup.closure_le _).mpr ?_
          intro z hz
          exact Subgroup.mem_centralizer_iff.mpr (fun w hw => by
            rw [Set.mem_singleton_iff] at hw
            rw [hw]
            exact (hcomm z (Finset.mem_insert_of_mem hz) a (Finset.mem_insert_self a s)).symm)
        exact hle hx
      have hax : a ∈ Subgroup.centralizer ({x} : Set G) :=
        Subgroup.mem_centralizer_iff.mpr (fun w hw => by
          rw [Set.mem_singleton_iff] at hw
          rw [hw]
          exact (Subgroup.mem_centralizer_iff.mp hLx a (Set.mem_singleton a)).symm)
      exact Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hax) hy) x (Set.mem_singleton x)
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.closure (↑s : Set G)) (Subgroup.zpowers a) hLR).1
    have hR : Nat.card ↥(Subgroup.zpowers a) ≤ p := by
      rw [Nat.card_zpowers]
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_iff_pow_eq_one.mpr
        (hpow a (Finset.mem_insert_self a s))) with h1 | h1
      · rw [h1]; exact hp.one_lt.le
      · rw [h1]
    calc Nat.card ↥(Subgroup.closure (↑(insert a s) : Set G))
        = Nat.card ↥(Subgroup.closure (↑s : Set G) ⊔ Subgroup.zpowers a) := by rw [hcl]
      _ ≤ Nat.card ↥(Subgroup.closure (↑s : Set G) ⊔ Subgroup.zpowers a) *
            Nat.card ↥(Subgroup.closure (↑s : Set G) ⊓ Subgroup.zpowers a) :=
          Nat.le_mul_of_pos_right _ Nat.card_pos
      _ = Nat.card ↥(Subgroup.closure (↑s : Set G)) * Nat.card ↥(Subgroup.zpowers a) := hcard
      _ ≤ p ^ s.card * p := Nat.mul_le_mul hih hR
      _ = p ^ (s.card + 1) := by rw [pow_succ]
      _ = p ^ (insert a s).card := by rw [Finset.card_insert_of_notMem ha]

theorem card_le_card_ne_bot_blockSpace (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    [Finite (V ≃ₗ[F] V)] {k : ℕ} (hk : Nat.card ↥A = p ^ k)
    {H : Subgroup (V ≃ₗ[F] V)} (hAH : A ≤ H) (hHH : CFSG.Open.pRank p H ≤ k)
    (htH : ∀ D, blockEnd A hp hpF hA t ht D ∈ H) :
    k ≤ Nat.card {D : Hyperplane A p // blockSpace A D.1 ≠ ⊥} := by
  classical
  have hAeq := eq_closure_blockEnd_of_pRank_le A hp hpF hA t ht hk hAH hHH htH
  have htriv : ∀ D : Hyperplane A p, blockSpace A D.1 = ⊥ →
      blockEnd A hp hpF hA t ht D = 1 := by
    intro D hD
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, r, hcu, rfl⟩ :=
      exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
    have hu : (u : V) = 0 := by
      have h : (u : V) ∈ (⊥ : Submodule F V) := by rw [← hD]; exact u.2
      simpa using h
    have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
      rw [LinearMap.mem_ker]; exact r.2
    rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
      blockEnd_apply_of_ker A hp hpF hA t ht D hr, hu]
    simp
  have hmemA : ∀ D : Hyperplane A p, blockEnd A hp hpF hA t ht D ∈ A := fun D =>
    hAeq.ge (Subgroup.subset_closure ⟨D, rfl⟩)
  set T : Finset ↥A := Finset.univ.image
    (fun D : {D : Hyperplane A p // blockSpace A D.1 ≠ ⊥} =>
      (⟨blockEnd A hp hpF hA t ht D.1, hmemA D.1⟩ : ↥A)) with hTdef
  have htop : Subgroup.closure (↑T : Set ↥A) = ⊤ := by
    refine eq_top_iff.mpr fun a _ => ?_
    have ha : (a : V ≃ₗ[F] V) ∈
        Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht)) := hAeq.le a.2
    have hle : Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht)) ≤
        (Subgroup.closure (↑T : Set ↥A)).map A.subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨D, rfl⟩
      by_cases hD : blockSpace A D.1 = ⊥
      · rw [htriv D hD]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_map.mpr ⟨⟨_, hmemA D⟩, Subgroup.subset_closure
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨D, hD⟩, Finset.mem_univ _, rfl⟩)), rfl⟩
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp (hle ha)
    rw [show b = a from Subtype.ext hba] at hb
    exact hb
  have hpow : ∀ x ∈ T, x ^ p = 1 := by
    intro x hx
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hx
    exact pow_eq_one A hA _
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x _ y _
    haveI : IsMulCommutative ↥A := hA.1
    exact mul_comm' x y
  have hcard₂ := card_closure_finset_le_pow T hp hpow hcomm
  have hcard₃ : T.card ≤ Nat.card {D : Hyperplane A p // blockSpace A D.1 ≠ ⊥} := by
    have h1 : T.card ≤ (Finset.univ : Finset
        {D : Hyperplane A p // blockSpace A D.1 ≠ ⊥}).card := Finset.card_image_le
    simpa [Finset.card_univ, Nat.card_eq_fintype_card] using h1
  have hbound : p ^ k ≤ p ^ Nat.card {D : Hyperplane A p // blockSpace A D.1 ≠ ⊥} := by
    have h1 : Nat.card ↥(Subgroup.closure (↑T : Set ↥A)) = Nat.card ↥A := by
      rw [htop]
      exact Nat.card_congr (Subgroup.topEquiv (G := ↥A)).toEquiv
    rw [← hk, ← h1]
    exact hcard₂.trans (Nat.pow_le_pow_right hp.pos hcard₃)
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hbound

def fixedByEnd (x : V ≃ₗ[F] V) : Submodule F V := Module.End.eigenspace x.toLinearMap 1

@[simp] theorem mem_fixedByEnd {x : V ≃ₗ[F] V} {v : V} : v ∈ fixedByEnd x ↔ x v = v := by
  simp [fixedByEnd, Module.End.mem_eigenspace_iff]

theorem finrank_ker_projBlock_add_finrank_blockSpace [FiniteDimensional F V] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) (D : Hyperplane A p) :
    Module.finrank F ↥(LinearMap.ker (projBlock A hp hpF hA D)) +
      Module.finrank F ↥(blockSpace A D.1) = Module.finrank F V :=
  Submodule.finrank_add_eq_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D).symm

theorem blockSpace_le_fixedByEnd_inf (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D E G : Hyperplane A p}
    (hGD : G ≠ D) (hGE : G ≠ E) :
    blockSpace A G.1 ≤ fixedByEnd (blockEnd A hp hpF hA t ht D) ⊓
      fixedByEnd (blockEnd A hp hpF hA t ht E) := by
  intro v hv
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_fixedByEnd]
    exact blockEnd_apply_of_mem_block A hp hpF hA t ht (D := D) (E := G) hGD hv
  · rw [mem_fixedByEnd]
    exact blockEnd_apply_of_mem_block A hp hpF hA t ht (D := E) (E := G) hGE hv

theorem finrank_blockSpace_le_finrank_fixedByEnd_inf [FiniteDimensional F V] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A)
    (ht : ∀ D, t D ∉ D.1) {D E G : Hyperplane A p} (hGD : G ≠ D) (hGE : G ≠ E) :
    Module.finrank F ↥(blockSpace A G.1) ≤
      Module.finrank F ↥(fixedByEnd (blockEnd A hp hpF hA t ht D) ⊓
        fixedByEnd (blockEnd A hp hpF hA t ht E)) :=
  Submodule.finrank_mono (blockSpace_le_fixedByEnd_inf A hp hpF hA t ht hGD hGE)

theorem three_mul_finrank_blockSpace_le [FiniteDimensional F V] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) {D E G : Hyperplane A p}
    (hDE : D ≠ E) (hDG : D ≠ G) (hEG : E ≠ G)
    (hDE' : Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F ↥(blockSpace A E.1))
    (hDG' : Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F ↥(blockSpace A G.1)) :
    3 * Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F V := by
  classical
  have hdisj : ∀ i : Hyperplane A p, Disjoint (blockSpace A i.1)
      (⨆ j, ⨆ (_ : j ≠ i), blockSpace A j.1) := iSupIndep_def.mp (iSupIndep_blockSpace A hp hpF hA)
  have hEGbot : blockSpace A E.1 ⊓ blockSpace A G.1 = ⊥ := by
    have h := disjoint_iff_inf_le.mp (hdisj E)
    refine le_bot_iff.mp (le_trans ?_ h)
    exact inf_le_inf_left _ (le_iSup₂ (f := fun j (_ : j ≠ E) => blockSpace A j.1) G (Ne.symm hEG))
  have hDbot : blockSpace A D.1 ⊓ (blockSpace A E.1 ⊔ blockSpace A G.1) = ⊥ := by
    have h := disjoint_iff_inf_le.mp (hdisj D)
    refine le_bot_iff.mp (le_trans ?_ h)
    refine inf_le_inf_left _ (sup_le ?_ ?_)
    · exact le_iSup₂ (f := fun j (_ : j ≠ D) => blockSpace A j.1) E (Ne.symm hDE)
    · exact le_iSup₂ (f := fun j (_ : j ≠ D) => blockSpace A j.1) G (Ne.symm hDG)
  have hEG : Module.finrank F ↥(blockSpace A E.1 ⊔ blockSpace A G.1) =
      Module.finrank F ↥(blockSpace A E.1) + Module.finrank F ↥(blockSpace A G.1) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (blockSpace A E.1) (blockSpace A G.1)
    rw [hEGbot, finrank_bot, add_zero] at h
    omega
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (blockSpace A D.1)
    (blockSpace A E.1 ⊔ blockSpace A G.1)
  rw [hDbot, finrank_bot, add_zero, hEG] at hsup
  have hle : Module.finrank F ↥(blockSpace A D.1 ⊔ (blockSpace A E.1 ⊔ blockSpace A G.1)) ≤
      Module.finrank F V := by
    have h := Submodule.finrank_mono (le_top : blockSpace A D.1 ⊔
      (blockSpace A E.1 ⊔ blockSpace A G.1) ≤ (⊤ : Submodule F V))
    rwa [finrank_top] at h
  omega

theorem two_mul_finrank_le_three_mul_finrank_fixedByEnd [FiniteDimensional F V] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A)
    (ht : ∀ D, t D ∉ D.1) {D E G : Hyperplane A p} (hDE : D ≠ E) (hDG : D ≠ G) (hEG : E ≠ G)
    (hDE' : Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F ↥(blockSpace A E.1))
    (hDG' : Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F ↥(blockSpace A G.1)) :
    2 * Module.finrank F V ≤ 3 * Module.finrank F ↥(fixedByEnd (blockEnd A hp hpF hA t ht D)) := by
  have hthree := three_mul_finrank_blockSpace_le A hp hpF hA hDE hDG hEG hDE' hDG'
  have hker : fixedByEnd (blockEnd A hp hpF hA t ht D) =
      LinearMap.ker (projBlock A hp hpF hA D) := by
    refine le_antisymm ?_ ?_
    · intro v hv
      rw [mem_fixedByEnd] at hv
      obtain ⟨u, r, hcu, rfl⟩ :=
        exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
      have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
        rw [LinearMap.mem_ker]; exact r.2
      have h1 : blockEnd A hp hpF hA t ht D ((u : V) + (r : V)) =
          (t D : V ≃ₗ[F] V) (u : V) + (r : V) := by
        rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
          blockEnd_apply_of_ker A hp hpF hA t ht D hr]
      rw [h1] at hv
      have h2 : (t D : V ≃ₗ[F] V) (u : V) = (u : V) := add_right_cancel hv
      have h3 : (u : V) = 0 := eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) u.2 h2
      rw [LinearMap.mem_ker, map_add, projBlock_apply_of_mem A hp hpF hA D u.2,
        LinearMap.mem_ker.mp hr, h3]
      simp
    · intro v hv
      rw [mem_fixedByEnd]
      exact blockEnd_apply_of_ker A hp hpF hA t ht D (by rw [LinearMap.mem_ker]; exact hv)
  have hdim := finrank_ker_projBlock_add_finrank_blockSpace A hp hpF hA D
  rw [← hker] at hdim
  omega

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

