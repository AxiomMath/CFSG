module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NPi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NTrans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open
open scoped commutatorElement

section Good

variable {A S : Type*} [Group A] [Group S]

@[expose] def GoodA (ρ : A →* MulAut S) (H : Subgroup S) : Prop :=
  ∀ P : Subgroup S, P ≤ fixA ρ ⊓ H → ⁅P, P⁆ = P → P ≤ GLALayer (fixA ρ ⊓ H)

theorem isSubnormal_of_commutator_le {V N : Subgroup S} (hNV : N ≤ V) (hcomm : ⁅V, V⁆ ≤ N) :
    IsSubnormal N V := by
  refine IsSubnormal.step hNV ⟨fun n hn g => ?_⟩ (IsSubnormal.refl V)
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : S) * (n : S) * (g : S)⁻¹ = ⁅(g : S), (n : S)⁆ * (n : S) := by
    rw [commutatorElement_def]
    group
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]
  exact N.mul_mem (hcomm (Subgroup.commutator_mem_commutator g.2 n.2)) hn

theorem isSubnormal_inf_of_normal {G : Type*} [Group G] (W K : Subgroup G) [K.Normal] :
    IsSubnormal (W ⊓ K) W := by
  refine IsSubnormal.step inf_le_left ⟨fun n hn g => ?_⟩ (IsSubnormal.refl W)
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnW, hnK⟩ := Subgroup.mem_inf.1 hn
  exact Subgroup.mem_inf.2 ⟨W.mul_mem (W.mul_mem g.2 hnW) (W.inv_mem g.2),
    Subgroup.Normal.conj_mem inferInstance _ hnK _⟩

@[expose] def coordKer {ι : Type*} [DecidableEq ι] (H : ι → Subgroup S) (i : ι) :
    Subgroup (∀ j, ↥(H j)) where
  carrier := {f | ∀ j, j ≠ i → f j = 1}
  one_mem' := fun j _ => Pi.one_apply j
  mul_mem' := fun {f g} hf hg j hj => by
    simp [Pi.mul_apply, hf j hj, hg j hj]
  inv_mem' := fun {f} hf j hj => by
    simp [Pi.inv_apply, hf j hj]

theorem coordKer_normal {ι : Type*} [DecidableEq ι] (H : ι → Subgroup S) (i : ι) :
    (coordKer H i).Normal := by
  refine ⟨fun n hn g j hj => ?_⟩
  have hn' : ∀ j, j ≠ i → n j = 1 := hn
  simp [Pi.mul_apply, Pi.inv_apply, hn' j hj]

@[expose] def coordPr {ι : Type*} (H : ι → Subgroup S) (i : ι) : (∀ j, ↥(H j)) →* S :=
  (H i).subtype.comp (Pi.evalMonoidHom (fun j => ↥(H j)) i)

theorem coordPr_apply {ι : Type*} (H : ι → Subgroup S) (i : ι) (f : ∀ j, ↥(H j)) :
    coordPr H i f = (f i : S) := rfl

theorem good_of_upstairs [Finite S] {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : A →* MulAut S)
    (H : ι → Subgroup S) (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y)
    (σ : A →* Equiv.Perm ι) (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i))
    (hup : ∀ Q : Subgroup (∀ j, ↥(H j)), Q ≤ fixA (coordHom ρ H σ hmap) → ⁅Q, Q⁆ = Q →
      Q ≤ GLALayer (fixA (coordHom ρ H σ hmap))) :
    GoodA ρ (⨆ i, H i) := by
  intro P hP hPp
  have hk : ∀ g : (∀ j, ↥(H j)), piProd H hcomm g = 1 → g ∈ Subgroup.center (∀ j, ↥(H j)) :=
    fun g hg => piProd_ker_central H hcomm hg
  have hc : ∀ (a : A) (x : ∀ j, ↥(H j)),
      piProd H hcomm (coordHom ρ H σ hmap a x) = ρ a (piProd H hcomm x) :=
    fun a x => piProd_coordHom ρ H hcomm σ hmap a x
  have hr : (piProd H hcomm).range = ⨆ i, H i := piProd_range H hcomm
  have hPr : P ≤ fixA ρ ⊓ (piProd H hcomm).range := by
    rw [hr]
    exact hP
  obtain ⟨Q, hQW, hQp, hQP⟩ := exists_perfect_lift hc hk hPr hPp
  have hQL : Q ≤ GLALayer (fixA (coordHom ρ H σ hmap)) := hup Q hQW hQp
  have hNV : (fixA (coordHom ρ H σ hmap)).map (piProd H hcomm) ≤
      fixA ρ ⊓ (piProd H hcomm).range := by
    rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, MonoidHom.mem_range.2 ⟨w, rfl⟩⟩
    rw [mem_fixA]
    intro a
    rw [← hc a w, mem_fixA.1 hw a]
  have hsub : IsSubnormal ((fixA (coordHom ρ H σ hmap)).map (piProd H hcomm))
      (fixA ρ ⊓ (piProd H hcomm).range) :=
    isSubnormal_of_commutator_le hNV (commutator_fixA_le_map hk hc)
  have hP2 : P ≤ GLALayer (fixA ρ ⊓ (piProd H hcomm).range) := by
    calc P = Q.map (piProd H hcomm) := hQP.symm
      _ ≤ (GLALayer (fixA (coordHom ρ H σ hmap))).map (piProd H hcomm) := Subgroup.map_mono hQL
      _ ≤ GLALayer ((fixA (coordHom ρ H σ hmap)).map (piProd H hcomm)) :=
          GLALayer_map_le _ hk _
      _ ≤ GLALayer (fixA ρ ⊓ (piProd H hcomm).range) := GLALayer_mono_of_isSubnormal hsub
  rw [hr] at hP2
  exact hP2

theorem one_symm_apply {ι : Type*} (a : A) (k : ι) :
    ((1 : A →* Equiv.Perm ι) a).symm k = k := rfl

theorem hmap_one {ι : Type*} (ρ : A →* MulAut S) (H : ι → Subgroup S)
    (hinv : ∀ a i, (H i).map (ρ a).toMonoidHom = H i) :
    ∀ a i, (H i).map (ρ a).toMonoidHom = H (((1 : A →* Equiv.Perm ι) a) i) := by
  intro a i
  rw [MonoidHom.one_apply, Equiv.Perm.one_apply]
  exact hinv a i

@[expose] def stabSub {ι : Type*} (σ : A →* Equiv.Perm ι) (i₀ : ι) : Subgroup A where
  carrier := {a | (σ a) i₀ = i₀}
  one_mem' := by
    show (σ 1) i₀ = i₀
    rw [map_one, Equiv.Perm.one_apply]
  mul_mem' := fun {a b} ha hb => by
    show (σ (a * b)) i₀ = i₀
    have ha' : (σ a) i₀ = i₀ := ha
    have hb' : (σ b) i₀ = i₀ := hb
    rw [map_mul, Equiv.Perm.mul_apply, hb', ha']
  inv_mem' := fun {a} ha => by
    show (σ a⁻¹) i₀ = i₀
    have ha' : (σ a) i₀ = i₀ := ha
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq, ha']

theorem mem_stabSub {ι : Type*} (σ : A →* Equiv.Perm ι) (i₀ : ι) (a : A) :
    a ∈ stabSub σ i₀ ↔ (σ a) i₀ = i₀ := Iff.rfl

theorem upstairs_coord [Finite S] {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : A →* MulAut S)
    (H : ι → Subgroup S) (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y)
    (hinv : ∀ a i, (H i).map (ρ a).toMonoidHom = H i) (hfac : ∀ i, GoodA ρ (H i))
    (Q : Subgroup (∀ j, ↥(H j)))
    (hQ : Q ≤ fixA (coordHom ρ H 1 (hmap_one ρ H hinv))) (hQp : ⁅Q, Q⁆ = Q) :
    Q ≤ GLALayer (fixA (coordHom ρ H 1 (hmap_one ρ H hinv))) := by
  have hm := hmap_one ρ H hinv
  have hfixc : ∀ f ∈ fixA (coordHom ρ H 1 hm), ∀ i (a : A), ρ a (f i : S) = f i := by
    intro f hf i a
    have h1 : coordFun ρ H 1 hm a f = f := mem_fixA.1 hf a
    have h2 := congrArg (fun g : (∀ j, ↥(H j)) => ((g i : ↥(H i)) : S)) h1
    rw [coordFun_apply, one_symm_apply] at h2
    exact h2
  have hXi : ∀ i, (fixA (coordHom ρ H 1 hm) ⊓ coordKer H i).map (coordPr H i) =
      fixA ρ ⊓ H i := by
    intro i
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxW, _⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨?_, (x i).2⟩
      rw [mem_fixA]
      intro a
      exact hfixc x hxW i a
    · intro hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
      refine ⟨Pi.mulSingle i ⟨y, hy2⟩, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
      · rw [mem_fixA]
        intro a
        funext k
        apply Subtype.ext
        show ((coordFun ρ H 1 hm a (Pi.mulSingle (M := fun j => ↥(H j)) i (⟨y, hy2⟩ : ↥(H i))) k :
          ↥(H k)) : S) = ((Pi.mulSingle (M := fun j => ↥(H j)) i (⟨y, hy2⟩ : ↥(H i)) k : ↥(H k)) : S)
        rw [coordFun_apply, one_symm_apply]
        by_cases hk : k = i
        · subst hk
          simp only [Pi.mulSingle_eq_same]
          exact mem_fixA.1 hy1 a
        · simp [Pi.mulSingle_apply, hk]
      · intro j hj
        simp [Pi.mulSingle_apply, hj]
      · rw [coordPr_apply, Pi.mulSingle_eq_same]
  have hinjc : ∀ i, ∀ x ∈ fixA (coordHom ρ H 1 hm) ⊓ coordKer H i, coordPr H i x = 1 → x = 1 := by
    intro i x hx hx1
    obtain ⟨_, hxK⟩ := Subgroup.mem_inf.1 hx
    funext j
    by_cases hj : j = i
    · subst hj
      exact Subtype.ext hx1
    · exact hxK j hj
  have hLi : ∀ i, ∀ q ∈ Q, Pi.mulSingle i (q i) ∈ GLALayer (fixA (coordHom ρ H 1 hm)) := by
    intro i q hq
    have hpq : Q.map (coordPr H i) ≤ fixA ρ ⊓ H i := by
      rintro _ ⟨x, hx, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, (x i).2⟩
      rw [mem_fixA]
      intro a
      exact hfixc x (hQ hx) i a
    have hperf : ⁅Q.map (coordPr H i), Q.map (coordPr H i)⁆ = Q.map (coordPr H i) := by
      rw [← Subgroup.map_commutator, hQp]
    have hL := hfac i _ hpq hperf
    rw [← hXi i] at hL
    have hILL := layer_map_ge_of_injOn (coordPr H i) (hinjc i)
    have hq' : coordPr H i q ∈ (GLALayer (fixA (coordHom ρ H 1 hm) ⊓ coordKer H i)).map
        (coordPr H i) := hILL (hL (Subgroup.mem_map_of_mem _ hq))
    obtain ⟨g, hg, hgq⟩ := Subgroup.mem_map.1 hq'
    have hgX : g ∈ fixA (coordHom ρ H 1 hm) ⊓ coordKer H i := GLALayer_le _ hg
    have hgi : g = Pi.mulSingle i (q i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Pi.mulSingle_eq_same]
        exact Subtype.ext hgq
      · have hgj : g j = 1 := (Subgroup.mem_inf.1 hgX).2 j hj
        rw [hgj, Pi.mulSingle_eq_of_ne hj]
    haveI := coordKer_normal H i
    have hmono := GLALayer_mono_of_isSubnormal
      (isSubnormal_inf_of_normal (fixA (coordHom ρ H 1 hm)) (coordKer H i))
    rw [← hgi] at *
    exact hmono hg
  intro q hq
  have hq_eq := (Finset.noncommProd_mulSingle q).symm
  rw [hq_eq]
  apply Subgroup.noncommProd_mem
  intro i _
  exact hLi i q hq

theorem upstairs_transitive [Finite S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : A →* MulAut S) (H : ι → Subgroup S)
    (σ : A →* Equiv.Perm ι) (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i))
    (i₀ : ι) (htrans : ∀ j, ∃ a, (σ a) i₀ = j)
    (hgood : GoodA (ρ.comp (stabSub σ i₀).subtype) (H i₀))
    (Q : Subgroup (∀ j, ↥(H j))) (hQ : Q ≤ fixA (coordHom ρ H σ hmap)) (hQp : ⁅Q, Q⁆ = Q) :
    Q ≤ GLALayer (fixA (coordHom ρ H σ hmap)) := by
  set W := fixA (coordHom ρ H σ hmap) with hW
  set Φ : (∀ j, ↥(H j)) →* S := coordPr H i₀ with hΦ
  set V₁ := fixA (ρ.comp (stabSub σ i₀).subtype) ⊓ H i₀ with hV₁
  have hkey : ∀ g ∈ W, ∀ (a : A) (k : ι),
      ((g k : ↥(H k)) : S) = ρ a ((g ((σ a).symm k) : ↥(H _)) : S) := by
    intro g hg a k
    have h1 : coordFun ρ H σ hmap a g = g := mem_fixA.1 hg a
    have h2 := congrArg (fun f : (∀ j, ↥(H j)) => ((f k : ↥(H k)) : S)) h1
    rw [coordFun_apply] at h2
    exact h2.symm
  have hinj : ∀ g ∈ W, Φ g = 1 → g = 1 := by
    intro g hg hg1
    funext j
    apply Subtype.ext
    obtain ⟨c, hc⟩ := htrans j
    have h1 := hkey g hg c j
    have hsymm : (σ c).symm j = i₀ := by rw [← hc, Equiv.symm_apply_apply]
    rw [hsymm] at h1
    have hΦ' : ((g i₀ : ↥(H i₀)) : S) = 1 := hg1
    show ((g j : ↥(H j)) : S) = 1
    rw [h1, hΦ', map_one]
  have hWmap : W.map Φ = V₁ := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, (g i₀).2⟩
      rw [mem_fixA]
      intro a
      have hs : (σ (a : A)).symm i₀ = i₀ := (Equiv.symm_apply_eq (σ (a : A))).2 (a.2).symm
      have h1 := hkey g hg (a : A) i₀
      rw [hs] at h1
      show ρ (a : A) ((g i₀ : ↥(H i₀)) : S) = ((g i₀ : ↥(H i₀)) : S)
      exact h1.symm
    · intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
      have hfixE : ∀ a : A, (σ a) i₀ = i₀ → ρ a (y : S) = y := fun a ha =>
        mem_fixA.1 hy1 ⟨a, ha⟩
      choose c hc using htrans
      let g : ∀ k, ↥(H k) := fun k => ⟨ρ (c k) (y : S), by
        have h := mem_coordTarget ρ H σ hmap (c k) i₀ ⟨y, hy2⟩
        rwa [hc k] at h⟩
      have hgW : g ∈ W := by
        apply mem_fixA.2
        intro a
        funext k
        apply Subtype.ext
        show ((coordFun ρ H σ hmap a g k : ↥(H k)) : S) = ((g k : ↥(H k)) : S)
        rw [coordFun_apply]
        set m := (σ a).symm k with hm
        have hd : (σ ((c k)⁻¹ * (a * c m))) i₀ = i₀ := by
          rw [map_mul, Equiv.Perm.mul_apply, map_inv, map_mul, Equiv.Perm.mul_apply, hc m,
            Equiv.apply_symm_apply]
          exact Equiv.Perm.inv_eq_iff_eq.2 (hc k).symm
        show ρ a (ρ (c m) (y : S)) = ρ (c k) (y : S)
        calc ρ a (ρ (c m) (y : S)) = ρ (a * c m) (y : S) := by rw [map_mul, MulAut.mul_apply]
          _ = ρ (c k * ((c k)⁻¹ * (a * c m))) (y : S) := by rw [mul_inv_cancel_left]
          _ = ρ (c k) (ρ ((c k)⁻¹ * (a * c m)) (y : S)) := by rw [map_mul, MulAut.mul_apply]
          _ = ρ (c k) (y : S) := by rw [hfixE _ hd]
      refine Subgroup.mem_map.2 ⟨g, hgW, ?_⟩
      show ((g i₀ : ↥(H i₀)) : S) = y
      show ρ (c i₀) (y : S) = y
      exact hfixE _ (hc i₀)
  have hILL := layer_map_ge_of_injOn Φ hinj
  rw [hWmap] at hILL
  have hPhi : Q.map Φ ≤ V₁ := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hWmap]
    exact Subgroup.mem_map_of_mem Φ (hQ hg)
  have hperf : ⁅Q.map Φ, Q.map Φ⁆ = Q.map Φ := by
    rw [← Subgroup.map_commutator, hQp]
  have hL := hgood (Q.map Φ) hPhi hperf
  intro q hq
  have hqΦ : Φ q ∈ (GLALayer W).map Φ := hILL (hL (Subgroup.mem_map_of_mem Φ hq))
  obtain ⟨g, hgL, hgq⟩ := Subgroup.mem_map.1 hqΦ
  have hgW : g ∈ W := GLALayer_le W hgL
  have hgq1 : g⁻¹ * q = 1 := hinj (g⁻¹ * q) (W.mul_mem (W.inv_mem hgW) (hQ hq))
    (by rw [map_mul, map_inv, hgq, inv_mul_cancel])
  have hgq2 : g = q := inv_mul_eq_one.1 hgq1
  rw [← hgq2]
  exact hgL

theorem goodA_iSup_coord [Finite S] {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : A →* MulAut S)
    (H : ι → Subgroup S) (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y)
    (hinv : ∀ a i, (H i).map (ρ a).toMonoidHom = H i) (hfac : ∀ i, GoodA ρ (H i)) :
    GoodA ρ (⨆ i, H i) :=
  good_of_upstairs ρ H hcomm 1 (hmap_one ρ H hinv)
    (fun Q hQ hQp => upstairs_coord ρ H hcomm hinv hfac Q hQ hQp)

theorem goodA_iSup_transitive [Finite S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : A →* MulAut S) (H : ι → Subgroup S)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y)
    (σ : A →* Equiv.Perm ι) (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i))
    (i₀ : ι) (htrans : ∀ j, ∃ a, (σ a) i₀ = j)
    (hgood : GoodA (ρ.comp (stabSub σ i₀).subtype) (H i₀)) :
    GoodA ρ (⨆ i, H i) :=
  good_of_upstairs ρ H hcomm σ hmap
    (fun Q hQ hQp => upstairs_transitive ρ H σ hmap i₀ htrans hgood Q hQ hQp)

end Good

end CFSG.LocalAnalysis.GLTheoremA.I142N
