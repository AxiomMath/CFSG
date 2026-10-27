module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3LSound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Codes

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof Subgroup

section Helpers

variable {Γ : Type} [Group Γ] {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f12_mulE_lt (x y : ℕ) : mulE P x y < 128 := atR_lt _ _

theorem f12_ord2 (x : Γ) : orderOf x = 2 ↔ x ≠ 1 ∧ x * x = 1 := by
  rw [orderOf_eq_prime_iff, pow_two, and_comm]

theorem f12_gens {l : List ℕ} {X : Set Γ} (h : {x | x ∈ l.map elt} = X) :
    {x | ∃ g ∈ l, elt g = x} = X := by
  rw [← h]
  ext x
  simp only [Set.mem_setOf_eq, List.mem_map]

theorem f12_getD_mem {α : Type} (l : List α) (d : α) {j : ℕ} (h : j < l.length) :
    l.getD j d ∈ l := by
  rw [List.getD_eq_getElem (l := l) (d := d) h]
  exact List.getElem_mem h

theorem f12_cls_eq (T : Subgroup Γ) (y : Γ) :
    {g | ∃ x ∈ (T : Set Γ), x * y * x⁻¹ = g} = conjClass T y := by
  ext g
  simp only [conjClass, Set.mem_setOf_eq, SetLike.mem_coe]
  exact exists_congr fun t => and_congr_right fun _ => eq_comm

theorem f12_conjClass_eq {T : Subgroup Γ} {x y : Γ} (hy : y ∈ conjClass T x) :
    conjClass T y = conjClass T x := by
  obtain ⟨s, hs, hsx⟩ := hy
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * s, T.mul_mem ht hs, ?_⟩
    rw [hsx]
    group
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * s⁻¹, T.mul_mem ht (T.inv_mem hs), ?_⟩
    rw [hsx]
    group

theorem f12_prodEquiv {X U W : Subgroup Γ} (h : IsInternalDirect X U W) :
    Nonempty (↥X ≃* ↥U × ↥W) := by
  have hUV : U ⊔ W = X := h.1
  have hinf : U ⊓ W = ⊥ := h.2.1
  have hcomm : ∀ u ∈ U, ∀ v ∈ W, u * v = v * u := h.2.2
  let φ : ↥U × ↥W →* ↥X :=
    { toFun := fun p => ⟨(p.1 : Γ) * (p.2 : Γ), by
        rw [← hUV]
        exact Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩
        apply Subtype.ext
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, MonoidHom.coe_mk,
          OneHom.coe_mk]
        calc (↑u₁ * ↑u₂ : Γ) * (↑v₁ * ↑v₂)
            = ↑u₁ * (↑u₂ * ↑v₁) * ↑v₂ := by group
          _ = ↑u₁ * (↑v₁ * ↑u₂) * ↑v₂ := by rw [hcomm u₂ u₂.2 v₁ v₁.2]
          _ = ↑u₁ * ↑v₁ * (↑u₂ * ↑v₂) := by group }
  have hinj : Function.Injective φ := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ heq
    have hval : (u₁ : Γ) * (v₁ : Γ) = (u₂ : Γ) * (v₂ : Γ) := congrArg Subtype.val heq
    have hthis : (u₂ : Γ)⁻¹ * (u₁ : Γ) = (v₂ : Γ) * (v₁ : Γ)⁻¹ := by
      calc (u₂ : Γ)⁻¹ * (u₁ : Γ)
          = (u₂ : Γ)⁻¹ * ((u₁ : Γ) * (v₁ : Γ)) * (v₁ : Γ)⁻¹ := by group
        _ = (u₂ : Γ)⁻¹ * ((u₂ : Γ) * (v₂ : Γ)) * (v₁ : Γ)⁻¹ := by rw [hval]
        _ = (v₂ : Γ) * (v₁ : Γ)⁻¹ := by group
    have hmem : (u₂ : Γ)⁻¹ * u₁ ∈ U ⊓ W := by
      refine ⟨U.mul_mem (U.inv_mem u₂.2) u₁.2, ?_⟩
      rw [hthis]
      exact W.mul_mem v₂.2 (W.inv_mem v₁.2)
    have h1 : (u₂ : Γ)⁻¹ * u₁ = 1 := by
      rw [hinf] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hu : u₁ = u₂ := by
      apply Subtype.ext
      apply mul_left_cancel (a := (u₂ : Γ)⁻¹)
      rw [h1, inv_mul_cancel]
    have h2 : (v₂ : Γ) * (v₁ : Γ)⁻¹ = 1 := by rw [← hthis, h1]
    have hv : v₁ = v₂ := by
      apply Subtype.ext
      have hinv : (v₁ : Γ)⁻¹ = (v₂ : Γ)⁻¹ := by
        apply mul_left_cancel (a := (v₂ : Γ))
        rw [h2, mul_inv_cancel]
      exact inv_injective hinv
    exact Prod.ext hu hv
  have hsurj : Function.Surjective φ := by
    intro x
    let M : Subgroup Γ :=
      { carrier := {y | ∃ u ∈ U, ∃ v ∈ W, u * v = y}
        one_mem' := ⟨1, U.one_mem, 1, W.one_mem, one_mul 1⟩
        mul_mem' := by
          rintro a b ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
          refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, v₁ * v₂, W.mul_mem hv₁ hv₂, ?_⟩
          calc (u₁ * u₂ : Γ) * (v₁ * v₂)
              = u₁ * (u₂ * v₁) * v₂ := by group
            _ = u₁ * (v₁ * u₂) * v₂ := by rw [hcomm u₂ hu₂ v₁ hv₁]
            _ = (u₁ * v₁) * (u₂ * v₂) := by group
        inv_mem' := by
          rintro a ⟨u, hu, v, hv, rfl⟩
          refine ⟨u⁻¹, U.inv_mem hu, v⁻¹, W.inv_mem hv, ?_⟩
          change u⁻¹ * v⁻¹ = (u * v)⁻¹
          rw [mul_inv_rev]
          exact hcomm u⁻¹ (U.inv_mem hu) v⁻¹ (W.inv_mem hv) }
    have hle : U ⊔ W ≤ M :=
      sup_le (fun u hu => ⟨u, hu, 1, W.one_mem, mul_one u⟩)
        (fun v hv => ⟨1, U.one_mem, v, hv, one_mul v⟩)
    have hx : (x : Γ) ∈ M := hle (by rw [hUV]; exact x.2)
    obtain ⟨u, hu, v, hv, huv⟩ := hx
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext huv⟩
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

section Tables

variable (hR : RealT elt P C V Q)
include hR

theorem f12_cen {Sm : ℕ} {T : Subgroup Γ} (hS : mset elt Sm = (T : Set Γ)) {y : ℕ}
    (hy : y < 128) : mset elt (cenE P C Sm y) = (centEl T (elt y) : Set Γ) := by
  rw [cenE_mset hR Sm hy, hS]
  ext x
  simp only [centEl, Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_setOf_eq,
    Subgroup.mem_centralizer_singleton_iff]

theorem f12_clos {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 128) {R : ℕ} (hc : closOK C gs R = true)
    {X : Set Γ} (hX : {x | ∃ g ∈ gs, elt g = x} = X) :
    mset elt (closK C gs R) = (closure X : Set Γ) := by
  rw [← hX]
  exact closK_closure hR hgs hc

theorem f12_dec {Sm : ℕ} {T : Subgroup Γ} (hS : mset elt Sm = (T : Set Γ)) {c g1 g2 R : ℕ}
    (hc : c < 128) (hg1 : g1 < 128) (hg2 : g2 < 128)
    (h : z2d8K P C Q (cenE P C Sm c) c g1 g2 R = true) :
    IsZ2xD8Decomp (centEl T (elt c)) (elt c) (closure {elt g1, elt g2}) := by
  obtain ⟨hD, hne, hsq, hX, hnot, hcen, φ, hinj, hrng⟩ := z2d8K_sound hR hc hg1 hg2 h
  have hgs : {x | ∃ g ∈ [g1, g2], elt g = x} = {elt g1, elt g2} := by
    refine f12_gens ?_
    ext x
    simp only [Set.mem_setOf_eq, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hgs] at hD
  have hXset : (centEl T (elt c) : Set Γ) =
      mset elt (closK C [g1, g2] R) ∪ (elt c * ·) '' mset elt (closK C [g1, g2] R) := by
    rw [← f12_cen hR hS hc, hX]
  rw [hD] at hXset hnot hcen hrng
  have hcC : ∀ u ∈ closure ({elt c} : Set Γ), u = 1 ∨ u = elt c := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ => u = 1 ∨ u = elt c) ?_ (Or.inl rfl) ?_ ?_ hu
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact Or.inr hx
    · rintro x y - - (rfl | rfl) (rfl | rfl) <;> simp [hsq]
    · rintro x - (rfl | rfl)
      · exact Or.inl inv_one
      · exact Or.inr (inv_eq_of_mul_eq_one_right hsq)
  have hcX : elt c ∈ centEl T (elt c) := by
    have hm : elt c ∈ (centEl T (elt c) : Set Γ) := by
      rw [hXset]
      exact Or.inr ⟨1, (closure {elt g1, elt g2}).one_mem, mul_one _⟩
    exact hm
  have hDX : closure {elt g1, elt g2} ≤ centEl T (elt c) := fun d hd => by
    have hm : d ∈ (centEl T (elt c) : Set Γ) := by
      rw [hXset]
      exact Or.inl hd
    exact hm
  have hsup : closure {elt c} ⊔ closure {elt g1, elt g2} = centEl T (elt c) := by
    refine le_antisymm (sup_le ((closure_le _).2 (Set.singleton_subset_iff.2 hcX)) hDX)
      fun x hx => ?_
    have hm : x ∈ (centEl T (elt c) : Set Γ) := hx
    rw [hXset] at hm
    rcases hm with hm | ⟨d, hd, rfl⟩
    · exact mem_sup_right hm
    · exact mul_mem_sup (subset_closure rfl) hd
  have hinf : closure {elt c} ⊓ closure {elt g1, elt g2} = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [mem_inf] at hu
    rcases hcC u hu.1 with rfl | rfl
    · exact one_mem _
    · exact absurd hu.2 hnot
  have hcomm : ∀ u ∈ closure {elt c}, ∀ v ∈ closure {elt g1, elt g2}, u * v = v * u := by
    intro u hu v hv
    rcases hcC u hu with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (hcen v hv).symm
  have hord : orderOf (elt c) = 2 := (f12_ord2 _).2 ⟨hne, hsq⟩
  have hD8 : Nonempty (↥(closure {elt g1, elt g2}) ≃* DihedralGroup 4) := by
    have hr : φ.range = closure {elt g1, elt g2} :=
      SetLike.coe_injective (by rw [MonoidHom.coe_range, hrng])
    exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)).symm⟩
  have hC2 : ↥(closure {elt c}) ≃* Multiplicative (ZMod 2) := by
    have hcard : Nat.card ↥(zpowers (elt c)) = 2 := by rw [Nat.card_zpowers, hord]
    have e1 : ↥(zpowers (elt c)) ≃* Multiplicative (ZMod 2) := by
      have e := zmodCyclicMulEquiv (G := ↥(zpowers (elt c))) inferInstance
      rw [hcard] at e
      exact e.symm
    exact (MulEquiv.subgroupCongr (zpowers_eq_closure (elt c))).symm.trans e1
  obtain ⟨eID⟩ := f12_prodEquiv ⟨hsup, hinf, hcomm⟩
  exact ⟨⟨hsup, hinf, hcomm⟩, hord, hD8,
    ⟨eID.trans (MulEquiv.prodCongr hC2 (Classical.choice hD8))⟩⟩

end Tables

end Helpers

section Frame

variable {Γ : Type} [Group Γ] [Finite Γ] {fr : Frame Γ} {elt : ℕ → Γ} {P C V Q : ℕ}
  (hR : RealT elt P C V Q) (hg : ∀ s < 5, elt (s + 1) = sGen fr s)
include hR hg

theorem f12_elts : elt 1 = fr.a₁ ∧ elt 2 = fr.b₁ ∧ elt 3 = fr.a₂ ∧ elt 4 = fr.b₂ ∧
    elt 5 = fr.h₀ ∧ elt (atR Q 2) = fr.z := by
  have e2 : elt 2 = fr.b₁ := (hg 1 (by norm_num)).trans (sGen_one fr)
  refine ⟨(hg 0 (by norm_num)).trans (sGen_zero fr), e2, (hg 2 (by norm_num)).trans (sGen_two fr),
    (hg 3 (by norm_num)).trans (sGen_three fr), (hg 4 (by norm_num)).trans (sGen_four fr), ?_⟩
  rw [hR.sq (by norm_num), e2, SFrame.z, pow_two]

omit hR hg in
theorem f12_cls_lt : ∀ c ∈ cls12K P (atR Q 2) 1 2 3 4 5, ∀ x ∈ c, x < 128 := by
  simp [cls12K, f12_mulE_lt, atR_lt]

omit hR hg in
theorem f12_cls_len : (cls12K P (atR Q 2) 1 2 3 4 5).length = 7 := rfl

theorem f12_hset (j : Fin 7) :
    mset elt (lstM ((cls12K P (atR Q 2) 1 2 3 4 5).getD j [])) = fr.classes12 j := by
  obtain ⟨e1, e2, e3, e4, e5, ez⟩ := f12_elts hR hg
  have hj : (j : ℕ) < (cls12K P (atR Q 2) 1 2 3 4 5).length := by
    rw [f12_cls_len]
    exact j.isLt
  rw [lstM_mset (f12_cls_lt _ (f12_getD_mem _ _ hj))]
  refine f12_gens ?_
  fin_cases j <;> ext x <;>
    simp [cls12K, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Frame.classes12, Matrix.cons_val, mulE_elt hR, f12_mulE_lt, atR_lt, e1, e2, e3, e4, e5, ez]

theorem f12_classes {Sm : ℕ} (hS : mset elt Sm = (fr.S : Set Γ))
    (h : listsOK P C V Sm (involM Q Sm) (cls12K P (atR Q 2) 1 2 3 4 5) = true) :
    {X : Set Γ | ∃ y ∈ invols fr.S, X = conjClass fr.S y} = Set.range fr.classes12 ∧
      Function.Injective fr.classes12 := by
  obtain ⟨h1, h2, h3⟩ := listsOK_sound hR h
  have hI : mset elt (involM Q Sm) = invols fr.S := by
    rw [involM_mset hR, hS]
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, invols, f12_ord2]
  have hcl : ∀ c ∈ cls12K P (atR Q 2) 1 2 3 4 5,
      mset elt (lstM c) = conjClass fr.S (elt (hdL c)) ∧ elt (hdL c) ∈ invols fr.S := by
    intro c hc
    obtain ⟨-, -, hm, he⟩ := h1 c hc
    rw [hI] at hm
    rw [he, hS, f12_cls_eq]
    exact ⟨rfl, hm⟩
  have hlen := f12_cls_len (P := P) (Q := Q)
  constructor
  · ext X
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, hc, hyc⟩ := h2 y (by rw [hI]; exact hy)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
      have hj7 : j < 7 := by rw [← hlen]; exact hj
      have e0 : mset elt (lstM ((cls12K P (atR Q 2) 1 2 3 4 5).getD j [])) =
          fr.classes12 ⟨j, hj7⟩ := f12_hset hR hg ⟨j, hj7⟩
      rw [List.getD_eq_getElem (l := cls12K P (atR Q 2) 1 2 3 4 5) (d := []) hj] at e0
      obtain ⟨hc1, -⟩ := hcl _ hc
      rw [hc1] at hyc
      exact ⟨⟨j, hj7⟩, by rw [← e0, hc1]; exact (f12_conjClass_eq hyc).symm⟩
    · rintro ⟨j, rfl⟩
      have hj : (j : ℕ) < (cls12K P (atR Q 2) 1 2 3 4 5).length := by
        rw [hlen]
        exact j.isLt
      obtain ⟨hc1, hinv⟩ := hcl _ (f12_getD_mem _ _ hj)
      exact ⟨_, hinv, by rw [← f12_hset hR hg j, hc1]⟩
  · have key : ∀ i k : Fin 7, (i : ℕ) < k → fr.classes12 i = fr.classes12 k → False := by
      intro i k hlt he
      have hi : (i : ℕ) < (cls12K P (atR Q 2) 1 2 3 4 5).length := by
        rw [hlen]
        exact i.isLt
      have hk : (k : ℕ) < (cls12K P (atR Q 2) 1 2 3 4 5).length := by
        rw [hlen]
        exact k.isLt
      rw [← f12_hset hR hg i, ← f12_hset hR hg k,
        List.getD_eq_getElem (l := cls12K P (atR Q 2) 1 2 3 4 5) (d := []) hi,
        List.getD_eq_getElem (l := cls12K P (atR Q 2) 1 2 3 4 5) (d := []) hk] at he
      have hb : ∀ c ∈ cls12K P (atR Q 2) 1 2 3 4 5, ∀ n, (lstM c).testBit n = true → n < 128 :=
        fun c hc _ hn => testBit_lstM_lt (f12_cls_lt c hc) hn
      have heq := eq_of_mset_eq hR.inj (hb _ (List.getElem_mem hi)) (hb _ (List.getElem_mem hk)) he
      have hp := List.pairwise_iff_getElem.1 h3 i k (by simpa using hi) (by simpa using hk) hlt
      simp only [List.getElem_map] at hp
      exact hp heq
    intro i k hik
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact key i k hlt hik
    · exact key k i hlt hik.symm

theorem f12_cent {Sm R : ℕ} (hS : mset elt Sm = (fr.S : Set Γ))
    (h1 : cenE P C Sm (atR Q 2) = Sm) (h2 : closOK C [mulE P 1 3, 2, 4, 5] R = true)
    (h3 : cenE P C Sm (mulE P 2 4) = closK C [mulE P 1 3, 2, 4, 5] R)
    (h4 : closOK C [mulE P 2 4, 5, atR Q 2] R = true)
    (h5 : cenE P C Sm 5 = closK C [mulE P 2 4, 5, atR Q 2] R)
    (h6 : elemAbK P C Q (closK C [mulE P 2 4, 5, atR Q 2] R) = true)
    (h7 : pop (closK C [mulE P 2 4, 5, atR Q 2] R) = 8) :
    centEl fr.S fr.z = fr.S ∧
      centEl fr.S (fr.b₁ * fr.b₂) = closure {fr.a₁ * fr.a₂, fr.b₁, fr.b₂, fr.h₀} ∧
      centEl fr.S fr.h₀ = closure {fr.b₁ * fr.b₂, fr.h₀, fr.z} ∧ IsE 3 ↥(centEl fr.S fr.h₀) := by
  obtain ⟨e1, e2, e3, e4, e5, ez⟩ := f12_elts hR hg
  have e13 : elt (mulE P 1 3) = fr.a₁ * fr.a₂ := by
    rw [mulE_elt hR (by norm_num) (by norm_num), e1, e3]
  have e24 : elt (mulE P 2 4) = fr.b₁ * fr.b₂ := by
    rw [mulE_elt hR (by norm_num) (by norm_num), e2, e4]
  have cz : mset elt (cenE P C Sm (atR Q 2)) = (centEl fr.S fr.z : Set Γ) := by
    rw [f12_cen hR hS (atR_lt _ _), ez]
  have cb : mset elt (cenE P C Sm (mulE P 2 4)) = (centEl fr.S (fr.b₁ * fr.b₂) : Set Γ) := by
    rw [f12_cen hR hS (f12_mulE_lt _ _), e24]
  have ch : mset elt (cenE P C Sm 5) = (centEl fr.S fr.h₀ : Set Γ) := by
    rw [f12_cen hR hS (by norm_num), e5]
  have hE : (centEl fr.S fr.h₀ : Set Γ) = mset elt (closK C [mulE P 2 4, 5, atR Q 2] R) := by
    rw [← ch, h5]
  refine ⟨SetLike.coe_injective ?_, SetLike.coe_injective ?_, SetLike.coe_injective ?_, ?_⟩
  · rw [← cz, h1, hS]
  · rw [← cb, h3]
    refine f12_clos hR (by simp [f12_mulE_lt]) h2 (f12_gens ?_)
    simp only [List.map_cons, List.map_nil, e13, e2, e4, e5]
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  · rw [hE]
    refine f12_clos hR (by simp [f12_mulE_lt, atR_lt]) h4 (f12_gens ?_)
    simp only [List.map_cons, List.map_nil, e24, e5, ez]
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  · have hab := elemAbK_spec hR h6
    have hmem : ∀ x : Γ, x ∈ centEl fr.S fr.h₀ → x ∈ mset elt (closK C [mulE P 2 4, 5, atR Q 2] R) :=
      fun x hx => by
        rw [← hE]
        exact hx
    refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩, ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact (hab _ (hmem _ b.1.2)).2 _ (hmem _ a.1.2)
    · have hx2 := (hab _ (hmem _ x.2)).1
      simpa [Subtype.ext_iff, pow_two] using hx2
    · rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hE,
        pop_sound hR.inj (repM_mset hR.inj _), h7]
      norm_num

theorem f12_decs {Sm R : ℕ} (hS : mset elt Sm = (fr.S : Set Γ))
    (d1 : z2d8K P C Q (cenE P C Sm (mulE P 1 3)) (mulE P 1 3) 1 (mulE P 2 4) R = true)
    (d2 : z2d8K P C Q (cenE P C Sm (mulE P 1 4)) (mulE P 1 4) 1 (mulE P 2 3) R = true)
    (d3 : z2d8K P C Q (cenE P C Sm (mulE P 2 3)) (mulE P 2 3) 2 (mulE P 1 4) R = true)
    (d4 : z2d8K P C Q (cenE P C Sm (mulE P (mulE P 1 2) 3)) (mulE P (mulE P 1 2) 3) 3
      (mulE P 1 4) R = true) :
    IsZ2xD8Decomp (centEl fr.S (fr.a₁ * fr.a₂)) (fr.a₁ * fr.a₂) (closure {fr.a₁, fr.b₁ * fr.b₂}) ∧
    IsZ2xD8Decomp (centEl fr.S (fr.a₁ * fr.b₂)) (fr.a₁ * fr.b₂) (closure {fr.a₁, fr.b₁ * fr.a₂}) ∧
    IsZ2xD8Decomp (centEl fr.S (fr.b₁ * fr.a₂)) (fr.b₁ * fr.a₂) (closure {fr.b₁, fr.a₁ * fr.b₂}) ∧
    IsZ2xD8Decomp (centEl fr.S (fr.a₁ * fr.b₁ * fr.a₂)) (fr.a₁ * fr.b₁ * fr.a₂)
      (closure {fr.a₂, fr.a₁ * fr.b₂}) := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := f12_elts hR hg
  have hm : ∀ x y, x < 128 → y < 128 → elt (mulE P x y) = elt x * elt y :=
    fun _ _ hx hy => mulE_elt hR hx hy
  have e13 : elt (mulE P 1 3) = fr.a₁ * fr.a₂ := by rw [hm _ _ (by norm_num) (by norm_num), e1, e3]
  have e24 : elt (mulE P 2 4) = fr.b₁ * fr.b₂ := by rw [hm _ _ (by norm_num) (by norm_num), e2, e4]
  have e14 : elt (mulE P 1 4) = fr.a₁ * fr.b₂ := by rw [hm _ _ (by norm_num) (by norm_num), e1, e4]
  have e23 : elt (mulE P 2 3) = fr.b₁ * fr.a₂ := by rw [hm _ _ (by norm_num) (by norm_num), e2, e3]
  have e123 : elt (mulE P (mulE P 1 2) 3) = fr.a₁ * fr.b₁ * fr.a₂ := by
    rw [hm _ _ (f12_mulE_lt _ _) (by norm_num), hm _ _ (by norm_num) (by norm_num), e1, e2, e3]
  have k1 := f12_dec hR hS (f12_mulE_lt _ _) (by norm_num) (f12_mulE_lt _ _) d1
  have k2 := f12_dec hR hS (f12_mulE_lt _ _) (by norm_num) (f12_mulE_lt _ _) d2
  have k3 := f12_dec hR hS (f12_mulE_lt _ _) (by norm_num) (f12_mulE_lt _ _) d3
  have k4 := f12_dec hR hS (f12_mulE_lt _ _) (by norm_num) (f12_mulE_lt _ _) d4
  rw [e13, e1, e24] at k1
  rw [e14, e1, e23] at k2
  rw [e23, e2, e14] at k3
  rw [e123, e3, e14] at k4
  exact ⟨k1, k2, k3, k4⟩

end Frame

theorem fact12_of_twin {Γ : Type} [Group Γ] [Finite Γ] {fr : Frame Γ}
    {elt : ℕ → Γ} {P C V Q R : ℕ} (hR : RealT elt P C V Q)
    (hg : ∀ s < 5, elt (s + 1) = sGen fr s)
    (h : f12K P C V Q 1 2 3 4 5 R = true) : fr.Fact12 := by
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := f12_elts hR hg
  unfold f12K at h
  rw [bAnd_eq, Bool.and_eq_true, strictB_eq] at h
  obtain ⟨hcl, h⟩ := h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hcls, hcent, hdec⟩ := h
  have hS : mset elt (closK C [1, 2, 3, 4, 5] R) = (fr.S : Set Γ) := by
    rw [SFrame.S]
    refine f12_clos hR (by simp) hcl (f12_gens ?_)
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4, e5]
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  unfold f12ClassK at hcls
  rw [strictB_eq] at hcls
  have hc := f12_classes hR hg hS hcls
  unfold f12CentK at hcent
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, strictB_eq] at hcent
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hcent
  have ht := f12_cent hR hg hS c1 c2 c3 c4 c5 c6 c7
  unfold f12DecK at hdec
  simp only [bAnd_eq, Bool.and_eq_true] at hdec
  obtain ⟨d1, d2, d3, d4⟩ := hdec
  have hd := f12_decs hR hg hS d1 d2 d3 d4
  exact ⟨hc.1, hc.2, ht.1, ht.2.1, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, ht.2.2.1, ht.2.2.2⟩

end CFSG.KC.G2Three.Sec1T3
