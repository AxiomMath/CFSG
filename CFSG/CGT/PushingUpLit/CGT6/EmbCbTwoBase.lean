module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbLab
import CFSG.CGT.PushingUpLit.CGT6.EmbAltCAw
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltEnd
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbApi

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)} {m : ℕ}

structure CbtY (Y : Subgroup (MulAut V)) (m : ℕ) where
  θ : ↥Y ≃* alternatingGroup (Fin m)
  hnat : IsNatSectionWith (altAct m) θ (commV Y) ⊥
  w : Fin m → V
  hmem : ∀ r, w r ∈ commV Y ∧ w r ≠ 1
  hinj : Function.Injective w
  hact : ∀ (y : MulAut V) (hy : y ∈ Y) (r : Fin m),
    y (w r) = w ((θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) r)
  hspan : Subgroup.closure (Set.range w) = commV Y
  huniq : ∀ (r : Fin m) (u : V), u ∈ commV Y →
    (∀ (y : MulAut V) (hy : y ∈ Y), (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) r = r → y u = u) →
    u = 1 ∨ u = w r
  h4 : ∀ p q p' q' : Fin m, p ≠ q → p ≠ p' → p ≠ q' → q ≠ p' → q ≠ q' → p' ≠ q' →
    w p * w q * w p' * w q' ≠ 1

theorem CbtY.nonempty {G T : Subgroup (MulAut V)} [Finite V] (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) :
    Nonempty (CbtY Y m) := by
  obtain ⟨θ, hnat⟩ := h.exists_natSection hV hm hodd hY
  obtain ⟨w, hmem, hinj, hact, hspan, huniq, h4⟩ := exists_wfam hodd hm θ hnat
  exact ⟨⟨θ, hnat, w, hmem, hinj, hact, hspan, huniq, h4⟩⟩

structure CbtLift (C : CbtY Y m) (t : MulAut V) (X : Subgroup (MulAut V)) where
  D : CbData Y t m X
  hYX : Y ≤ X
  j : Fin m → Fin (m + 2)
  hjinj : Function.Injective j
  hja : ∀ r, j r ≠ D.a
  hjb : ∀ r, j r ≠ D.b
  hjsurj : ∀ q, q ≠ D.a → q ≠ D.b → ∃ r, j r = q
  hjθ : ∀ (y : MulAut V) (hy : y ∈ Y) (r : Fin m),
    (D.θ ⟨y, hYX hy⟩ : Equiv.Perm (Fin (m + 2))) (j r) =
      j ((C.θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) r)

theorem CbtLift.nonempty [Finite V] (C : CbtY Y m) (hm : 7 ≤ m) (hodd : Odd m) {t : MulAut V}
    {X : Subgroup (MulAut V)} (hX : CbAlg Y t m X) : Nonempty (CbtLift C t X) := by
  obtain ⟨D⟩ := hX.nonempty_data hm hodd
  obtain ⟨j, hinj, hab, hsurj, hjθ⟩ := cbtExists_label hm C.θ hX.Y_le D.θ D.hab D.hstab
  exact ⟨⟨D, hX.Y_le, j, hinj, fun r => (hab r).1, fun r => (hab r).2, hsurj, hjθ⟩⟩

theorem cbtPow_odd {M : Type*} [Monoid M] {w : M} (hw : w * w = 1) {n : ℕ} (hn : Odd n) :
    w ^ n = w := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, sq, hw, one_pow, one_mul]

theorem cbtExists_alt_perm {n : ℕ} (hn : 7 ≤ n) {F : Finset (Fin n)} (hF : F.card ≤ 3)
    {i j : Fin n} (hi : i ∉ F) (hj : j ∉ F) :
    ∃ σ : alternatingGroup (Fin n), (∀ f ∈ F, (σ : Equiv.Perm (Fin n)) f = f) ∧
      (σ : Equiv.Perm (Fin n)) i = j := by
  classical
  by_cases hij : i = j
  · exact ⟨1, fun f _ => rfl, hij⟩
  have hcard : 1 < (insert i (insert j F))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have h1 := Finset.card_insert_le i (insert j F)
    have h2 := Finset.card_insert_le j F
    omega
  obtain ⟨l, hl, n', hn', hln⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_compl, Finset.mem_insert, not_or] at hl hn'
  refine ⟨⟨Equiv.swap i j * Equiv.swap l n', ?_⟩, fun f hf => ?_, ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hij, hln]
  · have hfi : f ≠ i := fun h => hi (h ▸ hf)
    have hfj : f ≠ j := fun h => hj (h ▸ hf)
    have hfl : f ≠ l := fun h => hl.2.2 (h ▸ hf)
    have hfn : f ≠ n' := fun h => hn'.2.2 (h ▸ hf)
    show (Equiv.swap i j) ((Equiv.swap l n') f) = f
    rw [Equiv.swap_apply_of_ne_of_ne hfl hfn, Equiv.swap_apply_of_ne_of_ne hfi hfj]
  · show (Equiv.swap i j) ((Equiv.swap l n') i) = j
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hl.1) (Ne.symm hn'.1), Equiv.swap_apply_left]

namespace CbtLift

variable {C : CbtY Y m} {t : MulAut V} {X : Subgroup (MulAut V)} (L : CbtLift C t X)

theorem fix_ab (y : MulAut V) (hy : y ∈ Y) :
    (L.D.θ ⟨y, L.hYX hy⟩ : Equiv.Perm (Fin (m + 2))) L.D.a = L.D.a ∧
      (L.D.θ ⟨y, L.hYX hy⟩ : Equiv.Perm (Fin (m + 2))) L.D.b = L.D.b := by
  have h : L.D.θ ⟨y, L.hYX hy⟩ ∈ altStabilizer (m + 2) {L.D.a, L.D.b} := by
    rw [← L.D.hstab]
    exact ⟨⟨y, L.hYX hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rw [mem_altStabilizer_iff] at h
  exact ⟨h L.D.a (by simp), h L.D.b (by simp)⟩

theorem y_wa (y : MulAut V) (hy : y ∈ Y) : y (L.D.w L.D.a) = L.D.w L.D.a := by
  rw [L.D.hwact y (L.hYX hy), (L.fix_ab y hy).1]

theorem y_wb (y : MulAut V) (hy : y ∈ Y) : y (L.D.w L.D.b) = L.D.w L.D.b := by
  rw [L.D.hwact y (L.hYX hy), (L.fix_ab y hy).2]

theorem y_wj (y : MulAut V) (hy : y ∈ Y) (r : Fin m) :
    y (L.D.w (L.j r)) = L.D.w (L.j ((C.θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) r)) := by
  rw [L.D.hwact y (L.hYX hy), L.hjθ y hy r]

theorem prod_w [Finite V] (hm : 7 ≤ m) (hodd : Odd m) : ∏ p : Fin (m + 2), L.D.w p = 1 := by
  have hmem : (∏ p : Fin (m + 2), L.D.w p) ∈ commV X :=
    Subgroup.prod_mem _ fun p _ => (L.D.hwmem p).1
  have hfix : (∏ p : Fin (m + 2), L.D.w p) ∈ fixV X := by
    rw [mem_fixV]
    intro x hx
    rw [map_prod x]
    simp_rw [L.D.hwact x hx]
    exact Equiv.prod_comp (L.D.θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) L.D.w
  have h2 : (∏ p : Fin (m + 2), L.D.w p) ∈ commV X ⊓ fixV X := ⟨hmem, hfix⟩
  rw [(L.D.split hm hodd).2] at h2
  exact h2

theorem exists_third (hm : 3 ≤ m) (r r' : Fin m) : ∃ s : Fin m, s ≠ r ∧ s ≠ r' := by
  by_contra hcon
  push Not at hcon
  have h1 : (Finset.univ : Finset (Fin m)) ⊆ {r, r'} := by
    intro s _
    by_cases hs : s = r
    · simp [hs]
    · simp [hcon s hs]
  have h2 := Finset.card_le_card h1
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 := Finset.card_le_two (a := r) (b := r')
  omega

theorem pair_mem [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) {r r' : Fin m} (hrr : r ≠ r') :
    L.D.w (L.j r') * L.D.w (L.j r) ∈ commV Y := by
  obtain ⟨s, hsr, hsr'⟩ := exists_third (by omega) r r'
  let σ : alternatingGroup (Fin m) := ⟨swap r r' * swap r' s, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hrr,
      Equiv.Perm.sign_swap (Ne.symm hsr')]
    decide⟩
  have hσ : (σ : Equiv.Perm (Fin m)) r = r' := by
    show (swap r r') ((swap r' s) r) = r'
    rw [swap_apply_of_ne_of_ne hrr (Ne.symm hsr), swap_apply_left]
  let y : ↥Y := C.θ.symm σ
  have h1 : (C.θ ⟨(y : MulAut V), y.2⟩ : alternatingGroup (Fin m)) = σ := C.θ.apply_symm_apply σ
  have h2 : (y : MulAut V) (L.D.w (L.j r)) = L.D.w (L.j r') := by
    rw [L.y_wj y y.2 r, h1, hσ]
  have h3 : (y : MulAut V) (L.D.w (L.j r)) * (L.D.w (L.j r))⁻¹ ∈ commV Y :=
    Subgroup.subset_closure ⟨y, y.2, _, rfl⟩
  rw [h2, inv_eq_of_mul_eq_one_right (L.D.w_sq hV _)] at h3
  exact h3

theorem prod_wj [Finite V] (hm : 7 ≤ m) (hodd : Odd m) :
    (∏ r : Fin m, L.D.w (L.j r)) * (L.D.w L.D.a * L.D.w L.D.b) = 1 := by
  classical
  have h1 := L.prod_w hm hodd
  have hu : (Finset.univ : Finset (Fin (m + 2))) =
      (Finset.univ.image L.j) ∪ {L.D.a, L.D.b} := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    refine iff_of_true trivial ?_
    by_cases hpa : p = L.D.a
    · exact Or.inr (Or.inl hpa)
    by_cases hpb : p = L.D.b
    · exact Or.inr (Or.inr hpb)
    exact Or.inl (L.hjsurj p hpa hpb)
  have hd : Disjoint (Finset.univ.image L.j) ({L.D.a, L.D.b} : Finset (Fin (m + 2))) := by
    rw [Finset.disjoint_left]
    intro p hp hp2
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hp
    rcases Finset.mem_insert.mp hp2 with h | h
    · exact L.hja r h
    · exact L.hjb r (Finset.mem_singleton.mp h)
  rw [hu, Finset.prod_union hd, Finset.prod_image fun x _ y _ h => L.hjinj h,
    Finset.prod_pair L.D.hab] at h1
  exact h1

@[expose] def vvec : V := L.D.w L.D.a * L.D.w L.D.b

@[expose] def zvec : V := L.D.w L.D.b

@[expose] def eps (r : Fin m) : V := L.D.w (L.j r) * (L.D.w L.D.a * L.D.w L.D.b)

theorem eps_mem [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) (r : Fin m) :
    L.eps r ∈ commV Y := by
  classical
  let r₀ : Fin m := ⟨0, by omega⟩
  let e : Fin m → V := fun r => L.D.w (L.j r) * L.D.w (L.j r₀)
  have hw2 : ∀ p, L.D.w p * L.D.w p = 1 := fun p => L.D.w_sq hV p
  have he : ∀ r, e r ∈ commV Y := by
    intro r
    by_cases hr : r₀ = r
    · simp only [e, ← hr, hw2]
      exact one_mem _
    · exact L.pair_mem hV hm hr
  have h1 : ∀ r, L.D.w (L.j r) = e r * L.D.w (L.j r₀) := fun r => by
    simp only [e]
    rw [mul_assoc, hw2, mul_one]
  have hpow : L.D.w (L.j r₀) ^ m = L.D.w (L.j r₀) := cbtPow_odd (hw2 _) hodd
  have hP : (∏ r : Fin m, L.D.w (L.j r)) = (∏ r : Fin m, e r) * L.D.w (L.j r₀) := by
    calc ∏ r : Fin m, L.D.w (L.j r) = ∏ r : Fin m, (e r * L.D.w (L.j r₀)) :=
          Finset.prod_congr rfl fun r _ => h1 r
      _ = (∏ r : Fin m, e r) * L.D.w (L.j r₀) ^ m := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (∏ r : Fin m, e r) * L.D.w (L.j r₀) := by rw [hpow]
  have hprod := L.prod_wj hm hodd
  rw [hP, mul_assoc] at hprod
  have h0 : L.eps r₀ = (∏ r : Fin m, e r)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have h2 : L.eps r = e r * L.eps r₀ := by
    have : e r * L.eps r₀ = L.D.w (L.j r) * (L.D.w (L.j r₀) * L.D.w (L.j r₀)) *
        (L.D.w L.D.a * L.D.w L.D.b) := by
      simp only [e, eps]
      group
    rw [this, hw2, mul_one]
    rfl
  rw [h2, h0]
  exact mul_mem (he r) (inv_mem (Subgroup.prod_mem _ fun r _ => he r))

theorem eps_ne_one [Finite V] (hm : 7 ≤ m) (r : Fin m) : L.eps r ≠ 1 := by
  intro h
  obtain ⟨r', hr'⟩ : ∃ r' : Fin m, r' ≠ r := by
    by_cases h0 : r = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, fun h' => by
        rw [h0] at h'
        exact absurd (congrArg Fin.val h') (by simp)⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h0 h'.symm⟩
  have hbF : L.D.b ∉ ({L.j r, L.D.a} : Finset (Fin (m + 2))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => L.hjb r h'.symm, fun h' => L.D.hab h'.symm⟩
  have hjF : L.j r' ∉ ({L.j r, L.D.a} : Finset (Fin (m + 2))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => hr' (L.hjinj h'), L.hja r'⟩
  obtain ⟨σ, hσF, hσ⟩ := cbtExists_alt_perm (n := m + 2) (by omega) (F := {L.j r, L.D.a})
    (by
      have := Finset.card_le_two (a := L.j r) (b := L.D.a)
      omega) hbF hjF
  let g : ↥X := L.D.θ.symm σ
  have hg : (L.D.θ ⟨(g : MulAut V), g.2⟩ : alternatingGroup (Fin (m + 2))) = σ :=
    L.D.θ.apply_symm_apply σ
  have h1 : (g : MulAut V) (L.eps r) = 1 := by rw [h, map_one]
  have e1 : (g : MulAut V) (L.D.w (L.j r)) = L.D.w (L.j r) := by
    rw [L.D.hwact g g.2, hg, hσF (L.j r) (by simp)]
  have e2 : (g : MulAut V) (L.D.w L.D.a) = L.D.w L.D.a := by
    rw [L.D.hwact g g.2, hg, hσF L.D.a (by simp)]
  have e3 : (g : MulAut V) (L.D.w L.D.b) = L.D.w (L.j r') := by
    rw [L.D.hwact g g.2, hg, hσ]
  simp only [eps, map_mul, e1, e2, e3] at h1
  have h2 : L.D.w (L.j r) * (L.D.w L.D.a * L.D.w (L.j r')) =
      L.D.w (L.j r) * (L.D.w L.D.a * L.D.w L.D.b) := h1.trans h.symm
  have h3 := mul_left_cancel (mul_left_cancel h2)
  exact L.hjb r' (L.D.hwinj h3)

theorem eps_fix (y : MulAut V) (hy : y ∈ Y) (r : Fin m)
    (hyr : (C.θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) r = r) : y (L.eps r) = L.eps r := by
  simp only [eps, map_mul, L.y_wj y hy r, L.y_wa y hy, L.y_wb y hy, hyr]

theorem eps_eq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) (r : Fin m) :
    L.eps r = C.w r := by
  rcases C.huniq r (L.eps r) (L.eps_mem hV hm hodd r) (fun y hy hyr => L.eps_fix y hy r hyr) with
    h | h
  · exact absurd h (L.eps_ne_one hm r)
  · exact h

end CbtLift

structure CbtCtx [Finite V] (G T Y : Subgroup (MulAut V)) (t : MulAut V) (m : ℕ)
    (X₁ X₂ : Subgroup (MulAut V)) where
  h2 : Alt2Rank1
  h : EndCfg4 G T Y
  hV : ∀ v : V, v ^ 2 = 1
  hm : 7 ≤ m
  hodd : Odd m
  hY : YAlt Y m
  htG : t ∈ G
  htT : t ∈ T
  ht2 : t ^ 2 = 1
  ht1 : t ≠ 1
  h₁ : IsCbLift G Y t m X₁
  h₂ : IsCbLift G Y t m X₂
  hne : X₁ ≠ X₂
  C : CbtY Y m
  L₁ : CbtLift C t X₁
  L₂ : CbtLift C t X₂

theorem CbtCtx.exists [Finite V] {G T Y : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ}
    {X₁ X₂ : Subgroup (MulAut V)} (h2 : Alt2Rank1) (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) (htG : t ∈ G)
    (htT : t ∈ T) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (h₁ : IsCbLift G Y t m X₁)
    (h₂ : IsCbLift G Y t m X₂) (hne : X₁ ≠ X₂) : Nonempty (CbtCtx G T Y t m X₁ X₂) := by
  obtain ⟨C⟩ := CbtY.nonempty h hV hm hodd hY
  obtain ⟨L₁⟩ := CbtLift.nonempty C hm hodd h₁.toCbAlg
  obtain ⟨L₂⟩ := CbtLift.nonempty C hm hodd h₂.toCbAlg
  exact ⟨⟨h2, h, hV, hm, hodd, hY, htG, htT, ht2, ht1, h₁, h₂, hne, C, L₁, L₂⟩⟩

namespace CbtCtx

variable [Finite V] {G T : Subgroup (MulAut V)} {t : MulAut V} {X₁ X₂ : Subgroup (MulAut V)}
  (K : CbtCtx G T Y t m X₁ X₂)

@[expose] def symm : CbtCtx G T Y t m X₂ X₁ where
  h2 := K.h2
  h := K.h
  hV := K.hV
  hm := K.hm
  hodd := K.hodd
  hY := K.hY
  htG := K.htG
  htT := K.htT
  ht2 := K.ht2
  ht1 := K.ht1
  h₁ := K.h₂
  h₂ := K.h₁
  hne := K.hne.symm
  C := K.C
  L₁ := K.L₂
  L₂ := K.L₁

include K

theorem t_comm_Y (y : MulAut V) (hy : y ∈ Y) : t * y = y * t := by
  have := K.h.toEmb4Cfg.adm.le_centralizer K.htT
  exact (Subgroup.mem_centralizer_iff.mp this y hy).symm

theorem t_mul_self : t * t = 1 := by
  rw [← sq]; exact K.ht2

end CbtCtx

end CFSG.CGT.PushingUpLit.CGT6
