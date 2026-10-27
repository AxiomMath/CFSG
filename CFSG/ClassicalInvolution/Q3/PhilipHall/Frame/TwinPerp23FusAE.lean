module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Ext
public import CFSG.ClassicalInvolution.Q3.TL4AE286Aut
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Fam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

theorem exists_kStarList_d₁ : ∃ k ∈ kStarList, k.perm = d₁ := by decide +kernel

theorem exists_kStarList_d₂ : ∃ k ∈ kStarList, k.perm = d₂ := by decide +kernel

theorem exists_kStarList_d₃ : ∃ k ∈ kStarList, k.perm = d₃ := by decide +kernel

theorem not_three_outside {n : ℕ} (hn : n ≤ 6) (ι : Fin 4 ↪ Fin n) {y₁ y₂ y₃ : Fin n}
    (h₁ : y₁ ∉ Set.range ι) (h₂ : y₂ ∉ Set.range ι) (h₃ : y₃ ∉ Set.range ι) (h12 : y₁ ≠ y₂)
    (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃) : False := by
  classical
  set s : Finset (Fin n) := Finset.univ.image ι with hs
  have hscard : s.card = 4 := by
    rw [hs, Finset.card_image_of_injective _ ι.injective]
    simp
  have hnot : ∀ y, y ∉ Set.range ι → y ∉ s := fun y hy hys => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hys
    exact hy ⟨i, hi⟩
  have e3 : y₃ ∉ insert y₂ (insert y₁ s) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨h23.symm, h13.symm, hnot _ h₃⟩
  have e2 : y₂ ∉ insert y₁ s := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨h12.symm, hnot _ h₂⟩
  have e1 : y₁ ∉ s := hnot _ h₁
  have hcard : (insert y₃ (insert y₂ (insert y₁ s))).card = 7 := by
    rw [Finset.card_insert_of_notMem e3, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e1, hscard]
  have := Finset.card_le_univ (insert y₃ (insert y₂ (insert y₁ s)))
  rw [Fintype.card_fin] at this
  omega

theorem perm_involutive_of_cent {n : ℕ} (hn : n = 5 ∨ n = 6) (ι : Fin 4 ↪ Fin n)
    {L : List (Wr 4)} (h₁ : ∃ k ∈ L, k.perm = d₁) (h₂ : ∃ k ∈ L, k.perm = d₂)
    (h₃ : ∃ k ∈ L, k.perm = d₃) {σ : Equiv.Perm (Fin n)}
    (hpc : ∀ a ∈ L, σ * embedPerm ι a.perm = embedPerm ι a.perm * σ) :
    ∀ y, σ (σ y) = y := by
  classical
  obtain ⟨k₁, hk₁, hk₁p⟩ := h₁
  obtain ⟨k₂, hk₂, hk₂p⟩ := h₂
  obtain ⟨k₃, hk₃, hk₃p⟩ := h₃
  have hmap : ∀ i, σ (ι i) ∈ Set.range ι := by
    intro i
    by_contra hy
    have hc := hpc k₁ hk₁
    rw [hk₁p] at hc
    have e1 : σ (embedPerm ι d₁ (ι i)) = embedPerm ι d₁ (σ (ι i)) := by
      have := congrArg (fun f : Equiv.Perm (Fin n) => f (ι i)) hc
      simpa using this
    rw [embedPerm_apply, embedPerm_of_not_mem ι d₁ hy] at e1
    exact TwinDisc.AE5.d1_fixed_free i (ι.injective (σ.injective e1))
  set c := localPerm ι σ hmap with hcdef
  have hspec : ∀ i, σ (ι i) = ι (c i) := localPerm_spec ι σ hmap
  have hcomm_c : ∀ a ∈ L, c * a.perm = a.perm * c := by
    intro a ha
    refine Equiv.ext fun i => ι.injective ?_
    have hc := hpc a ha
    have e1 := congrArg (fun f : Equiv.Perm (Fin n) => f (ι i)) hc
    simp only [Equiv.Perm.mul_apply, embedPerm_apply, hspec] at e1
    simpa [Equiv.Perm.mul_apply] using e1
  have hcV : c = 1 ∨ c = d₁ ∨ c = d₂ ∨ c = d₃ :=
    TwinDisc.AE5.loc_perm c (by rw [← hk₁p]; exact hcomm_c k₁ hk₁)
      (by rw [← hk₂p]; exact hcomm_c k₂ hk₂) (by rw [← hk₃p]; exact hcomm_c k₃ hk₃)
  have hcc : c * c = 1 := by
    rcases hcV with h | h | h | h <;> rw [h] <;> decide
  have hsymm : ∀ i, σ.symm (ι i) = ι (c.symm i) := by
    intro i
    apply σ.injective
    rw [Equiv.apply_symm_apply, hspec, Equiv.apply_symm_apply]
  have hout : ∀ y, y ∉ Set.range ι → σ y ∉ Set.range ι := by
    rintro y hy ⟨j, hj⟩
    apply hy
    refine ⟨c.symm j, ?_⟩
    rw [← hsymm, hj, Equiv.symm_apply_apply]
  intro y
  by_cases hy : y ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hy
    rw [hspec, hspec]
    have : c (c i) = i := by simpa [Equiv.Perm.mul_apply] using congrArg (fun f => f i) hcc
    rw [this]
  · by_contra hne
    have hy1 := hout y hy
    have hy2 := hout _ hy1
    have h1 : σ y ≠ y := fun h => hne (by rw [h, h])
    have h2 : σ (σ y) ≠ σ y := fun h => h1 (σ.injective h)
    exact not_three_outside (by rcases hn with rfl | rfl <;> norm_num) ι hy hy1 hy2 h1.symm
      (fun h => hne h.symm) h2.symm

theorem wr_pow_four_of_perm_sq {n : ℕ} (w : Wr n) (h : ∀ y, w.perm (w.perm y) = y) :
    w * w * (w * w) = 1 := by
  have hp : (w * w).perm = 1 := Equiv.ext fun y => by
    rw [mul_perm, Equiv.Perm.mul_apply, h y]
    rfl
  refine Wr.ext (funext fun y => ?_) ?_
  · rw [mul_vec, hp, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply, one_vec]
    exact CharTwo.add_self_eq_zero _
  · rw [mul_perm, hp, mul_one, one_perm]

theorem cent_pow_four {n : ℕ} (hn : n = 5 ∨ n = 6) (ι : Fin 4 ↪ Fin n) {L : List (Wr 4)}
    (h₁ : ∃ k ∈ L, k.perm = d₁) (h₂ : ∃ k ∈ L, k.perm = d₂) (h₃ : ∃ k ∈ L, k.perm = d₃)
    {x : AEQ n} (hx : ∀ a ∈ L, x * mkQ n (embed ι a) = mkQ n (embed ι a) * x) :
    x * x * (x * x) = 1 := by
  classical
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub n) x
  have hpc : ∀ a ∈ L, w.perm * embedPerm ι a.perm = embedPerm ι a.perm * w.perm := by
    intro a ha
    have h := hx a ha
    rw [← map_mul, ← map_mul] at h
    have := (TwinDisc.AE5.comm_comp h).1
    simpa only [mul_perm, embed_perm] using this
  have hsq := perm_involutive_of_cent hn ι h₁ h₂ h₃ hpc
  have := wr_pow_four_of_perm_sq w hsq
  show mkQ n w * mkQ n w * (mkQ n w * mkQ n w) = 1
  rw [← map_mul, ← map_mul, this, map_one]

theorem cent_memBar_pow_four {n : ℕ} (hn : n = 5 ∨ n = 6) (α : Finset (Fin n)) (h : α.card = 4)
    (b : Bool) {x : AEQ n} (hx : ∀ y ∈ memBar α h b, x * y = y * x) : x * x * (x * x) = 1 := by
  cases b
  · exact cent_pow_four hn (emb α h) exists_kStarList_d₁ exists_kStarList_d₂ exists_kStarList_d₃
      (fun a ha => hx _ ⟨embed (emb α h) a, ⟨a, ha, rfl⟩, rfl⟩)
  · exact cent_pow_four hn (emb α h) TwinDisc.AE5.exists_kList_d₁ TwinDisc.AE5.exists_kList_d₂
      TwinDisc.AE5.exists_kList_d₃ (fun a ha => hx _ ⟨embed (emb α h) a, ⟨a, ha, rfl⟩, rfl⟩)

section Aut

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {n : ℕ}

theorem theta_perm (I : AEIdent P n) (ψ : MulAut ↥(pSpan P)) (θ : MulAut ↥(TL4.aeModel n))
    (hθ : ∀ y, θ (I.toModel y) = I.toModel (ψ y))
    (hψP : ∀ M ∈ P, ∃ M' ∈ P,
      (M.subgroupOf (pSpan P)).map ψ.toMonoidHom = M'.subgroupOf (pSpan P)) :
    ∀ (γ : Finset (Fin n)) (hγ : γ.card = 4) (c : Bool),
      ∃ (γ' : Finset (Fin n)) (hγ' : γ'.card = 4) (c' : Bool),
        ((memBar γ hγ c).subgroupOf (TL4.aeModel n)).map θ.toMonoidHom =
          (memBar γ' hγ' c').subgroupOf (TL4.aeModel n) := by
  classical
  intro γ hγ c
  obtain ⟨L, hL, hLl⟩ := I.label_surj γ hγ c
  obtain ⟨M', hM', hM'e⟩ := hψP L hL
  obtain ⟨γ', hγ', c', hM'l⟩ := I.label M' hM'
  refine ⟨γ', hγ', c', ?_⟩
  ext ⟨g, hg⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨⟨g₀, hg₀⟩, hg₀m, hθg⟩
    have hg₀m' : g₀ ∈ memBar γ hγ c := hg₀m
    rw [← hLl] at hg₀m'
    obtain ⟨l, hl, hly⟩ := hg₀m'
    have e : (⟨g₀, hg₀⟩ : ↥(TL4.aeModel n)) = I.toModel l := Subtype.ext hly.symm
    rw [e, hθ] at hθg
    have hψl : ψ l ∈ (M'.subgroupOf (pSpan P)) := by
      rw [← hM'e]
      exact ⟨l, hl, rfl⟩
    have : (g : AEQ n) ∈ (M'.subgroupOf (pSpan P)).map I.φ := by
      refine ⟨ψ l, hψl, ?_⟩
      have := congrArg Subtype.val hθg
      exact this
    rw [hM'l] at this
    exact this
  · intro hg'
    have hg'' : g ∈ (M'.subgroupOf (pSpan P)).map I.φ := by rw [hM'l]; exact hg'
    obtain ⟨m, hm, hmy⟩ := hg''
    rw [← hM'e] at hm
    obtain ⟨l, hl, hlm⟩ := hm
    have hlmem : (I.φ l) ∈ memBar γ hγ c := by
      rw [← hLl]
      exact ⟨l, hl, rfl⟩
    refine ⟨I.toModel l, hlmem, ?_⟩
    rw [hθ]
    apply Subtype.ext
    show I.φ (ψ l) = g
    rw [show ψ l = m from hlm, hmy]

theorem theta_fix (I : AEIdent P n) (ψ : MulAut ↥(pSpan P)) (θ : MulAut ↥(TL4.aeModel n))
    (hθ : ∀ y, θ (I.toModel y) = I.toModel (ψ y)) {L : Subgroup G} (hL : L ∈ P)
    (hfix : ∀ y : ↥(pSpan P), (y : G) ∈ L → ψ y = y) {α : Finset (Fin n)} {h : α.card = 4}
    {c : Bool} (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h c) :
    ∀ y (hy : y ∈ memBar α h c), θ ⟨y, memBar_le_aeModel α h c hy⟩ =
      ⟨y, memBar_le_aeModel α h c hy⟩ := by
  intro y hy
  rw [← hlab] at hy
  obtain ⟨l, hl, hly⟩ := hy
  have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have e : (⟨y, memBar_le_aeModel α h c (by rw [← hlab]; exact ⟨l, hl, hly⟩)⟩ :
      ↥(TL4.aeModel n)) = I.toModel l := Subtype.ext hly.symm
  rw [e, hθ, hfix l hl']

theorem aut_eq_one_of_odd_fix (hn : n = 5 ∨ n = 6)
    (F : ExitO2.Q8Fam G P) (I : AEIdent P n) (ψ : MulAut ↥(pSpan P))
    (hψP : ∀ M ∈ P, ∃ M' ∈ P,
      (M.subgroupOf (pSpan P)).map ψ.toMonoidHom = M'.subgroupOf (pSpan P))
    {J : Subgroup G} (hJ : J ∈ P) (hfixJ : ∀ y : ↥(pSpan P), (y : G) ∈ J → ψ y = y) {k : ℕ}
    (hk : Odd k) (hψk : ψ ^ k = 1) : ∀ y, ψ y = y := by
  classical
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn7 : n ≤ 7 := by rcases hn with rfl | rfl <;> norm_num
  set θ := I.inducedAutOf hn5 ψ with hθdef
  have hθ : ∀ y, θ (I.toModel y) = I.toModel (ψ y) := fun y => I.inducedAutOf_apply hn5 ψ y
  obtain ⟨α, h, b, hl⟩ := I.label J hJ
  have hperm := theta_perm I ψ θ hθ hψP
  have hfix := theta_fix I ψ θ hθ hJ hfixJ hl
  obtain ⟨a, ha⟩ := model117_proved n hn5 hn7 θ hperm
  have hcomm : ∀ y ∈ memBar α h b, a * y = y * a := by
    intro y hy
    have h1 := ha ⟨y, memBar_le_aeModel α h b hy⟩
    rw [hfix y hy] at h1
    calc a * y = (a * y * a⁻¹) * a := by group
      _ = y * a := by rw [← h1]
  have ha4 := cent_memBar_pow_four hn α h b hcomm
  have hpow : ∀ j : ℕ, ∀ g : ↥(TL4.aeModel n),
      (((θ ^ j) g : ↥(TL4.aeModel n)) : AEQ n) = a ^ j * g * (a ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro g; simp
    | succ j ih =>
      intro g
      rw [pow_succ' θ j, MulAut.mul_apply, ha, ih, pow_succ' a j]
      group
  have hθ4 : θ ^ 4 = 1 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [hpow 4 g]
    have : a ^ 4 = 1 := by
      calc a ^ 4 = a * a * (a * a) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
        _ = 1 := ha4
    rw [this]
    simp
  have hθk : θ ^ k = 1 := I.inducedAutOf_pow_eq_one hn5 hψk
  have hθ1 : θ = 1 := by
    have hcop : Nat.Coprime 4 k := by
      have : Nat.Coprime (2 ^ 2) k := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hk)
      simpa using this
    have := (pow_gcd_eq_one (a := θ)).mpr ⟨hθ4, hθk⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hcent : ∀ g : ↥(pSpan P), g⁻¹ * ψ g ∈ Subgroup.center ↥(pSpan P) := by
    intro g
    apply I.ker_le
    rw [← I.ker_toModel, MonoidHom.mem_ker, map_mul, map_inv, ← hθ g, hθ1, MulAut.one_apply,
      inv_mul_cancel]
  exact TwinDisc.AE5.fixed_of_cent F.gen F.trans hJ ψ.toMonoidHom hcent hfixJ

end Aut

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
