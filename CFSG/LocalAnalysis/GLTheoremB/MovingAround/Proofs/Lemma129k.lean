module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129g

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129k

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)

@[expose] def Input23_9 : Prop :=
  ∀ (p k n : ℕ), p.Prime → p ≠ 2 →
    ∀ B : Subgroup ↥(alternatingGroup (Fin n)), IsElemAbelian p B → k ≤ CFSG.Open.pRank p B →
      ∀ i : Fin n, (∃ b ∈ B, ((b : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) i ≠ i) →
        ∀ g : ↥(alternatingGroup (Fin n)),
          (∀ j : Fin n, (∀ b ∈ B, ((b : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) i ≠ j) →
            ((g : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) j = j) →
          g ∈ GLBCore p (k - 1) B

section Transport

theorem glbCore_le_comap {A Y : Type} [Group A] [Group Y] [Finite A] [Finite Y] {p k : ℕ}
    (hp : 1 < p) (f : A →* Y) (hf : Function.Injective f) (H : Subgroup A) :
    GLBCore p k H ≤ (GLBCore p k (H.map f)).comap f := by
  refine sSup_le ?_
  rintro _ ⟨Q, hQH, hQk, rfl⟩
  intro g hg
  show f g ∈ GLBCore p k (H.map f)
  have hQ' : Q.map f ≤ H.map f := Subgroup.map_mono hQH
  have hrk : k ≤ CFSG.Open.pRank p (Q.map f) := by
    rw [pRank_map_eq_of_injective hp f hf]
    exact hQk
  have hmem : Subgroup.normalizer ((Q.map f : Subgroup Y) : Set Y) ≤ GLBCore p k (H.map f) :=
    le_sSup ⟨Q.map f, hQ', hrk, rfl⟩
  apply hmem
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨g * q * g⁻¹, (hg q).1 hq, by simp⟩
  · rintro ⟨q', hq', hy⟩
    have hq'' : g⁻¹ * q' * g ∈ Q := by
      refine (hg (g⁻¹ * q' * g)).2 ?_
      have : g * (g⁻¹ * q' * g) * g⁻¹ = q' := by group
      rw [this]
      exact hq'
    refine ⟨g⁻¹ * q' * g, hq'', ?_⟩
    simp only [map_mul, map_inv]
    rw [hy]
    group

end Transport

section Core

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

theorem cycle_factor_mem_core (h239 : Input23_9) {n r : ℕ}
    (ψ : ↥(barX 3 N K) ≃* alternatingGroup (Fin n))
    {H : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N)} (hHK : H ≤ barX 3 N K)
    (hHel : IsElemAbelian 3 H) (hr : r ≤ CFSG.Open.pRank 3 H) {i : Fin n}
    (hmov : ∃ b ∈ permImage ψ H, b i ≠ i) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ alternatingGroup (Fin n))
    (hgsupp : ∀ j : Fin n, (∀ b ∈ permImage ψ H, b i ≠ j) → g j = j) :
    ((ψ.symm ⟨g, hg⟩ : ↥(barX 3 N K)) : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈ GLBCore 3 (r - 1) H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Bt : Subgroup ↥(alternatingGroup (Fin n)) := (H.subgroupOf (barX 3 N K)).map ψ.toMonoidHom
  have hBel : IsElemAbelian 3 Bt := (hHel.subgroupOf _).map _
  have hrank : CFSG.Open.pRank 3 Bt = CFSG.Open.pRank 3 H := by
    rw [pRank_map_eq_of_injective Nat.prime_three.one_lt ψ.toMonoidHom ψ.injective,
      ← pRank_map_eq_of_injective Nat.prime_three.one_lt (barX 3 N K).subtype
        (barX 3 N K).subtype_injective, Subgroup.map_subgroupOf_eq_of_le hHK]
  have hmemBt : ∀ x : ↥(barX 3 N K), (x : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈ H → ψ x ∈ Bt := by
    intro x hx
    exact ⟨x, (Subgroup.mem_subgroupOf).2 hx, rfl⟩
  have hmov' : ∃ b ∈ Bt, ((b : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) i ≠ i := by
    obtain ⟨b, hb, hbi⟩ := hmov
    obtain ⟨x, hx, rfl⟩ := (mem_permImage ψ).1 hb
    exact ⟨ψ x, hmemBt x hx, hbi⟩
  have hsupp' : ∀ j : Fin n, (∀ b ∈ Bt,
      ((b : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) i ≠ j) →
      ((⟨g, hg⟩ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) j = j := by
    intro j hj
    apply hgsupp
    intro b hb
    obtain ⟨x, hx, rfl⟩ := (mem_permImage ψ).1 hb
    exact hj _ (hmemBt x hx)
  have h1 := h239 3 r n Nat.prime_three (by norm_num) Bt hBel (hrank ▸ hr) i hmov' ⟨g, hg⟩ hsupp'
  let f : ↥(alternatingGroup (Fin n)) →* ↥N ⧸ GLAPPrimeCore 3 ↥N :=
    (barX 3 N K).subtype.comp ψ.symm.toMonoidHom
  have hf : Function.Injective f := (barX 3 N K).subtype_injective.comp ψ.symm.injective
  have hBf : Bt.map f = H := by
    simp only [Bt, Subgroup.map_map]
    have : f.comp ψ.toMonoidHom = (barX 3 N K).subtype := by
      ext x
      simp [f]
    rw [this, Subgroup.map_subgroupOf_eq_of_le hHK]
  have h2 := glbCore_le_comap Nat.prime_three.one_lt f hf Bt h1
  rw [hBf] at h2
  exact h2

end Core

section Gamma

open Equiv Equiv.Perm

theorem exists_two_cycles_avoiding {α : Type} [Fintype α] [DecidableEq α] {C : Finset (Perm α)}
    (hdisj : (C : Set (Perm α)).Pairwise Equiv.Perm.Disjoint) (hC4 : 4 ≤ C.card) (x y : α) :
    ∃ c ∈ C, ∃ c' ∈ C, c ≠ c' ∧ x ∉ c.support ∧ y ∉ c.support ∧ x ∉ c'.support ∧
      y ∉ c'.support := by
  classical
  have hone : ∀ z : α, (C.filter (fun c => z ∈ c.support)).card ≤ 1 := by
    intro z
    apply Finset.card_le_one.2
    intro a ha b hb
    by_contra hne
    have ha' := Finset.mem_filter.1 ha
    have hb' := Finset.mem_filter.1 hb
    rcases hdisj (Finset.mem_coe.2 ha'.1) (Finset.mem_coe.2 hb'.1) hne z with h1 | h1
    · exact (mem_support.1 ha'.2) h1
    · exact (mem_support.1 hb'.2) h1
  set D : Finset (Perm α) := C.filter (fun c => x ∉ c.support ∧ y ∉ c.support) with hD
  have hcov : C ⊆ D ∪ (C.filter (fun c => x ∈ c.support) ∪ C.filter (fun c => y ∈ c.support)) := by
    intro c hc
    by_cases hx : x ∈ c.support
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hc, hx⟩))
    · by_cases hy : y ∈ c.support
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hc, hy⟩))
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hc, hx, hy⟩)
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_union_le D (C.filter (fun c => x ∈ c.support) ∪ C.filter (fun c => y ∈ c.support))
  have h3 := Finset.card_union_le (C.filter (fun c => x ∈ c.support)) (C.filter (fun c => y ∈ c.support))
  have h4 := hone x
  have h5 := hone y
  have hD2 : 1 < D.card := by omega
  obtain ⟨c, hc, c', hc', hne⟩ := Finset.one_lt_card.1 hD2
  have hc1 := Finset.mem_filter.1 hc
  have hc2 := Finset.mem_filter.1 hc'
  exact ⟨c, hc1.1, c', hc2.1, hne, hc1.2.1, hc1.2.2, hc2.2.1, hc2.2.2⟩

theorem core_gamma2 {Cb : Type} [Group Cb] [Finite Cb] {p n s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Kb : Subgroup Cb) (ψ : ↥Kb ≃* ↥(alternatingGroup (Fin n)))
    (e1 : ↥Kb) (hcyc : ((ψ e1 : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)).cycleType =
      Multiset.replicate s p)
    (hs4 : 4 ≤ s) (hn : s * p < n) (Q : Subgroup Cb)
    (hQ : ∀ x : ↥Kb, ((ψ x : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) ∈
      ((ψ e1 : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)).cycleFactorsFinset →
        (x : Cb) ∈ Q) :
    ∃ P : Subgroup Cb, P ≤ Q ∧ P ≤ Kb ∧ IsElemAbelian p P ∧ p ^ s ≤ Nat.card P ∧
      Kb ≤ GLBCore p 2 P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let ι : ↥Kb →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp ψ.toMonoidHom
  have hι_inj : Function.Injective ι := fun x y hxy =>
    ψ.injective (Subtype.ext (show ((ψ x : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) =
      ((ψ y : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) from hxy))
  have hι_mem : ∀ x : ↥Kb, ι x ∈ alternatingGroup (Fin n) := fun x => (ψ x).2
  have hι_surj : ∀ y ∈ alternatingGroup (Fin n), ∃ x : ↥Kb, ι x = y := by
    intro y hy
    exact ⟨ψ.symm ⟨y, hy⟩, by simp [ι]⟩
  set π : Equiv.Perm (Fin n) := ι e1 with hπ
  set C : Finset (Equiv.Perm (Fin n)) := π.cycleFactorsFinset with hC
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hCc : ∀ c ∈ C, c.IsCycle ∧ c.support.card = p := fun c hc =>
    ⟨(Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1, Lemma116.card_support_of_mem hcyc hc⟩
  have hCcard : C.card = s := Lemma116.card_cycleFactorsFinset_of hcyc
  have hCdisj : (C : Set (Equiv.Perm (Fin n))).Pairwise Equiv.Perm.Disjoint :=
    Equiv.Perm.cycleFactorsFinset_pairwise_disjoint π
  have hCalt : ∀ c ∈ C, c ∈ alternatingGroup (Fin n) := by
    intro c hc
    rw [Equiv.Perm.mem_alternatingGroup, (hCc c hc).1.sign, (hCc c hc).2, Odd.neg_one_pow hodd,
      neg_neg]
  have hCcomm : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c := by
    intro c hc c' hc'
    by_cases h : c = c'
    · rw [h]
    · exact (hCdisj (Finset.mem_coe.2 hc) (Finset.mem_coe.2 hc') h).commute
  have hCpow : ∀ c ∈ C, c ^ p = 1 := by
    intro c hc
    rw [← (hCc c hc).2, ← (hCc c hc).1.orderOf]
    exact pow_orderOf_eq_one c
  have hCne : ∀ c ∈ C, c ≠ 1 := by
    intro c hc h1
    have := (hCc c hc).2
    rw [h1] at this
    simp at this
    exact hp.ne_zero this.symm
  set Kc : Set ↥Kb := {x | ι x ∈ C} with hKc
  have hKc_surj : ∀ c ∈ C, ∃ x ∈ Kc, ι x = c := by
    intro c hc
    obtain ⟨x, hx⟩ := hι_surj c (hCalt c hc)
    exact ⟨x, by simp [hKc, hx, hc], hx⟩
  have hKc_image : ι '' Kc = (C : Set (Equiv.Perm (Fin n))) := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_coe.2 hx
    · intro hc
      obtain ⟨x, hx, hxc⟩ := hKc_surj c (Finset.mem_coe.1 hc)
      exact ⟨x, hx, hxc⟩
  have hKc_comm : ∀ x ∈ Kc, ∀ y ∈ Kc, x * y = y * x := by
    intro x hx y hy
    apply hι_inj
    rw [map_mul, map_mul]
    exact hCcomm _ hx _ hy
  have hKc_pow : ∀ x ∈ Kc, x ^ p = 1 := by
    intro x hx
    apply hι_inj
    rw [map_pow, map_one]
    exact hCpow _ hx
  have hKc_ne : ∀ x ∈ Kc, x ≠ 1 := by
    intro x hx h1
    apply hCne (ι x) hx
    rw [h1, map_one]
  set P : Subgroup Cb := (Subgroup.closure Kc).map Kb.subtype with hP
  have hPab : IsElemAbelian p P :=
    (Lemma116.isElemAbelian_closure_of_comm Kc hKc_comm hKc_pow).map _
  have hPK_card : p ^ s ≤ Nat.card (Subgroup.closure Kc) := by
    have h1 : Nat.card ((Subgroup.closure Kc).map ι) = Nat.card (Subgroup.closure Kc) :=
      Subgroup.card_map_of_injective hι_inj
    rw [← h1, MonoidHom.map_closure, hKc_image]
    have := Lemma116.card_closure_ge hp C hCc hCdisj
    rw [hCcard] at this
    exact this
  have hPcard : p ^ s ≤ Nat.card P := by
    have h1 : Nat.card P = Nat.card (Subgroup.closure Kc) :=
      Subgroup.card_map_of_injective Kb.subtype_injective
    rw [h1]
    exact hPK_card
  have hPQ : P ≤ Q := by
    rw [hP, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    exact hQ x hx
  have hPK : P ≤ Kb := Subgroup.map_subtype_le _
  obtain ⟨w, hw⟩ := Lemma116.exists_fixed_of_card_lt hcyc (by simpa using hn)
  have hwπ : w ∉ π.support := by
    rw [Equiv.Perm.mem_support, not_not]
    exact hw
  have hwC : ∀ c ∈ C, w ∉ c.support := fun c hc hwc =>
    hwπ (Equiv.Perm.mem_cycleFactorsFinset_support_le hc hwc)
  set Tset : Set (Equiv.Perm (Fin n)) := {τ | τ.IsThreeCycle ∧ w ∈ τ.support} with hTset
  have hT_gen : Subgroup.closure Tset = alternatingGroup (Fin n) :=
    Lemma116.closure_threeCycles_through w
  set Tk : Set ↥Kb := {x | ι x ∈ Tset} with hTk
  have hTset_alt : ∀ τ ∈ Tset, τ ∈ alternatingGroup (Fin n) :=
    fun τ hτ => hτ.1.mem_alternatingGroup
  have hTk_image : ι '' Tk = Tset := by
    ext τ
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hτ
      obtain ⟨x, hx⟩ := hι_surj τ (hTset_alt τ hτ)
      exact ⟨x, show ι x ∈ Tset from by rw [hx]; exact hτ, hx⟩
  have hmap : (Subgroup.closure Tk).map ι = Subgroup.closure Tset := by
    rw [MonoidHom.map_closure, hTk_image]
  have hall : ∀ x : ↥Kb, x ∈ Subgroup.closure Tk := by
    intro x
    have h1 : ι x ∈ (Subgroup.closure Tk).map ι := by
      rw [hmap, hT_gen]
      exact hι_mem x
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 h1
    have hzx' : z = x := hι_inj hzx
    rw [← hzx']
    exact hz
  have claim1 : ∀ x ∈ Tk, ((x : ↥Kb) : Cb) ∈ GLBCore p 2 P := by
    intro x hx
    have hx' : ι x ∈ Tset := hx
    obtain ⟨h3, hwτ⟩ := hx'
    have hE : ((ι x).support.erase w).card = 2 := by
      rw [Finset.card_erase_of_mem hwτ, h3.card_support]
    obtain ⟨a, b, hab, hEq⟩ := Finset.card_eq_two.1 hE
    have hmemτ : ∀ y, y ∈ (ι x).support → y = w ∨ y = a ∨ y = b := by
      intro y hy
      by_cases hyw : y = w
      · exact Or.inl hyw
      · have hy2 : y ∈ (ι x).support.erase w := Finset.mem_erase.2 ⟨hyw, hy⟩
        rw [hEq] at hy2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy2
        exact Or.inr hy2
    obtain ⟨c, hc, c', hc', hcc', hac, hbc, hac', hbc'⟩ :=
      exists_two_cycles_avoiding hCdisj (by rw [hCcard]; exact hs4) a b
    obtain ⟨xc, hxc, hιxc⟩ := hKc_surj c hc
    obtain ⟨xc', hxc', hιxc'⟩ := hKc_surj c' hc'
    have hdisj : ∀ d ∈ C, (d = c ∨ d = c') → Equiv.Perm.Disjoint d (ι x) := by
      intro d hd hdc y
      by_cases hy : y ∈ d.support
      · right
        by_contra hne
        have hyτ : y ∈ (ι x).support := Equiv.Perm.mem_support.2 hne
        rcases hmemτ y hyτ with h | h | h
        · exact hwC d hd (h ▸ hy)
        · rcases hdc with rfl | rfl
          · exact hac (h ▸ hy)
          · exact hac' (h ▸ hy)
        · rcases hdc with rfl | rfl
          · exact hbc (h ▸ hy)
          · exact hbc' (h ▸ hy)
      · left
        by_contra hne
        exact hy (Equiv.Perm.mem_support.2 hne)
    have hxcx : xc * x = x * xc := by
      apply hι_inj
      rw [map_mul, map_mul, hιxc]
      exact (hdisj c hc (Or.inl rfl)).commute.eq
    have hxcx' : xc' * x = x * xc' := by
      apply hι_inj
      rw [map_mul, map_mul, hιxc']
      exact (hdisj c' hc' (Or.inr rfl)).commute.eq
    have hxcb_pow : (xc : Cb) ^ p = 1 := by
      have h := congrArg (fun z : ↥Kb => (z : Cb)) (hKc_pow xc hxc)
      simpa using h
    have hxcb_pow' : (xc' : Cb) ^ p = 1 := by
      have h := congrArg (fun z : ↥Kb => (z : Cb)) (hKc_pow xc' hxc')
      simpa using h
    have hxcb_ne : (xc : Cb) ≠ 1 := fun h => hKc_ne xc hxc (Subtype.ext h)
    have hxcb_ne' : (xc' : Cb) ≠ 1 := fun h => hKc_ne xc' hxc' (Subtype.ext h)
    have hxcc' : (xc : Cb) * (xc' : Cb) = (xc' : Cb) * (xc : Cb) := by
      have := hKc_comm xc hxc xc' hxc'
      exact congrArg Subtype.val this
    have hind : ∀ i j : ℕ, (xc : Cb) ^ i = (xc' : Cb) ^ j → (xc : Cb) ^ i = 1 := by
      intro i j hij
      have h1 : xc ^ i = xc' ^ j := Subtype.ext (by simpa using hij)
      have h2 : c ^ i = c' ^ j := by
        have := congrArg ι h1
        rw [map_pow, map_pow, hιxc, hιxc'] at this
        exact this
      have hD : Equiv.Perm.Disjoint c c' :=
        hCdisj (Finset.mem_coe.2 hc) (Finset.mem_coe.2 hc') hcc'
      have h3 : c ^ i = 1 := by
        refine Equiv.ext fun t => ?_
        rcases hD t with ht | ht
        · exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self ht i
        · have h4 : c' ^ j = 1 := by
            refine Equiv.ext fun t' => ?_
            rcases hD t' with ht' | ht'
            · rw [← h2]
              exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self ht' i
            · exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self ht' j
          rw [h2, h4]
      have h5 : xc ^ i = 1 := by
        apply hι_inj
        rw [map_pow, hιxc, h3, map_one]
      have h6 := congrArg (fun z : ↥Kb => (z : Cb)) h5
      simpa using h6
    have hQrank : 2 ≤ CFSG.Open.pRank p (Subgroup.closure ({(xc : Cb), (xc' : Cb)} : Set Cb)) :=
      Lemma116.two_le_pRank_pair hp hxcc' hxcb_pow hxcb_pow' hxcb_ne hxcb_ne' hind
    have hQP : Subgroup.closure ({(xc : Cb), (xc' : Cb)} : Set Cb) ≤ P := by
      rw [Subgroup.closure_le]
      intro u hu
      rcases hu with h | h
      · rw [h]
        exact ⟨xc, Subgroup.subset_closure hxc, rfl⟩
      · rw [h]
        exact ⟨xc', Subgroup.subset_closure hxc', rfl⟩
    have hxnorm : ((x : ↥Kb) : Cb) ∈
        Subgroup.normalizer ((Subgroup.closure ({(xc : Cb), (xc' : Cb)} : Set Cb) : Subgroup Cb) :
          Set Cb) := by
      apply Lemma116.mem_normalizer_closure_of_comm
      intro s' hs'
      rcases hs' with h | h
      · rw [h]
        exact (congrArg Subtype.val hxcx).symm
      · rw [h]
        exact (congrArg Subtype.val hxcx').symm
    exact normalizer_le_glbCore hQP hQrank hxnorm
  have hKb : Kb ≤ GLBCore p 2 P := by
    intro g hg
    have hmem := hall ⟨g, hg⟩
    have hle : Subgroup.closure Tk ≤ (GLBCore p 2 P).comap Kb.subtype := by
      rw [Subgroup.closure_le]
      intro x hx
      exact claim1 x hx
    exact hle hmem
  exact ⟨P, hPQ, hPK, hPab, hPcard, hKb⟩

end Gamma

section CoreM

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}

theorem core_le_M (h : Sec11 G m p B M E A) {r : ℕ} (hr2 : 2 ≤ r) (hnot : ¬ (p = 3 ∧ r = 2))
    (hk : CFSG.Open.pRank p (E ⊓ A) ≤ r) {S : Subgroup G} (hSM : S ≤ M)
    (hSab : IsElemAbelian p S) (hrank : p ^ (r - 1) ≤ CFSG.Open.pRank p S) :
    GLBCore p 2 S ≤ M := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hS.ne_two
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h3 | h3
    · exfalso; apply hp2; omega
    · exact h3
  have hSp : IsPGroup p S := hSab.isPGroup
  have hScard : p ^ (p ^ (r - 1)) ≤ Nat.card S := by
    rw [Lemma116.card_eq_pow_pRank hp hSab]
    exact Nat.pow_le_pow_right hp.pos hrank
  obtain ⟨F, hFS, hFab, hFcard⟩ := Lemma116.exists_sub_card hp hSab (j := p ^ (r - 1)) hScard
  have hFM : F ≤ M := hFS.trans hSM
  have hE𝒟 : inD p M E := h.pair.1.1
  have hEM2 : IsTwoLocal M := hE𝒟.2.maxTwoLocal.1
  have hsTLR : p ^ (r - 1) ≤ GLATwoLocalRank p G :=
    Lemma116.le_twoLocalRank hp hEM2 hFM hFab hFcard
  have hBD : inD p M B := lemma101_ii_holds h.toSec10Fails
  have hBM : B ≤ M := hBD.1.1.1
  obtain ⟨hBab, hBcard, -⟩ := h.bOne.1
  have hBp : IsPGroup p B := hBab.isPGroup
  obtain ⟨y, hyM, R, hSR, hBR, hRp⟩ := Lemma116.exists_sylow_cover hp hSM hBM hSp hBp
  have hB'D : inD p M (GLBConj y B) :=
    (lemma101_i_holds h.toSec10Fails hyM hBD h.pair.1.2.1).1
  have hB'ab : IsElemAbelian p (GLBConj y B) := hB'D.1.1.2.1
  have hB'card : Nat.card (GLBConj y B) = p ^ GLATwoLocalRank p G := by
    rw [← hBcard]
    unfold GLBConj
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have hcardB' : p ^ (p ^ (r - 1)) ≤ Nat.card (GLBConj y B) := by
    rw [hB'card]
    exact Nat.pow_le_pow_right hp.pos hsTLR
  obtain ⟨U, hUB, hUab, hUcard⟩ := Lemma116.exists_sub_card hp hB'ab hcardB'
  have hFek : IsEkIn p (p ^ (r - 1)) R F := ⟨hFS.trans hSR, hFab, hFcard⟩
  have hUek : IsEkIn p (p ^ (r - 1)) R U := ⟨hUB.trans hBR, hUab, hUcard⟩
  have hRconn : IsKConnectedIn p (r + 1) R F U :=
    input31_9_holds G p r hp hp2 hr2 hnot R hRp F U hFek hUek
  have hk1 : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ r + 1 := by omega
  have hconnk := Lemma116.isKConnectedIn_lower hp hk1 hRconn
  obtain ⟨Es, hEsSC, hS_Es⟩ := Lemma116.exists_isSCp_above hSab
  have hcardEs : p ^ (CFSG.Open.pRank p (E ⊓ A) + 1) ≤ Nat.card Es := by
    have h1 : p ^ (CFSG.Open.pRank p (E ⊓ A) + 1) ≤ p ^ (p ^ (r - 1)) :=
      Nat.pow_le_pow_right hp.pos (hk1.trans (Lemma116.succ_le_pow_pred hp3 hr2))
    exact h1.trans (hScard.trans (Subgroup.card_le_of_le hS_Es))
  have hcardB'' : p ^ (CFSG.Open.pRank p (E ⊓ A) + 1) ≤ Nat.card (GLBConj y B) := by
    refine le_trans ?_ hcardB'
    exact Nat.pow_le_pow_right hp.pos (hk1.trans (Lemma116.succ_le_pow_pred hp3 hr2))
  have hconnE : IsKConnectedIn p (CFSG.Open.pRank p (E ⊓ A) + 1) ⊤ Es (GLBConj y B) :=
    Lemma116.isKConnectedIn_extend hp le_top hconnk (hFS.trans hS_Es) hUB hEsSC.2.1 hB'ab hcardEs
      hcardB'' le_top le_top
  have hEsD : inD p M Es := lemma104_iii_holds h.toSec10Fails h.pair hEsSC hB'D hconnE
  exact (Lemma116.glbCore_mono hS_Es).trans hEsD.2.clause_d

end CoreM

section PermFacts

theorem orbit_regular {α : Type} [Finite α] {B : Subgroup (Equiv.Perm α)}
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {i : α}
    (hcard : Set.ncard {j | ∃ g ∈ B, g i = j} = Nat.card B) :
    ∀ b ∈ B, ∀ j, (∃ g ∈ B, g i = j) → b j = j → b = 1 := by
  classical
  let φ : ↥B → ↥{j | ∃ g ∈ B, g i = j} := fun g => ⟨(g : Equiv.Perm α) i, g, g.2, rfl⟩
  have hφs : Function.Surjective φ := by
    rintro ⟨j, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  have hcard' : Nat.card ↥B ≤ Nat.card ↥{j | ∃ g ∈ B, g i = j} := by
    rw [Nat.card_coe_set_eq, hcard]
  have hφb := hφs.bijective_of_nat_card_le hcard'
  intro b hb j hj hbj
  obtain ⟨g, hg, rfl⟩ := hj
  have h1 : b (g i) = g (b i) := congrArg (fun f => f i) (hB b hb g hg)
  have h2 : b i = i := g.injective (by rw [← h1]; exact hbj)
  have h3 : φ ⟨b, hb⟩ = φ 1 := Subtype.ext (by simpa [φ] using h2)
  have h4 := hφb.1 h3
  exact congrArg Subtype.val h4

theorem cycleType_of_pow_three {α : Type} [Fintype α] [DecidableEq α] {b : Equiv.Perm α}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    ∃ s : ℕ, b.cycleType = Multiset.replicate s 3 ∧ b.support.card = s * 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (hσ := by rw [hord]; exact Nat.prime_three)
  rw [hord] at hk
  exact ⟨k + 1, hk, Lemma116.card_support_eq_of hk⟩

end PermFacts

section GenCore

variable {G : Type} [Group G] [Finite G]

theorem glbCore_mono_k {p k k' : ℕ} (hk : k' ≤ k) (P : Subgroup G) :
    GLBCore p k P ≤ GLBCore p k' P := by
  refine sSup_le ?_
  rintro _ ⟨Q, hQP, hQk, rfl⟩
  exact le_sSup ⟨Q, hQP, hk.trans hQk, rfl⟩

theorem barX_inf_right {p : ℕ} {N M : Subgroup G} : barX p N (M ⊓ N) = barX p N M := by
  unfold barX
  rw [Subgroup.inf_subgroupOf_right]

theorem glbCore_barX_le_barX_M' {p : ℕ} {N M P : Subgroup G} (hp : p.Prime) (hPN : P ≤ N)
    (hPel : IsElemAbelian p P)
    (hnorm : ∀ X : Subgroup G, X ≤ P → 2 ≤ CFSG.Open.pRank p X →
      Subgroup.normalizer (X : Set G) ≤ M) :
    GLBCore p 2 (barX p N P) ≤ barX p N M := by
  refine sSup_le ?_
  rintro _ ⟨Q, hQP, hQ2, rfl⟩
  obtain ⟨E', hE'P, hE'Q, hE'r⟩ := exists_le_barX_eq hp hPel.isPGroup hPN hQP
  have hE'N : E' ≤ N := hE'P.trans hPN
  rw [← hE'Q]
  refine (normalizer_barX_le hp (hPel.isPGroup.to_le hE'P) hE'N).trans (barX_mono129 ?_)
  have hrank2 : 2 ≤ CFSG.Open.pRank p E' := by rw [hE'r]; exact hQ2
  exact hnorm E' hE'P hrank2

end GenCore

section Final

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129e
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129f
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129g
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (card_barX_of_isPGroup elemAbelian_barX)

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D S F K : Subgroup G}

theorem alt_rank_two (h239 : Input23_9) (h23 : Input23_5) (h121 : Prop121_corStatement)
    (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (D' : AltData p N K F) (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.Open.pRank p F = 2 := by
  have hp := prime_of h
  have hFA := alt_F_ne_A h23 h hs D'
  obtain ⟨hp3, hδ4⟩ := alt_p_three_delta_four h121 h hs D' hAK hFA
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 := ne_two_of h
  by_contra hr2
  have hr3 : 3 ≤ CFSG.Open.pRank 3 F := by
    have := hs.hr
    omega
  obtain ⟨hm1, htrans, a, haA, hAeq, hFa, σ, hσ3, hσsupp, hperm⟩ :=
    alt_structure h hs D' hAK hFA rfl hδ4
  have hn : D'.n = 3 ^ CFSG.Open.pRank 3 F + 4 := by
    have := D'.hn
    rw [hδ4, hm1] at this
    simpa using this
  have hAN := A_le_N h
  have hFA' := hs.F_le_A
  have hFN : F ≤ N := hFA'.trans hAN
  have hle := alt_le_K h hs D' hAK hFA rfl hδ4
  have hn11 := D'.hn11 (le_refl 3) hs.hr
  have hA0N : E ⊓ A ≤ N := inf_le_right.trans hAN
  have hA0el : IsElemAbelian 3 (E ⊓ A) := (A_el h).mono inf_le_right
  have hA0K : barX 3 N (E ⊓ A) ≤ barX 3 N K := (barX_mono129 inf_le_right).trans hle
  have hH : barX 3 N (E ⊓ A) ≤
      Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    barX_le_normalizer (inf_le_right.trans hAK)
  have hHp : IsPGroup 3 ↥(barX 3 N (E ⊓ A)) := Lemma129.isPGroup_barX hA0el.isPGroup hA0N
  obtain ⟨κ₀, hκ₀⟩ := exists_implementer (by omega) (by omega) D'.ψ hp hp2 hH hHp
  have hκself : ∀ a : ↥(barX 3 N (E ⊓ A)), κ₀ a = ⟨(a : ↥N ⧸ GLAPPrimeCore 3 ↥N), hA0K a.2⟩ := by
    intro a
    apply impl_unique (by omega) D'.ψ
    intro x
    rw [← hκ₀ a x]
  have hAr : CFSG.Open.pRank 3 A = CFSG.Open.pRank 3 F + 1 := by
    have h1 := card_A_of_ne hp hs hFA
    rw [card_eq_pow_pRank hp (A_el h), card_eq_pow_pRank hp ((A_el h).mono hFA'),
      ← pow_succ'] at h1
    exact (Nat.pow_right_injective hp.two_le) h1
  obtain ⟨i, hi⟩ := alt_orbit_big h23 h hs D' hAK (Or.inr ⟨rfl, hδ4, hAr⟩) κ₀ hκ₀
  have hA0card : Nat.card (E ⊓ A : Subgroup G) ≤ 3 ^ CFSG.Open.pRank 3 F := by
    have hAcard : Nat.card A = 3 ^ (CFSG.Open.pRank 3 F + 1) := by
      rw [card_eq_pow_pRank hp (A_el h), hAr]
    have hlt : Nat.card (E ⊓ A : Subgroup G) < Nat.card A := card_lt_of_lt' (A0_lt_A h)
    have hdvd : Nat.card (E ⊓ A : Subgroup G) ∣ 3 ^ (CFSG.Open.pRank 3 F + 1) := by
      have := Subgroup.card_dvd_of_le (inf_le_right : E ⊓ A ≤ A)
      rwa [hAcard] at this
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [hjeq] at hlt ⊢
    rw [hAcard] at hlt
    have : j < CFSG.Open.pRank 3 F + 1 := by
      by_contra hj3
      have : 3 ^ (CFSG.Open.pRank 3 F + 1) ≤ 3 ^ j := Nat.pow_le_pow_right hp.pos (by omega)
      omega
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hB₀el : IsElemAbelian 3 (permImage D'.ψ (barX 3 N (E ⊓ A))) :=
    permImage_elemAbelian D'.ψ (isElemAbelian_barX hA0el)
  have hB₀card : Nat.card (permImage D'.ψ (barX 3 N (E ⊓ A))) = Nat.card (E ⊓ A : Subgroup G) := by
    rw [permImage_card D'.ψ hA0K, card_barX_of_isPGroup hp hA0N hA0el.isPGroup]
  have hset : {j : Fin D'.n | ∃ b ∈ κ₀.range,
      ((D'.ψ b : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) i = j} =
      {j : Fin D'.n | ∃ g ∈ permImage D'.ψ (barX 3 N (E ⊓ A)), g i = j} := by
    ext j
    constructor
    · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
      refine ⟨_, (mem_permImage D'.ψ).2 ⟨κ₀ a, ?_, rfl⟩, rfl⟩
      rw [hκself a]
      exact a.2
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (mem_permImage D'.ψ).1 hg
      refine ⟨x, ⟨⟨x, hx⟩, ?_⟩, rfl⟩
      rw [hκself]
  have hlen : orbitLen D'.ψ κ₀.range i =
      Set.ncard {j : Fin D'.n | ∃ g ∈ permImage D'.ψ (barX 3 N (E ⊓ A)), g i = j} := by
    unfold orbitLen
    rw [hset]
  have hrange_card : Nat.card κ₀.range ≤ Nat.card (E ⊓ A : Subgroup G) := by
    have h2 : Nat.card κ₀.range ≤ Nat.card (barX 3 N (E ⊓ A)) :=
      Nat.card_le_card_of_surjective _ κ₀.rangeRestrict_surjective
    rwa [card_barX_of_isPGroup hp hA0N hA0el.isPGroup] at h2
  have hlen_le := orbitLen_le_card D'.ψ κ₀.range i
  have hΩ₁ : Set.ncard {j : Fin D'.n | ∃ g ∈ permImage D'.ψ (barX 3 N (E ⊓ A)), g i = j} =
      3 ^ CFSG.Open.pRank 3 F := by
    rw [← hlen]
    omega
  have hA0eq : Nat.card (E ⊓ A : Subgroup G) = 3 ^ CFSG.Open.pRank 3 F := by omega
  have hB₀card' : Nat.card (permImage D'.ψ (barX 3 N (E ⊓ A))) = 3 ^ CFSG.Open.pRank 3 F := by
    rw [hB₀card, hA0eq]
  have hreg := orbit_regular (fun a ha b hb => elemAbelian_comm hB₀el ha hb) (i := i)
    (by rw [hΩ₁, hB₀card'])
  have hrkH : CFSG.Open.pRank 3 (barX 3 N (E ⊓ A)) = CFSG.Open.pRank 3 F := by
    have h1 := card_barX_of_isPGroup hp hA0N hA0el.isPGroup
    rw [card_eq_pow_pRank hp (isElemAbelian_barX hA0el), hA0eq] at h1
    exact (Nat.pow_right_injective hp.two_le) h1
  have hrkA0 : CFSG.Open.pRank 3 (E ⊓ A) = CFSG.Open.pRank 3 F := by
    have h1 := hA0eq
    rw [card_eq_pow_pRank hp hA0el] at h1
    exact (Nat.pow_right_injective hp.two_le) h1
  obtain ⟨b, hbB₀, hb1⟩ : ∃ b ∈ permImage D'.ψ (barX 3 N (E ⊓ A)), b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card (permImage D'.ψ (barX 3 N (E ⊓ A))) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b' => Subtype.ext ((hcon a a.2).trans (hcon b' b'.2).symm)⟩,
        ⟨1⟩⟩
    rw [hB₀card'] at h1
    have h2 : 1 < 3 ^ CFSG.Open.pRank 3 F := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hbalt : b ∈ alternatingGroup (Fin D'.n) := permImage_le_alt D'.ψ hbB₀
  have hb3 : b ^ 3 = 1 := hB₀el.2 b hbB₀
  obtain ⟨sc, hcyc, hsupp⟩ := cycleType_of_pow_three hb3 hb1
  have hmoves : ∀ j ∈ {j : Fin D'.n | ∃ g ∈ permImage D'.ψ (barX 3 N (E ⊓ A)), g i = j},
      b j ≠ j := by
    intro j hj hbj
    exact hb1 (hreg b hbB₀ j hj hbj)
  have hΩsub : {j : Fin D'.n | ∃ g ∈ permImage D'.ψ (barX 3 N (E ⊓ A)), g i = j} ⊆
      (b.support : Set (Fin D'.n)) := fun j hj => by
    rw [Finset.mem_coe, Equiv.Perm.mem_support]
    exact hmoves j hj
  have hsc_ge : 3 ^ CFSG.Open.pRank 3 F ≤ sc * 3 := by
    have h1 := Set.ncard_le_ncard hΩsub (Finset.finite_toSet _)
    rw [hΩ₁, Set.ncard_coe_finset, hsupp] at h1
    exact h1
  have hsc_le : sc * 3 ≤ D'.n := by
    rw [← hsupp]
    simpa using Finset.card_le_univ b.support
  obtain ⟨t, ht⟩ : ∃ t, 3 ^ CFSG.Open.pRank 3 F = 3 * t ∧ 9 ≤ t := by
    obtain ⟨r', hr'⟩ : ∃ r', CFSG.Open.pRank 3 F = r' + 3 := ⟨CFSG.Open.pRank 3 F - 3, by omega⟩
    refine ⟨3 ^ (r' + 2), by rw [hr']; ring, ?_⟩
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (r' + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsc4 : 4 ≤ sc := by omega
  have hsc_lt : sc * 3 < D'.n := by
    have hne : sc * 3 ≠ D'.n := by omega
    omega
  have hsct : t ≤ sc := by omega
  have hnormA0 : ∀ X : Subgroup G, X ≤ E ⊓ A → 2 ≤ CFSG.Open.pRank 3 X →
      Subgroup.normalizer (X : Set G) ≤ M := fun X hX hXr =>
    (normalizer_le_glbCore (hX.trans inf_le_left) hXr).trans (uniq_E h).clause_d
  have hΓM : GLBCore 3 2 (barX 3 N (E ⊓ A)) ≤ barX 3 N M :=
    glbCore_barX_le_barX_M' hp hA0N hA0el hnormA0
  let e1 : ↥(barX 3 N K) := D'.ψ.symm ⟨b, hbalt⟩
  have hψe1 : ((D'.ψ e1 : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) = b := by
    simp [e1]
  have hQ : ∀ x : ↥(barX 3 N K),
      ((D'.ψ x : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) ∈
        ((D'.ψ e1 : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)).cycleFactorsFinset →
        (x : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈ barX 3 N M := by
    intro x hx
    rw [hψe1] at hx
    have hcycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hx).1
    obtain ⟨i', hi'⟩ := hcycle.nonempty_support
    have hcb : ((D'.ψ x : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) = b.cycleOf i' :=
      Equiv.Perm.cycle_is_cycleOf hi' hx
    have hi'b : i' ∈ b.support := Equiv.Perm.mem_cycleFactorsFinset_support_le hx hi'
    have hmov : ∃ b' ∈ permImage D'.ψ (barX 3 N (E ⊓ A)), b' i' ≠ i' :=
      ⟨b, hbB₀, Equiv.Perm.mem_support.1 hi'b⟩
    have hgsupp : ∀ j : Fin D'.n, (∀ b' ∈ permImage D'.ψ (barX 3 N (E ⊓ A)), b' i' ≠ j) →
        ((D'.ψ x : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) j = j := by
      intro j hj
      by_contra hne
      have hjs : j ∈ (((D'.ψ x : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n))).support :=
        Equiv.Perm.mem_support.2 hne
      rw [hcb] at hjs
      obtain ⟨⟨k, hk⟩, -⟩ := Equiv.Perm.mem_support_cycleOf_iff.1 hjs
      exact hj (b ^ k) (zpow_mem hbB₀ k) hk
    have hmem := cycle_factor_mem_core h239 (r := CFSG.Open.pRank 3 F) D'.ψ hA0K
      (isElemAbelian_barX hA0el) hrkH.ge hmov (D'.ψ x).2 hgsupp
    have hxeq : D'.ψ.symm ⟨((D'.ψ x : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)),
        (D'.ψ x).2⟩ = x := by
      have : (⟨((D'.ψ x : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)), (D'.ψ x).2⟩ :
          alternatingGroup (Fin D'.n)) = D'.ψ x := Subtype.ext rfl
      rw [this]
      exact D'.ψ.symm_apply_apply x
    rw [hxeq] at hmem
    exact hΓM (glbCore_mono_k (by omega) _ hmem)
  obtain ⟨P, hPQ, hPK, hPel, hPcard, hKP⟩ := core_gamma2 hp hp2 (barX 3 N K) D'.ψ e1
    (by rw [hψe1]; exact hcyc) hsc4 hsc_lt (barX 3 N M) hQ
  have hPM : P ≤ barX 3 N (M ⊓ N) := by
    rw [barX_inf_right]
    exact hPQ
  obtain ⟨S₁, hS₁MN, hS₁p, hS₁bar⟩ := Lemma116.exists_lift hp (inf_le_right : M ⊓ N ≤ N) hPM
    hPel.isPGroup
  have hS₁M : S₁ ≤ M := hS₁MN.trans inf_le_left
  have hS₁N : S₁ ≤ N := hS₁MN.trans inf_le_right
  have hS₁el : IsElemAbelian 3 S₁ :=
    Lemma116.elemAbelian_of_barX_elemAbelian hp hS₁N hS₁p (by rw [hS₁bar]; exact hPel)
  have hS₁rank : 3 ^ (CFSG.Open.pRank 3 F - 1) ≤ CFSG.Open.pRank 3 S₁ := by
    have h1 := card_barX_of_isPGroup hp hS₁N hS₁p
    rw [hS₁bar] at h1
    have h2 : 3 ^ sc ≤ Nat.card S₁ := h1 ▸ hPcard
    rw [card_eq_pow_pRank hp hS₁el] at h2
    have h3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
    have h4 : 3 ^ (CFSG.Open.pRank 3 F - 1) ≤ sc := by
      have h5 : 3 ^ CFSG.Open.pRank 3 F = 3 * 3 ^ (CFSG.Open.pRank 3 F - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    omega
  have hnot : ¬ (3 = 3 ∧ CFSG.Open.pRank 3 F = 2) := fun h' => hr2 h'.2
  have hcoreM : GLBCore 3 2 S₁ ≤ M :=
    core_le_M h.toSec11 (r := CFSG.Open.pRank 3 F) hs.hr hnot hrkA0.le hS₁M hS₁el hS₁rank
  have hnormS : ∀ X : Subgroup G, X ≤ S₁ → 2 ≤ CFSG.Open.pRank 3 X →
      Subgroup.normalizer (X : Set G) ≤ M := fun X hX hXr =>
    (normalizer_le_glbCore hX hXr).trans hcoreM
  have hΓS : GLBCore 3 2 (barX 3 N S₁) ≤ barX 3 N M :=
    glbCore_barX_le_barX_M' hp hS₁N hS₁el hnormS
  rw [hS₁bar] at hΓS
  exact hs.hnc (hKP.trans hΓS)

end Final

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129k

end
