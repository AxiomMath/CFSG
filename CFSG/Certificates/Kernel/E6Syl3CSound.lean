module

public import Certificates.Data.Kernel.E6Syl3C
public import CFSG.Certificates.Kernel.E6Syl3PSound
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3CaseITau

public section

namespace CFSG.KC.E6Syl3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3 CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint


noncomputable def nodeSub : Subgroup (WeylGroup Tag.E6) where
  carrier := {w | E6FixesNode3 w}
  mul_mem' {a b} ha hb γ hγ := by
    rw [mul_smul]
    exact (ha _ (IsRoot.smul hγ b)).trans (hb γ hγ)
  one_mem' γ _ := by rw [one_smul]
  inv_mem' {a} ha γ hγ := by
    have h := ha _ (IsRoot.smul hγ a⁻¹)
    rw [smul_inv_smul] at h
    exact h.symm

theorem mem_nodeSub {w : WeylGroup Tag.E6} : w ∈ nodeSub ↔ E6FixesNode3 w := Iff.rfl

theorem n3_eq (k : ℕ) : n3 k = e6Certificate.root k 3 := rfl

theorem fixN3_sound {t : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    (h : fixN3 t = true) : w ∈ nodeSub := by
  intro γ hγ
  obtain ⟨k, hk, rfl⟩ := exists_root72 hγ
  simp only [fixN3, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have e := h k hk
  have g3 : ∀ v : Fin Tag.E6.rank → ℤ, (List.ofFn v).getD 3 0 = v 3 := fun v => getD_ofFn6 v 3
  rw [actV_rvL hrep, g3, n3_eq] at e
  exact (Int.ModEq.symm ((Int.modEq_iff_dvd).2 (Int.dvd_of_emod_eq_zero e)))

theorem qSub_le_nodeSub {gw : List (List ℕ)} (hl : ∀ w ∈ gw, ∀ i ∈ w, i < 6)
    (h : genN3 gw = true) : qSub gw ≤ nodeSub := by
  refine qSub_le fun w hw => ?_
  simp only [genN3, List.all_eq_true] at h
  have hrep := rep_wordT (RootCertificate.represents_one (C := e6Certificate) e6Certificate_check)
    w (hl w hw)
  rw [mul_one] at hrep
  exact fixN3_sound hrep (h w hw)

theorem factorization_of_dvd {m : ℕ} (h1 : 81 ∣ m) (h2 : m ∣ 51840) : m.factorization 3 = 4 := by
  obtain ⟨k, rfl⟩ := h1
  have hk : k ∣ 640 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 81) (by simpa using h2)
  have hk0 : k ≠ 0 := by rintro rfl; norm_num at hk
  have h3 : ¬ 3 ∣ k := fun h => absurd (h.trans hk) (by norm_num)
  rw [Nat.factorization_mul (by norm_num) hk0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h3, add_zero]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three, show (81 : ℕ) = 3 ^ 4 by norm_num,
    padicValNat.prime_pow]

theorem exists_conj_yIN {gw wd lt : List (List ℕ)} (hF : QFacts gw wd lt)
    (hcard : Nat.card (qSub gw) = 81) (hQN : qSub gw ≤ nodeSub)
    {s : Set (WeylGroup Tag.E6)} (hsN : s ⊆ nodeSub) (hs : ∀ a ∈ s, ∀ b ∈ s, Commute a b)
    (h3 : ∀ a ∈ s, a ^ 3 = 1) :
    ∃ g ∈ nodeSub, ∀ x ∈ s, ∃ i < 81, MulAut.conj g (yI gw wd i) = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set s' : Set nodeSub := {x | (x : WeylGroup Tag.E6) ∈ s}
  have hs' : ∀ a ∈ s', ∀ b ∈ s', Commute a b := fun a ha b hb =>
    Subtype.ext (hs a ha b hb).eq
  have h3' : ∀ a ∈ s', a ^ 3 = 1 := fun a ha => Subtype.ext (by simpa using h3 a ha)
  have hS : Nat.card ((qSub gw).subgroupOf nodeSub) =
      3 ^ (Nat.card nodeSub).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv, hcard,
      factorization_of_dvd (hcard ▸ Subgroup.card_dvd_of_le hQN)
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_weylGroup_E6 ▸
          Subgroup.card_subgroup_dvd_card nodeSub)]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_le _ hS (isPGroup_closure hs' h3')
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hm := hg ⟨x, hsN hx⟩ (Subgroup.subset_closure hx)
  rw [Subgroup.mem_subgroupOf] at hm
  obtain ⟨i, hi, hyi⟩ := exists_yI hF hm
  refine ⟨i, hi, ?_⟩
  rw [MulAut.conj_apply, hyi]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem three_dvd_smul {g : WeylGroup Tag.E6} (hg : g ∈ nodeSub) {δ : Fin Tag.E6.rank → ℤ}
    (hδ : IsRoot Tag.E6 δ) : (3 : ℤ) ∣ (g • δ) 3 ↔ (3 : ℤ) ∣ δ 3 :=
  (hg δ hδ).dvd_iff

theorem a2Roots_inv {α β δ : Fin Tag.E6.rank → ℤ} (g : WeylGroup Tag.E6)
    (h : δ ∈ a2Roots (g • α) (g • β)) : g⁻¹ • δ ∈ a2Roots α β := by
  have h' := a2Roots_smul h g⁻¹
  rwa [inv_smul_smul, inv_smul_smul] at h'

theorem div_conj {g : WeylGroup Tag.E6} (hg : g ∈ nodeSub) {α β : Fin Tag.E6.rank → ℤ}
    (hp : IsA2Pair (τ := Tag.E6) α β) (h : ∀ δ ∈ a2Roots α β, (3 : ℤ) ∣ δ 3) :
    ∀ δ ∈ a2Roots (g • α) (g • β), (3 : ℤ) ∣ δ 3 := by
  intro δ hδ
  have h1 := a2Roots_inv g hδ
  have h2 := (three_dvd_smul hg (a2Roots_isRoot hp _ h1)).2 (h _ h1)
  rwa [smul_inv_smul] at h2

theorem none_conj {g : WeylGroup Tag.E6} (hg : g ∈ nodeSub) {α β : Fin Tag.E6.rank → ℤ}
    (hp : IsA2Pair (τ := Tag.E6) α β) (h : ∀ δ ∈ a2Roots α β, ¬ (3 : ℤ) ∣ δ 3) :
    ∀ δ ∈ a2Roots (g • α) (g • β), ¬ (3 : ℤ) ∣ δ 3 := by
  intro δ hδ hd
  have h1 := a2Roots_inv g hδ
  refine h _ h1 ((three_dvd_smul hg (a2Roots_isRoot hp _ h1)).1 ?_)
  rwa [smul_inv_smul]

@[expose] noncomputable def chiHom (χ : Fin Tag.E6.rank → ZMod 3) : (Fin Tag.E6.rank → ℤ) →+ ZMod 3 where
  toFun v := ∑ i, χ i * (v i : ZMod 3)
  map_zero' := by simp
  map_add' u v := by simp [Int.cast_add, mul_add, Finset.sum_add_distrib]

theorem chiHom_apply (χ : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    chiHom χ v = ∑ i, χ i * (v i : ZMod 3) := rfl

theorem chiHom_single (χ : Fin Tag.E6.rank → ZMod 3) (j : Fin Tag.E6.rank) :
    chiHom χ (Pi.single j 1) = χ j := by
  rw [chiHom_apply, Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi])
    (by simp)]
  simp

@[expose] noncomputable def chiConj (χ : Fin Tag.E6.rank → ZMod 3) (g : WeylGroup Tag.E6) :
    Fin Tag.E6.rank → ZMod 3 := fun i => chiHom χ (g • Pi.single i 1)

theorem chiConj_apply (χ : Fin Tag.E6.rank → ZMod 3) (g : WeylGroup Tag.E6)
    (v : Fin Tag.E6.rank → ℤ) : chiHom (chiConj χ g) v = chiHom χ (g • v) := by
  have hv : v = ∑ j : Fin Tag.E6.rank, v j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  rw [Finset.smul_sum, map_sum, chiHom_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm, map_zsmul]
  simp only [chiConj, zsmul_eq_mul, smul_eq_mul]
  ring

theorem tauChars_conj {g y : WeylGroup Tag.E6} (hg : g ∈ nodeSub) {γ : Fin Tag.E6.rank → ℤ}
    (h : E6TauChars y γ) : E6TauChars (g * y * g⁻¹) (g • γ) := by
  intro χ hχ hinv hγχ
  have hc : ∀ v, chiHom (chiConj χ g) v = chiHom χ (g • v) := chiConj_apply χ g
  have hne : chiConj χ g ≠ 0 := by
    intro h0
    refine hχ (funext fun j => ?_)
    have e := hc (g⁻¹ • Pi.single j 1)
    rw [smul_inv_smul, chiHom_single, h0] at e
    rw [← e]
    simp [chiHom_apply]
  have hinv' : ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, chiConj χ g i * (((y • v) i : ℤ) : ZMod 3) =
      ∑ i, chiConj χ g i * ((v i : ℤ) : ZMod 3) := by
    intro v
    rw [← chiHom_apply, ← chiHom_apply, hc, hc]
    have e := hinv (g • v)
    rw [← chiHom_apply, ← chiHom_apply] at e
    rw [← e, mul_smul, mul_smul, inv_smul_smul]
  have hγ' : ∑ i, chiConj χ g i * ((γ i : ℤ) : ZMod 3) = 0 := by
    rw [← chiHom_apply, hc, chiHom_apply]
    exact hγχ
  rcases h _ hne hinv' hγ' with h18 | ⟨β, hβ, h3, hk, o1, o2, o3⟩
  · left
    rw [← h18]
    refine Finset.card_bij (fun δ _ => g⁻¹ • δ) ?_ ?_ ?_
    · intro δ hδ
      simp only [Finset.mem_filter, mem_rootFinset] at hδ ⊢
      refine ⟨IsRoot.smul hδ.1 g⁻¹, ?_⟩
      rw [← chiHom_apply, hc, smul_inv_smul, chiHom_apply]
      exact hδ.2
    · intro a _ b _ e
      exact smul_left_cancel _ e
    · intro δ hδ
      simp only [Finset.mem_filter, mem_rootFinset] at hδ
      refine ⟨g • δ, ?_, inv_smul_smul g δ⟩
      simp only [Finset.mem_filter, mem_rootFinset]
      refine ⟨IsRoot.smul hδ.1 g, ?_⟩
      rw [← chiHom_apply, ← hc, chiHom_apply]
      exact hδ.2
  · right
    refine ⟨g • β, IsRoot.smul hβ g, (three_dvd_smul hg hβ).2 h3, ?_, ?_, ?_, ?_⟩
    · rw [← chiHom_apply, ← hc, chiHom_apply]
      exact hk
    · simp only [mul_smul, inv_smul_smul, iform_smul]
      exact o1
    · simp only [mul_smul, inv_smul_smul, iform_smul]
      exact o2
    · simp only [mul_smul, inv_smul_smul, iform_smul]
      exact o1

theorem idxV_spec {v : List ℤ} (h : idxV v < 72) : rvL (idxV v) = v := by
  unfold idxV at h ⊢
  cases hl : (List.range 72).filter (fun k => rvL k == v) with
  | nil => rw [hl] at h; exact absurd h (by simp)
  | cons k ks =>
    have hk : k ∈ (List.range 72).filter (fun k => rvL k == v) := hl ▸ List.mem_cons_self
    simpa using (List.mem_filter.1 hk).2

theorem iform_eq_zero_of_reflIdx {a c : ℕ} (ha : a < 72) (hc : c < 72) (h : reflIdx 72 a c = c) :
    iform (e6Certificate.root a) (e6Certificate.root c) = 0 := by
  obtain ⟨-, hroot⟩ := reflIdx_spec 72 a (by omega) ha c hc
  rw [h] at hroot
  have hra := isRoot_root72 ha
  have h1 := rootReflection_smul hra (e6Certificate.root c)
  rw [← hroot] at h1
  have h2 : corootPair (e6Certificate.root a) (e6Certificate.root c) • e6Certificate.root a = 0 :=
    sub_eq_self.1 h1.symm
  rcases smul_eq_zero.1 h2 with h3 | h3
  · have := corootPair_mul hra (e6Certificate.root c)
    rw [h3, iform_self_e6 hra, zero_mul] at this
    omega
  · exact absurd h3 hra.ne_zero

theorem tauB_sound {t : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    {a : ℕ} (ha : a < 72) (h : tauB t a = true) : E6TauChars w (e6Certificate.root a) := by
  intro χ hχ hinv hγχ
  obtain ⟨n, hn, rfl⟩ := exists_idx χ
  have hn0 : n ≠ 0 := by
    rintro rfl
    refine hχ (funext fun j => ?_)
    simp [vec3, digits3]
  have hchi : chiTestL .E6 (RootTables.ofCert e6Certificate) (digits3 .E6 n) t = true := by
    refine StabCert3.chiTestL_of_pairing (S := ⟨digits3 .E6 n, [], []⟩) hrep fun j => ?_
    rw [(hrep.2 j).2]
    have h1 : triPairing (vec3 (τ := .E6) (digits3 .E6 n))
          (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) =
        triPairing (vec3 (τ := .E6) (digits3 .E6 n)) (Pi.single j 1 : Fin Tag.E6.rank → ℤ) :=
      hinv (Pi.single j 1)
    rw [h1]
    have := triPairing_zsmul_single (vec3 (τ := .E6) (digits3 .E6 n)) 1 j
    rwa [one_smul, Int.cast_one, mul_one] at this
  have hkill : killBit (RootTables.ofCert e6Certificate) a n = true := (killBit_iff ha n).2 hγχ
  simp only [tauB, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h n hn with (((h0 | h0) | h0) | h18) | ⟨b, hb, ⟨hb3, hbk⟩, ⟨hx, hy⟩, hbo⟩
  · exact absurd h0 hn0
  · rw [hchi] at h0
    exact absurd h0 (by decide)
  · rw [hkill] at h0
    exact absurd h0 (by decide)
  · left
    rw [card_filter_rootFinset, ← h18, killCount]
    refine congrArg List.length (List.filter_congr fun r hr => ?_)
    have hr72 := List.mem_range.1 hr
    exact (Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff]; exact (killBit_iff hr72 n).symm))
  · right
    have ex := idxV_spec hx
    rw [rvL_eq (idxV (actV t (rvL b)))] at ex
    conv at ex => rhs; rw [actV_rvL hrep]
    have rx := ofFn_inj' ex
    have ey := idxV_spec hy
    rw [rvL_eq (idxV (actV t (rvL (idxV (actV t (rvL b))))))] at ey
    conv at ey => rhs; rw [actV_rvL hrep, rx]
    have ry := ofFn_inj' ey
    simp only [orthC, Bool.and_eq_true, beq_iff_eq] at hbo
    obtain ⟨⟨o1, o2⟩, o3⟩ := hbo
    refine ⟨e6Certificate.root b, isRoot_root72 hb, (three_dvd_iff rfl).2 hb3,
      (killBit_iff hb n).1 hbk, ?_, ?_, ?_⟩
    · rw [← rx]
      exact iform_eq_zero_of_reflIdx hb hx o1
    · rw [← ry]
      exact iform_eq_zero_of_reflIdx hb hy o2
    · rw [← ry, ← rx]
      exact iform_eq_zero_of_reflIdx hx hy o3

end CFSG.KC.E6Syl3
