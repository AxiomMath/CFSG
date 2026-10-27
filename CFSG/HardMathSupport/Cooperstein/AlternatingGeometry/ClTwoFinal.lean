module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClTwoMove
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClTwo
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClTwoBlock
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClTwoUniq
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenMatchingFalse

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.Quasithin CFSG.AGLEmbedding CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique

theorem eq_or_eq_sigma_of_fst_eq {Ω : Type*} [DecidableEq Ω] {n : ℕ} (σ : Perm Ω) (e : Ω ≃ Fin n × Bool)
    (he : ∀ x, e (σ x) = ((e x).1, !(e x).2)) {x y : Ω} (h : (e y).1 = (e x).1) :
    y = x ∨ y = σ x := by
  by_cases hb : (e y).2 = (e x).2
  · left
    exact e.injective (Prod.ext h hb)
  · right
    apply e.injective
    rw [he]
    refine Prod.ext h ?_
    simp only
    cases h1 : (e y).2 <;> cases h2 : (e x).2 <;> simp_all


theorem eightTenNodeColourFourTwoMove : EightTenNodeColourFourTwoMove := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hN2 hiff' hmv
  classical
  obtain ⟨s0, hs0, y0, hy1, hy2⟩ := hmv
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  have hNS' := hNS
  obtain ⟨π, hπ, hkerπ, hAd, hequiv, hker⟩ := hNS
  have hS2 : IsPGroup 2 S := hA'.twoRadical.isPGroup
  have hP := pre_of_theta hS2 (le_sup_right : S ≤ L ⊔ S) θ hsh
  set W : Subgroup (Perm (Fin m)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  set Sstar : Subgroup (Perm (Fin m)) := (S.subgroupOf (L ⊔ S)).map θ with hSstar
  obtain ⟨hσ1, hσ2, hg, hc, hcol, hdbl⟩ := hbd
  have hbd' : BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c := ⟨hσ1, hσ2, hg, hc, hcol, hdbl⟩
  have hAJ : A ≤ thompsonJ S :=
    le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAm
  have hEW : (A.subgroupOf (L ⊔ S)).map θ ≤ W := Subgroup.map_mono (Subgroup.comap_mono hAJ)
  have hJS : thompsonJ S ≤ S := iSup_le fun A => iSup_le fun hA => hA.1
  have hWS : W ≤ Sstar := Subgroup.map_mono (Subgroup.comap_mono hJS)
  have hiffP : ∀ y, Classif.partner hP.twoGroup y = y ↔ c y = true := by
    intro y
    rw [← hiff' y]
    constructor
    · intro h z hz1 hz2
      have := Classif.partner_eq_of_swap_mem hP.twoGroup hz1 hz2
      rw [h] at this
      exact hz1 this
    · intro h
      by_contra hne
      obtain ⟨z, hz1, hz2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
      exact h z hz1 hz2
  have hex : ∃ z, Classif.partner hP.twoGroup z = z := by
    obtain ⟨z, hz⟩ := hunm
    refine ⟨z, ?_⟩
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
    exact hz y hy1 hy2
  have h2N : 2 * Nat.card {x : Fin m // ∃ y, x < y ∧ IsIsoPair W x y} =
      Nat.card {z : Fin m // Classif.partner hP.twoGroup z ≠ z} := hP.two_mul_isoCount_eq hex
  have hMcard : Nat.card {z : Fin m // Classif.partner hP.twoGroup z ≠ z} =
      (Finset.univ.filter fun y : Fin m => c y = false).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Ne, hiffP y]
    simp
  have htot : (Finset.univ.filter fun y : Fin m => c y = false).card +
      (Finset.univ.filter fun y : Fin m => c y = true).card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun y => c y = false)
    simp only [Bool.not_eq_false, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hF4 : (Finset.univ.filter fun y : Fin m => c y = false).card = 4 := by omega
  obtain ⟨ι, i1, i2, eι, hcard, -⟩ := exists_blockEquiv σ hσ1 hσ2
  have hmn : 2 * Fintype.card ι = m := by simpa using hcard.symm
  have hm10 : 10 ≤ m := by omega
  have hT : (Finset.univ.filter fun y : Fin m => c y = true).card = m - 4 := by omega
  have hsw : ∀ y, swap y (σ y) ∉ W ↔ c y = true := by
    intro y
    constructor
    · intro h
      exact (hcol y).2 fun h' => h (hEW h')
    · intro h hmem
      exact (hiff' y).2 h (σ y) (Ne.symm (hσ1 y)) hmem
  have hsetT : (Finset.univ.filter fun y : Fin m => swap y (σ y) ∉ W) =
      Finset.univ.filter fun y : Fin m => c y = true := by
    ext y; simp [hsw y]
  have hWsw : ∀ y, c y = false → swap y (σ y) ∈ W := by
    intro y hy
    by_contra h
    have := (hsw y).1 h
    rw [hy] at this; exact absurd this (by simp)
  have hle : W ≤ pairPres σ hσ1 hσ2 :=
    le_trans hP.sup (iSup_le fun i =>
      hP.le_pairPres_of_blockData (i₀ := ⟨A, hAm⟩) hbd' hiffP (by omega) (by omega) i)
  have hD : ∀ x y, y ≠ x → y ≠ σ x → swap x (σ x) ∉ W → swap y (σ y) ∉ W →
      swap x (σ x) * swap y (σ y) ∈ W := by
    intro x y hyx hyσ hx' hy'
    have hcx := (hsw x).1 hx'
    have hcy := (hsw y).1 hy'
    exact hEW (hdbl (Subgroup.subset_closure ⟨x, y, hyx, hyσ, hcy.trans hcx.symm, rfl⟩))
  have hN1 : (Finset.univ.filter fun x : Fin m => swap x (σ x) ∉ W).card ≠ 2 * 1 := by
    rw [hsetT, hT]; omega
  by_cases h8 : (Finset.univ.filter fun x : Fin m => swap x (σ x) ∉ W).card = 2 * 4
  · exact eightTenNodeMatching G X S L hX hA hL m hm e hN θ hNS' hθS σ hσ1 hσ2 hle hD hN1
      (Or.inl h8)
  exfalso
  rw [hsetT, hT] at h8
  set n := Fintype.card ι with hn
  obtain ⟨e', he'⟩ := exists_finBlockEquiv σ hσ1 hσ2 n (by simp; omega)
  let θ' : ↥(L ⊔ S) →* Perm (Fin n × Bool) := e'.permCongrHom.toMonoidHom.comp θ
  have hθ' : ∀ m, θ' m = e'.permCongr (θ m) := fun m => rfl
  have hW' : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ' = W.map e'.permCongrHom.toMonoidHom := by
    rw [Subgroup.map_map]
  have hWF' := reindex_blockFix σ hσ1 hσ2 e' he' hle
  have hD' := reindex_hD σ e' he' hσ1 hσ2 hD
  obtain ⟨T, hTW, hts⟩ := exists_AT_of_dbl hWF' hD'
  have hTcard : 2 * T.card = m - 4 := by
    have h1 := card_filter_swap_eq σ e' he' (W := W) Not
    have h2 : (Finset.univ.filter fun i : Fin n => ¬ blockTransp i ∈ W.map e'.permCongrHom.toMonoidHom) = T := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hts i, not_not]
    rw [h2, hsetT, hT] at h1
    exact h1.symm
  have hAlt' : ∀ x ∈ alternatingGroup (Fin n × Bool), ∃ l : ↥(L ⊔ S), θ' l = x := by
    intro x hx
    have hx' : e'.permCongr.symm x ∈ alternatingGroup (Fin m) := by
      rw [mem_alternatingGroup] at hx ⊢
      rw [← hx]
      have := Equiv.Perm.sign_permCongr e' (e'.permCongr.symm x)
      rw [← this]
      simp
    obtain ⟨l, hl⟩ := hAd _ hx'
    exact ⟨⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩, by rw [hθ', hl]; exact Equiv.apply_symm_apply _ _⟩
  have hker' : ∀ m' : ↥(L ⊔ S), θ' m' = 1 → (m' : G) ∈ S := by
    intro m' h
    apply hθS
    exact e'.permCongr.injective (by rw [← hθ', h]; exact (map_one e'.permCongrHom).symm)
  have hfix := fun (s : ↥(L ⊔ S)) (hs : (s : G) ∈ S) (i : Fin n) (hi : i ∈ T) (b : Bool) =>
    theta_S_fixes_true_blocks hA' (by rw [Fintype.card_fin]; omega) θ' hker' hAlt' T (hW'.trans hTW) (by omega) (by omega)
      (by omega) s hs i hi b
  have htrue : ∀ s ∈ Sstar, ∀ y, c y = true → s y = y ∨ s y = σ y := by
    rintro _ ⟨s', hs', rfl⟩ y hy
    have hs'S : (s' : G) ∈ S := Subgroup.mem_subgroupOf.1 hs'
    have hyT : (e' y).1 ∈ T := by
      by_contra h
      have := (hts _).2 h
      rw [blockTransp_mem_map_iff σ e' he'] at this
      exact ((hsw y).2 hy) this
    have h1 := hfix s' hs'S _ hyT (e' y).2
    have h2 : (e' (θ s' y)).1 = (e' y).1 := by
      have : θ' s' (e' y) = e' (θ s' y) := by simp [hθ']
      rw [← this]; exact h1
    exact eq_or_eq_sigma_of_fst_eq σ e' he' h2
  have hflip : ∀ y, ∃ w ∈ W, w y = σ y := by
    intro y
    by_cases hy : c y = false
    · exact ⟨_, hWsw y hy, swap_apply_left _ _⟩
    · have hyt : c y = true := by simpa using hy
      obtain ⟨z, hz, hzy, hzσ⟩ : ∃ z, c z = true ∧ z ≠ y ∧ z ≠ σ y := by
        by_contra hno
        push Not at hno
        have hsub : (Finset.univ.filter fun z : Fin m => c z = true) ⊆ {y, σ y} := by
          intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases h1 : z = y
          · exact Or.inl h1
          · exact Or.inr (hno z hz h1)
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_le_two (a := y) (b := σ y)
        omega
      have hz' : swap y (σ y) * swap z (σ z) ∈ W :=
        hD y z hzy hzσ ((hsw y).2 hyt) ((hsw z).2 hz)
      refine ⟨_, hz', ?_⟩
      have hyz : y ≠ z := hzy.symm
      have hyσz : y ≠ σ z := fun h => hzσ (by rw [h, hσ2])
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hyz hyσz, swap_apply_left]
  have hσcomm : ∀ h ∈ Subgroup.normalizer (W : Set (Perm (Fin m))), ∀ y, h (σ y) = σ (h y) :=
    fun h hh y => comm_sigma_of_normalizer hle hflip hh y
  let U : Subgroup (Perm (Fin m)) := pairPres σ hσ1 hσ2 ⊓ alternatingGroup (Fin m)
  have hUN : U ≤ Subgroup.normalizer (W : Set (Perm (Fin m))) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h1 := pairPres_comm hu.1 (hle hw)
      have : u * w * u⁻¹ = w := by rw [h1]; group
      rw [this]; exact hw
    · intro hw'
      have h1 := pairPres_comm ((pairPres σ hσ1 hσ2).inv_mem hu.1) (hle hw')
      have : u⁻¹ * (u * w * u⁻¹) * u = w := by group
      rw [← this, h1]
      simpa using hw'
  have hU2 : IsPGroup 2 U := by
    rintro ⟨u, hu⟩
    refine ⟨1, Subtype.ext ?_⟩
    show u ^ 2 ^ 1 = 1
    simpa [pow_two] using sq_eq_one_of_pair hσ1 hσ2 (g := u) hu.1
  have hUr : U ≤ θ.range := by
    intro u hu
    obtain ⟨l, hl⟩ := hAd u hu.2
    exact ⟨⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩, hl⟩
  have hUnorm : ∀ h ∈ Subgroup.normalizer (W : Set (Perm (Fin m))), h ∈ θ.range →
      ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
    intro h hh _ u hu
    exact ⟨conj_mem_pairPres (hσcomm h hh) hu.1, Subgroup.Normal.conj_mem inferInstance u hu.2 h⟩
  have hUS : U ≤ Sstar :=
    le_theta_S_of_normal_two hA' (le_sup_right : S ≤ L ⊔ S) θ hθS W rfl U hUN hU2 hUr hUnorm
  have hU : ∀ g ∈ pairPres σ hσ1 hσ2, g ∈ alternatingGroup (Fin m) → g ∈ Sstar :=
    fun g hg ha => hUS ⟨hg, ha⟩
  have hnormW : ∀ s ∈ Sstar, ∀ w ∈ W, s * w * s⁻¹ ∈ W := by
    rintro _ ⟨s', hs', rfl⟩ w hw
    have hh := theta_mem_normalizer_W θ s' (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hs'))
    exact ((Subgroup.mem_normalizer_iff.1 hh) w).1 hw
  have hWuniq : ∀ x y, x ≠ y → swap x y ∈ W → c x = false → y = σ x := by
    intro x y hxy hmem hcx
    have h1 := Classif.partner_eq_of_swap_mem hP.twoGroup hxy hmem
    have h2 := Classif.partner_eq_of_swap_mem hP.twoGroup (hσ1 x).symm (hWsw x hcx)
    exact h1.symm.trans h2
  obtain ⟨a, b, haσ, hba, hbσa, hca, hcb, hFset, s2, hs2, hs2alt, hs2true, hs2F, hs2ab⟩ :=
    exists_even_swapping_element σ hσ1 hσ2 c hc Sstar W hWS hWsw hWuniq hnormW htrue hU hF4
      ⟨s0, hs0, y0, hy1, hy2⟩
  let P : Subgroup (Perm (Fin m)) :=
    { carrier := {p | p ∈ Sstar ∧ p ∈ alternatingGroup (Fin m) ∧ ∀ i, c i = true → p i = i}
      mul_mem' := by
        rintro p q ⟨hp1, hp2, hp3⟩ ⟨hq1, hq2, hq3⟩
        exact ⟨Sstar.mul_mem hp1 hq1, (alternatingGroup (Fin m)).mul_mem hp2 hq2, fun i hi => by
          simp [Perm.mul_apply, hq3 i hi, hp3 i hi]⟩
      one_mem' := ⟨Sstar.one_mem, one_mem _, fun i _ => rfl⟩
      inv_mem' := by
        rintro p ⟨hp1, hp2, hp3⟩
        exact ⟨Sstar.inv_mem hp1, inv_mem hp2, fun i hi => Perm.inv_eq_iff_eq.2 (hp3 i hi).symm⟩ }
  have hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p := by
    intro p hp
    obtain ⟨s, hs, hsp⟩ := hp.1
    obtain ⟨l, hl⟩ := hAd p hp.2.1
    refine ⟨l, ?_, hl⟩
    have h1 : θ (s⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩) = 1 := by
      rw [map_mul, map_inv, hsp, hl, inv_mul_cancel]
    have h2 := hθS _ h1
    have h3 : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have h4 : (l : G) = (s : G) * ((s⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ : ↥(L ⊔ S)) : G) := by
      simp
    rw [h4]
    exact S.mul_mem h3 h2
  let Δ : Finset (Fin m) := {a, σ a, b, σ b}
  have hΔF : ∀ i, i ∉ Δ → c i = true := by
    intro i hi
    by_contra h
    have h' : c i = false := by simpa using h
    rcases hFset i h' with e | e | e | e <;> exact hi (by simp [Δ, e])
  have hPfix : ∀ p ∈ P, ∀ i : Fin m, i ∉ Δ → p i = i := fun p hp i hi => hp.2.2 i (hΔF i hi)
  have hΓ : ∃ k : Fin m, k ∉ Δ := by
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (by omega : 0 < (Finset.univ.filter fun y : Fin m => c y = true).card)
    refine ⟨y, fun hyΔ => ?_⟩
    have hy' : c y = true := by simpa using hy
    simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hyΔ
    rcases hyΔ with e | e | e | e
    · rw [e, hca] at hy'; simp at hy'
    · rw [e, hc, hca] at hy'; simp at hy'
    · rw [e, hcb] at hy'; simp at hy'
    · rw [e, hc, hcb] at hy'; simp at hy'
  have hσaF : c (σ a) = false := by rw [hc]; exact hca
  have hσbF : c (σ b) = false := by rw [hc]; exact hcb
  have hσbb : σ b ≠ b := hσ1 b
  have hσba : σ b ≠ a := fun h => hbσa (by rw [← hσ2 b, h])
  have hbσaa : σ a ≠ σ b := fun h => hba (by simpa [hσ2] using (congrArg σ h).symm)
  let zz : Perm (Fin m) := swap a (σ a) * swap b (σ b)
  have hzzP : zz ∈ P := by
    refine ⟨Sstar.mul_mem (hWS (hWsw a hca)) (hWS (hWsw b hcb)), ?_, ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap haσ, sign_swap (hσ1 b).symm]
      decide
    · intro i hi
      have hia : i ≠ a := fun h => by rw [h, hca] at hi; simp at hi
      have hia' : i ≠ σ a := fun h => by rw [h, hσaF] at hi; simp at hi
      have hib : i ≠ b := fun h => by rw [h, hcb] at hi; simp at hi
      have hib' : i ≠ σ b := fun h => by rw [h, hσbF] at hi; simp at hi
      simp only [zz, Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hib hib', swap_apply_of_ne_of_ne hia hia']
  have hs2P : s2 ∈ P := ⟨hs2, hs2alt, hs2true⟩
  have hzza : zz a = σ a := by
    simp only [zz, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hba.symm hσba.symm, swap_apply_left]
  have hzzb : zz b = σ b := by
    simp only [zz, Perm.mul_apply]
    rw [swap_apply_left, swap_apply_of_ne_of_ne hσba hbσaa.symm]
  have hzzσb : zz (σ b) = b := by
    simp only [zz, Perm.mul_apply]
    rw [swap_apply_right, swap_apply_of_ne_of_ne hba hbσa]
  have hkey : ∀ i ∈ Δ, ∃ p ∈ P, p a = i := by
    intro i hi
    simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨1, P.one_mem, rfl⟩
    · exact ⟨zz, hzzP, hzza⟩
    · rcases hs2ab with h | h
      · exact ⟨s2, hs2P, h⟩
      · exact ⟨zz * s2, P.mul_mem hzzP hs2P, by rw [Perm.mul_apply, h, hzzσb]⟩
    · rcases hs2ab with h | h
      · exact ⟨zz * s2, P.mul_mem hzzP hs2P, by rw [Perm.mul_apply, h, hzzb]⟩
      · exact ⟨s2, hs2P, h⟩
  have hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j := by
    intro i hi j hj
    obtain ⟨p, hp, hpa⟩ := hkey i hi
    obtain ⟨q, hq, hqa⟩ := hkey j hj
    refine ⟨q * p⁻¹, P.mul_mem hq (P.inv_mem hp), ?_⟩
    have : p⁻¹ i = a := Perm.inv_eq_iff_eq.2 hpa.symm
    rw [Perm.mul_apply, this, hqa]
  obtain ⟨j, hj, hjθ⟩ := hWsw a hca
  have hjS : (j : G) ∈ S := hJS (Subgroup.mem_subgroupOf.1 hj)
  have hja : θ j a = σ a := by rw [hjθ, swap_apply_left]
  have hjσ : θ j (σ a) = a := by rw [hjθ, swap_apply_right]
  have hjb : θ j b = b := by rw [hjθ, swap_apply_of_ne_of_ne hba hbσa]
  exact CFSG.HardMathSupport.RichardWeiss.Proving.false_of_swap_mem_theta hA hL hSL (by omega) hNS'
    Δ hΓ P hPS hPfix hPtrans (a := a) (b := σ a) (c := b) (by simp [Δ]) (by simp [Δ])
    (by simp [Δ]) haσ hba.symm hbσa.symm hjS hja hjσ hjb

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
