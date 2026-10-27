module

public import CFSG.Holt.H78.Sec4Prop46A2
import CFSG.Holt.H78.Lemma27Blocks
import CFSG.Holt.H78.DataTransport
public import CFSG.Holt.H78.Sec4Prop46B
public import CFSG.Holt.H78.Sec4U34
import CFSG.Holt.H78.Sec4Prop46BEnd

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

theorem HoltData.exists_involution_fix {K X : Type*} [Group K] [Finite K] [MulAction K X]
    (D : HoltData K X) (k : D.ι) (p : D.Ψc k) :
    ∃ m ∈ D.M k, m ≠ 1 ∧ m * m = 1 ∧ m p = p := by
  classical
  by_cases hout : IsOuterFactor (D.M k)
  · have h4 : Fintype.card (Fin 4) ≤ Fintype.card {q : D.Ψc k // q ≠ p} := by
      rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      have := D.five_le_card k
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h4
    have hne : ∀ i j : Fin 4, i ≠ j → (e i : D.Ψc k) ≠ e j := fun i j h h' =>
      h (e.injective (Subtype.ext h'))
    set a := (e 0 : D.Ψc k)
    set b := (e 1 : D.Ψc k)
    set c := (e 2 : D.Ψc k)
    set d := (e 3 : D.Ψc k)
    have hab : a ≠ b := hne 0 1 (by decide)
    have hcd : c ≠ d := hne 2 3 (by decide)
    have hac : a ≠ c := hne 0 2 (by decide)
    have had : a ≠ d := hne 0 3 (by decide)
    have hbc : b ≠ c := hne 1 2 (by decide)
    have hbd : b ≠ d := hne 1 3 (by decide)
    have hdisj : (Equiv.swap a b).Disjoint (Equiv.swap c d) := fun z => by
      by_cases h1 : z = c ∨ z = d
      · left
        rcases h1 with rfl | rfl
        · exact Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm
        · exact Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm
      · exact Or.inr (Equiv.swap_apply_of_ne_of_ne (not_or.mp h1).1 (not_or.mp h1).2)
    refine ⟨Equiv.swap a b * Equiv.swap c d, ?_, fun h => hab ?_, ?_, ?_⟩
    · rw [hout.1, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
      decide
    · have := congrArg (fun σ : Equiv.Perm (D.Ψc k) => σ a) h
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at this
      rw [Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_left] at this
      exact this.symm
    · calc Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b * Equiv.swap c d)
          = Equiv.swap a b * Equiv.swap a b * (Equiv.swap c d * Equiv.swap c d) := by
            rw [mul_assoc, ← mul_assoc (Equiv.swap c d), hdisj.commute.eq.symm]; group
        _ = 1 := by rw [Equiv.swap_mul_self, Equiv.swap_mul_self, one_mul]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (e 2).2.symm (e 3).2.symm,
        Equiv.swap_apply_of_ne_of_ne (e 0).2.symm (e 1).2.symm]
  · have hτM := D.inner k hout
    have hτ := D.rho_mem_longInv D.t_mem k
    obtain ⟨q, hq, -⟩ := hτ.2
    obtain ⟨g, hg⟩ := (D.factor k).isPretransitive.exists_smul_eq q p
    set τ := D.ρ k ⟨D.t, Subgroup.subset_closure D.t_mem⟩
    have hτ2 : τ * τ = 1 := by
      rw [← sq, ← hτ.1, pow_orderOf_eq_one]
    refine ⟨(g : Equiv.Perm (D.Ψc k)) * τ * (g : Equiv.Perm (D.Ψc k))⁻¹,
      mul_mem (mul_mem g.2 hτM) (inv_mem g.2), fun h => ?_, ?_, ?_⟩
    · have h1 : τ = 1 := by
        have := congrArg (fun σ => (g : Equiv.Perm (D.Ψc k))⁻¹ * σ * g) h
        simpa [mul_assoc] using this
      have := hτ.1
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    · calc (g : Equiv.Perm (D.Ψc k)) * τ * (g : Equiv.Perm (D.Ψc k))⁻¹ *
            ((g : Equiv.Perm (D.Ψc k)) * τ * (g : Equiv.Perm (D.Ψc k))⁻¹)
          = (g : Equiv.Perm (D.Ψc k)) * (τ * τ) * (g : Equiv.Perm (D.Ψc k))⁻¹ := by group
        _ = 1 := by rw [hτ2, mul_one, mul_inv_cancel]
    · have hgq : (g : Equiv.Perm (D.Ψc k)) q = p := hg
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.mpr hgq.symm]
      rw [show τ q = q from hq, hgq]

theorem liftsCommute_of_forall_eq {ι : Type} {Ψc : ι → Type} [∀ i, Fintype (Ψc i)]
    [∀ i, DecidableEq (Ψc i)] {c₀ : ι} (hc₀ : ∀ k, k = c₀)
    {R : Subgroup (∀ i, Equiv.Perm (Ψc i))} (hR : ∀ σ : Equiv.Perm (Ψc c₀), ∃ r ∈ R, r c₀ = σ)
    {q g : ∀ i, Equiv.Perm (Ψc i)} (hgS : ∀ x, q c₀ x ≠ x → (g c₀ * (q c₀ ^ 2)⁻¹) x = x)
    (hsign : Equiv.Perm.sign (g c₀ * (q c₀ ^ 2)⁻¹) = 1)
    (h5 : 5 ≤ Fintype.card {x // q c₀ x = x} ∨ g c₀ = q c₀ ^ 2) : LiftsCommute R q g := by
  intro Y _ π hker hrange a b ha hb
  set π' : Y →* Equiv.Perm (Ψc c₀) := (Pi.evalMonoidHom (fun i => Equiv.Perm (Ψc i)) c₀).comp π
  have hker' : π'.ker ≤ Subgroup.center Y := by
    intro y hy
    refine hker ((MonoidHom.mem_ker).mpr (funext fun k => ?_))
    obtain rfl := hc₀ k
    exact hy
  have hsurj : Function.Surjective π' := fun σ => by
    obtain ⟨r, hr, hrσ⟩ := hR σ
    obtain ⟨y, hy⟩ : r ∈ π.range := hrange ▸ hr
    exact ⟨y, by simp [π', hy, hrσ]⟩
  exact commute_of_map_eq_of_sq π' hker' hsurj hgS hsign h5 (by simp [π', ha]) (by simp [π', hb])

theorem exists_four_cycle {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ] {g : Equiv.Perm Ψ}
    (hg2 : g * g = 1) (hgs : Equiv.Perm.sign g = 1) {F : Finset Ψ} (hF : ∀ x, g x = x ↔ x ∈ F)
    (hcard : Fintype.card Ψ = F.card + 4 ∨ (F.card + 4 ≤ Fintype.card Ψ ∧ 9 ≤ Fintype.card Ψ)) :
    ∃ h : Equiv.Perm Ψ, Commute h g ∧ Equiv.Perm.sign h = -1 ∧ h ^ 4 = 1 ∧
      (∀ x ∈ F, h x = x) ∧ (∀ x, h x ≠ x → (g * (h ^ 2)⁻¹) x = x) ∧
      Equiv.Perm.sign (g * (h ^ 2)⁻¹) = 1 ∧ (5 ≤ Fintype.card {x // h x = x} ∨ g = h ^ 2) := by
  classical
  have hgg : ∀ x, g (g x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, hg2, Equiv.Perm.one_apply]
  have hFc : 4 ≤ (Fᶜ).card := by
    rw [Finset.card_compl]
    omega
  have hmoved : ∀ x, x ∉ F → g x ≠ x := fun x hx h => hx ((hF x).mp h)
  have hmovedg : ∀ x, x ∉ F → g x ∉ F := fun x hx h => hmoved x hx (by
    have := (hF (g x)).mpr h
    rw [hgg] at this
    exact this.symm)
  obtain ⟨a, ha⟩ : (Fᶜ).Nonempty := Finset.card_pos.mp (by omega)
  rw [Finset.mem_compl] at ha
  obtain ⟨c, hc⟩ : ((Fᶜ).erase a |>.erase (g a)).Nonempty := Finset.card_pos.mp (by
    have h2 := Finset.pred_card_le_card_erase (s := Fᶜ) (a := a)
    have h3 := Finset.pred_card_le_card_erase (s := (Fᶜ).erase a) (a := g a)
    omega)
  simp only [Finset.mem_erase, Finset.mem_compl] at hc
  obtain ⟨hcb, hca, hcF⟩ := hc
  obtain ⟨b, hga⟩ : ∃ b, g a = b := ⟨_, rfl⟩
  obtain ⟨d, hgc⟩ : ∃ d, g c = d := ⟨_, rfl⟩
  rw [hga] at hcb
  have hgb : g b = a := by rw [← hga, hgg]
  have hgd : g d = c := by rw [← hgc, hgg]
  have hab : a ≠ b := fun h => hmoved a ha (by rw [hga, h])
  have hcd : c ≠ d := fun h => hmoved c hcF (by rw [hgc, h])
  have hbF : b ∉ F := hga ▸ hmovedg a ha
  have hdF : d ∉ F := hgc ▸ hmovedg c hcF
  have hda : d ≠ a := fun h => hcb (by rw [← hgd, h, hga])
  have hdb : d ≠ b := fun h => hca (by rw [← hgd, h, hgb])
  set h := Equiv.swap a c * Equiv.swap c b * Equiv.swap b d with hh
  have hpa : h a = c := by
    simp only [hh, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hab hda.symm, Equiv.swap_apply_of_ne_of_ne hca.symm hab,
      Equiv.swap_apply_left]
  have hpc : h c = b := by
    simp only [hh, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hcb hcd, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hab.symm hcb.symm]
  have hpb : h b = d := by
    simp only [hh, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hcd.symm hdb,
      Equiv.swap_apply_of_ne_of_ne hda hcd.symm]
  have hpd : h d = a := by
    simp only [hh, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_right, Equiv.swap_apply_right, Equiv.swap_apply_right]
  have hpx : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → h x = x := fun x h1 h2 h3 h4 => by
    simp only [hh, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h2 h4, Equiv.swap_apply_of_ne_of_ne h3 h2,
      Equiv.swap_apply_of_ne_of_ne h1 h3]
  have hFx : ∀ x ∈ F, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := fun x hx =>
    ⟨fun h' => ha (h' ▸ hx), fun h' => hbF (h' ▸ hx), fun h' => hcF (h' ▸ hx),
      fun h' => hdF (h' ▸ hx)⟩
  have h2a : (h ^ 2) a = b := by rw [sq, Equiv.Perm.mul_apply, hpa, hpc]
  have h2b : (h ^ 2) b = a := by rw [sq, Equiv.Perm.mul_apply, hpb, hpd]
  have h2c : (h ^ 2) c = d := by rw [sq, Equiv.Perm.mul_apply, hpc, hpb]
  have h2d : (h ^ 2) d = c := by rw [sq, Equiv.Perm.mul_apply, hpd, hpa]
  have h2x : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → (h ^ 2) x = x := fun x h1 h2 h3 h4 => by
    rw [sq, Equiv.Perm.mul_apply, hpx x h1 h2 h3 h4, hpx x h1 h2 h3 h4]
  have h22 : h ^ 2 * h ^ 2 = 1 := Equiv.ext fun x => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases h1 : x = a; · rw [h1, h2a, h2b]
    by_cases h2 : x = b; · rw [h2, h2b, h2a]
    by_cases h3 : x = c; · rw [h3, h2c, h2d]
    by_cases h4 : x = d; · rw [h4, h2d, h2c]
    rw [h2x x h1 h2 h3 h4, h2x x h1 h2 h3 h4]
  have h2inv : (h ^ 2)⁻¹ = h ^ 2 := inv_eq_of_mul_eq_one_right h22
  have hsignh : Equiv.Perm.sign h = -1 := by
    rw [hh, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hca.symm,
      Equiv.Perm.sign_swap hcb, Equiv.Perm.sign_swap hdb.symm]
    decide
  have hgabcd : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d →
      g x ≠ a ∧ g x ≠ b ∧ g x ≠ c ∧ g x ≠ d := fun x h1 h2 h3 h4 =>
    ⟨fun h' => h2 (by rw [← hgg x, h', hga]), fun h' => h1 (by rw [← hgg x, h', hgb]),
      fun h' => h4 (by rw [← hgg x, h', hgc]), fun h' => h3 (by rw [← hgg x, h', hgd])⟩
  refine ⟨h, ?_, hsignh, ?_, fun x hx => ?_, fun x hx => ?_, ?_, ?_⟩
  · refine Equiv.ext fun x => ?_
    simp only [Equiv.Perm.mul_apply]
    by_cases h1 : x = a; · rw [h1, hga, hpb, hpa, hgc]
    by_cases h2 : x = b; · rw [h2, hgb, hpa, hpb, hgd]
    by_cases h3 : x = c; · rw [h3, hgc, hpd, hpc, hgb]
    by_cases h4 : x = d; · rw [h4, hgd, hpc, hpd, hga]
    obtain ⟨g1, g2, g3, g4⟩ := hgabcd x h1 h2 h3 h4
    rw [hpx x h1 h2 h3 h4, hpx (g x) g1 g2 g3 g4]
  · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, h22]
  · obtain ⟨h1, h2, h3, h4⟩ := hFx x hx
    exact hpx x h1 h2 h3 h4
  · rw [h2inv, Equiv.Perm.mul_apply]
    by_cases h1 : x = a; · rw [h1, h2a, hgb]
    by_cases h2 : x = b; · rw [h2, h2b, hga]
    by_cases h3 : x = c; · rw [h3, h2c, hgd]
    by_cases h4 : x = d; · rw [h4, h2d, hgc]
    exact absurd (hpx x h1 h2 h3 h4) hx
  · rw [Equiv.Perm.sign_mul, hgs, h2inv, map_pow, hsignh]
    decide
  · rcases hcard with h7 | ⟨-, h9⟩
    · refine Or.inr (Equiv.ext fun x => ?_)
      by_cases h1 : x = a; · rw [h1, h2a, hga]
      by_cases h2 : x = b; · rw [h2, h2b, hgb]
      by_cases h3 : x = c; · rw [h3, h2c, hgc]
      by_cases h4 : x = d; · rw [h4, h2d, hgd]
      rw [h2x x h1 h2 h3 h4]
      by_contra hx
      have hxF : x ∉ F := fun h' => hx ((hF x).mpr h')
      have hsub : ({a, b, c, d, x} : Finset Ψ) ⊆ Fᶜ := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rw [Finset.mem_compl]
        rcases hy with rfl | rfl | rfl | rfl | rfl
        · exact ha
        · exact hbF
        · exact hcF
        · exact hdF
        · exact hxF
      have h5 := Finset.card_le_card hsub
      rw [Finset.card_compl, h7, Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hab, hca.symm, hda.symm, Ne.symm h1⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hcb.symm, hdb.symm, Ne.symm h2⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hcd, Ne.symm h3⟩),
        Finset.card_pair (Ne.symm h4)] at h5
      omega
    · refine Or.inl ?_
      have hsub : (Finset.univ \ {a, b, c, d} : Finset Ψ) ⊆
          Finset.univ.filter fun x => h x = x := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          not_or, true_and] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hpx x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
      have h1 := Finset.card_le_card hsub
      have h2 : ({a, b, c, d} : Finset Ψ).card ≤ 4 := Finset.card_le_four
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at h1
      rw [Fintype.card_subtype]
      omega

theorem exists_four_group {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ] {g : Equiv.Perm Ψ}
    (hg2 : g * g = 1) {M : Finset Ψ} (hM : ∀ x ∈ M, g x ≠ x) (hMg : ∀ x ∈ M, g x ∈ M)
    (hM4 : 4 ≤ M.card) :
    ∃ σ₁ σ₂ : Equiv.Perm Ψ, σ₁ ∈ alternatingGroup Ψ ∧ σ₂ ∈ alternatingGroup Ψ ∧ σ₁ ≠ 1 ∧
      σ₂ ≠ 1 ∧ σ₁ ≠ σ₂ ∧ σ₁ * σ₁ = 1 ∧ σ₂ * σ₂ = 1 ∧ Commute σ₁ σ₂ ∧ Commute σ₁ g ∧
      Commute σ₂ g ∧ ∀ x, x ∉ M → σ₁ x = x ∧ σ₂ x = x := by
  classical
  have hgg : ∀ x, g (g x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, hg2, Equiv.Perm.one_apply]
  obtain ⟨a, ha⟩ : M.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ : ((M.erase a).erase (g a)).Nonempty := Finset.card_pos.mp (by
    have h2 := Finset.pred_card_le_card_erase (s := M) (a := a)
    have h3 := Finset.pred_card_le_card_erase (s := M.erase a) (a := g a)
    omega)
  simp only [Finset.mem_erase] at hc
  obtain ⟨hcb, hca, hcM⟩ := hc
  obtain ⟨b, hga⟩ : ∃ b, g a = b := ⟨_, rfl⟩
  obtain ⟨d, hgc⟩ : ∃ d, g c = d := ⟨_, rfl⟩
  rw [hga] at hcb
  have hgb : g b = a := by rw [← hga, hgg]
  have hgd : g d = c := by rw [← hgc, hgg]
  have hab : a ≠ b := fun h => hM a ha (by rw [hga, h])
  have hcd : c ≠ d := fun h => hM c hcM (by rw [hgc, h])
  have hbM : b ∈ M := hga ▸ hMg a ha
  have hdM : d ∈ M := hgc ▸ hMg c hcM
  have hda : d ≠ a := fun h => hcb (by rw [← hgd, h, hga])
  have hdb : d ≠ b := fun h => hca (by rw [← hgd, h, hgb])
  set σ₁ := Equiv.swap a b * Equiv.swap c d with h1
  set σ₂ := Equiv.swap a c * Equiv.swap b d with h2
  have p1a : σ₁ a = b := by
    rw [h1, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hca.symm hda.symm,
      Equiv.swap_apply_left]
  have p1b : σ₁ b = a := by
    rw [h1, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hcb.symm hdb.symm,
      Equiv.swap_apply_right]
  have p1c : σ₁ c = d := by
    rw [h1, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hda hdb]
  have p1d : σ₁ d = c := by
    rw [h1, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hca hcb]
  have p2a : σ₂ a = c := by
    rw [h2, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hda.symm,
      Equiv.swap_apply_left]
  have p2b : σ₂ b = d := by
    rw [h2, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hda hcd.symm]
  have p2c : σ₂ c = a := by
    rw [h2, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hcb hcd,
      Equiv.swap_apply_right]
  have p2d : σ₂ d = b := by
    rw [h2, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hab.symm hcb.symm]
  have px : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → σ₁ x = x ∧ σ₂ x = x :=
    fun x x1 x2 x3 x4 => by
      refine ⟨?_, ?_⟩
      · rw [h1, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne x3 x4,
          Equiv.swap_apply_of_ne_of_ne x1 x2]
      · rw [h2, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne x2 x4,
          Equiv.swap_apply_of_ne_of_ne x1 x3]
  have hg' : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → g x ≠ a ∧ g x ≠ b ∧ g x ≠ c ∧ g x ≠ d :=
    fun x x1 x2 x3 x4 =>
      ⟨fun h => x2 (by rw [← hgg x, h, hga]), fun h => x1 (by rw [← hgg x, h, hgb]),
        fun h => x4 (by rw [← hgg x, h, hgc]), fun h => x3 (by rw [← hgg x, h, hgd])⟩
  have ext5 : ∀ (f k : Equiv.Perm Ψ), f a = k a → f b = k b → f c = k c → f d = k d →
      (∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → f x = k x) → f = k :=
    fun f k ea eb ec ed ex => Equiv.ext fun x => by
      by_cases x1 : x = a; · rw [x1, ea]
      by_cases x2 : x = b; · rw [x2, eb]
      by_cases x3 : x = c; · rw [x3, ec]
      by_cases x4 : x = d; · rw [x4, ed]
      exact ex x x1 x2 x3 x4
  refine ⟨σ₁, σ₂, ?_, ?_, fun h => hab ?_, fun h => hca.symm ?_, fun h => hcb ?_, ?_, ?_, ?_,
    ?_, ?_, fun x hx => ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, h1, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hcd]; decide
  · rw [Equiv.Perm.mem_alternatingGroup, h2, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hca.symm,
      Equiv.Perm.sign_swap hdb.symm]; decide
  · rw [← p1a, h, Equiv.Perm.one_apply]
  · rw [← p2a, h, Equiv.Perm.one_apply]
  · rw [← p1a, h, p2a]
  · refine ext5 _ _ ?_ ?_ ?_ ?_ fun x x1 x2 x3 x4 => ?_ <;>
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    · rw [p1a, p1b]
    · rw [p1b, p1a]
    · rw [p1c, p1d]
    · rw [p1d, p1c]
    · rw [(px x x1 x2 x3 x4).1, (px x x1 x2 x3 x4).1]
  · refine ext5 _ _ ?_ ?_ ?_ ?_ fun x x1 x2 x3 x4 => ?_ <;>
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    · rw [p2a, p2c]
    · rw [p2b, p2d]
    · rw [p2c, p2a]
    · rw [p2d, p2b]
    · rw [(px x x1 x2 x3 x4).2, (px x x1 x2 x3 x4).2]
  · refine ext5 _ _ ?_ ?_ ?_ ?_ fun x x1 x2 x3 x4 => ?_ <;> simp only [Equiv.Perm.mul_apply]
    · rw [p2a, p1c, p1a, p2b]
    · rw [p2b, p1d, p1b, p2a]
    · rw [p2c, p1a, p1c, p2d]
    · rw [p2d, p1b, p1d, p2c]
    · rw [(px x x1 x2 x3 x4).2, (px x x1 x2 x3 x4).1, (px x x1 x2 x3 x4).2]
  · refine ext5 _ _ ?_ ?_ ?_ ?_ fun x x1 x2 x3 x4 => ?_ <;> simp only [Equiv.Perm.mul_apply]
    · rw [hga, p1b, p1a, hgb]
    · rw [hgb, p1a, p1b, hga]
    · rw [hgc, p1d, p1c, hgd]
    · rw [hgd, p1c, p1d, hgc]
    · obtain ⟨g1, g2, g3, g4⟩ := hg' x x1 x2 x3 x4
      rw [(px _ g1 g2 g3 g4).1, (px x x1 x2 x3 x4).1]
  · refine ext5 _ _ ?_ ?_ ?_ ?_ fun x x1 x2 x3 x4 => ?_ <;> simp only [Equiv.Perm.mul_apply]
    · rw [hga, p2b, p2a, hgc]
    · rw [hgb, p2a, p2b, hgd]
    · rw [hgc, p2d, p2c, hga]
    · rw [hgd, p2c, p2d, hgb]
    · obtain ⟨g1, g2, g3, g4⟩ := hg' x x1 x2 x3 x4
      rw [(px _ g1 g2 g3 g4).2, (px x x1 x2 x3 x4).2]
  · exact px x (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hbM)) (fun h => hx (h ▸ hcM))
      (fun h => hx (h ▸ hdM))

theorem four_le_card_closure {M : Type*} [Group M] [Finite M] {σ₁ σ₂ : M} (h1 : σ₁ * σ₁ = 1)
    (h2 : σ₂ * σ₂ = 1) (hc : Commute σ₁ σ₂) (h₁ : σ₁ ≠ 1) (h₂ : σ₂ ≠ 1) (h₁₂ : σ₁ ≠ σ₂) :
    IsPGroup 2 (Subgroup.closure {σ₁, σ₂}) ∧ 4 ≤ Nat.card (Subgroup.closure {σ₁, σ₂}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq := mul_self_eq_one_of_mem_closure (S := {σ₁, σ₂})
    (by rintro s (rfl | rfl); exacts [h1, h2])
    (by
      rintro s (rfl | rfl) t (rfl | rfl)
      exacts [Commute.refl _, hc, hc.symm, Commute.refl _])
  have hP := isPGroup_of_mul_self hsq
  refine ⟨hP, ?_⟩
  have h3 : 3 ≤ Nat.card (Subgroup.closure {σ₁, σ₂}) := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    have hsub : ({1, σ₁, σ₂} : Set M) ⊆ (Subgroup.closure {σ₁, σ₂} : Set M) := by
      rintro x (rfl | rfl | rfl)
      · exact one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_eq_three.mpr ⟨1, σ₁, σ₂, h₁.symm, h₂.symm, h₁₂, rfl⟩] at this
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn] at h3 ⊢
  rcases n with _ | _ | n
  · norm_num at h3
  · norm_num at h3
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem three_le_ncard_fixedBy {A : Type*} [Finite A] {N : Subgroup (Equiv.Perm A)}
    (hN : Odd (Nat.card N)) [IsPretransitive N A] {a b : Equiv.Perm A} (ha : a * a = 1)
    (hb : b * b = 1) (hab : Commute a b) (haN : a ∈ Subgroup.normalizer (N : Set (Equiv.Perm A)))
    (hbN : b ∈ Subgroup.normalizer (N : Set (Equiv.Perm A))) {α : A} (hb' : fixedBy A b = {α})
    {β : A} (hβ : (a * b) β ≠ β) : 3 ≤ (fixedBy A a).ncard := by
  have hBW := ncard_eq_mul_of_fixedBy_eq_singleton hN ha hb hab haN hbN hb'
  have hodd : Odd (Nat.card A) := by
    have h := MulAction.index_stabilizer_of_transitive N α
    exact Odd.of_dvd_nat hN (h ▸ Subgroup.index_dvd_card _)
  have h1 : (fixedBy A (a * b)).ncard < Nat.card A := by
    rw [← Set.ncard_univ]
    exact Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr fun h => hβ (by
      have : β ∈ fixedBy A (a * b) := h ▸ Set.mem_univ β
      exact this)) (Set.toFinite _)
  have h3 : Odd (fixedBy A a).ncard := Odd.of_dvd_nat hodd ⟨_, hBW⟩
  have h4 : (fixedBy A a).ncard ≠ 1 := fun h => by
    rw [h, one_mul] at hBW
    omega
  obtain ⟨k, hk⟩ := h3
  omega

section Normalizers

theorem smul_mem_orbit_jOddCore_of_mem_normalizer {X : Type*} {K : Subgroup (Equiv.Perm X)}
    {σ : Equiv.Perm X} (hσ : σ ∈ Subgroup.normalizer (K : Set (Equiv.Perm X))) {x y : X}
    (hxy : x ∈ orbit (jOddCore K X) y) : σ x ∈ orbit (jOddCore K X) (σ y) := by
  set f : K →* K :=
    { toFun := fun k => ⟨σ * k * σ⁻¹, (Subgroup.mem_normalizer_iff.mp hσ k).mp k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) } with hfdef
  have hf : Function.Injective f := fun a b h => Subtype.ext (by
    have := congrArg Subtype.val h
    simpa [hfdef] using this)
  have he : ∀ (g : K) (ω : X), (σ : X ≃ X) (g • ω) = f g • (σ : X ≃ X) ω := fun g ω => by
    show σ ((g : Equiv.Perm X) ω) = (σ * g * σ⁻¹) (σ ω)
    simp
  have hJ : longInv K X ⊆ f.range := fun t _ => by
    refine ⟨⟨σ⁻¹ * t * σ, ?_⟩, Subtype.ext ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hσ) t).mp t.2
      simpa using this
    · show σ * (σ⁻¹ * t * σ) * σ⁻¹ = t
      group
  have he' : ∀ (h : jHull K X) (ω : X), (σ : X ≃ X) ((h : K) • ω) =
      (hullEquivOfInjective f (σ : X ≃ X) hf he hJ h : K) • (σ : X ≃ X) ω :=
    fun h ω => he h ω
  exact (mem_orbit_jOddCore_hullEquiv_iff he' x y).mpr hxy

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

variable (Ω) in
@[expose] def permFixSet {V : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    Equiv.Perm (fixSet Ω V) where
  toFun ω := ⟨g • (ω : Ω), smul_mem_fixSet_of_mem_normalizer hg ω.2⟩
  invFun ω := ⟨g⁻¹ • (ω : Ω), smul_mem_fixSet_of_mem_normalizer (inv_mem hg) ω.2⟩
  left_inv _ := Subtype.ext (inv_smul_smul g _)
  right_inv _ := Subtype.ext (smul_inv_smul g _)

theorem permFixSet_mem_normalizer {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    permFixSet Ω hg ∈
      Subgroup.normalizer (centralizerImage Ω V : Set (Equiv.Perm (fixSet Ω V))) := by
  have key : ∀ {h : G} (hh : h ∈ Subgroup.normalizer (V : Set G)) (k : Equiv.Perm (fixSet Ω V)),
      k ∈ centralizerImage Ω V → permFixSet Ω hh * k * (permFixSet Ω hh)⁻¹ ∈
        centralizerImage Ω V := by
    rintro h hh _ ⟨c, rfl⟩
    have hc : h * c * h⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : h⁻¹ * u * h ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hh) u).mp hu
        simpa using this
      have := Subgroup.mem_centralizer_iff.mp c.2 _ hu'
      calc u * (h * c * h⁻¹) = h * ((h⁻¹ * u * h) * c) * h⁻¹ := by group
        _ = h * (c * (h⁻¹ * u * h)) * h⁻¹ := by rw [this]
        _ = h * c * h⁻¹ * u := by group
    refine ⟨⟨_, hc⟩, Equiv.ext fun ω => Subtype.ext ?_⟩
    show (h * c * h⁻¹) • (ω : Ω) = h • (c : G) • h⁻¹ • (ω : Ω)
    rw [mul_smul, mul_smul]
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key hg k, fun hk => ?_⟩
  have h1 := key (inv_mem hg) _ hk
  have h2 : permFixSet Ω (inv_mem hg) = (permFixSet Ω hg)⁻¹ := Equiv.ext fun _ => rfl
  rw [h2, inv_inv] at h1
  simpa [mul_assoc] using h1

end Normalizers

section Start3

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace CaseAStart

variable (X : CaseAStart G Ω α v P)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem caseACentralizer_le_stabilizer (Λ' : Set Ω) :
    caseACentralizer G Ω α X.β v Λ' ≤ stabilizer G (holtDelta G Ω α X.β) := fun _ hg =>
  stabilizer_pair_le (G := G) α X.β
    (stabilizer_inf_le_stabilizer_pair α X.β (Subgroup.mem_inf.mp hg).1.2)

omit [FaithfulSMul G Ω] in
theorem w_smul_Λ (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) : X.w • X.Λ = X.Λ := by
  classical
  have hwΔ : X.w • holtDelta G Ω α X.β = holtDelta G Ω α X.β := by
    have := stabilizer_pair_le (G := G) α X.β X.w_mem_pair
    rwa [mem_stabilizer_iff] at this
  have hww : X.w * X.w = 1 := mul_self_eq_one_of_mem_longInv X.w_mem.1
  suffices h : ∀ δ ∈ X.Λ, X.w • δ ∈ X.Λ by
    refine Set.Subset.antisymm ?_ fun δ hδ => ?_
    · rintro _ ⟨δ, hδ, rfl⟩
      exact h δ hδ
    · refine ⟨X.w • δ, h δ hδ, ?_⟩
      show X.w • X.w • δ = δ
      rw [smul_smul, hww, one_smul]
  rcases X.admissible with ⟨-, i₀, hΛ⟩ | ⟨-, -, hΛ⟩ | ⟨-, -, O, -, -, -, -, hwO, hΛ⟩
  · have h3 : 3 ≤ Nat.card (holtDelta G Ω α X.β) :=
      le_trans (by norm_num) X.five_le_card_holtDelta
    have h1 : twoPointElt X.w_mem_pair ∈
        longInv (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β) :=
      (hS.mem_longInv_twoPointSection_iff X.α_ne h3 _).mpr ⟨X.w, X.w_mem, fun _ => rfl⟩
    set ŵ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β) :=
      ⟨_, mem_jHull_of_mem_longInv h1⟩
    have hact : ∀ (δ : holtDelta G Ω α X.β) (j : X.A.D.ι), X.A.D.coord ⟨X.w • (δ : Ω),
        X.smul_mem_holtDelta X.w_mem_pair δ.2⟩ j = X.A.D.ρ j ŵ (X.A.D.coord δ j) :=
      fun δ j => X.A.D.coord_smul ŵ δ j
    have hwγ : (⟨X.w • (X.γ : Ω), X.smul_mem_holtDelta X.w_mem_pair X.γ.2⟩ :
        holtDelta G Ω α X.β) = X.γ := Subtype.ext (X.w_fix hP)
    rw [hΛ]
    rintro _ ⟨δ, hδ, rfl⟩
    refine ⟨⟨X.w • (δ : Ω), X.smul_mem_holtDelta X.w_mem_pair δ.2⟩, fun j hj => ?_, rfl⟩
    rw [hact, hδ j hj, ← hact, hwγ]
  · rw [hΛ]
    intro δ hδ
    rw [← hwΔ]
    exact Set.smul_mem_smul_set hδ
  · rw [hΛ]
    intro δ hδ
    rcases hδ with rfl | hδ
    · exact Or.inl (X.w_fix hP)
    · refine Or.inr ?_
      rw [← hwO]
      exact Set.smul_mem_smul_set hδ

theorem lemma_3_1 (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) {V : Subgroup G}
    (hV : fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ)) :
    V ≠ ⊥ ∧ holtDelta G Ω α X.β ∩ fixSet Ω V = X.Λ := by
  obtain ⟨E, hE, hE𝒞, hE1, hEΛ⟩ : ∃ E : Subgroup G, IsPGroup 2 E ∧
      E ≤ caseACentralizer G Ω α X.β v X.Λ ∧ E ≠ ⊥ ∧
      ∀ δ ∈ holtDelta G Ω α X.β, δ ∈ fixSet Ω E → δ ∈ X.Λ := by
    rcases X.admissible with ⟨h2, i₀, hΛ⟩ | ⟨-, hT, hΛ⟩ | ⟨h1, hodd, O, -, hγO, hO4, hvO, -, hΛ⟩
    · by_cases hodd : Odd (Nat.card (twoPointKernel G Ω α X.β))
      · exact X.exists_testGroup_a_odd hS hP h2 hΛ hodd
      · exact X.exists_testGroup_a_even hS hP h2 hΛ hodd
    · exact X.exists_testGroup_b hP hT hΛ
    · exact X.exists_testGroup_c hP h1 hodd hγO hO4 hvO hΛ
  obtain ⟨h1, hsub⟩ := fixSet_inter_subset_of_fusionIsSylowIn hV hE hE𝒞
    (X.caseACentralizer_le_stabilizer X.Λ) (fun g hg => (Subgroup.mem_inf.mp hg).2) hEΛ
  refine ⟨h1 hE1, Set.Subset.antisymm (fun δ hδ => hsub δ hδ.1 hδ.2) fun δ hδ =>
    ⟨X.Λ_subset_and_γ_mem.1 hδ, fun g hg => (mem_fixingSubgroup_iff G).mp (hV.1 hg).2 δ hδ⟩⟩

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_sylow_le_normalizer {T : Subgroup G} (hT : IsPGroup 2 T)
    (hT𝒞 : T ≤ Subgroup.normalizer (caseACentralizer G Ω α X.β v X.Λ : Set G)) :
    ∃ V : Subgroup G, fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ) ∧
      T ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨V, -, hV, hTV⟩ := exists_fusionIsSylowIn_ge_le_normalizer (V := ⊥) IsPGroup.of_bot
    bot_le hT hT𝒞 (by
      rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]; exact le_top)
  exact ⟨V, hV, hTV⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_fixSet_of_le {V : Subgroup G} (hV : V ≤ caseACentralizer G Ω α X.β v X.Λ) :
    α ∈ fixSet Ω V ∧ X.β ∈ fixSet Ω V ∧ ∀ δ ∈ X.Λ, δ ∈ fixSet Ω V :=
  ⟨fun _ hg => (hV hg).1.2.1, fun _ hg => (hV hg).1.2.2,
    fun δ hδ _ hg => (mem_fixingSubgroup_iff G).mp (hV hg).2 δ hδ⟩

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem three_le_card_fixSet {V : Subgroup G} (hV : V ≤ caseACentralizer G Ω α X.β v X.Λ) :
    3 ≤ Nat.card (fixSet Ω V) := by
  obtain ⟨hα, hβ, hΛ⟩ := X.mem_fixSet_of_le hV
  rw [Nat.card_coe_set_eq]
  exact (Set.ncard_eq_three.mpr ⟨α, X.β, X.γ, X.α_ne, X.γ_ne.1.symm, X.γ_ne.2.symm,
    rfl⟩).symm.le.trans (Set.ncard_le_ncard (Set.insert_subset hα (Set.insert_subset hβ
      (Set.singleton_subset_iff.mpr (hΛ _ X.Λ_subset_and_γ_mem.2)))) (Set.toFinite _))

omit [FaithfulSMul G Ω] [Fintype Ω] [DecidableEq Ω] in
theorem exists_lift_of_odd (hP : Prop46Setup G Ω α v P)
    (hodd : Odd (Nat.card (twoPointKernel G Ω α X.β)))
    {S : Set (Equiv.Perm (holtDelta G Ω α X.β))}
    (hSG : ∀ σ ∈ S, σ ∈ ⁅twoPointSection G Ω α X.β, twoPointSection G Ω α X.β⁆)
    (hSγ : ∀ σ ∈ S, σ X.γ = X.γ)
    (hSv : ∀ σ ∈ S, Commute σ
      ((twoPointElt (X.v_mem_pair hP) : twoPointSection G Ω α X.β) :
        Equiv.Perm (holtDelta G Ω α X.β)))
    (hĒ2 : IsPGroup 2 (Subgroup.closure S)) {Λ' : Set Ω} (hΛ'Δ : Λ' ⊆ holtDelta G Ω α X.β)
    (hSΛ : ∀ σ ∈ S, ∀ δ : holtDelta G Ω α X.β, (δ : Ω) ∈ Λ' → σ δ = δ) :
    ∃ E : Subgroup G, IsPGroup 2 E ∧ E ≤ caseACentralizer G Ω α X.β v Λ' ∧
      Nat.card (Subgroup.closure S) ≤ Nat.card E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set vP : Equiv.Perm (holtDelta G Ω α X.β) :=
    ((twoPointElt (X.v_mem_pair hP) : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β))
  set Ē := Subgroup.closure S
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) :=
    zpowers_isPGroup_two_of_pow_eq_one (n := 1)
      (by rw [pow_one, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one])
  set H₃ := stabilizer G α ⊓ stabilizer G X.β ⊓ stabilizer G (X.γ : Ω)
  have hH₃Δ : H₃ ≤ stabilizer G (holtDelta G Ω α X.β) := fun g hg => by
    have := stabilizer_pair_le (G := G) α X.β
      (stabilizer_inf_le_stabilizer_pair α X.β (Subgroup.mem_inf.mp hg).1)
    exact this
  set res := inducedHom H₃ (holtDelta G Ω α X.β) hH₃Δ
  set Y' : Subgroup H₃ := Ē.comap res ⊓
    (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)).subgroupOf H₃
  have hYmap : Y'.map res = Ē := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_left)
      ((Subgroup.closure_le _).mpr ?_)
    intro σ hσ
    obtain ⟨g, hgαβ, hg⟩ := exists_mem_stabilizer_eq_of_mem_commutator (hSG σ hσ)
    have hgγ : g • (X.γ : Ω) = X.γ := by
      rw [← hg X.γ, hSγ σ hσ]
    have hcomm : ∀ δ ∈ (holtDelta G Ω α X.β), g • v • δ = v • g • δ := fun δ hδ => by
      have h1 := congrArg (fun π : Equiv.Perm (holtDelta G Ω α X.β) =>
        ((π ⟨δ, hδ⟩ : holtDelta G Ω α X.β) : Ω)) (hSv σ hσ).eq
      simp only [Equiv.Perm.mul_apply] at h1
      calc g • v • δ = ((σ (vP ⟨δ, hδ⟩) : (holtDelta G Ω α X.β)) : Ω) := (hg (vP ⟨δ, hδ⟩)).symm
        _ = ((vP (σ ⟨δ, hδ⟩) : (holtDelta G Ω α X.β)) : Ω) := h1
        _ = v • g • δ := by
          rw [show ((vP (σ ⟨δ, hδ⟩) : holtDelta G Ω α X.β) : Ω) =
            v • ((σ ⟨δ, hδ⟩ : holtDelta G Ω α X.β) : Ω) from rfl, hg]
    obtain ⟨c, hc, hcv, hcg⟩ := exists_commute_eqOn_of_odd_twoPointKernel X.γ.2 hodd
      (X.v_mem_stab hP) hv2 ⟨hgαβ, hgγ⟩ hcomm
    have hres : res ⟨c, hc⟩ = σ :=
      Equiv.ext fun δ => Subtype.ext ((hcg δ δ.2).trans (hg δ).symm)
    refine ⟨⟨c, hc⟩, ⟨?_, ?_⟩, hres⟩
    · show res ⟨c, hc⟩ ∈ Ē
      rw [hres]; exact Subgroup.subset_closure hσ
    · refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr ?_)
      rintro _ ⟨n, rfl⟩
      exact (hcv.zpow_right n).eq.symm
  obtain ⟨E₀, hE₀, hE₀Ē⟩ := exists_fusionIsSylowIn_map_eq res (H := Y') (Q := Ē)
    (by rw [hYmap]; exact ⟨le_rfl, hĒ2, fun Q hQ _ hle => le_antisymm hQ hle⟩)
  have hĒΛ : Ē ≤ fixingSubgroup (Equiv.Perm (holtDelta G Ω α X.β))
      {δ : holtDelta G Ω α X.β | (δ : Ω) ∈ Λ'} :=
    (Subgroup.closure_le _).mpr fun σ hσ =>
      (mem_fixingSubgroup_iff _).mpr fun δ hδ => hSΛ σ hσ δ hδ
  refine ⟨E₀.map H₃.subtype, hE₀.2.1.map _, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hyY := hE₀.1 hy
    refine ⟨⟨Subgroup.mem_subgroupOf.mp hyY.2, (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
    refine (mem_fixingSubgroup_iff G).mpr fun l hl => ?_
    exact congrArg Subtype.val ((mem_fixingSubgroup_iff _).mp (hĒΛ hyY.1) ⟨l, hΛ'Δ hl⟩ hl)
  · rw [← hE₀Ē, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)

end CaseAStart

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem CaseAData.ncard_line {β : Ω} (A : CaseAData G Ω α β) (γ : holtDelta G Ω α β)
    (i₀ : A.D.ι) : ((↑) '' {δ : holtDelta G Ω α β | ∀ j, j ≠ i₀ →
      A.D.coord δ j = A.D.coord γ j} : Set Ω).ncard = Fintype.card (A.D.Ψc i₀) := by
  classical
  rw [Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq,
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective (fun δ => A.D.coord δ.1 i₀)
    ⟨fun δ δ' h => Subtype.ext (A.coord_injective (funext fun j => ?_)), fun y => ?_⟩)
  · by_cases hj : j = i₀
    · subst hj; exact h
    · rw [δ.2 j hj, δ'.2 j hj]
  · obtain ⟨δ, hδ⟩ := A.D.coord_surjective (Function.update (A.D.coord γ) i₀ y)
    refine ⟨⟨δ, fun j hj => by rw [hδ, Function.update_of_ne hj]⟩, ?_⟩
    show A.D.coord δ i₀ = y
    rw [hδ, Function.update_self]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem CaseAData.exists_commElt {β : Ω} (A : CaseAData G Ω α β) (j : A.D.ι)
    {m : Equiv.Perm (A.D.Ψc j)} (hm : m ∈ A.D.M j) :
    ∃ ℓ : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β),
      ((ℓ : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) ∈
        ⁅twoPointSection G Ω α β, twoPointSection G Ω α β⁆ ∧
      A.D.ρ j ℓ = m ∧ ∀ k, k ≠ j → A.D.ρ k ℓ = 1 := by
  have hperf := A.D.isPerfect_M j
  rw [Subgroup.isPerfect_iff] at hperf
  rw [← hperf] at hm
  have hM : A.D.M j = ((A.D.L j).subgroupOf
      (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β))).map (A.D.ρ j) := rfl
  rw [hM, ← Subgroup.map_commutator] at hm
  obtain ⟨ℓ, hℓ, hℓm⟩ := hm
  have hℓL : ℓ ∈ (A.D.L j).subgroupOf
      (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)) :=
    (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hℓ
  refine ⟨ℓ, ?_, hℓm, fun k hk => A.D.rho_eq_one_of_mem_L (Ne.symm hk) hℓL⟩
  have h1 := Subgroup.mem_map_of_mem
    (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)).subtype
    (Subgroup.commutator_mono le_top le_top hℓ)
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h1
  have h2 := Subgroup.mem_map_of_mem (twoPointSection G Ω α β).subtype
    (Subgroup.commutator_mono le_top le_top h1)
  rwa [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2

namespace CaseAStart

variable (X : CaseAStart G Ω α v P)

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem ncard_Λ : X.Λ.ncard % 4 = 1 ∧ 5 ≤ X.Λ.ncard := by
  classical
  rcases X.admissible with ⟨-, i₀, hΛ⟩ | ⟨h1, -, hΛ⟩ | ⟨-, -, O, -, hγO, hO4, -, -, hΛ⟩
  · rw [hΛ, X.A.ncard_line]
    exact ⟨X.A.mod4 i₀, X.A.D.five_le_card i₀⟩
  · obtain ⟨i⟩ : Nonempty X.A.D.ι := Fintype.card_pos_iff.mp (by omega)
    have hcard : X.Λ.ncard = Fintype.card (X.A.D.Ψc i) := by
      rw [hΛ, ← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.ofBijective _ (X.A.coord_bijective_of_card_eq_one h1 i))
    rw [hcard]
    exact ⟨X.A.mod4 i, X.A.D.five_le_card i⟩
  · rw [hΛ, Set.ncard_insert_of_notMem hγO (Set.toFinite _), hO4]
    omega

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_box {V : Subgroup G} (hΛ : holtDelta G Ω α X.β ∩ fixSet Ω V = X.Λ) :
    ∃ (Λc : ∀ i, Set (X.A.D.Ψc i)) (j₀ : X.A.D.ι),
      (∀ δ : holtDelta G Ω α X.β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, X.A.D.coord δ i ∈ Λc i) ∧
      (Λc j₀).Nontrivial ∧ (Λc j₀).ncard = X.Λ.ncard ∧ (∀ i, i ≠ j₀ → ¬ (Λc i).Nontrivial) ∧
      ∀ δ δ' : holtDelta G Ω α X.β, (δ : Ω) ∈ X.Λ → (δ' : Ω) ∈ X.Λ →
        X.A.D.coord δ j₀ = X.A.D.coord δ' j₀ → δ = δ' := by
  classical
  have hmem : ∀ δ : holtDelta G Ω α X.β, (δ : Ω) ∈ fixSet Ω V ↔ (δ : Ω) ∈ X.Λ := fun δ => by
    rw [← hΛ]
    exact ⟨fun h => ⟨δ.2, h⟩, fun h => h.2⟩
  have hnt : ∀ {S : Set Ω} {i : X.A.D.ι} {Λi : Set (X.A.D.Ψc i)}, Λi.ncard = S.ncard →
      5 ≤ S.ncard → Λi.Nontrivial := fun h h5 =>
    Set.one_lt_ncard_iff_nontrivial.mp (by omega)
  rcases X.admissible with ⟨-, i₀, hΛ'⟩ | ⟨h1, -, hΛ'⟩ | ⟨h1, -, O, -, -, -, -, -, hΛ'⟩
  · refine ⟨fun i => if i = i₀ then Set.univ else {X.A.D.coord X.γ i}, i₀, fun δ => ?_, ?_, ?_,
      fun i hi => ?_, fun δ δ' hδ hδ' h => ?_⟩
    · rw [hmem, hΛ']
      constructor
      · rintro ⟨δ', hδ', hδδ'⟩ i
        rw [show δ = δ' from Subtype.ext hδδ'.symm]
        by_cases hi : i = i₀
        · simp [hi]
        · simp only [hi, ite_false]; exact hδ' i hi
      · intro h
        refine ⟨δ, fun j hj => ?_, rfl⟩
        have := h j
        simp only [hj, ite_false, Set.mem_singleton_iff] at this
        exact this
    · simp only [ite_true]
      exact hnt (S := X.Λ) (by rw [Set.ncard_univ, Nat.card_eq_fintype_card, hΛ',
        X.A.ncard_line]) X.ncard_Λ.2
    · simp only [ite_true]
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hΛ', X.A.ncard_line]
    · simp only [hi, ite_false]
      exact Set.not_nontrivial_singleton
    · rw [hΛ'] at hδ hδ'
      obtain ⟨d, hd, hdδ⟩ := hδ
      obtain ⟨d', hd', hdδ'⟩ := hδ'
      rw [show δ = d from Subtype.ext hdδ.symm, show δ' = d' from Subtype.ext hdδ'.symm] at h ⊢
      refine X.A.coord_injective (funext fun j => ?_)
      by_cases hj : j = i₀
      · subst hj; exact h
      · rw [hd j hj, hd' j hj]
  · obtain ⟨i⟩ : Nonempty X.A.D.ι := Fintype.card_pos_iff.mp (by omega)
    have hcard : X.Λ.ncard = Fintype.card (X.A.D.Ψc i) := by
      rw [hΛ', ← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.ofBijective _ (X.A.coord_bijective_of_card_eq_one h1 i))
    refine ⟨fun _ => Set.univ, i, fun δ => ?_, ?_, ?_, fun k hk => absurd
      (Fintype.card_le_one_iff.mp h1.le k i) hk, fun δ δ' _ _ h =>
        (X.A.coord_bijective_of_card_eq_one h1 i).1 h⟩
    · rw [hmem, hΛ']
      exact iff_of_true δ.2 fun _ => Set.mem_univ _
    · exact hnt (S := X.Λ) (by rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard])
        X.ncard_Λ.2
    · rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
  · obtain ⟨i⟩ : Nonempty X.A.D.ι := Fintype.card_pos_iff.mp (by omega)
    have hinj := (X.A.coord_bijective_of_card_eq_one h1 i).1
    set Λc : ∀ k, Set (X.A.D.Ψc k) := fun k =>
      (fun δ : holtDelta G Ω α X.β => X.A.D.coord δ k) '' {δ | (δ : Ω) ∈ X.Λ}
    have hcard : (Λc i).ncard = X.Λ.ncard := by
      rw [Set.ncard_image_of_injective _ hinj]
      have hsub := X.Λ_subset_and_γ_mem.1
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
      congr 1
      ext ω
      exact ⟨fun ⟨δ, hδ, hδω⟩ => hδω ▸ hδ, fun hω => ⟨⟨ω, hsub hω⟩, hω, rfl⟩⟩
    refine ⟨Λc, i, fun δ => ?_, hnt hcard X.ncard_Λ.2, hcard, fun k hk => absurd
      (Fintype.card_le_one_iff.mp h1.le k i) hk, fun δ δ' _ _ h => hinj h⟩
    rw [hmem]
    constructor
    · intro h k
      exact ⟨δ, h, rfl⟩
    · intro h
      obtain ⟨δ', hδ', hδδ'⟩ := h i
      rw [← hinj hδδ']
      exact hδ'

end CaseAStart

variable (X : CaseAStart G Ω α v P)

structure CaseASection (V : Subgroup G) (τ : G) where
  sylow : fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ)
  w_mem : X.w ∈ Subgroup.normalizer (V : Set G)
  ne_bot : V ≠ ⊥
  inter : holtDelta G Ω α X.β ∩ fixSet Ω V = X.Λ
  star : IsStarGroup (centralizerImage Ω V) (fixSet Ω V)
  below : HoltTheorem1Below (Nat.card (centralizerImage Ω V)) (Nat.card (fixSet Ω V) + 1)
  τ_two : IsPGroup 2 (Subgroup.zpowers τ)
  τ_mem : τ ∈ Subgroup.normalizer (V : Set G)
  τ_comm : Commute τ v
  W : Subgroup G
  le_W : V ≤ W
  sylow_W : fusionIsSylowIn 2 W (fixingSubgroup G (fixSet Ω V))
  v_mem_W : v ∈ Subgroup.normalizer (W : Set G)
  τ_mem_W : τ ∈ Subgroup.normalizer (W : Set G)
  x : G
  x_mem : x ∈ Subgroup.centralizer (W : Set G)
  x_two : IsPGroup 2 (Subgroup.zpowers x)
  x_smul : ∀ ω ∈ fixSet Ω V, x • ω = v • ω
  x_comm : ∀ c ∈ Subgroup.centralizer (W : Set G), Commute c x → Commute c v
  D : HoltData (centralizerImage Ω V) (fixSet Ω V)
  x_socPre : (restrictCentralizer Ω V ⟨x, Subgroup.centralizer_le le_W x_mem⟩ :
    centralizerImage Ω V) ∈ D.socPre
  c₀ : D.ι
  alt : D.M c₀ = alternatingGroup (D.Ψc c₀)
  card : Fintype.card (D.Ψc c₀) = X.Λ.ncard + 2
  coord_ne : ∀ a b : fixSet Ω V, (a : Ω) = α → (b : Ω) = X.β → D.coord a c₀ ≠ D.coord b c₀
  coord_Λ : ∀ δ δ' : fixSet Ω V, (δ : Ω) ∈ X.Λ → (δ' : Ω) ∈ X.Λ →
    D.coord δ c₀ = D.coord δ' c₀ → δ = δ'
  coord_Λ_ne : ∀ δ a b : fixSet Ω V, (δ : Ω) ∈ X.Λ → (a : Ω) = α → (b : Ω) = X.β →
    D.coord δ c₀ ≠ D.coord a c₀ ∧ D.coord δ c₀ ≠ D.coord b c₀
  parallel : ∀ k, k ≠ c₀ → ∀ δ a b : fixSet Ω V, (δ : Ω) ∈ X.Λ → (a : Ω) = α →
    (b : Ω) = X.β → D.coord δ k = D.coord a k ∧ D.coord b k = D.coord a k

namespace CaseAStart

theorem exists_section (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) {V : Subgroup G}
    (hV : fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ))
    (hVw : X.w ∈ Subgroup.normalizer (V : Set G)) {τ : G} (hτ2 : IsPGroup 2 (Subgroup.zpowers τ))
    (hτV : τ ∈ Subgroup.normalizer (V : Set G)) (hτv : Commute τ v) :
    Nonempty (CaseASection X V τ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV1, hΛ⟩ := X.lemma_3_1 hS hP hV
  have h3 := X.three_le_card_fixSet hV.1
  obtain ⟨hαV, hβV, hΛV⟩ := X.mem_fixSet_of_le hV.1
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  have hv2' : IsPGroup 2 (Subgroup.zpowers v) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, sq]; exact hv2)
  have hvV : v ∈ Subgroup.centralizer (V : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun g hg => (Subgroup.mem_centralizer_iff.mp (hV.1 hg).1.1 v (Subgroup.mem_zpowers v)).symm
  have hT : IsPGroup 2 (Subgroup.zpowers v ⊔ Subgroup.zpowers τ : Subgroup G) :=
    hv2'.to_sup_of_normal_left' hτ2 (Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun g hg => by
        obtain ⟨n, rfl⟩ := hg
        exact (hτv.zpow_right n).eq.symm)))
  have hTV : Subgroup.zpowers v ⊔ Subgroup.zpowers τ ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hvV))
      (Subgroup.zpowers_le.mpr hτV)
  obtain ⟨W, hVW, hW, hTW, x, hxW, hx2, hxv, hxc⟩ := hS.exists_sylow_centralizer_mul hV.2.1 h3
    hv2 hvV X.w_mem.1 X.wv_mem hVw hT (Subgroup.mem_sup_left (Subgroup.mem_zpowers v)) hTV
  obtain ⟨D⟩ := hS.holtData_centralizerImage hV.2.1 hV1 h3
  obtain ⟨Λc, j₀, hbox, hntj, hcardj, hothers, hinjΛ⟩ := X.exists_box hΛ
  have h5 : ∀ i, (Λc i).Nontrivial → 5 ≤ (Λc i).ncard := fun i hi => by
    by_cases hij : i = j₀
    · subst hij; rw [hcardj]; exact X.ncard_Λ.2
    · exact absurd hi (hothers i hij)
  obtain ⟨c, -, hcalt, hcfib, hcpar⟩ := hS.exists_ccl X.α_ne X.A hV.2.1 hV1 h3
    (a := ⟨α, hαV⟩) (b := ⟨X.β, hβV⟩) rfl rfl Λc hbox h5 D
  have hcj : ∀ j : {i // (Λc i).Nontrivial}, j = ⟨j₀, hntj⟩ := fun j => Subtype.ext (by
    by_contra h
    exact hothers j.1 h j.2)
  have hΔ : ∀ δ ∈ X.Λ, δ ∈ holtDelta G Ω α X.β := fun δ hδ => X.Λ_subset_and_γ_mem.1 hδ
  have hpt : ∀ (a : fixSet Ω V) {ω : Ω} (hω : ω ∈ fixSet Ω V), (a : Ω) = ω → a = ⟨ω, hω⟩ :=
    fun a _ _ h => Subtype.ext h
  have hxbar : restrictCentralizer Ω V ⟨x, Subgroup.centralizer_le hVW hxW⟩ =
      restrictCentralizer Ω V ⟨v, hvV⟩ :=
    Subtype.ext (Equiv.ext fun ω => Subtype.ext (hxv ω ω.2))
  have hxS : (restrictCentralizer Ω V ⟨x, Subgroup.centralizer_le hVW hxW⟩ :
      centralizerImage Ω V) ∈ D.socPre := by
    rw [hxbar]
    exact hS.restrict_mem_socPre hV.2.1 hV1 h3 hvV X.w_mem.1 X.wv_mem hVw D
  refine ⟨{ sylow := hV, w_mem := hVw, ne_bot := hV1, inter := hΛ
            star := hS.star_centralizerImage hV.2.1 h3
            below := hS.holtTheorem1Below_centralizerImage hV.2.1 hV1 h3
            τ_two := hτ2, τ_mem := hτV, τ_comm := hτv, W := W
            le_W := hVW, sylow_W := hW
            v_mem_W := hTW (Subgroup.mem_sup_left (Subgroup.mem_zpowers v))
            τ_mem_W := hTW (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)), x := x
            x_mem := hxW, x_two := hx2, x_smul := hxv, x_comm := hxc, D := D, x_socPre := hxS
            c₀ := c ⟨j₀, hntj⟩, alt := (hcalt _).1, card := by rw [(hcalt _).2.1, hcardj]
            coord_ne := fun a b ha hb => by
              rw [hpt a hαV ha, hpt b hβV hb]; exact (hcalt _).2.2
            coord_Λ := fun δ δ' hδ hδ' h => by
              have := ((hcfib ⟨j₀, hntj⟩ δ δ' (hΔ _ hδ) (hΔ _ hδ')).1.mp h)
              have h2 := hinjΛ _ _ hδ hδ' this
              obtain h3 := congrArg Subtype.val h2
              exact Subtype.ext h3
            coord_Λ_ne := fun δ a b hδ ha hb => by
              rw [hpt a hαV ha, hpt b hβV hb]
              exact (hcfib ⟨j₀, hntj⟩ δ δ (hΔ _ hδ) (hΔ _ hδ)).2
            parallel := fun k hk δ a b hδ ha hb => by
              rw [hpt a hαV ha, hpt b hβV hb]
              refine hcpar k ?_ δ (hΔ _ hδ)
              rintro ⟨j, rfl⟩
              exact hk (by rw [hcj j]) }⟩

end CaseAStart

structure IsCaseAOutput (V : Subgroup G) (r : G) (β₁ γ₁ : Ω) : Prop where
  two : IsPGroup 2 (Subgroup.zpowers r)
  mem_V : r ∈ Subgroup.centralizer (V : Set G)
  comm : Commute r v
  fix_α : r • α = α
  fixSet_eq : fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) = {α, β₁, γ₁}
  mem_β₁ : β₁ ∈ p46Orbit G Ω v P α
  ne : β₁ ≠ α
  mem_γ₁ : γ₁ ∈ p46Orbit G Ω v P α
  γ₁_mem : γ₁ ∈ holtDelta G Ω α β₁
  v_γ₁ : v • γ₁ = γ₁
  ncard_le : X.Λ.ncard ≤ (holtDelta G Ω α β₁ ∩ fixSet Ω V).ncard
  orbit : ∃ (hb : X.β ∈ fixSet Ω V) (hb₁ : β₁ ∈ fixSet Ω V) (hc : (X.γ : Ω) ∈ fixSet Ω V)
      (hc₁ : γ₁ ∈ fixSet Ω V),
    (⟨β₁, hb₁⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V))
      ⟨X.β, hb⟩ ∧
    (⟨γ₁, hc₁⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ⟨X.γ, hc⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_mem_p46Orbit (hP : Prop46Setup G Ω α v P) {g : G} (hgv : Commute g v)
    (hgα : g • α = α) {ω : Ω} (hω : ω ∈ p46Orbit G Ω v P α) : g • ω ∈ p46Orbit G Ω v P α := by
  obtain ⟨p, hp, a, ha, rfl⟩ := hω
  have hgC : g ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun _ ⟨n, hn⟩ => hn ▸ (hgv.zpow_right n).eq.symm
  set ĝ : typeLSection G Ω v := restrictCentralizer Ω (Subgroup.zpowers v) ⟨g, hgC⟩
  have hĝa : ĝ • a = a := Subtype.ext (show g • (a : Ω) = a by rw [ha]; exact hgα)
  refine ⟨ĝ * p * ĝ⁻¹, hP.normal.conj_mem p hp ĝ, a, ha, ?_⟩
  show ((ĝ * p * ĝ⁻¹) • a : fixSet Ω (Subgroup.zpowers v)) = g • ((p • a :
    fixSet Ω (Subgroup.zpowers v)) : Ω)
  rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hĝa.symm]
  rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem IsCaseAOutput.conj (hP : Prop46Setup G Ω α v P) {V : Subgroup G} {r : G} {β₁ γ₁ : Ω}
    (hout : IsCaseAOutput X V r β₁ γ₁) {q : G} (hqV : q ∈ Subgroup.centralizer (V : Set G))
    (hqv : Commute q v) (hqα : q • α = α)
    (hβ : ∃ (hb : X.β ∈ fixSet Ω V) (hb₁ : q⁻¹ • β₁ ∈ fixSet Ω V),
      (⟨q⁻¹ • β₁, hb₁⟩ : fixSet Ω V) ∈
        MulAction.orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V))
        ⟨X.β, hb⟩)
    (hγ : ∃ (hc : (X.γ : Ω) ∈ fixSet Ω V) (hc₁ : q⁻¹ • γ₁ ∈ fixSet Ω V),
      (⟨q⁻¹ • γ₁, hc₁⟩ : fixSet Ω V) ∈
        MulAction.orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V))
        ⟨X.γ, hc⟩) :
    IsCaseAOutput X V (q⁻¹ * r * q) (q⁻¹ • β₁) (q⁻¹ • γ₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqN : q ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hqV
  have hqα' : q⁻¹ • α = α := by rw [inv_smul_eq_iff, hqα]
  have hFV : ∀ ω, q • ω ∈ fixSet Ω V ↔ ω ∈ fixSet Ω V := fun ω =>
    ⟨fun h => by
      have := smul_mem_fixSet_of_mem_normalizer (inv_mem hqN) h
      rwa [inv_smul_smul] at this, fun h => smul_mem_fixSet_of_mem_normalizer hqN h⟩
  have hr' : ∀ ω : Ω, (q⁻¹ * r * q) • ω = ω ↔ r • q • ω = q • ω := fun ω => by
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  refine { two := ?_, mem_V := ?_, comm := ?_, fix_α := ?_, fixSet_eq := ?_, mem_β₁ := ?_
           ne := ?_, mem_γ₁ := ?_, γ₁_mem := ?_, v_γ₁ := ?_, ncard_le := ?_, orbit := ?_ }
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hout.two) ⟨r, Subgroup.mem_zpowers r⟩
    have hrn : r ^ 2 ^ n = 1 := by
      have := pow_orderOf_eq_one (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r)
      rw [hn] at this
      exact congrArg Subtype.val this
    refine zpowers_isPGroup_two_of_pow_eq_one (n := n) ?_
    have h := conj_pow (a := q⁻¹) (b := r) (i := 2 ^ n)
    rw [inv_inv] at h
    rw [h, hrn, mul_one, inv_mul_cancel]
  · exact mul_mem (mul_mem (inv_mem hqV) hout.mem_V) hqV
  · exact (hqv.inv_left.mul_left hout.comm).mul_left hqv
  · rw [mul_smul, mul_smul, hqα, hout.fix_α, hqα']
  · ext ω
    rw [fixSet_sup, fixSet_sup, fixSet_zpowers, fixSet_zpowers]
    simp only [Set.mem_inter_iff, mem_fixedBy]
    rw [hr', ← hFV ω, show v • ω = ω ↔ v • q • ω = q • ω by
      rw [smul_smul, ← hqv.eq, mul_smul]
      exact ⟨fun h => by rw [h], fun h => smul_left_cancel q h⟩]
    have := Set.ext_iff.mp hout.fixSet_eq (q • ω)
    rw [fixSet_sup, fixSet_sup, fixSet_zpowers, fixSet_zpowers] at this
    simp only [Set.mem_inter_iff, mem_fixedBy] at this
    rw [this]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have e1 : q • ω = α ↔ ω = α := by rw [← eq_inv_smul_iff, hqα']
    exact or_congr e1 (or_congr eq_inv_smul_iff.symm eq_inv_smul_iff.symm)
  · exact smul_mem_p46Orbit hP hqv.inv_left hqα' hout.mem_β₁
  · intro h
    exact hout.ne (by rw [inv_smul_eq_iff.mp h, hqα])
  · exact smul_mem_p46Orbit hP hqv.inv_left hqα' hout.mem_γ₁
  · have := Set.smul_mem_smul_set (a := q⁻¹) hout.γ₁_mem
    rwa [smul_holtDelta, hqα'] at this
  · rw [smul_smul, ← hqv.inv_left.eq, mul_smul, hout.v_γ₁]
  · have heq : holtDelta G Ω α (q⁻¹ • β₁) ∩ fixSet Ω V =
        q⁻¹ • (holtDelta G Ω α β₁ ∩ fixSet Ω V) := by
      rw [Set.smul_set_inter, smul_holtDelta, hqα']
      congr 1
      ext ω
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
      exact (hFV ω).symm
    rw [heq, Set.ncard_smul_set]
    exact hout.ncard_le
  · obtain ⟨hb, hb₁, hβo⟩ := hβ
    obtain ⟨hc, hc₁, hγo⟩ := hγ
    exact ⟨hb, hb₁, hc, hc₁, hβo, hγo⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_normalizer_centralizer {W : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) := by
  have key : ∀ {h : G}, h ∈ Subgroup.normalizer (W : Set G) → ∀ c : G,
      c ∈ Subgroup.centralizer (W : Set G) → h * c * h⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
    intro h hh c hc
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : h⁻¹ * u * h ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hh) u).mp hu
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hc _ hu'
    calc u * (h * c * h⁻¹) = h * ((h⁻¹ * u * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * u * h)) * h⁻¹ := by rw [this]
      _ = h * c * h⁻¹ * u := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key hg c, fun hc => ?_⟩
  have := key (inv_mem hg) _ hc
  rwa [inv_inv, show g⁻¹ * (g * c * g⁻¹) * g = c by group] at this

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_image_orbit_eq [Finite Ω] {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (ω₀ : fixSet Ω V) (hgω₀ : g • (ω₀ : Ω) = ω₀) :
    g • ((↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ : Set Ω) =
      (↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ := by
  have hsub : g • ((↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ : Set Ω) ⊆
      (↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ := by
    rintro _ ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
    have h1 := smul_mem_orbit_jOddCore_of_mem_normalizer (permFixSet_mem_normalizer (Ω := Ω) hg) hω
    have h2 : permFixSet Ω hg ω₀ = ω₀ := Subtype.ext hgω₀
    rw [h2] at h1
    exact ⟨_, h1, rfl⟩
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_smul_set]) (Set.toFinite _)

namespace CaseASection

variable {X} {V : Subgroup G} {τ : G} (S : CaseASection X V τ)

@[expose] def ptα : fixSet Ω V := ⟨α, (X.mem_fixSet_of_le S.sylow.1).1⟩

@[expose] def ptβ : fixSet Ω V := ⟨X.β, (X.mem_fixSet_of_le S.sylow.1).2.1⟩

@[expose] def ptγ : fixSet Ω V :=
  ⟨X.γ, (X.mem_fixSet_of_le S.sylow.1).2.2 _ X.Λ_subset_and_γ_mem.2⟩

@[expose] def xJ : jHull (centralizerImage Ω V) (fixSet Ω V) :=
  ⟨_, S.D.socPre_le_jHull S.x_socPre⟩

include S in
omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem v_mem : v ∈ Subgroup.centralizer (V : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hg =>
    (Subgroup.mem_centralizer_iff.mp (S.sylow.1 hg).1.1 v (Subgroup.mem_zpowers v)).symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem xJ_smul (ω : fixSet Ω V) :
    (((S.xJ : centralizerImage Ω V) • ω : fixSet Ω V) : Ω) = v • (ω : Ω) := S.x_smul ω ω.2

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem xJ_mul_self (hv2 : v * v = 1) : S.xJ * S.xJ = 1 :=
  Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
    show S.x • S.x • (ω : Ω) = ω
    have h1 : S.x • (ω : Ω) ∈ fixSet Ω V := smul_mem_fixSet_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le S.le_W S.x_mem)) ω.2
    rw [S.x_smul _ h1, S.x_smul _ ω.2, smul_smul, hv2, one_smul])))

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem card_mod_four : Fintype.card (S.D.Ψc S.c₀) % 4 = 3 := by
  have := X.ncard_Λ.1
  rw [S.card]
  omega

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem seven_le_card : 7 ≤ Fintype.card (S.D.Ψc S.c₀) := by
  have := X.ncard_Λ.2
  rw [S.card]
  omega

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem isOuterFactor : IsOuterFactor (S.D.M S.c₀) := ⟨S.alt, S.card_mod_four⟩

include S in
omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem ker : jOrbitKernel (centralizerImage Ω V) (fixSet Ω V) =
    jOddCore (centralizerImage Ω V) (fixSet Ω V) := S.D.ker_outer ⟨S.c₀, S.isOuterFactor⟩

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem t6 : SocInvFixesBlocks S.D := S.D.socInvFixesBlocks_of_below S.star S.below

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem x_smul_orbit (hv2 : v * v = 1) {ω₀ : fixSet Ω V} (hω₀ : v • (ω₀ : Ω) = ω₀)
    (ω : fixSet Ω V) (hω : ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀) :
    S.x • (ω : Ω) = ω := by
  have hfix : ∀ i, S.D.ρ i S.xJ (S.D.coord ω i) = S.D.coord ω i := fun i => by
    rw [← (S.D.coord_eq_iff ω₀ ω).mpr hω, ← S.D.coord_smul]
    congr 2
    exact Subtype.ext (by rw [S.xJ_smul]; exact hω₀)
  have := S.D.smul_eq_of_rho_eq S.t6 S.x_socPre (S.xJ_mul_self hv2) hfix
  rw [S.x_smul _ ω.2, ← S.xJ_smul]
  exact congrArg Subtype.val this

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem rho_surjective : Function.Surjective (S.D.ρ S.c₀) := by
  intro σ
  have hτ := S.D.rho_mem_longInv S.D.t_mem S.c₀
  have hτA : S.D.ρ S.c₀ S.D.tHull ∉ alternatingGroup (S.D.Ψc S.c₀) := by
    rw [mem_alternatingGroup_iff_of_mem_longInv_perm hτ, S.card_mod_four]
    decide
  have hmem : σ ∈ (S.D.ρ S.c₀).range := by
    rw [S.D.range_rho]
    by_cases hσ : σ ∈ alternatingGroup (S.D.Ψc S.c₀)
    · exact Subgroup.mem_sup_left (by rw [S.alt]; exact hσ)
    · have h1 : σ * (S.D.ρ S.c₀ S.D.tHull)⁻¹ ∈ alternatingGroup (S.D.Ψc S.c₀) := by
        rw [Equiv.Perm.mem_alternatingGroup] at hσ hτA ⊢
        rw [map_mul, map_inv, Int.units_ne_iff_eq_neg.mp hσ, Int.units_ne_iff_eq_neg.mp hτA]
        decide
      have he : σ = σ * (S.D.ρ S.c₀ S.D.tHull)⁻¹ * S.D.ρ S.c₀ S.D.tHull := by group
      rw [he]
      exact mul_mem (Subgroup.mem_sup_left (by rw [S.alt]; exact h1))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem socPre_of_psi_eq {e : G} (he : e ∈ Subgroup.centralizer (V : Set G))
    (he2 : IsPGroup 2 (Subgroup.zpowers e))
    (hJ : restrictCentralizer Ω V ⟨e, he⟩ ∈ jHull (centralizerImage Ω V) (fixSet Ω V))
    {ℓ : jHull (centralizerImage Ω V) (fixSet Ω V)} (hℓ : (ℓ : centralizerImage Ω V) ∈ S.D.socPre)
    (hψ : psiHom S.D ⟨_, hJ⟩ = psiHom S.D ℓ) (hℓ2 : psiHom S.D ℓ * psiHom S.D ℓ = 1) :
    (restrictCentralizer Ω V ⟨e, he⟩ : centralizerImage Ω V) ∈ S.D.socPre ∧
      (⟨_, hJ⟩ : jHull (centralizerImage Ω V) (fixSet Ω V)) * ⟨_, hJ⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ē : jHull (centralizerImage Ω V) (fixSet Ω V) := ⟨_, hJ⟩
  constructor
  · have hk : ((ℓ⁻¹ * ē : jHull (centralizerImage Ω V) (fixSet Ω V)) :
        centralizerImage Ω V) ∈ jOddCore (centralizerImage Ω V) (fixSet Ω V) := by
      rw [← S.ker, S.D.mem_jOrbitKernel_iff_rho]
      intro i
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact (congrFun hψ i).symm
    have := mul_mem hℓ (S.D.jOddCore_le_socPre hk)
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp he2) ⟨e, Subgroup.mem_zpowers e⟩
    have hen : e ^ 2 ^ n = 1 := by
      have := pow_orderOf_eq_one (⟨e, Subgroup.mem_zpowers e⟩ : Subgroup.zpowers e)
      rw [hn] at this
      exact congrArg Subtype.val this
    have hēn : (ē * ē) ^ 2 ^ n = 1 := by
      rw [← sq, ← pow_mul, mul_comm, pow_mul]
      have : ē ^ 2 ^ n = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        show (restrictCentralizer Ω V ⟨e, he⟩) ^ 2 ^ n = 1
        rw [← map_pow, show (⟨e, he⟩ : Subgroup.centralizer (V : Set G)) ^ 2 ^ n = 1 from
          Subtype.ext (by rw [Subgroup.coe_pow]; exact hen), map_one])
      rw [this, one_pow]
    have hk : ((ē * ē : jHull (centralizerImage Ω V) (fixSet Ω V)) : centralizerImage Ω V) ∈
        jOddCore (centralizerImage Ω V) (fixSet Ω V) := by
      rw [← S.ker, S.D.mem_jOrbitKernel_iff_rho]
      intro i
      rw [map_mul]
      have := congrFun hℓ2 i
      have hψi := congrFun hψ i
      simp only [psiHom, MonoidHom.pi_apply, Pi.mul_apply, Pi.one_apply] at this hψi
      rw [hψi, this]
    exact Subtype.ext (eq_one_of_pow_two_pow_eq_one_of_mem odd_card_jOddCore hk
      (by rw [← Subgroup.coe_pow, hēn, Subgroup.coe_one]))

theorem eq_c₀ (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) (k : S.D.ι) : k = S.c₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hk
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  have hxα : S.D.ρ k S.xJ (S.D.coord S.ptα k) = S.D.coord S.ptα k := by
    rw [← S.D.coord_smul]
    congr 2
    exact Subtype.ext (by rw [S.xJ_smul]; exact hP.typeL.smul_eq)
  obtain ⟨m, hmM, hm1, hm2, hmp, hmx⟩ : ∃ m ∈ S.D.M k, m ≠ 1 ∧ m * m = 1 ∧
      m (S.D.coord S.ptα k) = S.D.coord S.ptα k ∧
      (S.D.ρ k S.xJ = 1 ∨ S.D.ρ k S.xJ = m) := by
    by_cases hx1 : S.D.ρ k S.xJ = 1
    · obtain ⟨m, hm, h1, h2, h3⟩ := S.D.exists_involution_fix k (S.D.coord S.ptα k)
      exact ⟨m, hm, h1, h2, h3, Or.inl hx1⟩
    · refine ⟨_, S.D.rho_mem_M_of_mem_socPre S.x_socPre k, hx1, ?_, hxα, Or.inr rfl⟩
      rw [← map_mul, S.xJ_mul_self hv2, map_one]
  obtain ⟨ℓ, hℓL, hℓk, hℓo⟩ := S.D.exists_mem_L_rho_eq hmM
  have hlc : LiftsCommute (psiHom S.D).range (psiHom S.D ℓ) (psiHom S.D S.xJ) := by
    rcases hmx with h | h
    · exact S.D.liftsCommute_of_rho_eq_one S.x_socPre hℓo 0 (by rw [h, pow_zero, inv_one,
        one_mul])
    · exact S.D.liftsCommute_of_rho_eq_one S.x_socPre hℓo 1 (by rw [pow_one, hℓk, h,
        inv_mul_cancel])
  have hq2 : psiHom S.D ℓ * psiHom S.D ℓ = 1 := funext fun i => by
    show S.D.ρ i ℓ * S.D.ρ i ℓ = 1
    by_cases hi : i = k
    · subst hi; rw [hℓk, hm2]
    · rw [hℓo i hi, mul_one]
  have hqfix : ∀ ω : fixSet Ω V, S.D.coord ω k = S.D.coord S.ptα k →
      ∀ i, psiHom S.D ℓ i (S.D.coord ω i) = S.D.coord ω i := fun ω hω i => by
    show S.D.ρ i ℓ (S.D.coord ω i) = S.D.coord ω i
    by_cases hi : i = k
    · subst hi; rw [hℓk, hω, hmp]
    · rw [hℓo i hi]; rfl
  obtain ⟨e, he, hex, he2, heα, hJ, heq⟩ := hS.exists_lift_elt S.sylow.2.1
    (X.three_le_card_fixSet S.sylow.1) S.le_W S.sylow_W S.D S.ker S.x_mem S.x_two
    (S.D.socPre_le_jHull S.x_socPre)
    (q := psiHom S.D ℓ) ⟨ℓ, rfl⟩ (s := 1) (by rw [pow_one, sq]; exact hq2) hlc S.ptα
    (fun ω hω => S.x_smul_orbit hv2 hP.typeL.smul_eq ω hω) (hqfix S.ptα rfl)
  have heV' : e ∈ Subgroup.centralizer (V : Set G) := Subgroup.centralizer_le S.le_W he
  obtain ⟨hēS, hēē⟩ := S.socPre_of_psi_eq heV' he2 hJ (S.D.L_le_socPre k hℓL) heq hq2
  have hfixē : ∀ ω : fixSet Ω V, S.D.coord ω k = S.D.coord S.ptα k → e • (ω : Ω) = ω :=
    fun ω hω => congrArg Subtype.val (S.D.smul_eq_of_rho_eq S.t6 hēS hēē fun i => by
      have := hqfix ω hω i
      rw [← heq] at this
      exact this)
  have hpar := S.parallel k hk
  have hΛ := (X.mem_fixSet_of_le S.sylow.1).2.2
  have he𝒞 : e ∈ caseACentralizer G Ω α X.β v X.Λ := by
    refine ⟨⟨?_, heα, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨n, rfl⟩
      exact ((S.x_comm e he hex).zpow_right n).eq.symm
    · exact hfixē S.ptβ (hpar ⟨X.γ, hΛ _ X.Λ_subset_and_γ_mem.2⟩ S.ptα S.ptβ
        X.Λ_subset_and_γ_mem.2 rfl rfl).2
    · refine (mem_fixingSubgroup_iff G).mpr fun δ hδ => hfixē ⟨δ, hΛ δ hδ⟩ ?_
      exact (hpar ⟨δ, hΛ δ hδ⟩ S.ptα S.ptβ hδ rfl rfl).1
  have heV : e ∈ V := by
    have h2 : IsPGroup 2 (V ⊔ Subgroup.zpowers e : Subgroup G) :=
      S.sylow.2.1.to_sup_of_normal_left' he2
        (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ heV'))
    have := S.sylow.2.2 _ (sup_le S.sylow.1 (Subgroup.zpowers_le.mpr he𝒞)) h2 le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hē1 : (⟨_, hJ⟩ : jHull (centralizerImage Ω V) (fixSet Ω V)) = 1 :=
    Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      show e • (ω : Ω) = ω
      exact ω.2 e heV)))
  have := congrFun heq k
  rw [hē1, map_one] at this
  have h1 : (1 : Equiv.Perm (S.D.Ψc k)) = S.D.ρ k ℓ := this
  rw [hℓk] at h1
  exact hm1 h1.symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem rho_xJ_coord {ω : fixSet Ω V} (hω : v • (ω : Ω) = ω) (k : S.D.ι) :
    S.D.ρ k S.xJ (S.D.coord ω k) = S.D.coord ω k := by
  rw [← S.D.coord_smul]
  congr 2
  exact Subtype.ext (by rw [S.xJ_smul]; exact hω)

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_eq_of_rho_xJ (hv2 : v * v = 1) {ω : fixSet Ω V}
    (hω : ∀ k, S.D.ρ k S.xJ (S.D.coord ω k) = S.D.coord ω k) : v • (ω : Ω) = ω := by
  have := S.D.smul_eq_of_rho_eq S.t6 S.x_socPre (S.xJ_mul_self hv2) hω
  rw [← S.xJ_smul]
  exact congrArg Subtype.val this

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_Λ_coord_eq {p : S.D.Ψc S.c₀} (hpa : p ≠ S.D.coord S.ptα S.c₀)
    (hpb : p ≠ S.D.coord S.ptβ S.c₀) :
    ∃ δ : fixSet Ω V, (δ : Ω) ∈ X.Λ ∧ S.D.coord δ S.c₀ = p := by
  classical
  set Λ' : Set (fixSet Ω V) := Subtype.val ⁻¹' X.Λ
  have hΛ := (X.mem_fixSet_of_le S.sylow.1).2.2
  have hab := S.coord_ne S.ptα S.ptβ rfl rfl
  have hsub : (fun δ => S.D.coord δ S.c₀) '' Λ' ⊆
      ({S.D.coord S.ptα S.c₀, S.D.coord S.ptβ S.c₀}ᶜ : Set (S.D.Ψc S.c₀)) := by
    rintro _ ⟨δ, hδ, rfl⟩ h
    obtain ⟨h1, h2⟩ := S.coord_Λ_ne δ S.ptα S.ptβ hδ rfl rfl
    rcases h with h | h
    · exact h1 h
    · exact h2 h
  have hinj : Set.InjOn (fun δ => S.D.coord δ S.c₀) Λ' := fun δ hδ δ' hδ' h =>
    S.coord_Λ δ δ' hδ hδ' h
  have hcardΛ' : Λ'.ncard = X.Λ.ncard :=
    Set.ncard_preimage_of_injective_subset_range Subtype.val_injective fun δ hδ =>
      ⟨⟨δ, hΛ δ hδ⟩, rfl⟩
  have hcompl : (({S.D.coord S.ptα S.c₀, S.D.coord S.ptβ S.c₀} : Set (S.D.Ψc S.c₀))ᶜ).ncard =
      X.Λ.ncard := by
    rw [Set.ncard_compl, Set.ncard_pair hab, Nat.card_eq_fintype_card, S.card]
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [hcompl, hinj.ncard_image, hcardΛ']) (Set.toFinite _)
  have hp : p ∈ ((fun δ => S.D.coord δ S.c₀) '' Λ') := by
    rw [heq]
    rintro (h | h)
    · exact hpa h
    · exact hpb h
  obtain ⟨δ, hδ, hδp⟩ := hp
  exact ⟨δ, hδ, hδp⟩

theorem rho_xJ_eq_self_iff (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (p : S.D.Ψc S.c₀) : S.D.ρ S.c₀ S.xJ p = p ↔ p = S.D.coord S.ptα S.c₀ ∨
      p = S.D.coord S.ptβ S.c₀ ∨ p = S.D.coord S.ptγ S.c₀ := by
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  constructor
  · intro hp
    by_contra h
    simp only [not_or] at h
    obtain ⟨hpa, hpb, hpg⟩ := h
    obtain ⟨δ, hδ, rfl⟩ := S.exists_mem_Λ_coord_eq hpa hpb
    have hvδ : v • (δ : Ω) = δ := S.smul_eq_of_rho_xJ hv2 fun k => by
      obtain rfl := S.eq_c₀ hS hP k
      exact hp
    have hδγ := X.eq_γ_of_smul_eq hP (X.Λ_subset_and_γ_mem.1 hδ) hvδ
    exact hpg (by rw [show δ = S.ptγ from Subtype.ext hδγ])
  · rintro (rfl | rfl | rfl)
    · exact S.rho_xJ_coord hP.typeL.smul_eq S.c₀
    · exact S.rho_xJ_coord (smul_eq_of_mem_p46Orbit X.mem) S.c₀
    · exact S.rho_xJ_coord X.v_fix S.c₀

theorem smul_eq_self_iff (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (ω : fixSet Ω V) : v • (ω : Ω) = ω ↔ S.D.coord ω S.c₀ = S.D.coord S.ptα S.c₀ ∨
      S.D.coord ω S.c₀ = S.D.coord S.ptβ S.c₀ ∨ S.D.coord ω S.c₀ = S.D.coord S.ptγ S.c₀ := by
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  rw [← S.rho_xJ_eq_self_iff hS hP]
  refine ⟨fun h => S.rho_xJ_coord h S.c₀, fun h => S.smul_eq_of_rho_xJ hv2 fun k => ?_⟩
  obtain rfl := S.eq_c₀ hS hP k
  exact h

structure IsAdmissibleElt (r : G) : Prop where
  mem : r ∈ Subgroup.centralizer (S.W : Set G)
  comm : Commute r S.x
  two : IsPGroup 2 (Subgroup.zpowers r)
  fix : r • α = α
  hull : restrictCentralizer Ω V ⟨r, Subgroup.centralizer_le S.le_W mem⟩ ∈
    jHull (centralizerImage Ω V) (fixSet Ω V)
  odd : Equiv.Perm.sign (S.D.ρ S.c₀ ⟨_, hull⟩) = -1
  fix_β : S.D.ρ S.c₀ ⟨_, hull⟩ (S.D.coord S.ptβ S.c₀) = S.D.coord S.ptβ S.c₀
  fix_γ : S.D.ρ S.c₀ ⟨_, hull⟩ (S.D.coord S.ptγ S.c₀) = S.D.coord S.ptγ S.c₀

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coord_ne_three : S.D.coord S.ptα S.c₀ ≠ S.D.coord S.ptβ S.c₀ ∧
    S.D.coord S.ptγ S.c₀ ≠ S.D.coord S.ptα S.c₀ ∧
    S.D.coord S.ptγ S.c₀ ≠ S.D.coord S.ptβ S.c₀ :=
  ⟨S.coord_ne _ _ rfl rfl, S.coord_Λ_ne S.ptγ S.ptα S.ptβ X.Λ_subset_and_γ_mem.2 rfl rfl⟩

theorem exists_admissibleElt (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) :
    ∃ r, S.IsAdmissibleElt r := by
  classical
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  have hc₀ := S.eq_c₀ hS hP
  have hg2 : S.D.ρ S.c₀ S.xJ * S.D.ρ S.c₀ S.xJ = 1 := by
    rw [← map_mul, S.xJ_mul_self hv2, map_one]
  have hgs : Equiv.Perm.sign (S.D.ρ S.c₀ S.xJ) = 1 := by
    have := S.D.rho_mem_M_of_mem_socPre (h := S.xJ) S.x_socPre S.c₀
    rw [S.alt] at this
    exact this
  obtain ⟨hab, hga, hgb⟩ := S.coord_ne_three
  set F : Finset (S.D.Ψc S.c₀) :=
    {S.D.coord S.ptα S.c₀, S.D.coord S.ptβ S.c₀, S.D.coord S.ptγ S.c₀} with hFdef
  have hF : ∀ p, S.D.ρ S.c₀ S.xJ p = p ↔ p ∈ F := fun p => by
    rw [S.rho_xJ_eq_self_iff hS hP]
    simp [F]
  have hF3 : F.card = 3 := by
    rw [hFdef, Finset.card_insert_of_notMem (by simp [hab, hga.symm]),
      Finset.card_pair hgb.symm]
  have hcard : Fintype.card (S.D.Ψc S.c₀) = F.card + 4 ∨
      (F.card + 4 ≤ Fintype.card (S.D.Ψc S.c₀) ∧ 9 ≤ Fintype.card (S.D.Ψc S.c₀)) := by
    have h1 := S.card_mod_four
    have h2 := S.seven_le_card
    omega
  obtain ⟨h, -, hsign, h4, hhF, hgS, hsign', h5⟩ := exists_four_cycle hg2 hgs hF hcard
  obtain ⟨y, hy⟩ := S.rho_surjective h
  have hlc : LiftsCommute (psiHom S.D).range (psiHom S.D y) (psiHom S.D S.xJ) := by
    refine liftsCommute_of_forall_eq hc₀ (fun σ => ?_) (q := psiHom S.D y)
      (g := psiHom S.D S.xJ) ?_ ?_ ?_
    · obtain ⟨z, hz⟩ := S.rho_surjective σ
      exact ⟨psiHom S.D z, ⟨z, rfl⟩, hz⟩
    · show ∀ p, S.D.ρ S.c₀ y p ≠ p →
        (S.D.ρ S.c₀ S.xJ * (S.D.ρ S.c₀ y ^ 2)⁻¹) p = p
      rw [hy]; exact hgS
    · show Equiv.Perm.sign (S.D.ρ S.c₀ S.xJ * (S.D.ρ S.c₀ y ^ 2)⁻¹) = 1
      rw [hy]; exact hsign'
    · show 5 ≤ Fintype.card {p // S.D.ρ S.c₀ y p = p} ∨
        S.D.ρ S.c₀ S.xJ = S.D.ρ S.c₀ y ^ 2
      rw [hy]; exact h5
  have hq4 : psiHom S.D y ^ 2 ^ 2 = 1 := funext fun k => by
    obtain rfl := hc₀ k
    show S.D.ρ S.c₀ y ^ 2 ^ 2 = 1
    rw [hy]
    exact h4
  have hqα : ∀ k, psiHom S.D y k (S.D.coord S.ptα k) = S.D.coord S.ptα k := fun k => by
    obtain rfl := hc₀ k
    show S.D.ρ S.c₀ y _ = _
    rw [hy]
    exact hhF _ (by simp [F])
  obtain ⟨r, hr, hrx, hr2, hrα, hJ, hrq⟩ := hS.exists_lift_elt S.sylow.2.1
    (X.three_le_card_fixSet S.sylow.1) S.le_W S.sylow_W S.D S.ker S.x_mem S.x_two
    (S.D.socPre_le_jHull S.x_socPre) ⟨y, rfl⟩ (s := 2) hq4 hlc S.ptα
    (fun ω hω => S.x_smul_orbit hv2 hP.typeL.smul_eq ω hω) hqα
  have hρr : S.D.ρ S.c₀ ⟨_, hJ⟩ = h := by
    have := congrFun hrq S.c₀
    rw [← hy]
    exact this
  exact ⟨r, { mem := hr, comm := hrx, two := hr2, fix := hrα, hull := hJ
              odd := by rw [hρr]; exact hsign
              fix_β := by rw [hρr]; exact hhF _ (by simp [F])
              fix_γ := by rw [hρr]; exact hhF _ (by simp [F]) }⟩

theorem mem_orbit_iff (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (ω ω₀ : fixSet Ω V) : ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ ↔
      S.D.coord ω S.c₀ = S.D.coord ω₀ S.c₀ := by
  rw [← S.D.coord_eq_iff ω₀ ω]
  refine ⟨fun h => by rw [h], fun h => funext fun k => ?_⟩
  obtain rfl := S.eq_c₀ hS hP k
  exact h.symm

theorem coord_t_smul_β (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) {t : G}
    (ht : t ∈ longInvAt G Ω α) (htV : t ∈ Subgroup.centralizer (V : Set G)) (htv : Commute t v)
    (hJ : restrictCentralizer Ω V ⟨t, htV⟩ ∈ jHull (centralizerImage Ω V) (fixSet Ω V)) :
    S.D.ρ S.c₀ ⟨_, hJ⟩ (S.D.coord S.ptβ S.c₀) = S.D.coord S.ptγ S.c₀ := by
  set tJ : jHull (centralizerImage Ω V) (fixSet Ω V) := ⟨_, hJ⟩
  have h3 := X.three_le_card_fixSet S.sylow.1
  have htK : (tJ : centralizerImage Ω V) ∈ longInv (centralizerImage Ω V) (fixSet Ω V) :=
    (hS.mem_longInv_centralizerImage_iff S.sylow.2.1 h3 _).mpr ⟨t, ht.1, htV, fun _ => rfl⟩
  have hτ := S.D.rho_mem_longInv htK S.c₀
  obtain ⟨hab, hga, hgb⟩ := S.coord_ne_three
  have hτa : S.D.ρ S.c₀ tJ (S.D.coord S.ptα S.c₀) = S.D.coord S.ptα S.c₀ := by
    rw [← S.D.coord_smul]
    congr 2
    exact Subtype.ext ht.2
  have hcomm : S.D.ρ S.c₀ tJ * S.D.ρ S.c₀ S.xJ = S.D.ρ S.c₀ S.xJ * S.D.ρ S.c₀ tJ := by
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext ?_))
    show t • ((((S.xJ : centralizerImage Ω V) • ω : fixSet Ω V)) : Ω) =
      (((S.xJ : centralizerImage Ω V) • (⟨t • (ω : Ω), _⟩ : fixSet Ω V) : fixSet Ω V) : Ω)
    rw [S.xJ_smul, S.xJ_smul]
    show t • v • (ω : Ω) = v • t • (ω : Ω)
    rw [smul_smul, smul_smul, htv.eq]
  set y := S.D.ρ S.c₀ tJ (S.D.coord S.ptβ S.c₀)
  have hy : S.D.ρ S.c₀ S.xJ y = y := by
    show (S.D.ρ S.c₀ S.xJ * S.D.ρ S.c₀ tJ) _ = S.D.ρ S.c₀ tJ _
    rw [← hcomm, Equiv.Perm.mul_apply,
      (S.rho_xJ_eq_self_iff hS hP _).mpr (Or.inr (Or.inl rfl))]
  rcases (S.rho_xJ_eq_self_iff hS hP y).mp hy with h | h | h
  · rw [← hτa] at h
    exact absurd ((S.D.ρ S.c₀ tJ).injective h) hab.symm
  · obtain ⟨c, -, hcu⟩ := hτ.2
    have h1 := hcu _ h
    have h2 := hcu _ hτa
    exact absurd (h1.trans h2.symm) hab.symm
  · exact h

theorem smul_mem_orbit_of_rho (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (y : jHull (centralizerImage Ω V) (fixSet Ω V)) {ω₀ ω : fixSet Ω V}
    (hy : S.D.ρ S.c₀ y (S.D.coord ω₀ S.c₀) = S.D.coord ω₀ S.c₀)
    (hω : ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀) :
    (y : centralizerImage Ω V) • ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ := by
  rw [S.mem_orbit_iff hS hP] at hω ⊢
  rw [S.D.coord_smul, hω, hy]

include S in
omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem τ_smul_γ (hP : Prop46Setup G Ω α v P) (hτα : τ • α = α) (hτβ : τ • X.β = X.β) :
    τ • (X.γ : Ω) = X.γ := by
  have hτp : τ ∈ stabilizer G ({α, X.β} : Set Ω) :=
    stabilizer_inf_le_stabilizer_pair α X.β ⟨hτα, hτβ⟩
  refine X.eq_γ_of_smul_eq hP (X.smul_mem_holtDelta hτp X.γ.2) ?_
  rw [smul_smul, ← S.τ_comm.eq, mul_smul, X.v_fix]

namespace IsAdmissibleElt

variable {S} {r : G} (hr : S.IsAdmissibleElt r)
include hr

@[expose] def rJ : jHull (centralizerImage Ω V) (fixSet Ω V) := ⟨_, hr.hull⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem rJ_smul (ω : fixSet Ω V) :
    (((hr.rJ : centralizerImage Ω V) • ω : fixSet Ω V) : Ω) = r • (ω : Ω) := rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem rJ_notMem_socPre : (hr.rJ : centralizerImage Ω V) ∉ S.D.socPre := fun h => by
  have := S.D.rho_mem_M_of_mem_socPre (h := hr.rJ) h S.c₀
  rw [S.alt, Equiv.Perm.mem_alternatingGroup] at this
  have h2 := hr.odd
  rw [show (⟨_, hr.hull⟩ : jHull (centralizerImage Ω V) (fixSet Ω V)) = hr.rJ from rfl,
    this] at h2
  exact absurd h2 (by decide)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_rJ_pow : ∃ n : ℕ, hr.rJ ^ 2 ^ n = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hr.two) ⟨r, Subgroup.mem_zpowers r⟩
  have hrn : r ^ 2 ^ n = 1 := by
    have := pow_orderOf_eq_one (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r)
    rw [hn] at this
    exact congrArg Subtype.val this
  refine ⟨n, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show (restrictCentralizer Ω V ⟨r, _⟩) ^ 2 ^ n = 1
  rw [← map_pow, show (⟨r, Subgroup.centralizer_le S.le_W hr.mem⟩ :
    Subgroup.centralizer (V : Set G)) ^ 2 ^ n = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hrn), map_one]

theorem block (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) {ω : fixSet Ω V}
    (hω : S.D.ρ S.c₀ hr.rJ (S.D.coord ω S.c₀) = S.D.coord ω S.c₀) :
    (∀ ω' ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω, (r * r) • (ω' : Ω) = ω') ∧
      ∃! ω', ω' ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω ∧
        r • (ω' : Ω) = ω' := by
  obtain ⟨n, hn⟩ := hr.exists_rJ_pow
  obtain ⟨h1, ω', ⟨hω', hfix⟩, huniq⟩ := S.D.existsUnique_smul_eq_of_two_element S.star S.below
    (S.eq_c₀ hS hP) S.alt S.isOuterFactor (by have := S.seven_le_card; omega) hn
    hr.rJ_notMem_socPre hω
  refine ⟨fun ω'' hω'' => ?_, ω', ⟨hω', ?_⟩,
    fun ω'' ⟨h1', h2'⟩ => huniq ω'' ⟨h1', Subtype.ext h2'⟩⟩
  · have := congrArg Subtype.val (h1 ω'' hω'')
    rw [mul_smul] at this ⊢
    exact this
  · exact congrArg Subtype.val hfix

theorem exists_fixSet (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) :
    ∃ β₁ γ₁ : fixSet Ω V,
      β₁ ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptβ ∧
      γ₁ ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptγ ∧
      r • (β₁ : Ω) = β₁ ∧ r • (γ₁ : Ω) = γ₁ ∧
      (∀ ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptβ,
        r • (ω : Ω) = ω → ω = β₁) ∧
      fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) = {α, (β₁ : Ω), (γ₁ : Ω)} ∧
      ∀ ω : fixSet Ω V, v • (ω : Ω) = ω → (r * r) • (ω : Ω) = ω := by
  have hrα : S.D.ρ S.c₀ hr.rJ (S.D.coord S.ptα S.c₀) = S.D.coord S.ptα S.c₀ := by
    rw [← S.D.coord_smul]
    congr 2
    exact Subtype.ext (by rw [hr.rJ_smul]; exact hr.fix)
  obtain ⟨hα1, hα2⟩ := hr.block hS hP hrα
  obtain ⟨hβ1, β₁, ⟨hβ₁, hrβ₁⟩, hβu⟩ := hr.block hS hP hr.fix_β
  obtain ⟨hγ1, γ₁, ⟨hγ₁, hrγ₁⟩, hγu⟩ := hr.block hS hP hr.fix_γ
  have hblocks : ∀ ω : fixSet Ω V, v • (ω : Ω) = ω →
      ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptα ∨
      ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptβ ∨
      ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptγ := fun ω hω => by
    simp only [S.mem_orbit_iff hS hP]
    exact (S.smul_eq_self_iff hS hP ω).mp hω
  have hvβ₁ : v • (β₁ : Ω) = β₁ :=
    (S.smul_eq_self_iff hS hP β₁).mpr (Or.inr (Or.inl ((S.mem_orbit_iff hS hP _ _).mp hβ₁)))
  have hvγ₁ : v • (γ₁ : Ω) = γ₁ :=
    (S.smul_eq_self_iff hS hP γ₁).mpr (Or.inr (Or.inr ((S.mem_orbit_iff hS hP _ _).mp hγ₁)))
  refine ⟨β₁, γ₁, hβ₁, hγ₁, hrβ₁, hrγ₁, fun ω hω hrω => hβu ω ⟨hω, hrω⟩, ?_,
    fun ω hω => ?_⟩
  · ext ω
    rw [fixSet_sup, fixSet_sup, fixSet_zpowers, fixSet_zpowers]
    constructor
    · rintro ⟨⟨hV, hv⟩, hrω⟩
      rcases hblocks ⟨ω, hV⟩ hv with h | h | h
      · have := hα2.unique ⟨h, hrω⟩ ⟨mem_orbit_self _, hr.fix⟩
        exact Or.inl (congrArg Subtype.val this)
      · exact Or.inr (Or.inl (congrArg Subtype.val (hβu ⟨ω, hV⟩ ⟨h, hrω⟩)))
      · exact Or.inr (Or.inr (congrArg Subtype.val (hγu ⟨ω, hV⟩ ⟨h, hrω⟩)))
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨S.ptα.2, hP.typeL.smul_eq⟩, hr.fix⟩
      · exact ⟨⟨β₁.2, hvβ₁⟩, hrβ₁⟩
      · exact ⟨⟨γ₁.2, hvγ₁⟩, hrγ₁⟩
  · rcases hblocks ω hω with h | h | h
    · exact hα1 ω h
    · exact hβ1 ω h
    · exact hγ1 ω h

theorem mem_p46Orbit (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) {β₁ γ₁ : fixSet Ω V}
    (hβ₁ : β₁ ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptβ)
    (hγ₁ : γ₁ ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptγ)
    (hfix : fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) = {α, (β₁ : Ω), (γ₁ : Ω)})
    (hr2 : ∀ ω : fixSet Ω V, v • (ω : Ω) = ω → (r * r) • (ω : Ω) = ω) :
    (β₁ : Ω) ∈ p46Orbit G Ω v P α ∧ (γ₁ : Ω) ∈ p46Orbit G Ω v P α := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hab, hga, hgb⟩ := S.coord_ne_three
  have hcβ₁ := (S.mem_orbit_iff hS hP _ _).mp hβ₁
  have hcγ₁ := (S.mem_orbit_iff hS hP _ _).mp hγ₁
  have hαβ₁ : α ≠ (β₁ : Ω) := fun h => hab (by rw [show S.ptα = β₁ from Subtype.ext h, hcβ₁])
  have hαγ₁ : α ≠ (γ₁ : Ω) := fun h => hga (by
    rw [← hcγ₁, ← show S.ptα = γ₁ from Subtype.ext h])
  have hβγ₁ : (β₁ : Ω) ≠ γ₁ := fun h => hgb (by
    rw [← hcγ₁, ← hcβ₁, show β₁ = γ₁ from Subtype.ext h])
  have hrV : r ∈ Subgroup.centralizer (V : Set G) := Subgroup.centralizer_le S.le_W hr.mem
  have hrv : Commute r v := S.x_comm r hr.mem hr.comm
  have hvV := S.v_mem
  have hv2' : IsPGroup 2 (Subgroup.zpowers v) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one])
  have hX₀2 : IsPGroup 2 (V ⊔ Subgroup.zpowers v : Subgroup G) :=
    S.sylow.2.1.to_sup_of_normal_left' hv2'
      (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hvV))
  have hX₀r : V ⊔ Subgroup.zpowers v ≤ Subgroup.centralizer ((Subgroup.zpowers r : Subgroup G) :
      Set G) := by
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hrV)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun g hg => by
        obtain ⟨n, rfl⟩ := hg
        exact (hrv.zpow_left n).eq)
  have h𝔛2 : IsPGroup 2 (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r : Subgroup G) :=
    hX₀2.to_sup_of_normal_left' hr.two (Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer _ (Subgroup.le_centralizer_iff.mp hX₀r
        (Subgroup.mem_zpowers r))))
  have hfα : α ∈ fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) := by
    rw [hfix]; exact Set.mem_insert _ _
  have h3 : 3 ≤ Nat.card (fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r)) := by
    rw [hfix, Nat.card_coe_set_eq, Set.ncard_eq_three.mpr ⟨α, β₁, γ₁, hαβ₁, hαγ₁, hβγ₁, rfl⟩]
  obtain ⟨t, htα, ht𝔛⟩ := hS.star.star α _ h𝔛2 (fun g hg => hfα g hg) h3
  have htX : ∀ g ∈ V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r, Commute t g := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp ht𝔛 g hg).symm
  have htV : t ∈ Subgroup.centralizer (V : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun g hg => (htX g (Subgroup.mem_sup_left (Subgroup.mem_sup_left hg))).eq.symm
  have htv : Commute t v :=
    htX v (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers v)))
  have htr : Commute t r := htX r (Subgroup.mem_sup_right (Subgroup.mem_zpowers r))
  have ht2 : t * t = 1 := mul_self_eq_one_of_mem_longInv htα.1
  have hC : ∀ g : G, Commute g v → g ∈ Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G) := fun g hg =>
    Subgroup.mem_centralizer_iff.mpr fun _ ⟨n, hn⟩ => hn ▸ (hg.zpow_right n).eq.symm
  have hX₀C : V ⊔ Subgroup.zpowers v ≤ Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    sup_le (fun g hg => hC g (Subgroup.mem_centralizer_iff.mp hvV g hg))
      (Subgroup.zpowers_le.mpr (hC v (Commute.refl v)))
  set Ŝ : Subgroup (typeLSection G Ω v) := ((V ⊔ Subgroup.zpowers v).subgroupOf
    (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))).map
      (restrictCentralizer Ω (Subgroup.zpowers v)) with hŜdef
  have hŜ2 : IsPGroup 2 Ŝ := (hX₀2.comap_of_injective _ (Subgroup.subtype_injective _)).map _
  have hmemŜ : ∀ φ : fixSet Ω (Subgroup.zpowers v), φ ∈ fixSet (fixSet Ω (Subgroup.zpowers v)) Ŝ ↔
      ∀ g ∈ V ⊔ Subgroup.zpowers v, g • (φ : Ω) = φ := fun φ => by
    constructor
    · intro h g hg
      have := h _ ⟨⟨g, hX₀C hg⟩, hg, rfl⟩
      exact congrArg Subtype.val this
    · rintro h _ ⟨⟨g, hgC⟩, hg, rfl⟩
      exact Subtype.ext (h g hg)
  set res : ∀ g : G, Commute g v → typeLSection G Ω v := fun g hg =>
    restrictCentralizer Ω (Subgroup.zpowers v) ⟨g, hC g hg⟩ with hresdef
  have hres : ∀ g hg (φ : fixSet Ω (Subgroup.zpowers v)),
      ((res g hg • φ : fixSet Ω (Subgroup.zpowers v)) : Ω) = g • (φ : Ω) := fun _ _ _ => rfl
  have hresŜ : ∀ g (hg : Commute g v), (∀ k ∈ V ⊔ Subgroup.zpowers v, Commute g k) →
      res g hg ∈ Subgroup.centralizer (Ŝ : Set (typeLSection G Ω v)) := by
    rintro g hg hgk _ ⟨⟨k, hkC⟩, hk, rfl⟩
    refine Subtype.ext (Equiv.ext fun φ => Subtype.ext ?_)
    show k • g • (φ : Ω) = g • k • (φ : Ω)
    rw [smul_smul, smul_smul, (hgk k hk).eq]
  have hPodd : Odd (Nat.card P) :=
    Odd.of_dvd_nat (odd_card_pPrimeCore_two (G := typeLSection G Ω v))
    (Subgroup.card_dvd_of_le hP.le_oddCore)
  have hαΦ : α ∈ fixSet Ω (Subgroup.zpowers v) :=
    mem_fixSet_iff_le_stabilizer.mpr (Subgroup.zpowers_le.mpr hP.typeL.smul_eq)
  set αΦ : fixSet Ω (Subgroup.zpowers v) := ⟨α, hαΦ⟩
  set A : Set (fixSet Ω (Subgroup.zpowers v)) :=
    {φ | φ ∈ orbit P αΦ ∧ φ ∈ fixSet (fixSet Ω (Subgroup.zpowers v)) Ŝ} with hAdef
  have hstab : ∀ σ : typeLSection G Ω v, σ • αΦ ∈ orbit P αΦ →
      σ ∈ Subgroup.normalizer (Ŝ : Set (typeLSection G Ω v)) → σ ∈ stabilizer _ A := by
    intro σ hσα hσŜ
    have hsub : σ • A ⊆ A := by
      rintro _ ⟨φ, ⟨⟨p, rfl⟩, hφŜ⟩, rfl⟩
      obtain ⟨q, hq⟩ := hσα
      have hq' : (q : P) • αΦ = σ • αΦ := hq
      refine ⟨?_, smul_mem_fixSet_of_mem_normalizer hσŜ hφŜ⟩
      refine ⟨⟨σ * p * σ⁻¹, hP.normal.conj_mem _ p.2 σ⟩ * q, ?_⟩
      show (⟨σ * p * σ⁻¹, hP.normal.conj_mem _ p.2 σ⟩ * q : P) • αΦ = σ • ((p : P) • αΦ)
      rw [mul_smul, hq']
      show (σ * p * σ⁻¹) • σ • αΦ = σ • (p : typeLSection G Ω v) • αΦ
      rw [smul_smul, inv_mul_cancel_right, mul_smul]
    rw [mem_stabilizer_iff]
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_smul_set]) (Set.toFinite _)
  have hrHŜ : res r hrv ∈ Subgroup.centralizer (Ŝ : Set (typeLSection G Ω v)) :=
    hresŜ r hrv fun k hk => Subgroup.mem_centralizer_iff.mp (hX₀r hk) r (Subgroup.mem_zpowers r)
  have htHŜ : res t htv ∈ Subgroup.centralizer (Ŝ : Set (typeLSection G Ω v)) :=
    hresŜ t htv fun k hk => htX k (Subgroup.mem_sup_left hk)
  have hrHα : res r hrv • αΦ = αΦ := Subtype.ext hr.fix
  have htHα : res t htv • αΦ = αΦ := Subtype.ext htα.2
  have hrHA : res r hrv ∈ stabilizer _ A := hstab _ (by rw [hrHα]; exact mem_orbit_self _)
    (Subgroup.centralizer_le_normalizer _ hrHŜ)
  have htHA : res t htv ∈ stabilizer _ A := hstab _ (by rw [htHα]; exact mem_orbit_self _)
    (Subgroup.centralizer_le_normalizer _ htHŜ)
  set N₀ : Subgroup (typeLSection G Ω v) := P ⊓ Subgroup.centralizer (Ŝ : Set _) with hN₀def
  have hN₀A : N₀ ≤ stabilizer _ A := fun n hn =>
    hstab n ⟨⟨n, hn.1⟩, rfl⟩ (Subgroup.centralizer_le_normalizer _ hn.2)
  set ψA := MulAction.toPermHom (stabilizer (typeLSection G Ω v) A) A with hψAdef
  set N₂ := (N₀.subgroupOf (stabilizer (typeLSection G Ω v) A)).map ψA with hN₂def
  set a := ψA ⟨res r hrv, hrHA⟩ with hadef
  set b := ψA ⟨res t htv, htHA⟩ with hbdef
  have hαA : αΦ ∈ A :=
    ⟨mem_orbit_self _, (hmemŜ αΦ).mpr fun g hg => hfα g (Subgroup.mem_sup_left hg)⟩
  have hβΦ : X.β ∈ fixSet Ω (Subgroup.zpowers v) :=
    mem_fixSet_iff_le_stabilizer.mpr (Subgroup.zpowers_le.mpr (smul_eq_of_mem_p46Orbit X.mem))
  have hβA : (⟨X.β, hβΦ⟩ : fixSet Ω (Subgroup.zpowers v)) ∈ A := by
    refine ⟨?_, (hmemŜ _).mpr fun g hg => ?_⟩
    · obtain ⟨p, hp, a', ha', hpa⟩ := X.mem
      have h1 : a' = αΦ := Subtype.ext ha'
      refine ⟨⟨p, hp⟩, Subtype.ext ?_⟩
      show ((p • αΦ : fixSet Ω (Subgroup.zpowers v)) : Ω) = X.β
      rw [← h1]
      exact hpa
    · have : V ⊔ Subgroup.zpowers v ≤ stabilizer G X.β :=
        sup_le (mem_fixSet_iff_le_stabilizer.mp S.ptβ.2)
          (Subgroup.zpowers_le.mpr (smul_eq_of_mem_p46Orbit X.mem))
      exact this hg
  have hbase : ∀ y : A, ∃ m ∈ N₀, m • αΦ = (y : fixSet Ω (Subgroup.zpowers v)) := by
    intro y
    obtain ⟨⟨p, hp⟩, hpy⟩ := y.2.1
    obtain ⟨m, hm, hmy⟩ := exists_mem_centralizer_smul_eq (p := 2) (N := P) (S := Ŝ)
      hPodd.not_two_dvd_nat hŜ2
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hP.normal]; exact le_top) hαA.2 y.2.2 hp hpy
    exact ⟨m, hm, hmy⟩
  have htrans : IsPretransitive N₂ A := ⟨fun y z => by
    obtain ⟨m, hm, hmy⟩ := hbase y
    obtain ⟨m', hm', hmz⟩ := hbase z
    have hmm : m' * m⁻¹ ∈ N₀ := mul_mem hm' (inv_mem hm)
    refine ⟨⟨ψA ⟨m' * m⁻¹, hN₀A hmm⟩, ⟨⟨m' * m⁻¹, hN₀A hmm⟩, hmm, rfl⟩⟩, Subtype.ext ?_⟩
    show (m' * m⁻¹) • (y : fixSet Ω (Subgroup.zpowers v)) = z
    rw [mul_smul, ← hmy, inv_smul_smul, hmz]⟩
  have hN₂odd : Odd (Nat.card N₂) := by
    refine Odd.of_dvd_nat hPodd ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀A).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have ha : a * a = 1 := Equiv.ext fun y => Subtype.ext (Subtype.ext (by
    show r • r • ((y : fixSet Ω (Subgroup.zpowers v)) : Ω) = (y : fixSet Ω (Subgroup.zpowers v))
    have hyV : ((y : fixSet Ω (Subgroup.zpowers v)) : Ω) ∈ fixSet Ω V := fun g hg =>
      (hmemŜ _).mp y.2.2 g (Subgroup.mem_sup_left hg)
    have := hr2 ⟨_, hyV⟩ ((y : fixSet Ω (Subgroup.zpowers v)).2 v (Subgroup.mem_zpowers v))
    rwa [mul_smul] at this))
  have hb : b * b = 1 := Equiv.ext fun y => Subtype.ext (Subtype.ext (by
    show t • t • ((y : fixSet Ω (Subgroup.zpowers v)) : Ω) = (y : fixSet Ω (Subgroup.zpowers v))
    rw [smul_smul, ht2, one_smul]))
  have hab' : Commute a b := Equiv.ext fun y => Subtype.ext (Subtype.ext (by
    show r • t • ((y : fixSet Ω (Subgroup.zpowers v)) : Ω) =
      t • r • ((y : fixSet Ω (Subgroup.zpowers v)) : Ω)
    rw [smul_smul, smul_smul, htr.eq]))
  have hnorm : ∀ σ : stabilizer (typeLSection G Ω v) A,
      (σ : typeLSection G Ω v) ∈ Subgroup.centralizer (Ŝ : Set (typeLSection G Ω v)) →
      ψA σ ∈ Subgroup.normalizer (N₂ : Set (Equiv.Perm A)) := by
    intro σ hσ
    refine Subgroup.le_normalizer_map ψA ⟨σ, ?_, rfl⟩
    have key : ∀ k : typeLSection G Ω v, k ∈ Subgroup.centralizer (Ŝ : Set _) →
        ∀ m, m ∈ N₀ → k * m * k⁻¹ ∈ N₀ := fun k hk m hm =>
      Subgroup.mem_inf.mpr ⟨hP.normal.conj_mem m (Subgroup.mem_inf.mp hm).1 k,
        mul_mem (mul_mem hk (Subgroup.mem_inf.mp hm).2) (inv_mem hk)⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    refine ⟨fun hn => key _ hσ _ hn, fun hn => ?_⟩
    have := key _ (inv_mem hσ) _ hn
    rwa [inv_inv, show (σ : typeLSection G Ω v)⁻¹ * (σ * n * (σ : typeLSection G Ω v)⁻¹) * σ =
      n by group] at this
  have hb' : fixedBy A b = {⟨αΦ, hαA⟩} := by
    ext y
    rw [mem_fixedBy, Set.mem_singleton_iff]
    constructor
    · intro hy
      have h1 : t • ((y : fixSet Ω (Subgroup.zpowers v)) : Ω) =
          (y : fixSet Ω (Subgroup.zpowers v)) :=
        congrArg (fun z : A => ((z : fixSet Ω (Subgroup.zpowers v)) : Ω)) hy
      obtain ⟨c, -, hcu⟩ := htα.1.2
      exact Subtype.ext (Subtype.ext ((hcu _ h1).trans (hcu _ htα.2).symm))
    · rintro rfl
      exact Subtype.ext htHα
  have htJ : restrictCentralizer Ω V ⟨t, htV⟩ ∈ jHull (centralizerImage Ω V) (fixSet Ω V) :=
    mem_jHull_of_mem_longInv ((hS.mem_longInv_centralizerImage_iff S.sylow.2.1
      (X.three_le_card_fixSet S.sylow.1) _).mpr ⟨t, htα.1, htV, fun _ => rfl⟩)
  have hβne : (a * b) ⟨⟨X.β, hβΦ⟩, hβA⟩ ≠ ⟨⟨X.β, hβΦ⟩, hβA⟩ := by
    intro h
    have h1 : r • t • X.β = X.β :=
      congrArg (fun z : A => ((z : fixSet Ω (Subgroup.zpowers v)) : Ω)) h
    have hct := S.coord_t_smul_β hS hP htα htV htv htJ
    have h2 : (hr.rJ : centralizerImage Ω V) •
        ((⟨_, htJ⟩ : jHull (centralizerImage Ω V) (fixSet Ω V)) : centralizerImage Ω V) •
          S.ptβ = S.ptβ := Subtype.ext h1
    have h3 := congrArg (fun ω => S.D.coord ω S.c₀) h2
    have h4 : S.D.coord ((restrictCentralizer Ω V ⟨t, htV⟩ : centralizerImage Ω V) • S.ptβ)
        S.c₀ = S.D.coord S.ptγ S.c₀ := (S.D.coord_smul ⟨_, htJ⟩ S.ptβ S.c₀).trans hct
    simp only [S.D.coord_smul] at h3
    rw [h4] at h3
    exact hgb ((show S.D.ρ S.c₀ hr.rJ (S.D.coord S.ptγ S.c₀) = S.D.coord S.ptγ S.c₀ from
      hr.fix_γ).symm.trans h3)
  have h3a := three_le_ncard_fixedBy (A := A) (N := N₂) hN₂odd ha hb hab' (hnorm _ hrHŜ)
    (hnorm _ htHŜ) hb' hβne
  set f : A → Ω := fun y => ((y : fixSet Ω (Subgroup.zpowers v)) : Ω) with hfdef
  have hfinj : Function.Injective f := fun y z h => Subtype.ext (Subtype.ext h)
  have hsub : f '' fixedBy A a ⊆ {α, (β₁ : Ω), (γ₁ : Ω)} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hfix, fixSet_sup, fixSet_sup, fixSet_zpowers, fixSet_zpowers]
    have hyr : r • f y = f y :=
      congrArg (fun z : A => ((z : fixSet Ω (Subgroup.zpowers v)) : Ω)) hy
    exact ⟨⟨fun g hg => (hmemŜ _).mp y.2.2 g (Subgroup.mem_sup_left hg),
      (y : fixSet Ω (Subgroup.zpowers v)).2 v (Subgroup.mem_zpowers v)⟩, hyr⟩
  have heq : f '' fixedBy A a = {α, (β₁ : Ω), (γ₁ : Ω)} :=
    Set.eq_of_subset_of_ncard_le hsub (by
      rw [Set.ncard_image_of_injective _ hfinj,
        Set.ncard_eq_three.mpr ⟨α, β₁, γ₁, hαβ₁, hαγ₁, hβγ₁, rfl⟩]
      exact h3a) (Set.toFinite _)
  have hmemC : ∀ ω ∈ ({α, (β₁ : Ω), (γ₁ : Ω)} : Set Ω), ω ∈ p46Orbit G Ω v P α := by
    intro ω hω
    rw [← heq] at hω
    obtain ⟨y, -, rfl⟩ := hω
    obtain ⟨⟨p, hp⟩, hpy⟩ := y.2.1
    exact ⟨p, hp, αΦ, rfl, congrArg Subtype.val hpy⟩
  exact ⟨hmemC _ (by simp), hmemC _ (by simp)⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem γ₁_mem (hP : Prop46Setup G Ω α v P) {β₁ γ₁ : Ω} (hβ₁C : β₁ ∈ p46Orbit G Ω v P α)
    (hβ₁α : β₁ ≠ α) (hfix : fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) = {α, β₁, γ₁}) :
    γ₁ ∈ holtDelta G Ω α β₁ ∧ v • γ₁ = γ₁ := by
  obtain ⟨γ', ⟨hγ'Δ, hvγ'⟩, huniq⟩ := hP.one_point β₁ hβ₁C hβ₁α
  have hrv : Commute r v := S.x_comm r hr.mem hr.comm
  have hX : ∀ g ∈ V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r, Commute g v := by
    intro g hg
    have hle : V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r ≤
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro g hg
        exact Subgroup.mem_centralizer_iff.mpr fun _ ⟨n, hn⟩ => hn ▸
          ((show Commute g v from Subgroup.mem_centralizer_iff.mp S.v_mem g hg).zpow_right
            n).eq.symm
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun _ ⟨n, hn⟩ => hn ▸
          ((Commute.refl v).zpow_right n).eq.symm)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun _ ⟨n, hn⟩ => hn ▸
          (hrv.zpow_right n).eq.symm)
    exact (Subgroup.mem_centralizer_iff.mp (hle hg) v (Subgroup.mem_zpowers v)).symm
  have hmem : ∀ ω ∈ ({α, β₁, γ₁} : Set Ω), ω ∈ fixSet Ω (V ⊔ Subgroup.zpowers v ⊔
      Subgroup.zpowers r) := fun ω hω => by rw [hfix]; exact hω
  have hγ'fix : γ' ∈ fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) := by
    intro g hg
    have hgα := hmem α (by simp) g hg
    have hgβ := hmem β₁ (by simp) g hg
    have hgΔ : g • γ' ∈ holtDelta G Ω α β₁ := by
      have := stabilizer_pair_le (G := G) α β₁
        (stabilizer_inf_le_stabilizer_pair α β₁ ⟨hgα, hgβ⟩)
      rw [mem_stabilizer_iff] at this
      rw [← this]
      exact Set.smul_mem_smul_set hγ'Δ
    refine huniq _ ⟨hgΔ, ?_⟩
    rw [smul_smul, ← (hX g hg).eq, mul_smul, hvγ']
  rw [hfix] at hγ'fix
  rcases hγ'fix with h | h | h
  · exact absurd (h ▸ hγ'Δ) (left_notMem_holtDelta hβ₁α.symm)
  · exact absurd (h ▸ hγ'Δ) (right_notMem_holtDelta hβ₁α.symm)
  · rw [Set.mem_singleton_iff] at h
    exact h ▸ ⟨hγ'Δ, hvγ'⟩

omit hr in
theorem ncard_Λ_le (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) {β₁ : fixSet Ω V}
    (hβ₁ : β₁ ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptβ) :
    X.Λ.ncard ≤ (holtDelta G Ω α β₁ ∩ fixSet Ω V).ncard := by
  classical
  have hcβ₁ := (S.mem_orbit_iff hS hP _ _).mp hβ₁
  obtain ⟨hab, -, -⟩ := S.coord_ne_three
  have hab' : S.D.coord S.ptα S.c₀ ≠ S.D.coord β₁ S.c₀ := hcβ₁ ▸ hab
  have hne : S.ptα ≠ β₁ := fun h => hab' (by rw [h])
  set ΔK := holtDelta (centralizerImage Ω V) (fixSet Ω V) S.ptα β₁
  have himg : (fun δ => S.D.coord δ S.c₀) '' ΔK =
      ({S.D.coord S.ptα S.c₀, S.D.coord β₁ S.c₀}ᶜ : Set (S.D.Ψc S.c₀)) := by
    have h1 := S.D.coord_holtDelta_eq S.ptα β₁
    rw [← S.D.holtDelta_range_rho_eq_compl S.alt hab']
    ext p
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      exact S.D.coord_mem_holtDelta hδ S.c₀
    · intro hp
      obtain ⟨y, hy⟩ := S.D.coord_surjective (Function.update (S.D.coord S.ptα) S.c₀ p)
      have hmem : S.D.coord y ∈ Set.univ.pi fun i => holtDelta (S.D.ρ i).range (S.D.Ψc i)
          (S.D.coord S.ptα i) (S.D.coord β₁ i) := fun i _ => by
        obtain rfl := S.eq_c₀ hS hP i
        rw [hy, Function.update_self]
        exact hp
      rw [← h1] at hmem
      obtain ⟨δ, hδ, hδy⟩ := hmem
      refine ⟨δ, hδ, ?_⟩
      show S.D.coord δ S.c₀ = p
      rw [hδy, hy, Function.update_self]
  have h3 := X.three_le_card_fixSet S.sylow.1
  have hcard : X.Λ.ncard ≤ ΔK.ncard := by
    have h1 := Set.ncard_image_le (f := fun δ => S.D.coord δ S.c₀) (s := ΔK) (Set.toFinite _)
    rw [himg, Set.ncard_compl, Set.ncard_pair hab', Nat.card_eq_fintype_card, S.card] at h1
    omega
  refine hcard.trans ?_
  rw [← Set.ncard_image_of_injective ΔK Subtype.val_injective]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨δ, hδ, rfl⟩
  exact ⟨(hS.mem_holtDelta_centralizerImage_iff S.sylow.2.1 h3 hne).mp hδ, δ.2⟩

theorem isCaseAOutput (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) :
    ∃ β₁ γ₁ : fixSet Ω V, IsCaseAOutput X V r β₁ γ₁ ∧
      β₁ ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptβ ∧
      ∀ ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptβ,
        r • (ω : Ω) = ω → ω = β₁ := by
  obtain ⟨β₁, γ₁, hβ₁, hγ₁, -, -, huniq, hfix, hr2⟩ := hr.exists_fixSet hS hP
  obtain ⟨hβ₁C, hγ₁C⟩ := hr.mem_p46Orbit hS hP hβ₁ hγ₁ hfix hr2
  obtain ⟨hab, -, -⟩ := S.coord_ne_three
  have hcβ₁ := (S.mem_orbit_iff hS hP _ _).mp hβ₁
  have hβ₁α : (β₁ : Ω) ≠ α := fun h => hab (by
    rw [← hcβ₁, show S.ptα = β₁ from Subtype.ext h.symm])
  obtain ⟨hγΔ, hvγ⟩ := hr.γ₁_mem hP hβ₁C hβ₁α hfix
  refine ⟨β₁, γ₁, ?_, hβ₁, huniq⟩
  exact { two := hr.two, mem_V := Subgroup.centralizer_le S.le_W hr.mem
          comm := S.x_comm r hr.mem hr.comm, fix_α := hr.fix, fixSet_eq := hfix
          mem_β₁ := hβ₁C, ne := hβ₁α, mem_γ₁ := hγ₁C, γ₁_mem := hγΔ, v_γ₁ := hvγ
          ncard_le := ncard_Λ_le (S := S) hS hP hβ₁
          orbit := ⟨S.ptβ.2, β₁.2, S.ptγ.2, γ₁.2, hβ₁, hγ₁⟩ }

end IsAdmissibleElt

include S in
theorem exists_output_fix_τ (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (hτα : τ • α = α) (hτβ : τ • X.β = X.β) :
    ∃ (r : G) (β₁ γ₁ : Ω), IsCaseAOutput X V r β₁ γ₁ ∧ τ • β₁ = β₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B₂ : Set Ω := (↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptβ with hB₂
  set B₃ : Set Ω := (↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptγ with hB₃
  have hτB₂ : τ • B₂ = B₂ := smul_image_orbit_eq S.τ_mem S.ptβ hτβ
  have hτB₃ : τ • B₃ = B₃ := smul_image_orbit_eq S.τ_mem S.ptγ (S.τ_smul_γ hP hτα hτβ)
  set 𝒬₂ : Subgroup G := Subgroup.centralizer (S.W : Set G) ⊓
    Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ⊓ stabilizer G α ⊓
      stabilizer G B₂ ⊓ stabilizer G B₃ with h𝒬₂
  have hCv : ∀ g : G, Commute g v →
      g ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := fun g hg =>
    Subgroup.mem_centralizer_iff.mpr fun _ ⟨n, hn⟩ => hn ▸ (hg.zpow_right n).eq.symm
  have hτN : τ ∈ Subgroup.normalizer (𝒬₂ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.inf_normalizer_le_normalizer_inf
        ⟨mem_normalizer_centralizer S.τ_mem_W, Subgroup.le_normalizer (hCv τ S.τ_comm)⟩,
        Subgroup.le_normalizer (show τ ∈ stabilizer G α from hτα)⟩,
      Subgroup.le_normalizer (show τ ∈ stabilizer G B₂ from hτB₂)⟩,
      Subgroup.le_normalizer (show τ ∈ stabilizer G B₃ from hτB₃)⟩
  obtain ⟨r₀, hr₀⟩ := S.exists_admissibleElt hS hP
  obtain ⟨β₁, γ₁, hout, hβ₁, huniq⟩ := hr₀.isCaseAOutput hS hP
  have hr₀B : ∀ ω₀ : fixSet Ω V, S.D.ρ S.c₀ hr₀.rJ (S.D.coord ω₀ S.c₀) = S.D.coord ω₀ S.c₀ →
      r₀ • ((↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ : Set Ω) =
        (↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ := fun ω₀ h => by
    have hsub : r₀ • ((↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ :
        Set Ω) ⊆ (↑) '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ := by
      rintro _ ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
      exact ⟨_, S.smul_mem_orbit_of_rho hS hP hr₀.rJ h hω, rfl⟩
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_smul_set]) (Set.toFinite _)
  have hr₀𝒬 : r₀ ∈ 𝒬₂ := ⟨⟨⟨⟨hr₀.mem, hCv r₀ (S.x_comm r₀ hr₀.mem hr₀.comm)⟩, hr₀.fix⟩,
    hr₀B S.ptβ hr₀.fix_β⟩, hr₀B S.ptγ hr₀.fix_γ⟩
  obtain ⟨𝒮, hτ𝒮, h𝒮⟩ := exists_fusionIsSylowIn_ge S.τ_two
    (le_sup_right : Subgroup.zpowers τ ≤ 𝒬₂ ⊔ Subgroup.zpowers τ)
  obtain ⟨R, hr₀R, hR⟩ := exists_fusionIsSylowIn_ge hr₀.two
    ((Subgroup.zpowers_le.mpr hr₀𝒬).trans (le_sup_left : 𝒬₂ ≤ 𝒬₂ ⊔ Subgroup.zpowers τ))
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn h𝒮 hR
  have hk𝒮 : k⁻¹ * r₀ * k ∈ 𝒮 := (hkR r₀).mp (hr₀R (Subgroup.mem_zpowers r₀))
  have hkmem : k ∈ ((𝒬₂ : Set G) * (Subgroup.zpowers τ : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left 𝒬₂ (Subgroup.zpowers τ)
      (Subgroup.zpowers_le.mpr hτN)]
    exact hk
  obtain ⟨q, hq, h, hh, rfl⟩ := hkmem
  have hh𝒮 : h ∈ 𝒮 := hτ𝒮 hh
  have hr𝒮 : q⁻¹ * r₀ * q ∈ 𝒮 := by
    have := mul_mem (mul_mem hh𝒮 hk𝒮) (inv_mem hh𝒮)
    rwa [show h * ((q * h)⁻¹ * r₀ * (q * h)) * h⁻¹ = q⁻¹ * r₀ * q by group] at this
  obtain ⟨⟨⟨⟨hqW, hqC⟩, hqα⟩, hqB₂⟩, hqB₃⟩ := hq
  have hqV : q ∈ Subgroup.centralizer (V : Set G) := Subgroup.centralizer_le S.le_W hqW
  have hqv : Commute q v := (Subgroup.mem_centralizer_iff.mp hqC v (Subgroup.mem_zpowers v)).symm
  have hqinv : ∀ {B : Set Ω}, q • B = B → q⁻¹ • B = B := fun h' => by
    rw [inv_smul_eq_iff]; exact h'.symm
  have hβ' : q⁻¹ • (β₁ : Ω) ∈ B₂ := by
    rw [← hqinv hqB₂]; exact Set.smul_mem_smul_set ⟨β₁, hβ₁, rfl⟩
  have hγ₁B : (γ₁ : Ω) ∈ B₃ := by
    obtain ⟨hb, hb₁, hc, hc₁, hβo, hγo⟩ := hout.orbit
    exact ⟨⟨γ₁, hc₁⟩, hγo, rfl⟩
  have hγ' : q⁻¹ • (γ₁ : Ω) ∈ B₃ := by
    rw [← hqinv hqB₃]; exact Set.smul_mem_smul_set hγ₁B
  obtain ⟨ωβ, hωβ, hωβe⟩ := hβ'
  obtain ⟨ωγ, hωγ, hωγe⟩ := hγ'
  have hout' := hout.conj X hP hqV hqv hqα
    ⟨S.ptβ.2, hωβe ▸ ωβ.2, by
      rw [show (⟨q⁻¹ • (β₁ : Ω), hωβe ▸ ωβ.2⟩ : fixSet Ω V) = ωβ from Subtype.ext hωβe.symm]
      exact hωβ⟩
    ⟨S.ptγ.2, hωγe ▸ ωγ.2, by
      rw [show (⟨q⁻¹ • (γ₁ : Ω), hωγe ▸ ωγ.2⟩ : fixSet Ω V) = ωγ from Subtype.ext hωγe.symm]
      exact hωγ⟩
  have h𝒮B : 𝒮 ≤ stabilizer G B₂ :=
    h𝒮.1.trans (sup_le (fun g hg => hg.1.2) (Subgroup.zpowers_le.mpr hτB₂))
  have hB₂odd : Odd (Nat.card B₂) := by
    rw [Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Subtype.val_injective,
      ← Nat.card_coe_set_eq]
    exact odd_card_orbit_jOddCore _
  have hP𝒮 : IsPGroup 2 (𝒮.subgroupOf (stabilizer G B₂)) :=
    h𝒮.2.1.comap_of_injective _ (Subgroup.subtype_injective _)
  obtain ⟨ω₀, hω₀⟩ := fixSet_nonempty_of_odd hB₂odd hP𝒮
  have h𝒮ω₀ : ∀ s ∈ 𝒮, s • (ω₀ : Ω) = ω₀ := fun s hs => by
    have := hω₀ ⟨s, h𝒮B hs⟩ (Subgroup.mem_subgroupOf.mpr hs)
    exact congrArg Subtype.val this
  have hω₀eq : (ω₀ : Ω) = q⁻¹ • (β₁ : Ω) := by
    have h1 := h𝒮ω₀ _ hr𝒮
    rw [mul_smul, mul_smul, inv_smul_eq_iff] at h1
    have h3 : q • (ω₀ : Ω) ∈ q • B₂ := Set.smul_mem_smul_set ω₀.2
    rw [hqB₂] at h3
    obtain ⟨ω', hω', hω'eq⟩ := h3
    have h4 : ω' = β₁ := huniq ω' hω' (by rw [hω'eq]; exact h1)
    rw [eq_inv_smul_iff, ← hω'eq, h4]
  refine ⟨q⁻¹ * r₀ * q, q⁻¹ • (β₁ : Ω), q⁻¹ • (γ₁ : Ω), hout', ?_⟩
  rw [← hω₀eq]
  exact h𝒮ω₀ τ (hτ𝒮 (Subgroup.mem_zpowers τ))

end CaseASection

end Start3

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

theorem CaseASection.exists_output {X : CaseAStart G Ω α v P} {V : Subgroup G} {τ : G}
    (S : CaseASection X V τ) (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) :
    ∃ (r : G) (β₁ γ₁ : Ω), IsCaseAOutput X V r β₁ γ₁ := by
  obtain ⟨r, hr⟩ := S.exists_admissibleElt hS hP
  obtain ⟨β₁, γ₁, hout, -⟩ := hr.isCaseAOutput hS hP
  exact ⟨r, β₁, γ₁, hout⟩

omit [Finite G] in
theorem isPGroup_zpowers_one : IsPGroup 2 (Subgroup.zpowers (1 : G)) := by
  rw [Subgroup.zpowers_one_eq_bot]
  exact IsPGroup.of_bot

theorem Sec4Setting.caseA_typeB (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (h43 : ∀ a b : Ω, a ≠ b → IsEmpty (AltConfig G Ω a b)) (hD : CaseAStepA7 G Ω α v P)
    (X : CaseAStart G Ω α v P) {V : Subgroup G}
    (hVs : fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ))
    (hVw : X.w ∈ Subgroup.normalizer (V : Set G)) (hκ : IsKappaMaximal X V) :
    ∃ (r : G) (β₁ γ₁ : Ω), IsCaseAOutput X V r β₁ γ₁ ∧ IsTypeBAt G Ω α β₁ ∧
      Nat.card (holtDelta G Ω α β₁) ≠ 5 := by
  obtain ⟨S⟩ := X.exists_section hS hP hVs hVw isPGroup_zpowers_one (one_mem _)
    (Commute.one_left v)
  obtain ⟨r, β₁, γ₁, hout⟩ := S.exists_output hS hP
  exact ⟨r, β₁, γ₁, hout, hS.typeB_of_caseA_output hP h43 hD X hVs hVw hκ S.ne_bot hout.two
    hout.mem_V hout.comm hout.fix_α hout.fixSet_eq hout.mem_β₁ hout.ne hout.mem_γ₁ hout.γ₁_mem
    hout.v_γ₁ (X.ncard_Λ.2.trans hout.ncard_le) hout.orbit⟩

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem card_le_of_fusionIsSylowIn {S H Q : Subgroup G} (hS : fusionIsSylowIn 2 S H)
    (hQ : IsPGroup 2 Q) (hQH : Q ≤ H) : Nat.card Q ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hQR, hR⟩ := exists_fusionIsSylowIn_ge hQ hQH
  obtain ⟨k, -, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hS hR
  refine (Subgroup.card_le_of_le hQR).trans (Nat.card_le_card_of_injective
    (fun x : R => (⟨k⁻¹ * x * k, (hkR x).mp x.2⟩ : S)) fun x y h => ?_)
  have := congrArg Subtype.val h
  simp only [mul_left_inj, mul_right_inj] at this
  exact Subtype.ext this

theorem exists_forall_le_of_bdd {ι : Type*} (f : ι → ℕ) {B : ℕ} (hB : ∀ i, f i ≤ B) (i₀ : ι) :
    ∃ i, ∀ j, f j ≤ f i := by
  classical
  have hex : ∃ n, ∀ j, f j ≤ n := ⟨B, hB⟩
  set m := Nat.find hex with hm
  have hmle : ∀ j, f j ≤ m := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · exact ⟨i₀, fun j => (hmle j).trans (h0 ▸ Nat.zero_le _)⟩
  · have hlt : ¬ ∀ j, f j ≤ m - 1 := Nat.find_min hex (by omega)
    simp only [not_forall, not_le] at hlt
    obtain ⟨i, hi⟩ := hlt
    exact ⟨i, fun j => (hmle j).trans (by omega)⟩

omit [FaithfulSMul G Ω] in
theorem exists_isKappaMaximal (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (X₀ : CaseAStart G Ω α v P) :
    ∃ (X : CaseAStart G Ω α v P) (V : Subgroup G),
      fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ) ∧
      X.w ∈ Subgroup.normalizer (V : Set G) ∧ IsKappaMaximal X V := by
  classical
  obtain ⟨X₁, hX₁⟩ := exists_forall_le_of_bdd (fun X : CaseAStart G Ω α v P => X.Λ.ncard)
    (B := Nat.card Ω) (fun X => Set.ncard_le_card _) X₀
  set ι := {p : CaseAStart G Ω α v P × Subgroup G //
    p.2 ≤ caseACentralizer G Ω α p.1.β v p.1.Λ ∧ IsPGroup 2 p.2 ∧ p.1.Λ.ncard = X₁.Λ.ncard}
  obtain ⟨⟨⟨X, V₀⟩, hV₀, hV₀2, hXm⟩, hmax⟩ := exists_forall_le_of_bdd
    (fun p : ι => Nat.card p.1.2) (B := Nat.card G) (fun p => Subgroup.card_le_card_group _)
    ⟨⟨X₁, ⊥⟩, bot_le, IsPGroup.of_bot, rfl⟩
  have hw2 : IsPGroup 2 (Subgroup.zpowers X.w) := zpowers_isPGroup_two_of_pow_eq_one (n := 1)
    (by rw [pow_one, sq]; exact mul_self_eq_one_of_mem_longInv X.w_mem.1)
  obtain ⟨V, hV, hwV⟩ := X.exists_sylow_le_normalizer hw2
    (Subgroup.zpowers_le.mpr (X.w_mem_normalizer_caseACentralizer (X.w_smul_Λ hS hP)))
  refine ⟨X, V, hV, hwV (Subgroup.mem_zpowers _), fun X' V' hV' hV'2 => ?_⟩
  rcases (hX₁ X').lt_or_eq with h | h
  · exact Or.inl (h.trans_le (hXm ▸ le_rfl))
  · refine Or.inr ⟨h.trans hXm.symm, ?_⟩
    have h1 := hmax ⟨⟨X', V'⟩, hV', hV'2, h⟩
    exact h1.trans (card_le_of_fusionIsSylowIn hV hV₀2 hV₀)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem Prop46Setup.exists_caseB (hP : Prop46Setup G Ω α v P) {β : Ω}
    (hβ : β ∈ p46Orbit G Ω v P α) (hβα : β ≠ α) (hB : IsTypeBAt G Ω α β) :
    ∃ γ, Prop46CaseB G Ω α β γ v P := by
  obtain ⟨γ, ⟨hγΔ, hvγ⟩, huniq⟩ := hP.one_point β hβ hβα
  exact ⟨γ, { isTypeL := hP.typeL, ne := hβα.symm, normal := hP.normal, minimal := hP.minimal
              le_oddCore := hP.le_oddCore, mem_orbit := hβ, mem_holtDelta := hγΔ
              fixed_iff := fun δ hδ => ⟨fun h => huniq δ ⟨hδ, h⟩, fun h => h ▸ hvγ⟩
              isNaturalSE := hB.1, odd_card := hB.2 }⟩

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem IsCaseAOutput.rigid {X : CaseAStart G Ω α v P} {V : Subgroup G} {r : G} {β₁ γ₁ : Ω}
    (hout : IsCaseAOutput X V r β₁ γ₁) (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hB : IsTypeBAt G Ω α β₁)
    (hU : IsBenderAction ↥(twoPointJ G Ω α β₁) (holtDelta G Ω α β₁) 2 3 5) :
    Nat.card V = 2 ∧ X.Λ.ncard = 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix : ∀ ω ∈ ({α, β₁, γ₁} : Set Ω), ω ∈ fixSet Ω V := fun ω hω => by
    rw [← hout.fixSet_eq] at hω
    exact fixSet_anti (le_sup_left.trans le_sup_left) hω
  have hVst : V ≤ stabilizer G ({α, β₁} : Set Ω) := fun g hg =>
    stabilizer_inf_le_stabilizer_pair α β₁ ⟨hfix α (by simp) g hg, hfix β₁ (by simp) g hg⟩
  set ψ := twoPointHom G Ω α β₁
  set Pv : Subgroup (Equiv.Perm (holtDelta G Ω α β₁)) :=
    (V.subgroupOf (stabilizer G ({α, β₁} : Set Ω))).map ψ with hPv
  have hker : ∀ g (hg : g ∈ stabilizer G ({α, β₁} : Set Ω)), g ∈ V → ψ ⟨g, hg⟩ = 1 → g = 1 := by
    intro g hg hgV hψ
    have hgK : g ∈ twoPointKernel G Ω α β₁ := by
      refine ⟨⟨hfix α (by simp) g hgV, hfix β₁ (by simp) g hgV⟩,
        (mem_fixingSubgroup_iff G).mpr fun δ hδ => ?_⟩
      have := congrArg (fun σ : Equiv.Perm (holtDelta G Ω α β₁) => (σ ⟨δ, hδ⟩ : Ω)) hψ
      exact this
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hV2) ⟨g, hgV⟩
    have hgn : g ^ 2 ^ n = 1 := by
      have := pow_orderOf_eq_one (⟨g, hgV⟩ : V)
      rw [hn] at this
      exact congrArg Subtype.val this
    exact eq_one_of_pow_two_pow_eq_one_of_mem hB.2 hgK hgn
  set f := ψ.comp (V.subgroupOf (stabilizer G ({α, β₁} : Set Ω))).subtype with hfdef
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun x hx => ?_
    have h2 := hker _ (x : stabilizer G ({α, β₁} : Set Ω)).2 (Subgroup.mem_subgroupOf.mp x.2) hx
    exact Subtype.ext (Subtype.ext h2)
  have hrange : f.range = Pv := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card Pv = Nat.card V := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVst).toEquiv]
  have hPv2 : IsPGroup 2 Pv :=
    (hV2.comap_of_injective _ (Subgroup.subtype_injective _)).map _
  have hPvN : Pv ≤ Subgroup.normalizer (twoPointJ G Ω α β₁ :
      Set (Equiv.Perm (holtDelta G Ω α β₁))) := by
    rintro _ ⟨⟨g, hg⟩, -, rfl⟩
    exact twoPointHom_mem_normalizer hg
  have hPv1 : Pv ≠ ⊥ := fun h => hV1 (by
    rw [← Subgroup.card_eq_one] at h ⊢
    rw [← hcard, h])
  set Λ₁ : Set (holtDelta G Ω α β₁) := {δ | (δ : Ω) ∈ fixSet Ω V}
  have hΛ₁ : Λ₁ ⊆ fixSet (holtDelta G Ω α β₁) Pv := by
    rintro δ hδ _ ⟨⟨g, hg⟩, hgV, rfl⟩
    exact Subtype.ext (hδ g (Subgroup.mem_subgroupOf.mp hgV))
  have hΛ₁card : Λ₁.ncard = (holtDelta G Ω α β₁ ∩ fixSet Ω V).ncard := by
    rw [← Set.ncard_image_of_injective Λ₁ Subtype.val_injective]
    congr 1
    ext ω
    exact ⟨fun ⟨δ, hδ, hδω⟩ => hδω ▸ ⟨δ.2, hδ⟩, fun ⟨h1, h2⟩ => ⟨⟨ω, h1⟩, h2, rfl⟩⟩
  have h5 : 5 ≤ Λ₁.ncard := hΛ₁card ▸ X.ncard_Λ.2.trans hout.ncard_le
  obtain ⟨h2, h5'⟩ := IsBenderAction.card_eq_two_of_subset_fixSet_of_unitary_four hU hPv2 hPvN
    hPv1 hΛ₁ h5
  refine ⟨hcard ▸ h2, le_antisymm ?_ X.ncard_Λ.2⟩
  rw [← h5', hΛ₁card]
  exact hout.ncard_le

omit [Finite G] [FaithfulSMul G Ω] in
theorem Prop46Setup.exists_caseAStart (hP : Prop46Setup G Ω α v P) {β : Ω}
    (hβ : β ∈ p46Orbit G Ω v P α) (hβα : β ≠ α) (h1 : 1 < Nat.card (holtDelta G Ω α β))
    (hA : IsTypeAAt G Ω α β) : ∃ X : CaseAStart G Ω α v P, X.β = β := by
  classical
  obtain ⟨A⟩ := hA
  obtain ⟨w, hw, hwv, hwvJ⟩ := hP.exists_w β hβ hβα
  obtain ⟨γ, ⟨hγΔ, hvγ⟩, huniq⟩ := hP.one_point β hβ hβα
  have hne : Nonempty A.D.ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have hsub : (holtDelta G Ω α β).Subsingleton := fun δ hδ δ' hδ' => by
      have h1 := (A.D.coord_eq_iff ⟨δ, hδ⟩ ⟨δ', hδ'⟩).mp (Subsingleton.elim _ _)
      rw [orbit_jOddCore_eq_singleton A.oddCore_eq_bot] at h1
      exact (congrArg Subtype.val (Set.mem_singleton_iff.mp h1)).symm
    have : (holtDelta G Ω α β).ncard ≤ 1 := Set.ncard_le_one_iff_subsingleton.mpr hsub
    rw [Nat.card_coe_set_eq] at h1
    omega
  obtain ⟨i₀⟩ := hne
  have hwα : w • α = β := hw.2
  have hwγ : w • γ = γ := by
    have hwp : w ∈ stabilizer G ({α, β} : Set Ω) := by
      rw [mem_stabilizer_iff]
      have hwβ : w • β = α := by
        rw [← hwα, smul_smul, mul_self_eq_one_of_mem_longInv hw.1, one_smul]
      rw [Set.smul_set_insert, Set.smul_set_singleton, hwα, hwβ, Set.pair_comm]
    have hΔ := stabilizer_pair_le (G := G) α β hwp
    rw [mem_stabilizer_iff] at hΔ
    have hwγΔ : w • γ ∈ holtDelta G Ω α β := hΔ ▸ Set.smul_mem_smul_set hγΔ
    exact huniq _ ⟨hwγΔ, by rw [smul_smul, ← hwv.eq, mul_smul, hvγ]⟩
  let mk : ∀ Λ : Set Ω, IsAdmissible v w A ⟨γ, hγΔ⟩ Λ → CaseAStart G Ω α v P := fun Λ hΛ =>
    { β := β, mem := hβ, ne := hβα, A := A, w := w, w_mem := hw, w_comm := hwv
      wv_mem := hwvJ, γ := ⟨γ, hγΔ⟩, v_fix := hvγ, Λ := Λ, admissible := hΛ }
  by_cases h2 : 2 ≤ Fintype.card A.D.ι
  · exact ⟨mk _ (Or.inl ⟨h2, i₀, rfl⟩), rfl⟩
  have hι1 : Fintype.card A.D.ι = 1 := by
    have := Fintype.card_pos_iff.mpr ⟨i₀⟩
    omega
  by_cases hT : Odd (Nat.card (twoPointKernel G Ω α β))
  swap
  · exact ⟨mk _ (Or.inr (Or.inl ⟨hι1, hT, rfl⟩)), rfl⟩
  have h5 : 5 ≤ Nat.card (holtDelta G Ω α β) :=
    (A.D.five_le_card i₀).trans (A.card_le_card_holtDelta ⟨γ, hγΔ⟩ i₀)
  obtain ⟨δ, hδΔ, hδγ⟩ : ∃ δ ∈ holtDelta G Ω α β, δ ≠ γ := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have : (holtDelta G Ω α β).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.mpr fun x hx y hy => (h x hx).trans (h y hy).symm
    rw [Nat.card_coe_set_eq] at h5
    omega
  have hvp : v ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    ⟨hP.typeL.smul_eq, smul_eq_of_mem_p46Orbit hβ⟩
  have hvΔ := stabilizer_pair_le (G := G) α β hvp
  rw [mem_stabilizer_iff] at hvΔ
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  have hw2 : w * w = 1 := mul_self_eq_one_of_mem_longInv hw.1
  have hwv2 : (w * v) * (w * v) = 1 := mul_self_eq_one_of_mem_longInv hwvJ
  have hfixw : ∀ ω, w • ω = ω → ω = γ := fun ω h => by
    obtain ⟨c, -, hcu⟩ := hw.1.2
    exact (hcu ω h).trans (hcu γ hwγ).symm
  have hfixwv : ∀ ω, (w * v) • ω = ω → ω = γ := fun ω h => by
    obtain ⟨c, -, hcu⟩ := hwvJ.2
    exact (hcu ω h).trans (hcu γ (show (w * v) • γ = γ by rw [mul_smul, hvγ, hwγ])).symm
  have hfixv : ∀ ω ∈ holtDelta G Ω α β, v • ω = ω → ω = γ := fun ω hω h => huniq ω ⟨hω, h⟩
  have hwp : w ∈ stabilizer G ({α, β} : Set Ω) := by
    rw [mem_stabilizer_iff]
    have hwβ : w • β = α := by rw [← hwα, smul_smul, hw2, one_smul]
    rw [Set.smul_set_insert, Set.smul_set_singleton, hwα, hwβ, Set.pair_comm]
  have hwΔ := stabilizer_pair_le (G := G) α β hwp
  rw [mem_stabilizer_iff] at hwΔ
  have hcomm : w * v = v * w := hwv.eq
  set O : Set Ω := {δ, v • δ, w • δ, (w * v) • δ} with hOdef
  have hvδ : v • δ ∈ holtDelta G Ω α β := hvΔ ▸ Set.smul_mem_smul_set hδΔ
  have hwδ : w • δ ∈ holtDelta G Ω α β := hwΔ ▸ Set.smul_mem_smul_set hδΔ
  have hwvδ : (w * v) • δ ∈ holtDelta G Ω α β := by
    rw [mul_smul]; exact hwΔ ▸ Set.smul_mem_smul_set hvδ
  have hvδγ : v • δ ≠ γ := fun h => hδγ (by rw [← one_smul G δ, ← hv2, mul_smul, h, hvγ])
  have hwδγ : w • δ ≠ γ := fun h => hδγ (by rw [← one_smul G δ, ← hw2, mul_smul, h, hwγ])
  have hwvδγ : (w * v) • δ ≠ γ := fun h => hδγ (by
    rw [← one_smul G δ, ← hwv2, mul_smul, h, mul_smul, hvγ, hwγ])
  have d1 : δ ≠ v • δ := fun h => hδγ (hfixv δ hδΔ h.symm)
  have d2 : δ ≠ w • δ := fun h => hδγ (hfixw δ h.symm)
  have d3 : δ ≠ (w * v) • δ := fun h => hδγ (hfixwv δ h.symm)
  have d4 : v • δ ≠ w • δ := fun h => d3 (by rw [mul_smul, h, ← mul_smul, hw2, one_smul])
  have d5 : v • δ ≠ (w * v) • δ := fun h => hvδγ (hfixw _ (by rw [← mul_smul]; exact h.symm))
  have d6 : w • δ ≠ (w * v) • δ := fun h => d1 (by
    rw [mul_smul] at h
    exact smul_left_cancel w h)
  have hO4 : O.ncard = 4 := by
    rw [hOdef, Set.ncard_insert_of_notMem (by simp [d1, d2, d3]),
      Set.ncard_insert_of_notMem (by simp [d4, d5]), Set.ncard_insert_of_notMem (by simp [d6]),
      Set.ncard_singleton]
  have hγO : γ ∉ O := by
    simp only [hOdef, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hδγ, Ne.symm hvδγ, Ne.symm hwδγ, Ne.symm hwvδγ⟩
  have hOΔ : O ⊆ holtDelta G Ω α β := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact hδΔ
    · exact hvδ
    · exact hwδ
    · exact hwvδ
  have hvO : v • O = O := by
    refine Set.eq_of_subset_of_ncard_le ?_ (by rw [Set.ncard_smul_set]) (Set.toFinite _)
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl <;> beta_reduce
    · exact Or.inr (Or.inl rfl)
    · rw [smul_smul, hv2, one_smul]; exact Or.inl rfl
    · rw [smul_smul, ← hcomm]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [smul_smul, ← mul_assoc, ← hcomm, mul_assoc, hv2, mul_one]
      exact Or.inr (Or.inr (Or.inl rfl))
  have hwO : w • O = O := by
    refine Set.eq_of_subset_of_ncard_le ?_ (by rw [Set.ncard_smul_set]) (Set.toFinite _)
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl <;> beta_reduce
    · exact Or.inr (Or.inr (Or.inl rfl))
    · rw [smul_smul]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [smul_smul, hw2, one_smul]; exact Or.inl rfl
    · rw [smul_smul, ← mul_assoc, hw2, one_mul]; exact Or.inr (Or.inl rfl)
  exact ⟨mk _ (Or.inr (Or.inr ⟨hι1, hT, O, hOΔ, hγO, hO4, hvO, hwO, rfl⟩)), rfl⟩

theorem two_le_card_of_isPGroup {K : Subgroup G} (hK : IsPGroup 2 K) (hK1 : K ≠ ⊥) :
    2 ≤ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hK1 (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
  rw [hn]
  exact le_self_pow₀ (by norm_num) hn0

theorem CaseAStart.four_le_of_kind_a_even (X : CaseAStart G Ω α v P) (hS : Sec4Setting G Ω)
    (hP : Prop46Setup G Ω α v P) (h2 : 2 ≤ Fintype.card X.A.D.ι) {i₀ : X.A.D.ι}
    (hΛ : X.Λ = (↑) '' {δ : holtDelta G Ω α X.β | ∀ j, j ≠ i₀ →
      X.A.D.coord δ j = X.A.D.coord X.γ j})
    (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α X.β))) :
    ∃ V : Subgroup G, V ≤ caseACentralizer G Ω α X.β v X.Λ ∧ IsPGroup 2 V ∧ 3 ≤ Nat.card V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV, -⟩ := X.exists_sylow_le_normalizer (T := ⊥) IsPGroup.of_bot bot_le
  obtain ⟨hV1, hVΛ⟩ := X.lemma_3_1 hS hP hV
  refine ⟨V, hV.1, hV.2.1, ?_⟩
  by_contra hlt
  set 𝒞Δ := caseACentralizer G Ω α X.β v (holtDelta G Ω α X.β)
  have hΛΔ := X.Λ_subset_and_γ_mem.1
  have h𝒞le : 𝒞Δ ≤ caseACentralizer G Ω α X.β v X.Λ := fun g hg =>
    ⟨(Subgroup.mem_inf.mp hg).1, (mem_fixingSubgroup_iff G).mpr fun δ hδ =>
      (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp hg).2 δ (hΛΔ hδ)⟩
  have hnorm : (𝒞Δ.subgroupOf (caseACentralizer G Ω α X.β v X.Λ)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgΔ := X.caseACentralizer_le_stabilizer X.Λ g.2
    rw [mem_stabilizer_iff] at hgΔ
    set K₁ : Subgroup G := Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ⊓
      (stabilizer G α ⊓ stabilizer G X.β)
    have hgK : (g : G) ∈ K₁ := (Subgroup.mem_inf.mp g.2).1
    have hnK : (n : G) ∈ K₁ := (Subgroup.mem_inf.mp hn).1
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hgK hnK) (inv_mem hgK), ?_⟩
    refine (mem_fixingSubgroup_iff G).mpr fun δ hδ => ?_
    have hδ' : (g : G)⁻¹ • δ ∈ holtDelta G Ω α X.β := by
      rw [← hgΔ] at hδ
      obtain ⟨δ', hδ', rfl⟩ := hδ
      rwa [inv_smul_smul]
    show ((g : G) * (n : G) * (g : G)⁻¹) • δ = δ
    rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp hn).2 _ hδ',
      smul_inv_smul]
  have hVΔ := fusionIsSylowIn_inf_of_normal_subgroupOf hV h𝒞le hnorm
  obtain ⟨E₀, hE₀2, hE₀𝒞, hE₀1⟩ := X.exists_isPGroup_le_caseACentralizer_holtDelta hP hT
  have h2V' : 2 ≤ Nat.card ↥(V ⊓ 𝒞Δ) :=
    (two_le_card_of_isPGroup hE₀2 hE₀1).trans (card_le_of_fusionIsSylowIn hVΔ hE₀2 hE₀𝒞)
  have hV2 : Nat.card V ≤ 2 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV.2.1
    rw [hn] at hlt ⊢
    rcases n with _ | _ | n
    · norm_num
    · norm_num
    · exfalso
      exact hlt (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega :
        2 ≤ n + 2)))
  have heq : V ⊓ 𝒞Δ = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card X.A.D.ι) i₀
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card
    (by have := X.A.D.five_le_card j; omega : 1 < Fintype.card (X.A.D.Ψc j))
    (X.A.D.coord X.γ j)
  obtain ⟨δ, hδ⟩ := X.A.D.coord_surjective (Function.update (X.A.D.coord X.γ) j y)
  have hδV : (δ : Ω) ∈ fixSet Ω V := fun g hg => by
    have hg' : g ∈ V ⊓ 𝒞Δ := by rw [heq]; exact hg
    exact (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg').2).2 δ δ.2
  have hδΛ : (δ : Ω) ∈ X.Λ := by rw [← hVΛ]; exact ⟨δ.2, hδV⟩
  rw [hΛ] at hδΛ
  obtain ⟨δ', hδ', hδ'δ⟩ := hδΛ
  have := hδ' j hj
  rw [show δ' = δ from Subtype.ext hδ'δ, hδ, Function.update_self] at this
  exact hy this

omit [FaithfulSMul G Ω] in
theorem CaseAStart.four_le_of_kind_c (X : CaseAStart G Ω α v P) (hP : Prop46Setup G Ω α v P)
    (h1 : Fintype.card X.A.D.ι = 1) (hodd : Odd (Nat.card (twoPointKernel G Ω α X.β)))
    {O : Set Ω} (hγO : (X.γ : Ω) ∉ O) (hO4 : O.ncard = 4) (hvO : v • O = O)
    (hΛ : X.Λ = insert (X.γ : Ω) O) :
    ∃ V : Subgroup G, V ≤ caseACentralizer G Ω α X.β v X.Λ ∧ IsPGroup 2 V ∧ 3 ≤ Nat.card V := by
  classical
  obtain ⟨i₁⟩ : Nonempty X.A.D.ι := Fintype.card_pos_iff.mp (by omega)
  have hcardΔ : Fintype.card (holtDelta G Ω α X.β) = Fintype.card (X.A.D.Ψc i₁) :=
    Fintype.card_of_bijective (X.A.coord_bijective_of_card_eq_one h1 i₁)
  have h9 : 9 ≤ Fintype.card (holtDelta G Ω α X.β) := by
    have h5 := X.A.D.five_le_card i₁
    have hne : Fintype.card (X.A.D.Ψc i₁) ≠ 5 := fun h => X.A.five h1 i₁ h hodd
    have hmod := X.A.mod4 i₁
    omega
  have hΛ5 : X.Λ.ncard = 5 := by rw [hΛ, Set.ncard_insert_of_notMem hγO, hO4]
  have hvΛ : ∀ δ : Ω, v • δ ∈ X.Λ ↔ δ ∈ X.Λ := fun δ => by
    have e1 : v • δ = (X.γ : Ω) ↔ δ = X.γ := ⟨fun h => by
      rw [← X.v_fix] at h; exact smul_left_cancel v h, fun h => by rw [h, X.v_fix]⟩
    have e2 : v • δ ∈ O ↔ δ ∈ O := by
      conv_lhs => rw [← hvO]
      exact Set.smul_mem_smul_set_iff
    rw [hΛ, Set.mem_insert_iff, Set.mem_insert_iff, e1, e2]
  have hΛΔ := X.Λ_subset_and_γ_mem.1
  have hγΛ := X.Λ_subset_and_γ_mem.2
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  set vP : Equiv.Perm (holtDelta G Ω α X.β) :=
    ((twoPointElt (X.v_mem_pair hP) : twoPointSection G Ω α X.β) :
      Equiv.Perm (holtDelta G Ω α X.β)) with hvPdef
  have hvP : ∀ δ : holtDelta G Ω α X.β, (vP δ : Ω) = v • (δ : Ω) := fun _ => rfl
  have hvP2 : vP * vP = 1 := Equiv.ext fun δ => Subtype.ext (by
    rw [Equiv.Perm.mul_apply, hvP, hvP, Equiv.Perm.one_apply, ← mul_smul, hv2, one_smul])
  set M : Finset (holtDelta G Ω α X.β) := Finset.univ.filter fun δ => (δ : Ω) ∉ X.Λ with hMdef
  have hM : ∀ x ∈ M, vP x ≠ x := fun x hx h => by
    simp only [hMdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply hx
    rw [X.eq_γ_of_smul_eq hP x.2 (by rw [← hvP, h])]
    exact hγΛ
  have hMg : ∀ x ∈ M, vP x ∈ M := fun x hx => by
    simp only [hMdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hvP, hvΛ]
    exact hx
  have hM4 : 4 ≤ M.card := by
    have h1 : Fintype.card {δ : holtDelta G Ω α X.β // (δ : Ω) ∈ X.Λ} = 5 := by
      rw [← hΛ5, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      exact Fintype.card_congr
        { toFun := fun x => ⟨x.1.1, x.2⟩, invFun := fun y => ⟨⟨y.1, hΛΔ y.2⟩, y.2⟩,
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have h2 := Fintype.card_subtype_compl (fun δ : holtDelta G Ω α X.β => (δ : Ω) ∈ X.Λ)
    rw [h1] at h2
    have h3 : M.card = Fintype.card {δ : holtDelta G Ω α X.β // ¬ (δ : Ω) ∈ X.Λ} :=
      (Fintype.card_subtype _).symm
    rw [h3, h2]
    omega
  obtain ⟨σ₁, σ₂, hσ₁A, hσ₂A, hσ₁1, hσ₂1, hσ₁₂, hσ₁2, hσ₂2, hσc, hσ₁v, hσ₂v, hσM⟩ :=
    exists_four_group hvP2 hM hMg hM4
  obtain ⟨hĒ2, hĒ4⟩ := four_le_card_closure hσ₁2 hσ₂2 hσc hσ₁1 hσ₂1 hσ₁₂
  have hAG : ∀ σ ∈ alternatingGroup (holtDelta G Ω α X.β),
      σ ∈ ⁅twoPointSection G Ω α X.β, twoPointSection G Ω α X.β⁆ := fun σ hσ => by
    have h5 : 5 ≤ Nat.card (holtDelta G Ω α X.β) := by rw [Nat.card_eq_fintype_card]; omega
    rw [← commutator_alternatingGroup_eq_self h5] at hσ
    exact Subgroup.commutator_mono (X.A.alternatingGroup_le_twoPointSection h1)
      (X.A.alternatingGroup_le_twoPointSection h1) hσ
  have hnotM : ∀ δ : holtDelta G Ω α X.β, (δ : Ω) ∈ X.Λ → δ ∉ M := fun δ hδ h => by
    simp only [hMdef, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h hδ
  obtain ⟨E, hE2, hE𝒞, hEcard⟩ := X.exists_lift_of_odd hP hodd (S := {σ₁, σ₂})
    (by rintro σ (rfl | rfl); exacts [hAG _ hσ₁A, hAG _ hσ₂A])
    (by
      rintro σ (rfl | rfl)
      · exact (hσM _ (hnotM _ hγΛ)).1
      · exact (hσM _ (hnotM _ hγΛ)).2)
    (by rintro σ (rfl | rfl); exacts [hσ₁v, hσ₂v]) hĒ2 hΛΔ
    (by
      rintro σ (rfl | rfl) δ hδ
      · exact (hσM δ (hnotM δ hδ)).1
      · exact (hσM δ (hnotM δ hδ)).2)
  exact ⟨E, hE𝒞, hE2, by omega⟩

omit [FaithfulSMul G Ω] in
theorem CaseAStart.four_le_of_kind_a_odd (X : CaseAStart G Ω α v P) (hS : Sec4Setting G Ω)
    (hP : Prop46Setup G Ω α v P) (h2 : 2 ≤ Fintype.card X.A.D.ι) {i₀ : X.A.D.ι}
    (hΛ : X.Λ = (↑) '' {δ : holtDelta G Ω α X.β | ∀ j, j ≠ i₀ →
      X.A.D.coord δ j = X.A.D.coord X.γ j})
    (hodd : Odd (Nat.card (twoPointKernel G Ω α X.β))) :
    ∃ V : Subgroup G, V ≤ caseACentralizer G Ω α X.β v X.Λ ∧ IsPGroup 2 V ∧ 3 ≤ Nat.card V := by
  classical
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card X.A.D.ι) i₀
  obtain ⟨hvc, hvfix⟩ := X.coord_v hS hP
  set vΔ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β) :=
    ⟨_, X.A.D.socPre_le_jHull (X.vDelta_mem_socPre hS hP)⟩ with hvΔdef
  set g := X.A.D.ρ j vΔ with hgdef
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  have hvΔ2 : vΔ * vΔ = 1 := Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
    show v • v • (δ : Ω) = δ
    rw [← mul_smul, hv2, one_smul])))
  have hg2 : g * g = 1 := by rw [hgdef, ← map_mul, hvΔ2, map_one]
  have hgγ : g (X.A.D.coord X.γ j) = X.A.D.coord X.γ j := by
    have e₀ : (⟨v • (X.γ : Ω), X.smul_mem_holtDelta (X.v_mem_pair hP) X.γ.2⟩ :
        holtDelta G Ω α X.β) = X.γ := Subtype.ext X.v_fix
    rw [hgdef, ← hvc X.γ j, e₀]
  set M : Finset (X.A.D.Ψc j) := Finset.univ.filter (· ≠ X.A.D.coord X.γ j) with hMdef
  have hM : ∀ x ∈ M, g x ≠ x := fun x hx h => by
    simp only [hMdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx (hvfix j x h)
  have hMg : ∀ x ∈ M, g x ∈ M := fun x hx => by
    simp only [hMdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro h
    apply hx
    rw [← hgγ, ← h, ← Equiv.Perm.mul_apply, hg2, Equiv.Perm.one_apply]
  have hM4 : 4 ≤ M.card := by
    have h5 := X.A.D.five_le_card j
    have : M.card = Fintype.card (X.A.D.Ψc j) - 1 := by
      rw [hMdef, Finset.filter_ne' Finset.univ (X.A.D.coord X.γ j),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨σ₁, σ₂, hσ₁A, hσ₂A, hσ₁1, hσ₂1, hσ₁₂, hσ₁2, hσ₂2, hσc, hσ₁v, hσ₂v, hσM⟩ :=
    exists_four_group hg2 hM hMg hM4
  have hMj := X.A.alt j
  have hMj' : X.A.D.M j = alternatingGroup (X.A.D.Ψc j) := hMj
  obtain ⟨ℓ₁, hℓ₁G, hℓ₁j, hℓ₁o⟩ := X.A.exists_commElt j (m := σ₁) (by rw [hMj']; exact hσ₁A)
  obtain ⟨ℓ₂, hℓ₂G, hℓ₂j, hℓ₂o⟩ := X.A.exists_commElt j (m := σ₂) (by rw [hMj']; exact hσ₂A)
  set τ₁ := ((ℓ₁ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β))
  set τ₂ := ((ℓ₂ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β))
  have hc : ∀ (ℓ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β))
      (δ : holtDelta G Ω α X.β) (k : X.A.D.ι),
      X.A.D.coord (((ℓ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) δ) k =
        X.A.D.ρ k ℓ (X.A.D.coord δ k) := fun ℓ δ k => X.A.D.coord_smul ℓ δ k
  have hext : ∀ π₁ π₂ : Equiv.Perm (holtDelta G Ω α X.β),
      (∀ δ k, X.A.D.coord (π₁ δ) k = X.A.D.coord (π₂ δ) k) → π₁ = π₂ := fun π₁ π₂ h =>
    Equiv.ext fun δ => X.A.coord_injective (funext (h δ))
  have hτj : ∀ {ℓ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β)}
      {σ : Equiv.Perm (X.A.D.Ψc j)}, X.A.D.ρ j ℓ = σ → ∀ δ, X.A.D.coord
        (((ℓ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) δ) j =
          σ (X.A.D.coord δ j) := fun hℓ δ => by rw [hc, hℓ]
  have hτo : ∀ {ℓ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β)},
      (∀ k, k ≠ j → X.A.D.ρ k ℓ = 1) → ∀ δ k, k ≠ j → X.A.D.coord
        (((ℓ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) δ) k =
          X.A.D.coord δ k := fun hℓ δ k hk => by rw [hc, hℓ k hk, Equiv.Perm.one_apply]
  have hγM : X.A.D.coord X.γ j ∉ M := by simp [hMdef]
  set vP : Equiv.Perm (holtDelta G Ω α X.β) :=
    ((twoPointElt (X.v_mem_pair hP) : twoPointSection G Ω α X.β) :
      Equiv.Perm (holtDelta G Ω α X.β)) with hvPdef
  have hvP : ∀ δ k, X.A.D.coord (vP δ) k = X.A.D.ρ k vΔ (X.A.D.coord δ k) := hvc
  have hsq : ∀ {ℓ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β)}
      {σ : Equiv.Perm (X.A.D.Ψc j)}, X.A.D.ρ j ℓ = σ → σ * σ = 1 →
      (∀ k, k ≠ j → X.A.D.ρ k ℓ = 1) →
      ((ℓ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) *
        ((ℓ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) = 1 :=
    fun hℓ hσ ho => hext _ _ fun δ k => by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      by_cases hk : k = j
      · subst hk
        rw [hτj hℓ, hτj hℓ, ← Equiv.Perm.mul_apply, hσ, Equiv.Perm.one_apply]
      · rw [hτo ho _ k hk, hτo ho _ k hk]
  have hτc : Commute τ₁ τ₂ := hext _ _ fun δ k => by
    simp only [Equiv.Perm.mul_apply]
    by_cases hk : k = j
    · subst hk
      rw [hτj hℓ₁j, hτj hℓ₂j, hτj hℓ₂j, hτj hℓ₁j, ← Equiv.Perm.mul_apply, hσc.eq,
        Equiv.Perm.mul_apply]
    · rw [hτo hℓ₁o _ k hk, hτo hℓ₂o _ k hk, hτo hℓ₂o _ k hk, hτo hℓ₁o _ k hk]
  have hne : ∀ {ℓ ℓ' : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β)}
      {σ σ' : Equiv.Perm (X.A.D.Ψc j)}, X.A.D.ρ j ℓ = σ → X.A.D.ρ j ℓ' = σ' → σ ≠ σ' →
      ((ℓ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) ≠
        ((ℓ' : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) :=
    fun hℓ hℓ' hσσ' h => hσσ' (Equiv.ext fun x => by
      obtain ⟨δ, hδ⟩ := X.A.D.exists_coord_apply_eq j x
      rw [← hδ, ← hτj hℓ, ← hτj hℓ', h])
  have hτ₁1 : τ₁ ≠ 1 := fun h => hne hℓ₁j (map_one (X.A.D.ρ j)) hσ₁1 (h.trans rfl)
  have hτ₂1 : τ₂ ≠ 1 := fun h => hne hℓ₂j (map_one (X.A.D.ρ j)) hσ₂1 (h.trans rfl)
  obtain ⟨hĒ2, hĒ4⟩ := four_le_card_closure (hsq hℓ₁j hσ₁2 hℓ₁o) (hsq hℓ₂j hσ₂2 hℓ₂o) hτc
    hτ₁1 hτ₂1 (hne hℓ₁j hℓ₂j hσ₁₂)
  have hfixγ : ∀ {ℓ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β)}
      {σ : Equiv.Perm (X.A.D.Ψc j)}, X.A.D.ρ j ℓ = σ → (∀ x, x ∉ M → σ x = x) →
      (∀ k, k ≠ j → X.A.D.ρ k ℓ = 1) → ∀ δ : holtDelta G Ω α X.β,
        X.A.D.coord δ j = X.A.D.coord X.γ j →
          ((ℓ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) δ = δ :=
    fun hℓ hσ ho δ hδ => X.A.coord_injective (funext fun k => by
      by_cases hk : k = j
      · subst hk
        rw [hτj hℓ, hδ, hσ _ hγM]
      · rw [hτo ho _ k hk])
  have hcomv : ∀ {ℓ : jHull (twoPointSection G Ω α X.β) (holtDelta G Ω α X.β)}
      {σ : Equiv.Perm (X.A.D.Ψc j)}, X.A.D.ρ j ℓ = σ → Commute σ g →
      (∀ k, k ≠ j → X.A.D.ρ k ℓ = 1) →
      Commute ((ℓ : twoPointSection G Ω α X.β) : Equiv.Perm (holtDelta G Ω α X.β)) vP :=
    fun hℓ hσ ho => hext _ _ fun δ k => by
      simp only [Equiv.Perm.mul_apply]
      by_cases hk : k = j
      · subst hk
        rw [hτj hℓ, hvP, hvP, hτj hℓ, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, hσ.eq]
      · rw [hτo ho _ k hk, hvP, hvP, hτo ho _ k hk]
  have hΛΔ := X.Λ_subset_and_γ_mem.1
  have hΛj : ∀ δ : holtDelta G Ω α X.β, (δ : Ω) ∈ X.Λ →
      X.A.D.coord δ j = X.A.D.coord X.γ j := fun δ hδ => by
    rw [hΛ] at hδ
    obtain ⟨δ', hδ', hδ'δ⟩ := hδ
    rw [← show δ' = δ from Subtype.ext hδ'δ]
    exact hδ' j hj
  obtain ⟨E, hE2, hE𝒞, hEcard⟩ := X.exists_lift_of_odd hP hodd (S := {τ₁, τ₂})
    (by rintro σ (rfl | rfl); exacts [hℓ₁G, hℓ₂G])
    (by
      rintro σ (rfl | rfl)
      · exact hfixγ hℓ₁j (fun x hx => (hσM x hx).1) hℓ₁o X.γ rfl
      · exact hfixγ hℓ₂j (fun x hx => (hσM x hx).2) hℓ₂o X.γ rfl)
    (by
      rintro σ (rfl | rfl)
      · exact hcomv hℓ₁j hσ₁v hℓ₁o
      · exact hcomv hℓ₂j hσ₂v hℓ₂o) hĒ2 hΛΔ
    (by
      rintro σ (rfl | rfl) δ hδ
      · exact hfixγ hℓ₁j (fun x hx => (hσM x hx).1) hℓ₁o δ (hΛj δ hδ)
      · exact hfixγ hℓ₂j (fun x hx => (hσM x hx).2) hℓ₂o δ (hΛj δ hδ))
  exact ⟨E, hE𝒞, hE2, le_trans (by norm_num) (hĒ4.trans hEcard)⟩

theorem CaseAStart.kind_b (X : CaseAStart G Ω α v P) (hS : Sec4Setting G Ω)
    (hP : Prop46Setup G Ω α v P)
    (hrig : ∀ V' : Subgroup G, V' ≤ caseACentralizer G Ω α X.β v X.Λ → IsPGroup 2 V' →
      Nat.card V' ≤ 2) :
    Fintype.card X.A.D.ι = 1 ∧ ¬ Odd (Nat.card (twoPointKernel G Ω α X.β)) ∧
      X.Λ = holtDelta G Ω α X.β := by
  rcases X.admissible with ⟨h2, i₀, hΛ⟩ | ⟨h1, hT, hΛ⟩ | ⟨h1, hodd, O, -, hγO, hO4, hvO, -, hΛ⟩
  · exfalso
    by_cases hodd : Odd (Nat.card (twoPointKernel G Ω α X.β))
    · obtain ⟨V, hV, hV2, h3⟩ := X.four_le_of_kind_a_odd hS hP h2 hΛ hodd
      have := hrig V hV hV2
      omega
    · obtain ⟨V, hV, hV2, h3⟩ := X.four_le_of_kind_a_even hS hP h2 hΛ hodd
      have := hrig V hV hV2
      omega
  · exact ⟨h1, hT, hΛ⟩
  · exfalso
    obtain ⟨V, hV, hV2, h3⟩ := X.four_le_of_kind_c hP h1 hodd hγO hO4 hvO hΛ
    have := hrig V hV hV2
    omega

theorem Sec4Setting.caseA (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (h43 : ∀ a b : Ω, a ≠ b → IsEmpty (AltConfig G Ω a b)) (hD : CaseAStepA7 G Ω α v P)
    (hU4 : ∀ β ∈ p46Orbit G Ω v P α, β ≠ α → IsTypeBAt G Ω α β →
      Nat.card (holtDelta G Ω α β) ≠ 5 →
        IsBenderAction ↥(twoPointJ G Ω α β) (holtDelta G Ω α β) 2 3 5)
    (X₀ : CaseAStart G Ω α v P) :
    (∀ X : CaseAStart G Ω α v P, X.Λ.ncard = 5 ∧
      (∀ V' : Subgroup G, V' ≤ caseACentralizer G Ω α X.β v X.Λ → IsPGroup 2 V' →
        Nat.card V' ≤ 2) ∧
      Fintype.card X.A.D.ι = 1 ∧ ¬ Odd (Nat.card (twoPointKernel G Ω α X.β)) ∧
      X.Λ = holtDelta G Ω α X.β) ∧
    ∀ (X : CaseAStart G Ω α v P) (V : Subgroup G) (τ : G),
      fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ) →
      X.w ∈ Subgroup.normalizer (V : Set G) → IsPGroup 2 (Subgroup.zpowers τ) →
      τ ∈ Subgroup.normalizer (V : Set G) → Commute τ v → τ • α = α → τ • X.β = X.β →
      ∃ (r : G) (β₁ γ₁ : Ω), IsCaseAOutput X V r β₁ γ₁ ∧ τ • β₁ = β₁ ∧
        IsTypeBAt G Ω α β₁ ∧ Nat.card (holtDelta G Ω α β₁) ≠ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Xm, Vm, hVm, hwVm, hκm⟩ := exists_isKappaMaximal hS hP X₀
  obtain ⟨r, β₁, γ₁, hout, hB, h5⟩ := hS.caseA_typeB hP h43 hD Xm hVm hwVm hκm
  obtain ⟨hVm2, hΛm⟩ := hout.rigid hVm.2.1 (Xm.lemma_3_1 hS hP hVm).1 hB
    (hU4 β₁ hout.mem_β₁ hout.ne hB h5)
  have hrigid : ∀ X : CaseAStart G Ω α v P, X.Λ.ncard = 5 ∧
      ∀ V' : Subgroup G, V' ≤ caseACentralizer G Ω α X.β v X.Λ → IsPGroup 2 V' →
        Nat.card V' ≤ 2 := by
    intro X
    have h1 := X.ncard_Λ.2
    have hX5 : X.Λ.ncard = 5 := by
      rcases hκm X ⊥ bot_le IsPGroup.of_bot with h | ⟨h, -⟩ <;> omega
    refine ⟨hX5, fun V' hV' hV'2 => ?_⟩
    rcases hκm X V' hV' hV'2 with h | ⟨-, h⟩
    · omega
    · omega
  refine ⟨fun X => ⟨(hrigid X).1, (hrigid X).2, X.kind_b hS hP (hrigid X).2⟩,
    fun X V τ hV hwV hτ2 hτV hτv hτα hτβ => ?_⟩
  have hV1 := (X.lemma_3_1 hS hP hV).1
  have hV2 : 2 ≤ Nat.card V := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV.2.1
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hV1 (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
    rw [hn]
    exact le_self_pow₀ (by norm_num) hn0 |>.trans' le_rfl
  have hκ : IsKappaMaximal X V := fun X' V' hV' hV'2 =>
    Or.inr ⟨by rw [(hrigid X').1, (hrigid X).1], ((hrigid X').2 V' hV' hV'2).trans hV2⟩
  obtain ⟨S⟩ := X.exists_section hS hP hV hwV hτ2 hτV hτv
  obtain ⟨r', β₁', γ₁', hout', hτβ₁⟩ := S.exists_output_fix_τ hS hP hτα hτβ
  obtain ⟨hB', h5'⟩ := hS.typeB_of_caseA_output hP h43 hD X hV hwV hκ hV1 hout'.two hout'.mem_V
    hout'.comm hout'.fix_α hout'.fixSet_eq hout'.mem_β₁ hout'.ne hout'.mem_γ₁ hout'.γ₁_mem
    hout'.v_γ₁ (X.ncard_Λ.2.trans hout'.ncard_le) hout'.orbit
  exact ⟨r', β₁', γ₁', hout', hτβ₁, hB', h5'⟩

end Main

section Certified

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

theorem Prop46Setup.isBenderAction_of_typeB (hS : Sec4Setting G Ω)
    (hP : Prop46Setup G Ω α v P) {β : Ω} (hβ : β ∈ p46Orbit G Ω v P α) (hβα : β ≠ α)
    (hB : IsTypeBAt G Ω α β) (h5 : Nat.card (holtDelta G Ω α β) ≠ 5) :
    IsBenderAction ↥(twoPointJ G Ω α β) (holtDelta G Ω α β) 2 3 5 := by
  obtain ⟨γ, hC⟩ := hP.exists_caseB hβ hβα hB
  exact hB.1.isBenderAction_unitary_four (hC.card_rootCenter_eq_four hS) h5

theorem Sec4Setting.caseA_of_certificates (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (h43 : ∀ a b : Ω, a ≠ b → IsEmpty (AltConfig G Ω a b)) (hD : CaseAStepA7 G Ω α v P)
    (X₀ : CaseAStart G Ω α v P) :
    (∀ X : CaseAStart G Ω α v P, X.Λ.ncard = 5 ∧
      (∀ V' : Subgroup G, V' ≤ caseACentralizer G Ω α X.β v X.Λ → IsPGroup 2 V' →
        Nat.card V' ≤ 2) ∧
      Fintype.card X.A.D.ι = 1 ∧ ¬ Odd (Nat.card (twoPointKernel G Ω α X.β)) ∧
      X.Λ = holtDelta G Ω α X.β) ∧
    ∀ (X : CaseAStart G Ω α v P) (V : Subgroup G) (τ : G),
      fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ) →
      X.w ∈ Subgroup.normalizer (V : Set G) → IsPGroup 2 (Subgroup.zpowers τ) →
      τ ∈ Subgroup.normalizer (V : Set G) → Commute τ v → τ • α = α → τ • X.β = X.β →
      ∃ (r : G) (β₁ γ₁ : Ω), IsCaseAOutput X V r β₁ γ₁ ∧ τ • β₁ = β₁ ∧
        IsTypeBAt G Ω α β₁ ∧ Nat.card (holtDelta G Ω α β₁) ≠ 5 :=
  hS.caseA hP h43 hD (fun _ hβ hβα hB h5 => hP.isBenderAction_of_typeB hS hβ hβα hB h5) X₀

end Certified

end CFSG.Holt.H78
