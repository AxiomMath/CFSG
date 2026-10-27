module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartTheta
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartRoot
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartEmb
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartCase

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv CFSG.OddStandard.AltStdBal

section Near

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem mk_ne_of_partner (d : Cyc L Q z) {R : Subgroup G} {a : G} (ha : a ∈ centralizer ({z} : Set G))
    (haz : a ≠ z) (haa : a * a = 1) (hzR : z ∈ centralizer (R : Set G))
    (haR : a ∈ centralizer (R : Set G)) :
    (QuotientGroup.mk ⟨a, haR⟩ : Sec G R) ≠ QuotientGroup.mk ⟨z, hzR⟩ := by
  intro heq
  have hmem := QuotientGroup.eq.1 heq
  have hodd := orderOf_odd_of_mem_oddCore hmem
  rw [Subgroup.orderOf_mk] at hodd
  change Odd (orderOf (a⁻¹ * z)) at hodd
  have hz2 : z * z = 1 := d.mul_self
  have hcomm : a * z = z * a := mem_centralizer_singleton_iff.1 ha
  have hw2 : (a⁻¹ * z) * (a⁻¹ * z) = 1 := by
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    rw [ha']
    calc a * z * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [← hcomm]
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [haa, hz2, one_mul]
  have hdvd : orderOf (a⁻¹ * z) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
  have h1 : orderOf (a⁻¹ * z) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd; exact absurd hodd (by decide)
  have h2 : a⁻¹ * z = 1 := orderOf_eq_one_iff.1 h1
  exact haz (inv_mul_eq_one.1 h2)

theorem eq_swapIota_or (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G)) :
    x = (swapIota h d T e (permOf h d e hx) : G) ∨
      x = z * (swapIota h d T e (permOf h d e hx) : G) := by
  set s : G := (swapIota h d T e (permOf h d e hx) : G) with hs
  have hsC : s ∈ centralizer ({z} : Set G) := swapIota_mem_centralizer h d T e _
  have hps : permOf h d e hsC = permOf h d e hx := permOf_swapIota h d T e _
  have hinv : s⁻¹ ∈ centralizer ({z} : Set G) := inv_mem hsC
  have hxs : x * s⁻¹ ∈ centralizer ({z} : Set G) := mul_mem hx hinv
  have hp1 : permOf h d e hxs = 1 := by
    rw [permOf_mul h d e hx hinv hxs, permOf_inv h d e hsC hinv, hps, mul_inv_cancel]
  have hK : x * s⁻¹ ∈ centralizer (L : Set G) :=
    (rho_eq_one_iff e h.hn ⟨x * s⁻¹, AltStdBal.centralizer_le_normalizer h d hxs⟩).1 hp1
  have hQ : x * s⁻¹ ∈ Q := by
    rw [← cent_inf_eq h d]
    exact Subgroup.mem_inf.2 ⟨hK, hxs⟩
  rcases eq_one_or_eq_of_card_eq_two d T.card hQ with h1 | h1
  · exact Or.inl (mul_inv_eq_one.1 h1)
  · right
    rw [← h1]
    group

theorem eq_one_of_forall_commute {α : Type*} [DecidableEq α] [Fintype α]
    (h3 : 3 ≤ Fintype.card α) {σ : Perm α} (hσ : ∀ π : Perm α, σ * π = π * σ) : σ = 1 := by
  ext x
  have key : ∀ y, y ≠ x → σ x = x ∨ σ x = y := by
    intro y hyx
    have h1 := congrArg (fun f : Perm α => f x) (hσ (swap x y))
    simp only [Perm.mul_apply, swap_apply_left] at h1
    by_contra hcon
    push Not at hcon
    rw [swap_apply_of_ne_of_ne hcon.1 hcon.2] at h1
    exact hyx (σ.injective h1)
  have hcard : 2 ≤ ((Finset.univ.erase x).card) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    omega
  obtain ⟨y, hy, w, hw, hyw⟩ := Finset.one_lt_card.1 hcard
  have hyx : y ≠ x := Finset.ne_of_mem_erase hy
  have hwx : w ≠ x := Finset.ne_of_mem_erase hw
  rcases key y hyx with h | h
  · simpa using h
  rcases key w hwx with h' | h'
  · simpa using h'
  exact absurd (h.symm.trans h') hyw

theorem exists_ofSubtype_eq {S : Finset (Fin n)} {f : Perm (Fin n)} (hfS : ∀ i ∈ S, f i = i) :
    ∃ σ : Perm ↥Sᶜ, Perm.ofSubtype σ = f := by
  have h₁ : ∀ x, (f x ∈ Sᶜ) ↔ x ∈ Sᶜ := by
    intro x
    simp only [Finset.mem_compl]
    constructor
    · intro hfx hx
      exact hfx (by rw [hfS x hx]; exact hx)
    · intro hx hfx
      have : f (f x) = f x := hfS _ hfx
      exact hx (by rw [← f.injective this]; exact hfx)
  have h₂ : ∀ x, f x ≠ x → x ∈ Sᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    intro hxS
    exact hx (hfS x hxS)
  exact ⟨f.subtypePerm h₁, Perm.ofSubtype_subtypePerm h₁ h₂⟩

theorem mk_eq_thetaHom_or (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)} {a : G}
    (ha : a ∈ centralizer ({z} : Set G)) {σ : Perm ↥Sᶜ}
    (hσ : Perm.ofSubtype σ = permOf h d e ha)
    (haR : a ∈ centralizer (corr (X := G) e (altSub S) : Set G))
    (hzS : z ∈ centralizer (corr (X := G) e (altSub S) : Set G)) :
    (QuotientGroup.mk ⟨a, haR⟩ : Sec G (corr (X := G) e (altSub S))) = thetaHom h d T e S σ ∨
      (QuotientGroup.mk ⟨a, haR⟩ : Sec G (corr (X := G) e (altSub S))) =
        QuotientGroup.mk ⟨z, hzS⟩ * thetaHom h d T e S σ := by
  have hκ : kappa h d T e S σ = (swapIota h d T e (permOf h d e ha) : G) := by
    rw [kappa_apply, hσ]
  rw [thetaHom_apply]
  rcases eq_swapIota_or h d T e ha with h1 | h1
  · left
    congr 1
    exact Subtype.ext (h1.trans hκ.symm)
  · right
    rw [← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    change a = z * kappa h d T e S σ
    rw [hκ]
    exact h1

theorem exists_partner_root_at (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {a g : G} (ha : a ∈ centralizer ({z} : Set G))
    (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf h d e ha)).card ∧ (fixFin (permOf h d e ha)).card ≠ 6)
    {S : Finset (Fin n)} (hSF : S ⊆ fixFin (permOf h d e ha)) :
    ∃ S₁ : Finset (Fin n), S₁.card = S.card ∧
      ∃ (hz₁ : z ∈ centralizer (corr (X := G) e (altSub S₁) : Set G))
        (haR : a ∈ centralizer (corr (X := G) e (altSub S) : Set G))
        (Φ : Sec G (corr (X := G) e (altSub S₁)) ≃* Sec G (corr (X := G) e (altSub S))),
        Φ (QuotientGroup.mk ⟨z, hz₁⟩) = QuotientGroup.mk ⟨a, haR⟩ := by
  obtain ⟨S₁, hS₁card, hrS⟩ := exists_common_root₂ h d T e ha hg haz hf hSF
  have hE : ExactShape z L n := exactShape_of_setting h d T.card
  have hz₁ : z ∈ centralizer (corr (X := G) e (altSub S₁) : Set G) :=
    t_mem_centralizer_corr (X := G) e hE (altSub S₁)
  have haR : a ∈ centralizer (corr (X := G) e (altSub S) : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (comm_of_mem_corr_of_permOf_fix h d e ha (fun i hi => mem_fixFin.1 (hSF hi)) hw).symm
  obtain ⟨Φ, hΦ⟩ := exists_secEquiv_of_conj e hrS hg hz₁ haR
  exact ⟨S₁, hS₁card, hz₁, haR, Φ, hΦ⟩

theorem exists_partner_root (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {k : ℕ} (hk : k ≤ 4)
    {a g : G} (ha : a ∈ centralizer ({z} : Set G)) (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf h d e ha)).card ∧ (fixFin (permOf h d e ha)).card ≠ 6) :
    ∃ S S₁ : Finset (Fin n), S ⊆ fixFin (permOf h d e ha) ∧ S.card = k ∧ S₁.card = k ∧
      ∃ (hz₁ : z ∈ centralizer (corr (X := G) e (altSub S₁) : Set G))
        (haR : a ∈ centralizer (corr (X := G) e (altSub S) : Set G))
        (Φ : Sec G (corr (X := G) e (altSub S₁)) ≃* Sec G (corr (X := G) e (altSub S))),
        Φ (QuotientGroup.mk ⟨z, hz₁⟩) = QuotientGroup.mk ⟨a, haR⟩ := by
  classical
  obtain ⟨S, hSF, hScard⟩ :=
    Finset.exists_subset_card_eq (show k ≤ (fixFin (permOf h d e ha)).card by omega)
  obtain ⟨S₁, hS₁card, hz₁, haR, Φ, hΦ⟩ := exists_partner_root_at h d T e ha hg haz hf hSF
  exact ⟨S, S₁, hSF, hScard, hS₁card.trans hScard, hz₁, haR, Φ, hΦ⟩

theorem near_partner_swap (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {S₀ : Finset (Fin n)}
    (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n) (hII : CaseIIAt e z S₀)
    {a g : G} (ha : a ∈ centralizer ({z} : Set G)) (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf h d e ha)).card ∧ (fixFin (permOf h d e ha)).card ≠ 6) :
    (permOf h d e ha).IsSwap := by
  classical
  obtain ⟨S, S₁, hSF, hScard, hS₁card, hz₁, haR, Φ, hΦ⟩ :=
    exists_partner_root h d T e (show S₀.card ≤ 4 by omega) ha hg haz hf
  have hE : ExactShape z L n := exactShape_of_setting h d T.card
  have hSc : 2 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  obtain ⟨hz₁', hs₁⟩ := caseIIAt_transport hE e (show S₀.card = S₁.card by omega) hSc hII
  obtain ⟨hzS, ε, hε⟩ := caseIIAt_transport hE e (show S₀.card = S.card by omega) hSc hII
  have hsa : SymOutcome (QuotientGroup.mk ⟨a, haR⟩ : Sec G (corr (X := G) e (altSub S)))
      (n - S.card) := by
    have := SymOutcome.map' Φ hs₁
    rw [hΦ, hS₁card, ← hScard] at this
    exact this
  obtain ⟨ε', hε'⟩ := hsa
  set zb : Sec G (corr (X := G) e (altSub S)) := QuotientGroup.mk ⟨z, hzS⟩ with hzb
  set ab : Sec G (corr (X := G) e (altSub S)) := QuotientGroup.mk ⟨a, haR⟩ with hab
  have hSc5 : 5 ≤ Sᶜ.card := by rw [card_compl_fin]; omega
  have hScn : Sᶜ.card = n - S.card := card_compl_fin S
  have hτ' : (ε.symm ab).IsSwap := by
    have := isSwap_map_of_mulEquiv (ε'.trans ε.symm) rfl (by simp only [Fintype.card_fin]; omega)
      hε'
    simpa using this
  have hz2 : z * z = 1 := d.mul_self
  have haa : a * a = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hza : ab * zb = zb * ab := by
    rw [hab, hzb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 ha)
  have hne : ab ≠ zb := mk_ne_of_partner d ha haz haa hzS haR
  set Ψ : Perm ↥Sᶜ →* Perm (Fin (n - S.card + 2)) :=
    ε.symm.toMonoidHom.comp (thetaHom h d T e S) with hΨ
  have hinj : Function.Injective Ψ :=
    ε.symm.injective.comp (thetaHom_injective h d T e hSc5)
  have hθz : ∀ π : Perm ↥Sᶜ, thetaHom h d T e S π * zb = zb * thetaHom h d T e S π := by
    intro π
    rw [thetaHom_apply, hzb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (kappa_mem_centralizer h d T e S π))
  have hcomm : ∀ π, Ψ π * ε.symm zb = ε.symm zb * Ψ π := by
    intro π
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hθz]
  have hneΨ : ∀ π, Ψ π ≠ ε.symm zb := by
    intro π hπ
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hπ
    exact thetaHom_ne_z h d T e S hzS π (ε.symm.injective hπ)
  have hτ'c : ε.symm ab * ε.symm zb = ε.symm zb * ε.symm ab := by
    rw [← map_mul, ← map_mul, hza]
  have hτ'ne : ε.symm ab ≠ ε.symm zb := fun h' => hne (ε.symm.injective h')
  obtain ⟨σ, hσf⟩ := exists_ofSubtype_eq (fun i hi => mem_fixFin.1 (hSF hi))
  have hσΨ : Ψ σ = ε.symm ab ∨ Ψ σ = ε.symm zb * ε.symm ab := by
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rcases mk_eq_thetaHom_or h d T e ha hσf haR hzS with h1 | h1
    · left
      have h1' : ab = thetaHom h d T e S σ := h1
      rw [h1']
    · right
      have h1' : ab = zb * thetaHom h d T e S σ := h1
      rw [← map_mul, h1', ← mul_assoc]
      have hzz : zb * zb = 1 := by
        rw [hzb, ← QuotientGroup.mk_mul]
        have : (⟨z, hzS⟩ : ↥(centralizer (corr (X := G) e (altSub S) : Set G))) * ⟨z, hzS⟩ = 1 :=
          Subtype.ext hz2
        rw [this]
        rfl
      rw [hzz, one_mul]
  have hσswap : σ.IsSwap := by
    refine isSwap_of_embedding (α := ↥Sᶜ) (β := Fin (n - S.card + 2)) ?_ ?_ Ψ hinj hε hcomm
      hneΨ hτ' hτ'c hτ'ne hσΨ
    · simp only [Fintype.card_fin, Fintype.card_coe]; omega
    · simp only [Fintype.card_coe]; omega
  have := hσswap.of_subtype_isSwap
  rwa [hσf] at this

theorem near_partner_false (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {S₀ : Finset (Fin n)}
    (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n) (hI : CaseIAt e z S₀)
    {a g : G} (ha : a ∈ centralizer ({z} : Set G)) (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf h d e ha)).card ∧ (fixFin (permOf h d e ha)).card ≠ 6) :
    False := by
  classical
  obtain ⟨S, S₁, hSF, hScard, hS₁card, hz₁, haR, Φ, hΦ⟩ :=
    exists_partner_root h d T e (show S₀.card ≤ 4 by omega) ha hg haz hf
  have hE : ExactShape z L n := exactShape_of_setting h d T.card
  have hSc : 2 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  obtain ⟨hz₁', hc₁⟩ := caseIAt_transport hE e (show S₀.card = S₁.card by omega) hSc hI
  obtain ⟨hzS, hcS⟩ := caseIAt_transport hE e (show S₀.card = S.card by omega) hSc hI
  set zb : Sec G (corr (X := G) e (altSub S)) := QuotientGroup.mk ⟨z, hzS⟩ with hzb
  set ab : Sec G (corr (X := G) e (altSub S)) := QuotientGroup.mk ⟨a, haR⟩ with hab
  have hac : ab ∈ Subgroup.center (Sec G (corr (X := G) e (altSub S))) := by
    rw [← hΦ, Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := Φ.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hc₁) y']
  obtain ⟨σ, hσf⟩ := exists_ofSubtype_eq (fun i hi => mem_fixFin.1 (hSF hi))
  have hθc : thetaHom h d T e S σ ∈ Subgroup.center (Sec G (corr (X := G) e (altSub S))) := by
    rcases mk_eq_thetaHom_or h d T e ha hσf haR hzS with h1 | h1
    · rw [← h1]; exact hac
    · have h1' : ab = zb * thetaHom h d T e S σ := h1
      have : thetaHom h d T e S σ = zb⁻¹ * ab := by rw [h1']; group
      rw [this]
      exact mul_mem (inv_mem hcS) hac
  have hSc5 : 5 ≤ Sᶜ.card := by rw [card_compl_fin]; omega
  have hσ1 : σ = 1 := by
    refine eq_one_of_forall_commute (by simp only [Fintype.card_coe]; omega) fun π => ?_
    apply thetaHom_injective h d T e hSc5
    rw [map_mul, map_mul]
    exact ((Subgroup.mem_center_iff.1 hθc) (thetaHom h d T e S π)).symm
  have hp1 : permOf h d e ha = 1 := by rw [← hσf, hσ1, map_one]
  have hι1 : (swapIota h d T e 1 : G) = 1 := by rw [map_one]; rfl
  rcases eq_swapIota_or h d T e ha with h1 | h1
  · rw [hp1, hι1] at h1
    have hz1 : z = 1 := by
      have : g * z * g⁻¹ = 1 := hg.trans h1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    have := d.order
    rw [hz1, orderOf_one] at this
    exact absurd this (by decide)
  · rw [hp1, hι1, mul_one] at h1
    exact haz h1

end Near

end CFSG.OddStandard.AltStdSec
