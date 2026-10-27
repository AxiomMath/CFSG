module

public import CFSG.CGT.PushingUpLit.SolKR2.FirstCore
public import CFSG.CGT.PushingUpLit.SolKR2.SigmaLocal
public import CFSG.CGT.PushingUpLit.SolKR2.Pair

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n (conjSubgroup_mul conjSubgroup_eq_self_iff exists_mul_of_mem_sup
  inSubgroup_pCore_two mem_normalizer_inf mem_normalizer_centralizer)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def IsE16 (E : Subgroup G) : Prop :=
  (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card ↥E = 16

theorem IsE16.conj {E : Subgroup G} (hE : IsE16 E) (g : G) : IsE16 (conjSubgroup g E) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, ?_⟩
  · have := hE.1 _ (mem_conjSubgroup.mp hx) _ (mem_conjSubgroup.mp hy)
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = y * x := by group
  · have := hE.2.1 _ (mem_conjSubgroup.mp hx)
    calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  · rw [card_conjSubgroup, hE.2.2]

theorem conj_eq_self_of_forall_le {E Y : Subgroup G} (hE : ∀ g ∈ E, conjSubgroup g Y ≤ Y)
    {g : G} (hg : g ∈ E) : conjSubgroup g Y = Y := by
  refine le_antisymm (hE g hg) ?_
  have h' := hE g⁻¹ (E.inv_mem hg)
  intro w hw
  have : g⁻¹ * w * g ∈ Y := h' (by
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
    exact hw)
  rw [mem_conjSubgroup]
  exact this

theorem exists_two_ne {E : Subgroup G} (hE : Nat.card ↥E = 4) :
    ∃ e₁ ∈ E, e₁ ≠ 1 ∧ ∃ e₂ ∈ E, e₂ ≠ 1 ∧ e₂ ≠ e₁ := by
  classical
  have hne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hE
    omega
  obtain ⟨⟨e₁, he₁⟩, he₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he₁1' : e₁ ≠ 1 := fun e => he₁1 (Subtype.ext e)
  refine ⟨e₁, he₁, he₁1', ?_⟩
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun x : ↥E => decide ((x : G) = 1)) := by
    intro x y hxy
    by_cases hx : (x : G) = 1
    · have hy : (y : G) = 1 := by
        by_contra hy
        simp [hx, hy] at hxy
      exact Subtype.ext (hx.trans hy.symm)
    · have hy : (y : G) ≠ 1 := by
        intro hy
        simp [hx, hy] at hxy
      exact Subtype.ext ((hcon _ x.2 hx).trans (hcon _ y.2 hy).symm)
  have := Nat.card_le_card_of_injective _ hinj
  rw [hE, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

section Descent

variable
  [Finite G] {M B : Subgroup G}
  (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) (hW : R2Weak) (h : R2 M B)
include hCen hU hW h

theorem pair_facts {F : Subgroup G} (hF : F ∈ Lam M B) (hne : F ≠ omegaOneSub B) :
    IsE16 (omegaOneSub B ⊔ F) ∧
    (∀ y ∈ omegaTwoSub B, y ∉ omegaOneSub B → ∀ m ∈ omegaOneSub B ⊔ F, y * m = m * y →
      m ∈ omegaOneSub B) ∧
    F ⊔ omegaTwoSub B ≤ Subgroup.normalizer ((omegaOneSub B ⊔ F : Subgroup G) : Set G) ∧
    Nat.card ↥(F ⊔ omegaTwoSub B) = 64 := by
  obtain ⟨g, hg, P⟩ := Pair.ncpair_of_comm_ne hW h hF hne
  have hΩ := Pair.omegaOne_conj_U h g
  have hΩU := h.omegaOne_omegaTwo
  have hN : omegaOneSub (omegaTwoSub B) ⊔ omegaOneSub (conjSubgroup g (omegaTwoSub B)) =
      omegaOneSub B ⊔ F := by
    rw [hΩ, hΩU, ← hg]
  have hFV : F ≤ conjSubgroup g (omegaTwoSub B) := by
    rw [hg]
    exact Pair.conj_B0_le_U h g
  refine ⟨⟨fun x hx y hy => ?_, fun x hx => ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [← hN] at hx hy
    exact P.comm_N hCen hU hx hy
  · rw [← hN] at hx
    exact P.sq_N hCen hU hx
  · have h1 := P.card_N hCen hU
    rw [hN, hΩ, hΩU, h.card4, Pair.card_conj_B0 h g] at h1
    exact h1
  · intro y hy hyL m hm hc
    rw [← hN] at hm
    have := P.cent hCen hU hy (by rwa [hΩU]) hm hc
    rwa [hΩU] at this
  · have hle := P.le_normalizer hCen hU
    rw [hN] at hle
    exact (sup_le (hFV.trans le_sup_right) le_sup_left).trans hle
  · have hdisj : Disjoint (omegaTwoSub B) F := by
      rw [disjoint_iff]
      have := P.setup.inf_eq_bot P.ne
      exact eq_bot_iff.mpr (le_trans (inf_le_inf_left _ hFV) this.le)
    have hnorm : F ≤ Subgroup.normalizer (omegaTwoSub B : Set G) :=
      fun x hx => Pair.le_normalizer_U h (Lam.le_M hF hx)
    rw [sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm
      hdisj, Pair.card_U h, Lam.card_eq h hF]

theorem E16_unique {F : Subgroup G} (hF : F ∈ Lam M B) (hne : F ≠ omegaOneSub B)
    {E' E'' : Subgroup G} (h' : E' ≤ F ⊔ omegaTwoSub B) (h'' : E'' ≤ F ⊔ omegaTwoSub B)
    (hE' : IsE16 E') (hE'' : IsE16 E'')
    (hn' : E' ≠ omegaOneSub B ⊔ F) (hn'' : E'' ≠ omegaOneSub B ⊔ F) : E' = E'' := by
  obtain ⟨hN16, hcent, hnorm, hY⟩ := pair_facts hCen hU hW h hF hne
  set N := omegaOneSub B ⊔ F with hNdef
  set Y := F ⊔ omegaTwoSub B with hYdef
  have hB0N : omegaOneSub B ≤ N := le_sup_left
  have hFN : F ≤ N := le_sup_right
  have hNY : N ≤ Y := sup_le ((Pair.B0_le_U h).trans le_sup_right) le_sup_left
  have hB0card : Nat.card ↥(omegaOneSub B) = 4 := h.card4
  have key : ∀ E : Subgroup G, E ≤ Y → IsE16 E → E ≠ N →
      (∀ y ∈ Y, ∃ e ∈ E, ∃ n ∈ N, y = e * n) ∧ E ⊓ N = omegaOneSub B ∧
      (∀ s ∈ E, s ∉ N → ∀ x ∈ N, s * x = x * s → x ∈ omegaOneSub B) := by
    intro E hEY hE hEN
    have ha1 : ∀ s ∈ E, s ∉ N → ∀ x ∈ N, s * x = x * s → x ∈ omegaOneSub B := by
      intro s hsE hsN x hxN hsx
      have hsY : s ∈ omegaTwoSub B ⊔ F := by
        rw [sup_comm]
        exact hEY hsE
      obtain ⟨u, hu, f, hf, rfl⟩ := exists_mul_of_mem_sup (V := omegaTwoSub B) (U := F)
        (fun x hx => Pair.le_normalizer_U h (Lam.le_M hF hx)) hsY
      have huB : u ∉ omegaOneSub B := fun huB => hsN (N.mul_mem (hB0N huB) (hFN hf))
      have hxf : x * f = f * x := hN16.1 x hxN f (hFN hf)
      have hux : u * x = x * u := by
        have h1 : u * x * f = x * u * f := by
          calc u * x * f = u * (x * f) := by group
            _ = u * (f * x) := by rw [hxf]
            _ = u * f * x := by group
            _ = x * (u * f) := hsx
            _ = x * u * f := by group
        exact mul_right_cancel h1
      exact hcent u hu huB x hxN hux
    have hEnle : E ⊓ N ≤ omegaOneSub B := by
      have hex : ∃ s ∈ E, s ∉ N := by
        by_contra hcon
        push Not at hcon
        exact hEN (Subgroup.eq_of_le_of_card_ge hcon (by rw [hN16.2.2, hE.2.2]))
      obtain ⟨s, hsE, hsN⟩ := hex
      intro x hx
      obtain ⟨hxE, hxN⟩ := Subgroup.mem_inf.mp hx
      exact ha1 s hsE hsN x hxN (hE.1 s hsE x hxE)
    have hNnormal : (N.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hnorm
    have hprod := CFSG.RankThree.GF2n.Tim78.card_map_mk_mul (X := Y) (H := E) (N := N) hEY
    have hEN4 : Nat.card ↥(E ⊓ N) ≤ 4 := by
      have := Subgroup.card_le_of_le hEnle
      rwa [hB0card] at this
    have hquot : Nat.card (↥Y ⧸ N.subgroupOf Y) = 4 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf Y)
      rw [hY, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv, hN16.2.2] at this
      omega
    set img := (E.subgroupOf Y).map (QuotientGroup.mk' (N.subgroupOf Y)) with himg
    have himg4 : Nat.card ↥img ≤ 4 := by
      have := Subgroup.card_le_card_group img
      rwa [hquot] at this
    rw [hE.2.2] at hprod
    have ha : Nat.card ↥img = 4 := by
      by_contra hne4
      have h3 : Nat.card ↥img ≤ 3 := by omega
      have := Nat.mul_le_mul h3 hEN4
      omega
    have hb : Nat.card ↥(E ⊓ N) = 4 := by
      rw [ha] at hprod
      omega
    have hEq : E ⊓ N = omegaOneSub B :=
      (Subgroup.eq_of_le_of_card_ge hEnle (by rw [hb, hB0card])).symm ▸ rfl
    refine ⟨?_, hEq, ha1⟩
    have htop : img = ⊤ := Subgroup.eq_top_of_card_eq img (by rw [ha, hquot])
    intro y hy
    have hmem : QuotientGroup.mk' (N.subgroupOf Y) ⟨y, hy⟩ ∈ img := by rw [htop]; trivial
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hzy
    have hzy' : ((z : ↥Y) : G)⁻¹ * y ∈ N := by
      have := Subgroup.mem_subgroupOf.mp hzy
      simpa using this
    exact ⟨(z : G), Subgroup.mem_subgroupOf.mp hz, _, hzy', by group⟩
  have k' := key E' h' hE' hn'
  have k'' := key E'' h'' hE'' hn''
  have hsub : E'' ≤ E' := by
    intro s' hs'
    by_cases hs'N : s' ∈ N
    · have h1 : s' ∈ E'' ⊓ N := ⟨hs', hs'N⟩
      rw [k''.2.1] at h1
      have h2 : s' ∈ E' ⊓ N := by rw [k'.2.1]; exact h1
      exact h2.1
    · obtain ⟨e, he, n, hn, hs'e⟩ := k'.1 s' (h'' hs')
      have heN : e ∉ N := fun heN => hs'N (hs'e ▸ N.mul_mem heN hn)
      have hee : e * e = 1 := hE'.2.1 e he
      have hnn : n * n = 1 := hN16.2.1 n hn
      have hs'sq : e * n * (e * n) = 1 := by
        have := hE''.2.1 s' hs'
        rwa [hs'e] at this
      have hcomm : e * n = n * e := by
        calc e * n = (e * n)⁻¹ := eq_inv_of_mul_eq_one_left hs'sq
          _ = n⁻¹ * e⁻¹ := mul_inv_rev _ _
          _ = n * e := by
            rw [inv_eq_of_mul_eq_one_right hnn, inv_eq_of_mul_eq_one_right hee]
      have hnB : n ∈ omegaOneSub B := k'.2.2 e he heN n hn hcomm
      have hnE' : n ∈ E' := by
        have : n ∈ E' ⊓ N := by rw [k'.2.1]; exact hnB
        exact this.1
      rw [hs'e]
      exact E'.mul_mem he hnE'
  exact (Subgroup.eq_of_le_of_card_ge hsub (by rw [hE'.2.2, hE''.2.2])).symm

omit hCen hU hW in
theorem uniform_conj {S : Sylow 2 M} {F E : Subgroup G} (hF : F ∈ Lam M B) (hE : E ∈ Lam M B)
    (hFS : F ≤ (S : Subgroup M).map M.subtype) (hES : E ≤ (S : Subgroup M).map M.subtype)
    {m : ℕ} (hm : 2 ≤ m)
    (hord : ∀ f ∈ F, f ≠ 1 → ∀ e ∈ E, e ≠ 1 → orderOf (f * e) = 2 ^ (m + 1))
    {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    conjSubgroup e F ≠ F ∧ conjSubgroup e F ∈ Lam M B ∧
      conjSubgroup e F ≤ (S : Subgroup M).map M.subtype ∧
      ∀ f ∈ F, f ≠ 1 → ∀ f' ∈ conjSubgroup e F, f' ≠ 1 → orderOf (f * f') = 2 ^ m := by
  have heM : e ∈ M := Lam.le_M hE he
  have hee : e * e = 1 := Lam.mul_self h hE e he
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hF' : conjSubgroup e F ∈ Lam M B := Lam.conj_mem hF heM
  have heS : e ∈ (S : Subgroup M).map M.subtype := hES he
  have hF'S : conjSubgroup e F ≤ (S : Subgroup M).map M.subtype := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have := ((S : Subgroup M).map M.subtype).mul_mem
      (((S : Subgroup M).map M.subtype).mul_mem heS (hFS hx))
      (((S : Subgroup M).map M.subtype).inv_mem heS)
    rwa [show e * (e⁻¹ * x * e) * e⁻¹ = x by group] at this
  obtain ⟨f₀, hf₀, hf₀1⟩ : ∃ f₀ ∈ F, f₀ ≠ 1 := by
    obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Lam.ne_bot h hF)
    exact ⟨f, hf, fun e => hf1 (Subtype.ext e)⟩
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hx₀F' : e * f₀ * e⁻¹ ∈ conjSubgroup e F := by
    rw [mem_conjSubgroup, show e⁻¹ * (e * f₀ * e⁻¹) * e = f₀ by group]
    exact hf₀
  have hmul : f₀ * (e * f₀ * e⁻¹) = (f₀ * e) ^ 2 := by
    rw [hei, sq]
    group
  have hord₀ : orderOf (f₀ * (e * f₀ * e⁻¹)) = 2 ^ m := by
    rw [hmul, orderOf_pow' _ (by norm_num : 2 ≠ 0), hord f₀ hf₀ hf₀1 e he he1,
      Nat.gcd_eq_right (dvd_pow_self 2 (by omega : m + 1 ≠ 0)), pow_succ,
      Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  have hx₀1 : e * f₀ * e⁻¹ ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hord₀
    have := orderOf_dvd_of_pow_eq_one
      (show f₀ ^ 2 = 1 by rw [sq]; exact Lam.mul_self h hF f₀ hf₀)
    rw [hord₀] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hne : conjSubgroup e F ≠ F := by
    intro heq
    rw [heq] at hx₀F'
    have hcomm := Lam.comm_self h hF f₀ hf₀ _ hx₀F'
    have hsq : (f₀ * (e * f₀ * e⁻¹)) ^ 2 = 1 := by
      calc (f₀ * (e * f₀ * e⁻¹)) ^ 2 = f₀ * (e * f₀ * e⁻¹) * (f₀ * (e * f₀ * e⁻¹)) := sq _
        _ = f₀ * ((e * f₀ * e⁻¹) * f₀) * (e * f₀ * e⁻¹) := by group
        _ = f₀ * (f₀ * (e * f₀ * e⁻¹)) * (e * f₀ * e⁻¹) := by rw [← hcomm]
        _ = (f₀ * f₀) * ((e * f₀ * e⁻¹) * (e * f₀ * e⁻¹)) := by group
        _ = 1 := by
          rw [Lam.mul_self h hF f₀ hf₀, Lam.mul_self h hF _ hx₀F', one_mul]
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [hord₀] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  refine ⟨hne, hF', hF'S, ?_⟩
  obtain ⟨g, hg⟩ := Lam.exists_conj hF
  obtain ⟨k, hk⟩ := Lam.exists_conj hF'
  have hgR : conjSubgroup g (omegaOneSub B) ≤ (S : Subgroup M).map M.subtype := hg ▸ hFS
  have hkR : conjSubgroup k (omegaOneSub B) ≤ (S : Subgroup M).map M.subtype := hk ▸ hF'S
  have hneg : conjSubgroup g (omegaOneSub B) ≠ conjSubgroup k (omegaOneSub B) := by
    rw [← hg, ← hk]
    exact fun e => hne e.symm
  intro f hf hf1 f' hf' hf'1
  exact orderOf_mul_uniform (fun v hv => Pair.sq_B0 h hv) h.root
    (R := (S : Subgroup M).map M.subtype) m g k hgR hkR hneg f₀ (hg ▸ hf₀) hf₀1
    (e * f₀ * e⁻¹) (hk ▸ hx₀F') hx₀1 hord₀ f (hg ▸ hf) hf1 f' (hk ▸ hf') hf'1

theorem false_of_order_eight (hcore : R2FirstCore) {S : Sylow 2 M} {F E : Subgroup G}
    (hF : F ∈ Lam M B) (hE : E ∈ Lam M B)
    (hFS : F ≤ (S : Subgroup M).map M.subtype) (hES : E ≤ (S : Subgroup M).map M.subtype)
    (hord : ∀ f ∈ F, f ≠ 1 → ∀ e ∈ E, e ≠ 1 → orderOf (f * e) = 2 ^ 3) : False := by
  have hord' : ∀ f ∈ F, f ≠ 1 → ∀ e ∈ E, e ≠ 1 → orderOf (f * e) = 2 ^ (2 + 1) := hord
  obtain ⟨f₀, hf₀, hf₀1⟩ : ∃ f₀ ∈ F, f₀ ≠ 1 := by
    obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Lam.ne_bot h hF)
    exact ⟨f, hf, fun e => hf1 (Subtype.ext e)⟩
  obtain ⟨e₁, he₁, he₁1, e₂, he₂, he₂1, hne12⟩ := exists_two_ne (Lam.card_eq h hE)
  have hFB : F ≠ omegaOneSub B := by
    rintro rfl
    have hc := R2.comm_B0 h hE e₁ he₁ f₀ hf₀
    have hsq : f₀ * e₁ * (f₀ * e₁) = 1 := by
      calc f₀ * e₁ * (f₀ * e₁) = f₀ * (e₁ * f₀) * e₁ := by group
        _ = f₀ * (f₀ * e₁) * e₁ := by rw [hc]
        _ = (f₀ * f₀) * (e₁ * e₁) := by group
        _ = 1 := by rw [Lam.mul_self h hF f₀ hf₀, Lam.mul_self h hE e₁ he₁, one_mul]
    have := orderOf_dvd_of_pow_eq_one (show (f₀ * e₁) ^ 2 = 1 by rw [sq]; exact hsq)
    rw [hord f₀ hf₀ hf₀1 e₁ he₁ he₁1] at this
    norm_num at this
  have hY : ∀ e ∈ E, conjSubgroup e F ≤ F ⊔ omegaTwoSub B := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1, conjSubgroup_one]
      exact le_sup_left
    obtain ⟨hne, hF', hF'S, hunif⟩ := uniform_conj h hF hE hFS hES (m := 2) le_rfl
      hord' he he1
    have := hcore G M B h S (conjSubgroup e F) F hF' hF hF'S hFS (fun a ha ha1 d hd hd1 => by
      rw [CFSG.Timmesfeld.orderOf_mul_comm_eq]
      simpa using hunif d hd hd1 a ha ha1)
    rw [← this.2]
    exact le_sup_left
  have hnormY : ∀ e ∈ E, conjSubgroup e (F ⊔ omegaTwoSub B) ≤ F ⊔ omegaTwoSub B := by
    intro e he
    have heM : e ∈ M := Lam.le_M hE he
    have hU' : conjSubgroup e (omegaTwoSub B) = omegaTwoSub B :=
      conjSubgroup_eq_self_iff.mpr (Pair.le_normalizer_U h heM)
    have e1 : conjSubgroup e (F ⊔ omegaTwoSub B) =
        conjSubgroup e F ⊔ conjSubgroup e (omegaTwoSub B) := Subgroup.map_sup _ _ _
    rw [e1, hU']
    exact sup_le (hY e he) le_sup_right
  have hYe : ∀ e ∈ E, conjSubgroup e (F ⊔ omegaTwoSub B) = F ⊔ omegaTwoSub B :=
    fun e he => conj_eq_self_of_forall_le hnormY he
  obtain ⟨hN16, -, -, -⟩ := pair_facts hCen hU hW h hF hFB
  have hNY : omegaOneSub B ⊔ F ≤ F ⊔ omegaTwoSub B :=
    sup_le ((Pair.B0_le_U h).trans le_sup_right) le_sup_left
  have hTY : ∀ e ∈ E, conjSubgroup e (omegaOneSub B ⊔ F) ≤ F ⊔ omegaTwoSub B := by
    intro e he
    rw [← hYe e he]
    exact Subgroup.map_mono hNY
  have hex : ∃ e₀ ∈ E, e₀ ≠ 1 ∧ conjSubgroup e₀ (omegaOneSub B ⊔ F) = omegaOneSub B ⊔ F := by
    by_cases h1 : conjSubgroup e₁ (omegaOneSub B ⊔ F) = omegaOneSub B ⊔ F
    · exact ⟨e₁, he₁, he₁1, h1⟩
    by_cases h2 : conjSubgroup e₂ (omegaOneSub B ⊔ F) = omegaOneSub B ⊔ F
    · exact ⟨e₂, he₂, he₂1, h2⟩
    have heq : conjSubgroup e₁ (omegaOneSub B ⊔ F) = conjSubgroup e₂ (omegaOneSub B ⊔ F) :=
      E16_unique hCen hU hW h hF hFB (hTY e₁ he₁) (hTY e₂ he₂) (hN16.conj e₁) (hN16.conj e₂)
        h1 h2
    refine ⟨e₂⁻¹ * e₁, E.mul_mem (E.inv_mem he₂) he₁, ?_, ?_⟩
    · intro hc
      apply hne12
      exact inv_inj.mp (mul_eq_one_iff_eq_inv.mp hc)
    · calc conjSubgroup (e₂⁻¹ * e₁) (omegaOneSub B ⊔ F)
          = conjSubgroup e₂⁻¹ (conjSubgroup e₁ (omegaOneSub B ⊔ F)) := conjSubgroup_mul _ _ _
        _ = conjSubgroup e₂⁻¹ (conjSubgroup e₂ (omegaOneSub B ⊔ F)) := by rw [heq]
        _ = omegaOneSub B ⊔ F := by rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  obtain ⟨e₀, he₀, he₀1, hstab⟩ := hex
  have hee₀ : e₀ * e₀ = 1 := Lam.mul_self h hE e₀ he₀
  have hei₀ : e₀⁻¹ = e₀ := inv_eq_of_mul_eq_one_right hee₀
  have hf'N : e₀ * f₀ * e₀⁻¹ ∈ omegaOneSub B ⊔ F := by
    have : e₀ * f₀ * e₀⁻¹ ∈ conjSubgroup e₀ (omegaOneSub B ⊔ F) := by
      rw [mem_conjSubgroup, show e₀⁻¹ * (e₀ * f₀ * e₀⁻¹) * e₀ = f₀ by group]
      exact Subgroup.mem_sup_right hf₀
    rwa [hstab] at this
  have hf₀N : f₀ ∈ omegaOneSub B ⊔ F := Subgroup.mem_sup_right hf₀
  have hcomm := hN16.1 _ hf₀N _ hf'N
  have hsq : (f₀ * e₀) ^ 4 = 1 := by
    have e1 : (f₀ * e₀) ^ 2 = f₀ * (e₀ * f₀ * e₀⁻¹) := by
      rw [hei₀, sq]
      group
    calc (f₀ * e₀) ^ 4 = ((f₀ * e₀) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (f₀ * (e₀ * f₀ * e₀⁻¹)) * (f₀ * (e₀ * f₀ * e₀⁻¹)) := by rw [e1, sq]
      _ = (f₀ * f₀) * ((e₀ * f₀ * e₀⁻¹) * (e₀ * f₀ * e₀⁻¹)) := by
        calc (f₀ * (e₀ * f₀ * e₀⁻¹)) * (f₀ * (e₀ * f₀ * e₀⁻¹))
            = f₀ * ((e₀ * f₀ * e₀⁻¹) * f₀) * (e₀ * f₀ * e₀⁻¹) := by group
          _ = f₀ * (f₀ * (e₀ * f₀ * e₀⁻¹)) * (e₀ * f₀ * e₀⁻¹) := by rw [← hcomm]
          _ = _ := by group
      _ = 1 := by
        rw [hN16.2.1 f₀ hf₀N, hN16.2.1 _ hf'N, one_mul]
  have := orderOf_dvd_of_pow_eq_one hsq
  rw [hord f₀ hf₀ hf₀1 e₀ he₀ he₀1] at this
  norm_num at this

theorem no_uniform_order (hcore : R2FirstCore) : ∀ m : ℕ, 3 ≤ m → ∀ (S : Sylow 2 M)
    (F E : Subgroup G), F ∈ Lam M B → E ∈ Lam M B → F ≤ (S : Subgroup M).map M.subtype →
    E ≤ (S : Subgroup M).map M.subtype →
    (∀ f ∈ F, f ≠ 1 → ∀ e ∈ E, e ≠ 1 → orderOf (f * e) = 2 ^ m) → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm S F E hF hE hFS hES hord
    by_cases h3 : m = 3
    · subst h3
      exact false_of_order_eight hCen hU hW h hcore hF hE hFS hES hord
    · obtain ⟨e, he, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
        obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Lam.ne_bot h hE)
        exact ⟨e, he, fun e' => he1 (Subtype.ext e')⟩
      obtain ⟨-, hF', hF'S, hunif⟩ := uniform_conj h hF hE hFS hES (m := m - 1)
        (by omega) (by rwa [show m - 1 + 1 = m by omega]) he he1
      exact ih (m - 1) (by omega) (by omega) S F (conjSubgroup e F) hF hF' hFS hF'S hunif

end Descent

section Reduction


theorem R2First_of_core (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hW : R2Weak) (hcore : R2FirstCore) : R2First := by
  intro G _ _ M B h S A D hA hD hAS hDS hnc
  simp only [not_forall] at hnc
  obtain ⟨a, ha, d, hd, had⟩ := hnc
  have haa : a * a = 1 := Lam.mul_self h hA a ha
  have hdd : d * d = 1 := Lam.mul_self h hD d hd
  have ha1 : a ≠ 1 := fun e => had (by rw [e, one_mul, mul_one])
  have hd1 : d ≠ 1 := fun e => had (by rw [e, one_mul, mul_one])
  obtain ⟨g, hg⟩ := Lam.exists_conj hA
  obtain ⟨k, hk⟩ := Lam.exists_conj hD
  have hAD : A ≠ D := by
    rintro rfl
    exact had (Lam.comm_self h hA a ha d hd)
  have hS2 : IsPGroup 2 ((S : Subgroup M).map M.subtype) := S.isPGroup'.map M.subtype
  have hadS : a * d ∈ (S : Subgroup M).map M.subtype :=
    ((S : Subgroup M).map M.subtype).mul_mem (hAS ha) (hDS hd)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, orderOf (a * d) = 2 ^ m := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hS2) ⟨a * d, hadS⟩
    exact ⟨j, by rwa [Subgroup.orderOf_mk] at hj⟩
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hdvd : orderOf (a * d) ∣ 2 := by
      rw [hm]
      calc 2 ^ m ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
        _ = 2 := by norm_num
    have hsq : (a * d) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [sq] at hsq
    exact had (comm_of_mul_mul_self haa hdd hsq)
  have hgR : conjSubgroup g (omegaOneSub B) ≤ (S : Subgroup M).map M.subtype := hg ▸ hAS
  have hkR : conjSubgroup k (omegaOneSub B) ≤ (S : Subgroup M).map M.subtype := hk ▸ hDS
  have hunif : ∀ a' ∈ A, a' ≠ 1 → ∀ d' ∈ D, d' ≠ 1 → orderOf (a' * d') = 2 ^ m :=
    fun a' ha' ha'1 d' hd' hd'1 =>
      orderOf_mul_uniform (fun v hv => Pair.sq_B0 h hv) h.root
        (R := (S : Subgroup M).map M.subtype) m g k hgR hkR (by rw [← hg, ← hk]; exact hAD)
        a (hg ▸ ha) ha1 d (hk ▸ hd) hd1 hm a' (hg ▸ ha') ha'1 d' (hk ▸ hd') hd'1
  by_cases hm2' : m = 2
  · subst hm2'
    exact hcore G M B h S A D hA hD hAS hDS fun a' ha' ha'1 d' hd' hd'1 => by
      simpa using hunif a' ha' ha'1 d' hd' hd'1
  · exact (no_uniform_order hCen hU hW h hcore m (by omega) S A D hA hD hAS hDS hunif).elim

end Reduction

end CFSG.CGT.PushingUpLit.SolKR2
