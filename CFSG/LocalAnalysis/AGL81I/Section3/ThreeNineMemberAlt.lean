module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveSteps
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineAltPerm
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Action

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Equiv Equiv.Perm GL83 GL83.PiGen
open CFSG.LocalAnalysis.AGL81I.Section3.AltPerm

theorem false_of_threeNineHyp_alt_of_perm {X : Type} [Group X] [Finite X]
    {K E D X₁ : Subgroup X} {p d : ℕ} (h : ThreeNineHyp K E D X₁ p d) {n : ℕ} (hn5 : 5 ≤ n)
    (hn6 : n ≠ 6) (φ : ↥K ≃* alternatingGroup (Fin n))
    (hperm : ∀ G R : Subgroup (Perm (Fin n)), IsPGroup p R → Nat.card R = p ^ 2 →
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) → (∀ r ∈ R, r ^ p = 1) →
      (∀ r ∈ R, r ≠ 1 → ∀ τ ∈ alternatingGroup (Fin n), τ * r = r * τ → τ ∈ G) →
      ∀ σ : Perm (Fin n), σ.IsCycle → σ.support.card = d → σ ∈ G →
      (∀ τ ∈ alternatingGroup (Fin n), τ * σ = σ * τ → τ ∈ G) →
      alternatingGroup (Fin n) ≤ G) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  have : Group.IsPerfect ↥K := h.quasisimple.1
  have hZ : Subgroup.center ↥K = ⊥ := by
    have hA := alternatingGroup.center_eq_bot (α := Fin n) (by simp; omega)
    rw [eq_bot_iff]
    intro z hz
    have : φ z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro a
      obtain ⟨b, rfl⟩ := φ.surjective a
      rw [← map_mul, ← map_mul, hz b]
    rw [hA, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact φ.injective (by rw [this, map_one])
  let e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ
  have hA : (⊤ : Subgroup X) ≤ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal]
  let π : X →* Perm (Fin n) :=
    (permHom hA hn5 hn6 e).comp (Subgroup.topEquiv.symm : X ≃* (⊤ : Subgroup X)).toMonoidHom
  let ψ : ↥K →* Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))
  have hψ : ∀ c : ↥K, ψ c = (e (QuotientGroup.mk c) : Perm (Fin n)) := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    rw [hψ, hψ] at hab
    have h1 : (QuotientGroup.mk a : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk b :=
      e.injective (Subtype.ext hab)
    rw [QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  have hψsurj : ∀ τ ∈ alternatingGroup (Fin n), ∃ c : ↥K, ψ c = τ := by
    intro τ hτ
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (e.symm ⟨τ, hτ⟩)
    refine ⟨c, ?_⟩
    rw [hψ, hc, MulEquiv.apply_symm_apply]
  have hψmem : ∀ c : ↥K, ψ c ∈ alternatingGroup (Fin n) := fun c => (e (QuotientGroup.mk c)).2
  have hspec : ∀ (x : X) (c : ↥K), ∃ y : ↥K, (y : X) = x * c * x⁻¹ ∧
      π x * ψ c * (π x)⁻¹ = ψ y := by
    intro x c
    obtain ⟨y, hy, hy'⟩ := permHom_spec hA hn5 hn6 e ⟨x, Subgroup.mem_top x⟩ c
    exact ⟨y, hy, hy'⟩
  have hcomm : ∀ (x : X) (c : ↥K), π x * ψ c = ψ c * π x → x * c = c * x := by
    intro x c hxc
    obtain ⟨y, hy, hy'⟩ := hspec x c
    have h1 : ψ y = ψ c := by rw [← hy', hxc, mul_inv_cancel_right]
    have h2 : y = c := hψinj h1
    have h3 : x * c * x⁻¹ = c := by rw [← hy, h2]
    calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [h3]
  have hπK : ∀ k : ↥K, π k = ψ k := by
    intro k
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
    ext a
    obtain ⟨c, hc⟩ := hψsurj a a.2
    obtain ⟨y, hy, hy'⟩ := hspec k c
    have hyk : y = k * c * k⁻¹ := Subtype.ext (by rw [hy]; rfl)
    simp only [MulAut.conjNormal_apply]
    rw [← hc, hy', hyk, map_mul, map_mul, map_inv]
  have hπ1 : ∀ x : X, π x = 1 → ∀ c ∈ K, x * c = c * x := by
    intro x hx c hc
    have h1 := (permHom_eq_one_iff hA hn5 hn6 e ⟨x, Subgroup.mem_top x⟩).mp hx ⟨c, hc⟩
    exact h1
  let G' : Subgroup (Perm (Fin n)) := (X₁.subgroupOf K).map ψ
  have hG'mem : ∀ c : ↥K, (c : X) ∈ X₁ → ψ c ∈ G' := fun c hc => ⟨c, hc, rfl⟩
  have hcentG : ∀ x : X, (∀ c : ↥K, x * c = c * x → (c : X) ∈ X₁) →
      ∀ τ ∈ alternatingGroup (Fin n), τ * π x = π x * τ → τ ∈ G' := by
    intro x hx τ hτ hτx
    obtain ⟨c, rfl⟩ := hψsurj τ hτ
    exact hG'mem c (hx c (hcomm x c hτx.symm))
  let fE : ↥E →* Perm (Fin n) := π.comp E.subtype
  have hfEinj : Function.Injective fE := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (h.E_faithful a.2 (hπ1 a ha))
  let R : Subgroup (Perm (Fin n)) := fE.range
  have hRc : Nat.card R = p ^ 2 := by
    rw [← h.card_E]
    exact Nat.card_congr (MonoidHom.ofInjective hfEinj).toEquiv.symm
  have hRp : IsPGroup p R :=
    (CFSG.Open.IsElemAbelian.isPGroup h.elem).of_surjective fE.rangeRestrict
      fE.rangeRestrict_surjective
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, h.elem.1.is_comm.comm a b]
  have hRexp : ∀ r ∈ R, r ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha : a ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h.elem.2 a a.2)
    rw [← map_pow, ha, map_one]
  have hRG : ∀ r ∈ R, r ≠ 1 → ∀ τ ∈ alternatingGroup (Fin n), τ * r = r * τ → τ ∈ G' := by
    rintro _ ⟨a, rfl⟩ ha1
    refine hcentG a fun c hac => h.mem_of_commute_E a.2 ?_ (le_sup_left (a := K) c.2) hac
    intro ha
    exact ha1 (by rw [show a = 1 from Subtype.ext ha, map_one])
  obtain ⟨g₀, hg₀D, hg₀1⟩ : ∃ g ∈ D, g ≠ 1 := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.D_ne_bot
    exact ⟨g, hg, fun h' => hg1 (Subtype.ext h')⟩
  have hπD : ∀ g ∈ D, π g = 1 → g = 1 := by
    intro g hg hg1
    have hmem : g ∈ D ⊓ Subgroup.centralizer (K : Set X) :=
      ⟨hg, Subgroup.mem_centralizer_iff.mpr fun c hc => (hπ1 g hg1 c hc).symm⟩
    rw [h.D_faithful, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨a₀, ha₀⟩ := h.isPGroup_D ⟨g₀, hg₀D⟩
  obtain ⟨g₁, hg₁D, hg₁⟩ : ∃ g ∈ D, orderOf g = d := by
    have hord : orderOf (⟨g₀, hg₀D⟩ : D) ∣ d ^ a₀ := orderOf_dvd_of_pow_eq_one ha₀
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow h.d_prime).1 hord
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hi
      exact hg₀1 (congrArg Subtype.val hi)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) d
      (by
        have : d ∣ orderOf (⟨g₀, hg₀D⟩ : D) := by rw [hi]; exact dvd_pow_self d hi0
        exact this.trans (orderOf_dvd_natCard _))
    exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩
  have hσ₀ord : orderOf (π g₁) = d := by
    have hinj : Function.Injective (π.comp D.subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      exact Subtype.ext (hπD a a.2 ha)
    have h1 := orderOf_injective (π.comp D.subtype) hinj ⟨g₁, hg₁D⟩
    have h2 : (π.comp D.subtype) ⟨g₁, hg₁D⟩ = π g₁ := rfl
    rw [h2] at h1
    rw [h1, Subgroup.orderOf_mk]
    exact hg₁
  have hσ₀1 : π g₁ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ₀ord
    exact h.d_prime.one_lt.ne hσ₀ord
  obtain ⟨z, hz⟩ : ∃ z, π g₁ z ≠ z := by
    by_contra hcon
    push Not at hcon
    exact hσ₀1 (Equiv.ext hcon)
  set c := (π g₁).cycleOf z
  have hcyc : c.IsCycle := isCycle_cycleOf _ hz
  have hcd : c.support.card = d := by
    have h1 : orderOf c ∣ d := hσ₀ord ▸ orderOf_cycleOf_dvd_orderOf (π g₁) z
    have h2 : c.support.card ∣ d := hcyc.orderOf ▸ h1
    rcases (Nat.dvd_prime h.d_prime).1 h2 with h3 | h3
    · exact absurd h3 (by have := hcyc.two_le_card_support; omega)
    · exact h3
  have hcalt : c ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, hcyc.sign, hcd]
    have hodd : Odd d := h.d_prime.odd_of_ne_two h.d_ne_two
    rw [hodd.neg_one_pow]
    rfl
  obtain ⟨k, hk⟩ := hψsurj c hcalt
  have hkd : IsPGroup d (Subgroup.zpowers (k : X)) := by
    have hko : orderOf (k : X) = d := by
      rw [Subgroup.orderOf_coe, ← orderOf_injective ψ hψinj k, hk, hcyc.orderOf, hcd]
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hko, pow_one])
  obtain ⟨S, hkS⟩ := hkd.exists_le_sylow
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf d (S : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  obtain ⟨y, -, hy⟩ := h.sylow.exists_mem_conj hSsyl
  set g : X := y⁻¹ * k * y
  have hgD : g ∈ D := (hy k).mp (hkS (Subgroup.mem_zpowers _))
  have hσ : π g = (π y)⁻¹ * c * (π y)⁻¹⁻¹ := by
    rw [show g = y⁻¹ * (k : X) * y from rfl, map_mul, map_mul, map_inv, hπK, hk, inv_inv]
  have hσc : (π g).IsCycle := by rw [hσ]; exact hcyc.conj
  have hσd : (π g).support.card = d := by rw [hσ, card_support_conj, hcd]
  have hg1 : g ≠ 1 := by
    intro hg
    have : π g = 1 := by rw [hg, map_one]
    rw [this, Equiv.Perm.support_one, Finset.card_empty] at hσd
    exact h.d_prime.ne_zero hσd.symm
  have hσalt : π g ∈ alternatingGroup (Fin n) := by
    rw [hσ]
    exact (alternatingGroup.normal (α := Fin n)).conj_mem c hcalt _
  have hσG : π g ∈ G' := by
    obtain ⟨k', hk'⟩ := hψsurj (π g) hσalt
    rw [← hk']
    refine hG'mem k' (h.mem_of_commute_D hgD hg1 (le_sup_left (a := K) k'.2) ?_)
    exact hcomm g k' (by rw [hk'])
  have hσcent : ∀ τ ∈ alternatingGroup (Fin n), τ * π g = π g * τ → τ ∈ G' :=
    hcentG g fun c' hgc => h.mem_of_commute_D hgD hg1 (le_sup_left (a := K) c'.2) hgc
  have hle := hperm G' R hRp hRc hRcomm hRexp hRG (π g) hσc hσd hσG hσcent
  refine h.not_K_le fun x hx => ?_
  obtain ⟨k', hk'X, hk'⟩ := hle (hψmem ⟨x, hx⟩)
  have := hψinj hk'
  rw [this] at hk'X
  exact hk'X

theorem false_of_threeNineHyp_alt {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    {p d : ℕ} (h : ThreeNineHyp K E D X₁ p d) (hp5 : 5 ≤ p) {n : ℕ}
    (hn : n = 2 * p ∨ n = 3 * p) (φ : ↥K ≃* alternatingGroup (Fin n)) : False :=
  have : Fact p.Prime := ⟨h.prime⟩
  false_of_threeNineHyp_alt_of_perm h (by omega) (by omega) φ
    fun _ _ hRp hRc hRcomm _ hRG _ hσc hσd hσG hσG' =>
      alternatingGroup_le_of_plane_of_isCycle hp5 h.d_prime h.d_ne (by simpa using hn) hRp hRc
        hRcomm (fun r hr hr1 => altOn_fixed_le_of_centralizer (hRG r hr hr1)) hσc hσd hσG
        (altOn_fixed_le_of_centralizer hσG')

theorem threeNineFiveAlt_holds : ThreeNineFiveAlt := by
  intro X _ _ K E D X₁ p d h hp5 hK
  rcases hK with hK | hK
  · obtain ⟨φ⟩ := hK
    exact false_of_threeNineHyp_alt h hp5 (Or.inl rfl) φ
  · obtain ⟨φ⟩ := hK
    exact false_of_threeNineHyp_alt h hp5 (Or.inr rfl) φ

end CFSG.LocalAnalysis.AGL81I.Section3
