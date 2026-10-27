module

public import CFSG.CGT.Foote82.Lemma62Min
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure Core62 (G L K : Subgroup (GLV V)) (s : GLV V) (p : ℕ) : Prop where
  conf : Conf62 G (Subgroup.zpowers s) L K
  s_ord : orderOf s = 2
  min : Min62 (Subgroup.zpowers s) L K
  KL : ⁅K, L⁆ = K
  prime : p.Prime
  p_ne : p ≠ 2
  pgroup : IsPGroup p K
  frat_L : ⁅frat K, L⁆ = ⊥
  frat_center : frat K ≤ Subgroup.centralizer (K : Set (GLV V))
  fix : fixedSpace K = ⊥
  inverts : ∀ k ∈ K, s * k * s⁻¹ * k ∈ frat K

private theorem exists_central_involution {S : Subgroup (GLV V)} (hS : IsPGroup 2 S)
    (hne : S ≠ ⊥) : ∃ s ∈ S, (∀ t ∈ S, t * s = s * t) ∧ orderOf s = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hne
  haveI : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center S) := hS.to_subgroup _
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hZ).1 inferInstance
  have h2 : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨((z : S) : GLV V), (z : S).2, fun t ht => ?_, ?_⟩
  · have := Subgroup.mem_center_iff.1 z.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  · calc orderOf (((z : S) : GLV V)) = orderOf (z : S) := Subgroup.orderOf_coe _
      _ = orderOf z := Subgroup.orderOf_coe _
      _ = 2 := hz

section PlusMinus

variable {G : Type*} [Group G]

private structure PMData (K Φ : Subgroup G) (σ : G ≃* G) : Prop where
  Φ_le : Φ ≤ K
  Φ_norm : ∀ a ∈ K, ∀ φ ∈ Φ, a * φ * a⁻¹ ∈ Φ
  comm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ Φ
  σ_K : ∀ k ∈ K, σ k ∈ K
  σ_Φ : ∀ φ ∈ Φ, σ φ ∈ Φ
  σ_sq : ∀ g, σ (σ g) = g

private def PMData.plus {K Φ : Subgroup G} {σ : G ≃* G} (h : PMData K Φ σ) : Subgroup G where
  carrier := {k | k ∈ K ∧ σ k * k⁻¹ ∈ Φ}
  mul_mem' := by
    rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
    refine ⟨K.mul_mem haK hbK, ?_⟩
    have e : σ (a * b) * (a * b)⁻¹ = (σ a * (σ b * b⁻¹) * (σ a)⁻¹) * (σ a * a⁻¹) := by
      simp only [map_mul, mul_inv_rev]
      group
    rw [e]
    exact Φ.mul_mem (h.Φ_norm _ (h.σ_K a haK) _ hb) ha
  one_mem' := ⟨K.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨haK, ha⟩
    refine ⟨K.inv_mem haK, ?_⟩
    have e : σ a⁻¹ * (a⁻¹)⁻¹ = (a⁻¹ * (σ a * a⁻¹) * (a⁻¹)⁻¹)⁻¹ := by
      simp only [map_inv, inv_inv, mul_inv_rev]
      group
    rw [e]
    exact Φ.inv_mem (h.Φ_norm _ (K.inv_mem haK) _ ha)

private def PMData.minus {K Φ : Subgroup G} {σ : G ≃* G} (h : PMData K Φ σ) : Subgroup G where
  carrier := {k | k ∈ K ∧ σ k * k ∈ Φ}
  mul_mem' := by
    rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
    refine ⟨K.mul_mem haK hbK, ?_⟩
    have e : σ (a * b) * (a * b) =
        (σ a * (σ b * a * (σ b)⁻¹ * a⁻¹) * (σ a)⁻¹) * (σ a * a) * (σ b * b) := by
      simp only [map_mul]
      group
    rw [e]
    exact Φ.mul_mem (Φ.mul_mem
      (h.Φ_norm _ (h.σ_K a haK) _ (h.comm _ (h.σ_K b hbK) _ haK)) ha) hb
  one_mem' := ⟨K.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨haK, ha⟩
    refine ⟨K.inv_mem haK, ?_⟩
    have e : σ a⁻¹ * a⁻¹ = ((σ a)⁻¹ * (σ a * a) * ((σ a)⁻¹)⁻¹)⁻¹ := by
      simp only [map_inv, inv_inv, mul_inv_rev]
      group
    rw [e]
    exact Φ.inv_mem (h.Φ_norm _ (K.inv_mem (h.σ_K a haK)) _ ha)

variable {K Φ : Subgroup G} {σ : G ≃* G}

private theorem PMData.plus_le (h : PMData K Φ σ) : h.plus ≤ K := fun _ hk => hk.1

private theorem PMData.minus_le (h : PMData K Φ σ) : h.minus ≤ K := fun _ hk => hk.1

private theorem PMData.Φ_le_plus (h : PMData K Φ σ) : Φ ≤ h.plus := fun φ hφ =>
  ⟨h.Φ_le hφ, Φ.mul_mem (h.σ_Φ φ hφ) (Φ.inv_mem hφ)⟩

private theorem PMData.conj_mem_plus (h : PMData K Φ σ) {g : G}
    (hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hgΦ : ∀ φ ∈ Φ, g * φ * g⁻¹ ∈ Φ)
    (hgσ : ∀ x, σ (g * x * g⁻¹) = g * σ x * g⁻¹) :
    ∀ k ∈ h.plus, g * k * g⁻¹ ∈ h.plus := by
  rintro k ⟨hkK, hk⟩
  refine ⟨hgK k hkK, ?_⟩
  have e : σ (g * k * g⁻¹) * (g * k * g⁻¹)⁻¹ = g * (σ k * k⁻¹) * g⁻¹ := by
    rw [hgσ]
    group
  rw [e]
  exact hgΦ _ hk

private theorem PMData.conj_mem_minus (h : PMData K Φ σ) {g : G}
    (hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hgΦ : ∀ φ ∈ Φ, g * φ * g⁻¹ ∈ Φ)
    (hgσ : ∀ x, σ (g * x * g⁻¹) = g * σ x * g⁻¹) :
    ∀ k ∈ h.minus, g * k * g⁻¹ ∈ h.minus := by
  rintro k ⟨hkK, hk⟩
  refine ⟨hgK k hkK, ?_⟩
  have e : σ (g * k * g⁻¹) * (g * k * g⁻¹) = g * (σ k * k) * g⁻¹ := by
    rw [hgσ]
    group
  rw [e]
  exact hgΦ _ hk

private theorem PMData.le_sup (h : PMData K Φ σ) {p : ℕ} (hp : Odd p)
    (hpow : ∀ k ∈ K, k ^ p ∈ Φ) : K ≤ h.plus ⊔ h.minus := by
  intro k hk
  obtain ⟨x, hx⟩ : ∃ x, x = σ k := ⟨_, rfl⟩
  have hxK : x ∈ K := hx ▸ h.σ_K k hk
  have hσx : σ x = k := by rw [hx, h.σ_sq]
  have h1 : k * x ∈ h.plus := by
    refine ⟨K.mul_mem hk hxK, ?_⟩
    have e : σ (k * x) * (k * x)⁻¹ = x * k * x⁻¹ * k⁻¹ := by
      rw [map_mul, hσx, ← hx]
      group
    rw [e]
    exact h.comm x hxK k hk
  have h2 : k * x⁻¹ ∈ h.minus := by
    refine ⟨K.mul_mem hk (K.inv_mem hxK), ?_⟩
    have e : σ (k * x⁻¹) * (k * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hσx, ← hx]
      group
    rw [e]
    exact Φ.one_mem
  have h3 : x * k⁻¹ * x⁻¹ * k ∈ Φ := by
    simpa using h.comm x hxK k⁻¹ (K.inv_mem hk)
  have hkk : k * k ∈ h.plus ⊔ h.minus := by
    have e : k * k = (k * x) * (k * x⁻¹) * (x * k⁻¹ * x⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
      (Subgroup.mem_sup_right h2)) (Subgroup.mem_sup_left (h.Φ_le_plus h3))
  obtain ⟨m, hm⟩ := hp
  have hpk : k ^ (p + 1) ∈ h.plus ⊔ h.minus := by
    have e : k ^ (p + 1) = (k * k) ^ (m + 1) := by
      rw [hm, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul, sq]
    rw [e]
    exact Subgroup.pow_mem _ hkk _
  have e : k = (k ^ p)⁻¹ * k ^ (p + 1) := by
    rw [pow_succ, inv_mul_cancel_left]
  rw [e]
  exact Subgroup.mul_mem _
    (Subgroup.inv_mem _ (Subgroup.mem_sup_left (h.Φ_le_plus (hpow k hk)))) hpk

private theorem PMData.fixed_of_plus {p : ℕ} (h : PMData K Φ σ) (hp : Odd p)
    (hpg : ∀ t ∈ K, ∃ N : ℕ, t ^ p ^ N = 1)
    (hfrat : ∀ H : Subgroup G, H ≤ K → H ⊔ Φ = K → H = K)
    (hplus : ∀ k ∈ K, σ k * k⁻¹ ∈ Φ) : ∀ k ∈ K, σ k = k := by
  let H : Subgroup G :=
    { carrier := {g | g ∈ K ∧ σ g = g}
      mul_mem' := fun {a b} ha hb => ⟨K.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      one_mem' := ⟨K.one_mem, map_one σ⟩
      inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  have hsup : H ⊔ Φ = K := by
    refine le_antisymm (sup_le (fun g hg => hg.1) h.Φ_le) fun k hk => ?_
    obtain ⟨t, ht⟩ : ∃ t, t = σ k * k⁻¹ := ⟨_, rfl⟩
    have htΦ : t ∈ Φ := ht ▸ hplus k hk
    have htK : t ∈ K := h.Φ_le htΦ
    have hσk : σ k = t * k := by rw [ht]; group
    have hσt : σ t = t⁻¹ := by
      rw [ht, map_mul, map_inv, h.σ_sq]
      group
    obtain ⟨N, hN⟩ := hpg t htK
    obtain ⟨m, hm⟩ : Odd (p ^ N) := hp.pow
    obtain ⟨r, hr⟩ : ∃ r, r = t ^ (m + 1) := ⟨_, rfl⟩
    have hrr : r * r = t := by
      rw [hr, ← pow_add, show m + 1 + (m + 1) = p ^ N + 1 by omega, pow_succ, hN, one_mul]
    have hσr : σ r = r⁻¹ := by rw [hr, map_pow, hσt, inv_pow]
    have hrΦ : r ∈ Φ := hr ▸ Φ.pow_mem htΦ _
    have hc : r * k ∈ H := by
      refine ⟨K.mul_mem (h.Φ_le hrΦ) hk, ?_⟩
      rw [map_mul, hσr, hσk, ← hrr]
      group
    have e : k = r⁻¹ * (r * k) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hrΦ))
      (Subgroup.mem_sup_left hc)
  have hHK : H = K := hfrat H (fun g hg => hg.1) hsup
  intro k hk
  have hkH : k ∈ H := hHK ▸ hk
  exact hkH.2

private theorem mem_of_mul_self_mem {p : ℕ} (hp : Odd p) {Φ : Subgroup G} {k : G}
    (hkk : k * k ∈ Φ) (hkp : k ^ p ∈ Φ) : k ∈ Φ := by
  obtain ⟨j, hj⟩ := hp
  have e : k = ((k * k) ^ j)⁻¹ * k ^ p := by
    rw [hj, pow_succ, ← sq, ← pow_mul, pow_mul', sq]
    group
  rw [e]
  exact Φ.mul_mem (Φ.inv_mem (Φ.pow_mem hkk _)) hkp

end PlusMinus

private theorem le_normalizer_of_conj_mem {T H : Subgroup (GLV V)}
    (h : ∀ g ∈ T, ∀ n ∈ H, g * n * g⁻¹ ∈ H) : T ≤ Subgroup.normalizer (H : Set (GLV V)) := by
  intro g hg n
  refine ⟨fun hn => h g hg n hn, fun hn => ?_⟩
  have := h g⁻¹ (T.inv_mem hg) _ hn
  have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
  rwa [e] at this

theorem exists_core {G S L K : Subgroup (GLV V)} (hc : Conf62 G S L K)
    (IH : ∀ G' S' L' K' : Subgroup (GLV V), Conf62 G' S' L' K' → Nat.card K' < Nat.card K →
      ⁅K', L'⁆ = ⊥)
    (hne : ⁅K, L⁆ ≠ ⊥) (hfix : fixedSpace K = ⊥) :
    ∃ (G' : Subgroup (GLV V)) (s : GLV V) (p : ℕ), Core62 G' L K s p := by
  have hmin : Min62 S L K := fun K' hK' hSK' hLK' =>
    IH G S L K' ⟨hc.setup, hK'.le.trans hc.K_le,
      Odd.of_dvd_nat hc.odd (Subgroup.card_dvd_of_le hK'.le), hSK', hLK'⟩
      (Subgroup.card_lt_of_lt hK')
  obtain ⟨hKL, ⟨p, hp, hp2, hpg⟩, hΦL, hΦc⟩ := hc.min_structure hmin hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpg' : ∀ t ∈ K, ∃ N : ℕ, t ^ p ^ N = 1 := fun t ht => by
    obtain ⟨N, hN⟩ := hpg ⟨t, ht⟩
    exact ⟨N, by simpa using congrArg Subtype.val hN⟩
  have hS : S ≠ ⊥ := by
    intro hS
    refine hne (Setup6.commutator_eq_bot_of_le_centralizer hc.setup hc.odd
      (le_inf hc.K_le fun k _ => Subgroup.mem_centralizer_iff.2 fun h hh => ?_) hc.L_le)
    have : h = 1 := by
      rw [hS] at hh
      exact Subgroup.mem_bot.1 hh
    rw [this, one_mul, mul_one]
  obtain ⟨s, hsS, hsc, hs2⟩ := exists_central_involution hc.setup.isPGroup hS
  have hss : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs2, sq] at this
  have hss' : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hss, inv_one]
  have hLs : ∀ l ∈ L, l * s = s * l := fun l hl =>
    ((Subgroup.mem_centralizer_iff.1 (hc.setup.component.1 hl).2) s hsS).symm
  let σ : GLV V ≃* GLV V := MulAut.conj s
  have hσ : ∀ x, σ x = s * x * s⁻¹ := fun x => MulAut.conj_apply s x
  have hΦn : ∀ g ∈ Subgroup.normalizer (K : Set (GLV V)), ∀ φ ∈ frat K,
      g * φ * g⁻¹ ∈ frat K := fun g hg φ hφ =>
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_frat K hg) φ).1 hφ
  have hKn : ∀ g ∈ Subgroup.normalizer (K : Set (GLV V)), ∀ k ∈ K, g * k * g⁻¹ ∈ K :=
    fun g hg k hk => (Subgroup.mem_normalizer_iff.1 hg k).1 hk
  have hsn : s ∈ Subgroup.normalizer (K : Set (GLV V)) := hc.S_le hsS
  have hPM : PMData K (frat K) σ :=
    { Φ_le := frat_le K
      Φ_norm := fun a ha φ hφ => hΦn a (Subgroup.le_normalizer ha) φ hφ
      comm := fun a ha b hb => by
        have := commutator_le_frat hpg (Subgroup.commutator_mem_commutator ha hb)
        simpa [commutatorElement_def] using this
      σ_K := fun k hk => by rw [hσ]; exact hKn s hsn k hk
      σ_Φ := fun φ hφ => by rw [hσ]; exact hΦn s hsn φ hφ
      σ_sq := fun g => by
        rw [hσ, hσ]
        calc s * (s * g * s⁻¹) * s⁻¹ = (s * s) * g * (s⁻¹ * s⁻¹) := by group
          _ = g := by rw [hss, hss', one_mul, mul_one] }
  have hconjσ : ∀ g : GLV V, g * s = s * g → ∀ x, σ (g * x * g⁻¹) = g * σ x * g⁻¹ := by
    intro g hg x
    rw [hσ, hσ]
    have hsg : s * g = g * s := hg.symm
    calc s * (g * x * g⁻¹) * s⁻¹ = (s * g) * x * (s * g)⁻¹ := by group
      _ = (g * s) * x * (g * s)⁻¹ := by rw [hsg]
      _ = g * (s * x * s⁻¹) * g⁻¹ := by group
  have hnormT : ∀ T : Subgroup (GLV V), T ≤ Subgroup.normalizer (K : Set (GLV V)) →
      (∀ g ∈ T, g * s = s * g) →
      T ≤ Subgroup.normalizer (hPM.plus : Set (GLV V)) ∧
        T ≤ Subgroup.normalizer (hPM.minus : Set (GLV V)) := fun T hTK hTs =>
    ⟨le_normalizer_of_conj_mem fun g hg => hPM.conj_mem_plus (hKn g (hTK hg))
        (hΦn g (hTK hg)) (hconjσ g (hTs g hg)),
      le_normalizer_of_conj_mem fun g hg => hPM.conj_mem_minus (hKn g (hTK hg))
        (hΦn g (hTK hg)) (hconjσ g (hTs g hg))⟩
  have hdich : hPM.plus = K ∨ hPM.minus = K := by
    by_contra hcon
    obtain ⟨hp1, hm1⟩ := not_or.1 hcon
    obtain ⟨hSp, hSm⟩ := hnormT S hc.S_le hsc
    obtain ⟨hLp, hLm⟩ := hnormT L hc.L_le hLs
    have h1 := hmin _ (lt_of_le_of_ne hPM.plus_le hp1) hSp hLp
    have h2 := hmin _ (lt_of_le_of_ne hPM.minus_le hm1) hSm hLm
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2 ⊢
    exact (hPM.le_sup hpodd fun k hk => pow_mem_frat hpg hk).trans (sup_le h1 h2)
  rcases hdich with hplus | hminus
  ·
    exfalso
    have hplus' : ∀ k ∈ K, σ k * k⁻¹ ∈ frat K := fun k hk =>
      (show k ∈ hPM.plus by rw [hplus]; exact hk).2
    have hfixσ := hPM.fixed_of_plus hpodd hpg' (fun H hH hsup => eq_of_sup_frat hH hsup)
      hplus'
    have hcent : ∀ k ∈ K, k * s = s * k := fun k hk => by
      have h1 := hfixσ k hk
      rw [hσ] at h1
      calc k * s = (s * k * s⁻¹) * s := by rw [h1]
        _ = s * k := by group
    have hinvX : Invariant K (commSpace (Subgroup.zpowers s) ⊤) := by
      intro k hk w hw
      have hle : commSpace (Subgroup.zpowers s) ⊤ ≤
          (commSpace (Subgroup.zpowers s) ⊤).comap (k : V →ₗ[ZMod 2] V) := by
        refine commSpace_le_iff.2 fun g hg u _ => ?_
        show k (g u - u) ∈ commSpace (Subgroup.zpowers s) ⊤
        have hkg : k * g = g * k := by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
          exact ((Commute.zpow_right (show Commute k s from hcent k hk) i)).eq
        have e : k (g u - u) = g (k u) - k u := by
          rw [map_sub]
          congr 1
          have := congrArg (fun f : GLV V => f u) hkg
          simpa using this
        rw [e]
        exact sub_mem_commSpace hg Submodule.mem_top
      exact hle hw
    have hKfix := fixes_of_commutator hinvX (hc.setup.lemma61 hsS).1
    have hX : commSpace (Subgroup.zpowers s) ⊤ = ⊥ := by
      rw [eq_bot_iff, ← hfix]
      intro w hw k hk
      exact hKfix k (by rw [hKL]; exact hk) w hw
    have hs1 : s = 1 := by
      ext v
      have := commSpace_eq_bot_iff.1 hX s (Subgroup.mem_zpowers s) v Submodule.mem_top
      simpa using this
    rw [hs1, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  ·
    have hinv : ∀ k ∈ K, s * k * s⁻¹ * k ∈ frat K := fun k hk => by
      have h2 := (show k ∈ hPM.minus by rw [hminus]; exact hk).2
      rwa [hσ] at h2
    have hKs : ∀ k ∈ K, s * k = k * s → k ∈ frat K := fun k hk hks => by
      refine mem_of_mul_self_mem hpodd ?_ (pow_mem_frat hpg hk)
      have h2 := hinv k hk
      rwa [show s * k * s⁻¹ = k from by rw [hks]; group] at h2
    have hΦc' : ∀ φ ∈ frat K, ∀ n ∈ L, φ * n = n * φ := fun φ hφ n hn =>
      ((Subgroup.mem_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hΦL hφ)) n hn).symm
    have hzS : (Subgroup.zpowers s : Set (GLV V)) ⊆ (S : Set (GLV V)) :=
      SetLike.coe_subset_coe.2 (Subgroup.zpowers_le.2 hsS)
    have hLcen : L ≤ Subgroup.centralizer (Subgroup.zpowers s : Set (GLV V)) := fun l hl =>
      Subgroup.centralizer_le hzS (hc.setup.component.1 hl).2
    have hzK : Subgroup.zpowers s ≤ Subgroup.normalizer (K : Set (GLV V)) :=
      Subgroup.zpowers_le.2 hsn
    have hzL : Subgroup.zpowers s ≤ Subgroup.centralizer (L : Set (GLV V)) :=
      Subgroup.le_centralizer_iff.2 hLcen
    have hAK : Subgroup.zpowers s ⊔ L ≤ Subgroup.normalizer (K : Set (GLV V)) :=
      sup_le hzK hc.L_le
    have hAN : Subgroup.zpowers s ⊔ L ≤ Subgroup.normalizer (L : Set (GLV V)) :=
      sup_le (hzL.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
    have hAcen : Subgroup.zpowers s ⊔ L ≤ Subgroup.centralizer ({s} : Set (GLV V)) := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (hLcen.trans (Subgroup.centralizer_le ?_))
      · exact Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]
      · exact Set.singleton_subset_iff.2 (Subgroup.mem_zpowers s)
    have hAs : ∀ u ∈ Subgroup.zpowers s ⊔ L, u * s = s * u := fun u hu =>
      ((Subgroup.mem_centralizer_iff.1 (hAcen hu)) s rfl).symm
    have hMnorm : ∀ g ∈ (Subgroup.zpowers s ⊔ L ⊔ K) ⊓
        Subgroup.centralizer (Subgroup.zpowers s : Set (GLV V)), ∀ n ∈ L, g * n * g⁻¹ ∈ L := by
      intro g hg n hn
      have hgs : s * g = g * s :=
        (Subgroup.mem_centralizer_iff.1 hg.2) s (Subgroup.mem_zpowers s)
      have hg' : g ∈ ((Subgroup.zpowers s ⊔ L : Subgroup (GLV V)) : Set (GLV V)) *
          (K : Set (GLV V)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ K hAK]
        exact hg.1
      obtain ⟨u, hu, k, hk, rfl⟩ := hg'
      have hus : u * s = s * u := hAs u hu
      have hus' : u⁻¹ * s = s * u⁻¹ := (Commute.inv_left (show Commute u s from hus)).eq
      have hks : s * k = k * s := by
        have h1 : s * (u * k) = u * k * s := hgs
        calc s * k = s * (u⁻¹ * (u * k)) := by group
          _ = (s * u⁻¹) * (u * k) := by group
          _ = (u⁻¹ * s) * (u * k) := by rw [hus']
          _ = u⁻¹ * (s * (u * k)) := by group
          _ = u⁻¹ * (u * k * s) := by rw [h1]
          _ = k * s := by group
      have hkn : k * n = n * k := hΦc' k (hKs k hk hks) n hn
      have e : u * k * n * (u * k)⁻¹ = u * n * u⁻¹ := by
        calc u * k * n * (u * k)⁻¹ = u * (k * n) * k⁻¹ * u⁻¹ := by group
          _ = u * (n * k) * k⁻¹ * u⁻¹ := by rw [hkn]
          _ = u * n * u⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hAN hu) n).1 hn
    have hnorm : (L.subgroupOf ((Subgroup.zpowers s ⊔ L ⊔ K) ⊓
        Subgroup.centralizer (Subgroup.zpowers s : Set (GLV V)))).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hMnorm g.1 g.2 n hn
    have hconf : Conf62 (Subgroup.zpowers s ⊔ L ⊔ K) (Subgroup.zpowers s) L K :=
      { setup :=
          { S_le := le_sup_left.trans le_sup_left
            isPGroup := hc.setup.isPGroup.to_le (Subgroup.zpowers_le.2 hsS)
            component :=
              ⟨le_inf (le_sup_right.trans le_sup_left) hLcen,
                IsSubnormal.step (le_inf (le_sup_right.trans le_sup_left) hLcen) hnorm
                  (IsSubnormal.refl _), hc.setup.component.2.2⟩
            irrTilde := hc.setup.irrTilde }
        K_le := le_sup_right
        odd := hc.odd
        S_le := hzK
        L_le := hc.L_le }
    refine ⟨Subgroup.zpowers s ⊔ L ⊔ K, s, p,
      ⟨hconf, hs2, ?_, hKL, hp, hp2, hpg, hΦL, hΦc, hfix, hinv⟩⟩
    intro K' hK' hSK' hLK'
    exact IH _ (Subgroup.zpowers s) L K' ⟨hconf.setup, hK'.le.trans hconf.K_le,
      Odd.of_dvd_nat hc.odd (Subgroup.card_dvd_of_le hK'.le), hSK', hLK'⟩
      (Subgroup.card_lt_of_lt hK')

end CFSG.CGT.Foote82
