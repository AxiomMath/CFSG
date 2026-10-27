module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLineComp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwE6FrameLayer

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.SeitzPlane
  CFSG.HardMathSupport.Lang.TwE6Step3 CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twE6Emb twE6Emb_mem twE6Emb_fixed card_fixSubfield_twisted
  e6_tw_rational lang_conjugator_twisted_gen rootSpan_commute_of_orth)
open scoped Matrix

set_option linter.unusedSectionVars false

section Abstract

variable {G M : Type*} [Group G] [Group M]

theorem twLine_mem_centralizer_singleton {g x : G} :
    x ∈ Subgroup.centralizer {g} ↔ g * x = x * g := by
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

theorem twLine_map_conj_one (X : Subgroup G) :
    X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext x
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem twLine_commute_mul {c d t : G} (hc : d = c * d * c⁻¹) (ht : t * d = d * t) :
    d * (c * t) = c * t * d := by
  calc d * (c * t) = c * d * c⁻¹ * (c * t) := by rw [← hc]
    _ = c * (d * t) := by group
    _ = c * (t * d) := by rw [ht]
    _ = c * t * d := by group

theorem twLine_map_conj_comap (ψ : G →* M) (C : Subgroup G) {g : G} (hg : g ∈ C)
    {X Y : Subgroup M} (h : X.map (MulAut.conj (ψ g)).toMonoidHom = Y) :
    (C ⊓ X.comap ψ).map (MulAut.conj g).toMonoidHom = C ⊓ Y.comap ψ := by
  subst h
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyC, hyX⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_comap.2 (Subgroup.mem_map.2
      ⟨ψ y, Subgroup.mem_comap.1 hyX, ?_⟩)⟩
    · change g * y * g⁻¹ ∈ C
      exact mul_mem (mul_mem hg hyC) (inv_mem hg)
    · change ψ g * ψ y * (ψ g)⁻¹ = ψ (g * y * g⁻¹)
      rw [map_mul, map_mul, map_inv]
  · intro hx
    obtain ⟨hxC, hxY⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨z, hzX, hz⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hxY)
    change ψ g * z * (ψ g)⁻¹ = ψ x at hz
    refine Subgroup.mem_map.2 ⟨g⁻¹ * x * g, Subgroup.mem_inf.2
      ⟨mul_mem (mul_mem (inv_mem hg) hxC) hg, Subgroup.mem_comap.2 ?_⟩, ?_⟩
    · have e : ψ (g⁻¹ * x * g) = z := by
        rw [map_mul, map_mul, map_inv, ← hz]
        group
      rw [e]
      exact hzX
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem twLine_exists_pow {F : Fin 3 → Subgroup M} {m : M}
    (hm : ∀ i, (F i).map (MulAut.conj m).toMonoidHom = F (i + 1)) (k : Fin 3) :
    ∃ j < 3, ∀ i, (F i).map (MulAut.conj (m ^ j)).toMonoidHom = F (i + k) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 1 + 1 := by
    revert k
    decide
  rcases hk with rfl | rfl | rfl
  · refine ⟨0, by norm_num, fun i => ?_⟩
    rw [pow_zero, add_zero, twLine_map_conj_one]
  · refine ⟨1, by norm_num, fun i => ?_⟩
    rw [pow_one, hm]
  · refine ⟨2, by norm_num, fun i => ?_⟩
    rw [pow_two, map_conj_mul_aux, hm, hm, add_assoc]

theorem twLine_comap_commute (ψ : G →* M) (hψ : Function.Injective ψ) (C : Subgroup G)
    {X Y : Subgroup M} (h : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) :
    ∀ x ∈ C ⊓ X.comap ψ, ∀ y ∈ C ⊓ Y.comap ψ, x * y = y * x := by
  intro x hx y hy
  apply hψ
  rw [map_mul, map_mul]
  exact h (ψ x) (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hx).2) (ψ y)
    (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hy).2)

theorem twLine_shift_eq_zero (L : Fin 3 → Subgroup G)
    (hL : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hnab : ∀ i, ∃ a ∈ L i, ∃ b ∈ L i, a * b ≠ b * a) {k : Fin 3}
    (h : ∀ i, L (i + k) = L i) : k = 0 := by
  by_contra hk
  obtain ⟨a, ha, b, hb, hab⟩ := hnab 0
  have h0 : (0 : Fin 3) ≠ 0 + k := by
    rw [zero_add]
    exact Ne.symm hk
  rw [← h 0] at hb
  exact hab (hL 0 (0 + k) h0 a ha b hb)

theorem twLine_mul_mem_sup {T : Subgroup G} {L : Fin 3 → Subgroup G} {t l₀ l₁ l₂ : G}
    (ht : t ∈ T) (h₀ : l₀ ∈ L 0) (h₁ : l₁ ∈ L 1) (h₂ : l₂ ∈ L 2) :
    t * l₀ * l₁ * l₂ ∈ T ⊔ ⨆ i, L i :=
  mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left ht)
    (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 0 h₀)))
    (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1 h₁)))
    (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 2 h₂))

theorem twLine_exists_ne_comm {P : Subgroup G} (h : CFSG.IsQuasisimple P) :
    ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, a.2, b, b.2, fun e => hab ?_⟩
  have e' : a * b = b * a := Subtype.ext e
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e']

theorem twLine_map_comap_eq (ψ : G →* M) (C : Subgroup G) (X P : Subgroup M)
    (h1 : ∀ x ∈ C, ψ x ∈ X → ψ x ∈ P) (h2 : P ≤ C.map ψ) (h3 : P ≤ X) :
    (C ⊓ X.comap ψ).map ψ = P := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h1 x (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hx).2)
  · obtain ⟨x, hxC, rfl⟩ := h2 hy
    exact ⟨x, Subgroup.mem_inf.2 ⟨hxC, Subgroup.mem_comap.2 (h3 hy)⟩, rfl⟩

theorem twLine_conj_shift_comap (ψ : G →* M) (C : Subgroup G) (F : Fin 3 → Subgroup M)
    {Z : Subgroup G} (hZC : Z ≤ C)
    (hshift : ∀ g ∈ Z, ∃ k : Fin 3, ∀ i, (F i).map (MulAut.conj (ψ g)).toMonoidHom = F (i + k))
    {g : G} (hg : g ∈ Z) :
    ∃ k : Fin 3, ∀ i, (C ⊓ (F i).comap ψ).map (MulAut.conj g).toMonoidHom =
      C ⊓ (F (i + k)).comap ψ := by
  obtain ⟨k, hk⟩ := hshift g hg
  exact ⟨k, fun i => twLine_map_conj_comap ψ C (hZC hg) (hk i)⟩

theorem twLine_shift_zero_comap (ψ : G →* M) (hψ : Function.Injective ψ) (C : Subgroup G)
    (F : Fin 3 → Subgroup M) (H : Subgroup M) {Z : Subgroup G}
    (hF : ∀ i j, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, a * b = b * a)
    (hnab : ∀ i, ∃ a ∈ C ⊓ (F i).comap ψ, ∃ b ∈ C ⊓ (F i).comap ψ, a * b ≠ b * a)
    (hZC : Z ≤ C)
    (hshift : ∀ g ∈ Z, ∃ k : Fin 3, ∀ i, (F i).map (MulAut.conj (ψ g)).toMonoidHom = F (i + k))
    (hsplit : ∀ g ∈ Z, (∀ i, (F i).map (MulAut.conj (ψ g)).toMonoidHom = F i) →
      ∃ t ∈ C ⊓ H.comap ψ, ∃ l₀ ∈ C ⊓ (F 0).comap ψ, ∃ l₁ ∈ C ⊓ (F 1).comap ψ,
        ∃ l₂ ∈ C ⊓ (F 2).comap ψ, g = t * l₀ * l₁ * l₂)
    {g : G} (hg : g ∈ Z)
    (hfix : ∀ i, (C ⊓ (F i).comap ψ).map (MulAut.conj g).toMonoidHom = C ⊓ (F i).comap ψ) :
    g ∈ C ⊓ H.comap ψ ⊔ ⨆ i, C ⊓ (F i).comap ψ := by
  obtain ⟨k, hk⟩ := hshift g hg
  have hk0 : k = 0 := twLine_shift_eq_zero (fun i => C ⊓ (F i).comap ψ)
    (fun i j hij => twLine_comap_commute ψ hψ C (hF i j hij)) hnab fun i => by
      show C ⊓ (F (i + k)).comap ψ = C ⊓ (F i).comap ψ
      rw [← twLine_map_conj_comap ψ C (hZC hg) (hk i), hfix i]
  subst hk0
  obtain ⟨t, ht, l₀, hl₀, l₁, hl₁, l₂, hl₂, rfl⟩ := hsplit g hg fun i => by rw [hk i, add_zero]
  exact twLine_mul_mem_sup (L := fun i => C ⊓ (F i).comap ψ) ht hl₀ hl₁ hl₂

theorem twLine_centralizer_mul_comap (ψ : G →* M) (C : Subgroup G) (F : Fin 3 → Subgroup M)
    (H : Subgroup M) {Z : Subgroup G} {n : G} (hnZ : n ∈ Z)
    (hn : ∀ i, (F i).map (MulAut.conj (ψ n)).toMonoidHom = F (i + 1))
    (hshift : ∀ g ∈ Z, ∃ k : Fin 3, ∀ i, (F i).map (MulAut.conj (ψ g)).toMonoidHom = F (i + k))
    (hsplit : ∀ g ∈ Z, (∀ i, (F i).map (MulAut.conj (ψ g)).toMonoidHom = F i) →
      ∃ t ∈ C ⊓ H.comap ψ, ∃ l₀ ∈ C ⊓ (F 0).comap ψ, ∃ l₁ ∈ C ⊓ (F 1).comap ψ,
        ∃ l₂ ∈ C ⊓ (F 2).comap ψ, g = t * l₀ * l₁ * l₂)
    {g : G} (hg : g ∈ Z) :
    ∃ t ∈ C ⊓ H.comap ψ, ∃ l₀ ∈ C ⊓ (F 0).comap ψ, ∃ l₁ ∈ C ⊓ (F 1).comap ψ,
      ∃ l₂ ∈ C ⊓ (F 2).comap ψ, ∃ k < 3, g = t * l₀ * l₁ * l₂ * n ^ k := by
  obtain ⟨k, hk⟩ := hshift g hg
  obtain ⟨j, hj3, hpow⟩ := twLine_exists_pow hn k
  have hfix : ∀ i, (F i).map (MulAut.conj (ψ (g * (n ^ j)⁻¹))).toMonoidHom = F i := by
    intro i
    have h1 : (F i).map (MulAut.conj (ψ n ^ j)⁻¹).toMonoidHom = F (i - k) := by
      have h2 := hpow (i - k)
      rw [sub_add_cancel] at h2
      rw [← h2, twLine_map_conj_inv_map]
    rw [map_mul, map_inv, map_pow, map_conj_mul_aux, h1, hk, sub_add_cancel]
  obtain ⟨t, ht, l₀, hl₀, l₁, hl₁, l₂, hl₂, he⟩ :=
    hsplit _ (mul_mem hg (inv_mem (pow_mem hnZ _))) hfix
  exact ⟨t, ht, l₀, hl₀, l₁, hl₁, l₂, hl₂, j, hj3, by rw [← he, inv_mul_cancel_right]⟩

theorem twLine_centralizer_eq_comap (ψ : G →* M) (hψ : Function.Injective ψ) (C : Subgroup G)
    (F : Fin 3 → Subgroup M) (H : Subgroup M) {h₀ n : G}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hh₀H : ψ h₀ ∈ H)
    (hcen : ∀ i, ∀ a ∈ F i, ψ h₀ * a = a * ψ h₀) (hnC : n ∈ C) (hnh : h₀ * n = n * h₀)
    (hmul : ∀ g ∈ C ⊓ Subgroup.centralizer {h₀}, ∃ t ∈ C ⊓ H.comap ψ,
      ∃ l₀ ∈ C ⊓ (F 0).comap ψ, ∃ l₁ ∈ C ⊓ (F 1).comap ψ, ∃ l₂ ∈ C ⊓ (F 2).comap ψ,
        ∃ k < 3, g = t * l₀ * l₁ * l₂ * n ^ k) :
    C ⊓ Subgroup.centralizer {h₀} =
      (C ⊓ H.comap ψ ⊔ ⨆ i, C ⊓ (F i).comap ψ) ⊔ Subgroup.zpowers n := by
  refine le_antisymm (fun g hg => ?_)
    (sup_le (sup_le (fun t ht => ?_) (iSup_le fun i x hx => ?_))
      (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hnC, twLine_mem_centralizer_singleton.2 hnh⟩)))
  · obtain ⟨t, ht, l₀, hl₀, l₁, hl₁, l₂, hl₂, k, -, rfl⟩ := hmul g hg
    exact mul_mem (Subgroup.mem_sup_left
      (twLine_mul_mem_sup (L := fun i => C ⊓ (F i).comap ψ) ht hl₀ hl₁ hl₂))
      (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers n k))
  · obtain ⟨htC, htH⟩ := Subgroup.mem_inf.1 ht
    refine Subgroup.mem_inf.2 ⟨htC, twLine_mem_centralizer_singleton.2 (hψ ?_)⟩
    rw [map_mul, map_mul]
    exact hH _ hh₀H _ (Subgroup.mem_comap.1 htH)
  · obtain ⟨hxC, hxF⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨hxC, twLine_mem_centralizer_singleton.2 (hψ ?_)⟩
    rw [map_mul, map_mul]
    exact hcen i _ (Subgroup.mem_comap.1 hxF)

theorem twLine_le_normalizer_iSup {L : Fin 3 → Subgroup G} {Z : Subgroup G}
    (hshift : ∀ g ∈ Z, ∃ k : Fin 3, ∀ i, (L i).map (MulAut.conj g).toMonoidHom = L (i + k)) :
    Z ≤ Subgroup.normalizer ((⨆ i, L i : Subgroup G) : Set G) := by
  intro g hg
  obtain ⟨k, hk⟩ := hshift g hg
  refine mem_normalizer_of_map_conj_eq_aux ?_
  rw [Subgroup.map_iSup]
  simp_rw [hk]
  exact (Equiv.addRight k).iSup_comp (g := L)

theorem twLine_comap_le_normalizer (ψ : G →* M) (C : Subgroup G) {H X : Subgroup M}
    (hHX : H ≤ Subgroup.normalizer (X : Set M)) :
    C ⊓ H.comap ψ ≤ Subgroup.normalizer ((C ⊓ X.comap ψ : Subgroup G) : Set G) := by
  intro t ht
  obtain ⟨htC, htH⟩ := Subgroup.mem_inf.1 ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer htC) x
  have h2 := Subgroup.mem_normalizer_iff.1 (hHX (Subgroup.mem_comap.1 htH)) (ψ x)
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
  exact and_congr h1 h2

theorem twLine_center_eq_zpowers {L : Subgroup G} [Finite L] {h : G} (hhL : h ∈ L)
    (hh : ∀ x ∈ L, h * x = x * h) (h3 : h ^ 3 = 1) (h1 : h ≠ 1)
    (hcard : Nat.card (Subgroup.center L) = 3) :
    Subgroup.center L = (Subgroup.zpowers h).subgroupOf L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e : Nat.card ((Subgroup.zpowers h).subgroupOf L) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hhL)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime h3 h1]
  refine (Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hcard.trans e.symm).le).symm
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm]
  exact (Commute.zpow_right (show Commute (y : G) h from (hh y y.2).symm) m).eq

end Abstract

section Main


theorem twLine_psi_mem {K : Type} [Field K] {σ : K ≃+* K}
    {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg₀C : g₀ ∈ adjointGroup Tag.E6 (AlgebraicClosure K)) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ twistedE6RootGroup K σ) :
    twLinePsi K g₀ x ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
  have e : twLinePsi K g₀ x = g₀⁻¹ * twE6Emb K σ (AlgebraicClosure K) ⟨x, hx⟩ * g₀ := by
    rw [twLinePsi_apply]
    rfl
  rw [e]
  exact mul_mem (mul_mem (inv_mem hg₀C) (twE6Emb_mem _)) hg₀C

theorem twLine_psi_fixed {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ} (hσ : ∀ c, σ c = c ^ q)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg₀ : twistE6 (AlgebraicClosure K) Fr g₀ = g₀ * tw6N (AlgebraicClosure K))
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ twistedE6RootGroup K σ) :
    tw6Theta (AlgebraicClosure K) Fr (twLinePsi K g₀ x) = twLinePsi K g₀ x := by
  have hcomm : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
      Fr.comp (algebraMap K (AlgebraicClosure K)) := RingHom.ext fun c => by
    change algebraMap K (AlgebraicClosure K) (σ c) = Fr (algebraMap K (AlgebraicClosure K) c)
    rw [hσ, hFr, map_pow]
  have hF : twistE6 (AlgebraicClosure K) Fr (twE6Emb K σ (AlgebraicClosure K) ⟨x, hx⟩) =
      twE6Emb K σ (AlgebraicClosure K) ⟨x, hx⟩ := twE6Emb_fixed Fr hcomm ⟨x, hx⟩
  have e : twLinePsi K g₀ x = g₀⁻¹ * twE6Emb K σ (AlgebraicClosure K) ⟨x, hx⟩ * g₀ := by
    rw [twLinePsi_apply]
    rfl
  rw [e, tw6Theta_apply, map_mul, map_mul, map_inv, hF, hg₀]
  group

theorem twLine_perfect_le {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg₀C : g₀ ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg₀ : twistE6 (AlgebraicClosure K) Fr g₀ = g₀ * tw6N (AlgebraicClosure K))
    (P : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) (hPfin : Finite P)
    (hPA : P ≤ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hPθ : ∀ x ∈ P, tw6Theta (AlgebraicClosure K) Fr x = x) (hPperf : ⁅P, P⁆ = P) :
    P ≤ (twistedE6RootGroup K σ).map (twLinePsi K g₀) := by
  obtain ⟨kk, hrat, -⟩ := e6_tw_rational hℓ hf K hK σ hσ (AlgebraicClosure K) Fr hFr
  have hXfin : Finite (P.map (MulAut.conj g₀).toMonoidHom) :=
    Finite.of_surjective ((MulAut.conj g₀).toMonoidHom.subgroupMap P)
      ((MulAut.conj g₀).toMonoidHom.subgroupMap_surjective P)
  have hXC : P.map (MulAut.conj g₀).toMonoidHom ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem hg₀C (hPA hz)) (inv_mem hg₀C)
  have hXF : ∀ x ∈ P.map (MulAut.conj g₀).toMonoidHom,
      twistE6 (AlgebraicClosure K) Fr x = x := by
    rintro _ ⟨z, hz, rfl⟩
    have hθz := hPθ z hz
    rw [tw6Theta_apply] at hθz
    change twistE6 (AlgebraicClosure K) Fr (g₀ * z * g₀⁻¹) = g₀ * z * g₀⁻¹
    rw [map_mul, map_mul, map_inv, hg₀]
    calc g₀ * tw6N (AlgebraicClosure K) * twistE6 (AlgebraicClosure K) Fr z *
          (g₀ * tw6N (AlgebraicClosure K))⁻¹ =
        g₀ * (tw6N (AlgebraicClosure K) * twistE6 (AlgebraicClosure K) Fr z *
          (tw6N (AlgebraicClosure K))⁻¹) * g₀⁻¹ := by group
      _ = g₀ * z * g₀⁻¹ := by rw [hθz]
  have hXperf : ⁅P.map (MulAut.conj g₀).toMonoidHom, P.map (MulAut.conj g₀).toMonoidHom⁆ =
      P.map (MulAut.conj g₀).toMonoidHom := by
    rw [← Subgroup.map_commutator, hPperf]
  intro y hy
  obtain ⟨⟨x, hxC⟩, hx⟩ := (@hrat _ hXfin hXC hXF).2.2 _ le_rfl hXperf ⟨y, hy, rfl⟩
  refine ⟨x, hxC, ?_⟩
  rw [twLinePsi_apply]
  change g₀⁻¹ * twE6Emb K σ (AlgebraicClosure K) ⟨x, hxC⟩ * g₀ = y
  rw [hx]
  change g₀⁻¹ * (g₀ * y * g₀⁻¹) * g₀ = y
  group

theorem twLine_finrank_of_psi {K : Type} [Field K] {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
    {z : ModGL Tag.E6 K} {ω : (AlgebraicClosure K)ˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (hz : twLinePsi K g₀ z = rootDiagUnit Tag.E6 (twLineChar ω)) :
    Module.finrank K (LinearMap.ker ((z : Module.End K (RootModule Tag.E6 K)) - 1)) = 24 := by
  have e2 : twLinePsi K g₀ z =
      g₀⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) z * g₀ := twLinePsi_apply g₀ z
  have e : baseChangeGL (algebraMap K (AlgebraicClosure K)) z =
      g₀ * rootDiagUnit Tag.E6 (twLineChar ω) * g₀⁻¹ := by
    rw [← hz, e2]
    group
  have h := finrank_ker_baseChangeEnd (L := AlgebraicClosure K)
    ((z : Module.End K (RootModule Tag.E6 K)) - 1)
  rw [baseChangeEnd_sub_aux, baseChangeEnd_one_aux, ← coe_baseChangeGL, e,
    finrank_ker_conj_sub_one, twLine_diag_finrank h3 h1] at h
  exact h.symm

theorem exists_twE6ThreeA2Line_of_prime {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h3 : 3 ∣ ℓ ^ f + 1) (hq2 : 2 < ℓ ^ f) :
    ∃ (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
      (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K),
      TwE6ThreeA2Line K σ h₀ L T n := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := _root_.charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let Fr : Ω →+* Ω := iterateFrobenius Ω ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq : 2 ≤ ℓ ^ f := hq2.le
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) Ω := IsAlgClosure.ofAlgebraic (fixSubfield σ) K Ω
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ hσ
  have hnC : tw6N Ω ∈ adjointGroup Tag.E6 Ω := canonicalRep_mem_adjointGroup _ Ω _
  obtain ⟨g₀, hg₀C, hg₀⟩ : ∃ g₀ : ModGL Tag.E6 Ω, g₀ ∈ adjointGroup Tag.E6 Ω ∧
      twistE6 Ω Fr g₀ = g₀ * tw6N Ω :=
    lang_conjugator_twisted_gen K (ℓ := ℓ) (f := f) hf Ω _ hnC
  have hperf := twLine_perfect_le hℓ hf hK hσ hFr hg₀C hg₀
  have hψA : ∀ x ∈ twistedE6RootGroup K σ, twLinePsi K g₀ x ∈ adjointGroup Tag.E6 Ω :=
    fun x hx => twLine_psi_mem hg₀C hx
  have hψθ : ∀ x ∈ twistedE6RootGroup K σ,
      tw6Theta Ω Fr (twLinePsi K g₀ x) = twLinePsi K g₀ x := fun x hx =>
    twLine_psi_fixed hσ hFr hg₀ hx
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = twLinePsi K g₀ := ⟨_, rfl⟩
  rw [← hψ] at hperf hψA hψθ
  have hψinj : Function.Injective ψ := by
    rw [hψ]
    exact twLinePsi_injective K g₀
  have h3K : 3 ∣ Nat.card K - 1 := by
    have h1 : (ℓ ^ f) % 3 = 2 := by omega
    have h2 : (ℓ ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h1]
    rw [hK]
    omega
  obtain ⟨ωK, hωK3, hωK1⟩ := e6Line_exists_cube_root_unit h3K
  obtain ⟨ω, hω⟩ : ∃ ω : Ωˣ, ω = Units.map (algebraMap K Ω).toMonoidHom ωK := ⟨_, rfl⟩
  have hω3 : ω ^ 3 = 1 := by rw [hω, ← map_pow, hωK3, map_one]
  have hω1 : ω ≠ 1 := fun h => hωK1 (Units.map_injective (f := (algebraMap K Ω).toMonoidHom)
    (algebraMap K Ω).injective (by rw [← hω, h, map_one]))
  have hdθ : tw6Theta Ω Fr (rootDiagUnit Tag.E6 (twLineChar ω)) =
      rootDiagUnit Tag.E6 (twLineChar ω) := tw6Theta_twLine_diag hFr h3 hω3
  have hPS : ∀ (S : Set (Fin Tag.E6.rank → ℤ)) (w : WeylGroup Tag.E6),
      (∀ α ∈ S, IsRoot Tag.E6 α) → (∀ α ∈ S, e6T3W • α ∈ S) →
      (w • ·) '' S = parabolicRoots Tag.E6 support13 →
      rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) ≤
        (twistedE6RootGroup K σ).map ψ := by
    intro S w hSr hSu hw
    obtain ⟨Φ', ⟨e'⟩, -, hfin', hq'⟩ :=
      tw6_A2_layer_equiv (K := fixSubfield σ) (Fr := Fr) hf hkc hFr hSr hSu hw
    have := hfin'
    exact hperf _ (Finite.of_equiv _ e'.symm.toEquiv)
      (fun y hy => rootSpan_le_adjointGroup Ω S hy.1) (fun y hy => hy.2)
      (Subgroup.isPerfect_iff.1 (CFSG.IsQuasisimple.of_mulEquiv e' (hq' hq2).1).1)
  choose Φ he hH hfin hqs using fun i : Fin 3 =>
    tw6_A2_layer_equiv (K := fixSubfield σ) (Fr := Fr) hf hkc hFr
      (fun α hα => twE6FrameS_root i hα) (fun α hα => twE6FrameS_stable i hα)
      (twE6FrameS_conj i)
  have hLim : ∀ i : Fin 3,
      (twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS i)).comap ψ).map ψ =
        rootSpan Tag.E6 Ω (twE6FrameS i) ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) := fun i =>
    twLine_map_comap_eq ψ _ _ _ (fun x hx hxF => Subgroup.mem_inf.2 ⟨hxF, hψθ x hx⟩)
      (hPS _ _ (fun α hα => twE6FrameS_root i hα) (fun α hα => twE6FrameS_stable i hα)
        (twE6FrameS_conj i)) inf_le_left
  have hLiso : ∀ i : Fin 3, Nonempty
      (↥(twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS i)).comap ψ) ≃*
        ↥(fixSubgroup (Φ i))) := fun i =>
    ⟨((Subgroup.equivMapOfInjective _ ψ hψinj).trans (MulEquiv.subgroupCongr (hLim i))).trans
      (he i).some⟩
  have hLfin : ∀ i : Fin 3,
      Finite ↥(twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS i)).comap ψ) := by
    intro i
    have := hfin i
    exact Finite.of_equiv _ (hLiso i).some.symm.toEquiv
  have hLqs : ∀ i : Fin 3, CFSG.IsQuasisimple
      ↥(twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS i)).comap ψ) := fun i =>
    CFSG.IsQuasisimple.of_mulEquiv (hLiso i).some (hqs i hq2).1
  have hLcen : ∀ i : Fin 3, Nat.card (Subgroup.center
      ↥(twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS i)).comap ψ)) = 3 := by
    intro i
    rw [Nat.card_congr (Subgroup.centerCongr (hLiso i).some).toEquiv, (hqs i hq2).2.2.1,
      Nat.gcd_eq_left h3]
  have hFc : ∀ i j : Fin 3, i ≠ j → ∀ a ∈ rootSpan Tag.E6 Ω (twE6FrameS i),
      ∀ b ∈ rootSpan Tag.E6 Ω (twE6FrameS j), a * b = b * a := fun i j hij =>
    rootSpan_commute_of_orth (Or.inr (Or.inl rfl)) (fun α hα => twE6FrameS_root i hα)
      (fun α hα => twE6FrameS_root j hα) (twE6FrameS_orth hij)
  have hnab : ∀ i : Fin 3,
      ∃ a ∈ twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS i)).comap ψ,
        ∃ b ∈ twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS i)).comap ψ,
          a * b ≠ b * a := fun i =>
    twLine_exists_ne_comm (hLqs i)
  obtain ⟨h₀, hh₀C, hh₀⟩ := hPS _ _ (fun α hα => twE6FrameS_root 0 hα)
    (fun α hα => twE6FrameS_stable 0 hα) (twE6FrameS_conj 0)
    (Subgroup.mem_inf.2 ⟨twLine_diag_mem_rootSpan hω3 0, hdθ⟩)
  have hh₀L : ∀ i : Fin 3,
      h₀ ∈ twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS i)).comap ψ := fun i =>
    Subgroup.mem_inf.2 ⟨hh₀C, Subgroup.mem_comap.2 (by
      rw [hh₀]
      exact twLine_diag_mem_rootSpan hω3 i)⟩
  have hh₀H : ψ h₀ ∈ torusGroup Tag.E6 Ω := by
    rw [hh₀]
    exact rootDiagUnit_mem_torusGroup _
  have hcen : ∀ i : Fin 3, ∀ a ∈ rootSpan Tag.E6 Ω (twE6FrameS i), ψ h₀ * a = a * ψ h₀ := by
    intro i a ha
    rw [hh₀]
    exact twLine_diag_commute hω3 i ha
  have hh₀Lc : ∀ i : Fin 3,
      ∀ x ∈ twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS i)).comap ψ,
        h₀ * x = x * h₀ := by
    intro i x hx
    apply hψinj
    rw [map_mul, map_mul]
    exact hcen i _ (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hx).2)
  have hh₀3 : h₀ ^ 3 = 1 := hψinj (by
    rw [map_pow, hh₀, map_one]
    exact twLine_diag_pow_three hω3)
  have hh₀1 : h₀ ≠ 1 := fun h => twLine_diag_ne_one hω1 (by rw [← hh₀, h, map_one])
  have hmd : ∀ g, h₀ * g = g * h₀ →
      rootDiagUnit Tag.E6 (twLineChar ω) * ψ g = ψ g * rootDiagUnit Tag.E6 (twLineChar ω) := by
    intro g hg
    rw [← hh₀, ← map_mul ψ h₀ g, hg, map_mul]
  obtain ⟨n₀, hn₀S, hn₀θ, n₁, hn₁S, hn₁θ, t₀, ht₀, hnn⟩ :=
    twLine_exists_fixed_comp (Fr := Fr) hq hFr
  obtain ⟨ν₀, hν₀C, hν₀⟩ := hPS (twLineDS 0) (twLineXW 0) (fun α hα => twLineDS_root hα)
    (fun α hα => twLineDS_stable hα) (twLineDS_conj 0) (Subgroup.mem_inf.2 ⟨hn₀S, hn₀θ⟩)
  obtain ⟨ν₁, hν₁C, hν₁⟩ := hPS (twLineDS 1) (twLineXW 1) (fun α hα => twLineDS_root hα)
    (fun α hα => twLineDS_stable hα) (twLineDS_conj 1) (Subgroup.mem_inf.2 ⟨hn₁S, hn₁θ⟩)
  have hψn : ψ (ν₀ * ν₁) = canonicalRep (coxeterSystem Tag.E6) Ω twLineWeyl * t₀ := by
    rw [map_mul, hν₀, hν₁, hnn]
  have hnC' : ν₀ * ν₁ ∈ twistedE6RootGroup K σ := mul_mem hν₀C hν₁C
  have hnF : ∀ i : Fin 3, (rootSpan Tag.E6 Ω (twE6FrameS i)).map
      (MulAut.conj (ψ (ν₀ * ν₁))).toMonoidHom = rootSpan Tag.E6 Ω (twE6FrameS (i + 1)) := by
    intro i
    rw [hψn, map_conj_mul_aux, map_conj_eq_of_mem_normalizer_aux
      (torusGroup_le_normalizer_rootSpan_e6 (fun α hα => twE6FrameS_root i hα) ht₀),
      twLine_weyl_map]
  have hh₀n : h₀ * (ν₀ * ν₁) = ν₀ * ν₁ * h₀ := by
    apply hψinj
    rw [map_mul ψ h₀ (ν₀ * ν₁), map_mul ψ (ν₀ * ν₁) h₀, hh₀, hψn]
    exact twLine_commute_mul (twLine_conj_weyl hω3)
      (twLine_torusGroup_comm t₀ ht₀ _ (rootDiagUnit_mem_torusGroup _))
  have hshift : ∀ g ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀}, ∃ k : Fin 3, ∀ i,
      (rootSpan Tag.E6 Ω (twE6FrameS i)).map (MulAut.conj (ψ g)).toMonoidHom =
        rootSpan Tag.E6 Ω (twE6FrameS (i + k)) := fun g hg =>
    twLine_conj_shift hω3 hω1 (hψA g (Subgroup.mem_inf.1 hg).1)
      (hmd g (twLine_mem_centralizer_singleton.1 (Subgroup.mem_inf.1 hg).2))
  have hnc : ∃ a ∈ rootSpan Tag.E6 Ω (twE6FrameS 0), ∃ b ∈ rootSpan Tag.E6 Ω (twE6FrameS 0),
      a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      twLine_exists_ne_comm (CFSG.IsQuasisimple.of_mulEquiv (he 0).some (hqs 0 hq2).1)
    exact ⟨a, ha.1, b, hb.1, hab⟩
  have hsplit : ∀ g ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀},
      (∀ i, (rootSpan Tag.E6 Ω (twE6FrameS i)).map (MulAut.conj (ψ g)).toMonoidHom =
        rootSpan Tag.E6 Ω (twE6FrameS i)) →
      ∃ t ∈ twistedE6RootGroup K σ ⊓ (torusGroup Tag.E6 Ω).comap ψ,
        ∃ l₀ ∈ twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS 0)).comap ψ,
        ∃ l₁ ∈ twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS 1)).comap ψ,
        ∃ l₂ ∈ twistedE6RootGroup K σ ⊓ (rootSpan Tag.E6 Ω (twE6FrameS 2)).comap ψ,
          g = t * l₀ * l₁ * l₂ := by
    intro g hg hsh
    obtain ⟨hgC, hgZ⟩ := Subgroup.mem_inf.1 hg
    have hm := twLine_shift_zero hω3 hω1 hnc (hψA g hgC)
      (hmd g (twLine_mem_centralizer_singleton.1 hgZ)) hsh
    obtain ⟨t, htH, -, p₀, hp₀, hp₀θ, p₁, hp₁, hp₁θ, p₂, hp₂, hp₂θ, hgp⟩ :=
      twLine_fixed_split hq hFr hm (hψθ g hgC)
    obtain ⟨l₀, hl₀C, hl₀⟩ := (hLim 0).ge (Subgroup.mem_inf.2 ⟨hp₀, hp₀θ⟩)
    obtain ⟨l₁, hl₁C, hl₁⟩ := (hLim 1).ge (Subgroup.mem_inf.2 ⟨hp₁, hp₁θ⟩)
    obtain ⟨l₂, hl₂C, hl₂⟩ := (hLim 2).ge (Subgroup.mem_inf.2 ⟨hp₂, hp₂θ⟩)
    have hlC : l₀ * l₁ * l₂ ∈ twistedE6RootGroup K σ :=
      mul_mem (mul_mem (Subgroup.mem_inf.1 hl₀C).1 (Subgroup.mem_inf.1 hl₁C).1)
        (Subgroup.mem_inf.1 hl₂C).1
    refine ⟨g * (l₀ * l₁ * l₂)⁻¹, Subgroup.mem_inf.2 ⟨mul_mem hgC (inv_mem hlC),
      Subgroup.mem_comap.2 ?_⟩, l₀, hl₀C, l₁, hl₁C, l₂, hl₂C, by group⟩
    rw [map_mul, map_inv, map_mul, map_mul, hl₀, hl₁, hl₂, hgp]
    have e : t * p₀ * p₁ * p₂ * (p₀ * p₁ * p₂)⁻¹ = t := by group
    rw [e]
    exact htH
  have hmul := fun g (hg : g ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀}) =>
    twLine_centralizer_mul_comap ψ (twistedE6RootGroup K σ)
      (fun i => rootSpan Tag.E6 Ω (twE6FrameS i)) (torusGroup Tag.E6 Ω)
      (Subgroup.mem_inf.2 ⟨hnC', twLine_mem_centralizer_singleton.2 hh₀n⟩) hnF hshift hsplit hg
  subst hψ
  refine ⟨h₀, fun i => twistedE6RootGroup K σ ⊓
      (rootSpan Tag.E6 Ω (twE6FrameS i)).comap (twLinePsi K g₀),
    twistedE6RootGroup K σ ⊓ (torusGroup Tag.E6 Ω).comap (twLinePsi K g₀), ν₀ * ν₁, ?_⟩
  exact
    { h₀_mem := hh₀C
      h₀_pow := hh₀3
      h₀_ne := hh₀1
      finrank_fixed := twLine_finrank_of_psi hω3 hω1 hh₀
      L_le := fun i => inf_le_left
      L_finite := hLfin
      L_quasisimple := hLqs
      L_center := hLcen
      L_center_eq := fun i => by
        have := hLfin i
        exact twLine_center_eq_zpowers (hh₀L i) (hh₀Lc i) hh₀3 hh₀1 (hLcen i)
      h₀_mem_L := hh₀L
      L_commute := fun i j hij =>
        twLine_comap_commute (twLinePsi K g₀) hψinj (twistedE6RootGroup K σ) (hFc i j hij)
      T_le := inf_le_left
      T_comm := twLine_comap_commute (twLinePsi K g₀) hψinj (twistedE6RootGroup K σ)
        twLine_torusGroup_comm
      h₀_mem_T := Subgroup.mem_inf.2 ⟨hh₀C, Subgroup.mem_comap.2 hh₀H⟩
      T_le_normalizer := fun i => twLine_comap_le_normalizer (twLinePsi K g₀)
        (twistedE6RootGroup K σ)
        (torusGroup_le_normalizer_rootSpan_e6 fun α hα => twE6FrameS_root i hα)
      n_mem := hnC'
      n_conj := fun i =>
        twLine_map_conj_comap (twLinePsi K g₀) (twistedE6RootGroup K σ) hnC' (hnF i)
      centralizer_eq := twLine_centralizer_eq_comap (twLinePsi K g₀) hψinj
        (twistedE6RootGroup K σ) (fun i => rootSpan Tag.E6 Ω (twE6FrameS i))
        (torusGroup Tag.E6 Ω) twLine_torusGroup_comm hh₀H hcen hnC' hh₀n hmul
      centralizer_mul := hmul
      conj_shift := fun g hg => twLine_conj_shift_comap (twLinePsi K g₀)
        (twistedE6RootGroup K σ) (fun i => rootSpan Tag.E6 Ω (twE6FrameS i)) inf_le_left
        hshift hg
      shift_zero := fun g hg hfix => twLine_shift_zero_comap (twLinePsi K g₀) hψinj
        (twistedE6RootGroup K σ) (fun i => rootSpan Tag.E6 Ω (twE6FrameS i))
        (torusGroup Tag.E6 Ω) hFc hnab inf_le_left hshift hsplit hg hfix
      le_normalizer := twLine_le_normalizer_iSup
        (L := fun i => twistedE6RootGroup K σ ⊓
          (rootSpan Tag.E6 Ω (twE6FrameS i)).comap (twLinePsi K g₀))
        fun g hg => twLine_conj_shift_comap (twLinePsi K g₀) (twistedE6RootGroup K σ)
          (fun i => rootSpan Tag.E6 Ω (twE6FrameS i)) inf_le_left hshift hg
      picture := ⟨ℓ ^ f, Fr, g₀,
        { card_eq := hK
          σ_apply := hσ
          Fr_apply := hFr
          g₀_mem := hg₀C
          g₀_lang := hg₀
          psi_mem := hψA
          psi_fixed := hψθ
          perfect_le := hperf
          h₀_image := ⟨ω, hω3, hω1, hh₀⟩
          mem_L := fun i x => Iff.rfl
          L_image := hLim
          L_model := fun i => ⟨Φ i, hLiso i, hH i⟩
          mem_T := fun x => Iff.rfl
          n_image := ⟨t₀, ht₀, hψn⟩ }⟩ }

theorem exists_twE6ThreeA2Line (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (_hchar : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q + 1) (hq : q ≠ 2) :
    ∃ (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
      (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K),
      TwE6ThreeA2Line K σ h₀ L T n := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hpm, hcard⟩ := FiniteField.card K (ringChar K)
  obtain ⟨p, hp⟩ : ∃ p, p = ringChar K := ⟨_, rfl⟩
  rw [← hp] at hpm hcard
  have hqd : q ∣ p ^ (m : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hpm).1 hqd
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at h3
      omega
    · exact h
  have hq2 : 2 < p ^ f := by
    have h1 : p ^ 1 ≤ p ^ f := Nat.pow_le_pow_right hpm.pos hf
    rw [pow_one] at h1
    have h2 := hpm.two_le
    omega
  exact exists_twE6ThreeA2Line_of_prime hpm hf K hK σ hσ h3 hq2

theorem twE6ThreeA2LineStmt_holds : TwE6ThreeA2LineStmt := by
  intro K _ _ σ q hK3 hσ hKq h3 hq2
  exact exists_twE6ThreeA2Line K σ q hK3 hσ hKq h3 hq2

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
