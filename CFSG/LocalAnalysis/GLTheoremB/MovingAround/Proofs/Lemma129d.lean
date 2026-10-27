module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129P
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltWeakBalance

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centralizer_barX_eq card_barX_of_isPGroup elemAbelian_barX)

section Impl

variable {Y : Type} [Group Y]

theorem eq_one_of_central {K₀ : Subgroup Y} {n : ℕ} (hn : 4 ≤ n)
    (ψ : K₀ ≃* alternatingGroup (Fin n)) {z : K₀} (hz : ∀ x : K₀, z * x = x * z) : z = 1 := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn
  have hψz : ((ψ z : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 1 := by
    apply hinj
    rw [map_one]
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have := congrArg (fun w : K₀ => ((ψ w : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)))
      (hz (ψ.symm a))
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at this
    show _ * _ * _ = _
    rw [this]
    simp
  have : ψ z = 1 := Subtype.ext hψz
  exact ψ.injective (by rw [this, map_one])

theorem sign_eq_one_of_pow_eq_one {n p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g : Equiv.Perm (Fin n)} (hg : g ^ (p ^ k) = 1) : Equiv.Perm.sign g = 1 := by
  have h1 : (Equiv.Perm.sign g) ^ (p ^ k) = 1 := by
    rw [← map_pow, hg, map_one]
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
  · exact h
  · rw [h, hodd.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem exists_implementer {K₀ : Subgroup Y} {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (ψ : K₀ ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Subgroup Y} (hH : H ≤ Subgroup.normalizer (K₀ : Set Y)) (hHp : IsPGroup p ↥H) :
    ∃ κ : ↥H →* ↥K₀, ∀ (h : ↥H) (x : ↥K₀),
      ((h : Y) * (x : Y) * (h : Y)⁻¹ : Y) =
        ((κ h : K₀) : Y) * (x : Y) * ((κ h : K₀) : Y)⁻¹ := by
  have bij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  let e : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ bij
  let act : ↥H →* MulAut K₀ := K₀.normalizerMonoidHom.comp (Subgroup.inclusion hH)
  let ρ : ↥H →* Equiv.Perm (Fin n) :=
    e.symm.toMonoidHom.comp ((MulAut.congr ψ).toMonoidHom.comp act)
  have hρ : ∀ h : ↥H, e (ρ h) = MulAut.congr ψ (act h) := fun h => e.apply_symm_apply _
  have hev : ∀ h : ↥H, ρ h ∈ alternatingGroup (Fin n) := by
    intro h
    obtain ⟨k, hk⟩ := hHp h
    rw [Equiv.Perm.mem_alternatingGroup]
    refine sign_eq_one_of_pow_eq_one hp hp2 (k := k) ?_
    rw [← map_pow, hk, map_one]
  refine ⟨ψ.symm.toMonoidHom.comp (ρ.codRestrict (alternatingGroup (Fin n)) hev), ?_⟩
  intro h x
  set κh : K₀ := ψ.symm ⟨ρ h, hev h⟩ with hκh
  have hψκ : ψ κh = ⟨ρ h, hev h⟩ := ψ.apply_symm_apply _
  have key : (act h x : K₀) = κh * x * κh⁻¹ := by
    apply ψ.injective
    have h1 : ψ (act h x) = MulAut.congr ψ (act h) (ψ x) := by simp [MulAut.congr_apply]
    rw [h1, ← hρ h]
    apply Subtype.ext
    simp only [map_mul, map_inv, hψκ, Subgroup.coe_mul, InvMemClass.coe_inv]
    show ((ρ h : Equiv.Perm (Fin n)) * (ψ x : Equiv.Perm (Fin n)) * (ρ h)⁻¹ : Equiv.Perm (Fin n)) = _
    rfl
  have h2 : ((act h x : K₀) : Y) = (h : Y) * (x : Y) * (h : Y)⁻¹ := by
    show ((K₀.normalizerMonoidHom ⟨(h : Y), hH h.2⟩ x : K₀) : Y) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  show (h : Y) * (x : Y) * (h : Y)⁻¹ = ((κh : K₀) : Y) * (x : Y) * ((κh : K₀) : Y)⁻¹
  rw [← h2, key]
  simp

end Impl

section AltDataSec

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D S F K : Subgroup G}

theorem perm_eq_of_conj_eq {n : ℕ} (hn : 4 ≤ n) {g₁ g₂ : Equiv.Perm (Fin n)}
    (h : ∀ a : alternatingGroup (Fin n),
      g₁ * (a : Equiv.Perm (Fin n)) * g₁⁻¹ = g₂ * (a : Equiv.Perm (Fin n)) * g₂⁻¹) : g₁ = g₂ := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn
  apply hinj
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
  exact h a

structure AltData (p : ℕ) (N K F : Subgroup G) where
  n : ℕ
  m : ℕ
  δ : ℕ
  hm : 0 < m
  hδ : δ = 2 ∨ δ = 4
  hn : n = m * p ^ CFSG.Open.pRank p F + δ
  ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)
  κ : ↥(barX p N F) →* ↥(barX p N K)
  hκ : ∀ (f : ↥(barX p N F)) (x : ↥(barX p N K)),
    ((f : ↥N ⧸ GLAPPrimeCore p ↥N) * (x : ↥N ⧸ GLAPPrimeCore p ↥N) *
      (f : ↥N ⧸ GLAPPrimeCore p ↥N)⁻¹) =
      ((κ f : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N) * (x : ↥N ⧸ GLAPPrimeCore p ↥N) *
        ((κ f : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N)⁻¹
  Ω₀ : Set (Fin n)
  hΩ₀ : Ω₀.ncard = δ
  hfix : ∀ (f : ↥(barX p N F)), ∀ j ∈ Ω₀, ((ψ (κ f) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) j = j
  hsemi : ∀ (f : ↥(barX p N F)), f ≠ 1 → ∀ j, j ∉ Ω₀ →
    ((ψ (κ f) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) j ≠ j

theorem exists_altData (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (halt : Alt1916 p (CFSG.Open.pRank p F) (autBar p F K)) : Nonempty (AltData p N K F) := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  obtain ⟨m', δ, hm', hδ, φ₀, ρ, Ω₀, hact, hΩ₀, hsemi⟩ := halt
  have hAN := A_le_N h
  have hFA := hs.F_le_A
  have hFN : F ≤ N := hFA.trans hAN
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h9 : 9 ≤ p ^ CFSG.Open.pRank p F := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ CFSG.Open.pRank p F := Nat.pow_le_pow_right hp.pos hs.hr
  have hn11 : 11 ≤ m' * p ^ CFSG.Open.pRank p F + δ := by
    have h1 : p ^ CFSG.Open.pRank p F ≤ m' * p ^ CFSG.Open.pRank p F :=
      Nat.le_mul_of_pos_left _ hm'
    omega
  let e := quotEquivBarX hp hs.hK.1 hs.hK.2.1
  let ψ : ↥(barX p N K) ≃* alternatingGroup (Fin (m' * p ^ CFSG.Open.pRank p F + δ)) :=
    e.symm.trans φ₀
  have hH : barX p N F ≤ Subgroup.normalizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) :=
    barX_le_normalizer hs.hFK
  have hHp : IsPGroup p ↥(barX p N F) :=
    Lemma129.isPGroup_barX ((A_el h).mono hFA).isPGroup hFN
  obtain ⟨κ, hκ⟩ := exists_implementer (by omega) (by omega) ψ hp hp2 hH hHp
  have key : ∀ f : ↥(barX p N F), ∃ b : ↥(autBar p F K),
      ((ψ (κ f) : alternatingGroup (Fin (m' * p ^ CFSG.Open.pRank p F + δ))) :
        Equiv.Perm (Fin (m' * p ^ CFSG.Open.pRank p F + δ))) = ρ b ∧ (f ≠ 1 → b ≠ 1) := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨f₀, hf₀N⟩, hf₀F, rfl⟩ := hx
    have hf₀F' : f₀ ∈ F := (Subgroup.mem_subgroupOf).1 hf₀F
    have hmem : autHom p hs.hFK ⟨f₀, hf₀F'⟩ ∈ autBar p F K := by
      rw [autBar_eq_range p hs.hFK]
      exact ⟨_, rfl⟩
    refine ⟨⟨autHom p hs.hFK ⟨f₀, hf₀F'⟩, hmem⟩, ?_, ?_⟩
    · apply perm_eq_of_conj_eq (by omega)
      intro a
      obtain ⟨y, rfl⟩ := φ₀.surjective a
      have h1 := hact ⟨autHom p hs.hFK ⟨f₀, hf₀F'⟩, hmem⟩ y
      have h2 := Lemma129b.quotEquivBarX_barAut hp hs.hK hf₀N (hs.hFK hf₀F') y
      rw [← autHom_apply p hs.hFK ⟨f₀, hf₀F'⟩] at h2
      have h3 := hκ ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f₀, hf₀N⟩, ⟨⟨f₀, hf₀N⟩, hf₀F, rfl⟩⟩ (e y)
      have h4 : e (autHom p hs.hFK ⟨f₀, hf₀F'⟩ y) =
          κ ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f₀, hf₀N⟩, ⟨⟨f₀, hf₀N⟩, hf₀F, rfl⟩⟩ *
            e y * (κ ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f₀, hf₀N⟩,
              ⟨⟨f₀, hf₀N⟩, hf₀F, rfl⟩⟩)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [← h3]
        exact h2
      have h5 : φ₀ (autHom p hs.hFK ⟨f₀, hf₀F'⟩ y) =
          ψ (κ ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f₀, hf₀N⟩, ⟨⟨f₀, hf₀N⟩, hf₀F, rfl⟩⟩) *
            φ₀ y * (ψ (κ ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f₀, hf₀N⟩,
              ⟨⟨f₀, hf₀N⟩, hf₀F, rfl⟩⟩))⁻¹ := by
        have := congrArg ψ h4
        simpa [ψ, map_mul, map_inv] using this
      rw [← h1, h5]
      simp
    · intro hf1 hb1
      apply hf1
      have hb1' : autHom p hs.hFK ⟨f₀, hf₀F'⟩ = 1 := congrArg Subtype.val hb1
      have : (⟨f₀, hf₀F'⟩ : ↥F) = 1 := autHom_injective p hs.hFK hs.hFc (by rw [hb1', map_one])
      have hf01 : f₀ = 1 := congrArg Subtype.val this
      apply Subtype.ext
      show QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f₀, hf₀N⟩ = 1
      have : (⟨f₀, hf₀N⟩ : ↥N) = 1 := Subtype.ext hf01
      rw [this, map_one]
  refine ⟨⟨m' * p ^ CFSG.Open.pRank p F + δ, m', δ, hm', hδ, rfl, ψ, κ, hκ, Ω₀, hΩ₀, ?_, ?_⟩⟩
  · intro f j hj
    obtain ⟨b, hb, -⟩ := key f
    rw [hb]
    exact hsemi.1 b j hj
  · intro f hf j hj
    obtain ⟨b, hb, hb1⟩ := key f
    rw [hb]
    exact hsemi.2 b (hb1 hf) j hj

theorem n_eq_of_alt_equiv {n n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n')
    (e : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n')) : n = n' := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  haveI : Nontrivial (Fin n') := Fin.nontrivial_iff_two_le.2 hn'
  have h1 := Nat.card_congr e.toEquiv
  rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  have h3 : 2 ∣ n'.factorial := Nat.dvd_factorial (by norm_num) hn'
  have h4 : n.factorial = n'.factorial := by
    rw [← Nat.mul_div_cancel' h2, ← Nat.mul_div_cancel' h3, h1]
  exact (Nat.factorial_inj (by omega)).1 h4

theorem impl_unique {Y : Type} [Group Y] {K₀ : Subgroup Y} {n : ℕ} (hn : 4 ≤ n)
    (ψ : K₀ ≃* alternatingGroup (Fin n)) {u v : ↥K₀}
    (h : ∀ x : ↥K₀, ((u : K₀) : Y) * (x : Y) * ((u : K₀) : Y)⁻¹ =
      ((v : K₀) : Y) * (x : Y) * ((v : K₀) : Y)⁻¹) : u = v := by
  have hz : u⁻¹ * v = 1 := by
    refine eq_one_of_central hn ψ fun x => ?_
    apply Subtype.ext
    have := h x
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    calc ((u : Y))⁻¹ * (v : Y) * (x : Y) = (u : Y)⁻¹ * ((v : Y) * (x : Y) * (v : Y)⁻¹) * (v : Y) := by
          group
      _ = (u : Y)⁻¹ * ((u : Y) * (x : Y) * (u : Y)⁻¹) * (v : Y) := by rw [this]
      _ = (x : Y) * ((u : Y)⁻¹ * (v : Y)) := by group
  exact (inv_mul_eq_one.1 hz)

theorem exists_three_cycle_in {n : ℕ} {Ω : Set (Fin n)} (hΩ : 3 ≤ Ω.ncard) :
    ∃ τ : Equiv.Perm (Fin n), τ.IsThreeCycle ∧ (∀ j, j ∉ Ω → τ j = j) ∧ ∃ j ∈ Ω, τ j ≠ j := by
  have hfin : Ω.Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff hfin).1 (by omega)
  refine ⟨Equiv.swap a b * Equiv.swap a c, Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc,
    fun j hj => ?_, a, ha, ?_⟩
  · have hja : j ≠ a := fun h => hj (h ▸ ha)
    have hjb : j ≠ b := fun h => hj (h ▸ hb)
    have hjc : j ≠ c := fun h => hj (h ▸ hc)
    simp [Equiv.swap_apply_of_ne_of_ne hja hjc, Equiv.swap_apply_of_ne_of_ne hja hjb]
  · have : (Equiv.swap a b * Equiv.swap a c) a = c := by
      simp [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm, Equiv.swap_apply_left]
    rw [this]
    exact hac.symm

theorem mem_of_commute_implementers {Y : Type} [Group Y] {p : ℕ} {K₀ Ab : Subgroup Y}
    (hAb : IsSCp p ⊤ Ab) (κ : ↥Ab →* ↥K₀)
    (hκ : ∀ (a : ↥Ab) (x : ↥K₀), ((a : Ab) : Y) * (x : Y) * ((a : Ab) : Y)⁻¹ =
      ((κ a : K₀) : Y) * (x : Y) * ((κ a : K₀) : Y)⁻¹)
    {τ : ↥K₀} (hτp : (τ : Y) ^ p = 1)
    (hcomm : ∀ a : ↥Ab, ((κ a : K₀) : Y) * (τ : Y) = (τ : Y) * ((κ a : K₀) : Y)) :
    (τ : Y) ∈ Ab := by
  refine Lemma129Y.mem_of_isSCp_of_commute_of_pow_eq_one hAb (fun a ha => ?_) hτp
  have h1 := hκ ⟨a, ha⟩ τ
  have h2 := hcomm ⟨a, ha⟩
  simp only at h1
  have h3 : a * (τ : Y) * a⁻¹ = (τ : Y) := by
    rw [h1, h2]
    group
  calc a * (τ : Y) = a * (τ : Y) * a⁻¹ * a := by group
    _ = (τ : Y) * a := by rw [h3]

theorem AltData.hn11 (D' : AltData p N K F) (hp3 : 3 ≤ p) (hr : 2 ≤ CFSG.Open.pRank p F) :
    11 ≤ D'.n := by
  have h9 : 9 ≤ p ^ CFSG.Open.pRank p F := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ CFSG.Open.pRank p F := Nat.pow_le_pow_right (by omega) hr
  have h1 : p ^ CFSG.Open.pRank p F ≤ D'.m * p ^ CFSG.Open.pRank p F :=
    Nat.le_mul_of_pos_left _ D'.hm
  have := D'.hn
  have := D'.hδ
  omega

theorem AltData.exists_not_mem (D' : AltData p N K F) (hp0 : 0 < p) : ∃ j : Fin D'.n, j ∉ D'.Ω₀ := by
  by_contra hcon
  push Not at hcon
  have h1 : D'.Ω₀ = Set.univ := Set.eq_univ_of_forall hcon
  have h2 : D'.Ω₀.ncard = D'.n := by rw [h1, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := D'.hΩ₀
  have := D'.hδ
  have h3 : D'.m * p ^ CFSG.Open.pRank p F ≥ 1 := Nat.mul_pos D'.hm (pow_pos hp0 _)
  have h4 := D'.hn
  omega

theorem AltData.κ_injective (D' : AltData p N K F) (hp0 : 0 < p) : Function.Injective D'.κ := by
  rw [injective_iff_map_eq_one]
  intro f hf
  by_contra hf1
  obtain ⟨j, hj⟩ := D'.exists_not_mem hp0
  have := D'.hsemi f hf1 j hj
  rw [hf, map_one] at this
  exact this rfl

theorem card_A_of_ne (hp : p.Prime) (hs : Setup2 M A N p S F K) (hFA : F ≠ A) :
    Nat.card A = p * Nat.card F := by
  obtain ⟨B', hB'F, hB'i⟩ := hs.hyp
  have hdvd : (F.subgroupOf A).index ∣ p := hB'i ▸ Subgroup.relIndex_dvd_of_le_left A hB'F
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exfalso
    apply hFA
    have : F.subgroupOf A = ⊤ := Subgroup.index_eq_one.1 h1
    exact le_antisymm hs.F_le_A (Subgroup.subgroupOf_eq_top.1 this)
  · have := Subgroup.card_mul_index (F.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.F_le_A).toEquiv, h1] at this
    rw [← this, mul_comm]

theorem alt_p_le_delta (h121 : Prop121_corStatement) (h : Cex127 G m p B M E A N D)
    (hs : Setup2 M A N p S F K) (D' : AltData p N K F)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hFA : F ≠ A) : p ≤ D'.δ := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hn11 := D'.hn11 hp3 hs.hr
  have h5 : 5 ≤ D'.n := by omega
  have h6 : D'.n ≠ 6 := by omega
  have hFA' := hs.F_le_A
  have hFS := hs.F_le_cent
  have hSK := hs.S_le_normalizer hp h
  have hFN : F ≤ N := hFA'.trans (A_le_N h)
  obtain ⟨σ, hσS, a, haA, hnot⟩ :=
    exists_comm_not_mem_centBar h hs.hS hs.hK (hs.hFdef ▸ hFA) hSK hAK hs.hKc
  obtain ⟨f₀, hf₀F, hf₀1⟩ : ∃ f₀ ∈ F, f₀ ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one F with hbot | hex
    · exfalso
      have h1 := card_eq_pow_pRank hp ((A_el h).mono hFA')
      have h2 : p ^ 2 ≤ p ^ CFSG.Open.pRank p F := Nat.pow_le_pow_right hp.pos hs.hr
      have h3 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      have h4 : Nat.card F = 1 := by rw [hbot]; exact Subgroup.card_bot
      omega
    · exact hex
  set e : barOf p K ≃* alternatingGroup (Fin D'.n) :=
    (quotEquivBarX hp hs.hK.1 hs.hK.2.1).trans D'.ψ with he
  set H := innerAut (barOf p K) ⊔ autBar p (deltaTwo N F) K with hH
  set d := barAut p K ⟨f₀, hs.hFK hf₀F⟩ with hd
  set b := barAut p K ⟨a, hAK haA⟩ with hb
  set x := barAut p K ⟨σ, hSK hσS⟩ with hx
  have hd1 : d ≠ 1 := by
    intro hd1
    apply hf₀1
    have hmem : f₀ ∈ F ⊓ centBar p ⊤ K := ⟨hf₀F, (mem_centBar_top_iff (hs.hFK hf₀F)).2 hd1⟩
    rw [hs.hFc, Subgroup.mem_bot] at hmem
    exact hmem
  have hxW : x ∈ localDeltaTwoIn H (autBar p F K) :=
    hs.hW (barAut_mem_autBar (le_deltaTwo h121 h hs.hS hFA' hFS hσS) (hSK hσS))
  have hxd : x ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (barOf p K)))) := by
    simp only [localDeltaTwoIn, Subgroup.mem_iInf] at hxW
    exact hxW d (barAut_mem_autBar hf₀F (hs.hFK hf₀F)) hd1
  have hdp : d ^ p = 1 := by
    rw [hd, ← map_pow]
    have : (⟨f₀, hs.hFK hf₀F⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
      Subtype.ext ((A_el h).2 f₀ (hFA' hf₀F))
    rw [this, map_one]
  have hbp : b ^ p = 1 := by
    rw [hb, ← map_pow]
    have : (⟨a, hAK haA⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
      Subtype.ext ((A_el h).2 a haA)
    rw [this, map_one]
  have hbd : b * d = d * b := by
    rw [hb, hd, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (elemAbelian_comm (A_el h) haA (hFA' hf₀F))
  set fb : ↥(barX p N F) := ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f₀, hFN hf₀F⟩,
    ⟨⟨f₀, hFN hf₀F⟩, (Subgroup.mem_subgroupOf).2 hf₀F, rfl⟩⟩ with hfb
  have hΘd : AltWeakBalance.autPerm e h5 h6 d =
      ((D'.ψ (D'.κ fb) : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) := by
    apply AltWeakBalance.autPerm_eq
    intro y
    have h2 := Lemma129b.quotEquivBarX_barAut hp hs.hK (hFN hf₀F) (hs.hFK hf₀F) y
    have h3 := D'.hκ fb (quotEquivBarX hp hs.hK.1 hs.hK.2.1 y)
    have h4 : quotEquivBarX hp hs.hK.1 hs.hK.2.1 (d y) =
        D'.κ fb * quotEquivBarX hp hs.hK.1 hs.hK.2.1 y * (D'.κ fb)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [← h3]
      exact h2
    simp only [he, MulEquiv.trans_apply, h4, map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv]
  have hfb1 : fb ≠ 1 := by
    intro h1
    apply hd1
    have h7 : AltWeakBalance.autPerm e h5 h6 d = 1 := by rw [hΘd, h1]; simp
    exact (AltWeakBalance.autPerm e h5 h6).injective (h7.trans (map_one _).symm)
  have hfix : {j : Fin D'.n | AltWeakBalance.autPerm e h5 h6 d j = j} = D'.Ω₀ := by
    ext j
    simp only [Set.mem_setOf_eq, hΘd]
    constructor
    · intro hj
      by_contra hjΩ
      exact D'.hsemi fb hfb1 j hjΩ hj
    · exact D'.hfix fb j
  have hcomm : x * b = b * x :=
    AltWeakBalance.comm_of_mem_pCoreOf e h5 h6 hp hp2 le_sup_left hdp hbp hbd
      (by rw [hfix, D'.hΩ₀]; exact hlt) hxd
  apply hnot
  have hc : σ * a * σ⁻¹ * a⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSK hσS) (hAK haA))
      (Subgroup.inv_mem _ (hSK hσS))) (Subgroup.inv_mem _ (hAK haA))
  rw [mem_centBar_top_iff hc]
  have e1 : (⟨σ * a * σ⁻¹ * a⁻¹, hc⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨σ, hSK hσS⟩ * ⟨a, hAK haA⟩ * ⟨σ, hSK hσS⟩⁻¹ * ⟨a, hAK haA⟩⁻¹ := rfl
  rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, ← hx, ← hb, hcomm]
  group

theorem alt_p_three_delta_four (h121 : Prop121_corStatement)
    (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K) (D' : AltData p N K F)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hFA : F ≠ A) : p = 3 ∧ D'.δ = 4 := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  have hple := alt_p_le_delta h121 h hs D' hAK hFA
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases D'.hδ with hδ | hδ
  · omega
  · refine ⟨?_, hδ⟩
    rw [hδ] at hple
    have h4 : p ≠ 4 := by
      intro h4
      rw [h4] at hp
      norm_num at hp
    omega

theorem alt_centralizer_trivial (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (D' : AltData p N K F) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hFA : F ≠ A)
    (hp3 : p = 3) (hδ4 : D'.δ = 4) :
    ∀ x ∈ barX p N A, (∀ y ∈ barX p N K, x * y = y * x) → x = 1 := by
  subst hp3
  have hp := prime_of h
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 := ne_two_of h
  have hAN := A_le_N h
  have hFA' := hs.F_le_A
  have hFN : F ≤ N := hFA'.trans hAN
  have hn11 := D'.hn11 (le_refl 3) hs.hr
  have hAbar : IsSCp 3 ⊤ (barX 3 N A) := Lemma129b.barX_A_isSCp h
  have hĀN : barX 3 N A ≤ Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    barX_le_normalizer hAK
  have hĀp : IsPGroup 3 ↥(barX 3 N A) := Lemma129.isPGroup_barX (A_el h).isPGroup hAN
  obtain ⟨κA, hκA⟩ := exists_implementer (by omega) (by omega) D'.ψ hp hp2 hĀN hĀp
  intro x hx hxc
  by_contra hx1
  let xA : ↥(barX 3 N A) := ⟨x, hx⟩
  have hκx : κA xA = 1 := by
    apply impl_unique (by omega) D'.ψ
    intro y
    have h1 := hκA xA y
    have h2 : x * (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) * x⁻¹ = y := by
      have := hxc y y.2
      calc x * (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) * x⁻¹ = (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) * x * x⁻¹ := by
            rw [this]
        _ = y := by group
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
    rw [← h1]
    exact h2
  have hFcard : Nat.card (barX 3 N F) = 3 ^ CFSG.Open.pRank 3 F := by
    rw [card_barX_of_isPGroup hp hFN ((A_el h).mono hFA').isPGroup,
      card_eq_pow_pRank hp ((A_el h).mono hFA')]
  have hAcard : Nat.card (barX 3 N A) = 3 * 3 ^ CFSG.Open.pRank 3 F := by
    rw [card_barX_of_isPGroup hp hAN (A_el h).isPGroup, card_A_of_ne hp hs hFA,
      card_eq_pow_pRank hp ((A_el h).mono hFA')]
  have hker : κA.ker ≠ ⊥ := by
    intro hbot
    have : xA ∈ κA.ker := hκx
    rw [hbot, Subgroup.mem_bot] at this
    exact hx1 (congrArg Subtype.val this)
  have hrange : Nat.card κA.range ≤ 3 ^ CFSG.Open.pRank 3 F := by
    have h1 : κA.ker.index * Nat.card κA.ker = Nat.card (barX 3 N A) := Subgroup.index_mul_card _
    rw [Subgroup.index_ker, hAcard] at h1
    have hdvd : Nat.card κA.ker ∣ 3 ^ (CFSG.Open.pRank 3 F + 1) := by
      rw [pow_succ, mul_comm, ← hAcard]
      exact Subgroup.card_subgroup_dvd_card κA.ker
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hj0 : j ≠ 0 := by
      intro hj0
      rw [hj0, pow_zero] at hj
      exact hker (Subgroup.card_eq_one.1 hj)
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    rw [hj, pow_succ] at h1
    have h2 : Nat.card κA.range * 3 ^ j' = 3 ^ CFSG.Open.pRank 3 F := by
      have : 3 * (Nat.card κA.range * 3 ^ j') = 3 * 3 ^ CFSG.Open.pRank 3 F := by
        rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    calc Nat.card κA.range ≤ Nat.card κA.range * 3 ^ j' :=
          Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
      _ = 3 ^ CFSG.Open.pRank 3 F := h2
  have hFle : ∀ f : ↥(barX 3 N F), (f : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈ barX 3 N A :=
    fun f => barX_mono129 hFA' f.2
  have hκeq : ∀ f : ↥(barX 3 N F), κA ⟨f, hFle f⟩ = D'.κ f := by
    intro f
    apply impl_unique (by omega) D'.ψ
    intro y
    rw [← hκA ⟨f, hFle f⟩ y, ← D'.hκ f y]
  have hlerange : D'.κ.range ≤ κA.range := by
    rintro _ ⟨f, rfl⟩
    exact ⟨⟨f, hFle f⟩, hκeq f⟩
  have hFrange : Nat.card D'.κ.range = 3 ^ CFSG.Open.pRank 3 F := by
    rw [← hFcard]
    exact (Nat.card_congr (MonoidHom.ofInjective (D'.κ_injective hp.pos)).toEquiv).symm
  have hrangeeq : D'.κ.range = κA.range :=
    Subgroup.eq_of_le_of_card_ge hlerange (by rw [hFrange]; exact hrange)
  have hΩ3 : 3 ≤ D'.Ω₀.ncard := by rw [D'.hΩ₀, hδ4]; norm_num
  obtain ⟨τ₀, hτ₀, hτ₀supp, a₀, ha₀, hτ₀a⟩ := exists_three_cycle_in hΩ3
  have hτ₀A : τ₀ ∈ alternatingGroup (Fin D'.n) := Equiv.Perm.mem_alternatingGroup.2 hτ₀.sign
  set τ : ↥(barX 3 N K) := D'.ψ.symm ⟨τ₀, hτ₀A⟩ with hτdef
  have hψτ : D'.ψ τ = ⟨τ₀, hτ₀A⟩ := D'.ψ.apply_symm_apply _
  have hτ3 : (τ : ↥N ⧸ GLAPPrimeCore 3 ↥N) ^ 3 = 1 := by
    have : τ ^ 3 = 1 := by
      apply D'.ψ.injective
      rw [map_pow, hψτ, map_one]
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      have := pow_orderOf_eq_one τ₀
      rwa [hτ₀.orderOf] at this
    have := congrArg Subtype.val this
    simpa using this
  have hcomm : ∀ a : ↥(barX 3 N A), ((κA a : ↥(barX 3 N K)) : ↥N ⧸ GLAPPrimeCore 3 ↥N) *
      (τ : ↥N ⧸ GLAPPrimeCore 3 ↥N) = (τ : ↥N ⧸ GLAPPrimeCore 3 ↥N) *
        ((κA a : ↥(barX 3 N K)) : ↥N ⧸ GLAPPrimeCore 3 ↥N) := by
    intro a
    have hmem : κA a ∈ D'.κ.range := by rw [hrangeeq]; exact ⟨a, rfl⟩
    obtain ⟨f, hf⟩ := hmem
    rw [← hf]
    have hdisj : Equiv.Perm.Disjoint τ₀ ((D'.ψ (D'.κ f) : alternatingGroup (Fin D'.n)) :
        Equiv.Perm (Fin D'.n)) := by
      intro j
      by_cases hj : j ∈ D'.Ω₀
      · right; exact D'.hfix f j hj
      · left; exact hτ₀supp j hj
    have hc := hdisj.commute
    have : (D'.κ f) * τ = τ * (D'.κ f) := by
      apply D'.ψ.injective
      rw [map_mul, map_mul, hψτ]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hc.symm.eq
    have := congrArg Subtype.val this
    simpa using this
  have hτA : (τ : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈ barX 3 N A :=
    mem_of_commute_implementers hAbar κA hκA hτ3 hcomm
  have hκτ : κA ⟨τ, hτA⟩ = τ := by
    apply impl_unique (by omega) D'.ψ
    intro y
    rw [← hκA ⟨τ, hτA⟩ y]
  have hτr : τ ∈ D'.κ.range := by
    rw [hrangeeq]
    exact ⟨⟨τ, hτA⟩, hκτ⟩
  obtain ⟨f, hf⟩ := hτr
  have h1 := D'.hfix f a₀ ha₀
  rw [hf, hψτ] at h1
  exact hτ₀a h1

theorem alt_le_K (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (D' : AltData p N K F) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hFA : F ≠ A)
    (hp3 : p = 3) (hδ4 : D'.δ = 4) : barX p N A ≤ barX p N K := by
  have hcen := alt_centralizer_trivial h hs D' hAK hFA hp3 hδ4
  subst hp3
  have hp := prime_of h
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 := ne_two_of h
  have hAN := A_le_N h
  have hn11 := D'.hn11 (le_refl 3) hs.hr
  have hAbar : IsSCp 3 ⊤ (barX 3 N A) := Lemma129b.barX_A_isSCp h
  have hĀN : barX 3 N A ≤ Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    barX_le_normalizer hAK
  have hĀp : IsPGroup 3 ↥(barX 3 N A) := Lemma129.isPGroup_barX (A_el h).isPGroup hAN
  have hĀel : IsElemAbelian 3 (barX 3 N A) := isElemAbelian_barX (A_el h)
  obtain ⟨κA, hκA⟩ := exists_implementer (by omega) (by omega) D'.ψ hp hp2 hĀN hĀp
  intro y hy
  set z : ↥(barX 3 N K) := κA ⟨y, hy⟩ with hz
  have hz3 : (z : ↥N ⧸ GLAPPrimeCore 3 ↥N) ^ 3 = 1 := by
    have : z ^ 3 = 1 := by
      rw [hz, ← map_pow]
      have : (⟨y, hy⟩ : ↥(barX 3 N A)) ^ 3 = 1 := Subtype.ext (hĀel.2 y hy)
      rw [this, map_one]
    have := congrArg Subtype.val this
    simpa using this
  have hcomm : ∀ a : ↥(barX 3 N A), ((κA a : ↥(barX 3 N K)) : ↥N ⧸ GLAPPrimeCore 3 ↥N) *
      (z : ↥N ⧸ GLAPPrimeCore 3 ↥N) = (z : ↥N ⧸ GLAPPrimeCore 3 ↥N) *
        ((κA a : ↥(barX 3 N K)) : ↥N ⧸ GLAPPrimeCore 3 ↥N) := by
    intro a
    have : κA a * z = z * κA a := by
      rw [hz, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hĀel.comm a.2 hy)
    have := congrArg Subtype.val this
    simpa using this
  have hzA : (z : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈ barX 3 N A :=
    mem_of_commute_implementers hAbar κA hκA hz3 hcomm
  have hw : (z : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ * y = 1 := by
    refine hcen _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hzA) hy) fun k hk => ?_
    have h1 := hκA ⟨y, hy⟩ ⟨k, hk⟩
    simp only at h1
    calc (z : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ * y * k
        = (z : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ * (y * k * y⁻¹) * y := by group
      _ = (z : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ * ((z : ↥N ⧸ GLAPPrimeCore 3 ↥N) * k *
            (z : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹) * y := by rw [h1]
      _ = k * ((z : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ * y) := by group
  have : y = (z : ↥N ⧸ GLAPPrimeCore 3 ↥N) := by
    have := congrArg ((z : ↥N ⧸ GLAPPrimeCore 3 ↥N) * ·) hw
    simpa using this
  rw [this]
  exact z.2

@[expose] def permImage {p : ℕ} {N K : Subgroup G} {n : ℕ}
    (ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)) (H : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  (H.subgroupOf (barX p N K)).map ((alternatingGroup (Fin n)).subtype.comp ψ.toMonoidHom)

theorem mem_permImage {p : ℕ} {N K : Subgroup G} {n : ℕ}
    (ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)) {H : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)}
    {g : Equiv.Perm (Fin n)} :
    g ∈ permImage ψ H ↔ ∃ (x : ↥(barX p N K)), (x : ↥N ⧸ GLAPPrimeCore p ↥N) ∈ H ∧
      ((ψ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = g := by
  unfold permImage
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]

theorem permImage_mono {p : ℕ} {N K : Subgroup G} {n : ℕ}
    (ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)) {H H' : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)}
    (hHH : H ≤ H') : permImage ψ H ≤ permImage ψ H' := by
  intro g hg
  obtain ⟨x, hx, hxg⟩ := (mem_permImage ψ).1 hg
  exact (mem_permImage ψ).2 ⟨x, hHH hx, hxg⟩

theorem permImage_le_alt {p : ℕ} {N K : Subgroup G} {n : ℕ}
    (ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)) {H : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)} :
    permImage ψ H ≤ alternatingGroup (Fin n) := by
  intro g hg
  obtain ⟨x, -, rfl⟩ := (mem_permImage ψ).1 hg
  exact (ψ x).2

theorem permImage_injective {p : ℕ} {N K : Subgroup G} {n : ℕ}
    (ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)) :
    Function.Injective ((alternatingGroup (Fin n)).subtype.comp ψ.toMonoidHom) := by
  intro x y hxy
  apply ψ.injective
  exact Subtype.ext hxy

theorem permImage_card {p : ℕ} {N K : Subgroup G} {n : ℕ}
    (ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)) {H : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)}
    (hHK : H ≤ barX p N K) : Nat.card (permImage ψ H) = Nat.card H := by
  unfold permImage
  rw [Subgroup.card_map_of_injective (permImage_injective ψ)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv

theorem permImage_elemAbelian {p : ℕ} {N K : Subgroup G} {n : ℕ}
    (ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)) {H : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)}
    (hH : IsElemAbelian p H) : IsElemAbelian p (permImage ψ H) :=
  (hH.subgroupOf _).map _

theorem permImage_zpowers {p : ℕ} {N K : Subgroup G} {n : ℕ}
    (ψ : ↥(barX p N K) ≃* alternatingGroup (Fin n)) (x : ↥(barX p N K)) :
    permImage ψ (Subgroup.zpowers (x : ↥N ⧸ GLAPPrimeCore p ↥N)) =
      Subgroup.zpowers ((ψ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
  ext g
  rw [mem_permImage]
  constructor
  · rintro ⟨x', hx', rfl⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hx'
    have : x' = x ^ z := Subtype.ext (by rw [← hz]; rfl)
    rw [this, map_zpow]
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨x ^ z, ⟨z, rfl⟩, ?_⟩
    rw [map_zpow]
    rfl

theorem alt_structure (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (D' : AltData p N K F) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hFA : F ≠ A)
    (hp3 : p = 3) (hδ4 : D'.δ = 4) :
    D'.m = 1 ∧
      (∀ j k : Fin D'.n, j ∉ D'.Ω₀ → k ∉ D'.Ω₀ →
        ∃! g : Equiv.Perm (Fin D'.n), g ∈ permImage D'.ψ (barX p N F) ∧ g j = k) ∧
      ∃ a ∈ A, A = F ⊔ Subgroup.zpowers a ∧ F ⊓ Subgroup.zpowers a = ⊥ ∧
        ∃ σ : Equiv.Perm (Fin D'.n), σ.IsThreeCycle ∧ (∀ j, j ∉ D'.Ω₀ → σ j = j) ∧
          permImage D'.ψ (barX p N (Subgroup.zpowers a)) = Subgroup.zpowers σ := by
  have hle := alt_le_K h hs D' hAK hFA hp3 hδ4
  subst hp3
  have hp := prime_of h
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 := ne_two_of h
  have hAN := A_le_N h
  have hFA' := hs.F_le_A
  have hFN : F ≤ N := hFA'.trans hAN
  have hn11 := D'.hn11 (le_refl 3) hs.hr
  have hAbar : IsSCp 3 ⊤ (barX 3 N A) := Lemma129b.barX_A_isSCp h
  have hFK : barX 3 N F ≤ barX 3 N K := (barX_mono129 hFA').trans hle
  have hκself : ∀ f : ↥(barX 3 N F), D'.κ f = ⟨(f : ↥N ⧸ GLAPPrimeCore 3 ↥N), hFK f.2⟩ := by
    intro f
    apply impl_unique (by omega) D'.ψ
    intro x
    rw [← D'.hκ f x]
  have hFperm : ∀ g ∈ permImage D'.ψ (barX 3 N F), ∃ f : ↥(barX 3 N F),
      g = ((D'.ψ (D'.κ f) : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := (mem_permImage D'.ψ).1 hg
    refine ⟨⟨(x : ↥N ⧸ GLAPPrimeCore 3 ↥N), hx⟩, ?_⟩
    rw [hκself]
  have hn4 : D'.n = D'.m * 3 ^ CFSG.Open.pRank 3 F + 4 := by
    have := D'.hn
    rwa [hδ4] at this
  have hFel : IsElemAbelian 3 F := (A_el h).mono hFA'
  have hFbel : IsElemAbelian 3 (barX 3 N F) := isElemAbelian_barX hFel
  have hAbel : IsElemAbelian 3 (barX 3 N A) := isElemAbelian_barX (A_el h)
  have hFcard : Nat.card (barX 3 N F) = 3 ^ CFSG.Open.pRank 3 F := by
    rw [card_barX_of_isPGroup hp hFN hFel.isPGroup, card_eq_pow_pRank hp hFel]
  have hAcard : Nat.card (barX 3 N A) = 3 ^ (CFSG.Open.pRank 3 F + 1) := by
    rw [card_barX_of_isPGroup hp hAN (A_el h).isPGroup, card_A_of_ne hp hs hFA,
      card_eq_pow_pRank hp hFel, pow_succ, mul_comm]
  have hmax : ∀ Y' : Subgroup (Equiv.Perm (Fin D'.n)), Y' ≤ alternatingGroup (Fin D'.n) →
      IsElemAbelian 3 Y' → permImage D'.ψ (barX 3 N A) ≤ Y' → Y' = permImage D'.ψ (barX 3 N A) := by
    intro Y' hY'A hY'el hXY'
    set ν : ↥(barX 3 N K) →* Equiv.Perm (Fin D'.n) :=
      (alternatingGroup (Fin D'.n)).subtype.comp D'.ψ.toMonoidHom with hν
    have hνinj : Function.Injective ν := permImage_injective D'.ψ
    set Zk : Subgroup ↥(barX 3 N K) := Y'.comap ν with hZk
    have hZkel : IsElemAbelian 3 Zk := hY'el.comap hνinj
    set Zk' : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N) := Zk.map (barX 3 N K).subtype with hZk'
    have hZk'el : IsElemAbelian 3 Zk' := hZkel.map _
    have hĀZ : barX 3 N A ≤ Zk' := by
      intro y hy
      refine ⟨⟨y, hle hy⟩, ?_, rfl⟩
      show ν ⟨y, hle hy⟩ ∈ Y'
      exact hXY' ((mem_permImage D'.ψ).2 ⟨⟨y, hle hy⟩, hy, rfl⟩)
    have hZ'eq : Zk' = barX 3 N A := hAbar.2.2 Zk' le_top hZk'el hĀZ
    apply le_antisymm _ hXY'
    intro g hg
    have hgA := hY'A hg
    obtain ⟨x, hx⟩ := D'.ψ.surjective ⟨g, hgA⟩
    have hxg : ν x = g := by
      show ((D'.ψ x : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) = g
      rw [hx]
    have hxZ : x ∈ Zk := by
      show ν x ∈ Y'
      rw [hxg]; exact hg
    have : (x : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈ Zk' := ⟨x, hxZ, rfl⟩
    rw [hZ'eq] at this
    exact (mem_permImage D'.ψ).2 ⟨x, this, hxg⟩
  obtain ⟨hm1, htrans, σ, hσ3, hσsupp, hXeq, hdisj⟩ := Lemma129P.permA hs.hr D'.hm hn4 D'.Ω₀
    (by rw [D'.hΩ₀, hδ4])
    (permImage D'.ψ (barX 3 N F)) (permImage D'.ψ (barX 3 N A))
    (permImage_elemAbelian D'.ψ hFbel)
    (by rw [permImage_card D'.ψ hFK, hFcard])
    (by
      intro g hg j hj
      obtain ⟨f, rfl⟩ := hFperm g hg
      exact D'.hfix f j hj)
    (by
      intro g hg hg1 j hj
      obtain ⟨f, rfl⟩ := hFperm g hg
      have hf1 : f ≠ 1 := by
        intro hf
        apply hg1
        rw [hf, map_one]
        simp
      exact D'.hsemi f hf1 j hj)
    (permImage_le_alt D'.ψ) (permImage_elemAbelian D'.ψ hAbel)
    (permImage_mono D'.ψ (barX_mono129 hFA'))
    (by rw [permImage_card D'.ψ hle, hAcard]) hmax
  refine ⟨hm1, htrans, ?_⟩
  have hσX : σ ∈ permImage D'.ψ (barX 3 N A) := by
    rw [hXeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
  obtain ⟨x, hxA, hxσ⟩ := (mem_permImage D'.ψ).1 hσX
  obtain ⟨⟨a, haN⟩, haA', hax⟩ := hxA
  have haA : a ∈ A := (Subgroup.mem_subgroupOf).1 haA'
  have hAinj : ∀ u (huA : u ∈ A), QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨u, hAN huA⟩ = 1 →
      u = 1 := by
    intro u huA hu1
    have hinj := injective_barX_comp hp (A_el h).isPGroup hAN
    have : (⟨⟨u, hAN huA⟩, (Subgroup.mem_subgroupOf).2 huA⟩ : ↥(A.subgroupOf N)) = 1 :=
      hinj (by simpa using hu1)
    exact congrArg (fun w : ↥(A.subgroupOf N) => ((w : ↥N) : G)) this
  have hσ1 : σ ≠ 1 := by
    intro h1
    have := hσ3.orderOf
    rw [h1, orderOf_one] at this
    omega
  have hbz : barX 3 N (Subgroup.zpowers a) =
      Subgroup.zpowers (x : ↥N ⧸ GLAPPrimeCore 3 ↥N) := by
    rw [Lemma129b.barX_zpowers haN, hax]
  have hperm : permImage D'.ψ (barX 3 N (Subgroup.zpowers a)) = Subgroup.zpowers σ := by
    rw [hbz, permImage_zpowers, hxσ]
  have ha1 : a ≠ 1 := by
    intro ha1
    apply hσ1
    rw [← hxσ]
    have hx1 : x = 1 := by
      apply Subtype.ext
      rw [← hax, show (⟨a, haN⟩ : ↥N) = 1 from Subtype.ext ha1, map_one]
      rfl
    rw [hx1, map_one]
    rfl
  have hap : a ^ 3 = 1 := (A_el h).2 a haA
  have hord : orderOf a = 3 := orderOf_eq_prime hap ha1
  have hFa : F ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huF, hu⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hu
    have huA : u ∈ A := hFA' huF
    have huN : u ∈ N := hAN huA
    have hu_eq : (⟨u, huN⟩ : ↥N) = (⟨a, haN⟩ : ↥N) ^ z := Subtype.ext (by simpa using hz.symm)
    have hπu : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨u, huN⟩ = (x : ↥N ⧸ GLAPPrimeCore 3 ↥N) ^ z := by
      rw [hu_eq, map_zpow, hax]
    have huF' : (x : ↥N ⧸ GLAPPrimeCore 3 ↥N) ^ z ∈ barX 3 N F := by
      rw [← hπu]
      exact ⟨⟨u, huN⟩, (Subgroup.mem_subgroupOf).2 huF, rfl⟩
    have hmemF : ((D'.ψ (x ^ z) : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) ∈
        permImage D'.ψ (barX 3 N F) := (mem_permImage D'.ψ).2 ⟨x ^ z, huF', rfl⟩
    have hmemσ : ((D'.ψ (x ^ z) : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) ∈
        Subgroup.zpowers σ := by
      rw [map_zpow, ← hxσ]
      exact ⟨z, rfl⟩
    have hbot : ((D'.ψ (x ^ z) : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) = 1 := by
      have : ((D'.ψ (x ^ z) : alternatingGroup (Fin D'.n)) : Equiv.Perm (Fin D'.n)) ∈
          permImage D'.ψ (barX 3 N F) ⊓ Subgroup.zpowers σ := ⟨hmemF, hmemσ⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact this
    have hxz1 : x ^ z = 1 := by
      apply D'.ψ.injective
      apply Subtype.ext
      rw [hbot, map_one]
      rfl
    have hπ1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨u, huN⟩ = 1 := by
      rw [hπu]
      have := congrArg Subtype.val hxz1
      simpa using this
    rw [Subgroup.mem_bot]
    exact hAinj u huA hπ1
  have hAeq : A = F ⊔ Subgroup.zpowers a := by
    apply le_antisymm _ (sup_le hFA' (Subgroup.zpowers_le.2 haA))
    have hle2 : F ⊔ Subgroup.zpowers a ≤ A := sup_le hFA' (Subgroup.zpowers_le.2 haA)
    have hcard : Nat.card ↥(F ⊔ Subgroup.zpowers a) = Nat.card A := by
      rw [Lemma129b.card_sup_of_commute_disjoint (fun u hu b hb => ?_) hFa, card_A_of_ne hp hs hFA,
        Nat.card_zpowers, hord, mul_comm]
      exact elemAbelian_comm (A_el h) (hFA' hu) ((Subgroup.zpowers_le.2 haA) hb)
    exact (Subgroup.eq_of_le_of_card_ge hle2 (le_of_eq hcard.symm)).symm.le
  exact ⟨a, haA, hAeq, hFa, σ, hσ3, hσsupp, hperm⟩

end AltDataSec


end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d

end
