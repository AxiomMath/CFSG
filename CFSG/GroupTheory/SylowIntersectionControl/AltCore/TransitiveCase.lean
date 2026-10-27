module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Diagonal
public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Commute
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.GLIsolated
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.GLSquares
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Radical
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction
open CFSG.Quasithin (omegaOneCenterOf)

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
private theorem omegaOneCenter_comm (K : Subgroup (Perm α)) :
    ∀ e ∈ omegaOneCenterOf K, ∀ f ∈ omegaOneCenterOf K, e * f = f * e := fun _ he _ hf =>
  omegaOneCenter_commute K he (omegaOneCenter_le K hf)

omit [DecidableEq α] in
private theorem exists_card_orbit_eq_two_pow {E : Subgroup (Perm α)} (hE : IsPGroup 2 E)
    (x : α) : ∃ j, Nat.card (orbit E x) = 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hE.exists_card_eq
  have h1 : (stabilizer E x).index ∣ Nat.card E := index_dvd_card _
  rw [index_stabilizer, hm] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact ⟨j, by rw [Nat.card_coe_set_eq, hj]⟩

private theorem mem_M_of_mem_normalizer {K M : Subgroup (Perm α)} {Δ : Set α} (hKM : K ≤ M)
    (hKΔ : K ≤ fixOutside Δ)
    (hML : normalizer (K : Set (Perm α)) ⊓ fixOutside Δ ⊓ alternatingGroup α ≤ M) {g : Perm α}
    (hg : g ∈ normalizer (K : Set (Perm α))) (hgΔ : g ∈ fixOutside Δ)
    (hcase : g ∈ alternatingGroup α ∨ ∃ k ∈ K, k ∉ alternatingGroup α) : g ∈ M := by
  rcases hcase with hg2 | ⟨k, hk, hk2⟩
  · exact hML ⟨⟨hg, hgΔ⟩, hg2⟩
  · by_cases hg2 : g ∈ alternatingGroup α
    · exact hML ⟨⟨hg, hgΔ⟩, hg2⟩
    · have hgk : g * k ∈ alternatingGroup α := by
        rw [mem_alternatingGroup, map_mul] at *
        rcases Int.units_eq_one_or (sign g) with h | h
        · exact absurd h hg2
        · rcases Int.units_eq_one_or (sign k) with h' | h'
          · exact absurd h' hk2
          · rw [h, h']
            rfl
      have := hML ⟨⟨mul_mem hg (le_normalizer hk), mul_mem hgΔ (hKΔ hk)⟩, hgk⟩
      have hk' := hKM hk
      simpa using mul_mem this (inv_mem hk')

private theorem le_normalizer_sup {G : Type*} [Group G] {N A B : Subgroup G}
    (hA : N ≤ normalizer (A : Set G)) (hB : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun n hn d hd => ?_
  have hmap : (A ⊔ B).map (MulAut.conj n).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (mem_normalizer_iff.mp (hA hn) a).mp ha
    · rintro _ ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp (hB hn) b).mp hb
  exact hmap ⟨d, hd, rfl⟩

omit [Fintype α] [DecidableEq α] in
private theorem apply_mem_of_mem_fixOutside {Δ : Set α} {g : Perm α} (hg : g ∈ fixOutside Δ)
    {b : α} (hb : b ∈ Δ) : g b ∈ Δ := by
  by_contra h
  exact h (by rw [g.injective (hg (g b) h)]; exact hb)

omit [Fintype α] [DecidableEq α] in
private theorem blockBase_le_fixOutside {K : Subgroup (Perm α)} {Δ : Set α}
    (hKΔ : K ≤ fixOutside Δ) : blockBase (omegaOneCenterOf K) ≤ fixOutside Δ := fun g hg y hy => by
  obtain ⟨e, he, hge⟩ := hg y
  rw [hge y (mem_orbit_self y)]
  exact hKΔ (omegaOneCenter_le K he) y hy

omit [Fintype α] [DecidableEq α] in
private theorem not_mem_orbit_of_not_mem {K : Subgroup (Perm α)} {Δ : Set α}
    (hKΔ : K ≤ fixOutside Δ) {b y : α} (hb : b ∈ Δ) (hy : y ∉ Δ) :
    ∀ k ∈ K, k b ∉ orbit (omegaOneCenterOf K) y := fun k hk h => by
  obtain ⟨⟨e, he⟩, hey⟩ := h
  have h1 : e y = y := hKΔ (omegaOneCenter_le K he) y hy
  have h2 : k b ∈ Δ := apply_mem_of_mem_fixOutside (hKΔ hk) hb
  change e y = k b at hey
  rw [h1] at hey
  exact hy (hey ▸ h2)

theorem blockBase_omegaOneCenter_le {K M : Subgroup (Perm α)} {Δ : Set α} (hK : IsPGroup 2 K)
    (hKM : K ≤ M) (hMN : M ≤ normalizer (K : Set (Perm α))) (hKΔ : K ≤ fixOutside Δ)
    (hML : normalizer (K : Set (Perm α)) ⊓ fixOutside Δ ⊓ alternatingGroup α ≤ M)
    (hiso : IsPIsolatedOver 2 M K) (h4 : ∀ x : α, Nat.card (orbit (omegaOneCenterOf K) x) = 1 ∨
      4 ∣ Nat.card (orbit (omegaOneCenterOf K) x)) :
    blockBase (omegaOneCenterOf K) ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := omegaOneCenterOf K
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := fun e he => omegaOneCenter_sq K he
  have hBp : IsPGroup 2 (blockBase E) := isPGroup_blockBase hE2
  have hBL : blockBase E ≤ alternatingGroup α :=
    blockBase_le_alternatingGroup hE2 (omegaOneCenter_comm K) h4
  have hNB : normalizer (K : Set (Perm α)) ≤ normalizer (blockBase E : Set (Perm α)) :=
    (normalizer_le_normalizer_omegaOneCenterOf K).trans (normalizer_le_normalizer_blockBase E)
  have hD : IsPGroup 2 (K ⊔ blockBase E : Subgroup (Perm α)) :=
    hK.to_sup_of_normal_right' hBp (le_normalizer.trans hNB)
  have hPM : (K ⊔ blockBase E) ⊓ normalizer (K : Set (Perm α)) ≤ M := by
    rintro g ⟨hgD, hgN⟩
    have hgΔ : g ∈ fixOutside Δ := sup_le hKΔ (blockBase_le_fixOutside hKΔ) hgD
    by_cases hKL : K ≤ alternatingGroup α
    · exact mem_M_of_mem_normalizer hKM hKΔ hML hgN hgΔ (Or.inl (sup_le hKL hBL hgD))
    · obtain ⟨k, hk, hk2⟩ := SetLike.not_le_iff_exists.mp hKL
      exact mem_M_of_mem_normalizer hKM hKΔ hML hgN hgΔ (Or.inr ⟨k, hk, hk2⟩)
  have hMP : M ≤ normalizer (((K ⊔ blockBase E) ⊓ normalizer (K : Set (Perm α)) :
      Subgroup (Perm α)) : Set (Perm α)) :=
    le_normalizer_of_conj_mem fun m hm d hd => mem_inf.mpr
      ⟨(mem_normalizer_iff.mp (le_normalizer_sup hMN (hMN.trans hNB) hm) d).mp (mem_inf.mp hd).1,
        mul_mem (mul_mem (hMN hm) (mem_inf.mp hd).2) (inv_mem (hMN hm))⟩
  have hPK := IsPIsolatedOver.le_of_normal hiso hK hKM hMN hPM (hD.to_le inf_le_left) hMP
  exact le_sup_right.trans (le_of_inf_normalizer_le_of_isPGroup hD le_sup_left hPK)

omit [Fintype α] [DecidableEq α] in
private theorem mem_orbit_iff'' {E : Subgroup (Perm α)} {x y : α} :
    y ∈ orbit E x ↔ ∃ e ∈ E, e x = y :=
  ⟨fun ⟨⟨e, he⟩, h⟩ => ⟨e, he, h⟩, fun ⟨e, he, h⟩ => ⟨⟨e, he⟩, h⟩⟩

omit [Fintype α] [DecidableEq α] in
private theorem apply_mem_orbit_of_commute {E : Subgroup (Perm α)} {k : Perm α}
    (hk : ∀ e ∈ E, e * k = k * e) {x y : α} (hy : y ∈ orbit E x) : k y ∈ orbit E (k x) := by
  obtain ⟨e, he, rfl⟩ := mem_orbit_iff''.mp hy
  refine mem_orbit_iff''.mpr ⟨e, he, ?_⟩
  rw [← Perm.mul_apply, hk e he, Perm.mul_apply]

@[expose] noncomputable def localConj (E : Subgroup (Perm α)) (x₀ : α) (S : Subgroup (Perm α))
    (hS : ∀ m ∈ S, m ∈ normalizer (E : Set (Perm α)) ∧ m x₀ ∈ orbit E x₀) :
    S →* MulAut (localBase E x₀) where
  toFun m :=
    { toFun := fun u => ⟨m * u * (m : Perm α)⁻¹, conj_mem_localBase (hS m m.2).1 (hS m m.2).2 u.2⟩
      invFun := fun u => ⟨(m : Perm α)⁻¹ * u * m, by
        have := conj_mem_localBase (hS _ (inv_mem m.2)).1 (hS _ (inv_mem m.2)).2 u.2
        simpa only [inv_inv] using this⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext u
    simp
  map_mul' m m' := by
    ext u
    simp [mul_assoc]

omit [Fintype α] [DecidableEq α] in
theorem localConj_apply {E : Subgroup (Perm α)} {x₀ : α} {S : Subgroup (Perm α)}
    {hS : ∀ m ∈ S, m ∈ normalizer (E : Set (Perm α)) ∧ m x₀ ∈ orbit E x₀} (m : S)
    (u : localBase E x₀) :
    ((localConj E x₀ S hS m u : localBase E x₀) : Perm α) = m * u * (m : Perm α)⁻¹ :=
  rfl

omit [Fintype α] [DecidableEq α] in
private theorem actsE_of_comm {E : Subgroup (Perm α)} (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    {x₀ : α} {m : Perm α} (hm : m ∈ blockKer E)
    (hc : ∀ u ∈ localBase E x₀, m * u = u * m) : ∃ e ∈ E, ∀ y ∈ orbit E x₀, m y = e y := by
  obtain ⟨⟨u₀, hu₀⟩, hu₀x, -⟩ := localBase_regular hEab x₀ (hm x₀)
  obtain ⟨e₀, he₀, h₀⟩ := (mem_inf.mp hu₀).1 x₀
  refine ⟨e₀, he₀, fun y hy => ?_⟩
  obtain ⟨⟨u, hu⟩, hux, -⟩ := localBase_regular hEab x₀ hy
  simp only at hux hu₀x
  have hcomm : u * u₀ = u₀ * u := congrArg Subtype.val (localBase_comm hEab x₀ ⟨u, hu⟩ ⟨u₀, hu₀⟩)
  calc m y = (m * u) x₀ := by rw [Perm.mul_apply, hux]
    _ = (u * u₀) x₀ := by rw [hc u hu, Perm.mul_apply, Perm.mul_apply, hu₀x]
    _ = u₀ y := by rw [hcomm, Perm.mul_apply, hux]
    _ = e₀ y := h₀ y hy

omit [Fintype α] [DecidableEq α] in
private theorem mem_normalizer_of_commute {E : Subgroup (Perm α)} {k : Perm α}
    (hk : ∀ e ∈ E, e * k = k * e) : k ∈ normalizer (E : Set (Perm α)) := by
  refine mem_normalizer_iff.mpr fun e => ⟨fun he => ?_, fun he => ?_⟩
  · rwa [← hk e he, mul_inv_cancel_right]
  · have h := hk _ he
    have h2 : k * e * k⁻¹ * k = k * e := by group
    rw [h2] at h
    have : e = k * e * k⁻¹ := mul_left_cancel h
    rwa [this]

omit [Fintype α] [DecidableEq α] in
private theorem mul_mem_orbit {E : Subgroup (Perm α)} {e : Perm α} (he : e ∈ E) {x z : α}
    (hz : z ∈ orbit E x) : e z ∈ orbit E x := by
  obtain ⟨f, hf, rfl⟩ := mem_orbit_iff''.mp hz
  exact mem_orbit_iff''.mpr ⟨e * f, mul_mem he hf, rfl⟩

omit [Fintype α] [DecidableEq α] in
private theorem actsE_of_comm_of_mem {E K : Subgroup (Perm α)}
    (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hEK : ∀ e ∈ E, ∀ k ∈ K, e * k = k * e)
    {x₀ : α} {m : Perm α} (hm : m ∈ blockKer E) (hmN : m ∈ normalizer (K : Set (Perm α)))
    (hc : ∀ u ∈ localBase E x₀, m * u = u * m) {k : Perm α} (hk : k ∈ K) :
    ∃ e ∈ E, ∀ z ∈ orbit E (k x₀), m z = e z := by
  obtain ⟨e₀, he₀, h₀⟩ := actsE_of_comm hEab hm hc
  have hkE : ∀ e ∈ E, e * k = k * e := fun e he => hEK e he k hk
  set c := m * k * m⁻¹ * k⁻¹ with hcdef
  have hcK : c ∈ K := mul_mem ((mem_normalizer_iff.mp hmN k).mp hk) (inv_mem hk)
  have hcB : c ∈ blockKer E := by
    have h1 : k * m⁻¹ * k⁻¹ ∈ blockKer E := (mem_normalizer_iff.mp
      (normalizer_le_normalizer_blockKer E (mem_normalizer_of_commute hkE)) _).mp (inv_mem hm)
    rw [show c = m * (k * m⁻¹ * k⁻¹) by rw [hcdef]; group]
    exact mul_mem hm h1
  obtain ⟨ec, hec, hc'⟩ := mem_blockBase_of_mem_blockKer hEK hEab hcK hcB (k x₀)
  refine ⟨ec * e₀, mul_mem hec he₀, fun z hz => ?_⟩
  have hy : k⁻¹ z ∈ orbit E x₀ := by
    have := apply_mem_orbit_of_commute (fun e he => hEK e he k⁻¹ (inv_mem hk)) hz
    rwa [show k⁻¹ (k x₀) = x₀ from k.symm_apply_apply x₀] at this
  have e1 : m = c * k * m * k⁻¹ := by rw [hcdef]; group
  have e2 : k (e₀ (k⁻¹ z)) = e₀ z := by
    rw [← Perm.mul_apply, ← hkE e₀ he₀, Perm.mul_apply]
    exact congrArg e₀ (k.apply_symm_apply z)
  conv_lhs => rw [e1]
  simp only [Perm.mul_apply]
  rw [h₀ _ hy, e2, hc' _ (mul_mem_orbit he₀ hz)]

theorem two_dvd_relIndex_of_sq_mem {G : Type*} [Group G] [Finite G] {H K₁ : Subgroup G}
    (hHK : H ≤ K₁) (hKN : K₁ ≤ normalizer (H : Set G)) {x : G} (hx : x ∈ K₁) (hxH : x ∉ H)
    (hx2 : x ^ 2 ∈ H) : 2 ∣ H.relIndex K₁ := by
  have : (H.subgroupOf K₁).Normal := (normal_subgroupOf_iff_le_normalizer hHK).mpr hKN
  have hq1 : QuotientGroup.mk' (H.subgroupOf K₁) ⟨x, hx⟩ ≠ 1 := by
    rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hxH
  have hq2 : (QuotientGroup.mk' (H.subgroupOf K₁) ⟨x, hx⟩) ^ 2 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simpa using hx2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord := orderOf_eq_prime hq2 hq1
  rw [relIndex, index, ← hord]
  exact orderOf_dvd_natCard _

private theorem mem_blockBase_of_comm {E K : Subgroup (Perm α)}
    (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hEK : ∀ e ∈ E, ∀ k ∈ K, e * k = k * e)
    {x₀ : α} {m : Perm α} (hm : m ∈ blockKer E) (hmN : m ∈ normalizer (K : Set (Perm α)))
    (hc : ∀ u ∈ localBase E x₀, m * u = u * m)
    (hfix : ∀ y, (∀ k ∈ K, k x₀ ∉ orbit E y) → m y = y) : m ∈ blockBase E := by
  intro y
  by_cases hy : ∃ k ∈ K, k x₀ ∈ orbit E y
  · obtain ⟨k, hk, hky⟩ := hy
    obtain ⟨e, he, h⟩ := actsE_of_comm_of_mem hEab hEK hm hmN hc hk
    rw [orbit_eq_iff.mpr hky] at h
    exact ⟨e, he, h⟩
  · push Not at hy
    refine ⟨1, one_mem _, fun z hz => ?_⟩
    rw [← orbit_eq_iff.mpr hz] at hy
    rw [hfix z hy, Perm.one_apply]

omit [Fintype α] [DecidableEq α] in
private theorem blockBase_comm_localBase {E : Subgroup (Perm α)}
    (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) {x₀ : α} {g u : Perm α} (hg : g ∈ blockBase E)
    (hu : u ∈ localBase E x₀) : g * u = u * g := by
  obtain ⟨e, he, hge⟩ := hg x₀
  obtain ⟨f, hf, huf⟩ := (mem_inf.mp hu).1 x₀
  have hfix := (mem_inf.mp hu).2
  ext y
  simp only [Perm.mul_apply]
  by_cases hy : y ∈ orbit E x₀
  · rw [huf y hy, hge y hy, hge _ (mul_mem_orbit hf hy), huf _ (mul_mem_orbit he hy),
      ← Perm.mul_apply, ← Perm.mul_apply, hEab e he f hf]
  · have hgy : g y ∉ orbit E x₀ := fun h => hy (by
      obtain ⟨e', he', h'⟩ := hg y
      rw [h' y (mem_orbit_self y)] at h
      have := mul_mem_orbit (inv_mem he') h
      rwa [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply] at this)
    rw [hfix y hy, hfix _ hgy]

private theorem sq_mem_alternatingGroup (d : Perm α) : d ^ 2 ∈ alternatingGroup α := by
  rw [mem_alternatingGroup, map_pow, Int.units_sq]

omit [DecidableEq α] in
private theorem nonempty_mulAut_equiv_GL {E : Subgroup (Perm α)}
    (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hE2 : ∀ e ∈ E, e ^ 2 = 1) {b : α} {j : ℕ}
    (hj : Nat.card (orbit E b) = 2 ^ j) :
    Nonempty (MulAut (localBase E b) ≃* GL (Fin j) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψe⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := localBase E b) (n := j) (fun u v => localBase_comm hEab b u v)
    (fun u => localBase_sq hE2 b u) ((card_localBase hEab b).trans hj)
  exact ⟨CFSG.SectionRank.Ccomm.elemAutEquivGL ψe⟩

private theorem exists_diag_sq_mem {K M : Subgroup (Perm α)} {Δ : Set α} (hKΔ : K ≤ fixOutside Δ)
    (hML : normalizer (K : Set (Perm α)) ⊓ fixOutside Δ ⊓ alternatingGroup α ≤ M)
    (hBK : blockBase (omegaOneCenterOf K) ≤ K) (b : α) (hb : b ∈ Δ)
    (s : MulAut (localBase (omegaOneCenterOf K) b)) :
    ∃ x ∈ M ⊓ blockKer (omegaOneCenterOf K), x ∈ normalizer (K : Set (Perm α)) ∧
      (∀ u : localBase (omegaOneCenterOf K) b, x * (u : Perm α) * x⁻¹ = ((s ^ 2) u : Perm α)) ∧
      ∀ y, (∀ k ∈ K, k b ∉ orbit (omegaOneCenterOf K) y) → x y = y := by
  obtain ⟨d, hdB, hdN, hdc, hdfix⟩ := exists_diag (omegaOneCenter_comm K)
    (fun e he k hk => omegaOneCenter_commute K he hk) (omegaOneCenter_le K) hBK b s
  have hdΔ : d ∈ fixOutside Δ := fun y hy => hdfix y (not_mem_orbit_of_not_mem hKΔ hb hy)
  refine ⟨d ^ 2, mem_inf.mpr ⟨hML (mem_inf.mpr ⟨mem_inf.mpr ⟨pow_mem hdN 2, pow_mem hdΔ 2⟩,
    sq_mem_alternatingGroup d⟩), pow_mem hdB 2⟩, pow_mem hdN 2, fun u => ?_, fun y hy => ?_⟩
  · have e0 : d ^ 2 * (u : Perm α) * (d ^ 2)⁻¹ = d * (d * u * d⁻¹) * d⁻¹ := by
      simp only [pow_two, mul_inv_rev, mul_assoc]
    calc d ^ 2 * (u : Perm α) * (d ^ 2)⁻¹ = d * (d * u * d⁻¹) * d⁻¹ := e0
      _ = d * (s u : Perm α) * d⁻¹ := by rw [hdc u]
      _ = (s (s u) : Perm α) := hdc (s u)
      _ = ((s ^ 2) u : Perm α) := by rw [pow_two]; rfl
  · rw [pow_two, Perm.mul_apply, hdfix y hy, hdfix y hy]

private theorem exists_order_two {K M : Subgroup (Perm α)} {Δ : Set α} (hKΔ : K ≤ fixOutside Δ)
    (hML : normalizer (K : Set (Perm α)) ⊓ fixOutside Δ ⊓ alternatingGroup α ≤ M)
    (hBK : blockBase (omegaOneCenterOf K) ≤ K) {b : α} (hb : b ∈ Δ) {j : ℕ} (hj3 : 3 ≤ j)
    (hj : Nat.card (orbit (omegaOneCenterOf K) b) = 2 ^ j) :
    ∃ x ∈ M ⊓ blockKer (omegaOneCenterOf K), x ∉ blockBase (omegaOneCenterOf K) ∧
      x ^ 2 ∈ blockBase (omegaOneCenterOf K) ∧
      ∀ y, (∀ k ∈ K, k b ∉ orbit (omegaOneCenterOf K) y) → x y = y := by
  have hEab := omegaOneCenter_comm K
  obtain ⟨ψ⟩ := nonempty_mulAut_equiv_GL hEab (fun e he => omegaOneCenter_sq K he) hj
  obtain ⟨g, hg2, hg4⟩ := exists_sq_ne_one_pow_four_eq_one_GL_two hj3
  obtain ⟨x, hxM, hxN, hxc, hxfix⟩ := exists_diag_sq_mem hKΔ hML hBK b hb (ψ.symm g)
  have hs4 : (ψ.symm g) ^ 4 = 1 := by rw [← map_pow, hg4, map_one]
  refine ⟨x, hxM, fun hxB => hg2 ?_, ?_, hxfix⟩
  · have h1 : (ψ.symm g) ^ 2 = 1 := MulEquiv.ext fun u => Subtype.ext (by
      have := hxc u
      rw [blockBase_comm_localBase hEab hxB u.2, mul_assoc, mul_inv_cancel, mul_one] at this
      exact this.symm)
    have := congrArg ψ h1
    rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
  · refine mem_blockBase_of_comm (x₀ := b) hEab (fun e he k hk => omegaOneCenter_commute K he hk)
      (pow_mem (mem_inf.mp hxM).2 2) (pow_mem hxN 2) (fun u hu => ?_) (fun y hy => ?_)
    · have e0 : x ^ 2 * u * (x ^ 2)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by
        simp only [pow_two, mul_inv_rev, mul_assoc]
      have e1 : x ^ 2 * u * (x ^ 2)⁻¹ = u := by
        calc x ^ 2 * u * (x ^ 2)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := e0
          _ = x * (((ψ.symm g) ^ 2) ⟨u, hu⟩ : Perm α) * x⁻¹ := by rw [← hxc ⟨u, hu⟩]
          _ = (((ψ.symm g) ^ 2) (((ψ.symm g) ^ 2) ⟨u, hu⟩) : Perm α) := hxc _
          _ = (((ψ.symm g) ^ 4) ⟨u, hu⟩ : Perm α) := by
            rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]; rfl
          _ = u := by rw [hs4]; rfl
      calc x ^ 2 * u = x ^ 2 * u * (x ^ 2)⁻¹ * x ^ 2 := by rw [inv_mul_cancel_right]
        _ = u * x ^ 2 := by rw [e1]
    · rw [pow_two, Perm.mul_apply, hxfix y hy, hxfix y hy]

private theorem le_normalizer_inf {G : Type*} [Group G] {N A B : Subgroup G}
    (hA : N ≤ normalizer (A : Set G)) (hB : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  le_normalizer_of_conj_mem fun _ hn d hd => mem_inf.mpr
    ⟨(mem_normalizer_iff.mp (hA hn) d).mp (mem_inf.mp hd).1,
      (mem_normalizer_iff.mp (hB hn) d).mp (mem_inf.mp hd).2⟩

omit [Fintype α] [DecidableEq α] in
private theorem inf_blockKer_inf_eq {K M : Subgroup (Perm α)} (hKM : K ≤ M)
    (hBK : blockBase (omegaOneCenterOf K) ≤ K) :
    M ⊓ blockKer (omegaOneCenterOf K) ⊓ K = blockBase (omegaOneCenterOf K) :=
  le_antisymm (fun _ hg => mem_blockBase_of_mem_blockKer
      (fun _ he _ hk => omegaOneCenter_commute K he hk) (omegaOneCenter_comm K)
      (mem_inf.mp hg).2 (mem_inf.mp (mem_inf.mp hg).1).2)
    (le_inf (le_inf (hBK.trans hKM) (blockBase_le_blockKer _)) hBK)

omit [DecidableEq α] in
theorem isPIsolatedOver_inf_blockKer {K M : Subgroup (Perm α)} (hK : IsPGroup 2 K)
    (hKM : K ≤ M) (hMN : M ≤ normalizer (K : Set (Perm α))) (hiso : IsPIsolatedOver 2 M K)
    (hBK : blockBase (omegaOneCenterOf K) ≤ K) {x : Perm α}
    (hx : x ∈ M ⊓ blockKer (omegaOneCenterOf K)) (hxB : x ∉ blockBase (omegaOneCenterOf K))
    (hx2 : x ^ 2 ∈ blockBase (omegaOneCenterOf K)) :
    IsPIsolatedOver 2 (M ⊓ blockKer (omegaOneCenterOf K)) (blockBase (omegaOneCenterOf K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM₀N : M ⊓ blockKer (omegaOneCenterOf K) ≤ normalizer (K : Set (Perm α)) :=
    inf_le_left.trans hMN
  have hMM₀ : M ≤ normalizer ((M ⊓ blockKer (omegaOneCenterOf K) : Subgroup (Perm α)) :
      Set (Perm α)) := le_normalizer_inf le_normalizer
    (hMN.trans ((normalizer_le_normalizer_omegaOneCenterOf K).trans
      (normalizer_le_normalizer_blockKer _)))
  have hY : ((M ⊓ blockKer (omegaOneCenterOf K) ⊔ K).subgroupOf M).IsSubnormal :=
    ((normal_subgroupOf_iff_le_normalizer (sup_le inf_le_left hKM)).mpr
      (le_normalizer_sup hMM₀ hMN)).isSubnormal
  have hxK : x ∉ K := fun hxK => hxB (by
    rw [← inf_blockKer_inf_eq hKM hBK]
    exact mem_inf.mpr ⟨hx, hxK⟩)
  have hp : 2 ∣ K.relIndex (M ⊓ blockKer (omegaOneCenterOf K) ⊔ K) :=
    two_dvd_relIndex_of_sq_mem le_sup_right (sup_le hM₀N le_normalizer) (mem_sup_left hx) hxK
      (hBK hx2)
  have h1 := hiso.of_isSubnormal_le_over hK hMN le_sup_right le_rfl (sup_le inf_le_left hKM) hY hp
  rw [isPIsolatedOver_sup_iff hK hM₀N, inf_blockKer_inf_eq hKM hBK] at h1
  exact h1

omit [Fintype α] [DecidableEq α] in
private theorem inv_apply_eq {E : Subgroup (Perm α)} {g e : Perm α} (he : e ∈ E) {y : α}
    (hg : ∀ z ∈ orbit E y, g z = e z) {z : α} (hz : z ∈ orbit E y) : g⁻¹ z = e⁻¹ z := by
  rw [Perm.inv_eq_iff_eq, hg _ (mul_mem_orbit (E.inv_mem he) hz), ← Perm.mul_apply,
    mul_inv_cancel, Perm.one_apply]

omit [Fintype α] [DecidableEq α] in
private theorem blockKer_apply_mem {E : Subgroup (Perm α)} {g : Perm α} (hg : g ∈ blockKer E)
    {y z : α} (hz : z ∈ orbit E y) : g z ∈ orbit E y := by
  have := hg z
  rwa [orbit_eq_iff.mpr hz] at this

def blockBaseOn (E : Subgroup (Perm α)) (Γ : Set α) : Subgroup (Perm α) where
  carrier := {g | ∀ y ∈ Γ, ∃ e ∈ E, ∀ z ∈ orbit E y, g z = e z}
  mul_mem' := by
    intro a b ha hb y hy
    obtain ⟨e, he, hae⟩ := ha y hy
    obtain ⟨f, hf, hbf⟩ := hb y hy
    refine ⟨e * f, E.mul_mem he hf, fun z hz => ?_⟩
    rw [Perm.mul_apply, hbf z hz, Perm.mul_apply, hae _ (mul_mem_orbit hf hz)]
  one_mem' := fun _ _ => ⟨1, E.one_mem, fun _ _ => rfl⟩
  inv_mem' := by
    intro a ha y hy
    obtain ⟨e, he, hae⟩ := ha y hy
    exact ⟨e⁻¹, E.inv_mem he, fun z hz => inv_apply_eq he hae hz⟩

omit [Fintype α] [DecidableEq α] in
private theorem blockBase_le_blockBaseOn (E : Subgroup (Perm α)) (Γ : Set α) :
    blockBase E ≤ blockBaseOn E Γ := fun _ hg y _ => hg y

omit [Fintype α] [DecidableEq α] in
private theorem commutator_mem_blockBase {E : Subgroup (Perm α)} {Γ₁ Γ₂ : Set α} {x y : Perm α}
    (hΓ : ∀ z, z ∈ Γ₁ ∨ z ∈ Γ₂) (hxB : x ∈ blockKer E) (hyB : y ∈ blockKer E)
    (hxN : x ∈ normalizer (E : Set (Perm α))) (hyN : y ∈ normalizer (E : Set (Perm α)))
    (hx : x ∈ blockBaseOn E Γ₁) (hy : y ∈ blockBaseOn E Γ₂) :
    x * y * x⁻¹ * y⁻¹ ∈ blockBase E := by
  intro z
  rcases hΓ z with hz | hz
  · obtain ⟨e, he, hxe⟩ := hx z hz
    have he' : y * e⁻¹ * y⁻¹ ∈ E := (mem_normalizer_iff.mp hyN _).mp (E.inv_mem he)
    refine ⟨e * (y * e⁻¹ * y⁻¹), E.mul_mem he he', fun w hw => ?_⟩
    have h1 : y⁻¹ w ∈ orbit E z := blockKer_apply_mem (inv_mem hyB) hw
    have h2 : (y * e⁻¹ * y⁻¹) w ∈ orbit E z := mul_mem_orbit he' hw
    simp only [Perm.mul_apply] at h2 ⊢
    rw [inv_apply_eq he hxe h1, hxe _ h2]
  · obtain ⟨f, hf, hyf⟩ := hy z hz
    have hf' : x * f * x⁻¹ ∈ E := (mem_normalizer_iff.mp hxN _).mp hf
    refine ⟨x * f * x⁻¹ * f⁻¹, E.mul_mem hf' (E.inv_mem hf), fun w hw => ?_⟩
    have h1 : f⁻¹ w ∈ orbit E z := mul_mem_orbit (E.inv_mem hf) hw
    have h2 : x⁻¹ (f⁻¹ w) ∈ orbit E z := blockKer_apply_mem (inv_mem hxB) h1
    simp only [Perm.mul_apply]
    rw [inv_apply_eq hf hyf hw, hyf _ h2]

omit [Fintype α] [DecidableEq α] in
private theorem le_normalizer_inf_blockBaseOn {E N : Subgroup (Perm α)} (hNB : N ≤ blockKer E)
    (hNE : N ≤ normalizer (E : Set (Perm α))) (Γ : Set α) :
    N ≤ normalizer ((N ⊓ blockBaseOn E Γ : Subgroup (Perm α)) : Set (Perm α)) := by
  refine le_normalizer_of_conj_mem fun n hn g hg => mem_inf.mpr ⟨?_, fun y hy => ?_⟩
  · exact mul_mem (mul_mem hn (mem_inf.mp hg).1) (inv_mem hn)
  · obtain ⟨e, he, hge⟩ := (mem_inf.mp hg).2 y hy
    refine ⟨n * e * n⁻¹, (mem_normalizer_iff.mp (hNE hn) e).mp he, fun z hz => ?_⟩
    have h1 : n⁻¹ z ∈ orbit E y := blockKer_apply_mem (inv_mem (hNB hn)) hz
    simp only [Perm.mul_apply]
    rw [hge _ h1]

omit [Fintype α] [DecidableEq α] in
private theorem mem_blockBaseOn_of_fix {E K : Subgroup (Perm α)} {x₀ : α} {x : Perm α}
    (hfix : ∀ y, (∀ k ∈ K, k x₀ ∉ orbit E y) → x y = y) :
    x ∈ blockBaseOn E {y | ∀ k ∈ K, k x₀ ∉ orbit E y} := fun y hy =>
  ⟨1, one_mem _, fun z hz => by
    rw [Perm.one_apply]
    refine hfix z fun k hk hkz => hy k hk ?_
    rwa [orbit_eq_iff.mpr hz] at hkz⟩

theorem not_isPIsolatedOver_of_not_transitive {K M : Subgroup (Perm α)} {Δ : Set α}
    (hMN : M ≤ normalizer (K : Set (Perm α))) (hKΔ : K ≤ fixOutside Δ)
    (hML : normalizer (K : Set (Perm α)) ⊓ fixOutside Δ ⊓ alternatingGroup α ≤ M)
    (hBK : blockBase (omegaOneCenterOf K) ≤ K) (hKM : K ≤ M) {x₀ b : α} (hx₀ : x₀ ∈ Δ)
    (hbΔ : b ∈ Δ) {j : ℕ} (hj3 : 3 ≤ j)
    (hjx : Nat.card (orbit (omegaOneCenterOf K) x₀) = 2 ^ j)
    (hjb : Nat.card (orbit (omegaOneCenterOf K) b) = 2 ^ j)
    (hb : ∀ k ∈ K, k x₀ ∉ orbit (omegaOneCenterOf K) b) :
    ¬ IsPIsolatedOver 2 (M ⊓ blockKer (omegaOneCenterOf K)) (blockBase (omegaOneCenterOf K)) := by
  have hEK : ∀ e ∈ omegaOneCenterOf K, ∀ k ∈ K, e * k = k * e :=
    fun e he k hk => omegaOneCenter_commute K he hk
  have hNE : M ⊓ blockKer (omegaOneCenterOf K) ≤ normalizer (omegaOneCenterOf K : Set (Perm α)) :=
    inf_le_left.trans (hMN.trans (normalizer_le_normalizer_omegaOneCenterOf K))
  have hHN : blockBase (omegaOneCenterOf K) ≤ M ⊓ blockKer (omegaOneCenterOf K) :=
    le_inf (hBK.trans hKM) (blockBase_le_blockKer _)
  have hNH := hNE.trans (normalizer_le_normalizer_blockBase (omegaOneCenterOf K))
  obtain ⟨x, hxM, hxB, hx2, hxfix⟩ := exists_order_two hKΔ hML hBK hx₀ hj3 hjx
  obtain ⟨y, hyM, hyB, hy2, hyfix⟩ := exists_order_two hKΔ hML hBK hbΔ hj3 hjb
  have hy : y ∈ blockBaseOn (omegaOneCenterOf K)
      {z | ∃ k ∈ K, k x₀ ∈ orbit (omegaOneCenterOf K) z} := by
    rintro z ⟨k₁, hk₁, hz⟩
    refine ⟨1, one_mem _, fun w hw => ?_⟩
    rw [Perm.one_apply]
    refine hyfix w fun k hk hkw => ?_
    have h1 : k b ∈ orbit (omegaOneCenterOf K) (k₁ x₀) := by
      rw [orbit_eq_iff.mpr hz, ← orbit_eq_iff.mpr hw]
      exact hkw
    have h2 := apply_mem_orbit_of_commute (fun e he => hEK e he k⁻¹ (inv_mem hk)) h1
    rw [← Perm.mul_apply k⁻¹ k b, inv_mul_cancel, Perm.one_apply, ← Perm.mul_apply k⁻¹ k₁ x₀] at h2
    exact hb _ (mul_mem (inv_mem hk) hk₁) (mem_orbit_symm.mp h2)
  refine not_isPIsolatedOver_of_commute (isPGroup_blockBase fun e he => omegaOneCenter_sq K he)
    hHN hNH (le_inf hHN (blockBase_le_blockBaseOn _ _))
    (le_inf hHN (blockBase_le_blockBaseOn _ _)) inf_le_left inf_le_left
    (le_normalizer_inf_blockBaseOn inf_le_right hNE _)
    (le_normalizer_inf_blockBaseOn inf_le_right hNE _)
    (fun g hg h hh => commutator_mem_blockBase (fun z => (em (∀ k ∈ K, k x₀ ∉ orbit _ z)).imp id
        (fun hz => by push Not at hz; exact hz))
      (mem_inf.mp (mem_inf.mp hg).1).2 (mem_inf.mp (mem_inf.mp hh).1).2 (hNE (mem_inf.mp hg).1)
      (hNE (mem_inf.mp hh).1) (mem_inf.mp hg).2 (mem_inf.mp hh).2)
    (two_dvd_relIndex_of_sq_mem (le_inf hHN (blockBase_le_blockBaseOn _ _))
      (inf_le_left.trans hNH) (mem_inf.mpr ⟨hxM, mem_blockBaseOn_of_fix hxfix⟩) hxB hx2)
    (two_dvd_relIndex_of_sq_mem (le_inf hHN (blockBase_le_blockBaseOn _ _))
      (inf_le_left.trans hNH) (mem_inf.mpr ⟨hyM, hy⟩) hyB hy2)

private theorem exists_hom_GL {K M : Subgroup (Perm α)} {Δ : Set α}
    (hMN : M ≤ normalizer (K : Set (Perm α))) (hKΔ : K ≤ fixOutside Δ)
    (hML : normalizer (K : Set (Perm α)) ⊓ fixOutside Δ ⊓ alternatingGroup α ≤ M)
    (hBK : blockBase (omegaOneCenterOf K) ≤ K) {x₀ : α} (hx₀ : x₀ ∈ Δ) {j : ℕ}
    (hj : Nat.card (orbit (omegaOneCenterOf K) x₀) = 2 ^ j) :
    ∃ f : (M ⊓ blockKer (omegaOneCenterOf K) : Subgroup (Perm α)) →* GL (Fin j) (ZMod 2),
      (∀ m : (M ⊓ blockKer (omegaOneCenterOf K) : Subgroup (Perm α)),
        f m = 1 ↔ ∀ u ∈ localBase (omegaOneCenterOf K) x₀, (m : Perm α) * u = u * m) ∧
      ∀ g : GL (Fin j) (ZMod 2), ∃ m, f m = g ^ 2 := by
  have hS : ∀ m ∈ M ⊓ blockKer (omegaOneCenterOf K),
      m ∈ normalizer (omegaOneCenterOf K : Set (Perm α)) ∧ m x₀ ∈ orbit (omegaOneCenterOf K) x₀ :=
    fun m hm => ⟨normalizer_le_normalizer_omegaOneCenterOf K (hMN (mem_inf.mp hm).1),
      (mem_inf.mp hm).2 x₀⟩
  obtain ⟨ψ⟩ := nonempty_mulAut_equiv_GL (omegaOneCenter_comm K)
    (fun e he => omegaOneCenter_sq K he) hj
  refine ⟨ψ.toMonoidHom.comp (localConj (omegaOneCenterOf K) x₀ _ hS), fun m => ?_, fun g => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    refine ⟨fun h u hu => ?_, fun h => MulEquiv.ext fun u => Subtype.ext ?_⟩
    · have := congrArg (fun φ : MulAut _ => ((φ ⟨u, hu⟩ : localBase _ x₀) : Perm α)) h
      simp only [localConj_apply, MulAut.one_apply] at this
      calc (m : Perm α) * u = m * u * (m : Perm α)⁻¹ * m := (inv_mul_cancel_right _ _).symm
        _ = u * m := by rw [this]
    · rw [localConj_apply, h u u.2, mul_inv_cancel_right]
      rfl
  · obtain ⟨x, hxM, -, hxc, -⟩ := exists_diag_sq_mem hKΔ hML hBK x₀ hx₀ (ψ.symm g)
    refine ⟨⟨x, hxM⟩, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show localConj (omegaOneCenterOf K) x₀ _ hS ⟨x, hxM⟩ = (ψ.symm g) ^ 2 from
        MulEquiv.ext fun u => Subtype.ext (by rw [localConj_apply]; exact hxc u),
      map_pow, MulEquiv.apply_symm_apply]

theorem not_isPIsolatedOver_of_transitive {K M : Subgroup (Perm α)} {Δ : Set α}
    (hMN : M ≤ normalizer (K : Set (Perm α))) (hKΔ : K ≤ fixOutside Δ)
    (hML : normalizer (K : Set (Perm α)) ⊓ fixOutside Δ ⊓ alternatingGroup α ≤ M)
    (hBK : blockBase (omegaOneCenterOf K) ≤ K) (hKM : K ≤ M) {x₀ : α} (hx₀ : x₀ ∈ Δ) {j : ℕ}
    (hj3 : 3 ≤ j)
    (hj : Nat.card (orbit (omegaOneCenterOf K) x₀) = 2 ^ j)
    (htr : ∀ y, (∃ k ∈ K, k x₀ ∈ orbit (omegaOneCenterOf K) y) ∨ ∀ k ∈ K, k y = y) :
    ¬ IsPIsolatedOver 2 (M ⊓ blockKer (omegaOneCenterOf K)) (blockBase (omegaOneCenterOf K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf1, hfsq⟩ := exists_hom_GL hMN hKΔ hML hBK hx₀ hj
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    exact eq_top_of_sq_mem_GL_two hj3 fun g => MonoidHom.mem_range.mpr (hfsq g)
  have hker : f.ker = (blockBase (omegaOneCenterOf K)).subgroupOf
      (M ⊓ blockKer (omegaOneCenterOf K)) := by
    ext m
    rw [MonoidHom.mem_ker, mem_subgroupOf, hf1]
    refine ⟨fun h => mem_blockBase_of_comm (x₀ := x₀) (omegaOneCenter_comm K)
      (fun e he k hk => omegaOneCenter_commute K he hk) (mem_inf.mp m.2).2
      (hMN (mem_inf.mp m.2).1) h fun y hy => ?_, fun h u hu =>
        blockBase_comm_localBase (omegaOneCenter_comm K) h hu⟩
    rcases htr y with ⟨k, hk, hky⟩ | hfix
    · exact absurd hky (hy k hk)
    · obtain ⟨⟨e, he⟩, hey⟩ := (mem_inf.mp m.2).2 y
      rw [← hey]
      exact hfix e (omegaOneCenter_le K he)
  intro hiso
  have h1 := (isPIsolatedOver_subgroupOf_iff (p := 2)
    (le_inf (hBK.trans hKM) (blockBase_le_blockKer _)) le_rfl).mpr hiso
  rw [subgroupOf_self, ← hker] at h1
  have hkerp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_blockBase fun e he => omegaOneCenter_sq K he).comap_subtype
  have h2 := (isPIsolatedOver_map_iff hsurj hkerp (H := f.ker) (K := ⊤) le_rfl le_top).mpr h1
  rw [map_top_of_surjective f hsurj,
    (Subgroup.map_eq_bot_iff (f := f) (H := f.ker)).mpr le_rfl] at h2
  exact not_isPIsolatedOver_GL_two hj3 h2

theorem card_orbit_omegaOneCenter_le_four {K M : Subgroup (Perm α)} {Δ : Set α}
    (hK : IsPGroup 2 K) (hKΔ : K ≤ fixOutside Δ) (hKM : K ≤ M)
    (hMN : M ≤ normalizer (K : Set (Perm α)))
    (hML : normalizer (K : Set (Perm α)) ⊓ fixOutside Δ ⊓ alternatingGroup α ≤ M)
    (htr : ∀ x ∈ Δ, ∀ y ∈ Δ, ∃ g ∈ normalizer (K : Set (Perm α)), g x = y)
    (hiso : IsPIsolatedOver 2 M K) {x : α} (hx : x ∈ Δ) :
    Nat.card (orbit (omegaOneCenterOf K) x) ≤ 4 := by
  obtain ⟨j, hj⟩ := exists_card_orbit_eq_two_pow (hK.to_le (omegaOneCenter_le K)) x
  have hall : ∀ y ∈ Δ, Nat.card (orbit (omegaOneCenterOf K) y) = 2 ^ j := fun y hy => by
    obtain ⟨g, hg, rfl⟩ := htr x hx y hy
    rw [card_orbit_eq_of_normalizer (normalizer_le_normalizer_omegaOneCenterOf K hg) x, hj]
  have hout : ∀ y ∉ Δ, Nat.card (orbit (omegaOneCenterOf K) y) = 1 := fun y hy => by
    refine Nat.card_eq_one_iff_exists.mpr ⟨⟨y, mem_orbit_self y⟩, fun ⟨z, hz⟩ => ?_⟩
    obtain ⟨⟨e, he⟩, rfl⟩ := hz
    exact Subtype.ext (hKΔ (omegaOneCenter_le K he) y hy)
  rw [hj]
  by_contra hlt
  have hj3 : 3 ≤ j := by
    by_contra h
    exact hlt ((Nat.pow_le_pow_right (by norm_num) (by omega : j ≤ 2)).trans (by norm_num))
  have h4 : ∀ y, Nat.card (orbit (omegaOneCenterOf K) y) = 1 ∨
      4 ∣ Nat.card (orbit (omegaOneCenterOf K) y) := fun y => by
    by_cases hy : y ∈ Δ
    · rw [hall y hy]
      exact Or.inr (by simpa using Nat.pow_dvd_pow 2 (show 2 ≤ j by omega))
    · exact Or.inl (hout y hy)
  have hBK := blockBase_omegaOneCenter_le hK hKM hMN hKΔ hML hiso h4
  obtain ⟨x₁, hx₁, hx₁B, hx₁2, -⟩ := exists_order_two hKΔ hML hBK hx hj3 hj
  have hiso₀ := isPIsolatedOver_inf_blockKer hK hKM hMN hiso hBK hx₁ hx₁B hx₁2
  by_cases hT : ∀ y ∈ Δ, ∃ k ∈ K, k x ∈ orbit (omegaOneCenterOf K) y
  · refine not_isPIsolatedOver_of_transitive hMN hKΔ hML hBK hKM hx hj3 hj (fun y => ?_) hiso₀
    by_cases hy : y ∈ Δ
    · exact Or.inl (hT y hy)
    · exact Or.inr fun k hk => hKΔ hk y hy
  · push Not at hT
    obtain ⟨b, hb, hbk⟩ := hT
    exact not_isPIsolatedOver_of_not_transitive hMN hKΔ hML hBK hKM hx hb hj3 hj (hall b hb) hbk
      hiso₀

end CFSG.GroupTheory.AltCore
