module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartBasic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartIdent
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermSec

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv CFSG.OddStandard.AltStdBal

section Gen

variable {G : Type} [Group G]

theorem le_of_forall_orderOf_three {K M : Subgroup G} {f : ℕ} (φ : K ≃* alternatingGroup (Fin f))
    (h3 : ∀ x ∈ K, orderOf x = 3 → x ∈ M) : K ≤ M := by
  set M' : Subgroup K := M.comap K.subtype with hM'
  have hT : (Subgroup.closure {a : alternatingGroup (Fin f) |
      (a : Perm (Fin f)).IsThreeCycle}) ≤ M'.map φ.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro a ha
    have ha3 : orderOf (φ.symm a) = 3 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact Equiv.Perm.IsThreeCycle.orderOf ha
    refine ⟨φ.symm a, h3 _ (φ.symm a).2 ?_, by simp⟩
    show orderOf (((φ.symm a : K)) : G) = 3
    rw [Subgroup.orderOf_coe]
    exact ha3
  rw [alternatingGroup.closure_isThreeCycles_eq_top] at hT
  intro x hx
  have : φ ⟨x, hx⟩ ∈ M'.map φ.toMonoidHom := hT (mem_top _)
  obtain ⟨u, hu, hux⟩ := this
  have : u = ⟨x, hx⟩ := φ.injective hux
  rw [this] at hu
  exact hu

end Gen

section Partner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

omit [Finite G] in
theorem mem_conjSub_inv_iff {g x : G} {H : Subgroup G} : x ∈ conjSub g⁻¹ H ↔ g * x * g⁻¹ ∈ H := by
  rw [mem_conjSub_iff, inv_inv]

omit [Finite G] in
theorem conj_inv_mem_centralizer {a g : G} (ha : a ∈ centralizer ({z} : Set G))
    (hg : g * z * g⁻¹ = a) : g⁻¹ * z * g ∈ centralizer ({z} : Set G) := by
  rw [mem_centralizer_singleton_iff] at ha ⊢
  have h1 : g⁻¹ * a * g = z := by rw [← hg]; group
  calc g⁻¹ * z * g * z = g⁻¹ * z * g * (g⁻¹ * a * g) := by rw [h1]
    _ = g⁻¹ * (z * a) * g := by group
    _ = g⁻¹ * (a * z) * g := by rw [ha]
    _ = (g⁻¹ * a * g) * (g⁻¹ * z * g) := by group
    _ = z * (g⁻¹ * z * g) := by rw [h1]

theorem orderOf_permOf_conj (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) {a g : G} (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (ha' : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) :
    orderOf (permOf h d e ha') = 2 := by
  have hz2 : z * z = 1 := d.mul_self
  have hz1 : z ≠ 1 := fun h1 => by simpa [h1] using d.order
  have ha'2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  have hN : g⁻¹ * z * g ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d ha'
  have hsq : (permOf h d e ha') ^ 2 = 1 := by
    unfold permOf
    rw [← map_pow]
    have : (⟨g⁻¹ * z * g, hN⟩ : normalizer (L : Set G)) ^ 2 = 1 :=
      Subtype.ext (by simp [pow_two, ha'2])
    rw [this, map_one]
  have hne : permOf h d e ha' ≠ 1 := by
    intro h1
    have hc : g⁻¹ * z * g ∈ centralizer (L : Set G) := (rho_eq_one_iff e h.hn ⟨_, hN⟩).1 h1
    have hQ : g⁻¹ * z * g ∈ Q := by
      rw [← cent_inf_eq h d]
      exact ⟨hc, ha'⟩
    rcases eq_one_or_eq_of_card_eq_two d hQ2 hQ with h2 | h2
    · apply hz1
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h2]; group
    · apply haz
      rw [← hg]
      calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h2]
        _ = z := by group
  have hdvd : orderOf (permOf h d e ha') ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.1 h1) hne
  · exact h2

theorem exists_corr_eq_conj₂ (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {a g : G} (ha : a ∈ centralizer ({z} : Set G))
    (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hid : NormalAltIdentSym n (fixFin (permOf h d e ha)).card) :
    ∃ F' : Finset (Fin n), F'.card = (fixFin (permOf h d e ha)).card ∧
      conjSub g⁻¹ (corr (X := G) e (altSub (fixFin (permOf h d e ha)))) =
        corr (X := G) e (altSub F') := by
  set F : Finset (Fin n) := fixFin (permOf h d e ha) with hF
  set N : Subgroup G := corr (X := G) e (altSub F) with hN
  have ha' : g⁻¹ * z * g ∈ centralizer ({z} : Set G) := conj_inv_mem_centralizer ha hg
  have hz2 : z * z = 1 := d.mul_self
  have hNL : N ≤ L := corr_le e _
  have hNa : ∀ w ∈ N, a * w = w * a := fun w hw =>
    comm_of_mem_corr_of_permOf_fix h d e ha (fun i hi => mem_fixFin.1 hi) hw
  have hNz : ∀ w ∈ N, w * z = z * w := fun w hw =>
    mem_centralizer_singleton_iff.1 (le_centralizer_single h d (hNL hw))
  have hKz : ∀ w ∈ N, (g⁻¹ * w * g) ∈ centralizer ({z} : Set G) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    have h1 := hNa w hw
    rw [← hg] at h1
    calc g⁻¹ * w * g * z = g⁻¹ * (w * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * w) * g := by rw [h1]
      _ = z * (g⁻¹ * w * g) := by group
  obtain ⟨φ⟩ := exists_equiv_corr_altSub (X := G) e F
  let ψ : ↥N ≃* ↥(conjSub g⁻¹ N) :=
    N.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hN'L : conjSub g⁻¹ N ≤ L := by
    have hφ' : ↥(conjSub g⁻¹ N) ≃* alternatingGroup (Fin F.card) := ψ.symm.trans φ
    refine le_of_forall_orderOf_three hφ' fun x hx hx3 => ?_
    have hx' : x ∈ centralizer ({z} : Set G) := by
      have hw := mem_conjSub_inv_iff.1 hx
      have := hKz _ hw
      simpa [mul_assoc] using this
    exact T.mem_of_odd h d hx' (by rw [hx3]; exact ⟨1, rfl⟩)
  set ye' : Perm (Fin n) := permOf h d e ha' with hye'
  have hye'2 : orderOf ye' = 2 := orderOf_permOf_conj h d T.card e hg haz ha'
  have hKt : permImg e (conjSub g⁻¹ N) ≤ centralizer ({ye'} : Set (Perm (Fin n))) := by
    intro σ hσ
    obtain ⟨x, hx, rfl⟩ := (mem_permImg e).1 hσ
    rw [mem_centralizer_singleton_iff]
    have hxN : ∃ w ∈ N, g⁻¹ * w * g = (x : G) :=
      ⟨g * x * g⁻¹, mem_conjSub_inv_iff.1 hx, by group⟩
    obtain ⟨w, hw, hwx⟩ := hxN
    have hxc : (x : G) * (g⁻¹ * z * g) = (g⁻¹ * z * g) * x := by
      rw [← hwx]
      calc g⁻¹ * w * g * (g⁻¹ * z * g) = g⁻¹ * (w * z) * g := by group
        _ = g⁻¹ * (z * w) * g := by rw [hNz w hw]
        _ = (g⁻¹ * z * g) * (g⁻¹ * w * g) := by group
    have hxC : (x : G) ∈ centralizer ({z} : Set G) := le_centralizer_single h d x.2
    have h1 := permOf_of_mem h d e hxC x.2
    have h2 : permOf h d e hxC * permOf h d e ha' = permOf h d e ha' * permOf h d e hxC := by
      rw [← permOf_mul h d e hxC ha' (mul_mem hxC ha'), ← permOf_mul h d e ha' hxC
        (mul_mem ha' hxC)]
      congr 1
    have h3 : ((e x : alternatingGroup (Fin n)) : Perm (Fin n)) * ye' =
        ye' * ((e x : alternatingGroup (Fin n)) : Perm (Fin n)) := by
      rw [← h1]
      exact h2
    exact h3
  have hKn : ∀ c ∈ centralizer ({ye'} : Set (Perm (Fin n))),
      ∀ k ∈ permImg e (conjSub g⁻¹ N), c * k * c⁻¹ ∈ permImg e (conjSub g⁻¹ N) := by
    intro c hc k hk
    have hc' : c * ye' = ye' * c := mem_centralizer_singleton_iff.1 hc
    obtain ⟨s, hsC, hs, hsa'⟩ := exists_lift_commuting h d T e ha' hc'
    obtain ⟨x, hx, rfl⟩ := (mem_permImg e).1 hk
    obtain ⟨w, hw, hwx⟩ : ∃ w ∈ N, g⁻¹ * w * g = (x : G) :=
      ⟨g * x * g⁻¹, mem_conjSub_inv_iff.1 hx, by group⟩
    set y : G := g * s * g⁻¹ with hy
    have hyz : y * z = z * y := by
      have h1 : s * (g⁻¹ * z * g) = (g⁻¹ * z * g) * s := hsa'
      calc y * z = g * (s * (g⁻¹ * z * g)) * g⁻¹ := by rw [hy]; group
        _ = g * ((g⁻¹ * z * g) * s) * g⁻¹ := by rw [h1]
        _ = z * y := by rw [hy]; group
    have hyC : y ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hyz
    have hya : y * a = a * y := by
      have h1 := mem_centralizer_singleton_iff.1 hsC
      rw [← hg]
      calc y * (g * z * g⁻¹) = g * (s * z) * g⁻¹ := by rw [hy]; group
        _ = g * (z * s) * g⁻¹ := by rw [h1]
        _ = (g * z * g⁻¹) * y := by rw [hy]; group
    have hynorm := mem_normalizer_corr_fixFin h d e ha hyC hya
    have hywy : y * w * y⁻¹ ∈ N := (mem_normalizer_iff.1 hynorm w).1 hw
    have hsx : s * (x : G) * s⁻¹ = g⁻¹ * (y * w * y⁻¹) * g := by
      rw [← hwx, hy]; group
    have hsxL : s * (x : G) * s⁻¹ ∈ L := by
      rw [hsx]
      exact hN'L (mem_conjSub_inv_iff.2 (by simpa [mul_assoc] using hywy))
    refine (mem_permImg e).2 ⟨⟨s * (x : G) * s⁻¹, hsxL⟩, ?_, ?_⟩
    · show s * (x : G) * s⁻¹ ∈ conjSub g⁻¹ N
      exact mem_conjSub_inv_iff.2 (by
        rw [hsx]; simpa [mul_assoc] using hywy)
    · have hsN : (s : G) ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d hsC
      have h1 := rho_conj_apply e h.hn hsN x ⟨s * (x : G) * s⁻¹, hsxL⟩ rfl
      have h2 : rho e h.hn ⟨s, hsN⟩ = c := hs
      rw [h2] at h1
      rw [← h1]
  have hKequiv : Nonempty (permImg e (conjSub g⁻¹ N) ≃* alternatingGroup (Fin F.card)) :=
    ⟨((permImgEquiv e hN'L).symm.trans ψ.symm).trans φ⟩
  obtain ⟨hKeq, hcard⟩ := hid ye' hye'2 _ (permImg_le_alt e _) hKt hKn hKequiv
  refine ⟨fixFin ye', hcard, ?_⟩
  rw [← hKeq]
  exact (corr_permImg e hN'L).symm

theorem exists_common_root₂ (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {a g : G} (ha : a ∈ centralizer ({z} : Set G))
    (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf h d e ha)).card ∧ (fixFin (permOf h d e ha)).card ≠ 6)
    {S : Finset (Fin n)} (hS : S ⊆ fixFin (permOf h d e ha)) :
    ∃ S₁ : Finset (Fin n), S₁.card = S.card ∧
      rootGroup (G := G) e S = conjSub g (rootGroup e S₁) := by
  set F : Finset (Fin n) := fixFin (permOf h d e ha) with hF
  obtain ⟨F', hcard, hconj⟩ :=
    exists_corr_eq_conj₂ h d T e ha hg haz (normalAltIdentSym_of_five_le hf.1)
  have hFF' : ∀ x ∈ corr (X := G) e (altSub F), g⁻¹ * x * g ∈ corr (X := G) e (altSub F') := by
    intro x hx
    rw [← hconj]
    refine mem_conjSub_iff.2 ?_
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    simpa [this] using hx
  have hF'F : ∀ x ∈ corr (X := G) e (altSub F'), g * x * g⁻¹ ∈ corr (X := G) e (altSub F) := by
    intro x hx
    rw [← hconj] at hx
    simpa using mem_conjSub_iff.1 hx
  obtain ⟨β, hβ1, hβ2, hβ3, hβ4⟩ :=
    exists_conj_intertwining e g hcard.symm (Or.inl hf) hFF' hF'F
  refine ⟨S.image β, ?_, rootGroup_eq_conjSub_image e g hFF' hF'F hβ1 hβ2 hβ3 hβ4 hS⟩
  exact Finset.card_image_of_injOn fun i hi j hj hij => hβ2 i (hS hi) j (hS hj) hij

end Partner

end CFSG.OddStandard.AltStdSec
