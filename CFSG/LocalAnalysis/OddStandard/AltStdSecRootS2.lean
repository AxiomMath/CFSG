module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS2a
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootSupp
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootA4
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermSec
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootComp
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootPartner

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal Equiv

section Ident

variable {n : ℕ}

@[expose] def NormalAltIdent (n f : ℕ) : Prop :=
  ∀ t : Perm (Fin n), orderOf t = 2 → t ∈ alternatingGroup (Fin n) →
    ∀ K : Subgroup (Perm (Fin n)), K ≤ alternatingGroup (Fin n) →
      K ≤ centralizer ({t} : Set (Perm (Fin n))) →
      (∀ c ∈ alternatingGroup (Fin n), c ∈ centralizer ({t} : Set (Perm (Fin n))) →
        ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      Nonempty (K ≃* alternatingGroup (Fin f)) → K = altSub (fixFin t) ∧ (fixFin t).card = f

theorem normalAltIdent_of_five_le {f : ℕ} (hf : 5 ≤ f) : NormalAltIdent n f := by
  intro t ht htA K hKA hKt hKn ⟨eK⟩
  obtain ⟨hK, h5⟩ := eq_altSub_of_normal_quasisimple ht htA hKA hKt hKn hf eK
  refine ⟨hK, ?_⟩
  have h5' : 5 ≤ (fixFin t).card := h5
  have h1 : Nat.card K = f.factorial / 2 := card_eq_of_equiv_alt (by omega) eK
  have h2 : Nat.card K = (fixFin t).card.factorial / 2 :=
    card_eq_of_equiv_alt (by omega) ((MulEquiv.subgroupCongr hK).trans (altSubEquiv (fixFin t)))
  have h3 : 2 ∣ f.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h4 : 2 ∣ (fixFin t).card.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h6 : (fixFin t).card.factorial = f.factorial := by omega
  exact (Nat.factorial_inj (by omega)).1 h6

theorem normalAltIdent_four (hn : 12 ≤ n) : NormalAltIdent n 4 := by
  intro t ht htA K hKA hKt hKn ⟨eK⟩
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  rcases rootSupp_support_card_of_involution ht (Perm.mem_alternatingGroup.1 htA) with h4 | h8
  · exact (rootSupp_false_of_normal_alt_four_of_support_four hn ht2 h4 hKt
      (fun c hc hcA => hKn c hcA hc) ⟨eK⟩).elim
  · obtain ⟨hcard, hK⟩ := rootA4_root_alt_four_of_normal_alt_centralizer ht2 h8 hKt
      (fun c hc hcA => hKn c hcA hc) ⟨eK⟩
    refine ⟨?_, by rw [← card_fixedPoints_eq]; exact hcard⟩
    rw [hK]
    convert map_ofSubtype_alternatingGroup_eq_altSub (fun i => i ∈ Function.fixedPoints t)
      (fixFin t) (fun i => by
        rw [mem_fixFin]
        simp [Function.fixedPoints, Function.IsFixedPt])

end Ident

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem exists_corr_eq_conj (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (e : L ≃* alternatingGroup (Fin n)) {y g : G}
    (hy : y ∈ L) (hy2 : orderOf y = 2) (hg : g * z * g⁻¹ = z * y)
    (hid : NormalAltIdent n
      (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card) :
    ∃ F' : Finset (Fin n),
      F'.card = (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ∧
      conjSub g⁻¹ (corr (X := G) e
        (altSub (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))))) =
        corr (X := G) e (altSub F') := by
  set F : Finset (Fin n) :=
    fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) with hF
  have hNL : corr (X := G) e (altSub F) ≤ L := corr_le e _
  have hNy : ∀ w ∈ corr (X := G) e (altSub F), w * y = y * w :=
    fun w hw => comm_of_mem_corr_of_fix e hy (fun i hi => mem_fixFin.1 hi) hw
  obtain ⟨φ⟩ := exists_equiv_corr_altSub (X := G) e F
  have hNg : corr (X := G) e (altSub F) ≤ conjSub g L :=
    le_conjSub_of_orderOf_three h d hQ2 hE hg hNL hNy φ
  have hyg : y ∈ conjSub g L := mem_conjSub_of_partner h d hQ2 hE hy hg
  have hyL : g⁻¹ * y * g ∈ L := mem_conjSub_iff.1 hyg
  have hN'L : conjSub g⁻¹ (corr (X := G) e (altSub F)) ≤ L := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ corr (X := G) e (altSub F) := by
      have := mem_conjSub_iff.1 hx
      simpa using this
    have h2 := mem_conjSub_iff.1 (hNg h1)
    simpa [mul_assoc] using h2
  set ye' : Perm (Fin n) := ((e ⟨g⁻¹ * y * g, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
    with hye'
  have hye'2 : orderOf ye' = 2 := by
    rw [hye', Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    have : g⁻¹ * y * g = (MulAut.conj g⁻¹) y := by simp
    rw [this, MulEquiv.orderOf_eq]
    exact hy2
  have hKt : permImg e (conjSub g⁻¹ (corr (X := G) e (altSub F))) ≤
      centralizer ({ye'} : Set (Perm (Fin n))) := by
    intro σ hσ
    obtain ⟨x, hx, rfl⟩ := (mem_permImg e).1 hσ
    rw [mem_centralizer_singleton_iff]
    have hgx : g * (x : G) * g⁻¹ ∈ corr (X := G) e (altSub F) := by
      simpa using mem_conjSub_iff.1 hx
    have h1 := hNy _ hgx
    have h2 : (x : G) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * x := by
      calc (x : G) * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * y * g) * x := by group
    have h3 : x * ⟨g⁻¹ * y * g, hyL⟩ = ⟨g⁻¹ * y * g, hyL⟩ * x := Subtype.ext h2
    have h4 := congrArg e h3
    rw [map_mul, map_mul] at h4
    exact congrArg Subtype.val h4
  have hKn : ∀ c ∈ alternatingGroup (Fin n), c ∈ centralizer ({ye'} : Set (Perm (Fin n))) →
      ∀ k ∈ permImg e (conjSub g⁻¹ (corr (X := G) e (altSub F))),
        c * k * c⁻¹ ∈ permImg e (conjSub g⁻¹ (corr (X := G) e (altSub F))) := by
    intro c hcA hcC k hk
    obtain ⟨x, hx, rfl⟩ := (mem_permImg e).1 hk
    set l : L := e.symm ⟨c, hcA⟩ with hl
    have hel : e l = ⟨c, hcA⟩ := by simp [hl]
    have hly : (l : G) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * l := by
      have h1 : c * ye' = ye' * c := mem_centralizer_singleton_iff.1 hcC
      have h2 : e (l * ⟨g⁻¹ * y * g, hyL⟩) = e (⟨g⁻¹ * y * g, hyL⟩ * l) := by
        rw [map_mul, map_mul, hel]
        exact Subtype.ext h1
      exact congrArg Subtype.val (e.injective h2)
    have hnorm := normalizes_conj h d hQ2 hE hy hg hNL
      (fun c' hc' hc'y => mem_normalizer_corr_fix e hy hc' hc'y) l.2 hly
    have hx' : (l : G) * x * (l : G)⁻¹ ∈ conjSub g⁻¹ (corr (X := G) e (altSub F)) :=
      (mem_normalizer_iff.1 hnorm _).1 hx
    refine (mem_permImg e).2 ⟨l * x * l⁻¹, hx', ?_⟩
    rw [map_mul, map_mul, map_inv, hel]
    rfl
  have hKequiv : Nonempty (permImg e (conjSub g⁻¹ (corr (X := G) e (altSub F))) ≃*
      alternatingGroup (Fin F.card)) := by
    let ψ : ↥(corr (X := G) e (altSub F)) ≃* ↥(conjSub g⁻¹ (corr (X := G) e (altSub F))) :=
      (corr (X := G) e (altSub F)).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective
    exact ⟨((permImgEquiv e hN'L).symm.trans ψ.symm).trans φ⟩
  obtain ⟨hKeq, hcard⟩ := hid ye' hye'2 (e ⟨g⁻¹ * y * g, hyL⟩).2 _ (permImg_le_alt e _) hKt hKn
    hKequiv
  refine ⟨fixFin ye', hcard, ?_⟩
  rw [← hKeq]
  exact (corr_permImg e hN'L).symm

theorem exists_common_root_of_fix (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (e : L ≃* alternatingGroup (Fin n)) {y g : G}
    (hy : y ∈ L) (hy2 : orderOf y = 2) (hg : g * z * g⁻¹ = z * y)
    (hf : (5 ≤ (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ∧
        (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ≠ 6) ∨
      (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card = 4)
    (hid : NormalAltIdent n
      (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card)
    {S : Finset (Fin n)}
    (hS : ∀ i ∈ S, ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i) :
    ∃ S₁ : Finset (Fin n), S₁.card = S.card ∧
      rootGroup (G := G) e S = conjSub g (rootGroup e S₁) := by
  set F : Finset (Fin n) :=
    fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) with hF
  obtain ⟨F', hcard, hconj⟩ := exists_corr_eq_conj h d hQ2 hE e hy hy2 hg hid
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
  obtain ⟨β, hβ1, hβ2, hβ3, hβ4⟩ := exists_conj_intertwining e g hcard.symm hf hFF' hF'F
  have hSF : S ⊆ F := fun i hi => mem_fixFin.2 (hS i hi)
  refine ⟨S.image β, ?_, rootGroup_eq_conjSub_image e g hFF' hF'F hβ1 hβ2 hβ3 hβ4 hSF⟩
  exact Finset.card_image_of_injOn fun i hi j hj hij => hβ2 i (hSF hi) j (hSF hj) hij

end Main

end CFSG.OddStandard.AltStdSec
