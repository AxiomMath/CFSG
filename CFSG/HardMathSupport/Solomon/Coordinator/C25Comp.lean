module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCover
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FIa

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem c25_isQuasisimple_of_simple {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hna : ∃ a b : Q, a * b ≠ b * a) : CFSG.Open.IsQuasisimple Q := by
  obtain ⟨a, b, hab⟩ := hna
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      apply hab
      have : a ∈ Subgroup.center Q := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.mp this) b).symm
  have hC : commutator Q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      apply hab
      have h1 : a * b * a⁻¹ * b⁻¹ ∈ commutator Q := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
        _ = b * a := by rw [h1]; group
    · exact h
  refine ⟨hC, ?_⟩
  have e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.isSimpleGroup_congr.2 hs


omit [Finite G] in
private theorem c25_le_normalizer {J O : Subgroup G}
    (h : ∀ j ∈ J, ∀ n ∈ O, j * n * j⁻¹ ∈ O) : J ≤ Subgroup.normalizer (O : Set G) := by
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => h j hj n hn, fun hn => ?_⟩
  have := h j⁻¹ (J.inv_mem hj) _ hn
  simpa [mul_assoc] using this

theorem exists_component_of_normal_sup {C J : Subgroup G} (hJC : J ≤ C)
    (hD : ((J ⊔ GLAPPrimeCoreOf 3 C).subgroupOf C).Normal)
    (hJq : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J)) :
    ∃ J' : Subgroup G, GLAPComponent 3 C J' ∧
      Nonempty ((↥J' ⧸ GLAPPrimeCore 3 ↥J') ≃* (↥J ⧸ GLAPPrimeCore 3 ↥J)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set O := GLAPPrimeCoreOf 3 C with hO
  set D := J ⊔ O with hDdef
  have hOC : O ≤ C := glaPPrimeCoreOf_le C
  have hDC : D ≤ C := sup_le hJC hOC
  have hJD : J ≤ D := le_sup_left
  have hOD : O ≤ D := le_sup_right
  have hsnD : IsSubnormal D C := IsSubnormal.step hDC hD (IsSubnormal.refl C)
  have hJN : ∀ j ∈ J, ∀ n ∈ O, j * n * j⁻¹ ∈ O := fun j hj n hn =>
    conj_mem_glaPPrimeCoreOf (hJC hj) hn
  have hJnorm : J ≤ Subgroup.normalizer (O : Set G) := c25_le_normalizer hJN
  have hcoreD : GLAPPrimeCoreOf 3 D = O := by
    refine le_antisymm (glaPPrimeCoreOf_le_of_isSubnormal hp hsnD) ?_
    exact le_glaPPrimeCoreOf hOD (fun a ha n hn => conj_mem_glaPPrimeCoreOf (hDC ha) hn)
      (coprime_card_glaPPrimeCoreOf C)
  let ψ : ↥J →* ↥D ⧸ GLAPPrimeCore 3 ↥D :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥D)).comp (Subgroup.inclusion hJD)
  have hOmem : ∀ u (hu : u ∈ O), (⟨u, hOD hu⟩ : ↥D) ∈ GLAPPrimeCore 3 ↥D := fun u hu => by
    have hu' : u ∈ GLAPPrimeCoreOf 3 D := hcoreD ▸ hu
    exact (mem_glaPPrimeCoreOf_iff.1 hu').2
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨j, hj, u, hu, hdu⟩ := ia_exists_mul_of_mem_sup hJnorm d.2
    refine ⟨⟨j, hj⟩, ?_⟩
    show (QuotientGroup.mk (⟨j, hJD hj⟩ : ↥D) : ↥D ⧸ GLAPPrimeCore 3 ↥D) = QuotientGroup.mk d
    have hd : d = ⟨j, hJD hj⟩ * ⟨u, hOD hu⟩ := Subtype.ext hdu
    rw [hd, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (⟨u, hOD hu⟩ : ↥D)).2 (hOmem u hu)]
    simp
  have hker : GLAPPrimeCore 3 ↥J = ψ.ker := by
    ext x
    have hx1 : x ∈ ψ.ker ↔ (x : G) ∈ O := by
      rw [MonoidHom.mem_ker]
      show (QuotientGroup.mk (⟨(x : G), hJD x.2⟩ : ↥D) : ↥D ⧸ GLAPPrimeCore 3 ↥D) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff]
      constructor
      · intro h
        have : (x : G) ∈ GLAPPrimeCoreOf 3 D := mem_glaPPrimeCoreOf_iff.2 ⟨hJD x.2, h⟩
        rwa [hcoreD] at this
      · intro h
        have : (x : G) ∈ GLAPPrimeCoreOf 3 D := hcoreD ▸ h
        exact (mem_glaPPrimeCoreOf_iff.1 this).2
    rw [hx1]
    constructor
    · intro hx
      set N₀ := GLAPPrimeCoreOf 3 J with hN₀
      have hN₀J : N₀ ≤ J := glaPPrimeCoreOf_le J
      have hN₀D : N₀ ≤ D := hN₀J.trans hJD
      set φ : ↥D →* ↥D ⧸ GLAPPrimeCore 3 ↥D := QuotientGroup.mk' (GLAPPrimeCore 3 ↥D) with hφ
      set S : Subgroup (↥D ⧸ GLAPPrimeCore 3 ↥D) := (N₀.subgroupOf D).map φ with hS
      have hSnorm : ∀ g : ↥D ⧸ GLAPPrimeCore 3 ↥D, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
        intro g s hs
        obtain ⟨d0, rfl⟩ := QuotientGroup.mk_surjective g
        obtain ⟨m, hm, rfl⟩ := hs
        obtain ⟨j, hj, u, hu, hdu⟩ := ia_exists_mul_of_mem_sup hJnorm d0.2
        have hd : d0 = ⟨j, hJD hj⟩ * ⟨u, hOD hu⟩ := Subtype.ext hdu
        have hg : φ d0 = φ ⟨j, hJD hj⟩ := by
          rw [hd, map_mul, hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
            (QuotientGroup.eq_one_iff (⟨u, hOD hu⟩ : ↥D)).2 (hOmem u hu)]
          simp
        refine ⟨⟨j, hJD hj⟩ * m * ⟨j, hJD hj⟩⁻¹, ?_, ?_⟩
        · refine Subgroup.mem_subgroupOf.2 ?_
          exact conj_mem_glaPPrimeCoreOf (A := J) hj (Subgroup.mem_subgroupOf.1 hm)
        · simp only [map_mul, map_inv]
          change _ = φ d0 * φ m * (φ d0)⁻¹
          rw [hg]
      have hScard : Nat.Coprime 3 (Nat.card S) := by
        refine Nat.Coprime.coprime_dvd_right ?_ (coprime_card_glaPPrimeCoreOf J)
        refine (Subgroup.card_map_dvd (H := N₀.subgroupOf D) φ).trans ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀D).toEquiv]
      have hSle : S ≤ GLAPPrimeCore 3 (↥D ⧸ GLAPPrimeCore 3 ↥D) :=
        le_sSup ⟨⟨fun s hs g => hSnorm g s hs⟩, hScard⟩
      rw [glaPPrimeCore_quotient_eq_bot hp] at hSle
      have hxN : (x : G) ∈ N₀ := (mem_glaPPrimeCoreOf_iff.2 ⟨x.2, hx⟩)
      have h1 : φ ⟨(x : G), hN₀D hxN⟩ ∈ S := ⟨_, Subgroup.mem_subgroupOf.2 hxN, rfl⟩
      have h2 : φ ⟨(x : G), hN₀D hxN⟩ = 1 := Subgroup.mem_bot.1 (hSle h1)
      have h3 : (⟨(x : G), hN₀D hxN⟩ : ↥D) ∈ GLAPPrimeCore 3 ↥D := (QuotientGroup.eq_one_iff _).1 h2
      have : (x : G) ∈ GLAPPrimeCoreOf 3 D := mem_glaPPrimeCoreOf_iff.2 ⟨hN₀D hxN, h3⟩
      rwa [hcoreD] at this
    · intro hx
      have hle : J ⊓ O ≤ GLAPPrimeCoreOf 3 J := by
        refine le_glaPPrimeCoreOf inf_le_left (fun a ha n hn => ?_) ?_
        · exact ⟨J.mul_mem (J.mul_mem ha hn.1) (J.inv_mem ha), hJN a ha n hn.2⟩
        · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
            (coprime_card_glaPPrimeCoreOf C)
      exact (mem_glaPPrimeCoreOf_iff.1 (hle ⟨x.2, hx⟩)).2
  have e₁ : (↥J ⧸ GLAPPrimeCore 3 ↥J) ≃* (↥D ⧸ GLAPPrimeCore 3 ↥D) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)
  have hQ : CFSG.Open.IsQuasisimple (↥D ⧸ GLAPPrimeCore 3 ↥D) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₁ hJq
  obtain ⟨J₀, hJ₀, htop, -⟩ := exists_glaPComponent_of_isQuasisimple hQ
  refine ⟨J₀, ia_comp_up hp hJ₀ hDC (isSubnormal_trans' hJ₀.2.1 hsnD), ⟨?_⟩⟩
  exact (quotEquivBarX hp hJ₀.1 hJ₀.2.1).trans
    ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans e₁.symm))

end CFSG.HardMathSupport.Solomon.Coordinator
