module

public import CFSG.CGT.T75I.NAct
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.CGT.T75I.CenBasic

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] noncomputable def hGamma (T₁ : Subgroup G) (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2)) :
    Subgroup (GL (Fin 4) (ZMod 2)) :=
  ((actGL e).comp (Subgroup.inclusion (hSub_le_normalizer' (T := T) (T₁ := T₁)))).range

theorem mem_hGamma {e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2)} {g : GL (Fin 4) (ZMod 2)} :
    g ∈ hGamma T₁ e ↔ ∃ (h : G) (hh : h ∈ hSub T (normIn T₁ T)),
      actGL e ⟨h, hSub_le_normalizer' hh⟩ = g := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem hGamma_equiv (hC : Subgroup.centralizer (T : Set G) = T)
    (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2))
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal] :
    Nonempty (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)) ≃*
      ↥(hGamma T₁ e)) := by
  let φ := (actGL e).comp (Subgroup.inclusion (hSub_le_normalizer' (T := T) (T₁ := T₁)))
  have hker : φ.ker = T.subgroupOf (hSub T (normIn T₁ T)) := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact actGL_eq_one_iff hC e ⟨h, hSub_le_normalizer' h.2⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)⟩

theorem hGamma_iso_of [Finite G] (hC : Subgroup.centralizer (T : Set G) = T)
    (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2))
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal] (k : ℕ) (hk : k = 6 ∨ k = 7)
    (hY : IsHatA k (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)))) :
    Nonempty (↥(hGamma T₁ e) ≃* alternatingGroup (Fin k)) := by
  classical
  obtain ⟨eY⟩ := hGamma_equiv (T₁ := T₁) hC e
  have hdvd : Nat.card ↥(hGamma T₁ e) ∣ 20160 := by
    have := Subgroup.card_subgroup_dvd_card (hGamma T₁ e)
    rwa [CFSG.GH74.Exceptional.card_GL_four_two] at this
  have hcardΓ : Nat.card ↥(hGamma T₁ e) =
      Nat.card (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) :=
    (Nat.card_congr eY.toEquiv).symm
  obtain ⟨-, Z, -, hZcard, hZn, ⟨φ⟩⟩ := hY
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hA : Nat.card (alternatingGroup (Fin k)) = k.factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have hY : Nat.card (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) =
      k.factorial / 2 * Nat.card Z := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, Nat.card_congr φ.toEquiv, hA]
  have hZ : Nat.card Z = 1 ∨ Nat.card Z = 3 := (Nat.dvd_prime Nat.prime_three).1 hZcard
  have hZ1 : Nat.card Z = 1 := by
    rcases hZ with h | h
    · exact h
    · exfalso
      rw [hcardΓ, hY, h] at hdvd
      rcases hk with rfl | rfl <;> revert hdvd <;> decide
  have hZbot : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z hZ1
  subst hZbot
  exact ⟨eY.symm.trans (QuotientGroup.quotientBot.symm.trans φ)⟩

theorem conj_mem_hGamma {e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2)}
    (n : ↥(Subgroup.normalizer (T : Set G))) {g : GL (Fin 4) (ZMod 2)}
    (hg : g ∈ hGamma T₁ e) :
    actGL e n * g * (actGL e n)⁻¹ ∈ hGamma T₁ e := by
  obtain ⟨h, hh, rfl⟩ := mem_hGamma.1 hg
  refine mem_hGamma.2 ⟨(n : G) * h * (n : G)⁻¹, conj_mem_hSub n.2 hh, ?_⟩
  have e1 : (⟨(n : G) * h * (n : G)⁻¹, hSub_le_normalizer' (conj_mem_hSub n.2 hh)⟩ :
      ↥(Subgroup.normalizer (T : Set G))) =
      n * ⟨h, hSub_le_normalizer' hh⟩ * n⁻¹ := Subtype.ext rfl
  rw [e1, map_mul, map_mul, map_inv]

theorem actGL_mem_normalizer_hGamma {e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2)}
    (n : ↥(Subgroup.normalizer (T : Set G))) :
    actGL e n ∈ Subgroup.normalizer (hGamma T₁ e : Set (GL (Fin 4) (ZMod 2))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_hGamma n hg, fun h => ?_⟩
  have := conj_mem_hGamma (e := e) (T₁ := T₁) n⁻¹ h
  rw [map_inv, inv_inv] at this
  have e2 : (actGL e n)⁻¹ * (actGL e n * g * (actGL e n)⁻¹) * actGL e n = g := by group
  rwa [e2] at this

theorem mem_hSub_of_actGL_mem {e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2)}
    (hC : Subgroup.centralizer (T : Set G) = T) (n : ↥(Subgroup.normalizer (T : Set G)))
    (hn : actGL e n ∈ hGamma T₁ e) : (n : G) ∈ hSub T (normIn T₁ T) := by
  obtain ⟨h, hh, hθ⟩ := mem_hGamma.1 hn
  have h1 : actGL e (⟨h, hSub_le_normalizer' hh⟩⁻¹ * n) = 1 := by
    rw [map_mul, map_inv, hθ, inv_mul_cancel]
  have h2 := (actGL_eq_one_iff hC e _).1 h1
  have h3 : h⁻¹ * (n : G) ∈ T := h2
  have h4 : (n : G) = h * (h⁻¹ * (n : G)) := by group
  rw [h4]
  exact (hSub T (normIn T₁ T)).mul_mem hh (left_le_hSub h3)

end CFSG.CGT.T75I
