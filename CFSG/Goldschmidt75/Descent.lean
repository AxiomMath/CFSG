module

public import CFSG.Goldschmidt75.Closure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.X.ConjugationFamily

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

@[expose] def Respects (R : Set G → Set G → Prop) (P S₀ : Subgroup G) : Prop :=
  ∀ h ∈ normalizer (S₀ : Set G), ∀ U : Set G,
    U ⊆ ((P ⊓ normalizer (S₀ : Set G) : Subgroup G) : Set G) → rconj h U ⊆ P → R U (rconj h U)

theorem conjSub_closure (g : G) (U : Set G) : conjSub g (closure U) = closure (rconj g U) := by
  unfold conjSub rconj
  rw [MonoidHom.map_closure]
  rfl

variable [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) {S : Subgroup G}

theorem respects_conj_of_le (hSP : S ≤ P) (hS : fusionStronglyClosed (S : Set G) P)
    (hS1 : S ≠ ⊥) {R : Set G → Set G → Prop} (hR : Equivalence R) {m : ℕ}
    (hresp : ∀ S₁ : Subgroup G, S₁ ≤ S → S₁ ≠ ⊥ → m ≤ Nat.card S₁ → Respects R P S₁)
    {A : Subgroup G} (hAP : A ≤ P) (hm : m ≤ Nat.card ↥(S ⊓ A)) {z : G}
    (hz : conjSub z A ≤ P) : ∀ U : Set G, U ⊆ A → R U (rconj z U) := by
  obtain ⟨z₀, hz₀S, hz₀1, hz₀c⟩ := exists_mem_center P hSP hS hS1
  suffices key : ∀ z : G, HuppertCentricConjugationDecomposition (P : Subgroup G)
      (HuppertExtremal P) A z → ∀ U : Set G, U ⊆ A → R U (rconj z U) from
    key z (HuppertExtremal.centric_conjugation_decomposition P hAP hz)
  intro z hdec
  induction hdec with
  | one => intro U _; rw [rconj_one]; exact hR.refl U
  | @tail g h U₀ _ _ hU₀P hcur hn hcase ih =>
    intro U hU
    have hgU : rconj g U ⊆ U₀ := by
      have : rconj g U ⊆ ((conjSub g A : Subgroup G) : Set G) := by
        rw [coe_conjSub]; exact rconj_mono hU
      exact this.trans hcur
    rw [rconj_mul]
    rcases hcase with hcen | hcen
    ·
      set S₁ := S ⊓ U₀
      have hz₀U₀ : z₀ ∈ U₀ := hcen ⟨hSP hz₀S, Subgroup.centralizer_le hU₀P hz₀c⟩
      have hS₁1 : S₁ ≠ ⊥ := by
        intro h
        have : z₀ ∈ S₁ := ⟨hz₀S, hz₀U₀⟩
        rw [h, mem_bot] at this
        exact hz₀1 this
      have hmS₁ : m ≤ Nat.card S₁ := by
        have hle : conjSub g (S ⊓ A) ≤ S₁ := by
          have h1 : conjSub g (S ⊓ A) ≤ U₀ := (conjSub_mono inf_le_right).trans hcur
          exact le_inf (conjSub_le P hS inf_le_left (h1.trans hU₀P)) h1
        calc m ≤ Nat.card ↥(S ⊓ A) := hm
          _ = Nat.card (conjSub g (S ⊓ A)) := (card_conjSub g _).symm
          _ ≤ Nat.card S₁ := Subgroup.card_le_of_le hle
      have hhS₁ : h ∈ normalizer (S₁ : Set G) := normalizer_le_normalizer_inf P hS hU₀P hn
      have hsub : rconj g U ⊆ ((P ⊓ normalizer (S₁ : Set G) : Subgroup G) : Set G) :=
        fun x hx => ⟨hU₀P (hgU hx), le_normalizer_inf P hSP hS hU₀P (hgU hx)⟩
      have hsubP : rconj h (rconj g U) ⊆ P :=
        (rconj_subset_of_mem_normalizer hn hgU).trans hU₀P
      exact hR.trans (ih U hU) (hresp S₁ inf_le_left hS₁1 hmS₁ h hhS₁ _ hsub hsubP)
    ·
      rw [rconj_eq_self_of_mem_centralizer hcen hgU]
      exact ih U hU

theorem respects_all (hSP : S ≤ P) (hS : fusionStronglyClosed (S : Set G) P) (hS1 : S ≠ ⊥)
    {R : Set G → Set G → Prop} (hR : Equivalence R)
    (hstep : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → FullyNormalized p P S₀ →
      (∀ S₁ : Subgroup G, S₁ ≤ S → Nat.card S₀ < Nat.card S₁ → Respects R P S₁) →
      Respects R P S₀) :
    ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → Respects R P S₀ := by
  suffices key : ∀ n, ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ →
      Nat.card S - Nat.card S₀ = n → Respects R P S₀ from
    fun S₀ h1 h2 => key _ S₀ h1 h2 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S₀ hS₀ hS₀1 hn
  have hlarger : ∀ S₁ : Subgroup G, S₁ ≤ S → Nat.card S₀ < Nat.card S₁ → Respects R P S₁ := by
    intro S₁ hS₁ hlt
    have hS₁1 : S₁ ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hlt
      exact absurd hlt (by have := Nat.card_pos (α := S₀); omega)
    have hle := Subgroup.card_le_of_le hS₁
    exact ih _ (by omega) S₁ hS₁ hS₁1 rfl
  by_cases hfn : FullyNormalized p P S₀
  · exact hstep S₀ hS₀ hS₀1 hfn hlarger
  have hlt : S₀ < S := lt_of_le_of_ne hS₀ fun h => hfn (h ▸ fullyNormalized_self P hSP hS)
  obtain ⟨y, hyA, hyS, hyfn⟩ := exists_conj_fullyNormalized P hSP hS hS₀
  set A := (P : Subgroup G) ⊓ normalizer (S₀ : Set G) with hAdef
  have hmA : Nat.card S₀ + 1 ≤ Nat.card ↥(S ⊓ A) := by
    have e : S ⊓ A = S ⊓ normalizer (S₀ : Set G) := by
      rw [hAdef, ← inf_assoc, inf_eq_left.mpr hSP]
    rw [e]
    exact Subgroup.card_lt_of_lt (lt_inf_normalizer (P.isPGroup'.to_le hSP) hlt)
  have hconjA := respects_conj_of_le P hSP hS hS1 hR
    (fun S₁ h1 _ h3 => hlarger S₁ h1 (by omega)) inf_le_left hmA hyA
  have hS₀y1 : conjSub y S₀ ≠ ⊥ := by
    intro h
    apply hS₀1
    rw [← Subgroup.card_eq_one, ← card_conjSub y S₀, h, Subgroup.card_bot]
  have hrespy : Respects R P (conjSub y S₀) :=
    hstep _ hyS hS₀y1 hyfn fun S₁ h1 h2 => hlarger S₁ h1 (by rwa [card_conjSub] at h2)
  intro h hh U hU hUh
  have hUA : U ⊆ A := hU
  have hUhA : rconj h U ⊆ A := fun x hx =>
    ⟨hUh hx, rconj_subset_of_mem_normalizer (A := normalizer (S₀ : Set G))
      (Subgroup.le_normalizer hh) (fun u hu => (hU hu).2) hx⟩
  have h1 := hconjA U hUA
  have h2 := hconjA (rconj h U) hUhA
  have hyAP : rconj y (A : Set G) ⊆ P := by rw [← coe_conjSub]; exact hyA
  have hyAN : rconj y (A : Set G) ⊆ normalizer ((conjSub y S₀ : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_rconj] at hx
    exact mem_normalizer_conjSub_iff.mpr hx.2
  have h3 : R (rconj y U) (rconj (y⁻¹ * h * y) (rconj y U)) := by
    have hconj : rconj (y⁻¹ * h * y) (rconj y U) = rconj y (rconj h U) := by
      rw [← rconj_mul, ← rconj_mul]
      congr 1
      group
    apply hrespy
    · rw [mem_normalizer_conjSub_iff]
      simpa [mul_assoc] using hh
    · exact fun x hx => ⟨hyAP (rconj_mono hUA hx), hyAN (rconj_mono hUA hx)⟩
    · rw [hconj]
      exact hyAP.trans' (rconj_mono hUhA)
  have hconj : rconj (y⁻¹ * h * y) (rconj y U) = rconj y (rconj h U) := by
    rw [← rconj_mul, ← rconj_mul]
    congr 1
    group
  rw [hconj] at h3
  exact hR.trans h1 (hR.trans h3 (hR.symm h2))

theorem descent (hSP : S ≤ P) (hS : fusionStronglyClosed (S : Set G) P) (hS1 : S ≠ ⊥)
    {R : Set G → Set G → Prop} (hR : Equivalence R)
    (hstep : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → FullyNormalized p P S₀ →
      (∀ S₁ : Subgroup G, S₁ ≤ S → Nat.card S₀ < Nat.card S₁ → Respects R P S₁) →
      Respects R P S₀) :
    ∀ U : Set G, U ⊆ P → ∀ g : G, rconj g U ⊆ P → R U (rconj g U) := by
  intro U hU g hg
  have hall := respects_all P hSP hS hS1 hR hstep
  have hA : closure U ≤ P := (closure_le _).2 hU
  have hz : conjSub g (closure U) ≤ P := by
    rw [conjSub_closure]
    exact (closure_le _).2 hg
  exact respects_conj_of_le P hSP hS hS1 hR (m := 1) (fun S₁ h1 h2 _ => hall S₁ h1 h2) hA
    Nat.card_pos hz U subset_closure

end CFSG.Goldschmidt75
