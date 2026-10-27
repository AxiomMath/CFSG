module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UY6Fix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UY6Sylow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType CFSG.StandardType.NoOffRest CFSG.StandardType.NoOffE8Five

local instance y6FactFiveLang : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance y6NeZeroRankLang : NeZero Tag.E8.rank := ⟨by decide⟩

theorem exists_conjLe_of_lang {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) (hℓK : ℓ ∣ Nat.card K) {ζ : Lˣ}
    (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) {lam : ZMod 5} (hlam : lam * lam = -1)
    (hq : ((Nat.card K : ℕ) : ZMod 5) * lam = 1) (h5 : 5 ∣ Nat.card K * Nat.card K + 1)
    {g₀ : ModGL Tag.E8 L} (hg₀C : g₀ ∈ adjointGroup Tag.E8 L)
    (hg₀ : Units.map (entrywiseHom Fr) g₀ =
      g₀ * canonicalRep (coxeterSystem Tag.E8) L weylE8W) :
    ∃ ι : Multiplicative (eigE8 5 lam) →* adjointGroup Tag.E8 K,
      Function.Injective ι ∧ IsElemAbelian 5 ι.range ∧ Nat.card ι.range = 5 ^ 4 ∧
        ∀ A : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian 5 A → 5 ^ 3 ≤ Nat.card A →
          ∃ c : adjointGroup Tag.E8 K, A ≤ ι.range.map (MulAut.conj c).toMonoidHom := by
  classical
  haveI : Finite (ModGL Tag.E8 K) := finite_modGL
  obtain ⟨ι, hιinj, hιval⟩ := exists_langTorsionHom hFr hζo hζ hq hg₀C hg₀
  have hξ : ∀ s : eigE8 5 lam,
      g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) * g₀⁻¹ =
        adjEmb Tag.E8 K L (ι (Multiplicative.ofAdd s)) := fun s => by
    rw [hιval s, frameElt_apply]
  have hXT : ι.range ≤ langTorusRat K Fr g₀ := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨s, hvs⟩ : ∃ s, v = Multiplicative.ofAdd s := ⟨Multiplicative.toAdd v, rfl⟩
    rw [hvs, mem_langTorusRat, langPhi_apply, hιval s, frameElt_apply]
    have : g₀⁻¹ * (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) *
        g₀⁻¹) * g₀ = ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) := by
      group
    rw [this]
    exact (frameDiag_mem_twistedTorus_iff hFr hζo hζ hq _).2 s.2
  have hTp : ∀ t ∈ langTorusRat K Fr g₀, t ^ 5 = 1 → t ∈ ι.range := by
    intro t ht ht5
    have hx5 : (langPhi K g₀ t) ^ 5 = 1 := by rw [← map_pow, ht5, map_one]
    obtain ⟨s, hs, hts⟩ := exists_frameDiag_of_mem_twistedTorus_pow hFr hζo hζ hq ht hx5
    refine ⟨Multiplicative.ofAdd ⟨s, hs⟩, ?_⟩
    apply adjEmb_injective (K := K) (L := L) (τ := Tag.E8)
    rw [← hξ ⟨s, hs⟩, adjEmb_eq_conj_langPhi g₀ t, hts]
  have hcent : ∀ c : adjointGroup Tag.E8 K, (∀ x ∈ ι.range, c * x = x * c) →
      c ∈ langTorusRat K Fr g₀ := by
    intro c hc
    refine mem_langTorusRat_of_commute hFr hζo hζ hlam hg₀C hg₀ fun s hs => ?_
    have h1 := hc (ι (Multiplicative.ofAdd ⟨s, hs⟩)) ⟨_, rfl⟩
    have h2 := congrArg (adjEmb Tag.E8 K L) h1
    rw [map_mul, map_mul] at h2
    change adjEmb Tag.E8 K L c * (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * g₀⁻¹) =
      (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * g₀⁻¹) * adjEmb Tag.E8 K L c
    exact (hξ ⟨s, hs⟩).symm ▸ h2
  have hcardX : Nat.card ι.range = 5 ^ 4 := by
    rw [← card_eigE8 (p := 5) (by norm_num) hlam]
    exact (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  have hord : (Nat.card (adjointGroup Tag.E8 K)).factorization 5 =
      (Nat.card (langTorusRat K Fr g₀)).factorization 5 + 1 := by
    rw [factorization_card_adjointGroup_E8_five h5, card_langTorusRat hFr hℓK hg₀C hg₀,
      Nat.factorization_pow]
    simp
  have hfix : ∀ a : adjointGroup Tag.E8 K, a ∈ Subgroup.normalizer (ι.range : Set _) →
      a ^ 5 = 1 → (∃ x ∈ ι.range, a * x ≠ x * a) →
        Nat.card {x : ι.range // a * (x : adjointGroup Tag.E8 K) = (x : adjointGroup Tag.E8 K) * a}
          < 5 ^ 2 := by
    intro a ha ha5 hnc
    have hnorm : ∀ s : eigE8 5 lam, ∃ t : eigE8 5 lam,
        a * ι (Multiplicative.ofAdd s) * a⁻¹ = ι (Multiplicative.ofAdd t) := by
      intro s
      have h1 := (Subgroup.mem_normalizer_iff.mp ha (ι (Multiplicative.ofAdd s))).mp ⟨_, rfl⟩
      obtain ⟨v, hv⟩ := h1
      exact ⟨Multiplicative.toAdd v, hv.symm⟩
    exact card_centralizer_lt_sq_of_automizer hlam ι hιinj
      (exists_centE8W_conj_of_langTorsion hζo hζ hlam hg₀C (fun s => by rw [hιval s]) hnorm) ha5 hnc
  refine ⟨ι, hιinj, isElemAbelian_range_of_module (p := 5) ι, hcardX, fun A hA hA3 => ?_⟩
  exact exists_conj_map_le_of_exponent_card (p := 5) (T := langTorusRat K Fr g₀)
    (X := ι.range) hXT (fun x hx => (isElemAbelian_range_of_module (p := 5) ι).2 x hx) hTp hord
    hcent hfix (fun x hx y hy => congrArg Subtype.val (hA.1.1.1 ⟨x, hx⟩ ⟨y, hy⟩)) hA.2 hA3

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
