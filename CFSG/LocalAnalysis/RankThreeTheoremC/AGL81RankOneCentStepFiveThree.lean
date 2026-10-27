module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc5
import CFSG.RankThree.PartOne.FTL.Frattini
import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open

variable {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

theorem mem_centralizer_of_comm_mem_frattini {S : Subgroup A} (hS : IsPGroup p S) {x : A}
    (hxN : x ∈ Subgroup.normalizer (S : Set A)) {m : ℕ} (hxm : x ^ m = 1)
    (hcop : Nat.Coprime m p)
    (htriv : ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ (frattini ↥S).map S.subtype) :
    x ∈ Subgroup.centralizer (S : Set A) := by
  set τ : MulAut ↥S := Subgroup.normalizerMonoidHom S ⟨x, hxN⟩ with hτ
  have hτs : ∀ s : ↥S, ((τ s : ↥S) : A) = x * s * x⁻¹ := fun s => rfl
  have hτm : τ ^ m = 1 := by
    rw [hτ, ← map_pow]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (S : Set A)) ^ m = 1 := Subtype.ext (by simpa using hxm)
    rw [this, map_one]
  have htr : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥S) τ =
      1 := by
    ext q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥S) q
    change QuotientGroup.mk' (frattini ↥S) (τ s) = QuotientGroup.mk' (frattini ↥S) s
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨f, hf, hfe⟩ := htriv s s.2
    have hfτ : f = τ s * s⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv, hτs]; exact hfe)
    have hf' : (τ s)⁻¹ * s = s⁻¹ * f⁻¹ * s⁻¹⁻¹ := by rw [hfτ]; group
    rw [hf']
    have hn : (frattini ↥S).Normal := inferInstance
    exact hn.conj_mem f⁻¹ ((frattini ↥S).inv_mem hf) s⁻¹
  have h1 := CFSG.RankThree.PartOne.FTL.eq_one_of_trivial_mod_frattini hS hτm hcop htr
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have := congrArg (fun σ : MulAut ↥S => ((σ ⟨s, hs⟩ : ↥S) : A)) h1
  simp only [hτs, MulAut.one_apply] at this
  calc s * x = (x * s * x⁻¹) * x := by rw [this]
    _ = x * s := by group

theorem hasNormalPComplement_of_comm_mem_frattini {S L : Subgroup A} (hS : IsPGroup p S)
    (hC : CFSG.HasNormalPComplement p ↥(Subgroup.centralizer (S : Set A)))
    (hLN : L ≤ Subgroup.normalizer (S : Set A))
    (htriv : ∀ g ∈ L, ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ (frattini ↥S).map S.subtype) :
    CFSG.HasNormalPComplement p ↥L := by
  have hp : p.Prime := Fact.out
  set N : Subgroup ↥L := (Subgroup.centralizer (S : Set A)).subgroupOf L with hN
  haveI hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : A) ∈ Subgroup.normalizer (S : Set A) := hLN g.2
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro s hs
    have hs' : (g : A)⁻¹ * s * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp hg ((g : A)⁻¹ * s * g)).mpr (by simpa [mul_assoc])
      exact this
    have h := hn _ hs'
    have e : ((g * n * g⁻¹ : ↥L) : A) = (g : A) * (n : A) * (g : A)⁻¹ := by simp
    rw [e]
    calc s * ((g : A) * (n : A) * (g : A)⁻¹)
        = (g : A) * (((g : A)⁻¹ * s * g) * n) * (g : A)⁻¹ := by group
      _ = (g : A) * (n * ((g : A)⁻¹ * s * g)) * (g : A)⁻¹ := by rw [h]
      _ = (g : A) * (n : A) * (g : A)⁻¹ * s := by group
  have hc : CFSG.HasNormalPComplement p ↥N := by
    let f : ↥N →* ↥(Subgroup.centralizer (S : Set A)) :=
      { toFun := fun n => ⟨((n : ↥L) : A), n.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc5.hasNormalPComplement_of_injective
      f (fun a b hab => ?_) hC
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc5.hasNormalPComplement_of_normal
    (fun q => ?_) hc
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  set n := orderOf g with hn
  have hn0 : n ≠ 0 := (orderOf_pos g).ne'
  refine ⟨n.factorization p, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
  have hy : ((g : A) ^ (p ^ n.factorization p)) ^ (ordCompl[p] n) = 1 := by
    rw [← pow_mul, Nat.ordProj_mul_ordCompl_eq_self, hn, ← Subgroup.orderOf_coe,
      pow_orderOf_eq_one]
  have hgL : (g : A) ^ (p ^ n.factorization p) ∈ L := L.pow_mem g.2 _
  have := mem_centralizer_of_comm_mem_frattini hS (hLN hgL) hy
    (Nat.coprime_ordCompl hp hn0).symm (htriv _ hgL)
  simpa using this

theorem le_of_not_hasNormalPComplement (hI1 : KFactStepThreeCentNilp) (hI2 : KFactStepThreeIrred)
    {Inn S N L : Subgroup A} (hInn : Inn.Normal)
    (hCI : Subgroup.centralizer (Inn : Set A) = ⊥) (hSt : StepThreeGroup p ↥Inn)
    (hS : CFSG.ABGLocalTools.IsSylowOf p S Inn) (hNS : N ≤ Subgroup.normalizer (S : Set A))
    (hIN : Inn ⊓ Subgroup.normalizer (S : Set A) ≤ N) (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set A)) (hnp : ¬ CFSG.HasNormalPComplement p ↥L) :
    S ≤ L := by
  have hSp : IsPGroup p S := hS.isPGroup
  have hSI : S ≤ Inn := hS.le
  have hSN : S ≤ N := hIN.trans' (le_inf hSI Subgroup.le_normalizer)
  set W := L ⊓ S with hW
  have hNW : N ≤ Subgroup.normalizer (W : Set A) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNL hg, hNS hg⟩
  have hWΦ : ¬ W ≤ (frattini ↥S).map S.subtype := by
    intro hle
    apply hnp
    refine hasNormalPComplement_of_comm_mem_frattini hSp (hI1 p A Inn S hInn hCI hSt hS)
      (hLN.trans hNS) fun g hg s hs => hle ⟨?_, ?_⟩
    · have h1 : s * g⁻¹ * s⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hNL (hSN hs)) g⁻¹).mp (L.inv_mem hg)
      have := L.mul_mem hg h1
      simpa [mul_assoc] using this
    · have h1 : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hNS (hLN hg)) s).mp hs
      exact S.mul_mem h1 (S.inv_mem hs)
  obtain ⟨S₀, hS₀⟩ := hS
  set V₀ : Subgroup ↥Inn := W.comap Inn.subtype with hV₀
  have hV₀S : V₀ ≤ (S₀ : Subgroup ↥Inn) := by
    intro x hx
    have hxS : (x : A) ∈ S := hx.2
    rw [← hS₀] at hxS
    obtain ⟨y, hy, hyx⟩ := hxS
    rwa [Inn.subtype_injective hyx] at hy
  have hV₀Φ : ¬ V₀ ≤ (frattini ↥(S₀ : Subgroup ↥Inn)).map (S₀ : Subgroup ↥Inn).subtype := by
    intro hle
    apply hWΦ
    intro w hw
    have hwI : w ∈ Inn := hSI hw.2
    have hx : (⟨w, hwI⟩ : ↥Inn) ∈ V₀ := hw
    have h := CFSG.RankThree.PartOne.Torsion37.inSubgroup_frattini_map Inn.subtype
      Inn.subtype_injective (S₀ : Subgroup ↥Inn)
    unfold CFSG.inSubgroup at h
    rw [hS₀] at h
    rw [h]
    exact ⟨_, hle hx, rfl⟩
  have hN₀ : Subgroup.normalizer ((S₀ : Subgroup ↥Inn) : Set ↥Inn) ≤
      Subgroup.normalizer (V₀ : Set ↥Inn) := by
    intro k hk
    have hkS : (k : A) ∈ Subgroup.normalizer (S : Set A) := by
      rw [← hS₀]
      exact Subgroup.le_normalizer_map Inn.subtype ⟨k, hk, rfl⟩
    exact Subgroup.le_normalizer_comap Inn.subtype (hNW (hIN ⟨k.2, hkS⟩))
  have heq := (hI2 p ↥Inn hSt S₀).1 V₀ hV₀S hV₀Φ hN₀
  intro s hs
  have hs' := hs
  rw [← hS₀, ← heq] at hs'
  obtain ⟨x, hx, rfl⟩ := hs'
  exact hx.1

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
