module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BFi24QR
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BFi24Aut
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenFour

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S8
open CFSG.LocalAnalysis.GLTheoremA.H301B (exists_mulEquiv_fi24R fi24QR_local
  comm_of_mem_normalizer)
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime (zR fi24QR fi24CR fi24CR_injective)
open CFSG.EvenSporadicStandard.TwoFi22.DS81 (fi24QC card_fi24QC)
open CFSG.Sporadic.Fi24 (R jR)

private theorem exists_normalizing_of_not_le {G : Type*} [Group G] [Finite G]
    {Q R' : Subgroup G} (hR : IsPGroup 2 R') (hRR : Q ≤ R') (hne : ¬ R' ≤ Q) :
    ∃ y ∈ R', y ∈ Subgroup.normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hR.isNilpotent
  set Q' : Subgroup R' := Q.subgroupOf R'
  have hlt : Q' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun r hr => ?_
    have h1 : (⟨r, hr⟩ : R') ∈ Q' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨y, hyN, hyQ⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q' hlt)
  have hconj : ∀ u : R', u ∈ Subgroup.normalizer (Q' : Set R') → ∀ q ∈ Q,
      (u : G) * q * (u : G)⁻¹ ∈ Q := by
    intro u hu q hq
    have h1 := (Subgroup.mem_normalizer_iff.1 hu ⟨q, hRR hq⟩).1 (Subgroup.mem_subgroupOf.2 hq)
    have h2 := Subgroup.mem_subgroupOf.1 h1
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  have hN : (y : G) ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hconj y hyN q, fun hq => ?_⟩
    have h := hconj y⁻¹ ((Subgroup.normalizer (Q' : Set R')).inv_mem hyN) _ hq
    rw [Subgroup.coe_inv, inv_inv] at h
    have e : (y : G)⁻¹ * ((y : G) * q * (y : G)⁻¹) * (y : G) = q := by group
    rwa [e] at h
  exact ⟨y, y.2, hN, fun h => hyQ (Subgroup.mem_subgroupOf.2 h)⟩

private theorem exists_conj_embedding {K A : Type*} [Group K] [Group A] (ι : K →* A)
    (hι : Function.Injective ι) (hN : ι.range.Normal)
    (hC : Subgroup.centralizer (ι.range : Set A) = ⊥) :
    ∃ c : A →* MulAut K, Function.Injective c ∧ ∀ k : K, c (ι k) = MulAut.conj k := by
  have := hN
  have hinj : Function.Injective (MulAut.conjNormal : A →* MulAut ι.range) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : a ∈ Subgroup.centralizer (ι.range : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 := congrArg (fun α : MulAut ι.range => ((α ⟨f, hf⟩ : ι.range) : A)) ha
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc f * a = a * f * a⁻¹ * a := by rw [h1]
        _ = a * f := by group
    rw [hC, Subgroup.mem_bot] at hc
    exact hc
  refine ⟨(MulAut.congr (MonoidHom.ofInjective hι).symm).toMonoidHom.comp MulAut.conjNormal,
    (MulAut.congr _).injective.comp hinj, fun k => MulEquiv.ext fun x => hι ?_⟩
  simp [MulAut.conj_apply, MonoidHom.ofInjective_apply]

private theorem hMax_of_mulEquiv {K G A : Type} [Group K] [Group G] [Finite G] [Group A]
    [Finite A] {Q B : Subgroup K} {z : K} (hQ : IsExtraSpec2 Q) (hzQ : z ∈ Q)
    (hzc : ∀ q ∈ Q, q * z = z * q) (hz1 : z ≠ 1) (hB : IsElemAbelian 3 B)
    (hBc : Nat.card B = 3 ^ 5) (hBz : ∀ b ∈ B, b * z = z * b)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set K)) (e : MulAut K ≃* G) {J Q₀ : Subgroup G} {a : G}
    (hez : e (MulAut.conj z) = a) (hinn : ∀ k : K, e (MulAut.conj k) ∈ J)
    (hQ₀ : Nat.card Q₀ = Nat.card Q)
    (hU : ∀ F : Subgroup G, F ≤ J → F ≤ Subgroup.centralizer ({a} : Set G) →
      IsElemAbelian 3 F → Nat.card F = 243 → ∀ T : Subgroup G, IsPGroup 2 T →
      T ≤ Subgroup.centralizer ({a} : Set G) → F ≤ Subgroup.normalizer (T : Set G) → T ≤ Q₀)
    {ι : K →* A} (hι : Function.Injective ι) {c : A →* MulAut K} (hc : Function.Injective c)
    (hcι : ∀ k : K, c (ι k) = MulAut.conj k) {R' : Subgroup A} (hR' : IsPGroup 2 R')
    (hBR : B.map ι ≤ Subgroup.normalizer (R' : Set A)) (hQR : Q.map ι ≤ R') :
    R' = Q.map ι := by
  obtain ⟨f, hfdef⟩ : ∃ f : A →* G, f = e.toMonoidHom.comp c := ⟨_, rfl⟩
  have hf : Function.Injective f := by
    rw [hfdef]
    exact e.injective.comp hc
  have hfι : ∀ k : K, f (ι k) = e (MulAut.conj k) := fun k => by
    rw [hfdef, MonoidHom.comp_apply, hcι]
    rfl
  have hfz : f (ι z) = a := by rw [hfι, hez]
  have hcomm : ∀ x : A, x * ι z = ι z * x → f x ∈ Subgroup.centralizer ({a} : Set G) :=
    fun x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hfz]
      exact (map_mul f x (ι z)).symm.trans ((congrArg f hx).trans (map_mul f (ι z) x))
  have hFJ : (B.map ι).map f ≤ J := by
    rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
    rw [hfι]
    exact hinn b
  have hFz : (B.map ι).map f ≤ Subgroup.centralizer ({a} : Set G) := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact hcomm _ ((map_mul ι b z).symm.trans ((congrArg ι (hBz b hb)).trans (map_mul ι z b)))
  have hFc : Nat.card ((B.map ι).map f) = 243 := by
    rw [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hι, hBc]
    norm_num
  have hUF := hU _ hFJ hFz ((hB.map ι).map f) hFc
  have hQι : timmesfeldIsExtraspecial ↥(Q.map ι) :=
    CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
      (Q.equivMapOfInjective ι hι) hQ
  have hzι : ι z ∈ Q.map ι := Subgroup.mem_map_of_mem ι hzQ
  have hzιc : ∀ r ∈ Q.map ι, r * ι z = ι z * r := by
    rintro _ ⟨q, hq, rfl⟩
    exact (map_mul ι q z).symm.trans ((congrArg ι (hzc q hq)).trans (map_mul ι z q))
  have hzι1 : ι z ≠ 1 := fun h => hz1 (hι (h.trans (map_one ι).symm))
  let N : Subgroup A := R' ⊓ Subgroup.normalizer ((Q.map ι : Subgroup A) : Set A)
  have hN2 : IsPGroup 2 N := hR'.to_le inf_le_left
  have hNz : N.map f ≤ Subgroup.centralizer ({a} : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    exact hcomm n (comm_of_mem_normalizer hQι hzι hzιc hzι1 (Subgroup.mem_inf.1 hn).2)
  have hBQι : B.map ι ≤ Subgroup.normalizer ((Q.map ι : Subgroup A) : Set A) :=
    (Subgroup.map_mono hBQ).trans (Subgroup.le_normalizer_map ι)
  have hBN : B.map ι ≤ Subgroup.normalizer (N : Set A) := by
    intro b hb
    have hbR := Subgroup.mem_normalizer_iff.1 (hBR hb)
    have hbQ := hBQι hb
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · exact Subgroup.mem_inf.2 ⟨(hbR n).1 (Subgroup.mem_inf.1 hn).1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hbQ (Subgroup.mem_inf.1 hn).2)
          (Subgroup.inv_mem _ hbQ)⟩
    · have hn' := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨(hbR n).2 hn'.1, ?_⟩
      have e : b⁻¹ * (b * n * b⁻¹) * b = n := by group
      rw [← e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hbQ) hn'.2) hbQ
  have hNQ : N.map f ≤ Q₀ :=
    hUF _ (hN2.map f) hNz ((Subgroup.map_mono hBN).trans (Subgroup.le_normalizer_map f))
  have hQN : Q.map ι ≤ N := le_inf hQR Subgroup.le_normalizer
  have hQeq : (Q.map ι).map f = Q₀ :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.map_mono hQN).trans hNQ) (le_of_eq (by
      rw [hQ₀, Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hι]))
  refine le_antisymm ?_ hQR
  by_contra hne
  obtain ⟨y, hyR, hyN, hyQ⟩ := exists_normalizing_of_not_le hR' hQR hne
  have hy : f y ∈ (Q.map ι).map f := by
    rw [hQeq]
    exact hNQ (Subgroup.mem_map_of_mem f (Subgroup.mem_inf.2 ⟨hyR, hyN⟩))
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
  exact hyQ (hf hxy ▸ hx)


theorem fi24_hMax {K : Type} [Group K] [Finite K] (hK : catalogIs K (sporIs .Fi24Prime))
    {Q B : Subgroup K} {z : K} (hQ : IsExtraSpec2 Q) (hQc : Nat.card Q = 2 ^ 13)
    (hzQ : z ∈ Q) (hzc : ∀ q ∈ Q, q * z = z * q) (hz1 : z ≠ 1)
    (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 3 ^ 5) (hBz : ∀ b ∈ B, b * z = z * b)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set K)) :
    ∀ (A : Type) [Group A] [Finite A] (ι : K →* A), Function.Injective ι → ι.range.Normal →
      Subgroup.centralizer (ι.range : Set A) = ⊥ → ∀ R' : Subgroup A, IsPGroup 2 R' →
      B.map ι ≤ Subgroup.normalizer (R' : Set A) → Q.map ι ≤ R' → R' = Q.map ι := by
  intro A _ _ ι hι hN hC R' hR' hBR hQR
  obtain ⟨c, hc, hcι⟩ := exists_conj_embedding ι hι hN hC
  have hγinj : Function.Injective (MulAut.conj : K →* MulAut K) := fun x y h =>
    hι (hc (by rw [hcι, hcι]; exact h))
  have hγcomm : ∀ x y : K, x * y = y * x →
      MulAut.conj x * MulAut.conj y = MulAut.conj y * MulAut.conj x := fun x y h =>
    (map_mul MulAut.conj x y).symm.trans ((congrArg MulAut.conj h).trans (map_mul MulAut.conj y x))
  have hQγ : IsExtraSpec2 (Q.map (MulAut.conj : K →* MulAut K)) :=
    CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
      (Q.equivMapOfInjective _ hγinj) hQ
  have hQγc : Nat.card (Q.map (MulAut.conj : K →* MulAut K)) = 2 ^ 13 :=
    (Subgroup.card_map_of_injective hγinj).trans hQc
  obtain ⟨e, hez, hinn⟩ := exists_mulEquiv_fi24R hK hQγ (by rw [hQγc]; norm_num)
    (Subgroup.mem_map_of_mem _ hzQ)
    (by rintro _ ⟨q, hq, rfl⟩; exact hγcomm q z (hzc q hq))
    (fun h => hz1 (hγinj (h.trans (map_one _).symm))) (Subgroup.map_le_range _ B) (hB.map _)
    ((Subgroup.card_map_of_injective hγinj).trans hBc)
    (by rintro _ ⟨b, hb, rfl⟩; exact hγcomm b z (hBz b hb))
    ((Subgroup.map_mono hBQ).trans (Subgroup.le_normalizer_map _))
  have hcardQR : Nat.card ↥fi24QR = 2 ^ 13 := by
    show Nat.card ↥(fi24QC.map fi24CR) = 2 ^ 13
    rw [Subgroup.card_map_of_injective fi24CR_injective, card_fi24QC]
  have key := hMax_of_mulEquiv (K := K) (G := ↥R) (A := A) (Q := Q) (B := B) (z := z)
    (J := jR.range) (Q₀ := fi24QR) (a := zR)
  exact key hQ hzQ hzc hz1 hB hBc hBz hBQ e hez (fun k => hinn _ ⟨k, rfl⟩)
    (hcardQR.trans hQc.symm) (fun F h1 h2 h3 h4 => (fi24QR_local.2.2 F h1 h2 h3 h4).2.2.1)
    hι hc hcι hR' hBR hQR

end CFSG.LocalAnalysis.GLTheoremA.H301

end
